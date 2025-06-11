use std::collections::VecDeque;
use std::os::fd::AsRawFd;
use std::result;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;

use evdev::Device;
use nix::ioctl_read_buf;
use utils::eventfd::EventFd;
use vm_memory::{ByteValued, Bytes, GuestMemoryMmap};

use super::super::{
    ActivateError, ActivateResult, DeviceState, Queue as VirtQueue, VirtioDevice,
    VIRTIO_MMIO_INT_VRING,
};
use super::{defs, defs::uapi, InputError, Result};
use crate::legacy::IrqChip;
use crate::Error as DeviceError;

// Request queue.
pub(crate) const REQ_INDEX: usize = 0;

// Supported features.
pub(crate) const AVAIL_FEATURES: u64 = 1 << uapi::VIRTIO_F_VERSION_1 as u64;

ioctl_read_buf!(eviocgname, b'E', 0x06, u8);
ioctl_read_buf!(eviocgbit_key, b'E', 0x21, u8);
ioctl_read_buf!(eviocgbit_relative, b'E', 0x22, u8);
ioctl_read_buf!(eviocgbit_absolute, b'E', 0x23, u8);
ioctl_read_buf!(eviocgbit_misc, b'E', 0x24, u8);
ioctl_read_buf!(eviocgbit_switch, b'E', 0x25, u8);

const VIRTIO_INPUT_CFG_ID_NAME: u8 = 0x01;
const VIRTIO_INPUT_CFG_ID_DEVIDS: u8 = 0x03;
const VIRTIO_INPUT_CFG_EV_BITS: u8 = 0x11;
const VIRTIO_INPUT_CFG_SIZE: usize = 128;

const EV_SYN: u8 = 0x00;
const EV_KEY: u8 = 0x01;
const EV_REL: u8 = 0x02;
const EV_ABS: u8 = 0x03;
const EV_MSC: u8 = 0x04;
const EV_SW: u8 = 0x05;

const SYN_REPORT: u8 = 0x00;

#[repr(C, packed)]
#[derive(Copy, Clone, Debug)]
pub(crate) struct InputConfig {
    select: u8,
    subsel: u8,
    size: u8,
    reserved: [u8; 5],
    val: [u8; VIRTIO_INPUT_CFG_SIZE],
}
unsafe impl ByteValued for InputConfig {}

// If deriving the 'Default' trait, an array is limited with a maximum size of 32 bytes,
// thus it cannot meet the length VIRTIO_INPUT_CFG_SIZE (128) for the 'val' array.
// Implement Default trait to accommodate array 'val'.
impl Default for InputConfig {
    fn default() -> InputConfig {
        InputConfig {
            select: 0,
            subsel: 0,
            size: 0,
            reserved: [0; 5],
            val: [0; VIRTIO_INPUT_CFG_SIZE],
        }
    }
}

#[repr(C, packed)]
#[derive(Copy, Clone, Debug, Default)]
pub(crate) struct InputEvent {
    ev_type: u16,
    code: u16,
    value: u32,
}
unsafe impl ByteValued for InputEvent {}

#[derive(Copy, Clone, Debug, Default)]
#[repr(C, packed)]
pub struct VirtioInput {}

pub struct Input {
    pub(crate) queues: Vec<VirtQueue>,
    pub(crate) queue_events: Vec<EventFd>,
    pub(crate) avail_features: u64,
    pub(crate) acked_features: u64,
    pub(crate) interrupt_status: Arc<AtomicUsize>,
    pub(crate) interrupt_evt: EventFd,
    pub(crate) activate_evt: EventFd,
    pub(crate) device_state: DeviceState,
    select: u8,
    subsel: u8,
    ev_dev: Device,
    ev_list: VecDeque<InputEvent>,
    intc: Option<IrqChip>,
    irq_line: Option<u32>,
}

impl Input {
    pub(crate) fn with_queues(queues: Vec<VirtQueue>) -> super::Result<Input> {
        let mut queue_events = Vec::new();
        for _ in 0..queues.len() {
            queue_events
                .push(EventFd::new(utils::eventfd::EFD_NONBLOCK).map_err(InputError::EventFd)?);
        }

        Ok(Input {
            queues,
            queue_events,
            avail_features: AVAIL_FEATURES,
            acked_features: 0,
            interrupt_status: Arc::new(AtomicUsize::new(0)),
            interrupt_evt: EventFd::new(utils::eventfd::EFD_NONBLOCK)
                .map_err(InputError::EventFd)?,
            activate_evt: EventFd::new(utils::eventfd::EFD_NONBLOCK)
                .map_err(InputError::EventFd)?,
            device_state: DeviceState::Inactive,
            select: 0,
            subsel: 0,
            ev_dev: Device::open("/dev/input/event3").unwrap(),
            ev_list: VecDeque::new(),
            intc: None,
            irq_line: None,
        })
    }

    pub fn new() -> super::Result<Input> {
        let queues: Vec<VirtQueue> = defs::QUEUE_SIZES
            .iter()
            .map(|&max_size| VirtQueue::new(max_size))
            .collect();
        Self::with_queues(queues)
    }

    pub fn id(&self) -> &str {
        defs::INPUT_DEV_ID
    }

    pub fn set_intc(&mut self, intc: IrqChip) {
        self.intc = Some(intc);
    }

    pub fn signal_used_queue(&self) -> result::Result<(), DeviceError> {
        debug!("input: raising IRQ");
        self.interrupt_status
            .fetch_or(VIRTIO_MMIO_INT_VRING as usize, Ordering::SeqCst);
        if let Some(intc) = &self.intc {
            intc.lock()
                .unwrap()
                .set_irq(self.irq_line, Some(&self.interrupt_evt))?;
        }
        Ok(())
    }

    fn process_event(&mut self) -> bool {
        let mem = match self.device_state {
            DeviceState::Activated(ref mem) => mem,
            // This should never happen, it's been already validated in the event handler.
            DeviceState::Inactive => unreachable!(),
        };

        let last_sync_index = self
            .ev_list
            .iter()
            .rposition(|event| event.ev_type == EV_SYN as u16 && event.code == SYN_REPORT as u16)
            .unwrap_or(0);

        if last_sync_index == 0 {
            log::warn!("No available events on the list!");
            return true;
        }

        let mut have_used = false;
        let mut index = 0;

        while index <= last_sync_index {
            let event = self.ev_list.get(index).unwrap();
            index += 1;

            if let Some(head) = self.queues[REQ_INDEX].pop(mem) {
                let index = head.index;
                let mut written = 0;
                for desc in head.into_iter() {
                    if let Err(e) = mem.write_obj(*event, desc.addr) {
                        error!("Failed to write slice: {:?}", e);
                        self.queues[REQ_INDEX].go_to_previous_position();
                        break;
                    }
                    written += desc.len;
                }

                have_used = true;
                if let Err(e) = self.queues[REQ_INDEX].add_used(mem, index, written) {
                    error!("failed to add used elements to the queue: {:?}", e);
                }
            } else {
                // Now cannot get available descriptor, which means the host cannot process
                // event data in time and overrun happens in the backend. In this case,
                // we simply drop the incomping input event and notify guest for handling
                // events. At the end, it returns Ok(false) so can avoid exiting the thread loop.
                self.ev_list.clear();

                return true;
            }
        }

        // Sent the events [0..last_sync_index] to vring and remove them from the list.
        // The range end parameter is an exclusive value, so use 'last_sync_index + 1'.
        self.ev_list.drain(0..last_sync_index + 1);
        have_used
    }

    pub fn process_req(&mut self) -> bool {
        debug!("input: process_req()");
        let events = self.ev_dev.fetch_events().unwrap();

        for event in events {
            let ev_raw_data = InputEvent {
                ev_type: event.event_type().0,
                code: event.code(),
                value: event.value() as u32,
            };
            self.ev_list.push_back(ev_raw_data);
        }

        self.process_event()
    }

    pub fn read_event_config(&self) -> Result<InputConfig> {
        let mut cfg: [u8; VIRTIO_INPUT_CFG_SIZE] = [0; VIRTIO_INPUT_CFG_SIZE];

        let func: unsafe fn(nix::libc::c_int, &mut [u8]) -> nix::Result<libc::c_int> =
            match self.subsel {
                EV_KEY => eviocgbit_key,
                EV_ABS => eviocgbit_absolute,
                EV_REL => eviocgbit_relative,
                EV_MSC => eviocgbit_misc,
                EV_SW => eviocgbit_switch,
                _ => {
                    return Err(InputError::HandleEventUnknownEvent);
                }
            };

        // SAFETY: Safe as the file is a valid event device, the kernel will only
        // update the correct amount of memory in func.
        if unsafe { func(self.ev_dev.as_raw_fd(), &mut cfg) }.is_err() {
            return Err(InputError::UnexpectedInputDeviceError);
        }

        let mut size: u8 = 0;
        for (index, val) in cfg.iter().enumerate() {
            if *val != 0 {
                size = (index + 1) as u8;
            }
        }

        Ok(InputConfig {
            select: self.select,
            subsel: self.subsel,
            size,
            reserved: [0; 5],
            val: cfg,
        })
    }

    pub fn read_name_config(&self) -> Result<InputConfig> {
        let mut name: [u8; VIRTIO_INPUT_CFG_SIZE] = [0; VIRTIO_INPUT_CFG_SIZE];

        // SAFETY: Safe as the file is a valid event device, the kernel will only
        // update the correct amount of memory in func.
        match unsafe { eviocgname(self.ev_dev.as_raw_fd(), name.as_mut_slice()) } {
            Ok(len) if len as usize > name.len() => {
                return Err(InputError::UnexpectedInputDeviceError);
            }
            Ok(len) if len <= 1 => {
                return Err(InputError::UnexpectedInputDeviceError);
            }
            Err(_) => {
                return Err(InputError::UnexpectedInputDeviceError);
            }
            _ => (),
        }

        let size = String::from_utf8(name.to_vec()).unwrap().len();

        Ok(InputConfig {
            select: self.select,
            subsel: 0,
            size: size as u8,
            reserved: [0; 5],
            val: name,
        })
    }

    pub fn read_id_config(&self) -> Result<InputConfig> {
        let input_id = self.ev_dev.input_id();

        let mut dev_id = [
            input_id.bus_type().0.as_slice(),
            input_id.vendor().as_slice(),
            input_id.product().as_slice(),
            input_id.version().as_slice(),
        ]
        .concat();

        dev_id.resize(VIRTIO_INPUT_CFG_SIZE, 0);

        Ok(InputConfig {
            select: VIRTIO_INPUT_CFG_ID_DEVIDS,
            subsel: 0,
            size: VIRTIO_INPUT_CFG_SIZE as u8,
            reserved: [0; 5],
            val: dev_id.try_into().unwrap(),
        })
    }
}

impl VirtioDevice for Input {
    fn avail_features(&self) -> u64 {
        self.avail_features
    }

    fn acked_features(&self) -> u64 {
        self.acked_features
    }

    fn set_acked_features(&mut self, acked_features: u64) {
        self.acked_features = acked_features
    }

    fn device_type(&self) -> u32 {
        uapi::VIRTIO_ID_INPUT
    }

    fn queues(&self) -> &[VirtQueue] {
        &self.queues
    }

    fn queues_mut(&mut self) -> &mut [VirtQueue] {
        &mut self.queues
    }

    fn queue_events(&self) -> &[EventFd] {
        &self.queue_events
    }

    fn interrupt_evt(&self) -> &EventFd {
        &self.interrupt_evt
    }

    fn interrupt_status(&self) -> Arc<AtomicUsize> {
        self.interrupt_status.clone()
    }

    fn set_irq_line(&mut self, irq: u32) {
        debug!("SET_IRQ_LINE (INPUT)={}", irq);
        self.irq_line = Some(irq);
    }

    fn read_config(&self, offset: u64, data: &mut [u8]) {
        error!("input: invalid request to read config space");
        let cfg = match self.select {
            VIRTIO_INPUT_CFG_ID_NAME => self.read_name_config(),
            VIRTIO_INPUT_CFG_ID_DEVIDS => self.read_id_config(),
            VIRTIO_INPUT_CFG_EV_BITS => self.read_event_config(),
            _ => unreachable!("invalid input config request"),
        };

        let val = match cfg {
            Ok(v) => v.as_slice().to_vec(),
            _ => vec![0; data.len() as usize],
        };

        let mut result: Vec<_> = val
            .as_slice()
            .iter()
            .skip(offset as usize)
            .take(data.len() as usize)
            .copied()
            .collect();

        result.resize(data.len() as usize, 0);
        data.copy_from_slice(&result);
    }

    fn write_config(&mut self, _offset: u64, data: &[u8]) {
        self.select = data[0];
        self.subsel = data[1];
    }

    fn activate(&mut self, mem: GuestMemoryMmap) -> ActivateResult {
        if self.queues.len() != defs::NUM_QUEUES {
            error!(
                "Cannot perform activate. Expected {} queue(s), got {}",
                defs::NUM_QUEUES,
                self.queues.len()
            );
            return Err(ActivateError::BadActivate);
        }

        if self.activate_evt.write(1).is_err() {
            error!("Cannot write to activate_evt",);
            return Err(ActivateError::BadActivate);
        }

        self.device_state = DeviceState::Activated(mem);

        Ok(())
    }

    fn is_activated(&self) -> bool {
        match self.device_state {
            DeviceState::Inactive => false,
            DeviceState::Activated(_) => true,
        }
    }

    fn reset(&mut self) -> bool {
        // Strictly speaking, we should unsubscribe the queue events resubscribe
        // the activate eventfd and deactivate the device, but we don't support
        // any scenario in which neither GuestMemory nor the queue events would
        // change, so let's avoid doing any unnecessary work.
        true
    }
}
