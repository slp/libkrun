use std::collections::VecDeque;
use std::os::fd::AsRawFd;
use std::result;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;
use std::thread::JoinHandle;

use evdev::Device;
use libc::EFD_NONBLOCK;
use nix::ioctl_read_buf;
use utils::eventfd::EventFd;
use virtio_bindings::virtio_blk::virtio_blk_outhdr;
use virtio_bindings::virtio_input;
use vm_memory::{ByteValued, Bytes, GuestMemoryMmap};

use super::super::{
    ActivateError, ActivateResult, DeviceState, Queue as VirtQueue, VirtioDevice,
    VIRTIO_MMIO_INT_VRING,
};
use super::worker::InputWorker;
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

#[repr(C, packed)]
#[derive(Copy, Clone, Debug)]
struct virtio_input_absinfo {
    min: u32,
    max: u32,
    fuzz: u32,
    flat: u32,
    res: u32,
}

const VIRTIO_INPUT_CFG_ID_NAME: u8 = 0x01;
const VIRTIO_INPUT_CFG_ID_DEVIDS: u8 = 0x03;
const VIRTIO_INPUT_CFG_EV_BITS: u8 = 0x11;
const VIRTIO_INPUT_CFG_ABS_INFO: u8 = 0x12;
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
    intc: Option<IrqChip>,
    irq_line: Option<u32>,
    pub(crate) ev_dev: Device,
    worker_thread: Option<JoinHandle<()>>,
    worker_stopfd: EventFd,
}

impl Input {
    pub(crate) fn with_queues(queues: Vec<VirtQueue>) -> super::Result<Input> {
        debug!("input: with_queues");
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
            intc: None,
            irq_line: None,
            ev_dev: Device::open("/dev/input/event3").unwrap(),
            worker_thread: None,
            worker_stopfd: EventFd::new(utils::eventfd::EFD_NONBLOCK)
                .map_err(InputError::EventFd)?,
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

    pub fn read_abs_config(&self) -> Result<InputConfig> {
        for (code, info) in self.ev_dev.get_absinfo().unwrap().into_iter() {
            if code.0 == self.subsel as u16 {
                info!("absinfo found");
                let vinfo = virtio_input_absinfo {
                    min: info.minimum() as u32,
                    max: info.maximum() as u32,
                    fuzz: info.fuzz() as u32,
                    flat: info.flat() as u32,
                    res: info.resolution() as u32,
                };

                let mut val: [u8; VIRTIO_INPUT_CFG_SIZE] = [0; VIRTIO_INPUT_CFG_SIZE];

                val[..std::mem::size_of::<virtio_input_absinfo>()].copy_from_slice(unsafe {
                    std::slice::from_raw_parts(
                        &vinfo as *const _ as *const u8,
                        std::mem::size_of::<virtio_input_absinfo>(),
                    )
                });

                return Ok(InputConfig {
                    select: self.select,
                    subsel: self.subsel,
                    size: std::mem::size_of::<virtio_input_absinfo>() as u8,
                    reserved: [0; 5],
                    val,
                });
            }
        }

        Err(InputError::HandleEventUnknownEvent)
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
            VIRTIO_INPUT_CFG_ABS_INFO => self.read_abs_config(),
            _ => {
                error!("invalid input config request: {}", self.select);
                return;
            }
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

    fn write_config(&mut self, offset: u64, data: &[u8]) {
        debug!("input: write_config: offset={offset}");
        if offset == 0 {
            self.select = data[0];
        } else {
            self.subsel = data[0];
        }
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

        let worker = InputWorker::new(
            self.queues[0].clone(),
            self.interrupt_status.clone(),
            self.interrupt_evt.try_clone().unwrap(),
            self.intc.clone(),
            self.irq_line,
            mem.clone(),
            self.worker_stopfd.try_clone().unwrap(),
        );
        self.worker_thread = Some(worker.run());

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
