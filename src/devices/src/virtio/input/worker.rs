use crate::legacy::IrqChip;
use crate::virtio::descriptor_utils::{Reader, Writer};
use crate::Error as DeviceError;

use super::super::{Queue, VIRTIO_MMIO_INT_VRING};

use evdev::Device;
use std::collections::VecDeque;
use std::io::{self, Write};
use std::os::fd::AsRawFd;
use std::result;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;
use std::thread;
use utils::epoll::{ControlOperation, Epoll, EpollEvent, EventSet};
use utils::eventfd::EventFd;
use virtio_bindings::virtio_blk::*;
use vm_memory::{ByteValued, Bytes, GuestMemoryMmap};

const EV_SYN: u8 = 0x00;
const EV_KEY: u8 = 0x01;
const EV_REL: u8 = 0x02;
const EV_ABS: u8 = 0x03;
const EV_MSC: u8 = 0x04;
const EV_SW: u8 = 0x05;

const SYN_REPORT: u8 = 0x00;

#[repr(C, packed)]
#[derive(Copy, Clone, Debug, Default)]
pub(crate) struct InputEvent {
    ev_type: u16,
    code: u16,
    value: u32,
}
unsafe impl ByteValued for InputEvent {}

pub struct InputWorker {
    queue: Queue,
    interrupt_status: Arc<AtomicUsize>,
    interrupt_evt: EventFd,
    intc: Option<IrqChip>,
    irq_line: Option<u32>,

    mem: GuestMemoryMmap,
    ev_dev: Device,
    ev_list: VecDeque<InputEvent>,
    stop_fd: EventFd,
}

impl InputWorker {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        queue: Queue,
        interrupt_status: Arc<AtomicUsize>,
        interrupt_evt: EventFd,
        intc: Option<IrqChip>,
        irq_line: Option<u32>,
        mem: GuestMemoryMmap,
        stop_fd: EventFd,
    ) -> Self {
        Self {
            queue,
            interrupt_status,
            interrupt_evt,
            intc,
            irq_line,

            mem,
            ev_dev: Device::open("/dev/input/event3").unwrap(),
            ev_list: VecDeque::new(),
            stop_fd,
        }
    }

    pub fn run(self) -> thread::JoinHandle<()> {
        thread::Builder::new()
            .name("block worker".into())
            .spawn(|| self.work())
            .unwrap()
    }

    fn work(mut self) {
        loop {
            let events = self.ev_dev.fetch_events().unwrap();

            debug!("input: after fetch events()");
            for event in events {
                debug!("input: event");
                let ev_raw_data = InputEvent {
                    ev_type: event.event_type().0,
                    code: event.code(),
                    value: event.value() as u32,
                };
                self.ev_list.push_back(ev_raw_data);
            }

            if self.process_events() {
                self.signal_used_queue();
            }
        }
    }

    fn process_events(&mut self) -> bool {
        debug!("input: process_event()");

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
            debug!("input: index={index}");
            let event = self.ev_list.get(index).unwrap();
            index += 1;

            if let Some(head) = self.queue.pop(&self.mem) {
                debug!("input: REQ_INDEX");
                let index = head.index;
                let mut written = 0;
                for desc in head.into_iter() {
                    if let Err(e) = self.mem.write_obj(*event, desc.addr) {
                        error!("Failed to write slice: {:?}", e);
                        self.queue.go_to_previous_position();
                        break;
                    }
                    written += desc.len;
                }

                have_used = true;
                if let Err(e) = self.queue.add_used(&self.mem, index, written) {
                    error!("failed to add used elements to the queue: {:?}", e);
                }
            } else {
                debug!("input: no desc");
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

    fn signal_used_queue(&self) -> result::Result<(), DeviceError> {
        self.interrupt_status
            .fetch_or(VIRTIO_MMIO_INT_VRING as usize, Ordering::SeqCst);
        if let Some(intc) = &self.intc {
            intc.lock()
                .unwrap()
                .set_irq(self.irq_line, Some(&self.interrupt_evt))?;
        }
        Ok(())
    }
}
