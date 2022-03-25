use std::os::unix::io::{AsRawFd, RawFd};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};
use std::thread;

use super::super::Queue as VirtQueue;
use super::super::VIRTIO_MMIO_INT_VRING;
use super::muxer::ProxyMap;
use super::muxer_rxq::MuxerRxQ;
use super::proxy::{ProxyStatus, ProxyUpdate};

use utils::epoll::{ControlOperation, Epoll, EpollEvent, EventSet};
use utils::eventfd::EventFd;
use vm_memory::GuestMemoryMmap;

pub struct MuxerThread {
    pub epoll: Epoll,
    rxq: Arc<Mutex<MuxerRxQ>>,
    proxy_map: ProxyMap,
    mem: GuestMemoryMmap,
    queue_rx: Arc<Mutex<VirtQueue>>,
    queue_dr: Arc<Mutex<VirtQueue>>,
    interrupt_evt: EventFd,
    interrupt_status: Arc<AtomicUsize>,
}

impl MuxerThread {
    pub fn new(
        epoll: Epoll,
        rxq: Arc<Mutex<MuxerRxQ>>,
        proxy_map: ProxyMap,
        mem: GuestMemoryMmap,
        queue_rx: Arc<Mutex<VirtQueue>>,
        queue_dr: Arc<Mutex<VirtQueue>>,
        interrupt_evt: EventFd,
        interrupt_status: Arc<AtomicUsize>,
    ) -> Self {
        MuxerThread {
            epoll,
            rxq,
            proxy_map,
            mem,
            queue_rx,
            queue_dr,
            interrupt_evt,
            interrupt_status,
        }
    }

    pub fn run(self) {
        thread::spawn(|| self.work());
    }

    pub fn update_polling(&self, id: u64, fd: RawFd, evset: EventSet) {
        debug!("update_polling id={} fd={:?}", id, fd);
        self.epoll
            .ctl(ControlOperation::Delete, fd, &EpollEvent::default())
            .unwrap();
        if !evset.is_empty() {
            self.epoll
                .ctl(
                    ControlOperation::Add,
                    fd,
                    &EpollEvent::new(evset, id as u64),
                )
                .unwrap();
        }
    }

    fn process_proxy_update(&self, id: u64, update: ProxyUpdate) -> bool {
        if update.signal_queue {
            self.interrupt_status
                .fetch_or(VIRTIO_MMIO_INT_VRING as usize, Ordering::SeqCst);
            self.interrupt_evt.write(1).map_err(|e| {
                error!("Failed to signal used queue: {:?}", e);
            });
        }

        if let Some(polling) = update.polling {
            self.update_polling(polling.0, polling.1, polling.2);
        }

        update.remove_proxy
    }

    fn work(self) {
        loop {
            let mut epoll_events = vec![EpollEvent::new(EventSet::empty(), 0); 32];
            match self
                .epoll
                .wait(epoll_events.len(), -1, epoll_events.as_mut_slice())
            {
                Ok(ev_cnt) => {
                    for ev in &epoll_events[0..ev_cnt] {
                        debug!("Event: ev.data={} ev.fd={}", ev.data(), ev.fd());
                        let evset = EventSet::from_bits(ev.events).unwrap();
                        let id = ev.data();

                        let remove_proxy = self
                            .proxy_map
                            .read()
                            .unwrap()
                            .get(&id)
                            .map(|proxy_lock| {
                                let mut proxy = proxy_lock.lock().unwrap();
                                let update = proxy.process_event(
                                    evset,
                                    &mut self.queue_rx.lock().unwrap(),
                                    &mut self.queue_dr.lock().unwrap(),
                                    &self.mem,
                                );
                                self.process_proxy_update(id, update)
                            })
                            .map_or(false, |r| r);

                        if remove_proxy {
                            self.proxy_map.write().unwrap().remove(&id);
                        }
                    }
                }
                Err(e) => {
                    debug!("vsock: failed to consume muxer epoll event: {}", e);
                }
            }
        }
    }
}
