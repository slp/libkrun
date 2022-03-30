use std::os::unix::io::{AsRawFd, RawFd};
use std::sync::atomic::{AtomicU32, AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};
use std::thread;

use super::super::Queue as VirtQueue;
use super::super::VIRTIO_MMIO_INT_VRING;
use super::muxer::ProxyMap;
use super::muxer_rxq::MuxerRxQ;
use super::proxy::{ProxyStatus, ProxyUpdate};
use super::tcp::TcpProxy;

use rand::{rngs::ThreadRng, thread_rng, Rng};
use utils::epoll::{ControlOperation, Epoll, EpollEvent, EventSet};
use utils::eventfd::EventFd;
use vm_memory::GuestMemoryMmap;

pub struct MuxerThread {
    cid: u64,
    pub epoll: Epoll,
    rxq_stream: Arc<Mutex<MuxerRxQ>>,
    rxq_dgram: Arc<Mutex<MuxerRxQ>>,
    proxy_map: ProxyMap,
    mem: GuestMemoryMmap,
    queue_rx: Arc<Mutex<VirtQueue>>,
    queue_dr: Arc<Mutex<VirtQueue>>,
    interrupt_evt: EventFd,
    interrupt_status: Arc<AtomicUsize>,
}

impl MuxerThread {
    pub fn new(
        cid: u64,
        epoll: Epoll,
        rxq_stream: Arc<Mutex<MuxerRxQ>>,
        rxq_dgram: Arc<Mutex<MuxerRxQ>>,
        proxy_map: ProxyMap,
        mem: GuestMemoryMmap,
        queue_rx: Arc<Mutex<VirtQueue>>,
        queue_dr: Arc<Mutex<VirtQueue>>,
        interrupt_evt: EventFd,
        interrupt_status: Arc<AtomicUsize>,
    ) -> Self {
        MuxerThread {
            cid,
            epoll,
            rxq_stream,
            rxq_dgram,
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

    fn process_proxy_update(&self, id: u64, update: ProxyUpdate, thread_rng: &mut ThreadRng) {
        if let Some(polling) = update.polling {
            self.update_polling(polling.0, polling.1, polling.2);
        }

        if update.remove_proxy {
            self.proxy_map.write().unwrap().remove(&id);
        }

        let mut should_signal = update.signal_queue;

        if let Some((peer_port, accept_fd)) = update.new_proxy {
            let local_port: u32 = thread_rng.gen_range(1024..u32::MAX);
            let new_id: u64 = (peer_port as u64) << 32 | local_port as u64;
            let new_proxy = TcpProxy::new_reverse(
                new_id,
                self.cid,
                id,
                local_port,
                peer_port,
                accept_fd,
                self.rxq_stream.clone(),
                self.rxq_dgram.clone(),
            );
            self.proxy_map
                .write()
                .unwrap()
                .insert(new_id, Mutex::new(Box::new(new_proxy)));
            self.proxy_map
                .read()
                .unwrap()
                .get(&new_id)
                .map(|proxy_lock| {
                    let mut proxy = proxy_lock.lock().unwrap();
                    proxy.push_op_request(&mut self.queue_rx.lock().unwrap(), &self.mem);
                });
            should_signal = true;
        }

        if should_signal {
            self.interrupt_status
                .fetch_or(VIRTIO_MMIO_INT_VRING as usize, Ordering::SeqCst);
            self.interrupt_evt.write(1).map_err(|e| {
                error!("Failed to signal used queue: {:?}", e);
            });
        }
    }

    fn work(self) {
        let mut thread_rng = thread_rng();
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

                        let update = self.proxy_map.read().unwrap().get(&id).map(|proxy_lock| {
                            let mut proxy = proxy_lock.lock().unwrap();
                            proxy.process_event(
                                evset,
                                &mut self.queue_rx.lock().unwrap(),
                                &mut self.queue_dr.lock().unwrap(),
                                &self.mem,
                            )
                        });

                        if let Some(update) = update {
                            self.process_proxy_update(id, update, &mut thread_rng);
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
