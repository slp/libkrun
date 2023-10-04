use std::os::unix::io::AsRawFd;

use polly::event_manager::{EventManager, Subscriber};
use utils::epoll::{EpollEvent, EventSet};

use super::device::{Snd, CTL_INDEX, EVT_INDEX, RXQ_INDEX, TXQ_INDEX};
use crate::virtio::device::VirtioDevice;

impl Snd {
    pub(crate) fn handle_ctl_event(&mut self, event: &EpollEvent) {
        debug!("snd: control queue event");

        let event_set = event.event_set();
        if event_set != EventSet::IN {
            warn!("snd: control queue unexpected event {:?}", event_set);
            return;
        }

        if let Err(e) = self.queue_events[CTL_INDEX].read() {
            error!("Failed to read control queue event: {:?}", e);
        } else if self.process_ctl_queue() {
            self.signal_used_queue().unwrap();
        }
    }

    pub(crate) fn handle_evt_event(&mut self, event: &EpollEvent) {
        debug!("snd: evt queue event");

        let event_set = event.event_set();
        if event_set != EventSet::IN {
            warn!("snd: evt queue unexpected event {:?}", event_set);
            return;
        }

        if let Err(e) = self.queue_events[EVT_INDEX].read() {
            error!("Failed to read evt queue event: {:?}", e);
        } else if self.process_evt() {
            self.signal_used_queue().unwrap();
        }
    }

    pub(crate) fn handle_txq_event(&mut self, event: &EpollEvent) {
        debug!("snd: txq queue event");

        let event_set = event.event_set();
        if event_set != EventSet::IN {
            warn!("snd: txq queue unexpected event {:?}", event_set);
            return;
        }

        if let Err(e) = self.queue_events[TXQ_INDEX].read() {
            error!("Failed to read txq queue event: {:?}", e);
        } else if self.process_txq_queue() {
            self.signal_used_queue().unwrap();
        }
    }

    pub(crate) fn handle_rxq_event(&mut self, event: &EpollEvent) {
        debug!("snd: rxq queue event");

        let event_set = event.event_set();
        if event_set != EventSet::IN {
            warn!("snd: rxq queue unexpected event {:?}", event_set);
            return;
        }

        if let Err(e) = self.queue_events[RXQ_INDEX].read() {
            error!("Failed to read rxq queue event: {:?}", e);
        } else if self.process_rxq() {
            self.signal_used_queue().unwrap();
        }
    }

    fn handle_activate_event(&self, event_manager: &mut EventManager) {
        debug!("snd: activate event");
        if let Err(e) = self.activate_evt.read() {
            error!("Failed to consume snd activate event: {:?}", e);
        }

        // The subscriber must exist as we previously registered activate_evt via
        // `interest_list()`.
        let self_subscriber = event_manager
            .subscriber(self.activate_evt.as_raw_fd())
            .unwrap();

        event_manager
            .register(
                self.queue_events[CTL_INDEX].as_raw_fd(),
                EpollEvent::new(
                    EventSet::IN,
                    self.queue_events[CTL_INDEX].as_raw_fd() as u64,
                ),
                self_subscriber.clone(),
            )
            .unwrap_or_else(|e| {
                error!("Failed to register snd ctl with event manager: {:?}", e);
            });

        event_manager
            .register(
                self.queue_events[EVT_INDEX].as_raw_fd(),
                EpollEvent::new(
                    EventSet::IN,
                    self.queue_events[EVT_INDEX].as_raw_fd() as u64,
                ),
                self_subscriber.clone(),
            )
            .unwrap_or_else(|e| {
                error!("Failed to register snd evt with event manager: {:?}", e);
            });

        event_manager
            .register(
                self.queue_events[TXQ_INDEX].as_raw_fd(),
                EpollEvent::new(
                    EventSet::IN,
                    self.queue_events[TXQ_INDEX].as_raw_fd() as u64,
                ),
                self_subscriber.clone(),
            )
            .unwrap_or_else(|e| {
                error!("Failed to register snd txq with event manager: {:?}", e);
            });

        event_manager
            .register(
                self.queue_events[RXQ_INDEX].as_raw_fd(),
                EpollEvent::new(
                    EventSet::IN,
                    self.queue_events[RXQ_INDEX].as_raw_fd() as u64,
                ),
                self_subscriber.clone(),
            )
            .unwrap_or_else(|e| {
                error!("Failed to register snd rxq with event manager: {:?}", e);
            });

        event_manager
            .unregister(self.activate_evt.as_raw_fd())
            .unwrap_or_else(|e| {
                error!("Failed to unregister snd activate evt: {:?}", e);
            })
    }
}

impl Subscriber for Snd {
    fn process(&mut self, event: &EpollEvent, event_manager: &mut EventManager) {
        let source = event.fd();
        let ctl = self.queue_events[CTL_INDEX].as_raw_fd();
        let evt = self.queue_events[EVT_INDEX].as_raw_fd();
        let txq = self.queue_events[TXQ_INDEX].as_raw_fd();
        let rxq = self.queue_events[RXQ_INDEX].as_raw_fd();
        let activate_evt = self.activate_evt.as_raw_fd();

        if self.is_activated() {
            match source {
                _ if source == ctl => self.handle_ctl_event(event),
                _ if source == evt => self.handle_evt_event(event),
                _ if source == txq => self.handle_txq_event(event),
                _ if source == rxq => self.handle_rxq_event(event),
                _ if source == activate_evt => {
                    self.handle_activate_event(event_manager);
                }
                _ => warn!("Unexpected snd event received: {:?}", source),
            }
        } else {
            warn!(
                "snd: The device is not yet activated. Spurious event received: {:?}",
                source
            );
        }
    }

    fn interest_list(&self) -> Vec<EpollEvent> {
        vec![EpollEvent::new(
            EventSet::IN,
            self.activate_evt.as_raw_fd() as u64,
        )]
    }
}
