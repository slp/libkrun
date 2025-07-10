use std::os::unix::io::AsRawFd;

use polly::event_manager::{EventManager, Subscriber};
use utils::epoll::{EpollEvent, EventSet};

use super::device::{Input, REQ_INDEX};
use crate::virtio::device::VirtioDevice;

impl Input {
    fn handle_activate_event(&self, event_manager: &mut EventManager) {
        debug!("input: activate event");
        if let Err(e) = self.activate_evt.read() {
            error!("Failed to consume input activate event: {:?}", e);
        }

        // The subscriber must exist as we previously registered activate_evt via
        // `interest_list()`.
        let self_subscriber = event_manager
            .subscriber(self.activate_evt.as_raw_fd())
            .unwrap();

        event_manager
            .unregister(self.activate_evt.as_raw_fd())
            .unwrap_or_else(|e| {
                error!("Failed to unregister input activate evt: {:?}", e);
            })
    }
}

impl Subscriber for Input {
    fn process(&mut self, event: &EpollEvent, event_manager: &mut EventManager) {
        let source = event.fd();
        let activate_evt = self.activate_evt.as_raw_fd();

        if self.is_activated() {
            match source {
                _ if source == activate_evt => {
                    self.handle_activate_event(event_manager);
                }
                _ => warn!("Unexpected input event received: {:?}", source),
            }
        } else {
            warn!(
                "input: The device is not yet activated. Spurious event received: {:?}",
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
