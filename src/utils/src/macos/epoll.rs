// Copyright 2020 Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use std::io;
use std::ops::Deref;
use std::os::unix::io::{AsRawFd, RawFd};
use std::time::Duration;

use kqueue::{EventData, EventFilter, FilterFlag, Ident, Watcher};

use crate::syscall::SyscallReturnCode;

/// Wrapper over EPOLL_CTL_* operations that can be performed on a file descriptor.
#[repr(i32)]
pub enum ControlOperation {
    /// Add a file descriptor to the interest list.
    Add,
    /// Change the settings associated with a file descriptor that is
    /// already in the interest list.
    Modify,
    /// Remove a file descriptor from the interest list.
    Delete,
}

bitflags! {
    /// The type of events we can monitor a file descriptor for.
    pub struct EventSet: u32 {
        /// The associated file descriptor is available for read operations.
        const IN = 0b00000001;
        /// The associated file descriptor is available for write operations.
        const OUT = 0b00000010;
    }
}

/// Wrapper over 'libc::epoll_event'.
///
// We are using `transparent` here to be super sure that this struct and its fields
// have the same alignment as those from the `epoll_event` struct from C.
#[derive(Clone)]
pub struct EpollEvent {
    events: u32,
    u64: u64,
}

impl Default for EpollEvent {
    fn default() -> Self {
        EpollEvent {
            events: 0u32,
            u64: 0u64,
        }
    }
}

impl EpollEvent {
    /// Create a new epoll_event instance with the following fields: `events`, which contains
    /// an event mask and `data` which represents a user data variable. `data` field can be
    /// a fd on which we want to monitor the events specified by `events`.
    pub fn new(events: EventSet, data: u64) -> Self {
        EpollEvent {
            events: events.bits(),
            u64: data,
        }
    }

    /// Returns the `events` from `libc::epoll_event`.
    pub fn events(&self) -> u32 {
        self.events
    }

    /// Returns the `EventSet` corresponding to `epoll_event.events`.
    ///
    /// # Panics
    ///
    /// Panics if `libc::epoll_event` contains invalid events.
    pub fn event_set(&self) -> EventSet {
        // This unwrap is safe because `epoll_events` can only be user created or
        // initialized by the kernel. We trust the kernel to only send us valid
        // events. The user can only initialize `epoll_events` using valid events.
        EventSet::from_bits(self.events()).unwrap()
    }

    /// Returns the `data` from the `libc::epoll_event`.
    pub fn data(&self) -> u64 {
        self.u64
    }

    /// Converts the `libc::epoll_event` data to a RawFd.
    ///
    /// This conversion is lossy when the data does not correspond to a RawFd
    /// (data does not fit in a i32).
    pub fn fd(&self) -> RawFd {
        self.u64 as i32
    }
}

/// Wrapper over epoll functionality.
#[derive(Debug)]
pub struct Epoll {
    watcher: Watcher,
    enabled: bool,
}

impl Epoll {
    /// Create a new epoll file descriptor.
    pub fn new() -> io::Result<Self> {
        let watcher = Watcher::new()?;
        Ok(Epoll {
            watcher,
            enabled: false,
        })
    }

    /// Wrapper for `libc::epoll_ctl`.
    ///
    /// This can be used for adding, modifying or removing a file descriptor in the
    /// interest list of the epoll instance.
    ///
    /// # Arguments
    ///
    /// * `operation` refers to the action to be performed on the file descriptor.
    /// * `fd` is the file descriptor on which we want to perform `operation`.
    /// * `event` refers to the `epoll_event` instance that is linked to `fd`.
    pub fn ctl(
        &mut self,
        operation: ControlOperation,
        fd: RawFd,
        event: &EpollEvent,
    ) -> io::Result<()> {
        let eset = EventSet::from_bits(event.events).unwrap();

        match operation {
            ControlOperation::Add | ControlOperation::Modify => {
                if eset.contains(EventSet::IN) {
                    self.watcher
                        .add_fd(fd, EventFilter::EVFILT_READ, FilterFlag::empty())?;
                }
                if eset.contains(EventSet::OUT) {
                    self.watcher
                        .add_fd(fd, EventFilter::EVFILT_WRITE, FilterFlag::empty())?;
                }
            }
            ControlOperation::Delete => {
                if eset.contains(EventSet::IN) {
                    self.watcher.remove_fd(fd, EventFilter::EVFILT_READ)?;
                }
                if eset.contains(EventSet::OUT) {
                    self.watcher.remove_fd(fd, EventFilter::EVFILT_WRITE)?;
                }
            }
        }
        self.enabled = false;
        Ok(())
    }

    /// Wrapper for `libc::epoll_wait`.
    /// Returns the number of file descriptors in the interest list that became ready
    /// for I/O or `errno` if an error occurred.
    ///
    /// # Arguments
    ///
    /// * `max_events` is the maximum number of events that we want to be returned in
    /// `events` buffer.
    /// * `timeout` specifies for how long the `epoll_wait` system call will block
    /// (measured in milliseconds).
    /// * `events` points to a memory area that will be used for storing the events
    /// returned by `epoll_wait()` call.
    pub fn wait(
        &mut self,
        max_events: usize,
        timeout: i32,
        events: &mut [EpollEvent],
    ) -> io::Result<usize> {
        if !self.enabled {
            self.watcher.watch()?;
            self.enabled = true;
        }

        let tout = if timeout > 0 {
            Some(Duration::from_millis(timeout as u64))
        } else {
            None
        };

        match self.watcher.poll(tout) {
            Some(event) => {
                let fd = match event.ident {
                    Ident::Fd(fd) => fd,
                    _ => panic!("Unexpected event type"),
                };
                match event.data {
                    EventData::ReadReady(_) => events[0].events = EventSet::IN.bits(),
                    EventData::WriteReady(_) => events[0].events = EventSet::OUT.bits(),
                    _ => panic!("Unexpected EventData type"),
                }
                events[0].u64 = fd as u64;
                Ok(1)
            }
            None => Ok(0),
        }
    }
}

/*
impl AsRawFd for Epoll {
    fn as_raw_fd(&self) -> RawFd {
        self.device_fd
    }
}

impl std::ops::Drop for Epoll {
    fn drop(&mut self) {
        // Safe because this fd is opened with `epoll_create` and we trust
        // the kernel to give us a valid fd.
        unsafe {
            libc::close(self.epoll_fd);
        }
    }
}
*/

#[cfg(test)]
mod tests {
    use super::*;

    use crate::eventfd;
    use crate::eventfd::EventFd;

    #[test]
    fn test_event_ops() {
        let mut event = EpollEvent::default();
        assert_eq!(event.events(), 0);
        assert_eq!(event.data(), 0);

        event = EpollEvent::new(EventSet::IN, 2);
        assert_eq!(event.events(), 1);
        assert_eq!(event.event_set(), EventSet::IN);

        assert_eq!(event.data(), 2);
        assert_eq!(event.fd(), 2);
    }

    #[test]
    fn test_epoll() {
        const DEFAULT__TIMEOUT: i32 = 250;
        const EVENT_BUFFER_SIZE: usize = 128;
        const MAX_EVENTS: usize = 10;

        let mut epoll = Epoll::new().unwrap();
        //assert_eq!(epoll.epoll_fd, epoll.as_raw_fd());

        // Let's test different scenarios for `epoll_ctl()` and `epoll_wait()` functionality.

        let event_fd_1 = EventFd::new(eventfd::EFD_NONBLOCK).unwrap();
        // For EPOLLOUT to be available it is enough only to be possible to write a value of
        // at least 1 to the eventfd counter without blocking.
        // If we write a value greater than 0 to this counter, the fd will be available for
        // EPOLLIN events too.
        event_fd_1.write(1).unwrap();

        let mut event_1 =
            EpollEvent::new(EventSet::IN | EventSet::OUT, event_fd_1.as_raw_fd() as u64);

        // For EPOLL_CTL_ADD behavior we will try to add some fds with different event masks into
        // the interest list of epoll instance.
        assert!(epoll
            .ctl(
                ControlOperation::Add,
                event_fd_1.as_raw_fd() as i32,
                &event_1
            )
            .is_ok());

        // We can't add twice the same fd to epoll interest list.
        assert!(epoll
            .ctl(
                ControlOperation::Add,
                event_fd_1.as_raw_fd() as i32,
                &event_1
            )
            .is_err());

        let event_fd_2 = EventFd::new(eventfd::EFD_NONBLOCK).unwrap();
        event_fd_2.write(1).unwrap();
        assert!(epoll
            .ctl(
                ControlOperation::Add,
                event_fd_2.as_raw_fd() as i32,
                // For this fd, we want an Event instance that has `data` field set to other
                // value than the value of the fd and `events` without EPOLLIN type set.
                &EpollEvent::new(EventSet::OUT, 10)
            )
            .is_ok());

        // For the following eventfd we won't write anything to its counter, so we expect EPOLLIN
        // event to not be available for this fd, even if we say that we want to monitor this type
        // of event via EPOLL_CTL_ADD operation.
        let event_fd_3 = EventFd::new(eventfd::EFD_NONBLOCK).unwrap();
        let event_3 = EpollEvent::new(EventSet::OUT | EventSet::IN, event_fd_3.as_raw_fd() as u64);
        assert!(epoll
            .ctl(
                ControlOperation::Add,
                event_fd_3.as_raw_fd() as i32,
                &event_3
            )
            .is_ok());

        // Let's check `epoll_wait()` behavior for our epoll instance.
        let mut ready_events = vec![EpollEvent::default(); EVENT_BUFFER_SIZE];
        let mut ev_count = epoll
            .wait(MAX_EVENTS, DEFAULT__TIMEOUT, &mut ready_events[..])
            .unwrap();

        // We expect to have 3 fds in the ready list of epoll instance.
        assert_eq!(ev_count, 3);

        // Let's check also the Event values that are now returned in the ready list.
        assert_eq!(ready_events[0].data(), event_fd_1.as_raw_fd() as u64);
        // For this fd, `data` field was populated with random data instead of the
        // corresponding fd value.
        assert_eq!(ready_events[1].data(), 10);
        assert_eq!(ready_events[2].data(), event_fd_3.as_raw_fd() as u64);

        // EPOLLIN and EPOLLOUT should be available for this fd.
        assert_eq!(
            ready_events[0].events(),
            (EventSet::IN | EventSet::OUT).bits()
        );
        // Only EPOLLOUT is expected because we didn't want to monitor EPOLLIN on this fd.
        assert_eq!(ready_events[1].events(), EventSet::OUT.bits());
        // Only EPOLLOUT too because eventfd counter value is 0 (we didn't write a value
        // greater than 0 to it).
        assert_eq!(ready_events[2].events(), EventSet::OUT.bits());

        // Now we're gonna modify the Event instance for a fd to test EPOLL_CTL_MOD
        // behavior.
        // We create here a new Event with some events, other than those previously set,
        // that we want to monitor this time on event_fd_1.
        event_1 = EpollEvent::new(EventSet::OUT, 20);
        assert!(epoll
            .ctl(
                ControlOperation::Modify,
                event_fd_1.as_raw_fd() as i32,
                &event_1
            )
            .is_ok());

        let event_fd_4 = EventFd::new(eventfd::EFD_NONBLOCK).unwrap();
        // Can't modify a fd that wasn't added to epoll interest list.
        assert!(epoll
            .ctl(
                ControlOperation::Modify,
                event_fd_4.as_raw_fd() as i32,
                &EpollEvent::default()
            )
            .is_err());

        let _ = epoll
            .wait(MAX_EVENTS, DEFAULT__TIMEOUT, &mut ready_events[..])
            .unwrap();

        // Let's check that Event fields were indeed changed for the `event_fd_1` fd.
        assert_eq!(ready_events[0].data(), 20);
        // EPOLLOUT is now available for this fd as we've intended with EPOLL_CTL_MOD operation.
        assert_eq!(ready_events[0].events(), EventSet::OUT.bits());

        // Now let's set for a fd to not have any events monitored.
        assert!(epoll
            .ctl(
                ControlOperation::Modify,
                event_fd_1.as_raw_fd() as i32,
                &EpollEvent::default()
            )
            .is_ok());

        // In this particular case we expect to remain only with 2 fds in the ready list.
        ev_count = epoll
            .wait(MAX_EVENTS, DEFAULT__TIMEOUT, &mut ready_events[..])
            .unwrap();
        assert_eq!(ev_count, 2);

        // Let's also delete a fd from the interest list.
        assert!(epoll
            .ctl(
                ControlOperation::Delete,
                event_fd_2.as_raw_fd() as i32,
                &EpollEvent::default()
            )
            .is_ok());

        // We expect to have only one fd remained in the ready list (event_fd_3).
        ev_count = epoll
            .wait(MAX_EVENTS, DEFAULT__TIMEOUT, &mut ready_events[..])
            .unwrap();

        assert_eq!(ev_count, 1);
        assert_eq!(ready_events[0].data(), event_fd_3.as_raw_fd() as u64);
        assert_eq!(ready_events[0].events(), EventSet::OUT.bits());

        // If we try to remove a fd from epoll interest list that wasn't added before it will fail.
        assert!(epoll
            .ctl(
                ControlOperation::Delete,
                event_fd_4.as_raw_fd() as i32,
                &EpollEvent::default()
            )
            .is_err());
    }
}
