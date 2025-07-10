mod device;
mod event_handler;
mod worker;

pub use self::defs::uapi::VIRTIO_ID_INPUT as TYPE_INPUT;
pub use self::device::Input;

mod defs {
    pub const INPUT_DEV_ID: &str = "virtio_input";
    pub const NUM_QUEUES: usize = 2;
    pub const QUEUE_SIZES: &[u16] = &[256; NUM_QUEUES];

    pub mod uapi {
        pub const VIRTIO_F_VERSION_1: u32 = 32;
        pub const VIRTIO_ID_INPUT: u32 = 18;
    }
}

#[derive(Debug)]
pub enum InputError {
    /// Failed to create event fd.
    EventFd(std::io::Error),

    SendNotificationFailed,

    EventFdError,

    HandleEventNotEpollIn,

    HandleEventUnknownEvent,

    UnexpectedConfig(u8),

    UnexpectedFetchEventError,

    UnexpectedDescriptorCount(usize),

    UnexpectedInputDeviceError,

    UnexpectedWriteDescriptorError,

    UnexpectedWriteVringError,
}

type Result<T> = std::result::Result<T, InputError>;
