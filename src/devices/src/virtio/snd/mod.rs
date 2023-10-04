use std::{
    io::Error as IoError,
    sync::{atomic::AtomicUsize, Arc, Mutex},
};

mod audio_backends;
mod device;
mod event_handler;
pub mod stream;
mod virtio_sound;

use thiserror::Error as ThisError;
use utils::eventfd::EventFd;
use vm_memory::{ByteValued, Bytes, GuestAddress, GuestMemoryMmap};

pub use self::defs::uapi::VIRTIO_ID_SND as TYPE_SND;
pub use self::device::Snd;
use self::virtio_sound::{
    VIRTIO_SND_R_CHMAP_INFO, VIRTIO_SND_R_JACK_INFO, VIRTIO_SND_R_JACK_REMAP,
    VIRTIO_SND_R_PCM_INFO, VIRTIO_SND_R_PCM_PREPARE, VIRTIO_SND_R_PCM_RELEASE,
    VIRTIO_SND_R_PCM_SET_PARAMS, VIRTIO_SND_R_PCM_START, VIRTIO_SND_R_PCM_STOP,
};

use super::Queue as VirtQueue;
use crate::{
    legacy::Gic,
    virtio::{
        snd::virtio_sound::{VirtioSoundHeader, VirtioSoundPcmStatus},
        VIRTIO_MMIO_INT_VRING,
    },
};

mod defs {
    use super::virtio_sound::*;

    pub const SND_DEV_ID: &str = "virtio_snd";
    pub const NUM_QUEUES: usize = 4;
    pub const QUEUE_SIZES: &[u16] = &[256; NUM_QUEUES];

    pub const SUPPORTED_FORMATS: u64 = 1 << VIRTIO_SND_PCM_FMT_U8
        | 1 << VIRTIO_SND_PCM_FMT_S16
        | 1 << VIRTIO_SND_PCM_FMT_S24
        | 1 << VIRTIO_SND_PCM_FMT_S32;

    pub const SUPPORTED_RATES: u64 = 1 << VIRTIO_SND_PCM_RATE_8000
        | 1 << VIRTIO_SND_PCM_RATE_11025
        | 1 << VIRTIO_SND_PCM_RATE_16000
        | 1 << VIRTIO_SND_PCM_RATE_22050
        | 1 << VIRTIO_SND_PCM_RATE_32000
        | 1 << VIRTIO_SND_PCM_RATE_44100
        | 1 << VIRTIO_SND_PCM_RATE_48000;

    pub mod uapi {
        pub const VIRTIO_F_VERSION_1: u32 = 32;
        pub const VIRTIO_ID_SND: u32 = 25;
    }
}

pub type Result<T> = std::result::Result<T, Error>;

/// Custom error types
#[derive(Debug, ThisError)]
pub enum Error {
    #[error("Notification send failed")]
    SendNotificationFailed,
    #[error("Descriptor not found")]
    DescriptorNotFound,
    #[error("Descriptor read failed")]
    DescriptorReadFailed,
    #[error("Descriptor write failed")]
    DescriptorWriteFailed,
    #[error("Failed to handle event other than EPOLLIN event")]
    HandleEventNotEpollIn,
    #[error("Failed to handle unknown event")]
    HandleUnknownEvent,
    #[error("Invalid control message code {0}")]
    InvalidControlMessage(u32),
    #[error("Failed to create a new EventFd")]
    EventFdCreate(IoError),
    #[error("Request missing data buffer")]
    SoundReqMissingData,
    #[error("Audio backend not supported")]
    AudioBackendNotSupported,
    #[error("Invalid virtio_snd_hdr size, expected: {0}, found: {1}")]
    UnexpectedSoundHeaderSize(usize, u32),
    #[error("Received unexpected write only descriptor at index {0}")]
    UnexpectedWriteOnlyDescriptor(usize),
    #[error("Received unexpected readable descriptor at index {0}")]
    UnexpectedReadableDescriptor(usize),
    #[error("Invalid descriptor count {0}")]
    UnexpectedDescriptorCount(usize),
    #[error("Invalid descriptor size, expected: {0}, found: {1}")]
    UnexpectedDescriptorSize(usize, u32),
    #[error("Protocol or device error: {0}")]
    Stream(stream::Error),
    #[error("Stream with id {0} not found")]
    StreamWithIdNotFound(u32),
    #[error("Channel number not supported: {0}")]
    ChannelNotSupported(u8),
    #[error("No audio backend is present")]
    MissingAudioBackend,
}

/*
impl From<SndError> for IoError {
    fn from(e: SndError) -> Self {
        Self::new(ErrorKind::Other, e)
    }
}
*/

impl From<stream::Error> for Error {
    fn from(val: stream::Error) -> Self {
        Self::Stream(val)
    }
}

#[derive(Clone, Copy, Default, Debug, Eq, PartialEq)]
pub enum BackendType {
    #[default]
    Pipewire,
}

pub struct Vring {
    mem: GuestMemoryMmap,
    queue: VirtQueue,
    interrupt_evt: EventFd,
    interrupt_status: Arc<AtomicUsize>,
    intc: Option<Arc<Mutex<Gic>>>,
    irq_line: Option<u32>,
}

impl Vring {
    pub fn signal_used_queue(&self) {
        debug!("snd: raising IRQ");
        self.interrupt_status.fetch_or(
            VIRTIO_MMIO_INT_VRING as usize,
            std::sync::atomic::Ordering::SeqCst,
        );
        if let Some(intc) = &self.intc {
            intc.lock().unwrap().set_irq(self.irq_line.unwrap());
        } else {
            if let Err(e) = self.interrupt_evt.write(1) {
                error!("Failed to signal used queue: {:?}", e);
            };
        }
    }
}

#[derive(Debug)]
pub struct InvalidControlMessage(u32);

impl std::fmt::Display for InvalidControlMessage {
    fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(fmt, "Invalid control message code {}", self.0)
    }
}

impl From<InvalidControlMessage> for Error {
    fn from(val: InvalidControlMessage) -> Self {
        Self::InvalidControlMessage(val.0)
    }
}

impl std::error::Error for InvalidControlMessage {}

#[derive(Copy, Debug, Clone, Eq, PartialEq)]
#[repr(u32)]
pub enum ControlMessageKind {
    JackInfo = 1,
    JackRemap = 2,
    PcmInfo = 0x0100,
    PcmSetParams = 0x0101,
    PcmPrepare = 0x0102,
    PcmRelease = 0x0103,
    PcmStart = 0x0104,
    PcmStop = 0x0105,
    ChmapInfo = 0x0200,
}

impl TryFrom<u32> for ControlMessageKind {
    type Error = InvalidControlMessage;

    fn try_from(val: u32) -> std::result::Result<Self, Self::Error> {
        Ok(match u32::from(val) {
            VIRTIO_SND_R_JACK_INFO => Self::JackInfo,
            VIRTIO_SND_R_JACK_REMAP => Self::JackRemap,
            VIRTIO_SND_R_PCM_INFO => Self::PcmInfo,
            VIRTIO_SND_R_PCM_SET_PARAMS => Self::PcmSetParams,
            VIRTIO_SND_R_PCM_PREPARE => Self::PcmPrepare,
            VIRTIO_SND_R_PCM_RELEASE => Self::PcmRelease,
            VIRTIO_SND_R_PCM_START => Self::PcmStart,
            VIRTIO_SND_R_PCM_STOP => Self::PcmStop,
            VIRTIO_SND_R_CHMAP_INFO => Self::ChmapInfo,
            other => return Err(InvalidControlMessage(other)),
        })
    }
}

pub struct ControlMessage {
    pub kind: ControlMessageKind,
    pub code: u32,
    pub desc_addr: GuestAddress,
    pub head_index: u16,
    pub vring: Arc<Mutex<Vring>>,
}

impl std::fmt::Debug for ControlMessage {
    fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
        fmt.debug_struct(stringify!(ControlMessage))
            .field("kind", &self.kind)
            .field("code", &self.code)
            .finish()
    }
}

impl Drop for ControlMessage {
    fn drop(&mut self) {
        debug!(
            "dropping ControlMessage {:?} reply = {}",
            self.kind,
            match self.code {
                virtio_sound::VIRTIO_SND_S_OK => "VIRTIO_SND_S_OK",
                virtio_sound::VIRTIO_SND_S_BAD_MSG => "VIRTIO_SND_S_BAD_MSG",
                virtio_sound::VIRTIO_SND_S_NOT_SUPP => "VIRTIO_SND_S_NOT_SUPP",
                virtio_sound::VIRTIO_SND_S_IO_ERR => "VIRTIO_SND_S_IO_ERR",
                _ => "other",
            }
        );
        let resp = VirtioSoundHeader {
            code: self.code.into(),
        };

        let mut vring = self.vring.lock().unwrap();
        let mem = vring.mem.clone();

        if let Err(err) = vring.mem.write_obj(resp, self.desc_addr) {
            log::error!("Error::DescriptorWriteFailed: {}", err);
            return;
        }
        vring
            .queue
            .add_used(&mem, self.head_index, resp.as_slice().len() as u32);
        vring.signal_used_queue();
    }
}

pub struct IOMessage {
    status: std::sync::atomic::AtomicU32,
    desc_addr: GuestAddress,
    head_index: u16,
    pub data_addr: GuestAddress,
    pub data_len: u32,
    pub mem: GuestMemoryMmap,
    vring: Arc<Mutex<Vring>>,
    pub notify: bool,
}

impl Drop for IOMessage {
    fn drop(&mut self) {
        if self.notify {
            let resp = VirtioSoundPcmStatus {
                status: self.status.load(std::sync::atomic::Ordering::SeqCst).into(),
                latency_bytes: 0.into(),
            };

            let mut vring = self.vring.lock().unwrap();
            let mem = vring.mem.clone();

            if let Err(err) = mem.write_obj(resp, self.desc_addr) {
                log::error!("Error::DescriptorWriteFailed: {}", err);
                return;
            }
            vring
                .queue
                .add_used(&mem, self.head_index, resp.as_slice().len() as u32);
            vring.signal_used_queue();
        } else {
            debug!("avoiding nofitication");
        }
    }
}
