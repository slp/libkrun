use std::collections::BTreeSet;
use std::io::Write;
use std::mem::size_of;
use std::result;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};

use utils::eventfd::EventFd;
use vm_memory::{ByteValued, Bytes, GuestMemoryMmap};

use super::super::{
    ActivateError, ActivateResult, DeviceState, Queue as VirtQueue, VirtioDevice,
    VIRTIO_MMIO_INT_VRING,
};
use super::audio_backends::{alloc_audio_backend, AudioBackend};
use super::stream::Buffer;
use super::stream::{Error as StreamError, Stream};
use super::virtio_sound::{VirtioSoundConfig, VIRTIO_SND_D_INPUT, VIRTIO_SND_D_OUTPUT};
use super::Vring;
use super::{defs, defs::uapi};
use super::{BackendType, Error};
use super::{ControlMessage, ControlMessageKind, IOMessage};
use crate::legacy::Gic;
use crate::virtio::snd::virtio_sound::{
    VirtioSndPcmSetParams, VirtioSoundHeader, VirtioSoundPcmHeader, VirtioSoundPcmInfo,
    VirtioSoundPcmStatus, VirtioSoundPcmXfer, VirtioSoundQueryInfo, VIRTIO_SND_S_BAD_MSG,
    VIRTIO_SND_S_IO_ERR, VIRTIO_SND_S_NOT_SUPP, VIRTIO_SND_S_OK,
};
use crate::virtio::DescriptorChain;
use crate::Error as DeviceError;

// Virtqueues.
pub(crate) const CTL_INDEX: usize = 0;
pub(crate) const EVT_INDEX: usize = 1;
pub(crate) const TXQ_INDEX: usize = 2;
pub(crate) const RXQ_INDEX: usize = 3;

// Supported features.
pub(crate) const AVAIL_FEATURES: u64 = 1 << uapi::VIRTIO_F_VERSION_1 as u64;

#[derive(Copy, Clone, Debug, Default)]
#[repr(C, packed)]
pub struct VirtioSnd {}

pub struct Snd {
    pub(crate) vring_ctl: Option<Arc<Mutex<Vring>>>,
    pub(crate) vring_evt: Option<Arc<Mutex<Vring>>>,
    pub(crate) vring_txq: Option<Arc<Mutex<Vring>>>,
    pub(crate) vring_rxq: Option<Arc<Mutex<Vring>>>,
    pub(crate) queues: Vec<VirtQueue>,
    pub(crate) queue_events: Vec<EventFd>,
    pub(crate) avail_features: u64,
    pub(crate) acked_features: u64,
    pub(crate) interrupt_status: Arc<AtomicUsize>,
    pub(crate) interrupt_evt: EventFd,
    pub(crate) activate_evt: EventFd,
    pub(crate) device_state: DeviceState,
    intc: Option<Arc<Mutex<Gic>>>,
    irq_line: Option<u32>,
    streams: Arc<Mutex<Vec<Stream>>>,
    streams_no: usize,
    audio_backend: Option<Mutex<Box<dyn AudioBackend + Send + Sync>>>,
}

impl Snd {
    pub(crate) fn with_queues(queues: Vec<VirtQueue>) -> super::Result<Snd> {
        let mut queue_events = Vec::new();
        for _ in 0..queues.len() {
            queue_events
                .push(EventFd::new(utils::eventfd::EFD_NONBLOCK).map_err(Error::EventFdCreate)?);
        }

        let streams = vec![
            Stream {
                id: 0,
                direction: VIRTIO_SND_D_OUTPUT,
                ..Stream::default()
            },
            Stream {
                id: 1,
                direction: VIRTIO_SND_D_INPUT,
                ..Stream::default()
            },
        ];
        let streams_no = streams.len();
        let streams = Arc::new(Mutex::new(streams));

        Ok(Snd {
            vring_ctl: None,
            vring_evt: None,
            vring_rxq: None,
            vring_txq: None,
            queues,
            queue_events,
            avail_features: AVAIL_FEATURES,
            acked_features: 0,
            interrupt_status: Arc::new(AtomicUsize::new(0)),
            interrupt_evt: EventFd::new(utils::eventfd::EFD_NONBLOCK)
                .map_err(Error::EventFdCreate)?,
            activate_evt: EventFd::new(utils::eventfd::EFD_NONBLOCK)
                .map_err(Error::EventFdCreate)?,
            device_state: DeviceState::Inactive,
            intc: None,
            irq_line: None,
            streams,
            streams_no,
            audio_backend: None,
        })
    }

    pub fn new() -> super::Result<Snd> {
        let queues: Vec<VirtQueue> = defs::QUEUE_SIZES
            .iter()
            .map(|&max_size| VirtQueue::new(max_size))
            .collect();
        Self::with_queues(queues)
    }

    pub fn id(&self) -> &str {
        defs::SND_DEV_ID
    }

    pub fn set_intc(&mut self, intc: Arc<Mutex<Gic>>) {
        self.intc = Some(intc);
    }

    pub fn signal_used_queue(&self) -> result::Result<(), DeviceError> {
        debug!("snd: raising IRQ");
        self.interrupt_status
            .fetch_or(VIRTIO_MMIO_INT_VRING as usize, Ordering::SeqCst);
        if let Some(intc) = &self.intc {
            intc.lock().unwrap().set_irq(self.irq_line.unwrap());
            Ok(())
        } else {
            self.interrupt_evt.write(1).map_err(|e| {
                error!("Failed to signal used queue: {:?}", e);
                DeviceError::FailedSignalingUsedQueue(e)
            })
        }
    }

    fn process_ctl_message(
        &mut self,
        mem: &GuestMemoryMmap,
        vring_ctl: &Arc<Mutex<Vring>>,
        head: DescriptorChain,
    ) -> result::Result<bool, Error> {
        let audio_backend = match self.audio_backend.as_ref() {
            Some(ab) => ab,
            None => return Err(Error::MissingAudioBackend),
        };

        let descriptors: Vec<_> = head.clone().into_iter().collect();
        if descriptors.len() < 2 {
            return Err(Error::UnexpectedDescriptorCount(descriptors.len()).into());
        }

        // Request descriptor.
        let desc_request = &descriptors[0];
        if desc_request.is_write_only() {
            return Err(Error::UnexpectedWriteOnlyDescriptor(0).into());
        }

        let request = mem
            .read_obj::<VirtioSoundHeader>(desc_request.addr)
            .map_err(|_| Error::DescriptorReadFailed)?;

        // Keep track of bytes that will be written in the VQ.
        let mut used_len = 0;

        // Reply header descriptor.
        let desc_hdr = &descriptors[1];
        if !desc_hdr.is_write_only() {
            return Err(Error::UnexpectedReadableDescriptor(1).into());
        }

        let mut resp = VirtioSoundHeader {
            code: VIRTIO_SND_S_OK.into(),
        };

        let code = ControlMessageKind::try_from(request.code.to_native()).unwrap();
        match code {
            ControlMessageKind::ChmapInfo
            | ControlMessageKind::JackInfo
            | ControlMessageKind::JackRemap => {
                resp.code = VIRTIO_SND_S_NOT_SUPP.into();
            }
            ControlMessageKind::PcmInfo => {
                if descriptors.len() != 3 {
                    error!("a PCM_INFO request should have three descriptors total.");
                    return Err(Error::UnexpectedDescriptorCount(descriptors.len()).into());
                } else if !descriptors[2].is_write_only() {
                    error!(
                        "a PCM_INFO request should have a writeable descriptor for the info \
                             payload response after the header status response"
                    );
                    return Err(Error::UnexpectedReadableDescriptor(2).into());
                }

                let request = mem
                    .read_obj::<VirtioSoundQueryInfo>(desc_request.addr)
                    .map_err(|_| Error::DescriptorReadFailed)?;

                let start_id = u32::from(request.start_id) as usize;
                let count = u32::from(request.count) as usize;
                let streams = self.streams.lock().unwrap();
                if streams.len() <= start_id || streams.len() < start_id + count {
                    resp.code = VIRTIO_SND_S_BAD_MSG.into();
                } else {
                    let desc_response = &descriptors[2];

                    let mut buf = vec![];
                    let mut p: VirtioSoundPcmInfo;

                    for s in streams
                        .iter()
                        .skip(u32::from(request.start_id) as usize)
                        .take(u32::from(request.count) as usize)
                    {
                        p = VirtioSoundPcmInfo::default();
                        p.hdr.hda_fn_nid = 0.into();
                        p.features = s.params.features;
                        p.formats = s.formats;
                        p.rates = s.rates;
                        p.direction = s.direction;
                        p.channels_min = s.channels_min;
                        p.channels_max = s.channels_max;
                        buf.extend_from_slice(p.as_slice());
                    }
                    mem.write_slice(&buf, desc_response.addr)
                        .map_err(|_| Error::DescriptorWriteFailed)?;
                    used_len += desc_response.len;
                }
            }
            ControlMessageKind::PcmSetParams => {
                let request = mem
                    .read_obj::<VirtioSndPcmSetParams>(desc_request.addr)
                    .map_err(|_| Error::DescriptorReadFailed)?;
                let stream_id: u32 = request.hdr.stream_id.into();

                if stream_id as usize >= self.streams_no {
                    log::error!("{}", Error::from(StreamError::InvalidStreamId(stream_id)));
                    resp.code = VIRTIO_SND_S_BAD_MSG.into();
                } else {
                    audio_backend
                        .lock()
                        .unwrap()
                        .set_parameters(
                            stream_id,
                            ControlMessage {
                                kind: code,
                                code: VIRTIO_SND_S_OK,
                                desc_addr: desc_hdr.addr,
                                head_index: head.index,
                                vring: vring_ctl.clone(),
                            },
                            request,
                        )
                        .unwrap();

                    // PcmSetParams needs check valid formats/rates; the audio backend will
                    // reply when it drops the ControlMessage.
                    return Ok(false);
                }
            }
            ControlMessageKind::PcmPrepare => {
                let request = mem
                    .read_obj::<VirtioSoundPcmHeader>(desc_request.addr)
                    .map_err(|_| Error::DescriptorReadFailed)?;
                let stream_id = request.stream_id.into();

                if stream_id as usize >= self.streams_no {
                    log::error!("{}", Error::from(StreamError::InvalidStreamId(stream_id)));
                    resp.code = VIRTIO_SND_S_BAD_MSG.into();
                } else {
                    audio_backend.lock().unwrap().prepare(stream_id).unwrap();
                }
            }
            ControlMessageKind::PcmRelease => {
                let request = mem
                    .read_obj::<VirtioSoundPcmHeader>(desc_request.addr)
                    .map_err(|_| Error::DescriptorReadFailed)?;
                let stream_id = request.stream_id.into();

                if stream_id as usize >= self.streams_no {
                    log::error!("{}", Error::from(StreamError::InvalidStreamId(stream_id)));
                    resp.code = VIRTIO_SND_S_BAD_MSG.into();
                } else {
                    audio_backend
                        .lock()
                        .unwrap()
                        .release(
                            stream_id,
                            ControlMessage {
                                kind: code,
                                code: VIRTIO_SND_S_OK,
                                desc_addr: desc_hdr.addr,
                                head_index: head.index,
                                vring: vring_ctl.clone(),
                            },
                        )
                        .unwrap();

                    // PcmRelease needs to flush IO messages; the audio backend will reply when
                    // it drops the ControlMessage.
                    return Ok(false);
                }
            }
            ControlMessageKind::PcmStart => {
                let request = mem
                    .read_obj::<VirtioSoundPcmHeader>(desc_request.addr)
                    .map_err(|_| Error::DescriptorReadFailed)?;
                let stream_id = request.stream_id.into();

                if stream_id as usize >= self.streams_no {
                    log::error!("{}", Error::from(StreamError::InvalidStreamId(stream_id)));
                    resp.code = VIRTIO_SND_S_BAD_MSG.into();
                } else {
                    audio_backend.lock().unwrap().start(stream_id).unwrap();
                }
            }
            ControlMessageKind::PcmStop => {
                let request = mem
                    .read_obj::<VirtioSoundPcmHeader>(desc_request.addr)
                    .map_err(|_| Error::DescriptorReadFailed)?;
                let stream_id = request.stream_id.into();

                if stream_id as usize >= self.streams_no {
                    log::error!("{}", Error::from(StreamError::InvalidStreamId(stream_id)));
                    resp.code = VIRTIO_SND_S_BAD_MSG.into();
                } else {
                    audio_backend.lock().unwrap().stop(stream_id).unwrap();
                }
            }
        }
        debug!(
            "returned {} for ctrl msg {:?}",
            match u32::from(resp.code) {
                v if v == VIRTIO_SND_S_OK => "OK",
                v if v == VIRTIO_SND_S_BAD_MSG => "BAD_MSG",
                v if v == VIRTIO_SND_S_NOT_SUPP => "NOT_SUPP",
                v if v == VIRTIO_SND_S_IO_ERR => "IO_ERR",
                _ => unreachable!(),
            },
            code
        );

        mem.write_obj(resp, desc_hdr.addr).unwrap();
        vring_ctl
            .lock()
            .unwrap()
            .queue
            .add_used(mem, head.index, used_len);

        Ok(true)
    }

    pub fn process_ctl_queue(&mut self) -> bool {
        debug!("snd: process_control()");
        let mem = match self.device_state {
            DeviceState::Activated(ref mem) => mem.clone(),
            // This should never happen, it's been already validated in the event handler.
            DeviceState::Inactive => unreachable!(),
        };
        let vring_ctl_mutex = match self.vring_ctl.as_ref() {
            Some(v) => v.clone(),
            None => unreachable!(),
        };

        let mut have_used = false;
        loop {
            let mut vring_ctl = vring_ctl_mutex.lock().unwrap();
            let head = vring_ctl.queue.pop(&mem);
            drop(vring_ctl);

            if let Some(head) = head {
                match self.process_ctl_message(&mem, &vring_ctl_mutex, head) {
                    Ok(used) => {
                        if used {
                            have_used = true
                        }
                    }
                    Err(e) => {
                        error!("Error processing control message: {:?}", e);
                    }
                }
            } else {
                break;
            }
        }

        have_used
    }

    fn process_txq_message(
        &mut self,
        mem: &GuestMemoryMmap,
        vring_txq: &Arc<Mutex<Vring>>,
        desc_chain: DescriptorChain,
    ) -> result::Result<bool, Error> {
        let audio_backend = match self.audio_backend.as_ref() {
            Some(ab) => ab,
            None => return Err(Error::MissingAudioBackend),
        };

        #[derive(Copy, Clone, PartialEq, Debug)]
        enum TxState {
            Ready,
            WaitingBufferForStreamId(u32),
            Done,
        }

        let mut stream_ids = BTreeSet::default();

        let mut state = TxState::Ready;
        let mut buffers: Vec<Buffer> = vec![];

        let mut notify = true;
        let descriptors: Vec<_> = desc_chain.clone().into_iter().collect();
        for descriptor in &descriptors {
            match state {
                TxState::Done => {
                    return Err(Error::UnexpectedDescriptorCount(descriptors.len()).into());
                }
                TxState::Ready if descriptor.is_write_only() => {
                    if descriptor.len as usize != size_of::<VirtioSoundPcmStatus>() {
                        return Err(Error::UnexpectedDescriptorSize(
                            size_of::<VirtioSoundPcmStatus>(),
                            descriptor.len,
                        )
                        .into());
                    }
                    state = TxState::Done;
                }
                TxState::WaitingBufferForStreamId(stream_id) if descriptor.is_write_only() => {
                    if descriptor.len as usize != size_of::<VirtioSoundPcmStatus>() {
                        return Err(Error::UnexpectedDescriptorSize(
                            size_of::<VirtioSoundPcmStatus>(),
                            descriptor.len,
                        )
                        .into());
                    }
                    let mut streams = self.streams.lock().unwrap();
                    let _nbuffers = buffers.len();
                    for b in std::mem::take(&mut buffers) {
                        streams[stream_id as usize].buffers.push_back(b);
                    }
                    state = TxState::Done;
                }
                TxState::Ready if descriptor.len as usize != size_of::<VirtioSoundPcmXfer>() => {
                    return Err(Error::UnexpectedDescriptorSize(
                        size_of::<VirtioSoundPcmXfer>(),
                        descriptor.len,
                    )
                    .into());
                }
                TxState::Ready => {
                    let xfer = mem
                        .read_obj::<VirtioSoundPcmXfer>(descriptor.addr)
                        .map_err(|_| Error::DescriptorReadFailed)?;
                    let stream_id: u32 = xfer.stream_id.into();
                    stream_ids.insert(stream_id);

                    state = TxState::WaitingBufferForStreamId(stream_id);
                }
                TxState::WaitingBufferForStreamId(stream_id)
                    if descriptor.len as usize == size_of::<VirtioSoundPcmXfer>() =>
                {
                    return Err(Error::UnexpectedDescriptorSize(
                        u32::from(
                            self.streams.lock().unwrap()[stream_id as usize]
                                .params
                                .buffer_bytes,
                        ) as usize,
                        descriptor.len,
                    )
                    .into());
                }
                TxState::WaitingBufferForStreamId(_stream_id) => {
                    debug!(
                        "new buffer: len={} index={} head_index={}",
                        descriptor.len, descriptor.index, desc_chain.index
                    );
                    let mut buf = vec![0; descriptor.len as usize];
                    let bytes_read = mem
                        .read(&mut buf, descriptor.addr)
                        .map_err(|_| Error::DescriptorReadFailed)?;
                    buf.truncate(bytes_read);

                    let message = Arc::new(IOMessage {
                        status: VIRTIO_SND_S_OK.into(),
                        desc_addr: desc_chain.addr,
                        head_index: desc_chain.index,
                        data_addr: descriptor.addr,
                        data_len: descriptor.len,
                        mem: mem.clone(),
                        vring: vring_txq.clone(),
                        notify,
                    });

                    buffers.push(Buffer::new(buf, Arc::clone(&message)));

                    notify = false;
                }
            }
        }

        /*
        if notify {
            let resp = VirtioSoundPcmStatus {
                status: VIRTIO_SND_S_OK.into(),
                latency_bytes: 0.into(),
            };

            let mut vring = vring_txq.lock().unwrap();
            mem.write_obj(resp, desc_chain.addr);
            vring
                .queue
                .add_used(mem, desc_chain.index, resp.as_slice().len() as u32);
            vring.signal_used_queue();
        }
        */

        if !stream_ids.is_empty() {
            let b = audio_backend.lock().unwrap();
            for id in stream_ids {
                b.write(id).unwrap();
            }
        }

        Ok(false)
    }

    pub fn process_txq_queue(&mut self) -> bool {
        debug!("snd: process_txq_queue()");
        let mem = match self.device_state {
            DeviceState::Activated(ref mem) => mem.clone(),
            // This should never happen, it's been already validated in the event handler.
            DeviceState::Inactive => unreachable!(),
        };
        let vring_txq_mutex = match self.vring_txq.as_ref() {
            Some(v) => v.clone(),
            None => unreachable!(),
        };

        let mut have_used = false;
        loop {
            let mut vring_txq = vring_txq_mutex.lock().unwrap();
            let head = vring_txq.queue.pop(&mem);
            drop(vring_txq);

            if let Some(head) = head {
                match self.process_txq_message(&mem, &vring_txq_mutex, head) {
                    Ok(used) => {
                        if used {
                            have_used = true
                        }
                    }
                    Err(e) => {
                        error!("Error processing control message: {:?}", e);
                    }
                }
            } else {
                break;
            }
        }

        have_used
    }

    pub fn process_evt(&mut self) -> bool {
        error!("snd: process_evt()");
        false
    }

    pub fn process_txq(&mut self) -> bool {
        error!("snd: process_txq()");
        false
    }

    pub fn process_rxq(&mut self) -> bool {
        error!("snd: process_rxq()");
        false
    }
}

impl VirtioDevice for Snd {
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
        uapi::VIRTIO_ID_SND
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
        self.irq_line = Some(irq);
    }

    fn read_config(&self, offset: u64, mut data: &mut [u8]) {
        let config = VirtioSoundConfig {
            jacks: 0.into(),
            streams: 1.into(),
            chmaps: 0.into(),
        };

        let config_slice = config.as_slice();
        let config_len = config_slice.len() as u64;
        if offset >= config_len {
            error!("Failed to read config space");
            return;
        }
        if let Some(end) = offset.checked_add(data.len() as u64) {
            // This write can't fail, offset and end are checked against config_len.
            data.write_all(&config_slice[offset as usize..std::cmp::min(end, config_len) as usize])
                .unwrap();
        }
    }

    fn write_config(&mut self, offset: u64, data: &[u8]) {
        warn!(
            "snd: guest driver attempted to write device config (offset={:x}, len={:x})",
            offset,
            data.len()
        );
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

        let vring_ctl = Vring {
            mem: mem.clone(),
            queue: self.queues[CTL_INDEX].clone(),
            interrupt_evt: self.interrupt_evt.try_clone().unwrap(),
            interrupt_status: self.interrupt_status.clone(),
            intc: self.intc.clone(),
            irq_line: self.irq_line.clone(),
        };
        let vring_evt = Vring {
            mem: mem.clone(),
            queue: self.queues[EVT_INDEX].clone(),
            interrupt_evt: self.interrupt_evt.try_clone().unwrap(),
            interrupt_status: self.interrupt_status.clone(),
            intc: self.intc.clone(),
            irq_line: self.irq_line.clone(),
        };
        let vring_txq = Vring {
            mem: mem.clone(),
            queue: self.queues[TXQ_INDEX].clone(),
            interrupt_evt: self.interrupt_evt.try_clone().unwrap(),
            interrupt_status: self.interrupt_status.clone(),
            intc: self.intc.clone(),
            irq_line: self.irq_line.clone(),
        };
        let vring_rxq = Vring {
            mem: mem.clone(),
            queue: self.queues[RXQ_INDEX].clone(),
            interrupt_evt: self.interrupt_evt.try_clone().unwrap(),
            interrupt_status: self.interrupt_status.clone(),
            intc: self.intc.clone(),
            irq_line: self.irq_line.clone(),
        };

        self.vring_ctl = Some(Arc::new(Mutex::new(vring_ctl)));
        self.vring_evt = Some(Arc::new(Mutex::new(vring_evt)));
        self.vring_txq = Some(Arc::new(Mutex::new(vring_txq)));
        self.vring_rxq = Some(Arc::new(Mutex::new(vring_rxq)));

        let audio_backend = alloc_audio_backend(
            BackendType::Pipewire,
            self.vring_ctl.as_ref().unwrap().clone(),
            self.vring_rxq.as_ref().unwrap().clone(),
            self.streams.clone(),
        )
        .unwrap();

        self.audio_backend = Some(Mutex::new(audio_backend));

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
}
