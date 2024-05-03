use std::io::Write;
use std::sync::atomic::AtomicUsize;
use std::sync::{Arc, Mutex};
use std::thread::JoinHandle;

use crossbeam_channel::Sender;
use utils::eventfd::{EventFd, EFD_NONBLOCK};
use virtio_bindings::{virtio_config::VIRTIO_F_VERSION_1, virtio_ring::VIRTIO_RING_F_EVENT_IDX};
use vm_memory::{ByteValued, GuestMemoryMmap};

use super::super::{
    ActivateError, ActivateResult, DeviceState, GpuError, Queue as VirtQueue, VirtioDevice,
    VirtioShmRegion,
};
use super::defs;
use super::defs::uapi;
use super::defs::uapi::virtio_gpu_config;
use super::worker::GpuWorker;
use crate::legacy::Gic;
#[cfg(target_os = "macos")]
use hvf::MemoryMapping;

// Control queue.
pub(crate) const CTL_INDEX: usize = 0;
// Cursor queue.
pub(crate) const CUR_INDEX: usize = 1;

// Supported features.
pub(crate) const AVAIL_FEATURES: u64 = 1u64 << VIRTIO_F_VERSION_1
    | 1u64 << uapi::VIRTIO_GPU_F_VIRGL
    | 1u64 << uapi::VIRTIO_GPU_F_RESOURCE_UUID
    | 1u64 << uapi::VIRTIO_GPU_F_RESOURCE_BLOB
    | 1u64 << uapi::VIRTIO_GPU_F_CONTEXT_INIT;

pub struct Gpu {
    pub(crate) queues: Vec<VirtQueue>,
    pub(crate) queue_events: Vec<EventFd>,
    pub(crate) avail_features: u64,
    pub(crate) acked_features: u64,
    pub(crate) interrupt_status: Arc<AtomicUsize>,
    pub(crate) interrupt_evt: EventFd,
    pub(crate) activate_evt: EventFd,
    pub(crate) device_state: DeviceState,
    shm_region: Option<VirtioShmRegion>,
    intc: Option<Arc<Mutex<Gic>>>,
    irq_line: Option<u32>,
    pub(crate) sender: Option<Sender<u64>>,
    virgl_flags: u32,
    worker_thread: Option<JoinHandle<()>>,
    worker_stopfd: EventFd,
    #[cfg(target_os = "macos")]
    map_sender: Sender<MemoryMapping>,
}

impl Gpu {
    pub(crate) fn with_queues(
        queues: Vec<VirtQueue>,
        virgl_flags: u32,
        #[cfg(target_os = "macos")] map_sender: Sender<MemoryMapping>,
    ) -> super::Result<Gpu> {
        let mut queue_events = Vec::new();
        for _ in 0..queues.len() {
            queue_events
                .push(EventFd::new(utils::eventfd::EFD_NONBLOCK).map_err(GpuError::EventFd)?);
        }

        Ok(Gpu {
            queues,
            queue_events,
            avail_features: AVAIL_FEATURES,
            acked_features: 0,
            interrupt_status: Arc::new(AtomicUsize::new(0)),
            interrupt_evt: EventFd::new(utils::eventfd::EFD_NONBLOCK).map_err(GpuError::EventFd)?,
            activate_evt: EventFd::new(utils::eventfd::EFD_NONBLOCK).map_err(GpuError::EventFd)?,
            device_state: DeviceState::Inactive,
            shm_region: None,
            intc: None,
            irq_line: None,
            sender: None,
            virgl_flags,
            worker_thread: None,
            worker_stopfd: EventFd::new(EFD_NONBLOCK).map_err(GpuError::EventFd)?,
            #[cfg(target_os = "macos")]
            map_sender,
        })
    }

    pub fn new(
        virgl_flags: u32,
        #[cfg(target_os = "macos")] map_sender: Sender<MemoryMapping>,
    ) -> super::Result<Gpu> {
        let queues: Vec<VirtQueue> = defs::QUEUE_SIZES
            .iter()
            .map(|&max_size| VirtQueue::new(max_size))
            .collect();
        Self::with_queues(
            queues,
            virgl_flags,
            #[cfg(target_os = "macos")]
            map_sender,
        )
    }

    pub fn id(&self) -> &str {
        defs::GPU_DEV_ID
    }

    pub fn set_intc(&mut self, intc: Arc<Mutex<Gic>>) {
        self.intc = Some(intc);
    }

    pub fn set_shm_region(&mut self, shm_region: VirtioShmRegion) {
        debug!("virtio_gpu: set_shm_region");
        self.shm_region = Some(shm_region);
    }
}

impl VirtioDevice for Gpu {
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
        uapi::VIRTIO_ID_GPU
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
        let config = virtio_gpu_config {
            events_read: 0,
            events_clear: 0,
            num_scanouts: 0,
            num_capsets: 5,
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
            "gpu: guest driver attempted to write device config (offset={:x}, len={:x})",
            offset,
            data.len()
        );
    }

    fn activate(&mut self, mem: GuestMemoryMmap) -> ActivateResult {
        if self.worker_thread.is_some() {
            panic!("virtio_fs: worker thread already exists");
        }

        if self.queues.len() != defs::NUM_QUEUES {
            error!(
                "Cannot perform activate. Expected {} queue(s), got {}",
                defs::NUM_QUEUES,
                self.queues.len()
            );
            return Err(ActivateError::BadActivate);
        }

        let event_idx: bool = (self.acked_features & (1 << VIRTIO_RING_F_EVENT_IDX)) != 0;
        self.queues[CTL_INDEX].set_event_idx(event_idx);
        self.queues[CUR_INDEX].set_event_idx(event_idx);
        let queue_ctl = Arc::new(Mutex::new(self.queues[CTL_INDEX].clone()));
        let queue_cur = Arc::new(Mutex::new(self.queues[CUR_INDEX].clone()));

        let shm_region = match self.shm_region.as_ref() {
            Some(s) => s.clone(),
            None => panic!("virtio_gpu: missing SHM region"),
        };

        let queue_evts = self
            .queue_events
            .iter()
            .map(|e| e.try_clone().unwrap())
            .collect();
        let worker = GpuWorker::new(
            queue_ctl,
            queue_cur,
            queue_evts,
            self.interrupt_status.clone(),
            self.interrupt_evt.try_clone().unwrap(),
            self.intc.clone(),
            self.irq_line,
            mem.clone(),
            shm_region,
            self.virgl_flags,
            self.worker_stopfd.try_clone().unwrap(),
            #[cfg(target_os = "macos")]
            self.map_sender.clone(),
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

    fn shm_region(&self) -> Option<&VirtioShmRegion> {
        debug!("virtio_gpu: GET_shm_region");
        self.shm_region.as_ref()
    }
}
