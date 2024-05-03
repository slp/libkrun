use std::io::Read;
use std::os::fd::AsRawFd;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};
use std::thread;

#[cfg(target_os = "macos")]
use crossbeam_channel::Sender;
#[cfg(target_os = "macos")]
use hvf::MemoryMapping;
use rutabaga_gfx::{
    ResourceCreate3D, ResourceCreateBlob, RutabagaFence, Transfer3D,
    RUTABAGA_PIPE_BIND_RENDER_TARGET, RUTABAGA_PIPE_TEXTURE_2D,
};
use utils::epoll::{ControlOperation, Epoll, EpollEvent, EventSet};
use utils::eventfd::EventFd;
use vm_memory::{GuestAddress, GuestMemoryMmap};

use super::super::descriptor_utils::{Reader, Writer};
use super::super::{GpuError, Queue, VirtioShmRegion, VIRTIO_MMIO_INT_VRING};
use super::device::{CTL_INDEX, CUR_INDEX};
use super::protocol::{
    virtio_gpu_ctrl_hdr, virtio_gpu_mem_entry, GpuCommand, GpuResponse, VirtioGpuResult,
};
use super::virtio_gpu::VirtioGpu;
use crate::legacy::Gic;
use crate::virtio::gpu::protocol::{VIRTIO_GPU_FLAG_FENCE, VIRTIO_GPU_FLAG_INFO_RING_IDX};
use crate::virtio::gpu::virtio_gpu::VirtioGpuRing;

pub struct GpuWorker {
    queue_ctl: Arc<Mutex<Queue>>,
    queue_cur: Arc<Mutex<Queue>>,
    queue_evts: Vec<EventFd>,
    interrupt_status: Arc<AtomicUsize>,
    interrupt_evt: EventFd,
    intc: Option<Arc<Mutex<Gic>>>,
    irq_line: Option<u32>,

    mem: GuestMemoryMmap,
    shm_region: VirtioShmRegion,
    virgl_flags: u32,
    stop_fd: EventFd,
    #[cfg(target_os = "macos")]
    map_sender: Sender<MemoryMapping>,
}

impl GpuWorker {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        queue_ctl: Arc<Mutex<Queue>>,
        queue_cur: Arc<Mutex<Queue>>,
        queue_evts: Vec<EventFd>,
        interrupt_status: Arc<AtomicUsize>,
        interrupt_evt: EventFd,
        intc: Option<Arc<Mutex<Gic>>>,
        irq_line: Option<u32>,
        mem: GuestMemoryMmap,
        shm_region: VirtioShmRegion,
        virgl_flags: u32,
        stop_fd: EventFd,
        #[cfg(target_os = "macos")] map_sender: Sender<MemoryMapping>,
    ) -> Self {
        Self {
            queue_ctl,
            queue_cur,
            queue_evts,
            interrupt_status,
            interrupt_evt,
            intc,
            irq_line,
            mem,
            shm_region,
            virgl_flags,
            stop_fd,
            #[cfg(target_os = "macos")]
            map_sender,
        }
    }

    pub fn run(self) -> thread::JoinHandle<()> {
        thread::spawn(|| self.work())
    }

    fn work(mut self) {
        let mut virtio_gpu = VirtioGpu::new(
            self.mem.clone(),
            self.queue_ctl.clone(),
            self.interrupt_status.clone(),
            self.interrupt_evt.try_clone().unwrap(),
            self.intc.clone(),
            self.irq_line,
            self.virgl_flags,
            #[cfg(target_os = "macos")]
            self.map_sender.clone(),
        );

        let virtq_ctl_ev_fd = self.queue_evts[CTL_INDEX].as_raw_fd();
        let virtq_cur_ev_fd = self.queue_evts[CUR_INDEX].as_raw_fd();
        let stop_ev_fd = self.stop_fd.as_raw_fd();

        let epoll = Epoll::new().unwrap();

        let _ = epoll.ctl(
            ControlOperation::Add,
            virtq_ctl_ev_fd,
            &EpollEvent::new(EventSet::IN, virtq_ctl_ev_fd as u64),
        );
        let _ = epoll.ctl(
            ControlOperation::Add,
            virtq_cur_ev_fd,
            &EpollEvent::new(EventSet::IN, virtq_cur_ev_fd as u64),
        );
        let _ = epoll.ctl(
            ControlOperation::Add,
            stop_ev_fd,
            &EpollEvent::new(EventSet::IN, stop_ev_fd as u64),
        );

        loop {
            let mut epoll_events = vec![EpollEvent::new(EventSet::empty(), 0); 32];
            match epoll.wait(epoll_events.len(), -1, epoll_events.as_mut_slice()) {
                Ok(ev_cnt) => {
                    for event in &epoll_events[0..ev_cnt] {
                        let source = event.fd();
                        let event_set = event.event_set();
                        match event_set {
                            EventSet::IN if source == virtq_ctl_ev_fd => {
                                self.handle_event(&mut virtio_gpu, CTL_INDEX);
                            }
                            EventSet::IN if source == virtq_cur_ev_fd => {
                                self.handle_event(&mut virtio_gpu, CUR_INDEX);
                            }
                            EventSet::IN if source == stop_ev_fd => {
                                debug!("stopping worker thread");
                                let _ = self.stop_fd.read();
                                return;
                            }
                            _ => {
                                log::warn!(
                                    "Received unknown event: {:?} from fd: {:?}",
                                    event_set,
                                    source
                                );
                            }
                        }
                    }
                }
                Err(e) => {
                    debug!("failed to consume muxer epoll event: {}", e);
                }
            }
        }
    }

    fn process_gpu_command(
        virtio_gpu: &mut VirtioGpu,
        mem: &GuestMemoryMmap,
        hdr: virtio_gpu_ctrl_hdr,
        cmd: GpuCommand,
        reader: &mut Reader,
        shm_region: &VirtioShmRegion,
    ) -> VirtioGpuResult {
        virtio_gpu.force_ctx_0();

        match cmd {
            GpuCommand::GetDisplayInfo(_) => {
                panic!("virtio_gpu: GpuCommand::GetDisplayInfo unimplemented");
            }
            GpuCommand::ResourceCreate2d(info) => {
                let resource_id = info.resource_id;

                let resource_create_3d = ResourceCreate3D {
                    target: RUTABAGA_PIPE_TEXTURE_2D,
                    format: info.format,
                    bind: RUTABAGA_PIPE_BIND_RENDER_TARGET,
                    width: info.width,
                    height: info.height,
                    depth: 1,
                    array_size: 1,
                    last_level: 0,
                    nr_samples: 0,
                    flags: 0,
                };

                virtio_gpu.resource_create_3d(resource_id, resource_create_3d)
            }
            GpuCommand::ResourceUnref(info) => virtio_gpu.unref_resource(info.resource_id),
            GpuCommand::SetScanout(_info) => {
                panic!("virtio_gpu: GpuCommand::SetScanout unimplemented");
            }
            GpuCommand::ResourceFlush(info) => virtio_gpu.flush_resource(info.resource_id),
            GpuCommand::TransferToHost2d(info) => {
                let resource_id = info.resource_id;
                let transfer = Transfer3D::new_2d(info.r.x, info.r.y, info.r.width, info.r.height);
                virtio_gpu.transfer_write(0, resource_id, transfer)
            }
            GpuCommand::ResourceAttachBacking(info) => {
                let available_bytes = reader.available_bytes();
                if available_bytes != 0 {
                    let entry_count = info.nr_entries as usize;
                    let mut vecs = Vec::with_capacity(entry_count);
                    for _ in 0..entry_count {
                        match reader.read_obj::<virtio_gpu_mem_entry>() {
                            Ok(entry) => {
                                let addr = GuestAddress(entry.addr);
                                let len = entry.length as usize;
                                vecs.push((addr, len))
                            }
                            Err(_) => return Err(GpuResponse::ErrUnspec),
                        }
                    }
                    virtio_gpu.attach_backing(info.resource_id, mem, vecs)
                } else {
                    error!("missing data for command {:?}", cmd);
                    Err(GpuResponse::ErrUnspec)
                }
            }
            GpuCommand::ResourceDetachBacking(info) => virtio_gpu.detach_backing(info.resource_id),
            GpuCommand::UpdateCursor(_info) => {
                panic!("virtio_gpu: GpuCommand:UpdateCursor unimplemented");
            }
            GpuCommand::MoveCursor(_info) => {
                panic!("virtio_gpu: GpuCommand::MoveCursor unimplemented");
            }
            GpuCommand::ResourceAssignUuid(info) => {
                let resource_id = info.resource_id;
                virtio_gpu.resource_assign_uuid(resource_id)
            }
            GpuCommand::GetCapsetInfo(info) => virtio_gpu.get_capset_info(info.capset_index),
            GpuCommand::GetCapset(info) => {
                virtio_gpu.get_capset(info.capset_id, info.capset_version)
            }

            GpuCommand::CtxCreate(info) => {
                let context_name: Option<String> = String::from_utf8(info.debug_name.to_vec()).ok();
                virtio_gpu.create_context(hdr.ctx_id, info.context_init, context_name.as_deref())
            }
            GpuCommand::CtxDestroy(_info) => virtio_gpu.destroy_context(hdr.ctx_id),
            GpuCommand::CtxAttachResource(info) => {
                virtio_gpu.context_attach_resource(hdr.ctx_id, info.resource_id)
            }
            GpuCommand::CtxDetachResource(info) => {
                virtio_gpu.context_detach_resource(hdr.ctx_id, info.resource_id)
            }
            GpuCommand::ResourceCreate3d(info) => {
                let resource_id = info.resource_id;
                let resource_create_3d = ResourceCreate3D {
                    target: info.target,
                    format: info.format,
                    bind: info.bind,
                    width: info.width,
                    height: info.height,
                    depth: info.depth,
                    array_size: info.array_size,
                    last_level: info.last_level,
                    nr_samples: info.nr_samples,
                    flags: info.flags,
                };

                virtio_gpu.resource_create_3d(resource_id, resource_create_3d)
            }
            GpuCommand::TransferToHost3d(info) => {
                let ctx_id = hdr.ctx_id;
                let resource_id = info.resource_id;

                let transfer = Transfer3D {
                    x: info.box_.x,
                    y: info.box_.y,
                    z: info.box_.z,
                    w: info.box_.w,
                    h: info.box_.h,
                    d: info.box_.d,
                    level: info.level,
                    stride: info.stride,
                    layer_stride: info.layer_stride,
                    offset: info.offset,
                };

                virtio_gpu.transfer_write(ctx_id, resource_id, transfer)
            }
            GpuCommand::TransferFromHost3d(info) => {
                let ctx_id = hdr.ctx_id;
                let resource_id = info.resource_id;

                let transfer = Transfer3D {
                    x: info.box_.x,
                    y: info.box_.y,
                    z: info.box_.z,
                    w: info.box_.w,
                    h: info.box_.h,
                    d: info.box_.d,
                    level: info.level,
                    stride: info.stride,
                    layer_stride: info.layer_stride,
                    offset: info.offset,
                };

                virtio_gpu.transfer_read(ctx_id, resource_id, transfer, None)
            }
            GpuCommand::CmdSubmit3d(info) => {
                if reader.available_bytes() != 0 {
                    let num_in_fences = info.num_in_fences as usize;
                    let cmd_size = info.size as usize;
                    let mut cmd_buf = vec![0; cmd_size];
                    let mut fence_ids: Vec<u64> = Vec::with_capacity(num_in_fences);

                    for _ in 0..num_in_fences {
                        match reader.read_obj::<u64>() {
                            Ok(fence_id) => {
                                fence_ids.push(fence_id);
                            }
                            Err(_) => return Err(GpuResponse::ErrUnspec),
                        }
                    }

                    if reader.read_exact(&mut cmd_buf[..]).is_ok() {
                        virtio_gpu.submit_command(hdr.ctx_id, &mut cmd_buf[..], &fence_ids)
                    } else {
                        Err(GpuResponse::ErrInvalidParameter)
                    }
                } else {
                    // Silently accept empty command buffers to allow for
                    // benchmarking.
                    Ok(GpuResponse::OkNoData)
                }
            }
            GpuCommand::ResourceCreateBlob(info) => {
                let resource_id = info.resource_id;
                let ctx_id = hdr.ctx_id;

                let resource_create_blob = ResourceCreateBlob {
                    blob_mem: info.blob_mem,
                    blob_flags: info.blob_flags,
                    blob_id: info.blob_id,
                    size: info.size,
                };

                let entry_count = info.nr_entries;
                if reader.available_bytes() == 0 && entry_count > 0 {
                    return Err(GpuResponse::ErrUnspec);
                }

                let mut vecs = Vec::with_capacity(entry_count as usize);
                for _ in 0..entry_count {
                    match reader.read_obj::<virtio_gpu_mem_entry>() {
                        Ok(entry) => {
                            let addr = GuestAddress(entry.addr);
                            let len = entry.length as usize;
                            vecs.push((addr, len))
                        }
                        Err(_) => return Err(GpuResponse::ErrUnspec),
                    }
                }

                virtio_gpu.resource_create_blob(
                    ctx_id,
                    resource_id,
                    resource_create_blob,
                    vecs,
                    mem,
                )
            }
            GpuCommand::SetScanoutBlob(_info) => {
                panic!("virtio_gpu: GpuCommand::SetScanoutBlob unimplemented");
            }
            GpuCommand::ResourceMapBlob(info) => {
                let resource_id = info.resource_id;
                let offset = info.offset;
                virtio_gpu.resource_map_blob(resource_id, shm_region, offset)
            }
            GpuCommand::ResourceUnmapBlob(info) => {
                let resource_id = info.resource_id;
                virtio_gpu.resource_unmap_blob(resource_id, shm_region)
            }
        }
    }

    fn handle_event(&mut self, virtio_gpu: &mut VirtioGpu, queue_index: usize) {
        debug!("gpu: queue event: {}", queue_index);
        if let Err(e) = self.queue_evts[queue_index].read() {
            error!("Failed to get queue event: {:?}", e);
        }

        let queue = match queue_index {
            CTL_INDEX => self.queue_ctl.clone(),
            CUR_INDEX => self.queue_cur.clone(),
            _ => panic!("gpu: unknown queue"),
        };

        loop {
            queue
                .lock()
                .unwrap()
                .disable_notification(&self.mem)
                .unwrap();

            debug!("processing queue");
            self.process_queue(virtio_gpu, &queue);
            debug!("after processing queue");

            if !queue
                .lock()
                .unwrap()
                .enable_notification(&self.mem)
                .unwrap()
            {
                break;
            }
        }
        debug!("unlocking queue");
    }

    pub fn process_queue(&mut self, virtio_gpu: &mut VirtioGpu, queue: &Arc<Mutex<Queue>>) {
        loop {
            let head = queue.lock().unwrap().pop(&self.mem);
            if let Some(head) = head {
                let mut reader = Reader::new(&self.mem, head.clone())
                    .map_err(GpuError::QueueReader)
                    .unwrap();
                let mut writer = Writer::new(&self.mem, head.clone())
                    .map_err(GpuError::QueueWriter)
                    .unwrap();

                let mut resp = Err(GpuResponse::ErrUnspec);
                let mut gpu_cmd = None;
                let mut ctrl_hdr = None;
                let mut len = 0;

                match GpuCommand::decode(&mut reader) {
                    Ok((hdr, cmd)) => {
                        resp = GpuWorker::process_gpu_command(
                            virtio_gpu,
                            &self.mem,
                            hdr,
                            cmd,
                            &mut reader,
                            &self.shm_region,
                        );
                        ctrl_hdr = Some(hdr);
                        gpu_cmd = Some(cmd);
                    }
                    Err(e) => debug!("descriptor decode error: {:?}", e),
                }

                let mut gpu_response = match resp {
                    Ok(gpu_response) => gpu_response,
                    Err(gpu_response) => {
                        debug!("{:?} -> {:?}", gpu_cmd, gpu_response);
                        gpu_response
                    }
                };

                let mut add_to_queue = true;

                if writer.available_bytes() != 0 {
                    let mut fence_id = 0;
                    let mut ctx_id = 0;
                    let mut flags = 0;
                    let mut ring_idx = 0;
                    if let Some(_cmd) = gpu_cmd {
                        let ctrl_hdr = ctrl_hdr.unwrap();
                        if ctrl_hdr.flags & VIRTIO_GPU_FLAG_FENCE != 0 {
                            flags = ctrl_hdr.flags;
                            fence_id = ctrl_hdr.fence_id;
                            ctx_id = ctrl_hdr.ctx_id;
                            ring_idx = ctrl_hdr.ring_idx;

                            let fence = RutabagaFence {
                                flags,
                                fence_id,
                                ctx_id,
                                ring_idx,
                            };
                            gpu_response = match virtio_gpu.create_fence(fence) {
                                Ok(_) => gpu_response,
                                Err(fence_resp) => {
                                    warn!("create_fence {} -> {:?}", fence_id, fence_resp);
                                    fence_resp
                                }
                            };
                        }
                    }

                    // Prepare the response now, even if it is going to wait until
                    // fence is complete.
                    match gpu_response.encode(flags, fence_id, ctx_id, ring_idx, &mut writer) {
                        Ok(l) => len = l,
                        Err(e) => debug!("ctrl queue response encode error: {:?}", e),
                    }

                    if flags & VIRTIO_GPU_FLAG_FENCE != 0 {
                        let ring = match flags & VIRTIO_GPU_FLAG_INFO_RING_IDX {
                            0 => VirtioGpuRing::Global,
                            _ => VirtioGpuRing::ContextSpecific { ctx_id, ring_idx },
                        };

                        add_to_queue = virtio_gpu.process_fence(ring, fence_id, head.index, len);
                    }
                }

                if add_to_queue {
                    if let Err(e) = queue.lock().unwrap().add_used(&self.mem, head.index, len) {
                        error!("failed to add used elements to the queue: {:?}", e);
                    }
                }

                if queue.lock().unwrap().needs_notification(&self.mem).unwrap() {
                    self.interrupt_status
                        .fetch_or(VIRTIO_MMIO_INT_VRING as usize, Ordering::SeqCst);
                    if let Some(intc) = &self.intc {
                        intc.lock().unwrap().set_irq(self.irq_line.unwrap());
                    } else if let Err(e) = self.interrupt_evt.write(1) {
                        error!("Failed to signal used queue: {:?}", e);
                    }
                }
            } else {
                break;
            }
        }
    }
}
