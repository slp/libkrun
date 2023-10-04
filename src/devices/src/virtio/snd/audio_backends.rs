// Manos Pitsidianakis <manos.pitsidianakis@linaro.org>
// SPDX-License-Identifier: Apache-2.0 or BSD-3-Clause

mod pipewire;

use std::sync::{Arc, Mutex};

use self::pipewire::PwBackend;

use super::stream::Stream;
use super::virtio_sound::VirtioSndPcmSetParams;
use super::BackendType;
use super::ControlMessage;
use super::Result;
use super::Vring;

pub trait AudioBackend {
    fn write(&self, stream_id: u32) -> Result<()>;

    fn read(&self, stream_id: u32) -> Result<()>;

    fn set_parameters(
        &mut self,
        _stream_id: u32,
        _msg: ControlMessage,
        _: VirtioSndPcmSetParams,
    ) -> Result<()> {
        Ok(())
    }

    fn prepare(&self, _stream_id: u32) -> Result<()> {
        Ok(())
    }

    fn release(&self, _stream_id: u32, _: ControlMessage) -> Result<()> {
        Ok(())
    }

    fn start(&self, _stream_id: u32) -> Result<()> {
        Ok(())
    }

    fn stop(&self, _stream_id: u32) -> Result<()> {
        Ok(())
    }
}

pub fn alloc_audio_backend(
    backend: BackendType,
    _vring_ctl: Arc<Mutex<Vring>>,
    _vring_txq: Arc<Mutex<Vring>>,
    streams: Arc<Mutex<Vec<Stream>>>,
) -> Result<Box<dyn AudioBackend + Send + Sync>> {
    log::trace!("allocating audio backend {:?}", backend);
    match backend {
        BackendType::Pipewire => Ok(Box::new(PwBackend::new(streams))),
    }
}
