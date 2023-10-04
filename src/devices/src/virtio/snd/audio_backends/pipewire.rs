// Pipewire backend device
// SPDX-License-Identifier: Apache-2.0 or BSD-3-Clause

use std::collections::VecDeque;
use std::thread;

use crate::virtio::snd::virtio_sound::VIRTIO_SND_S_OK;

use super::super::stream::Buffer;
use super::super::ControlMessage;
use super::super::Result;
use crossbeam_channel::unbounded;
use crossbeam_channel::Receiver;
use crossbeam_channel::Sender;
use vm_memory::{Address, Bytes};

use super::super::virtio_sound::{
    VirtioSndPcmSetParams, VIRTIO_SND_D_INPUT, VIRTIO_SND_D_OUTPUT, VIRTIO_SND_PCM_FMT_A_LAW,
    VIRTIO_SND_PCM_FMT_FLOAT, VIRTIO_SND_PCM_FMT_FLOAT64, VIRTIO_SND_PCM_FMT_MU_LAW,
    VIRTIO_SND_PCM_FMT_S16, VIRTIO_SND_PCM_FMT_S18_3, VIRTIO_SND_PCM_FMT_S20,
    VIRTIO_SND_PCM_FMT_S20_3, VIRTIO_SND_PCM_FMT_S24, VIRTIO_SND_PCM_FMT_S24_3,
    VIRTIO_SND_PCM_FMT_S32, VIRTIO_SND_PCM_FMT_S8, VIRTIO_SND_PCM_FMT_U16,
    VIRTIO_SND_PCM_FMT_U18_3, VIRTIO_SND_PCM_FMT_U20, VIRTIO_SND_PCM_FMT_U20_3,
    VIRTIO_SND_PCM_FMT_U24, VIRTIO_SND_PCM_FMT_U24_3, VIRTIO_SND_PCM_FMT_U32,
    VIRTIO_SND_PCM_FMT_U8, VIRTIO_SND_PCM_RATE_11025, VIRTIO_SND_PCM_RATE_16000,
    VIRTIO_SND_PCM_RATE_176400, VIRTIO_SND_PCM_RATE_192000, VIRTIO_SND_PCM_RATE_22050,
    VIRTIO_SND_PCM_RATE_32000, VIRTIO_SND_PCM_RATE_384000, VIRTIO_SND_PCM_RATE_44100,
    VIRTIO_SND_PCM_RATE_48000, VIRTIO_SND_PCM_RATE_5512, VIRTIO_SND_PCM_RATE_64000,
    VIRTIO_SND_PCM_RATE_8000, VIRTIO_SND_PCM_RATE_88200, VIRTIO_SND_PCM_RATE_96000,
    VIRTIO_SND_S_BAD_MSG, VIRTIO_SND_S_NOT_SUPP,
};
use super::super::Error;
use super::AudioBackend;
use super::Stream;
use std::sync::Mutex;
use std::{collections::HashMap, mem::size_of, ops::Deref, ptr, ptr::NonNull, rc::Rc, sync::Arc};

use log::debug;
use spa::param::{audio::AudioFormat, audio::AudioInfoRaw, ParamType};
use spa::pod::{serialize::PodSerializer, Object, Pod, Value};

use spa::sys::{
    spa_audio_info_raw, SPA_PARAM_EnumFormat, SPA_TYPE_OBJECT_Format, SPA_AUDIO_CHANNEL_FC,
    SPA_AUDIO_CHANNEL_FL, SPA_AUDIO_CHANNEL_FR, SPA_AUDIO_CHANNEL_LFE, SPA_AUDIO_CHANNEL_MONO,
    SPA_AUDIO_CHANNEL_RC, SPA_AUDIO_CHANNEL_RL, SPA_AUDIO_CHANNEL_RR, SPA_AUDIO_CHANNEL_UNKNOWN,
    SPA_AUDIO_FORMAT_ALAW, SPA_AUDIO_FORMAT_F32, SPA_AUDIO_FORMAT_F64, SPA_AUDIO_FORMAT_S16,
    SPA_AUDIO_FORMAT_S18_LE, SPA_AUDIO_FORMAT_S20, SPA_AUDIO_FORMAT_S20_LE, SPA_AUDIO_FORMAT_S24,
    SPA_AUDIO_FORMAT_S24_LE, SPA_AUDIO_FORMAT_S32, SPA_AUDIO_FORMAT_S8, SPA_AUDIO_FORMAT_U16,
    SPA_AUDIO_FORMAT_U18_LE, SPA_AUDIO_FORMAT_U20, SPA_AUDIO_FORMAT_U20_LE, SPA_AUDIO_FORMAT_U24,
    SPA_AUDIO_FORMAT_U24_LE, SPA_AUDIO_FORMAT_U32, SPA_AUDIO_FORMAT_U8, SPA_AUDIO_FORMAT_ULAW,
    SPA_AUDIO_FORMAT_UNKNOWN,
};

use pw::sys::{
    pw_loop, pw_thread_loop, pw_thread_loop_get_loop, pw_thread_loop_lock, pw_thread_loop_new,
    pw_thread_loop_signal, pw_thread_loop_start, pw_thread_loop_unlock, pw_thread_loop_wait,
    PW_ID_CORE,
};
use pw::{properties, spa, LoopRef};

struct PwThreadLoop(NonNull<pw_thread_loop>);

impl PwThreadLoop {
    pub fn new(name: Option<&str>) -> Option<Self> {
        let inner = unsafe {
            pw_thread_loop_new(
                name.map_or(ptr::null(), |p| p.as_ptr() as *const _),
                std::ptr::null_mut(),
            )
        };
        if inner.is_null() {
            None
        } else {
            Some(Self(
                NonNull::new(inner).expect("pw_thread_loop can't be null"),
            ))
        }
    }

    pub fn get_loop(&self) -> PwInnerLoop {
        let inner = unsafe { pw_thread_loop_get_loop(self.0.as_ptr()) };
        PwInnerLoop {
            inner: Rc::new(NonNull::new(inner).unwrap()),
        }
    }

    pub fn unlock(&self) {
        unsafe { pw_thread_loop_unlock(self.0.as_ptr()) }
    }

    pub fn lock(&self) {
        unsafe { pw_thread_loop_lock(self.0.as_ptr()) }
    }

    pub fn start(&self) {
        unsafe {
            pw_thread_loop_start(self.0.as_ptr());
        }
    }

    pub fn signal(&self) {
        unsafe {
            pw_thread_loop_signal(self.0.as_ptr(), false);
        }
    }

    pub fn wait(&self) {
        unsafe {
            pw_thread_loop_wait(self.0.as_ptr());
        }
    }
}

#[derive(Debug, Clone)]
struct PwInnerLoop {
    inner: Rc<NonNull<pw_loop>>,
}

impl AsRef<LoopRef> for PwInnerLoop {
    fn as_ref(&self) -> &LoopRef {
        self.deref()
    }
}

impl Deref for PwInnerLoop {
    type Target = LoopRef;

    fn deref(&self) -> &Self::Target {
        unsafe { &*(self.inner.as_ptr() as *mut LoopRef) }
    }
}

// SAFETY: Safe as the structure can be sent to another thread.
unsafe impl Send for PwBackend {}

// SAFETY: Safe as the structure can be shared with another thread as the state
// is protected with a lock.
unsafe impl Sync for PwBackend {}

#[derive(Debug)]
enum PwAction {
    SetParameters(usize, ControlMessage, VirtioSndPcmSetParams),
    Prepare(usize),
    Release(usize, ControlMessage),
    Start(usize),
    Stop(usize),
    Write(usize),
    Read(usize),
}

pub struct PwBackend {
    sender: Arc<Mutex<Sender<PwAction>>>,
}

impl PwBackend {
    pub fn new(streams: Arc<Mutex<Vec<Stream>>>) -> Self {
        let (sender, receiver): (Sender<PwAction>, Receiver<PwAction>) = unbounded();
        let sender = Arc::new(Mutex::new(sender));

        thread::spawn(move || {
            if let Err(err) = Self::run(streams, receiver) {
                log::error!("Main thread exited with error: {}", err);
            }
        });

        Self { sender }
    }

    fn run(streams_mutex: Arc<Mutex<Vec<Stream>>>, receiver: Receiver<PwAction>) -> Result<()> {
        pw::init();

        let thread_loop = Rc::new(PwThreadLoop::new(Some("Pipewire thread loop")).unwrap());
        let get_loop = thread_loop.get_loop();

        thread_loop.lock();

        let context = pw::Context::new(&get_loop).expect("failed to create context");
        thread_loop.start();
        let core = context.connect(None).expect("Failed to connect to core");

        // Create new reference for the variable so that it can be moved into the closure.
        let thread_clone = thread_loop.clone();

        // Trigger the sync event. The server's answer won't be processed until we start the thread loop,
        // so we can safely do this before setting up a callback. This lets us avoid using a Cell.
        let pending = core.sync(0).expect("sync failed");
        let _listener_core = core
            .add_listener_local()
            .done(move |id, seq| {
                if id == PW_ID_CORE && seq == pending {
                    thread_clone.signal();
                }
            })
            .register();

        thread_loop.wait();
        thread_loop.unlock();

        let mut ready_buffers: Arc<Mutex<VecDeque<Buffer>>> = Arc::new(Mutex::new(VecDeque::new()));

        log::trace!("pipewire backend running");

        let stream_hash: Mutex<HashMap<usize, pw::stream::Stream>> = Mutex::new(HashMap::new());
        let stream_listener: Mutex<HashMap<usize, pw::stream::StreamListener<i32>>> =
            Mutex::new(HashMap::new());

        while let Ok(action) = receiver.recv() {
            match action {
                PwAction::Read(_) => {}
                PwAction::Write(stream_id) => {
                    let mut streams = streams_mutex.lock().unwrap();
                    let stream = streams.get_mut(stream_id as usize).unwrap();
                    for b in std::mem::take(&mut stream.buffers) {
                        ready_buffers.lock().unwrap().push_back(b);
                    }
                }
                PwAction::Start(stream_id) => {
                    debug!("pipewire start");
                    let start_result = streams_mutex.lock().unwrap()[stream_id as usize]
                        .state
                        .start();
                    if let Err(err) = start_result {
                        // log the error and continue
                        log::error!("Stream {} start {}", stream_id, err);
                    } else {
                        thread_loop.lock();
                        let stream_hash = stream_hash.lock().unwrap();
                        let Some(stream) = stream_hash.get(&stream_id) else {
                            continue;
                        };
                        stream.set_active(true).expect("could not start stream");
                        thread_loop.unlock();
                    }
                }
                PwAction::Stop(stream_id) => {
                    debug!("pipewire stop");
                    let stop_result = streams_mutex.lock().unwrap()[stream_id as usize]
                        .state
                        .stop();
                    if let Err(err) = stop_result {
                        log::error!("Stream {} stop {}", stream_id, err);
                    } else {
                        thread_loop.lock();
                        let stream_hash = stream_hash.lock().unwrap();
                        let Some(stream) = stream_hash.get(&stream_id) else {
                            continue;
                        };
                        stream.set_active(false).expect("could not stop stream");
                        thread_loop.unlock();
                    }
                }
                PwAction::Prepare(stream_id) => {
                    debug!("pipewire prepare");
                    let prepare_result = streams_mutex.lock().unwrap()[stream_id as usize]
                        .state
                        .prepare();
                    if let Err(err) = prepare_result {
                        log::error!("Stream {} prepare {}", stream_id, err);
                    } else {
                        let mut stream_hash = stream_hash.lock().unwrap();
                        let mut stream_listener = stream_listener.lock().unwrap();
                        thread_loop.lock();
                        let streams = streams_mutex.lock().unwrap();

                        let params = &streams[stream_id as usize].params;

                        let mut pos: [u32; 64] = [SPA_AUDIO_CHANNEL_UNKNOWN; 64];

                        match params.channels {
                            6 => {
                                pos[0] = SPA_AUDIO_CHANNEL_FL;
                                pos[1] = SPA_AUDIO_CHANNEL_FR;
                                pos[2] = SPA_AUDIO_CHANNEL_FC;
                                pos[3] = SPA_AUDIO_CHANNEL_LFE;
                                pos[4] = SPA_AUDIO_CHANNEL_RL;
                                pos[5] = SPA_AUDIO_CHANNEL_RR;
                            }
                            5 => {
                                pos[0] = SPA_AUDIO_CHANNEL_FL;
                                pos[1] = SPA_AUDIO_CHANNEL_FR;
                                pos[2] = SPA_AUDIO_CHANNEL_FC;
                                pos[3] = SPA_AUDIO_CHANNEL_LFE;
                                pos[4] = SPA_AUDIO_CHANNEL_RC;
                            }
                            4 => {
                                pos[0] = SPA_AUDIO_CHANNEL_FL;
                                pos[1] = SPA_AUDIO_CHANNEL_FR;
                                pos[2] = SPA_AUDIO_CHANNEL_FC;
                                pos[3] = SPA_AUDIO_CHANNEL_RC;
                            }
                            3 => {
                                pos[0] = SPA_AUDIO_CHANNEL_FL;
                                pos[1] = SPA_AUDIO_CHANNEL_FR;
                                pos[2] = SPA_AUDIO_CHANNEL_LFE;
                            }
                            2 => {
                                pos[0] = SPA_AUDIO_CHANNEL_FL;
                                pos[1] = SPA_AUDIO_CHANNEL_FR;
                            }
                            1 => {
                                pos[0] = SPA_AUDIO_CHANNEL_MONO;
                            }
                            _ => {
                                return Err(Error::ChannelNotSupported(params.channels));
                            }
                        }

                        let info = spa_audio_info_raw {
                            format: match params.format {
                                VIRTIO_SND_PCM_FMT_MU_LAW => SPA_AUDIO_FORMAT_ULAW,
                                VIRTIO_SND_PCM_FMT_A_LAW => SPA_AUDIO_FORMAT_ALAW,
                                VIRTIO_SND_PCM_FMT_S8 => SPA_AUDIO_FORMAT_S8,
                                VIRTIO_SND_PCM_FMT_U8 => SPA_AUDIO_FORMAT_U8,
                                VIRTIO_SND_PCM_FMT_S16 => SPA_AUDIO_FORMAT_S16,
                                VIRTIO_SND_PCM_FMT_U16 => SPA_AUDIO_FORMAT_U16,
                                VIRTIO_SND_PCM_FMT_S18_3 => SPA_AUDIO_FORMAT_S18_LE,
                                VIRTIO_SND_PCM_FMT_U18_3 => SPA_AUDIO_FORMAT_U18_LE,
                                VIRTIO_SND_PCM_FMT_S20_3 => SPA_AUDIO_FORMAT_S20_LE,
                                VIRTIO_SND_PCM_FMT_U20_3 => SPA_AUDIO_FORMAT_U20_LE,
                                VIRTIO_SND_PCM_FMT_S24_3 => SPA_AUDIO_FORMAT_S24_LE,
                                VIRTIO_SND_PCM_FMT_U24_3 => SPA_AUDIO_FORMAT_U24_LE,
                                VIRTIO_SND_PCM_FMT_S20 => SPA_AUDIO_FORMAT_S20,
                                VIRTIO_SND_PCM_FMT_U20 => SPA_AUDIO_FORMAT_U20,
                                VIRTIO_SND_PCM_FMT_S24 => SPA_AUDIO_FORMAT_S24,
                                VIRTIO_SND_PCM_FMT_U24 => SPA_AUDIO_FORMAT_U24,
                                VIRTIO_SND_PCM_FMT_S32 => SPA_AUDIO_FORMAT_S32,
                                VIRTIO_SND_PCM_FMT_U32 => SPA_AUDIO_FORMAT_U32,
                                VIRTIO_SND_PCM_FMT_FLOAT => SPA_AUDIO_FORMAT_F32,
                                VIRTIO_SND_PCM_FMT_FLOAT64 => SPA_AUDIO_FORMAT_F64,
                                _ => SPA_AUDIO_FORMAT_UNKNOWN,
                            },
                            rate: match params.rate {
                                VIRTIO_SND_PCM_RATE_5512 => 5512,
                                VIRTIO_SND_PCM_RATE_8000 => 8000,
                                VIRTIO_SND_PCM_RATE_11025 => 11025,
                                VIRTIO_SND_PCM_RATE_16000 => 16000,
                                VIRTIO_SND_PCM_RATE_22050 => 22050,
                                VIRTIO_SND_PCM_RATE_32000 => 32000,
                                VIRTIO_SND_PCM_RATE_44100 => 44100,
                                VIRTIO_SND_PCM_RATE_48000 => 48000,
                                VIRTIO_SND_PCM_RATE_64000 => 64000,
                                VIRTIO_SND_PCM_RATE_88200 => 88200,
                                VIRTIO_SND_PCM_RATE_96000 => 96000,
                                VIRTIO_SND_PCM_RATE_176400 => 176400,
                                VIRTIO_SND_PCM_RATE_192000 => 192000,
                                VIRTIO_SND_PCM_RATE_384000 => 384000,
                                _ => 44100,
                            },
                            flags: 0,
                            channels: params.channels as u32,
                            position: pos,
                        };

                        let mut audio_info = AudioInfoRaw::new();
                        audio_info.set_format(AudioFormat::S16LE);
                        audio_info.set_rate(info.rate);
                        audio_info.set_channels(info.channels);

                        let values: Vec<u8> = PodSerializer::serialize(
                            std::io::Cursor::new(Vec::new()),
                            &Value::Object(Object {
                                type_: SPA_TYPE_OBJECT_Format,
                                id: SPA_PARAM_EnumFormat,
                                properties: audio_info.into(),
                            }),
                        )
                        .unwrap()
                        .0
                        .into_inner();

                        let value_clone = values.clone();

                        let mut param = [Pod::from_bytes(&values).unwrap()];

                        let props = properties! {
                            *pw::keys::MEDIA_TYPE => "Audio",
                            *pw::keys::MEDIA_CATEGORY => "Playback",
                        };

                        let stream = pw::stream::Stream::new(&core, "audio-output", props)
                            .expect("could not create new stream");

                        let listener_streams_mutex = streams_mutex.clone();
                        let listener_ready_buffers = ready_buffers.clone();

                        let listener_stream = stream
                            .add_local_listener()
                            .state_changed(|old, new| {
                                debug!("State changed: {:?} -> {:?}", old, new);
                            })
                            .param_changed(move |stream, id, _data, param| {
                                let Some(_param) = param else {
                                    return;
                                };
                                if id != ParamType::Format.as_raw() {
                                    return;
                                }
                                let mut param = [Pod::from_bytes(&value_clone).unwrap()];

                                //callback to negotiate new set of streams
                                stream
                                    .update_params(&mut param)
                                    .expect("could not update params");
                            })
                            .process(move |stream, _data| match stream.dequeue_buffer() {
                                None => debug!("No buffer recieved"),
                                Some(mut buf) => {
                                    let datas = buf.datas_mut();
                                    let frame_size = info.channels as u32 * size_of::<i16>() as u32;
                                    let data = &mut datas[0];
                                    let n_bytes = if let Some(slice) = data.data() {
                                        let mut streams = listener_streams_mutex.lock().unwrap();
                                        let streams = streams
                                            .get_mut(stream_id as usize)
                                            .expect("Stream does not exist");
                                        let mut buffers = listener_ready_buffers.lock().unwrap();

                                        let n_bytes =
                                            streams.params.period_bytes.to_native() as usize;
                                        let mut total_read = 0;
                                        while total_read < n_bytes {
                                            let Some(buffer) = buffers.front_mut() else {
                                                return;
                                            };

                                            let mut to_read = n_bytes - total_read;
                                            let buf_len =
                                                buffer.message.data_len as usize - buffer.pos;

                                            if to_read > buf_len {
                                                to_read = buf_len;
                                            }

                                            let p = &mut slice
                                                [total_read..total_read + to_read as usize];

                                            let mut buf = vec![0; to_read];
                                            let bytes_read = buffer
                                                .message
                                                .mem
                                                .read(
                                                    &mut buf,
                                                    buffer
                                                        .message
                                                        .data_addr
                                                        .checked_add(buffer.pos as u64)
                                                        .unwrap(),
                                                )
                                                .unwrap();
                                            assert!(bytes_read == to_read);

                                            let slice =
                                                &buf[buffer.pos..buffer.pos + to_read as usize];
                                            p.copy_from_slice(&slice);

                                            total_read += to_read;

                                            if to_read == buf_len {
                                                buffers.pop_front();
                                            } else {
                                                buffer.pos += to_read;
                                            }
                                        }
                                        total_read
                                    } else {
                                        0
                                    };
                                    let chunk = data.chunk_mut();
                                    *chunk.offset_mut() = 0;
                                    *chunk.stride_mut() = frame_size as _;
                                    *chunk.size_mut() = n_bytes as _;
                                }
                            })
                            .register()
                            .expect("failed to register stream listener");

                        stream_listener.insert(stream_id, listener_stream);

                        let direction = match streams[stream_id as usize].direction {
                            VIRTIO_SND_D_OUTPUT => spa::Direction::Output,
                            VIRTIO_SND_D_INPUT => spa::Direction::Input,
                            _ => panic!("Invalid direction"),
                        };

                        stream
                            .connect(
                                direction,
                                Some(pw::constants::ID_ANY),
                                pw::stream::StreamFlags::RT_PROCESS
                                    | pw::stream::StreamFlags::AUTOCONNECT
                                    | pw::stream::StreamFlags::INACTIVE
                                    | pw::stream::StreamFlags::MAP_BUFFERS,
                                &mut param,
                            )
                            .expect("could not connect to the stream");

                        // insert created stream in a hash table
                        stream_hash.insert(stream_id, stream);

                        thread_loop.unlock();
                    }
                }
                PwAction::Release(stream_id, mut msg) => {
                    let release_result = streams_mutex.lock().unwrap()[stream_id as usize]
                        .state
                        .release();
                    if let Err(err) = release_result {
                        log::error!("Stream {} release {}", stream_id, err);
                        msg.code = VIRTIO_SND_S_BAD_MSG;
                    } else {
                        thread_loop.lock();
                        let mut stream_hash = stream_hash.lock().unwrap();
                        let mut stream_listener = stream_listener.lock().unwrap();
                        let st_buffer = &mut streams_mutex.lock().unwrap();

                        let Some(stream) = stream_hash.get(&stream_id) else {
                            continue;
                        };
                        stream.disconnect().expect("could not disconnect stream");
                        std::mem::take(&mut st_buffer[stream_id as usize].buffers);
                        std::mem::take(&mut ready_buffers);
                        stream_hash.remove(&stream_id);
                        stream_listener.remove(&stream_id);

                        thread_loop.unlock();
                    }
                }
                PwAction::SetParameters(stream_id, _msg, request) => {
                    let mut _code = VIRTIO_SND_S_OK;

                    let stream_clone = streams_mutex.clone();
                    let mut streams = stream_clone.lock().unwrap();
                    let st = streams
                        .get_mut(stream_id as usize)
                        .expect("Stream does not exist");

                    if let Err(err) = st.state.set_parameters() {
                        log::error!("Stream {} set_parameters {}", stream_id, err);
                        _code = VIRTIO_SND_S_BAD_MSG;
                    } else if !st.supports_format(request.format) || !st.supports_rate(request.rate)
                    {
                        _code = VIRTIO_SND_S_NOT_SUPP;
                    } else {
                        st.params.features = request.features;
                        st.params.buffer_bytes = request.buffer_bytes;
                        st.params.period_bytes = request.period_bytes;
                        st.params.channels = request.channels;
                        st.params.format = request.format;
                        st.params.rate = request.rate;
                    }
                }
            }
        }
        Ok(())
    }
}

macro_rules! send_action {
    ($($fn_name:ident $action:tt),+$(,)?) => {
        $(
            fn $fn_name(&self, id: u32) -> Result<()> {
                self.sender
                    .lock()
                    .unwrap()
                    .send(PwAction::$action(id as usize))
                    .unwrap();
                Ok(())
            }
        )*
    };
    ($(ctrl $fn_name:ident $action:tt),+$(,)?) => {
        $(
            fn $fn_name(&self, id: u32, msg: ControlMessage) -> Result<()> {
                self.sender
                    .lock()
                    .unwrap()
                    .send(PwAction::$action(id as usize, msg))
                    .unwrap();
                Ok(())
            }
        )*
    };
    ($(ctrl_p $fn_name:ident $action:tt),+$(,)?) => {
        $(
            fn $fn_name(&mut self, id: u32, msg: ControlMessage, request: VirtioSndPcmSetParams) -> Result<()> {
                self.sender
                    .lock()
                    .unwrap()
                    .send(PwAction::$action(id as usize, msg, request))
                    .unwrap();
                Ok(())
            }
        )*
    }
}

impl AudioBackend for PwBackend {
    send_action! {
        write Write,
        read Read,
        prepare Prepare,
        start Start,
        stop Stop,
    }
    send_action! {
        ctrl release Release,
    }
    send_action! {
        ctrl_p set_parameters SetParameters,
    }
}
