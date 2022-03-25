use std::collections::HashMap;
use std::os::unix::io::{AsRawFd, RawFd};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex, RwLock};

use nix::sys::socket::{IpAddr, Ipv4Addr, SockAddr};

use super::super::Queue as VirtQueue;
use super::defs;
use super::defs::uapi;
use super::muxer_rxq::{rx_to_pkt, MuxerRxQ};
use super::muxer_thread::MuxerThread;
use super::packet::{
    TsiConnectReq, TsiConnectRsp, TsiGetnameReq, TsiGetnameRsp, TsiProxyCreate, VsockPacket,
};
use super::proxy::{Proxy, ProxyError};
use super::tcp::TcpProxy;
use super::udp::UdpProxy;
use super::VsockError;
use utils::epoll::{ControlOperation, Epoll, EpollEvent, EventSet};
use utils::eventfd::EventFd;
use vm_memory::GuestMemoryMmap;

pub type ProxyMap = Arc<RwLock<HashMap<u64, Mutex<Box<dyn Proxy>>>>>;
//pub type TcpProxyMap = Arc<RwLock<HashMap<u64, Mutex<TcpProxy>>>>;
//pub type UdpProxyMap = Arc<RwLock<HashMap<u64, Mutex<UdpProxy>>>>;

/// A muxer RX queue item.
#[derive(Debug)]
pub enum MuxerRx {
    Reset {
        local_port: u32,
        peer_port: u32,
    },
    GetnameResponse {
        local_port: u32,
        peer_port: u32,
        data: TsiGetnameRsp,
    },
    ConnResponse {
        local_port: u32,
        peer_port: u32,
        result: i32,
    },
    OpResponse {
        local_port: u32,
        peer_port: u32,
    },
    CreditRequest {
        local_port: u32,
        peer_port: u32,
        fwd_cnt: u32,
    },
    CreditUpdate {
        local_port: u32,
        peer_port: u32,
        fwd_cnt: u32,
    },
}

pub struct VsockMuxer {
    cid: u64,
    rxq_stream: Arc<Mutex<MuxerRxQ>>,
    rxq_dgram: Arc<Mutex<MuxerRxQ>>,
    epoll: Epoll,
    interrupt_evt: EventFd,
    interrupt_status: Arc<AtomicUsize>,
    proxy_map: ProxyMap,
    //tcp_proxy_map: TcpProxyMap,
    //udp_proxy_map: UdpProxyMap,
}

impl VsockMuxer {
    pub(crate) fn new(
        cid: u64,
        interrupt_evt: EventFd,
        interrupt_status: Arc<AtomicUsize>,
    ) -> Self {
        VsockMuxer {
            cid,
            rxq_stream: Arc::new(Mutex::new(MuxerRxQ::new())),
            rxq_dgram: Arc::new(Mutex::new(MuxerRxQ::new())),
            epoll: Epoll::new().unwrap(),
            interrupt_evt,
            interrupt_status,
            proxy_map: Arc::new(RwLock::new(HashMap::new())),
            //tcp_proxy_map: Arc::new(RwLock::new(HashMap::new())),
            //udp_proxy_map: Arc::new(RwLock::new(HashMap::new())),
        }
    }

    pub(crate) fn activate(
        &mut self,
        mem: GuestMemoryMmap,
        queue_rx: Arc<Mutex<VirtQueue>>,
        queue_dr: Arc<Mutex<VirtQueue>>,
    ) {
        let thread = MuxerThread::new(
            self.epoll.clone(),
            self.rxq_stream.clone(),
            //self.tcp_proxy_map.clone(),
            //self.udp_proxy_map.clone(),
            self.proxy_map.clone(),
            mem,
            queue_rx,
            queue_dr,
            self.interrupt_evt.try_clone().unwrap(),
            self.interrupt_status.clone(),
        );
        thread.run();
    }

    pub(crate) fn has_pending_stream_rx(&self) -> bool {
        !self.rxq_stream.lock().unwrap().is_empty()
    }

    pub(crate) fn has_pending_dgram_rx(&self) -> bool {
        !self.rxq_dgram.lock().unwrap().is_empty()
    }

    pub(crate) fn recv_stream_pkt(&mut self, pkt: &mut VsockPacket) -> super::Result<()> {
        debug!("vsock: recv_stream_pkt");
        if self.rxq_stream.lock().unwrap().is_empty() {
            return Err(VsockError::NoData);
        }

        if let Some(rx) = self.rxq_stream.lock().unwrap().pop() {
            rx_to_pkt(self.cid, rx, pkt);
        }

        Ok(())
    }

    pub(crate) fn recv_dgram_pkt(&mut self, pkt: &mut VsockPacket) -> super::Result<()> {
        debug!("vsock: recv_dgram_pkt");
        if self.rxq_dgram.lock().unwrap().is_empty() {
            return Err(VsockError::NoData);
        }

        if let Some(rx) = self.rxq_dgram.lock().unwrap().pop() {
            rx_to_pkt(self.cid, rx, pkt);
        }

        Ok(())
    }

    pub fn update_polling(&self, id: u64, fd: RawFd, evset: EventSet) {
        debug!("update_polling id={} fd={:?}", id, fd);
        let _ = self
            .epoll
            .ctl(ControlOperation::Delete, fd, &EpollEvent::default());
        if !evset.is_empty() {
            self.epoll
                .ctl(
                    ControlOperation::Add,
                    fd,
                    &EpollEvent::new(evset, id as u64),
                )
                .unwrap();
        }
    }

    pub(crate) fn send_stream_pkt(&mut self, pkt: &VsockPacket) -> super::Result<()> {
        debug!(
            "vsock: send_pkt: src_port={} dst_port={}, op={}",
            pkt.src_port(),
            pkt.dst_port(),
            pkt.op()
        );

        if pkt.dst_cid() != uapi::VSOCK_HOST_CID {
            debug!(
                "vsock: dropping guest packet for unknown CID: {:?}",
                pkt.hdr()
            );
            return Ok(());
        }

        match pkt.op() {
            uapi::VSOCK_OP_REQUEST => {
                debug!("vsock: OP_REQUEST");
                self.proxy_map
                    .read()
                    .unwrap()
                    .get(&(pkt.src_port() as u64))
                    .map(|proxy| proxy.lock().unwrap().confirm_connect(pkt));
            }
            uapi::VSOCK_OP_SHUTDOWN => {
                debug!("vsock: OP_SHUTDOWN");
                self.proxy_map
                    .read()
                    .unwrap()
                    .get(&(pkt.src_port() as u64))
                    .map(|proxy| proxy.lock().unwrap().shutdown(pkt));
            }
            uapi::VSOCK_OP_RW => {
                debug!("vsock: OP_RW");
                if let Some(proxy_lock) =
                    self.proxy_map.read().unwrap().get(&(pkt.src_port() as u64))
                {
                    debug!("vsock: allowing OP_RW for {}", pkt.src_port());
                    let mut proxy = proxy_lock.lock().unwrap();
                    proxy.sendmsg(pkt);
                } else {
                    debug!("vsock: invalid OP_RW for {}, sending reset", pkt.src_port());
                    self.rxq_stream.lock().unwrap().push(MuxerRx::Reset {
                        local_port: pkt.dst_port(),
                        peer_port: pkt.src_port(),
                    });
                }
            }
            uapi::VSOCK_OP_CREDIT_UPDATE => {
                debug!("vsock: OP_CREDIT_UPDATE");
                let update = self
                    .proxy_map
                    .read()
                    .unwrap()
                    .get(&(pkt.src_port() as u64))
                    .map(|proxy| proxy.lock().unwrap().update_peer_credit(pkt));

                update
                    .and_then(|u| u.polling)
                    .map(|p| self.update_polling(p.0, p.1, p.2));
            }
            _ => error!("stream: unhandled op={}", pkt.op()),
        }
        Ok(())
    }

    pub(crate) fn send_dgram_pkt(&mut self, pkt: &VsockPacket) -> super::Result<()> {
        debug!(
            "vsock: send_dgram_pkt: src_port={} dst_port={}",
            pkt.src_port(),
            pkt.dst_port()
        );

        if pkt.dst_cid() != uapi::VSOCK_HOST_CID {
            debug!(
                "vsock: dropping guest packet for unknown CID: {:?}",
                pkt.hdr()
            );
            return Ok(());
        }

        if pkt.dst_port() == 1024 {
            debug!("vsock: proxy create request");
            if let Some(req) = pkt.read_proxy_create() {
                debug!(
                    "vsock: proxy create request: id={}, type={}",
                    req.id, req._type
                );
                match req._type {
                    defs::SOCK_STREAM => {
                        debug!("vsock: proxy create stream");
                        TcpProxy::new(
                            req.id,
                            self.cid,
                            pkt.src_port(),
                            self.rxq_stream.clone(),
                            self.rxq_dgram.clone(),
                        )
                        .map(|proxy| {
                            self.proxy_map
                                .write()
                                .unwrap()
                                .insert(req.id, Mutex::new(Box::new(proxy)))
                        })
                        .map_err(|e| debug!("vsock: error creating socket: {}", e));
                    }
                    defs::SOCK_DGRAM => {
                        debug!("vsock: proxy create dgram");
                        UdpProxy::new(
                            req.id,
                            self.cid,
                            pkt.src_port(),
                            pkt.dst_port(),
                            self.epoll.clone(),
                            self.rxq_dgram.clone(),
                        )
                        .map(|proxy| {
                            self.proxy_map
                                .write()
                                .unwrap()
                                .insert(req.id, Mutex::new(Box::new(proxy)))
                        })
                        .map_err(|e| debug!("vsock: error creating socket: {}", e));
                    }
                    _ => debug!("vsock: unknown type on connection request"),
                };
            }
        } else if pkt.dst_port() == 1025 {
            debug!("vsock: proxy connect request");
            if let Some(req) = pkt.read_connect_req() {
                debug!("vsock: proxy connect request: id={}", req.id);
                let update = self
                    .proxy_map
                    .read()
                    .unwrap()
                    .get(&req.id)
                    .map(|proxy| proxy.lock().unwrap().connect(pkt, req));

                update
                    .and_then(|u| u.polling)
                    .map(|p| self.update_polling(p.0, p.1, p.2));
            }
        } else if pkt.dst_port() == 1026 {
            debug!("vsock: new getname request");
            if let Some(req) = pkt.read_getname_req() {
                self.proxy_map
                    .read()
                    .unwrap()
                    .get(&req.id)
                    .map(|proxy| proxy.lock().unwrap().getpeername(pkt, req));
            }
        } else if pkt.dst_port() == 1027 {
            debug!("vsock: new DGRAM sendto addr: src={}", pkt.src_port());
            if let Some(req) = pkt.read_sendto_addr() {
                debug!("vsock: new DGRAM sendto addr: id={}", req.id);
                self.proxy_map
                    .read()
                    .unwrap()
                    .get(&req.id)
                    .map(|proxy| proxy.lock().unwrap().sendto_addr(req));
            }
        } else if pkt.dst_port() == 1028 {
            debug!("vsock: DGRAM sendto data: src={}", pkt.src_port());
            self.proxy_map
                .read()
                .unwrap()
                .get(&(pkt.src_port() as u64))
                .map(|proxy| proxy.lock().unwrap().sendto_data(pkt));
        } else {
            if pkt.op() == uapi::VSOCK_OP_RW {
                debug!("vsock: DGRAM OP_RW");
                if let Some(proxy_lock) =
                    self.proxy_map.read().unwrap().get(&(pkt.src_port() as u64))
                {
                    debug!("vsock: DGRAM allowing OP_RW for {}", pkt.src_port());
                    let mut proxy = proxy_lock.lock().unwrap();
                    proxy.sendmsg(pkt);
                } else {
                    debug!("vsock: DGRAM ignoring OP_RW for {}", pkt.src_port());
                }
            }
        }

        Ok(())
    }
}
