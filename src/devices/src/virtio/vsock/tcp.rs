use std::fmt;
use std::num::Wrapping;
use std::os::unix::io::{AsRawFd, RawFd};
use std::sync::{Arc, Mutex};

use nix::sys::socket::{
    connect, getpeername, recv, send, shutdown, socket, AddressFamily, InetAddr, IpAddr, Ipv4Addr,
    MsgFlags, Shutdown, SockAddr, SockFlag, SockType,
};
use nix::unistd::close;

use super::super::Queue as VirtQueue;
use super::defs;
use super::defs::uapi;
use super::muxer::MuxerRx;
use super::muxer_rxq::MuxerRxQ;
use super::packet::{TsiConnectReq, TsiConnectRsp, TsiGetnameReq, TsiGetnameRsp, VsockPacket};
use super::proxy::{Proxy, ProxyError, ProxyStatus, ProxyUpdate};
use utils::epoll::EventSet;

use vm_memory::GuestMemoryMmap;

pub struct TcpProxy {
    id: u64,
    cid: u64,
    local_port: u32,
    control_port: u32,
    fd: RawFd,
    pub status: ProxyStatus,
    rxq_stream: Arc<Mutex<MuxerRxQ>>,
    rxq_dgram: Arc<Mutex<MuxerRxQ>>,
    rx_cnt: Wrapping<u32>,
    tx_cnt: Wrapping<u32>,
    peer_buf_alloc: u32,
    peer_fwd_cnt: Wrapping<u32>,
    push_cnt: Wrapping<u32>,
}

impl TcpProxy {
    pub fn new(
        id: u64,
        cid: u64,
        control_port: u32,
        rxq_stream: Arc<Mutex<MuxerRxQ>>,
        rxq_dgram: Arc<Mutex<MuxerRxQ>>,
    ) -> Result<Self, ProxyError> {
        let fd = socket(
            AddressFamily::Inet,
            SockType::Stream,
            SockFlag::SOCK_NONBLOCK,
            None,
        )
        .map_err(ProxyError::CreatingSocket)?;
        Ok(TcpProxy {
            id,
            cid,
            local_port: 0,
            control_port,
            fd,
            status: ProxyStatus::Idle,
            rxq_stream,
            rxq_dgram,
            rx_cnt: Wrapping(0),
            tx_cnt: Wrapping(0),
            peer_buf_alloc: 0,
            peer_fwd_cnt: Wrapping(0),
            push_cnt: Wrapping(0),
        })
    }

    fn init_control_pkt(&self, pkt: &mut VsockPacket) {
        debug!(
            "tcp: init_control_pkt: id={}, control_port={}",
            self.id, self.control_port
        );
        pkt.set_op(uapi::VSOCK_OP_RW)
            .set_src_cid(self.cid)
            .set_dst_cid(uapi::VSOCK_HOST_CID)
            .set_dst_port(self.control_port)
            .set_type(uapi::VSOCK_TYPE_DGRAM)
            .set_buf_alloc(defs::CONN_TX_BUF_SIZE as u32)
            .set_fwd_cnt(self.tx_cnt.0);
    }

    fn init_data_pkt(&self, pkt: &mut VsockPacket) {
        debug!("tcp: init_data_pkt: id={}", self.id);
        assert!(self.local_port != 0);
        pkt.set_op(uapi::VSOCK_OP_RW)
            .set_src_cid(self.cid)
            .set_dst_cid(uapi::VSOCK_HOST_CID)
            .set_src_port(self.local_port)
            .set_dst_port(self.id as u32)
            .set_type(uapi::VSOCK_TYPE_STREAM)
            .set_buf_alloc(defs::CONN_TX_BUF_SIZE as u32)
            .set_fwd_cnt(self.tx_cnt.0);
    }

    fn peer_avail_credit(&self) -> usize {
        (Wrapping(self.peer_buf_alloc as u32) - (self.rx_cnt - self.peer_fwd_cnt)).0 as usize
    }

    fn recv_to_pkt(&mut self, pkt: &mut VsockPacket) -> Option<usize> {
        if let Some(buf) = pkt.buf_mut() {
            let peer_credit = self.peer_avail_credit();
            let max_len = std::cmp::min(buf.len(), peer_credit);

            debug!(
                "recv_to_pkt: peer_avail_credit={}, buf.len={}, max_len={}",
                self.peer_avail_credit(),
                buf.len(),
                max_len,
            );

            if max_len == 0 {
                if self.status != ProxyStatus::WaitingCreditUpdate {
                    self.status = ProxyStatus::WaitingCreditUpdate;
                    self.rxq_stream
                        .lock()
                        .unwrap()
                        .push(MuxerRx::CreditRequest {
                            local_port: pkt.src_port(),
                            peer_port: pkt.dst_port(),
                            fwd_cnt: self.tx_cnt.0,
                        });
                }
                return None;
            }

            match recv(self.fd, &mut buf[..max_len], MsgFlags::empty()) {
                Ok(cnt) => {
                    debug!("vsock: tcp: recv cnt={}", cnt);
                    if cnt > 0 {
                        self.rx_cnt += Wrapping(cnt as u32);
                        debug!("vsock: tcp: recv rx_cnt={}", self.rx_cnt);
                        self.init_data_pkt(pkt);
                        pkt.set_len(cnt as u32);
                        Some(pkt.hdr().len() + cnt)
                    } else {
                        self.status = ProxyStatus::Closed;
                        None
                    }
                }
                Err(e) => {
                    debug!("vsock: tcp: recv_pkt: recv error: {:?}", e);
                    None
                }
            }
        } else {
            debug!("vsock: tcp: recv_pkt: pkt without buf");
            None
        }
    }

    fn recv_pkt(&mut self, queue_rx: &mut VirtQueue, mem: &GuestMemoryMmap) -> bool {
        let mut have_used = false;

        while let Some(head) = queue_rx.pop(mem) {
            let len = match VsockPacket::from_rx_virtq_head(&head) {
                Ok(mut pkt) => match self.recv_to_pkt(&mut pkt) {
                    Some(len) => len,
                    None => {
                        queue_rx.undo_pop();
                        break;
                    }
                },
                Err(e) => {
                    debug!("vsock: tcp: recv_pkt: RX queue error: {:?}", e);
                    queue_rx.undo_pop();
                    break;
                }
            };

            have_used = true;
            self.push_cnt += Wrapping(len as u32);
            debug!(
                "vsock: tcp: recv_pkt: pushing packet with {} bytes, push_cnt={}",
                len, self.push_cnt
            );
            queue_rx.add_used(mem, head.index, len as u32);
        }

        debug!("vsock: tcp: recv_pkt: have_used={}", have_used);
        have_used
    }

    fn push_connect_rsp(&mut self, result: i32, queue_rx: &mut VirtQueue, mem: &GuestMemoryMmap) {
        if let Some(head) = queue_rx.pop(mem) {
            match VsockPacket::from_rx_virtq_head(&head) {
                Ok(mut pkt) => {
                    self.init_control_pkt(&mut pkt);
                    pkt.set_src_port(1025);
                    debug!(
                        "tcp: ConnResponse: control_port: {}, result: {}",
                        self.control_port, result
                    );
                    pkt.write_connect_rsp(TsiConnectRsp { result });
                    pkt.set_len(pkt.buf().unwrap().len() as u32);
                    queue_rx.add_used(mem, head.index, pkt.hdr().len() as u32 + pkt.len());
                }
                Err(_) => {}
            }
        } else {
            warn!("couldn't push connect rsp, adding it to rxq queue");
            self.rxq_stream.lock().unwrap().push(MuxerRx::ConnResponse {
                local_port: 1025,
                peer_port: self.control_port,
                result,
            });
        }
    }

    fn push_reset(&mut self, queue_rx: &mut VirtQueue, mem: &GuestMemoryMmap) {
        if let Some(head) = queue_rx.pop(mem) {
            match VsockPacket::from_rx_virtq_head(&head) {
                Ok(mut pkt) => {
                    self.init_data_pkt(&mut pkt);
                    pkt.set_op(uapi::VSOCK_OP_RST).set_len(0);
                    debug!(
                        "tcp: reset: id: {}, local_port: {}",
                        self.id, self.local_port
                    );
                    queue_rx.add_used(mem, head.index, pkt.hdr().len() as u32);
                }
                Err(_) => {}
            }
        } else {
            warn!("couldn't push reset, adding it to rxq queue");
            self.rxq_stream.lock().unwrap().push(MuxerRx::Reset {
                local_port: self.local_port,
                peer_port: self.id as u32,
            });
        }
    }
}

impl Proxy for TcpProxy {
    fn id(&self) -> u64 {
        self.id
    }

    fn status(&self) -> ProxyStatus {
        self.status
    }

    fn connect(&mut self, pkt: &VsockPacket, req: TsiConnectReq) -> ProxyUpdate {
        let mut update = ProxyUpdate::default();

        let res = match connect(
            self.fd,
            &SockAddr::Inet(InetAddr::new(IpAddr::V4(req.addr), req.port)),
        ) {
            Ok(()) => {
                debug!("vsock: connect: Connected");
                self.status = ProxyStatus::Connected;
                0
            }
            Err(nix::errno::Errno::EINPROGRESS) => {
                debug!("vsock: connect: Connecting");
                self.status = ProxyStatus::Connecting;
                0
            }
            Err(e) => {
                debug!("vsock: TcpProxy: Error connecting: {}", e);
                -nix::errno::errno()
            }
        };

        if self.status == ProxyStatus::Connecting {
            update.polling = Some((self.id, self.fd, EventSet::IN | EventSet::OUT));
        } else {
            self.rxq_stream.lock().unwrap().push(MuxerRx::ConnResponse {
                local_port: 1025,
                peer_port: pkt.src_port(),
                result: res,
            });
        }

        update
    }

    fn confirm_connect(&mut self, pkt: &VsockPacket) {
        debug!(
            "tcp: confirm_connect: local_port={} peer_port={}",
            pkt.dst_port(),
            pkt.src_port()
        );

        self.peer_buf_alloc = pkt.buf_alloc();
        self.peer_fwd_cnt = Wrapping(pkt.fwd_cnt());

        self.local_port = pkt.dst_port();
        self.rxq_stream.lock().unwrap().push(MuxerRx::OpResponse {
            local_port: pkt.dst_port(),
            peer_port: pkt.src_port(),
        });
    }

    fn getpeername(&mut self, pkt: &VsockPacket, req: TsiGetnameReq) {
        debug!("vsock: process_getpeername");

        let name = getpeername(self.fd).unwrap();
        let (ipv4, port) = match name {
            SockAddr::Inet(iaddr) => match iaddr.ip() {
                IpAddr::V4(ipv4) => (ipv4, iaddr.port()),
                _ => panic!("IPv6 is not yet supported"),
            },
            _ => panic!("unknown SockAddr family"),
        };
        let data = TsiGetnameRsp {
            addr: ipv4,
            port,
            result: 0,
        };

        self.rxq_dgram
            .lock()
            .unwrap()
            .push(MuxerRx::GetnameResponse {
                local_port: pkt.dst_port(),
                peer_port: pkt.src_port(),
                data,
            });
    }

    fn sendmsg(&mut self, pkt: &VsockPacket) {
        debug!("vsock: tcp_proxy: sendmsg");

        let ret = if let Some(buf) = pkt.buf() {
            match send(self.fd, buf, MsgFlags::empty()) {
                Ok(sent) => {
                    self.tx_cnt += Wrapping(sent as u32);
                    (sent as i32)
                }
                Err(err) => -(err as i32),
            }
        } else {
            -libc::EINVAL
        };

        if ret > 0 && self.tx_cnt.0 > (defs::CONN_TX_BUF_SIZE / 2) as u32 {
            self.rxq_stream.lock().unwrap().push(MuxerRx::CreditUpdate {
                local_port: pkt.dst_port(),
                peer_port: pkt.src_port(),
                fwd_cnt: self.tx_cnt.0,
            });
        }

        debug!("vsock: tcp_proxy: sendmsg ret={}", ret);
    }

    fn update_peer_credit(&mut self, pkt: &VsockPacket) -> ProxyUpdate {
        debug!(
            "vsock: tcp_proxy: update_credit: buf_alloc={} rx_cnt={} fwd_cnt={}",
            pkt.buf_alloc(),
            self.rx_cnt,
            pkt.fwd_cnt()
        );
        self.peer_buf_alloc = pkt.buf_alloc();
        self.peer_fwd_cnt = Wrapping(pkt.fwd_cnt());
        self.status = ProxyStatus::Connected;

        let mut update = ProxyUpdate::default();
        update.polling = Some((self.id, self.fd, EventSet::IN));
        update
    }

    fn shutdown(&mut self, pkt: &VsockPacket) {
        let recv_off = pkt.flags() & uapi::VSOCK_FLAGS_SHUTDOWN_RCV != 0;
        let send_off = pkt.flags() & uapi::VSOCK_FLAGS_SHUTDOWN_SEND != 0;

        let how = if recv_off && send_off {
            Shutdown::Both
        } else if recv_off {
            Shutdown::Read
        } else {
            Shutdown::Write
        };

        shutdown(self.fd, how);
    }

    fn process_event(
        &mut self,
        evset: EventSet,
        queue_rx: &mut VirtQueue,
        queue_dr: &mut VirtQueue,
        mem: &GuestMemoryMmap,
    ) -> ProxyUpdate {
        let mut update = ProxyUpdate::default();

        if evset.contains(EventSet::HANG_UP) {
            debug!("process_event: HANG_UP");
            if self.status == ProxyStatus::Connecting {
                self.push_connect_rsp(-libc::ECONNREFUSED, queue_dr, mem);
            } else {
                self.push_reset(queue_rx, mem);
            }

            self.status = ProxyStatus::Closed;
            close(self.fd);
            update.signal_queue = true;
            update.remove_proxy = true;
            return update;
        }

        if evset.contains(EventSet::IN) {
            debug!("process_event: IN");
            if self.status == ProxyStatus::Connected {
                update.signal_queue = self.recv_pkt(queue_rx, mem);
                if self.status == ProxyStatus::Closed {
                    self.push_reset(queue_rx, mem);
                    update.signal_queue = true;
                    update.remove_proxy = true;
                    return update;
                } else if self.status == ProxyStatus::WaitingCreditUpdate {
                    update.polling = Some((self.id(), self.fd, EventSet::empty()));
                }
            } else {
                error!("vsock::tcp: EventSet::IN while not connected");
            }
        }

        if evset.contains(EventSet::OUT) {
            debug!("process_event: OUT");
            if self.status == ProxyStatus::Connecting {
                self.status = ProxyStatus::Connected;
                self.push_connect_rsp(0, queue_dr, mem);
                update.signal_queue = true;
                update.polling = Some((self.id(), self.fd, EventSet::IN));
            } else {
                error!("vsock::tcp: EventSet::OUT while not connecting");
            }
        }

        update
    }
}

impl AsRawFd for TcpProxy {
    fn as_raw_fd(&self) -> RawFd {
        self.fd
    }
}

impl Drop for TcpProxy {
    fn drop(&mut self) {
        close(self.fd);
    }
}
