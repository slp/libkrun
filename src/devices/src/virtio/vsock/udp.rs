use std::fmt;
use std::num::Wrapping;
use std::os::unix::io::{AsRawFd, RawFd};
use std::sync::{Arc, Mutex};

use nix::sys::socket::{
    bind, connect, getpeername, recv, send, sendto, socket, AddressFamily, InetAddr, IpAddr,
    Ipv4Addr, MsgFlags, SockAddr, SockFlag, SockType,
};
use nix::unistd::close;

use super::super::Queue as VirtQueue;
use super::defs;
use super::defs::uapi;
use super::muxer::MuxerRx;
use super::muxer_rxq::MuxerRxQ;
use super::packet::{
    TsiAcceptReq, TsiConnectReq, TsiConnectRsp, TsiGetnameReq, TsiGetnameRsp, TsiListenReq,
    TsiSendtoAddr, VsockPacket,
};
use super::proxy::{Proxy, ProxyError, ProxyStatus, ProxyUpdate};
use utils::epoll::{ControlOperation, Epoll, EpollEvent, EventSet};

use vm_memory::GuestMemoryMmap;

pub struct UdpProxy {
    pub id: u64,
    cid: u64,
    local_port: u32,
    peer_port: u32,
    control_port: u32,
    fd: RawFd,
    pub status: ProxyStatus,
    sendto_addr: Option<SockAddr>,
    listening: bool,
    epoll: Epoll,
    rxq_dgram: Arc<Mutex<MuxerRxQ>>,
    rx_cnt: Wrapping<u32>,
    tx_cnt: Wrapping<u32>,
    peer_buf_alloc: u32,
    peer_fwd_cnt: Wrapping<u32>,
}

impl UdpProxy {
    pub fn new(
        id: u64,
        cid: u64,
        peer_port: u32,
        control_port: u32,
        epoll: Epoll,
        rxq_dgram: Arc<Mutex<MuxerRxQ>>,
    ) -> Result<Self, ProxyError> {
        let fd = socket(
            AddressFamily::Inet,
            SockType::Datagram,
            SockFlag::SOCK_NONBLOCK,
            None,
        )
        .map_err(ProxyError::CreatingSocket)?;
        Ok(UdpProxy {
            id,
            cid,
            local_port: 0,
            peer_port,
            control_port,
            fd,
            status: ProxyStatus::Idle,
            sendto_addr: None,
            listening: false,
            epoll,
            rxq_dgram,
            rx_cnt: Wrapping(0),
            tx_cnt: Wrapping(0),
            peer_buf_alloc: 0,
            peer_fwd_cnt: Wrapping(0),
        })
    }

    fn init_pkt(&self, pkt: &mut VsockPacket) {
        debug!(
            "udp: init_pkt: id={}, src_port={}, dst_port={}",
            self.id, self.local_port, self.peer_port
        );
        pkt.set_op(uapi::VSOCK_OP_RW)
            .set_src_cid(self.cid)
            .set_dst_cid(uapi::VSOCK_HOST_CID)
            .set_dst_port(self.peer_port)
            .set_src_port(0)
            .set_type(uapi::VSOCK_TYPE_DGRAM)
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
                    self.rxq_dgram.lock().unwrap().push(MuxerRx::CreditRequest {
                        local_port: pkt.src_port(),
                        peer_port: pkt.dst_port(),
                        fwd_cnt: self.tx_cnt.0,
                    });
                }
                return None;
            }

            match recv(self.fd, &mut buf[..max_len], MsgFlags::empty()) {
                Ok(cnt) => {
                    debug!("vsock: udp: recv cnt={}", cnt);
                    if cnt > 0 {
                        self.rx_cnt += Wrapping(cnt as u32);
                        self.init_pkt(pkt);
                        pkt.set_len(cnt as u32);
                        Some(pkt.hdr().len() + cnt)
                    } else {
                        self.status = ProxyStatus::Closed;
                        None
                    }
                }
                Err(e) => {
                    debug!("vsock: udp: recv_pkt: recv error: {:?}", e);
                    None
                }
            }
        } else {
            debug!("vsock: udp: recv_pkt: pkt without buf");
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
                    debug!("vsock: udp: recv_pkt: RX queue error: {:?}", e);
                    queue_rx.undo_pop();
                    break;
                }
            };

            have_used = true;
            debug!("vsock: udp: recv_pkt: pushing packet with {} bytes", len);
            queue_rx.add_used(mem, head.index, len as u32);
        }

        debug!("vsock: udp: recv_pkt: have_used={}", have_used);
        have_used
    }

    fn register_events(&mut self, eset: EventSet) {
        self.epoll
            .ctl(
                ControlOperation::Add,
                self.fd,
                &EpollEvent::new(eset, self.id),
            )
            .unwrap();
    }
}

impl Proxy for UdpProxy {
    fn id(&self) -> u64 {
        self.id
    }

    fn status(&self) -> ProxyStatus {
        self.status
    }

    fn connect(&mut self, pkt: &VsockPacket, req: TsiConnectReq) -> ProxyUpdate {
        debug!("vsock: udp: connect: addr={}, port={}", req.addr, req.port);
        let res = match connect(
            self.fd,
            &SockAddr::Inet(InetAddr::new(IpAddr::V4(req.addr), req.port)),
        ) {
            Ok(()) => {
                debug!("vsock: connect: Connected");
                self.status = ProxyStatus::Connected;
                0
            }
            Err(e) => {
                debug!("vsock: UdpProxy: Error connecting: {}", e);
                -nix::errno::errno()
            }
        };

        self.peer_buf_alloc = pkt.buf_alloc();
        self.peer_fwd_cnt = Wrapping(pkt.fwd_cnt());

        self.rxq_dgram.lock().unwrap().push(MuxerRx::ConnResponse {
            local_port: pkt.dst_port(),
            peer_port: pkt.src_port(),
            result: res,
        });

        let mut update = ProxyUpdate::default();
        if res == 0 && !self.listening {
            update.polling = Some((self.id, self.fd, EventSet::IN));
        }
        update
    }

    fn getpeername(&mut self, pkt: &VsockPacket, req: TsiGetnameReq) {
        debug!("vsock: udp: process_getpeername");

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
        debug!("vsock: udp_proxy: sendmsg");

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

        debug!("vsock: udp_proxy: sendmsg ret={}", ret);
    }

    fn sendto_addr(&mut self, req: TsiSendtoAddr) {
        debug!(
            "vsock: udp_proxy: sendto_addr: addr={}, port={}",
            req.addr, req.port
        );
        self.sendto_addr = Some(SockAddr::Inet(InetAddr::new(
            IpAddr::V4(req.addr),
            req.port,
        )));
        if !self.listening {
            match bind(
                self.fd,
                &SockAddr::Inet(InetAddr::new(IpAddr::new_v4(0, 0, 0, 0), 0)),
            ) {
                Ok(_) => {
                    self.listening = true;
                    self.register_events(EventSet::IN);
                }
                Err(e) => debug!("vsock: udp_proxy: couldn't bind socket: {}", e),
            }
        }
    }

    fn sendto_data(&mut self, pkt: &VsockPacket) {
        debug!("vsock: udp_proxy: sendto_data");

        self.peer_buf_alloc = pkt.buf_alloc();
        self.peer_fwd_cnt = Wrapping(pkt.fwd_cnt());

        if let Some(addr) = self.sendto_addr {
            if let Some(buf) = pkt.buf() {
                match sendto(self.fd, buf, &addr, MsgFlags::empty()) {
                    Ok(sent) => {}
                    Err(err) => debug!("error in sendto: {}", err),
                }
            } else {
                debug!("vsock: udp_proxy: sendto_data pkt without buffer");
            }
        } else {
            debug!("vsock: udp_proxy: sendto_data without sendto_addr");
        }
    }

    fn listen(&mut self, pkt: &VsockPacket, req: TsiListenReq) -> ProxyUpdate {
        ProxyUpdate::default()
    }

    fn accept(&mut self, pkt: &VsockPacket, req: TsiAcceptReq) -> ProxyUpdate {
        ProxyUpdate::default()
    }

    fn update_peer_credit(&mut self, pkt: &VsockPacket) -> ProxyUpdate {
        debug!(
            "vsock: udp_proxy: update_credit: buf_alloc={} rx_cnt={} fwd_cnt={}",
            pkt.buf_alloc(),
            self.rx_cnt,
            pkt.fwd_cnt()
        );
        self.peer_buf_alloc = pkt.buf_alloc();
        self.peer_fwd_cnt = Wrapping(pkt.fwd_cnt());
        //self.status = ProxyStatus::Connected;

        let mut update = ProxyUpdate::default();
        update.polling = Some((self.id, self.fd, EventSet::IN));
        update
    }

    fn process_op_response(&mut self, pkt: &VsockPacket) -> ProxyUpdate {
        ProxyUpdate::default()
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
            update.remove_proxy = true;
            return update;
        }

        if evset.contains(EventSet::IN) {
            update.signal_queue = self.recv_pkt(queue_rx, mem);
        }

        if evset.contains(EventSet::OUT) {
            error!("vsock::udp: EventSet::OUT unexpected");
        }

        update
    }
}

impl AsRawFd for UdpProxy {
    fn as_raw_fd(&self) -> RawFd {
        self.fd
    }
}

impl Drop for UdpProxy {
    fn drop(&mut self) {
        close(self.fd);
    }
}
