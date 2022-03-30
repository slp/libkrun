use std::fmt;
use std::os::unix::io::{AsRawFd, RawFd};

use nix::sys::socket::Ipv4Addr;
use vm_memory::GuestMemoryMmap;

use super::super::Queue as VirtQueue;
use super::muxer::MuxerRx;
use super::muxer_rxq::MuxerRxQ;
use super::packet::{
    TsiAcceptReq, TsiConnectReq, TsiGetnameReq, TsiListenReq, TsiSendtoAddr, VsockPacket,
};
use utils::epoll::EventSet;

#[derive(Debug)]
pub enum ProxyError {
    CreatingSocket(nix::errno::Errno),
    Connecting(nix::errno::Errno),
    GettingPeerName(nix::errno::Errno),
    PeerNeedsCreditUpdate,
}

#[derive(PartialEq, Clone, Copy)]
pub enum ProxyStatus {
    Idle,
    Connecting,
    Connected,
    Listening,
    Closed,
    WaitingCreditUpdate,
    ReverseInit,
}

pub struct ProxyUpdate {
    pub signal_queue: bool,
    pub remove_proxy: bool,
    pub polling: Option<(u64, RawFd, EventSet)>,
    pub new_proxy: Option<(u32, RawFd)>,
    pub push_accept: Option<(u64, u64)>,
}

impl Default for ProxyUpdate {
    fn default() -> ProxyUpdate {
        ProxyUpdate {
            signal_queue: false,
            remove_proxy: false,
            polling: None,
            new_proxy: None,
            push_accept: None,
        }
    }
}

impl fmt::Display for ProxyError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

pub trait Proxy: Send + AsRawFd {
    fn id(&self) -> u64;
    fn status(&self) -> ProxyStatus;
    fn connect(&mut self, pkt: &VsockPacket, req: TsiConnectReq) -> ProxyUpdate;
    fn confirm_connect(&mut self, pkt: &VsockPacket) {}
    fn getpeername(&mut self, pkt: &VsockPacket, req: TsiGetnameReq);
    fn sendmsg(&mut self, pkt: &VsockPacket);
    fn sendto_addr(&mut self, req: TsiSendtoAddr) {}
    fn sendto_data(&mut self, pkt: &VsockPacket) {}
    fn listen(&mut self, pkt: &VsockPacket, req: TsiListenReq) -> ProxyUpdate;
    fn accept(&mut self, pkt: &VsockPacket, req: TsiAcceptReq) -> ProxyUpdate;
    fn update_peer_credit(&mut self, pkt: &VsockPacket) -> ProxyUpdate;
    fn push_op_request(&mut self, queue: &mut VirtQueue, mem: &GuestMemoryMmap) {}
    fn process_op_response(&mut self, pkt: &VsockPacket) -> ProxyUpdate;
    fn push_accept_rsp(
        &mut self,
        new_id: u64,
        result: i32,
        queue: &mut VirtQueue,
        mem: &GuestMemoryMmap,
    ) {
    }
    fn shutdown(&mut self, pkt: &VsockPacket) {}
    fn process_event(
        &mut self,
        evset: EventSet,
        queue_rx: &mut VirtQueue,
        queue_dr: &mut VirtQueue,
        meme: &GuestMemoryMmap,
    ) -> ProxyUpdate;
}
