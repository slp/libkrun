use std::fmt;
use std::os::unix::io::{AsRawFd, RawFd};

use nix::sys::socket::Ipv4Addr;
use vm_memory::GuestMemoryMmap;

use super::super::Queue as VirtQueue;
use super::muxer::MuxerRx;
use super::muxer_rxq::MuxerRxQ;
use super::packet::{TsiConnectReq, TsiGetnameReq, TsiSendtoAddr, VsockPacket};
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
}

pub struct ProxyUpdate {
    pub signal_queue: bool,
    pub remove_proxy: bool,
    pub polling: Option<(u64, RawFd, EventSet)>,
}

impl Default for ProxyUpdate {
    fn default() -> ProxyUpdate {
        ProxyUpdate {
            signal_queue: false,
            remove_proxy: false,
            polling: None,
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
    fn update_peer_credit(&mut self, pkt: &VsockPacket) -> ProxyUpdate;
    fn shutdown(&mut self, pkt: &VsockPacket) {}
    fn process_event(
        &mut self,
        evset: EventSet,
        queue_rx: &mut VirtQueue,
        queue_dr: &mut VirtQueue,
        meme: &GuestMemoryMmap,
    ) -> ProxyUpdate;
    /*
    fn data_in(&mut self, queue_rx: &mut VirtQueue, mem: &GuestMemoryMmap) -> bool;
    fn data_out(
        &mut self,
        queue_rx: &mut VirtQueue,
        queue_dr: &mut VirtQueue,
        mem: &GuestMemoryMmap,
    ) -> bool;
    fn data_error(&mut self, queue_dr: &mut VirtQueue, mem: &GuestMemoryMmap) -> bool;
    */
}
