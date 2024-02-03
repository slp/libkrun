use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};
use std::{io, thread};

use vm_memory::{GuestMemory, GuestMemoryError, GuestMemoryMmap, GuestMemoryRegion};

use crate::virtio::console::console_control::ConsoleControl;
use crate::virtio::console::irq_signaler::IRQSignaler;
use crate::virtio::console::port_io::PortInput;
use crate::virtio::{DescriptorChain, Queue};

pub(crate) fn process_rx(
    mem: GuestMemoryMmap,
    mut queue: Queue,
    irq: IRQSignaler,
    mut input: Arc<Mutex<Box<dyn PortInput + Send>>>,
    control: Arc<ConsoleControl>,
    port_id: u32,
    stopfd: utils::eventfd::EventFd,
    stop: Arc<AtomicBool>,
) {
    let mem = &mem;
    let mut eof = false;

    //println!("ZZZ - process_rx");
    let mut input = input.lock().unwrap();
    loop {
        let head = pop_head_blocking(&mut queue, mem, &irq);
        //println!("ZZZ - some descriptor!\n");

        let head_index = head.index;
        let mut bytes_read = 0;
        for chain in head.into_iter().writable() {
            match read_to_desc(chain, input.as_mut(), &mut eof) {
                Ok(0) => {
                    break;
                }
                Ok(len) => {
                    bytes_read += len;
                }
                Err(e) => {
                    log::error!("Failed to read: {e:?}")
                }
            }
        }

        if bytes_read != 0 {
            //println!("Rx {bytes_read} bytes queue len{}", queue.len(mem));
            queue.add_used(mem, head_index, bytes_read as u32);
        }

        // We signal_used_queue only when we get WouldBlock or EOF
        if eof {
            //println!("XXX - signal_used");
            irq.signal_used_queue("rx EOF");
            log::trace!("signaling EOF on port {port_id}");
            control.port_open(port_id, false);
            return;
        } else if bytes_read == 0 {
            //println!("XXX - wait until");
            queue.undo_pop();
            irq.signal_used_queue("rx WouldBlock");
            input.wait_until_readable(Some(&stopfd));
        }

        if stop.load(Ordering::Acquire) {
            //println!("XXX - RX thread stopping");
            return;
        }
    }
}

fn pop_head_blocking<'mem>(
    queue: &mut Queue,
    mem: &'mem GuestMemoryMmap,
    irq: &IRQSignaler,
) -> DescriptorChain<'mem> {
    //println!("ZZZ - pop_head_blocking");
    loop {
        match queue.pop(mem) {
            Some(descriptor) => break descriptor,
            None => {
                //println!("ZZZ - no descriptor");
                irq.signal_used_queue("rx queue empty, parking");
                //let ten_millis = std::time::Duration::from_secs(1);
                //thread::sleep(ten_millis);

                thread::park();
                log::trace!("rx unparked, queue len {}", queue.len(mem))
            }
        }
    }
}

fn read_to_desc(
    desc: DescriptorChain,
    input: &mut (dyn PortInput + Send),
    eof: &mut bool,
) -> Result<usize, GuestMemoryError> {
    //println!("ZZZ - read_to_desc");
    desc.mem
        .try_access(desc.len as usize, desc.addr, |_, len, addr, region| {
            let mut target = region.get_slice(addr, len).unwrap();
            match input.read_volatile(&mut target) {
                Ok(n) => {
                    //println!("read: {}", n);
                    if n == 0 {
                        *eof = true
                    }
                    Ok(n)
                }
                // We can't return an error otherwise we would not know how many bytes were processed before WouldBlock
                Err(e) if e.kind() == io::ErrorKind::WouldBlock => {
                    //println!("wouldblock");
                    Ok(0)
                }

                Err(e) => Err(GuestMemoryError::IOError(e)),
            }
        })
}
