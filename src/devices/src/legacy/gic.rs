use std::collections::VecDeque;
use std::convert::TryInto;

use arch::aarch64::layout;

use crate::bus::BusDevice;

const GIC_V2_DIST_SIZE: u64 = 0x1000;
const GIC_V2_CPU_SIZE: u64 = 0x2000;
const DEFAULT_IRQ_NUM: u32 = 64;

pub type kern_return_t = ::std::os::raw::c_int;
pub type mach_error_t = kern_return_t;
pub type hv_return_t = mach_error_t;

pub type hv_vcpu_t = u64;
pub const hv_interrupt_type_t_HV_INTERRUPT_TYPE_IRQ: hv_interrupt_type_t = 0;
pub const hv_interrupt_type_t_HV_INTERRUPT_TYPE_FIQ: hv_interrupt_type_t = 1;
pub type hv_interrupt_type_t = u32;

extern "C" {
    #[doc = " @function   hv_vcpu_set_pending_interrupt."]
    #[doc = " @abstract   Sets pending interrupts for a vcpu."]
    #[doc = " @param      vcpu ID of the vcpu instance."]
    #[doc = " @param      type Interrupt type."]
    #[doc = " @param      pending Whether the interrupt is pending or not."]
    #[doc = " @discussion"]
    #[doc = "             Must be called by the owning thread."]
    #[doc = "             The pending interrupts automatically cleared after hv_vcpu_run returns. It is expected that"]
    #[doc = "             hv_vcpu_set_pending_interrupt be called before every hv_vcpu_run to set pending interrupts."]
    pub fn hv_vcpu_set_pending_interrupt(
        vcpu: hv_vcpu_t,
        type_: hv_interrupt_type_t,
        pending: bool,
    ) -> hv_return_t;
}

pub struct Gic {
    irq_num: u32,
    ctlr: u32,
    irq_cfg: [u32; DEFAULT_IRQ_NUM as usize],
    pending_irqs: VecDeque<u32>,
}

impl Gic {
    pub fn new() -> Self {
        Self {
            irq_num: DEFAULT_IRQ_NUM,
            ctlr: 0,
            irq_cfg: [0; DEFAULT_IRQ_NUM as usize],
            pending_irqs: VecDeque::new(),
        }
    }

    /// Get the address of the GICv2 distributor.
    pub const fn get_addr() -> u64 {
        layout::MAPPED_IO_START - GIC_V2_DIST_SIZE - GIC_V2_CPU_SIZE
    }

    /// Get the size of the GIC_v2 distributor.
    pub const fn get_size() -> u64 {
        GIC_V2_DIST_SIZE + GIC_V2_CPU_SIZE
    }

    pub fn set_irq(&mut self, irq_line: u32) {
        debug!("GIC should set irq={}", irq_line);
        let ret = unsafe {
            hv_vcpu_set_pending_interrupt(0, hv_interrupt_type_t_HV_INTERRUPT_TYPE_IRQ, true)
        };
        if ret != 0 {
            panic!("Error setting pending IRQ");
        }
        self.pending_irqs.push_back(irq_line);
    }

    fn handle_dist_read8(&mut self, offset: u64, data: &mut [u8]) {
        debug!("GIC DIST read8 offset=0x{:x}", offset);
    }

    fn handle_dist_read16(&mut self, offset: u64, data: &mut [u8]) {
        debug!("GIC DIST read16 offset=0x{:x}", offset);
    }

    fn handle_dist_read32(&mut self, offset: u64, data: &mut [u8]) {
        debug!("GIC DIST read32 offset=0x{:x}", offset);
        let mut val: u32 = 0;
        match offset {
            0x0 => val = self.ctlr,
            0x4 => val = (self.irq_num / 32) - 1,
            0xc00..=0xf00 => {
                let irq = offset - 0xc00;
                val = self.irq_cfg[irq as usize];
                debug!("Reading irq={} val={}", irq, val);
            }
            _ => {}
        }
        for (i, b) in val.to_le_bytes().iter().enumerate() {
            data[i] = *b;
        }
        debug!("data={:?}", data);
    }

    fn handle_dist_write8(&mut self, offset: u64, data: &[u8]) {
        debug!("GIC DIST write8 offset=0x{:x}, data={:?}", offset, data);
    }

    fn handle_dist_write16(&mut self, offset: u64, data: &[u8]) {
        debug!("GIC DIST write16 offset=0x{:x}, data={:?}", offset, data);
    }

    fn handle_dist_write32(&mut self, offset: u64, data: &[u8]) {
        debug!("GIC DIST write32 offset=0x{:x}, data={:?}", offset, data);
        let val: u32 = u32::from_le_bytes(data.try_into().unwrap());
        match offset {
            0x0 => self.ctlr = val,
            0xc00..=0xeff => {
                let irq = offset - 0xc00;
                debug!("Setting irq={} to val={}", irq, val);
                self.irq_cfg[irq as usize] = val;
            }
            _ => {}
        }
    }

    fn handle_cpu_read8(&mut self, offset: u64, data: &mut [u8]) {
        debug!("GIC CPU read8 offset=0x{:x}", offset);
    }

    fn handle_cpu_read16(&mut self, offset: u64, data: &mut [u8]) {
        debug!("GIC CPU read16 offset=0x{:x}", offset);
    }

    fn handle_cpu_read32(&mut self, offset: u64, data: &mut [u8]) {
        debug!("GIC CPU read32 offset=0x{:x}", offset);
        let mut val = 0;
        match offset {
            0xc => {
                val = self.pending_irqs.pop_front().unwrap_or(1023);
                //val = self.pending_irqs.pop_front().unwrap();
                debug!("pending irq={}", val);
            }
            _ => {}
        }
        for (i, b) in val.to_le_bytes().iter().enumerate() {
            data[i] = *b;
        }
        debug!(
            "data={:?} val={}",
            data,
            u32::from_le_bytes((data as &[u8]).try_into().unwrap())
        );
    }

    fn handle_cpu_write8(&mut self, offset: u64, data: &[u8]) {
        debug!("GIC CPU write8 offset=0x{:x}, data={:?}", offset, data);
    }

    fn handle_cpu_write16(&mut self, offset: u64, data: &[u8]) {
        debug!("GIC CPU write16 offset=0x{:x}, data={:?}", offset, data);
    }

    fn handle_cpu_write32(&mut self, offset: u64, data: &[u8]) {
        debug!("GIC CPU write32 offset=0x{:x}, data={:?}", offset, data);
    }
}

impl BusDevice for Gic {
    fn read(&mut self, offset: u64, data: &mut [u8]) {
        if offset >= GIC_V2_CPU_SIZE {
            let offset = offset - GIC_V2_CPU_SIZE;
            match data.len() {
                1 => self.handle_dist_read8(offset, data),
                2 => self.handle_dist_read16(offset, data),
                4 => self.handle_dist_read32(offset, data),
                _ => panic!("GIC DIST unsupported read size"),
            }
        } else {
            match data.len() {
                1 => self.handle_cpu_read8(offset, data),
                2 => self.handle_cpu_read16(offset, data),
                4 => self.handle_cpu_read32(offset, data),
                _ => panic!("GIC CPU unsupported read size"),
            }
        }
    }

    fn write(&mut self, offset: u64, data: &[u8]) {
        if offset >= GIC_V2_CPU_SIZE {
            let offset = offset - GIC_V2_CPU_SIZE;
            match data.len() {
                1 => self.handle_dist_write8(offset, data),
                2 => self.handle_dist_write16(offset, data),
                4 => self.handle_dist_write32(offset, data),
                _ => panic!("GIC DIST unsupported read size"),
            }
        } else {
            match data.len() {
                1 => self.handle_cpu_write8(offset, data),
                2 => self.handle_cpu_write16(offset, data),
                4 => self.handle_cpu_write32(offset, data),
                _ => panic!("GIC CPU unsupported write size"),
            }
        }
    }
}
