use std::sync::{Arc, Mutex};

use crate::bus::BusDevice;
use crate::legacy::gic::GICDevice;

pub type IrqChip = Arc<Mutex<IrqChipDevice>>;

pub struct IrqChipDevice {
    inner: Box<dyn IrqChipT>,
}

impl IrqChipDevice {
    pub fn new(irqchip: Box<dyn IrqChipT>) -> Self {
        Self { inner: irqchip }
    }

    pub fn get_mmio_addr(&self) -> u64 {
        self.inner.get_mmio_addr()
    }

    pub fn get_mmio_size(&self) -> u64 {
        self.inner.get_mmio_size()
    }

    pub fn set_irq(&self, irq_line: u32) {
        self.inner.set_irq(irq_line)
    }
}

impl BusDevice for IrqChipDevice {
    fn read(&mut self, vcpuid: u64, offset: u64, data: &mut [u8]) {
        self.inner.read(vcpuid, offset, data)
    }

    fn write(&mut self, vcpuid: u64, offset: u64, data: &[u8]) {
        self.inner.write(vcpuid, offset, data)
    }
}

impl GICDevice for IrqChipDevice {
    /// Returns an array with GIC device properties
    fn device_properties(&self) -> &[u64] {
        self.inner.device_properties()
    }

    /// Returns the number of vCPUs this GIC handles
    fn vcpu_count(&self) -> u64 {
        self.inner.vcpu_count()
    }

    /// Returns the fdt compatibility property of the device
    fn fdt_compatibility(&self) -> &str {
        self.inner.fdt_compatibility()
    }

    /// Returns the maint_irq fdt property of the device
    fn fdt_maint_irq(&self) -> u32 {
        self.inner.fdt_maint_irq()
    }

    /// Returns the GIC version of the device
    fn version(&self) -> u32 {
        self.inner.version()
    }
}

#[cfg(target_arch = "x86_64")]
pub trait IrqChipT: BusDevice {
    fn get_mmio_addr(&self) -> u64;
    fn get_mmio_size(&self) -> u64;
    fn set_irq(&self, irq_line: u32);
}

#[cfg(target_arch = "aarch64")]
pub trait IrqChipT: BusDevice + GICDevice {
    fn get_mmio_addr(&self) -> u64;
    fn get_mmio_size(&self) -> u64;
    fn set_irq(&self, irq_line: u32);
}
