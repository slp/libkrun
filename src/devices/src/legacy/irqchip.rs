use std::sync::{Arc, Mutex};

use crate::bus::BusDevice;
#[cfg(target_arch = "aarch64")]
use crate::legacy::gic::GICDevice;
use crate::Error as DeviceError;

use utils::eventfd::EventFd;

pub type IrqChip = IrqChipDevice;

#[derive(Clone)]
pub struct IrqChipDevice {
    inner: Arc<Mutex<Box<dyn IrqChipT>>>,
}

impl IrqChipDevice {
    pub fn new(irqchip: Box<dyn IrqChipT>) -> Self {
        Self {
            inner: Arc::new(Mutex::new(irqchip)),
        }
    }

    pub fn get_mmio_addr(&self) -> u64 {
        self.inner.lock().unwrap().get_mmio_addr()
    }

    pub fn get_mmio_size(&self) -> u64 {
        self.inner.lock().unwrap().get_mmio_size()
    }

    pub fn set_irq(
        &self,
        irq_line: Option<u32>,
        interrupt_evt: Option<&EventFd>,
    ) -> Result<(), DeviceError> {
        self.inner.lock().unwrap().set_irq(irq_line, interrupt_evt)
    }
}

impl BusDevice for IrqChipDevice {
    fn read(&mut self, vcpuid: u64, offset: u64, data: &mut [u8]) {
        self.inner.lock().unwrap().read(vcpuid, offset, data)
    }

    fn write(&mut self, vcpuid: u64, offset: u64, data: &[u8]) {
        self.inner.lock().unwrap().write(vcpuid, offset, data)
    }
}

#[cfg(target_arch = "aarch64")]
impl GICDevice for IrqChipDevice {
    /// Returns an array with GIC device properties
    fn device_properties(&self) -> Vec<u64> {
        self.inner.lock().unwrap().device_properties().clone()
    }

    /// Returns the number of vCPUs this GIC handles
    fn vcpu_count(&self) -> u64 {
        self.inner.lock().unwrap().vcpu_count()
    }

    /// Returns the fdt compatibility property of the device
    fn fdt_compatibility(&self) -> String {
        self.inner.lock().unwrap().fdt_compatibility().clone()
    }

    /// Returns the maint_irq fdt property of the device
    fn fdt_maint_irq(&self) -> u32 {
        self.inner.lock().unwrap().fdt_maint_irq()
    }

    /// Returns the GIC version of the device
    fn version(&self) -> u32 {
        self.inner.lock().unwrap().version()
    }
}

#[cfg(target_arch = "x86_64")]
pub trait IrqChipT: BusDevice {
    fn get_mmio_addr(&self) -> u64;
    fn get_mmio_size(&self) -> u64;
    fn set_irq(
        &self,
        irq_line: Option<u32>,
        interrupt_evt: Option<&EventFd>,
    ) -> Result<(), DeviceError>;
}

#[cfg(target_arch = "aarch64")]
pub trait IrqChipT: BusDevice + GICDevice {
    fn get_mmio_addr(&self) -> u64;
    fn get_mmio_size(&self) -> u64;
    fn set_irq(
        &self,
        irq_line: Option<u32>,
        interrupt_evt: Option<&EventFd>,
    ) -> Result<(), DeviceError>;
}
