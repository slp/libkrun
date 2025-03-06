use std::sync::{Arc, Mutex};

use crate::bus::BusDevice;

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

pub trait IrqChipT: BusDevice {
    fn get_mmio_addr(&self) -> u64;
    fn get_mmio_size(&self) -> u64;
    fn set_irq(&self, irq_line: u32);
}
