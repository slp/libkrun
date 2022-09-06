use super::Apic;

use crate::bus::BusDevice;

pub type IrqChip = IrqChipG<Apic>;

pub trait IrqChipBackend {
    fn new() -> Self;
    fn set_irq(&mut self, irq_line: u32);
    fn bus_get_addr(&self) -> u64;
    fn bus_get_size(&self) -> u64;
    fn bus_read(&mut self, vcpuid: u64, offset: u64, data: &mut [u8]);
    fn bus_write(&mut self, vcpuid: u64, offset: u64, data: &[u8]);
}

pub struct IrqChipG<B> {
    backend: B,
}

unsafe impl<B: IrqChipBackend> Send for IrqChipG<B> {}

impl<B: IrqChipBackend> IrqChipG<B> {
    pub fn new() -> Self {
        IrqChipG { backend: B::new() }
    }

    pub fn set_irq(&mut self, irq_line: u32) {
        self.backend.set_irq(irq_line);
    }

    pub fn get_addr(&self) -> u64 {
        self.backend.bus_get_addr()
    }

    pub fn get_size(&self) -> u64 {
        self.backend.bus_get_size()
    }
}

impl<B: IrqChipBackend + 'static> BusDevice for IrqChipG<B> {
    fn read(&mut self, vcpuid: u64, offset: u64, data: &mut [u8]) {
        self.backend.bus_read(vcpuid, offset, data);
    }

    fn write(&mut self, vcpuid: u64, offset: u64, data: &[u8]) {
        self.backend.bus_write(vcpuid, offset, data);
    }
}
