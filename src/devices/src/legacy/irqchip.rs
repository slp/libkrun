use crate::bus::BusDevice;

pub trait IrqChip: BusDevice {
    fn set_irq(&mut self, irq_line: u32) -> bool;
}
