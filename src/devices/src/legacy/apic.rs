use super::irqchip::IrqChipBackend;

use bit_field::*;

// ICH10 I/O APIC version: 0x20
const IOAPIC_VERSION_ID: u32 = 0x00000020;
pub const IOAPIC_BASE_ADDRESS: u64 = 0xfec00000;
// The Intel manual does not specify this size, but KVM uses it.
pub const IOAPIC_MEM_LENGTH_BYTES: u64 = 0x100;

// Constants for IOAPIC direct register offset.
const IOAPIC_REG_ID: u8 = 0x00;
const IOAPIC_REG_VERSION: u8 = 0x01;
const IOAPIC_REG_ARBITRATION_ID: u8 = 0x02;

// Register offsets
const IOREGSEL_OFF: u8 = 0x0;
const IOREGSEL_DUMMY_UPPER_32_BITS_OFF: u8 = 0x4;
const IOWIN_OFF: u8 = 0x10;
const IOEOIR_OFF: u8 = 0x40;

const IOWIN_SCALE: u8 = 0x2;

#[bitfield]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DestinationMode {
    Physical = 0,
    Logical = 1,
}

#[bitfield]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TriggerMode {
    Edge = 0,
    Level = 1,
}

#[bitfield]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DeliveryMode {
    Fixed = 0b000,
    Lowest = 0b001,
    SMI = 0b010,        // System management interrupt
    RemoteRead = 0b011, // This is no longer supported by intel.
    NMI = 0b100,        // Non maskable interrupt
    Init = 0b101,
    Startup = 0b110,
    External = 0b111,
}

#[bitfield]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DeliveryStatus {
    Idle = 0,
    Pending = 1,
}

/// Represents a IOAPIC redirection table entry.
#[bitfield]
#[derive(Clone, Copy, Default, PartialEq, Eq)]
pub struct IoapicRedirectionTableEntry {
    vector: BitField8,
    #[bits = 3]
    delivery_mode: DeliveryMode,
    #[bits = 1]
    dest_mode: DestinationMode,
    #[bits = 1]
    delivery_status: DeliveryStatus,
    polarity: BitField1,
    remote_irr: bool,
    #[bits = 1]
    trigger_mode: TriggerMode,
    interrupt_mask: bool, // true iff interrupts are masked.
    reserved: BitField39,
    dest_id: BitField8,
}

/// The level of a level-triggered interrupt: asserted or deasserted.
#[bitfield]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Level {
    Deassert = 0,
    Assert = 1,
}

// These MSI structures are for Intel's implementation of MSI.  The PCI spec defines most of MSI,
// but the Intel spec defines the format of messages for raising interrupts.  The PCI spec defines
// three u32s -- the address, address_high, and data -- but Intel only makes use of the address and
// data.  The Intel portion of the specification is in Volume 3 section 10.11.
#[bitfield]
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct MsiAddressMessage {
    pub reserved: BitField2,
    #[bits = 1]
    pub destination_mode: DestinationMode,
    pub redirection_hint: BitField1,
    pub reserved_2: BitField8,
    pub destination_id: BitField8,
    // According to Intel's implementation of MSI, these bits must always be 0xfee.
    pub always_0xfee: BitField12,
}

#[bitfield]
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct MsiDataMessage {
    pub vector: BitField8,
    #[bits = 3]
    pub delivery_mode: DeliveryMode,
    pub reserved: BitField3,
    #[bits = 1]
    pub level: Level,
    #[bits = 1]
    pub trigger: TriggerMode,
    pub reserved2: BitField16,
}

/// Given an offset that was read from/written to, return a tuple of the relevant IRQ and whether
/// the offset refers to the high bits of that register.
fn decode_irq_from_selector(selector: u8) -> (usize, bool) {
    (
        ((selector - IOWIN_OFF) / IOWIN_SCALE) as usize,
        selector & 1 != 0,
    )
}

pub struct Apic {
    /// Number of supported IO-APIC inputs / redirection entries.
    num_pins: usize,
    /// ioregsel register. Used for selecting which entry of the redirect table to read/write.
    ioregsel: u8,
    /// ioapicid register. Bits 24 - 27 contain the APIC ID for this device.
    ioapicid: u32,
    /// Redirection settings for each irq line.
    redirect_table: Vec<IoapicRedirectionTableEntry>,
    /// Interrupt activation state.
    interrupt_level: Vec<bool>,
}

impl Apic {
    pub fn new() -> Self {
        let num_pins = 24;
        let mut entry = IoapicRedirectionTableEntry::new();
        entry.set_interrupt_mask(true);

        Apic {
            num_pins,
            ioregsel: 0,
            ioapicid: 0,
            redirect_table: (0..num_pins).map(|_| entry).collect(),
            interrupt_level: (0..num_pins).map(|_| false).collect(),
        }
    }

    pub fn service_irq(&mut self, irq: usize, level: bool) -> bool {
        let entry = &mut self.redirect_table[irq];

        // De-assert the interrupt.
        if !level {
            self.interrupt_level[irq] = false;
            return true;
        }

        // If it's an edge-triggered interrupt that's already high we ignore it.
        if entry.get_trigger_mode() == TriggerMode::Edge && self.interrupt_level[irq] {
            return false;
        }

        self.interrupt_level[irq] = true;

        // Interrupts are masked, so don't inject.
        if entry.get_interrupt_mask() {
            return false;
        }

        // Level-triggered and remote irr is already active, so we don't inject a new interrupt.
        // (Coalesce with the prior one(s)).
        if entry.get_trigger_mode() == TriggerMode::Level && entry.get_remote_irr() {
            return false;
        }

        /*
            // Coalesce RTC interrupt to make tick stuffing work.
            if irq == RTC_IRQ && self.rtc_remote_irr {
                return false;
            }

            let injected = match self.out_events.get(irq) {
                Some(Some(evt)) => evt.event.write(1).is_ok(),
                _ => false,
            };

            if entry.get_trigger_mode() == TriggerMode::Level && level && injected {
                entry.set_remote_irr(true);
            } else if irq == RTC_IRQ && injected {
                self.rtc_remote_irr = true;
        }

        injected
         */
        false
    }

    fn ioapic_read(&mut self) -> u32 {
        match self.ioregsel {
            IOAPIC_REG_VERSION => ((self.num_pins - 1) as u32) << 16 | IOAPIC_VERSION_ID,
            IOAPIC_REG_ID | IOAPIC_REG_ARBITRATION_ID => self.ioapicid,
            _ => {
                if self.ioregsel < IOWIN_OFF {
                    // Invalid read; ignore and return 0.
                    0
                } else {
                    let (index, is_high_bits) = decode_irq_from_selector(self.ioregsel);
                    if index < self.num_pins {
                        let offset = if is_high_bits { 32 } else { 0 };
                        self.redirect_table[index].get(offset, 32) as u32
                    } else {
                        !0 // Invalid index - return all 1s
                    }
                }
            }
        }
    }

    fn ioapic_write(&mut self, val: u32) {
        match self.ioregsel {
            IOAPIC_REG_VERSION => { /* read-only register */ }
            IOAPIC_REG_ID => self.ioapicid = val & 0x0f00_0000,
            IOAPIC_REG_ARBITRATION_ID => { /* read-only register */ }
            _ => {
                if self.ioregsel < IOWIN_OFF {
                    // Invalid write; ignore.
                    return;
                }
                let (index, is_high_bits) = decode_irq_from_selector(self.ioregsel);
                if index >= self.num_pins {
                    // Invalid write; ignore.
                    return;
                }

                println!("setting up irq: {}", index);

                let entry = &mut self.redirect_table[index];
                if is_high_bits {
                    entry.set(32, 32, val.into());
                } else {
                    let before = *entry;
                    entry.set(0, 32, val.into());

                    // respect R/O bits.
                    entry.set_delivery_status(before.get_delivery_status());
                    entry.set_remote_irr(before.get_remote_irr());

                    // Clear remote_irr when switching to edge_triggered.
                    if entry.get_trigger_mode() == TriggerMode::Edge {
                        entry.set_remote_irr(false);
                    }

                    // NOTE: on pre-4.0 kernels, there's a race we would need to work around.
                    // "KVM: x86: ioapic: Fix level-triggered EOI and IOAPIC reconfigure race"
                    // is the fix for this.
                }

                if self.redirect_table[index].get_trigger_mode() == TriggerMode::Level
                    && self.interrupt_level[index]
                    && !self.redirect_table[index].get_interrupt_mask()
                {
                    self.service_irq(index, true);
                }

                let mut address = MsiAddressMessage::new();
                let mut data = MsiDataMessage::new();
                let entry = &self.redirect_table[index];
                address.set_destination_mode(entry.get_dest_mode());
                address.set_destination_id(entry.get_dest_id());
                address.set_always_0xfee(0xfee);
                data.set_vector(entry.get_vector());
                data.set_delivery_mode(entry.get_delivery_mode());
                data.set_trigger(entry.get_trigger_mode());

                let msi_address = address.get(0, 32);
                let msi_data = data.get(0, 32);
                /*
                    if let Err(e) = self.setup_msi(index, msi_address, msi_data as u32) {
                        error!("IOAPIC failed to set up MSI for index {}: {}", index, e);
                }
                     */
                println!(
                    "setup_msi: index={}, msi_address={}, msi_data={}",
                    index, msi_address, msi_data
                );
            }
        }
    }

    pub fn end_of_interrupt(&mut self, vector: u8) {
        /*
            if self.redirect_table[RTC_IRQ].get_vector() == vector && self.rtc_remote_irr {
                // Specifically clear RTC IRQ field
                self.rtc_remote_irr = false;
        }
            */

        for i in 0..self.num_pins {
            if self.redirect_table[i].get_vector() == vector
                && self.redirect_table[i].get_trigger_mode() == TriggerMode::Level
            {
                /*
                    if self
                        .resample_events
                        .get(i)
                        .map_or(false, |events| !events.is_empty())
                    {
                        self.service_irq(i, false);
                    }

                    if let Some(resample_events) = self.resample_events.get(i) {
                        for resample_evt in resample_events {
                            resample_evt.write(1).unwrap();
                        }
                }
                    */
                self.redirect_table[i].set_remote_irr(false);
            }
            // There is an inherent race condition in hardware if the OS is finished processing an
            // interrupt and a new interrupt is delivered between issuing an EOI and the EOI being
            // completed.  When that happens the ioapic is supposed to re-inject the interrupt.
            if self.interrupt_level[i] {
                self.service_irq(i, true);
            }
        }
    }
}

impl IrqChipBackend for Apic {
    fn new() -> Self {
        Apic::new()
    }
    fn set_irq(&mut self, irq_line: u32) {
        println!("Apic: should trigger: {}", irq_line);
    }

    fn bus_get_addr(&self) -> u64 {
        0xFEC00000
    }
    fn bus_get_size(&self) -> u64 {
        0x1000
    }
    fn bus_read(&mut self, vcpuid: u64, offset: u64, data: &mut [u8]) {
        println!("Apic: bus_read: offset={}", offset);
        if data.len() > 8 || data.is_empty() {
            println!("IOAPIC: Bad read size: {}", data.len());
            return;
        }
        if offset >= IOAPIC_MEM_LENGTH_BYTES {
            println!("IOAPIC: Bad read from {}", offset);
        }
        let out = match offset as u8 {
            IOREGSEL_OFF => self.ioregsel.into(),
            IOREGSEL_DUMMY_UPPER_32_BITS_OFF => 0,
            IOWIN_OFF => self.ioapic_read(),
            IOEOIR_OFF => 0,
            _ => {
                println!("IOAPIC: Bad read from {}", offset);
                return;
            }
        };
        let out_arr = out.to_ne_bytes();
        for i in 0..4 {
            if i < data.len() {
                data[i] = out_arr[i];
            }
        }
    }

    fn bus_write(&mut self, vcpuid: u64, offset: u64, data: &[u8]) {
        println!("Apic: bus_write: offset={}", offset);
        if data.len() > 8 || data.is_empty() {
            warn!("IOAPIC: Bad write size: {}", data.len());
            return;
        }
        if offset >= IOAPIC_MEM_LENGTH_BYTES {
            warn!("IOAPIC: Bad write to {}", offset);
        }
        match offset as u8 {
            IOREGSEL_OFF => self.ioregsel = data[0],
            IOREGSEL_DUMMY_UPPER_32_BITS_OFF => {} // Ignored.
            IOWIN_OFF => {
                if data.len() != 4 {
                    warn!("IOAPIC: Bad write size for iowin: {}", data.len());
                    return;
                }
                let data_arr = [data[0], data[1], data[2], data[3]];
                let val = u32::from_ne_bytes(data_arr);
                self.ioapic_write(val);
            }
            IOEOIR_OFF => self.end_of_interrupt(data[0]),
            _ => {
                warn!("IOAPIC: Bad write to {}", offset);
            }
        }
    }
}
