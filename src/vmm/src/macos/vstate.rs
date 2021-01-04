// Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// Portions Copyright 2017 The Chromium OS Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the THIRD-PARTY file.

use libc::{c_int, c_void, siginfo_t};
use std::cell::Cell;
use std::convert::TryInto;
use std::fmt::{Display, Formatter};
use std::io;
use std::result;
use std::sync::atomic::{fence, Ordering};
use std::sync::mpsc::{channel, Receiver, Sender, TryRecvError};
#[cfg(not(test))]
use std::sync::Barrier;
use std::thread;

use super::super::TimestampUs;
use super::super::{FC_EXIT_CODE_GENERIC_ERROR, FC_EXIT_CODE_OK};
use super::bindings::{
    hv_reg_t_HV_REG_CPSR, hv_reg_t_HV_REG_PC, hv_reg_t_HV_REG_X0, hv_vcpu_create, hv_vcpu_exit_t,
    hv_vcpu_get_reg, hv_vcpu_run, hv_vcpu_set_reg, hv_vcpu_t, hv_vm_create, hv_vm_map,
    HV_MEMORY_EXEC, HV_MEMORY_READ, HV_MEMORY_WRITE,
};
use super::hvf::{
    hv_call, EC_AA64_BKPT, EC_AA64_HVC, EC_AA64_SMC, EC_DATAABORT, EC_SVEACCESSTRAP,
    EC_SYSTEMREGISTERTRAP, EC_WFX_TRAP, PSTATE_FAULT_BITS_64, SYSREG_MASK,
};

use arch;
use arch::aarch64::gic::GICDevice;
use utils::eventfd::EventFd;
//use utils::signal::{register_signal_handler, sigrtmin, Killable};
use utils::sm::StateMachine;
use vm_memory::{
    Address, GuestAddress, GuestMemory, GuestMemoryError, GuestMemoryMmap, GuestMemoryRegion,
};
use vmm_config::machine_config::CpuFeaturesTemplate;

#[cfg(target_arch = "x86_64")]
const MAGIC_IOPORT_SIGNAL_GUEST_BOOT_COMPLETE: u64 = 0x03f0;
#[cfg(target_arch = "aarch64")]
const MAGIC_IOPORT_SIGNAL_GUEST_BOOT_COMPLETE: u64 = 0x40000000;
const MAGIC_VALUE_SIGNAL_GUEST_BOOT_COMPLETE: u8 = 123;

/// Signal number (SIGRTMIN) used to kick Vcpus.
pub(crate) const VCPU_RTSIG_OFFSET: i32 = 0;

/// Errors associated with the wrappers over KVM ioctls.
#[derive(Debug)]
pub enum Error {
    /// Invalid guest memory configuration.
    GuestMemoryMmap(GuestMemoryError),
    /// The number of configured slots is bigger than the maximum reported by KVM.
    NotEnoughMemorySlots,
    /// Error configuring the general purpose aarch64 registers.
    REGSConfiguration(arch::aarch64::regs::Error),
    /// Error setting up the global interrupt controller.
    SetupGIC(arch::aarch64::gic::Error),
    /// Cannot set the memory regions.
    SetUserMemoryRegion,
    /// Failed to signal Vcpu.
    SignalVcpu(utils::errno::Error),
    /// Error doing Vcpu Init on Arm.
    VcpuArmInit,
    /// Error getting the Vcpu preferred target on Arm.
    VcpuArmPreferredTarget,
    /// vCPU count is not initialized.
    VcpuCountNotInitialized,
    /// Cannot run the VCPUs.
    VcpuRun,
    /// Cannot spawn a new vCPU thread.
    VcpuSpawn(io::Error),
    /// Cannot cleanly initialize vcpu TLS.
    VcpuTlsInit,
    /// Vcpu not present in TLS.
    VcpuTlsNotPresent,
    /// Unexpected KVM_RUN exit reason
    VcpuUnhandledKvmExit,
    /// Failed to set KVM vm irqchip.
    VmSetIrqChip,
    /// Cannot configure the microvm.
    VmSetup,
}

impl Display for Error {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        use self::Error::*;

        match self {
            GuestMemoryMmap(e) => write!(f, "Guest memory error: {:?}", e),
            VcpuCountNotInitialized => write!(f, "vCPU count is not initialized"),
            VmSetup => write!(f, "Cannot configure the microvm"),
            VcpuRun => write!(f, "Cannot run the VCPUs"),
            NotEnoughMemorySlots => write!(
                f,
                "The number of configured slots is bigger than the maximum reported by KVM"
            ),
            SetUserMemoryRegion => write!(f, "Cannot set the memory regions"),
            SignalVcpu(e) => write!(f, "Failed to signal Vcpu: {}", e),
            REGSConfiguration(e) => write!(
                f,
                "Error configuring the general purpose aarch64 registers: {:?}",
                e
            ),
            Irq => write!(f, "Cannot configure the IRQ"),
            VcpuSpawn(e) => write!(f, "Cannot spawn a new vCPU thread: {}", e),
            VcpuTlsInit => write!(f, "Cannot clean init vcpu TLS"),
            VcpuTlsNotPresent => write!(f, "Vcpu not present in TLS"),
            VcpuUnhandledKvmExit => write!(f, "Unexpected KVM_RUN exit reason"),
            SetupGIC(e) => write!(
                f,
                "Error setting up the global interrupt controller: {:?}",
                e
            ),
            VcpuArmPreferredTarget => write!(f, "Error getting the Vcpu preferred target on Arm"),
            VcpuArmInit => write!(f, "Error doing Vcpu Init on Arm"),
        }
    }
}

pub type Result<T> = result::Result<T, Error>;

/// Describes a KVM context that gets attached to the microVM.
/// It gives access to the functionality of the KVM wrapper as
/// long as every required KVM capability is present on the host.
pub struct KvmContext {
    max_memslots: usize,
}

impl KvmContext {
    pub fn new() -> Result<Self> {
        Ok(KvmContext { max_memslots: 8 })
    }

    /// Get the maximum number of memory slots reported by this KVM context.
    pub fn max_memslots(&self) -> usize {
        self.max_memslots
    }
}

/// A wrapper around creating and using a VM.
pub struct Vm {
    // Arm specific fields.
    // On aarch64 we need to keep around the fd obtained by creating the VGIC device.
    irqchip_handle: Option<Box<dyn GICDevice>>,
}

impl Vm {
    /// Constructs a new `Vm` using the given `Kvm` instance.
    pub fn new() -> Result<Self> {
        unsafe { hv_call(hv_vm_create(std::ptr::null_mut())).expect("Error initializing HVF") };

        Ok(Vm {
            irqchip_handle: None,
        })
    }

    /// Initializes the guest memory.
    pub fn memory_init(&mut self, guest_mem: &GuestMemoryMmap) -> Result<()> {
        guest_mem
            .with_regions(|index, region| {
                // It's safe to unwrap because the guest address is valid.
                let host_addr = guest_mem.get_host_address(region.start_addr()).unwrap();
                println!(
                    "Guest memory host_addr={:x?} guest_addr={:x?} len={:x?}",
                    host_addr,
                    region.start_addr().raw_value(),
                    region.len()
                );

                guest_mem.with_regions(|_, region| unsafe {
                    hv_call(hv_vm_map(
                        host_addr as *mut core::ffi::c_void,
                        region.start_addr().raw_value() as u64,
                        region.len() as u64,
                        (HV_MEMORY_READ | HV_MEMORY_WRITE | HV_MEMORY_EXEC).into(),
                    ))
                })
            })
            .map_err(|_| Error::SetUserMemoryRegion)?;

        Ok(())
    }

    /// Creates the GIC (Global Interrupt Controller).
    pub fn setup_irqchip(&mut self, vcpu_count: u8) -> Result<()> {
        self.irqchip_handle =
            Some(arch::aarch64::gic::create_gic(vcpu_count.into()).map_err(Error::SetupGIC)?);
        Ok(())
    }

    /// Gets a reference to the irqchip of the VM
    pub fn get_irqchip(&self) -> &Box<dyn GICDevice> {
        &self.irqchip_handle.as_ref().unwrap()
    }
}

/// Encapsulates configuration parameters for the guest vCPUS.
#[derive(Debug, PartialEq)]
pub struct VcpuConfig {
    /// Number of guest VCPUs.
    pub vcpu_count: u8,
    /// Enable hyperthreading in the CPUID configuration.
    pub ht_enabled: bool,
    /// CPUID template to use.
    pub cpu_template: Option<CpuFeaturesTemplate>,
}

struct HvfVcpu<'a> {
    vcpuid: hv_vcpu_t,
    vcpu_exit: &'a hv_vcpu_exit_t,
}

impl<'a> HvfVcpu<'a> {
    unsafe fn new(entry_addr: GuestAddress, fdt_addr: u64) -> Self {
        let mut vcpuid: hv_vcpu_t = 0;
        let vcpu_exit_ptr: *mut hv_vcpu_exit_t = std::ptr::null_mut();

        hv_call(hv_vcpu_create(
            &mut vcpuid,
            &vcpu_exit_ptr as *const _ as *mut *mut _,
            std::ptr::null_mut(),
        ))
        .unwrap();

        hv_call(hv_vcpu_set_reg(
            vcpuid,
            hv_reg_t_HV_REG_CPSR,
            PSTATE_FAULT_BITS_64,
        ))
        .unwrap();
        hv_call(hv_vcpu_set_reg(
            vcpuid,
            hv_reg_t_HV_REG_PC,
            entry_addr.raw_value(),
        ))
        .unwrap();
        hv_call(hv_vcpu_set_reg(vcpuid, hv_reg_t_HV_REG_X0, fdt_addr)).unwrap();

        let pc: u64 = 0;
        hv_call(hv_vcpu_get_reg(
            vcpuid,
            hv_reg_t_HV_REG_PC,
            &pc as *const _ as *mut _,
        ))
        .unwrap();

        /*
        hv_call(hv_vcpu_set_sys_reg(
            vcpuid,
            hv_sys_reg_t_HV_SYS_REG_SP_EL0,
            MAIN_MEMORY + 0x4000,
        ))?;
        hv_call(hv_vcpu_set_sys_reg(
            vcpuid,
            hv_sys_reg_t_HV_SYS_REG_SP_EL1,
            MAIN_MEMORY + 0x8000,
        ))?;
         */

        //hv_call(hv_vcpu_set_trap_debug_exceptions(vcpuid, true))?;

        let vcpu_exit: &hv_vcpu_exit_t = vcpu_exit_ptr.as_mut().unwrap();

        Self { vcpuid, vcpu_exit }
    }
}

// Using this for easier explicit type-casting to help IDEs interpret the code.
type VcpuCell = Cell<Option<*const Vcpu>>;

/// A wrapper around creating and using a kvm-based VCPU.
pub struct Vcpu {
    id: u8,
    fdt_addr: u64,
    create_ts: TimestampUs,
    mmio_bus: Option<devices::Bus>,
    #[cfg_attr(all(test, target_arch = "aarch64"), allow(unused))]
    exit_evt: EventFd,

    #[cfg(target_arch = "aarch64")]
    mpidr: u64,

    // The receiving end of events channel owned by the vcpu side.
    event_receiver: Receiver<VcpuEvent>,
    // The transmitting end of the events channel which will be given to the handler.
    event_sender: Option<Sender<VcpuEvent>>,
    // The receiving end of the responses channel which will be given to the handler.
    response_receiver: Option<Receiver<VcpuResponse>>,
    // The transmitting end of the responses channel owned by the vcpu side.
    response_sender: Sender<VcpuResponse>,
}

impl Vcpu {
    thread_local!(static TLS_VCPU_PTR: VcpuCell = Cell::new(None));

    /// Associates `self` with the current thread.
    ///
    /// It is a prerequisite to successfully run `init_thread_local_data()` before using
    /// `run_on_thread_local()` on the current thread.
    /// This function will return an error if there already is a `Vcpu` present in the TLS.
    fn init_thread_local_data(&mut self) -> Result<()> {
        Self::TLS_VCPU_PTR.with(|cell: &VcpuCell| {
            if cell.get().is_some() {
                return Err(Error::VcpuTlsInit);
            }
            cell.set(Some(self as *const Vcpu));
            Ok(())
        })
    }

    /// Deassociates `self` from the current thread.
    ///
    /// Should be called if the current `self` had called `init_thread_local_data()` and
    /// now needs to move to a different thread.
    ///
    /// Fails if `self` was not previously associated with the current thread.
    fn reset_thread_local_data(&mut self) -> Result<()> {
        // Best-effort to clean up TLS. If the `Vcpu` was moved to another thread
        // _before_ running this, then there is nothing we can do.
        Self::TLS_VCPU_PTR.with(|cell: &VcpuCell| {
            if let Some(vcpu_ptr) = cell.get() {
                if vcpu_ptr == self as *const Vcpu {
                    Self::TLS_VCPU_PTR.with(|cell: &VcpuCell| cell.take());
                    return Ok(());
                }
            }
            Err(Error::VcpuTlsNotPresent)
        })
    }

    /// Runs `func` for the `Vcpu` associated with the current thread.
    ///
    /// It requires that `init_thread_local_data()` was run on this thread.
    ///
    /// Fails if there is no `Vcpu` associated with the current thread.
    ///
    /// # Safety
    ///
    /// This is marked unsafe as it allows temporary aliasing through
    /// dereferencing from pointer an already borrowed `Vcpu`.
    unsafe fn run_on_thread_local<F>(func: F) -> Result<()>
    where
        F: FnOnce(&Vcpu),
    {
        Self::TLS_VCPU_PTR.with(|cell: &VcpuCell| {
            if let Some(vcpu_ptr) = cell.get() {
                // Dereferencing here is safe since `TLS_VCPU_PTR` is populated/non-empty,
                // and it is being cleared on `Vcpu::drop` so there is no dangling pointer.
                let vcpu_ref: &Vcpu = &*vcpu_ptr;
                func(vcpu_ref);
                Ok(())
            } else {
                Err(Error::VcpuTlsNotPresent)
            }
        })
    }

    /// Registers a signal handler which makes use of TLS and kvm immediate exit to
    /// kick the vcpu running on the current thread, if there is one.
    pub fn register_kick_signal_handler() {
        extern "C" fn handle_signal(_: c_int, _: *mut siginfo_t, _: *mut c_void) {
            // This is safe because it's temporarily aliasing the `Vcpu` object, but we are
            // only reading `vcpu.fd` which does not change for the lifetime of the `Vcpu`.
            unsafe {
                let _ = Vcpu::run_on_thread_local(|vcpu| {
                    //vcpu.fd.set_kvm_immediate_exit(1);
                    fence(Ordering::Release);
                });
            }
        }

        //register_signal_handler(sigrtmin() + VCPU_RTSIG_OFFSET, handle_signal)
        //    .expect("Failed to register vcpu signal handler");
    }

    /// Constructs a new VCPU for `vm`.
    ///
    /// # Arguments
    ///
    /// * `id` - Represents the CPU number between [0, max vcpus).
    /// * `vm_fd` - The kvm `VmFd` for the virtual machine this vcpu will get attached to.
    /// * `exit_evt` - An `EventFd` that will be written into when this vcpu exits.
    /// * `create_ts` - A timestamp used by the vcpu to calculate its lifetime.
    pub fn new_aarch64(
        id: u8,
        _vm: &Vm,
        exit_evt: EventFd,
        create_ts: TimestampUs,
    ) -> Result<Self> {
        //let mut vcpuid: hv_vcpu_t = 0;
        //let vcpu_exit_ptr: *mut hv_vcpu_exit_t = std::ptr::null_mut();

        let (event_sender, event_receiver) = channel();
        let (response_sender, response_receiver) = channel();

        /*
        unsafe {
            hv_call(hv_vcpu_create(
                &mut vcpuid,
                &vcpu_exit_ptr as *const _ as *mut *mut _,
                std::ptr::null_mut(),
            ))
            .unwrap();
        }
        */

        Ok(Vcpu {
            id,
            fdt_addr: 0,
            create_ts,
            mmio_bus: None,
            exit_evt,
            mpidr: 0,
            event_receiver,
            event_sender: Some(event_sender),
            response_receiver: Some(response_receiver),
            response_sender,
        })
    }

    /// Returns the cpu index as seen by the guest OS.
    pub fn cpu_index(&self) -> u8 {
        self.id
    }

    /// Gets the MPIDR register value.
    pub fn get_mpidr(&self) -> u64 {
        self.mpidr
    }

    /// Sets a MMIO bus for this vcpu.
    pub fn set_mmio_bus(&mut self, mmio_bus: devices::Bus) {
        self.mmio_bus = Some(mmio_bus);
    }

    /// Configures an aarch64 specific vcpu.
    ///
    /// # Arguments
    ///
    /// * `vm_fd` - The kvm `VmFd` for this microvm.
    /// * `guest_mem` - The guest memory used by this microvm.
    /// * `kernel_load_addr` - Offset from `guest_mem` at which the kernel is loaded.
    pub fn configure_aarch64(
        &mut self,
        _vm: &Vm,
        guest_mem: &GuestMemoryMmap,
        kernel_load_addr: GuestAddress,
    ) -> Result<()> {
        self.mpidr = 0x410fd083;
        /*
        arch::aarch64::regs::setup_regs(self.id, kernel_load_addr.raw_value(), guest_mem)
            .map_err(Error::REGSConfiguration)?;

        self.mpidr = arch::aarch64::regs::read_mpidr().map_err(Error::REGSConfiguration)?;

        unsafe {
            hv_call(hv_vcpu_set_reg(
                self.vcpuid,
                hv_reg_t_HV_REG_CPSR,
                PSTATE_FAULT_BITS_64,
            ))
            .unwrap();
            hv_call(hv_vcpu_set_reg(
                self.vcpuid,
                hv_reg_t_HV_REG_PC,
                kernel_load_addr.raw_value(),
            ))
            .unwrap();
            hv_call(hv_vcpu_set_reg(
                self.vcpuid,
                hv_reg_t_HV_REG_X0,
                /*fdt_addr*/ 0,
            ))
            .unwrap();

            let pc: u64 = 0;
            hv_call(hv_vcpu_get_reg(
                self.vcpuid,
                hv_reg_t_HV_REG_PC,
                &pc as *const _ as *mut _,
            ))
            .unwrap();
        }
         */
        self.fdt_addr = arch::aarch64::get_fdt_addr(guest_mem);

        Ok(())
    }

    /// Moves the vcpu to its own thread and constructs a VcpuHandle.
    /// The handle can be used to control the remote vcpu.
    pub fn start_threaded(mut self) -> Result<VcpuHandle> {
        let event_sender = self.event_sender.take().unwrap();
        let response_receiver = self.response_receiver.take().unwrap();
        let (init_tls_sender, init_tls_receiver) = channel();
        let vcpu_thread = thread::Builder::new()
            .name(format!("fc_vcpu {}", self.cpu_index()))
            .spawn(move || {
                self.init_thread_local_data()
                    .expect("Cannot cleanly initialize vcpu TLS.");

                init_tls_sender
                    .send(true)
                    .expect("Cannot notify vcpu TLS initialization.");

                //self.hvf_vcpu =
                //    Some(unsafe { HvfVcpu::new(GuestAddress(0x80000000), self.fdt_addr) });

                self.run();
            })
            .map_err(Error::VcpuSpawn)?;

        init_tls_receiver
            .recv()
            .expect("Error waiting for TLS initialization.");

        Ok(VcpuHandle::new(
            event_sender,
            response_receiver,
            vcpu_thread,
        ))
    }

    fn check_boot_complete_signal(&self, addr: u64, data: &[u8]) {
        if addr == MAGIC_IOPORT_SIGNAL_GUEST_BOOT_COMPLETE
            && data[0] == MAGIC_VALUE_SIGNAL_GUEST_BOOT_COMPLETE
        {
            super::super::Vmm::log_boot_time(&self.create_ts);
        }
    }

    /// Runs the vCPU in KVM context and handles the kvm exit reason.
    ///
    /// Returns error or enum specifying whether emulation was handled or interrupted.
    fn run_emulation(&mut self, vcpu: &HvfVcpu) -> Result<VcpuEmulation> {
        //let vcpu = self.hvf_vcpu.as_ref().unwrap();
        //let vcpu_exit: &hv_vcpu_exit_t =
        //   unsafe { (vcpu.vcpu_exit_addr as *mut _).as_mut().unwrap() };
        //println!("vcpu_exit2: {:?}", vcpu_exit);
        let vcpu_exit = vcpu.vcpu_exit;

        hv_call(unsafe { hv_vcpu_run(vcpu.vcpuid) }).unwrap();
        match vcpu_exit.reason {
            hv_exit_reason_t_HV_EXIT_REASON_EXCEPTION => {
                let pc: u64 = 0;
                hv_call(unsafe {
                    hv_vcpu_get_reg(vcpu.vcpuid, hv_reg_t_HV_REG_PC, &pc as *const _ as *mut _)
                })
                .unwrap();
                //println!("exception with pc at 0x{:x}", pc);

                let syndrome = vcpu_exit.exception.syndrome;
                let ec = (syndrome >> 26) & 0x3f;

                let mut advance_pc = false;
                match ec {
                    EC_AA64_HVC => println!("HVC call"),
                    EC_AA64_SMC => {
                        println!("SMC call");
                        advance_pc = true;
                    }
                    EC_SYSTEMREGISTERTRAP => {
                        let isread: bool = ((syndrome >> 0) & 1) != 0;
                        let rt: u32 = ((syndrome >> 5) & 0x1f) as u32;
                        let reg: u64 = syndrome & SYSREG_MASK;

                        /*
                        println!("sysreg operation reg={} (op0={} op1={} op2={} crn={} crm={}) isread={:?}",
                                     reg, (reg >> 20) & 0x3,
                                     (reg >> 14) & 0x7, (reg >> 17) & 0x7,
                                     (reg >> 10) & 0xf, (reg >> 1) & 0xf,
                                     isread);
                        */

                        if isread {
                            //let val: u64 = 0;
                            //self.read_sys_reg(reg);
                            //hv_call(hv_vcpu_set_reg(self.vcpuid, rt, val))?;
                        } else {
                            //let val: u64 = 0;
                            //hv_call(hv_vcpu_get_reg(vcpu.vcpuid, rt, &val as *const _ as *mut _))?;
                            //self.write_sys_reg(reg);
                            //hv_call(hv_vcpu_set_sys_reg(self.vcpuid, reg as u16, val))?;
                        }

                        advance_pc = true;
                    }
                    EC_DATAABORT => {
                        let isv: bool = (syndrome & (1 << 24)) != 0;
                        let iswrite: bool = ((syndrome >> 6) & 1) != 0;
                        let s1ptw: bool = ((syndrome >> 7) & 1) != 0;
                        let sas: u32 = (syndrome as u32 >> 22) & 3;
                        let len: usize = (1 << sas) as usize;
                        let srt: u32 = (syndrome as u32 >> 16) & 0x1f;

                        if vcpu_exit.exception.physical_address > 0x40004000
                            && vcpu_exit.exception.physical_address < 0x40005000
                        {
                            //println!("data abort: pc={:x} va={:x}, pa={:x}, isv={}, iswrite={:?}, s1ptrw={}, len={}, srt={}", pc, vcpu_exit.exception.virtual_address, vcpu_exit.exception.physical_address, isv, iswrite, s1ptw, len, srt);
                        }

                        let pa = vcpu_exit.exception.physical_address;
                        if iswrite {
                            let val: u64 = 0;
                            if srt < 31 {
                                hv_call(unsafe {
                                    hv_vcpu_get_reg(
                                        vcpu.vcpuid,
                                        hv_reg_t_HV_REG_X0 + srt,
                                        &val as *const _ as *mut _,
                                    )
                                })
                                .unwrap();
                            }

                            if let Some(ref mmio_bus) = self.mmio_bus {
                                match len {
                                    1 => {
                                        let data = (val as u8).to_le_bytes();
                                        mmio_bus.write(pa, &data);
                                    }
                                    4 => {
                                        let data = (val as u32).to_le_bytes();
                                        mmio_bus.write(pa, &data);
                                    }
                                    8 => {
                                        let data = (val as u64).to_le_bytes();
                                        mmio_bus.write(pa, &data);
                                    }
                                    _ => panic!("unsupported mmio len={}", len),
                                };
                            } else {
                                println!("no mmio_bus");
                            }

                            //if self.uart.is_owner(pa) {
                            //    self.uart.handle_write(pa, val);
                            //} else if self.gic.is_owner(pa) {
                            //    self.gic.handle_write(pa, val);
                            //} else {
                            //println!("write to unhandled address={:x}", pa);
                            //}
                        } else {
                            if let Some(ref mmio_bus) = self.mmio_bus {
                                let val: u64 = match len {
                                    1 => {
                                        let mut data: [u8; 1] = [0; 1];
                                        mmio_bus.read(pa, &mut data);
                                        u8::from_le_bytes(data) as u64
                                    }
                                    2 => {
                                        let mut data: [u8; 2] = [0; 2];
                                        mmio_bus.read(pa, &mut data);
                                        u16::from_le_bytes(data) as u64
                                    }
                                    4 => {
                                        let mut data: [u8; 4] = [0; 4];
                                        mmio_bus.read(pa, &mut data);
                                        u32::from_le_bytes(data) as u64
                                    }
                                    8 => {
                                        let mut data: [u8; 8] = [0; 8];
                                        mmio_bus.read(pa, &mut data);
                                        u64::from_le_bytes(data) as u64
                                    }
                                    _ => panic!("unsupported mmio len={} pa=0x{:x}", len, pa),
                                };
                                if srt < 31 {
                                    hv_call(unsafe {
                                        hv_vcpu_set_reg(vcpu.vcpuid, hv_reg_t_HV_REG_X0 + srt, val)
                                    })
                                    .unwrap();
                                }
                            } else {
                                println!("no mmio_bus");
                            }
                            //let val = if self.uart.is_owner(pa) {
                            //    self.uart.handle_read(pa)
                            //} else {
                            //println!("read from unhandled address={:x}", pa);
                            //    0
                            //};
                            //hv_call(hv_vcpu_set_reg(self.vcpuid, hv_reg_t_HV_REG_X0 + srt, val))?;
                        }

                        advance_pc = true;
                    }
                    EC_AA64_BKPT => {
                        println!("BRK call");
                    }
                    EC_WFX_TRAP => {
                        //println!("WFX_TRAP: pc=0x{:x}", pc);
                        advance_pc = true;
                        std::thread::sleep(std::time::Duration::from_millis(10));
                    }
                    _ => panic!("unexpected exception: 0x{:x}", ec),
                }

                if advance_pc {
                    let pc: u64 = 0;
                    hv_call(unsafe {
                        hv_vcpu_get_reg(vcpu.vcpuid, hv_reg_t_HV_REG_PC, &pc as *const _ as *mut _)
                    })
                    .unwrap();
                    hv_call(unsafe { hv_vcpu_set_reg(vcpu.vcpuid, hv_reg_t_HV_REG_PC, pc + 4) })
                        .unwrap();
                }
            }

            _ => {
                let pc: u64 = 0;
                hv_call(unsafe {
                    hv_vcpu_get_reg(vcpu.vcpuid, hv_reg_t_HV_REG_PC, &pc as *const _ as *mut _)
                })
                .unwrap();

                println!("unexpected exit reason: pc=0x{:x}", pc);
            }
        }
        Ok(VcpuEmulation::Handled)
    }

    /// Main loop of the vCPU thread.
    ///
    /// Runs the vCPU in KVM context in a loop. Handles KVM_EXITs then goes back in.
    /// Note that the state of the VCPU and associated VM must be setup first for this to do
    /// anything useful.
    pub fn run(&mut self) {
        // Start running the machine state in the `Paused` state.
        StateMachine::run(self, Self::paused);
    }

    // This is the main loop of the `Running` state.
    fn running(&mut self) -> StateMachine<Self> {
        // This loop is here just for optimizing the emulation path.
        // No point in ticking the state machine if there are no external events.
        let vcpu = unsafe { HvfVcpu::new(GuestAddress(0x80000000), self.fdt_addr) };
        loop {
            match self.run_emulation(&vcpu) {
                // Emulation ran successfully, continue.
                Ok(VcpuEmulation::Handled) => (),
                // Emulation was interrupted, check external events.
                Ok(VcpuEmulation::Interrupted) => break,
                // If the guest was rebooted or halted:
                // - vCPU0 will always exit out of `KVM_RUN` with KVM_EXIT_SHUTDOWN or
                //   KVM_EXIT_HLT.
                // - the other vCPUs won't ever exit out of `KVM_RUN`, but they won't consume CPU.
                // Moreover if we allow the vCPU0 thread to finish execution, this might generate a
                // seccomp failure because musl calls `sigprocmask` as part of `pthread_exit`.
                // So we pause vCPU0 and send a signal to the emulation thread to stop the VMM.
                Ok(VcpuEmulation::Stopped) => return self.exit(FC_EXIT_CODE_OK),
                // Emulation errors lead to vCPU exit.
                Err(_) => return self.exit(FC_EXIT_CODE_GENERIC_ERROR),
            }
        }

        // By default don't change state.
        let mut state = StateMachine::next(Self::running);

        // Break this emulation loop on any transition request/external event.
        match self.event_receiver.try_recv() {
            // Running ---- Pause ----> Paused
            Ok(VcpuEvent::Pause) => {
                // Nothing special to do.
                self.response_sender
                    .send(VcpuResponse::Paused)
                    .expect("failed to send pause status");

                // TODO: we should call `KVM_KVMCLOCK_CTRL` here to make sure
                // TODO continued: the guest soft lockup watchdog does not panic on Resume.

                // Move to 'paused' state.
                state = StateMachine::next(Self::paused);
            }
            Ok(VcpuEvent::Resume) => {
                self.response_sender
                    .send(VcpuResponse::Resumed)
                    .expect("failed to send resume status");
            }
            // Unhandled exit of the other end.
            Err(TryRecvError::Disconnected) => {
                // Move to 'exited' state.
                state = self.exit(FC_EXIT_CODE_GENERIC_ERROR);
            }
            // All other events or lack thereof have no effect on current 'running' state.
            Err(TryRecvError::Empty) => (),
        }

        state
    }

    // This is the main loop of the `Paused` state.
    fn paused(&mut self) -> StateMachine<Self> {
        match self.event_receiver.recv() {
            // Paused ---- Resume ----> Running
            Ok(VcpuEvent::Resume) => {
                // Nothing special to do.
                self.response_sender
                    .send(VcpuResponse::Resumed)
                    .expect("failed to send resume status");
                // Move to 'running' state.
                StateMachine::next(Self::running)
            }
            // All other events have no effect on current 'paused' state.
            Ok(_) => StateMachine::next(Self::paused),
            // Unhandled exit of the other end.
            Err(_) => {
                // Move to 'exited' state.
                self.exit(FC_EXIT_CODE_GENERIC_ERROR)
            }
        }
    }

    #[cfg(not(test))]
    // Transition to the exited state.
    fn exit(&mut self, exit_code: u8) -> StateMachine<Self> {
        self.response_sender
            .send(VcpuResponse::Exited(exit_code))
            .expect("failed to send Exited status");

        if let Err(e) = self.exit_evt.write(1) {
            error!("Failed signaling vcpu exit event: {}", e);
        }

        // State machine reached its end.
        StateMachine::next(Self::exited)
    }

    #[cfg(not(test))]
    // This is the main loop of the `Exited` state.
    fn exited(&mut self) -> StateMachine<Self> {
        // Wait indefinitely.
        // The VMM thread will kill the entire process.
        let barrier = Barrier::new(2);
        barrier.wait();

        StateMachine::finish()
    }

    #[cfg(test)]
    // In tests the main/vmm thread exits without 'exit()'ing the whole process.
    // All channels get closed on the other side while this Vcpu thread is still running.
    // This Vcpu thread should just do a clean finish without reporting back to the main thread.
    fn exit(&mut self, _: u8) -> StateMachine<Self> {
        // State machine reached its end.
        StateMachine::finish()
    }
}

impl Drop for Vcpu {
    fn drop(&mut self) {
        let _ = self.reset_thread_local_data();
    }
}

// Allow currently unused Pause and Exit events. These will be used by the vmm later on.
#[allow(unused)]
#[derive(Debug)]
/// List of events that the Vcpu can receive.
pub enum VcpuEvent {
    /// Pause the Vcpu.
    Pause,
    /// Event that should resume the Vcpu.
    Resume,
    // Serialize and Deserialize to follow after we get the support from kvm-ioctls.
}

#[derive(Debug, PartialEq)]
/// List of responses that the Vcpu reports.
pub enum VcpuResponse {
    /// Vcpu is paused.
    Paused,
    /// Vcpu is resumed.
    Resumed,
    /// Vcpu is stopped.
    Exited(u8),
}

/// Wrapper over Vcpu that hides the underlying interactions with the Vcpu thread.
pub struct VcpuHandle {
    event_sender: Sender<VcpuEvent>,
    response_receiver: Receiver<VcpuResponse>,
    // Rust JoinHandles have to be wrapped in Option if you ever plan on 'join()'ing them.
    // We want to be able to join these threads in tests.
    vcpu_thread: Option<thread::JoinHandle<()>>,
}

impl VcpuHandle {
    pub fn new(
        event_sender: Sender<VcpuEvent>,
        response_receiver: Receiver<VcpuResponse>,
        vcpu_thread: thread::JoinHandle<()>,
    ) -> Self {
        Self {
            event_sender,
            response_receiver,
            vcpu_thread: Some(vcpu_thread),
        }
    }

    pub fn send_event(&self, event: VcpuEvent) -> Result<()> {
        // Use expect() to crash if the other thread closed this channel.
        self.event_sender
            .send(event)
            .expect("event sender channel closed on vcpu end.");
        // Kick the vcpu so it picks up the message.
        /*
        self.vcpu_thread
            .as_ref()
            // Safe to unwrap since constructor make this 'Some'.
            .unwrap()
            .kill(sigrtmin() + VCPU_RTSIG_OFFSET)
            .map_err(Error::SignalVcpu)?;
        */
        Ok(())
    }

    pub fn response_receiver(&self) -> &Receiver<VcpuResponse> {
        &self.response_receiver
    }
}

enum VcpuEmulation {
    Handled,
    Interrupted,
    Stopped,
}

#[cfg(test)]
mod tests {
    use std::fs::File;
    #[cfg(target_arch = "x86_64")]
    use std::os::unix::io::AsRawFd;
    #[cfg(target_arch = "x86_64")]
    use std::sync::mpsc;
    use std::sync::{Arc, Barrier};
    #[cfg(target_arch = "x86_64")]
    use std::time::Duration;

    use super::super::devices;
    use super::*;

    use utils::signal::validate_signal_num;

    // In tests we need to close any pending Vcpu threads on test completion.
    impl Drop for VcpuHandle {
        fn drop(&mut self) {
            // Make sure the Vcpu is out of KVM_RUN.
            self.send_event(VcpuEvent::Pause).unwrap();
            // Close the original channel so that the Vcpu thread errors and goes to exit state.
            let (event_sender, _event_receiver) = channel();
            self.event_sender = event_sender;
            // Wait for the Vcpu thread to finish execution
            self.vcpu_thread.take().unwrap().join().unwrap();
        }
    }

    // Auxiliary function being used throughout the tests.
    fn setup_vcpu(mem_size: usize) -> (Vm, Vcpu, GuestMemoryMmap) {
        let kvm = KvmContext::new().unwrap();
        let gm = GuestMemoryMmap::from_ranges(&[(GuestAddress(0), mem_size)]).unwrap();
        let mut vm = Vm::new(kvm.fd()).expect("Cannot create new vm");
        assert!(vm.memory_init(&gm, kvm.max_memslots()).is_ok());

        let exit_evt = EventFd::new(utils::eventfd::EFD_NONBLOCK).unwrap();

        let vcpu;
        #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
        {
            vm.setup_irqchip().unwrap();
            vcpu = Vcpu::new_x86_64(
                1,
                vm.fd(),
                vm.supported_cpuid().clone(),
                vm.supported_msrs().clone(),
                devices::Bus::new(),
                exit_evt,
                super::super::TimestampUs::default(),
            )
            .unwrap();
        }
        #[cfg(target_arch = "aarch64")]
        {
            vcpu = Vcpu::new_aarch64(1, vm.fd(), exit_evt, super::super::TimestampUs::default())
                .unwrap();
            vm.setup_irqchip(1).expect("Cannot setup irqchip");
        }

        (vm, vcpu, gm)
    }

    #[test]
    fn test_set_mmio_bus() {
        let (_, mut vcpu, _) = setup_vcpu(0x1000);
        assert!(vcpu.mmio_bus.is_none());
        vcpu.set_mmio_bus(devices::Bus::new());
        assert!(vcpu.mmio_bus.is_some());
    }

    #[test]
    #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
    fn test_get_supported_cpuid() {
        let kvm = KvmContext::new().unwrap();
        let vm = Vm::new(kvm.fd()).expect("Cannot create new vm");
        let cpuid = kvm
            .kvm
            .get_supported_cpuid(KVM_MAX_CPUID_ENTRIES)
            .expect("Cannot get supported cpuid");
        assert_eq!(vm.supported_cpuid().as_slice(), cpuid.as_slice());
    }

    #[test]
    fn test_vm_memory_init() {
        let mut kvm_context = KvmContext::new().unwrap();
        let mut vm = Vm::new(kvm_context.fd()).expect("Cannot create new vm");

        // Create valid memory region and test that the initialization is successful.
        let gm = GuestMemoryMmap::from_ranges(&[(GuestAddress(0), 0x1000)]).unwrap();
        assert!(vm.memory_init(&gm, kvm_context.max_memslots()).is_ok());

        // Set the maximum number of memory slots to 1 in KvmContext to check the error
        // path of memory_init. Create 2 non-overlapping memory slots.
        kvm_context.max_memslots = 1;
        let gm = GuestMemoryMmap::from_ranges(&[
            (GuestAddress(0x0), 0x1000),
            (GuestAddress(0x1001), 0x2000),
        ])
        .unwrap();
        assert!(vm.memory_init(&gm, kvm_context.max_memslots()).is_err());
    }

    #[cfg(target_arch = "x86_64")]
    #[test]
    fn test_setup_irqchip() {
        let kvm_context = KvmContext::new().unwrap();
        let vm = Vm::new(kvm_context.fd()).expect("Cannot create new vm");

        vm.setup_irqchip().expect("Cannot setup irqchip");
        // Trying to setup two irqchips will result in EEXIST error. At the moment
        // there is no good way of testing the actual error because io::Error does not implement
        // PartialEq.
        assert!(vm.setup_irqchip().is_err());

        let _vcpu = Vcpu::new_x86_64(
            1,
            vm.fd(),
            vm.supported_cpuid().clone(),
            vm.supported_msrs().clone(),
            devices::Bus::new(),
            EventFd::new(utils::eventfd::EFD_NONBLOCK).unwrap(),
            super::super::TimestampUs::default(),
        )
        .unwrap();
        // Trying to setup irqchip after KVM_VCPU_CREATE was called will result in error.
        assert!(vm.setup_irqchip().is_err());
    }

    #[cfg(target_arch = "aarch64")]
    #[test]
    fn test_setup_irqchip() {
        let kvm = KvmContext::new().unwrap();

        let mut vm = Vm::new(kvm.fd()).expect("Cannot create new vm");
        let vcpu_count = 1;
        let _vcpu = Vcpu::new_aarch64(
            1,
            vm.fd(),
            EventFd::new(utils::eventfd::EFD_NONBLOCK).unwrap(),
            super::super::TimestampUs::default(),
        )
        .unwrap();

        vm.setup_irqchip(vcpu_count).expect("Cannot setup irqchip");
        // Trying to setup two irqchips will result in EEXIST error.
        assert!(vm.setup_irqchip(vcpu_count).is_err());
    }

    #[cfg(target_arch = "x86_64")]
    #[test]
    fn test_configure_vcpu() {
        let (_vm, mut vcpu, vm_mem) = setup_vcpu(0x10000);

        let mut vcpu_config = VcpuConfig {
            vcpu_count: 1,
            ht_enabled: false,
            cpu_template: None,
        };

        assert!(vcpu
            .configure_x86_64(&vm_mem, GuestAddress(0), &vcpu_config)
            .is_ok());

        // Test configure while using the T2 template.
        vcpu_config.cpu_template = Some(CpuFeaturesTemplate::T2);
        assert!(vcpu
            .configure_x86_64(&vm_mem, GuestAddress(0), &vcpu_config)
            .is_ok());

        // Test configure while using the C3 template.
        vcpu_config.cpu_template = Some(CpuFeaturesTemplate::C3);
        assert!(vcpu
            .configure_x86_64(&vm_mem, GuestAddress(0), &vcpu_config)
            .is_ok());
    }

    #[cfg(target_arch = "aarch64")]
    #[test]
    fn test_configure_vcpu() {
        let kvm = KvmContext::new().unwrap();
        let gm = GuestMemoryMmap::from_ranges(&[(GuestAddress(0), 0x10000)]).unwrap();
        let mut vm = Vm::new(kvm.fd()).expect("new vm failed");
        assert!(vm.memory_init(&gm, kvm.max_memslots()).is_ok());

        // Try it for when vcpu id is 0.
        let mut vcpu = Vcpu::new_aarch64(
            0,
            vm.fd(),
            EventFd::new(utils::eventfd::EFD_NONBLOCK).unwrap(),
            super::super::TimestampUs::default(),
        )
        .unwrap();

        assert!(vcpu
            .configure_aarch64(vm.fd(), &gm, GuestAddress(0))
            .is_ok());

        // Try it for when vcpu id is NOT 0.
        let mut vcpu = Vcpu::new_aarch64(
            1,
            vm.fd(),
            EventFd::new(utils::eventfd::EFD_NONBLOCK).unwrap(),
            super::super::TimestampUs::default(),
        )
        .unwrap();

        assert!(vcpu
            .configure_aarch64(vm.fd(), &gm, GuestAddress(0))
            .is_ok());
    }

    #[test]
    fn test_kvm_context() {
        use std::os::unix::fs::MetadataExt;
        use std::os::unix::io::{AsRawFd, FromRawFd};

        let c = KvmContext::new().unwrap();

        assert!(c.max_memslots >= 32);

        let kvm = Kvm::new().unwrap();
        let f = unsafe { File::from_raw_fd(kvm.as_raw_fd()) };
        let m1 = f.metadata().unwrap();
        let m2 = File::open("/dev/kvm").unwrap().metadata().unwrap();

        assert_eq!(m1.dev(), m2.dev());
        assert_eq!(m1.ino(), m2.ino());
    }

    #[test]
    fn test_vcpu_tls() {
        let (_, mut vcpu, _) = setup_vcpu(0x1000);

        // Running on the TLS vcpu should fail before we actually initialize it.
        unsafe {
            assert!(Vcpu::run_on_thread_local(|_| ()).is_err());
        }

        // Initialize vcpu TLS.
        vcpu.init_thread_local_data().unwrap();

        // Validate TLS vcpu is the local vcpu by changing the `id` then validating against
        // the one in TLS.
        vcpu.id = 12;
        unsafe {
            assert!(Vcpu::run_on_thread_local(|v| assert_eq!(v.id, 12)).is_ok());
        }

        // Reset vcpu TLS.
        assert!(vcpu.reset_thread_local_data().is_ok());

        // Running on the TLS vcpu after TLS reset should fail.
        unsafe {
            assert!(Vcpu::run_on_thread_local(|_| ()).is_err());
        }

        // Second reset should return error.
        assert!(vcpu.reset_thread_local_data().is_err());
    }

    #[test]
    fn test_invalid_tls() {
        let (_, mut vcpu, _) = setup_vcpu(0x1000);
        // Initialize vcpu TLS.
        vcpu.init_thread_local_data().unwrap();
        // Trying to initialize non-empty TLS should error.
        vcpu.init_thread_local_data().unwrap_err();
    }

    #[test]
    fn test_vcpu_kick() {
        Vcpu::register_kick_signal_handler();
        let (vm, mut vcpu, _mem) = setup_vcpu(0x1000);

        let kvm_run =
            KvmRunWrapper::mmap_from_fd(&vcpu.fd, vm.fd.run_size()).expect("cannot mmap kvm-run");
        let success = Arc::new(std::sync::atomic::AtomicBool::new(false));
        let vcpu_success = success.clone();
        let barrier = Arc::new(Barrier::new(2));
        let vcpu_barrier = barrier.clone();
        // Start Vcpu thread which will be kicked with a signal.
        let handle = std::thread::Builder::new()
            .name("test_vcpu_kick".to_string())
            .spawn(move || {
                vcpu.init_thread_local_data().unwrap();
                // Notify TLS was populated.
                vcpu_barrier.wait();
                // Loop for max 1 second to check if the signal handler has run.
                for _ in 0..10 {
                    if kvm_run.as_mut_ref().immediate_exit == 1 {
                        // Signal handler has run and set immediate_exit to 1.
                        vcpu_success.store(true, Ordering::Release);
                        break;
                    }
                    std::thread::sleep(std::time::Duration::from_millis(100));
                }
            })
            .expect("cannot start thread");

        // Wait for the vcpu to initialize its TLS.
        barrier.wait();
        // Kick the Vcpu using the custom signal.
        handle
            .kill(sigrtmin() + VCPU_RTSIG_OFFSET)
            .expect("failed to signal thread");
        handle.join().expect("failed to join thread");
        // Verify that the Vcpu saw its kvm immediate-exit as set.
        assert!(success.load(Ordering::Acquire));
    }

    #[cfg(target_arch = "x86_64")]
    // Sends an event to a vcpu and expects a particular response.
    fn queue_event_expect_response(handle: &VcpuHandle, event: VcpuEvent, response: VcpuResponse) {
        handle
            .send_event(event)
            .expect("failed to send event to vcpu");
        assert_eq!(
            handle
                .response_receiver()
                .recv_timeout(Duration::from_millis(100))
                .expect("did not receive event response from vcpu"),
            response
        );
    }

    #[cfg(target_arch = "x86_64")]
    // Sends an event to a vcpu and expects no response.
    fn queue_event_expect_timeout(handle: &VcpuHandle, event: VcpuEvent) {
        handle
            .send_event(event)
            .expect("failed to send event to vcpu");
        assert_eq!(
            handle
                .response_receiver()
                .recv_timeout(Duration::from_millis(100)),
            Err(mpsc::RecvTimeoutError::Timeout)
        );
    }

    #[test]
    fn test_vcpu_rtsig_offset() {
        assert!(validate_signal_num(sigrtmin() + VCPU_RTSIG_OFFSET).is_ok());
    }

    #[cfg(target_arch = "x86_64")]
    #[test]
    fn test_vm_save_restore_state() {
        let kvm_fd = Kvm::new().unwrap();
        let vm = Vm::new(&kvm_fd).expect("new vm failed");
        // Irqchips, clock and pitstate are not configured so trying to save state should fail.
        assert!(vm.save_state().is_err());

        let (vm, _, _mem) = setup_vcpu(0x1000);
        let vm_state = vm.save_state().unwrap();
        assert_eq!(
            vm_state.pitstate.flags | KVM_PIT_SPEAKER_DUMMY,
            KVM_PIT_SPEAKER_DUMMY
        );
        assert_eq!(vm_state.clock.flags & KVM_CLOCK_TSC_STABLE, 0);
        assert_eq!(vm_state.pic_master.chip_id, KVM_IRQCHIP_PIC_MASTER);
        assert_eq!(vm_state.pic_slave.chip_id, KVM_IRQCHIP_PIC_SLAVE);
        assert_eq!(vm_state.ioapic.chip_id, KVM_IRQCHIP_IOAPIC);

        let (vm, _, _mem) = setup_vcpu(0x1000);
        assert!(vm.restore_state(&vm_state).is_ok());
    }

    #[cfg(target_arch = "x86_64")]
    #[test]
    fn test_vcpu_save_restore_state() {
        let (_vm, vcpu, _mem) = setup_vcpu(0x1000);
        let state = vcpu.save_state();
        assert!(state.is_ok());
        assert!(vcpu.restore_state(state.unwrap()).is_ok());

        unsafe { libc::close(vcpu.fd.as_raw_fd()) };
        let state = VcpuState {
            cpuid: CpuId::new(1),
            msrs: Msrs::new(1),
            debug_regs: Default::default(),
            lapic: Default::default(),
            mp_state: Default::default(),
            regs: Default::default(),
            sregs: Default::default(),
            vcpu_events: Default::default(),
            xcrs: Default::default(),
            xsave: Default::default(),
        };
        // Setting default state should always fail.
        assert!(vcpu.restore_state(state).is_err());
    }
}
