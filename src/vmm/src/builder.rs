// Copyright 2019 Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Enables pre-boot setup, instantiation and booting of a Firecracker VMM.

use std::fmt::{Display, Formatter};
use std::io;
use std::os::unix::io::{AsRawFd, RawFd};
use std::sync::{Arc, Mutex};

use super::{Error, Vmm};

#[cfg(target_arch = "x86_64")]
use device_manager::legacy::PortIODeviceManager;
use device_manager::mmio::MMIODeviceManager;
use devices::legacy::{Gic, Serial};
use devices::virtio::MmioTransport;
#[cfg(target_os = "linux")]
use devices::virtio::{Vsock, VsockUnixBackend};

use polly::event_manager::{Error as EventManagerError, EventManager};
#[cfg(target_os = "linux")]
use signal_handler::register_sigwinch_handler;
use utils::eventfd::EventFd;
use utils::terminal::Terminal;
use utils::time::TimestampUs;
use vm_memory::{mmap::GuestRegionMmap, mmap::MmapRegion, Bytes, GuestAddress, GuestMemoryMmap};
use vmm_config::boot_source::DEFAULT_KERNEL_CMDLINE;
use vmm_config::fs::FsBuilder;
#[cfg(target_os = "linux")]
use vstate::KvmContext;
use vstate::{Vcpu, VcpuConfig, Vm};
use {device_manager, VmmEventsObserver};

/// Errors associated with starting the instance.
#[derive(Debug)]
pub enum StartMicrovmError {
    /// Unable to attach block device to Vmm.
    AttachBlockDevice(io::Error),
    /// Failed to create a `RateLimiter` object.
    CreateRateLimiter(io::Error),
    /// Memory regions are overlapping or mmap fails.
    GuestMemoryMmap(vm_memory::Error),
    /// Cannot load initrd due to an invalid memory configuration.
    InitrdLoad,
    /// Cannot load initrd due to an invalid image.
    InitrdRead(io::Error),
    /// Internal error encountered while starting a microVM.
    Internal(Error),
    /// The kernel command line is invalid.
    KernelCmdline(String),
    /// Cannot inject the kernel into the guest memory due to a problem with the bundle.
    KernelBundle(vm_memory::mmap::MmapRegionError),
    /// Cannot load command line string.
    LoadCommandline(kernel::cmdline::Error),
    /// The start command was issued more than once.
    MicroVMAlreadyRunning,
    /// Cannot start the VM because the kernel was not configured.
    MissingKernelConfig,
    /// Cannot start the VM because the size of the guest memory  was not specified.
    MissingMemSizeConfig,
    /// The net device configuration is missing the tap device.
    NetDeviceNotConfigured,
    /// Cannot open the block device backing file.
    OpenBlockDevice(io::Error),
    /// Cannot initialize a MMIO Balloon device or add a device to the MMIO Bus.
    RegisterBalloonDevice(device_manager::mmio::Error),
    /// Cannot initialize a MMIO Block Device or add a device to the MMIO Bus.
    RegisterBlockDevice(device_manager::mmio::Error),
    /// Cannot register an EventHandler.
    RegisterEvent(EventManagerError),
    /// Cannot initialize a MMIO Fs Device or add ad device to the MMIO Bus.
    RegisterFsDevice(device_manager::mmio::Error),
    /// Cannot register SIGWINCH event file descriptor.
    #[cfg(target_os = "linux")]
    RegisterFsSigwinch(kvm_ioctls::Error),
    /// Cannot initialize a MMIO Network Device or add a device to the MMIO Bus.
    RegisterNetDevice(device_manager::mmio::Error),
    /// Cannot initialize a MMIO Vsock Device or add a device to the MMIO Bus.
    RegisterVsockDevice(device_manager::mmio::Error),
}

/// It's convenient to automatically convert `kernel::cmdline::Error`s
/// to `StartMicrovmError`s.
impl std::convert::From<kernel::cmdline::Error> for StartMicrovmError {
    fn from(e: kernel::cmdline::Error) -> StartMicrovmError {
        StartMicrovmError::KernelCmdline(e.to_string())
    }
}

impl Display for StartMicrovmError {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        use self::StartMicrovmError::*;
        match *self {
            AttachBlockDevice(ref err) => {
                write!(f, "Unable to attach block device to Vmm. Error: {}", err)
            }
            CreateRateLimiter(ref err) => write!(f, "Cannot create RateLimiter: {}", err),
            GuestMemoryMmap(ref err) => {
                // Remove imbricated quotes from error message.
                let mut err_msg = format!("{:?}", err);
                err_msg = err_msg.replace("\"", "");
                write!(f, "Invalid Memory Configuration: {}", err_msg)
            }
            InitrdLoad => write!(
                f,
                "Cannot load initrd due to an invalid memory configuration."
            ),
            InitrdRead(ref err) => write!(f, "Cannot load initrd due to an invalid image: {}", err),
            Internal(ref err) => write!(f, "Internal error while starting microVM: {:?}", err),
            KernelCmdline(ref err) => write!(f, "Invalid kernel command line: {}", err),
            KernelBundle(ref err) => {
                let mut err_msg = format!("{}", err);
                err_msg = err_msg.replace("\"", "");
                write!(
                    f,
                    "Cannot inject the kernel into the guest memory due to a problem with the \
                     bundle. {}",
                    err_msg
                )
            }
            LoadCommandline(ref err) => {
                let mut err_msg = format!("{}", err);
                err_msg = err_msg.replace("\"", "");
                write!(f, "Cannot load command line string. {}", err_msg)
            }
            MicroVMAlreadyRunning => write!(f, "Microvm already running."),
            MissingKernelConfig => write!(f, "Cannot start microvm without kernel configuration."),
            MissingMemSizeConfig => {
                write!(f, "Cannot start microvm without guest mem_size config.")
            }
            NetDeviceNotConfigured => {
                write!(f, "The net device configuration is missing the tap device.")
            }
            OpenBlockDevice(ref err) => {
                let mut err_msg = format!("{:?}", err);
                err_msg = err_msg.replace("\"", "");

                write!(f, "Cannot open the block device backing file. {}", err_msg)
            }
            RegisterBalloonDevice(ref err) => {
                let mut err_msg = format!("{}", err);
                err_msg = err_msg.replace("\"", "");
                write!(
                    f,
                    "Cannot initialize a MMIO Balloon Device or add a device to the MMIO Bus. {}",
                    err_msg
                )
            }
            RegisterBlockDevice(ref err) => {
                let mut err_msg = format!("{}", err);
                err_msg = err_msg.replace("\"", "");
                write!(
                    f,
                    "Cannot initialize a MMIO Block Device or add a device to the MMIO Bus. {}",
                    err_msg
                )
            }
            RegisterEvent(ref err) => write!(f, "Cannot register EventHandler. {:?}", err),
            RegisterFsDevice(ref err) => {
                let mut err_msg = format!("{}", err);
                err_msg = err_msg.replace("\"", "");

                write!(
                    f,
                    "Cannot initialize a MMIO Fs Device or add a device to the MMIO Bus. {}",
                    err_msg
                )
            }
            #[cfg(target_os = "linux")]
            RegisterFsSigwinch(ref err) => {
                let mut err_msg = format!("{}", err);
                err_msg = err_msg.replace("\"", "");

                write!(
                    f,
                    "Cannot register SIGWINCH file descriptor for Fs Device. {}",
                    err_msg
                )
            }
            RegisterNetDevice(ref err) => {
                let mut err_msg = format!("{}", err);
                err_msg = err_msg.replace("\"", "");

                write!(
                    f,
                    "Cannot initialize a MMIO Network Device or add a device to the MMIO Bus. {}",
                    err_msg
                )
            }
            RegisterVsockDevice(ref err) => {
                let mut err_msg = format!("{}", err);
                err_msg = err_msg.replace("\"", "");

                write!(
                    f,
                    "Cannot initialize a MMIO Vsock Device or add a device to the MMIO Bus. {}",
                    err_msg
                )
            }
        }
    }
}

// Wrapper over io::Stdin that implements `Serial::ReadableFd` and `vmm::VmmEventsObserver`.
pub struct SerialStdin(io::Stdin);
impl SerialStdin {
    /// Returns a `SerialStdin` wrapper over `io::stdin`.
    pub fn get() -> Self {
        let stdin = io::stdin();
        stdin.lock().set_raw_mode().unwrap();
        SerialStdin(stdin)
    }

    pub fn restore() {
        let stdin = io::stdin();
        stdin.lock().set_canon_mode().unwrap();
    }
}

impl io::Read for SerialStdin {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        self.0.read(buf)
    }
}

impl AsRawFd for SerialStdin {
    fn as_raw_fd(&self) -> RawFd {
        self.0.as_raw_fd()
    }
}

impl devices::legacy::ReadableFd for SerialStdin {}

impl VmmEventsObserver for SerialStdin {
    fn on_vmm_boot(&mut self) -> std::result::Result<(), utils::errno::Error> {
        // Set raw mode for stdin.
        self.0.lock().set_raw_mode().map_err(|e| {
            warn!("Cannot set raw mode for the terminal. {:?}", e);
            e
        })
    }
    fn on_vmm_stop(&mut self) -> std::result::Result<(), utils::errno::Error> {
        self.0.lock().set_canon_mode().map_err(|e| {
            warn!("Cannot set canonical mode for the terminal. {:?}", e);
            e
        })
    }
}

/// Builds and starts a microVM based on the current Firecracker VmResources configuration.
///
/// This is the default build recipe, one could build other microVM flavors by using the
/// independent functions in this module instead of calling this recipe.
///
/// An `Arc` reference of the built `Vmm` is also plugged in the `EventManager`, while another
/// is returned.
pub fn build_microvm(
    vm_resources: &super::resources::VmResources,
    event_manager: &mut EventManager,
) -> std::result::Result<Arc<Mutex<Vmm>>, StartMicrovmError> {
    // Timestamp for measuring microVM boot duration.
    let request_ts = TimestampUs::default();

    let kernel_bundle = vm_resources
        .kernel_bundle()
        .ok_or(StartMicrovmError::MissingKernelConfig)?;
    //let kernel_region = unsafe {
    //    MmapRegion::build_raw(kernel_bundle.host_addr as *mut u8, kernel_bundle.size, 0, 0)
    //        .map_err(StartMicrovmError::KernelBundle)?
    //};

    let guest_memory = create_guest_memory(
        vm_resources
            .vm_config()
            .mem_size_mib
            .ok_or(StartMicrovmError::MissingMemSizeConfig)?,
        kernel_bundle.host_addr,
        kernel_bundle.guest_addr,
        kernel_bundle.size,
    )?;
    let vcpu_config = vm_resources.vcpu_config();

    // Clone the command-line so that a failed boot doesn't pollute the original.
    #[allow(unused_mut)]
    let mut kernel_cmdline = kernel::cmdline::Cmdline::new(arch::CMDLINE_MAX_SIZE);
    match &vm_resources.boot_config.kernel_cmdline_prolog {
        None => kernel_cmdline.insert_str(DEFAULT_KERNEL_CMDLINE).unwrap(),
        Some(s) => kernel_cmdline.insert_str(s).unwrap(),
    };
    let mut vm = setup_vm(&guest_memory)?;

    /*
    // On x86_64 always create a serial device,
    // while on aarch64 only create it if 'console=' is specified in the boot args.
    let serial_device = if cfg!(target_arch = "x86_64")
        || (cfg!(target_arch = "aarch64")/*&& kernel_cmdline.as_str().contains("console=")*/)
    {
        Some(setup_serial_device(
            event_manager,
            Box::new(SerialStdin::get()),
            Box::new(io::stdout()),
        )?)
    } else {
        None
    };
     */
    let serial_device = None;

    let exit_evt = EventFd::new(utils::eventfd::EFD_NONBLOCK)
        .map_err(Error::EventFd)
        .map_err(StartMicrovmError::Internal)?;

    #[cfg(target_arch = "x86_64")]
    // Safe to unwrap 'serial_device' as it's always 'Some' on x86_64.
    // x86_64 uses the i8042 reset event as the Vmm exit event.
    let mut pio_device_manager = PortIODeviceManager::new(
        serial_device,
        exit_evt
            .try_clone()
            .map_err(Error::EventFd)
            .map_err(StartMicrovmError::Internal)?,
    )
    .map_err(Error::CreateLegacyDevice)
    .map_err(StartMicrovmError::Internal)?;

    // Instantiate the MMIO device manager.
    // 'mmio_base' address has to be an address which is protected by the kernel
    // and is architectural specific.
    #[allow(unused_mut)]
    let mut mmio_device_manager = MMIODeviceManager::new(
        &mut (arch::MMIO_MEM_START as u64),
        (arch::IRQ_BASE, arch::IRQ_MAX),
    );

    let interrupt_controller = if cfg!(target_os = "macos") {
        Some(Arc::new(Mutex::new(devices::legacy::Gic::new())))
    } else {
        None
    };

    let vcpus;
    // For x86_64 we need to create the interrupt controller before calling `KVM_CREATE_VCPUS`
    // while on aarch64 we need to do it the other way around.
    #[cfg(target_arch = "x86_64")]
    {
        setup_interrupt_controller(&mut vm)?;
        attach_legacy_devices(&vm, &mut pio_device_manager)?;

        vcpus = create_vcpus_x86_64(
            &vm,
            &vcpu_config,
            &guest_memory,
            GuestAddress(kernel_bundle.guest_addr),
            request_ts,
            &pio_device_manager.io_bus,
            &exit_evt,
        )
        .map_err(StartMicrovmError::Internal)?;
    }

    // On aarch64, the vCPUs need to be created (i.e call KVM_CREATE_VCPU) and configured before
    // setting up the IRQ chip because the `KVM_CREATE_VCPU` ioctl will return error if the IRQCHIP
    // was already initialized.
    // Search for `kvm_arch_vcpu_create` in arch/arm/kvm/arm.c.
    #[cfg(target_arch = "aarch64")]
    {
        vcpus = create_vcpus_aarch64(
            &vm,
            &vcpu_config,
            &guest_memory,
            GuestAddress(kernel_bundle.guest_addr),
            request_ts,
            &exit_evt,
        )
        .map_err(StartMicrovmError::Internal)?;

        setup_interrupt_controller(&mut vm, vcpu_config.vcpu_count)?;
        attach_legacy_devices(
            &vm,
            &mut mmio_device_manager,
            &mut kernel_cmdline,
            interrupt_controller.clone(),
            serial_device,
        )?;
    }

    let mut vmm = Vmm {
        //events_observer: Some(Box::new(SerialStdin::get())),
        guest_memory,
        kernel_cmdline,
        vcpus_handles: Vec::new(),
        exit_evt,
        vm,
        mmio_device_manager,
        #[cfg(target_arch = "x86_64")]
        pio_device_manager,
    };

    //println!("attaching balloon");
    attach_balloon_device(&mut vmm, event_manager, interrupt_controller.clone())?;
    //println!("attaching console");
    attach_console_devices(&mut vmm, event_manager, interrupt_controller.clone())?;
    //println!("done attaching console");
    attach_fs_devices(
        &mut vmm,
        &vm_resources.fs,
        event_manager,
        interrupt_controller,
    )?;
    #[cfg(target_os = "linux")]
    if let Some(vsock) = vm_resources.vsock.get() {
        attach_unixsock_vsock_device(&mut vmm, vsock, event_manager, interrupt_controller.clone())?;
    }

    if let Some(s) = &vm_resources.boot_config.kernel_cmdline_epilog {
        vmm.kernel_cmdline.insert_str(s).unwrap();
    };

    // Write the kernel command line to guest memory. This is x86_64 specific, since on
    // aarch64 the command line will be specified through the FDT.
    #[cfg(target_arch = "x86_64")]
    load_cmdline(&vmm)?;

    //println!("system");
    vmm.configure_system(vcpus.as_slice(), &None)
        .map_err(StartMicrovmError::Internal)?;
    //println!("vcpus");
    vmm.start_vcpus(vcpus)
        .map_err(StartMicrovmError::Internal)?;

    //println!("vmm");
    let vmm = Arc::new(Mutex::new(vmm));
    event_manager
        .add_subscriber(vmm.clone())
        .map_err(StartMicrovmError::RegisterEvent)?;
    Ok(vmm)
}

/// Creates GuestMemory of `mem_size_mib` MiB in size.
pub fn create_guest_memory(
    mem_size_mib: usize,
    kernel_host_addr: u64,
    kernel_guest_addr: u64,
    kernel_size: usize,
) -> std::result::Result<GuestMemoryMmap, StartMicrovmError> {
    let mem_size = mem_size_mib << 20;
    let arch_mem_regions = arch::arch_memory_regions(mem_size, kernel_guest_addr, kernel_size);

    let guest_mem = GuestMemoryMmap::from_ranges(&arch_mem_regions)
        /*
          .and_then(|memory| {
              memory.insert_region(Arc::new(GuestRegionMmap::new(
                  kernel_region,
                  GuestAddress(kernel_load_addr as u64),
              )?))
          })
        */
        .map_err(StartMicrovmError::GuestMemoryMmap)?;

    let kernel_data =
        unsafe { std::slice::from_raw_parts(kernel_host_addr as *const _, kernel_size) };
    guest_mem
        .write(kernel_data, GuestAddress(kernel_guest_addr))
        .unwrap();
    Ok(guest_mem)
}

#[cfg(target_arch = "x86_64")]
fn load_cmdline(vmm: &Vmm) -> std::result::Result<(), StartMicrovmError> {
    kernel::loader::load_cmdline(
        vmm.guest_memory(),
        GuestAddress(arch::x86_64::layout::CMDLINE_START),
        &vmm.kernel_cmdline
            .as_cstring()
            .map_err(StartMicrovmError::LoadCommandline)?,
    )
    .map_err(StartMicrovmError::LoadCommandline)
}

#[cfg(target_os = "linux")]
pub(crate) fn setup_vm(
    guest_memory: &GuestMemoryMmap,
) -> std::result::Result<Vm, StartMicrovmError> {
    let kvm = KvmContext::new()
        .map_err(Error::KvmContext)
        .map_err(StartMicrovmError::Internal)?;
    let mut vm = Vm::new(kvm.fd())
        .map_err(Error::Vm)
        .map_err(StartMicrovmError::Internal)?;
    vm.memory_init(&guest_memory, kvm.max_memslots())
        .map_err(Error::Vm)
        .map_err(StartMicrovmError::Internal)?;
    Ok(vm)
}

#[cfg(target_os = "macos")]
pub(crate) fn setup_vm(
    guest_memory: &GuestMemoryMmap,
) -> std::result::Result<Vm, StartMicrovmError> {
    let mut vm = Vm::new()
        .map_err(Error::Vm)
        .map_err(StartMicrovmError::Internal)?;
    vm.memory_init(&guest_memory)
        .map_err(Error::Vm)
        .map_err(StartMicrovmError::Internal)?;
    Ok(vm)
}

/// Sets up the irqchip for a x86_64 microVM.
#[cfg(target_arch = "x86_64")]
pub fn setup_interrupt_controller(vm: &mut Vm) -> std::result::Result<(), StartMicrovmError> {
    vm.setup_irqchip()
        .map_err(Error::Vm)
        .map_err(StartMicrovmError::Internal)
}

/// Sets up the irqchip for a aarch64 microVM.
#[cfg(target_arch = "aarch64")]
pub fn setup_interrupt_controller(
    vm: &mut Vm,
    vcpu_count: u8,
) -> std::result::Result<(), StartMicrovmError> {
    vm.setup_irqchip(vcpu_count)
        .map_err(Error::Vm)
        .map_err(StartMicrovmError::Internal)
}

/// Sets up the serial device.
pub fn setup_serial_device(
    event_manager: &mut EventManager,
    input: Box<dyn devices::legacy::ReadableFd + Send>,
    out: Box<dyn io::Write + Send>,
) -> std::result::Result<Arc<Mutex<Serial>>, StartMicrovmError> {
    let interrupt_evt = EventFd::new(utils::eventfd::EFD_NONBLOCK)
        .map_err(Error::EventFd)
        .map_err(StartMicrovmError::Internal)?;
    let serial = Arc::new(Mutex::new(Serial::new_in_out(interrupt_evt, input, out)));
    if let Err(e) = event_manager.add_subscriber(serial.clone()) {
        // TODO: We just log this message, and immediately return Ok, instead of returning the
        // actual error because this operation always fails with EPERM when adding a fd which
        // has been redirected to /dev/null via dup2 (this may happen inside the jailer).
        // Find a better solution to this (and think about the state of the serial device
        // while we're at it).
        warn!("Could not add serial input event to epoll: {:?}", e);
    }
    Ok(serial)
}

#[cfg(target_arch = "x86_64")]
fn attach_legacy_devices(
    vm: &Vm,
    pio_device_manager: &mut PortIODeviceManager,
) -> std::result::Result<(), StartMicrovmError> {
    pio_device_manager
        .register_devices()
        .map_err(Error::LegacyIOBus)
        .map_err(StartMicrovmError::Internal)?;

    macro_rules! register_irqfd_evt {
        ($evt: ident, $index: expr) => {{
            vm.fd()
                .register_irqfd(&pio_device_manager.$evt, $index)
                .map_err(|e| {
                    Error::LegacyIOBus(device_manager::legacy::Error::EventFd(
                        io::Error::from_raw_os_error(e.errno()),
                    ))
                })
                .map_err(StartMicrovmError::Internal)?;
        }};
    }

    register_irqfd_evt!(com_evt_1_3, 4);
    register_irqfd_evt!(com_evt_2_4, 3);
    register_irqfd_evt!(kbd_evt, 1);
    Ok(())
}

#[cfg(target_arch = "aarch64")]
fn attach_legacy_devices(
    vm: &Vm,
    mmio_device_manager: &mut MMIODeviceManager,
    kernel_cmdline: &mut kernel::cmdline::Cmdline,
    interrupt_controller: Option<Arc<Mutex<Gic>>>,
    serial: Option<Arc<Mutex<Serial>>>,
) -> std::result::Result<(), StartMicrovmError> {
    if let Some(serial) = serial {
        mmio_device_manager
            .register_mmio_serial(vm, kernel_cmdline, interrupt_controller.clone(), serial)
            .map_err(Error::RegisterMMIODevice)
            .map_err(StartMicrovmError::Internal)?;
    }

    mmio_device_manager
        .register_mmio_rtc(vm, interrupt_controller.clone())
        .map_err(Error::RegisterMMIODevice)
        .map_err(StartMicrovmError::Internal)?;

    mmio_device_manager
        .register_mmio_gic(vm, interrupt_controller)
        .map_err(Error::RegisterMMIODevice)
        .map_err(StartMicrovmError::Internal)?;

    Ok(())
}

#[cfg(target_arch = "x86_64")]
fn create_vcpus_x86_64(
    vm: &Vm,
    vcpu_config: &VcpuConfig,
    guest_mem: &GuestMemoryMmap,
    entry_addr: GuestAddress,
    request_ts: TimestampUs,
    io_bus: &devices::Bus,
    exit_evt: &EventFd,
) -> super::Result<Vec<Vcpu>> {
    let mut vcpus = Vec::with_capacity(vcpu_config.vcpu_count as usize);
    for cpu_index in 0..vcpu_config.vcpu_count {
        let mut vcpu = Vcpu::new_x86_64(
            cpu_index,
            vm.fd(),
            vm.supported_cpuid().clone(),
            vm.supported_msrs().clone(),
            io_bus.clone(),
            exit_evt.try_clone().map_err(Error::EventFd)?,
            request_ts.clone(),
        )
        .map_err(Error::Vcpu)?;

        vcpu.configure_x86_64(guest_mem, entry_addr, vcpu_config)
            .map_err(Error::Vcpu)?;

        vcpus.push(vcpu);
    }
    Ok(vcpus)
}

#[cfg(target_arch = "aarch64")]
fn create_vcpus_aarch64(
    vm: &Vm,
    vcpu_config: &VcpuConfig,
    guest_mem: &GuestMemoryMmap,
    entry_addr: GuestAddress,
    request_ts: TimestampUs,
    exit_evt: &EventFd,
) -> super::Result<Vec<Vcpu>> {
    let mut vcpus = Vec::with_capacity(vcpu_config.vcpu_count as usize);
    for cpu_index in 0..vcpu_config.vcpu_count {
        let mut vcpu = Vcpu::new_aarch64(
            cpu_index,
            vm,
            exit_evt.try_clone().map_err(Error::EventFd)?,
            request_ts.clone(),
        )
        .map_err(Error::Vcpu)?;

        vcpu.configure_aarch64(vm, guest_mem, entry_addr)
            .map_err(Error::Vcpu)?;

        vcpus.push(vcpu);
    }
    Ok(vcpus)
}

/// Attaches an MmioTransport device to the device manager.
fn attach_mmio_device(
    vmm: &mut Vmm,
    id: String,
    device: MmioTransport,
) -> std::result::Result<(), device_manager::mmio::Error> {
    let type_id = device
        .device()
        .lock()
        .expect("Poisoned device lock")
        .device_type();
    let cmdline = &mut vmm.kernel_cmdline;

    //#[cfg(target_arch = "x86_64")]
    let (_mmio_base, _irq) = vmm
        .mmio_device_manager
        .register_mmio_device(/*vmm.vm.fd(),*/ device, type_id, id)?;
    #[cfg(target_arch = "x86_64")]
    vmm.mmio_device_manager
        .add_device_to_cmdline(cmdline, _mmio_base, _irq)?;

    Ok(())
}

fn attach_fs_devices(
    vmm: &mut Vmm,
    fs_devs: &FsBuilder,
    event_manager: &mut EventManager,
    intc: Option<Arc<Mutex<Gic>>>,
) -> std::result::Result<(), StartMicrovmError> {
    use self::StartMicrovmError::*;

    for fs in fs_devs.list.iter() {
        let id = String::from(fs.lock().unwrap().id());

        if let Some(ref intc) = intc {
            fs.lock().unwrap().set_intc(intc.clone());
        }

        event_manager
            .add_subscriber(fs.clone())
            .map_err(RegisterEvent)?;

        // The device mutex mustn't be locked here otherwise it will deadlock.
        attach_mmio_device(
            vmm,
            id,
            MmioTransport::new(vmm.guest_memory().clone(), fs.clone()),
        )
        .map_err(RegisterFsDevice)?;
    }

    Ok(())
}

fn attach_console_devices(
    vmm: &mut Vmm,
    event_manager: &mut EventManager,
    intc: Option<Arc<Mutex<Gic>>>,
) -> std::result::Result<(), StartMicrovmError> {
    use self::StartMicrovmError::*;

    let console = Arc::new(Mutex::new(
        devices::virtio::Console::new(Box::new(SerialStdin::get()), Box::new(io::stdout()))
            .unwrap(),
    ));

    if let Some(intc) = intc {
        console.lock().unwrap().set_intc(intc);
    }

    // Stdin may not be pollable (i.e. when running a container without "-i"). If that's
    // the case, disable the interactive mode in the console.
    //if !event_manager.is_pollable(io::stdin().as_raw_fd()) {
    //console.lock().unwrap().set_interactive(false);
    //}

    event_manager
        .add_subscriber(console.clone())
        .map_err(RegisterEvent)?;

    // The device mutex mustn't be locked here otherwise it will deadlock.
    attach_mmio_device(
        vmm,
        "hvc0".to_string(),
        MmioTransport::new(vmm.guest_memory().clone(), console.clone()),
    )
    .map_err(RegisterFsDevice)?;

    #[cfg(target_os = "linux")]
    register_sigwinch_handler(console.lock().unwrap().get_sigwinch_fd())
        .map_err(RegisterFsSigwinch)?;

    Ok(())
}

#[cfg(target_os = "linux")]
fn attach_unixsock_vsock_device(
    vmm: &mut Vmm,
    unix_vsock: &Arc<Mutex<Vsock<VsockUnixBackend>>>,
    event_manager: &mut EventManager,
    intc: Option<Arc<Mutex<Gic>>>,
) -> std::result::Result<(), StartMicrovmError> {
    use self::StartMicrovmError::*;

    event_manager
        .add_subscriber(unix_vsock.clone())
        .map_err(RegisterEvent)?;

    let id = String::from(unix_vsock.lock().unwrap().id());

    if let Some(intc) = intc {
        unix_vsock.lock().unwrap().set_intc(intc);
    }

    // The device mutex mustn't be locked here otherwise it will deadlock.
    attach_mmio_device(
        vmm,
        id,
        MmioTransport::new(vmm.guest_memory().clone(), unix_vsock.clone()),
    )
    .map_err(RegisterVsockDevice)?;

    Ok(())
}

fn attach_balloon_device(
    vmm: &mut Vmm,
    event_manager: &mut EventManager,
    intc: Option<Arc<Mutex<Gic>>>,
) -> std::result::Result<(), StartMicrovmError> {
    use self::StartMicrovmError::*;

    let balloon = Arc::new(Mutex::new(devices::virtio::Balloon::new().unwrap()));

    event_manager
        .add_subscriber(balloon.clone())
        .map_err(RegisterEvent)?;

    let id = String::from(balloon.lock().unwrap().id());

    if let Some(intc) = intc {
        balloon.lock().unwrap().set_intc(intc);
    }

    // The device mutex mustn't be locked here otherwise it will deadlock.
    attach_mmio_device(
        vmm,
        id,
        MmioTransport::new(vmm.guest_memory().clone(), balloon),
    )
    .map_err(RegisterBalloonDevice)?;

    Ok(())
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use arch::DeviceType;
    use devices::virtio::TYPE_VSOCK;
    use kernel::cmdline::Cmdline;
    use polly::event_manager::EventManager;
    use utils::tempfile::TempFile;
    use vmm_config::boot_source::DEFAULT_KERNEL_CMDLINE;
    #[cfg(target_os = "linux")]
    use vmm_config::vsock::tests::{default_config, TempSockFile};
    #[cfg(target_os = "linux")]
    use vmm_config::vsock::VsockBuilder;

    fn default_mmio_device_manager() -> MMIODeviceManager {
        MMIODeviceManager::new(
            &mut (arch::MMIO_MEM_START as u64),
            (arch::IRQ_BASE, arch::IRQ_MAX),
        )
    }

    #[cfg(target_arch = "x86_64")]
    fn default_portio_device_manager() -> PortIODeviceManager {
        PortIODeviceManager::new(
            Some(Arc::new(Mutex::new(Serial::new_sink(
                EventFd::new(utils::eventfd::EFD_NONBLOCK).unwrap(),
            )))),
            EventFd::new(utils::eventfd::EFD_NONBLOCK).unwrap(),
        )
        .unwrap()
    }

    fn default_kernel_cmdline() -> Cmdline {
        let mut kernel_cmdline = kernel::cmdline::Cmdline::new(4096);
        kernel_cmdline.insert_str(DEFAULT_KERNEL_CMDLINE).unwrap();
        kernel_cmdline
    }

    fn default_guest_memory(
        mem_size_mib: usize,
    ) -> std::result::Result<GuestMemoryMmap, StartMicrovmError> {
        let kernel_guest_addr: u64 = 0x1000;
        let kernel_size: usize = 0x1000;
        let kernel_host_addr: u64 = 0x1000;

        let kernel_region = unsafe {
            MmapRegion::build_raw(kernel_host_addr as *mut _, kernel_size, 0, 0).unwrap()
        };

        create_guest_memory(mem_size_mib, kernel_region, kernel_guest_addr, kernel_size)
    }

    fn default_vmm() -> Vmm {
        let guest_memory = default_guest_memory(128).unwrap();
        let kernel_cmdline = default_kernel_cmdline();

        let exit_evt = EventFd::new(utils::eventfd::EFD_NONBLOCK)
            .map_err(Error::EventFd)
            .map_err(StartMicrovmError::Internal)
            .unwrap();

        let vm = setup_kvm_vm(&guest_memory).unwrap();
        let mmio_device_manager = default_mmio_device_manager();
        #[cfg(target_arch = "x86_64")]
        let pio_device_manager = default_portio_device_manager();

        Vmm {
            //events_observer: Some(Box::new(SerialStdin::get())),
            guest_memory,
            kernel_cmdline,
            vcpus_handles: Vec::new(),
            exit_evt,
            vm,
            mmio_device_manager,
            #[cfg(target_arch = "x86_64")]
            pio_device_manager,
        }
    }

    #[test]
    fn test_stdin_wrapper() {
        let wrapper = SerialStdin::get();
        assert_eq!(wrapper.as_raw_fd(), io::stdin().as_raw_fd())
    }

    #[test]
    #[cfg(target_arch = "x86_64")]
    fn test_create_vcpus_x86_64() {
        let vcpu_count = 2;

        let guest_memory = default_guest_memory(128).unwrap();
        let mut vm = setup_kvm_vm(&guest_memory).unwrap();
        setup_interrupt_controller(&mut vm).unwrap();
        let vcpu_config = VcpuConfig {
            vcpu_count,
            ht_enabled: false,
            cpu_template: None,
        };

        // Dummy entry_addr, vcpus will not boot.
        let entry_addr = GuestAddress(0);
        let bus = devices::Bus::new();
        let vcpu_vec = create_vcpus_x86_64(
            &vm,
            &vcpu_config,
            &guest_memory,
            entry_addr,
            TimestampUs::default(),
            &bus,
            &EventFd::new(utils::eventfd::EFD_NONBLOCK).unwrap(),
        )
        .unwrap();
        assert_eq!(vcpu_vec.len(), vcpu_count as usize);
    }

    #[test]
    #[cfg(target_arch = "aarch64")]
    fn test_create_vcpus_aarch64() {
        let guest_memory = create_guest_memory(128).unwrap();
        let vm = setup_kvm_vm(&guest_memory).unwrap();
        let vcpu_count = 2;

        let vcpu_config = VcpuConfig {
            vcpu_count,
            ht_enabled: false,
            cpu_template: None,
        };

        // Dummy entry_addr, vcpus will not boot.
        let entry_addr = GuestAddress(0);
        let vcpu_vec = create_vcpus_aarch64(
            &vm,
            &vcpu_config,
            &guest_memory,
            entry_addr,
            TimestampUs::default(),
            &EventFd::new(utils::eventfd::EFD_NONBLOCK).unwrap(),
        )
        .unwrap();
        assert_eq!(vcpu_vec.len(), vcpu_count as usize);
    }

    #[test]
    fn test_attach_vsock_device() {
        let mut event_manager = EventManager::new().expect("Unable to create EventManager");
        let mut vmm = default_vmm();

        #[cfg(target_arch = "x86_64")]
        setup_interrupt_controller(&mut vmm.vm).unwrap();

        #[cfg(target_arch = "aarch64")]
        setup_interrupt_controller(&mut vmm.vm, 1).unwrap();

        let tmp_sock_file = TempSockFile::new(TempFile::new().unwrap());
        let vsock_config = default_config(&tmp_sock_file);

        let vsock_dev_id = vsock_config.vsock_id.clone();
        let vsock = VsockBuilder::create_unixsock_vsock(vsock_config).unwrap();
        let vsock = Arc::new(Mutex::new(vsock));
        assert!(attach_unixsock_vsock_device(&mut vmm, &vsock, &mut event_manager).is_ok());

        assert!(vmm
            .mmio_device_manager
            .get_device(DeviceType::Virtio(TYPE_VSOCK), &vsock_dev_id)
            .is_some());
    }

    #[test]
    fn test_error_messages() {
        use builder::StartMicrovmError::*;
        let err = AttachBlockDevice(io::Error::from_raw_os_error(0));
        let _ = format!("{}{:?}", err, err);

        let err = CreateRateLimiter(io::Error::from_raw_os_error(0));
        let _ = format!("{}{:?}", err, err);

        let err = Internal(Error::Serial(io::Error::from_raw_os_error(0)));
        let _ = format!("{}{:?}", err, err);

        let err = KernelCmdline(String::from("dummy --cmdline"));
        let _ = format!("{}{:?}", err, err);

        let err = KernelBundle(vm_memory::mmap::MmapRegionError::InvalidPointer);
        let _ = format!("{}{:?}", err, err);

        let err = LoadCommandline(kernel::cmdline::Error::TooLarge);
        let _ = format!("{}{:?}", err, err);

        let err = MicroVMAlreadyRunning;
        let _ = format!("{}{:?}", err, err);

        let err = MissingKernelConfig;
        let _ = format!("{}{:?}", err, err);

        let err = MissingMemSizeConfig;
        let _ = format!("{}{:?}", err, err);

        let err = NetDeviceNotConfigured;
        let _ = format!("{}{:?}", err, err);

        let err = OpenBlockDevice(io::Error::from_raw_os_error(0));
        let _ = format!("{}{:?}", err, err);

        let err = RegisterBlockDevice(device_manager::mmio::Error::EventFd(
            io::Error::from_raw_os_error(0),
        ));
        let _ = format!("{}{:?}", err, err);

        let err = RegisterEvent(EventManagerError::EpollCreate(
            io::Error::from_raw_os_error(0),
        ));
        let _ = format!("{}{:?}", err, err);

        let err = RegisterNetDevice(device_manager::mmio::Error::EventFd(
            io::Error::from_raw_os_error(0),
        ));
        let _ = format!("{}{:?}", err, err);

        let err = RegisterVsockDevice(device_manager::mmio::Error::EventFd(
            io::Error::from_raw_os_error(0),
        ));
        let _ = format!("{}{:?}", err, err);
    }

    #[test]
    fn test_kernel_cmdline_err_to_startuvm_err() {
        let err = StartMicrovmError::from(kernel::cmdline::Error::HasSpace);
        let _ = format!("{}{:?}", err, err);
    }
}
