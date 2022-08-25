use super::super::resources::TeeConfig;
use super::vstate::MeasuredRegion;
use super::vstate::Vcpu;

use kvm_bindings::{kvm_enc_region, kvm_tdx_cmd, kvm_tdx_cmd_id, CpuId};
use kvm_ioctls::{Kvm, VcpuFd, VmFd};
use vm_memory::{GuestMemory, GuestMemoryMmap, GuestMemoryRegion};

#[derive(Debug)]
pub enum Error {
    TdxCapabilities(kvm_ioctls::Error),
    TdxInit(kvm_ioctls::Error),
    TdxInitRegion(kvm_ioctls::Error),
    TdxFinalizeVm(kvm_ioctls::Error),
    MemoryEncryptRegion(kvm_ioctls::Error),
}

const TDX_MAX_NR_CPUID_CONFIGS: usize = 6;

#[repr(C)]
#[derive(Debug, Default)]
pub struct TdxCpuidConfig {
    pub leaf: u32,
    pub sub_leaf: u32,
    pub eax: u32,
    pub ebx: u32,
    pub ecx: u32,
    pub edx: u32,
}

#[repr(C)]
#[derive(Debug, Default)]
pub struct TdxCapabilities {
    pub attrs_fixed0: u64,
    pub attrs_fixed1: u64,
    pub xfam_fixed0: u64,
    pub xfam_fixed1: u64,
    pub nr_cpuid_configs: u32,
    pub padding: u32,
    pub cpuid_configs: [TdxCpuidConfig; TDX_MAX_NR_CPUID_CONFIGS],
}

pub struct IntelTdx {
    tee_config: TeeConfig,
}

impl IntelTdx {
    pub fn new(tee_config: &TeeConfig) -> Self {
        Self {
            tee_config: tee_config.clone(),
        }
    }

    pub fn tdx_capabilities(&self, kvm: &Kvm) -> Result<TdxCapabilities, Error> {
        let mut data = TdxCapabilities {
            nr_cpuid_configs: TDX_MAX_NR_CPUID_CONFIGS as u32,
            ..Default::default()
        };

        let mut cmd = kvm_tdx_cmd {
            id: kvm_tdx_cmd_id::KVM_TDX_CAPABILITIES,
            metadata: 0,
            data: &mut data as *mut _ as u64,
        };

        kvm.encrypt_op_tdx(&mut cmd)
            .map_err(Error::TdxCapabilities)?;

        Ok(data)
    }

    fn tdx_init(&self, vm_fd: &VmFd, cpuid: &CpuId) -> Result<(), Error> {
        #[repr(C)]
        struct TdxInitVm {
            max_vcpus: u32,
            tsc_khz: u32,
            attributes: u64,
            cpuid: u64,
            mrconfigid: [u64; 6],
            mrowner: [u64; 6],
            mrownerconfig: [u64; 6],
            reserved: [u64; 43],
        }
        let data = TdxInitVm {
            max_vcpus: 1,
            tsc_khz: 0,
            attributes: 0,
            cpuid: cpuid.as_fam_struct_ptr() as u64,
            mrconfigid: [0; 6],
            mrowner: [0; 6],
            mrownerconfig: [0; 6],
            reserved: [0; 43],
        };

        let mut cmd = kvm_tdx_cmd {
            id: kvm_tdx_cmd_id::KVM_TDX_INIT_VM,
            metadata: 0,
            data: &data as *const _ as u64,
        };

        vm_fd.encrypt_op_tdx(&mut cmd).map_err(Error::TdxInit)
    }

    fn tdx_init_region(
        &self,
        vm_fd: &VmFd,
        host_address: u64,
        guest_address: u64,
        size: usize,
    ) -> Result<(), Error> {
        #[repr(C)]
        struct TdxInitMemRegion {
            host_address: u64,
            guest_address: u64,
            pages: u64,
        }
        let data = TdxInitMemRegion {
            host_address,
            guest_address,
            pages: (size / 4096) as u64,
        };

        let mut cmd = kvm_tdx_cmd {
            id: kvm_tdx_cmd_id::KVM_TDX_INIT_MEM_REGION,
            metadata: 1,
            data: &data as *const _ as u64,
        };

        vm_fd.encrypt_op_tdx(&mut cmd).map_err(Error::TdxInitRegion)
    }

    fn tdx_finalize(&self, vm_fd: &VmFd) -> Result<(), Error> {
        let mut cmd = kvm_tdx_cmd {
            id: kvm_tdx_cmd_id::KVM_TDX_FINALIZE_VM,
            metadata: 0,
            data: 0,
        };

        vm_fd.encrypt_op_tdx(&mut cmd).map_err(Error::TdxFinalizeVm)
    }

    pub fn init_vcpu(&self, vcpu_fd: &VcpuFd) -> Result<(), Error> {
        let mut cmd = kvm_tdx_cmd {
            id: kvm_tdx_cmd_id::KVM_TDX_INIT_VCPU,
            metadata: 0,
            data: 0,
        };

        vcpu_fd.encrypt_op_tdx(&mut cmd).map_err(Error::TdxInit)
    }

    pub fn vm_prepare(
        &self,
        vm_fd: &VmFd,
        guest_mem: &GuestMemoryMmap,
        cpuid: &CpuId,
    ) -> Result<(), Error> {
        self.tdx_init(vm_fd, cpuid)?;

        /*
            for region in guest_mem.iter() {
                // It's safe to unwrap because the guest address is valid.
                let host_addr = guest_mem.get_host_address(region.start_addr()).unwrap();
                let enc_region = kvm_enc_region {
                    addr: host_addr as u64,
                    size: region.len() as u64,
                };
                vm_fd
                    .register_enc_memory_region(&enc_region)
                    .map_err(Error::MemoryEncryptRegion)?;
        }
            */

        Ok(())
    }

    pub fn vm_attest(
        &self,
        vm_fd: &VmFd,
        guest_mem: &GuestMemoryMmap,
        vcpus: &[Vcpu],
        measured_regions: Vec<MeasuredRegion>,
    ) -> Result<(), Error> {
        for vcpu in vcpus {
            vcpu.init_tdx(&self).unwrap();
        }

        for region in measured_regions {
            self.tdx_init_region(vm_fd, region.host_addr, region.guest_addr, region.size)?;
        }

        self.tdx_finalize(vm_fd)?;

        Ok(())
    }
}
