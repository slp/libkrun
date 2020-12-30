use super::bindings::*;

const MAIN_MEMORY: u64 = 0x8000_0000;
const MAIN_MEMORY_SIZE: usize = 0x1000_0000;

const PSR_MODE_EL1h: u64 = 0x0000_0005;
const PSR_F_BIT: u64 = 0x0000_0040;
const PSR_I_BIT: u64 = 0x0000_0080;
const PSR_A_BIT: u64 = 0x0000_0100;
const PSR_D_BIT: u64 = 0x0000_0200;
// Taken from arch/arm64/kvm/inject_fault.c.
pub const PSTATE_FAULT_BITS_64: u64 = PSR_MODE_EL1h | PSR_A_BIT | PSR_F_BIT | PSR_I_BIT | PSR_D_BIT;

const EC_AA64_HVC: u64 = 0x16;
const EC_AA64_SMC: u64 = 0x17;
const EC_SYSTEMREGISTERTRAP: u64 = 0x18;
const EC_SVEACCESSTRAP: u64 = 0x19;
const EC_DATAABORT: u64 = 0x24;
const EC_AA64_BKPT: u64 = 0x3c;

macro_rules! arm64_sys_reg {
    ($name: tt, $op0: tt, $op1: tt, $op2: tt, $crn: tt, $crm: tt) => {
        const $name: u64 = ($op0 as u64) << 20
            | ($op2 as u64) << 17
            | ($op1 as u64) << 14
            | ($crn as u64) << 10
            | ($crm as u64) << 1;
    };
}

arm64_sys_reg!(SYSREG_MASK, 0x3, 0x7, 0x7, 0xf, 0xf);
arm64_sys_reg!(SYSREG_CNTPCT_EL0, 3, 3, 1, 14, 0);
arm64_sys_reg!(SYSREG_PMCCNTR_EL0, 3, 3, 0, 9, 13);

arm64_sys_reg!(SYSREG_ICC_AP0R0_EL1, 3, 0, 4, 12, 8);
arm64_sys_reg!(SYSREG_ICC_AP0R1_EL1, 3, 0, 5, 12, 8);
arm64_sys_reg!(SYSREG_ICC_AP0R2_EL1, 3, 0, 6, 12, 8);
arm64_sys_reg!(SYSREG_ICC_AP0R3_EL1, 3, 0, 7, 12, 8);
arm64_sys_reg!(SYSREG_ICC_AP1R0_EL1, 3, 0, 0, 12, 9);
arm64_sys_reg!(SYSREG_ICC_AP1R1_EL1, 3, 0, 1, 12, 9);
arm64_sys_reg!(SYSREG_ICC_AP1R2_EL1, 3, 0, 2, 12, 9);
arm64_sys_reg!(SYSREG_ICC_AP1R3_EL1, 3, 0, 3, 12, 9);
arm64_sys_reg!(SYSREG_ICC_ASGI1R_EL1, 3, 0, 6, 12, 11);
arm64_sys_reg!(SYSREG_ICC_BPR0_EL1, 3, 0, 3, 12, 8);
arm64_sys_reg!(SYSREG_ICC_BPR1_EL1, 3, 0, 3, 12, 12);
arm64_sys_reg!(SYSREG_ICC_CTLR_EL1, 3, 0, 4, 12, 12);
arm64_sys_reg!(SYSREG_ICC_DIR_EL1, 3, 0, 1, 12, 11);
arm64_sys_reg!(SYSREG_ICC_EOIR0_EL1, 3, 0, 1, 12, 8);
arm64_sys_reg!(SYSREG_ICC_EOIR1_EL1, 3, 0, 1, 12, 12);
arm64_sys_reg!(SYSREG_ICC_HPPIR0_EL1, 3, 0, 2, 12, 8);
arm64_sys_reg!(SYSREG_ICC_HPPIR1_EL1, 3, 0, 2, 12, 12);
arm64_sys_reg!(SYSREG_ICC_IAR0_EL1, 3, 0, 0, 12, 8);
arm64_sys_reg!(SYSREG_ICC_IAR1_EL1, 3, 0, 0, 12, 12);
arm64_sys_reg!(SYSREG_ICC_IGRPEN0_EL1, 3, 0, 6, 12, 12);
arm64_sys_reg!(SYSREG_ICC_IGRPEN1_EL1, 3, 0, 7, 12, 12);
arm64_sys_reg!(SYSREG_ICC_PMR_EL1, 3, 0, 0, 4, 6);
arm64_sys_reg!(SYSREG_ICC_RPR_EL1, 3, 0, 3, 12, 11);
arm64_sys_reg!(SYSREG_ICC_SGI0R_EL1, 3, 0, 7, 12, 11);
arm64_sys_reg!(SYSREG_ICC_SGI1R_EL1, 3, 0, 5, 12, 11);
arm64_sys_reg!(SYSREG_ICC_SRE_EL1, 3, 0, 5, 12, 12);

#[derive(Clone, Debug)]
pub enum Error {
    Error,
    LoadKernel,
    OpenKernel,
}

pub fn hv_call(code: hv_return_t) -> Result<(), Error> {
    match code {
        HV_SUCCESS => Ok(()),
        _ => Err(Error::Error),
    }
}
