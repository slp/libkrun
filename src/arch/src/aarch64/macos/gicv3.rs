// Copyright 2019 Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use std::{boxed::Box, result};

use super::gic::{Error, GICDevice};

type Result<T> = result::Result<T, Error>;

pub struct GICv3 {
    /// GIC device properties, to be used for setting up the fdt entry
    properties: [u64; 4],

    /// Number of CPUs handled by the device
    vcpu_count: u64,
}

impl GICv3 {
    // Unfortunately bindgen omits defines that are based on other defines.
    // See arch/arm64/include/uapi/asm/kvm.h file from the linux kernel.
    const SZ_64K: u64 = 0x0001_0000;
    const KVM_VGIC_V3_DIST_SIZE: u64 = GICv3::SZ_64K;
    const KVM_VGIC_V3_REDIST_SIZE: u64 = (2 * GICv3::SZ_64K);

    // Device trees specific constants
    const ARCH_GIC_V3_MAINT_IRQ: u32 = 9;

    /// Get the address of the GIC distributor.
    fn get_dist_addr(vcpu_count: u64) -> u64 {
        super::super::layout::MAPPED_IO_START
            - GICv3::get_dist_size()
            - GICv3::get_redists_size(vcpu_count)
    }

    /// Get the size of the GIC distributor.
    fn get_dist_size() -> u64 {
        GICv3::KVM_VGIC_V3_DIST_SIZE
    }

    /// Get the address of the GIC redistributors.
    fn get_redists_addr(vcpu_count: u64) -> u64 {
        GICv3::get_dist_addr(vcpu_count) + GICv3::get_dist_size()
    }

    /// Get the size of the GIC redistributors.
    fn get_redists_size(vcpu_count: u64) -> u64 {
        vcpu_count * GICv3::KVM_VGIC_V3_REDIST_SIZE
    }
}

impl GICDevice for GICv3 {
    fn version() -> u32 {
        7
    }

    fn device_properties(&self) -> &[u64] {
        &self.properties
    }

    fn vcpu_count(&self) -> u64 {
        self.vcpu_count
    }

    fn fdt_compatibility(&self) -> &str {
        "arm,gic-v3"
    }

    fn fdt_maint_irq(&self) -> u32 {
        GICv3::ARCH_GIC_V3_MAINT_IRQ
    }

    fn create_device(vcpu_count: u64) -> Box<dyn GICDevice> {
        println!("dist_size={}", GICv3::get_dist_size());
        println!("redist_size={}", GICv3::get_redists_size(1));
        Box::new(GICv3 {
            properties: [
                GICv3::get_dist_addr(vcpu_count),
                GICv3::get_dist_size(),
                GICv3::get_redists_addr(vcpu_count),
                GICv3::get_redists_size(vcpu_count),
            ],
            vcpu_count,
        })
    }

    fn init_device_attributes(_gic_device: &Box<dyn GICDevice>) -> Result<()> {
        Ok(())
    }
}
