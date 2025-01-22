// Copyright 2024, Red Hat Inc. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use std::path::PathBuf;

#[derive(Clone, Debug)]
pub enum ExternalKernelFormat {
    BzImage,
    Elf,
    Pe,
    Raw,
}

impl Default for ExternalKernelFormat {
    fn default() -> Self {
        Self::Raw
    }
}

/// Data structure holding the attributes read from the `libkrunfw` kernel config.
#[derive(Clone, Debug, Default)]
pub struct ExternalKernel {
    pub path: PathBuf,
    pub format: ExternalKernelFormat,
}
