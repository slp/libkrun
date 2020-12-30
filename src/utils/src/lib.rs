// Copyright 2019 Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

#[macro_use]
extern crate bitflags;

pub use vmm_sys_util::{errno, tempdir, tempfile, terminal};
#[cfg(target_os = "linux")]
pub use vmm_sys_util::{eventfd, ioctl};

pub mod arg_parser;
pub mod byte_order;
#[cfg(target_os = "linux")]
pub mod linux;
#[cfg(target_os = "linux")]
pub use linux::epoll;
#[cfg(target_os = "macos")]
pub mod macos;
#[cfg(target_os = "macos")]
pub use macos::epoll;
#[cfg(target_os = "macos")]
pub use macos::eventfd;
pub mod rand;
#[cfg(target_os = "linux")]
pub mod signal;
pub mod sm;
pub mod structs;
pub mod syscall;
pub mod time;
pub mod validators;
