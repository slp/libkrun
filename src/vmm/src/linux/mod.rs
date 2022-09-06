#[cfg(feature = "amd-sev")]
mod amdsev;
#[cfg(feature = "intel-tdx")]
mod inteltdx;
pub mod vstate;
