fn main() {
    println!("cargo:rustc-link-lib=framework=Hypervisor");
    println!("cargo:rustc-link-search=/opt/local/lib");
    println!("cargo:rustc-link-lib=krunfw");
    println!("cargo:rustc-link-lib=fdt");
}
