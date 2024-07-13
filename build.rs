fn main() {
    println!("cargo::rerun-if-changed=cread.c");
    std::process::Command::new("gcc")
        .args(["-c", "-o", "cread.o", "cread.c"])
        .output()
        .unwrap();
    std::process::Command::new("ar")
        .args(["-rcs", "libcread.a", "cread.o"])
        .output()
        .unwrap();
    println!("cargo::rustc-link-search=.");
    println!("cargo:rustc-link-lib=cread");
}
