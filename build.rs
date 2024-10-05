use std::env;
use std::path::Path;

fn main() {
    let outdir = env::var("OUT_DIR").unwrap();
    std::process::Command::new("gcc")
        .args(["-c", "-o", &format!("{}/cread.o", outdir), "cread.c"])
        .status()
        .unwrap();
    std::process::Command::new("ar")
        .args(["crs", "libcread.a", "cread.o"])
        .current_dir(&Path::new(&outdir))
        .status()
        .unwrap();
    println!("cargo::rustc-link-search=native={}", outdir);
    println!("cargo::rustc-link-lib=static=cread");
    println!("cargo::rerun-if-changed=cread.c");
}
