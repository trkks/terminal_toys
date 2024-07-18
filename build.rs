fn main() {
    const OUTDIR: &str = "./target";
    let outobj = format!("{}/{}", OUTDIR, "cread.o");
    let outlib = format!("{}/{}", OUTDIR, "libcread.a");
    println!("cargo::rerun-if-changed=cread.c");
    std::process::Command::new("gcc")
        .args(["-c", "-o", &outobj, "cread.c"])
        .output()
        .unwrap();
    std::process::Command::new("ar")
        .args(["-rcs", &outlib, &outobj])
        .output()
        .unwrap();
    println!("cargo::rustc-link-search={}", OUTDIR);
    println!("cargo:rustc-link-lib={}", outlib.strip_prefix(&format!("{}/lib", OUTDIR)).unwrap().strip_suffix(".a").unwrap());
}
