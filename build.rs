use std::fs;
use std::io;

fn main() {
    println!("cargo::rerun-if-changed=cread.c");
    const OUTDIR: &str = "./target";
    let outobj = format!("{}/{}", OUTDIR, "cread.o");
    let outlib = format!("{}/{}", OUTDIR, "libcread.a");

    // Remove previous build.
    for path in vec![&outobj, &outlib] {
        match fs::remove_file(path) {
            Err(error) => match error.kind() {
                io::ErrorKind::PermissionDenied => {
                    eprintln!("Not allowed to remove old file: {}", path);
                    std::process::exit(1);
                },
                io::ErrorKind::NotFound => {
                    eprintln!("File not found: {}", path);
                },
                other_kind => panic!("Should not happen: {}", other_kind)
            },
            _ => {}
        }
    }

    std::process::Command::new("gcc")
        .args(["-c", "-o", &outobj, "cread.c"])
        .output()
        .unwrap();
    std::process::Command::new("ar")
        .args(["-rcs", &outlib, &outobj])
        .output()
        .unwrap();
    println!("cargo::rustc-link-search={}", OUTDIR);
    println!("cargo::rustc-link-lib={}", outlib.strip_prefix(&format!("{}/lib", OUTDIR)).unwrap().strip_suffix(".a").unwrap());
}
