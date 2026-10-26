//! For a musl target, puts musl's start file (`crt1.o`), C library and
//! unwinder inside the static library, from the Rust toolchain's own copies
//! (its `self-contained` folder), so that `stitchwort build` links an
//! executable statically from this one file and the C compiler's `libgcc`.

use std::path::PathBuf;
use std::process::Command;

fn main() {
    println!("cargo:rerun-if-changed=build.rs");
    if std::env::var("CARGO_CFG_TARGET_ENV").as_deref() != Ok("musl") {
        return;
    }
    let target = std::env::var("TARGET").expect("set by cargo");
    let rustc = std::env::var("RUSTC").unwrap_or_else(|_| "rustc".into());
    let sysroot = Command::new(rustc)
        .args(["--print", "sysroot"])
        .output()
        .expect("run rustc --print sysroot");
    let sysroot = String::from_utf8(sysroot.stdout).expect("a UTF-8 path");
    let dir = PathBuf::from(sysroot.trim())
        .join("lib/rustlib")
        .join(&target)
        .join("lib/self-contained");
    let crt1 = dir.join("crt1.o");
    assert!(
        crt1.is_file(),
        "no {}: the Rust toolchain has no musl files for {target}",
        crt1.display()
    );
    // An archive of `crt1.o` alone, which cargo bundles in.
    cc::Build::new()
        .object(&crt1)
        .cargo_warnings(false)
        .compile("stitchwort_start");
    println!("cargo:rustc-link-search=native={}", dir.display());
    println!("cargo:rustc-link-lib=static:+bundle=c");
    println!("cargo:rustc-link-lib=static:+bundle=unwind");
}
