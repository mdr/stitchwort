//! The build fingerprint's hash ([`crate::driver::FINGERPRINT`]), from its
//! inputs: shared by `build.rs`, which gathers them, and the test that the
//! fingerprint changes with each.

/// The fingerprint of a build: `Cargo.lock`, the hashed source files (name
/// and contents), and the Rust toolchain (`rustc -vV`) and target it is built
/// with. The toolchain is there because the checker's floats depend on it:
/// literals are parsed by the standard library's `str::parse::<f64>`, and
/// the float primitives are compiled by it (docs/proposals/float.md §3.3).
pub fn fingerprint(
    lock: Option<&[u8]>,
    files: &[(String, Vec<u8>)],
    rustc: &str,
    target: &str,
) -> String {
    let mut hasher = blake3::Hasher::new();
    // Each input with its length, so adjacent ones can't run together.
    let mut field = |bytes: &[u8]| {
        hasher.update(&(bytes.len() as u64).to_le_bytes());
        hasher.update(bytes);
    };
    if let Some(lock) = lock {
        field(b"Cargo.lock");
        field(lock);
    }
    for (name, text) in files {
        field(name.as_bytes());
        field(text);
    }
    field(b"rustc");
    field(rustc.as_bytes());
    field(b"target");
    field(target.as_bytes());
    hasher.finalize().as_bytes()[..12]
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect()
}
