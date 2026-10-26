//! Stage S5 of docs/proposals/standalone-executables.md: the islands
//! compiled into an object file (`aot::compile_object`), which `stitchwort
//! build --native` links into an executable. The object exports the
//! manifest and the roots' trampolines, leaves the runtime's helpers to the
//! linker, and its code is position-independent: no absolute address in
//! the text (§1.2: macOS can't relocate one, and the binary dies with
//! `SIGBUS`). Running the linked code is tested in
//! `crates/cli/tests/build.rs`.

mod common;

use common::*;
use object::{Object as _, ObjectSection as _, ObjectSymbol as _, RelocationFlags};
use stitchwort_driver::driver::with_stack;
use stitchwort_native::aot::compile_object;
use stitchwort_native::n1::Options;
use stitchwort_rt::code;

#[test]
fn the_object_exports_its_manifest_and_roots_and_its_code_is_relocatable() {
    with_stack(STACK, || {
        let (program, _) = lowered(&bench("closures.sw"));
        let image = code::compile(&program);
        let options = Options {
            trace_refcounts: false,
            stack_size: Some(STACK),
        };
        let compiled = compile_object(&program, &image, options).expect("compiles");
        assert_eq!(compiled.roots, ["Main.run"]);
        let bytes = compiled.object.write().expect("writes");
        let file = object::File::parse(&*bytes).expect("parses");
        let prefix = if cfg!(target_os = "macos") { "_" } else { "" };
        let symbol = |name: &str| {
            file.symbols()
                .find(|s| s.name() == Ok(&format!("{prefix}{name}")))
                .unwrap_or_else(|| panic!("no {name}"))
        };
        let manifest = symbol("sw_native_manifest");
        assert!(manifest.is_definition() && manifest.is_global());
        let g = program
            .globals
            .iter()
            .position(|global| &*global.name == "Main.run")
            .expect("`Main.run`");
        let root = symbol(&format!("sw_root_{g}"));
        assert!(root.is_definition() && root.is_global());
        // The helpers are the runtime library's, for the linker.
        for helper in ["sw_closure", "sw_apply_prepare", "sw_ctor"] {
            assert!(symbol(helper).is_undefined(), "{helper}");
        }
        // Position-independent: the text's relocations are calls and
        // GOT loads, never an absolute address.
        let text = file
            .sections()
            .find(|s| s.kind() == object::SectionKind::Text)
            .expect("a text section");
        let mut relocations = 0;
        for (_, relocation) in text.relocations() {
            relocations += 1;
            let absolute = match relocation.flags() {
                RelocationFlags::MachO { r_type, .. } => {
                    r_type == object::macho::ARM64_RELOC_UNSIGNED
                        || r_type == object::macho::X86_64_RELOC_UNSIGNED
                }
                RelocationFlags::Elf { r_type } => {
                    r_type == object::elf::R_AARCH64_ABS64 || r_type == object::elf::R_X86_64_64
                }
                _ => false,
            };
            assert!(
                !absolute,
                "an absolute relocation in the text: {relocation:?}"
            );
        }
        assert!(relocations > 0, "the code calls the helpers");
    });
}
