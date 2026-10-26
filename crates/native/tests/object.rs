//! Stage S5 of docs/proposals/standalone-executables.md: the islands
//! compiled into an object file (`aot::compile_object`), which `stitchwort
//! build --native` links into an executable. The object exports the
//! manifest and the crossing's trampolines, leaves the runtime's helpers
//! (the effect runtime's leaves among them) to the
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
fn the_object_exports_its_manifest_and_trampolines_and_its_code_is_relocatable() {
    with_stack(STACK, || {
        let (program, _) = lowered(&bench("effects.sw"));
        let image = code::compile(&program);
        let options = Options {
            trace_refcounts: false,
        };
        let frames = stitchwort_rt::Limits::from_core(Default::default()).frames as u64;
        let limits = stitchwort_rt::Limits::from_core(Default::default());
        let tables = stitchwort_rt::linked::encode(&program, &image, &limits);
        let compiled =
            compile_object(&program, &image, &tables, options, frames).expect("compiles");
        // Every body `main` reaches, its entry included (stage NO4 of
        // native-only.md), on the stack sized for them (stage NO5).
        assert_eq!(
            compiled.bodies,
            stitchwort_rt::census::island(&image, image.entry_code).len()
        );
        assert_eq!(
            Some(compiled.stack_size),
            stitchwort_rt::native_abi::native_stack(frames, compiled.max_frame)
        );
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
        let trampolines: Vec<_> = file
            .symbols()
            .filter(|s| {
                s.name()
                    .is_ok_and(|name| name.starts_with(&format!("{prefix}sw_cross_")))
            })
            .collect();
        assert!(!trampolines.is_empty(), "no trampoline");
        for trampoline in trampolines {
            assert!(trampoline.is_definition() && trampoline.is_global());
        }
        // The helpers are the runtime library's, for the linker: the
        // effect runtime's leaves too.
        for helper in [
            "sw_closure",
            "sw_apply_prepare",
            "sw_ctor",
            "sw_bind",
            "sw_eff_step",
            // And the way the library runs it (stage NO6 of native-only.md).
            "sw_run_native",
        ] {
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
