//! JavaScript extraction (DESIGN.md §12): erase types and proofs, generate an
//! ES module, and wrap each export in decode → compute → encode.
//!
//! First-milestone scope: exports take and return concrete first-order data
//! (`Nat`, `Bool`, `Text`, `Char`, `List`, and data types built from them,
//! such as `Option Text`), and their proof arguments are checked at runtime.

use stitchwort_core::ProofMark;
#[cfg(test)]
use stitchwort_test_alloc as _;

use std::cell::{Cell, OnceCell, RefCell};
use std::fmt::Write;
use std::rc::Rc;

use stitchwort_core::backend::View;
use stitchwort_core::check::is_type_former;
use stitchwort_core::collections::{HashMap, HashSet};
use stitchwort_core::erase::def_telescope;
use stitchwort_core::globals::FieldDefault;
use stitchwort_core::js_repr::{self, JsRepr};
use stitchwort_core::native;
use stitchwort_core::partial::Primitive;
use stitchwort_core::registry::Builtin;
use stitchwort_core::term::Branch;
use stitchwort_core::value::{Head, eval, expand_step, force, quot_mk_rep, quote};
use stitchwort_core::{
    BigUint, DataId, DefId, Icit, Limits, QuotForm, ResourceError, Sort, Term, Value, pretty,
};
use stitchwort_rt::erasure::{def_shape, text_literal};
use stitchwort_rt::hoist::SigMaps;
use stitchwort_rt::natives::{
    ArrayNative, FloatPrim, Representation, bind_array, float_data, int_data, nat_data,
    safe_int_data, safe_nat_data, text_data,
};
use stitchwort_rt::specialise::{self, Specialiser};
// Shared with the runtime (D389), and part of this crate's interface.
pub use stitchwort_rt::natives::{
    IntBinding, IntNative, NAT_DATA_HASH, NativeBinding, SAFE_INT_HASH, SAFE_NAT_HASH,
    TEXT_DATA_HASH, TextBinding, TextNative, bind_int, bind_text_natives,
};
use stitchwort_syntax::Diagnostic;

mod codegen;
mod effect;
mod emit;
mod exports;
mod expr;
mod fast;
mod names;
mod prelude;
pub mod run;
pub mod sourcemap;

pub use sourcemap::Mapping;

/// Generating code recurses over a definition's body, so each level checks
/// there's stack left first (docs/proposals/stack-safe-evaluation.md).
type Fallible<T> = Result<T, Diagnostic>;
const PASS: &str = "JavaScript generator";

/// A state the generator has no way to produce from a checked program: the
/// caller reports it like any other error instead of panicking.
fn internal(message: impl Into<String>) -> Diagnostic {
    Diagnostic::error("E-INTERNAL", format!("internal error: {}", message.into()))
}

// The generator's modules share their items through the crate root.
pub(crate) use codegen::*;
pub(crate) use emit::*;
pub(crate) use exports::*;
pub(crate) use expr::*;
pub(crate) use names::*;
pub(crate) use prelude::*;

pub use emit::{generate, generate_exports, generate_with};
pub use exports::{
    Boundary, Check, ExportSig, Options, Output, exportable, exports_fit_together,
    exports_fit_together_among, field_boundaries,
};
pub use expr::{FLOAT_BITS, float_literal_js};
pub use names::{boundary_literal, encode, field_key, js_string_literal, record_key};

#[cfg(test)]
mod tests {
    use stitchwort_core::collections::HashMap;

    use super::{IntNative, TextNative, native};
    use crate::expr::{
        forwards_to, int_native_js, is_simple, mentions, native_js, text_native_js, uncurry_arrows,
    };
    use crate::names::{def_name, encode, info_name, is_js_identifier, wrapper_name};
    use crate::prelude::RUNTIME;

    /// Every name of up to four characters from the characters names can
    /// contain (docs/proposals/namespaces.md §7.3): those the lexer accepts
    /// in a name (letters, digits, `_`, `'`), the `.` of a qualified name,
    /// the `%` of a generated one, and one character beyond ASCII.
    fn names() -> Vec<String> {
        const CHARS: &[char] = &['a', 'Z', '0', '_', '\'', '.', '%', 'é'];
        let mut names = vec![String::new()];
        let mut all = Vec::new();
        for _ in 0..4 {
            names = names
                .iter()
                .flat_map(|n| CHARS.iter().map(move |c| format!("{n}{c}")))
                .collect();
            all.extend(names.iter().cloned());
        }
        all
    }

    #[test]
    fn definition_names_are_distinct_valid_identifiers() {
        let mut seen: HashMap<String, String> = HashMap::default();
        for name in names() {
            let js = def_name(&name);
            assert!(is_js_identifier(&js), "{name:?} is {js:?}");
            if let Some(other) = seen.insert(js.clone(), name.clone()) {
                panic!("{name:?} and {other:?} are both {js:?}");
            }
            assert!(is_js_identifier(&info_name(&name)), "{name:?}");
            assert_eq!(
                encode(&name).contains('$'),
                name.chars().any(|c| !c.is_ascii_alphanumeric() && c != '_')
            );
        }
    }

    /// The generator's naming schemes never meet: definitions are `$` and a
    /// letter, `_` or `$$$`; export wrappers `$$` and a letter (an export's
    /// name is a JS identifier without `$`); descriptions of data types
    /// `info$…`; the runtime's own names have no `$`.
    #[test]
    fn naming_schemes_are_disjoint() {
        let defs: Vec<String> = names().iter().map(|n| def_name(n)).collect();
        for export in ["f", "Shape", "_x", "x1"] {
            let wrapper = wrapper_name(export);
            assert!(!defs.contains(&wrapper), "{wrapper}");
        }
        for name in names() {
            assert!(!def_name(&name).starts_with("info"));
            assert!(info_name(&name).starts_with("info$"));
        }
        let runtime: Vec<&str> = RUNTIME
            .lines()
            .filter_map(|l| {
                l.strip_prefix("const ")
                    .or_else(|| l.strip_prefix("function "))
            })
            .filter_map(|l| {
                l.split(|c: char| !c.is_ascii_alphanumeric() && c != '_' && c != '$')
                    .next()
            })
            .collect();
        assert!(runtime.len() > 5, "{runtime:?}");
        for helper in runtime {
            assert!(!helper.contains('$'), "{helper}");
        }
    }

    #[test]
    fn finds_whole_identifiers() {
        assert!(mentions("return v1;", "v1"));
        assert!(mentions("f(v1)(v2)", "v2"));
        assert!(!mentions("return v10 + $v1 + v1_ + v1$;", "v1"));
        assert!(!mentions("", "v1"));
    }

    #[test]
    fn recognises_javascript_identifiers() {
        for ok in ["f", "appendNats", "_private", "$x", "x1", "a_b$c"] {
            assert!(is_js_identifier(ok), "{ok}");
        }
        for bad in ["", "1x", "x'", "x-y", "x y", "é"] {
            assert!(!is_js_identifier(bad), "{bad}");
        }
    }

    #[test]
    fn finds_functions_that_only_pass_their_arguments_on() {
        let block = "(v0, v1) => {\n  const v2 = v0;\n  const v3 = v1;\n  return $Std$dText$dcompare(v2, v3);\n}";
        assert_eq!(forwards_to(block), Some("$Std$dText$dcompare"));
        assert_eq!(
            forwards_to("(v0) => $Main$dEmail$dvalue(v0)"),
            Some("$Main$dEmail$dvalue")
        );
        for not in [
            // Another order, another argument, fewer, or more.
            "(v0, v1) => g(v1, v0)",
            "(v0, v1) => g(v0, 1n)",
            "(v0, v1) => g(v0)",
            "(v0) => g(v0, v0)",
            // Not just a call.
            "(v0) => g(v0).x",
            "(v0) => g(h(v0))",
            "(v0) => (v1) => g(v0)(v1)",
            "(v0) => {\n  const v1 = v0.id;\n  return g(v1);\n}",
            "(v0) => {\n  const v1 = v0;\n  return g(v1);\n  h();\n}",
            "(v0) => v0(v0)",
        ] {
            assert_eq!(forwards_to(not), None, "{not}");
        }
    }

    #[test]
    fn uncurries_natives() {
        assert_eq!(
            uncurry_arrows("(m) => (n) => m + n", 2).as_deref(),
            Some("(m, n) => m + n")
        );
        assert_eq!(
            uncurry_arrows("(f) => (z) => (t) => {\n  return z;\n}", 3).as_deref(),
            Some("(f, z, t) => {\n  return z;\n}")
        );
        // Fewer arrows than parameters, or not an arrow at all.
        assert_eq!(uncurry_arrows("(a) => -a", 2), None);
        assert_eq!(uncurry_arrows("charsOfText", 2), None);
        assert_eq!(uncurry_arrows("(a) => (a < 0n ? -a : a)", 2), None);
        // Every native with two or more runtime parameters uncurries.
        for js in [
            native_js(native::Native::Add),
            native_js(native::Native::DivFuel),
            int_native_js(IntNative::IntDiv),
            text_native_js(TextNative::TextFold),
            text_native_js(TextNative::TextJoin),
        ] {
            let arrows = js.matches(") => (").count() + 1;
            assert!(uncurry_arrows(js, arrows).is_some(), "{js}");
        }
    }

    #[test]
    fn simple_arguments() {
        for simple in ["v0", "v12", "3n", "0"] {
            assert!(is_simple(simple), "{simple}");
        }
        for not in ["", "v", "f(v0)", "undefined", "{ tag: \"Nil\" }"] {
            assert!(!is_simple(not), "{not}");
        }
    }
}
