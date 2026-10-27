//! A call written with dot notation or `|>` elaborates to the same term as
//! the prefix call it stands for, so the two have one content hash: with an
//! effectful function, and with a constructor (a list literal) as the
//! receiver or the value piped in.

use std::collections::BTreeMap;

use stitchwort_core::DefId;
use stitchwort_core::hash::def_hash;
use stitchwort_driver::driver::Session;

/// The hash of each definition `text` adds, by name.
fn hashes_by_name(text: &str) -> BTreeMap<String, String> {
    let mut session = Session::new();
    let first = session.elab.globals.defs.len();
    if let Err(errors) = session.load("pipe-forms.sw", text) {
        panic!("{errors:#?}");
    }
    let g = &session.elab.globals;
    (first..g.defs.len())
        .map(|i| {
            let hash = def_hash(g, DefId(i)).unwrap().map(|h| h.hex());
            (g.defs[i].name.to_string(), format!("{hash:?}"))
        })
        .collect()
}

/// Each `…Prefix` definition must have the hash of every `…Dot`, `…Pipe`
/// and `…DotPipe` definition with the same stem.
#[test]
fn pipe_and_dot_forms_have_the_prefix_hash() {
    let text = r#"
import Std (Fail, List, Text)

def literalPrefix(): {Fail} Nat := List.sum (List.map ["1", " 2 ", "3"] Text.toNatOrFail)
def literalDotPipe(): {Fail} Nat := ["1", " 2 ", "3"].map Text.toNatOrFail |> .sum
def literalPipe(): {Fail} Nat := ["1", " 2 ", "3"] |> List.map Text.toNatOrFail |> List.sum

def variablePrefix (texts: List Text): {Fail} Nat := List.sum (List.map texts Text.toNatOrFail)
def variableDotPipe (texts: List Text): {Fail} Nat := texts.map Text.toNatOrFail |> .sum

def purePrefix: Nat := List.sum (List.map [1, 2, 3] (n => n + 1))
def pureDot: Nat := [1, 2, 3].map (n => n + 1) |> .sum
"#;
    let by_name = hashes_by_name(text);
    let mut checked = 0;
    for (name, hash) in &by_name {
        let Some(stem) = name.strip_suffix("Prefix") else {
            continue;
        };
        for form in ["Dot", "Pipe", "DotPipe"] {
            let other = format!("{stem}{form}");
            if let Some(other_hash) = by_name.get(&other) {
                assert_eq!(hash, other_hash, "{name} and {other} differ");
                checked += 1;
            }
        }
    }
    assert_eq!(checked, 4);
}
