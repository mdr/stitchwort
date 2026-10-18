//! Comparing syntax trees without their positions: a source in the new
//! declaration syntax must parse to the tree its old-syntax equivalent
//! parses to (docs/proposals/declaration-syntax.md §5.4, layer 8). For the
//! parser's tests, and for the converter's.
//!
//! Spans are left out, and so is the marker saying an equation was an arm
//! ([`Decl::Equation`]'s `arm`), which only the new syntax sets.

use crate::SourceMap;
use crate::ast::{Decl, Module};
use crate::parser::{DEFAULT_STACK, Syntax, parse_module_in};
use crate::source::HIDE_SPANS;

/// `module` printed without spans or arm markers: two modules mean the same
/// to everything after the parser when these are equal.
pub fn shape(module: &Module) -> String {
    let mut module = module.clone();
    for decl in &mut module.decls {
        if let Decl::Equation { arm, .. } = decl {
            *arm = None;
        }
    }
    let hidden = HIDE_SPANS.with(|h| h.replace(true));
    let text = format!("{module:#?}");
    HIDE_SPANS.with(|h| h.set(hidden));
    text
}

/// Parses `text`, written in `syntax`, and gives its [`shape`], or the
/// parse errors' messages.
pub fn parse_shape(syntax: Syntax, text: &str) -> Result<String, String> {
    let mut sources = SourceMap::new();
    let file = sources.add("equivalence.sw", text);
    match parse_module_in(syntax, file, text, DEFAULT_STACK) {
        Ok(module) => Ok(shape(&module)),
        Err(errors) => Err(errors
            .iter()
            .map(|d| format!("{}: {}", d.code, d.message))
            .collect::<Vec<_>>()
            .join("\n")),
    }
}

/// Whether `new` (in the new syntax) and `old` (in the old) parse to the
/// same tree. The error says which failed to parse, or where the trees
/// first differ.
pub fn compare(new: &str, old: &str) -> Result<(), String> {
    let new_shape =
        parse_shape(Syntax::New, new).map_err(|e| format!("the new syntax doesn't parse:\n{e}"))?;
    let old_shape =
        parse_shape(Syntax::Old, old).map_err(|e| format!("the old syntax doesn't parse:\n{e}"))?;
    if new_shape == old_shape {
        return Ok(());
    }
    let (new_lines, old_lines): (Vec<&str>, Vec<&str>) =
        (new_shape.lines().collect(), old_shape.lines().collect());
    let at = new_lines
        .iter()
        .zip(&old_lines)
        .position(|(a, b)| a != b)
        .unwrap_or(new_lines.len().min(old_lines.len()));
    let from = at.saturating_sub(12);
    let excerpt = |lines: &[&str]| lines[from..(at + 3).min(lines.len())].join("\n");
    Err(format!(
        "the trees differ at line {} of their shapes\n--- new:\n{}\n--- old:\n{}",
        at + 1,
        excerpt(&new_lines),
        excerpt(&old_lines)
    ))
}

/// Panics, showing the difference, unless `new` and `old` parse to the same
/// tree.
#[track_caller]
pub fn assert_equivalent(new: &str, old: &str) {
    if let Err(difference) = compare(new, old) {
        panic!("{difference}\n--- new source:\n{new}\n--- old source:\n{old}");
    }
}
