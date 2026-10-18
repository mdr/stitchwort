//! Comparing syntax trees without their positions: a converted source must
//! parse to the tree the old declaration syntax read from the original
//! (docs/proposals/declaration-syntax.md §5.4, layer 8). For the parser's
//! tests, and for the converter's.
//!
//! Spans are left out, and so is the marker saying an equation was an arm
//! ([`Decl::Equation`]'s `arm`), which the old syntax never set.

use crate::SourceMap;
use crate::ast::{Decl, Module};
use crate::parser::{DEFAULT_STACK, parse_module_within};
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

/// Parses `text` and gives its [`shape`], or the parse errors' messages.
pub fn parse_shape(text: &str) -> Result<String, String> {
    let mut sources = SourceMap::new();
    let file = sources.add("equivalence.sw", text);
    match parse_module_within(file, text, DEFAULT_STACK) {
        Ok(module) => Ok(shape(&module)),
        Err(errors) => Err(errors
            .iter()
            .map(|d| format!("{}: {}", d.code, d.message))
            .collect::<Vec<_>>()
            .join("\n")),
    }
}
