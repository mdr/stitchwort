//! Comparing syntax trees without their positions: a converted source must
//! parse to the tree the old declaration syntax read from the original
//! (docs/proposals/declaration-syntax.md §5.4, layer 8). For the parser's
//! tests, and for the converter's.
//!
//! Spans are left out, and so is the marker saying an equation was an arm
//! ([`Decl::Equation`]'s `arm`), which the old syntax never set.

use crate::SourceMap;
use crate::ast::{CHAIN, Decl, Module};
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
    renumber_chains(&text)
}

/// A chain of comparisons names its hidden binding by the middle
/// operand's offset ([`CHAIN`]), which moves with the text: number the
/// names by first appearance instead.
fn renumber_chains(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    let mut seen: Vec<&str> = Vec::new();
    let mut rest = text;
    while let Some(at) = rest.find(CHAIN) {
        let (before, after) = rest.split_at(at + CHAIN.len());
        out.push_str(before);
        let digits = after.bytes().take_while(u8::is_ascii_digit).count();
        let (offset, tail) = after.split_at(digits);
        let index = seen.iter().position(|s| *s == offset).unwrap_or_else(|| {
            seen.push(offset);
            seen.len() - 1
        });
        out.push_str(&index.to_string());
        rest = tail;
    }
    out.push_str(rest);
    out
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
