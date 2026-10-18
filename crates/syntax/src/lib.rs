//! Surface syntax for Stitchwort: source files, spans, diagnostics, the lexer,
//! the parser and the surface syntax tree.

pub mod ast;
mod diagnostic;
pub mod equivalence;
mod lexer;
mod parser;
mod source;
pub mod stack;

pub use diagnostic::{Diagnostic, Label, Severity};
/// The token stream, for tools that edit source text at token spans (the
/// one-off declaration-syntax converter, `crates/convert`).
pub use lexer::{Tok, Token, lex};
pub use parser::{
    DEFAULT_STACK, parse_expression, parse_expression_within, parse_module, parse_module_within,
};
pub use source::{FileId, SourceFile, SourceMap, Span};
