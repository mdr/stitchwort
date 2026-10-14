//! Surface syntax for Stitchwort: source files, spans, diagnostics, the lexer,
//! the parser and the surface syntax tree.

pub mod ast;
mod diagnostic;
mod lexer;
mod parser;
mod source;

pub use diagnostic::{Diagnostic, Label, Severity};
pub use parser::{parse_expression, parse_module};
pub use source::{FileId, SourceFile, SourceMap, Span};
