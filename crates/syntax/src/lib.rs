//! Surface syntax for Stitchwort: source files, spans, diagnostics, the lexer,
//! the parser and the surface syntax tree.

pub mod ast;
mod diagnostic;
mod lexer;
mod parser;
mod source;
pub mod stack;

pub use diagnostic::{Diagnostic, Label, Severity};
pub use parser::{
    DEFAULT_STACK, parse_expression, parse_expression_within, parse_module, parse_module_within,
};
pub use source::{FileId, SourceFile, SourceMap, Span};
