//! Surface syntax for Stitchwort: source files, spans, diagnostics, the lexer,
//! the parser and the surface syntax tree.

pub mod ast;
mod diagnostic;
pub mod equivalence;
mod lexer;
mod negation;
mod parser;
mod source;
pub mod stack;

pub use diagnostic::{Diagnostic, Label, Severity};
/// The token stream, for tools that edit source text at token spans.
pub use lexer::{Comment, Lexed, Tok, Token, Trivia, UNICODE_ALIASES, lex, lex_with_trivia};
pub use negation::{argument_minus, closes_operand, negative_numeral, opens_atom};
pub use parser::{
    DEFAULT_STACK, decl_ranges, parse_expression, parse_expression_within, parse_module,
    parse_module_recovering, parse_module_within, parse_namespace_line,
};
pub use source::{FileId, SourceFile, SourceMap, Span};
