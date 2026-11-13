//! Surface syntax for Stitchwort: source files, spans, diagnostics, the lexer,
//! the parser and the surface syntax tree.

#[cfg(test)]
use stitchwort_test_alloc as _;

pub mod ast;
mod diagnostic;
pub mod docs;
pub mod equivalence;
mod lexer;
mod negation;
mod parser;
mod source;
pub mod stack;
pub mod tree;

pub use diagnostic::{
    BuildSite, COMPUTES_TO_LIMIT, Counterexample, Detail, Diagnostic, GoalData, Hypothesis, Label,
    MissingCases, Severity, SuggestedImport, cut_computed,
};
/// The token stream, for tools that edit source text at token spans.
pub use lexer::{
    Comment, Lexed, Tok, Token, Trivia, UNICODE_ALIASES, keywords, lex, lex_recovering,
    lex_with_bars, lex_with_trivia,
};
pub use negation::{
    argument_bang, argument_minus, argument_prefix, closes_operand, negative_numeral, opens_atom,
};
pub use parser::{
    DEFAULT_STACK, MAX_UNIVERSE_LEVEL, decl_ranges, parse_expression, parse_expression_within,
    parse_module, parse_module_and_tree, parse_module_recovering, parse_module_within,
    parse_namespace_line, parse_tree, record_braces,
};
pub use source::{FileId, SourceFile, SourceMap, Span};
