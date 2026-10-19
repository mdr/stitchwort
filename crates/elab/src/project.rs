//! The pieces of a module that is more than one file (docs/proposals/
//! multi-file.md §4.4): the files [`Elaborator::elaborate_namespace`] takes.

use stitchwort_syntax::FileId;
use stitchwort_syntax::ast::Module;

/// One file of a module: its display name (project-relative path, for
/// messages) and its syntax.
pub struct SourceUnit<'a> {
    /// `None` only from `elaborate_module`, which isn't told its file.
    pub file: Option<FileId>,
    pub name: &'a str,
    pub module: &'a Module,
}
