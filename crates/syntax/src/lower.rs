//! The lowering: the compiler's tree ([`crate::ast`]) built from the
//! lossless tree ([`crate::tree`]), steps 3 and 4 of
//! docs/proposals/syntax-tree-architecture.md, designed in
//! docs/proposals/syntax-tree-lowering.md.
//!
//! For now the parser still builds the compiler's tree directly, and the
//! lowering runs only in the oracle ([`oracle`], `stitchwort dev tree
//! --lower`), which parses every file both ways and requires the two trees
//! to be identical, spans and hidden names included. It is written kind by
//! kind, in lanes L0 to L4 of the design; a declaration holding a kind not
//! lowered yet is [`Unsupported`], which the oracle counts per kind rather
//! than failing.
//!
//! # Rules
//!
//! - **One function per node kind**, recursive descent shaped like the
//!   parser: [`Lower::decl`] dispatches on a root's kind, `Lower::expr` on
//!   an expression's. The same kind can lower differently by context, which
//!   is why it isn't a generic fold.
//! - **The lowering reads, never parses.** It looks at node kinds, a node's
//!   own tokens (which operator, which bracket, the text of a name) and its
//!   children. If it would have to look at tokens to work out where
//!   something ends or what it belongs to, the parser marks it instead.
//! - **A slot is found by the token that introduces it** (`:=`, `then`,
//!   `=>`), not by position (`lower/access.rs`): with error recovery, a
//!   child may be missing, and reading by position would put the next child
//!   in its slot.
//! - **Spans are the parser's**, quirks included; the oracle compares them.
//! - **Infallible.** In step 3 every error is still the parser's; the
//!   lowering only ever reports that it can't lower something yet.
//! - **`Error` nodes are not looked inside**: what finished before an error
//!   keeps its nodes for the editor, but for the checker it is skipped text.

use crate::Diagnostic;
use crate::ast::{Decl, Expr, FailedName, Import, Module, NamespaceDecl};
use crate::source::FileId;
use crate::stack::StackLimit;
use crate::tree::{Node, NodeKind, SyntaxFile};
use std::fmt;

mod access;
pub(crate) mod binding;
mod decls;
mod definitions;
pub(crate) mod exprs;
pub(crate) mod header;
pub mod oracle;
mod patterns;
pub(crate) mod sections;
mod types;

/// What the lowering can't lower yet: the first such thing it met in a
/// declaration. The oracle counts declarations by it.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Unsupported {
    /// A node of this kind.
    Kind(NodeKind),
    /// A token where an expression should be that the lowering doesn't
    /// read as one: a parser or lowering bug if ever counted.
    Token,
    /// A node of this kind without one of its parts, which the parser
    /// always gives it: a bug if ever counted, until recovery leaves parts
    /// out.
    Missing(NodeKind, &'static str),
    /// An expression nested more deeply than the stack the lowering was
    /// given allows. The parser has the same limit and frames larger than
    /// the lowering's, so a declaration that parsed shouldn't reach it;
    /// when the lowering is the parser's route (lane L5), this is its
    /// `E-RESOURCE`.
    TooDeep,
}

impl fmt::Display for Unsupported {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Unsupported::Kind(kind) => write!(f, "{kind:?}"),
            Unsupported::Token => write!(f, "a token read as an expression"),
            Unsupported::Missing(kind, part) => write!(f, "{kind:?} without {part}"),
            Unsupported::TooDeep => write!(f, "nested too deeply to lower"),
        }
    }
}

pub(crate) type Lowering<T> = Result<T, Unsupported>;

/// What one declaration's tree lowers to.
#[derive(Clone, Debug)]
pub enum LoweredDecl {
    Namespace(NamespaceDecl),
    Import(Import),
    /// A declaration that parsed: one [`Decl`], or a definition's signature
    /// and equations.
    Decls(Vec<Decl>),
    /// A declaration that didn't parse: the names it would have declared
    /// ([`Module::failed`]).
    Failed(Vec<FailedName>),
}

/// The lowering of one file's tree.
pub struct Lower<'f> {
    pub(crate) tree: &'f SyntaxFile,
    pub(crate) text: &'f str,
    pub(crate) file: FileId,
    /// The parser's errors for the file, in file order: a declaration that
    /// didn't parse gives its first error's position to its failed names.
    pub(crate) errors: &'f [Diagnostic],
    /// How deep the lowering may recurse, as the parser's `StackLimit`.
    pub(crate) stack: StackLimit,
}

impl<'f> Lower<'f> {
    /// `tree` is `text`'s, and `errors` the errors of the parse that built
    /// it (as [`crate::parse_module_and_tree`] gives them).
    pub fn new(
        tree: &'f SyntaxFile,
        text: &'f str,
        file: FileId,
        errors: &'f [Diagnostic],
    ) -> Self {
        Lower {
            tree,
            text,
            file,
            errors,
            stack: StackLimit::from_here(crate::DEFAULT_STACK),
        }
    }

    /// Allows the lowering `bytes` of the stack from here, as the parser is
    /// allowed: the `stack` given to [`crate::parse_module_and_tree`].
    pub fn with_stack(mut self, bytes: usize) -> Self {
        self.stack = StackLimit::from_here(bytes);
        self
    }

    /// The whole module, and each declaration that couldn't be lowered yet
    /// (by its index among [`SyntaxFile::decls`]), which the module leaves
    /// out.
    pub fn module(&self) -> (Module, Vec<(usize, Unsupported)>) {
        let mut module = Module::default();
        let mut unsupported = Vec::new();
        for (i, root) in self.tree.decls().enumerate() {
            match self.decl(root) {
                Ok(LoweredDecl::Namespace(namespace)) => module.namespace = Some(namespace),
                Ok(LoweredDecl::Import(import)) => module.imports.push(import),
                Ok(LoweredDecl::Decls(decls)) => module.decls.extend(decls),
                Ok(LoweredDecl::Failed(names)) => module.failed.extend(names),
                Err(what) => unsupported.push((i, what)),
            }
        }
        // A file whose first declaration isn't at the start of a line is
        // one error, with no module at all.
        if !self.split_failed() {
            module.doc_links = crate::docs::bar_links(self.text, self.tree.bars());
        }
        (module, unsupported)
    }

    /// One declaration.
    pub fn decl(&self, root: Node<'f>) -> Lowering<LoweredDecl> {
        match root.kind() {
            NodeKind::Namespace => self.namespace(root).map(LoweredDecl::Namespace),
            NodeKind::Import => self.import(root).map(LoweredDecl::Import),
            NodeKind::Test => Ok(LoweredDecl::Decls(vec![self.test(root)?])),
            NodeKind::Def | NodeKind::Theorem | NodeKind::Instance => {
                self.definition(root).map(LoweredDecl::Decls)
            }
            NodeKind::DataType | NodeKind::RecordType | NodeKind::Interface => {
                Ok(LoweredDecl::Decls(vec![self.data(root)?]))
            }
            NodeKind::TypeSynonym => self.type_synonym(root).map(LoweredDecl::Decls),
            NodeKind::Ability => Ok(LoweredDecl::Decls(vec![self.ability(root)?])),
            NodeKind::Error if root.signature_kept() => {
                Ok(LoweredDecl::Decls(vec![self.kept_signature(root)?]))
            }
            NodeKind::Error => self.failed(root).map(LoweredDecl::Failed),
            kind => Err(Unsupported::Kind(kind)),
        }
    }

    /// The root of a single expression's tree ([`NodeKind::Expression`],
    /// from [`crate::parse_expression_tree`]).
    pub fn expression(&self, root: Node<'f>) -> Lowering<Expr> {
        match root.kind() {
            NodeKind::Expression => {
                let mut elements = root.children();
                match (elements.next(), elements.next()) {
                    (Some(only), None) => self.expr(only),
                    _ => Err(Unsupported::Missing(NodeKind::Expression, "one expression")),
                }
            }
            kind => Err(Unsupported::Kind(kind)),
        }
    }
}
