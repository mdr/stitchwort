//! The lowering: the compiler's tree ([`crate::ast`]) built from the
//! lossless tree ([`crate::tree`]), steps 3 and 4 of
//! docs/proposals/syntax-tree-architecture.md, designed in
//! docs/proposals/syntax-tree-lowering.md.
//!
//! The public parse functions ([`crate::parse_module_recovering`],
//! [`crate::parse_expression_within`] and the rest) build the lossless tree
//! and lower it: the parser only marks where constructs start and end
//! (step 4). A declaration the lowering can't lower ([`Unsupported`]) is an
//! error on the public route: one the lowering raises itself
//! ([`Unsupported::Invalid`]), `E-RESOURCE` if it ran out of stack,
//! otherwise an internal error.
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
//! - **Spans are the ones the parser used to give**, quirks included: the
//!   hash snapshots and messages depend on them.
//! - **Errors about meaning are the lowering's.** The parser checks only
//!   what decides how tokens group; a check on what has been grouped, such
//!   as a parameter named twice, is the lowering's
//!   ([`Unsupported::Invalid`]). Without recovery, a declaration reports its
//!   earliest error, so the parser's errors after the lowering's in the same
//!   declaration are dropped.
//! - **`Error` nodes are not looked inside**: what finished before an error
//!   keeps its nodes for the editor, but for the checker it is skipped text.
//!   In a declaration the parser recovered in ([`crate::tree::Node::recoveries`]),
//!   an `Error` node in an expression's place, and an operand or body the
//!   text ran out before, lower to [`crate::ast::Expr::Missing`]: a gap the
//!   checker fills with an error hole and reports nothing about.
//!
//! # Errors
//!
//! A declaration reports one error, the earliest, unless the parser
//! recovered in it (a `def` or `theorem` body,
//! docs/proposals/syntax-error-recovery.md): then each recovery's error is
//! reported, the declaration keeps its signature with
//! `syntax_error` set, and its body lowers
//! with the gaps missing. Otherwise the parser stops a declaration at its
//! first error; the lowering runs after the parse, so its
//! own error ([`Unsupported::Invalid`]) can come after one the parser found
//! later in the same declaration's text. The lowering's error replaces the
//! parser's later ones in that declaration (`lowered_module` in
//! `parser.rs`), and the errors are put back in file order. A `def` or
//! `theorem` the lowering refuses keeps its signature
//! (`Lower::signature_despite`), so what uses it still checks against its
//! stated type; any other declaration it refuses is a failed name, as one
//! that didn't parse is ([`crate::ast::Module::failed`]). Which errors are
//! shown, and their text, are what is held; the order is not (D3574).
//!
//! # Stack
//!
//! The parser and the lowering each recurse as deep as the expression
//! nests. The parser is given half of the stack a caller offers
//! (`parser_limit` in `parser.rs`) and the lowering all of it
//! ([`Lower::with_stack`]): the lowering's frames hold trees, and for some
//! shapes it needs up to 1.55 times the parser's stack per level
//! (`(.f (.f …))`, `f (f (…))`; 1.2 in release builds). Giving the parser
//! half keeps the rule that whatever parses lowers, so [`Unsupported::TooDeep`]
//! is reached only by a bug. A function on a recursive path should keep its
//! frame small: a lowering function that inlines a large helper can cost the
//! nesting limit more than a measurable slowdown would.

use crate::ast::{Decl, Expr, FailedName, Import, Module, NamespaceDecl};
use crate::source::FileId;
use crate::stack::StackLimit;
use crate::tree::{Node, NodeKind, SyntaxFile};
use crate::{Diagnostic, Span};
use std::fmt;

mod access;
mod binding;
#[cfg(test)]
mod coverage;
mod decls;
mod definitions;
mod exprs;
mod header;
mod matching;
mod patterns;
mod proofs;
pub(crate) mod sections;
mod types;

/// What the lowering couldn't lower: the first such thing it met in a
/// declaration.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Unsupported {
    /// An error in the program that only shows once its parts are grouped,
    /// such as a parameter named twice: reported as it is.
    Invalid(Box<Diagnostic>),
    /// A node of this kind.
    Kind(NodeKind),
    /// A token where an expression should be that the lowering doesn't
    /// read as one: a parser or lowering bug if ever counted.
    Token,
    /// A node of this kind without one of its parts, which the parser
    /// always gives it: a bug if ever counted, until recovery leaves parts
    /// out.
    Missing(NodeKind, &'static str),
    /// A node of this kind with more parts than the parser gives it, which
    /// the lowering would leave unread: a bug if ever counted, such as an
    /// operator lying flat beside its operands because its node was lost.
    Unread(NodeKind),
    /// An expression or pattern nested more deeply than the stack the
    /// lowering was given allows, at the first token of the node it was
    /// about to lower. The parser stops at half the stack the lowering gets,
    /// so a declaration that parsed shouldn't reach it; if one does, it is
    /// an `E-RESOURCE` error like the parser's.
    TooDeep(Span),
    /// A declaration whose marks the tree's builder couldn't nest, and why
    /// ([`Node::misnested`]): a parser bug. Its tree isn't what was parsed,
    /// so lowering it could check a different statement than the one
    /// written.
    Misnested(&'static str),
}

impl fmt::Display for Unsupported {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Unsupported::Invalid(error) => write!(f, "{}", error.message),
            Unsupported::Kind(kind) => write!(f, "{kind:?}"),
            Unsupported::Token => write!(f, "a token read as an expression"),
            Unsupported::Missing(kind, part) => write!(f, "{kind:?} without {part}"),
            Unsupported::Unread(kind) => write!(f, "{kind:?} with parts left unread"),
            Unsupported::TooDeep(_) => write!(f, "nested too deeply to lower"),
            Unsupported::Misnested(why) => write!(f, "its nodes don't nest: {why}"),
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
                Err(what) => {
                    module.decls.extend(self.signature_despite(root, &what));
                    unsupported.push((i, what));
                }
            }
        }
        // A file whose first declaration isn't at the start of a line is
        // one error, with no module at all.
        if !self.split_failed() {
            module.doc_links = crate::docs::bar_links(self.text, self.tree.bars());
        }
        (module, unsupported)
    }

    /// For a top-level `def` or `theorem` that parsed but whose body the
    /// lowering refused (`what`), its signature, kept as the parser keeps
    /// one whose body doesn't parse (docs/proposals/tests-with-errors.md
    /// §3.3); none if its header is what was refused.
    pub(crate) fn signature_despite(&self, root: Node<'f>, what: &Unsupported) -> Option<Decl> {
        let Unsupported::Invalid(error) = what else {
            return None;
        };
        if !matches!(root.kind(), NodeKind::Def | NodeKind::Theorem) {
            return None;
        }
        let at = error.primary_span()?;
        self.signature_with_error(root, at).ok()
    }

    /// One declaration.
    pub fn decl(&self, root: Node<'f>) -> Lowering<LoweredDecl> {
        Self::whole(root)?;
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
            NodeKind::Error => {
                // A definition that failed after its header: the header's
                // own error, such as a parameter named twice, came first.
                if let Err(refused @ Unsupported::Invalid(_)) = self.header_of(root) {
                    return Err(refused);
                }
                self.failed(root).map(LoweredDecl::Failed)
            }
            kind => Err(Unsupported::Kind(kind)),
        }
    }

    /// That the stack ran out before `node`: cold and out of line, to keep
    /// it out of the frames of the functions that check.
    #[cold]
    #[inline(never)]
    pub(crate) fn too_deep(&self, node: Node<'f>) -> Unsupported {
        let first = self.tree.tokens().get(node.token_range().start);
        Unsupported::TooDeep(first.map_or(Span::NOWHERE, |token| token.span))
    }

    /// The root of a single expression's tree ([`NodeKind::Expression`],
    /// from [`crate::parse_expression_tree`]).
    pub fn expression(&self, root: Node<'f>) -> Lowering<Expr> {
        Self::whole(root)?;
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

    /// Refuses a root whose marks didn't nest: its tree isn't the parse,
    /// and could read as a different statement, such as `a ∧ b ∧ c` for
    /// `a ∧ b ∧ c → q` with the arrow's node gone.
    fn whole(root: Node<'f>) -> Lowering<()> {
        match root.misnested() {
            None => Ok(()),
            Some(why) => Err(Unsupported::Misnested(why)),
        }
    }
}

#[cfg(test)]
mod dispatch_inlining {
    /// The lower/ sources, including the dispatchers and every file a
    /// dispatched function may be defined in.
    const SOURCES: [(&str, &str); 12] = [
        ("access.rs", include_str!("lower/access.rs")),
        ("binding.rs", include_str!("lower/binding.rs")),
        ("coverage.rs", include_str!("lower/coverage.rs")),
        ("decls.rs", include_str!("lower/decls.rs")),
        ("definitions.rs", include_str!("lower/definitions.rs")),
        ("exprs.rs", include_str!("lower/exprs.rs")),
        ("header.rs", include_str!("lower/header.rs")),
        ("matching.rs", include_str!("lower/matching.rs")),
        ("patterns.rs", include_str!("lower/patterns.rs")),
        ("proofs.rs", include_str!("lower/proofs.rs")),
        ("sections.rs", include_str!("lower/sections.rs")),
        ("types.rs", include_str!("lower/types.rs")),
    ];

    fn source(file: &str) -> &'static str {
        SOURCES
            .iter()
            .find(|(name, _)| *name == file)
            .map(|(_, text)| *text)
            .expect("a lower/ source")
    }

    /// The names called directly in the arms of `function`'s
    /// `match node.kind()` — as `self.NAME(`, `Self::NAME(` or a bare
    /// function `NAME(` — and whether each is called as a method.
    fn dispatched(function: &str, file: &str) -> Vec<(String, bool)> {
        let lines: Vec<&str> = source(file).lines().collect();
        let at = lines
            .iter()
            .position(|line| line.contains(&format!("fn {function}(")))
            .unwrap_or_else(|| panic!("`fn {function}` is not in `{file}`"));
        let matched = lines[at..]
            .iter()
            .position(|line| line.contains("match node.kind()"))
            .map(|offset| at + offset)
            .unwrap_or_else(|| panic!("`{function}` has no `match node.kind()`"));
        let mut depth = 0i32;
        let mut arms = String::new();
        for line in &lines[matched..] {
            arms.push_str(line);
            arms.push('\n');
            depth += line.matches('{').count() as i32;
            depth -= line.matches('}').count() as i32;
            if depth <= 0 {
                break;
            }
        }
        let mut names: Vec<(String, bool)> = Vec::new();
        for (marker, method) in [("self.", true), ("Self::", false)] {
            let mut rest = arms.as_str();
            while let Some(found) = rest.find(marker) {
                let after = &rest[found + marker.len()..];
                let name: String = after
                    .chars()
                    .take_while(|c| c.is_alphanumeric() || *c == '_')
                    .collect();
                let called = !name.is_empty() && after[name.len()..].starts_with('(');
                if called && !names.iter().any(|(seen, _)| *seen == name) {
                    names.push((name, method));
                }
                rest = after;
            }
        }
        // Bare calls of free functions, such as `unit(node)`. Names after a
        // `.` or `::` are already handled, and an uppercase name is a
        // constructor, such as `Err(...)`.
        let bytes = arms.as_bytes();
        let mut i = 0;
        while i < bytes.len() {
            if !(bytes[i].is_ascii_alphabetic() || bytes[i] == b'_') {
                i += 1;
                continue;
            }
            let start = i;
            while i < bytes.len() && (bytes[i].is_ascii_alphanumeric() || bytes[i] == b'_') {
                i += 1;
            }
            let name = &arms[start..i];
            let plain = match arms[..start].chars().next_back() {
                Some('.') | Some(':') => false,
                Some(c) if c.is_alphanumeric() || c == '_' => false,
                _ => true,
            };
            let free = name.starts_with(|c: char| c.is_ascii_lowercase());
            if plain && free && arms[i..].starts_with('(') {
                let name = name.to_string();
                if !names.iter().any(|(seen, _)| *seen == name) {
                    names.push((name, false));
                }
            }
        }
        names.sort();
        names
    }

    /// Whether `name` is defined in `source` with `#[inline(never)]` just
    /// above its `fn`; `None` if it isn't defined there. A `method` is one
    /// taking `&self`, so a free function of the same name doesn't count. A
    /// file's trailing test module is ignored.
    fn definition(source: &str, name: &str, method: bool) -> Option<bool> {
        let source = &source[..source.find("#[cfg(test)]").unwrap_or(source.len())];
        let lines: Vec<&str> = source.lines().collect();
        let mut marked = None;
        for (i, line) in lines.iter().enumerate() {
            let trimmed = line.trim_start();
            let Some(found) = trimmed.find("fn ") else {
                continue;
            };
            if found > 0 && !trimmed[..found].ends_with(' ') {
                continue;
            }
            let after = &trimmed[found + "fn ".len()..];
            if !after.starts_with(name) || !after[name.len()..].starts_with('(') {
                continue;
            }
            if method && !after[name.len()..].starts_with("(&self") {
                continue;
            }
            let mut inline_never = false;
            for above in lines[..i].iter().rev() {
                let above = above.trim();
                if above.is_empty() || above.starts_with("//") {
                    continue;
                }
                if above.starts_with("#[") {
                    inline_never |= above.replace(' ', "") == "#[inline(never)]";
                    continue;
                }
                break;
            }
            marked = Some(marked.unwrap_or(true) && inline_never);
        }
        marked
    }

    /// Every function `node_expr` and `node_pattern` dispatch to stays out
    /// of line. When the compiler inlines one into a dispatcher, the
    /// dispatcher's frame grows (once from 96 to 816 bytes for
    /// `node_expr`), and deeply nested input exhausts the stack in release
    /// builds (SW-3220).
    #[test]
    fn dispatched_functions_stay_out_of_line() {
        let mut missing = Vec::new();
        for (function, file) in [("node_expr", "exprs.rs"), ("node_pattern", "patterns.rs")] {
            for (name, method) in dispatched(function, file) {
                let definitions: Vec<_> = SOURCES
                    .iter()
                    .filter_map(|(path, text)| {
                        definition(text, &name, method).map(|marked| (*path, marked))
                    })
                    .collect();
                assert!(
                    !definitions.is_empty(),
                    "`{name}` is dispatched by `{function}` but is not defined in the lower/ files"
                );
                if definitions.iter().any(|(_, marked)| !marked) {
                    missing.push((function, name));
                }
            }
        }
        let report = missing
            .iter()
            .map(|(function, name)| {
                format!(
                    "`{name}` is dispatched by `{function}` but is not marked `#[inline(never)]`"
                )
            })
            .collect::<Vec<_>>()
            .join("\n");
        assert!(
            missing.is_empty(),
            "{report}\n\nEvery function a kind dispatcher calls must stay out of line so the \
             dispatcher keeps a small stack frame at every level of nesting. Inlining one into \
             `node_expr` once grew its frame from 96 to 816 bytes, and deeply nested input then \
             exhausted the stack in release builds (SW-3220)."
        );
    }
}
