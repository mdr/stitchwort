//! The lossless syntax tree: every token of a file, with its comments and
//! blank lines, grouped into nodes that say which construct they are.
//! Reading its leaves left to right, each with the text between it and the
//! previous one, gives back the file byte for byte.
//!
//! It is the first step of docs/proposals/syntax-tree-architecture.md
//! (architecture A2, D3562): today it is built *beside* the compiler's tree
//! ([`crate::ast`]) by the same parse; later the compiler's tree is lowered
//! from it and the parser builds nothing else. The formatter, the editor's
//! shape features (outline, folding, selection) and the quick fixes and
//! sweeps are its readers (docs/proposals/formatter-architecture.md §4).
//!
//! # The tree
//!
//! A file is a list of declaration trees, one per top-level declaration as
//! the parser already cuts them (a token at column 0 starts one;
//! [`crate::decl_ranges`]). Each declaration's tree is generic: a node is a
//! [`NodeKind`] and a run of consecutive tokens; its children are the nodes
//! and tokens inside that run, in order. A token's *trivia* (the own-line
//! comments and blank lines before it, and the comment after it on its line)
//! is the lexer's [`Trivia`], so a comment always stays with the token it
//! was written next to, whatever node that token ends up in. The spaces
//! between tokens are not stored: they are the source text between two
//! tokens' spans, which is whitespace and those comments only (the round
//! trip checks it).
//!
//! The nodes are stored flat, in preorder, each with its token range and
//! where its subtree ends, so a node's children are found by walking forward
//! and skipping subtrees, and a node's tokens that are not inside a child
//! are its own leaves. There is no separate "green" and "red" tree as in
//! rowan: a declaration is reparsed whole on every edit, in microseconds.
//!
//! Every construct of the language has a kind, including the shorthand as
//! written (`let (a, b) = e`, a chain `a ≤ b < c`, a `.f` section), since
//! the lowering to the compiler's tree will need them all. A construct of
//! one token (a name, a literal, `_`) is that token, with no node around it.
//! A construct the parser doesn't mark yet is inside an
//! [`NodeKind::Unmarked`] node: its tokens, flat. The parser marks only
//! some constructs so far ([`TreeStats::unmarked`] counts the rest); each
//! one marked replaces an `Unmarked` node with real structure.
//!
//! # Marks
//!
//! The parser doesn't build this tree. It records *marks*: when a parsing
//! function finishes a construct it notes the construct's kind and the
//! token range it started and ended at ([`Mark`]). Its position only ever
//! moves forward, so the ranges of the marks of one parse nest; the builder
//! here sorts them (by start, then the longest first, then the one finished
//! last first, since a construct finishes after everything inside it) and
//! nests them with a stack. A function that only knows its construct's kind
//! after the fact (an expression that turns out to be a binder, say)
//! records it when it does know, at the end; the marks of its parts are
//! already in the list, and could be relabelled from a saved list length
//! the same way. A parse that fails partway leaves its unfinished
//! constructs unmarked, which is why nothing has to be undone.
//!
//! The marks are recorded only when asked for ([`crate::parse_tree`]): the
//! parser holds an `Option` of the list, so with marks off each mark costs
//! one test of `None`, and nothing is allocated.
//!
//! # Errors
//!
//! A declaration that doesn't parse is, for now, one [`NodeKind::Error`]
//! node holding its tokens flat, and a file that doesn't lex has no tree.
//! The end state (D3563, SW-3161) keeps going inside a declaration: a
//! parsing function that meets an error marks an `Error` node around the
//! tokens it skips and carries on, so a broken declaration's tree is whole
//! but for the `Error` nodes, wherever in it they fall; the lowering turns
//! each into a hole. Nothing here assumes an `Error` node is a root.

use crate::lexer::{Comment, Tok, Token, Trivia};
use std::ops::Range;

/// The bytes a token stands for in the source: its span, and for the pieces
/// of an interpolated text, the `${` and `}` around each interpolation,
/// which the lexer's spans leave out (`"a${` is `StrStart`'s, `}b${`
/// `StrMid`'s and `}c"` `StrEnd`'s).
pub fn token_text_range(token: &Token) -> Range<usize> {
    let (start, end) = (token.span.start as usize, token.span.end as usize);
    match token.tok {
        Tok::StrStart(_) => start..end + 2,
        Tok::StrMid(_) | Tok::StrEnd(_) => start - 1..end,
        _ => start..end,
    }
}

/// What a node of the lossless tree is. Single tokens (names, literals,
/// `_`) are leaves, not nodes.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum NodeKind {
    /// A construct the parser doesn't mark yet: its tokens, flat.
    Unmarked,
    /// Tokens that didn't parse.
    Error,

    // Declarations: the root of each declaration's tree.
    /// `namespace Day05`
    Namespace,
    /// `import List (map, filter as f)`
    Import,
    /// `def f …`, at top level or in a block, with `export` or `opaque`.
    Def,
    /// `theorem t …`
    Theorem,
    /// `instance i: Ord Nat := …`
    Instance,
    /// `type T = | A | B`, or a type without constructors.
    DataType,
    /// `type R = { x: Nat }`
    RecordType,
    /// `type Grid = List (List Nat)`
    TypeSynonym,
    /// `interface Ord (a: Type) = { … }`
    Interface,
    /// `ability State (s: Type) where …`
    Ability,
    /// `test "name" := e`
    Test,

    // Parts of declarations.
    /// One group `@[a, b "x"]`.
    Attributes,
    /// One attribute in a group: `js.name "x"`.
    Attribute,
    /// An imported name and its alias: `filter as f`.
    ImportItem,
    /// A header's parameter: `(x y: A)`, `(x: A := v)`, `[x: A]`,
    /// `[auto h: P]`, `()`.
    Param,
    /// `:= v` after a parameter's or field's type.
    Default,
    /// `: T` after a header's parameters, or a theorem's statement; a data
    /// type's `: Nat -> Type`.
    ResultType,
    /// `decreasing e`
    Decreasing,
    /// `unfolding f, g`
    Unfolding,
    /// `:= e` after a header; `= T` after a type synonym's name.
    Body,
    /// A definition's arms, all of them.
    Arms,
    /// `| p, q if c => e`: a definition's arm, or an alternative of a
    /// `match` or a clause lambda.
    Arm,
    /// `if c` or `if h: c` after an arm's patterns.
    Guard,
    /// A type's parameter or a constructor's field in brackets: `(x y: A)`,
    /// `[x: A]`, `[auto ord: Ord k]`; a binder of a function type.
    Binder,
    /// `| C (x: A) : T`: a constructor of a data type.
    Constructor,
    /// `{ name: Text, age: Nat := 0 }`: a record's or constructor's fields.
    Fields,
    /// `name: Text := v` in braces.
    Field,
    /// `get: () -> {State s} s`: one operation of an ability.
    AbilityOp,

    // Blocks.
    /// The lines of a block, when there is more than one.
    Block,
    /// `let p := e` or `let p : T := e`, a block's line.
    Let,

    // Expressions.
    /// `(e)`
    Paren,
    /// `(a, b, c)`
    Tuple,
    /// `[a, b, ..xs]`
    List,
    /// `..xs` in a list.
    Spread,
    /// `{ x = 1, y }`, or an update `{ r | x = 1 }`.
    Record,
    /// `x = 1` in a record literal or update.
    RecordField,
    /// `C { x = 1 }`
    CtorFields,
    /// `f a b`
    App,
    /// `(x := e)` or `[x := e]` as an argument.
    NamedArg,
    /// `e.f`
    FieldAccess,
    /// `.f a`, a function of what is piped into it.
    Section,
    /// `a + b`, `a ∧ b`, `a = b` and every other binary operator.
    Binary,
    /// `a ≤ b < c`, comparisons written as a chain.
    Chain,
    /// `x ∈ xs`, `x ∉ xs`
    Membership,
    /// `a ..< b`, `a ..= b`
    Range,
    /// `-x`, `!b`, `¬p`
    Prefix,
    /// `x |> f`
    Pipe,
    /// `A -> B`
    Arrow,
    /// `(x: A) -> B`, `[x: A] -> B`
    FunctionType,
    /// `∀ (x: A) => P`
    Forall,
    /// `∃ (x: A) => P`
    Exists,
    /// `p ↔ q`
    Iff,
    /// `x (a, b) => e`
    Lambda,
    /// One parameter of a lambda.
    LambdaParam,
    /// `if c then a else b`, or the block form.
    If,
    /// `(e : T)`
    Annotation,
    /// `{IO, State s} T`: a type with abilities.
    Effect,
    /// `{IO, State s}`
    Row,
    /// `a; b`
    Seq,
    /// `(let x := e; body)`
    LetExpr,
    /// `"a${x}b"`, `"""…${x}…"""`
    Interpolated,
    /// `${x}` in a text.
    Interpolation,
    /// `handle e with | op x, k => …`
    Handle,
    /// One clause of a handler.
    HandlerClause,
    /// `match e, f with | …`
    Match,
    /// One matched expression, `h: e` or `e`.
    Scrutinee,
    /// `match | …`, `match some | …`, `matches | …`
    ClauseLambda,
    /// `match induct n with | …`
    Induct,
    /// One case of a `match induct`.
    InductArm,
    /// `match reify e with | …`
    Reify,
    /// `calc a` and its steps.
    Calc,
    /// `_ = b := proof`
    CalcStep,
    /// `rewrite h in e`, `rewrite h at x in e`
    Rewrite,
    /// One rule of a `rewrite`.
    RewriteRule,
    /// `omega [h]`
    Omega,
    /// `ring [h]`
    Ring,
    /// `cases in t`
    Cases,

    // Patterns.
    /// `Cons x xs`, `(C a b)`
    PatternCtor,
    /// `(a, b)`
    PatternTuple,
    /// `[a, ..rest]`
    PatternList,
    /// `x @ p`
    PatternNamed,
    /// `{ x, y = p }`
    PatternRecord,
    /// `C { x = p }`
    PatternCtorFields,
    /// `p | q`
    PatternOr,
    /// `(p)`
    PatternParen,
    /// `(p: T)`
    PatternTyped,
    /// `-3`
    PatternNegative,
}

/// A finished construct, as the parser records it: its kind and the tokens
/// it covers, `start..end`, counted from the declaration's first token.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Mark {
    pub(crate) kind: NodeKind,
    pub(crate) start: u32,
    pub(crate) end: u32,
}

/// What the parser hands over for one declaration: where its tokens are in
/// the file, what it is, and the marks of its parse.
pub(crate) struct DeclMarks {
    /// Its tokens, as indices into the file's tokens.
    pub(crate) tokens: Range<u32>,
    /// The declaration's kind; `Error` if it didn't parse.
    pub(crate) root: NodeKind,
    pub(crate) marks: Vec<Mark>,
}

/// One node, stored flat: see the module's notes.
#[derive(Clone, Copy, Debug)]
struct NodeData {
    kind: NodeKind,
    /// The tokens it covers, as indices into the file's tokens.
    start: u32,
    end: u32,
    /// The index (in its declaration's `nodes`) just past its last
    /// descendant.
    subtree_end: u32,
}

/// The lossless tree of one declaration: its nodes in preorder, the root
/// first.
#[derive(Clone, Debug)]
struct DeclTree {
    nodes: Vec<NodeData>,
}

/// The lossless tree of a file: its tokens with their trivia, and a tree for
/// each declaration. Built by [`crate::parse_tree`].
#[derive(Clone, Debug)]
pub struct SyntaxFile {
    tokens: Vec<Token>,
    trivia: Vec<Trivia>,
    /// What follows the last token.
    eof: Trivia,
    decls: Vec<DeclTree>,
    /// Marks that crossed another's range, which the builder left out: a
    /// parser bug if not 0.
    dropped: usize,
}

/// A node of a [`SyntaxFile`].
#[derive(Clone, Copy)]
pub struct Node<'f> {
    file: &'f SyntaxFile,
    decl: u32,
    index: u32,
}

/// A token of a [`SyntaxFile`], with its trivia.
#[derive(Clone, Copy)]
pub struct Leaf<'f> {
    file: &'f SyntaxFile,
    index: u32,
}

/// A node's child: a node or a token.
#[derive(Clone, Copy)]
pub enum Element<'f> {
    Node(Node<'f>),
    Leaf(Leaf<'f>),
}

/// Counts over a file's trees, for the round-trip tool and the tests.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct TreeStats {
    pub decls: usize,
    /// Declarations that didn't parse.
    pub errors: usize,
    pub nodes: usize,
    /// `Unmarked` nodes: constructs the parser doesn't mark yet.
    pub unmarked: usize,
    /// Marks the builder left out because they crossed another's range.
    pub dropped: usize,
}

impl SyntaxFile {
    pub(crate) fn build(
        tokens: Vec<Token>,
        trivia: Vec<Trivia>,
        eof: Trivia,
        groups: Vec<DeclMarks>,
    ) -> SyntaxFile {
        let mut dropped = 0;
        let decls = groups
            .into_iter()
            .map(|group| build_decl(group, &mut dropped))
            .collect();
        SyntaxFile {
            tokens,
            trivia,
            eof,
            decls,
            dropped,
        }
    }

    /// The root node of each declaration, in file order.
    pub fn decls(&self) -> impl Iterator<Item = Node<'_>> {
        (0..self.decls.len() as u32).map(|decl| Node {
            file: self,
            decl,
            index: 0,
        })
    }

    pub fn tokens(&self) -> &[Token] {
        &self.tokens
    }

    /// The comments and blank lines after the last token.
    pub fn eof(&self) -> &Trivia {
        &self.eof
    }

    /// The file's text, read back from the tree: each leaf in tree order,
    /// with the source text between it and the leaf before. `source` is the
    /// text the tree was parsed from; only the gaps between tokens are read
    /// from it besides the tokens themselves.
    pub fn text(&self, source: &str) -> String {
        let mut out = String::with_capacity(source.len());
        let mut at = 0usize;
        for root in self.decls() {
            root.for_each_leaf(&mut |leaf| {
                let end = leaf.text_range().end;
                out.push_str(&source[at..end]);
                at = end;
            });
        }
        out.push_str(&source[at..]);
        out
    }

    /// Checks that the tree is the whole of `source`, losing nothing: every
    /// token is a leaf exactly once, in order; between two tokens there is
    /// only whitespace and the comments their trivia hold, in order; and
    /// reading the tree back gives `source`. Returns what's wrong, first
    /// problem only.
    pub fn check_round_trip(&self, source: &str) -> Result<TreeStats, String> {
        let mut next = 0u32;
        let mut problem = None;
        for root in self.decls() {
            root.for_each_leaf(&mut |leaf| {
                if problem.is_none() && leaf.index != next {
                    problem = Some(format!(
                        "token {} is a leaf where token {next} should be",
                        leaf.index
                    ));
                }
                next = leaf.index + 1;
            });
        }
        if let Some(problem) = problem {
            return Err(problem);
        }
        if next as usize != self.tokens.len() {
            return Err(format!(
                "the tree's leaves end at token {next} of {}",
                self.tokens.len()
            ));
        }
        let mut at = 0usize;
        for (i, token) in self.tokens.iter().enumerate() {
            let before = i
                .checked_sub(1)
                .and_then(|p| self.trivia[p].trailing.as_ref());
            let comments = before.into_iter().chain(&self.trivia[i].leading);
            let range = token_text_range(token);
            check_gap(source, at, range.start, comments)
                .map_err(|e| format!("before token {i}: {e}"))?;
            at = range.end;
        }
        let last = self.trivia.last().and_then(|t| t.trailing.as_ref());
        check_gap(
            source,
            at,
            source.len(),
            last.into_iter().chain(&self.eof.leading),
        )
        .map_err(|e| format!("at the end: {e}"))?;
        let text = self.text(source);
        if text != source {
            let at = text
                .bytes()
                .zip(source.bytes())
                .position(|(a, b)| a != b)
                .unwrap_or(text.len().min(source.len()));
            return Err(format!("the text read back differs at byte {at}"));
        }
        Ok(self.stats())
    }

    pub fn stats(&self) -> TreeStats {
        let mut stats = TreeStats {
            decls: self.decls.len(),
            dropped: self.dropped,
            ..TreeStats::default()
        };
        for decl in &self.decls {
            if decl.nodes[0].kind == NodeKind::Error {
                stats.errors += 1;
            }
            stats.nodes += decl.nodes.len();
            stats.unmarked += decl
                .nodes
                .iter()
                .filter(|n| n.kind == NodeKind::Unmarked)
                .count();
        }
        stats
    }

    /// The tree as indented text, one node or token per line, for tests and
    /// for looking at: `Def` then its children, a token as its source text.
    pub fn dump(&self, source: &str) -> String {
        let mut out = String::new();
        for root in self.decls() {
            dump_node(root, source, 0, &mut out);
        }
        out
    }
}

fn dump_node(node: Node<'_>, source: &str, depth: usize, out: &mut String) {
    out.push_str(&format!(
        "{:indent$}{:?}\n",
        "",
        node.kind(),
        indent = depth * 2
    ));
    for child in node.children() {
        match child {
            Element::Node(n) => dump_node(n, source, depth + 1, out),
            Element::Leaf(leaf) => {
                out.push_str(&format!(
                    "{:indent$}{}\n",
                    "",
                    &source[leaf.text_range()],
                    indent = (depth + 1) * 2
                ));
            }
        }
    }
}

/// Checks that `source[from..to]` is whitespace and `comments`, in order.
fn check_gap<'c>(
    source: &str,
    from: usize,
    to: usize,
    comments: impl Iterator<Item = &'c Comment>,
) -> Result<(), String> {
    let blank = |s: &str| s.bytes().all(|b| matches!(b, b' ' | b'\n' | b'\r'));
    let mut at = from;
    for comment in comments {
        let (start, end) = (comment.span.start as usize, comment.span.end as usize);
        if start < at || end > to {
            return Err(format!("a comment at byte {start} is outside its gap"));
        }
        if !blank(&source[at..start]) {
            return Err(format!(
                "text at byte {at} is neither a token nor a comment"
            ));
        }
        if source[start..end] != comment.text {
            return Err(format!("the comment at byte {start} isn't its text"));
        }
        at = end;
    }
    if !blank(&source[at..to]) {
        return Err(format!(
            "text at byte {at} is neither a token nor a comment"
        ));
    }
    Ok(())
}

/// Nests one declaration's marks into its tree.
fn build_decl(group: DeclMarks, dropped: &mut usize) -> DeclTree {
    let offset = group.tokens.start;
    let mut marks: Vec<(usize, Mark)> = if group.root == NodeKind::Error {
        Vec::new()
    } else {
        group
            .marks
            .into_iter()
            .filter(|m| m.start < m.end)
            .enumerate()
            .collect()
    };
    // Outer first: by start, then the longest, then the one finished last.
    marks.sort_by(|(i, a), (j, b)| a.start.cmp(&b.start).then(b.end.cmp(&a.end)).then(j.cmp(i)));
    let root = NodeData {
        kind: group.root,
        start: group.tokens.start,
        end: group.tokens.end,
        subtree_end: 0,
    };
    let mut nodes = vec![root];
    // The open nodes, as indices into `nodes`.
    let mut stack: Vec<usize> = vec![0];
    let len = group.tokens.end - group.tokens.start;
    for (k, &(_, mark)) in marks.iter().enumerate() {
        // An `Unmarked` node around a construct that is marked is that
        // construct.
        if mark.kind == NodeKind::Unmarked
            && marks
                .get(k + 1)
                .is_some_and(|(_, next)| next.start == mark.start && next.end == mark.end)
        {
            continue;
        }
        let (start, end) = (mark.start, mark.end.min(len));
        // The whole declaration is the root already.
        if start == 0 && end == len {
            continue;
        }
        while let Some(&top) = stack.last()
            && nodes[top].end <= offset + start
        {
            nodes[top].subtree_end = nodes.len() as u32;
            stack.pop();
        }
        let parent = *stack.last().expect("the root covers every mark");
        if offset + end > nodes[parent].end {
            *dropped += 1;
            continue;
        }
        // Inside an `Unmarked` node, an `Unmarked` part is no news: only
        // the outermost is kept, so that each is one unmarked construct.
        if mark.kind == NodeKind::Unmarked && nodes[parent].kind == NodeKind::Unmarked {
            continue;
        }
        stack.push(nodes.len());
        nodes.push(NodeData {
            kind: mark.kind,
            start: offset + start,
            end: offset + end,
            subtree_end: 0,
        });
    }
    let total = nodes.len() as u32;
    for open in stack {
        nodes[open].subtree_end = total;
    }
    DeclTree { nodes }
}

impl<'f> Node<'f> {
    fn data(&self) -> &'f NodeData {
        &self.file.decls[self.decl as usize].nodes[self.index as usize]
    }

    pub fn kind(&self) -> NodeKind {
        self.data().kind
    }

    /// The tokens it covers, as indices into [`SyntaxFile::tokens`].
    pub fn token_range(&self) -> Range<usize> {
        let data = self.data();
        data.start as usize..data.end as usize
    }

    /// Its child nodes and its own tokens, in source order.
    pub fn children(&self) -> impl Iterator<Item = Element<'f>> + 'f {
        let file = self.file;
        let decl = self.decl;
        let nodes = &file.decls[decl as usize].nodes;
        let data = nodes[self.index as usize];
        let mut child = self.index + 1;
        let mut token = data.start;
        std::iter::from_fn(move || {
            let next = (child < data.subtree_end).then(|| nodes[child as usize]);
            match next {
                Some(node) if node.start == token => {
                    let element = Element::Node(Node {
                        file,
                        decl,
                        index: child,
                    });
                    child = node.subtree_end;
                    token = node.end;
                    Some(element)
                }
                _ if token < data.end => {
                    token += 1;
                    Some(Element::Leaf(Leaf {
                        file,
                        index: token - 1,
                    }))
                }
                _ => None,
            }
        })
    }

    /// Calls `f` on every token under this node, in order.
    pub fn for_each_leaf(&self, f: &mut impl FnMut(Leaf<'f>)) {
        for child in self.children() {
            match child {
                Element::Node(node) => node.for_each_leaf(f),
                Element::Leaf(leaf) => f(leaf),
            }
        }
    }
}

impl<'f> Leaf<'f> {
    /// Its index in [`SyntaxFile::tokens`].
    pub fn index(&self) -> usize {
        self.index as usize
    }

    pub fn token(&self) -> &'f Token {
        &self.file.tokens[self.index as usize]
    }

    pub fn trivia(&self) -> &'f Trivia {
        &self.file.trivia[self.index as usize]
    }

    /// Its bytes in the source ([`token_text_range`]).
    pub fn text_range(&self) -> Range<usize> {
        token_text_range(self.token())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::SourceMap;
    use crate::parser::parse_both;

    /// A few files of each kind, with comments, attributes, text blocks and
    /// interpolation among them.
    const SAMPLES: &[&str] = &[
        "crates/elab/src/std/List/Sort.sw",
        "crates/elab/src/std/List/Toolkit.sw",
        "crates/elab/src/std/Option/Option.sw",
        "crates/elab/src/std/Parse/Parse.sw",
        "aoc/src/Aoc/Year2020/Day01/Day01.sw",
        "aoc/src/Aoc/Year2020/Day01/Proofs/Proofs.sw",
        "aoc/src/Aoc/Year2025/Day07/Tests/Examples.sw",
        "examples/accept/text-block.sw",
        "examples/accept/attributes.sw",
        "examples/accept/abort-inversion.sw",
        "examples/accept/handlers.sw",
        "examples/accept/decisions.sw",
        "examples/accept/rows.sw",
    ];

    fn sample(path: &str) -> String {
        let root = concat!(env!("CARGO_MANIFEST_DIR"), "/../../");
        std::fs::read_to_string(format!("{root}{path}")).expect("a sample file")
    }

    fn tree(text: &str) -> SyntaxFile {
        let file = SourceMap::new().next_id();
        crate::parse_tree(file, text, crate::DEFAULT_STACK).expect("it lexes")
    }

    #[test]
    fn every_sample_reads_back_as_written() {
        for path in SAMPLES {
            let text = sample(path);
            let stats = tree(&text)
                .check_round_trip(&text)
                .unwrap_or_else(|e| panic!("{path}: {e}"));
            assert_eq!((stats.errors, stats.dropped), (0, 0), "{path}: {stats:?}");
        }
    }

    #[test]
    fn marks_leave_the_compilers_tree_unchanged() {
        for path in SAMPLES {
            let text = sample(path);
            let file = SourceMap::new().next_id();
            let (module, errors) =
                crate::parse_module_recovering(file, &text, crate::DEFAULT_STACK);
            let (marked, marked_errors, _) =
                parse_both(file, &text, crate::DEFAULT_STACK).expect("it lexes");
            assert_eq!(format!("{module:?}"), format!("{marked:?}"), "{path}");
            assert_eq!(
                format!("{errors:?}"),
                format!("{marked_errors:?}"),
                "{path}"
            );
        }
    }

    #[test]
    fn a_definition_is_marked_down_to_its_arms() {
        let text = "\
-- About f.
@[tailrec]
def f (n: Nat) [a: Type] (x: a := d): Nat
  | 0 => 1 -- the base
  | k if k > 2 => match k with
    | j => j

theorem t: 1 = 1 := rfl
";
        let tree = tree(text);
        tree.check_round_trip(text).unwrap();
        assert_eq!(
            tree.dump(text),
            "\
Def
  Attributes
    @
    [
    Attribute
      tailrec
    ]
  def
  f
  Param
    (
    n
    :
    Unmarked
      Nat
    )
  Param
    [
    a
    :
    Unmarked
      Type
    ]
  Param
    (
    x
    :
    Unmarked
      a
    Default
      :=
      Unmarked
        d
    )
  ResultType
    :
    Unmarked
      Nat
  Arms
    Arm
      |
      Unmarked
        0
      =>
      Unmarked
        1
    Arm
      |
      Unmarked
        k
      Guard
        if
        Unmarked
          k
          >
          2
      =>
      Match
        match
        Scrutinee
          Unmarked
            k
        with
        Arm
          |
          Unmarked
            j
          =>
          Unmarked
            j
Theorem
  theorem
  t
  ResultType
    :
    Unmarked
      1
      =
      1
  Body
    :=
    Unmarked
      rfl
"
        );
        assert_eq!(tree.stats().unmarked, 14);
        // The comments stay with the tokens they were written beside.
        let first = tree.decls().next().unwrap();
        let mut leaves = Vec::new();
        first.for_each_leaf(&mut |leaf| leaves.push(leaf));
        assert_eq!(leaves[0].trivia().leading[0].text, "-- About f.");
        let one = leaves
            .iter()
            .find(|l| &text[l.text_range()] == "1")
            .unwrap();
        assert_eq!(one.trivia().trailing.as_ref().unwrap().text, "-- the base");
    }

    #[test]
    fn a_block_marks_its_lines() {
        let text = "\
def f (n: Nat): Nat :=
  let m := n + 1
  def g (k: Nat): Nat := k
  g m
";
        let tree = tree(text);
        tree.check_round_trip(text).unwrap();
        let dump = tree.dump(text);
        let body = &dump[dump.find("  Body").unwrap()..];
        assert_eq!(
            body,
            "  Body
    :=
    Block
      Let
        let
        Unmarked
          m
        :=
        Unmarked
          n
          +
          1
      Def
        def
        g
        Param
          (
          k
          :
          Unmarked
            Nat
          )
        ResultType
          :
          Unmarked
            Nat
        Body
          :=
          Unmarked
            k
      Unmarked
        g
        m
"
        );
    }

    #[test]
    fn a_declaration_that_does_not_parse_is_an_error_node() {
        let text = "def f (n: Nat): Nat := (\n\n-- trailing\ndef g: Nat := 1\n";
        let tree = tree(text);
        let stats = tree.check_round_trip(text).unwrap();
        assert_eq!((stats.decls, stats.errors), (2, 1));
        let kinds: Vec<NodeKind> = tree.decls().map(|d| d.kind()).collect();
        assert_eq!(kinds, [NodeKind::Error, NodeKind::Def]);
    }
}
