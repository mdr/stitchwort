//! The lossless syntax tree: every token of a file, with its comments and
//! blank lines, grouped into nodes that say which construct they are.
//! Reading its leaves left to right, each with the text between it and the
//! previous one, gives back the file byte for byte.
//!
//! It is the one thing the parser builds (architecture A2 of
//! docs/proposals/syntax-tree-architecture.md, D3562): the compiler's tree
//! ([`crate::ast`]) is lowered from it ([`crate::lower`]), and the formatter
//! (docs/proposals/formatter-architecture.md), the editor's shape features
//! (outline, folding, selection) and the quick fixes and sweeps read it
//! directly (formatter-architecture.md §4).
//!
//! Every construct is marked, and the whole-repo gate over std, `aoc/src`,
//! `games` and `examples` is one command, for a rolling check: every file
//! reads back as written, every declaration's marks nest, and every span of
//! the compiler's tree is a node ([`SyntaxFile::check_spans`]). A construct the
//! parser forgets to mark fails it, since the lowering gives the compiler's
//! tree a span that no node has.
//!
//! ```text
//! stitchwort dev tree --spans crates/elab/src/std aoc/src games examples
//! ```
//!
//! which exits 1 if any file doesn't read back, a declaration's marks don't
//! nest, or a span is no node, and prints each. (`examples` has files that don't lex or
//! parse on purpose; they are counted, not failures.) `--time N` times
//! parsing as `check` does (the lossless tree, then the lowering) and the
//! lossless tree alone, so the difference is the lowering; with
//! `--parse-only` it times the first alone and skips the rest, so that an
//! instruction count of the process measures that and nothing else.
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
//! the lowering to the compiler's tree needs them all. A construct of
//! one token (a name, a literal, `_`) is that token, with no node around it.
//! A construct the parser forgot to mark would leave its tokens flat in its
//! parent; the span-containment check ([`SyntaxFile::check_spans`]) is what
//! finds one, since the compiler's tree has a span for it that no node has.
//!
//! # Marks
//!
//! The parser doesn't build this tree. It records *marks*: when a parsing
//! function finishes a construct it notes the construct's kind and the
//! token range from where it started to the last token read (`Mark`). The
//! function keeps its start as a value (`let start = self.mark()`) and
//! records one mark when it finishes; no mark is recorded any other way,
//! changed afterwards, or read back to decide where another starts. So the
//! marks come in the order the constructs finish: ends never go back, and
//! of two with the same range the later is the outer. The builder
//! (`Nester`) nests them in two linear passes, with no sort, and checks
//! as it goes: marks out of that order, or two that cross, are a parser
//! bug, and the declaration's tree is then its root alone
//! ([`Node::misnested`]), which the lowering refuses as an internal error,
//! rather than a tree that reads as a different program.
//!
//! Why marks, rather than parsing functions that return the nodes they
//! built (docs/proposals/parser-marks-or-nodes.md, D3600): the tree stores
//! the tokens once and a node is a range of them, so a function has
//! nothing to return but where it started, which its caller already knows;
//! a function that fails has written nothing, and what finished before it
//! stays, so recovery needs no undoing (a recovery point's `Error` node
//! starts where the construct that failed started, and what finished
//! inside nests in it); and frames that hold no nodes keep nesting deep.
//!
//! An operator only learns it has a left operand once the operand is read
//! (`a` in `a + b`): the function that reads both keeps the start before
//! reading the operand, and marks the operator's node from there. A
//! construct whose kind is known late (`exists` reads a lambda) is marked
//! by the function that knows it, given the kind or the start. A construct
//! that read nothing (a part R1 found missing) gives an empty mark, which
//! is no node.
//!
//! # Errors
//!
//! A declaration that doesn't parse, and isn't recovered in, is an
//! [`NodeKind::Error`] root: the constructs finished before the error keep their nodes (a
//! definition's header, say), and the rest of its tokens are flat under the
//! root. A declaration that doesn't lex has no tokens: it is an `Error` root
//! with no children over its raw text ([`Node::raw_text_range`]), which
//! the round trip reads back like the text between tokens, so the rest of
//! the file still has its tree. The end state
//! (docs/proposals/syntax-error-recovery.md, D3563) keeps going inside a
//! declaration: a parsing function that meets an error marks an `Error` node
//! around the tokens it skips and carries on, so a broken declaration's tree
//! is whole but for the `Error` nodes, wherever in it they fall; the
//! lowering turns each into a hole. Nothing here assumes an `Error` node is
//! a root.

use crate::Span;
use crate::lexer::{Comment, Token, Trivia};
use std::ops::Range;

mod spans;
pub use spans::{SpanCheck, SpanMiss, Synthetic};

/// What a node of the lossless tree is. Single tokens (names, literals,
/// `_`) are leaves, not nodes.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum NodeKind {
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
    /// `rules words := [r1, <- r2]`: a named set of rules for `rewrite
    /// repeatedly` (docs/proposals/simp-revisited.md §2.3).
    Rules,
    /// A single expression parsed on its own ([`crate::parse_expression_tree`]),
    /// as a search query or in the playground: the root of its tree, with
    /// the expression its one child.
    Expression,

    // Parts of declarations.
    /// One group `@[a, b "x"]`.
    Attributes,
    /// One attribute in a group: `js.name "x"`.
    Attribute,
    /// An attribute's name of more than one part: `js.name`.
    AttributeName,
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
    /// `()`
    Unit,
    /// `Type 1`; `Type` alone is a token.
    Universe,
    /// `include "inputs/day04.txt"`
    Include,
    /// `(a, b, c)`
    Tuple,
    /// `[a, b, ..xs]`
    List,
    /// `..xs` in a list.
    Spread,
    /// `{ x = 1, y }`, or an update `{ r | x = 1 }`.
    Record,
    /// `x = 1` in a record literal or update; a punned `x` is a token.
    RecordField,
    /// `C { x = 1 }` or `C { r | x = 1 }`: a constructor's name and a
    /// `Record`.
    CtorFields,
    /// `f a b`, one node however many arguments; `f()`, its argument a
    /// `Unit`.
    App,
    /// `(x := e)` or `[x := e]` as an argument.
    NamedArg,
    /// `e.f`; in a method section, `.f` (no receiver).
    FieldAccess,
    /// A method section: the function `x => x.f a` written `.f a`. It runs
    /// from the `.` to the end of the function, its body: `.f a` (the
    /// arguments of `.f` at the head of an application), or the whole of
    /// `.id == id` (an expression that starts with a section). The `.f` is
    /// a `FieldAccess` without a receiver.
    Section,
    /// `(+ 1)`, `(k +)`, `(&&)`: an operator as a function.
    OperatorSection,
    /// `a + b`, `a ∧ b`, `a = b` and every other binary operator. Each
    /// node has one operator: `a + b + c` is `(a + b) + c` and
    /// `a ++ b ++ c` is `a ++ (b ++ c)`, grouped as the operators group.
    Binary,
    /// `a ≤ b < c`, comparisons written as a chain.
    Chain,
    /// `x ∈ xs`, `x ∉ xs`
    Membership,
    /// `a ..< b`, `a ..= b`
    Range,
    /// `-x`, `!b`, `¬p`, and a negative numeral `-1`.
    Prefix,
    /// `x |> f`; `x |> f |> g` is `(x |> f) |> g`.
    Pipe,
    /// `A -> B`
    Arrow,
    /// `(x: A) -> B`, `[x: A] -> B`
    FunctionType,
    /// `∀ (x: A) => P`: the keyword, its parameters (as a lambda's) and the
    /// body.
    Forall,
    /// `∃ (x: A) => P`; the parameters are a lambda's too.
    Exists,
    /// `p ↔ q`
    Iff,
    /// `x (a, b) => e`
    Lambda,
    /// One parameter of a lambda, `∀` or `∃` with a written type:
    /// `(x y: A)`, `[t: Type]`. A bare name is a token, and a pattern
    /// (`(a, b)`, `((a, b): P)`) is its pattern's node.
    LambdaParam,
    /// `if c then a else b`, `if h: c then …`; an `else if` is an `If` in
    /// the else branch.
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
    /// `"a${x}b"`, `"""…${x}…"""`: the pieces of text, which are tokens,
    /// and the [`Interpolation`](NodeKind::Interpolation)s between them.
    Interpolated,
    /// `${x}` in a text: the `${`, the expression and the `}`.
    Interpolation,
    /// `handle e with | op x, k => …`
    Handle,
    /// `| return x => e` or `| op p, k => e`: one clause of a `handle` or
    /// `match reify`.
    HandlerClause,
    /// `match e, f with | …`
    Match,
    /// One matched expression, `h: e` or `e`.
    Scrutinee,
    /// `match | …`, `match some | …`, `matches | …`
    ClauseLambda,
    /// `match induct n with | …`
    Induct,
    /// `| eq1 x ih => e`: one case of a `match induct`.
    InductArm,
    /// `match reify e with | …`
    Reify,
    /// `calc a` and its steps.
    Calc,
    /// `_ = b := proof`
    CalcStep,
    /// `rewrite h then e`, `rewrite h at x then e`
    Rewrite,
    /// One rule of a `rewrite`.
    RewriteRule,
    /// `[r1, r2]`, the rules of `rewrite repeatedly`.
    RewriteRules,
    /// `arithmetic [h]`
    Omega,
    /// `algebra [h]`
    Ring,
    /// `cases then t`
    Cases,
    /// `byWalking [items] then t`
    Walk,

    // Patterns.
    /// `Cons x xs`: a constructor with arguments, in a `PatternParen` if bracketed
    PatternCtor,
    /// `(a, b)`
    PatternTuple,
    /// `[a, ..rest]`
    PatternList,
    /// `[n := p]`: a constructor's implicit field, by name.
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
    /// `()`: the pattern of an empty type.
    PatternAbsurd,
    /// `"--" ++ rest`: a text pattern's fixed start and the rest.
    PatternAppend,
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
    /// For a declaration that didn't lex, which has no tokens (`tokens` is
    /// empty, at the first token after it): the bytes it covers.
    pub(crate) raw: Option<Range<u32>>,
    /// For a definition that didn't parse (an `Error` root): whether the
    /// parser kept its signature, its header having parsed, rather than
    /// giving only its names as failed ([`Node::signature_kept`]).
    pub(crate) signature_kept: bool,
    /// Where the parser recovered from a syntax error in it, in the order
    /// met ([`Node::recoveries`]).
    pub(crate) recovered: Vec<Recovery>,
}

/// A recovery point of the parser (docs/proposals/syntax-error-recovery.md
/// §2.2): how it carried on past a syntax error in a declaration.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum RecoveryPoint {
    /// R1: an expression or a closing token was wanted where the line or
    /// the declaration ended. Nothing is skipped; the part is absent.
    RanOut,
    /// R6: nothing inside caught the error, so the rest of a definition's
    /// body is skipped, as an `Error` node.
    Body,
}

impl RecoveryPoint {
    /// The point's name in the design note: `R1`, `R6`.
    pub fn label(self) -> &'static str {
        match self {
            RecoveryPoint::RanOut => "R1",
            RecoveryPoint::Body => "R6",
        }
    }
}

/// A syntax error the parser recovered from: where it was reported, and
/// which point recovered.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Recovery {
    pub point: RecoveryPoint,
    pub at: Span,
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
    /// [`DeclMarks::raw`].
    raw: Option<Range<u32>>,
    /// [`DeclMarks::signature_kept`].
    signature_kept: bool,
    /// [`DeclMarks::recovered`].
    recovered: Vec<Recovery>,
    /// Why the builder couldn't nest the parser's marks, which is a parser
    /// bug: the tree is then the root alone ([`Node::misnested`]).
    misnested: Option<&'static str>,
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
    /// The spans of the `--|` comments, whose doc links the module lists.
    bars: Vec<Span>,
    /// How many declarations' marks didn't nest: a parser bug if not 0.
    misnested: usize,
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
    /// Those of them that didn't lex: an `Error` root over raw text.
    pub unlexed: usize,
    pub nodes: usize,
    /// Declarations whose marks didn't nest, a parser bug
    /// ([`Node::misnested`]).
    pub misnested: usize,
}

impl SyntaxFile {
    pub(crate) fn build(
        tokens: Vec<Token>,
        trivia: Vec<Trivia>,
        eof: Trivia,
        bars: Vec<Span>,
        groups: Vec<DeclMarks>,
    ) -> SyntaxFile {
        let file = SyntaxFile::build_allowing_misnested(tokens, trivia, eof, bars, groups);
        debug_assert_eq!(
            file.misnested, 0,
            "the parser recorded marks that don't nest (see `Node::misnested`)"
        );
        file
    }

    /// [`Self::build`] without its debug check that every declaration's
    /// marks nest, for the tests of what the compiler does when they don't.
    pub(crate) fn build_allowing_misnested(
        tokens: Vec<Token>,
        trivia: Vec<Trivia>,
        eof: Trivia,
        bars: Vec<Span>,
        groups: Vec<DeclMarks>,
    ) -> SyntaxFile {
        let mut nester = Nester::default();
        let decls: Vec<DeclTree> = groups.into_iter().map(|g| nester.build(g)).collect();
        let misnested = decls.iter().filter(|decl| decl.misnested.is_some()).count();
        SyntaxFile {
            tokens,
            trivia,
            eof,
            decls,
            bars,
            misnested,
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

    /// The spans of the `--|` comments, as the lexer records them.
    pub fn bars(&self) -> &[Span] {
        &self.bars
    }

    /// Each token's comments and blank lines: `trivia()[i]` is
    /// `tokens()[i]`'s.
    pub fn trivia(&self) -> &[Trivia] {
        &self.trivia
    }

    /// The comments and blank lines after the last token.
    pub fn eof(&self) -> &Trivia {
        &self.eof
    }

    /// The file's text, read back from the tree: each leaf in tree order,
    /// with the source text between it and the leaf before. `source` is the
    /// text the tree was parsed from; only the gaps between tokens are read
    /// from it besides the tokens themselves. A declaration that didn't lex
    /// is in such a gap, and [`Self::check_round_trip`] checks that the
    /// gap holds only it, comments and whitespace.
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
        let mut raws: Vec<Range<usize>> = self
            .decls
            .iter()
            .filter_map(|decl| decl.raw.as_ref())
            .map(|raw| raw.start as usize..raw.end as usize)
            .collect();
        raws.sort_by_key(|raw| raw.start);
        let mut raws = raws.as_slice();
        // The raw declarations that end by `to`, taken off the front.
        let mut raws_until = |to: usize| {
            let n = raws.partition_point(|raw| raw.end <= to);
            let (now, later) = raws.split_at(n);
            raws = later;
            now
        };
        let mut at = 0usize;
        for (i, token) in self.tokens.iter().enumerate() {
            let before = i
                .checked_sub(1)
                .and_then(|p| self.trivia[p].trailing.as_ref());
            let comments = before.into_iter().chain(&self.trivia[i].leading);
            let range = token.span.start as usize..token.span.end as usize;
            check_gap(source, at, range.start, comments, raws_until(range.start))
                .map_err(|e| format!("before token {i}: {e}"))?;
            at = range.end;
        }
        let last = self.trivia.last().and_then(|t| t.trailing.as_ref());
        check_gap(
            source,
            at,
            source.len(),
            last.into_iter().chain(&self.eof.leading),
            raws_until(source.len()),
        )
        .map_err(|e| format!("at the end: {e}"))?;
        if let Some(raw) = raws.first() {
            return Err(format!(
                "the declaration that didn't lex at byte {} is inside a token",
                raw.start
            ));
        }
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
            misnested: self.misnested,
            ..TreeStats::default()
        };
        for decl in &self.decls {
            if decl.nodes[0].kind == NodeKind::Error {
                stats.errors += 1;
            }
            if decl.raw.is_some() {
                stats.unlexed += 1;
            }
            stats.nodes += decl.nodes.len();
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
    if let Some(raw) = node.raw_text_range() {
        out.push_str(&format!(
            "{:indent$}{:?} (didn't lex)\n",
            "",
            source[raw].trim_end(),
            indent = (depth + 1) * 2
        ));
    }
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

/// Checks that `source[from..to]` is whitespace, `comments` and the
/// declarations that didn't lex (`raws`), each list in order.
fn check_gap<'c>(
    source: &str,
    from: usize,
    to: usize,
    comments: impl Iterator<Item = &'c Comment>,
    raws: &[Range<usize>],
) -> Result<(), String> {
    let blank = |s: &str| s.bytes().all(|b| matches!(b, b' ' | b'\n' | b'\r'));
    let mut at = from;
    let mut raws = raws.iter().peekable();
    // Steps over the raw declarations that start before `until`.
    let mut skip_raws = |at: &mut usize, until: usize| -> Result<(), String> {
        while let Some(raw) = raws.next_if(|raw| raw.start < until) {
            if raw.start < *at {
                return Err(format!(
                    "the declaration that didn't lex at byte {} overlaps a token or a comment",
                    raw.start
                ));
            }
            if !blank(&source[*at..raw.start]) {
                return Err(format!(
                    "text at byte {at} is neither a token nor a comment"
                ));
            }
            *at = raw.end;
        }
        Ok(())
    };
    for comment in comments {
        let (start, end) = (comment.span.start as usize, comment.span.end as usize);
        skip_raws(&mut at, start)?;
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
    skip_raws(&mut at, to)?;
    if !blank(&source[at..to]) {
        return Err(format!(
            "text at byte {at} is neither a token nor a comment"
        ));
    }
    Ok(())
}

/// The builder's working space, kept across a file's declarations so that
/// building allocates only the trees.
#[derive(Default)]
struct Nester {
    /// For each mark, how many nodes its subtree has, itself included.
    size: Vec<u32>,
    /// The forward pass's marks that have no parent yet, as indices.
    orphans: Vec<u32>,
    /// The backward pass's open nodes: where each starts, and where the
    /// next subtree placed under it ends.
    open: Vec<(u32, u32)>,
}

impl Nester {
    /// One declaration's tree, from its marks in finishing order
    /// (docs/proposals/parser-end-state.md §3, A′): a construct's mark comes
    /// after the marks of everything inside it, so ends never go back, and
    /// of two marks with the same range the later is the outer. Two linear
    /// passes, no sort: forward, each mark gathers the subtrees that start
    /// inside it and counts their nodes; backward, parents now come before
    /// their children and the last child first, so each subtree is placed
    /// ending where the one after it begins. Marks that break the order or
    /// cross give the root alone, and why ([`Node::misnested`]).
    fn build(&mut self, group: DeclMarks) -> DeclTree {
        let offset = group.tokens.start;
        let len = group.tokens.end - group.tokens.start;
        let mut marks = group.marks;
        let root = |subtree_end| NodeData {
            kind: group.root,
            start: group.tokens.start,
            end: group.tokens.end,
            subtree_end,
        };
        let (nodes, misnested) = match self.sizes(&mut marks, len) {
            Ok(()) => (self.place(&marks, offset, root), None),
            Err(why) => (vec![root(1)], Some(why)),
        };
        DeclTree {
            nodes,
            raw: group.raw,
            signature_kept: group.signature_kept,
            recovered: group.recovered,
            misnested,
        }
    }

    /// The forward pass: checks the order and the nesting, and fills
    /// `size`. Drops the empty marks, of constructs that read nothing (as
    /// after R1), which are no node.
    fn sizes(&mut self, marks: &mut Vec<Mark>, len: u32) -> Result<(), &'static str> {
        let mut last_end = 0;
        for mark in marks.iter() {
            if mark.end < last_end || mark.start > mark.end || mark.end > len {
                return Err("a mark out of order");
            }
            last_end = mark.end;
        }
        marks.retain(|m| m.start < m.end);
        self.size.clear();
        self.size.resize(marks.len(), 1);
        self.orphans.clear();
        for (i, mark) in marks.iter().enumerate() {
            while let Some(&top) = self.orphans.last() {
                let inner = marks[top as usize];
                if inner.start >= mark.start {
                    self.size[i] += self.size[top as usize];
                    self.orphans.pop();
                } else if inner.end > mark.start {
                    return Err("two marks cross");
                } else {
                    break;
                }
            }
            self.orphans.push(i as u32);
        }
        Ok(())
    }

    /// The backward pass: the nodes in preorder, the root first.
    fn place(
        &mut self,
        marks: &[Mark],
        offset: u32,
        root: impl Fn(u32) -> NodeData,
    ) -> Vec<NodeData> {
        let total = marks.len() as u32 + 1;
        let mut nodes = vec![root(total); total as usize];
        self.open.clear();
        self.open.push((0, total));
        for (i, mark) in marks.iter().enumerate().rev() {
            while self.open.len() > 1 && self.open[self.open.len() - 1].0 > mark.start {
                self.open.pop();
            }
            let parent = self.open.len() - 1;
            let end = self.open[parent].1;
            let at = end - self.size[i];
            self.open[parent].1 = at;
            nodes[at as usize] = NodeData {
                kind: mark.kind,
                start: offset + mark.start,
                end: offset + mark.end,
                subtree_end: end,
            };
            self.open.push((mark.start, end));
        }
        nodes
    }
}

impl<'f> Node<'f> {
    fn data(&self) -> &'f NodeData {
        &self.file.decls[self.decl as usize].nodes[self.index as usize]
    }

    /// The tree it belongs to.
    pub fn file(&self) -> &'f SyntaxFile {
        self.file
    }

    pub fn kind(&self) -> NodeKind {
        self.data().kind
    }

    /// The tokens it covers, as indices into [`SyntaxFile::tokens`]. Empty
    /// for a declaration that didn't lex ([`Self::raw_text_range`]).
    pub fn token_range(&self) -> Range<usize> {
        let data = self.data();
        data.start as usize..data.end as usize
    }

    /// For the root of a declaration that didn't lex: the bytes of its
    /// text, which no token holds. Such a root is an `Error` node with no
    /// children, whose empty token range is at the first token after it.
    pub fn raw_text_range(&self) -> Option<Range<usize>> {
        if self.index != 0 {
            return None;
        }
        let raw = self.file.decls[self.decl as usize].raw.as_ref()?;
        Some(raw.start as usize..raw.end as usize)
    }

    /// For the root of a definition that didn't parse: whether the parser
    /// kept its signature, because its header parsed and only what came
    /// after failed (`Decl::Signature::syntax_error`). Its `Error` root then
    /// holds the header's nodes. False for any other node.
    pub fn signature_kept(&self) -> bool {
        self.index == 0 && self.file.decls[self.decl as usize].signature_kept
    }

    /// The root of the declaration it belongs to.
    pub fn root(&self) -> Node<'f> {
        Node {
            file: self.file,
            decl: self.decl,
            index: 0,
        }
    }

    /// For the root of a declaration: the syntax errors the parser
    /// recovered from in it, in the order met. A declaration with any is
    /// failed whatever it checks to, and never gets a kernel term
    /// (docs/proposals/syntax-error-recovery.md §4.1). Empty for any other
    /// node.
    pub fn recoveries(&self) -> &'f [Recovery] {
        if self.index != 0 {
            return &[];
        }
        &self.file.decls[self.decl as usize].recovered
    }

    /// For a declaration's root: why the builder couldn't nest the
    /// parser's marks for it, if it couldn't (two cross, or one is out of
    /// order). Only through a parser bug, and then the tree is the root
    /// alone with every token flat under it, which isn't the parse, so the
    /// lowering refuses the declaration. `None` for any other node.
    pub fn misnested(&self) -> Option<&'static str> {
        if self.index == 0 {
            self.file.decls[self.decl as usize].misnested
        } else {
            None
        }
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

    /// Its bytes in the source.
    pub fn text_range(&self) -> Range<usize> {
        let span = self.token().span;
        span.start as usize..span.end as usize
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::SourceMap;
    use crate::parser::parse_module_and_tree;

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
        crate::parse_tree(file, text, crate::DEFAULT_STACK)
    }

    #[test]
    fn every_sample_reads_back_as_written() {
        for path in SAMPLES {
            let text = sample(path);
            let stats = tree(&text)
                .check_round_trip(&text)
                .unwrap_or_else(|e| panic!("{path}: {e}"));
            assert_eq!((stats.errors, stats.misnested), (0, 0), "{path}: {stats:?}");
        }
    }

    #[test]
    fn every_span_of_the_compilers_tree_is_a_node() {
        for path in SAMPLES {
            let text = sample(path);
            let file = SourceMap::new().next_id();
            let (module, _, tree) = parse_module_and_tree(file, &text, crate::DEFAULT_STACK);
            let check = tree.check_spans(&module);
            let misses: Vec<_> = check
                .misses
                .iter()
                .map(|miss| (miss.what, &text[miss.span.range()]))
                .collect();
            assert!(misses.is_empty(), "{path}: {misses:?}");
            assert!(check.checked > 0, "{path}");
        }
    }

    /// Each kind of span the parser makes up, in one file: all known, and
    /// every other span a node.
    #[test]
    fn the_spans_the_parser_makes_up_are_known() {
        let text = r#"@[js.tag "type"]
type Shape =
  | @[js.name "CIRCLE"] Circle (radius: Nat)

def f (x: Nat) (y: Nat): Bool :=
  let (a, b): (Nat, Nat) := (x, y)
  let s := "${a}"
  (p => p) (0 < f a b <= y) && (b > a + 1) && (x ∉ [a, b, y]) && ((a = a) <-> True)

def g: Option (Nat, Nat) -> Option Nat := match some
  | Some (Some x, y) => (x, y, x) |> (match some | (z, _, _) => z) |> .head

def h (xs: List Nat): Nat := match xs with
  | [a, b, ..r] => a
  | _ => 0

theorem t ∀ (n: Nat): ∃ (m k: Nat) => m = n + k := xs |> .map h
"#;
        let file = SourceMap::new().next_id();
        let (module, errors, tree) = parse_module_and_tree(file, text, crate::DEFAULT_STACK);
        assert!(errors.is_empty(), "{errors:?}");
        let check = tree.check_spans(&module);
        let misses: Vec<_> = check
            .misses
            .iter()
            .map(|miss| (miss.what, &text[miss.span.range()]))
            .collect();
        assert!(misses.is_empty(), "{misses:?}");
        let mut kinds: Vec<Synthetic> = check.synthetic.keys().copied().collect();
        kinds.sort();
        use Synthetic::*;
        assert_eq!(
            kinds,
            [
                Empty,
                PartialApp,
                Nested,
                BlockRest,
                Generated,
                Added,
                Attributes,
                Exists,
                Chain,
                Section,
                PatternMatch,
                Header,
            ]
        );
    }

    /// A span that is no node is found, even with the brackets around it
    /// added back.
    #[test]
    fn a_span_that_is_no_node_is_reported() {
        use crate::ast::{Decl, Expr, Name};
        let text = "def x: Nat := f (g a) b\n";
        let file = SourceMap::new().next_id();
        let (mut module, _, tree) = parse_module_and_tree(file, text, crate::DEFAULT_STACK);
        assert!(tree.check_spans(&module).misses.is_empty());
        let at = |s: &str| text.find(s).unwrap() as u32;
        // `f (g`, and `(g a` (which is `(g a)` but for its bracket).
        for (start, end) in [(at("f ("), at("g a") + 1), (at("(g"), at("a)") + 1)] {
            let Some(Decl::Equation { rhs: Some(rhs), .. }) = module.decls.last_mut() else {
                panic!("an equation")
            };
            *rhs = Expr::Var(Name {
                text: "f".into(),
                span: crate::Span::new(file, start, end),
            });
            let found = tree.check_spans(&module).misses.len();
            assert_eq!(found, usize::from(start == at("f (")), "{start}..{end}");
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

theorem t: 1 = 1 := byComputing
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
    Nat
    )
  Param
    [
    a
    :
    Type
    ]
  Param
    (
    x
    :
    a
    Default
      :=
      d
    )
  ResultType
    :
    Nat
  Arms
    Arm
      |
      0
      =>
      1
    Arm
      |
      k
      Guard
        if
        Binary
          k
          >
          2
      =>
      Match
        match
        Scrutinee
          k
        with
        Arm
          |
          j
          =>
          j
Theorem
  theorem
  t
  ResultType
    :
    Binary
      1
      =
      1
  Body
    :=
    byComputing
"
        );
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
        m
        :=
        Binary
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
          Nat
          )
        ResultType
          :
          Nat
        Body
          :=
          k
      App
        g
        m
"
        );
    }

    #[test]
    fn a_declaration_that_does_not_parse_is_an_error_node() {
        let text = "def f (n Nat): Nat := 1\n\n-- trailing\ndef g: Nat := 1\n";
        let tree = tree(text);
        let stats = tree.check_round_trip(text).unwrap();
        assert_eq!((stats.decls, stats.errors), (2, 1));
        let kinds: Vec<NodeKind> = tree.decls().map(|d| d.kind()).collect();
        assert_eq!(kinds, [NodeKind::Error, NodeKind::Def]);
    }

    /// A definition whose body broke keeps its kind and its header's nodes,
    /// and the rest of its body is an `Error` node in its `Body` (R6 of
    /// docs/proposals/syntax-error-recovery.md).
    #[test]
    fn a_broken_body_keeps_its_headers_nodes() {
        let text = "def f (n: Nat): Nat := (n +\n";
        let tree = tree(text);
        let stats = tree.check_round_trip(text).unwrap();
        assert_eq!((stats.errors, stats.misnested), (0, 0), "{stats:?}");
        let root = tree.decls().next().unwrap();
        assert_eq!(
            compact(root, text),
            "Def[def f Param[( n : Nat )] ResultType[: Nat] Body[:= Error[( Binary[n +]]]]"
        );
    }

    /// A bracket left open at a line end is an `Error` node, not a `Paren`
    /// or a `List`, and the rest of the declaration still parses: the block's
    /// next statement, the match's next arm (SW-3289).
    #[test]
    fn a_bracket_left_open_stays_an_error_node() {
        let text = "def f (x: Nat): Nat :=\n  g (\n  let y := 1\n  y\n";
        let parsed = tree(text);
        let stats = parsed.check_round_trip(text).unwrap();
        assert_eq!((stats.errors, stats.misnested), (0, 0), "{stats:?}");
        let root = parsed.decls().next().unwrap();
        let shape = compact(root, text);
        assert!(shape.contains("App[g Error[(]]"), "{shape}");
        assert!(shape.contains("Let["), "{shape}");

        let text =
            "def h (x: List Nat): Nat := match x with\n  | a if a == [\n    => 1\n  | _ => 2\n";
        let parsed = tree(text);
        let stats = parsed.check_round_trip(text).unwrap();
        assert_eq!((stats.errors, stats.misnested), (0, 0), "{stats:?}");
        let shape = compact(parsed.decls().next().unwrap(), text);
        assert!(shape.contains("Guard["), "{shape}");
        assert!(shape.contains("Error[["), "{shape}");
        assert_eq!(
            shape.matches("Alt").count() + shape.matches("Arm[").count(),
            2,
            "{shape}"
        );
    }

    /// An arm that breaks after one that parsed: the arms are an `Error`
    /// node from the first `|`, and the arm that finished nests in it.
    #[test]
    fn a_broken_arm_keeps_the_arms_before_it() {
        let text = "def f (n: Nat): Nat\n  | 0 => 1\n  | ) => 2\n";
        let tree = tree(text);
        let root = tree.decls().next().unwrap();
        assert_eq!(
            compact(root, text),
            "Def[def f Param[( n : Nat )] ResultType[: Nat] Error[Arm[| 0 => 1] | ) => 2]]"
        );
    }

    /// The tree of tokens `a b c d` from these marks, in the order given,
    /// as [`compact`] writes it, and why they didn't nest if they didn't.
    fn nested(marks: &[(NodeKind, u32, u32)]) -> (String, Option<&'static str>) {
        let file = SourceMap::new().next_id();
        let text = "a b c d\n";
        let lexed = crate::lexer::lex_with_trivia(file, text).unwrap();
        let marks = marks
            .iter()
            .map(|&(kind, start, end)| Mark { kind, start, end })
            .collect();
        let group = DeclMarks {
            tokens: 0..lexed.tokens.len() as u32,
            root: NodeKind::Expression,
            marks,
            raw: None,
            signature_kept: false,
            recovered: Vec::new(),
        };
        let tree = SyntaxFile::build_allowing_misnested(
            lexed.tokens,
            lexed.trivia,
            lexed.eof,
            lexed.bars,
            vec![group],
        );
        let root = tree.decls().next().unwrap();
        (compact(root, text), root.misnested())
    }

    /// The builder nests marks given in finishing order, the later of two
    /// with the same range outside, and leaves out empty ones.
    #[test]
    fn marks_in_finishing_order_nest() {
        use NodeKind::{App, Binary, Paren};
        assert_eq!(
            nested(&[
                (Paren, 1, 2),
                (App, 0, 2),
                (Paren, 2, 2),
                (Binary, 2, 4),
                (App, 0, 4)
            ]),
            (
                "Expression[App[App[a Paren[b]] Binary[c d]]]".to_string(),
                None
            )
        );
        assert_eq!(
            nested(&[(Paren, 0, 4), (Binary, 0, 4)]),
            ("Expression[Binary[Paren[a b c d]]]".to_string(), None)
        );
    }

    /// Marks out of finishing order, or two that cross, are a parser bug:
    /// the tree is the root alone, with why.
    #[test]
    fn marks_that_do_not_nest_are_refused() {
        use NodeKind::{App, Binary};
        let alone = "Expression[a b c d]".to_string();
        assert_eq!(
            nested(&[(App, 0, 3), (Binary, 1, 2)]),
            (alone.clone(), Some("a mark out of order"))
        );
        assert_eq!(
            nested(&[(App, 0, 2), (Binary, 1, 3)]),
            (alone.clone(), Some("two marks cross"))
        );
        assert_eq!(nested(&[(App, 0, 5)]), (alone, Some("a mark out of order")));
    }

    /// A header that breaks fails the declaration whole, as before: its
    /// root is `Error`, holding what finished before the error.
    #[test]
    fn a_broken_header_is_an_error_root() {
        let text = "def f (n: Nat): Nat + := n\n";
        let tree = tree(text);
        let root = tree.decls().next().unwrap();
        assert_eq!(root.kind(), NodeKind::Error);
        assert!(root.recoveries().is_empty());
    }

    /// A declaration that doesn't lex is an `Error` root over its raw
    /// text, in its place among the others, and the file still reads back.
    #[test]
    fn a_declaration_that_does_not_lex_is_raw_text() {
        let text = "\
def f: Nat := 1

-- About g.
def g: Text := \"no end
  more

-- About h.
def h: Nat := 2
";
        let tree = tree(text);
        let stats = tree.check_round_trip(text).unwrap();
        assert_eq!(
            (stats.decls, stats.errors, stats.unlexed, stats.misnested),
            (3, 1, 1, 0),
            "{stats:?}"
        );
        let kinds: Vec<NodeKind> = tree.decls().map(|d| d.kind()).collect();
        assert_eq!(kinds, [NodeKind::Def, NodeKind::Error, NodeKind::Def]);
        let raw = tree.decls().nth(1).unwrap();
        assert_eq!(raw.children().count(), 0);
        assert_eq!(
            &text[raw.raw_text_range().unwrap()],
            "def g: Text := \"no end\n  more\n\n"
        );
        assert_eq!(raw.token_range(), 6..6);
        assert_eq!(tree.decls().nth(2).unwrap().raw_text_range(), None);
        assert!(
            tree.dump(text)
                .contains("Error\n  \"def g: Text := \\\"no end\\n  more\" (didn't lex)\n")
        );
        let file = SourceMap::new().next_id();
        let (module, errors, tree) = parse_module_and_tree(file, text, crate::DEFAULT_STACK);
        assert_eq!(errors.len(), 1);
        assert!(tree.check_spans(&module).misses.is_empty());
    }

    /// At the end of the file, and as the whole file.
    #[test]
    fn a_last_or_only_declaration_that_does_not_lex_reads_back() {
        for text in [
            "def f: Nat := 1\ndef g: Text := \"no end\n",
            "def g: Text := \"no end",
            "def f: Nat := 1\n-- note\ndef g := `\n-- after\n",
        ] {
            let tree = tree(text);
            let stats = tree
                .check_round_trip(text)
                .unwrap_or_else(|e| panic!("{text:?}: {e}"));
            assert_eq!(stats.unlexed, 1, "{text:?}");
            assert_eq!(tree.decls().last().unwrap().kind(), NodeKind::Error);
        }
    }

    /// A node on one line, `Kind[child child]`, a token as its text.
    fn compact(node: Node<'_>, source: &str) -> String {
        let children: Vec<String> = node
            .children()
            .map(|child| match child {
                Element::Node(n) => compact(n, source),
                Element::Leaf(leaf) => source[leaf.text_range()].to_string(),
            })
            .collect();
        format!("{:?}[{}]", node.kind(), children.join(" "))
    }

    /// What follows `:=` in each declaration of `text`, as [`compact`]
    /// writes it.
    fn bodies(text: &str) -> Vec<String> {
        let tree = tree(text);
        let stats = tree.check_round_trip(text).unwrap();
        assert_eq!((stats.errors, stats.misnested), (0, 0), "{stats:?}");
        tree.decls()
            .map(|decl| {
                let body = decl
                    .children()
                    .find_map(|child| match child {
                        Element::Node(n) if n.kind() == NodeKind::Body => Some(n),
                        _ => None,
                    })
                    .expect("a body");
                let mut parts: Vec<String> = body
                    .children()
                    .map(|child| match child {
                        Element::Node(n) => compact(n, text),
                        Element::Leaf(leaf) => text[leaf.text_range()].to_string(),
                    })
                    .collect();
                assert_eq!(parts.remove(0), ":=");
                parts.join(" ")
            })
            .collect()
    }

    /// Checks each expression's tree: `cases` pairs an expression with
    /// its tree, as [`compact`] writes it.
    fn check_expressions(cases: &[(&str, &str)]) {
        let text: String = cases
            .iter()
            .enumerate()
            .map(|(i, (expr, _))| format!("def x{i}: T := {expr}\n\n"))
            .collect();
        let got = bodies(&text);
        for ((expr, want), got) in cases.iter().zip(&got) {
            assert_eq!(got, want, "{expr}");
        }
    }

    #[test]
    fn operators_are_marked_as_written() {
        check_expressions(&[
            ("a + b * c - d", "Binary[Binary[a + Binary[b * c]] - d]"),
            ("a ++ b ++ c", "Binary[a ++ Binary[b ++ c]]"),
            (
                "a || b && c || d",
                "Binary[a || Binary[Binary[b && c] || d]]",
            ),
            ("p <-> q && r", "Iff[p <-> Binary[q && r]]"),
            ("0 <= x < y", "Chain[0 <= x < y]"),
            (
                "a = if c then x else y",
                "Binary[a = If[if c then x else y]]",
            ),
            (
                "x !in xs && y in 0 ..< n",
                "Binary[Membership[x !in xs] && Membership[y in Range[0 ..< n]]]",
            ),
            ("-x + !b", "Binary[Prefix[- x] + Prefix[! b]]"),
            ("-1.abs", "FieldAccess[Prefix[- 1] . abs]"),
            (
                "xs |> List.map f |> .sum",
                "Pipe[Pipe[xs |> App[List.map f]] |> Section[FieldAccess[. sum]]]",
            ),
            ("Nat -> Nat", "Arrow[Nat -> Nat]"),
            ("a; b", "Seq[a ; b]"),
            (
                "(let x := 1; x + 1)",
                "Paren[( LetExpr[Let[let x := 1] ; Binary[x + 1]] )]",
            ),
        ]);
    }

    /// An operator looser than `&&` and `||` takes the whole chain before
    /// it as its left operand, however many operands the chain has and
    /// however they group (SW-3243: with three or more, the `->` lost its
    /// node and the chain was read without it).
    #[test]
    fn operators_after_logic_chains_take_the_whole_chain() {
        check_expressions(&[
            ("a && b -> q", "Arrow[Binary[a && b] -> q]"),
            (
                "a && b && c -> q",
                "Arrow[Binary[a && Binary[b && c]] -> q]",
            ),
            (
                "a || b || c -> q",
                "Arrow[Binary[a || Binary[b || c]] -> q]",
            ),
            (
                "a || b && c -> q",
                "Arrow[Binary[a || Binary[b && c]] -> q]",
            ),
            (
                "a && b || c -> q",
                "Arrow[Binary[Binary[a && b] || c] -> q]",
            ),
            (
                "a && b || c && d -> q",
                "Arrow[Binary[Binary[a && b] || Binary[c && d]] -> q]",
            ),
            (
                "a || b && c || d -> q",
                "Arrow[Binary[a || Binary[Binary[b && c] || d]] -> q]",
            ),
            (
                "a && b && c && d -> q",
                "Arrow[Binary[a && Binary[b && Binary[c && d]]] -> q]",
            ),
            ("a ∧ b ∧ c → q", "Arrow[Binary[a ∧ Binary[b ∧ c]] → q]"),
            // Operands with nodes of their own, finished before the chain's.
            (
                "f a && b || g c && h d",
                "Binary[Binary[App[f a] && b] || Binary[App[g c] && App[h d]]]",
            ),
            (
                "a && b && c <-> q",
                "Iff[Binary[a && Binary[b && c]] <-> q]",
            ),
            (
                "a || b && c <-> q -> r",
                "Arrow[Iff[Binary[a || Binary[b && c]] <-> q] -> r]",
            ),
            (
                "q -> a && b && c -> r",
                "Arrow[q -> Arrow[Binary[a && Binary[b && c]] -> r]]",
            ),
            (
                "(a && b && c; e)",
                "Paren[( Seq[Binary[a && Binary[b && c]] ; e] )]",
            ),
            (
                "(a || b || c <-> q; e)",
                "Paren[( Seq[Iff[Binary[a || Binary[b || c]] <-> q] ; e] )]",
            ),
            (
                "x => a && b && c -> q",
                "Lambda[x => Arrow[Binary[a && Binary[b && c]] -> q]]",
            ),
            (
                "(.f && b && c)",
                "Paren[( Section[Binary[FieldAccess[. f] && Binary[b && c]]] )]",
            ),
        ]);
    }

    #[test]
    fn applications_and_brackets_are_marked_as_written() {
        check_expressions(&[
            (
                "f a (g b) p.q.r x.f()",
                "App[f a Paren[( App[g b] )] FieldAccess[FieldAccess[p . q] . r] \
                 App[FieldAccess[x . f] Unit[( )]]]",
            ),
            (
                "f (x := 1) [y := 2] ()",
                "App[f NamedArg[( x := 1 )] NamedArg[[ y := 2 ]] Unit[( )]]",
            ),
            (
                "((a, b, c), (x : Nat))",
                "Tuple[( Tuple[( a , b , c )] , Annotation[( x : Nat )] )]",
            ),
            ("[1, ..xs]", "List[[ 1 , Spread[.. xs] ]]"),
            (
                "\"a${x + 1}b${y}\"",
                "Interpolated[\"a Interpolation[${ Binary[x + 1] }] b Interpolation[${ y }] \"]",
            ),
            ("include \"x\"", "Include[include \"x\"]"),
            ("Type 1", "Universe[Type 1]"),
        ]);
    }

    #[test]
    fn records_are_marked_as_written() {
        check_expressions(&[
            ("{ r | x = 1, y }", "Record[{ r | RecordField[x = 1] , y }]"),
            (
                "C { x = 1 }",
                "CtorFields[C Record[{ RecordField[x = 1] }]]",
            ),
            (
                "f C { s | x = 2 }",
                "App[f CtorFields[C Record[{ s | RecordField[x = 2] }]]]",
            ),
        ]);
    }

    /// A section is the function it stands for: `.f a` takes its
    /// arguments, and a section starting an expression takes all of it.
    #[test]
    fn sections_are_marked_as_written() {
        check_expressions(&[
            (
                "xs.map .name",
                "App[FieldAccess[xs . map] Section[FieldAccess[. name]]]",
            ),
            ("(.f a)", "Paren[( Section[App[FieldAccess[. f] a]] )]"),
            (
                "(.f a + 1)",
                "Paren[( Section[Binary[App[FieldAccess[. f] a] + 1]] )]",
            ),
            (
                "xs |> .length + 1",
                "Pipe[xs |> Section[Binary[FieldAccess[. length] + 1]]]",
            ),
            (
                "f (+ 1) (k +) (&&)",
                "App[f OperatorSection[( + 1 )] OperatorSection[( k + )] OperatorSection[( && )]]",
            ),
            ("(|| a && b)", "OperatorSection[( || Binary[a && b] )]"),
            (
                "(|| a && b && c)",
                "OperatorSection[( || Binary[a && Binary[b && c]] )]",
            ),
            // A section inside a section's argument is its own.
            (
                "xs |> .flatMap (i => i |> .map f)",
                "Pipe[xs |> Section[App[FieldAccess[. flatMap] Paren[( Lambda[i => \
                 Pipe[i |> Section[App[FieldAccess[. map] f]]]] )]]]]",
            ),
            // Up to a `->`, which a section doesn't take.
            (
                "(.f a + 1 -> T)",
                "Paren[( Arrow[Section[Binary[App[FieldAccess[. f] a] + 1]] -> T] )]",
            ),
            ("(.f; b)", "Paren[( Seq[Section[FieldAccess[. f]] ; b] )]"),
        ]);
    }

    #[test]
    fn lambdas_and_quantifiers_are_marked_as_written() {
        check_expressions(&[
            ("x => x + 1", "Lambda[x => Binary[x + 1]]"),
            (
                "x (a, b) (y: A) [t: Type] => e",
                "Lambda[x PatternTuple[( a , b )] LambdaParam[( y : A )] \
                 LambdaParam[[ t : Type ]] => e]",
            ),
            (
                "forall (n: Nat) k => n + k = k",
                "Forall[forall LambdaParam[( n : Nat )] k => Binary[Binary[n + k] = k]]",
            ),
            (
                "exists (n: Nat) => n = 1",
                "Exists[exists LambdaParam[( n : Nat )] => Binary[n = 1]]",
            ),
            (
                "p && forall n => q n",
                "Binary[p && Forall[forall n => App[q n]]]",
            ),
            (
                "(n: Nat) -> [a: Type] -> Vec a n",
                "FunctionType[Binder[( n : Nat )] -> FunctionType[Binder[[ a : Type ]] -> \
                 App[Vec a n]]]",
            ),
        ]);
    }

    /// Checks each pattern's tree, written as the only arm of a `match`.
    fn check_patterns(cases: &[(&str, &str)]) {
        let text: String = cases
            .iter()
            .enumerate()
            .map(|(i, (pattern, _))| format!("def x{i}: T := match v with\n  | {pattern} => 0\n\n"))
            .collect();
        for ((pattern, want), got) in cases.iter().zip(&bodies(&text)) {
            let got = got
                .strip_prefix("Match[match Scrutinee[v] with Arm[| ")
                .and_then(|rest| rest.strip_suffix(" => 0]]"))
                .unwrap_or(got);
            assert_eq!(got, *want, "{pattern}");
        }
    }

    #[test]
    fn patterns_are_marked_as_written() {
        check_patterns(&[
            ("x", "x"),
            ("Some", "Some"),
            ("Some x", "PatternCtor[Some x]"),
            (
                "Pair (Some x) _",
                "PatternCtor[Pair PatternParen[( PatternCtor[Some x] )] _]",
            ),
            ("(a, b)", "PatternTuple[( a , b )]"),
            (
                "(a, Some b, c)",
                "PatternTuple[( a , PatternCtor[Some b] , c )]",
            ),
            ("[a, ..rest]", "PatternList[[ a , .. rest ]]"),
            ("[]", "PatternList[[ ]]"),
            (
                "{ x, y = Some z }",
                "PatternRecord[{ x , y = PatternCtor[Some z] }]",
            ),
            ("Point { x, .. }", "PatternCtorFields[Point { x , .. }]"),
            (
                "Some [n := k]",
                "PatternCtor[Some PatternNamed[[ n := k ]]]",
            ),
            ("Some -1", "PatternCtor[Some PatternNegative[- 1]]"),
            ("(-1)", "PatternParen[( PatternNegative[- 1] )]"),
            ("(-1, 2)", "PatternTuple[( PatternNegative[- 1] , 2 )]"),
            ("1 | 2 | 3", "PatternOr[1 | 2 | 3]"),
            (
                "(None | Some _)",
                "PatternParen[( PatternOr[None | PatternCtor[Some _]] )]",
            ),
            ("()", "PatternAbsurd[( )]"),
        ]);
    }

    #[test]
    fn text_prefix_patterns_are_marked_as_written() {
        check_patterns(&[
            ("\"--\" ++ rest", "PatternAppend[\"--\" ++ rest]"),
            (
                "\"a\" ++ \"b\" ++ _",
                "PatternAppend[\"a\" ++ PatternAppend[\"b\" ++ _]]",
            ),
            (
                "(\"set \" ++ x, n)",
                "PatternTuple[( PatternAppend[\"set \" ++ x] , n )]",
            ),
            (
                "Some (\"a\" ++ r)",
                "PatternCtor[Some PatternParen[( PatternAppend[\"a\" ++ r] )]]",
            ),
            (
                "\"a\" ++ _ | \"b\" ++ _",
                "PatternOr[PatternAppend[\"a\" ++ _] | PatternAppend[\"b\" ++ _]]",
            ),
            (
                "\"->\" ++ [c, ..cs]",
                "PatternAppend[\"->\" ++ PatternList[[ c , .. cs ]]]",
            ),
        ]);
    }

    #[test]
    fn let_and_lambda_patterns_are_marked_as_written() {
        check_expressions(&[
            (
                "(let (a, b) := p; a)",
                "Paren[( LetExpr[Let[let PatternTuple[( a , b )] := p] ; a] )]",
            ),
            (
                "((a, b): P) => a",
                "Lambda[PatternTyped[( PatternTuple[( a , b )] : P )] => a]",
            ),
        ]);
    }

    #[test]
    fn rows_in_types_are_marked_as_written() {
        check_expressions(&[(
            "(f: () -> {IO, State s} Nat) -> {Fail} Nat",
            "FunctionType[Binder[( f : Arrow[Unit[( )] -> Effect[Row[{ IO , App[State s] }] Nat]] )] \
             -> Effect[Row[{ Fail }] Nat]]",
        )]);
    }

    #[test]
    fn ifs_are_marked_as_written() {
        check_expressions(&[
            ("if c then a else b", "If[if c then a else b]"),
            (
                "if h: x < y then a else if d then b else c",
                "If[if h : Binary[x < y] then a else If[if d then b else c]]",
            ),
        ]);
    }

    #[test]
    fn handlers_inductions_and_reifications_are_marked_as_written() {
        check_expressions(&[
            (
                "handle f x with | return v => v | get u, k => k u",
                "Handle[handle App[f x] with HandlerClause[| return v => v] \
                 HandlerClause[| get u , k => App[k u]]]",
            ),
            (
                "match reify t with | return v => v",
                "Reify[match reify t with HandlerClause[| return v => v]]",
            ),
            (
                "match induct (f a) with | eq1 x ih => x | eq2 => y",
                "Induct[match induct Paren[( App[f a] )] with \
                 InductArm[| eq1 x ih => x] InductArm[| eq2 => y]]",
            ),
        ]);
    }

    #[test]
    fn proof_constructs_are_marked_as_written() {
        check_expressions(&[
            (
                "calc a + 0\n  _ = a := h\n  _ <= b",
                "Calc[calc Binary[a + 0] CalcStep[_ = a := h] CalcStep[_ <= b]]",
            ),
            (
                "rewrite <- h, g x at y then t",
                "Rewrite[rewrite RewriteRule[< - h] , RewriteRule[App[g x]] at y then t]",
            ),
            (
                "arithmetic [h, f x]",
                "Omega[arithmetic List[[ h , App[f x] ]]]",
            ),
            ("algebra [h]", "Ring[algebra List[[ h ]]]"),
            ("cases then t", "Cases[cases then t]"),
            (
                "arithmetic [h] + 1",
                "Binary[Omega[arithmetic List[[ h ]]] + 1]",
            ),
        ]);
    }
}
