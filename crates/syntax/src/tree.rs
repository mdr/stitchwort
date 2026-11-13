//! The lossless syntax tree: every token of a file, with its comments and
//! blank lines, grouped into nodes that say which construct they are.
//! Reading its leaves left to right, each with the text between it and the
//! previous one, gives back the file byte for byte.
//!
//! It is step 1 of docs/proposals/syntax-tree-architecture.md (architecture
//! A2, D3562), and stage 1 of docs/proposals/formatter-architecture.md: it
//! is built *beside* the compiler's tree ([`crate::ast`]) by the same parse.
//! Later the compiler's tree is lowered from it and the parser builds
//! nothing else (steps 3 and 4). The formatter, the editor's shape features
//! (outline, folding, selection) and the quick fixes and sweeps are its
//! readers (formatter-architecture.md §4).
//!
//! Step 1 is finished: every construct is marked, and its gates hold over
//! the repo (std, `aoc/src`, `games`, `examples`): every file reads back as
//! written, no mark is dropped, every span of the compiler's tree is a node
//! ([`SyntaxFile::check_spans`]), the compiler's tree and its hashes are
//! unchanged, and parsing without marks costs what it did. The whole-repo
//! gate is one command, for a rolling check:
//!
//! ```text
//! stitchwort dev tree --spans crates/elab/src/std aoc/src games examples
//! ```
//!
//! which exits 1 if any file doesn't read back, a mark is dropped, or a span
//! is no node, and prints each. (`examples` has files that don't lex or
//! parse on purpose; they are counted, not failures.) `--time N
//! --parse-only` times parsing without marks alone, so that an instruction
//! count of the process measures that and nothing else.
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
//! A construct the parser forgot to mark would leave its tokens flat in its
//! parent; the span-containment check ([`SyntaxFile::check_spans`]) is what
//! finds one, since the compiler's tree has a span for it that no node has.
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
//! An operator only learns it has a left operand once the operand is read:
//! `a` in `a + b`. Rather than every function the operand passes through
//! keeping its start (each such local grows the frames nested expressions
//! pile up), the operator reads it from the marks: every operand of more
//! than one token is marked, and is marked last, so the last mark ending at
//! the operator is the whole operand; if none does, the operand is one
//! token. The operator then holds that start on a small stack of open
//! constructs, beside the marks, until its right operand is read. The
//! span-containment check holds this up: an operand left unmarked would
//! start its operator's node in the wrong place, and the compiler's span
//! for the operator's expression would be no node.
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

mod spans;
pub use spans::{SpanCheck, SpanMiss, Synthetic};

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
    /// `"a${x}b"`, `"""…${x}…"""`: the pieces of text, which are tokens
    /// holding the `${` and `}` around each interpolated expression, and the
    /// expressions.
    Interpolated,
    /// `${x}` in a text. Not used yet: the `${` and `}` are inside the text
    /// pieces' tokens (SW-3171).
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
    for &(_, mark) in &marks {
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
                parse_module_and_tree(file, &text, crate::DEFAULT_STACK).expect("it lexes");
            assert_eq!(format!("{module:?}"), format!("{marked:?}"), "{path}");
            assert_eq!(
                format!("{errors:?}"),
                format!("{marked_errors:?}"),
                "{path}"
            );
        }
    }

    #[test]
    fn every_span_of_the_compilers_tree_is_a_node() {
        for path in SAMPLES {
            let text = sample(path);
            let file = SourceMap::new().next_id();
            let (module, _, tree) =
                parse_module_and_tree(file, &text, crate::DEFAULT_STACK).expect("it lexes");
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
        let (module, errors, tree) =
            parse_module_and_tree(file, text, crate::DEFAULT_STACK).expect("it lexes");
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
                OperatorHead,
                Generated,
                Added,
                Attributes,
                Flipped,
                Exists,
                Chain,
                Section,
                Interpolation,
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
        let (mut module, _, tree) =
            parse_module_and_tree(file, text, crate::DEFAULT_STACK).expect("it lexes");
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
    rfl
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
        let text = "def f (n: Nat): Nat := (\n\n-- trailing\ndef g: Nat := 1\n";
        let tree = tree(text);
        let stats = tree.check_round_trip(text).unwrap();
        assert_eq!((stats.decls, stats.errors), (2, 1));
        let kinds: Vec<NodeKind> = tree.decls().map(|d| d.kind()).collect();
        assert_eq!(kinds, [NodeKind::Error, NodeKind::Def]);
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
        assert_eq!((stats.errors, stats.dropped), (0, 0), "{stats:?}");
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
                "Interpolated[\"a${ Binary[x + 1] }b${ y }\"]",
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
                "rewrite <- h, g x at y in t",
                "Rewrite[rewrite RewriteRule[< - h] , RewriteRule[App[g x]] at y in t]",
            ),
            ("omega [h, f x]", "Omega[omega List[[ h , App[f x] ]]]"),
            ("ring [h]", "Ring[ring List[[ h ]]]"),
            ("cases in t", "Cases[cases in t]"),
            ("omega [h] + 1", "Binary[Omega[omega List[[ h ]]] + 1]"),
        ]);
    }
}
