# Marks, or functions that return the node they built

**Status:** design note, 14 November 2026 (SW-3276, for Matt's question on
D3582). Paper lane: nothing in the product changed. One prototype, thrown
away after measuring ([Appendix](#appendix-the-prototype)). Two questions
for Matt ([§12](#12-questions-for-matt)); the first replaces D3582.

It follows [parser-end-state.md](parser-end-state.md) (SW-3233), which
recommended *strict marks* and weighed them against rust-analyzer's events
and against building the flat tree top-down, but not against the textbook
design: every parsing function returns the node it built. This note weighs
that.

Claims are marked **[measured]** (the prototype, release build, on
Speedwell, load 2.9–3.6, best of 25 runs), **[source]** (this repo at
`cddd1a6e2`, or another project's source at the commit named in
[§10](#10-what-other-parsers-do)) or **[estimated]**.

## In plain words

**The problem.** The usual way to write a recursive-descent parser is that
each function returns what it parsed:

```rust
fn sum(&mut self) -> Result<Node> {
    let mut left = self.product()?;
    while self.at(Plus) {
        let op = self.bump();
        let right = self.product()?;
        left = Node::new(Binary, [left, op, right]);
    }
    Ok(left)
}
```

Stitchwort's parser doesn't. Its functions return nothing; when one
finishes a construct it writes a *mark*, "tokens 12 to 19 are a `Binary`",
and a builder nests the marks into the tree afterwards. Today that went
wrong (`a ∧ b ∧ c → q` was checked as `a ∧ b ∧ c`), and the fix proposed
(D3582) keeps marks and tightens them. A fair question is whether the
textbook design would have made the whole class of mistake impossible, and
whether it is the better end state.

**What I found.** Three things decide it, and they are particular to this
tree and this parser.

1. *In this tree a node has nothing to hold.* The textbook returns nodes
   because a node contains its children, so the parent needs them in hand.
   Here the tokens sit once in a flat array, a node is "a kind and a first
   and last token", and its children are whatever nodes lie inside that
   range. The only thing a function could usefully hand its caller is
   *where it started*, and the caller already knows that: it is where the
   parser stood before the call. Strict marks are the textbook design with
   the returned node shrunk to the one number it would be used for:

   ```rust
   fn sum(&mut self) -> Result<()> {
       let start = self.mark();
       self.product()?;
       while self.at(Plus) {
           self.bump();
           self.product()?;
           self.node(start, Binary);
       }
       Ok(())
   }
   ```

   Same shape, same number of lines, and the operator holds its left
   operand as a value (`start`), which is what today's bug lacked.

2. *This parser's functions give up by returning early*, at about 300
   `?` [source]. A returned node that a failing function was holding is
   dropped with it. A mark already written stays. So with marks the
   finished pieces of a broken line survive on their own, and with returned
   nodes they are lost, unless every function is rewritten never to fail.
   The parsers that do return nodes and keep broken code well (C#'s,
   TypeScript's, Swift's, Ruff's) are all written that second way
   [source]. Ours recovers at a few points by layout instead, which was
   decided in the recovery design (D3563).

3. *Returning nodes costs stack and, in its plain form, a lot of time.*
   In the prototype a level of nesting costs 272 bytes with marks, 464 with
   node handles in an arena, 928 with a pointer tree; the pointer tree
   takes 2.9 times as long to parse and 5.7 times the memory [measured].

What returning nodes would give: nesting right by construction rather than
checked, the parser able to look at what it just parsed, and code any
parser-writer recognises. The first is real but small once the builder
checks (a mistake is an internal error at that declaration, not a wrong
tree). The second is exactly what parser-end-state.md wants less of. The
third the strict form already mostly gives.

The textbook style has not left the code base. The step that builds the
compiler's tree out of the lossless one (the lowering, `crates/syntax/src/lower/`)
is written that way: each function returns the `Expr` it built. The old
parser did both jobs at once; they are now two passes, and the first one's
output is flat.

**The change.** None to parser-end-state.md's plan: keep marks, make them
strict (stages T1–T4 as written there). Two small additions from the
prototype: its builder (two passes, no sort, checks nesting, 55 lines) is
ready for T1 to lift, and T2 should pass facts about what was just parsed
through a parser field, not through return values, on the deeply recursive
path.

**What it should do.** Against returning nodes, on the prototype's 2.1 MB
of generated expressions [measured]:

| | Strict marks | Node handles in an arena | Pointer tree |
|---|---|---|---|
| Parse and build the flat tree | 11.7 ms | 11.4 ms | 34.0 ms |
| Memory for the finished tree | 5.2 MB | 5.2 MB (10.8 if the arena is kept) | 7.3 MB (29.4 if the tree is kept) |
| Allocations | 10,075 | 10,076 (59,382 kept) | 874,360 |
| Stack for one bracket level | 272 bytes | 464 | 928 |
| Nodes surviving in 3,954 broken declarations | 167,847 | 165,499 | 162,612 |

For the real parser that is about 16,900 nested brackets with strict marks,
about 14,500–15,000 with arena handles and about 10,800–11,700 with a
pointer tree, under the 12,000 the benchmark needs [estimated from the
measured frames].

## 1. The designs compared

**(M) Strict marks**, as parser-end-state.md recommends: a function that
may wrap what it reads keeps `let start = self.mark()`; when it finishes it
appends `node(start, kind)`; the list is in finishing order (children
before parents), and a builder turns it into the flat preorder tree in two
linear passes, refusing anything that doesn't nest.

**(R1) A pointer tree.** `Node { kind, children: Vec<Child> }`, a child a
token or a boxed node. Functions return `Result<Child>`. Either consumers
read it directly, or it is converted to the flat tree and freed.

**(R2) Handles into an arena.** Functions return a 4-byte handle; nodes are
appended to one array as they finish, each with its token range and a list
of its child nodes' indices (Zig's design, with this tree's token ranges).
Children of a construct with any number of parts (an application's
arguments) are gathered on a scratch stack in the parser. Either consumers
read the arena, or it is converted.

**(R3) Returned starts over marks.** A hybrid found while writing the
prototype: functions return an `Operand`, which is only a start token;
`node(kind, first)` writes M's mark from `first` to here. The textbook's
look, M's list and builder.

A pointer tree in a bump arena (oxc's and swift-syntax's design) I did not
build; it would land near R2 on time and between R2 and R1 on stack
[estimated], with R1's behaviour on errors.

All four parse the same slice of the grammar in the prototype: `match` with
scrutinees and arms, `if`, a lambda, seven operator levels (left, right and
prefix), n-ary application, brackets, tuples, lists, patterns, and recovery
inside brackets (the recovery note's R2). All four give the *same flat
tree*, node for node, for all 10,052 generated declarations [measured].

### 1.1 A binary operator

```rust
// M                                    // R1
fn add_expr(&mut self) -> R<()> {       fn add_expr(&mut self) -> R<Child> {
    let start = self.mark();                let mut left = self.mul_expr()?;
    self.mul_expr()?;                       while matches!(self.peek(), Plus | Minus) {
    while matches!(self.peek(), Plus | Minus) {     let op = self.bump();
        self.bump();                            let right = self.mul_expr()?;
        self.mul_expr()?;                       left = node(Binary, vec![left, op, right]);
        self.node(start, Binary);           }
    }                                       Ok(left)
    Ok(())                              }
}
```

```rust
// R2                                   // R3
fn add_expr(&mut self) -> R<Elem> {     fn add_expr(&mut self) -> R<Operand> {
    let mut left = self.mul_expr()?;        let left = self.mul_expr()?;
    while matches!(self.peek(), Plus | Minus) {  while matches!(self.peek(), Plus | Minus) {
        self.bump();                            self.bump();
        let right = self.mul_expr()?;           self.mul_expr()?;
        left = self.tree.node(Binary, &[left, right]);  self.node(Binary, left);
    }                                       }
    Ok(left)                                Ok(left)
}                                       }
```

R2 needs only the first and last child to know the range, plus the child
nodes for its list; the operator token is implied. In R3 `left` never
changes: it is the start.

### 1.2 An application, `f a b` as one node

```rust
// M                                    // R1
fn app(&mut self) -> R<()> {            fn app(&mut self) -> R<Child> {
    let start = self.mark();                let head = self.atom()?;
    self.atom()?;                           if starts_atom(self.peek()) {
    if starts_atom(self.peek()) {               let mut children = vec![head];
        while starts_atom(self.peek()) {        while starts_atom(self.peek()) {
            self.atom()?;                           children.push(self.atom()?);
        }                                       }
        self.node(start, App);                  return Ok(node(App, children));
    }                                       }
    Ok(())                                  Ok(head)
}                                       }
```

```rust
// R2: the arguments wait on a scratch stack shared by all the functions in progress
fn app(&mut self) -> R<Elem> {
    let head = self.atom()?;
    if starts_atom(self.peek()) {
        let base = self.scratch.len();
        self.scratch.push(head);
        while starts_atom(self.peek()) {
            let arg = self.atom()?;
            self.scratch.push(arg);
        }
        return Ok(self.gathered(App, base));   // makes the node, truncates to `base`
    }
    Ok(head)
}
```

### 1.3 A `match` with arms

```rust
// M
fn match_expr(&mut self) -> R<()> {
    let start = self.mark();
    self.bump();
    loop {
        let scrutinee = self.mark();
        self.or_expr()?;
        self.node(scrutinee, Scrutinee);
        if !self.eat(Comma) { break; }
    }
    self.expect(KwWith, "`with`")?;
    while self.peek() == Pipe {
        let arm = self.mark();
        self.bump();
        loop {
            self.pattern()?;
            if !self.eat(Comma) { break; }
        }
        self.expect(FatArrow, "`=>`")?;
        self.expr()?;
        self.node(arm, Arm);
    }
    self.node(start, Match);
    Ok(())
}
```

```rust
// R1
fn match_expr(&mut self) -> R<Child> {
    let mut children = vec![self.bump()];
    loop {
        let scrutinee = self.or_expr()?;
        children.push(node(Scrutinee, vec![scrutinee]));
        if self.peek() != Comma { break; }
        children.push(self.bump());
    }
    children.push(self.expect(KwWith, "`with`")?);
    while self.peek() == Pipe {
        let mut arm = vec![self.bump()];
        loop {
            arm.push(self.pattern()?);
            if self.peek() != Comma { break; }
            arm.push(self.bump());
        }
        arm.push(self.expect(FatArrow, "`=>`")?);
        arm.push(self.expr()?);
        children.push(node(Arm, arm));
    }
    Ok(node(Match, children))
}
```

R1 has to place every token by hand, commas and keywords included: 10
places in this function where a child is put in a list, against 3 `node`
calls in M. Each is a chance to lose or misplace a token, which M cannot do
([§3](#3-correctness)). Parser lines in the prototype, outside builders and
converters [measured]: M 265, R1 243, R2 288, R3 237.

### 1.4 A construct that fails, with recovery

An error inside brackets whose partner exists: skip to the partner, put an
`Error` node over what was skipped, carry on.

```rust
// M: the whole of it
fn recover_bracket(&mut self, open: u32, e: Box<Diag>) -> R<Kind> {
    let partner = self.matching[open as usize];
    if !self.recover || partner == NONE { return Err(e); }
    self.errors += 1;
    self.pos = partner as usize;
    if open + 1 < partner { self.node(open + 1, Error); }
    Ok(Paren)
}
```

Whatever finished inside the brackets before the error is already in the
list and lies inside the `Error` node's range, so it nests there. Whatever
didn't finish never wrote a mark. Nothing is undone, and nothing has to be
handed to the recovery point.

```rust
// R1: the recovery point has only what it was itself holding
fn recover_bracket(&mut self, open: u32, children: &mut Vec<Child>, e: Box<Diag>) -> R<Kind> {
    let partner = self.matching[open as usize];
    if !self.recover || partner == NONE { return Err(e); }
    self.errors += 1;
    let mut inside: Vec<Child> = children.drain(1..).collect();  // the elements that finished
    let mut next = open + 1;
    for c in &inside { next = end_of(c); }
    inside.extend((next..partner).map(Child::Tok));   // the element that failed: flat tokens
    self.pos = partner as usize;
    if !inside.is_empty() { children.push(node(Error, inside)); }
    Ok(Paren)
}
```

The element that failed, with every node finished inside it, went with the
frames that `?` unwound. R2 does a little better (what failed functions
had put on the scratch stack can be adopted; what they held in locals, an
operator's left operand, cannot) and leaves unreachable nodes in the arena.
R3 is M.

## 2. What the prototype measured

The corpus: 10,052 generated expressions, 2,100,111 bytes, 683,557 tokens,
308,673 nodes, nesting up to 22 deep. It is denser than real code: std's
2.1 MB has 169,503 nodes [parser-end-state.md §4.1], because std has
comments, docs and declarations' headers. Tokens are lexed first; times
are for parsing the token arrays.

| [measured] | M | R3 | R2 | R1 |
|---|---|---|---|---|
| Parse only (marks / arena / pointer tree) | 7.5 ms | — | 11.5 ms | 20.4 ms |
| Parse and produce the flat tree | 11.7 ms | 12.0 ms | 11.4 ms | 34.0 ms |
| Freeing the parser's own tree | — | — | 0.3 ms | 10.6 ms |
| Memory kept, flat tree as the result | 5.18 MB | as M (the same list and builder) | 5.18 MB | 7.32 MB |
| Memory kept, the design's own tree as the result | — | — | 10.80 MB (7.69 shrunk to fit) | 29.41 MB |
| Allocations, flat tree as the result | 10,075 | as M | 10,076 | 874,360 |
| Allocations, own tree as the result | — | — | 59,382 | 842,096 |
| Stack a level: `(((x)))`, `f (f (x))`, `(1 + (1 + x))`, `[[x]]` | 272 B | 368 B | 464 B | 928 B |
| Stack a level: `if c then a else if …` | 64 B | 80 B | 112 B | 208 B |
| Walking the finished tree, every element once | 4.1 ms (flat) | — | 4.1 ms (arena) | 4.1 ms (pointers) |
| Broken corpus: nodes in the 3,954 recovered declarations | 167,847 | 167,847 | 165,499, and 2,348 unreachable | 162,612 |

(For scale, lexing the same text takes 9.1 ms.)

What the numbers say:

- **Handles in an arena cost no time** against marks. The pointer tree
  costs 2.9 times: 2.7 allocations a node, and freeing it alone takes
  about as long as M's whole parse and build.
- **The flat tree is the smallest finished form**: 16.8 bytes a node,
  against 25 for the arena (35 as it comes) and 95 for the pointer tree.
- **Reading is the same speed in all three** forms, through the same kind
  of "children of this node" walk the lowering and the formatter use.
- **Stack: each step towards returning more costs about 100 bytes a
  level** over this prototype's eleven functions: a start returned instead
  of kept (+96), a handle and a scratch stack (+192), owned nodes and
  vectors (+656).
- **Recovery by unwinding keeps 3.1% fewer nodes with a pointer tree**,
  1.4% fewer with an arena: on average 1.3 nodes a broken declaration, and
  always the ones next to the error, where the cursor is. The checking
  builder accepted every recovered declaration's marks with no filtering.

Scaled to the real parser [estimated]. Strict marks are put at 1,489 bytes
a bracket level by parser-end-state.md §4.2 (1,377 measured today, plus at
most 112). The real path through a bracket has about as many recursive
functions as the prototype's (12–14 against 11), so the additions carry
over at 1.0–1.3 times:

| [estimated] | Bytes a level | Brackets in the parser's 24 MiB |
|---|---|---|
| Today (read-back) [measured] | 1,377 | 18,264 |
| M strict marks | ≤ 1,489 | ≥ 16,900 |
| R3 returned starts | 1,585–1,614 | 15,600–15,900 |
| R2 arena handles | 1,681–1,739 | 14,500–15,000 |
| R1 pointer tree | 2,145–2,339 | 10,800–11,700 |

The benchmark needs 12,000. October's parser, which did return trees (the
compiler's), managed 12,740 after a round of work on its frames
[parser-end-state.md §4.2], which fits R1's line.

On time: R1's extra 72 ns a node would be about 12 ms on std's 78.9 ms
parse-and-lower, 15% [estimated from measured]; parser-end-state.md §3.2
guessed 5–10%. The strict builder took 13.6 ns a node here, against about
39 ns for today's sorting one (8.4% of 78.9 ms over 169,503 nodes), so T1
should save about 4 ms on std, not the 2–3 estimated there [estimated;
two measurements on different loads].

## 3. Correctness

What each design rules out, and what it leaves easy to get wrong:

| Mistake | M strict | R1 pointer tree | R2 arena | R3 |
|---|---|---|---|---|
| An operator wraps the wrong left operand (today's bug) | can't: `start` is a local of the function that wraps | can't: `left` is the value | can't | can't |
| Two nodes that cross | builder refuses: internal error at that declaration | can't be written | can't be written; a child outside its parent's range is refused by the converter | as M |
| A token lost, repeated or out of order | can't: a node is a range, every token in it is in it | easy (each token is pushed by hand); the converter's check finds it | can't (ranges) | can't |
| A child node left out of its parent | can't: children are whatever lies inside | the token check finds it | **silent**: the node is unreachable and its tokens lie flat in the parent; needs a "no unreachable nodes" check, which recovery then breaks | can't |
| A construct never given a node | silent in all four: its tokens lie flat in the parent. Found by the span check today and by T4's table of allowed children |
| A start taken at the wrong moment (`mark()` after the first token instead of before) | possible: the node is short by a token; still nests. T4's table finds it | no such thing | no such thing | no such thing: the start is the first child's |
| The parser deciding by looking at what it parsed | has to be passed back on purpose | free: it holds the node | free | has to be passed back |

Two readings of that table.

*By construction against checked.* R1 and R2 make crossing nodes
unwritable; M makes them an error the first time they happen, in every
build, at the declaration that has them (SW-3243, the arrow after a logic
chain, already made a dropped mark `E-INTERNAL`). The difference is between "can't
ship" and "can't ship unnoticed". What made today's bug bad was not that
marks could cross but that crossing was silent and the start was a guess.
Strict marks remove both.

*Each design moves the unchecked part somewhere else.* M can't lose a token
or a child, because it never handles them; R1 handles every token and R2
every child node, so they need a check M doesn't. All four are equally
blind to a construct that was never marked, which is the commonest slip
(the span check exists for it).

**Kinds known late.** `exists` reads a lambda and then is an `Exists`; a
section at the head of an expression widens to the whole expression.
Returning nodes makes these plain code: build the node last, with the kind
now known. In R1 "rewrap" means taking a finished node apart; in R2 it
leaves an unreachable node or edits one in place, the thing strict marks
forbid. In M the answer is parser-end-state.md's: the function that knows
writes the mark. All workable; R1 reads best here.

**The parser reading its own output.** With a node in hand, `atom` can ask
"was that a bracketed lambda?" and `definition` "is this type an
equation?". M has to return such facts on purpose, and parser-end-state.md
§6 lists a dozen such questions asked of the mark list today. Its
conclusion was that all but three or four are checks on meaning that belong
in the lowering, which has the tree. Returning nodes would make every one
of them free to keep in the parser, and to add to. I count that against
it, mildly: the parser's one job is grouping, and a design in which
meaning checks are awkward there keeps them out.

## 4. Error recovery

The recovery design ([syntax-error-recovery.md](syntax-error-recovery.md),
D3563; S1 merged today as SW-1983, a definition checks past a syntax error
in its body) has two kinds of point:

- *Carry on in place* (R1 "ran out"): the function reports the error and
  returns success with a part missing. No node for the missing part.
- *Unwind and skip* (R2–R6): an error raised anywhere inside propagates by
  `?` to the nearest recovery point, which skips to a token it can resume
  at and writes an `Error` or `Gap` node over what it skipped. Layout
  gives the resume points: the next line of the block, the next arm, the
  bracket's partner.

How each tree design serves them:

| | M / R3 | R1 | R2 |
|---|---|---|---|
| Carry on in place | write the mark as usual; the child is absent | return the node with the child absent | the same |
| Unwind: finished constructs inside the skipped range | all kept, nested in the `Error` node, with no code | only those the recovery point's own function holds; the rest dropped with the frames | those on the scratch stack can be adopted; those in locals are unreachable |
| Unwind: state to restore | the modes (`open` goes with T1) | the modes | the modes and the scratch stack's length |
| `Error` node placed | `node(from, Error)` | built from the kept children plus the loose tokens | pushed by hand with its range and adopted children |
| A new recovery point (S2–S3 add five) | one `node` call; the builder checks it nests | each must be handed, or rebuild, what was parsed before the failure | as R1, plus the scratch rule |

The measured gap in kept nodes is small (1.4–3.1%), and today nothing reads
the nodes inside an `Error` node: the lowering turns it into a hole and the
formatter refuses the file. The editor's shape features (selection ranges,
folding, the outline) are the ones that would. So "what survives" is a
modest win for marks in numbers, and a larger one in code: with marks a
recovery point is two lines that can't be wrong about nesting without the
builder saying so.

**The real alternative is a parser that never fails.** Parsers that return
nodes and recover well don't unwind at all. Of the twelve
hand-written parsers in [§10](#10-what-other-parsers-do), ten never
unwind: they put a missing identifier, a missing token, a bogus node or an
error flag in the tree and carry on. Only swc and Zig propagate errors, and each only partly
[source]. In that style returned nodes are at their best: `a + ` is a
`Binary` with a missing right operand, in place, and the checker can still
look at `a`.

For Stitchwort that would mean rewriting the roughly 300 `?` and 158 places
that raise an error [source, counts in `parser.rs` and
`parser/declarations.rs`] so that each decides what partial node to return,
whether it consumed anything, and how its caller makes progress. That is
not only migration, which doesn't count (D2303). Its end state has costs of
its own: every function carries a contract ("return absent without eating
a token or reporting", Biome's rule [source]), loops need a progress
guarantee, and one typing slip tends to produce several errors, where the
recovery note wants one a line. Stitchwort has layout to give it resume
points without any of that (syntax-error-recovery.md §2.4), and marks
serve both kinds of point without preferring either: a function that
carries on writes its mark, one that gives up writes nothing. If S2–S5
show that layout recovery checks too little of a broken file, a
never-failing parser returning nodes is the design to look at then, and
this question reopens with it. Nothing in strict marks makes that harder.

## 5. Trivia and losslessness

No difference between the designs, because none of them carries trivia.
The lexer attaches comments and blank lines to tokens (`Trivia`, one per
token, in an array beside the tokens); whitespace is the source text
between two tokens' spans; nodes hold neither [source, `tree.rs`'s module
doc]. Roslyn and swift-syntax do the same with returned nodes (trivia on
tokens) [source].

What differs is who keeps the tree lossless. In M, R2 and R3 a node is a
token range, so "every token appears once, in order" holds without the
parser doing anything. In R1 it is something the parser does 10 times in
`match_expr` alone and can get wrong; the converter has to check it (the
prototype's does).

## 6. Stack

Measured figures are in [§2](#2-what-the-prototype-measured). Why the
order is what it is:

- M's functions return `Result<(), Box<Diagnostic>>`, one word, and hold
  one `u32`.
- R3 returns a start through the same `Result`, two words; the prototype's
  frames grew by 96 bytes over eleven functions.
- R2 holds a handle for the left operand and another for the right, and
  the scratch stack's base.
- R1 holds owned children (a 16-byte `Child` each, or a 24-byte `Vec`),
  which need cleanup code and a stack slot on every path where `?` can
  leave.

The parser has half the stack, 24 MiB (`parser_limit`); the lowering,
which does return nodes and takes more stack a level for some shapes, gets
all of it [source, `parser/entry.rs`, `parser_limit`]. So the one place in the pipeline
where frames hold trees already takes up to 1.2 times the parser's stack a
level in release builds, 1.55 in debug ones [source, the same comment,
SW-3213].

A pointer tree has one more stack user: dropping it recurses. Measured at
64 bytes a level (130,000 levels on an 8 MiB stack), so not a limit here.

## 7. Time and memory

[§2](#2-what-the-prototype-measured). In short: R2 and R3 are free against
M; R1 is not (2.9 times on parse-and-build, 15% of std's parse-and-lower
[estimated]), and a bump arena would get most of that back [estimated].
Speed doesn't choose between M and R2. Memory favours the flat tree as the
finished form whatever builds it.

## 8. What the lowering, the formatter and the editor read

They read `Node<'f>`: `kind()`, `children()` (child nodes and own tokens in
order), `token_range()`, and helpers on top (`after(tok)`, `child(kind)`,
`own_leaves()`; `lower/access.rs`). Nothing they do depends on the tree
being flat or on how it was built [source: `crates/syntax/src/lower/`,
`crates/fmt/src/printer/`, `crates/cli/src/breaks_cmd.rs`; the LSP still
reads the compiler's tree and tokens].

Would they be better off with R1's or R2's tree as the tree?

- *Speed:* no. The same walk takes 4.1 ms on all three [measured].
- *What they can ask:* a pointer tree or an arena finds a node's n-th
  child node without skipping subtrees. The flat tree's `children()`
  skips each child's subtree in one step (`subtree_end`), so it is already
  proportional to the number of children. None of them has parent links;
  all could add them.
- *What they'd lose:* 16 bytes a node; a tree that is one `Vec` a
  declaration, compared with `==` and dumped by a loop (the gate for every
  stage, and for the self-hosted twin, is that dump).

So if nodes were returned, the right form is still "convert to the flat
tree and drop the rest", which is what makes R2's arena a second, temporary
copy of what marks hold in 12 bytes a node.

## 9. The self-hosted parser

[self-hosted-fmt.md](self-hosted-fmt.md) §3.2 has the Stitchwort twin
return nodes ("the natural shape in a functional language"), and that
stands. Its reasons are the mirror of this note's: in Stitchwort there is
no stack to protect (16 million pending calls), a value returned costs
nothing extra, the tree is a data type to match on and prove things about,
and the twin's parser is strict (the formatter refuses a broken file), so
there is no unwinding to lose nodes in.

Does the Rust parser need to match its shape? No: the twin is gated on the
tree dump being identical for every file (513,279 nodes), not on the code
looking alike. The port is function for function either way. Strict marks
help it a little: with `let start` at the top and `node(start, K)` at the
bottom, each Rust function says plainly which range becomes which kind,
which is what the Stitchwort function's constructor call needs. Today's
read-back (`open`/`close`) hides that.

A self-hosted *compiler's* parser would need recovery, and would then face
this note's question again, in a language where "never fails, returns a
node with a hole" is the cheap style. That is self-hosted-fmt.md §9's
direction, not a plan.

## 10. What other parsers do

Read from each project's source at the commit given (fetched from GitHub
today) [source]. "Returns" is what a parsing function hands its caller.

| Parser | Functions return | An operator gets its left operand by | Tree | Keeps every token and comment? | On an error |
|---|---|---|---|---|---|
| **Roslyn** (C#), `b9b56c2c` | the green node | a value: `_syntaxFactory.BinaryExpression(kind, leftOperand, operatorToken, …)` | node objects | yes; trivia on tokens | always a node: missing identifiers and tokens with the error attached |
| **TypeScript**, `release-6.0` `050880ce` | the node | a value: `makeBinaryExpression(leftOperand, …)` | an object a node | nodes carry positions (where comments live: not checked) | always a node (`createMissingNode`) |
| **Go**, `840c8327` | the node | a value: `x = &ast.BinaryExpr{X: x, …}` | heap pointers | no; comments in a list beside | `BadExpr` and an error list; gives up after 10 errors |
| **swc**, `df1c0186` | `PResult<Box<Expr>>` | a value | a `Box` a node | spans only (comments: not checked) | mostly returns the error and unwinds; a few places substitute an `Invalid` node |
| **oxc**, `af14baca` | the node, no `Result` | a value | bump arena | spans only (comments: not checked) | a fatal error sets a flag, jumps the lexer to the end and returns a dummy |
| **Ruff**, `6bf61927` | the node | a value | a `Box` a child | no; tokens beside | never fails; invalid-name nodes |
| **swift-syntax**, `c4872164` | the raw node | not at parse time: operators are left as a flat sequence and folded later | bump arena | yes; trivia on tokens | never fails; missing nodes |
| **Zig**, `738d2be9` | an index into flat arrays | a value (the index): `.node_and_node = .{ node, rhs }` | flat arrays, nodes appended as they finish | no; tokens beside | returns the error, caught at member level; some places warn and return what they have |
| **rust-analyzer**, `114dcb8d` | a marker (a place in an event list), not a node | `lhs.precede(p)`: a new start event linked in front | events, replayed into rowan's tree | yes | never fails; error events, abandoned markers |
| **Biome**, `4cea5c6a` | absent, or a marker | `precede`, as rust-analyzer | events, then a rowan fork | yes | never fails; bogus nodes |
| **rowan's builder**, `d601b195` | nothing (a builder) | a *checkpoint*: the children stack's length saved before the operand; `start_node_at(checkpoint, kind)` | built bottom-up from a stack of children | yes | — |
| **Lean 4**, `a8f7ac94` | nothing: state in, state out | the syntax stack's size saved before, minus one: `mkTrailingNode k iniSz` wraps from there | `Syntax` values built bottom-up from the stack | yes; whitespace in each atom's source info | no exceptions: an error field in the state, `missing` pushed |
| **Carbon**, `7a3608ba` | nothing; an explicit state stack, no recursion | nothing to get: the operands are already in the array, and the operator's node is appended after them (the last step inferred: the helper wasn't read) | one flat array in postorder | nodes point at tokens | always nodes, with an error bit |
| **tree-sitter**, `afcfe343` | (table-driven) | a reduce pops the children off the parse stack | reference-counted blocks | with the source | error and missing nodes |

What I take from it:

- **Returning the node is the majority design**, as Matt expected: eight
  of the twelve hand-written parsers. Six of the eight pair it with
  functions that never fail.
- **"Save a position, wrap everything since" is the other family**:
  rowan's checkpoint, Lean's saved stack size, rust-analyzer's `precede`,
  and marks. They differ in what the position indexes (a stack of built
  children; an event list; the tokens). Marks index tokens, which is the
  simplest of the three because a token position needs no bookkeeping: it
  is where the parser is.
- **Carbon's finished tree is a strict mark list**: nodes in finishing
  order in one array, "an efficient layout to produce … requiring little
  context to be maintained during parsing" [source, its `parse.md`].
  Stitchwort's differs by one step, the reorder to preorder, which is for
  the readers' sake (children found by walking forward).
- **Zig is R2**, and shows its cost on errors: it has "zombie nodes" for
  slots reserved and not used [source].
- rust-analyzer says why it has events: to keep "the parser and the syntax
  tree isolated from each other, such that they can vary independently"
  [source, `event.rs` and its syntax doc]. Marks give the same separation:
  `Mark` is the only thing the parser and the tree share.

## 11. Recommendation

**Keep strict marks.** D3582's recommendation stands, now with the
textbook alternative weighed and measured. In one paragraph for the module
doc: *the tree stores tokens once and a node is a range of them, so a
parsing function has nothing to return but where it started, which its
caller already knows; a function that fails has written nothing, and what
finished before it stays, so recovery needs no undoing; and frames that
hold no nodes keep nesting deep.*

Returning built nodes would be the right design under three conditions,
none of which holds: a tree whose nodes contain their children; functions
that always return; and stack to spare. If the second ever changes
([§4](#4-error-recovery)), look again.

**Stages.** parser-end-state.md's T1–T4 are unchanged in scope, order and
model. T0 is done (SW-3243, the arrow after a logic chain, merged today),
and so is recovery's S1 (SW-1983), so T1 is next. Additions [estimated]:

| Stage | Addition | Hours |
|---|---|---|
| **T1** (strict marks; Opus, 6–9 h) | Lift the prototype's builder ([Appendix](#the-builder)): a size pass forward and a placing pass backward, no sort, order and crossing checked. Put the paragraph above in `tree.rs`'s module doc, pointing here | +0.5 |
| **T2** (the parser stops reading its output; Opus, 6–8 h) | Where a function must tell its caller what it read (`callable_paren`, the `()` pattern), use a parser field set by the callee, not a return value, on the recursive expression path: returning even a 4-byte value there cost 96 bytes a level in the prototype | 0 |
| **T3**, **T4** | none | 0 |

Total still 21–30 lane hours, less T0's 2–3 already spent.

For comparison, what the alternatives would cost [estimated]: R3's style
in T1, +2 h (about 100 `node` sites and 60 function signatures) and 6–8%
of nesting depth. R2 in place of T1, 14–20 h on Opus (every parsing
function, the scratch stack, the snapshot), 13% of depth, and S2–S3's
recovery points each written to be handed what survives. R with functions
that never fail, a further 20–30 h and a second edition of the recovery
design.

## 12. Questions for Matt

**D3600: the parser keeps strict marks; its functions don't return built
nodes.** This replaces D3582 (the same recommendation, which weighed
events and top-down building only): a yes here is a yes there.
*The problem:* the standard recursive-descent design returns the node from
each function, which makes wrong nesting impossible and is what any reader
expects. The parser writes marks instead, and today that let a statement
be misread.
*The change:* none to the plan. Marks stay, made strict (T1–T4 of
parser-end-state.md): each function keeps where it started and writes
"from there to here is an X" when it finishes; the builder checks nesting
and refuses what doesn't fit. This is the returned-node design with the
node reduced to its start, because in this tree that is all a node has.
*What it should do:* the same tree for every file. Against returning nodes
[measured on the prototype]: the same parse time as arena handles and a
third of a pointer tree's (11.7, 11.4 and 34.0 ms); 272 bytes of stack a
bracket level against 464 and 928, so about 16,900 nested brackets in the
real parser against about 14,700 and about 11,200 [estimated]; and after a
syntax error everything that finished stays in the tree with no code at
the recovery point, where returned nodes lose the 1–3% nearest the error.
*The alternative:* returned nodes come into their own in a parser whose
functions never fail (C#'s, TypeScript's, Swift's). That is a different
recovery design from the one decided in D3563, with a contract on every
function; worth another look only if layout recovery turns out to check
too little of a broken file.
**[rec: yes, strict marks]**

**D3601: should the parser's functions read the textbook way anyway, by
returning their start?** (R3 in [§1](#1-the-designs-compared).)
*The problem:* with strict marks a function starts with `let start =
self.mark()` and its calls return nothing, which is unfamiliar next to
`let left = self.product()?`.
*The change:* functions return an `Operand` (a start and nothing else),
and `self.node(Binary, left)` writes the mark. Same list, same builder,
same tree.
*What it should do:* code that looks like the textbook, and a start that
can't be taken at the wrong moment. It costs 96 bytes of stack a bracket
level in the prototype (272 to 368) [measured], about 1,000–1,300 fewer
nested brackets in the real parser [estimated], 2 more lane hours in T1
[estimated], and `left` is a name for something that is only a position.
**[rec: no: keep `let start`; 99 sites are already written that way]**

**Decided here as the orchestrator's kind of call** (say if you disagree):
T1 lifts the prototype's builder; T2 passes "what I just read" through a
parser field on the recursive path.

## Findings worth tickets

- **parser-end-state.md §3.2 underestimates a pointer tree's cost**
  ("5–10% of parsing"): 2.9 times on the prototype's parse-and-build, about
  15% of std's parse-and-lower [estimated from measured]. Its conclusion
  holds; the figure should point here.
- **T1's builder can be lifted from the prototype** ([Appendix](#the-builder)):
  two linear passes, 13.6 ns a node against about 39 ns today, so about
  4 ms off std's parse [estimated], and it accepted the marks of all 3,954
  recovered declarations with no filtering. Note for the T1 ticket.
- **Returning a small value up the recursive expression path costs stack**:
  +96 bytes a bracket level for a `u32` in the prototype [measured]. T2's
  "the function returns what it read" items (`callable_paren`, the
  absurd-pattern flag) should use a parser field on that path. Note for the
  T2 ticket.
- **`tree.rs`'s module doc should say why functions don't return nodes**,
  in the paragraph of [§11](#11-recommendation); it is the first thing a
  reader used to other parsers will ask. With T1 or T3's comment sweep.
- **S1's `recovering_body` filters marks by hand** (`recovering_body`, `parser.rs`:
  marks starting at the body's first token "would cross" the `Error` node,
  "so they go") [source]. The prototype's recovery point needed no filter
  because its `Error` node starts where the failed construct started.
  parser-end-state.md §5 already says T1 should restate it so; this is the
  measured support, and S2's five new points should follow the same rule
  from the start.
- **syntax-error-recovery.md §4.5 ("What other tools do") is marked "from
  memory"**; [§10](#10-what-other-parsers-do)'s table is from sources and
  covers the parser side (ten of twelve never unwind). Worth a pointer when
  that note is next edited.
- **If layout recovery checks too little** (to be judged from S5's
  recovery corpus and `stitchwort dev breaks`), the design to weigh is a
  never-failing parser, with returned nodes, not finer recovery points
  under marks. A question for after S5, not a ticket now.
- `docs/proposals/README.md` now lists this note; its row for
  parser-end-state.md says "D3582 open", which D3600 replaces.

## Appendix: the prototype

A scratch crate outside the workspace, about 1,900 lines, not committed
(`/private/tmp/claude-550/-Users-agent-repos-mdr-stitchwort/8230e28a-2fab-4832-920d-c5160adb7e00/scratchpad/sw3276/proto/`,
which won't outlive the session; everything needed to redo it is here and
in [§1](#1-the-designs-compared)).

- **One lexer, one token array, one flat tree type** (`kind`, `start`,
  `end`, `subtree_end`, as `tree.rs`'s `NodeData`), and four parsers over
  them: `marks.rs` (M), `ret.rs` (R3), `arena.rs` (R2), `ptr.rs` (R1).
  Errors are `Box<Diag>` through `?` in all four, as in the real parser.
- **Corpus:** a seeded generator of expressions over the slice's grammar,
  to 2.1 MB; nested constructs weighted roughly as code reads (35%
  operators, 35% applications of one to three arguments, 8% `match` of two
  to four arms, 6% `if`, 5% lambdas, the rest brackets, lists, tuples).
- **Agreement:** the four flat trees are compared with `==` for every
  declaration before anything is timed.
- **Time:** best of 25 rounds over the whole corpus, tokens lexed
  beforehand. M reuses one mark buffer; R2's converting run reuses one
  arena.
- **Memory:** a counting global allocator (bytes live, peak, calls), in a
  separate build so the timed build doesn't pay for it.
- **Stack:** the stack pointer read in `atom` (`mov x, sp`), its lowest
  value over a parse of 20,000 nested levels, subtracted from its value at
  entry.
- **Recovery:** in each declaration one token (not the first) is replaced
  by `=>`; 3,850 then fail whole (no bracket around the error), 3,954
  recover inside a bracket, 2,248 still parse. All four parsers agree on
  which.
- **Not covered:** layout, declarations, trivia (none of the designs
  touches it), the eight mode fields, a bump-arena pointer tree, and a
  never-failing variant of any of them.

### The builder

For T1. Marks arrive in finishing order: ends never go back, and of two
with the same range the later is the parent.

```rust
pub fn build(&mut self, marks: &[Mark], ntoks: u32) -> Result<Flat, &'static str> {
    let n = marks.len();
    self.size.clear();
    self.size.resize(n, 1);
    self.stack.clear();
    let mut last_end = 0;
    // Forward: each mark's subtree size. The stack holds the marks so far
    // that have no parent yet; a new mark takes the ones that start inside it.
    for (i, m) in marks.iter().enumerate() {
        if m.end < last_end || m.start >= m.end || m.end > ntoks {
            return Err("a mark out of order");
        }
        last_end = m.end;
        while let Some(&top) = self.stack.last() {
            let t = marks[top as usize];
            if t.start >= m.start {
                self.size[i] += self.size[top as usize];
                self.stack.pop();
            } else if t.end > m.start {
                return Err("two marks cross");
            } else {
                break;
            }
        }
        self.stack.push(i as u32);
    }
    let total = n as u32 + 1;
    let root = NodeData { kind: K::Expression, start: 0, end: ntoks, subtree_end: total };
    let mut out = vec![root; n + 1];
    // Backward: parents come before their children now, last child first,
    // so each subtree is placed ending where the one after it begins.
    // (start token, where the next subtree placed under it must end)
    self.open.clear();
    self.open.push((0, total));
    for i in (0..n).rev() {
        let m = marks[i];
        while self.open.len() > 1 && self.open[self.open.len() - 1].0 > m.start {
            self.open.pop();
        }
        let top = self.open.len() - 1;
        let end = self.open[top].1;
        let at = end - self.size[i];
        self.open[top].1 = at;
        out[at as usize] = NodeData { kind: m.kind, start: m.start, end: m.end, subtree_end: end };
        self.open.push((m.start, end));
    }
    Ok(out)
}
```
