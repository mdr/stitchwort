# Lowering: building the compiler's tree from the lossless tree

**Status:** design note, 14 November 2026 (SW-3160). Paper lane: nothing is
built. Steps 3 and 4 of
[syntax-tree-architecture.md](syntax-tree-architecture.md) (end state A2,
D3562 yes). Steps 1 (the lossless tree, SW-3170) and 2 (the formatter on it,
SW-3194) are done. It stops for Matt on two questions ([§9](#9-questions-for-matt)).
It fits with [syntax-error-recovery.md](syntax-error-recovery.md) (SW-3161):
the lowering lowers that note's error gaps, and its corpus of half-typed
declarations is part of the oracle.

Claims are marked **[source]** (read in the code at `051fe154a`),
**[measured]** (the main checkout's release binary, built 08:01 today; the
probes are in [Appendix A](#appendix-a-the-probes)) or **[estimated]**.

## In plain words

**What changes.** Today one parser does two jobs at once: it works out the
grammar (what is a `match`, where an argument ends), and it builds the
compiler's tree, expanding shorthand as it goes (`let (a, b) := e` into a
one-arm `match`, `a ≤ b < c` into a hidden `let` and `∧`, `.f a` into a
lambda, and fifteen more). Since step 1, the same parse also records the
lossless tree. After this work the parser only records the lossless tree,
and a separate step, the **lowering**, builds the compiler's tree from it.
Every piece of shorthand is then expanded in one place, the lowering, and
the grammar lives in one place, the parser.

**What a user or contributor notices.** Nothing directly: the compiler gets
exactly the tree it gets today, spans included, and every error message
stays word for word the same. That is the test: for as long as both routes
exist, every `.sw` file in the repo and every rejected example is parsed
both ways and the results must match exactly. A contributor adding syntax
afterwards changes the parser (the grammar, and a node kind) and the
lowering (what it means), each simpler than today's parsing function.

**Why.** One place for grammar and one for shorthand (D3562). And it is
what makes D3563 possible: once the parser builds nothing but marks, it can
mark an error node and carry on, and the lowering turns the gap into a
hole, so a declaration with a half-typed line keeps being checked.
SW-3161 ([syntax-error-recovery.md](syntax-error-recovery.md)) designs
that recovery and recommends it lands first; the lowering here lowers its
gaps (`Error` nodes and missing parts), and its corpus of half-typed
declarations is part of the test.

**Cost.** About 50 lane hours in eight lanes [estimated], including the
lowering of SW-3161's error gaps, none of them
risky in the usual way, because the old route is the oracle until the end.
Parsing gets roughly 10–30% slower in the end state [estimated]; parsing
all of std, which every `stitchwort check` does once, takes 55 ms today
[measured], so a check would take about 5–15 ms longer [estimated].

## 1. How the compiler's tree is built today

The parser is recursive descent over one declaration's tokens at a time
(`split_decls` cuts the file at column 0, `parser.rs:600`). Outside its
tests it is 7,296 lines in `parser.rs` (lines 1–6004),
`parser/declarations.rs` and `parser/sections.rs`: 234 functions, 99 of
which return a built value (`Result<Expr>`, `Result<Pattern>`,
`Result<Vec<Decl>>`, a `Name`, an `Alt`, …) [source, counted]. They build
the compiler's tree directly at 193 `Expr` construction sites, 49
`Pattern` and 27 `Decl` ones, and record the lossless tree's marks at 128
calls (`node`, `node_at`, `open`/`close`, `retag_last`, …) [source,
counted]. The compiler's tree (`ast.rs`) has 43 `Expr` variants, 14
`Pattern`s and 6 `Decl`s; the lossless tree has 94 node kinds
(`tree.rs`) [source].

The parse-time context the grammar needs is parser state: the block column
and its one exception (`limit`, `allow`), `calc_depth`, `rewrite_rule`,
`guard_start`, `rewrite_at`, `let_value`, `in_list` (`parser.rs:702–754`).
That is grammar and stays in the parser: it decides where constructs end,
which the marks then record. The lowering never needs it.

### Inventory of shorthand and expansion

Every place the compiler's tree is not what was written. "Count" is how
many spans of each kind the span check (`dev tree --spans`, `tree/spans.rs`
`Synthetic`) found over std, `aoc/src`, `games` and `examples` [measured];
"–" where the check has no category for it.

| # | Written | Compiler's tree | Where [source] | Count |
|---|---|---|---|---|
| 1 | `def f (x: A) (y: B): R := e` or arms | `Decl::Signature` with a `Pi` per parameter, then a `Decl::Equation` per arm with the header's names as patterns and `arm: Some(n)`; defaults moved to `defaults` | `declarations.rs:231` `definition`, `:825` `lower_header`, `:868` `take_defaults` | 66,135 Header |
| 2 | `theorem t ∀ (x: A) …` | the `∀` dropped (D3472) | `declarations.rs:251` | – |
| 3 | attributes before a declaration | moved onto its first `Decl` | `parser.rs:324` (`parse_tokens`) | 48 Attributes |
| 4 | `type R = { x: A }` | a `Data` with one constructor named `%mk` | `parser.rs:2394` (`data`) | – |
| 5 | `f a b` | `App(App(f, a), b)` | `parser.rs:4910` `app` | 100,817 PartialApp |
| 6 | `(f a) b` | `Bracketed(App(f, a))` at the head; other brackets dropped | `parser.rs:4916` | – |
| 7 | `f()`, `x.f()` | `App(f, Unit)` | `parser.rs:5076` (`atom`) | – |
| 8 | `(a, b, c)`, pattern too | `Tuple(a, Tuple(b, c))` | `parser.rs:1468` `tuple_expr`, `:1496` `tuple_pattern` | 355 Nested (with #9) |
| 9 | pattern `[a, b, ..r]` | `Cons(a, Cons(b, r))`, `Nil` | `parser.rs:1947` (`pattern`) | (in #8) |
| 10 | a block's lines | nested `Let`, `Seq`, `LocalDefs`, each spanning to the block's end; consecutive local `def`s grouped into one `LocalDefs` | `parser.rs:2612` `block`, `:855` `bind_let` | 2,215 BlockRest |
| 11 | `let (a, b) := e` (block or expression) | one-arm `Match` with `MatchKind::Let`, `Ann` if typed | `parser.rs:855` `bind_let`, `:2864` | 589 PatternMatch (with #12) |
| 12 | lambda with pattern parameters `(a, b) => e` | `Lam(%arg0, Match(MatchKind::Lambda))` | `parser.rs:3394` `lambda` (`:3451–3504`) | (in #11) |
| 13 | `match \| …`, `match some \| …`, `matches \| …` | `Lam(%arg…)` over a `Match` (`Clause`, `ClauseSome`, `ClauseMatches`); `Some` wrapped round bodies; an added last arm `_ => None` / `_ => False`; `True` for a bare `matches` arm | `parser.rs:3210` `clause_lambda` (`:3250–3298`) | 260 Empty, 41 Added, 44 Generated (with #15) |
| 14 | `a ≤ b < c` | `let %chain<offset> := b; a ≤ %chain… ∧ …` (atoms not bound) | `parser.rs:4636` `comparison_chain`, `:5710` `chain` | 252 Chain |
| 15 | `.f a`, `(.id == id)` | `Lam(%section, …)`, the section's arguments its own | `parser.rs:5067` `atom`, `:5131`, `:4929`; `sections.rs:241` | 976 Section |
| 16 | `(+ 1)`, `(k +)`, `(&&)` | `Lam(%section, …)`, `Lam(%left %right, …)` | `sections.rs:216–312` | (in #15) |
| 17 | `xs \|> .f a` | `xs.f a`, the section filled with the receiver | `parser.rs:5849` `piped` | – |
| 18 | `∃ x y => P` | `Std.Exists _ (x => Std.Exists _ (y => P))` | `parser.rs:4084`, `:5792` `exists_chain` | 512 Exists |
| 19 | `p ↔ q` | `App(App(Std.Iff, p), q)` | `parser.rs:4048` `iff` | – |
| 20 | `!b`, `x ∉ xs` | `App(Std.Bool.not, …)` | `parser.rs:5834` `prefix_op`, `:4753`, `:5445` | – |
| 21 | `a > b`, `a ≥ b` | `b < a`, `b ≤ a` (flipped) | `parser.rs:5781` `binary` | – |
| 22 | a `calc` with `>`/`≥` steps | reversed; `=` steps' proofs wrapped in `Std.Eq.sym` | `parser.rs:5864` `reverse_calc` | – |
| 23 | `"a${x}b"` | `Interpolated("a" ++ Std.Show.toText x ++ "b")` | `parser.rs:5349` `interpolated_str` | 509 Interpolation |
| 24 | `-x` vs `f -x` | `Neg(…, NegForm::Operand / Argument)`, decided by spacing | `parser.rs:5415`, `negation.rs` | – |

Tags that let later errors say what was written, which the lowering must
reproduce exactly: `MatchKind` (5 elaborator files), the `%section` name
(3), `NegForm` (2), `as_chain_let` (3), `Bracketed` (18) [source, grep
counts of files].

**Expansion after the parser.** Two elaborator modules undo part of an
expansion: `elab/src/chain.rs` puts a chain's operand back when the chain
is a proposition, and `elab/src/patlet.rs` turns a `MatchKind::Let` match
into projections. Neither is touched here: the lowering's first job is to
give exactly today's tree. Moving them into the lowering is a follow-up
([Findings](#findings-worth-tickets)).

## 2. The lowering's shape

**Where.** A module `crates/syntax/src/lower.rs` with submodules by
construct family, mirroring the parser's files: `lower/decls.rs`,
`lower/exprs.rs`, `lower/binding.rs` (blocks, lambdas, sections),
`lower/matching.rs` (match, handle, calc, rewrite, patterns). The
expansion helpers that are already free functions over finished values
move there unchanged: `bind_let`, `chain`, `binary`, `exists_chain`,
`library_var`, `prefix_op`, `piped`, `reverse_calc`, `lower_header`,
`take_defaults`, `sections::operation` and its helpers. That is a large
part of the shorthand already; the rest is inline in parsing functions
and gets pulled out into functions of the same kind.

**One function per node kind, not one fold** [implementation choice].
`expr(node) -> Expr`, `pattern(node) -> Pattern`, `decl(node) -> Vec<Decl>`
each dispatch on `node.kind()` to one function per kind (or per small
family). A generic fold doesn't fit: the compiler's tree isn't uniform,
and the same kind lowers differently by context (a `Paren` at the head of
an `App` with arguments is `Bracketed`, elsewhere it vanishes; a leaf `_`
is a `Hole` in an expression and a `Wildcard` in a pattern; a `Def` at top
level is a `Signature` and equations, in a block a `LocalDef`). Recursive
descent over the tree, shaped like the parser, also makes each lowering
function easy to check against the parsing function it replaces.

**What it reads.** Node kinds, the node's own leaves (tokens, which carry
names, numbers and text as the lexer read them, and their spans), and its
children. One rule: **the lowering never decides grouping.** If it would
have to look at tokens to work out where something ends or what it
belongs to, the parser must mark it instead (a new kind, or a marker
node). Reading which operator a `Binary` has, which bracket a `Param`
opens with, or whether a `Record` has a `|`, is fine; that is reading,
not parsing. Two decisions the parser makes from spacing are recorded
rather than recomputed, so the parser stays their one source: argument
versus operand minus (#24) and a section starting a line. I expect a
handful of such additions; the oracle finds every one.

A small accessor layer on `Node` keeps this readable: `child_nodes()`,
`own_leaves()`, `first_leaf()`, `leaf_after(kind)`, and typed views where
a kind's children vary (`Param`'s brackets and default, `Arm`'s patterns,
guard and body).

**Spans.** The lowering gives every node exactly the span the parser
gives it today, quirks included: the outer tuple covers its brackets and
the inner ones don't; an application's span comes from its parts and may
stop inside a bracket; a library name the parser writes has an empty span
at a chosen point; `Std.Show.toText` spans the `${…}`; a hidden chain
name carries its operand's byte offset. Most spans are a node's first and
last token; the rest are what the 13 `Synthetic` categories already list,
and the moved helpers compute them as before. The oracle compares spans,
so none can drift.

**No node identifier in the compiler's tree, for now** [implementation
choice, departing from the architecture note]. The architecture note
says each lowered node would carry the lossless node it came from. The
span already does that job: over 989,469 spans, every one is a node's
range or a single token, or one of the listed synthetic kinds
[measured]. A separate field would touch the 43 + 14 variants and every
positional match on them in the elaborator, for no gain in steps 3–4.
When a tool needs the link (the editor under D3563, say), a span-to-node
index built on demand from the lossless tree gives it; `tree/spans.rs`
already does that lookup.

**Single expressions.** `parse_expression` (used by `search`, `eval`, the
playground and elaborator tests) needs a tree too: a `SyntaxFile` whose one
root is a new kind, `Expression` [implementation choice].

### Error nodes and missing parts (SW-3161)

[syntax-error-recovery.md](syntax-error-recovery.md) (SW-3161, for
D3563) has the parser recover inside a declaration and recommends that it
lands **before** this work. It puts two kinds of gap in the lossless tree
(its §3), and the lowering handles both:

- **An `Error` node over skipped tokens** (its points R2–R6), where they
  were: a `Block`'s line, an `Arm` or its body, a `Paren`'s inside, a
  `calc` step, the rest of a body. The root keeps its real kind (`Def`,
  `Theorem`). The lowering turns the node into what the parser builds at
  that point: `Expr::Missing(span)` in an expression's place, the block's
  error statement (with a `let`'s name kept, bound to a missing value,
  when the name was read), an arm with a missing body, or no arm and the
  `match` marked incomplete when its patterns broke, a step with a missing
  side, and R6's equation with the header's patterns and a missing body.
  **The lowering never looks inside an `Error` node.** The finished
  constructs there keep their nodes for the editor, but they are skipped
  text to the checker.
- **A missing part** (R1, the text ran out) has no node: the parent lacks
  a required child. So each lowering function knows its kind's required
  slots, and finds which slot a child fills by reading the token that
  introduces it (`:` or `:=` in a `let`, `then` and `else`, `=>`, `in`,
  `with`). That is reading, not parsing. A slot whose token or child is
  absent is a missing expression, at the point SW-3161 gives: the end of
  the parent's last token. R1 only happens at a stop or at the end of a
  declaration, so nothing follows an absent slot, and slots can't be
  confused.

What the lowering builds for each gap, spans included, is whatever the
recovering parser builds directly: the oracle holds it to that, as for
everything else. The span check exempts a missing expression's point span
(SW-3161 §3), so `Synthetic` gets a `Missing` reason.

A **declaration that fails whole** (a broken header; `type`, `interface`,
`ability`, `namespace` and `import`, which aren't recovered, D2782; a
lexical error, SW-3185) stays one `Error` root, and the lowering gives
only its names in `Module::failed`, read off its tokens by
`failed_names_of` as today.

**If lowering lands first** (the other order): today's recovered signature
(`body_error`, parked in `header`, `parser.rs:747`) has to be lowered, and
the builder currently drops a failed declaration's marks (`tree.rs`
`build_decl`). Then L0 keeps the marks of the constructs that finished
before the error, under the `Error` root, and L2 makes the signature from
the `Param`, `ResultType`, `Decreasing` and `Unfolding` nodes there.
SW-3161's S0/S1 keep those marks anyway, and R6 replaces `body_error`, so
in the recommended order this part is not needed.

**Recovery and the parser's state.** SW-3161 restores the parser's mode
fields and truncates `open` at a recovery point, and keeps the marks
already recorded, which nest inside the new `Error` node. Since the
lowering skips `Error` nodes' insides, those marks don't need to be
consistent with anything outside them. Its marks hazard (an `Error` mark
taken for an operator's left operand, SW-3161 §3.2) is the parser's to
avoid; the oracle would show it as a different tree.

**Lexical errors.** `parse_module_recovering` recovers from a lexical
error per declaration (`lex_recovering`), while the tree today needs
`lex_with_trivia`, which fails for the whole file. The lowering route uses
`lex_recovering_with_trivia` (`lexer.rs:439`, exists, unused outside the
lexer) [source]. SW-3161's S0 folds in SW-3185, which makes such a
declaration an `Error` root over its raw text; with it, this is done.

**Stack.** The parser bounds its recursion with `StackLimit` and reports
`E-RESOURCE` (12,000 nested brackets parse within the 1.5 MiB default:
the bench's check-nested-parens, `crates/bench/src/programs.rs:266`). The
lowering recurses as deeply, so it takes the same `StackLimit`, reports the
same error, and keeps its frames small the way the parser does
(`#[inline(never)]` on the large arms). The two nesting benchmarks are a
gate.

## 3. Errors

The parser reports about 220 errors at their sites: 95 `error(…)` and 22
`Diagnostic::error(…)` calls, 45 `unexpected(…)` and about 60 `expect…`
calls [source, counted]. 96 examples under `reject/` and `soundness/`
expect a parse-stage code (86 `E-PARSE`, 6 `E-COMPARISON-CHAIN`, 2
`E-CALC-RELATION`, 1 `E-OR-PATTERN-BINDS`, 1 `E-NAMESPACE-NOT-FIRST`), and
their messages are snapshot-tested [source].

**Step 3: the lowering is infallible.** It runs on what parsed, including
a recovered declaration's tree with its gaps, and every error is still
reported by the parser, by the same code. The diagnostic text can't
change, and the oracle checks it anyway.

**Step 4: the parser has no values to inspect.** Its errors fall in three
groups:

- **A. Grammar errors on tokens** (expected this, found that; layout;
  a keyword in the wrong place): almost all of them. They stay in the
  parser, unchanged.
- **B. Parse decisions that read a built value**, about a dozen sites
  [source]: `arm_body`'s absurd-pattern test (`parser.rs:1215`), the
  alternative-count note (`:3154`), `Bracketed` (`:4916`), a unit call
  after a name or field (`:5076`), `result_is_equation`
  (`declarations.rs:276`), `clause_match` (`declarations.rs:369`), the
  `Ann` test (`declarations.rs:487`), the constructor and record checks of
  `ctor_fields_expr` and `brace_argument` (`parser.rs:5165–5204`), the fact
  list's spread (`:5338`), `rewrite_membership` (`:3872`). Each becomes a
  test of the last mark's kind ("the operand just read is an `App`") or of
  tokens. Where the value was only needed to build something (`piped`'s
  receiver, the record surgery), it moves to the lowering.
- **C. Checks on meaning that read built values**: duplicate parameters
  (`check_duplicates`, `declarations.rs:903`), an or-pattern binding names
  (`first_bound`, `parser.rs:3373`), an absurd arm with a guard (`:1215`),
  a lambda parameter's default (`lambda_default`, `:3420`), the operand
  text in a chain error's suggestion (`operand_text`, `:4656`, `:4719`), a
  block ending in a `let` or `def` (`:2642`). They move to the lowering,
  which becomes `Result`, keeping their text.

**Which errors a declaration reports.** Without recovery, the first check
the parser reaches wins and the declaration stops. With SW-3161's
recovery, a failed check ends only the construct around it: the nearest
recovery point (a line, an arm, a bracket) skips to where it resumes, and
SW-3161 keeps at most one error per line, the first. A check in group C
fires at a known point, the end of the construct it inspects (the
`ResultType` for duplicate parameters, the `Arm` for the absurd guard).
Moved into the lowering, it no longer stops the parser, so the parser may
find a second error in the text that today's recovery would have skipped.
The lowering keeps the old result by putting its errors in with the
parser's, each at the token where today's check fires, and applying the
same rules to the combined list: errors in file order, the first one per
line kept, and a parse error inside the construct that a recovery point
would have skipped dropped. (Without recovery the same rule reads: report
the earliest.) For one error per construct this is exact. For two in the
same construct, it is exact as long as each moved check is given the
right firing point; the fuzzers and the S5 corpus are how we find out
(§4), and D3574 asks what to do with a difference they find.

## 4. The oracle and test plan

**The tool.** `stitchwort dev tree --lower PATHS`: for every `.sw` file,
parse by both routes (today's `parse_module_recovering`, and the lossless
tree then the lowering) and compare:

- the module, declaration by declaration, as `format!("{:#?}")` **with
  spans**: equal text means equal trees, spans, hidden names and tags.
  This needs no `PartialEq` on the 60-odd AST types, and the elaborator's
  view is exactly what is compared. (`equivalence::shape` already prints
  without spans; an `exact` beside it prints with them.) The comparison
  runs on a thread with a large stack, since `Debug` recurses and some
  files nest deeply;
- `namespace`, `imports`, `failed` and `doc_links` the same way;
- the diagnostics: `Diagnostic` derives `PartialEq`, so the two lists are
  compared directly (code, message, labels with spans, notes).

It prints the first difference per declaration (a few lines of each side
around it) and totals, and exits 1 on any difference. While the lowering is
partial, a declaration containing a kind it doesn't lower yet is counted
under that kind as **unsupported**, not as a failure; the per-kind counts
are the lanes' progress meter, and "0 unsupported" is the last gate.

**Single expressions.** The tool also takes every `Body` node that fits on
one line and parses its text with `parse_expression` both ways, so that
entry is compared over real code too.

**Corpus.** Every `.sw` file in the repo: 2,983 outside `target/` and
`.claude/` [measured], including the 920 `reject/` examples, whose
partial modules and errors are compared too (recovered declarations, the
`failed` names), and SW-3161's new `recover-*.sw` examples. `dev tree` over std, `aoc/src`, `games` and `examples`
alone covers 2,618 files and 27,578 declarations, 99 of which don't parse
and 5 files that don't lex [measured]: the error paths have some coverage,
not much.

**Half-typed code: SW-3161's S5 corpus.** The repo's files are almost all
correct, so they hardly test the gaps. S5's recovery corpus cuts each
declaration of a sample at every token, the way a declaration looks while
it is typed. The oracle runs both routes on each cut, with `--cuts`, and
compares the same things: the `Error`-node lowering, missing expressions
and their point spans, kept `let` names, incomplete matches, R6's
equation, and every diagnostic. The cuts are made at run time from the
repo's files, not committed. Declarations parse independently, so only
the cut declaration is parsed each time. Over the whole repo that is
about 27,600 declarations times their tokens: roughly 200 MB of parsing
per route, under a minute with the comparison [estimated: about 250
bytes and some 60 tokens per declaration, from the probe's totals]. That
is Overmind's run; a lane uses S5's sample. If recovery lands first, the
cuts are part of every gate from L1 on, for the kinds that lane lowers.

**Fuzzing.** `task fuzz:syntax` (100,000 cases) gets one more property:
both routes agree on every input. With S5's cuts, it is where
declarations with several errors come from, so it is the test of §3's
rule for errors. It runs on Overmind before step 4. S5's own invariant
("no errors exactly when the tree has no `Error` node and no missing
child") then holds for the lowering route too.

**Existing tests.** The parser's unit tests (`parser.rs` from line 6005)
call the public functions, so after the switch (L5) they test the
lowering route without change. `dev tree --spans` stays: after step 4 it
checks that every lowered span is a node.

**Who runs it.** The whole-repo run is parse-only: about 0.3 s of parsing
with the release binary, a few seconds in debug [estimated from the
probes]. Step 1's whole-repo gate ran on Overmind (SW-3170). D3575 asks
whether the lowering lanes may run it themselves, since it is their only
real test.

## 5. Stages

Each lane has its gate in the oracle. Hours [estimated].

| Lane | What | Gate | Model | Hours | After |
|---|---|---|---|---|---|
| L0 | **Scaffolding.** `lower` module, accessors, required slots, dispatch with "unsupported"; `dev tree --lower` with the exact comparison, diagnostics, per-kind counts, and `--cuts` over S5's corpus; the `Expression` root and `parse_tree` for expressions; the `Error`-node and absent-slot framework (`Expr::Missing` at the parent's end; the `Missing` span reason); `lex_recovering_with_trivia` on the tree route unless SW-3185 did it; marks under `Error` roots only if recovery hasn't landed. Lowers `namespace`, `import`, `test` and leaves (names, literals, `_`, `?`, `Type`) | Tool runs over the repo and the cuts; namespace, import and test declarations with leaf bodies equal; `dev tree --spans` unchanged | Opus | 6–7 | – |
| L1 | **Expressions.** `Paren`/`Bracketed`, `Unit`, unit calls, `App`, `NamedArg`, `FieldAccess`, `Binary` (flips), `Prefix` (`not`, `NegForm`), `Membership`, `Range`, `Pipe` (not into a section), `Arrow`, `Annotation`, `Iff`, `Chain`, `Interpolated`, `Tuple`, `List`/`Spread`, `Record`, `RecordField`, `CtorFields`, `Universe`, `Include`; gaps: R2 (inside brackets), R2b (stray closers), R1 after an operator or in a bracket | 0 unequal, on the files and the cuts; these kinds 0 unsupported | Opus | 7–9 | L0 |
| L2 | **Declarations.** `Def`/`Theorem`/`Instance` (signature, `Pi`s, equations, arm counts, defaults, `∀`), `Arms`/`Arm`/`Guard` at top level, `Decreasing`, `Unfolding`, `DataType`/`RecordType`/`Interface`/`TypeSynonym`, `Constructor`, `Fields`, `Field`, `Binder`, `Attributes`, `Ability`/`AbilityOp`, `FunctionType`, `Effect`/`Row`; R6 (the rest of a body: one equation with a missing body), or, if recovery hasn't landed, today's signatures with `body_error` | 0 unequal; reject examples' recovered declarations equal | Opus | 6–8 | L0 (parallel with L1) |
| L3 | **Binding and sections.** `Block` (statements, `LocalDefs` grouping), `Let`, `LetExpr`, `Seq`, `Lambda`/`LambdaParam` (pattern parameters), `Section`, `OperatorSection`, pipe into a section, `ClauseLambda`, `Forall`, `Exists`, `If`; gaps: R3 (a block's line, a broken `let`'s name kept), R1 in `let`, `if`, lambdas | as above | Opus | 7–9 | L1 |
| L4 | **Matching, proofs, patterns.** `Match`/`Scrutinee`, `Handle`/`HandlerClause`, `Reify`, `Induct`/`InductArm`, `Calc`/`CalcStep` (reversal), `Rewrite`/`RewriteRule`, `Omega`, `Ring`, `Cases`; all 11 pattern kinds; gaps: R4 (arms, incomplete matches), R5 (calc steps), R1 after `=>`, `with`, `in` | **Whole repo and the whole cut corpus: 0 unsupported, 0 unequal, diagnostics equal** (Overmind); expressions equal; `fuzz:syntax` with the agreement property clean on Overmind | Opus | 7–9 | L1 (parallel with L3) |
| L5 | **Switch.** The public functions (`parse_module*`, `parse_expression*`, `parse_tree`) go through the lowering; the direct route is kept only for the oracle (`parse_module_direct`, test-only) | Hash snapshots unchanged; the verifier's example kinds; both nesting benchmarks parse; performance-log entry (D3444) | Opus | 3–4 | L2, L3, L4 |
| L6 | **Step 4: delete direct construction.** Parsing functions return `Result<()>` or a small value; group B rewritten on marks and tokens; group C moved into the lowering with the rule for errors; the recovery points stop building `Missing`, error statements and incomplete matches (they only mark); `header` parking, `Stmt`, `LamParam`, `Param` values and `parse_module_direct` gone | Reject snapshots unchanged; parser unit tests; hash snapshots; nesting benchmarks; a last oracle run against L5's route on the fuzz and cut corpora before the old route is deleted | Opus | 6–8 | L5 plus a day of Overmind's rolling checks |
| L7 | **Tidy.** Docs (`tree.rs` and `ast.rs` headers, `docs/syntax.md`'s pointer for contributors on where to add syntax), `dev tree --time` timing the lowering, dead `Synthetic` reasons, the chain and pattern-`let` follow-up filed | Docs only, plus `dev tree --spans` | Sonnet | 2–3 | L6 |

Total 44–58 hours, against the architecture note's 33–52. The +4–5 over a design without gaps is SW-3161's S7 (its estimate +3–5), spread over L0, L1, L3 and L4 by construct family rather than made a lane of its own, so each family's gaps are lowered by the lane that knows the family.

**Order with SW-3161** (sequencing, the orchestrator's call). I agree with
SW-3161 that recovery (its S0–S3, and S5's corpus) goes first. Then the
lowering is written once, knowing about gaps, against a parser that
already builds them; the `body_error` path and the "marks under `Error`
roots" work are never written. Recovery and L0 can overlap: L0 touches
`tree.rs`, `lower/` and the CLI, recovery touches the parsing functions.
L1–L4 should start after S3, since each changes the same parsing
functions' neighbourhood and the gates need the gaps to exist. If
lowering has to go first, every lane's gap column is empty, and S7 is a
lane after L4 (3–5 h), before L5. Opus throughout
by D2506 (syntax); with the oracle as an exact test, L1 could try Sonnet
if the orchestrator wants the comparison.

**What step 4 touches.** Almost only `crates/syntax`: the parser loses its
values, the lowering gains group C. The public functions keep their
signatures, so the 26 files outside the crate that call them (in `elab`,
`driver`, `lsp`, `web`, `fmt`, `cli`, `bench`) don't change [source,
grep]. Two things outside do: `dev tree`'s modes (`--lower` goes, since
there is nothing left to compare with), and the formatter's safety check,
which compares `equivalence::shape` of the compiler's tree (it keeps
working; it could compare lossless trees instead, see Findings).

## 6. Performance

Measured over std, `aoc/src`, `games` and `examples` (2,618 files,
6.88 MB), best of 5, load about 5 [measured]:

| | Today's parse (compiler's tree only) | With marks, trivia and the lossless tree |
|---|---|---|
| Whole repo, 6.88 MB | 168–170 ms | 195.5 ms (+15%) |
| std, 2.12 MB | 55.1 ms | 64.8 ms (+18%) |

A one-line `stitchwort check` takes 0.20 s, and builds the library index
first, which parses all of std once per process
(`elab/src/library.rs:142`) [source]: so parsing is about a quarter of a
trivial check [measured parse, the share inferred].

Through the stages [estimated]:

- **L0–L4:** nothing changes for `check`: the lowering runs only in the
  tool.
- **L5 to L6:** the parser builds both the compiler's tree (unused) and
  the marks, and the lowering builds the compiler's tree again: about
  1.3–1.5× today's parse, std 70–80 ms, a check 15–25 ms slower. Hence L6
  straight after a short soak.
- **End state:** marks and the tree builder (part of the measured +15%,
  which also includes lexing trivia), then the lowering, which allocates
  what the parser allocates today, plus a walk. About 1.1–1.3× today:
  std 60–72 ms, a check 5–15 ms slower. If trivia turns out to be a
  noticeable part, the compiler's route can build the tree without
  comments, which only the formatter and the editor read [implementation
  choice for L5, decided by measuring].

The nesting benchmarks also count allocations; their counts will change at
L5 and L6, each with its performance-log entry. Speed work is paused
(D3465); this is a regression to record, not to optimise, unless it is
larger than estimated.

## 7. Risks

- **The tree lacks a distinction the compiler's tree has.** The span check
  shows every compiler span has a node, not that every node says enough.
  Candidates: spacing decisions (#24), the double wrap of a lambda's
  `(x: A)` (`LambdaParam` around `Param`, an SW-3167 finding), `Paren`
  versus `Bracketed`. Each is found by the oracle and fixed by marking
  more in the parser; that may touch the formatter, which reads the same
  kinds.
- **Span quirks.** Many spans are derived, some oddly (#5, #8, #13, #22).
  Reproducing them is fiddly but fully checked.
- **Error order** for constructs with two errors (§3, D3574).
- **Two designs moving at once.** SW-3161's recovery and this lowering
  both change the parser and the lossless tree. Recovery first (§5) keeps
  one of them still while the other is written; if they overlap, the
  parsing functions are where they conflict.
- **Deep nesting** in the lowering and in the oracle's `Debug` printing:
  the stack limit and a large-stack thread, with the benchmarks as gates.
- **`Error` nodes inside declarations** (SW-3161, or this note's marks
  under `Error` roots if lowering goes first) change the lossless tree of
  broken declarations; the formatter refuses such files, but the editor's
  readers of the tree need checking.
- **An absent slot read wrongly.** A missing part has no node, so a
  lowering function that finds a child's slot by position instead of by
  its introducing token could put a child in the wrong slot. The cut
  corpus exercises every slot of every kind, cut after each token.
- **Parallel lanes** L1/L2 and L3/L4 share the dispatch functions and the
  tool: small, mechanical conflicts.
- **The window between L5 and L6** is slower (§6) and has two routes in
  the code; keep it short.

## 8. What I did not check

- That the tree records everything the lowering needs: I read the node
  kinds and enough of the parser to list the shorthand, not every parsing
  function. The oracle is the real check.
- Every site in group B and group C: I found them by searching for code
  that matches on a built `Expr` or `Pattern` (`matches!`, `let … else`,
  helper calls), and the list may be short by a few.
- How the editor (`driver/src/live.rs`, `lsp`) uses the tree today, beyond
  the call counts; whether it parses a file twice now (once per tree) and
  could parse once in the end state.
- The parse timings are one probe each at a load of about 5; the
  end-state cost is an estimate from them, not measured.
- SW-3161's note was read after this one was drafted (it landed during
  the lane); its rules are folded into §2, §3, §4 and §5, but I didn't
  read its §4.2 (the checker's cascade suppression), which the lowering
  doesn't touch. The exact compiler nodes for gaps (the error statement's
  shape, the incomplete flag) will be whatever S1–S3 build; this note
  only requires the lowering to build the same.

## 9. Questions for Matt

**D3574: where two syntax errors sit in one construct (one line, one
arm), may the errors shown change, if every rejected example's text stays
the same?** *The problem:* the parser stops a construct at the first check
it reaches (and with SW-3161's recovery, keeps one error per line). After
step 4, a handful of checks (duplicate parameters, an or-pattern that
binds names, and four more) run in the lowering instead, built to give
the same errors as before; but with two errors in one construct, the
fuzzer or the cut corpus may find inputs where a different one of the two
is shown, or both. *The change:* if they do, accept the difference rather
than contort the lowering to match. *What it should do:* nothing for one
error per construct, which covers every example in the repo [source];
for two in one construct, which of them is shown may change. **[rec:
yes]**

*Decided (Matt, 14 Nov 2026): "I don't care about the ordering in which
every message is shown when."* Broader than asked: the order in which
errors are reported may change anywhere; only which errors appear, and
their text, are held. Reject snapshots whose only change is order are
re-blessed.

**D3575: may the lowering lanes run the parse-only oracle over the whole
repo themselves?** *The problem:* the lanes' only real test is "both
routes agree on every file", and the test budget keeps whole-repo runs
away from lanes. *The change:* allow lanes L1–L6 to run `dev tree --lower`
over every `.sw` file. It parses and compares, nothing else: about 0.3 s
of parsing in release, a few seconds in debug [estimated], one at a time,
`nice`d. *What it should do:* each lane knows it is done when it says so,
instead of waiting for Overmind; the machine load is a fraction of one
test binary. **[rec: yes, for this tool only]**

## Implementation choices made here

Labelled as mine, for the orchestrator to overrule:

- One lowering function per node kind (or family), recursive descent, in
  `crates/syntax/src/lower/`; the existing expansion helpers move there.
- The lowering reads, never parses: anything it would have to decide from
  tokens is marked by the parser instead; spacing decisions are recorded.
- No node identifier in the compiler's tree in steps 3–4; spans are the
  link, with an index built on demand when a tool needs one.
- An `Expression` root kind for single-expression parses.
- Gaps: an `Error` node lowers to the node the recovering parser builds
  there, without looking inside it; an absent slot, found by its
  introducing token, lowers to a missing expression at the parent's end.
- Marks of finished constructs kept under `Error` roots, and recovered
  signatures lowered from them, only if lowering goes before recovery.
- SW-3161's S7 spread over L0, L1, L3 and L4 by construct family; the
  cut corpus is part of the gates.
- The oracle compares `Debug` text with spans per declaration and
  `Diagnostic`s by equality; "unsupported" counted per kind.
- Group C checks move to the lowering with each check's firing point
  recorded, and the parser's rules for errors (file order, first per
  line, skipped text dropped) applied to the combined list.

## Findings worth tickets

- **The library index parses all of std in every process**
  (`elab/src/library.rs:142`, 55 ms of a 0.20 s trivial `check`
  [measured]). Caching the index, or parsing std's declarations lazily,
  would save most of it. Parked with the speed work (D3465).
- **`chain.rs` and `patlet.rs` undo expansions** the parser makes; after
  step 4, the lowering is the place to expand once, the way the
  elaborator wants. It changes trees and possibly hashes, so it is its own
  lane after L6 (migration cost doesn't count, D2303).
- **The formatter's safety check** prints and compares the compiler's
  tree (`fmt/src/printer/mod.rs:303–347`), 85% of `fmt`'s time by
  SW-3145's finding. Comparing lossless trees with layout taken out would
  be cheaper; worth filing if not already.
- **`lex_recovering_with_trivia` has no callers** outside the lexer: the
  lossless tree is missing for any file with a lexical error, so the
  editor's shape features vanish there. SW-3185, folded into SW-3161's
  S0, covers it; if S0 waits, using it in `parse_tree` is a small change
  on its own.
- **The elaborator recognises shorthand by markers** (`%section` names in
  `check.rs`, `dot.rs`, `queue.rs`; `MatchKind`; `NegForm`) to word its
  errors. After step 4 it could ask the lossless tree what was written,
  by span; not worth doing on its own.

## Appendix A: the probes

Main checkout's release binary, `target/release/stitchwort`, built
14 November 08:01, run with `nice -n 15`, load average 4–8:

```text
dev tree --time 5 crates/elab/src/std aoc/src games examples
  2618 files (0 not read back, 5 not lexed): 27578 declarations (99 not parsed),
  512946 nodes, 0 marks dropped
  6879928 bytes, best of 5: parse 169.9 ms, with the tree 195.5 ms
dev tree --time 5 --parse-only (same paths)
  2618 files, 6879928 bytes, best of 5: parse 167.8 ms
dev tree --time 5 crates/elab/src/std
  2119145 bytes, best of 5: parse 55.1 ms, with the tree 64.8 ms
dev tree --spans (same paths as the first)
  989469 spans checked, 0 not a node or a token; 578 in declarations that
  didn't parse; made up: 260 Empty, 100817 PartialApp, 355 Nested,
  2215 BlockRest, 44 Generated, 41 Added, 48 Attributes, 512 Exists,
  252 Chain, 976 Section, 509 Interpolation, 589 PatternMatch, 66135 Header
check t.sw   (one line, `def x: Nat := 1`), three runs: 0.20 s real each
```
