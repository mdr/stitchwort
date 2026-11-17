# The proved formatter, in slices: a de-risked plan (SW-3824)

Fable, 17 November 2026. Paper only. This note re-plans stages 4 to 8 of
[self-hosted-fmt.md](self-hosted-fmt.md) §8 around Matt's direction of
17 Nov 2026 (on the ticket): the aim is the full end-to-end proof; two
formatters in step for a while is fine; re-proving after a style change is
"the cost of doing business"; build it incrementally, so hidden
complexity shows early ("maybe we could do proofs about a cut-down
version of Stitchwort"); and put the foundations in first.

It stands on [the stage 3 sketch](../../tools/fmt-sketch/SKETCH.md)
(66 statements, 44 open, estimate 3,200–5,900 theorems), the toy's
measurements ([after-the-toy-proof.md](after-the-toy-proof.md),
`tools/toyfmt/NOTES.md`), and stage 1's and stage 2a's code.

How claims are marked: **[measured]**, **[source]** (read in the code or
a note, place given), **[run]** (a command I ran), **[checked]**
(`stitchwort check` accepted a probe in my scratch folder),
**[inferred]**, **[estimated]**.

## In plain words

**The problem.** The plan so far builds the whole formatter (stages 0–7),
then proves it (stage 8, 30–70 agent hours). Anything the proof needs of
the program (what the tree holds, how the parser spends fuel, what rule N
can say without columns) is found after the program is finished, and the
toy showed twice that such things are found late.

**The change.** Seven slices. Each is a real, working, fully proved
formatter for a subset of Stitchwort, cut out of the real tree, the real
parser and the real printer by a small yes/no function on the tree
("is this file within slice 1?"). Slice 1 is definitions whose bodies are
arithmetic-style expressions. Each later slice widens the function; the
lemmas already proved are about the real functions and stay. The five
riskiest statements of the sketch are each given to the earliest slice
that can settle them, or to a short spike before it. The foundations
(the layout engine in std, `match` and `cases` fixes, a std lemma batch)
go in before slice 1's proof lanes.

**What it should do.** After slice 1 (about 6–10 agent hours of proof
[estimated]) every layer of the proof has been through once at the real
lexer's and real rule N's size, four of the five risks are settled or
known to be trouble, and the theorems-per-hour and theorems-per-layer
figures are measured, not scaled from the toy. Each slice ends with a
checkpoint and stop rules, so a blind alley costs one slice at most.

**Three things found while planning** (each is in [§9](#9-found-on-the-way)):
stage 2a's tree keeps each token's column and "starts its line" in its
leaves, which the sketch says makes the top theorem false; the parser's
fuel may not be enough for deep nesting; and the checker already supports
the slice idea well (cases outside the slice are simply left out of a
proof).

## 1. Slices

### 1.1 How a cut-down language is set up (the crux)

Four ways, compared by what survives when the grammar grows:

| Option | What it is | What carries forward | Verdict |
|---|---|---|---|
| A. A small language of its own | its own tree, parser and printer, as Sprig | methods and rates only | done twice (the toy, Toy++); a third adds little |
| B. A grammar with switches | the real parser takes a record of flags (`lambdas`, `blocks`, …); theorems are about the parser with flags off | little: a lemma about `parse` with `blocks = False` says nothing with it `True`; the flags thread through 250 functions and cost time on every parse | no |
| C. **A subset of the real tree, picked by a function** | theorems are about the real `parse`, `tidy`, `print` and tree, with one more hypothesis: `file.within = True` | every lemma about a parser function, a rule, a pass step or one constructor; only the top inductions are re-assembled | **recommended** |
| D. The parser as it stands at each stage | stage 2a's parser refuses what 2b and 2c will add ("not parsed yet") | the same as C, but the refusing branches become real ones and their lemmas flip | C covers it: 2a's refusals are C's "outside the slice" |

**Option C in detail.**

1. **The slice is a `Bool` function on the real tree**, one per slice:
   `Expr.within1`, `SourceFile.within1`, with `| _ => False` for every
   constructor outside. A new constructor added to the tree later is
   outside every earlier slice with no edit.
2. **Proofs by cases over the tree write only the arms inside the
   slice.** With `within: e.within = True` in scope, the checker sees
   that the other arms can't happen and accepts the `match` without them
   [checked: probe below; `W-UNREACHABLE` says "the arm can be deleted"
   if one is written]. Widening the slice is adding arms.
3. **Every arm is a lemma of its own about one real constructor**, taking
   what is known of its parts as hypotheses (`spellsBinary`,
   `readsBackApp`), and the induction over the tree is a thin dispatcher
   that calls them. The dispatchers are the only proofs rewritten when a
   slice widens, and they are a line an arm. This is a rule for the proof
   lanes, not a nicety: the toy's five largest proofs hold 3,144 lines in
   monolithic inductions (`exprSpells` 1,010 lines; after-the-toy-proof.md
   §1 [measured]), and a 1,000-line induction can't grow by a constructor
   without being reopened.
4. **Text-side theorems (`format source = …`) need the parser never to
   leave the slice.** For that each slice has a token alphabet (a `Bool`
   on token kinds) and an entry `formatWithin`, which lexes, settles,
   refuses a source that uses a token outside the alphabet ("outside
   slice 1"), and otherwise runs the real `format`. In the walk over the
   parser's functions, "every token left is in the alphabet" is a
   `Parse.Invariant.every`, which std's `Gives` and `ReadsIn` already
   carry (`std/Parse/Reads.sw:73`, `Gives.sw:18` [source]), so a branch
   that starts with `match` or `{` is dead at the peek
   (`Parse.readsInPeek` hands the invariant to the continuation
   [source]). The lemma for a function that only calls others is stated
   for any invariant and is permanent; the handful of functions that
   dispatch on the next token (`exprInline`, `unary`, `atomBase`,
   `suffixes`, `bracketed`) get one lemma per branch, permanent, and a
   dispatcher lemma per slice.
5. **Each slice has a lemma that the one before is inside it**
   (`within1 → within2`), so earlier slices' top theorems stay true and
   run as regression checks. In the last slice `within` is `True` of
   every tree, the hypothesis is dropped, and `formatWithin` is `format`.
6. **"Done" for a slice is mechanical:** `stitchwort axioms` on the
   slice's top theorems lists no axiom and no open goal. It already
   prints the open goals a theorem depends on [run: on
   `Fmt.Sketch.Proofs.formatIdempotent`, 8 s].

The probe [checked, `stitchwort check`, release binary, scratch project
`p1`]: a five-constructor type; `within` true of two constructors; a
theorem by `match` with only those two arms and the hypothesis; a second
slice with a third constructor, whose proof reuses the first slice's arm
lemma unchanged and adds one arm; and `within → within2` by induction.
All accepted. A view type (`V` with `embed: V → E`, theorems about
`v.embed`) also checked, and is the fallback if a mutual family's
unreachable arms confuse the checker at the real tree's size (37
expression constructors, not five; not probed).

**What does not carry, to be honest about it:** the dispatchers; each
slice's `within`, alphabet and widening lemma (about 40 lines and 10
theorems a slice [estimated]); and any statement a later slice shows to
be wrong. The toy's boundary predicates moved twice (SKETCH.md §4), which
is what slice 1 is for.

### 1.2 The slices

Constructor names are stage 2a's (`tools/fmt/src/Syntax/Expr.sw` on
`lane/SW-3819`, not yet merged [source]). Comments are in every slice,
wherever a token of the slice can hold one; so are blank lines between
declarations.

| Slice | Grammar added | Needs from the build | Passes live | Risks it meets | Theorems [estimated] |
|---|---|---|---|---|---|
| **S1 Expressions** | below | 2a; the continued-line rule; the `Def` frame; engine; rules for 8 constructs | P2 | rule N (closers, commas, `->`), fuel, the stop rule for continued lines, spacing-sensitive `-` | 550–850 |
| **S2 Binders** | `Def` and `Theorem` headers with parameter groups, a theorem's `∀`; `Lambda`, `∀`/`∃` with `NameParam` and `TypedParam`; effect rows (`{Fail} T`); `PatternWord` | 2b's headers and types; the four passes | P1, P3, P4 | `standsAt`, P4's idempotence, P3 before P4, `meaning` | 500–800 |
| **S3 Layout core** | `Block`, `Let`, `Match` with arms, `If` with block branches, a `then` that ends its line | 2c's blocks | — | `readsBack` by column; rule N's bar and expression-`let` clauses | 500–900 |
| **S4 Inline breadth and text** | the rest of 2a: records, field access, sections, chains, ranges, pipes, `Seq`, named arguments, annotations, the pattern family, clause lambdas; text literals, `${…}`, `"""` blocks | engine `Verbatim` | P2's other brackets | `Lexical` for text (sketch risk 7) | 600–900 |
| **S5 Declarations** | every declaration kind, attributes, imports, `decreasing`, `unfolding` | 2b complete | P2 (`Attributes`, `Import`, `Fields`, `RewriteRules`) | breadth; the rate | 700–1,100 |
| **S6 Rest of layout** | handlers, `calc`, `rewrite`, `cases`, `match induct`, local definitions | 2c complete | — | breadth on column-sensitive forms | 500–900 |
| **S7 Whole** | nothing: `within` is `True`; the three lowering refusals; `Degenerate`; the file loop | stage 7 | — | — | 100–200 |

The sum, 3,450–5,650, is the sketch's 3,200–5,900 split by where each
layer's fixed and per-construct costs fall. S3 comes before S4 and S5
because it carries a named risk and they carry only size; if 2c's parser
is late, S4 or S5 moves ahead of S3 with nothing lost.

**S1's grammar, exactly:**

```
File  ::= Def* comments-at-end
Def   ::= "def" name ":" Expr ":=" Expr        no attributes, no parameters
Expr  ::= Word                                  a name (plain or qualified) or a numeral
        | Paren      "(" Expr ")"
        | Tuple      "(" Expr ("," Expr)+ [","] ")"
        | ListOf     "[" [ Expr ("," Expr)* [","] ] "]"       no spread
        | App        Expr Expr+
        | Binary     Expr operator Expr         every operator 2a builds as `Binary`
        | Prefix     ("-" | "!") Expr
        | ArrowType  Expr "→" Expr
```

Token alphabet: `def`, names, numerals, `:`, `:=`, `(`, `)`, `[`, `]`,
`,`, the `Binary` operators, `-`, `!`, `→` and `->`. A body may run over
several lines (below); there is no `Block`. Eight of the 37 expression
constructors and one declaration form.

Why these eight: `Paren`, `Tuple` and `ListOf` bring closers and commas,
so rule N's first two clauses and P2 are live and `printedSettle` is met
at once; `Prefix` brings the one place where spacing decides the tree
(`glued`, `afterOperand` in 2a's `Item`; the toy's `- -x` bug);
`ArrowType` brings rule N's `->` clause and lets a result type be more
than a name; `App` and `Binary` are the precedence ladder, which is most
of the parser's recursion and so of `fuelEnough`.

**Does S1 reuse what stage 2a is building? Yes, with three changes**
[source: `lane/SW-3819`'s working tree at 15:30]:

- 2a's parser has every function S1 needs (`expression`, the ladder from
  `operatorExpr` to `atom`, `parenAtom`, `bracketed`, `listExpr`,
  `commaList`), on `Parse.recursiveWith`, never backing up.
- **Change 1: the leaf.** 2a's constructors hold `Leaf`s, and a `Leaf` is
  `{ token: { kind, text, column, lineStart }, trivia }` with a column on
  each comment and a count of blank lines. The sketch's §1 items 1 and 2
  say why that can't be the tree the theorems are about: the printer
  chooses columns, so `parse (print t) = Ok t` is false of every
  reformatted file. 2a also keeps each comma as a `Leaf` (`Sep`), against
  item 3. See [§9](#9-found-on-the-way).
- **Change 2: continued lines.** 2a refuses a token that starts a later
  line ("not parsed yet: a block or a continued line"). The printer
  breaks long expressions, so S1 needs the Rust rule: a line that starts
  right of the limit continues the expression; one at the limit ends it,
  unless it starts with an operator that can't begin an expression
  (`parser.rs:631–688` [source]). The tree doesn't depend on which
  [run: `dev tree --print` gives the same `Binary` for `def x: Nat := f a
  + (b * c)` on one line, with the body on a deeper line, and with `+`
  starting a line at the body's column; two operands at the same column
  give a `Block`]. That is the whole of layout in S1, and it is the
  mechanism S3's blocks are built on.
- **Change 3: the `Def` frame** (`def name: T := e`) from 2b, which a
  slice needs to be a file at all. `def x := e` without a type doesn't
  parse [run].

### 1.3 Build and proof go slice by slice

§8 builds stages 4–7 whole and proves last. Here each slice has four
steps, the first three short:

1. **Program:** the traversal, passes, rules and spacing for the slice's
   constructs, on the real engine. Gate: the harness, on every
   declaration `within` the slice, byte for byte against Rust (stage 5's
   gate, "every declaration using only those constructs", with `within`
   as the filter).
2. **Sketch:** the slice's predicates written out (`Shaped`, `Settled`,
   `Lexical`, `Spells`, `Printed`), every layer's statements open,
   `check --counterexamples` on each statement about written code
   (SW-3823). The top theorems proved from the open ones. A count per
   layer: the prediction the checkpoint is measured against.
3. **Spikes** due before this slice's lanes ([§2](#2-spikes)).
4. **Proof lanes**, by layer, side by side.

The build stages (2b, 2c, the rest of 4–6) carry on ahead on their own
track; a slice only needs its own constructs built. What changes is the
order inside stages 4–6: rules for S1's constructs first, then S2's.

## 2. Spikes

Ordered by when they run. Times are agent minutes [estimated from
similar past lanes: the sketch lanes took 21 and about 60].

| # | Risk (sketch §7) | Spike | When | Box | A blind alley looks like | Settled by |
|---|---|---|---|---|---|---|
| K1 | `printedSettle`: can `Settled` be said of a tree with no columns? | With stage 1's code only: take settled leaves from the corpus and the fuzzer, write them back out two ways (every break the comments don't forbid; only the breaks they force), lex and settle each, compare with columns removed. Then write `Settled` for all five clauses on the layout-free leaf and search it | now | 45 | a pair that differs after settling and that no rule of the Rust printer excludes: the tree then needs a flag, or rule N a change (Matt's, since it moves comments) | S1 for closers, commas, `->`; S3 for the bar and `let` |
| K4 | `fuelEnough` | Count, on 2a's parser, the most `self` calls between two tokens read; test `((((…))))`, nested sections and nested lambdas 200 deep through `fmt-twin --stage tree` | now, on 2a | 30 | a refusal "called itself without reading anything" on a valid file, or a count above 1: then `recursiveWith`'s fuel must be a multiple of the items left, or the ladder re-cut | S1 |
| K3a | `readsBack` by column, first half | S1's continued-line rule: state "every line after the first starts right of the limit, or with an infix-only operator at it" as a predicate on printed leaves and prove the read-back for `Binary` and `App` first of S1's lanes | first lane of S1 | 60 | the predicate needs the engine's actual columns, not "right of the limit" | S1 |
| K2 | `Expr.standsAt` against the trial parse | Write `standsAt` on 2b's tree; a harness stage comparing P3's output with Rust's on the corpus, the fuzzer and D2307's cases | when 2b merges | 60 | over about 60 lines, or it needs the precedence ladder again, or a mismatch no class of constructs explains. Fallback: P3 keeps the trial parse and `bracketsKeepParsed` is proved from the trial's success | S2 |
| K5 | P4's idempotence hypothesis | Write `mergeGroups` and `isMerged: Bool`; search `mergeGroups (mergeGroups g) = mergeGroups g` and `Settles tidySteps` for the three binder kinds | with K2 | 30 | a counterexample to "merging uncovers no new merge", or a merge that exposes a bracket P3 would drop: then idempotence is proved by "the traversal reaches `isMerged`", sketch risk 5's second form | S2 |
| K3b | `readsBack` by column, second half | On 2c's parser: state what may follow a block (`After`, `BlockEnds`) for `Block`, match arms and a line-ending `then` | when 2c merges | 60 | more than about three "what may follow" predicates, or one that depends on the printer's width | S3 |

K1 and K4 need nothing that isn't in the tree today (K4 needs 2a's
branch). A small slice settles four of the five: `printedSettle` in part
(S1), `fuelEnough` (S1), the first half of column read-back (S1), and
with S2 `standsAt` and P4's hypothesis. Only block read-back waits for
S3.

K4's concern, spelled out [inferred, not run]: `Parse.recursiveWith`
starts with fuel "items left + 1" and spends one unit each time the
parser calls itself (`std/Parse/Parse.sw:706–721` [source]). 2a's
expression parser calls itself by `Goal`, a ladder level, so a call
need not have read a token since the call before it; I did not trace
which do. A pair of brackets is two items, so two calls a nesting level
fit and three don't. The toy needed its own induction here
(`runsExpressionFuel`).

## 3. Foundations

In the order they should start, so S1's proof lanes have them. "Saves" is
against the sketch's estimate unless it says otherwise. Sizes are agent
minutes [estimated].

| # | Foundation | Evidence | Saves | Size |
|---|---|---|---|---|
| F1 | **The proof tree, in stage 2 now**: leaves without layout; commas as a flag; the traversal with the tree; `Parsed`'s parts as records | [§9](#9-found-on-the-way); sketch §1. The toy's boundary moved twice | every statement in every layer is about this type; changing it after 2b and 2c is three parser files, not one | 40, Opus, before 2b builds on 2a |
| F2 | **`Std.Doc`**: SW-3452 (`fits` from the new line), SW-3416 (cached `forcesBreak`), a list of what `engine.rs` (1,038 lines) does that the toy's `Doc` (392) doesn't, then the move with its 302 theorems | the engine is the one layer already proved; both tickets are in the backlog and are prerequisites (self-hosted-fmt.md §3.6) | 302 theorems never proved again; 40–80 new. S1's printer needs it | 60 + 40 + 30 + 60 |
| F3 | **`match` refinement**, the rest of match-refinement.md's S3–S6 (SW-3761, SW-3762) | 16 of the toy's 87 friction points; "the largest single source of lost rounds"; 26 type errors in one proof; about 50 `(rewrite e then fine)` in T1c | unmeasured in theorems; it is rounds per lemma. Check after S1 | 60–90 each, Opus |
| F4 | **`cases`**: on a hypothesis (SW-3461); the ten-character budget (SW-3459); closing the computed arms of a `match a, b` (SW-3748) | the toy's lexer layer (153 theorems) "is mostly this"; T6: four of five arms closed by computing, about 30 lines a lemma, 57 lemmas | the lexer layer here is 1.9 times the toy's; P4 about 85 lemmas | 40 each, Sonnet |
| F5 | **Loops with fuel in std `Parse`**: one combinator for "repeat while a test on the items left holds", with its `Gives`, `ReadsIn` and `Runs` lemmas | 2a has 21 hand-fuelled loops among its 170 functions (`arguments`, `commaList`, `chainLinks`, `suffixes`, … [measured: `grep -c '(fuel: Nat)'`]); in the toy each such loop's unreachable `Zero` case needed its own argument (T1c) | about a lemma a loop in each of three layers: 60 or so | 60, Sonnet; then 2a's loops moved onto it |
| F6 | **Std lemma batch 1**, for S1: lists (`All`, `append`, `reverse` and `snoc` for rule N's newest-first lists, `take`/`drop`, `last`), folds (an invariant lemma for the fold `assemble` is), `Text` (`repeat`, joining, length of a slice), character classes as decisions | only 17 of the toy's 1,262 theorems were std-only, and a std lemma cost a proof lane about 4 minutes of tests for three theorems (friction 70); SW-3454, SW-3457, SW-3476, SW-3653 filed from T1c | proof lanes stop to add std lemmas less often; later batches come from each slice's "std wants" list | 60, Sonnet, 40–60 lemmas |
| F7 | **Errors**: no warnings from a file that doesn't parse (2,242 from one bracket, frictions 76, 81); a name clash across `(..)` imports reported once, at the definition (34 errors, T3); `W-MATCH-NOT-FOUND` once per cause (10 for one wrong name, T5); a failing `test` shows both sides (stage 1) | each named in a friction list; "every error in the last two lanes was a bracket or a name clash" (friction 86) | rounds, not theorems | 20–40 each, DeepSeek or Sonnet; check which are already fixed first |
| F8 | **`rewrite repeatedly`**: rule sets for lists and for the engine's words in std; stage 3 (`↔`); the rollout (SW-3631) | Words.sw −15% proof characters [measured]; T6: one call closed six re-associations; simp-revisited.md estimates 22–29% on the engine slice | best case is the passes (250–450 lemmas) | stage 3: 240 + 60 as planned there; sets: 40 |
| F9 | **Induction over the tree**: confirm `Expr.induct`, `inductMem` and `size` generate for 2a's mutual family and time them; a traversal-keeps-P lemma schema | every traversal of children needs a helper per list (SW-3359, deferred by D3611); T6 ran at 57 lemmas against 25 because "the estimate counted statements, not the list helpers" | measured in S1: if list helpers are over a fifth of S1's theorems, reopening D3611 is worth a question to Matt | 20 to probe in S1's sketch |
| F10 | **Equations for definitions that perform abilities** (SW-3443) | the toy reshaped programs for their proofs (eight helper `def`s in part 2 alone); the real parser is written to mirror Rust, not to be proved | try three 2a functions in S1's sketch (`addExpr`, `suffixes`, `commaList`); build it only if they need reshaping | 90, Opus, if needed |
| F11 | **Check time and layout**: time `check` on the toy (1,741 theorems) once; keep the proofs in small namespaces beside each file | a lane may check only the namespace it edits (CLAUDE.md), and a project of 5,000 theorems is unmeasured (§8's risks) | lanes never need a whole-project check | one verifier job; a paragraph in the brief |
| F12 | **Proving-guide section**: slices, arm lemmas, dispatchers, statements as records, `axioms` for "done" | §1.1 | each lane's brief points at it | 20, Sonnet |

F1 and F2 gate S1. F3–F7 should be in before S1's proof lanes and
otherwise run beside them. F8–F10 are measured in S1 and decided at its
checkpoint.

What already exists and needs nothing: the parser-proof library (`Gives`,
`ReadsIn`, invariants, peek lemmas, declines, a `runsRecursiveWith` whose step may
assume a fact about the nested parser;
`std/Parse/*.sw`, 410 theorems [measured: `grep -c '^theorem'`]), proof
tuples (SW-3566), `Prop` records (`Parse.Fits`), `rewrite repeatedly`
stages 1 and 2, and the open-goal listing in `axioms`.

## 4. Checkpoints and stop rules

**Measured at the end of each slice**, by the lane that closes it, in
`tools/fmt/NOTES.md`:

- theorems per layer, against the slice's sketch count (step 2 of §1.3);
- lane minutes, and theorems per agent hour (the toy: 80–110);
- lines per theorem (the toy: median 11, mean 19) and the five longest
  proofs;
- the share of theorems that are list helpers, dispatchers, and slice
  bookkeeping;
- `check` time for the project;
- the harness score for declarations within the slice;
- the top five frictions, each with a ticket.

**Rules.**

| Reading | Action |
|---|---|
| Overall count within 1.5 times the sketch's, rate 60 an hour or more | carry on |
| One layer over 2 times its count | that layer is re-sketched for the next slice before its lanes start (one paper lane). T3's rule N ran at 2.4, so one layer doing this is expected once |
| Overall count over 2 times, or rate under 40 an hour over the slice, or two layers over 2 times | stop; a rethink note to Matt with options |
| A spike shows its blind-alley signal | the slice that depends on it doesn't start; a design note first |
| The total, projected from the slices so far, passes 9,000 theorems or 110 agent hours (1.5 times the sketch's top) | a question to Matt: carry on, cut the must set, or stop at the slices proved |
| A lane reaches 1.5 times its time estimate | it stops and reports, as CLAUDE.md says |

**What Matt sees at each checkpoint**, one screen:

1. what is now proved, in a sentence ("any file of definitions whose
   bodies are operator expressions formats to the same program, the same
   output second time, every comment kept; no open goals");
2. how much of real code that is: declarations in the repo within the
   slice, and the harness score on them;
3. the table of predicted against actual per layer, the rate, and the
   projected total;
4. which risks are now settled, and which stop rule, if any, fired;
5. the next slice, its estimate, and at most one decision.

## 5. Style changes and the Rust formatter

**Decided (D3677, Matt, 17 Nov 2026):** while the two formatters are built
and proved, keep changes to the Rust formatter to a minimum, except for
bugs. A bug the proofs uncover in the Stitchwort formatter is fixed there,
and in the Rust formatter too when it has the same bug, so the two stay in
step: "we should also correct the Rust formatter as well if it has the
same bug ... we should minimize changes to the Rust formatter during this
process unless we find bugs." Every such fix carries a test on both sides.

**When the rules are proved.** Per slice, with everything else:
self-hosted-fmt.md §7.4 put the rules layer last because the style moves;
Matt's "cost of doing business" lifts that, and proving S1's eight rules
early is how the largest and least certain layer (700–2,000 lemmas, the
whole spread of the estimate) gets a measured rate. By the end of S3
about a third of the rule functions are proved [estimated]; S5 and S6
hold most of the rest.

**What a style change costs.** A rule's words, joins and events lemmas,
and the spelling of its construct; nothing in the passes, `meaning`, the
parser or the engine (§7.5). With arm lemmas (§1.1, item 3) that is the
lemmas of one arm in three files. The first real one after S1 is timed
and recorded, so the price is a number.

**How one lands in both.**

1. Until the Stitchwort formatter replaces `stitchwort fmt` (decided
   after stage 7, self-hosted-fmt.md Q3), the Rust formatter leads. A
   style lane changes Rust as today, with no gate.
2. Overmind's rolling check runs the harness and reports drift, by
   construct.
3. Drift inside a proved slice becomes a "follow" ticket: the Stitchwort
   rule and its lemmas change in one lane and merge together. The proof
   project is never merged with a proved theorem reopened; until the
   follow lane lands, the Stitchwort formatter is behind and the drift
   list says where.
4. Follow tickets are batched: at most one lane a few days, unless a
   slice's lanes are about to touch the same rule.
5. Drift outside the proved slices costs only the port.
6. A change to the engine or to rule N is the expensive kind (every
   slice's `printedSettle`), and is flagged when it is proposed, not when
   it drifts.

## 6. The pending decision on `meaning`

The sketch found §3.4's table too generous: it forgets every comment-free
bracket pair, but the compiler reads the pair round an application's head
(`(f) x` [run, SW-3820]). The sketch's `meaning` forgets a pair only in
the two places P3 drops one. The rule it proposes: **`meaning` forgets
exactly what a pass changes, where the pass changes it.**

- **When it is needed:** before S2's sketch. S2 is the first slice where
  the two readings differ (P3's two slots, P4's groups, P1's `∀`), and
  where `meaning` gets its Opus review (D3643).
- **Does S1 settle it? No.** In S1 the only live pass is P2, and both
  readings forget a trailing comma. S1 does fix `meaning`'s frame: the
  traversal, the `Meaning` wrapper, the comma flag, and
  `traverseKeepsMeaning` as one generic lemma.
- **Recommendation: the narrow rule.** It is the safe direction for a
  trusted definition, and the wide one is false as §3.4 states it. Its
  price: a later pass that drops more (spare brackets by precedence, as
  Toy++'s P3 did) widens `meaning` and needs the review again.

## 7. Tickets

Estimates are agent minutes, set from similar past lanes' actual times,
not scaled-down human ones.

**Now (nothing blocks them):**

| # | Title | Model | Est. |
|---|---|---|---|
| 1 | Stage 2 tree for the proofs (F1): leaves hold text and comments only, commas a flag, on 2a's branch or straight after it merges; 2b and 2c briefed to match; sketch §1's fifteen items checked off | Opus | 40 |
| 2 | Spike K1: rule N re-layout search on stage 1's code; `Settled` written on the layout-free leaf | Fable | 45 |
| 3 | Spike K4: `self` calls per token in 2a's parser; deep-nesting tests | Opus | 30 |
| 4 | SW-3452, then SW-3416, on the toy's engine | Opus, Sonnet | 60, 40 |
| 5 | Engine gap list: `engine.rs` against `Toy.Doc`; then `Toy.Doc` and its theory to `Std.Doc` | Opus (list, 30), Sonnet (move, 60) | 90 |
| 6 | match-refinement S4 + S6 (SW-3761), S5 (SW-3762) | Opus, Sonnet | 90, 50 |
| 7 | `cases` trio: SW-3461, SW-3459, SW-3748 | Sonnet | 3 × 40 |
| 8 | Std `Parse`: a fuelled-loop combinator with lemmas (F5) | Sonnet | 60 |
| 9 | Std lemma batch 1 (F6) | Sonnet | 60 |
| 10 | Error fixes of F7, after checking which are done | DeepSeek | 4 × 30 |
| 11 | Proving guide: slices and arm lemmas (F12); SW-3823 with it | Sonnet | 20 |

**Slice 1 (after 1, 4, 5 and 2a):**

| # | Title | Model | Est. |
|---|---|---|---|
| 12 | S1 program: continued lines in the parser, the `Def` frame, traversal and P2, rules and spacing for S1's constructs on `Std.Doc`, `within1`, the alphabet, `formatWithin`, the harness filter | Opus | 90 |
| 13 | S1 sketch: predicates written out, statements per layer, counterexample search, counts; probes for F9 and F10 | Fable | 60 |
| 14 | S1 lexer layer for the alphabet (`lexCovers`, token read-back) | Sonnet | 90 |
| 15 | S1 rule N: the six `settled…` statements, `printedSettle` for closers, commas, `->` | Fable | 120 |
| 16 | S1 parser: one joint walk and the carry, about 25 functions; `fuelEnough` | Sonnet | 90 |
| 17 | S1 read-back, K3a first | Opus | 90 |
| 18 | S1 rules and spelling | Opus | 120 |
| 19 | S1 passes: the generic traversal lemmas, P2 | Sonnet | 60 |
| 20 | S1 glue, `axioms` clean, the checkpoint report | Opus | 45 |

About 13 hours estimated for 12–20; the toy's lanes ran at 0.45 of theirs.

**Later, one line each until S1's checkpoint re-estimates them:** K2 and
K5 with stage 4's passes (Opus, 90); S2 as 12–20 (the `meaning` review
with it); K3b (Fable, 60); S3; S4; S5; S6; S7; `rewrite repeatedly`
stage 3 and std rule sets (Opus 240 + review 60; Sonnet 40); SW-3443 if
S1 calls for it (Opus, 90).

## 8. Decisions for Matt

Two. The orchestrator numbers them.

**Q1. Build and prove in slices, so the rules for each slice are proved
with it, not last?** [rec: yes] **Decided: yes (D3676, Matt, 17 Nov
2026: "Yes, I think so. Agree with that.")**
*The problem:* §8 proves the rules last because the style moves; that
also leaves the least certain layer unmeasured until the end.
*The change:* §1.3: each slice is built, sketched and proved end to end;
a style change inside a proved slice is followed with its proofs (§5).
*What it should do:* by slice 1's checkpoint, measured rates for every
layer; from then on, each style change to a proved construct costs a
follow lane, which is recorded.

**Q2. `meaning` forgets exactly what a pass changes, where it changes
it?** [rec: yes; needed before slice 2's sketch, not before slice 1]
See §6.

Decided here as implementation (say if you disagree): the slice as a
`Bool` function on the real tree with an alphabet-gated entry; arm lemmas
and thin dispatchers; S3 before S4 and S5; the stop-rule thresholds.

## 9. Found on the way

- **Stage 2a's tree keeps layout in its leaves** [source:
  `lane/SW-3819`, `Syntax/Tree.sw` and `Syntax/Expr.sw`, uncommitted at
  15:30]. `Leaf` is the lexer's token with `column` and `lineStart`, and
  trivia with comment columns and a blank-line count; commas are `Leaf`s
  in `Sep`. The sketch's §1 (items 1, 2, 3) says each makes `printParses`
  false or adds a freedom nothing reproduces. The dump needs only the
  token's text. The sketch merged while 2a was already running, so its
  brief may not have had §1. The parser can keep reading `Item`s that
  carry the layout and build nodes that don't. Cheapest fixed now
  (ticket 1).
- **Fuel** (K4): `recursiveWith` gives "items left + 1" and 2a's ladder
  calls itself by level; whether any valid nesting spends more was not
  run.
- **A `def` needs a result type** [run]; so S1's frame has a type, and
  types are expressions.
- **The checker leaves out-of-slice arms out for you** [checked]; the
  note "the arm can be deleted" is exactly right.
- **Not checked:** whether the formatter keeps `->` as written or writes
  `→` (sketch item 12); which of F7's error fixes are already in; that
  `Expr.induct` generates for 37 constructors; the operator list in S1's
  `Binary`. Each is in a ticket above.

## 10. Spike K1's findings (SW-3825)

Fable, 17 November 2026, 25 minutes of the 45.

**Verdict: (a), layout-free, with one family left out that needs a
decision.** The tree needs no flag. `Settled` is `homed`
(`tools/fmt-sketch/src/Settled.sw`): a closer or a record update's `|`
has a trailing comment only when it has own-line comments above it, or
the code before it ends with a comment, looking back past closers,
commas and bars. The sketch's reading ("the token before it has a
trailing comment") was too narrow.

Rule N's result does depend on the source's line breaks, in the Rust
rule as in stage 1's: `g (h (x -- a⏎)⏎) -- b` leaves `b` on the second
`)`, and with the two closers on one line on the first. That is not the
blind-alley signal, because both results are `homed`, the tree says
which closer holds the comment, and the printer starts a line there
(Rust prints `(h (x) -- a⏎) -- b` for one and `(x -- a⏎)) -- b` for the
other; each reads back as itself). So `printedSettle` has two halves,
both stated in `tools/fmt-sketch/src`:

- `SettledProofs.settledAnyLayout` (rule N's half): settled leaves,
  written out in any layout that starts a line at each closer or bar
  holding a comment, with each trailing comment after the closers and
  commas that follow its token, settle to themselves.
- `Proofs.printedKeeping` (the printer's half): the printed leaves are
  such a layout of leaves that spell the tree.

with `SettledProofs.settledHomed` for `parseSettled`. All three ask for
`plain` leaves: four conditions on token kinds, three of them true of
every file that parses [inferred from the grammar, not checked against
the parser].

**Evidence.**

| What | Cases | Result |
|---|---|---|
| Real text, three layouts (a line a token; breaks only where comments force them; the printer's), stage 1's lexer and rule N (`Fmt.Sketch.Relay`): goldens, cached fuzzer cases, every eighth repo file | 836 files, 6,012 comments | all the same, but no comment kept on a closer or bar: these say nothing about the limits |
| The same on those files with comments added and lines broken before closers and commas (a throwaway script) | 533 files, 23,503 comments, 854 kept on a closer or bar | printer's layout 533 same; a line a token 533 same; forced breaks only: 40 differ |
| `stitchwort dev tokens` on each of those texts | 1,599 | Rust agrees with stage 1 on every one, so the 40 are real dependence on line breaks, not artefacts |
| Random token sequences of 2 to 9 over 13 kinds, with comments and breaks (`Fmt.Sketch.Search`) | 2,400,000; 1,942,953 `plain`; 614,437 with a comment kept | `plain`: 0 not `homed`, 0 moved in a keeping layout, 0 not idempotent; 25,790 move when the holder need not start its line |
| The same, not `plain` | 457,047 | 1,545 fail all three |
| `check --counterexamples` on the four statements | 10,000 each | none found (weak: it also found none for statements the search above shows false) |

[measured: Speedwell; the search natively at about 16,000 cases a second.]

**The family left out: a trailing comma that starts the closer's
line.** `g ([⏎1⏎-- above⏎, ] -- b⏎) -- c` parses. Rule 1 stops `b` on
the comma (it starts its line and has a comment above), `c` stays on
`)` because the line before now ends with a comment, and rule 2 then
moves the comma's comments above `]`. The result is not `homed` and
rule N is not idempotent on it: applied again, `c` moves to `1`, past
the two comments above `]`. Rust's rule does the same (`dev tokens`).
The Rust formatter still gives a stable answer, `-- above⏎] -- b⏎) --
c`, because its P2 deletes the comma from the text and rule N runs
again on what is left; `passes.rs`'s note that deleting the comma
"leaves every comment on the token it belongs to" is not true here.
The self-hosted order (rule N once, then P2 on the tree) would print
something else, so the twin harness would differ from stage 4 on.

What would change, one of:

1. **Take the last commas out before rule N** (`Settled.withoutLastCommas`,
   `Lexed.settledBare`), which is what Rust does in effect. Searched:
   320,000 cases, 271,472 grammatical, 0 failures of the three
   statements, and it gives Rust's answer on the case above. P2 then
   needs to know a comma bracket from the leaves alone, or the parser
   runs before rule N for this.
2. **Change rule 1** so a comment never stops on a comma, in both
   formatters. Matt's, since it moves comments. A first try (stop on
   the leaf after the comma) failed the search: 897 of 276,347 not
   idempotent.
3. **Leave it out**: `parseSettled` takes a hypothesis and the
   formatter refuses such a file, or the run-time check stays for it.

S1 doesn't wait for this: its statements carry `plain` either way. The
decision is needed before S1's `parseSettled` lane.

**Kept:** `tools/fmt-sketch/src/Settled.sw` (the predicate, the layouts,
the candidate), `SettledProofs.sw` (the statements), `SettledTests.sw`
(four tests on real text), `Relay.sw` and `Search.sw` (the two
programs: `stitchwort build --native Fmt.Sketch.Search.main -o search`,
then `search --count 500000 --seed 1`, and `--candidate`).

## Sources

`tools/fmt-sketch/SKETCH.md` and `src/`; self-hosted-fmt.md §3.4, §7,
§8; after-the-toy-proof.md §1, §2, §5; `tools/toyfmt/NOTES.md`
("Toy++ closed": timing, counts by layer, friction by stage, what
carries); `docs/reviews/SW-3414-toy-formatter-report.md` §2, §4;
parse-proof-library.md; simp-revisited.md (stages, "As built");
match-refinement.md §7; `tools/fmt/NOTES.md` (stage 1);
`docs/proving-guide.md` §3; `crates/elab/src/std/Parse/`;
`crates/syntax/src/parser.rs:265, 631–688, 2218–2239`; stage 2a's working
tree on `lane/SW-3819`. Not read in full: the toy's proof files, its
`SKETCH.md` and `plus/SKETCH-PLUS.md` (used through NOTES.md's summaries
and the stage 3 sketch), and simp-revisited.md §2–§7.
