# The self-hosted formatter's engine: from `Toy.Doc` to `Std.Doc` (SW-3902)

Opus, 17 November 2026. Paper only. This is foundation F2 of
[self-hosted-fmt-proof-plan.md](self-hosted-fmt-proof-plan.md) §3 and the
engine half of stage 5 of [self-hosted-fmt.md](self-hosted-fmt.md) §8. It
compares the Rust engine with the toy's, says which way each difference
goes, plans the move of the toy's 302 theorems, settles SW-3884 (a
comment-free `meaning`), and stages the work.

Claims are marked as in the proof plan: **[source]** (read in the code,
place given), **[run]** (a command I ran with the main checkout's
binary), **[inferred]**, **[estimated]**.

## In plain words

**The problem.** The Stitchwort formatter must print byte for byte what
the Rust one prints, and its proof needs a proved layout engine. The
toy's engine (`Toy.Doc`, 392 lines of program, 302 theorems) is proved
but does about half of what the Rust engine (`engine.rs`, 1,038 lines)
does, and in four places it deliberately or accidentally behaves
differently.

**The change.** Port the rest of the Rust engine onto the toy's, with a
harness that checks the engine alone: Rust writes out each declaration's
layout document, the Stitchwort engine prints it, and the two texts are
compared, before any formatting rule is ported. Four measuring bugs in
the Rust engine (it predicts a line break differently from how it then
prints) are fixed in Rust first, as bugs under D3677. The proofs follow
the program feature by feature, and the engine moves into the standard
library once every proof is closed.

**What it should do.** The engine identical to Rust's on every
declaration of the goldens and the repo after about 2 agent hours
[estimated], with no formatting rule ported yet; its proof closed about
2–3 agent hours later [estimated], about 450 theorems in all (302
carried, 140–180 new [estimated]). Stage 5's top theorem gets
"the same program" by congruence, with no lemma, from a blanking map
(SW-3884, option (b)).

## 1. What the Rust engine does that `Toy.Doc` doesn't

Read from `crates/fmt/src/printer/engine.rs` (the whole engine: the
`Doc` type, the printer, `fits_in`, `fits_flat`, `shift_lines`) and its
callers, `printer/mod.rs` (`WIDTH = 120`, one `print` per declaration,
line 193) and `printer/rules.rs` (the only other use of the engine is
`balanced_fill`, line 82, which prints each item flat to measure it)
[source]. `spacing.rs`, `tidy.rs` and `passes.rs` don't touch the
engine.

"Needed" means needed for byte identity with Rust's output; "where"
names the Rust rules that build it (`rules.rs` line) and the proof
plan's slice that first needs it. Proof cost is for the engine's own
theorems (the toy's layers: `Readings`, `Words`, `Joins`, `Lays`,
`Places`, and the budget in `Proofs.sw`); the rules' cost of using a
feature is the rules layer's.

A thing that matters for every row: the toy's proofs never look at
`fits`. A *reading* lets every question the printer asks of the width
go either way (`Readings.sw`, `printIsReading`), and every layer is
proved of every reading [source]. So a feature that only changes what
is measured costs the budget proofs and nothing else.

### 1.1 Constructors and printer state

| Feature (Rust) | What it does | Needed | Where | Proof cost |
|---|---|---|---|---|
| `Align` | breaks inside go to the column the doc starts at (or the indent, at a line start) | yes | `(let x := e; body)` and a sequence's parts, 557, 1761 | **medium**: `Place.Mid` must carry the line's current column, not only its indentation, so `Puts` and `Lays` take word widths (they already compute `lineWidth` for line starts) |
| `AlignInset` | as `Align`, but 2 in from a line start | yes | a sequence whose `;` line would end the block, 1759 | small once `Align` is done |
| `Displaced` | an element a comment put on its own line indents from where its first line lands; a waiting comment ends the line first | yes | 392, SW-3728 | **medium**: a new place rule in `Places` and `Joins`; S1 meets it (any element after a trailing comment) |
| `NarrowGroup(max)` | a group flat only if its line ends within `max` columns | yes | type declarations' constructors and fields, 1057, 1185 | **free**: a `Group` in every reading; budget only |
| `IdGroup` / `IfBroken` | a choice made by how an earlier group printed | yes | a body below a header that broke (S6), 671/699, 1352, 1527/1542 | **small**: in readings, `IfBroken` is a choice of its two branches, as `Choice`; the printer keeps a map of ids to modes (an association list is enough) |
| `Shared` | a doc built once and used in several `Choice` options, with its `forces_break` cached | no | 13 uses | none: Stitchwort values are shared already. The cache matters for speed: give `Choice` a cached flag as `Group` has (SW-3416's finding) |
| `Mark(key)` / `CloserLine(key)` | a closer that comments put on its own line goes at the indentation in force, unless a line since its opening bracket is at or left of that, then at the marked line's | yes | own-line comments before a closer, S40, 287, 371 | **high**: the place must carry each open mark's indentation and the least indentation since; `Places` states where the closer starts its line. S1 meets it (comments inside brackets) |
| `comment_floor` | after a comment break before an own-line comment (`LineStart`), every line up to the next code is indented at least to the break's line | yes | every `LineStart`, 291 | **medium**: the toy's `CommentEnd` is a different mechanism (one break to the comment's line). Rust's floor lasts over several lines and is a `max`, so the outputs differ where the layout wants a line deeper than the floor or where several lines follow the comment [inferred]. `Place` carries `floor: Option Nat`; `CommentEnd` goes |
| `TextBlock { text, src_indent }` and `shift_lines` | a `"""` block printed as written, its later lines moved by as much as its line moved | yes | 325, `"""` texts | **high**, and partly the lexer's: a word with line breaks in it breaks the layers' "a word is one piece on one line", and its read-back depends on how the lexer reads a moved block. The proof plan's slice S4 (sketch risk 7) |
| `Text` with a waiting comment: `before_code` | spaces after a waiting comment are *held*, and written before a closer that follows on the line; code text starts a comment break | yes | every record `{ … }`: Rust prints `def r: R := { a = 1 } -- c` [run], the toy's `write` drops the space and would print `{ a = 1} -- c` | **small–medium**: `Held` carries a count of held spaces; `Joins` gains "a held space may precede a closer" |
| Closers by character class | Rust treats any text made only of `)`, `]`, `}`, `,` as a closer | yes, as a convention | — | none: keep the toy's `Closing` constructor (its theory exists) and have the rules emit `Closing` for exactly those texts. A check in the harness: no `Chunk` made only of those characters |
| A flat `Line` / `SoftLine` while a comment waits | Rust writes the space (held) or nothing, and breaks only when code follows, at the continuation indent; the toy breaks at the `Line` itself, at the construct's indent | yes | every flat group holding a trailing comment | **medium**: the toy proves "no code after a comment on its line" from its `Line` rule (`Print.sw`'s comment); in Rust it follows from `before_code` alone, which is the same kind of argument in a different arm. The toy's rules need a `Choice` of flat-with-`Closing` to keep a call's `)` on a comment's line (NOTES, T3); with Rust's rule that workaround is not needed |
| `before_code` at a line start | a waiting comment doesn't break before text at a line start | yes, for fidelity | probably unreachable: a comment trails a word | small |
| `Blank` | an empty line unless the output is empty or ends in a blank line | the same | — | none: the toy's `started` and `newlinesAtEnd` say the same [inferred: `newline` always writes `\n`, and lines never end in spaces] |
| `CommentEnd` (toy only) | — | replaced by `comment_floor` | — | its arms go |

### 1.2 Measures and width rules

| Feature | Rust | Toy | Needed | Proof cost |
|---|---|---|---|---|
| `flat_break` in `fits_in` | a flat line break after a waiting comment fails only if *code* follows; closers alone still fit, so a comment on a bracket's last item measures as if after its closer | a flat `Line` after a comment never fits | yes | **free** (measure only) |
| Comment break in the measure | text after a waiting comment restarts the measure at `max indent (line_indent + 2)`, `line_indent` the *first* line's | the same, `lineIndent` moved to the new line | see §2 | free |
| `fits_flat` | `fits` with width `usize::MAX / 2`, no waiting comment, line indent 0 | `fitsFrom` with the real width, the waiting comment and the line's indent | see §2 | free |
| Spaces after a waiting comment, in the measure | not counted (`continue`), though the printer writes them before a following closer | dropped, and the printer drops them too | see §2 | free |
| `TextBlock` in the measure | its first line counts; a multi-line block leaves `width - last line` | — | yes, with `TextBlock` | free once `TextBlock` exists |
| `NarrowGroup` inside a measure | measured as a plain group | — | yes | free |
| Character widths | `chars().count()` | `Text.length` | the same if `Text.length` counts characters; one engine test (`∀∀∀ →→`) pins it | none |
| `WIDTH = 120`, `TYPE_WIDTH` | constants of the rules | — | yes | none |
| `flatWidth` | `balanced_fill` prints each item flat to learn its width (SW-3193) | — | yes, a `Doc.flatWidth: Doc → Option Nat` (none if the doc forces a break or holds a line break) | none in the engine; the rules' `balanced_fill` is a choice the readings already allow |

**Summary.** Of 15 Rust features the toy lacks, 13 are needed for byte
identity (`Shared` isn't; character-class closers are a convention).
Five are free or nearly (`NarrowGroup`, `flat_break`, `IfBroken`,
`flatWidth`, the measure fixes), six are small to medium, and two are
high (`Mark`/`CloserLine`, `TextBlock`). The slices need them in this
order: S1 needs the comment ones (held spaces, the flat `Line`, the
floor, `Mark`/`CloserLine`, `Displaced`) and `IdGroup`; S3 needs `Align`
and `AlignInset`; S4 `TextBlock`; S5 `NarrowGroup`.

## 2. The toy's differences from Rust: which way `Std.Doc` goes

Each of the toy's three deliberate differences (`tools/toyfmt/NOTES.md`,
"`fits` measures from the new line") is a place where Rust's *measure*
disagrees with what Rust's *printer* then does. The measure exists only
to predict the printer, so each is a bug in Rust, not a style: the
fixed measure gives the layout the style rules (E1: a group is flat if
it and what follows it on the line fit) already say. I found a fourth
of the same kind.

| # | Difference | Rust's printer | Rust's measure | Bug? | `Std.Doc` |
|---|---|---|---|---|---|
| D1 | The line indentation at a second comment break inside one measure | breaks at `max indent (line_indent + 2)` of the line it is on (`before_code`, `newline` sets `line_indent`) | uses the measure's first line's `line_indent` for every break (`at.line_indent` never changes) | yes | follows the toy; Rust fixed |
| D2 | The width in `fits_flat` (a broken `Fill`'s first item inside a measure; a `OneLineBelow` option of a `Choice`) | prints with the real width | measures with `usize::MAX / 2`, so after a comment break inside the item everything fits | yes | follows the toy; Rust fixed |
| D3 | A waiting comment when a broken `Fill`'s first item is measured | the comment is waiting | `fits_flat` starts with `suffix: false` | yes | follows the toy; Rust fixed |
| D4 (new) | Spaces held after a waiting comment, then a closer | writes them before the closer (`{ a = 1 }`) | doesn't count them | yes, off by the spaces' width | follows Rust's printer; both measures count them |

The toy differs from Rust in four more places that are not
deliberate: the flat `Line` while a comment waits, held spaces,
`CommentEnd` against the floor, and `before_code` at a line start
(§1.1). In all four `Std.Doc` follows Rust: they are the toy's
simplifications, and Rust's behaviour is the house style.

**Under D3677** a bug found by the proof work is fixed in both
formatters, with a test on each side. These four are that. What makes it
the orchestrator's call rather than Matt's is that each fix makes the
printed layout agree with the style rule as written; what would make it
Matt's is reach. So the Rust lane (R0, §5) first counts the outputs
that change: on the goldens, a repo sample and the fuzzer through the
harness. If a handful change and each is a group now measured as it
prints, it lands as a bug fix. If many change, or a change looks worse
to a reader, it comes to Matt as a D question with the examples, and
`Std.Doc` follows Rust's current measure meanwhile (the proofs don't
care: §1's readings).

Why not simply follow Rust in everything for byte identity? Because the
four measures are free to prove either way, the fixes are each a few
lines in Rust, and keeping a known misprediction in a proved engine
would need it written into `Std.Doc`'s documentation as intended
behaviour, which it is not.

## 3. How the 302 theorems move

### 3.1 Where

**Copy, don't move.** The toy is finished and tagged (`toy-v2`); its
1,700-odd theorems above the engine (`Toy.Fmt.*`) are stated against
`Toy.Doc`'s exact behaviour (`CommentEnd`, `Line` breaking after a
comment). Moving the engine under them would mean re-proving the toy
for nothing. The toy keeps `Toy.Doc`; the new engine starts as a copy.

**Grown in `tools/fmt`, moved into std when closed.** The copy lives
in `tools/fmt/src/Doc/` (namespace `Fmt.Doc`; a plain `Doc` clashes with the type, E-FOREIGN-NAMESPACE) while features are ported, so
the program can run ahead of its proofs with open goals (`?`, listed by
`stitchwort axioms`) without putting open goals into the standard
library. When `axioms` on its top theorems lists none, it moves to
`crates/elab/src/std/Doc/` as `Std.Doc` in one rename lane. This is an
implementation call; the alternative (in std from the start, each
feature lane closing its proofs before merging) keeps std clean too but
makes byte identity wait for the hardest proofs (`CloserLine`,
`TextBlock`).

### 3.2 What changes in the statements

| Layer (toy file, theorems) | Change |
|---|---|
| `Doc.sw`, `Print.sw` (program) | new constructors (`Align`, `AlignInset`, `Displaced`, `NarrowGroup`, `IdGroup`, `IfBroken`, `Mark`, `CloserLine`, `TextBlock`); `CommentEnd` gone; `Choice` caches its flag; `Printer` gains `heldSpaces`, `commentFloor`, `modes`, `marks` |
| `Readings.sw` (5) | the reading step gets arms for the new constructors: `NarrowGroup` as `Group`, `IfBroken` as a two-way choice, the others deterministic. `printIsReading` keeps its statement |
| `Proofs.sw`, the budget (42) | `Doc.size` and `Cmd.weight` for the new nodes; `printBudgetEnough`, `fitsFromEnough` keep their statements. The one layer every measure change touches, as SW-3452 found |
| `Words.sw` (69) | `Uniform` gets `IfBroken` (both branches the same words) and `TextBlock` (one word). `readingWords`' statement keeps its shape; held spaces are layout, so no word moves |
| `Joins.sw` (66) | `Edge` records held spaces after a waiting comment; `WriteJoins` loses the flat-`Line` break and gains "code after a waiting comment starts a line"; `CloseJoins` lets held spaces precede a closer. `readingJoins` and `printedJoins` keep their statements: "nothing follows a word that `follows` doesn't allow" is unchanged |
| `Lays.sw` (40), `Places.sw` (78) | the biggest change. `Place` gains the line's current column (for `Align`), the comment floor, and the open marks with their least indentation since (for `CloserLine`). `Puts`' arms for `Line`, `HardLine`, `LineStart` take the floor; new arms for the new constructors. `printPuts` and `printLays` keep their statements over the bigger `Place`; their callers in the rules layer see the bigger `Place` too |
| `Columns.sw` (2) | none |

No top statement of the engine changes in meaning: every reading of the
document writes its words (`readingWords`), joins only what `follows`
allows (`readingJoins`), and puts each word where `Puts` says
(`printPuts`). What grows is the predicates the rules must establish.

### 3.3 Order

1. **Copy as is** (E0): rename, std-style docs, `flatWidth`; 302
   theorems check unchanged.
2. **Measures** (with E2's program): `flat_break`, the four measure
   fixes, `NarrowGroup`'s limit. Only the budget proofs move.
3. **Comments** (E3): held spaces, the flat `Line`, `before_code` at a
   line start, the floor replacing `CommentEnd`, `Displaced`. `Joins`
   first (smallest change), then `Places` with the floor.
4. **Ids and columns** (E4): `IdGroup`/`IfBroken` in `Readings` and
   `Words`; `Align`, `AlignInset`; `Mark`/`CloserLine` in `Places`.
5. **Text blocks** (E5, with slice S4): `TextBlock` through every layer
   and its lexer side.
6. **Into std** (E6).

Steps 3 and 4 are what S1's rules-layer proofs need (S1 has comments
inside brackets, and a body after a header); `Align` could wait for S3
but costs least done with `Place`'s other changes.

**Size** [estimated, from the toy's per-feature counts: `Closing` and
its theory cost about 30 theorems in T3; SW-3452's measure change cost
5 restated, 0 new]: measures 5–10 restated; comments 40–60 new;
ids and columns 50–70; text blocks 30–60; about 140–180 new without
text blocks, so about 450 in all. That is more than the proof plan's
F2 figure (40–80 new): it counted features, not the `Place` growth that
`Align` and `CloserLine` force on every `Places` lemma.

## 4. SW-3884: a comment-free `meaning`

**Decision: (b), a blanking map, applied before the steps.**

```
def SourceFile.meaning (file: SourceFile): Meaning :=
  { plain = file.withoutComments.apply meaningSteps }
```

`withoutComments` sets every `Word`'s comments to none, the file's end
comments to none, and `Group.bare` to `True` (it summarises comments,
SW-3882). It is one generic map over the tree's words, about 90 sites
(`Word` appears 77 times in `Syntax/Expr.sw`, `Decl.sw` and
`Statements.sw` [source: grep]), written once as
`SourceFile.mapWords (f: Word → Word)` so it has other uses.

Why (b) makes stage 5's top theorem cheaper:

- **The top theorem gets meaning by congruence.** The printer's
  read-back gives `parse (print t)` equal to `t` up to comments at most
  (rule N re-homes nothing in a settled tree, but blank-line counts are
  normalised, and the parked comma moves a comment, K1). With blanking
  first, `t₁.withoutComments = t₂.withoutComments` gives `t₁.meaning =
  t₂.meaning` with no lemma. With (a), equal meanings are equal dump
  texts, and getting there from trees needs "the dump ignores comments",
  a lemma per node kind about text concatenation: (b)'s map, plus a
  proof over each site, in the layer (text) where the toy's proofs were
  slowest.
- **The passes' facts stay equations on trees.** `MeaningProofs.sw`'s
  step facts are tree equations [source]. With (b) each pass also needs
  "it commutes with `withoutComments`", which is one generic lemma about
  the traversal plus a line a step, since no step reads a comment any
  more (SW-3882). With (a) every fact would have to be carried through
  the dumper.
- **It fails safe.** `meaning` is trusted. A site the blanking map
  misses keeps a comment in `meaning`, which makes "the same program"
  stricter: the top theorem gets harder to prove, never wrong. A dump
  that leaves something out (it prints a token's text and the node kinds
  only, `Syntax/Tree.sw`'s `Leaf.treeLine`) makes `meaning` forget it,
  the unsafe direction, and the dump was written to match Rust's
  `dev tree --print`, not to be a definition.

Before or after the steps: before. After (`(file.apply meaningSteps)
.withoutComments`) the read-back's "up to comments" would need the
commuting lemma at the top as well as at the passes.

The dump stays what it is: the harness's comparison, untrusted.

## 5. Stages

Estimates are agent minutes **as lanes actually run**, from similar
lanes' `Model result` lines: the formatter's build stages ran at 20,
47, 31, 31, 38 and 20 minutes (SW-3808, SW-3819, SW-3836, SW-3847,
SW-3863, SW-3864; estimates 50–75), engine lanes at 9 (SW-3452, est. 50)
and 17 (SW-3447, est. 40), and proof work at 80–110 theorems an agent
hour (the toy). Each stage ends in a checkable state.

| # | Stage | Model | Est. | Ends with |
|---|---|---|---|---|
| R0 | **Rust measure fixes** D1–D4 in `engine.rs`, a unit test each (failing before), and the count of changed outputs through `dev/fmt-twin` on goldens, a repo sample and fuzz cases; a D question to Matt only if the changes are many or look worse (§2) | Sonnet | 25 | `engine.rs` tests pass; changed outputs listed and goldens updated |
| E0 | **Copy** `Toy.Doc` and its 302 theorems to `tools/fmt/src/Doc/` (namespace `Fmt.Doc`: a plain `Doc` clashes with the type, E-FOREIGN-NAMESPACE), docs in std style, `Doc.flatWidth`; the toy untouched | Sonnet | 25 | `stitchwort audit Fmt.Doc`: 302, 0 failed |
| E1 | **The engine harness**: `stitchwort dev doc FILE` writes each declaration's `Doc` (a small s-expression form; a dev command, no style change) and `engine::print`'s text; `Fmt.Twin --stage engine` reads the form, prints with `Doc`, compares; `dev/fmt-twin engine` | Sonnet | 35 | the stage runs; a baseline count of differing declarations, by the features they use |
| E2 | **The program**: every §1 feature in `Doc` (the measures as R0 left them); the 12 `engine.rs` tests as `Doc` tests; a proof broken by a changed definition becomes an open goal, listed | Opus | 60 | `--stage engine` identical on goldens, then the repo sample, fuzz and disturbed; open goals counted |
| E3 | **Comments' proofs**: held spaces, flat `Line`, the floor, `Displaced`, through `Joins`, `Words`, `Places`, `Lays` | Opus (Fable if `Places` runs over) | 60 | `axioms` lists no open goal from these arms; audit of `Doc` clean of them |
| E4 | **Ids and columns' proofs**: `IfBroken`, `NarrowGroup`, `Align`, `AlignInset`, `Mark`/`CloserLine` | Opus | 60 | as E3, all but `TextBlock` closed |
| E5 | **Text blocks' proofs**, with slice S4 (needs the lexer's text-block theorems) | Opus | 45 | `axioms` on the engine's top theorems lists nothing |
| E6 | **Into std** as `Std.Doc`; `tools/fmt` imports it | Sonnet | 15 | `audit Std.Doc` clean |

Then the rules (stage 5 proper), per the proof plan's slices: S1's
program lane (proof plan ticket 12, Opus, 90 estimated there, about 40
by the build stages' actuals) ports `spacing.rs`, the file driver
(`printer/mod.rs`) and the rules for S1's constructs on `Doc`, and adds
`Fmt.Twin --stage text`. Its gate: `--stage text` identical on every
golden declaration within S1, then on the repo's. Each later slice's
program lane widens the same gate; `rules.rs` is 2,096 lines, so the
rest is two or three lanes of 40–60 minutes [estimated], as §8's stage 6
said.

**Totals** [estimated]: program to byte identity of the engine (R0, E0,
E1, E2) about 2.5 agent hours; proofs E3–E5 about 2.75; E6 a quarter.
E3 and E4 can run beside S1's other foundation and sketch lanes, and
E1 beside E0. R0 must land before E2 sets its measure, or E2 ports
today's measure and a follow lane changes both.

**Stop rules**, as the proof plan's §4: a proof stage at 1.5 times its
estimate stops and reports; if E3's `Places` change runs over twice its
count, `Place`'s shape is re-sketched (one paper lane) before E4.

**Risks.**

- `Place` with marks and a floor may make every `Places` lemma longer,
  not just add arms. E3 measures it first on the floor alone.
- The harness's `Doc` form must cover `TextBlock`'s text and `Shared`
  (written out, since Stitchwort has no sharing to keep).
- `Text.length` must count characters as Rust does; E0 adds a test.

## 6. Decisions

**For Matt: none now.** One conditional: if R0 finds the measure fixes
change many outputs or make one worse, the D question is whether Rust
keeps its current measure (the proved engine then documents it as
intended) [rec: fix, unless the changes look worse].

**The orchestrator's calls**, recommended here:

1. `Std.Doc` follows the toy on D1–D3 and both engines get the fixes,
   with D4; Rust's behaviour on the toy's four simplifications (§2).
2. Keep `Closing` as a constructor; drop `Shared` and cache `Choice`'s
   flag; replace `CommentEnd` with Rust's floor.
3. Copy, not move, the toy's engine; grow it in `tools/fmt` with open
   goals, into std when closed (§3.1).
4. SW-3884: (b), blanking before the steps (§4).
5. The engine-only harness (E1) before any rule is ported.

## 7. Found on the way

- **D4**, Rust's measure ignores spaces held before a closer after a
  waiting comment (§2).
- **The toy's flat `Line` after a comment breaks at the construct's
  indent**, Rust's at the continuation indent; the toy's rules worked
  around it with a `Choice` (NOTES, T3), which `Std.Doc`'s rules won't
  need.
- **`balanced_fill` measures with the engine** (`rules.rs:82`), so the
  rules depend on a flat-width function as well as on `print`.
- **`NarrowGroup`'s limit is ignored inside a measure** (`fits_in`
  measures it as a plain group) [source]. Probably intended (the limit
  is about its own line); worth a sentence in `engine.rs`.

## Sources

`crates/fmt/src/printer/engine.rs` (all), `mod.rs:1–80, 193`,
`rules.rs:60–110` and the grep of its engine uses;
`tools/toyfmt/src/Toy/Doc/*.sw` (`Doc.sw`, `Print.sw` in full; the
others' headers and their predicates' definitions); `tools/toyfmt/NOTES.md`
("Toy++ closed", "`fits` measures from the new line");
`tools/fmt/NOTES.md` (stages 4a, 4b); `tools/fmt/src/Fmt/Meaning.sw`;
`tools/fmt/src/Syntax/Tree.sw`; self-hosted-fmt.md §3.6, §7.3, §8;
self-hosted-fmt-proof-plan.md; the board's `Model result` lines for the
tickets named in §5. [run]: `stitchwort fmt` on `def r: R := { a = 1 --
c⏎}` gives `def r: R := { a = 1 } -- c`.
