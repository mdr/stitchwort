# One proof for several cases of a `match`

**Status:** design note, 19 November 2026 (SW-4219, an Opus paper lane;
from the slice 1 retrospective, `docs/reviews/SW-4205-slice1-retrospective.md`
§6 item 3). Nothing is built. Part 2 below (or-patterns that bind) changes
what programs may say, so it is Matt's decision (§6); part 1 changes
docs and the formatter only.

Claims are marked **[source]** (read at `2515c4f96`), **[measured]** (the
survey script, or the main checkout's release binary, built 14:49 today, on
probes `p1.sw` to `p6.sw`; script and probes are in the lane's scratchpad,
`sw4219/arms.py` and `sw4219/p/`), **[cited]** (the Lean 4 and Rocq
reference manuals, read today) or **[recalled]** (not re-checked here).

## In plain words

**The problem.** Proofs in `tools/fmt` and std often repeat one arm's proof
for many cases: `spellsNotComment` writes `| LParen, same => rewrite same`
and 32 more arms just like it, and `andLevels` and `orLevels` are four arms
in two identical pairs. In `tools/fmt`, 1,787 of 10,970 theorem arms (16%)
repeat an earlier arm of the same `match`, up to the names they bind, in 648
of 5,556 theorems (12%); in std, 890 of 6,634 arms (13%) in 451 theorems
[measured]. A reader has to check 33 lines to see they say one thing.

**What the survey found.** Most of this repetition can already be written
once today, and nobody does:

- A catch-all arm is *already* checked separately in every case the other
  arms split off: after `| Plus => …`, the arm `| _ => byComputing` is
  checked with `tok` as `Minus`, as `Star`, and so on, and an error says
  which ("this arm is checked in 5 cases, and this error is in the case
  where `tok` is `Star`") [measured, p3/p6]. It may bind names:
  `| other, same => rewrite same` checks with `same: text = "+"` in one
  case and `same: text = "*"` in the next [measured, p2].
- Or-patterns exist and are checked one alternative at a time, but they
  can't bind names, and the formatter puts all the alternatives on one line
  however long [measured, p5]. `tools/fmt` and std use none at all
  [measured: zero matches]; neither guide mentions them for proofs.

So 72% of the repeated arms in `tools/fmt` bind nothing the body uses (an
or-pattern or catch-all writes them once today), and most of the rest could
be a named catch-all today. About 107 repeated arms in `tools/fmt` and 150
in std need something new: or-patterns that bind.

**The change.** (1) Teach what exists: a section in the language guide and
the proving guide, and the formatter wrapping long or-patterns. (2) Let
or-patterns bind names, every alternative the same names, each alternative
checked on its own (so a name may have a different type in each, as `same`
does above). No new keyword, no kernel change, the same terms as the arms
written out.

**What it should do.** At most 2,369 lines of `tools/fmt`'s 92,771 theorem
lines (2.6%) and 1,222 of std's 51,092 (2.4%) are repeated arms that would
go [measured, an upper bound: it counts every repeated arm's lines]. No
theorem goes away: this tidies the dispatchers, it doesn't remove them. The
retrospective's 26% "dispatchers" are mostly arms that call *different*
lemmas per case, which this doesn't touch (§1.3).

## 1. The problem in numbers

### 1.1 The survey

`arms.py` reads each `theorem` (5,556 in `tools/fmt/src`, 4,174 in
`crates/elab/src/std`), finds its arm groups (lines starting `|` at one
indent, one `match` or one definition's equations), and compares the arms'
bodies: *identical* (equal text), *alike* (equal after renaming each
pattern variable by its position in the pattern, so `Inl a => f a` is like
`Inr b => f b`), and *one token apart*. It is line-based and heuristic:
an arm whose pattern runs over two lines is missed, and *alike* arms need
not be next to each other [measured]:

| | `tools/fmt` | std |
|---|---|---|
| theorems | 5,556 | 4,174 |
| arms in groups of two or more | 10,970 | 6,634 |
| arms that repeat an earlier one (alike) | **1,787** (16%) | **890** (13%) |
| their lines | 2,369 of 92,771 (2.6%) | 1,222 of 51,092 (2.4%) |
| theorems with a repeat | 648 (12%) | 451 (11%) |
| arms whose body text is exactly an earlier arm's | 1,820* | 942* |
| repeats whose body uses no name the pattern binds | 1,293 (72%) | 596 (67%) |
| … of those, joined into one or-pattern line of at most 120 characters | 823 | 476 |
| repeats using names, which a named catch-all could take today | 387 (upper bound) | 144 |
| repeats using names that need a binding or-pattern | 107 | 150 |
| whole group one body (every arm alike) | 607 repeats | 385 |
| arms one token apart from an earlier one (not alike) | 609 | 448 |

\* Identical text counts a few more than *alike*: renaming by position
separates arms whose patterns bind a different number of names before the
one used (`| A x, same` and `| B, same`). So *alike* is slightly low, and
the true figure lies between the two.

"A named catch-all could take today" counts, per group, the largest class of
repeats whose body uses names, when some other arm splits the scrutinee
(so the catch-all is checked per case); it assumes the class's patterns
differ only in the split column, so it is an upper bound.

### 1.2 The largest

From `arms.py --list` [measured]: `GoodItemProofs.sw:441`, 35 list
patterns proved by `byComputing`; `LexReadsProofs.sw:386`, 34 keywords;
`TreeJoinProofs.sw:99` and `:1301`, `PrintLexProofs.sw:313` and
`LexProofs.sw:2378`, each 32 arms `| Kind, same => rewrite same` (the same
`Spells` dispatch four times); `GoodItemProofs.sw:96`, 18 arms
`| Kind, _, _, fixed => DecEq.sound fixed`; `SpeltSlots.sw:531`, 17 arms of
`byComputing` ending in `| other => byComputing`.

### 1.3 What this doesn't touch

The 609 arms one token apart are mostly the constructor named in the body
(`spellsOfText1 Lower text plain`, `… Upper …`); with `_` there instead
(`spellsOfText1 _ text plain`, the constructor found from the goal) many
become alike, a style point for lanes rather than a feature. The per-kind
walk lemmas (one theorem per token kind) and dispatchers whose arms call a
different lemma each are the bulk of the retrospective's 26%; folding those
needs lemmas stated over all kinds at once, not a match form.

## 2. What Stitchwort has today, and why lanes don't use it

**A catch-all after a split** [source: `check_leaf`, `crates/elab/src/lib.rs`;
measured]. A `match` compiles to a case tree; an arm reached through several
leaves is checked at each, with the goal and context refined for that leaf
(`catch-all-goals.md` §1). So:

```
theorem lowN ∀ (tok: Tok): (5 <= level tok) = False := match tok with
  | Plus => byComputing
  | _ => byComputing          -- checked for Minus, Star, Slash, Num, Name
```

checks, and a failure names the case. The catch-all may bind names, used at
a different type in each case (`| other, same => rewrite same`, p2). Why
unused: nothing says so in either guide; the goal shown for a catch-all is
the last leaf's, which looks like one case (`catch-all-goals.md`'s
problem); and with *no* other arm the scrutinee isn't split at all, so
`match tok with | _ => byComputing` fails (p1 `lowB`). The workaround,
`| Plus | _ => byComputing`, works (p6) but reads as a mistake.

**Or-patterns** (`docs/syntax.md`, "Or-patterns"). `| Plus | Minus | Star =>`
is expanded into one row per alternative (`expand_or_patterns`) and each is
checked on its own [source]. Why unused: an alternative can't bind a name
(`E-OR-PATTERN-BINDS`, raised in lowering, `crates/syntax/src/lower/patterns.rs`
[source]), and most repeated proof arms use one (`same`, `fixed`); a long
or-pattern can be written over lines ending in `|` (p4), but `stitchwort
fmt` joins it back into one line of any length (p5: 150 characters); an
error in one alternative doesn't say which one (p3 `lowE`, unlike the
catch-all's note); and the editor's "Add the missing arms" and split
actions write one arm per constructor [source: `crates/driver/src/fixes.rs`,
`crates/lsp/src/arms.rs`], which lanes then fill in one at a time.

**`cases then t`** splits what the goal is stuck on and tries `t` in each
case (`docs/syntax.md`, `cases`). It doesn't help here: it doesn't split
propositions such as `Spells kind text`, and it chooses its own split. On
`text.length = 1` it split `text`, not `kind` (p2 `shortB`); on
`(5 <= level tok) = False` it split the comparison and never `tok`
(p1 `lowC`, a finding of its own: §7).

**Helper lemmas** (state the shared step once, call it per arm) shorten the
bodies but keep one arm per case.

## 3. Precedents

- **Lean 4.** `tac <;> tac'` "runs `tac` on the main goal and `tac'` on each
  produced goal … If the tactic fails on any of the subgoals, then the whole
  `<;>` tactic fails"; `all_goals tac` runs `tac` on each goal and fails if
  it fails on any; `any_goals` fails only if it fails on all;
  `case tag₁ | tag₂ => tac` "is equivalent to `(case tag₁ => tac); (case
  tag₂ => tac)`" [cited: Lean Language Reference, "The Tactic Language",
  anchors `#_LT__SEMI__GT_`, `#all_goals`, `#any_goals`, `#case`].
  In term-mode `match`, `| p | q => rhs` with the same variables in each
  alternative is allowed, and I believe the right-hand side is elaborated
  once per alternative [recalled; the reference's "Pattern Matching"
  section doesn't say, checked today].
- **Rocq.** In `tac1; tac2`, "the tactic `v2` is applied to all the goals
  produced by the prior application", with backtracking into `tac1`
  [cited: Rocq reference manual 9.0, Ltac, "Sequence: `;`"]; `tac; [t1 |
  t2]` gives each goal its own tactic, `try t` turns failure into success
  and `repeat t` applies `t` until it fails [recalled; that part of the page
  wasn't read]. Gallina's `match` accepts `| p | q => t`, with each pattern
  binding the same variables [recalled].
- **Rust** requires every alternative of an or-pattern to bind the same
  names at the same types [recalled; SW-676 cites the Rust reference].

Stitchwort's proofs are terms, so the match arm is where Lean's `case a | b
=>` and Rocq's `;` live. A catch-all after a split is already `<;>` over the
remaining cases, failing if any case fails (as `all_goals`). Nothing like
`any_goals` or `try` is proposed: a proof text that silently skips cases it
can't prove would make the case that's left open harder to find.

## 4. Designs

### Design 1: teach and tidy what exists (no language change)

- **Guide.** A section "One proof for several cases" in
  `docs/guide/10-proofs.md` (after "Proof by cases"), a rule in
  `docs/proving-guide.md` §1 ("write a repeated arm once: an or-pattern, or
  a catch-all after the arms that differ"), and a line in `docs/syntax.md`'s
  or-pattern paragraph that a catch-all and each alternative are checked
  per case. Examples checked as usual.
- **Formatter.** `stitchwort fmt` wraps an or-pattern longer than the line,
  breaking after `|` with the continuation indented (the layout p4 already
  parses). This is a bug fix to the Rust formatter, allowed under D3677; the
  self-hosted formatter's slices admit no or-patterns so far (slice 3's
  patterns are names, `_`, numerals and constructors) [source:
  `tools/fmt/src/Fmt/Slice3.sw`].
- **Errors.** An error in an or-pattern's arm gets the catch-all's note,
  naming the alternative ("in the alternative `Star`"), from the
  `alternatives` spans the leaf already records [source: `Leaf.alternatives`].
- **The editor's "Add the missing arms"** offers, beside one arm per
  constructor, one arm with an or-pattern of them all.

It reaches the 72% that bind nothing and, through a named catch-all, most of
the rest. It doesn't reach `andLevels` (§5.1): its two classes both use
`same`, and there is only one catch-all.

### Design 2: or-patterns that bind, checked per alternative

Lift `E-OR-PATTERN-BINDS` when every alternative binds the same set of
names. Each alternative is already a row of its own with the arm's body
[source: `expand_or_patterns`]; the body is checked once per row, with that
row's bindings, so a name may have a different type in each alternative
(`same: text = "&&"` in one, `same: text = "∧"` in the other). That is what
proofs need, and it is more than Rust allows; in programs it is harmless,
since the body is already elaborated per row.

```
match logic with
  | Inl (Inl same) | Inl (Inr same) => Both (rewrite same) (rewrite same)
  | Inr (Inl same) | Inr (Inr same) => (Bool.falseNotTrue (rewrite same at tested)).impossible
```

and, nested, `| Inl (Inl same | Inr same) => …`. With several columns an
or-pattern in each multiplies: `| Arrow | OrOr, Inl same | Inr same` is four
rows.

- **Errors.** A name missing from an alternative stays `E-OR-PATTERN-BINDS`,
  reworded: "`same` is bound in `Inl (Inl same)` but not in `Inr _`". An
  error in the body names its alternative (Design 1's note).
- **Guards.** `| p | q if c =>` already tests the guard for whichever
  alternative matched (`docs/syntax.md`, guards); with names, `c` is checked
  per alternative like the body.
- **`cases`, `match induct`.** `cases` writes its own case tree and is
  untouched. `match induct` arms take the function's cases; or-patterns
  there follow whatever rows it accepts today, nothing new.
- **Equations.** `f.eqK.or1`, `f.eqK.or2`, … already exist per alternative
  [source: `docs/syntax.md` equations]; with names they take the names as
  parameters, as a single-pattern arm's equation does.
- **The kernel**: nothing. The term is the case tree the arms written out
  give, so hashes of existing code don't change.
- **Language server.** Hover on a name bound in several alternatives shows
  its type in each when they differ ("`same`: `text = "&&"` (first),
  `text = "∧"` (second)"); go-to-definition goes to the first binding;
  rename renames all of them [estimated: `nav.rs` already walks
  `Pattern::Or` alternatives for binders, source].
- **Formatter.** No new syntax: the parser already parses `Some x | None`
  and rejects it in lowering, so the grammar is unchanged.

### Design 3: a catch-all that splits on its own

For a `match` whose every arm would be alike (607 repeats in `tools/fmt`),
a way to say "split this, then the same proof in each case" with no arm
written out. Two spellings:

- **3a, a pattern word.** `| each, same => rewrite same`: `each` in a column
  splits it into every constructor and checks the arm in each. A new
  reserved word in patterns.
- **3b, a targeted `cases`.** `cases kind then rewrite spells`: split
  exactly `kind` (one level), rewrite the hypotheses that mention it, and
  check `rewrite spells` in each case; fail, naming the case, if it fails in
  any. This is Lean's `cases kind <;> t` and Rocq's `destruct kind; t`, and
  it fits the existing `cases then t`. But `cases`'s cases have no names for
  a constructor's fields, and the existing `cases then t` keeps splitting
  when `t` fails, so the targeted form would differ from the untargeted
  one in a way readers must learn.

Today's workaround costs one extra line (`| Plus | _ => …`, or naming one
case and using a catch-all), so both buy little against a new word.

## 5. Recommendation

**Design 1 now, Design 2 after Matt's decision, Design 3 not at all**
(revisit if the guide's section doesn't change what lanes write).

### 5.1 Before and after

`andLevels` and `orLevels` (`tools/fmt/src/Syntax/ParseWalk.sw`), Design 2:

```
-- before (each)
  match logic with
    | Inl (Inl same) => Both (rewrite same) (rewrite same)
    | Inl (Inr same) => Both (rewrite same) (rewrite same)
    | Inr (Inl same) => (Bool.falseNotTrue (rewrite same at tested)).impossible
    | Inr (Inr same) => (Bool.falseNotTrue (rewrite same at tested)).impossible

-- after
  match logic with
    | Inl (Inl same | Inr same) => Both (rewrite same) (rewrite same)
    | Inr (Inl same | Inr same) => (Bool.falseNotTrue (rewrite same at tested)).impossible
```

`spellsNotComment` (`tools/fmt/src/Fmt/TreeJoinProofs.sw:96`), 33 arms, and
its three copies: Design 1 alone gives 15 lines (the 14 two-spelling arms
written out, then `| _, same => rewrite same`, which works today, p2
`shortD`); with Design 2, two:

```
  match kind, spells with
    | Arrow | OrOr | AndAnd | NotEq | Le | Ge | Bang, Inl same | Inr same => rewrite same
    | _, same => rewrite same
```

`spellsOfTests` (`tools/fmt/src/Syntax/GoodItemProofs.sw:86`), 30 arms in
three classes plus a catch-all; the catch-all is taken by `within`, so the
classes need Design 2:

```
  match kind, within, plain, fixed with
    | Lower | Upper | Num | Float, _, plain, _ => spellsOfText1 _ text plain
    | KwDef | Colon | ColonEq | LParen | RParen | LBracket | RBracket | Comma | Equals | EqEq |
      Lt | Gt | PlusPlus | Plus | Minus | Star | Slash | Percent, _, _, fixed => DecEq.sound fixed
    | OrOr | AndAnd | NotEq | Le | Ge | Bang | Arrow, _, _, fixed => eitherText fixed
    | _, within, _, _ => (Bool.falseNotTrue within).impossible
```

(`spellsOfText1 _` relies on the constructor being found from the goal
[estimated: not probed in the fmt project].)

### 5.2 Cost [estimated, agent time, from similar past tasks]

| Lane | Model | Work | Time |
|---|---|---|---|
| Guide and proving-guide section, syntax.md line, examples | Sonnet | Design 1 docs | 30 min |
| Or-pattern wrapping in `stitchwort fmt`; per-alternative error note; "Add the missing arms" offering an or-pattern | Sonnet (fmt), Opus (elaborator note) | Design 1 tools | 1 to 1.5 h |
| Binding or-patterns: lowering check, names per alternative, equations, nav, hover, error wording, examples, guide | Opus (syntax and elaborator: D2506) | Design 2 | 1.5 to 2.5 h |
| Sweep `tools/fmt` and std to the new forms | DeepSeek, by file, reviewed | Both | 1 to 2 h; proofs re-checked by `check` on each namespace |

The sweep is optional and can follow the slice's consolidation; the
guide's rule is what changes new proofs.

### 5.3 Risks

- **Goals.** In an arm checked per case, the goal shown is the last case's
  (`catch-all-goals.md`); with more arms written this way that matters
  more. That note's change (show the arm's goal as written) should land
  first or alongside.
- **Cost of checking** is unchanged: the same leaves are checked as with the
  arms written out.
- **Readability.** A long or-pattern hides which cases are left for the
  catch-all; the formatter's wrapping and the editor's hover over `_`
  listing its cases (not in scope here) answer that.
- **Proved tools' scope** (D3688): none. Design 2 makes the language accept
  more, and no proved tool's input grammar changes (lowering, not parsing).

## 6. Decision for Matt

**D: let or-patterns bind names, each alternative checked on its own?
[rec: yes]**

- **The problem.** A proof that does the same thing in several cases has
  to write it once per case when the cases name a fact: `andLevels` is four
  arms for two proofs, `spellsOfTests` 30 for four. Or-patterns would say
  it once, but they can't bind a name (`E-OR-PATTERN-BINDS`, D1401).
- **The change.** Allow `| Inl same | Inr same => …` when every
  alternative binds the same names. Each alternative is checked on its own,
  so a name may have a different type in each, unlike Rust, because proofs
  need exactly that. This replaces SW-676's "same types" rule.
- **What it should do.** About 107 repeated arms in `tools/fmt` and 150 in
  std that nothing written today can join [measured, heuristic], with the
  rest joined through Design 1 (no decision needed): up to 2.6% of
  `tools/fmt`'s theorem lines and 2.4% of std's. No kernel, term or hash
  change. Cost about 2 hours of Opus [estimated].

## 7. Findings

- `cases` on `(5 <= level tok) = False`, with `level` an enumeration's
  table, splits the comparison and never `tok`, and fails; `match tok`
  with every arm `byComputing` proves it (p1 `lowC`) [measured].
- `stitchwort fmt` put an or-pattern on one line of any length (150
  characters in p5) [measured]; since SW-4224 (19 Nov) a long one breaks after each `|`.
- An error in an or-pattern's arm doesn't say which alternative failed;
  a catch-all's does (p3) [measured].
