# The Goals panel: what a goal shows, compared with other provers

**Status:** draft 1, 11 November 2026 (SW-2921), awaiting Matt's decisions
([§7](#7-decisions-for-matt)). Design only: no code changed. Written against `main` at
`04c85a5c2`.

It starts from the book: in section 2.1 (`book/src/02-cases.sw`), after "Split on `m`", the
text says the `Rock` arm's goal is `⊢ beats Rock Rock = False`, but the panel shows
`⊢ False = False`, because the goal is computed once `m` is a constructor. This note is
about **how a goal is printed**. *Where and when* one is shown (the panel following the
cursor, a step's goal before and after, `stitchwort goal --at`) was decided in
[goal-at-any-point.md](goal-at-any-point.md) (D3497–D3499) and is built; *what `rewrite`
and `match` search* was decided in [goal-as-written.md](goal-as-written.md) and
[bounded-readback.md](bounded-readback.md) (D2542). Related:
[folded-goals.md](folded-goals.md), [goal-printing-gaps.md](goal-printing-gaps.md) (D3090:
the printer may change notation but never refolds a definition),
[lsp-goal-holes.md](lsp-goal-holes.md).

Labels: **[ran]** run for this note with the release CLI in the main checkout (built
19:37 today) on scratch files outside the repository (§8 lists them); **[checked]** read in
this repository at the place given; **[cited]** read today in the source linked in §8;
**[recalled]** well-known behaviour I didn't re-check in a source today; **[inferred]** my
reasoning, not run.

## Contents

0. [Summary](#0-summary)
1. [Today's behaviour](#1-todays-behaviour)
2. [Other provers](#2-other-provers)
3. [The comparison table](#3-the-comparison-table)
4. [Options](#4-options)
5. [Recommendation and stages](#5-recommendation-and-stages)
6. [What changes in the book and the docs](#6-what-changes-in-the-book-and-the-docs)
7. [Decisions for Matt](#7-decisions-for-matt)
8. [Files run, sources, what this note didn't do](#8-files-run-sources-what-this-note-didnt-do)

## 0. Summary

**The problem.** A goal is printed *simplified*: every call whose first match can be decided
at once is computed, again and again, before printing. So after a split the goal the reader
expects is gone: `beats Rock Rock = False` shows as `False = False`, `0 ≤ n` as
`True = True`, `n + 0 = n` as `n = n`, and a goal mentioning `cost Red n` shows a
120-character polynomial instead **[ran]**. It is also uneven: `beats Rock Rock` computes but
`play Rock Rock` (defined with `if`) doesn't, though `rfl` proves both. The reader loses the
link between the statement and the goal, which is the thing a learner is trying to see. And
it disagrees with Stitchwort's own `rfl` message, which already says "`beats m m` and `True`
aren't equal; computing the left side gives `False`": as written, then what it computes to.

**What others do.** Lean, Rocq and Isabelle print a goal **as written**, with the variable
replaced and nothing computed; computing is a step the user takes (`simp only`, `cbn`,
`simp`). Agda and Idris print it **simplified**, as Stitchwort does today, and Agda gives a
choice per query: `C-u` as written, `C-u C-u` fully computed, `C-u C-u C-u` head-normal.

**The change (recommended).** Print the goal as written, with the substitution, and when what
it computes to is different, a second line under it:

```
⊢ beats Rock Rock = False
  computes to False = False
```

The first line is what the reader wrote with `Rock` put in for `m`; the second is today's
line, what `rfl` will see. The same in the CLI, hover, the playground and `--json`. A long
computed line is cut and folded (click to open in the panel). Hypotheses are printed as
written, without a second line.

**What it should do.** Book section 2.1's text becomes true as it stands, plus one sentence
for the new line. Every goal that today hides its statement (§1.2: the split arm,
`True = True`, `n = n`, the polynomial) shows the statement and keeps the computed form in
view. The read-back for it already exists (`quote_as_written`, used for unknowns' solutions,
`crates/core/src/value.rs:2888`) **[checked]**. Estimated one Sonnet lane of about 90
minutes for the printer, server, CLI and both panels, plus one for the docs and snapshots;
it should wait for SW-1004 (lifted `match`es printed as `match`), or as-written goals will
show `liftedArm.%match1 True n` more often (§1.4) **[inferred]**.

## 1. Today's behaviour

### 1.1 How a goal is printed

- Every goal, hypothesis and step is printed by `pretty::value_for_goal`
  (`crates/core/src/pretty.rs:329`), which reads the value back with `quote_shown`
  (`value.rs:2922`), mode `Readback::Shown` **[checked]**.
- `Shown` keeps a glued call as a call **unless it matches at once**: its definition's
  first case is on an argument that is already a constructor or a number (`matches_at_once`,
  `value.rs:945`). Such a call is replaced by its one step, and the result is read back the
  same way, so steps repeat while each next call also matches at once (`value.rs:3197-3213`)
  **[checked]**. This is Agda's "simplified" rule (§2.4) almost word for word.
- A sum stuck on an unknown is written with its number last (`k * 1 + 1`, SW-895), and
  numerals are added up (`… + 17`) **[ran]**.
- There is a third mode, `Readback::AsWritten` (`quote_as_written`, `value.rs:2888`): every
  glued call stays a call, "for … stating a goal as written". The goal printer doesn't use it
  **[checked]**.
- Long goals: a goal's text may be 4,000 characters (`GOAL_LIMIT`, `pretty.rs:322`); past
  that, inner parts are replaced by `…`, deepest first. The CLI cuts any goal line over 400
  characters in the middle, saying how much is left out, unless `--full-goals`
  **[checked]**.
- Hypotheses (`goals.rs:446-575`) **[checked]**:
  - in dependency order, otherwise the order of scope;
  - a variable a split replaced by a constructor isn't listed (in the `Rock` arm, `m` is
    gone);
  - an older hypothesis a later one of the same name replaced is dropped unless something
    mentions it; one that can't be referred to is `n✝`; compiler-made names (`%…`) and `_`
    are hidden;
  - a `let` shows its value (`twice: Nat := n + n`) unless it's a proof, which shows only
    its statement. A `let` name used in a later hypothesis's type is replaced by its value:
    `let fact: twice = n + n` is listed as `fact: n + n = n + n` **[ran]**.
- The docs say so: "Goals are shown *computed*, as `rfl`'s messages are: `k * 1 + 1`, not
  `Succ k * 1`" (`docs/syntax.md:1659`); "The goal is shown computed, as the checker sees
  it" (`docs/guide/10-proofs.md:127`) **[checked]**. The first half of the syntax.md line is
  no longer true of `rfl`'s messages (§1.3).

### 1.2 Examples from the binary **[ran]**

**The split arm (book 2.1).** `theorem noSelfWin (m: Move): beats m m = False`, `match m`,
arms `?`:

```
$ stitchwort goal --at src/02-cases.sw:54:15        # on the Rock arm's ?
in `noSelfWin`
  ⊢ False = False
$ stitchwort goal --at src/02-cases.sw:54:7         # on the pattern | Rock
in `noSelfWin`, arm 1 of 3, `| Rock`
  before ⊢ beats m m = False
  after  ⊢ False = False
```

All three arms print `⊢ False = False`; they are told apart only by their place. In book
2.3, the arm `| Rock, Rock` of `otherSideSwaps` prints `⊢ otherSide (play Rock Rock) = play
Rock Rock`, uncomputed: `play` starts with an `if` on `beats mine theirs`, not a match on an
argument, so it doesn't "match at once". Both arms are closed by `rfl`.

**A `Bool` comparison.** `theorem costPos (l: Light) (n: Nat): cost l n + 1 > 0` split on
`l`: all three arms print `⊢ True = True`. The `> 0` the reader wrote is gone, and so is
`cost`. A statement with a `match` in it, `(match b with | True => n | False => 0) ≤ n`, split
on `b`: the `True` arm prints `⊢ n ≤ n`, the `False` arm `⊢ True = True`.

**Induction step.** From the guide (`timesOne`) and a `double` of my own:

```
| Succ k => ?        k: Nat  ⊢ k * 1 + 1 = Succ k                     (written: Succ k * 1 = Succ k)
| Succ k => ?        k: Nat  ⊢ Succ (Succ (double k)) = k + k + 2     (written: double (Succ k) = Succ k + Succ k)
```

The guide's own prose explains the first with two forms: "In the `Succ k` arm it is `Succ k *
1 = Succ k`, which computes to `Succ (k * 1) = Succ k`" (`10-proofs.md:64`): the as-written
line and a "computes to" line. The panel shows only the second (and in a third notation,
`k * 1 + 1`).

**After `rewrite`.** `theorem rw1 (n m: Nat) (h: n = m): n + n = m + m := rewrite h in ?`
prints `before ⊢ n + n = m + m / rule n = m / after ⊢ m + m = m + m`: fine, nothing to
compute. With a definition that matches at once:

```
def cost: Light → Nat → Nat
  | Red, n => (n * n + 3 * n + 7) * (n + 1) + (n * n + 5) * (n + 2) + n * (n + 4)
  ...
theorem rwCost (a b: Nat) (h: a = b): cost Red a = cost Red b := rewrite h in ?

in `rwCost`, rule 1 of 1 of `rewrite`
  before ⊢ a + (a + (a + (a + (a + (a + (a + ((a * a + (3 * a)) * (a + 1)))))))) + (a + (a + (a + (a + (a + (a * a * (a + 2))))))) + (a * (a + 4)) + 17 = b + (b + … + 17
  rule   a = b
  after  ⊢ b + (b + (b + (b + (b + (b + (b + ((b * b + (3 * b)) * Succ b))))))) + … + 17 = …
```

Even the "before" isn't what was written: `cost Red a = cost Red b`. The rewrite itself is
right; only the printing computes. (`(a + 1)` before and `Succ b` after is a separate small
inconsistency of `Shown`.)

**A large definition next to a folded one.** `theorem totalCons (n: Nat) (ns: List Nat):
total Red [n, ..ns] = cost Red n + total Red ns` prints

```
⊢ total Red [n, ..ns] = n + (n + (n + (n + (n + (n + (n + ((n * n + (3 * n)) * (n + 1)))))))) + (n + (n + (n + (n + (n + (n * n * (n + 2))))))) + (n * (n + 4)) + total Red ns + 17
```

The left side stays folded (`total` doesn't match at once); `cost Red n` on the right, which
the reader wrote, is unfolded and its numbers moved to the end.

**A goal that computes away.** `theorem withLet (n: Nat): n + 0 = n` with two `let`s and `?`
prints `⊢ n = n`: the reader sees no `+ 0` and might not realise `rfl` is the whole proof
because of the computation.

### 1.3 What `rfl`'s message says in the same place **[ran]**

```
theorem wrongSelf (m: Move): beats m m = True := match m with | Rock => rfl | …

[E-REFL] `rfl` can't prove this
  `beats m m` and `True` aren't equal
  Note 1: computing the left side gives `False`
```

So the error message already uses the recommended shape: the side as written, then "computing
… gives". (It shows `beats m m`, not `beats Rock Rock`, inside the `Rock` arm: the message
reads the statement before the arm's substitution. A bug worth a ticket, §8.)

### 1.4 What would change with as-written read-back, and one trap

With `AsWritten`, the values above would print as `beats Rock Rock = False`, `Succ k * 1 =
Succ k`, `cost Red a = cost Red b`, `n + 0 = n`, because `match` on a variable substitutes
into the glued calls (`substitute_folded`, folded-goals.md §1.3) and `rewrite` builds its
next goal from the goal as written (goal-as-written.md stage 1) **[inferred from the code
read, not run: there is no switch to print with `AsWritten` today]**.

The trap: a statement's `match` is a lifted helper. Today `liftedWhole` prints
`⊢ Lifted.liftedWhole.%match1 b n ≤ n` when stuck **[ran]**, and in the arms `Shown`
computes the helper away. As written, the arms would print `…%match1 True n ≤ n` too. That
is SW-1004 (goal-printing-gaps.md stage D: print a lifted helper as `(match … with …)`); it
should land first.

## 2. Other provers

### 2.1 Lean 4

- **What a goal shows.** The goal is printed after instantiating metavariables only,
  `ppExpr (← instantiateMVars mvarDecl.type)` (folded-goals.md §3, from `PPGoal.lean`)
  **[cited there]**. After `cases m` on `beats m m = false` the goals are `case Rock: beats
  Move.Rock Move.Rock = false` and so on **[recalled]**. Computing is a tactic: `simp only
  [beats]`, `dsimp`, `unfold beats`, `decide`, `rfl`; `#reduce` evaluates on request.
- **Hypotheses.** Listed in order, name and type; inaccessible names (shadowed, or made by
  a tactic) get `✝`; a `let` shows `x : T := v` **[cited: Lean reference, "Reading proof
  states"]**. `cases h : m` keeps an equation `h : m = Rock` if asked for **[recalled]**.
  The infoview's filters hide type, instance or inaccessible assumptions and let-values,
  can put the target first, and can shrink side goals **[cited: vscode-lean4 manual]**.
- **Steps.** "When a proof goal changes as the result of a tactic operation, the
  corresponding part of the proof state that changes is highlighted using red or green"
  **[cited: manual]**. When the last goal closes the tactic state says "No goals", and a
  gutter mark shows a theorem with no errors or `sorry` **[cited: manual; "No goals"
  recalled]**.
- **Cursor.** Follows the cursor; the tactic state at a tactic, the expected type in a term
  **[cited]**.
- **Large terms.** `pp.deepTerms` (default off: terms deeper than
  `pp.deepTerms.threshold`, 50, print as `⋯`), `pp.proofs` (proofs inside terms print as
  `⋯`), `pp.maxSteps` (5,000 nodes); hovering a subterm in the infoview shows its type and
  docs; clicking pins it **[cited: reference and manual]**.
- **Learner/expert.** The as-written goal ties directly to the source; the price is that a
  beginner has to learn that `rfl`/`decide` computes even though the goal doesn't show it.
  Experts get `simp?`, `conv`, widgets.

### 2.2 Rocq

- **What a goal shows.** As written: after `destruct m`, `beats Rock Rock = false`; the
  user writes `simpl`, `cbn` or `reflexivity` **[recalled; Software Foundations is written
  this way]**. `simpl` "reduces a term to something still readable", `cbn` is the more
  predictable version, `unfold` one constant (folded-goals.md §3) **[cited there]**.
- **Hypotheses.** `H : T`; local definitions `n := 0 : nat` **[cited: refman, proof
  mode]**; shadowing gets fresh names (`H0`, `n0`) **[recalled]**. "The local context is
  only shown for the first goal" **[cited]**.
- **Steps.** `Set Diffs "on"` highlights added tokens green, `"removed"` also reprints
  removed ones red; each goal is compared with its predecessor, hypotheses "matched by name
  (order is ignored)" **[cited: refman]**. Proof General and VsRocq show it; the refman says
  not to use it in RocqIDE **[cited]**.
- **Cursor.** Step by step through a locked region in the classic IDEs; continuous in
  VsRocq and coq-lsp (goal-at-any-point.md §1.1) **[cited there]**.
- **Large terms.** `Printing Depth`/`Printing Width`, `Set Printing All` for the other
  direction **[recalled]**.
- **Learner/expert.** SF teaches `simpl` as a visible step: the reader watches the goal
  change. Explicit, but more typing.

### 2.3 Isabelle

- **What a goal shows.** As written: `apply (cases m)` gives subgoals with `Rock` put in;
  `simp` computes **[recalled]**. In Isar the claim is restated by the user (`show "beats
  Rock Rock = False"`), and `?thesis` names it.
- **Hypotheses.** Premises of each subgoal (`⋀x. A ⟹ B`); in Isar, named facts the user
  wrote; `print_cases` shows a case's `fix`/`assume` in source notation (goal-at-any-point.md
  §1.1) **[cited there]**.
- **Steps, cursor.** The Output panel shows the state after the command at the cursor; a
  State panel can be frozen to compare with an older state **[cited there]**. No diffs.
- **Large terms.** `goals_limit`, `show_types`; hovering a term in the output shows its type
  **[recalled]**.

### 2.4 Agda

- **What a goal shows.** "By default, terms and types printed by interactive commands will
  be simplified by evaluating certain functions … only those functions that match on a
  constructor pattern or a projection copattern will be reduced, as well as primitive
  functions … `(suc x) + y` will be simplified to `suc (x + y)` but `id 42` will be printed
  as is." With a prefix: **`C-u` "without any simplification"**, `C-u C-u` "the full normal
  form", `C-u C-u C-u` "the weak-head normal form" **[cited: Agda emacs-mode docs]**. This
  is today's Stitchwort rule, and it is the one prover that lets the reader choose per query.
- **Goal vs have.** `C-c C-,` goal and context; `C-c C-.` adds the type of what is typed in
  the hole ("Have"), `C-c C-;` checks it against the goal **[cited]**.
- **Hypotheses.** The context in scope order; toggles for hidden and irrelevant arguments
  (`C-c C-x C-h`, `C-c C-x C-i`); shadowed names greyed **[cited]**.
- **Steps, cursor.** Only at holes, on command. No diffs. Case split `C-c C-c` writes the
  clauses **[cited]**.
- **Learner/expert.** Simplified goals show a beginner what's left (`suc (x + y)`); the cost
  is the one Matt hit: the statement is gone after a split. Experts reach for `C-u` often
  enough that it is a well-known idiom **[recalled]**.

### 2.5 Idris 2

- **What a goal shows.** Simplified like Agda: after splitting `plus_commutes` on `n`, the
  holes are `m = plus m Z` (from `plus Z m = plus m Z`) and `S (plus k m) = plus m (S k)`;
  the docs explain the first "has been reduced from `plus Z m`" **[cited: Idris 2,
  "Pattern matching proofs"]**. No as-written option that I found **[inferred]**.
- **Hypotheses, holes.** Named holes; `:t ?hole` prints the context above a dashed line and
  the goal below; case split, add clause and proof search act on a hole
  (goal-at-any-point.md §1.1) **[cited there]**.
- **Learner.** The Idris tutorial has to stop and explain each reduced hole in prose, as the
  Stitchwort book and guide do.

### 2.6 F\* and Dafny

No goal display in this sense. F\*'s `dump` prints the proof state inside a tactic; Dafny
reports a failing assertion, and its IDE can show a counterexample (goal-at-any-point.md
§1.1) **[cited there]**. What they offer the comparison is the counterexample: Stitchwort's
`rfl` message already gives one (§1.3), and a goal that computes to `False`-like forms could
too, later.

### 2.7 "The goal computes away"

The case Matt hit, a goal that is closed by computation, is handled three ways:

| System | Display after the split | How the reader learns it computes |
|---|---|---|
| Lean, Rocq, Isabelle | `beats Rock Rock = False` | They try `rfl`/`decide`/`simp`/`reflexivity`, or run `simp only`/`cbn` and see the result |
| Agda, Idris, Stitchwort today | `False = False` | They see it, but no longer see the statement |
| Stitchwort's `rfl` error | `beats m m` and `True` … "computing the left side gives `False`" | Both, in one message |

No prover I looked at prints both forms in its goal display. That is the gap this note
proposes to fill, using a form Stitchwort's messages and its guide's prose already use.

## 3. The comparison table

| | Lean 4 | Rocq | Isabelle | Agda | Idris 2 | Stitchwort today |
|---|---|---|---|---|---|---|
| **Goal after substitution** | as written | as written | as written | simplified (calls that match at once); per query: as written, full, head | simplified | simplified, repeated |
| **User control of form** | tactics (`simp only`, `unfold`, `dsimp`) | tactics (`simpl`, `cbn`, `unfold`) | `simp`, restating in Isar | `C-u` prefixes per query | none found | none in the panel; restate with `(? : T)` |
| **Hypotheses: order** | scope | scope | premises | scope | scope | dependency, then scope |
| **Shadowed** | `x✝` | renamed `x0` | — | greyed | — | `n✝`; superseded ones dropped |
| **Let values** | `x : T := v`, filter to hide | `x := v : T` | — | — | — | `x: T := v`, proofs show only their type; let names inlined into later types |
| **Replaced by a split** | gone (`cases h :` keeps an equation) | gone | gone | gone | gone | gone |
| **Step before/after** | cursor before/after a tactic | step forward/back | Output at command, frozen State | — | — | built: before, rule, after, `+` added names |
| **Diff highlighting** | red/green in the infoview | `Set Diffs`, hypotheses by name | — | — | — | none |
| **Cursor vs command** | follows cursor | stepping or continuous | follows cursor | commands at holes | commands at holes | follows cursor everywhere (D3497) |
| **Large terms** | `⋯` past depth 50 / 5,000 nodes / proofs; hover a subterm | depth and width limits | `goals_limit` | — | — | 4,000 characters, `…` innermost first; CLI cuts lines at 400 |
| **Learner** | statement kept; computing is invisible until tried | statement kept; computing is a visible step | statement kept | what's left is visible; statement lost | same as Agda | same as Agda, unevenly |

## 4. Options

All options keep how a goal is *found* and what `rewrite`/`match` search; they change only
printing. Search (D2542) reads the goal with `quote_folded`, in which a call that matches at
once is computed (`rewrite/as_written.rs:294`) **[checked]**; a rule about `cost Red n`
still rewrites a goal containing `cost Red n` today **[ran: `rw.sw`]**, so showing the call
doesn't promise anything search can't do. D3090's rule (the printer never refolds a
definition) holds for all of them: `AsWritten` keeps calls that are in the value, it doesn't
invent them.

### A. Keep today's form; fix the book and docs

Print simplified, as now; change book 2.1 to say `⊢ False = False` and explain why.

- **Pro:** no code; matches Agda and Idris; the panel shows what `rfl` sees.
- **Con:** the statement disappears exactly where a learner is trying to connect it to the
  proof (every arm of `noSelfWin` reads `False = False`); uneven (`play` stays, `beats`
  goes, §1.2); a reader's own call can turn into a 120-character polynomial; disagrees with
  `rfl`'s message, which shows the written side. Long goals stay long.
- **Cost:** a paragraph of the book.

### B. As written only (Lean, Rocq, Isabelle)

Print with `quote_as_written`; nothing computed.

- **Pro:** the goal is the statement with the substitution, always; short; easy to explain
  ("the goal is your statement with `Rock` for `m`"); matches the three most used provers.
- **Con:** a learner no longer sees *why* `rfl` works (`beats Rock Rock = False` doesn't look
  closed); the guide's `timesOne` explanation needs the computed form (`Succ (k * 1)`) to
  see that `Eq.cong Succ` is next, which the reader would have to work out or get from an
  error. Stitchwort has no `simp only` to ask for it.
- **Cost:** small (one read-back mode), plus SW-1004 first.

### C. As written, with a "computes to" line (recommended)

Print the as-written goal; when the simplified form (today's line) prints differently, put it
underneath as `computes to …`. Steps show it for the *after* goal. Hypotheses as written,
no second line.

```
in `noSelfWin`, arm 1 of 3, `| Rock`
  before ⊢ beats m m = False
  after  ⊢ beats Rock Rock = False
           computes to False = False
```

- **Pro:** both questions answered at once: "what am I proving" and "what does the checker
  see". Same shape as `rfl`'s message (§1.3) and the guide's prose (§1.2). The first line is
  short and stable; the second is the thing to look at when stuck. Experts who only want one
  can ignore a dim line. Agents get both in `--json`.
- **Con:** two lines where there was one (only when they differ: `n + n = m + m` stays one
  line); a long computed form still has to be shown somehow (folded, below); a third read-back
  to keep honest (as written, simplified, folded for search) **[inferred]**. The `computes to`
  line can be the same for all arms (`False = False` three times), but now under three
  different first lines.
- **Long goals.** The `computes to` line is cut to one line's width with `…` (the message
  limit, 240 characters, as error notes are) and, in the panel, opens in full on click; the
  CLI prints it in full with `--full-goals`. A computed line that is longer than five times
  the written one is shown folded by default ("computes to (1,240 characters) ▸")
  **[a call to make in the lane]**.
- **Cost:** about 90 minutes, Sonnet: `Pending`/`GoalSnapshot`/`ContextAt` gain a computed
  text (`goals.rs`), `value_for_goal_as_written` beside `value_for_goal` (`pretty.rs`), the
  JSON gains `targetComputed` and `step.afterComputed` (version 2), `client.js` and the
  playground render the line dimmed, the CLI prints it. Then a docs-and-snapshots lane
  (Sonnet or DeepSeek, about 45 minutes): every goal snapshot in `examples/` changes,
  migration cost not counted (D2303) **[estimated]**.

### D. Agda's levels, with a switch

A setting (and a panel button) choosing as written / simplified / full normal form /
head-normal, for every goal shown.

- **Pro:** expert control, a known design; full normal form would answer "what is this
  really" for a stuck `omega`.
- **Con:** a learner won't find it, and the default still has to be chosen (so it doesn't
  answer the book's problem by itself); four forms to test and document; a global switch
  makes screenshots and the book disagree with a user's panel. Full normal form of real goals
  is huge (AoC goals hit the 4,000-character limit today **[cited: goal-readback.md §1]**).
- **Cost:** C's plumbing plus a setting, a request parameter and UI: about 2 hours
  **[estimated]**.

### E. Per-goal "show computed" (C without the line by default)

As written, with a small control on each goal in the panel ("≡ computed") that opens the
simplified form.

- **Pro:** one line by default; the computed form one click away.
- **Con:** the CLI and hover have no click (they need C's line or a flag); a learner doesn't
  know the click is the answer to "why does `rfl` work here". Good as C's way of showing a
  *long* computed line, which is what C proposes.

### F. Diffs between steps (independent of A–E)

Highlight the changed part of the goal between before and after, as Lean and Rocq do; match
hypotheses by name.

- **Pro:** with before/after built (D3497), this is the missing half of Lean's infoview; it
  finds `Rock` put in for `m` at a glance; useful for experts in long goals.
- **Con:** a token diff of two long arithmetic forms is noisy; with option C the as-written
  lines diff cleanly (`m` → `Rock`), which is an argument for C first.
- **Cost:** a Myers diff on tokens in `client.js` and the playground, about 60 minutes
  **[estimated]**; nothing server-side.

### G. Hypotheses: keep `let` names, show what a split replaced (small, independent)

- A `let`'s name used in a later hypothesis's type prints inlined (`fact: n + n = n + n` for
  `twice = n + n`, §1.1). Keeping it needs the let's value glued like a call; that is a
  read-back change, not a printer one **[inferred]**. Worth a ticket, not this note's.
- An arm doesn't say that `m` is now `Rock` except through its header. The step view could
  add `m ↦ Rock` beside `+ k: Nat` (Lean's `cases h : m` gives the equation as a
  hypothesis). Cheap, purely in the step's `adds` **[inferred]**.

## 5. Recommendation and stages

**C, then F; G's second item with C; not D now.** C answers the book's problem without hiding
what `rfl` sees, and it is the form Stitchwort's messages and prose already use, so the panel
stops being the odd one out. D can be added later on C's plumbing if experts ask for full
normal form; nothing in C closes that door.

1. **SW-1004 first** (goal-printing-gaps.md stage D, lifted `match` printed as `match`):
   otherwise as-written goals show `%match1` helpers more often (§1.4). Already filed, Sonnet,
   about 60 minutes.
2. **Stage 1: as written + computes to** (option C), everywhere goals print: the panel,
   hover on `?`, the playground, `check`'s goal diagnostics, `stitchwort goal` (with and
   without `--at`), `--json` (version 2, `targetComputed`, `step.afterComputed`). Arms show
   `m ↦ Rock` among what they add (G). Sonnet, about 90 minutes. Tests: the goal examples'
   snapshots (`task test:lane AREA=goals`), a new example with the four cases of §1.2.
3. **Stage 2: docs and book** (§6). DeepSeek or Sonnet, about 45 minutes.
4. **Stage 3: diffs** (option F) in the panel and playground. Sonnet, about 60 minutes.

**Risk.** Where the goal value itself was built unfolded (a `match e:` that had to generalise
inside a definition, some `cases` goals), "as written" is already the unfolded term and there
is no second line; that is no worse than today. Where `AsWritten` keeps a call that computes
hugely (`countDown 100000 []`), the first line gets shorter, not longer. I didn't run
`AsWritten` on real goals (there is no switch), so the share of AoC goals that would get a
second line is unknown; stage 1 should count it on the examples before the docs stage
**[inferred]**.

## 6. What changes in the book and the docs

- **Book 2.1** keeps its text ("In the first arm it shows `⊢ beats Rock Rock = False`"), with
  the panel's second line and one sentence:

  > ```
  > ⊢ beats Rock Rock = False
  >   computes to False = False
  > ```
  >
  > Inside the arm for `Rock`, the checker knows that `m` is `Rock`, so the goal says `Rock`
  > where it said `m`. The second line is what the goal computes to: `beats Rock Rock` is
  > `False`, by `beats`'s last arm, and both sides are now the same. That is when `rfl`
  > works. Replace each `?` with `rfl` …

  Book 2.3's `otherSide (play Rock theirs) = play theirs Rock` is unchanged (nothing
  computes). Later chapters that quote goals need a check.
- **Guide** `10-proofs.md`: line 127 ("The goal is shown computed") becomes "The goal is
  shown as written, with what it computes to underneath when that differs"; the `timesOne`
  hole output gains its `computes to k * 1 + 1 = Succ k` line, which makes line 64's prose
  visible.
- **`docs/syntax.md`** "Goals" (line 1659, "Goals are shown *computed*, as `rfl`'s messages
  are") and the `goal --at` section (line 1734, `n + 0 = n` "shows `⊢ n = n`").
- **Feature tour** (`web/guide/`): the split-from-a-hole page (SW-2885) shows the two lines.

## 7. Decisions for Matt

Placeholders; the orchestrator numbers them.

- **D-a: How a goal is printed.** As written (the statement with the split's values put in),
  and underneath, when it differs, `computes to` and the computed form; everywhere goals are
  shown (panel, hover, playground, `check`, `stitchwort goal`, JSON). [rec: **yes**. It keeps
  the statement the reader wrote, which Lean, Rocq and Isabelle all do, and keeps what `rfl`
  sees, which Agda's default does; Stitchwort's `rfl` messages and guide already explain goals
  this way. Alternatives: as written only (B: the reader loses why `rfl` works), keep today
  and fix the book (A: every arm of `noSelfWin` reads `False = False`).]
- **D-b: A switch for the form (Agda's levels).** Not now; revisit if experts ask for the full
  normal form. [rec: **not now**. C shows both forms without a setting; a switch makes the
  book and a user's panel disagree, and learners don't find it.]

Calls I made (the orchestrator may overrule): hypotheses get no `computes to` line (they
would double the context; the panel can open one on click later); a long computed line is
cut at 240 characters and folded in the panel; arms list `m ↦ Rock` with the names they add;
diffs (F) are a separate later stage; SW-1004 goes first.

## 8. Files run, sources, what this note didn't do

**Scratch files [ran]**, under the session scratchpad: `book/` (a copy of `book/` with
`noSelfWin`'s arms, `otherSideSwaps`' first arm and `otherSideTwice`'s first arm made `?`,
plus `swapsRock` and `wrongSelf`); `ex/ex.sw` (`timesOne`, `doubleAdd`, `rw1`, `withLet`);
`ex/big.sw` (`cost`, `costPos`, `totalCons`, `rwCost`); `ex/rw.sw` (rewriting with
`costRed` on a goal that mentions `cost Red n`); `ex/lifted.sw` (a statement with a
`match`). Commands: `stitchwort check FILE`, `stitchwort check Book.Cases`, `stitchwort goal
--at FILE:LINE:COL [--json]`.

**Sources [cited]**, read 11 Nov 2026:
- Agda, Emacs mode: <https://agda.readthedocs.io/en/latest/tools/emacs-mode.html>
- vscode-lean4 manual: <https://github.com/leanprover/vscode-lean4/blob/master/vscode-lean4/manual/manual.md>
- Lean reference, "Reading proof states": <https://lean-lang.org/doc/reference/4.30.0/Tactic-Proofs/Reading-Proof-States/>
- Rocq reference manual, proof mode (diffs, local definitions): <https://rocq-prover.org/doc/master/refman/proofs/writing-proofs/proof-mode.html>
- Idris 2, "Pattern matching proofs": <https://idris2.readthedocs.io/en/latest/proofs/patterns.html>
- And the surveys in [folded-goals.md](folded-goals.md) §3 and
  [goal-at-any-point.md](goal-at-any-point.md) §1, which this note reuses rather than
  repeats.

**Didn't do.** No code, no prototype of `AsWritten` printing (so §1.4's forms are inferred
from the read-back code, not run); no measurement of how many goals would get a second line;
didn't open the playground; didn't check Isabelle's or Rocq's display in a running system
(marked **[recalled]**).

**Findings for tickets.**
1. `rfl`'s E-REFL message inside a `match` arm shows the statement before the arm's
   substitution: "`beats m m` and `True` aren't equal" in the `Rock` arm (§1.3). It should
   say `beats Rock Rock`.
2. `docs/syntax.md:1659` says goals are shown computed "as `rfl`'s messages are"; `rfl`'s
   messages show the side as written and a "computing gives" note. Fix with stage 2, or now
   if D-a is no.
3. `Shown` prints the same sum as `(a + 1)` before a `rewrite` and `Succ b` after it
   (`rwCost`, §1.2).
4. A `let`'s name is inlined into later hypotheses' types (`fact: n + n = n + n` for
   `twice = n + n`, §4 G).
