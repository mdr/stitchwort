# Proposal: a premise left out at a call and closed by computing

**Status:** draft 1, 22 November 2026, SW-4557 (Opus, paper lane). Follows SW-4553's
traversal-lemma pilot ([review](../reviews/SW-4553-traversal-lemma-pilot.md)), whose
`rebuildsN` lemmas end every call with `(v1 => byComputing)`. The end state is user-visible
language, so it is Matt's: [§7](#7-recommendation) ends with the question.

Labels: **[checked]** means read in the source at the place given (worktree at `00acae30e`);
**[run]** means a scratch file checked with the main checkout's release `stitchwort check`
on 22 Nov 2026 (files in the lane's scratch folder, quoted below); **[est.]** is an estimate.

**The short answer.** Let `auto` prove what `byComputing` proves. Today an `[auto h: P]`
argument is found from a hypothesis of exactly type `P` or a decision procedure, and it never
introduces a `∀` or tries computing: it rejects `∀ (v: Nat) => Succ v = Succ v` (`E-AUTO-NONE`)
and even `C (blank t) = C (blank t)` (`E-AUTO-STUCK`) **[run]**. With two additions to its
search (introduce a goal's leading `∀`/`→` binders when nothing decides the goal whole, and
close an equation whose sides compute to the same value), a lemma states its always-computed
premise as `[auto rebuilt: ∀ (v1: a1) => g2 (bl1 v1) = blr (g v1)]` and its calls drop the
tail: `rebuilds1 deaf.expr (exprBlanks on deaf a)`. No new syntax, so neither formatter
changes; a call can still give the proof by name, `[rebuilt := …]`. It would remove 96
tails (about 2,100 characters, a handful of lines) at the calls of nine lemmas, all in
`tools/fmt` ([§5](#5-the-call-sites-it-would-clean)).

## 1. The problem

After SW-4553 an arm of `exprBlanks` reads **[checked]** (`tools/fmt/src/Fmt/TraverseFail.sw:52-81`):

```
| Paren _ a _ | Spread _ a | RecordField _ _ a | NamedArg _ _ _ a _ | Section a | Prefix _ a | Facts _ _ a =>
  rebuilds1 deaf.expr (exprBlanks on deaf a) (v1 => byComputing)
| CtorFields a b | Infix _ a _ b | Annotation _ a _ b _ =>
  rebuilds2 deaf.expr (exprBlanks on deaf a) (exprBlanks on deaf b) (v1 v2 => byComputing)
```

The lemma (`crates/elab/src/std/Fail/Walk.sw:310`, now `Fail.toResultRebuilds1`) **[checked]**:

```
theorem Fail.toResultRebuilds1 ∀ [t1 s1: () → {Fail} a1] [bl1: a1 → a1] [g g2: a1 → r] [k: r → {Fail} q]
    [blr: r → r] [blq: q → q]
    (deaf: ∀ (z: r) => Fail.toResult (() => k (blr z)) = (Fail.toResult (() => k z)).map blq)
    (h1: Fail.toResult s1 = (Fail.toResult t1).map bl1)
    (rebuilt: ∀ (v1: a1) => g2 (bl1 v1) = blr (g v1)):
    …
```

`rebuilt` says "blanking the rebuilt node is rebuilding around the blanked child". Once
unification has fixed `g`, `g2` and `blr` from the arm's goal it is true by computing: one
step of the blanking function on a known constructor. Every one of the 34 calls closes it
with `byComputing` under as many lambdas as there are children. The tail carries no
information, is the same at every call, and pushes three calls onto a second line. The
pilot's write-up called it "noise in every arm".

What's wanted: the lemma says once that the premise is found by computing, and calls leave
it out, while a call where computing isn't enough can still give a proof.

## 2. What the language has today

| Mechanism | Written | Filled when, how | Could it fill `rebuilt`? |
|---|---|---|---|
| Implicit `[x: T]` | header | by unification during the call | No: a proof of an equation isn't fixed by unifying types |
| Instance `[auto i: I T]` | header | instance search (`interfaces.rs`) | No: not an interface |
| Auto `[auto h: P]` | header; at a call `[h := …]` | after the declaration is elaborated, `auto::prove` (`crates/elab/src/auto.rs:298`) **[checked]**: a hypothesis of exactly type `P`; a lexicographic split; a decision procedure (an `instance` returning `Decidable …`, or `DecEq` for an equation) run to `True`; then facts in scope, conjunction parts, `arithmetic` within a budget, a contradiction, rules | No, **[run]** below |
| Parameter default `(x: T := e)` | header; at a call `(x := …)` | `e` is checked **once, at the declaration**, for any values of the earlier parameters, and becomes a helper `f.x%default` (`docs/syntax.md`, Parameter defaults) | No, **[run]** below |
| `byDecision` | in the body | an `[auto h: P]` argument under a name | No: same search as auto |
| Premises of a `rewrite` rule | left off or `_` in the rule | unification, a hypothesis, then `arithmetic` (`docs/syntax.md`, Premises) | Not outside `rewrite`, and not by computing |

What the search does with the shapes in question **[run]** (scratch files `auto_forall.sw`,
`stuck.sw`, `default_forall.sw`, `auto_param_default.sw`, `auto_named.sw`):

```
theorem lem ∀ (f g: Nat → Nat) [auto same: ∀ (v: Nat) => f v = g v]: f 1 = g 1 := same 1
theorem use: Succ 1 = 1 + 1 := lem (v => Succ v) (v => v + 1)
-- [E-AUTO-NONE] no way to decide `∀ (v: Nat) => Succ v = Succ v`

theorem lem ∀ [g g2: T → T] (t: T) [auto same: g2 (blank t) = blank (g t)]: …
theorem use (t: T): C (blank t) = blank (C t) := lem [g := C] [g2 := C] t
-- [E-AUTO-STUCK] can't decide `C (blank t) = C (blank t)` here

theorem lem ∀ (f g: Nat → Nat) (same: ∀ (v: Nat) => f v = g v := v => byComputing): …
-- [E-REFL] `byComputing` can't prove this … Note 2: a default must work for any values of
-- the earlier parameters (`f`, `g`), since a call may give them and leave this one out

theorem lem ∀ (f g: Nat → Nat) [auto same: ∀ (v: Nat) => f v = g v := v => byComputing]: …
-- [E-PARSE] only a definition's parameter or a field can have a default value

theorem use: Succ 1 = 1 + 1 := lem (v => Succ v) (v => v + 1) [same := v => byComputing]
-- checked (an auto argument given by name)
```

Two gaps, then: `auto` doesn't introduce binders, and it doesn't try conversion. The second
is a gap on its own: "can't decide `C (blank t) = C (blank t)`" is a message about an
equation whose sides are already the same. The search decides an equation through its type's
`DecEq`, whose test is stuck on the variable `t`, and nothing after that compares the sides.

The search is run when the declaration's elaboration is done (`solve_obligations`,
`auto.rs:106`) **[checked]**, so `g`, `g2` and `blr` are fixed from the arm's goal by then:
the timing auto already has is the timing this premise needs.

## 3. The options

### A. A parameter default checked at each call

```
(rebuilt: ∀ (v1: a1) => g2 (bl1 v1) = blr (g v1) := v1 => byComputing)
```

- **Elaborator.** Today's rule checks a default once, for any earlier values, and fails here
  (`E-REFL` above). It would have to change, for a default of a proposition, to "elaborate the
  default at each call that leaves it out, against the parameter's type with the call's
  values, once the call's other unknowns are solved". That is Lean's `autoParam`
  (`(h : p := by tac)`, run by the elaborator when the argument is missing; see the table in
  [signature-defaults.md](signature-defaults.md) §3).
- **Failure.** The default's own error (`E-REFL`) at the call, with a note: "`rebuilt` is left
  out, so its default `v1 => byComputing` is checked here; give it by name: `(rebuilt := …)`".
- **Cost per call.** The written proof's, as today **[est.]**.
- **Against it.** It changes the meaning of an existing rule for one kind of parameter, so
  `(ok: size = 8 := byComputing)`, an error today on purpose, would become a per-call check
  and its mistake would surface only at the calls. The default is source text elaborated at
  every call in the declaring module's scope (its imports, not the caller's), with the
  parameters bound to the call's values: elaborating in another module's scope is new
  machinery. Lean has the same hygiene issue with `autoParam`'s tactic syntax.

### B. `auto` proves what computing proves (recommended)

```
theorem Fail.toResultRebuilds1 ∀ … (deaf: …) (h1: …)
    [auto rebuilt: ∀ (v1: a1) => g2 (bl1 v1) = blr (g v1)]: …

| Paren _ a _ | … => rebuilds1 deaf.expr (exprBlanks on deaf a)
```

- **Syntax.** None new. An auto parameter may already come last in a header
  (`Grid.of (rows: List (List a)) [auto nonEmpty: …]`, `aoc/src/Aoc/Common/Grid.sw:162`)
  **[checked]**, and a call gives one by name, `[rebuilt := …]` **[run]**.
- **Elaborator.** Two additions to `auto::prove`, in this order:
  1. *Binders.* After a hypothesis of exactly the goal's type and a decision procedure for
     the goal as a whole have both failed (so a `∀` over a finite type that some procedure
     decides is still decided whole), a goal `∀ (x: A) => B` or `A → B` is introduced: `x` (or
     the hypothesis) joins the context, `B` is proved by the same search, and the proof is
     `x => …`. The hypotheses of an `→` are then in scope for step 1 of the inner search,
     which is what the `…Weaker` lemmas' premises need (`h => byComputing` today, below).
  2. *Computing.* When the decision procedure is stuck (the `_` branch, `auto.rs:332`), an
     equation `a = b` whose sides are convertible is closed by `byComputing` (`Term::Refl`),
     before the facts, `arithmetic` and the rest. Placed there, nothing accepted today changes
     its proof: an equation a decision procedure settles keeps `d.sound byComputing`. (Placed
     before the decision procedure it would be cheaper, and `Refl` is a smaller term than
     `d.sound Refl`, but every equation auto proves today would change its proof and hash;
     the migration doesn't count, D2303, so this is the build lane's call on measurement.)
  The conversion test is the one `byComputing` already runs when written, under
  `undo::attempt` so a failed comparison leaves no unknowns solved.
- **Failure.** When the sides compute to different values, the error is `E-AUTO-STUCK`, as
  today, with the notes `byComputing` gives (`E-REFL`): "with `v1` introduced, the two sides
  compute to `Paren o (blank v1) c` and `Paren o v1 c`", plus the call
  (`so rebuilds1 can't be called`, as auto messages already name it, `Obligation::call`) and
  "give it by name: `[rebuilt := …]`". `examples/reject/undecidable-auto.sw`
  (`[auto ok: ∀ (n: Nat) => n = 0]`) stays rejected; its code changes from `E-AUTO-NONE` to
  `E-AUTO-STUCK` (`n = 0` with `n` introduced), unless the build keeps `E-AUTO-NONE` for a
  goal whose introduced body no procedure decides at all. Either is fine; the example's
  expectation moves with it.
- **Cost per call.** A success goes through the hypothesis check, the decision procedure (built
  and run until it is stuck on the introduced variable) and then one conversion. Measured on a
  five-constructor type **[run]** (`stuck.sw` against `stuck_explicit.sw`): the declaration
  with the auto premise spent 1,927 steps failing, the one with `byComputing` written 815; so
  the search's failing steps cost about 1,100 there. For `Expr` (40 constructors, a larger
  derived `DecEq`) **[est.]** 1,000 to 3,000 extra steps per call, so 75 calls in
  `TraverseFail` add 75k to 225k steps to the file's 6.7M (1 to 3%); with conversion before
  the decision procedure, about the same as written **[est.]**. Kernel cost unchanged: the
  term is the same `λ v1. Refl`.
- **Against it.** The lemma's reader sees `[auto rebuilt: …]`, "found", not "by computing";
  the doc comment has to say so. `auto` gets stronger everywhere, so a failing auto argument
  costs a conversion more before it fails (small next to the decision search it already runs).
  An `auto` premise can't be given positionally: the two calls in `Fail/Walk.sw` that pass
  `toResultAlikeN` a real `step` become `[step := …]`.

### C. An auto parameter with a stated proof

```
[auto rebuilt: ∀ (v1: a1) => g2 (bl1 v1) = blr (g v1) := v1 => byComputing]
```

- **Syntax.** New: a default on an `auto` parameter, `E-PARSE` today **[run]**, so both
  formatters and the self-hosted formatter's slices would need it.
- **Elaborator.** The written proof, not the search, is elaborated at each call once the
  declaration is done, against the instantiated type. It keeps A's hygiene problem (source
  text elaborated per call in the declaring module's scope) unless stage 1 allows only
  lambdas ending in `byComputing`, which is a special syntax for B's one case.
- **Failure.** The proof's own error at the call, with a note naming the parameter.
- **Cost per call.** The written proof's **[est.]**: the cheapest.
- **For it.** The signature says how the premise is closed, and the proof could be any
  tactic (`arithmetic`, `cases`), not only computing. Worth reaching for if a premise turns
  up that is always closed by some *other* tactic; none has in this count.

### D. `_` at the call falls back to auto

```
rebuilds1 deaf.expr (exprBlanks on deaf a) _
```

- **Elaborator.** An explicit proof argument written `_` that unification leaves unsolved
  is handed to B's search instead of being an error. The lemma doesn't change, and the
  partly-computed premises (`Parse.givesWeaken`'s `implies`, 10 of 25 calls) could use it too.
- **Against it.** A `_` at every call still, and every unsolved proof hole becomes a search,
  so a hole left by mistake may be filled silently or fail later with a search's message
  instead of "couldn't infer". It also needs B's search to be useful.

### E. No change

Keep the tails. They are correct and cost nothing to check. The lemmas can't absorb them:
the premise depends on the constructor at each call, which is the lemma's whole point.

## 4. Comparison

| | Syntax | Lemma writes | Call writes | Per-call cost | Formatters | Other effects |
|---|---|---|---|---|---|---|
| A | none new; meaning of `:=` changes for propositions | `(rebuilt: P := v1 => byComputing)` | nothing | as written | none | a rule changes; cross-module elaboration |
| **B** | **none** | **`[auto rebuilt: P]`** | **nothing** | **+1k-3k steps [est.]** | **none** | **`auto` closes convertible equations everywhere** |
| C | `[auto x: P := e]` | the proof | nothing | as written | both, plus slices | cross-module elaboration |
| D | none; meaning of `_` changes | unchanged | `_` | B's | none | every proof hole searches |
| E | | | `(v1 => byComputing)` | | | |

## 5. The call sites it would clean

Counted with two scripts in the lane's scratch folder (`count.py`, `ratio.py`) over
`tools/fmt`, `crates/elab/src/std`, `aoc` and `games`:

1. Every argument of the form `(x … => byComputing)` (a lambda whose whole body is
   `byComputing`): **320** (tools/fmt 260, std 40, aoc 20, games 0). Each was attributed to
   the head of the application it is an argument of, by walking back at the same bracket
   depth.
2. For each lemma with three or more of them, its call sites (its name followed by a space,
   outside theorem headers, imports and doc comments) and how many of those pass such a
   lambda, the call scanned to its end (to the next arm or line at a lower indent).

The lemmas whose premise is closed by computing at every call, or nearly:

| Lemma | Where it's defined | Calls | With the tail | Characters |
|---|---|---:|---:|---:|
| `rebuilds1` to `rebuilds4` (`Fail.toResultRebuildsN`) | std `Fail/Walk.sw` | 34 | 34 | 783 |
| `Fail.toResultAlike1`, `Fail.toResultAlike2` | std `Fail/Walk.sw` | 41 in `tools/fmt` + 2 in std | 41 | 883 |
| `fitsWeaker` (`implies: before = True → before' = True`) | `Fmt/TouchSteps.sw` | 9 | 9 | 171 |
| `readyWeaker` | `Fmt/JoinProofs.sw` | 4 | 4 | 94 |
| `refinesOne` (two premises, `left` and `right`) | `Fmt/ToldDeclProofs.sw` | 5 | 8 tails | 152 |
| **Total** | | | **96** | **about 2,100** |

All of these calls are in `tools/fmt` (`TraverseFail.sw` for the first two rows,
`TouchProofs.sw`, `JoinProofs.sw`, `ToldDeclProofs.sw`). Lines saved: three or four (the
tails that wrap, `TraverseFail.sw:78-79`, `371-372`, and `rebuilds4`'s own line at 379), more
if shorter arms let or-patterns merge; the gain is the noise, not the lines.

Partly computed, so left explicit under B (their other calls pass real proofs, which an
`auto` premise would make named): `endsWeaker` 5 of 10, `Parse.givesWeaken` 10 of 25,
`Parse.readsWeaken` 10 of 84, `Parse.readsDone` 6 of 70. Under D these could use `_` too.

Not calls, so not touched by any option: about 50 record literals of proof records whose
fields are `(z => byComputing)` (`header = (z => byComputing)`, `Fmt/BlankProofs.sw:346`,
`Fmt/MergeProofs.sw:18`, …), and `Bool.inspect`'s branches (`(t => byComputing)`, 21), which
are case arms, not premises. The 20 in `aoc` are spread over 19 files and as many lemmas, one
call each. std's own 40 are inside the lemmas' proofs.

The pilot's lesson applies (proof tools came in below their sketches): this count is of
characters at calls, measured, and the line saving is small and stated as such.

## 6. What building B would touch

- `crates/elab/src/auto.rs`: the two steps in `prove`, and the failure notes (reusing the
  `E-REFL` "the two sides compute to" notes).
- `crates/elab/src/std/Fail/Walk.sw`: `rebuilt` and `step` become `[auto …]` in
  `toResultRebuilds1..4` and `toResultAlike1..4`; the two internal calls pass `[step := …]`.
  The local `…Weaker` lemmas and `refinesOne` in `tools/fmt` likewise.
- Calls: drop the ~96 tails.
- Docs: `docs/syntax.md` (the `[auto x: P]` row of the proofs table, the auto limits list,
  `byDecision`), `DESIGN.md` §6, the `auto.rs` module doc, and `docs/guide/10-proofs.md` if it
  describes the search. Examples: `examples/accept/auto-by-computing.sw` (a `∀` premise, an
  `→` premise closed from its hypothesis, a stuck-but-convertible equation),
  `examples/reject/auto-by-computing-differs.sw` (sides that differ, with the notes), and
  `undecidable-auto.sw`'s expected code if it moves.
- Hashes: the lemmas' types (an explicit binder becomes auto) and the calls' application
  nodes change; the proof terms are the same `λ…. Refl`.
- Formatters: nothing (no syntax).

Effort **[est.]**: one Opus lane (the auto search is core elaboration, D2506), from past auto
changes about 1 to 2 hours, then one Sonnet sweep of the calls.

## 7. Recommendation

**The problem.** Lemmas like SW-4553's `rebuildsN` have a premise that is always true by
computing once the call is known, so all 96 calls in the formatter's proofs end with the same
`(v1 v2 => byComputing)`, which says nothing. The compiler's `auto` can't fill it: it doesn't
look under a `∀`, and it doesn't compare the two sides of an equation by computing them, so
today it even rejects `C (blank t) = C (blank t)`.

**The change.** Teach `auto` two things: look under a premise's `∀` and `→` when nothing
decides it whole, and close an equation whose sides compute to the same value, as
`byComputing` does. A lemma then writes the premise as `[auto rebuilt: …]`, and calls leave it
out (or give it by name). No new syntax.

**What it should do.** The 96 tails go (about 2,100 characters in `tools/fmt`, measured; only
three or four lines, measured), and the traversal arms read as a table of constructors and
children's theorems. Each call costs about 1,000 to 3,000 more elaboration steps (estimated:
1 to 3% of `TraverseFail`); kernel checking is unchanged. Everything accepted today stays
accepted with the same proof; `auto` accepts more. If computing doesn't close a premise, the
error shows what the two sides computed to and how to give the proof by name.

**The question for Matt** (the orchestrator numbers it):

> D____: should `auto` also prove what computing proves (looking under `∀` and `→`, and
> closing an equation whose sides compute to the same value), so that a lemma's
> always-computed premise is written `[auto rebuilt: …]` and the formatter proofs' 96
> `(v1 => byComputing)` tails go? [rec: yes; no new syntax; the alternatives, a default
> checked at each call or `[auto x: P := proof]`, change an existing rule or add syntax for
> the same gain]
