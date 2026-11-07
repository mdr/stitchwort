# Proposal: proved instances answer the audit's vacuity warning

**Status:** draft 1, 7 November 2026. Ticket SW-2229, from the trip-journal review
([SW-2219](../reviews/SW-2219-trip-journal.md) §4, D3221). Decisions D3230 and D3231
([§7](#7-questions-for-matt)). Code references were checked at commit `6d1adc97c`.
**[checked]** means read at the `file:line` given; **[run]** means run with the release CLI
on 7 November 2026; **[inferred]** means reasoned from the code, not run.

**The short answer.** When a checked declaration applies a theorem to concrete arguments,
supplying a proof for every hypothesis, the kernel has proved that the hypotheses can hold.
The audit should look for such applications, and when it finds one for a theorem the random
search couldn't satisfy, it should pass the theorem and name the witness ("witnessed by
`Trip.Tests.extendedPinKept`") in `--verbose` and JSON instead of warning. It's the same
evidence the audit already accepts from a single lucky random input, only checked by the
kernel rather than sampled. Separately, the audit should stop searching the compiler's
generated equations, which `check --counterexamples` already skips; that removes 6 of the
trip journal's 14 warnings on its own.

## 1. The problem

`stitchwort audit Trip` in `examples/projects/accept/trip-journal` prints 14 warnings like
this one, and passes 173 theorems [run, 11 s]:

```
! Trip.Proofs.remotePinsKept
    warn: no input made the hypotheses true (0 of 1500 cases): if they contradict each other, the theorem is vacuous
```

Yet `Tests.sw:204` already proves an instance of it:

```
theorem extendedPinKept: latePin ∈ (merge localPin extended).pins :=
  remotePinsKept localPin extended latePin (Inr (Inl rfl)) latePin rfl
```

`Inr (Inl rfl)` proves `latePin ∈ extended.pins` and `rfl` proves `placePin … = Some latePin`:
both hypotheses hold at those arguments, and the kernel checked it. The warning tells the
reader to go and check something the project has already proved. A user who has done the
right thing (written a sanity instance, as the proving guide's advice amounts to) still gets
the warning, and `--strict` still fails.

The warning is raised only when the search's verdict is `NeverHeld`, that is when *no* input
satisfied every hypothesis (`crates/driver/src/audit.rs:233-241` [checked]). One satisfying
random input is enough to silence it: a theorem whose hypotheses held in 1 of 1500 cases gets
"gave up", and no warning. So the bar the audit sets is "the hypotheses hold at one point".
A proved instance clears exactly that bar, with a proof where the search has a sample.

### What D2357 actually doubted

The brief describes D2357 as doubting that a hand-written witness should silence the audit.
The record says something different. On SW-1261 (`board/tickets.json`, SW-1261's body
[checked]): "D2357 (Matt, 4 Nov): backlog only. Matt doubts random generation is a viable
strategy for vacuity at all (hoping it finds inputs); revisit the approach itself (e.g. what
a warning should require, or a non-random method) before doing A or B." No other mention of
D2357 exists in `docs/` apart from the SW-2219 review, which proposes this note as "a
cheaper, non-random answer to D2357's doubt" (`docs/reviews/SW-2219-trip-journal.md:299-305`
[checked]).

So the doubt is about randomness, and a proved instance is the non-random method it asked
for. §3 says what it does and doesn't settle.

## 2. What counts as a proved instance

### 2.1 The rule

A **proved instance** of theorem `T` is a sub-term of the checked body of some declaration
`W` such that:

1. its head is `T` (`Term::Def(T)`), and it applies `T` to at least as many arguments as
   `T`'s telescope has binders: every value parameter, every implicit and instance
   argument, and every hypothesis. This is the same telescope the search walks
   (`stitchwort_core::check::telescope`, used at `crates/elab/src/counterexample/mod.rs:393`
   [checked]), so "every hypothesis" means the same thing to both;
2. those arguments are **closed**: none mentions a variable bound outside the application
   (a `Term::Var` whose index reaches past the binders inside the argument itself). Binders
   inside an argument, a lambda in a list literal say, are fine;
3. `W` is not `T` itself;
4. `W` checked (`State::Final`), isn't unfinished (`marked_unfinished`), and its axioms are
   within the audit's allowlist (the `AxiomWalk` the audit already holds, `audit.rs:148`
   [checked]). A witness that rests on a `?` or a refused axiom proves nothing.

Any declaration can be `W`: a theorem, a definition, a local definition lifted out of a
proof (`%` names, reported under their parent's name). It needn't be in `Tests`.

Why this is sound: the arguments are closed and the application type-checks, so substituting
them into `T`'s hypotheses gives closed propositions, and the hypothesis arguments are closed
proofs of them. In a consistent kernel a closed proof means the proposition is true. The
claim "the hypotheses can hold together" then follows with no sampling and no trust in the
search's decision procedures [inferred; this is the definition of satisfiable, made
concrete].

### 2.2 What doesn't count

- **Open applications.** `remotePinsKeptAsTheyWere`'s body is
  `remotePinsKept local remote pin m pin` (`Proofs/Kept.sw:31` [checked]): every argument is
  a variable of the enclosing theorem. That only says "if `remotePinsKeptAsTheyWere`'s
  hypotheses can hold, so can these", which is no evidence on its own. Likewise `ownerSelf`'s
  `holderOf albums pd album m photo p` (`Proofs/Self.sw:124` [checked]).
- **Partial applications.** `T a b` with the hypotheses still to come leaves the question
  open, whatever `a` and `b` are.
- **Tests.** `test "…" := merge base base == base` is a run-time `Bool`, not a proof, and the
  trip journal's `==` on records containing `Float`s isn't known to agree with `=`. A test
  that evaluates a hypothesis to `True` would be good evidence, but it isn't kernel-checked,
  and a `theorem _ := T args (byDecision)` turns it into a proved instance for one line. So
  tests don't count.
- **The surface index.** `check --index` records where names are referred to in the source.
  It doesn't know the elaborated arguments (implicit ones, those a tactic such as `rewrite`
  or `omega [lemma …]` supplies) or whether they're closed, so it can't decide the rule.
  The scan reads the kernel terms (`def.body()`, the checked term, not `run_body`, which
  erases proofs; `crates/core/src/globals.rs:236-243` [checked]).

### 2.3 Partly concrete applications, and why not to chase them yet

There is a sound extension: an open application inside `U`'s body, at the top of the body
(not under a `match` branch, whose variables are refined), whose free variables are all
`U`'s own parameters, becomes a closed instance when `U` itself has one. `ownerSelf` →
`holderOf` is that shape. But the conditions (top of the body, through `let`s and
`rewrite`'s transports, never through a case tree) are fiddly to get right, a mistake there
would hide a really vacuous theorem, and the trip journal's warnings don't need it: each has
a one-line closed witness (SW-2219 §4's table). Not now; revisit if a project shows many
theorems that only chain.

A cheaper, safe widening: two theorems with **the same hypotheses** (the same telescope up
to the last hypothesis, compared by term hash) share witnesses. `placePinFits` and
`placePinId` have identical telescopes (`Proofs/Placing.sw:67`, `:76` [checked]), so one
instance would answer both. Sound because satisfiability depends only on the telescope.
Stage 3, optional.

### 2.4 How the audit finds them

One pass over the bodies of the loaded declarations, building a map from theorem to its
first witness. `Term::subterms` already yields each sub-term with the number of binders
above it (`crates/core/src/term.rs:717-726` [checked]) and `Term::spine` splits an
application (`term.rs:435-445` [checked]). This is the same kind of walk as the axiom scan
(`crates/driver/src/axioms.rs:271-312` [checked]), but over every loaded declaration, not
just those a theorem reaches, because a witness lives in a declaration that *uses* the
theorem, which the theorem never reaches.

Cost: linear in the loaded terms, once per audit. The scan is only needed if some theorem
came back `NeverHeld`, so it runs lazily on the first such verdict: an audit with no
warnings pays nothing. Std's bodies are skipped unless the audit targets Std, since a
library proof can't witness a project theorem. [inferred: no measurement; stage 1 measures
it on `aoc`, where the axiom walk before memoising cost about 1.6 s of 4.7 s (SW-1201), so a
single pass should cost well under that.]

### 2.5 Two designs compared

| | A. Detect instances (recommended) | B. A `witness` declaration |
|---|---|---|
| What the user writes | an ordinary `theorem` that applies `T` (as `extendedPinKept` already is) | `witness remotePinsKept localPin extended latePin (Inr (Inl rfl)) latePin rfl` |
| Language change | none | new syntax, guide and `docs/syntax.md` pages, formatter |
| Existing proofs | count at once (the trip journal's `extendedPinKept`) | must be rewritten |
| Intent visible | by convention (a `Tests` theorem) | explicit |
| Risk | the scan's rule (§2.1) must be right | the same check, behind a keyword |

B's only gain is that intent is explicit, and the closedness check is needed either way.
Isabelle's equivalent is the locale `interpretation`, which discharges a locale's
assumptions at concrete parameters and is the usual way to show a locale isn't vacuous;
Mathlib's practice is `example` blocks in its test folder applying a lemma to concrete
values. Both are ordinary declarations, not special syntax. Dafny takes the other road,
asking the solver whether the assumptions are contradictory
(`--warn-contradictory-assumptions`, Dafny 4 [from memory, not checked]); Stitchwort has no
solver, and a proved instance is the kernel-only analogue. A rules out nothing: B could be
added later as sugar for a theorem with no name.

## 3. What a proved instance settles, and what it doesn't

**Settles:** the hypotheses are jointly satisfiable, so the theorem isn't vacuous. That's
the whole of what the vacuity warning asks, and the question D2357 wanted answered without
randomness.

**Doesn't settle:**

- **Strength.** The theorem may still be weak: hypotheses that hold only at degenerate
  points (an empty trip, a single leg), or a conclusion that's true for a reason unrelated to
  the program. The warning never measured that, and neither does a random hit. The proving
  guide already asks the reader to judge narrow hypotheses (`docs/proving-guide.md:147-150`
  [checked]); audit stage 2's `--minimal` (SW-1029, unused hypotheses) is the tool aimed at
  over-strong hypotheses.
- **Counterexamples.** The search still runs and still fails a theorem it refutes; a
  witness changes only the `NeverHeld` outcome.
- **Theorems nobody wrote an instance for.** Without a witness the warning stays. That's
  the remaining half of D2357's doubt: random generation can't build inputs whose parts must
  agree (a pin inside a leg of the same trip). The answer there is to construct inputs from
  equations (SW-1317), not this note. This note makes the warning *actionable*: its text
  says how to answer it (§4).

## 4. How to report it

**The problem, plainly.** A reader of the audit should see warnings only for theorems
that need a look, and see why a theorem the search couldn't satisfy is nonetheless trusted.

**The change.** In `audit_one` (`audit.rs:233-241`), a `NeverHeld` verdict with a witness
adds no finding; the theorem passes and records the witness. Options for the output:

1. **Silence** (no record): the cheapest, but hides why it passed. Rejected.
2. **A different status** (recommended): it passes, also under `--strict`.
   - text, default: not listed (as for any pass); the summary says how many passed this
     way: `audited 187 theorems: 0 failed, 7 with warnings, 180 passed (1 by a proved
     instance)`;
   - `--verbose`: `✓ Trip.Proofs.remotePinsKept` and
     `    witnessed: Trip.Tests.extendedPinKept applies it to closed arguments, so its hypotheses can hold`;
   - JSON: a `"witness": "Trip.Tests.extendedPinKept"` field on the theorem (null otherwise).
     Additive, so the JSON `version` stays 1.
3. **A downgraded warning** ("warn, but witnessed by X"): still noise, still fails
   `--strict`. Rejected.

The unwitnessed warning's text gains the way out: `no input made the hypotheses true (0 of
1500 cases): if they contradict each other, the theorem is vacuous; a theorem applying it to
concrete arguments shows they can hold`. `check --counterexamples` prints the same `!` line
(`crates/cli/src/main.rs:1235-1265` [checked]) and should consult the same witness map, so
the two commands agree; the map belongs in `stitchwort_driver` next to the audit.

**Generated equations (SW-1261).** Six of the 14 warnings are on generated equations
(`pinFits.eq.some`, `placePin.eq.some.ifTrue`, …). A definition never applies its own
equation lemmas, so witnesses rarely exist for them, and they restate the definition's arms,
so they can't be misstated. `check --counterexamples` already leaves them out of its search
(`crates/driver/src/counterexample.rs:190-210`, `!stitchwort_elab::is_generated_name(…)`,
SW-1051 [checked]); `audit::theorems` has no such filter (`audit.rs:126-136` [checked]), and
the history shows no decision to include them [checked: `git log` on `audit.rs`]. The fix is
SW-1261's option A made consistent: the audit keeps checking their axioms and finish, and
skips only the search for them. That's D3231, because D2357 put SW-1261 on hold.

**`audit:touched`.** It audits the namespaces named and loads only those subtrees and what
they depend on (`main.rs:2560-2578`, `Target::Subtrees` [checked]). A witness is found only if
its declaration is loaded. For an AoC day this is fine: `Tests` sits under the day
(`aoc/src/Aoc/Year2020/Day01/Tests`), so `audit:touched -- Aoc.Year2020.Day01` loads it. But
`audit Trip.Proofs` would warn about `remotePinsKept` where `audit Trip` doesn't, since
`Trip.Tests` depends on `Trip.Proofs` and not the other way round. Alternatives: load the
reverse dependencies too (costs a check of everything downstream), or read witnesses from
the check cache (a stale cache could then hide a warning). Recommended: accept it, and say
in the verbose line and the docs that a witness counts when it is in the audited
namespaces; the result is then a function of what was audited, which is what a merge gate
wants. AoC's layout already satisfies it.

**What it should do, and how we'd know.** `audit Trip` goes from 14 warnings to 7 with
stages 1 and 2 (6 generated equations skipped, `remotePinsKept` witnessed), and to 0 once
the trip journal gains one-line witnesses for the other seven (SW-2219 §4 lists one for
each). A deliberately vacuous theorem (`(h: n + 1 = 0): n = 42`) still warns, and so does
one whose only "instance" is open or partial.

## 5. Calls I made

- Detection, not a `witness` keyword (§2.5).
- Tests don't count; only kernel-checked applications (§2.2).
- Full application of the search's telescope is required; no partial or chained instances
  for now (§2.3).
- The witness must itself be finished and within the axiom allowlist (§2.1, 4).
- The witness map is built lazily, skips Std unless Std is audited, and is shared with
  `check --counterexamples` (§2.4, §4).
- JSON gains a field; its version stays 1.
- `audit:touched` counts only witnesses in the loaded namespaces (§4).

## 6. Risks

- **A wrong closedness check hides a vacuous theorem.** The rule is small, and stage 1's
  tests include the open (`remotePinsKeptAsTheyWere`) and partial shapes, plus a witness
  under a lambda that does mention its binder. Opus reviews stage 1, as a trust check.
- **Cost on large projects.** Measured in stage 1; lazy, so zero when nothing warns.
- **Generated equations of an unreachable arm are vacuous for real** (a dead branch). Skipping
  them loses that signal, which was never the audit's job; a dead-arm lint, if wanted, is a
  separate ticket.

## 7. Questions for Matt

- **D3230:** Should a theorem the search couldn't satisfy pass the audit (also under
  `--strict`) when a checked declaration applies it to closed arguments, with the witness
  named in `--verbose` and JSON? [rec: yes, because it is the same "the hypotheses hold at
  one point" evidence the audit already accepts from one random input, now checked by the
  kernel; that is the non-random method D2357 asked for]
- **D3231:** Take SW-1261 off hold for option A only: the audit stops running the vacuity
  search on generated equations (`f.eq…`, `f.induct`), as `check --counterexamples` already
  does? [rec: yes, because they restate the definition and can't be misstated, the two
  commands disagree today, and it removes 6 of the trip journal's 14 warnings; options B and
  C stay with SW-1317]

## Tickets to file

In order; 1 and 2 are independent and can run side by side (they touch the same function,
`audit_one`, lightly; a small conflict at most).

1. **[Sonnet] Audit: proved instances answer the vacuity warning (D3230).** 75 min. New
   `crates/driver/src/witness.rs` (the §2.1 rule, lazy map), wired into `audit_one` and the
   `check --counterexamples` display; summary count, `--verbose` line, JSON field, the new
   warning hint; `docs/proving-guide.md`'s `!` paragraph and `docs/testing.md`'s audit
   lines. Tests: new cases in `crates/cli/tests/tools/audit.rs` (a witnessed theorem passes
   and names its witness; open, partial, self and `?`-witness cases still warn) and a unit
   test of the closedness check; `task test:one -- audit` (the tools/audit tests) only.
   Measure the scan with `audit` on one AoC day (`task audit:touched -- Aoc.Year2020.Day01`).
   Opus reviews (a trust check).
2. **[DeepSeek] Audit: skip the vacuity search on generated equations (D3231, SW-1261
   option A).** 30 min. Use the `is_generated_name` filter `search_theorems` has
   (`counterexample.rs:210`) for the search in `audit_one`, keeping the axioms and unfinished
   checks. Tests: one case in `crates/cli/tests/tools/audit.rs`; `audit Trip` on the trip
   journal shows 8 warnings. Updates SW-1261 (A done; B and C point at SW-1317).
3. **[Sonnet, optional] Audit: theorems with the same hypotheses share a witness.** 30 min.
   Compare telescopes up to the last hypothesis by hash. Tests: `tools/audit.rs` case with
   `placePinFits`/`placePinId`-shaped theorems. Only if stage 1 shows sibling theorems are
   common.
4. **[Sonnet] Trip journal: one-line witness theorems in `Tests.sw` for the seven
   non-generated warnings** (the SW-2219 §4 table gives each). 30 min; after stage 1. Could
   fold into SW-2225 (L4). Tests: `audit Trip` in the project, 0 warnings.

Not proposed: chained instances through open applications (§2.3); seeding the search with a
witness's arguments (it would test the neighbourhood of a known instance; SW-1317's
territory).
