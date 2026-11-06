# Strategy review: computing in proofs, Lean's way and ours

**Ticket:** SW-1726. **Reviewer:** Opus, reading only (nothing built or run: a profiling
lane was timing the machine), 6 Nov 2026, against `main` at `37b4a792b`. **Question**
(Matt): "Lean's strategy vs Stitchwort vs other languages: are we overcommitting to one
approach, should we rethink and copy Lean, or does our approach have advantages for the sort
of practical program proving we're shooting for?"

Labels:

- **[checked]**: read in this repository at the place given.
- **[cited]**: taken from a note, review or friction log in this repository, as named.
- **[web]**: read in Lean's documentation or the Lean Zulip archive on 6 Nov 2026 (sources
  at the end).
- **[inferred]**: my own reasoning from the above.

## Verdict

**Keep the approach, but drop one promise.** Stitchwort's bet is that a proof about an
ordinary program should be able to *run* the program: `rfl`, `byDecision`, `cases`, tests
checked by the kernel, the counterexample search, and `decreasing` functions that still
compute. That bet is right for AoC solutions, a roguelike and everyday std lemmas, and it is
where Stitchwort is clearly ahead of Lean. Lean's own experts now tell users to rewrite
well-founded functions with fuel so that `decide` and `rfl` work again, and fuel is what
Stitchwort's `decreasing` already compiles to. Copying Lean's transparency system (reducibility
levels, `simp` sets, `unseal`) would throw that away, and it needs a tactic language and a
large curated lemma library that Stitchwort doesn't have and decided not to build
(DESIGN.md: no tactic language).

**The one place Stitchwort overcommits is D484's promise that the elaborator's searches
(`rewrite`, `match`, `cases`, and the rest) see the goal fully computed, with no
regressions.** That promise has no counterpart in Lean, Rocq or Agda. It caused the most
common friction of the AoC 2020 track, on 14 of 20 days. Keeping it under record eta needs the
bounded-readback plan's most complex parts: a 100,000-node cap that must be "a function of
the call alone" (fixed limits, a cache keyed by folded arguments and the meta epoch, a
constant of the language), a reader whose skipping rule must agree *exactly* with
unification (the review found three counterexamples in draft 1), both-ways debug switches,
and "unconfirmed" warnings kept for two causes. Each part is well argued. Taken together
they keep a promise that users can't see or reason about ("a call whose unfolding is over
100,000 nodes is looked at as written"). The rest of Stitchwort is moving away from that
promise anyway: goals as written, searches as written first.

**Recommended: a hybrid that is mostly what Stitchwort already is.** Computation stays the
way to *decide* things (conversion, `rfl`, `decide`, `cases`, tests). *Searching* acts on the
goal as the user sees it, and looks inside a definition only when nothing visible matches
(Lean's rule, option B of goal-as-written.md). Limits fail with a message naming the call;
they never quietly switch to a different answer. In the bounded-readback plan this keeps
stages 0, 1, 4 and 5 as they are, a simpler reader (stage 3), and simpler search stages
(6a, 6b). It defers the cap (stage 2, D2519, D2529, D2533) until a real proof shows it is
needed. It costs seven existing proofs a step each. It removes a warning class, and about
five hours of the hardest Opus lanes. **[inferred]** The decisions are D2541–D2545 (§6).

## 1. Where Stitchwort and Lean really differ

The two are closer than the question suggests. The real difference is narrow.

### 1.1 What is the same

| Mechanism | Lean 4 | Stitchwort |
|---|---|---|
| Comparing two terms | lazy: same head, so compare arguments first; unfold one side at a time [web, SW-1718 §2.1] | the same: two calls of one definition compare arguments first, then unfold (`conv_step`, `crates/core/src/value.rs:2468`) **[checked]** |
| When a call unfolds | "smart unfolding": only if its `match` can take a step [SW-1718] | the same: "a definition stays folded until it has all its parameters *and* its case tree can take a step" (`value.rs:4–6`); `matches_at_once` (`value.rs:584`) **[checked]** |
| Goals shown | as written, never reduced [SW-1718] | as written since folded-calls and goal-as-written: glued `Value::Call` keeps the call (`value.rs:38–43`) **[checked]**. The proving guide still says "Goals are shown computed" (`docs/proving-guide.md:122`), which looks out of date **[inferred]** |
| Opaque definitions | `@[irreducible]`, `opaque`, `seal`/`unseal` | `opaque def`, `unfolding f` per theorem, `f.unfold` (`docs/syntax.md` "Opaque definitions") **[checked]** |
| Equation lemmas | `f.eq_1`, `f.eq_def`, generated | `f.eq1`, `f.eq2`, … and `f.unfold`, generated (proving guide §3) **[checked]** |
| Record eta | `toCtorWhenStructure` in `whnf` | rule 2, on `lane/SW-1642` **[cited, SW-1718 §0]** |

So Stitchwort is already a hybrid. It took Lean's lazy comparison (2024 day 22's friction
asked for exactly this, "Fix: lazy delta in conversion", `aoc/NOTES-2024.md:7298–7314`), Lean's
smart unfolding, and Agda's `opaque … unfolding`. **[checked]**

### 1.2 What is really different

1. **Defaults.** In Lean, a well-founded definition is irreducible by default ("Now functions
   defined by well-founded recursion are marked with `@[irreducible]` by default", v4.9.0
   [web]), instances are a separate level, and `simp` "does not unfold most definitions"
   [web]. In Stitchwort everything is transparent unless the user writes `opaque`, and a
   `decreasing` definition compiles to fuel that carries its proof, so it still computes in
   the kernel (`crates/elab/src/decreasing.rs:1–30`) **[checked]**.
2. **How proofs move.** Lean proofs move by *rewriting with lemmas*: `simp` with a curated set
   of `@[simp]` lemmas and a "simp normal form" ("a `simp` lemma should have the property that
   its right-hand side is simpler than its left-hand side" [web]), `rw` keyed at reducible
   transparency, and `unfold f` or `simp only [f]` to open a definition. Stitchwort proofs
   move by *computing*: `rfl`, `cases` (split what's stuck, close each case by computing),
   `match` on the program's own conditions so that the program's branch computes, and
   `rewrite` with lemmas in between. Counts over `aoc/src` (620 files): `rfl` 1,975 lines,
   `rewrite` 2,448, `omega` 1,150, `cases`/`byDecision` 300, `.unfold` 22, `opaque` 1.
   **[checked: grep]**
3. **What the searches see.** This is the real difference. Lean's `rw` and `kabstract` look at
   the term as written, keyed by head, and compare at reducible transparency, so they never
   look inside a user's definition [SW-1718 §2.1]. Stitchwort's searches looked at the
   *full normal form* (D484). Since goal-as-written (D2475–D2480) they look as written
   first, and fall back to the full normal form when nothing is found *or* when a copy hides
   inside a call ("the completeness check"). **[cited, goal-as-written.md §0]**
4. **Tests and counterexamples run in the checker.** A Stitchwort test is computed by the
   kernel's evaluator, and a failed proof triggers a counterexample search that runs the
   statement (`docs/guide/10-proofs.md`, "Note 3: this statement is false"). Lean evaluates
   compiled code outside the logic (`#eval`, `native_decide` trusted as an axiom). This is why
   well-founded-recursion.md ruled out Lean's design for us: "whatever we choose must compute
   in the kernel, quickly" (`docs/proposals/well-founded-recursion.md:68–74`) **[checked]**.

**The two philosophies, in a sentence each.** Lean: *the definitional machinery is a fallback
that tactics avoid touching; proofs are driven by named lemmas, and you say what to unfold.*
Stitchwort: *the program is the proof's best tool; computing is how you show things, and
naming lemmas is for what doesn't compute.* **[inferred]**

## 2. Fit for practical program proving

Each criterion, with evidence from the repository where I found it.

### 2.1 The user's experience

**Where computing visibly helped.**

- *Tests and small facts are free.* `theorem doubleFour: double 4 = 8 := rfl` (guide ch. 10).
  In Lean the same holds for structural definitions, but a well-founded one fails `rfl` and
  `decide` until `unseal` (well-founded-recursion.md §3.3, run on Lean 4.34.1: "`by rfl`
  fails", "`by decide` fails", "`unseal digitsOnto in … by rfl` passes") **[cited]**.
  Zulip shows how often this bites: `decide` on `IsSquare 4` stuck on `Nat.sqrt.iter`
  ("use `with_unfolding_all decide`" or `unseal`); `decide +kernel` on `List.mergeSort`
  broken by the 4.19 reducibility change, where Joachim Breitner's advice was "don't use
  well-founded recursion" and use fuel instead [web]. Stitchwort's `decreasing` *is* that
  advice, done by the compiler, with `f.unfold` generated. **[inferred]**
- *`cases` and `match` follow the program.* "What went well: … `match` on `last` that made
  the program's `if last != 0` compute in each arm" (`aoc/NOTES-2024.md:1912–1914`).
  Splitting on the program's own condition and letting each branch compute is the dominant
  AoC proof shape. It needs no lemma about the program's `if`. **[checked]**
- *Rewriting inside definitions without naming them.* Over AoC, 759 rewrites found their
  left side only in the computed goal (goal-as-written.md §5.3, prototype run) **[cited]**.
  In Lean each would be an `unfold f` or `simp only [f]` first. This is D484's real benefit,
  and it is large.
- *Almost no annotations.* One `opaque` in 620 AoC files and five in the roguelike; every 2021
  day reports "nothing is opaque" (`aoc/NOTES-2021.md:318` and on) **[checked]**. Lean users
  have to learn `@[simp]`, `@[reducible]`, `@[irreducible]`, `seal`, `unseal`,
  `@[semireducible]`, `simp!`/`autoUnfold`, `decide +kernel` and `native_decide` [web].

**Where computing visibly hurt.**

- *Searches acting on a form the user can't see.* "It hit 10 of the 11 days" (2020 days
  10–20), "the most common friction of the track: 14 of 20 days". Its cost is "detours, not
  lines: helper lemmas written only to dodge it, a program changed to suit a proof (day 20,
  whose theorem still takes 2.7 s …), and bisecting with `?`"
  (`docs/research/aoc-2020-friction-days-10-20.md` §1, §2 A) **[cited]**. Days 10 and 14
  were hurt by the search *reaching into* hidden copies, not by it failing to
  (goal-as-written.md §0) **[cited]**.
- *Large normal forms.* Day 18's `reachable` cost 10 s of checking until it was made opaque
  (later fixed by writing `omega` certificates and `let` types folded,
  `aoc/NOTES-2024.md:5866–5870`). The roguelike's level generator gave E-RESOURCE in every
  theorem about `resolve`: "a sound design, but the checker chose it, not me"
  (`games/rogue/NOTES.md:283–306`). Day 11's `settle … 1000` gave E-RESOURCE from a
  `match`, and trip-journal fails under record eta **[checked]**. In the board, 20 tickets
  mention E-RESOURCE and 7 "too large to show" (`board/tickets.json`, grep) **[checked]**.

So the evidence splits cleanly. **Computing to decide** (is this equal, is this true, which
branch) helped everywhere. **Computing to search** (where in this goal is my term) helped in
759 rewrites but was the top friction elsewhere, and it is the source of every blowup above
except day 18's. **[inferred]**

### 2.2 Predictability

The user's model of a Lean `rw` is one rule: it rewrites what you see. Lean's
well-known surprises come from the *other* direction: `rw` fails because the term is only
there up to unfolding ("did not find instance of the pattern"), `simp` doesn't unfold your
function, and `decide` gets stuck on an irreducible definition. Each needs knowledge of the
transparency system to fix. [web; the `rw` error recalled, not re-read]

Stitchwort's model today: "it looks as written first; if no copy hides inside a call, it uses
that; otherwise it uses the computed goal" (proving guide §3). With bounded read-back this
gets a further clause: "except inside a call whose unfolding is over 100,000 nodes, with its
large inner calls kept". Nobody can see a node count, so that clause is unpredictable *by
construction*, even though it is deterministic. The study found no system with such a cap
(SW-1718 §3.3) **[cited]**. A rule users can't apply in their heads is a cost even when it
never fires. **[inferred]**

### 2.3 Performance

Lean pays for laziness with lemmas: proof search never unfolds much, but someone has to
write and tag the lemmas. Stitchwort pays at the full read-back: about 290 places in the
elaborator read a value back fully unfolded, each up to 10,000,000 nodes
(bounded-readback.md §1.3, §2) **[cited]**. Stages 1, 4 and 5 of that note stop doing this
where nothing needs it, which is what every other system does. The rest of the cost is
the unfolded *search*. **[inferred]** The goal-as-written prototype measured Lean's rule (B)
at 69.1 s over AoC against 74.8 s for the completeness check (A) and 67.8 s for today's
search (§5.3; a shared machine, so differences of a few seconds are noise) **[cited]**.

### 2.4 Robustness to edits

- *Computing to decide* is robust: change a program and `rfl` still works or fails honestly;
  the "break the program" check (proving guide rule 6) relies on it. **[checked]**
- *Searching the computed form* is fragile. Editing a helper changes what a `rewrite`
  three definitions away finds, or whether a hidden copy exists. That is the day 10 and
  day 14 pattern **[cited]**. A size cap adds another fragility: an edit that grows a helper
  past 100,000 nodes changes what a distant search sees. **[inferred]**
- Lean's fragility is the reverse. An edit that changes a definition's shape breaks the `simp`
  lemmas about it, and a library change of reducibility breaks `decide` (the 4.19 mergeSort
  case [web]). The `grind` docs warn the same about annotated lemma sets [web].

### 2.5 Error quality

Stitchwort's errors that show both forms were praised. E-REWRITE-NOTHING's "already
computed past it" was cited favourably on days 11, 13, 16, 19 and 20 (friction synthesis §2
A) **[cited]**. Errors that came from the computed form misled: day 12's "unsolved `?42` and
the parser's unfolded run", and E-RESOURCE "too large to show" naming no definition (2020
day 11, `aoc/NOTES-2020.md:3013–3030`) **[checked]**. Lean's `decide` names the stuck
instance on failure, computed lazily (SW-1718 §2.1) **[cited]**. Under the recommendation,
a search error always speaks about the goal as written, plus "the left side may be inside
`f …`; `rewrite f.unfold` to look" **[inferred]**.

### 2.6 How much users must know

| Stitchwort user must know | Lean user must know |
|---|---|
| `rfl`/`cases`/`byDecision` compute; `+` computes on its first argument | reducibility levels; which definitions are irreducible (WF), `unseal` |
| searches look as written, then inside definitions | `rw` vs `erw` vs `simp only [f]` vs `unfold f` vs `delta` |
| `opaque`, `unfolding`, `f.unfold`, `f.eqN` | `@[simp]` normal forms, `simp!`, `decide +kernel`, `native_decide`, `grind` patterns |
| (with the cap) a hidden node count | — |

Stitchwort's list is shorter, except for the cap row. **[inferred]**

**Verdict on fit:** for programs (as opposed to mathematics), computing to decide is the
better default by a wide margin, and searching the computed form is a mixed blessing that
mainly helps when nothing is visible. **[inferred]**

## 3. Are we accumulating mechanisms?

A ledger of what exists or is planned, and whether each pays its way.

| Mechanism | Pays its way? | Why |
|---|---|---|
| Glued calls (`Value::Call`, folded read-back) | **yes** | Goals as written, lazy comparison, small output terms. Idris 2 and smalltt do the same [SW-1718 §2.4–2.5] |
| Smart unfolding (`matches_at_once`) | **yes** | Same as Lean's and Rocq's `simpl nomatch`, with no annotation |
| Lazy comparison, arguments first | **yes** | What 2024 day 22 asked for. It is Lean's lazy delta |
| `decreasing` as fuel with `f.unfold` | **yes, and ahead of Lean** | `rfl`/`decide` keep working; Lean's experts recommend the same by hand [web] |
| `opaque` / `unfolding` / `f.unfold` / `f.eqN` | **yes** | Rarely needed, but every system needs an escape hatch (SW-1718 §3.4) |
| As-written search first (goal-as-written stages 1–3) | **yes** | Answers the top friction |
| Output terms, zonk, messages, `decide` read folded (bounded-readback stages 1, 4, 5) | **yes** | What everyone does; removes cost without changing answers |
| The completeness check (fall back when a copy hides inside a call) | **doubtful** | Keeps D484's reach for mixed goals, at the price of days 10/14's surprises, the costliest search, the `todays_instance` agreement machinery and the unconfirmed paths. Lean's rule (B) broke seven declarations (two std, five AoC) [cited] |
| `W-REWRITE-UNCONFIRMED`, `W-MATCH-UNCONFIRMED` | **no, long term** | A warning that says "we couldn't check our own promise". It exists only because of the completeness check and the unbounded fallback |
| The capped normal form (`CAP` 100,000, D2519/D2533/D2529) | **not yet shown** | D1280 measured that nothing in std, AoC or the roguelike reaches it (goal-readback.md §5) [cited]. Its purpose is to keep D484 above the cap and to bound trip-journal. Whether the reader alone bounds trip-journal is stage 0a's open question (bounded-readback.md §4.2: "stage 0a measures how much is opened") |
| The reader's *exact* `find` (agree with the capped normal form in order and answer; relevant variables outside proof positions, rule unknowns, all-proof records; both-ways switch) | **partly** | Pruning and memoising are good and cheap. *Exact agreement with today* is what makes it Opus-hard (200 min, three counterexamples in draft 1). It is needed only to keep D484 exact |
| `mentions` exact | **yes** | `bind.rs:95` needs "doesn't mention" to be true (bounded-readback.md §2.2) |
| Recoverable E-RESOURCE that steers a branch | **no** | Results depend on where a shared budget ran out (study S6). Lean makes such limits uncatchable [cited] |
| Many numeric limits | **mostly fine** | `SEARCH_BUDGET` 1,000,000, `UNCONFIRMED_BUDGET` 100,000 (`rewrite.rs:75,82`), `CASES` 64, `KNOWN_CAP` 4,096, `cheaply` 10,000, size 10,000,000 (`budget.rs:109`) **[checked]**. Limits that *fail* are harmless; limits that *change the answer* (the cap, recovered E-RESOURCE) are the ones to avoid |

**So the answer to "are we overcommitting?" is yes, but only in one place.** Everything that
makes computing cheap and lazy is earning its keep, and most of it is what Lean does. What
doesn't is the set of mechanisms whose only job is to keep D484's promise that searches see the
full normal form. They are the completeness check, the unconfirmed warnings, the cap, and
`find`'s exact agreement. Each was added for a good local reason (no regressions), and each
review made it more exact and more complex. That is the shape of overcommitment.
**[inferred]**

## 4. The options

### (a) Continue as planned

Bounded-readback revision 2, stages 0a–6b, about 16 hours (its §7).

- *For:* no existing proof changes below the cap. The plan is careful, reviewed twice, and
  its stages 0, 1, 4 and 5 are good on any option.
- *Against:* stages 2, 3, 6a and 6b (590 min, all Opus) build machinery to keep a promise
  users can't see. The cap is a new user-visible rule in node counts, with no precedent and
  no measured proof that needs it on `main`. The unconfirmed warnings stay for two causes. It
  is the most code in the most delicate places (read-back, unification interplay, motives).
- *Risk:* time (D1280's 6× slowdown on rogue2q before a cache); subtle disagreement bugs, which
  is why it needs both-ways switches. **[cited, inferred]**

### (b) Adopt Lean-style transparency

Per-definition reducibility, levels per tactic, a `simp` with equation lemmas, searches at
"reducible" only.

- *For:* the most predictable searches, and well-trodden prior art.
- *Against:*
  - It inverts the language's main strength. `rfl`, `cases` and the counterexample search
    would stop seeing through definitions unless annotated, and the friction would move to
    Lean's (`unseal`, `simp only [f]`, `decide` stuck).
  - Stitchwort has no tactic language by design and no `simp`. A `simp` is only as good as
    its curated lemma set and normal forms: mathlib-scale work for std.
  - Kernel-checked tests and the counterexample search need definitions that compute.
  - The 759 AoC rewrites inside definitions would each need an explicit unfold. Migration
    cost doesn't count, but that is also the *ongoing* style cost of every new proof.
- *Risk:* a multi-month redesign that makes AoC proofs longer. **Not recommended.**
  **[inferred]**

### (c) A hybrid by inferred opacity

For example, treat well-founded, very large, or "expensive" definitions as opaque to searches
automatically, or add `abbrev`-like markers.

- Stitchwort already does the well-founded half: a `decreasing` call "stays folded until
  something takes it apart", and computes when something does (`decreasing.rs:16–18`)
  **[checked]**. Inferring opacity *by size* is the cap again, keyed per definition rather
  than per call, so it is less exact and just as invisible. Markers (`abbrev`) are useful
  only once searches stop unfolding by default, and then they are Lean's `reducible`.
- Verdict: no new opacity. The worthwhile part is an *inferred search status* (SW-1718's S8,
  in the backlog), and only if option (d) proves too weak. **[inferred]**

### (d) Recommended: compute to decide, search what you see

Three rules, all small to state:

1. **Searches act on what is visible.** `rewrite`, `match`, `cases`' generalisation and the
   transport use the as-written result whenever it finds something. Copies inside calls are
   left alone: no completeness check. This is Lean's rule, goal-as-written.md's option B.
2. **When nothing is visible, look inside, lazily.** The fallback is the reader's `find`: it
   opens a call only when its arguments mention a relevant variable of the needle, and
   memoises negative answers. It does *not* have to agree exactly with a full normal form. It
   must be deterministic and must find what the H1 unit tests describe. Its answer is checked
   by unification and the kernel, as today.
3. **Limits fail, they don't switch.** The fallback has a fixed work limit per search (as
   `cheaply` does). Running out is an error naming the largest call it opened and suggesting
   `rewrite f.unfold`, `rewrite f` (D1433) or `opaque`. No call is "kept because large", and
   a recovered E-RESOURCE never chooses a branch (D2540).

What it keeps from (a): stages 0a–0c, 1, 4 and 5 unchanged; D2538 (motives from opened calls
only); `mentions`, `unfold_where`, `shown` from the reader.

What it drops: stage 2 (the cap) for now; `find`'s exact-agreement contract (the both-ways
switch becomes a one-off measurement, not a guarantee); `hidden_copy_in` and
`todays_instance` (the agreement with today's instance only matters when two searches run);
`W-REWRITE-UNCONFIRMED`, `W-MATCH-UNCONFIRMED`. A literal-driven goal such as `settle x k 40`
is rescued by rule 1 with no warning, because the visible occurrence is simply used.

Costs and risks, in Stitchwort's terms:

- *Proofs that change:* the seven B broke (2020 day 17 `Neighbours.sw:41`, 2025 day 1
  `Part2.sw:82`, `:94`, 2025 day 8 `Labels.sw:107`, `:153`; std `Result.traverseCons`,
  `List.foldMaxMem`), plus whatever the `match` half adds (folded-goals.md's two std
  failures are the same two) **[cited]**. Each needs an extra `rewrite` naming the hidden
  copy or an unfold step.
- *A new surprise:* a hidden copy left behind can make a later `rfl` fail. The E-REFL note
  should then say "a copy of `lhs` is still inside `f …`, which this `rewrite` left as it
  is". That is an error-path search under `shown`'s budget **[inferred]**. Lean users meet the
  same thing; the message is what makes it cheap.
- *Trip-journal:* whether rules 2 and 3 alone bound it is stage 0a's question, the same one the
  plan already asks of the reader. If a needle mentioning only `trip` opens too much, option
  (e) is the next lever before the cap. **[inferred]**
- *Effort (estimate):* stage 3 shrinks (no exact agreement: perhaps 120 min instead of 200),
  and 6a and 6b shrink (completeness and agreement code removed rather than ported: perhaps
  90 and 100 instead of 120 and 150). With stage 2 dropped, that is about 5 hours fewer of
  Opus lanes. **[inferred; not measured]**

### (e) A cheap lever for record eta: rule 2 doesn't fire in searches

Rule 2 exists so that `rfl` and conversion compute through a function that takes an unknown
record apart (record-eta.md §6.4). Nothing on `main` relies on it in a *search*, because it
is only on the branch **[checked: bounded-readback.md §1.1 cites it as "(branch)"]**. If the
read-backs that searches use treat a case on an unknown record as stuck, as `matches_at_once`
already does for the folded form (`value.rs:584`), then trip-journal's `album =>` bodies stay
small in searches, and conversion keeps rule 2. Nothing regresses against `main`. The
inconsistency to check is a needle read back with rule 2 against a goal read back without
it. Both would go through the same read-back, so I expect none, but this is inferred. Worth
30 minutes inside stage 0a's scratch run before anything larger. **[inferred]**

## 5. Recommendation, and the bounded-readback note's pending decisions

**Take option (d), with (e) tried in stage 0a.** In plain terms: keep Stitchwort's "it
computes" for everything that decides; make every search speak about the goal as the user
sees it; make every limit an honest error; and keep one explicit way to look inside a
definition by name. Don't build Lean's transparency system, and don't build the cap until a
proof needs it.

What happens to each pending decision of bounded-readback.md §8:

| Decision | Recommendation under (d) |
|---|---|
| D2519 (capped normal form everywhere) | **defer**: replaced for now by D2543; revisit only if 0a/0c find a proof that needs a kept call |
| D2520 (one shared reader) | **yes, narrowed**: `mentions`, `unfold_where` and `shown` as planned; `find` deterministic and lazy, with the H1 unit tests, but no exact-agreement contract |
| D2523 (output terms folded) | **yes**, unchanged |
| D2529 (CAP fixed, no escape) | **defer** with D2519; the escape is D1433 (`rewrite f`), recommended yes |
| D2533 (cap's definition) | **defer** with D2519 |
| D2534 (remove unconfirmed only where the cap kept a call) | **replaced** by D2542: the completeness check goes, so both warnings go |
| D2535 (`decide` folded, unglued) | **yes**, unchanged |
| D2536 (test strategy exception) | **yes**, for 0c and the `find` stage |
| D2537 (order) | **amended** by D2545 |
| D2538 (motives partly folded) | **yes**, unchanged |
| D2539 (programs never choose on a kept call) | **moot** without the cap; its principle is folded into D2540 |
| D2540 (recovered E-RESOURCE never chooses) | **yes now**, in principle, with 0c used to find the places to change rather than to decide |

## 6. Decisions for Matt

- **D2541: direction.** Keep computation as the way to decide things (conversion, `rfl`,
  `byDecision`, `cases`, tests, counterexamples) and don't adopt Lean's transparency system
  or a `simp`. Retire D484's clause that searches see the full normal form. [rec: yes. The
  evidence splits exactly there: computing to decide helped on every day, computing to
  search was the top friction, and Lean's own users are moving towards Stitchwort's
  `decreasing` design.]
- **D2542: Lean's rule for searches** (revisits goal-as-written Q4). `rewrite`, `match`,
  `cases` and the transport use the as-written occurrence whenever there is one, with no
  completeness check. They look inside definitions only when nothing is visible.
  `W-REWRITE-UNCONFIRMED` and `W-MATCH-UNCONFIRMED` go. E-REFL gets a note when a rewrite
  left a copy inside a call. [rec: yes. One rule users can apply in their heads; it fixes
  days 10 and 14; it was the fastest of the measured variants. It costs seven proofs a step
  each, which by your rule on migration cost doesn't count.]
- **D2543: limits fail, they don't switch.** The fallback search has a fixed per-search work
  limit. Running out is an error naming the largest call opened and the ways to proceed.
  There is no size cap that keeps calls for now, which defers D2519, D2529 and D2533. [rec:
  yes. Every other system's limits are errors (SW-1718 §3.5). The cap is unprecedented and
  invisible, and D1280 found nothing that reaches it.]
- **D2544: try rule 2 off in search read-backs**, in stage 0a's scratch run on
  `lane/SW-1642`, and adopt it if trip-journal's searches then stay small and nothing else
  changes. [rec: yes, as an experiment. It is 30 minutes, regresses nothing on `main`, and
  may unblock SW-1667 without stages 2–6.]
- **D2545: order.** 0a (with D2544's experiment) first; then 1, 0b, 4 and 5, as planned;
  then the narrowed reader (3) and 6a/6b under D2542 and D2543. D1433 (`rewrite f`, one step
  of `f` by name) is built before 6a, because rule 1 makes explicit unfolding the normal
  escape. SW-1667 resumes as soon as 0a's failing site kinds have moved. [rec: yes.]

## 7. What this review did not do

- It ran nothing. The effort savings in §4 (d) are estimates. Whether the reader without
  the cap bounds trip-journal is a measurement (0a), as it already was in the plan.
- It didn't re-run goal-as-written's prototype for the `match` half of D2542. Its counts are
  for `rewrite`, plus folded-goals.md's two std failures for `match`.
- It didn't read every Lean Zulip thread on `simp`/`unfold` friction. The Lean evidence is the
  reference manual, release notes, the simp guide and three Zulip threads (below), plus
  SW-1718's study and the well-founded-recursion note's Lean runs.
- It didn't move SW-1726 on the board: the brief said not to edit `board/tickets.json`.
- Not checked: whether `docs/proving-guide.md:122` ("Goals are shown computed, not as
  written") is still true. Everything else I read says goals are shown as written, so it may
  be a stale line worth a one-line fix.

## Sources

Repository (at `37b4a792b`): `docs/proposals/bounded-readback.md` (rev. 2),
`goal-as-written.md`, `goal-readback.md`, `well-founded-recursion.md`;
`docs/reviews/SW-1717-bounded-readback-review.md`, `SW-1718-unfolding-comparison.md`;
`docs/research/aoc-2020-friction-days-10-20.md`; `aoc/NOTES-2020.md`, `NOTES-2021.md`,
`NOTES-2024.md`; `games/rogue/NOTES.md`; `docs/proving-guide.md`, `docs/syntax.md`,
`docs/guide/10-proofs.md`, `DESIGN.md`; `crates/core/src/value.rs`, `budget.rs`;
`crates/elab/src/decreasing.rs`, `rewrite.rs`.

Web, read 6 Nov 2026:

- Lean 4.9.0 release notes (well-founded definitions irreducible; `seal`/`unseal`):
  <https://lean-lang.org/doc/reference/latest/releases/v4.9.0/>
- The simp guide, Lean community ("by default `simp` does not unfold most definitions";
  simp normal form; `simp!`): <https://leanprover-community.github.io/extras/simp.html>
- Lean reference, invoking the simplifier (equation lemmas used when a constant is given):
  <https://lean-lang.org/doc/reference/latest/The-Simplifier/Invoking-the-Simplifier/>
- Lean reference, `grind` (annotation-driven E-matching; proofs may break when library
  annotations change): <https://lean-lang.org/doc/reference/latest/The--grind--tactic/>
- Zulip, "opaque recursion definitions break mergeSort decidability" (Apr 2025; Breitner:
  use fuel, not well-founded recursion, for definitional equations):
  <https://leanprover-community.github.io/archive/stream/270676-lean4/topic/opaque.20recursion.20definitions.20break.20mergeSort.20decidability.html>
- Zulip, "Not sure why decide fails on IsSquare" (`with_unfolding_all decide`, `unseal`,
  `decide +kernel`):
  <https://leanprover-community.github.io/archive/stream/113489-new-members/topic/Not.20sure.20why.20decide.20fails.20on.20IsSquare.html>
- Zulip, "How to make a recursively defined function reducible?" (`@[semireducible]`, fuel):
  <https://leanprover-community.github.io/archive/stream/270676-lean4/topic/How.20to.20make.20a.20recursively.20defined.20function.20.22reducible.22.3F.html>
