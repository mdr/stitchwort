# `byFacts` in context: other systems' finishers, and how far it reaches in Stitchwort

**Status:** review, 21 November 2026 (SW-4483, a Fable paper lane), for
D3708. Nothing is built. Read against `main` at `599e0332e`, which has
closer stage 0 (SW-4472, SW-4473). It reviews stage 1 of
[closer.md](../proposals/closer.md).

How claims are marked:

- **[run]**: I ran it today. Lean 4.35.0 and Rocq 9.1.1 from nixpkgs on
  [`SW-4483/Probe.lean`](SW-4483/Probe.lean) and
  [`SW-4483/Probe.v`](SW-4483/Probe.v); Stitchwort's release binary at
  `599e0332e` on scratch files and on probe theorems added to one
  namespace (`check --only`) and then removed.
- **[measured]**: counted today by the scripts in
  [`SW-4483/`](SW-4483/).
- **[read]**: read today in the file and line named, or on the page named
  through a summarising fetch (quotations are as the fetch returned them).
- **[estimated]**: my judgement, by hand, of a proof under a tool that
  doesn't exist.

## In plain words

**The question.** closer.md proposes one new proof word, `byFacts
[lemmas]`: finish a goal from the facts in scope and the lemmas you
name. Its evidence was 50 formatter proofs. Do other systems have this
tool, and would it earn its keep across Stitchwort?

**Where it sits.** Every system I looked at has it, and it is always
one of the small tools, not the headline: Rocq's `auto`, Lean's
`solve_by_elim`, Idris's and Agda's proof search. Each works backwards
from the goal through hypotheses and a short list of lemmas, to a small
depth, and finishes or does nothing. `byFacts` differs in one way that
matters: it takes "and" facts apart first. `auto` and `solve_by_elim`
both fail on a goal that needs one part of an "and" hypothesis [run];
the tools that do that are another family (Rocq's `intuition` and
`easy`, Lean's `simp_all` and Aesop). So `byFacts` is Rocq's `intuition`
with a small `auto` behind it, kept to "and".

**How generally useful.** 40 proofs drawn at random (seeded) from std,
AoC, the roguelike, the app and the formatter outside closer.md's
files, 641 lines:

- today's tools, used differently, take 34 lines (5.3%), 27 of them run;
- `byFacts` as specified takes a further 19 (3.0%) [estimated], in 3
  proofs; 26 (4.1%) in 5 proofs with two small additions; it makes 7
  more proofs simpler without shortening them;
- in formatter-style code that is about 9% of lines; in std, AoC, the
  roguelike and the app, 1.4% (2.7% with the additions). Those proofs
  end in `arithmetic [..]`, rewriting, induction and long one-off
  chains. closer.md's "4 to 10%" holds for the formatter, not outside.

**Why build it anyway.** No finisher in Stitchwort proves "b" from
"a → b" and "a" for plain propositions, or applies a local "for all"
fact: `cases` fails on eight such goals, most of which `auto` and
`solve_by_elim` close [run]. `cases` used as a finisher can fail very
slowly: 9 seconds on one sampled proof whose hand term checks in 21 ms
[run]; a finisher that never splits can't. And the formatter is the
shape proved software takes as it grows: invariants with a dozen parts.

**Recommendation for D3708: build it, with changes** (§4, §5). Split it
into a part that never backtracks and a small search, so its error is
exact. Take apart "there is" facts and records of proofs, not only
"and". Let a lemma's unknowns be fixed by a fact, never guessed. Give it
its own rule for equations in scope (closer.md leans on a `cases`
behaviour that isn't there). Drop `rules` sets from its list. Do "tell
`cases` what to split" (SW-4474) alongside: it has measured evidence
and is worth as much. Keep the name. Expect a small, dependable tool,
not a line-count win.

## 1. The map

### 1.1 The tools

"Records" is whether the tool can write down what it found, so that the
proof no longer depends on the search.

**Rocq 9.1.1**

| Tool | What it does | Limits, predictability | In finished proofs | Records |
|---|---|---|---|---|
| `auto` | "Implements a Prolog-like resolution procedure": `assumption`, then `intros`, then hints for the goal's head symbol, recursively. Uses "the hypotheses of the current goal and the hints of the database named `core`"; `auto using lemma` adds lemmas; `with db` adds databases [read: refman `auto.html`] | Depth 5 (`auto.ml:408` [read]). "Either completely solves the goal or leaves it unchanged": on a goal it can't prove it succeeds and changes nothing [run]. Uses "a weaker version of `apply` that is closer to `simple apply`", so "sometimes `auto` will fail even if applying manually one of the hints would succeed". Never takes a hypothesis apart: fails on `A ∧ B ⊢ A` [run] | Explicit databases: "not to put your own hints in the core database", and `auto with *` is "highly discouraged in finished scripts since it is both slower and less robust" | `info_auto` prints the script (`simple apply H. assumption.`) [run] |
| `eauto` | `auto`, also trying hints "which would leave existential variables in the goal" | The same, with a larger search. Closes `(∀ x y, P x → Q y → R y), P 5, Q 3 ⊢ R 3`, where `auto` fails because `x` isn't in the conclusion [run] | As `auto` | `info_eauto` [run] |
| `easy`, `now t` | A fixed script: takes `∧` hypotheses apart, tries `trivial`, `reflexivity`, `contradiction`, splits `∧` goals (`Init/Tactics.v:158-183` [read]) | No lemmas, no depth: fully predictable. Closes `A ∧ B ⊢ A` [run] | Used freely as a line ender (`now t` is `t; easy`) | Nothing to record |
| `tauto` | "A decision procedure for intuitionistic propositional calculus"; "unfolds negations and logical equivalence but does not unfold any other definition" [read: refman `logic.html`] | Complete for its fragment, so predictable. No quantifier instantiation: fails on a local `∀` [run] | Fine | No |
| `intuition t` | Takes the propositional structure apart, then runs `t` on what is left. The default `t` is "equivalent to `auto with *`" and "in a future version it will be changed to just `auto`", with a warning when the difference matters [read] | As its solver. Doesn't split a `bool`'s `&&`, doesn't use an equation in scope [run] | With an explicit solver | No |
| `firstorder` | "An experimental extension of `tauto` to first-order reasoning", depth bounded by `Firstorder Depth`, with `auto with core` where no rule applies [read] | Closes the `∧`, `∀` and `∃` probes [run] | Sparingly | No |
| `congruence` | "The standard Nelson and Oppen congruence closure algorithm … for ground equalities with uninterpreted symbols" [read] | Complete for its fragment. The only one of these that proves `f a = 0` from `a = b` and `f b = 0` [run] | Fine | No |

**Lean 4.35.0**

| Tool | What it does | Limits, predictability | In finished proofs | Records |
|---|---|---|---|---|
| `solve_by_elim [lemmas]` | "Calls `apply` on the main goal to find an assumption whose head matches and then repeatedly calls `apply` on the generated subgoals", with backtracking. Uses "the local context, `rfl`, `trivial`, `congrFun` and `congrArg`", plus the listed terms; `only` drops the context; `[-h]` removes a hypothesis (`Init/Tactics.lean:1724-1760` [read]) | Depth 6, `intro` and `constructor` on, hypotheses also used flipped (`symm`), `exfalso` retried (`Lean/Meta/Tactic/SolveByElim.lean:79-102` [read]). "Discharges the current goal or fails". Doesn't take hypotheses apart: fails on `A ∧ B ⊢ A`, on `(a && b) = true ⊢ a = true`, and on an equation in scope. Its whole error is the word "failed" [run] | Yes; it is terminal and names its lemmas | `show_term solve_by_elim` printed `exact ⟨imp a b, a⟩` [run] |
| `apply_rules`, `apply_assumption` | The same engine without backtracking: "greedily applies a lemma from the list until it gets stuck"; depth 50 (`:1788-1810`, `SolveByElim.lean:79-87` [read]) | Cheaper, less complete | Yes | `show_term` |
| `exact?`, `apply?` | "Searches environment for definitions or theorems that can solve the goal using `exact` with conditions resolved by `solve_by_elim`" (`:1832-1858` [read]) | The whole library, under a heartbeat limit | No: "`rw?` should not be left in proofs; it is a search tool, like `apply?`" (`:1868`). It prints "Try this: exact …" | Always; that is its output. On one probe it printed `exact And.elim (fun a => imp) (id (And.symm h))` where a person writes `imp h.1` [run] |
| `simp_all` | Rewrites goal and hypotheses with each other and the `@[simp]` set until nothing changes (closer.md §3) | Depends on the tagged set unless written `simp_all only [..]`. Closes the four probes `solve_by_elim` fails on [run] | As `simp only`/`simp_all only` when not terminal | `simp_all?` |
| Aesop | "A proof search tactic": best-first search; "a safe rule is applied eagerly and is never backtracked", unsafe rules "tried only if all available safe rules have failed"; goals are first normalised by `simp_all`. Built-in rules "safely split a goal `P ∧ Q`" and handle the connectives; rules join by attribute or `(add …)` on the call [read: README] | "Configurable limits on … the total number of rules applied or the search depth". Depends on the `@[simp]` and `@[aesop]` sets | Yes, with rule sets | `aesop?` "prints a tactic script"; "occasionally generates buggy scripts" |
| `grind` | Congruence closure, E-matching on tagged lemmas, case splits, arithmetic (closer.md §3) | "Not designed for goals whose search space explodes combinatorially" [read: reference, "The `grind` tactic"]; five separate limits | `grind only [..]` | `grind?` |
| `omega`, `decide` | Linear arithmetic over `Int` and `Nat` ("not yet a full decision procedure", `Init/Tactics.lean:1544`); `decide` evaluates a `Decidable` instance (`:1446`) [read] | Decision procedures: predictable inside the fragment | Freely | Nothing to record |

**Isabelle** [read: Nipkow, *Programming and Proving in Isabelle/HOL*,
24 October 2026 edition, §3.3 and §3.4]

| Tool | What it does | Limits, predictability | In finished proofs | Records |
|---|---|---|---|---|
| `simp`, `auto` | Rewriting; `auto` also "simple logical or set-theoretic goals". "They show you where they got stuck, giving you an idea how to continue. They perform the obvious steps but are highly incomplete" | `auto` may leave goals changed, so it is used last or as `by auto` | Yes, with `simp add:`, `intro:`, `dest:` naming lemmas | No |
| `fastforce`, `force` | "Tries harder than `auto`"; "either succeeds or fails, it acts on the first subgoal only" | "Even `fastforce` fails when the quantifier structure becomes more complicated" | Yes | No |
| `blast` | "(In principle) a complete proof procedure for first-order formulas … In practice there is a search bound"; "does no rewriting and knows very little about equality"; "either succeeds or fails" | "When `fastforce` or `blast` simply fail, you have no clue why" (§3.4) | Yes | No |
| `metis lemmas` | "Given a list of lemmas and tries to find a proof using just those lemmas (and pure logic)"; "using `metis` manually is tedious because one has to find all the relevant lemmas first" | Bounded by the list | Yes: it is what `sledgehammer` leaves behind | It *is* the record |
| `sledgehammer`, `try0` | External provers "for up to 30 seconds"; "a proof command is generated and can be inserted into your proof" | Not left in proofs | No | Always (`by (metis append_eq_conv_conj)`) |

**Agda and Idris**

| Tool | What it does | Limits, predictability | In finished proofs | Records |
|---|---|---|---|---|
| Agda's Auto | "Searches for type inhabitants and fills a hole when one is found". "Does not by default try using constants in scope": hints are named on the call, `-m` adds the current module's definitions [read: agda.readthedocs.io, `tools/auto.html`] | One second by default. "One should not expect it to handle large problems of any particular kind, but small enough problems of almost any kind" | It never is in the proof: it is an editor command | Always: "replaces the hole with the first solution found" |
| Idris 2's `auto` arguments and proof search | Tries, in order: "local variables … with exactly the right type"; "the constructors of the required type … recursively up to a maximum depth of 100"; "local variables with function types, searching recursively for the arguments"; functions marked `%hint` [read: idris2.readthedocs.io, `tutorial/miscellany.html`] | Depth only; "internally, this is exactly how interface resolution works" | Yes, for `auto` arguments | Not read |

**SMT-backed languages: no finisher, because everything is one**

Dafny, F\* and Verus send each obligation to Z3 with every fact in
scope, every visible definition and every quantified lemma whose
trigger matches. The user never spells out "and" plumbing or which
hypothesis feeds which; a lemma is used by calling it by name, and the
solver does the chaining. Their documentation is then largely about the
cost:

- F\*: "a small change in a query presented to Z3 can cause it to take a
  different search path"; "even a single poorly chosen quantified
  assumption in the prover's context can make an otherwise simple proof
  take very long"; of instantiating by hand, "this style is much
  preferred, if possible" [read: fstar-lang.org tutorial, "Understanding
  how F\* uses Z3"].
- Verus: lemmas reach the solver only by `broadcast use name;`, and "this
  feature should be used with caution … as every extra ambient fact
  slows the prover's overall performance" [read: Verus guide,
  `broadcast_proof.html`].
- Dafny: a proof "successfully verifies one time but fails or times out
  after a small change"; the remedies are `opaque` with `reveal`,
  `assert … by`, and smaller lemmas (quoted in
  [readable-proofs.md](../research/readable-proofs.md) §4.1; the
  reference manual's §13.7.6, "Debugging brittle verification", is in
  its contents today but the fetch didn't reach its text).

Stitchwort ruled a solver out of the trusted path (D573), and SW-3586's
experiment found an untrusted one closed nothing our closers didn't
(D3660). What these languages do show is the working style `byFacts
[lemmas]` gives without a solver: name the lemma, and let the tool match
it to the facts.

### 1.2 The same goals in three systems

All [run]. "Stitchwort" is `cases` at `599e0332e`, the nearest thing it
has ([`SW-4483/cases-probes.txt`](SW-4483/cases-probes.txt)).

| Goal | Rocq `auto` | Rocq, which does | Lean `solve_by_elim` | Lean, which does | Stitchwort `cases` |
|---|---|---|---|---|---|
| `a → b` and `a` give `b` | closes | | closes | | closes when `a` and `b` are equations (`p = True → q = True`, SW-4472); **fails** for `a b: Prop`, and for `a → b → c` |
| `a → b`, `b → c`, `c → d` and `a` give `d` | closes | | closes | | **fails** |
| a local `∀ x => p x → g x` and `p 3` give `g 3` | closes | | closes | | **fails** |
| the same with two premises | closes | | closes | | **fails** |
| a local `∀ x y => p x → q y → r y`, `p 5` and `q 3` give `r 3` (the conclusion doesn't fix `x`) | fails | `eauto` | closes | | **fails** |
| `a` and `b` give `a ∧ b` | closes | | closes | | closes, parts by computing, a fact or `arithmetic` |
| `a ∧ b` gives `a` | fails | `easy`, `tauto` | fails | `simp_all`, or `And.left` named | closes |
| `(a && b) = True` gives `a = True` | fails | `destruct` first | fails | `simp_all` | closes |
| `a → c` and `a ∧ b` give `c` | fails | `tauto`, `firstorder` | fails | `simp_all`, `grind` | **fails** (run with the goal `c ∧ b`) |
| a named lemma, its premise in scope | closes (`using lem`) | | closes (`[lem]`) | | no such form |
| `a = b` and `f b = 0` give `f a = 0` | fails | `congruence`, `subst` | fails | `simp_all` | **fails**, on `Nat` and on `List` |
| `∃ n => p n ∧ q n` gives `∃ n => q n` | fails (`eauto` too) | `firstorder` | fails | `grind` | **fails** |

### 1.3 Where `byFacts` sits, and what the neighbours teach

`byFacts` as specified is two tools the others keep apart, joined:

1. **Taking facts apart and goals apart**: Rocq's `easy` and the first
   half of `intuition`; Aesop's safe rules; the hypothesis side of
   `simp_all`. These steps lose nothing, so they never need undoing.
2. **Backward chaining to a small depth** over hypotheses and named
   lemmas: Rocq's `auto using`, Lean's `solve_by_elim [..]`, Idris's
   search. This is a search and can fail.

Its closest single relative is **Rocq's `intuition (auto using lemmas)`
with no `∨` splitting and no hint database**, or equally **Lean's
`solve_by_elim [lemmas]` run after the hypotheses have been taken
apart**. closer.md files it under "`auto`-style search"; that undersells
the first half, which is what its own count says the formatter needs
most (14 of 50 theorems) and which neither `auto` nor `solve_by_elim`
does (§1.2).

What their choices and pitfalls teach:

| Lesson | From | For `byFacts` |
|---|---|---|
| Keep the steps that lose nothing apart from the search, and never backtrack over them | Aesop's safe and unsafe rules; `intuition t` | Two phases (§4.1). It is also what makes a failure message possible |
| A finisher that fails with one word is hated; one that shows where it stuck is used | `solve_by_elim`'s "failed" [run]; Isabelle: "when `fastforce` or `blast` simply fail, you have no clue why", against `simp` and `auto`, which "show you where they got stuck" | `E-FACTS` shows the goals left after phase 1 (§4.5). closer.md has this right |
| All or nothing | `auto` "leaves it unchanged" and succeeds, so scripts need `solve [auto]` [run]; Isabelle's `auto` leaves a changed goal | `byFacts` is a term: it closes the goal or is an error. Right as specified |
| The default set is where brittleness comes from | `core`, `auto with *`, `@[simp]`, `intuition`'s default solver being changed under its users | No default set; right as specified. And don't let the shared finisher's meaning drift later (§4.9) |
| Depth is not the bound that matters | Rocq 5, Lean 6, Idris 100, all workable; what blows up is a lemma like transitivity, whose premises have unknowns | Bound attempts, as specified, and decide how unknowns are fixed (§4.2) |
| Matching up to unfolding is the cost | `solve_by_elim`: "often useful to change to `.reducible`, so semireducible definitions will not be unfolded when trying to apply a lemma"; `auto`'s weaker `apply` | Compute goal and facts once, then match by head (§4.7) |
| The found proof is worth keeping only if it reads like one | `exact?`'s `And.elim (fun a => imp) (id (And.symm h))` [run]; Aesop's "occasionally buggy scripts" | `--expand-facts` should print `imp h.left`, the term a lane writes (§4.6) |
| Search as an editor action is a real alternative | Agda's Auto, Idris's editor search, `exact?`, `sledgehammer`: the search runs once and the term goes in the file | Stitchwort has this already: `stitchwort search --at`. `byFacts` is worth having beside it only where the written term is noise or breaks when a predicate changes (§5) |

## 2. Earlier research here, and what it predicts

closer.md cited none of these. They agree with each other and with
what §3 finds.

- **practical-proof-languages.md** (SW-327, D570 to D573) set the
  rule: "automation finds, the kernel checks", and "*predictable*
  automation is worth more than *powerful* automation". `byFacts` fits
  both. It ranked rewriting and arithmetic first; neither it nor D571
  asked for a backward-chaining finisher.
- **proof-automation.md** (SW-894) ranked "local `∀` hypotheses
  instantiated once" third in "Steal next", from a probe that still
  fails today (§1.2, row 3), and "show what search found" sixth.
  `byFacts` does the first and `--expand-facts` the second.
- **congruence-closure-evidence.md** (SW-904, D2000): about 150 sites
  where congruence closure would close a step, "but it saves almost no
  lines", because each step was already one line. The same holds here:
  `byFacts` would simplify 12 of my 40 proofs and shorten 5 (§3).
  Anyone reading §3's percentages should read SW-904's result beside
  them: line counts understate these tools and are still the honest
  measure.
- **hammer-stage0.md** (SW-3586, D3660): on 160 leaf goals, plain
  `arithmetic` and `cases` closed 42% and a solver added nothing,
  because "Stitchwort's `arithmetic` and `cases` work *after
  computing*". Two things follow. `byFacts` must compute before it
  matches, or it will miss what `cases` finds (§4.7). And the note's
  own recommendation, "feed `search` hits … into `arithmetic [...]`",
  is the same shape as `byFacts [lemmas]`: named facts handed to a
  closer.
- **simp.md, simp-revisited.md** (D3639): named `rules` sets, no
  default set. Since it was built, `rewrite repeatedly` appears on 192
  lines: 99 in the toy formatter, 72 in std, 21 in the formatter, none
  in AoC, the roguelike or the app [measured]. That is the reference
  class for a new finisher's uptake: real, and local to the code it was
  designed on.
- **readable-proofs.md** (SW-3583) §4: proofs break on "rigid steps on
  flexible output" and "long lemma lists", and hold up with "automation
  that absorbs change within a fragment". `Bool.andLeft (Bool.andRight
  h)` is a rigid step; `byFacts` with a list of at most three names
  absorbs a predicate gaining a part. closer.md's bar 5 tests exactly
  this and is the right bar.
- **SW-4222 and SW-4464** are closer.md's own base and stand.

## 3. The sample: 40 proofs outside slice 1

### 3.1 How it was drawn

[`SW-4483/sample.py`](SW-4483/sample.py), seed 4483, counts a theorem
as closer.md does (statement and proof, to the next blank line) and
draws from six pools [measured]:

| Pool | Theorems | Lines | Drawn |
|---|---|---|---|
| std (`crates/elab/src/std`) | 4,275 | 42,309 | 10 |
| AoC (`aoc/src`) | 2,818 | 30,832 | 10 |
| Roguelike (`games/rogue`) | 173 | 1,660 | 6 |
| App (`apps/whereabouts`) | 181 | 3,691 | 6 |
| Formatter outside closer.md's pools (`tools/fmt/src`) | 3,956 | 56,116 | 4 |
| Toy formatter (`tools/toyfmt`) | 1,801 | 26,287 | 4 |

closer.md's three pools were 924 theorems and 11,157 lines, about a
sixth of the formatter; the fifth row here is the rest.

"Today" is today's tools used differently. "`byFacts`" is stage 1 as
closer.md specifies it, after "today". "With additions" adds §4.2's
and §4.3's (records of proofs; an unknown fixed by a fact).

### 3.2 The 40

| # | Theorem (pool) | Now | Today | `byFacts` | With additions | What it needs |
|---|---|---|---|---|---|---|
| 1 | `Doc.Proofs.writeTopped` (std) | 9 | 9 | 9 | 9 | Arms are `putTopped last printer text width isLast`: `byFacts [putTopped]` is simpler, not shorter |
| 2 | `Text.sliceToList` (std) | 3 | 3 | 3 | 3 | `byComputing` |
| 3 | `List.padRightExample` (std) | 1 | 1 | 1 | 1 | `byComputing` |
| 4 | `List.filterMapMap` (std) | 5 | 5 | 5 | 5 | induction, `rewrite` with the hypothesis |
| 5 | `Parse.givesThen` (std) | 6 | 6 | 6 | 6 | one lemma applied; the term is the proof |
| 6 | `Fin.ofNatCheckDec` (std) | 7 | 7 | 7 | 7 | a `match` on a record; one arm is "apply `c` to `lt`, contradiction", which `byFacts` closes; simpler |
| 7 | `List.allAppendLeft` (std) | 4 | 4 | 4 | 4 | induction; the step is `byFacts [List.allAppendLeft]` if `ys` may be fixed by the fact `hxs` (§4.2); simpler |
| 8 | `Parse.runFromLabelFromBack` (std) | 101 | 101 | 101 | 101 | a long one-off: `let` steps, `rewrite … at` |
| 9 | `Doc.Proofs.readingTouches` (std) | 17 | 17 | 17 | 17 | induction on fuel; uses a lemma's result forwards (`match stepTouches … with \| Both …`), which backward search doesn't do |
| 10 | `Parse.runsOperatorsExample` (std) | 31 | 18 [run] | 12 [estimated] | 12 | Today: 14 lines of `Both byComputing (Both (arithmetic []) …` are one `cases`. `byFacts [Parse.runsOne …]` then closes the four-part tuple of `runsOne` calls, which `cases` and `cases then t` don't [run] |
| 11 | `pathEnds` (AoC) | 6 | 6 | 6 | 6 | opens an `∃` fact and builds an `∃` goal (§4.3) |
| 12 | `sumBit` (AoC) | 3 | 3 | 3 | 3 | `rewrite`, one lemma |
| 13 | `patrolRoute` (AoC) | 10 | 10 | 10 | 10 | `let` steps, a split on `≤`, `rewrite` |
| 14 | `readsContentList` (AoC) | 7 | 7 | 7 | 7 | parser lemmas composed; a walk, if anything |
| 15 | `totalStep` (AoC) | 30 | 30 | 30 | 30 | `rewrite` with nine hypotheses, each named, then two decided splits. A rewriter that used every equation in scope would take it (Lean's `simp_all`); `byFacts` doesn't rewrite |
| 16 | `splitSelf` (AoC) | 10 | 4 [run] | 4 | 4 | Today: the six-arm `match` is `cases` (1.7 ms becomes 3.3) |
| 17 | `goodStepsSnoc` (AoC) | 16 | 16 | 15 [estimated] | 15 | induction; the step's two lines are `byFacts [goodStepsSnoc]` |
| 18 | `part1FromInput` (AoC) | 4 | 4 | 4 | 4 | two lemmas chained by conclusion; `input` fixed by the fact `parsed` (§4.2); simpler |
| 19 | `parseWorksheetSameCells` (AoC) | 10 | 10 | 10 | 10 | `rewrite` with lemmas applied to spelled arguments |
| 20 | `countedJoinAll` (AoC) | 17 | 13 [run] | 13 | 11 [estimated] | Today: `_` for two arguments. With additions: `byFacts [countedJoinAll, labelledJoin, countedJoin]`, the unknown `done` fixed by the fact `inv` |
| 21 | `playerMovesAtMost` (rogue) | 9 | 5 [run] | 5 | 5 | Today: `cases then (rewrite enterHitPoints … then atMost)` (2.1 ms becomes 9.7). Plain `cases` is `E-CASES-BUDGET` after 845 ms [run] |
| 22 | `turnKey` (rogue) | 6 | 6 | 6 | 6 | `rewrite` |
| 23 | `monstersTurnPlayer` (rogue) | 2 | 2 | 2 | 2 | already an or-pattern |
| 24 | `monstersTurnHurt` (rogue) | 6 | 6 | 6 | 6 | `arithmetic [lemma …]` |
| 25 | `insideOf` (rogue) | 7 | 7 | 7 | 2 [estimated] | The hypothesis is four `≤` tests joined by `&&`; the goal is a record of four proofs. `cases` fails on the record [run]. With records as "and" (§4.3) it is `byFacts` |
| 26 | `goalReachable` (rogue) | 13 | 13 | 13 | 13 | transitivity through a middle point: the case backward search is worst at |
| 27 | `remainderWithin` (app) | 7 | 7 | 7 | 7 | `Both (arithmetic [el, ed, h]) (arithmetic [eh, ed, h])`: one line either way; simpler |
| 28 | `nonzeroSize` (app) | 1 | 1 | 1 | 1 | `arithmetic [nz]` |
| 29 | `spanRange` (app) | 29 | 29 | 29 | 29 | a chain of `Float` monotonicity steps, each a `let` |
| 30 | `wrapNear` (app) | 103 | 103 | 103 | 103 | a long one-off |
| 31 | `notIeeeLeOfUnits` (app) | 11 | 11 | 11 | 11 | an `∨` split with `arithmetic [lemma …, h]` in each side |
| 32 | `turnTimes` (app) | 21 | 21 | 21 | 21 | cases on an `Int`, `algebra`, `arithmetic [..]` |
| 33 | `commentShapeExample` (fmt) | 2 | 2 | 2 | 2 | one lemma |
| 34 | `doc1Shape` (fmt) | 40 | 40 | 28 [estimated] | 28 | Twelve arguments that are `Bool.andLeft (Bool.andRight (… sound))` chains become `byFacts [plainDefShape]`. Today's alternative, `cases` as each argument, is `E-CASES-BUDGET` after 9.07 s (the hand proof: 21 ms) [run] |
| 35 | `calmShape` (fmt) | 10 | 10 | 10 | 10 | already an or-pattern |
| 36 | `valueElKept` (fmt) | 6 | 6 | 6 | 6 | one arm is `elCalm value around good`; simpler |
| 37 | `viewsCons` (toy) | 10 | 10 | 10 | 10 | take `[a, ..b] = [c, ..d]` apart, apply the local `∀` `step` to the parts: both arms are `byFacts`; simpler. 8 with stage 2's `cases tokens then byFacts` |
| 38 | `givesParameters` (toy) | 6 | 6 | 6 | 6 | a walk; its leaves are pairs of facts |
| 39 | `noteNotes` (toy) | 8 | 8 | 8 | 8 | `Eq.cong` with a function: congruence, the one such case in 40 |
| 40 | `runsExpressionExample` (toy) | 47 | 40 [estimated] | 40 | 40 | Today: an 8-line tuple of `byComputing` and `arithmetic []` is `cases`, as in row 10 (not run: the toy formatter doesn't check at this commit, §7). The other tuples hold data, which no finisher invents |
| | **All 40** | **641** | **607** | **588** | **581** | |

By pool:

| Pool | Now | Today | `byFacts` | With additions | `byFacts` beyond today |
|---|---|---|---|---|---|
| std | 184 | 171 | 165 | 165 | 3.3% |
| AoC | 113 | 103 | 102 | 100 | 0.9% (2.7% with additions) |
| Roguelike | 43 | 39 | 39 | 34 | 0 (11.6%) |
| App | 172 | 172 | 172 | 172 | 0 |
| **Outside the formatters** | **512** | **485** | **478** | **471** | **1.4% (2.7%)** |
| Formatter, elsewhere | 58 | 58 | 46 | 46 | 20.7% |
| Toy formatter | 71 | 64 | 64 | 64 | 0 |
| **Formatters** | **129** | **122** | **110** | **110** | **9.3%** |
| **All** | **641** | **607** | **588** | **581** | **3.0% (4.1%)** |

Each figure rests on one to three theorems, so each is good to a factor
of two at best, as closer.md says of its own.

### 3.3 Reading it

- **closer.md's 4 to 10% holds in the formatter and not outside it.**
  Its own random 30 gave 4.1% beyond today's tools; the formatter rows
  here give 9.3%, all of it one theorem (`doc1Shape`). Outside the
  formatters it is 1.4%, or 2.7% with the additions.
- **Today's tools take more than `byFacts` would: 5.3%**, 27 of the 34
  lines run. closer.md's stage 0 found the same in the formatter, and
  its pilot then beat its own estimate (8.3% and 7.6% of two files
  against 3.5% estimated [read: SW-4473]). The cheapest lines left are
  still the ones nobody has to build anything for (§7).
- **What finishes proofs outside the formatter.** Of the 28 proofs
  `byFacts` wouldn't touch: `rewrite` with named lemmas or hypotheses,
  6; long one-off chains of `let` steps, 5; `cases` or an or-pattern,
  now or with today's tools, 5; computing or a single lemma, 4;
  `arithmetic [..]` and `algebra` with hints, 4; walks and parser
  lemmas, 2; an `∃`, 1; congruence, 1 [by hand]. That
  matches SW-3586's finding that `arithmetic` and `cases` are the
  closers general code leans on.
- **Splitting, then one finisher, is as common as the finisher.** Rows
  16, 21, 25 and 37 are "split this, then close every case the same
  way"; row 21's plain `cases` runs out of budget because it can't be
  told what to split. That is SW-4474 and closer.md's stage 2, and in
  this sample it is worth about what stage 1 is.

Counts over whole projects [measured: [`SW-4483/counts.py`](SW-4483/counts.py)]:

| Project | Lines | `Bool.andLeft`, `andRight`, `andIntro` | `And.left`, `.left`, `.right` | `Both` | `Witness`, `Exists.elim` | `arithmetic [..]` | …naming a part of a fact | Lines that only name a part of a fact |
|---|---|---|---|---|---|---|---|---|
| std | 68,861 | 27 | 520 | 1,519 | 615 | 549 | 38 | 39 |
| AoC | 55,432 | 6 | 827 | 1,920 | 1,026 | 447 | 67 | 196 |
| Roguelike | 2,964 | 0 | 9 | 21 | 12 | 8 | 0 | 8 |
| App | 4,508 | 30 | 248 | 68 | 0 | 109 | 1 | 19 |
| Formatter | 107,239 | 2,808 | 573 | 416 | 226 | 236 | 0 | 293 |
| Toy formatter | 38,116 | 4 | 387 | 676 | 238 | 66 | 12 | 9 |

So the `Bool.and…` spelling closer.md counted is the formatter's alone
(2,808 of 2,875 lines), but taking "and" facts apart and building them
is everywhere under other names: 4,786 line matches of `Both`, `.left`
and `.right` in std and AoC. Almost none of those are whole lines (the last
column: 235 in std and AoC), which is why `byFacts` simplifies more
than it shortens. `∃` is as common as `∧` in AoC, and the stage 1
specification doesn't mention it.

## 4. The design, point by point

### 4.1 Shape: two phases

Specify it as Aesop and `intuition` are built:

1. **Phase 1, never undone.** Introduce `∀` and `→`. Take every fact
   apart (§4.3). Replace variables by equations (§4.4). Split the goal
   into its parts. Close any part that computes, is a fact, or is
   refuted by two facts.
2. **Phase 2, a bounded search, on each part left.** A fact or listed
   lemma whose conclusion fits; its premises the same way; then
   `arithmetic` with the facts.

closer.md's list has the same steps in one ordered list. Writing them
as two phases fixes what the error shows (§4.5), what `byFacts then ?`
shows, and what is shared with `cases` (§4.9).

### 4.2 Depth, and how unknowns are fixed

- **Depth 3 is fine.** Rocq uses 5 and Lean 6; three chained
  implications (§1.2, row 2) need exactly 3. Depth is not what makes
  these searches slow.
- **What is missing is a rule for unknowns.** A lemma's conclusion often
  doesn't fix all its arguments: `countedJoinAll`'s `done`,
  `part1FromInput`'s `input`, `List.allAppendLeft`'s `ys` (rows 20, 18,
  7: 3 of 40). Rocq splits this into two tools: `auto` refuses such a
  lemma and `eauto` searches for the unknown, at a larger cost; Lean's
  `solve_by_elim` allows it [run].
  Recommended rule: **an unknown the conclusion leaves open may be fixed
  by matching one of the lemma's premises against a fact in scope, and
  by nothing else.** After the premises are matched, an unknown still
  open is a failure. That is `eauto` cut down to what the three rows
  need, and it keeps transitivity (row 26) from searching: its middle
  point is fixed only if a fact names it.
- **No witness is ever invented.** An `∃` goal is closed only by a fact
  that is the same `∃`, or by a lemma. Rows 10 and 40 show the limit:
  tuples that carry data stay written.

### 4.3 Which facts are taken apart, and local `∀` facts

- **Apply local `∀` facts: yes.** Every system above does; it is
  proof-automation.md's rank 3; today nothing does (§1.2). Rows 5, 6
  and 37 need it.
- **Add `∃` facts** to what phase 1 opens (a `Witness` gives a variable
  and a fact). 1,641 lines in std and AoC handle `∃` by hand
  [measured]; row 11, and row 17's `new`, are of this kind.
- **Add records of proofs**, as facts (their fields) and as goals (each
  field a part). Row 25: `cases` closes an `∧` goal by parts and fails
  on the same four facts as a record [run]. Lean's `constructor` and
  Aesop's built-in rules treat any one-constructor proposition this way.
- **Don't split `∨` or data.** Right as specified: that is `cases`, and
  the reason `byFacts` can promise to fail fast.

### 4.4 Equations in scope

closer.md: "used as `cases` uses them now: a variable side is replaced".
**That behaviour isn't there** for a hypothesis as written: `cases`
fails on `(e: a = b) (h: f b = 0): f a = 0`, on `Nat` and on `List`
[run], and SW-4474 already records "a hypothesis written as `is: kind =
Minus` is never used to substitute". So stage 1 needs its own rule:

- in phase 1, an equation with a variable on one side replaces that
  variable everywhere (Rocq's `subst`);
- a fact closes a goal that is the same equation flipped
  (`solve_by_elim`'s `symm`);
- nothing else: no rewriting with equations between calls (that is
  `rewrite repeatedly [h]`, and row 15 shows the demand for it), and no
  congruence closure (SW-904: no lines saved; 1 of these 40, row 39).

### 4.5 The failure message

closer.md's `E-FACTS` is right in intent. With two phases it can be
exact: show **each part of the goal left after phase 1**, and under
each, the facts and lemmas whose conclusions fit and the first premise
of each that nothing closed. Say separately when the attempt limit
stopped it, with the count. `solve_by_elim`'s "failed" and `blast`'s
silence are what to avoid; `auto`'s silent no-op can't happen in a
term.

### 4.6 Naming lemmas, hint sets, and writing the term back

- **Named on the call, no default set**: right, and every system's own
  advice (closer.md §3).
- **Let the list take terms**, as `arithmetic [e1, e2]` and the walk's
  brackets do: `byFacts [putTopped last printer]`. `solve_by_elim` and
  `auto using` both take terms.
- **Cut `rules` sets from the list for stage 1.** A `rules` set is
  equations for rewriting; `byFacts` doesn't rewrite. Read as "apply
  each member backwards" it becomes a hint database by another name,
  with the brittleness Rocq warns of.
- **Warn on a listed lemma that wasn't used**, as
  `W-REWRITE-REPEATEDLY-UNUSED` does. Lists that only grow are the
  "long lemma lists" readable-proofs.md warns about.
- **`--expand-facts`**: keep it, and print projections as a lane writes
  them. Second priority: stage 1 is useful without it, and
  `search --at` already writes found terms.

### 4.7 Check-time bounds

- **Compute once, then match by head.** Normalise the goal and each
  fact once (as `cases` does; without it `area.contains position =
  True` is never seen as four facts, and SW-3586's lesson is lost),
  index facts and lemmas by the head of their conclusions, and try full
  unification only where heads agree. closer.md's "nothing unfolds to
  search" should be read as "nothing unfolds *during* the search".
- **Count attempts, never time**, as specified. F\*'s and Dafny's
  experience is that proofs near a resource limit are the brittle ones:
  print attempts used in `--timings`, and keep the limit small enough
  that a passing proof is far from it.
- **It must fail fast**, because `cases then byFacts [..]` runs it at
  every node of the split. Row 34 is the warning: a finisher that
  splits when a part isn't found took 9 s to fail [run]. closer.md's
  bar 2 measures successes only; add a bar for failures (§5).

### 4.8 With `cases … then`, and stage 2

- `cases then byFacts [lemmas]` is the useful pair, and the one
  Lean's `rcases … <;> simp_all` and Rocq's `destruct …; intuition`
  correspond to.
- Stage 2's `cases x then t` is SW-4474's "say what to split". It has
  the better evidence of the two: 8 budget failures in SW-4473's pilot
  and row 21 here, all [run], against estimates for stage 1. Do it
  alongside stage 1, not after its bar.

### 4.9 One shared finisher?

Yes, with a condition. Other systems are built this way: `intuition`
takes its solver as an argument, `exact?` discharges with
`solve_by_elim`, Aesop normalises with `simp_all`, Isabelle's `auto` is
its simplifier plus its classical reasoner over shared rule lists. The
warning is `intuition`, whose default solver is being changed under
every proof that uses it. So:

- share **phase 1 and the facts-only search** as the closer of `cases`,
  `rewrite repeatedly` and the walk's leaves: one list in place of
  three, as closer.md says;
- named lemmas stay explicit (`then byFacts [..]`, the walk's
  brackets);
- once shared, its steps are fixed: a later addition is a new form, not
  a change to what `cases` means.

Share it only after the pilot shows `cases` and the walk no slower on
the files that use them (closer.md's lane 1c already re-times this).

### 4.10 Anything to cut?

Only the `rules` sets (§4.6). The rest of stage 1 is the common core of
the tools in §1.

## 5. Recommendation for D3708

**Build it, with the changes of §4.**

- **The problem.** Stitchwort has no small logical finisher. Three
  chained "if … then" facts, or a local "for all" fact applied to what
  is in scope, have to be written out as a term; `cases` fails on them
  [run]. Where predicates are long "and"s, the term is positional
  (`Bool.andLeft (Bool.andRight …)`, 2,808 lines of the formatter
  [measured]) and breaks when a part is added. The one substitute,
  `cases` as a finisher, can take seconds to fail [run].
- **The change.** `byFacts [lemmas]`, as closer.md's stage 1 with six
  changes: two phases; `∃` facts and records of proofs taken apart;
  unknowns fixed by a fact and never guessed; its own small rule for
  equations; terms in the list and no `rules` sets; a failure message
  built on phase 1. "Tell `cases` what to split" (SW-4474) goes
  alongside. About 4 agent hours for `byFacts` with review and pilot
  [estimated: closer.md's 3 plus the additions], 1.5 to 2 for
  SW-4474.
- **What it should do.** Close the eight logical goals of §1.2 that
  `cases` fails on. About 3% of proof lines across Stitchwort, 4% with
  the additions; about 9% in formatter-style code and 1 to 3% in std,
  AoC, the roguelike and the app [estimated from 40 theorems, each
  figure good to a factor of two]. Simpler terms in about one proof in
  three (12 of 40) [estimated]. It is not a route to Lean's line
  counts: today's tools, used, are worth more lines (5.3% of this
  sample, mostly run).

**Why not "don't build".** The argument against is §3: under 3% outside
the formatter, and `search --at` already finds these terms once.
I come down for building because the cost is small, every comparable
system keeps this tool, the formatter is where Stitchwort's largest
proofs are and its next slices are the same shape, and a finisher that
can't split is the fix for row 34's 9 seconds.

**Bars that would show it is generally useful.** closer.md's six bars
are formatter bars and should stay, re-based (§6). Add:

| # | Bar |
|---|---|
| G1 | The goals of §1.2 marked "fails" close with `byFacts`, each within 1 ms of the hand term |
| G2 | Of this review's rows 7, 10, 17, 18, 20, 25, 34 and 37, at least five are shorter or the same length with fewer names spelled, and check |
| G3 | A pilot outside the formatter: one std file from `Doc/`, one AoC day that uses `Both` heavily, and `games/rogue`'s `Reach.sw`. After a today's-tools pass, `byFacts` takes a further 2% of their proof lines, with check time within 1.5 times |
| G4 | A `byFacts` that fails does so in under 5 ms on every reject example and on row 34's arguments with a part removed |
| G5 | Uptake, no threshold: uses per project four weeks on, beside `rewrite repeatedly`'s 192 lines (none outside std and the formatters) |

If G3 fails and closer.md's formatter bars pass, keep it and call it
what it is: a tool for code with large predicates. If both fail, stop
at stage 0.

**The name.** Keep `byFacts`. It says where the proof comes from, as
`byComputing`, `byDecision` and `byWalking` do, and `arithmetic [e1,
e2]` already documents its brackets as "facts … added", so `byFacts
[lemma]` reads the same way. The names other systems use are worse
here: `auto` is taken, `assumption` and `trivial` promise less than it
does, and `solve_by_elim` says nothing.

## 6. What changes or contradicts closer.md

1. **"4 to 10% of proof lines"** is a formatter figure. Outside the
   formatters this sample gives 1.4% (2.7% with additions).
2. **"Equations in scope are used as `cases` uses them now"** rests on
   a behaviour `cases` doesn't have for hypotheses as written (§4.4).
3. **"`auto`-style search"** misplaces it: neither `auto` nor
   `solve_by_elim` takes a fact apart [run]. It is `intuition` with a
   small `auto` (§1.3).
4. **Stage 0 took part of stage 1's ground.** SW-4472 made `cases`
   apply an implication to a fact and close conjunctions by parts, and
   the guide now shows `endedWeaker`, `signSymbolic`, `parenParsed`,
   `tupleParsed` and `itemsParsed` shortened by today's tools [read:
   proving guide, "Finishing small proofs"]. Those are five of bar 1's
   ten theorems. Bar 1 needs a new list and a recount of SW-4222's 21
   after stage 0 before stage 1's pilot can be judged against it.
5. **The implication step is narrower than the guide suggests.**
   `cases` applies `trails = True → trails' = True`, and fails on
   `(f: a → b → c) (x: a) (y: b): c` and on `(h: a ∧ b) (f: a → c): c ∧
   b` with `a b c: Prop` [run].
6. **`cases` as an argument** ("`ih cases cases`", closer.md's lane 0b)
   has a failure cost the guide's table doesn't show: 9.07 s on row 34
   [run].
7. **Stage 2 shouldn't wait for stage 1's bar** (§4.8).
8. **The unknowns rule** (§4.2) and **`∃` and records** (§4.3) are
   absent from the specification.

## 7. Findings worth tickets

- **A today's-tools pass over std's and the toy's example theorems.**
  `Both byComputing (Both (arithmetic []) …` tuples are one `cases`:
  `Parse.runsOperatorsExample` goes from 31 lines to 18 [run:
  [`SW-4483/example-probe.sw.txt`](SW-4483/example-probe.sw.txt)].
  `(arithmetic [])` in a tuple is on 15 lines of std, 35 of the
  formatter and 19 of the toy [measured].
- **`cases` fails on a goal that is a record of proofs** where it
  closes the same facts as an `∧` (`insideOf`, `games/rogue`'s
  `Reach.sw:102`) [run].
- **`cases` as an argument can run 9 s before `E-CASES-BUDGET`**
  (`doc1Shape`, `Fmt/ToldDeclProofs.sw:1939`, eleven arguments that are
  parts of `within`, `sound` and `nonCloser`) [run]. The guide's
  "Costs, and when not to" should say so; and a part of a hypothesis
  that isn't found shouldn't lead to splitting.
- **`cases` and implications between plain propositions**: §6, item 5,
  with the probes in `SW-4483/cases-probes.txt`.
- **`splitSelf`** (`aoc/…/Year2025/Day04/Proofs/Window.sw:199`) is
  `cases` (10 lines to 4); **`playerMovesAtMost`**
  (`games/rogue/…/HitPoints.sw:21`) is `cases then (rewrite
  enterHitPoints state (state.player.toward direction) then atMost)` (9
  to 5); **`countedJoinAll`** (`aoc/…/Year2025/Day08/Proofs/Part2.sw:366`)
  takes `_` for `done` and `c` (17 to 13). All [run].
- **The toy formatter may not check at `599e0332e`**: `check --only
  Toy.Fmt.Proofs.viewsCons Toy.Fmt.Proofs` in `tools/toyfmt` reported
  `E-TYPE-MISMATCH` about the test fact `isOperatorChar other`, near
  `Toy.Syntax.operatorNext.eq3`. I ran it once, in the lane's worktree
  with the main checkout's binary, and didn't look further; it may be
  known, or an effect of `--only`.
- **closer.md's bar 1** needs re-basing (§6, item 4).

## Sources

- Lean 4.35.0, `src/lean` under the Nix store path of `nixpkgs#lean4`:
  `Init/Tactics.lean` (lines 1446, 1544, 1704-1810 on `solve_by_elim`,
  `apply_assumption` and `apply_rules`, 1812-1858 on `exact?` and
  `apply?`, 1868, 1877-1881 on `show_term`);
  `Lean/Meta/Tactic/SolveByElim.lean:79-102`;
  `Lean/Meta/Tactic/Backtrack.lean:46-71`;
  `Lean/Elab/Tactic/LibrarySearch.lean:41-73`; `Init/Try.lean:30-56`.
  Run: `SW-4483/Probe.lean`.
- Rocq 9.1.1, the Nix store's `rocq-9.1.1` (`nixpkgs#rocq-core`):
  `lib/rocq-runtime/tactics/auto.ml:408-425`,
  `lib/coq/theories/Init/Tactics.v:158-187`. Run: `SW-4483/Probe.v`.
- Fetched 21 Nov 2026 through a summarising fetch:
  - rocq-prover.org/doc/V9.1.0/refman/proofs/automatic-tactics/auto.html
    (its first 100,000 characters; the "Creating hints" sections were
    not reached) and …/automatic-tactics/logic.html;
  - github.com/leanprover-community/aesop (README);
  - lean-lang.org/doc/reference/latest/The--grind--tactic/;
  - agda.readthedocs.io/en/latest/tools/auto.html;
  - idris2.readthedocs.io/en/latest/tutorial/miscellany.html;
  - fstar-lang.org/tutorial/book/under_the_hood/uth_smt.html;
  - verus-lang.github.io/verus/guide/broadcast_proof.html;
  - dafny.org/dafny/DafnyRef/DafnyRef (contents only; §13.7 not
    reached).
- Tobias Nipkow, *Programming and Proving in Isabelle/HOL*, edition of
  24 October 2026, isabelle.in.tum.de/doc/prog-prove.pdf, §3.3 and
  §3.4, read as text (`pdftotext`).
- Stitchwort: `docs/proposals/closer.md`, `simp.md`,
  `simp-revisited.md`; `docs/comparisons/practical-proof-languages.md`
  §5.1, §8; `docs/research/proof-automation.md` §1, §5.4, §6;
  `congruence-closure-evidence.md` (head, §1); `hammer-stage0.md` §1,
  §4; `readable-proofs.md` §4; `docs/proving-guide.md`, "Finishing
  small proofs"; `docs/syntax.md` (`arithmetic`, `cases`, `byWalking`,
  `search --at`); `crates/elab/src/closing.rs` (head comment); the
  commits of SW-4472 and SW-4473; the board entries for SW-4473,
  SW-4474 and SW-4480.
- Not read: the reviews SW-4222 and SW-4464 beyond what closer.md
  quotes from them; `simp.md` and `simp-revisited.md` beyond their
  summaries; Isabelle's reference manual; CoqHammer's `sauto`.
