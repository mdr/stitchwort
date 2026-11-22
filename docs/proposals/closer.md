# A closer for the leftovers: what it would close, and what to build

**Status:** design note, 20 November 2026 (SW-4242, a Fable paper lane).
Nothing is built. The decision in [§7](#7-one-decision-for-matt) is
Matt's. Read against `main` at `f3944b805`.

It follows [SW-4222](../reviews/SW-4222-lean-rocq-comparison.md) §6.3 and
[SW-4464](../reviews/SW-4464-lean-rocq-standing.md), and keeps the
constraints of [simp-revisited.md](simp-revisited.md) (named rule sets,
no default set, computing decides, nothing unfolds to search).

How claims are marked:

- **[measured]**: counted by script today, or checked with the main
  checkout's release binary on a probe theorem added to one namespace
  (`check --only`), then removed. The probes are kept as
  `dev/patches/SW-4242-closer-probes.patch`.
- **[read]**: read today in the file named (Lean 4.35.0's and Rocq 9.1.1's
  installed sources, from nixpkgs) or on the Rocq 9.1 reference manual's
  page named, through a summarising fetch.
- **[estimated]**: my judgement, by hand, of a proof under a tool that
  doesn't exist yet.

## In plain words

**The question.** Lean and Rocq finish small proofs with one word
(`grind`, `simp_all`, `auto`, `intuition`). Stitchwort writes the term
out. How much of the remaining gap would such a closer take, and which
kind should we build?

**What I did.** I went through 50 slice 1 proofs by hand: SW-4222's 21,
and 30 drawn at random (seeded) from the formatter's dispatcher,
tree-fact and printer files. For each I asked what a closer would have
to know to finish it, and where that knowledge is. Where today's tools
might already do it, I tried it: 23 probe proofs, checked.

**What I found.**

1. **Nearly half of the reachable saving needs nothing built.** On SW-4222's
   sample, 20 of the 217 lines go using `cases`, `rewrite repeatedly`,
   or-patterns and `_` as they are today (17 lines measured, 3
   estimated). Lanes don't write proofs that way. Two helper lemmas go
   too.
2. **A closer that uses the facts in scope takes about as much again.**
   217 lines become about 174 [estimated], against Lean's 159. In the
   random sample, which is mostly long one-off proofs, it takes much
   less: 314 lines become 303 with today's tools [measured] and about
   290 with the closer [estimated]. So expect **4 to 10% of proof lines**
   in these kinds of file, not a halving.
3. **What the closer needs is small and specific.** No proof in the
   sample needs Lean's `grind` machinery (congruence closure with a
   tagged library searched by pattern). They need four plain things:
   take "and" facts apart and put them together, apply a hypothesis
   that says "if A then B" when A is in scope, apply a named lemma whose
   conclusion is the goal, and close each part of an "and" goal
   separately. The formatter's proofs spell the first of these out
   4,299 times (`Bool.andLeft`, `Bool.andRight`, `Bool.andIntro`)
   [measured].
4. **A default lemma set (SW-4241) closes almost nothing here.** One of
   the 50 proofs rewrites with std list lemmas, and it would get no
   shorter in lines.
5. **Today's closers are slow on small goals.** The probe proofs that
   use `cases` to finish check 4 to 25 times slower than the hand terms
   (2 ms becomes 14 to 46 ms) [measured]. That is probably why lanes
   avoid them, and it sets the bar for anything new.

**Recommendation.** Not a `grind`, not a default set. Three small
stages, each with a bar:

- **Stage 0, no decision needed:** fix three gaps the probes found in
  `cases` and `rewrite repeatedly`, teach the forms, and convert two
  files as a pilot. About 2 agent hours.
- **Stage 1, the decision:** one proof term, working name `byFacts
  [lemmas]`: it closes a goal from the facts in scope and the lemmas
  named, by the four steps above, with no case splitting and no
  rewriting of its own. `cases`, `rewrite repeatedly` and the walk's
  leaves then share it as their closer. About 3 agent hours with its
  review and pilot.
- **Stage 2, only if stage 1 clears its bar:** one proof text over arms
  that split differently (`cases x then t`). The evidence is two large
  printer proofs, so it waits.

If all three land as estimated, SW-4222's sample is at about 150 to 175
lines against Lean's 159: level, within the noise of the sample.

## 1. The sample and the probes

**SW-4222's 21 theorems**, as SW-4464 counted them today: 217 lines.

**30 more, at random.** A script ([`closer/sample.py`](closer/sample.py), seed 4242) drew 10
theorems from each of three pools in `tools/fmt/src` [measured]:

| Pool | Files | Theorems | Lines |
|---|---|---|---|
| Dispatchers | `Fmt/Kinds.sw`, `SpellProofs.sw`, `TokenProofs.sw`, `Spacing*Proofs.sw`, `Syntax/Settle*Proofs.sw` | 483 | 6,375 |
| Tree facts | `Syntax/ParseWalk*.sw`, `ParseProofs.sw`, theorems whose text names no walk family | 138 | 1,007 |
| Printer | `Fmt/JoinProofs.sw`, `PassProofs.sw`, `TreeJoinProofs.sw`, `GlueProofs.sw` | 303 | 3,775 |

The 30 are 314 lines (statement and proof, to the next blank line, as
SW-4464 counts). `signSymbolic` came up in both samples. All of
`tools/fmt/src` is 5,399 theorems and 72,840 lines by the same count
[measured].

**A caution about the pools.** The "dispatcher" files are not mostly
dispatchers. Four of the ten drawn are long one-off proofs
(`settledHomed` 50 lines, `arrowGo` 31, `commaCarryDrop` 15, `dropFItem` 14)
made of `let` steps that each apply a named lemma to spelled arguments.
No closer shortens those. SW-4222's sample was chosen to show the kinds
where Lean was shorter; a random draw is the fairer guide to the whole.

**Probes.** 23 theorems, most of them a sample theorem's statement with
a shorter proof, appended to its own namespace and checked with
`stitchwort check --only`, one namespace at a time. 15 checked, 8
failed; the failures are as useful as the passes (§2.3).

## 2. What a closer would close

"Today" is today's tools, used differently. "Facts closer" is stage 1 of
§6. "Arms" is stage 2. Lines after each, cumulatively.

### 2.1 SW-4222's sample

| Theorem | Now | Today | Facts closer | What it needs, and from where |
|---|---|---|---|---|
| `signSymbolic` | 3 | 2 [measured] | 1 [estimated] | Today: `\| Inl is \| Inr is => rewrite is`; `minusSymbolic` and `bangSymbolic` are then unused. Closer: split the `∨` hypothesis and put the constructor in; `cases` should and doesn't (§2.3) |
| `closerNotComma` | 1 | 1 | 1 | already `cases` |
| `endedWeaker` | 9 | 9 | 5 [estimated] | Split `edge` (`cases` does), then apply the hypothesis `implies: trails = True → trails' = True` to the fact `waits` in scope. `cases` closes 4 of its 5 cases and fails on this one [measured] |
| `itemsParsed` | 10 | 10 | 9 [estimated] | the pairs at the end: facts in scope |
| `givesExpect` | 13 | 13 | 11 [estimated] | the leaf's three nested rewrites with `same`, `took`, `shape`: equations in scope |
| `givesTupleClose` | 5 | 5 | 5 | a walk (W4, SW-4421, in review) |
| `parenParsed` | 12 | 8 [measured] | 6 [estimated] | Today: `rewrite repeatedly [openText, closeText, lexical]` inside the tuple. Closer: apply `parsed` to `within`, take the result apart, rewrite with `openText` and `closeText`, compute |
| `tupleParsed` | 13 | 9 [measured, as `rewrite repeatedly [..] then cases`] | 7 [estimated] | the same, and the lemma `itemsParsed` by name |
| `givesParenClose` | 6 | 6 | 6 (5 with the lemma named at the walk's leaf) | `parenParsed` is a lemma whose conclusion is the leaf's goal, its premises all in scope |
| `givesTupleEnd` | 8 | 8 | 8 (6 likewise) | `tupleParsed`, the same way |
| `givesCommaListFrom` | 9 | 9 | 9 | already a walk |
| two-run group | 20 | 20 | 20 | walks |
| `alikeParen` | 9 | 9 | 6 [estimated] | compute both sides, rewrite with the three hypotheses, compute: the `calc` only orders this |
| `allTokensWithout` | 14 | 13 [measured] | 12 [estimated] | Today: `ih cases cases` for the `&&` facts. Closer: the same, cheaper |
| `joinsWeaker`, `writeWeaker`, `sepWeaker` | 54 | 54 | 47 [estimated] (25 with arms, low confidence) | `writeWeaker` and `sepWeaker`: split `edge`, then `implies _ after` and pairs, as `endedWeaker`. `joinsWeaker`'s 26 forms each apply a `…Weaker` lemma to what is in scope: one text, if arms can share it (§5, d) |
| `passesCons` | 7 | 7 | 7 | the term is the proof |
| `joinsAllAppend` | 11 | 8 [estimated] | 8 | `_` for arguments the goal fixes, as below; not probed |
| `passesAppend` | 13 | 6 [measured] | 6 | Today: `joinsAllAppend _ front back edge next (first edge _ holds (…))`: the two long arguments are found by unification |
| **All 21** | **217** | **197** | **174** (152 with arms, 149 with lemmas at the walks' leaves too) | Lean 159, Rocq 125 |

By kind, against SW-4464's table:

| Kind | Now | Today | Facts closer | Lean |
|---|---|---|---|---|
| 1 Dispatchers | 13 | 12 | 7 | 7 |
| 2 List helpers | 10 | 10 | 9 | 11 |
| 3 Parser walks and tree facts | 57 | 49 | 43 (40 with lemmas at leaves) | 29 |
| 4 Comma list | 9 | 9 | 9 | 16 |
| 5 Two runs | 29 | 29 | 26 | 33 |
| 6 Rule N | 14 | 13 | 12 | 15 |
| 7 Printer | 85 | 75 | 68 (46 with arms) | 48 |
| **All** | **217** | **197** | **174** | **159** |

Kind 3 stays behind Lean after everything: what is left there is
statements (3 to 5 lines of hypotheses each) and W4's conversion, not
closing.

### 2.2 The random 30

Only the theorems that change are listed; the other 19 (189 lines) stay
as they are under every option.

| Theorem (pool) | Now | Today | Facts closer | What it needs |
|---|---|---|---|---|
| `endsOnStep` (dispatcher) | 9 | 4 [measured] | 4 | `cases` does the two nested matches |
| `prefixSpells` (dispatcher) | 14 | 14 | 11 [estimated] | four `spells…` lemmas chained by their conclusions |
| `symbolicWithin` (tree) | 3 | 1 [measured] | 1 | `cases` |
| `signSymbolic` (tree) | 3 | 2 [measured] | 1 [estimated] | as above |
| `bangSymbolic` (tree) | 1 | 0 [measured] | 0 | not needed once `signSymbolic` rewrites |
| `leftLinkOf` (tree) | 12 | 12 | 10 [estimated] | apply hypotheses to facts, take pairs apart |
| `atomParsed` (tree) | 9 | 9 | 8 [estimated] | the first part of the tuple is a part of `within` |
| `signQuietOf` (tree) | 14 | 14 | 11 [estimated] | rewrite a hypothesis with three facts, take the `&&` apart, one lemma |
| `parenInnerPasses` (printer) | 7 | 5 [measured] | 5 | `cases` alone |
| `closerNotesPasses` (printer) | 11 | 11 | 8 [estimated] | `passes…` lemmas by conclusion, `&&` parts of `sound` |
| `lastArgumentPasses` (printer) | 42 | 42 | 42 (24 with arms [estimated]) | 11 arms with one text; a catch-all fails today because `Paren` needs a second split [measured] |
| **All 30** | **314** | **303** | **290** (272 with arms) | |

Today's tools: 3.5% of the lines [measured]. The facts closer: 4.1% more
[estimated]. Arms: 5.7%, all of it one theorem. Over the formatter's
72,840 theorem lines those rates are about 2,500, 3,000 and 4,000 lines,
each good to a factor of two at best: 30 theorems of 5,399.

### 2.3 What the probes found in today's tools

All [measured].

| # | Probe | Result |
|---|---|---|
| F1 | `rewrite repeatedly [openText, closeText, shaped, lexical]` on `parenParsed` | Fails with what is left: `True = True ∧ ("(" == "(" && ")" == ")" && True) = True ∧ True = True`. Every part computes; it has no closer for "each part of an `∧`" (simp-revisited's stage 3 closer was never built) |
| F2 | `signSymbolic := cases` | `E-CASES-BUDGET`: it splits `kind` (over 60 token kinds) and never splits the hypothesis `kind = Minus ∨ kind = Bang` first |
| F3 | `… then cases` on the closed goal of F1 | checks, in 46 ms against the hand term's 1.8 ms. The same proof with `rewrite repeatedly` inside one part of the tuple is 2.9 ms |
| F4 | `commaDeletedDrop := cases` | `E-CASES-BUDGET`: it splits `comma.token.kind`, which the hand proof never needs (it splits two things). There is no way to tell `cases` what to split |
| F5 | `endedWeaker := cases` | closes 4 cases and fails in the one that needs `implies waits`: no closer applies a hypothesis that is an implication |
| F6 | `lastArgumentPasses` with `\| other, joins => (elPasses kinds other within joins around, byComputing)` for its 11 like arms | type mismatch in the `Paren` case: the catch-all splits one level and the program splits two |

Check time of the probes that pass, hand proof then probe:

| Theorem | Probe | Hand, ms | Probe, ms |
|---|---|---|---|
| `symbolicWithin` | `cases` | 1.9 | 1.7 |
| `signSymbolic` | or-pattern, `rewrite is` | 0.5 | 0.6 |
| `passesAppend` | `_` arguments | 0.3 | 0.5 |
| `parenInnerPasses` | `cases` | 91 | 134 |
| `endsOnStep` | `cases` | 2.3 | 14.1 |
| `allTokensWithout` | `ih cases cases` | 11.1 | 42.9 |
| `itemsParsed` | `rewrite repeatedly … then cases` | 2.3 | 26.9 |
| `parenParsed` | `rewrite repeatedly … then cases` | 1.8 | 45.7 |
| `parenParsed` | `rewrite repeatedly` inside the tuple | 1.8 | 2.9 |
| `tupleParsed` | the same | 2.5 | 49.8 |

`cases` used as a finisher costs 10 to 45 ms where the term costs 2. At
the formatter's 0.064 s a theorem [read: SW-4195] that is not ruinous,
but a sweep that put it in a quarter of the theorems would add about a
minute to a 6.5-minute check [estimated].

### 2.4 What the closer needs to know

Counting the 50 theorems by what would finish them [by hand]:

| Step | Theorems (about) | Where the knowledge is | Today |
|---|---|---|---|
| Take `∧`, pairs and `(a && b) = True` apart; build them | 14 | hypotheses in scope | `cases`' fourth closer does it, at `cases`' cost. By hand: `Bool.andLeft`, `andRight`, `andIntro` 4,299 times on 2,814 lines of `tools/fmt/src`; 145 lines are nothing but `let x := Bool.andLeft h` [measured] |
| Apply a hypothesis `A → B` (or `∀ x => A x → B x`) to a fact in scope | 9 | hypotheses in scope | nothing (F5) |
| Apply a named lemma whose conclusion is the goal, premises from scope | 6 | lemmas of the file's own family (`…Parsed`, `spells…`, `passes…`, `…Weaker`) | `stitchwort search` plans exactly this for `?` (`crates/elab/src/closing.rs`), as suggestions, not as a proof term |
| Close each part of an `∧` goal on its own | 6 | — | `cases` and the walk's leaves do; `rewrite repeatedly` doesn't (F1) |
| Rewrite with equations in scope, then compute | 6 | hypotheses in scope | `rewrite` and `rewrite repeatedly`, each equation named |
| Split an `∨` hypothesis | 1 | hypotheses | `match`; `cases` doesn't (F2) |
| Rewrite with std list or Bool lemmas nobody should have to name | 1 (`bracketTrails`) | std | named, 3 rules |
| Congruence closure proper (transitivity and congruence over several equations), or lemmas found by pattern from a library-wide set | 0 | | |

The last two rows are the finding. The knowledge a closer needs here is
**in scope or in the file's own lemma family**, not in a library-wide
set. Slice 1's helper lemmas that SW-4222 noticed (`commaEnd`,
`allAppendB`, the Bool one-liners) have since gone to std by name
(SW-4218), which is why a default set finds nothing left to do.

## 3. Prior art, from the sources

**Lean 4.35.0** [read: installed `src/lean`].

- `grind`: "a tactic inspired by modern SMT solvers", a shared
  "whiteboard" on which congruence closure, E-matching, case analysis
  and arithmetic solvers work (`Init/Grind/Tactics.lean:15-21`). Lemmas
  join by attribute, `@[grind =]`, `@[grind →]`, `@[grind ←]`, each
  choosing a pattern to match (lines 124-137). Its limits are
  configuration: 9 case splits a branch, 5 E-matching rounds, generation
  8, 1,000 instances (`Init/Grind/Config.lean:30-44`). `grind only
  [..]` "does not use theorems tagged with `@[grind]`", and `grind?`
  "reports an equivalent call to `grind only`" (lines 155, 289-293):
  the tool's own answer to proofs that depend on the tagged set.
- `simp_all`: "a stronger version of `simp [*] at *` where the
  hypotheses and target are simplified multiple times until no
  simplification is applicable" (`Init/Tactics.lean:731-733`).
- `t <;> t'` "runs `t` on the main goal and `t'` on each produced goal";
  it is a macro for `focus (t; all_goals t')` (lines 447-456).
  `all_goals` fails if the tactic fails on any goal; `any_goals`
  succeeds if it works on one (lines 353-365).
- In SW-4222's Lean file: `rcases edge with … <;> simp_all [Ended]`
  (`endedWeaker`), `simp [Expr.shaped, …, h.1, h.2.1, openText,
  closeText]` (`parenParsed`), `all_goals grind [GoodItems]` (the comma
  list), `exact ih (by simp_all [tokens]) (by simp_all [tokens])` (rule
  N) [read: `SW-4222-samples/Sample.lean`]. Every one names the
  definitions to unfold; none leans on a library lemma it doesn't name.

**Rocq 9.1.1** [read: installed `lib/rocq-runtime/tactics`, and the
reference manual pages "Programmable proof search" and "Solvers for
logic and equality"].

- `auto` "implements a Prolog-like resolution procedure": the
  assumptions first, then hints by the goal's head symbol, lowest cost
  first, to a depth of 5 (`auto.ml:408`, `default_search_depth`). It
  "either completely solves the goal or leaves it unchanged". With no
  `with` clause it uses the hypotheses and the `core` database only.
- Hint databases are named. The manual: "You are advised not to put
  your own hints in the core database, but use one or more databases
  specific to your development", and of `auto with *`, "highly
  discouraged in finished scripts since it is both slower and less
  robust than explicitly selecting the required databases".
- `eauto` differs in trying hints "which would leave existential
  variables in the goal".
- `info_auto` "shows the tactics it uses to solve the goal".
- `intuition` takes the propositional structure apart and runs a solver
  on what is left; its default solver, `auto with *`, is being changed
  "in a future version … to just auto", with a warning when the
  difference matters. `tauto` "is simply `intuition fail`".
- `congruence` "implements the standard Nelson and Oppen congruence
  closure algorithm … for ground equalities with uninterpreted symbols",
  with constructors' injectivity and disjointness.
- `easy` and `now t` (`t; easy`) are a fixed list of closing steps
  (`theories/Init/Tactics.v:158-183`).
- `t1; t2` runs `t2` on every goal `t1` leaves (SW-4222's Rocq file uses
  it throughout, `destruct edge as …; simpl; intuition`) [read:
  `Sample.v`; the manual's Ltac page not re-read].

**What both say.** Each system has a library-wide default (`@[grind]`,
`@[simp]`, `core`, `auto with *`), and each system's own documentation
steers finished proofs away from it, towards named sets and a recorded
answer (`grind only`, `info_auto`, explicit databases). The parts used
in the 21 ported proofs are the plain ones: facts in scope, named
definitions, and one text over several goals.

## 4. What Stitchwort has

- **Three closers, three lists.** `cases` closes a case by computing, a
  contradiction, taking an equation apart, a hypothesis or a part of
  one (reading `(a && b) = True` as `a ∧ b`), `t`, then `arithmetic` and
  the goal's decision (`crates/elab/src/cases.rs`, head comment). The
  walk closes a leaf by `()`, a hypothesis, computing, a pair of closed
  leaves, `arithmetic`, or a bracket term (`docs/syntax.md`,
  "`byWalking`"). `rewrite repeatedly` closes by computing, a
  contradiction or a hypothesis (simp-revisited, "As built"). None
  applies an implication; only two split an `∧` goal [read].
- **`cases then t`** is already "`t` in every case": Lean's `<;>` after
  a split that `cases` chooses. What it lacks is a way to say what to
  split (F4, F6).
- **Or-patterns and catch-alls** join arms with one text (D3694,
  SW-4236), each alternative checked on its own.
- **`rules` sets**, named and listed in the call; no default set (D3639).
- **`stitchwort search`** finds lemmas whose conclusion matches a `?`
  and fills premises from hypotheses (`closing.rs`), as text to try.
- **`[auto h: P]`** arguments are filled from a hypothesis of exactly
  that type or a decision procedure. The word `auto` is taken.

## 5. The options

Costs are agent hours from like work's actuals: `rewrite repeatedly`
stage 1 took 72 minutes and 97 with review fixes (SW-3602), its stage 2
took 50 (SW-3642), the two-run walk 67 (SW-4240) [read: the board].

| | (a) Default lemma sets for `rewrite repeatedly` (SW-4241) | (b) Congruence closure and the facts in scope (`grind`-like) | (c) `auto`-style search | (d) One text over several arms |
|---|---|---|---|---|
| What it is | std lemmas tagged into sets that apply without being listed, to goal and hypotheses | equalities in scope closed under congruence, lemmas from a tagged set matched by pattern, case splits, arithmetic | from the goal backwards: a fact, or a lemma whose conclusion fits, premises the same way, to a small depth | split what is named, then one proof text in every case |
| Closes in SW-4222's 21 | 0 lines | 23 (197 to 174), none of it needing the closure or the pattern matching | the same 23 if it also takes facts apart; 3 more at walk leaves | 22, in the printer's `…Weaker` group, with (c) |
| Closes in the random 30 | 0 lines (1 theorem shorter in characters) | 13 | 13 | 18, one theorem |
| Cost | 2 to 3 h: an attribute, std's tagging, the index | 10 to 16 h [estimated; nothing built here is close in kind], and tuning after | 3 h with review and pilot: `closing.rs` has the matching, `cases` has the fact handling | 1.5 to 2 h |
| Check-time risk | High: every tagged rule is a candidate at every call. A shared set already cost 4.5 times on `Words.sw` before SW-3654 made set members match as written only, and 2.4 times after (SW-3654, SW-3659) | High and hard to bound: Lean bounds it by five separate limits | Low if bounded: depth 3, facts and listed lemmas only, a fixed count of attempts. Must beat `cases`' 10 to 45 ms (§2.3) | None of its own |
| Brittleness when std changes | Worst: a lemma added to a set can change or break any proof using it. Lean and Rocq both steer away from this (§3) | The same, through the tagged set | None from std: it uses what the proof names. *Less* brittle than today's proofs when a definition changes: `Bool.andLeft (Bool.andRight h)` breaks when a conjunct is added, and a closer that finds the part by its content doesn't | None |
| "The kernel checks what the tool produces" | Fits: a `rewrite` chain | Fits, but the terms are large (chains of transitivity and congruence), and so is the elaborator code that must be right for the tool to be useful | Fits best: the term is the applications a lane writes now, and can be written back into the source | Fits: the arms written out |

**(a) is not worth building now.** It answers a need that SW-4218's
lift to std already met by name. Matt chose named sets over a default
set for `rewrite repeatedly` (D3639), and nothing here argues for
reopening that. I would close SW-4241 as "not now", and keep
SW-3631's selective rollout of `rewrite repeatedly` as it is.

**(b) is more than the proofs ask for.** Every proof I put under (b)
needs only its plain half: facts taken apart, an implication applied, an
equation in scope used. That half is (c) with fact handling. The rest of
`grind` buys nothing in this sample and carries the cost and the risk.

**(c) is the closer to build**, in the form of §6.

**(d) is real but narrow.** `<;>` is 8 uses in SW-4222's Lean file, and
here it is two printer theorems of 37 and 42 lines. It is worth little
without (c), since arms that differ in shape need a text that adapts.

## 6. Recommendation

### Stage 0: use and mend what exists (no decision)

| Lane | What | Model | Estimate |
|---|---|---|---|
| 0a | F1: `rewrite repeatedly` closes an `∧` goal whose parts each close. F2: `cases` splits a hypothesis that is an `∨` before a variable of the goal. F3: find why `cases` takes 43 ms on a closed conjunction. Each with a failing-first example | Opus (tactics, D2506) | 45 min |
| 0b | Proving guide: "Before writing the term" (`cases` as an argument, `ih cases cases`; or-pattern with `rewrite is`; `_` for arguments the goal fixes; `rewrite repeatedly` with hypotheses). Then convert `Syntax/ParseWalk.sw`'s tree facts and `Fmt/JoinProofs.sw`, keeping a conversion only where the proof is shorter and the theorem's check time is within 3 times; report lines and time per file | Sonnet | 60 min |

**Bar for stage 0:** the two files' proof lines fall by 5% or more with
each file's check time within 1.5 times. If check time is the reason
conversions are dropped, that count is the case for stage 1 (a cheap
closer), not against it.

### Stage 1: `byFacts` (the decision)

A proof term, like `cases`. `byFacts` is a working name; `auto` is
taken. `byFacts [lemmas]` names lemmas or `rules` sets to use beside the
facts in scope.

- **Facts.** Every hypothesis in scope, taken apart: `∧` and pairs into
  parts, `(a && b) = True` into its parts, an equation between the same
  constructor into its fields' equations. This is `cases`' fourth
  closer, lifted out.
- **The goal.** `∧`, a pair or `(a && b) = True`: each part on its own.
  `→` or `∀`: introduced. Then, in order: computing; two facts that
  contradict; a fact; a fact or listed lemma whose conclusion fits the
  goal, each of its premises closed the same way, to depth 3;
  `arithmetic` for a `Nat` or `Int` goal.
- **Equations in scope** are used as `cases` uses them now: a variable
  side is replaced. Nothing more; if stage 1's pilot shows goals left
  open for want of congruence, that is the evidence for a later stage.
- **It does not** split data or an `∨` (write `cases then byFacts`),
  rewrite with lemmas (write `rewrite repeatedly [..] then byFacts`),
  unfold to search, or use any lemma the call doesn't name. No
  attribute, no default set.
- **Bounded.** A fixed number of attempts, then an error; never a slow
  success. The order is fixed (nearest fact first, then the list in
  order), so the same source gives the same term.
- **When it fails**, `E-FACTS` shows the part of the goal left open and
  the facts and lemmas whose conclusions came nearest. `byFacts then ?`
  shows it as a goal.
- **What it found** can be written back: `check --expand-facts`, as
  `--expand-walk` and `--expand-repeatedly` do. This is Rocq's
  `info_auto` and Lean's `grind?`, except that the result is the plain
  term, not a narrower call to the search.
- **Shared.** Once the term stands, `cases`, `rewrite repeatedly` and
  the walk's leaves use it as their closer, so that `endedWeaker :=
  cases` and a walk's `[parenParsed]` leaf close without `then`. One
  closer in place of three lists.

No kernel change. The term is applications of hypotheses and named
lemmas, so review is Opus's (it generates kernel terms, D2364).

| Lane | What | Model | Estimate |
|---|---|---|---|
| 1a | `byFacts`, `byFacts [..]`, `then ?`, the error, expand; `docs/syntax.md`, the guide, the proving guide; accept and reject examples. The self-hosted formatter refuses the new word until a slice reaches it | Opus | 90 min |
| 1b | Review of 1a | Opus, paper | 25 min |
| 1c | Pilot: the ten theorems below, then stage 0's two files again; then the shared closer, re-timing `cases` and the walk on files that use them | Sonnet | 60 min |

**Bars**, on the pilot:

| # | Bar |
|---|---|
| 1 | Of the ten theorems this note puts under the facts closer (`endedWeaker`, `signSymbolic`, `parenParsed`, `tupleParsed`, `itemsParsed`, `allTokensWithout`, `alikeParen`, `leftLinkOf`, `signQuietOf`, `givesExpect`), at least seven are shorter with it, and SW-4222's 21 are at 185 lines or fewer (197 after stage 0; §2.1 estimates 174) |
| 2 | Check time of each converted file within 1.5 times stage 0's; a `byFacts` that replaces a `cases` finisher is faster than it |
| 3 | Reject examples (a missing fact, a lemma whose premise isn't in scope, the attempt limit) each show the part left open |
| 4 | Every `byFacts` in the pilot expands to a term that checks |
| 5 | A scripted edit that adds a conjunct to one predicate (`Parsed`, or `within1`) breaks fewer converted proofs than hand proofs |
| 6 | A count, no threshold: places it was tried and left the goal open, by the step that was missing (§2.4's rows) |

**What means "stop".** After 1c, keep stage 0 and go no further if any
of these holds:

- fewer than five of the ten are shorter;
- the pilot files' proof lines fall by less than 3% beyond stage 0;
- check time is over 2 times stage 0's after one tuning lane;
- more than a third of the `byFacts` calls needed their lemma lists
  grown past three names to close (the search isn't finding what a
  reader would call obvious).

### Stage 2: one text over arms (after stage 1's bar)

`cases x then t` (and `cases x, y then t`): split exactly the named
values, as deep as `t` needs to check, and try `t` in each case. It is
`cases then t` with the choice of split taken from `cases` and given to
the proof, which also answers F4. Syntax is Matt's when it comes; the
evidence then will be bar 6's count and the two printer proofs. About
1.5 to 2 hours.

### Not recommended

- **SW-4241** (default sets): close as not now (§5, a).
- **A `grind`** (b): no proof in 50 needs it. Revisit only if bar 6
  shows goals left open for want of congruence closure.
- **A sweep of `Bool.andLeft`/`andRight` to `byFacts`** before the
  pilot's bar 2 is met: 4,299 sites at even 2 ms each is 9 seconds, at
  `cases`' present cost one to three minutes.

## 7. One decision for Matt

**Build the facts closer, `byFacts [lemmas]` (stage 1), after stage 0's
fixes and pilot; no default lemma set and no `grind`-like engine? [rec:
yes]**

- **The problem.** Small proofs end in terms written out by hand: which
  part of which "and" fact, which hypothesis applied to which. Lean and
  Rocq end them with one word. The same 21 theorems are 217 lines here
  and 159 in Lean.
- **The change.** First, fix three gaps in the tools we have and use them
  (20 of the 217 lines go that way, 17 of them measured). Then one new
  proof word that finishes a goal from the facts in scope and the
  lemmas the proof names, and that `cases`, `rewrite repeatedly` and the
  walk share as their finisher. It splits nothing, rewrites nothing,
  and uses no lemma the proof doesn't name. About 5 agent hours for
  both stages.
- **What it should do.** SW-4222's sample at about 174 lines [estimated]
  against Lean's 159; 4 to 10% of proof lines in dispatcher, tree-fact
  and printer files [estimated from 50 theorems]; proofs that no longer
  break when a predicate gains a conjunct. It stops after its pilot if
  fewer than five of ten named proofs get shorter or check time doubles.
- **Also yours, smaller:** the word itself. `byFacts` sits beside
  `byComputing`, `byDecision` and `byWalking`; say if you want another.

## 8. Findings worth tickets

- F1 to F4 and F6 of §2.3, each with its probe in
  `dev/patches/SW-4242-closer-probes.patch`.
- `minusSymbolic` and `bangSymbolic` (`Syntax/ParseWalk.sw`) are unused
  once `signSymbolic` is `| Inl is | Inr is => rewrite is` [measured].
- `passesAppend` checks with `_` for `(Follows kinds)` and the
  continuation [measured]; `joinsAllAppend`'s uses probably do too. A
  small sweep of `Fmt/JoinProofs.sw`.
- The three closers (`cases`, walk leaves, `rewrite repeatedly`) have
  three different lists (§4). Worth one, whatever is decided here.
- SW-4464's recount after W4 should use this note's "today" column as
  its base for kind 3: `parenParsed` and `tupleParsed` are tree facts W4
  doesn't touch.
- The "dispatcher" label for `Settle*Proofs.sw` is wrong for four in ten
  of its theorems (§1); SW-4195's 26% is an upper bound, as it says.

## Sources

- Lean 4.35.0, `src/lean` under the Nix store path of `nixpkgs#lean4`:
  `Init/Grind/Tactics.lean` (lines 14-293), `Init/Grind/Config.lean`
  (lines 30-71), `Init/Tactics.lean` (lines 353-367, 447-456, 731-735).
- Rocq 9.1.1, the Nix store's `rocq-9.1.1`:
  `lib/rocq-runtime/tactics/auto.ml:408`, `auto.mli`,
  `lib/coq/theories/Init/Tactics.v:158-187`, `Init/Tauto.v:99-122`.
- Rocq 9.1 reference manual, fetched 20 Nov 2026 through a summarising
  fetch (quotations are as the fetch returned them):
  rocq-prover.org/doc/V9.1.0/refman/proofs/automatic-tactics/auto.html
  and …/automatic-tactics/logic.html.
- `docs/reviews/SW-4222-samples/Sample.lean`, `Sample.v`.
- Stitchwort: `docs/reviews/SW-4222-lean-rocq-comparison.md`,
  `SW-4464-lean-rocq-standing.md`, `SW-4238-walk-step-review.md`;
  `docs/proposals/simp-revisited.md`, `proof-match-likewise.md`;
  `docs/proving-guide.md` §3; `docs/syntax.md` (`cases`, `byWalking`,
  `rewrite repeatedly`); `crates/elab/src/cases.rs`, `closing.rs`,
  `auto.rs` (head comments); the board entries for SW-3602, SW-3631,
  SW-3642, SW-3654, SW-3655, SW-3659, SW-4219, SW-4240, SW-4241.
