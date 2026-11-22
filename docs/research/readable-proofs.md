# Readable, repairable proofs, for people and agents

*SW-3583, Opus paper lane, 16 November 2026. Research only: no code changed, nothing built
or run. Written against `main` at `a25825f62`.*

Matt's question (16 Nov 2026): what are good ways to write proofs in systems like Stitchwort,
Lean, Idris, Agda and Rocq, particularly now that AI agents write most of them, and how can
proofs be made easy to follow, repair and understand, for humans and agents alike?

Labels, as elsewhere in `docs/research/`:
- **[cited]**: read in the linked source (web sources through a summarising fetch, so wording
  is sometimes paraphrased; quotes in quotation marks are the source's);
- **[checked]**: read or counted in this repo at the place given;
- **[inferred]**: my reasoning.

This note builds on, and doesn't repeat, [agentic-proving.md](agentic-proving.md) (SW-909:
cards C1-C24 on AI provers, cited here as "AP C*n*"), [proof-automation.md](proof-automation.md),
[simp-revisited.md](../proposals/simp-revisited.md) (SW-3522),
[proof-vocabulary.md](../proposals/proof-vocabulary.md) and
[toy-proof-complexity.md](../proposals/toy-proof-complexity.md) (SW-3500). SW-2921's paper on
the Goals panel covers what a goal display should show; this note covers the proof text.

## 1. Summary

1. **What makes a proof readable is that its intermediate states are on the page, or one cheap
   query away.** The proof-engineering survey puts it in one line: for structured proof
   languages, "the key difference for readability is that the intermediate goals are explicit
   in the proof language, so to reconstruct an English proof, the reader does not need to step
   through tactics one-by-one" ([QED at Large §5.1](https://arxiv.org/abs/2003.06458))
   [cited]. That cuts across the usual style split. A proof *term* can hide its state as well
   as a tactic script does: `Eq.trans (Eq.sym starts) (guardedStart first tail …)` says no more
   about what holds in between than `rw [h]; exact foo _ _` [inferred]. So Matt's view holds,
   with the refinement that the dividing line is *stated versus unstated intermediate facts*,
   not terms versus tactics.
2. **AI provers converged on the same shape.** Stepwise tactic search (LeanDojo, Proverbot9001,
   AlphaProof) suits per-step feedback, but the strongest recent systems work with *named
   intermediate statements whose gaps automation or the model fills*: Draft-Sketch-Prove's
   formal sketches (20.9% to 39.3% solved), DeepSeek-Prover-V2's `have … := by sorry` subgoals,
   Seed-Prover's lemma pool, APOLLO's "sorrifier", Thor's hammer calls, CoqPilot's `admit`
   holes, Laurel's helper assertions in Dafny (§3) [cited]. The intermediate statement is the
   unit of search, of repair and of reading.
3. **Repair needs three things**: the error at the first real cause, the goal at the point of
   failure, and a small blast radius (AP C10 Baldur, C11 Goedel-Prover-V2; experts in F* and
   Verus kept 0-4 errors active at a time, [Jain et al. 2025 §5.2.2](https://arxiv.org/abs/2508.02733))
   [cited].
4. **Proofs break where they lean on something unstated**: names the system generated, the
   exact output of flexible automation that a rigid step then consumes, the unfolded form of a
   definition, long lists of lemma names, and argument positions (§4) [cited]. They survive
   change where each step states what it establishes, where automation finishes a goal rather
   than shapes one, and where definitions are hidden behind lemmas.
5. **Stitchwort today** is strong on the tools (holes that keep checking, `goal --at` with
   before and after per step, counterexamples, `audit`, stable error codes, no generated
   hypothesis names) and weaker in the text. Its corpus nests `Eq.trans` 1,858 times against
   190 `calc`s; `rewrite` chains of up to six rules show no state between them; lemmas are
   called with up to nine positional arguments; and the Parse proofs repeat an eight-arm
   skeleton per combinator (§5) [checked].
6. **Recommendations** (§6), in order: a "state, don't chain" rule in the proving guide with a
   lint; `goal --steps` (SW-2781) as the agent's view of a whole proof; "this goal as a lemma"
   output; a one-line proof idea on long theorems; named or `_` arguments for long lemma calls;
   one induction principle per repeated proof skeleton; if `simp` is built, Mathlib's rule
   that flexible automation finishes a goal or is followed by a stated one; and a hammer
   experiment. Hammers (§3.3) are readable only when the solver's answer is turned into the
   prover's own source (Sledgehammer's one-liners, CoqHammer, querysmt); for Stitchwort's
   constructive kernel that means the solver finds the facts and Stitchwort's own closers
   re-prove the goal, with no solver at check time. Four D candidates are in §7.

## 2. The four styles compared

| Style | Systems | State on the page? | Strength | Weakness |
|---|---|---|---|---|
| Tactic script | Rocq/Ltac, SSReflect, HOL, Lean `by` | No: only in the IDE, step by step | Short; search and feedback per step; automation absorbs change | "Tactic soup" (QED at Large §5.1); generated names; breaks when automation output shifts |
| Proof term | Agda, Idris, Lean term mode, Stitchwort | Only where types are written (`let h: T`, ascriptions, `calc`) | One language for programs and proofs; checking is plain type checking; holes show goals | Nested applications hide every intermediate type; positional arguments |
| Declarative | Mizar, Isabelle/Isar, Lean `have`/`show`/`calc`, Agda `≡⟨⟩` chains | Yes, by construction | Reads like mathematics; each step checkable on its own; repair is local | Longer; the author must write each intermediate statement |
| Auto-active | Dafny, F*, Verus, Liquid Haskell | Partly: specs, invariants, `assert`s | The solver fills most steps; asserts are the "have"s | Solver brittleness (Dafny's "verification variability"); failures hard to localise |

Sources: QED at Large §5.1 on proof languages, SSReflect and Isar
([arXiv 2003.06458](https://arxiv.org/abs/2003.06458)); Wenzel's Isar paper, whose aim was a
notion of proof "suitable for human communication, or even just maintenance"
([TPHOLs 1999, LNCS 1690](https://www.doi.org/10.1007/3-540-48256-3_12)); Dafny's
[verification optimisation guide](https://dafny.org/latest/VerificationOptimization/VerificationOptimization)
[cited].

Points from each community that bear on Stitchwort [cited unless marked]:

- **Isabelle/Isar.** Isar is the recommended style for submissions to the Archive of Formal
  Proofs (QED at Large §5.1). The AFP survey found that most lemmas use no structured
  commands at all (proof depth 1) and that deep nesting "is also a potential indication that a
  monolithic proof should be refactored into smaller lemmas"
  ([Blanchette et al., CICM 2015 §2.2](https://www21.in.tum.de/~nipkow/pubs/cicm15.pdf)). AFP
  stays alive because the core developers push every Isabelle change through all entries
  before a release (same paper; AFP release notes).
- **SSReflect.** Every step is one of three kinds, deduction, bookkeeping (naming, moving
  hypotheses) or rewriting, and they are interleaved in "equal proportions" (QED at Large
  §5.1). Names are given explicitly after `=>`, which "reduces the chance of brittleness due
  to reliance of machine-generated variable names" (same). Its style guide: a line that closes
  a goal starts with a terminator (`by`, `exact`), bullets mark subgoals, and proofs are
  structured "in blocks", forward steps, to limit the scope of errors
  ([SSReflect CONTRIBUTING.md](https://sources.debian.org/src/ssreflect/2.5.0-2/CONTRIBUTING.md)).
- **Mathlib.** One tactic per line; side goals behind a focusing dot; `have` on one line when
  its justification is short; `calc` with the relations aligned; and terminal `simp` is not to
  be "squeezed" into the `simp only [...]` that `simp?` suggests, because "a squeezed `simp`
  call refers to many lemmas by name, meaning that it will break when one such lemma gets
  renamed" ([Mathlib style guide](https://mathlib.org/contribute/style.html)). The other half
  is the *flexible linter*: a rigid tactic (`rw`, `exact h`) must not act on the output of a
  flexible one (`simp`), since "the goal after `simp` is subject to change by even a small,
  likely, modification of the `simp` set"
  ([FlexibleLinter docs](https://florisvandoorn.com/LeanCourse25/docs/Mathlib/Tactic/Linter/FlexibleLinter.html)).
  Together: automation may *finish* a goal by itself; when it only *reshapes* one, pin the
  result down.
- **Agda.** PLFA prefers chains of equations: "proofs as chains of equalities are easier to
  follow, and we will stick with the latter when feasible", while `rewrite` is "far more
  compact" and used "sparingly" ([PLFA, Equality](https://plfa.github.io/Equality/)). Holes
  (`{! !}`) show the goal "after simplification" ([PLFA, Induction](https://plfa.github.io/Induction/)).
  Idris's type-driven development is the same hole-first loop [inferred from the same
  practice; not separately cited].
- **Dafny.** Intermediate assertions are "more information than Dafny strictly needs", but
  they make the code more readable and verification less variable; prefer `calc` to long
  chains of `assert`s; scope local facts with `assert P by { … }`; hide definitions with
  `opaque` and `reveal` them where needed; move a run of assertions into a lemma
  ([Dafny verification optimisation](https://dafny.org/latest/VerificationOptimization/VerificationOptimization)).

## 3. What AI-prover work shows

### 3.1 Systems and the style they use

| System | Prover | Unit generated | Feedback | Source |
|---|---|---|---|---|
| Proverbot9001 | Rocq | one tactic, tree search | proof state per step | [arXiv 1907.07794](https://arxiv.org/abs/1907.07794) |
| Tactician / Graph2Tac | Rocq | next tactic (k-NN, online learning) | proof state | [Springer 2023](https://link.springer.com/chapter/10.1007/978-3-031-43369-6_13) |
| LeanDojo / ReProver | Lean | one tactic + retrieved premises | proof state | [arXiv 2306.15626](https://arxiv.org/abs/2306.15626) |
| Lean Copilot | Lean | tactic suggestions, search through Aesop | proof state | [arXiv 2404.12534](https://arxiv.org/abs/2404.12534) |
| AlphaProof | Lean | tactics, RL with tree search | proof state | [Nature 2025](https://www.nature.com/articles/s41586-025-09833-y) |
| Thor | Isabelle | steps, plus "call the hammer here" | proof state | [arXiv 2205.10893](https://arxiv.org/abs/2205.10893) |
| Baldur | Isabelle | whole proof, then repair | error message | AP C10, [arXiv 2303.04910](https://arxiv.org/abs/2303.04910) |
| Draft, Sketch, Prove | Isabelle | informal proof → formal sketch of conjectures → hammer | per conjecture | [arXiv 2210.12283](https://arxiv.org/abs/2210.12283) |
| Kimina-Prover | Lean | whole proof, Lean snippets interleaved in reasoning | compile | [arXiv 2504.11354](https://arxiv.org/abs/2504.11354) |
| DeepSeek-Prover-V2 | Lean | `have … := by sorry` subgoals, then each as a lemma | compile | AP C13 |
| Goedel-Prover-V2 | Lean | whole proof, self-correction | compiler messages; `extract_goal` for the failing subgoal | AP C11 |
| Seed-Prover, Aristotle | Lean | lemma pool; lemmas proved or disproved | compile | AP C14, C15 |
| APOLLO | Lean | failing blocks replaced by `sorry`, automation on each, the rest back to the model | compile | proof-automation.md C25 |
| CoqPilot | Rocq | fills `admit` holes; repairs from errors | per hole | [arXiv 2410.19605](https://arxiv.org/abs/2410.19605) |
| Laurel | Dafny | one helper `assert`, placed from the error | verifier | [arXiv 2405.16792](https://arxiv.org/abs/2405.16792) |
| AutoVerus, VeruSAGE | Verus | annotations, proof blocks | verifier | AP C19, C20 |
| FStarDataSet | F* | whole definitions, type-directed | checker | [Chakraborty et al., ICSE 2025](https://www.microsoft.com/en-us/research/publication/towards-neural-synthesis-for-smt-assisted-proof-oriented-programming/) |
| mini-Lean-agent | Lean | whole file, bash only | compile | AP C1 |

### 3.2 What it says

1. **Stepwise versus whole-proof is a tooling choice more than a style verdict.** Search per
   tactic needs a proof state after every step, which is why most of this work targets
   Lean and Rocq tactics, where that state is the interface (LeanDojo, Proverbot9001,
   AlphaProof) [cited]. Whole-proof generation with repair loops matched or overtook it from
   2025 (Kimina 80.7% on miniF2F at pass@8192; Goedel-Prover-V2; mini-Lean-agent beat a
   Lean-specific harness, AP C1) [cited]. Neither line tells us that *tactic text* is the
   better artifact; they tell us that a cheap, exact state after each step is what search
   needs [inferred].
2. **Readable intermediate statements help models directly.** The cleanest evidence is
   Draft-Sketch-Prove: turning an informal proof into a formal sketch of intermediate
   conjectures, each left for the hammer, nearly doubled the solve rate (20.9% to 39.3%), and
   the sketches "follow the same reasoning steps as the informal proofs"
   ([arXiv 2210.12283](https://arxiv.org/abs/2210.12283)) [cited]. DeepSeek-Prover-V2 and
   Seed-Prover build the same structure on purpose (AP C13, C14); Kimina keeps most of the
   Lean snippets it writes while reasoning in its final proof [cited]. Goedel-Prover-V2's
   repair isolates "the unsolved subgoal" as a standalone statement (AP C11) [cited].
3. **Repair is driven by messages and locality.** Baldur's repair model beat resampling only
   when given the error message; adding the surrounding file raised proofs from 40.7% to
   47.5%, the model "readily copies and adapts proofs" nearby (AP C10) [cited]. Laurel finds
   *where* a missing assertion goes from the error before asking the model *what* it is, and
   then gets over half of them in a few tries ([arXiv 2405.16792](https://arxiv.org/abs/2405.16792))
   [cited]. In the F*/Verus expert study, the best participant kept 0-4 errors active by
   "deferring verification on segments of the code and tackling the proof section by
   section", and the authors ask for tools that turn dense verifier output into explanations
   and "breakpoint-like toggles to ignore specific lines" ([arXiv 2508.02733 §5.2.2, §7.1.3](https://arxiv.org/abs/2508.02733))
   [cited; eight participants, four tasks].
4. **Automation's place is the leaf, not the trunk.** Thor learns *when* to call the hammer
   (39% to 57% on PISA); APOLLO runs built-in automation on every `sorry` before the model sees
   it; Lean Copilot adds model tactics to Aesop's search [cited]. The model writes the
   structure, automation closes the small goals [inferred from these].
5. **Agents game an opaque checker.** Covered in AP §1 point 3 (VeruSAGE, misformalised
   statements); Stitchwort's answer is `audit` (D2040) [cited there].

### 3.3 Hammers: external provers whose proofs the kernel checks

A hammer has three parts: a *premise selector* picks a few hundred relevant facts, a
*translation* turns the goal and facts into the solver's logic (usually first-order), and a
*reconstruction* turns the solver's answer into something the kernel accepts
([Blanchette, Kaliszyk, Paulson, Urban, *Hammering towards QED*, JFR 9(1) 2016, §1](https://wwwbroy.in.tum.de/~blanchet/h4qed.pdf))
[cited]. The same survey names three ways to reconstruct (§4) [cited]:

- **(1) replay** the solver's proof inference by inference (Isabelle's `metis` and `smt`,
  HOL(y)Hammer's PRocH), which needs the solver, or stored raw proofs, at every check;
- **(2) check a certificate with a verified checker**, by reflection (SMTCoq);
- **(3) translate to source**: the found proof becomes proof text, at the extreme a one-liner
  naming only the facts the solver used. "Success rates can be arbitrarily high with any
  approach"; textual proofs with `metis` reached reconstruction rates "above 99%".

| System | Finds proofs with | Reconstruction | Success | What the user keeps |
|---|---|---|---|---|
| Sledgehammer (Isabelle) | E, Vampire, Zipperposition, SPASS, cvc5/veriT/Z3, in parallel, over hundreds of selected facts | (3), usually a `metis`/`smt` one-liner naming the facts; optionally a structured Isar proof, turned from refutation into a direct proof and compressed ([Blanchette et al., JAR 2016](https://wwwbroy.in.tum.de/~blanchet/isar2.pdf)) | "comparable" to the 40-47% of whole libraries reached elsewhere (JFR 2016); in a 2025 run, 70.0% of its suggestions were one-liners with instantiated facts (proof-automation.md C21) | One line; readable only as "these facts suffice". Isar output is "semi-intelligible", the paper's own word |
| HOL(y)Hammer (HOL Light) | E, Vampire, Z3, learned premise selection | (1) PRocH replay | 47% of HOL Light/Flyspeck (JFR 2016) | a tactic call |
| CoqHammer (Rocq) | E, Vampire, Z3 (classical) | Uses the ATP's proof "merely as hints": the lemmas it needed and the definitions it unfolded, then re-proves intuitionistically by its own search; "if the ATP proof is inherently classical then proof reconstruction will fail" | 40.8% of Rocq's standard library in about 40 s on 8 CPUs; 85.2% of ATP proofs reconstructed ([Czajka, Kaliszyk, JAR 2018](https://pmc.ncbi.nlm.nih.gov/articles/PMC6044314)) | a solver-free tactic, reproducible across machines |
| SMTCoq (Rocq) | veriT, CVC4, ZChaff | (2) a checker for their certificates, proved correct in Rocq ([Ekici et al., CAV 2017](https://theory.stanford.edu/~barrett/pubs/EMT+17-abstract.html)) | not compared here | a tactic; the certificate is not readable |
| lean-smt (Lean) | cvc5 | (1) replays about 200 of cvc5's 662 rules; 71% of 21,595 SMT-LIB proofs; 98% of Sledgehammer-derived proofs in under a second | proof-automation.md C17 | a tactic call |
| Lean-auto + Duper | ATPs and SMT via monomorphisation into HOL | Duper, a proof-producing superposition prover in Lean, rebuilds; other ATPs are trusted with a warning | 36.6% of its benchmark | proof-automation.md C15, C16 |
| querysmt (Lean) | cvc5 | (3): extracts the theory facts cvc5 derived as *hints*, writes "a self-contained proof script" in the source, `grind` proves the hints and Duper the goal, so "the proof does not depend on calling an SMT solver anymore" | 0.7-0.8 hints per script | proof-automation.md C18 |
| LeanHammer | neural premise selection + Lean-auto + Zipperposition + Duper inside Aesop | Duper | 33.3% to 37.3% of test theorems | proof-automation.md C19 |
| crush (Lean) | SMT with defunctionalisation | unsat-core-guided reconstruction with `omega`/`grind`, or Alethe replay | 91.9% reconstructed vs `grind` 85.0% on 754 VCs | proof-automation.md C20 |

What follows [inferred unless marked]:
- **Readability comes only from approach (3)**, and only when the reconstruction is in the
  language people already read: a fact list for a known procedure (CoqHammer, `metis`
  one-liners), a hint script (querysmt), or Isar steps. Replay and certificates keep the
  solver's reasoning out of sight, and (1) keeps the solver in the build.
- **Stability favours source**: querysmt's motivation is that SMT solvers "are notoriously
  unstable" [cited, C18]; CoqHammer's output has no time limits and needs no solver [cited].
  The Hammering survey adds that `metis` one-liners re-search on every check and are
  "vulnerable to small changes in the formalization" [cited, §4].
- **A constructive kernel limits the solver to hints.** Stitchwort has no excluded middle,
  no `propext` and no user axioms (agentic-proving.md §1). That is CoqHammer's situation: a
  classical solver can say *which facts and unfoldings* suffice, and the proof must be found
  again by Stitchwort's own procedures. It works where the atoms are decidable, which most
  AoC and std goals over `Nat`, `Int`, `Bool`, `List` and finite types are.
- **Premise selection is the part that pays alone.** "Looking for lemmas in a huge library is
  a time-consuming chore", and an advisor is valuable "when the ATP and translation methods are
  still weak" [cited, JFR 2016 §1]. proof-automation.md §5.4 found Stitchwort's failures were
  "about facts in scope, not about large lemma libraries" in October; std has since reached
  3,255 theorems [checked], so that is worth re-measuring.

So a Stitchwort hammer would be: `stitchwort prove --at FILE:LINE` (or the editor action on a
`?`) translates the goal, the hypotheses in scope and the top-k lemmas from `search` into
SMT-LIB, asks cvc5 or Z3 for an unsat core, maps the core back to Stitchwort names, and then
tries Stitchwort's own closers with exactly those facts: `omega [core]`, `cases in core`, a
`rewrite` chain, a `calc`, or `simp [core]` if built. What it writes into the file is that
source, which the kernel checks as usual; nothing calls a solver at check time, and nothing
enters the trusted base. Its output reads like any proof in the file, and a failed attempt
still yields the useful part: "these four lemmas suffice". This is approach (3) in CoqHammer's
and querysmt's form, and it puts automation at the leaves (§3.2 point 4) [inferred].

**For Stitchwort** [inferred]: `?` plus typed `let` is already DSP's sketch and
DeepSeek-Prover-V2's `have … sorry`; `cases`, `omega`, `byDecision` and a future `simp` are the
hammer at the leaves; `goal --at` is the per-step state. What is missing is mostly on the text
side: the sketch structure is used less than nested applications, and the agent can't yet ask
for the whole proof's states at once (§5).

## 4. What makes proofs repairable

### 4.1 What makes them brittle [cited]

- **Generated names.** Small changes to a statement change the names Rocq's `intros` picks;
  proofs that mention them break (QED at Large §6.2.3, §7.2). Answers: always name
  (Company-Coq), or "structural tactics" that never mention names (Woos et al., *Planning for
  Change*, CPP 2016, via QED at Large §6.2).
- **Rigid steps on flexible output.** Mathlib's flexible linter, above; and in the Lean 3 to
  4 port, `simp`'s lemma order changed with the new indexing, so proofs that relied on which
  lemma fired first broke, fixed by removing the lemma (`simp [-bad]`) or by moving
  `@[simp]` onto equation lemmas ([Zulip: simp lemma priorities](https://leanprover-community.github.io/archive/stream/287929-mathlib4/topic/Difference.20in.20simp.20lemma.20priorities.3F.html);
  [lean4#1937](https://github.com/leanprover/lean4/issues/1937)).
- **Long lemma lists.** A squeezed `simp only [...]` names many lemmas and "will break when one
  such lemma gets renamed" (Mathlib style guide). Mathport needed `#align` for every renamed
  declaration ([mathport](https://reservoir.lean-lang.org/@leanprover-community/mathport)).
- **Exposed definitions.** "Even a minor change to a single theorem or definition can break
  many dependent proofs" (QED at Large §6.2). Dafny's answer is `opaque` plus `reveal`; *Planning
  for Change* recommends information hiding so that only interface changes propagate.
- **Solver variability.** A Dafny proof "successfully verifies one time but fails or times
  out after a small change" (Dafny guide, Overview).

### 4.2 What makes them robust [cited unless marked]

- **Automation that absorbs change within a fragment**: a proof ending in `omega` survives any
  goal change that stays in linear arithmetic (QED at Large §6.2, on Rocq's `omega` and
  Isabelle's `presburger`).
- **Custom induction principles** that capture a repeated proof pattern (*Planning for Change*,
  via QED at Large §6.2), and program-specific automation that "localizes the burden of change
  to the automation itself" (CPDT, same section).
- **Stated intermediate facts and lemmas**: Dafny's guide (helper assertions, `calc`, proofs in
  lemmas); SSReflect's forward blocks "to limit the scope of errors"; AFP's advice to refactor
  deep proofs into lemmas.
- **Layered specifications**: seL4's abstract and executable specs let proofs evolve with the
  implementation for over eight years (QED at Large §6.2).
- **A maintainer who repairs downstream** (AFP's model; mathlib's continuous integration) and,
  for large changes, tools: Ringer et al.'s PUMPKIN Pi repairs proofs across type
  equivalences ([PLDI 2021](https://arxiv.org/abs/2010.00774)); REPLica found rewriting proofs
  "ubiquitous" during development ([CPP 2020](https://popl20.sigplan.org/details/CPP-2020-papers/13/REPLICA-REPL-Instrumentation-for-Coq-Analysis)).

The tension [inferred]: automation makes proofs robust and opaque at once. The resolution in
every community above is the same: let automation close goals, and make the author state any
goal that later steps depend on.

## 5. Stitchwort today: a scorecard

Counts are over `.sw` files with `grep` [checked]:

| | std | aoc | rogue | toyfmt |
|---|---|---|---|---|
| `theorem`s | 3,255 | 2,869 | 174 | 1,049 |
| `rewrite` | 1,604 | 2,551 | 74 | 790 |
| `calc` | 66 | 124 | 0 | 0 |
| `Eq.trans` | 1,188 | 531 | 5 | 134 |
| typed `let h: T :=` (the `have`) | 492 | 626 | 33 | 163 |

| Criterion | Today | Grade |
|---|---|---|
| Holes keep checking and print goals | `?` is an assumption; `check` and `goal` list goals and what relies on them (syntax.md "Goals, `?`") [checked] | Strong |
| State at any point, one query away | `goal --at` gives before, rule and after for each `rewrite` rule, arm and `calc` line (syntax.md "The goal at a point") [checked] | Strong for one point; no whole-proof view yet (SW-2781 `--steps`, backlog) |
| Goals as written | Goals keep calls, with "computes to" when different (D3522) [checked] | Strong; matches what the reader wrote |
| No generated hypothesis names | Pattern variables, `match e:` and `if h:` are named by the author; `cases` uses the goal's binder names [checked] | Strong: avoids the classic Rocq breakage |
| Errors to first cause, stable codes | E-codes; counterexample notes on false statements [checked] | Strong (AP §5 lists the remaining misnamed-cause cases) |
| Statement integrity | `audit`, no user axioms, `?` can't be smuggled (D2040) [checked] | Strong |
| Intermediate facts on the page | 1,314 typed `let`s but 1,858 `Eq.trans` and 190 `calc`; e.g. `Eq.trans (Eq.sym starts) (guardedStart first tail (apartOf …) (noCommentOf …))` (tools/toyfmt/src/Toy/Fmt/LexTextProofs.sw:270, deleted 22 Nov 2026, D3715; in git history before then) [checked] | Weak: the term style hides as much as a tactic script |
| `rewrite` chains | `seatIdSpec` runs four nested `rewrite … in` blocks, nine rules, with no stated state between (aoc/src/Aoc/Year2020/Day05/Proofs/Seat.sw:41-55) [checked] | Mixed: compact, and `goal --at` recovers each step, but the page shows none |
| Where `rewrite` matched | Two searches (as written, then as computed), first instance fixes open arguments (syntax.md "`rewrite`") [checked] | Mixed: a rewrite that silently matched inside a definition is hard to repair; the hover of SW-3563 would help |
| Argument positions | `Parse.runFromThenOk2Tree (() => q …) (later …) (s.next passes).snd j k w (Eq.trans …)`, nine positional arguments (crates/elab/src/std/Parse/Reads.sw:246-254); named arguments exist (D2367) but aren't used in proofs [checked] | Weak: brittle to parameter reordering and opaque to the reader |
| Repeated skeletons | Each `Parse.runFrom…Tree` theorem repeats the same eight arms (`span`, `next`, `literal`, `mark`, `reset`, `note`, `stop`, `fatal`), Reads.sw:180-330 [checked] | Weak: a fix is made N times; *Planning for Change*'s custom induction principle is the cure |
| Automation at the leaves | `omega`, `ring`, `cases`, `byDecision`, `Finite.check`; rewrite premises discharged by `omega` [checked] | Good; no simplifier yet (simp-revisited.md) |
| Proof ideas in words | Proving guide §2.7: a theorem's doc only for which spec part it covers or why a hypothesis is needed; "Don't narrate the steps" [checked] | Mixed: right about narration, but leaves long proofs with no sketch; Day05's file doc (Seat.sw:1-3) shows how much one sentence adds |

## 6. Recommendations, ranked

Ranked by expected effect on agents' repair success and readers' understanding, against cost.
Effects are estimates unless marked.

**R1. State, don't chain (proving guide rule plus a lint).**
*Problem:* nested `Eq.trans`/`Eq.sym` and long `rewrite … in` nests hide every intermediate
fact; 1,858 `Eq.trans` against 190 `calc` [checked]. A repairing agent must query `goal --at`
point by point to rebuild what a `calc` would show.
*Change:* a rule in docs/proving-guide.md §2: a chain of two or more equalities is a `calc`; a
`rewrite` nest of more than about three rules, or one whose result a later step depends on,
passes through a typed `let` (or an ascription) that states the fact reached. A warning (say
`W-PROOF-CHAIN`) on `Eq.trans` nested two deep, suggesting `calc`. Existing proofs move over
when they are next touched, not in a sweep.
*Effect:* the state is on the page where it matters (QED at Large's readability criterion;
PLFA's preference; Dafny's "less variable"). Repairs stay local, since a broken step is
bracketed by stated facts. Estimate: a few percent longer proofs, fewer `goal --at` round trips
per repair.

**R2. The whole proof's states in one query: `goal --steps` (SW-2781).**
*Problem:* `goal --at` answers one point; an agent repairing a proof with nine rewrites makes
nine calls, each a full check of the file [checked: syntax.md says each call takes about as long
as `check`].
*Change:* bring SW-2781 forward: `stitchwort goal --steps FILE:DECL` prints every step's before,
rule and after (JSON too), from the record stage 3 already keeps. The same data feeds SW-3563's
hover for `rewrite repeatedly`.
*Effect:* the "one cheap query away" half of the principle, for a whole declaration in one
check. This is the stepwise feedback that tactic-search systems rely on, without changing the
proof text.

**R3. "This goal as a lemma" output.**
*Problem:* the move both Goedel-Prover-V2 (`extract_goal`) and DeepSeek-Prover-V2 make, a
failing subgoal turned into a standalone lemma, is done by hand here [cited AP C11, C13]; no
ticket found [checked: board search].
*Change:* `stitchwort goal --at … --as-lemma` (and in the editor, a code action) prints the goal
as a `theorem name ∀ (…in-scope names…): goal := ?` declaration that pastes back, with the call
to put in its place.
*Effect:* the standard repair and decomposition step becomes one command. It also produces
the small lemmas the proving guide already recommends (§2.3).

**R4. A one-line proof idea on long theorems.** (D candidate D-a)
*Problem:* the guide says a theorem's statement is usually its doc and not to narrate steps.
That is right for short proofs, but a 40-line proof carries no sketch, and DSP's evidence is
that an informal outline is what lets a model (or a person) follow and redo the formal one
[cited].
*Change:* a theorem whose proof is longer than about 15 lines gets a `--|` doc ending with one
or two sentences of proof idea: the induction, the key lemma, the invariant ("by induction on
the bits; each letter halves the region, and the region's first row gains the bit's value").
Still no step narration.
*Effect:* a reader or agent knows the plan before the detail; a repair can check the plan
still holds. Cost: one sentence per long theorem.

**R5. Name or `_` long lemma arguments.**
*Problem:* lemma calls with six to nine positional arguments, many of them determined by
unification [checked, Reads.sw]. Reordering a lemma's parameters breaks every caller with a
type error far from the cause; a reader can't tell which argument is which.
*Change:* proving-guide rule extending D2367 to proofs: an argument that unification fixes is
`_` (or left implicit in the lemma's statement); a lemma call with more than about four
remaining explicit arguments names them, `(tree := later …) (rest := k)`.
*Effect:* shorter, self-describing calls; parameter changes fail at the name.

**R6. One induction principle per repeated skeleton.**
*Problem:* the `Parse.runFrom…Tree` theorems repeat the same eight-arm walk (Reads.sw); a
change to the `Parse` ability means N identical edits [checked].
*Change:* a ticket to state the walk once, as a lemma over a motive (the custom induction
principle *Planning for Change* recommends), and derive each theorem from it. Look for the same
pattern in toyfmt (toy-proof-complexity.md's "same walk done three times").
*Effect:* the change lands in one place. Size: not measured; toy-proof-complexity.md puts
repeated walks at part of its 20-30% "approach" share [cited there].

**R7. If `simp` is built: flexible automation finishes, or the next step states the goal.**
*Problem:* Mathlib's two rules (don't squeeze terminal `simp`; no rigid step on flexible
output) exist because the alternative broke proofs in practice, including the Lean 3 to 4 port
[cited].
*Change:* for `simp [rules]` and `rewrite repeatedly`: a terminal use is fine; a non-terminal
one must be followed by a stated fact (typed `let`, ascription, `calc` line), and the checker
warns otherwise. simp-revisited.md's named rule sets (its Q2) already avoid the default-set
problem; this covers the other half.
*Effect:* rule-set changes break proofs at the stated fact, with a goal to compare, not three
steps later.

**R8. A checked `show` step.** (D candidate D-b)
*Problem:* to state the goal at a point today you write a typed `let` whose body is the rest of
the proof, or an ascription after the term; neither reads as "now we must show P" [checked:
syntax.md has no `show`]. Lean's `show` and Isar's `show` are the declarative backbone.
*Change:* `show P from t` (or `show P` as a block line before the rest), checked to be the goal
up to computation, changing nothing else. It is sugar over ascription; no kernel change.
*Effect:* long proofs read as a sequence of goals; an agent can assert the state it expects
and get an error at the first divergence. Small: an elaborator and parser change.

**R9. A reconstructing hammer, measured first.** (D candidate D-c)
*Problem:* agents spend their attempts finding *which* facts close a goal (AP C12's top
failure kinds are "linarith failed" and "unknown identifier") [cited]; Stitchwort's closers
take facts but don't find them beyond what is in scope [checked: proving guide §3].
*Change:* stage 0, an experiment off the product: a script that sends the open `?` goals of a
sample of lanes to cvc5 with the in-scope facts plus the top 20 `search` hits, takes the unsat
core, and tries `omega [core]` / `cases in core` / `rewrite` on it; count goals closed that the
lane's agent had needed more than one attempt for. Stage 1 only if it clears a bar Matt sets:
`stitchwort prove --at`, writing Stitchwort source (§3.3), with the solver an optional tool,
never needed to check.
*Effect:* estimated, not measured: a fact-finder for the leaves, with proofs that read like
the rest of the file and no new trust. CoqHammer's 40.8% on Rocq's library and Thor's 39% to
57% bound what is possible; Stitchwort's smaller library and constructive logic make the
number lower [inferred].

**R10. Measure repairs.** Count, from lane transcripts, which E-codes were fixed on the next
attempt (AP C12's method, already T6 in agentic-proving.md), and add a column for whether the
failing step was bracketed by stated facts. This tests R1 with our own data before a sweep.

What the evidence does not support [inferred]:
- **A tactic language.** Nothing in §3 shows that tactic *text* helps models; it shows that
  per-step *state* helps search. R2 gives that state without a second proof language.
- **Reopening D2041** (CLI with JSON, no REPL or MCP server). The 2025-26 results still favour
  a fast check plus scratch files (AP C1, C8); R2 is a CLI output.

## 7. D candidates for Matt

Each would change user-visible language or reopen a writing rule, so they are Matt's. The
orchestrator numbers them.

**D-a. Long theorems carry a one-line proof idea in their doc (R4)?**
*Problem:* proofs over about 15 lines have no plan in words; DSP shows a sketch is what lets a
model follow and redo a formal proof (20.9% to 39.3%) [cited].
*Change:* amend the proving guide's §2.7 and syntax.md's "What to write": the doc of such a
theorem ends with its proof idea, one or two sentences; narration of steps stays banned. This
narrows SW-1099's "comment sparingly" for proofs only.
*What it should do:* readers and repairing agents see the plan first [estimated, not measured].
**[rec: yes]**

**D-b. Add a checked `show P from t` (R8)?**
*Problem:* there is no direct way to say "the goal here is P"; typed `let`s and trailing
ascriptions do it indirectly.
*Change:* sugar over ascription, checked against the goal up to computation; guide and
syntax.md updated; no kernel change.
*What it should do:* proofs read as stated goals; mismatches are reported where the author's
expectation and the checker part. **[rec: yes, after R1's rule has run for a week, so its
use is measured against typed `let`]**

**D-c. Run a hammer experiment (R9, stage 0), on the understanding that any hammer writes
Stitchwort source and never calls a solver at check time?**
*Problem:* agents spend attempts finding which facts close a goal; Stitchwort's automation
only uses facts in scope. External solvers find such facts well (Sledgehammer, CoqHammer
40.8% of Rocq's library) [cited].
*Change:* a measured experiment with cvc5 on real lane goals (§3.3); a product command only if
it clears a bar. The design rule, fixed up front: the solver's answer is a hint, the file gets
Stitchwort proof text, the kernel checks it, the trusted base is unchanged. This reopens
proof-automation.md §5.4's "not worth their translation and reconstruction layers" (a
recommendation, not a D decision), on the grounds that std has grown and that approach (3)
needs only a thin translation, no reconstruction library.
*What it should do:* tell us, with numbers, whether a fact-finder pays here before any solver
joins the toolchain. **[rec: yes to stage 0; no product until measured]**

R7's flexible rule (a non-terminal `simp` or `rewrite repeatedly` is followed by a stated fact)
belongs inside simp-revisited.md's Q1 if that is decided yes; it needs no separate question.

**D-d. Make "state, don't chain" a rule with a warning (R1)?**
*Problem:* 1,858 `Eq.trans` against 190 `calc` [checked]; the term style hides the state.
*Change:* the proving-guide rule, plus a warning on two-deep `Eq.trans` nesting suggesting
`calc`; no sweep, proofs converted when touched. (If D(e) of proof-vocabulary.md renames
`Eq.trans` to `chain`, the rule and warning follow the new name.)
*What it should do:* intermediate facts on the page where chains are long; local repairs
[estimated]. **[rec: yes]**

## 8. Findings worth tickets

1. `goal --at … --as-lemma` (R3): print a goal as a pasteable lemma. Small.
2. Bring SW-2781 (`goal --steps`) forward; it is the agent-facing half of R2.
3. Generic walk for `Parse.runFrom…Tree` theorems (R6), in std's Parse.
4. Proving-guide edits for R1 and R5 (rule text only), once D-d is decided.
5. Repair metrics from lane transcripts (R10; agentic-proving.md T6).
6. Hammer stage 0 (R9), if D-c is yes: a scratch-script experiment, cvc5 on a sample of lane
   goals, measured against the agents' attempts.

## Sources

Web (fetched 16 Nov 2026):
- Ringer, Palmskog, Sergey, Gligoric, Tatlock. *QED at Large*. FnT PL 5(2-3), 2019.
  [arXiv 2003.06458](https://arxiv.org/abs/2003.06458) (read §5.1, §6.2, §7.2 from the PDF).
- Wenzel. *Isar — a generic interpretative approach to readable formal proof documents*.
  TPHOLs 1999. [doi](https://www.doi.org/10.1007/3-540-48256-3_12) (abstract only).
- Blanchette, Haslbeck, Matichuk, Nipkow. *Mining the Archive of Formal Proofs*. CICM 2015.
  [PDF](https://www21.in.tum.de/~nipkow/pubs/cicm15.pdf) (read §2).
- Mathlib [style guide](https://mathlib.org/contribute/style.html);
  [flexible linter](https://florisvandoorn.com/LeanCourse25/docs/Mathlib/Tactic/Linter/FlexibleLinter.html);
  port: [mathport](https://reservoir.lean-lang.org/@leanprover-community/mathport),
  [Zulip on simp priorities](https://leanprover-community.github.io/archive/stream/287929-mathlib4/topic/Difference.20in.20simp.20lemma.20priorities.3F.html),
  [lean4#1937](https://github.com/leanprover/lean4/issues/1937) (through search summaries).
- SSReflect [CONTRIBUTING.md](https://sources.debian.org/src/ssreflect/2.5.0-2/CONTRIBUTING.md)
  (through a search summary).
- Wadler, Kokke, Siek. PLFA, [Equality](https://plfa.github.io/Equality/) and
  [Induction](https://plfa.github.io/Induction/).
- Dafny, [Verification optimisation](https://dafny.org/latest/VerificationOptimization/VerificationOptimization).
- Jain, Barke, Ebner, Misu, Lu, Fakhoury. *What's in a Proof?* [arXiv 2508.02733](https://arxiv.org/abs/2508.02733).
- Jiang et al. *Draft, Sketch, and Prove*. ICLR 2023. [arXiv 2210.12283](https://arxiv.org/abs/2210.12283) (abstract).
- Jiang et al. *Thor*. NeurIPS 2022. [arXiv 2205.10893](https://arxiv.org/abs/2205.10893) (abstract).
- Yang et al. *LeanDojo*. NeurIPS 2023. [arXiv 2306.15626](https://arxiv.org/abs/2306.15626) (abstract).
- Song, Yang, Anandkumar. *Lean Copilot*. [arXiv 2404.12534](https://arxiv.org/abs/2404.12534) (abstract).
- Hubert et al. *AlphaProof*. Nature 2025. [s41586-025-09833-y](https://www.nature.com/articles/s41586-025-09833-y) (abstract, through search).
- Wang et al. *Kimina-Prover Preview*. [arXiv 2504.11354](https://arxiv.org/abs/2504.11354) (abstract).
- Sanchez-Stern et al. *Proverbot9001*. [arXiv 1907.07794](https://arxiv.org/abs/1907.07794);
  Tactician/Graph2Tac [Springer](https://link.springer.com/chapter/10.1007/978-3-031-43369-6_13) (abstracts).
- Kozyrev et al. *CoqPilot*. ASE 2024. [arXiv 2410.19605](https://arxiv.org/abs/2410.19605) (abstract).
- Mugnier et al. *Laurel*. [arXiv 2405.16792](https://arxiv.org/abs/2405.16792) (abstract).
- Chakraborty et al. *Towards Neural Synthesis for SMT-Assisted Proof-Oriented Programming*.
  ICSE 2025. [MSR page](https://www.microsoft.com/en-us/research/publication/towards-neural-synthesis-for-smt-assisted-proof-oriented-programming/) (abstract).
- Ringer et al. *Proof Repair across Type Equivalences*. PLDI 2021. [arXiv 2010.00774](https://arxiv.org/abs/2010.00774);
  *REPLica*, CPP 2020, [page](https://popl20.sigplan.org/details/CPP-2020-papers/13/REPLICA-REPL-Instrumentation-for-Coq-Analysis) (abstracts).

Hammers (fetched 16 Nov 2026):
- Blanchette, Kaliszyk, Paulson, Urban. *Hammering towards QED*. JFR 9(1), 2016.
  [PDF](https://wwwbroy.in.tum.de/~blanchet/h4qed.pdf) (read §1, §4).
- Blanchette, Böhme, Fleury, Smolka, Steckermeier. *Semi-intelligible Isar Proofs from
  Machine-Generated Proofs*. JAR 2016. [PDF](https://wwwbroy.in.tum.de/~blanchet/isar2.pdf)
  (abstract, §1).
- Czajka, Kaliszyk. *Hammer for Coq*. JAR 2018. [PMC](https://pmc.ncbi.nlm.nih.gov/articles/PMC6044314)
  (reconstruction and evaluation sections, through a summarising fetch).
- Ekici et al. *SMTCoq*. CAV 2017. [abstract](https://theory.stanford.edu/~barrett/pubs/EMT+17-abstract.html).
- Lean hammers (lean-smt, Lean-auto, Duper, querysmt, LeanHammer, crush) through
  proof-automation.md C15-C20, read in full there.

Through [agentic-proving.md](agentic-proving.md): Baldur (C10), Goedel-Prover-V2 (C11),
Compile to Compress (C12), DeepSeek-Prover-V2 (C13), Seed-Prover (C14), Aristotle (C15),
AutoVerus (C19), VeruSAGE (C20), mini-Lean-agent (C1), Ax-Prover (C8); through
[proof-automation.md](proof-automation.md): APOLLO (C25).

Not reached: Woos et al., *Planning for Change* (CPP 2016), cited only through QED at Large;
Ringer's thesis; math-comp's own style guide; Idris documentation (the Idris point in §2 is
inferred).
