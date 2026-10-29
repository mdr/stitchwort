# Literature trawl: proof automation

*SW-894, cluster 4. Trawled 29 October 2026 against `main` at `fd34ebcd`. Research only: no
code changed. Window: 2022 onwards (D1831); older work appears only where in-window work or a
system we compare with relies on it, marked **classic**.*

Labels: **[cited]** read in the linked source (fetched 29 Oct 2026); **[checked]** read in
Stitchwort's code or docs at the place given; **[inferred]** my reasoning; **[unverified]** from
an abstract, a listing or a search summary only.

This cluster starts from more home work than the others. [proof-automation.md](../proposals/proof-automation.md)
(SW-374) already surveyed Lean's `simp`, Mathlib's `ring`, Rocq's `ring`/`lia`, Isabelle's
simplifier, Agda's reflective solvers and F\*'s SMT route, and Stitchwort built `rewrite` under
binders and `ring` from it; [simp.md](../proposals/simp.md) built `cases`;
[counterexample-search.md](../proposals/counterexample-search.md) built the counterexample search.
This file doesn't repeat those surveys. It looks for what is new since, or what they didn't
cover: congruence closure and e-graphs (Lean's `grind`), functional induction, automation that
writes back its explicit form, proof stability, decision procedures with certificates,
generators for hypotheses, lemma discovery, and designing for AI provers.

## Contents

1. [Summary](#1-summary)
2. [Method and queries](#2-method-and-queries)
3. [Screened list](#3-screened-list)
4. [Cards](#4-cards)
5. [Deep reads](#5-deep-reads)
6. [Steal next](#6-steal-next)
7. [Proposed tickets](#7-proposed-tickets)
8. [Decisions](#8-decisions)
9. [Sources not reached](#9-sources-not-reached)

## 1. Summary

The field has moved since proof-automation.md was written. Lean's answer to "simp is not
enough" is no longer a bigger `simp`. It is `grind`, an SMT-style engine: congruence closure
over everything in scope, lemma instantiation by pattern (e-matching), guided case splits, and
arithmetic solvers sharing one "whiteboard" of facts, each fact with an ordinary proof term
**[cited]** (§5.1). The e-graph rewriting tactic built on `egg` for Lean (POPL 2026) now
points its users to `grind` **[cited]**. Stitchwort's `cases` is already a small `grind`: it
splits on what the goal is stuck on and closes cases by computation, constructor
contradiction, injectivity, a hypothesis, or `omega` (`crates/elab/src/cases.rs:1-43`)
**[checked]**. What it lacks is the middle layer: equalities among hypotheses, and
hypotheses that are functions. That is exactly SW-608's items 2 and 5. A congruence-closure
closer is the most valuable thing to steal here (§5.1).

The second theme is **definitions as proof structure**. Lean generates, for every function,
a case theorem (`f.fun_cases`, 2025) and an induction theorem (`f.induct`, 2024) whose cases
are the function's own branches with their conditions as hypotheses **[cited]**. The AoC
notes say again and again that the proofs that went well were the ones that "match on the
program's own `match`" (days 17, 20, 21, 22, 24) **[checked]**, and the ones that broke were
those where a definition's `match found:` couldn't be stepped through (days 12, 16, 23;
SW-802) **[checked]**. Generated case theorems would do the first for free and remove the
second (§5.2).

The third is **stability**. Lean's `simp?`, `grind?` and `try?`, and Isabelle's
Sledgehammer one-liners, all run search once and write back the explicit form; Mariposa and
Dafny's brittleness work measure how fragile automated proofs are **[cited]**. Stitchwort's
`cases` (64-split budget) and `rewrite` (search budget) are deterministic but budgeted, and
nothing reports how close a proof is to its budget. Cheap to fix (§5.3).

Smaller items: a `decide` for finite propositions with a counterexample on failure (SW-800,
§5.4); generators derived from hypotheses for the counterexample search (§4, C17–C19);
machine-readable goals for agent-written proofs, which the Lean FRO now names as a design
requirement (§5.5).

What I'd not steal: an external SMT or first-order prover in the loop (Lean-auto, LeanHammer,
Lean-SMT, CoqHammer). They need a large reconstruction layer and a lemma library annotated for
them, and Stitchwort's evidence doesn't point there (§5.5, C25).

## 2. Method and queries

Searches were run with the web search tool (standard mode) on 29 Oct 2026. Rerun them as
written, adding the months since the last run.

| # | Query | Kept or useful hits |
|---|---|---|
| Q1 | `Lean 4 grind tactic congruence closure e-matching paper 2025` | grind reference; learned interventions (arXiv 2607.22972) |
| Q2 | `egg e-graphs equality saturation proof producing explanations dependent types ITP 2023 2024` | lean-egg thesis; Isabelle egg checker (AFP) |
| Q3 | `"bv_decide" Lean 4 bitblasting LRAT certificate verified checker paper` | OOPSLA 2025 |
| Q4 | `Lean 4 omega tactic implementation paper Kim Morrison justification` | Lean 4.7 notes, Zulip |
| Q5 | `Aesop white-box best-first proof search Lean 4 CPP 2023 Limperg From` | CPP 2023 |
| Q6 | `LeanHammer premise selection Duper Lean 4 hammer 2025 paper` | arXiv 2506.07477 |
| Q7 | `Lean-auto interface automated theorem provers Lean 4 CAV 2025 monomorphization` | CAV 2025 |
| Q8 | `Breitner functional induction Lean 4 paper ITP 2025 "functional induction" unfolding equations` | Lean 4.8 notes, Zulip |
| Q9 | `Sledgehammer proof reconstruction Isabelle 2023 2024 paper "one-liner" Mirabelle success rate` | CADE-30 (arXiv 2508.20738) |
| Q10 | `Plausible property based testing Lean 4 counterexample tactic` | Plausible; Chamelean |
| Q11 | `SMTCoq Sniper Rocq 2023 2024 preprocessing dependent types automation paper` | CPP 2023 |
| Q12 | `Lean 4 simp lemma set robustness "simp?" "simp only" flexible linter proof stability paper` | Zulip threads, Lean issue 4615 |
| Q13 | `QuickChick 2023 2024 paper "computing correctly" generators inductive relations derivation Rocq` | PLDI 2022; OOPSLA 2026 |
| Q14 | `proof repair Coq Lean "proof repair" 2023 2024 paper survey Ringer PUMPKIN library changes` | ProofRepairBench; Ringer (classic) |
| Q15 | `Lean Copilot LLMs as copilots for theorem proving Lean 2024 suggest_tactics search_proof` | arXiv 2404.12534 |
| Q16 | `Agda reflection solver tactic 2023 2024 "macro" ring solver Presburger Agda paper` | agda-stdlib-meta; Attic (2022 MSc) |
| Q17 | `"Testing Theorems Fully Automatically" OOPSLA 2026 Rocq QuickChick` | OOPSLA 2026; QuickerChick |
| Q18 | `Mariposa measuring SMT instability automated program verification FMCAD 2023 Dafny F*` | FMCAD 2023; SHAKE 2024 |
| Q19 | `Gross Erbsen Chlipala "verified rewriting engine" ITP 2022 reflective rewriting Coq` | ITP 2022; JAR 2024 |
| Q20 | `Lean 4 "try?" tactic suggestions release notes 2025 exact? rw? library search` | Lean 4.18, 4.20, 4.33 notes |
| Q21 | `egglog "Better Together: Unifying Datalog and Equality Saturation" PLDI 2023` | PLDI 2023 |
| Q22 | `Duper superposition prover Lean 4 ITP 2024 Clune Qian Bentkamp Avigad proof reconstruction` | ITP 2024; arXiv 2601.14495 |
| Q23 | `Lean mvcgen verification condition generator monadic programs Std.Do 2025` | reference (superseded by `vcgen`) |
| Q24 | `Lean grind reference "grind" annotations patterns e-matching ring solver cutsat linear integer arithmetic Lean 4.22` | grind reference pages |
| Q25 | `Verus SOSP 2024 practical foundation systems verification proof-to-code ratio automation comparison Dafny Creusot` | Verus artifact |
| Q26 | `lemma synthesis interactive proofs data-driven lfind OOPSLA 2022 Coq stuck induction` | OOPSLA 2022 |
| Q27 | `Lean 4 partial_fixpoint Breitner 2025 equation lemmas unfold "eq_def" "eq_1" generation` | Lean 4.17 notes |
| Q28 | `LLM proof repair compiler feedback Lean APOLLO 2025 error messages agent verification` | NeurIPS 2025 |
| Q29 | `Lean 4 "decide" kernel reduction "decide +kernel" Nat GMP acceleration release notes 2024 2025 Decidable instance performance` | Lean 4.33/4.34 notes, Zulip |
| Q30 | `Lean 4 simprocs release notes 2024 simp procedures "simproc" ground term evaluation arith` | Lean 4.6, 4.7, 4.10 notes |
| Q31 | `congruence closure dependent type theory Lean 4 grind proof "heterogeneous equality" congruence lemmas paper Selsam de Moura` | IJCAR 2016 (classic) |
| Q32 | `lean-egg equality saturation tactic Lean ITP 2025 Rossel Goens paper` | POPL 2026; arXiv 2405.10188 |
| Q33 | `Lean grind "What is grind" de Moura Ullrich 2025 talk blog SMT-inspired proof automation design` | reference only |
| Q34 | `CoqHammer 2023 2024 update "Tactician" Graph2Tac Rocq machine learning tactic prediction paper` | Graph2Tac 2024 |
| Q35 | `Trocq proof transfer Rocq ESOP 2024 parametricity "Trakt" arithmetic preprocessing lia` | ESOP 2024 |
| Q36 | `Isabelle Nitpick Quickcheck counterexample generator evaluation 2022 2023 2024 paper ...` | classics only |
| Q37 | `"Lean-SMT" OR "lean-smt" cvc5 proof reconstruction Lean 4 paper 2025 Mohamed Barbosa` | arXiv 2505.15796 |
| Q38 | `Lean "conv" mode or "occurrence selection" rewrite pattern ssreflect "rewrite [pattern]" paper 2023 ...` | Zulip 2024; QED in Context |
| Q39 | `verified code generation benchmark Lean proofs VERINA CLEVER 2025 LLM specifications proofs Dafny benchmark` | VERINA, CLEVER |
| Q40 | `Liquid Haskell "proof by logical evaluation" 2023 2024 follow-up automation refinement reflection PLE performance` | PLEX (OOPSLA 2026) |
| Q41 | `"Small Proofs from Congruence Closure" FMCAD 2022 Flatt egg explanations` | FMCAD 2022 |
| Q42 | `miniCodeProps benchmark proving code properties Lean 2024 LLM` | arXiv 2406.11915 |
| Q43 | `lemma conjecturing theory exploration 2024 2025 Lemmanaid OR QuickSpec OR "RoughSpec" OR "TheSy" ...` | Lemmanaid; IJCAR 2024 |
| Q44 | `"QED in Context" observation study proof assistant users OOPSLA 2025 findings automation` | OOPSLA 2025 |
| Q45 | `Agda Mimer proof search Agsy replacement Agda 2.7 2024 auto` | Agda 2.7 changelog |
| Q46 | `Canonical solver dependent type theory term search Lean Norman Avigad 2025 arXiv` | ITP 2025 |
| Q47 | `Chamelean derive generators inductive relations Lean 4 property-based testing 2025` | slides; Specimen |
| Q48 | `Coq-Elpi tactics 2023 2024 paper Tassi "Elpi" tactic writing ITP OR CPP` | docs; CoqPL 2025 keynote |
| Q49 | `lean-lang.org blog functional induction Breitner 2024 "fun_induction" "fun_cases" reference` | Lean 4.17 notes |
| Q50 | `Dafny hide reveal statement 2024 opaque functions brittleness verification stability "--isolate-assertions"` | Dafny blog 2023; 4.8 notes |
| Q51 | `Seed-Prover OR "DeepSeek-Prover-V2" OR "Kimina-Prover" Lean 4 2025 whole-proof generation miniF2F PutnamBench results` | arXiv 2504.21801 |
| Q52 | `Mathlib linarith polyrith linear_combination paper 2023 certificate checking ring normalization` | Mathlib docs |
| Q53 | `Rocq lia micromega 2023 2024 improvements "itauto" OR "zify" OR "Mczify" arithmetic preprocessing CoqPL` | Rocq docs only |
| Q54 | `Lean FRO roadmap 2026 year 3 proof automation grind tactics goals` | Y3 and Y4-1 roadmaps |

Direct fetches: the Lean reference's `grind` pages (index, Congruence Closure, E-matching,
Error Messages, Minimizing `grind` calls, Case Analysis, Linear Integer Arithmetic; "latest",
which is 4.35/4.36); Lean release notes v4.8.0 and v4.17.0; the Lean FRO Year 4 part 1 roadmap;
the POPL 2026 page for Rossel et al.; arXiv abstracts 2508.20738 and 2609.16079; the SPLASH 2025
page for the `bv_decide` paper; the Plausible README.

## 3. Screened list

Screened on title and abstract against SW-894's hooks, the open tickets in the brief, and the
AoC friction items. 59 sources: 25 keep, 21 maybe, 13 drop.

| # | Source | Verdict | Why |
|---|---|---|---|
| 1 | Lean 4 `grind` (reference manual, 4.22 to 4.36, 2025–26) | keep | congruence closure + case splits + solvers; `cases`, SW-608 |
| 2 | Selsam, de Moura, Congruence Closure in Intensional Type Theory, IJCAR 2016, **classic** | keep | the congruence lemmas `grind` relies on; needs only UIP |
| 3 | Flatt, Coward, Willsey, Tatlock, Panchekha, Small Proofs from Congruence Closure, FMCAD 2022 | keep | short proofs out of an e-graph; proof-term size |
| 4 | Rossel, Schneider, Koehler, Steuwer, Goens, pen-and-paper equational reasoning by equality saturation, POPL 2026 | keep | conditional rewriting by e-graphs; now deprecated for `grind` |
| 5 | Rossel et al., Bridging Syntax and Semantics of Lean Expressions in E-Graphs, arXiv 2405.10188 (2024) | maybe | binders and definitional unfolding inside an e-graph |
| 6 | Zhang et al., egglog (Better Together), PLDI 2023 | maybe | engine; only if we build an e-graph |
| 7 | Lean functional induction `f.induct` (v4.8.0 notes, 2024) | keep | SW-802; proofs mirror programs |
| 8 | Lean `f.fun_cases` (v4.17.0 notes, PR 6261, 2025) | keep | case theorem for any function; SW-802, E-MATCH-MOTIVE |
| 9 | Lean equation lemma naming `f.eq_1`, `f.eq_def` (v4.8.0 notes) | keep | with 7, 8 |
| 10 | Lean `partial_fixpoint` (v4.17.0, 2025) | drop | Stitchwort's `{Partial}` is a different design |
| 11 | Lean `simp?` / `simp only` / Mathlib flexible linter (Zulip, Lean issue 4615) | keep | write-back; stability |
| 12 | Lean `try?` (v4.18, 4.20, 4.33 notes, 2025–26) | keep | one word that tries the suite and writes back the result |
| 13 | `grind?` / `grind only [...]` (reference) | keep | with 1, 11 |
| 14 | Bartl, Blanchette, Nipkow, Exploiting Instantiations from Paramodulation Proofs in Isabelle/HOL, CADE-30 (2025) | keep | one-liners with instantiations; explaining a found proof |
| 15 | Zhou et al., Mariposa: Measuring SMT Instability, FMCAD 2023 | keep | measure fragility by mutation |
| 16 | Dafny, "avoiding verification brittleness" blog (Dec 2023) and `hide` statements (4.8) | keep | fragility from automation; local hiding |
| 17 | Böving et al., Interactive Bit Vector Reasoning using Verified Bitblasting, OOPSLA 2025 | keep | untrusted SAT + reflective LRAT checker; counterexamples |
| 18 | Lean `decide` / `decide +kernel` (Zulip 2025; v4.34 notes) | keep | SW-800 |
| 19 | Lean `omega` (v4.7 notes, 2024) | maybe | already copied (omega.md) |
| 20 | `grind` linear integer arithmetic (cutsat; reference) | maybe | `% d`, models on failure |
| 21 | Lean simprocs (v4.6, 4.7, 4.10 notes, 2024) | maybe | computation inside rewriting; Stitchwort computes anyway |
| 22 | Limperg, From, Aesop, CPP 2023 | maybe | white-box rule search; best-first with shared metavariables |
| 23 | Qian, Clune, Barrett, Avigad, Lean-auto, CAV 2025 | maybe | DTT to HOL for ATPs |
| 24 | Clune, Qian, Bentkamp, Avigad, Duper, ITP 2024 | maybe | proof-producing superposition for DTT |
| 25 | Zhu, Clune, Avigad, Jiang, Welleck, Premise Selection for a Lean Hammer, arXiv 2506.07477 (ICLR 2026) | maybe | premise selection; hammer pipeline |
| 26 | Mohamed et al., Lean-SMT, arXiv 2505.15796 (2025) | maybe | SMT proof replay; 71% of proofs verified |
| 27 | Clune, Barbosa, Avigad, Hint-Based SMT Proof Reconstruction, arXiv 2601.14495 (2026) | keep | untrusted solver gives hints, internal prover rebuilds |
| 28 | Blot et al., Compositional pre-processing (Sniper), CPP 2023 | maybe | goal transformations before automation |
| 29 | Cohen, Crance, Mahboubi, Trocq, ESOP 2024 | drop | proof transfer; no matching friction |
| 30 | Gross et al., Accelerating Verified-Compiler Development with a Verified Rewriting Engine, ITP 2022; JAR 2024 follow-up | keep | rewriting by reflection; when proof-producing rewriting is too slow |
| 31 | Norman, Avigad, Canonical, ITP 2025 | maybe | term search for `?` holes |
| 32 | Agda 2.7 Mimer (2024) | maybe | hole filling by refinement; no case split or equality |
| 33 | agda-stdlib reflective solvers, agda-stdlib-meta | drop | already in proof-automation.md §4.6 |
| 34 | Plausible (Lean 4) | keep | counterexample tactic; comparison for ours |
| 35 | Chamelean / Specimen (Lean 4, 2025–26) | keep | generators derived from inductive relations |
| 36 | Testing Theorems Fully Automatically, OOPSLA 2026 | keep | order-insensitive generator scheduling |
| 37 | Paraskevopoulou, Eline, Lampropoulos, Computing Correctly with Inductive Relations, PLDI 2022 | keep | checkers and generators with soundness proofs |
| 38 | Mladenov, Keles, Lampropoulos, QuickerChick, arXiv 2609.16079 (2026) | drop | extraction speed; we run in-process |
| 39 | Nitpick, Quickcheck, Nunchaku, **classic** | drop | no in-window work found |
| 40 | Sivaraman et al., Data-Driven Lemma Synthesis for Interactive Proofs (lfind), OOPSLA 2022 | keep | missing-lemma friction |
| 41 | Lemmanaid (arXiv 2504.04942, 2025); QuickSpec lemmas for Vampire induction, IJCAR 2024 | keep | lemma conjecturing from tests |
| 42 | Einarsdóttir, theory exploration thesis, Chalmers 2025 | drop | covered by 41 |
| 43 | Ospanov et al., APOLLO, NeurIPS 2025 | keep | error-driven repair; sub-goal isolation |
| 44 | Song, Yang, Anandkumar, Lean Copilot, PMLR 2025 | maybe | LLM in the tactic loop |
| 45 | VERINA, arXiv 2505.23135 (ICML 2025) | keep | proof generation is the bottleneck (3.6%) |
| 46 | CLEVER, arXiv 2505.13938 (2025) | maybe | spec + proof benchmark |
| 47 | Lohn, Welleck, miniCodeProps, NeurIPS 2024 workshop | keep | code-property proofs, AoC-like |
| 48 | DeepSeek-Prover-V2 (arXiv 2504.21801); Seed-Prover (2025) | maybe | whole-proof provers; competition maths |
| 49 | Verus, SOSP 2024 (artifact) | keep | proof-to-code ratios as an effort benchmark |
| 50 | Shi, Torczon, Goldstein, Pierce, Head, QED in Context, OOPSLA 2025 | keep | how people actually work with feedback |
| 51 | Graph2Tac, arXiv 2401.02949 (2024) | drop | tactic prediction; we have no tactics |
| 52 | Liquid Haskell PLEX, OOPSLA 2026 | maybe | proof by evaluation, higher order |
| 53 | Mathlib `linarith`, `polyrith`, `linear_combination` (docs) | maybe | `ring [h]` already copies `linear_combination` |
| 54 | Rocq `lia`/`zify`/Mczify (docs) | drop | nothing new for us |
| 55 | Coq-Elpi tactics (docs; CoqPL 2025 keynote) | drop | no tactic language (DESIGN §6) |
| 56 | Wang et al., Learned Interventions in Lean 4 grind, arXiv 2607.22972 (ICML 2026) | drop | ML heuristics; small gains |
| 57 | ProofRepairBench, ICLR 2026 | maybe | repair of AI proofs from errors |
| 58 | Ringer, Proof Repair, PhD thesis 2021, **classic** | drop | library-evolution repair; no in-window follow-up found |
| 59 | Lean `conv (occs := …)`, LeanSSR occurrence patterns (Mathlib guide; Zulip 2024) | keep | SW-758; aoc-2025 pain point 1 |

## 4. Cards

Cost scale: **small** (a local change in `crates/elab` or `std`), **elaborator** (a design
change in `crates/elab`, no kernel change), **kernel** (changes `crates/core`), **research**
(open design or theory). Every proposal here keeps the kernel as it is.

**C1. Lean `grind`.** lean-lang.org/doc/reference/latest/The--grind--tactic/. *Claim:*
"inspired by modern SMT solvers"; "all proofs are by contradiction"; cooperating engines
(congruence closure, constraint propagation, e-matching, guided case analysis, satellite
solvers for linear integer arithmetic and commutative rings) share facts; it "produces
ordinary Lean proof terms for every fact it adds"; it "is **not** designed for goals whose
search space explodes combinatorially" **[cited]**. *Steal:* the architecture as a target for
`cases`: a shared set of facts, closers that add to it, and a failure report that prints it.
*Helps:* SW-608 (items 2, 3, 5), the "constructors aren't known to differ" days (15, 17, now
fixed by `cases`), day 13's inversion. *Cost:* elaborator. *Full text:* reference pages read.
Deep read §5.1.

**C2. Selsam, de Moura, Congruence Closure in Intensional Type Theory.** IJCAR 2016, arXiv
1701.04391, **classic** (named by Lean's `cc` docs and a 2025 Zulip thread on `grind`).
*Claim:* "an efficient, proof-producing congruence closure procedure that applies to every
function in intensional type theory, regardless of how many dependencies exist among its
arguments, and relies only on the uniqueness of identity proofs axiom" **[unverified]**
(abstract via search). *Steal:* the congruence lemmas for dependent arguments. Stitchwort's
kernel has axiom K (docs/core.md, as quoted in proof-automation.md §3) **[checked]**, so the
assumption holds **[inferred]**. *Helps:* §5.1, where a proof argument inside a term (`x % d`
carrying `d != 0`) is the hard case. *Cost:* elaborator. *Full text:* PDF at
lean-lang.org/papers/congr.pdf, not read.

**C3. Flatt et al., Small Proofs from Congruence Closure.** FMCAD 2022, arXiv 2209.03398.
*Claim:* minimal proofs are NP-complete; an O(n log n) greedy algorithm gives small proofs
with no asymptotic overhead, "substantially smaller" than Z3's on 3,760 benchmarks; built into
`egg` **[unverified]** (abstract). *Steal:* how to read a short `Eq.trans`/`Eq.cong` chain out
of a congruence closure, so a closer's term stays small. *Helps:* §5.1 risk "proof size".
*Cost:* part of §5.1. *Full text:* PDF linked (TU Wien repository), not read.

**C4. Rossel et al., pen-and-paper equational reasoning by equality saturation.** POPL 2026,
doi 10.1145/3776667. *Claim:* "interpreting theorems as conditional rewrite rules, and use
equality saturation to automatically derive equational proofs"; "conditions that cannot be
automatically proven may be surfaced as proof obligations" **[cited]** (abstract on the POPL
page). The tactic's repository now says it is no longer developed and recommends `grind`
**[unverified]** (search summary of the README). *Steal:* the idea of leftover side
conditions becoming obligations, not failures. The deprecation is evidence that, in Lean,
an e-graph *rewriter* lost to an e-graph *refuter* (`grind`) **[inferred]**. *Helps:* the
deferred `simp [rules]` (D1168). *Cost:* research. *Full text:* preprint linked, not read.

**C5. Lean functional induction, `fun_cases` and equation lemmas.** Lean v4.8.0 and v4.17.0
release notes. *Claim:* "Derived from the definition of a (possibly mutually) recursive
function, a functional induction principle is created that is tailored to proofs about that
function"; `ackermann.induct` has one case per branch, with an induction hypothesis per
recursive call **[cited]**; `foo.fun_cases` is "an automatically generated theorem that
splits the goal according to the branching structure of `foo`", for all functions, not only
recursive ones **[cited]**; equation lemmas are named `f.eq_1 …` and `f.eq_def` **[cited]**.
*Steal:* generate `f.cases` (and later `f.induct`) from Stitchwort's elaborated case trees.
*Helps:* SW-802, SW-809, E-MATCH-MOTIVE on days 12, 16 and 23. *Cost:* elaborator. *Full
text:* release notes read; Breitner's blog post not reached (§9). Deep read §5.2.

**C6. Write-back automation: `simp?`, `grind?`, `try?`.** Lean reference and v4.18–4.33
release notes. *Claim:* `grind?` "automatically records the theorems used by `grind` and
suggests a suitable `grind only`" **[cited]**; `try?` was reimplemented with
`evalAndSuggest`, can suggest proofs "involving `exact?`", and since 4.33 can run "on its own
where a proof is missing", off by default **[unverified]** (release-note snippets via search).
`simp?` can emit lemmas in an order that gives a different result (Lean issue 4615)
**[unverified]**. *Steal:* every searching proof word reports what it used and offers the
explicit form. *Helps:* stability; reading proofs. *Cost:* small. Deep read §5.3.

**C7. Bartl, Blanchette, Nipkow, Exploiting Instantiations from Paramodulation Proofs in
Isabelle/HOL.** CADE-30 (2025), arXiv 2508.20738. *Claim:* analysing successful Metis proofs
for variable instantiations improves Sledgehammer's success rate and the speed of its
generated proofs, and helps users "understand why a goal follows from the lemmas"
**[unverified]** (abstract via fetch summary). Sledgehammer first tries a one-line proof, then
an Isar proof **[unverified]**. *Steal:* when a search proves something, show the user the
instantiated facts, not only that it worked. For Stitchwort: `omega` could print the facts it
combined; `cases` the splits it made. *Helps:* §5.3. *Cost:* small. *Full text:* abstract only.

**C8. Zhou et al., Mariposa.** FMCAD 2023. *Claim:* instability of SMT-based proofs is
measured by running mutated queries (renaming, shuffling) and classifying each query as
stable, unstable, unsolvable or inconclusive; 17,043 queries from six projects
**[unverified]** (abstract). *Steal:* measure fragility by mutation. Stitchwort's automation is
deterministic, so the mutation that matters is the budget: re-check std and AoC with each
budget halved and list what breaks. *Helps:* confidence in `cases`'s 64 splits
(`cases.rs:62`) and `rewrite`'s 1,000,000-step search (`rewrite.rs:70`) **[checked]**.
*Cost:* small (measurement). *Full text:* not read.

**C9. Dafny on brittleness.** dafny.org/blog/2023/12/01/avoiding-verification-brittleness/
and Dafny 4.8 release notes. *Claim:* relying "too much on automation" makes verification
"chaotic"; an example verified in Dafny 3.13.1 and not 4.x; `hide` statements hide a
function's body "at a particular proof location", making `opaque` "obsolete"
**[unverified]** (search summaries). *Steal:* local hiding as the dual of SW-796's local
unfolding. *Helps:* opaque-definitions.md; day 22's closed 130,321-element list.
*Cost:* elaborator. *Full text:* not read.

**C10. Böving et al., bv_decide.** OOPSLA 2025, doi 10.1145/3763167. *Claim:* a verified
bitblaster; an external SAT solver's LRAT certificate is checked by a checker proved correct
in Lean; trusts the Lean compiler and kernel; "either solves a goal or produces a
counterexample"; beats CoqQFBV on SMT-LIB; 7,000 LLVM rewrites verified **[unverified]**
(SPLASH abstract via fetch). The proofs use `Lean.ofReduceBool`, so the compiler is trusted
**[unverified]**. *Steal:* the pattern Stitchwort's `omega` already follows (untrusted search,
certificate checked by reflection), and the counterexample on failure. Not the bit-blasting
itself until a program needs bit vectors (day 17's XOR, day 24's adder). *Helps:* §5.4.
*Cost:* research for bit vectors; small for the counterexample. *Full text:* not read.

**C11. Lean `decide`.** Lean reference; Zulip 2025. *Claim:* `decide` evaluates a
`Decidable` instance; `decide +kernel` skips the elaborator's evaluation and reduces only in
the kernel **[unverified]** (Zulip). *Steal:* a proof word for finite propositions, with
Stitchwort's `auto` machinery (which already runs `Decidable` instances at compile time,
proof-automation.md §3) **[checked]**. *Helps:* SW-800 (day 12's two 16-case tables).
*Cost:* small. Deep read §5.4.

**C12. Clune, Barbosa, Avigad, Hint-Based SMT Proof Reconstruction.** arXiv 2601.14495
(2026). *Claim:* a tactic, `querysmt`, uses cvc5's proof as hints and has the proof-producing
prover Duper rebuild the proof from the facts it names, instead of replaying every SMT step
**[unverified]** (search summary). *Steal:* nothing to build; it confirms the shape Stitchwort
uses for `omega` (untrusted search narrows, checked procedure proves), and suggests the same
for any future external prover. *Helps:* none now. *Cost:* none. *Full text:* not read.

**C13. Gross et al., Accelerating Verified-Compiler Development with a Verified Rewriting
Engine.** ITP 2022 (LIPIcs 237), arXiv 2205.00862; JAR 2024 follow-up. *Claim:* rewrite rules
proved separately are compiled into a reflective rewriter; replacing a proof-producing
pipeline in Fiat Cryptography made it about 1000 times faster **[unverified]** (abstract).
*Steal:* evidence for when a `simp` should be reflective rather than proof-producing: when
rewriting large closed terms. Day 2 part 2's `rewrite`s over 100,000–550,000-step terms
(aoc-2025.md "Proofs with rewrite and calc") **[checked]** are the Stitchwort case.
*Helps:* the deferred `simp`'s design choice (proof-automation.md §4.8). *Cost:* research.
*Full text:* not read.

**C14. Lean conversion mode and occurrence selection.** Mathlib conv guide; Zulip, March 2024.
*Claim:* `conv in (occs := 1 2 3) pat => …`; Mahboubi: occurrence numbers are "quite not
robust to changes in your proof", ssreflect patterns (`rewrite [in X in …]`) are better
**[unverified]** (search summary of Zulip). *Steal:* pattern-based occurrence selection for
`rewrite` (`rewrite p in [pattern]`), not numbers. *Helps:* SW-758; aoc-2025.md pain point 1
("`rewrite` replaces every occurrence, and a `J` motive often wants one") **[checked]**.
*Cost:* elaborator. *Full text:* guide not read.

**C15. Limperg, From, Aesop.** CPP 2023, pp. 253–266. *Claim:* rule-based best-first proof
search, designed so that "users should be able to easily predict how their rules will be
applied"; an algorithm for metavariables shared between goals without backtracking
**[unverified]** (abstract). *Steal:* the "white-box" requirement as a test for any
Stitchwort search: the user can say in advance what it will try. *Helps:* `cases`, a future
`auto` search. *Cost:* none (a design principle). *Full text:* camera-ready PDF linked, not read.

**C16. Plausible.** github.com/leanprover-community/plausible. *Claim:* "A property testing
framework for Lean 4 that integrates into the tactic framework"; reports a counterexample with
a shrink count; custom types need `Shrinkable` and `SampleableExt`, or `deriving Arbitrary`;
"if no counter-examples are found, plausible behaves like admit" **[cited]** (README) / last
part **[unverified]** (search). *Steal:* nothing new; Stitchwort's search (D1154–D1159) runs
automatically on a failed proof, which Plausible doesn't. Lean's Year 3 roadmap listed
"counter-example generation" as a goal **[unverified]** (search summary). *Helps:* confirms
our design. *Cost:* none. *Full text:* README read.

**C17. Chamelean / Specimen.** ngernest.github.io/pdfs/chamelean_public_slides.pdf;
reservoir.lean-lang.org/@strata-org/specimen. *Claim:* Plausible extended to derive
generators, enumerators and checkers from Lean inductive relations, after QuickChick
**[unverified]** (search summaries). *Steal:* for hypotheses that are inductive propositions,
generate inputs that satisfy them instead of discarding inputs that don't. Stitchwort's
search decides each hypothesis and discards failing inputs (`counterexample/mod.rs:11-18`)
**[checked]**, which finds nothing when a hypothesis is rare (a sorted list, a valid grid)
**[inferred]**. *Helps:* counterexample search stage 4. *Cost:* elaborator. *Full text:* not read.

**C18. Testing Theorems Fully Automatically.** OOPSLA 2026 (SPLASH page). *Claim:* QuickChick's
effectiveness depends on hypothesis and constraint order; the paper treats choosing
generators as a constrained scheduling problem, with a "density" estimate per relation;
push-button testing "on par with and in some cases even more effective" than hand-written
generators **[unverified]** (listing via search). *Steal:* the order-insensitivity: which
hypothesis to generate from and which to check. *Helps:* C17. *Cost:* research. *Full text:*
not read.

**C19. Paraskevopoulou, Eline, Lampropoulos, Computing Correctly with Inductive Relations.**
PLDI 2022. *Claim:* derive checkers, enumerators and generators from inductive relations, with
mechanised soundness and completeness proofs **[unverified]** (abstract). *Steal:* a derived
checker for an inductive proposition is a `Decidable` instance with a proof; that would give
`auto`, `decide` (§5.4) and the counterexample search one source of decisions for user
relations. *Helps:* SW-800, C17. *Cost:* research. *Full text:* not read.

**C20. Sivaraman et al., lfind.** OOPSLA 2022. *Claim:* lemma synthesis as data-driven program
synthesis from examples generated at the stuck proof state; more stuck proofs get a useful
helper lemma than with earlier methods **[unverified]** (abstract). *Steal:* at a failed
proof, propose a candidate lemma tested on generated inputs. Stitchwort already has the
generator and evaluator (C16). *Helps:* "missing std" is an item on almost every AoC 2024 day
(NOTES-2024.md, days 1–24 "Missing std" headings) **[checked]**. *Cost:* research. *Full text:*
PDF linked, not read.

**C21. Lemmanaid; QuickSpec for induction.** arXiv 2504.04942 (2025); IJCAR 2024. *Claim:* an
LLM proposes lemma templates and a symbolic engine fills them; QuickSpec's tested conjectures
improve Vampire's induction **[unverified]**. *Steal:* run theory exploration over a std
module (e.g. `List`) offline, test conjectures with the counterexample search, and file the
survivors as candidate lemmas. *Helps:* the lemma-complete std policy
(practical-proof-languages.md §1 item 5) **[checked]**. *Cost:* research. *Full text:* not read.

**C22. APOLLO.** NeurIPS 2025, arXiv 2505.05758. *Claim:* an LLM's proof is repaired by
agents that fix syntax, use Lean to find failing sub-goals, run automated solvers on them,
and send only the rest back to the model; large gains at a few hundred samples
**[unverified]** (abstract versions differ). *Steal:* the loop needs (a) the failing sub-goal
with its context as data and (b) a cheap automated closer to try first. Stitchwort has (b)
(`cases`, `omega`); (a) is human-readable only today (no JSON output found in `docs/` or the
driver) **[checked]**. *Helps:* agent-written AoC proofs. *Cost:* small. Deep read §5.5.

**C23. VERINA; miniCodeProps; CLEVER.** arXiv 2505.23135, 2406.11915, 2505.13938. *Claim:*
on 189 Lean tasks the best model had 61.4% correct code, 51.0% sound and complete specs and
3.6% proofs; on miniCodeProps about a quarter of 177 code properties were proved; CLEVER's
models solved at most 1 of 161 end to end **[unverified]** (abstracts). *Steal:* a small
benchmark of AoC-style code properties for Stitchwort's own proof tools and agents.
*Helps:* measuring automation. *Cost:* small. *Full text:* not read.

**C24. Verus.** SOSP 2024, artifact guide. *Claim:* lower proof-to-code ratio than Dafny and
Linear Dafny on the same systems; one summary gives 6.1K implementation lines against 31K proof
lines **[unverified]**. *Steal:* report proof-to-code ratios the same way for AoC (Stitchwort's
own: day 4 2024 "290 proof lines for a 30-line program", aoc-2024-day04-community.md
**[checked]**). *Helps:* a stable effort metric for each automation stage. *Cost:* small.

**C25. Hammers: Lean-auto, Duper, LeanHammer, Lean-SMT.** CAV 2025; ITP 2024; arXiv
2506.07477; arXiv 2505.15796. *Claim:* DTT is translated to HOL by monomorphisation for
external provers; Duper rebuilds proofs inside Lean; neural premise selection adds 21% more
goals; Lean-SMT replays about 200 of cvc5's 662 rule kinds and verified 71% of produced proofs
**[unverified]** (abstracts and summaries). *Steal:* not now. Each needs a large translation
and reconstruction layer, and Stitchwort's friction is in definitions and case structure, not
in first-order reasoning over many lemmas **[inferred]**. *Helps:* none now. *Cost:* research.

**C26. QED in Context.** OOPSLA 2025, doi 10.1145/3720426. *Claim:* 30 Rocq and Lean users
observed; proof writers adjust proofs in response to the assistant's feedback, with "difficult
back-and-forth" **[unverified]** (abstract). *Steal:* evidence that what the tool says on
failure matters as much as what it proves; supports §5.3 and §5.5. *Cost:* none. *Full text:*
PDF linked, not read.

## 5. Deep reads

### 5.1 `grind`'s whiteboard, as a closer for `cases` (C1, C2, C3)

**What Lean does** [cited, reference pages]. `grind` negates the goal and collects facts.
Congruence closure keeps equivalence classes: a hypothesis `h: t₁ = t₂` merges two classes,
and "if `a = a'` and `b = b'`, then `f a b = f a' b'` is added"; "no term is rewritten;
instead, both representatives live in the same class". Two different constructors in one class
is a contradiction, and constructor applications are merged by congruence. E-matching
instantiates quantified facts when ground terms match a pattern; patterns come from
`@[grind =]` (the left side), `@[grind →]` (forward from hypotheses), or `grind_pattern`; each
instance gets a generation one higher than its inputs, and `gen < n` or `max_insts < n` bound
it. The reference warns that "certain combinations of theorems can lead to unbounded
instantiation". Case analysis splits every `if` and `match` it finds by default
(`splitIte`, `splitMatch`), bounded by `splits := n` per branch. Solvers (linear integer
arithmetic, rings) read the same classes. On failure it prints the remaining goal and "all the
information returned by its subsystems": equivalence classes, the `True` and `False`
propositions, e-matching instance counts, and for arithmetic an "Assignment satisfying linear
constraints".

**How Stitchwort does it today** [checked]. `cases` (`crates/elab/src/cases.rs`) has a node
loop (`node`, line 212) trying closers cheapest first: computation (`by_computation`, 375), a
constructor contradiction (`by_contradiction`, 466), taking `C a = C b` apart (`take_apart`,
599), a hypothesis of exactly the goal's type (`by_hypothesis`, 393), the user's `t`, then
`omega`. If none closes the node it finds an atom the goal or a constructor equation is stuck
on and splits (`split_on`, 1074), within 64 splits (`CASES`, line 62). So it has `grind`'s
case analysis and constructor reasoning, and `omega` as a solver. It has no equivalence
classes: two hypotheses `a = b` and `f b = c` don't give `f a = c` unless computation does it.
And it never applies a hypothesis that is a function.

**The friction it would remove** [checked, SW-608 and NOTES-2024.md].
- SW-608 (2): "hypotheses that are functions (∀ y, lookup = Some y → …) aren't applied, search
  runs into the 64-case budget". That is e-matching on a local hypothesis, Lean's `→` pattern.
- SW-608 (5): "`decEq x x = No` not treated as a contradiction". Congruence closure with the
  reflexivity class (`x = x` is `True`) plus `DecEq.sound` as a forward fact covers it
  [inferred].
- SW-608 (1): `cases in t` can't use a case's own split equations to fill `t`'s holes. With
  classes, a hole whose type mentions a split atom can be filled by the class's
  representative [inferred].
- Day 13: inverting `onlyPresses machine nonzero = Some (a, b)` failed; the program was
  rewritten so a std lemma applied. Lean's answer quoted there is `split at h`. Stitchwort's
  `cases` already splits on hypotheses that equate a constructor and a stuck term (D1318), so
  the missing piece is likely the follow-up equalities, not the split [inferred; not
  reproduced].
- The plumbing lines: 189 AoC body lines and 1,003 std lines are "a lemma inside
  `Eq.cong`/`Eq.trans`/`…Cong` plumbing" (proof-automation.md §1.2). Some of that is
  congruence closure written by hand [inferred; the share is not measured].

**Mapping.** Add one closer between `take_apart` and `by_hypothesis`: build classes from the
equations in scope (hypotheses and the split equations `%splitN`), close the goal `a = b` if
`a` and `b` meet, or close any goal if two constructors meet. Emit the proof as a chain of
`Eq.trans`, `Eq.sym` and `Eq.cong` (or `J`) terms read out of the proof forest; Flatt et al.'s
greedy algorithm keeps the chain short (C3). Then, as a second stage, local ∀-hypotheses
whose conclusion is an equation or a constructor fact are instantiated by matching their
premises against the classes (Lean's `→` pattern), bounded by generation 1 or 2. No library
lemmas are instantiated in either stage: only what is in scope, so nothing changes when std
grows (§5.3).

**Assumptions this depends on.**
- Comparing terms for congruence by *syntax after forcing*, as `cases` already compares
  atoms, is enough for AoC goals; full conversion in the closure would be too slow [inferred].
- Axiom K holds in the kernel, so Selsam and de Moura's congruence lemmas for dependent
  arguments apply (C2) [checked for K; inferred for the lemmas].
- The extra closer costs little when it fails: classes over the hypotheses in scope at one
  node are small (tens of terms) [inferred, not measured].

**Risks.**
- *Proof arguments inside terms.* Without proof irrelevance (SW-93, not built), `x % d` with
  two different proofs of `d != 0` are different terms. Congruence on such a call needs the
  proofs equal too; Lean gets that from definitional proof irrelevance [inferred]. The first
  version should skip congruence through proof arguments and say so.
- *Terms that compute.* A class may contain a term the evaluator would reduce; mixing
  "computed" and "as written" is the folded-goal question again (SW-794, SW-706). Pick one,
  probably computed, as `cases` does today [inferred].
- *Performance in the 64-split loop.* Each node rebuilds classes; incremental classes (as
  Lean's are) avoid that but need undo with the elaborator's snapshots (`undo.rs`).
- *Predictability.* Stage 2 (instantiating ∀-hypotheses) is where `grind` warns of unbounded
  instantiation; generation 1 only, and report the instances used (§5.3).

**Next step.** A design note (T1): the closer, its proof term, the stage 2 bound, and a
measurement on SW-608's program and on the AoC proofs with `Eq.trans (Eq.cong …)` chains.

### 5.2 Definitions as proof structure: generated case and induction theorems (C5)

**What Lean does** [cited, release notes]. For `ackermann` with three clauses, Lean generates
`ackermann.induct (motive) (case1: ∀ m, motive 0 m) (case2: ∀ n, motive n 1 → motive (n+1) 0)
(case3: ∀ n m, motive (n+1) m → motive n (ackermann (n+1) m) → motive (n+1) (m+1))`: one case
per branch, one hypothesis per recursive call, and the call's own arguments as they are in the
body. `foo.fun_cases` (2025) is the non-recursive half: "splits the goal according to the
branching structure of `foo`", for every function. The equation lemmas `foo.eq_1, …` state
each clause, and `foo.eq_def` the whole body. Lean generates them on demand ("reserved
names") [unverified for the on-demand part; the elaboration register's C1 read the Lean source
for postponement only].

**How Stitchwort does it today** [checked]. Proofs follow programs by hand: `match name: e
with` on the program's own scrutinee "refined both the goal and the hypotheses through the
program's own `match`es" (day 20), "the `operate` lemmas never `rewrite`" (day 21), "six
nested matches on `outputOf` results" (day 24), and "every `settle` proof … is by the same
`decreasing waiting.length` as the program" (day 24). Where the program's `match` carries
its equation (`match found:`), a proof can't step through it: day 23's `drain` got
`E-REWRITE-MOTIVE` from `rewrite drain.unfold set, found in rfl` and `E-MATCH-MOTIVE` from
`match popped: set.popMin with`, and the program was rewritten in guard style (NOTES-2024.md
lines 7513–7532). Days 12 and 16 hit the same (SW-802's description). equation-lemmas.md
built stages 1–2 (`f.unfold`, local definitions with names) and deferred Lean-style equation
lemmas (D231–D233, "not now"). The lifted matches are named `owner.%matchN` (`lift.rs`), and
the error comes from `lift.rs:831` and `:1256`.

**Mapping.** Generate, per top-level definition with a case tree, a theorem `f.cases`:

```text
f.cases: (motive: (args…) -> (result: R) -> Prop)
  -> (branch₁: (pattern vars…) -> (h₁: scrutinee₁ = pattern₁) … -> motive args… body₁)
  -> …
  -> (args…) -> motive args… (f args…)
```

Each branch is a leaf of the elaborated case tree; its hypotheses are the equations the tree
tested (the same `%splitN` equations `cases` writes), including a `match found:` equation,
whose proof is passed through rather than generalised. That last point is why it works where
`match popped:` fails: the theorem is proved once, inside the definition's own scope, where the
equation's proof is in hand [inferred]. Applying `f.cases` to a goal about `f x` is then one
application, with no motive written. `f.induct` follows for structurally recursive and
`decreasing` definitions, with the measure's proof reused, so day 24's proofs would not repeat
`decreasing waiting.length` [inferred].

**Assumptions.**
- The elaborated case tree keeps enough of the source (which equation each leaf tested) to
  state the branches readably [inferred; `matching.rs` would have to be read for this].
- Generating on demand, at first use, keeps every program's load time unchanged; content
  hashing then needs the generated theorem's hash to be a function of `f`'s hash only
  [inferred; DESIGN §11].
- Most AoC "match on the program's match" proofs would shrink, not only the failing ones; I
  haven't converted one to check [unverified].

**Risks.** Large case trees (a 25-arm `tabulateSame`, day 21) give large theorems; generate
only when used. The motive must be found for applying `f.cases` to a goal: the same
abstraction `rewrite` does (`rewrite.rs`, motive check and round trip), with its known
failures on proof arguments (E-REWRITE-MOTIVE). Names collide with user lemmas called
`cases`; Lean uses reserved suffixes.

**Next step.** A design note (T2), revisiting equation-lemmas.md's D231–D233 with SW-802 and
days 12, 16, 23 as the acceptance cases; it should answer whether `f.cases` replaces SW-802's
per-branch equation lemmas or comes on top of them.

### 5.3 Search that writes back what it found; fragility measured (C6, C7, C8, C9, C15)

**What others do** [cited or unverified as marked in the cards]. Lean: `simp?` turns `simp`
into `simp only [lemmas used]`; `grind?` into `grind only [...]` with each lemma's pattern
marked (`=`, `→`, `←`); `try?` tries a suite (`simp`, `grind`, `exact?`, …) and suggests the
first that works. Mathlib's flexible linter flags a step that depends on where a non-`only`
`simp` stopped. Isabelle: Sledgehammer finds a proof externally and writes a one-line `metis`
or `smt` call with the facts, and since CADE-30 the instantiations. Dafny and F\*: measure
brittleness (Mariposa: mutate the query, see if it still proves; Dafny's `--isolate-assertions`
and `hide`). Aesop's design rule: a user should be able to predict what a search will try.
The Lean FRO's Year 4 roadmap: `grind` and `bv_decide` "should fail fast and tell the user why"
**[cited]**.

**Where Stitchwort is** [checked]. Its searching words are budgeted and deterministic:
`cases` (64 splits), `rewrite` (`SEARCH_BUDGET` 1,000,000, `rewrite.rs:70`), `omega` (reads
"every arithmetic fact in scope", `omega.rs` header; splits disjunctions within
`search::Limits::splits`), `auto` (decision search, `auto.rs:249`). None has a lemma set that
grows behind the proof, which is Lean's main fragility source (proof-automation.md §4.2, and
"No `@[simp]` attribute in the first version"). The remaining fragility is in budgets and in
what computes: a std change that makes a definition compute further, or a program change that
adds a split, can push a proof over budget with no warning beforehand. The AoC 2025 notes
record two cases of a `rewrite` that was slow or over budget only after a change (day 2 part 2,
`fourChecked`, `kFold`), found by bisection (aoc-2025.md, pain point 8).

**Mapping.**
1. `cases?` and `omega?` (or a note on success under a flag, and an LSP code action): `cases?`
   prints the split tree it built (atoms in order) and which closer closed each leaf; `omega?`
   prints the facts it combined (the certificate's non-zero rows). This is Sledgehammer's
   "show the instantiated facts". Small: the data exists in `Run` (`cases.rs:101-105` already
   describes a run) and in the certificate.
2. Budget headroom: `stitchwort check --budgets` reporting, per declaration, the largest
   fraction of any budget used; a proof over 50% is listed as fragile. And a one-off
   Mariposa-style run: re-check std and aoc with every budget halved; the proofs that fail are
   the fragile ones. Small.
3. Keep the rule that no automation reads a global lemma set without listing it in the proof.
   If `simp` (D1168) or a `grind`-like closer ever takes library lemmas, take Lean's later
   lesson and make the `only` form the one written in files, with the open form a code
   action that writes it back [inferred from C6].

**Assumptions.** Budgets are the main source of breakage after std changes; I found no
measurement of this in the repo [unverified]. Code actions exist for the LSP (language-server.md,
stage 2 is goal holes) [checked that the note exists; not what it builds].

**Risks.** Printed split trees can be long (64 leaves); show the tree's shape, not every goal.
Halving budgets may flag many proofs that are fine in practice; the run's purpose is a list,
not a gate.

**Next step.** Tickets T3 (write-back) and T4 (the budget measurement).

### 5.4 `decide` for finite propositions, with a counterexample (C10, C11, C19)

**What others do.** Lean's `decide` evaluates a `Decidable` instance; for `∀ b: Bool, …` the
instances compose, so a truth table is one word [unverified that Lean's core has the
instance for `∀` over `Bool`]. `bv_decide` scales the idea: an untrusted SAT solver, an LRAT
certificate, a checker proved in Lean, and a counterexample when the goal is false.

**Where Stitchwort is** [checked]. `auto` already proves `[auto h: P]` "by running a
`Decidable` instance at compile time (`fromYes d Trivial`, which the kernel re-runs)"
(proof-automation.md §3), and `if` decides propositions with instances (docs/syntax.md, `if`
row). Day 12 wrote "two 16-case truth tables" as 16 `rfl` clauses each, and a wildcard in a
`match` on three `Bool`s left `s ∧ False` stuck (NOTES-2024.md, day 12 "6. Proofs"). SW-800
asks for `decide`, limited to a few `Bool` variables.

**Mapping.** (a) Library instances `Decidable ((b: Bool) -> P b)` from `Decidable (P True)` and
`Decidable (P False)`, and the same for `Fin n` and enumerations (derived like `DecEq`). (b) A
proof word `decide` that is `fromYes d Trivial` for the goal's instance, with a cap on
evaluation steps. (c) On `No`, run the instance's witness search (or the counterexample search,
which already decides statements, `counterexample/mod.rs:11`) and show the assignment, as
`bv_decide` does. Nothing new is trusted: the kernel re-runs the instance. `cases` already
covers some of this (it splits on stuck `Bool` atoms within 64 cases); `decide` is the
predictable version for a statement quantified over finite types, with no stuck atom to find.

**Assumptions.** Day 12's tables are statements over at most four `Bool`s (16 cases) [checked:
"16-case truth tables"]. Evaluating 2⁴–2⁶ cases in the kernel is cheap [inferred]. The
counterexample search's checker can be reused for the failing assignment [inferred from its
header].

**Risks.** Overlap with `cases` and `auto` (three words for decisions). Say in docs/syntax.md
when to use which. `Prop` connectives in Stitchwort are `if`s on `Bool`s
(`logic.rs:4-11`, per simp.md) [checked via simp.md], so the instances must compose with
that encoding.

**Next step.** Ticket T5; it can close SW-800.

### 5.5 Designing for agent-written proofs (C22, C23, C26, Lean FRO roadmap)

**What others found.** APOLLO's gains come from structure around the model, not the model:
isolate the failing sub-goal, try automated solvers first, ask the model only for what is left
(C22). VERINA puts proof generation at 3.6% for the best model of mid-2025 (C23). The Lean FRO
Year 4 roadmap says "AI-generated proofs are becoming a major source of `grind` and
`bv_decide` usage" and that "the tactics, their error messages, and their documentation must
work as well for agents as they do for humans" **[cited]**. QED in Context finds human
proof-writing is a loop driven by the assistant's feedback (C26).

**Where Stitchwort is.** The AoC proofs in this repo are written by agent lanes (board
`agent:` fields; the NOTES are their reports) [inferred from the board's format]. The errors
are already designed to be read: computed goals in `E-REWRITE-NOTHING`, notes, folded terms
(aoc-2025.md, "Since (SW-207)") [checked]. What an agent gets is text: I found no JSON
diagnostics or goal output in `docs/` or the driver [checked by search, so absence is
likely but not certain].

**Mapping.** (a) `stitchwort check --json`: every diagnostic with its code, span, notes, and
for each `?` hole its goal and the names in scope with their types, as data. (b) A lemma search
by type for a hole (`?search`, Lean's `exact?`), over std's names, using the unifier with a
small budget. (c) A small benchmark of AoC-style properties (miniCodeProps' shape) to measure
each automation stage and each agent change against.

**Assumptions.** Agents keep writing most proofs here [unverified]. Structured goals help an
agent more than the current text does [unverified; APOLLO's evidence is about sub-goal
isolation, not format].

**Risks.** A JSON format becomes an interface to keep stable; version it. Lemma search is a
budget and ranking problem; Lean's took years (`exact?` was `library_search`).

**Next step.** Ticket T6 (JSON goals and errors), T7 (benchmark). Lemma search is a maybe for
later.

## 6. Steal next

Ranked by value over effort. "Value" is how many open tickets and AoC friction items it
addresses; "effort" is the cost scale in §4.

| Rank | Idea | Source | Helps | Cost |
|---|---|---|---|---|
| 1 | Congruence-closure closer in `cases`, then local ∀-hypotheses instantiated (generation 1) | C1, C2, C3 | SW-608 (1, 2, 5); plumbing lines | elaborator (design note first) |
| 2 | Generated `f.cases` (then `f.induct`) from case trees | C5 | SW-802, SW-809; days 12, 16, 23 | elaborator (design note first) |
| 3 | `cases?` / `omega?`: report and write back what was used | C6, C7 | readability; stability | small |
| 4 | Budget headroom report and a halved-budget run over std and aoc | C8, C9 | silent breakage (aoc-2025 pain point 8) | small |
| 5 | `decide` with `Decidable` instances for ∀ over finite types; assignment on failure | C10, C11 | SW-800 | small |
| 6 | `check --json`: diagnostics and `?` goals as data | C22, C26 | agent loops; LSP | small |
| 7 | Pattern-based occurrence selection for `rewrite` | C14 | SW-758; aoc-2025 pain point 1 | elaborator |
| 8 | Generators derived from inductive hypotheses in the counterexample search | C17, C18, C19 | counterexample stage 4 | elaborator |
| 9 | AoC proof-effort benchmark (proof-to-code ratio per day, per stage) | C23, C24 | measuring 1–8 | small |
| 10 | Theory exploration over std with the counterexample tester | C20, C21 | "missing std" items | research |
| 11 | Reflective rewriting if `simp` is ever built for big closed terms | C13 | day 2 part 2 | research |

Not recommended now: external hammers (C25), an e-graph rewriter (C4: its own authors moved
to `grind`), a tactic language (C15, Elpi; DESIGN §6 "No tactics"), bit-blasting (C10) until a
program needs bit vectors.

## 7. Proposed tickets

Label `research` on each. Not added to the board.

**T1. Design note: a congruence-closure closer for `cases`.** `cases` closes a case by
computation, constructor contradiction, injectivity, an exact hypothesis, `t` or `omega`, but
never combines equations in scope: `a = b` and `f b = c` don't give `f a = c`, and a
hypothesis `∀ y, lookup = Some y → …` is never applied (SW-608 items 2 and 5). Lean's `grind`
does both with congruence closure and e-matching. Write a note deciding: the closer's place in
the order; term comparison (computed or as written); the proof term (an `Eq.trans`/`Eq.cong`
chain read from a proof forest, kept short by Flatt et al.'s greedy method); what to do with
proof arguments while SW-93 is unbuilt; and a second stage that instantiates local
∀-hypotheses, generation 1 only, never library lemmas. Measure on SW-608's program and on AoC
proofs with `Eq.trans (Eq.cong …)` chains. Refs: docs/research/proof-automation.md §5.1;
SW-608.

**T2. Design note: generated case and induction theorems (`f.cases`, `f.induct`).** Proofs
that follow the program's own `match` go well; proofs about a definition whose `match found:`
carries its equation can't step through it (E-MATCH-MOTIVE, days 12, 16, 23; SW-802). Lean
generates `f.fun_cases` and `f.induct` from the definition. Write a note on generating
`f.cases` from Stitchwort's elaborated case trees (one branch per leaf, the tested equations
as hypotheses, a `match found:` equation passed through), on demand, with content hashes
derived from `f`'s; then `f.induct` reusing a `decreasing` measure. Revisit equation-lemmas.md
D231–D233 and say whether this replaces SW-802's per-branch equation lemmas. Acceptance: day
23's `drain`, days 12 and 16's E-MATCH-MOTIVE cases. Refs: §5.2.

**T3. `cases?` and `omega?`: show what was used.** On success, `cases?` prints the split tree
(atoms in order, the closer of each leaf) and `omega?` the facts its certificate combined, and
the LSP offers to write the explicit form (nested `match`es; `omega [facts]`). Sledgehammer and
Lean's `simp?`/`grind?` do this; it makes automated proofs readable and shows how close a proof
is to its limits. Refs: §5.3.

**T4. Measure proof fragility: budget headroom.** Add a per-declaration report of the largest
fraction of each search budget used (`cases` splits, `rewrite` search steps, `omega` splits,
`auto` depth), and run std and aoc once with every budget halved; list what fails. Mariposa
measured SMT proof instability by mutation; Stitchwort's automation is deterministic, so
budgets are the mutation that matters. Output: a table in this register or a note, no gate.
Refs: §5.3; aoc-2025.md pain point 8.

**T5. `decide` for propositions over finite types (closes SW-800).** Library `Decidable`
instances for `(b: Bool) -> P b`, `(i: Fin n) -> P i` and derived enumerations (and the `∃`
forms), and a proof word `decide` that runs the goal's instance (`fromYes d Trivial`, re-run by
the kernel) with a step cap, showing the falsifying assignment when the answer is `No`.
Document when to use `decide`, `cases` and `auto`. Acceptance: day 12's two 16-case tables
become one word each. Refs: §5.4.

**T6. `stitchwort check --json`.** Emit every diagnostic (code, span, message, notes) and, for
each `?` hole, the goal and the names in scope with their types, as versioned JSON. Agent
repair loops (APOLLO) depend on isolating the failing sub-goal as data, and the Lean FRO now
treats agent use of error messages as a requirement. The LSP's goal holes could share the
code. Refs: §5.5.

**T7. An AoC proof-effort benchmark.** For each AoC day with proofs, record program lines,
proof lines, theorems, and check time, in one table refreshed per automation stage (as Verus
reports proof-to-code ratios against Dafny); add a small set of miniCodeProps-style properties
about std functions as a fixed target for automation and agents. Refs: §4 C23, C24.

**T8. Investigate: theory exploration over std.** Enumerate small equations over one std module
(`List` first), test each with the counterexample search's generators and evaluator, drop those
that already follow by `rfl` or exist in std, and list the rest as candidate lemmas for review.
QuickSpec, lfind and Lemmanaid do this; "Missing std" is a heading on most AoC 2024 days.
Time-boxed; output a list, not lemmas. Refs: §4 C20, C21.

## 8. Decisions

**D1880. Make a congruence-closure closer in `cases` (T1) the next proof-automation design,
ahead of `simp [rules]` (deferred, D1168)?** Assumptions: the open friction (SW-608, the
plumbing lines) is about combining facts in scope, not rewriting with library lemmas; Lean's
move from e-graph rewriting to `grind` transfers. [Yes, design note first.]

**D1881. For SW-802, write a design note on generated case theorems (`f.cases`, T2) rather
than per-branch equation lemmas alone?** Assumption: the elaborated case tree keeps which
equation each leaf tested, so the theorem can be stated readably; T2 checks this first.
[Yes.]

**D1882. Adopt as a standing rule: no proof automation reads a global lemma set unless the
proof lists the lemmas, and every searching word gets a `?` form that writes back what it used
(T3)?** Assumption: Lean's experience (`simp only`, `simp?`, the flexible linter, `grind?`)
transfers, and code actions can carry the write-back. [Yes.]

## 9. Sources not reached

- de Moura's `grind` slides (leodemoura.github.io/files/grind.pdf, CADE25.pdf): downloaded but
  image-only PDFs; no text extraction tool was available. So nothing here says how `grind`
  stores proofs (proof forest or on demand) or handles dependent arguments.
- Breitner's functional induction blog post (lean-lang.org/blog/2024-5-17-functional-induction/):
  redirects to web.archive.org, which the fetch tool can't reach. No ITP paper on functional
  induction was found.
- The Lean reference's `Recursive-Definitions` page doesn't describe `fun_induction` or
  `eq_def` in the parts read (two fetches of a 217,000-character page).
- `grind`'s cutsat page doesn't say how its proofs are produced.
- Full texts not read (abstract or summary only): Selsam and de Moura 2016, Flatt et al. 2022,
  Rossel et al. 2026, bv_decide (OOPSLA 2025), Bartl et al. (CADE-30), Mariposa, Gross et al.
  2022, Aesop, Lean-auto, Duper, LeanHammer, Lean-SMT, Clune et al. 2026, Chamelean slides,
  Testing Theorems Fully Automatically, Computing Correctly, lfind, Lemmanaid, APOLLO, VERINA,
  CLEVER, miniCodeProps, QED in Context, Verus.
- No 2022+ paper found on: Isabelle Nitpick/Quickcheck, CoqHammer updates, Rocq `lia`
  improvements, Elpi tactics, Lean `simp` robustness, a user study of rewriting.
- Lean Zulip was read only through search snippets.
- Not searched year by year: ITP, CPP, IJCAR, CADE, FroCoS and AITP programmes, and the Lean
  workshop (Lean Together) programme. A refresh should start there, and with the Lean FRO's
  six-month roadmaps.
