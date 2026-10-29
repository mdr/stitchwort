# Literature trawl: kernel and type theory

*SW-894, cluster 1. Trawled 29 October 2026 against `main` at `fd34ebcd`. Research only: no
code changed, no tests run. Window: 2022 onwards (D1831); older work appears only where
in-window work or a system we compare with relies on it, marked **classic**.*

Labels: **[cited]** read in the linked source (an abstract, a release note, an issue, a
manual page or a test description, fetched on 29 Oct 2026); **[checked]** read in
Stitchwort's code or docs at the place given; **[inferred]** my reasoning; **[unverified]**
from a search summary or a second-hand account only.

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

The most useful material in this cluster isn't a paper. It's the run of kernel soundness bugs
found in Lean and Rocq between July and October 2026, many by AI agents, and the Lean team's
response: a "kernel logic renovation" (lean4#14977), a public bank of good and bad kernel
inputs (the Lean Kernel Arena), several independent checkers bundled with the toolchain, and
the removal of the axiom that trusted the compiler. §5.1 sorts those bugs into ten classes
and checks each against `crates/core`. Stitchwort avoids most classes by construction
(nested types are checked as written, not translated; extras are pinned by content hash;
there's no conversion cache and no universe polymorphism). Two gaps are worth closing:

- **Nat natives are trusted by registry binding and type, not by body.** `register_native`
  (`crates/core/src/native.rs:378`) checks a native's type and arity only. R3 and R4, compact
  text and `Float` are pinned to their definitions' content hashes. Lean's lean4#15908 (Oct
  2026) is exactly this shape: `Nat.add`'s native trusted by name. In Stitchwort the prelude
  is compiled in and the registry never rebinds, so the exposure is small **[inferred]**,
  but pinning by hash is cheap and makes the rule uniform (T4).
- **Stitchwort's fuzzers only look for panics.** `crates/core/tests/fuzz.rs` checks that the
  kernel "never panics"; nothing searches for an accepted proof of `Void` **[checked]**. In
  Rocq, one person with Claude Opus 4.6 and expert hints found seven proofs of `False` in
  about 72 hours (Stérin, Mar 2026). A hint list from §5.1 and one audit lane (T1), plus the
  bug shapes ported as must-reject tests (T2), are the cheapest way to buy assurance.

The second theme is **large elimination from recursive propositions**. Lean is removing it
(lean4#13851) because it makes definitional equality undecidable once proofs are
irrelevant, which is Carneiro's counterexample. Felicissimo et al. (LICS 2026) give the
theory. Stitchwort accepts the same shape today (`Loop`, proof-irrelevance.md §5.1) and
plans definitional proof irrelevance (SW-93, SW-803). Adding one condition to `E-PROP-ELIM`
(`check.rs:923`) before SW-93 removes the problem rather than reasoning around it (§5.2, T3).

The third is **eta**. Lean's 2026 eta work shows that eta for records plus irrelevance of
proof fields breaks transitivity unless "unit-like" types (records whose fields are all
proofs) are handled. SW-55's draft excludes only records with no fields (records.md §7.1).
After SW-93, a record whose fields are all proofs is the same case (§5.4, T5).

Rewrite rules (§5.3): Stitchwort's R3 and R4 already meet everything Rocq and Agda check for
user rules, and more. What's worth stealing is a mechanical confluence check and a written
criterion for the next rule, not a general rewrite-rule feature.

## 2. Method and queries

Searches were run with the web search tool (standard mode) on 29 Oct 2026; GitHub issues and
the Kernel Arena repository were read with `gh` and `curl`. Rerun them as written, adding the
months since the last run.

| # | Query or source | Kept or useful hits |
|---|---|---|
| Q1 | `"The Taming of the Rew" rewrite rules type theory follow-up 2023 2024 Rocq rewrite rules` | Rocq refman rewrite rules (9.1, 9.3) |
| Q2 | `Lean4Lean Carneiro verified Lean kernel paper arXiv 2024` | arXiv 2403.14064 (v1–v3) |
| Q3 | `"Observational Equality: Now For Good" Pujet Tabareau POPL 2022` | POPL 2022; follow-ups |
| Q4 | `"Impredicative Observational Equality" Pujet Tabareau POPL 2023 quotients` | POPL 2023; Danielsson arXiv 2609.08578 |
| Q5 | `"Rewrite rules" Rocq 9 kernel Leray Gilbert Tabareau "symbol" rewrite rules confluence check 2024 2025` | Rewster (ITP 2024) |
| Q6 | `Lean 4 kernel soundness bug found 2024 2025 lean4checker nanoda independent checker` | Lean 4.32.2 notes; oss-security advisories |
| Q7 | `"Observational Equality Meets CIC" ESOP 2024 Pujet Tabareau indexed inductive types` | TOPLAS 2025 version |
| Q8 | `"The Rewster" type preserving rewrite rules Coq … abstract` | ITP 2024 abstract |
| Q9 | `CVE-2026-72711 Lean 4 kernel opaque declarations` | VulnCheck, OSV records |
| Q10 | `gh search issues --repo leanprover/lean4 "kernel soundness"` and `"proof of False"` | lean4#15908, 15704, 14484, 14576, 15101, 15100, 14875 |
| Q11 | `gh search issues --repo leanprover/lean4 kernel False --created >=2025-01-01` | lean4#14977, 15706, 15705, 15226, 13626, 15023, 13851 |
| Q12 | `hal-05474391 accessibility large elimination proof irrelevance decidability 2026` | (no hit; see Q14) |
| Q13 | `Lean "Kernel Arena" external checkers test suite nanoda lean4lean 2026` | arena.lean-lang.org; Lean 4.35.0 notes |
| Q14 | `"Definitional Proof Irrelevance" decidable "Acc" large elimination undecidable 2025 paper Lean Rocq SProp` | Felicissimo et al., LICS 2026 |
| Q15 | `nanoda_lib Rust Lean 4 type checker ammkrn type checking in lean4` | nanoda_lib; ammkrn's book |
| Q16 | `MetaRocq verified kernel "Correct and Complete Type Checking and Certified Erasure for Coq, in Coq" …` | JACM 2025 |
| Q17 | `Agda --rewriting confluence check "--local-confluence-check" "--confluence-check" …` | Agda manual, rewriting |
| Q18 | `Rocq sort polymorphism paper 2024 2025 "sort polymorphism" SProp Prop Type quality variables` | slides only (Poiret et al. 2025) |
| Q19 | `"Martin-Löf à la Coq" CPP 2024 decidability of conversion logical relation formalization` | CPP 2024 |
| Q20 | `"Higher Observational Type Theory" Altenkirch Kaposi Shulman Narya 2024 2025 paper` | talks, Narya docs |
| Q21 | `Rocq critical bugs list dev/doc/critical-bugs kernel soundness bugs history` | CVE-2026-72703/4/5/14 advisories; Stérin blog |
| Q22 | `Bezem Coquand Dybjer Escardó "Type theory with explicit universe polymorphism" 2022` | TYPES 2022 |
| Q23 | `Carneiro universe level comparison complete algorithm imax Lean 2025 2026 …` | Géran, CSL 2026; arena level tests |
| Q24 | `Kovács "Generalized Universe Hierarchies and First-Class Universe Levels" CSL 2022` | CSL 2022 |
| Q25 | `Lean 4 kernel unit-like eta structure eta "is_def_eq_unit_like" 15372 15373 …` | lean4#2258; Lean 4.33.1 notes |
| Q26 | `Pujet PhD thesis 2023 "Computing with Extensionality Principles in Type Theory"` | not found; Sestini thesis 2023 |
| Q27 | `type checker conversion performance hash-consing sharing "normalization by evaluation" dependent types 2023 2024 …` | Rebound (2025); classics |
| Q28 | `Lean 4.33.1 release notes kernel is_def_eq cache union-find soundness 14806` | 4.33.1 and 4.34.0 notes |
| Q29 | `"Two-level type theory" Kovács "Staged compilation with two-level type theory" ICFP 2022` | ICFP 2022, ICFP 2024 |
| Q30 | `Rocq primitive strings kernel "primitive" integers floats arrays trusted base justification 2024 2025` | Rocq refman, primitive objects |
| Q31 | `Dedukti Lambdapi rewrite rules confluence termination checker 2023 2024 "SizeChangeTool" …` | Lambdapi tooling (2023 talk) |
| Q32 | `Breitner "lean-inductive-models" kernel exploits …` | nothing new |
| Q33 | `Lean "comparator" tool trusted statement checking sandbox kernel external checker 2026` | Lean reference, "Validating proofs" |
| Q34 | `Sterling Angiuli Gratzer "A cubical language for Bishop sets" XTT LMCS 2022` | LMCS 2022 |
| Q35 | `quotient types dependent type theory definitional computation kernel 2023 2024 2025 …` | Monnier TyDe 2024; Felicissimo–Tabareau TYPES 2025 |
| Q36 | `Lean Zulip lean4lean "State of the Proof" Carneiro 2025 2026` | WITS 2026 keynote abstract |
| Q37 | `Cockx blog OR Kovács blog 2024 2025 "rewrite rules" OR "conversion checking" …` | nothing in window |
| Q38 | `"Strictly positive" OR "nested inductive" Lamiaux Forster Sozeau Tabareau 2025 …` | RocqPL 2026; Rocq 9.2 |
| Q39 | `"nanobruijn" OR "sokonanoda" Lean kernel checker fast techniques` | arena pages only |
| Q40 | `Agda 2.7 2.8 opaque definitions "--prop" "--two-level" changelog …` | Agda changelogs |
| Q41 | `"universe polymorphism" "cumulativity" Agda Lean Rocq comparison 2024 2025 paper …` | arXiv 2607.11329, 2609.24604; TYPES 2025 |
| Q42 | `"Strict propositions" OR "SProp" Agda Prop unsoundness bug issue 2023 2024 …` | Agda PR 6936 |

Direct fetches: Rocq refman `addendum/rewrite-rules.html` (9.3); arXiv abstracts 2403.14064,
2609.08578, 2607.11329, 2609.24604, 2310.06376; Lean release notes 4.32.2, 4.33.1, 4.34.0,
4.35.0 (first 100k characters); Lean reference "Validating proofs"; arena.lean-lang.org (front
page, `checker/sokonanoda`); the descriptions of 15 Kernel Arena tests (`tests/bugs/…`,
`tests/corner-cases/…` on the `master` branch of `leanprover/lean-kernel-arena`); oss-security
posts 2026/q3/381, 2026/q4/379, 381–384, openwall 2026/08/02/1 and 2026/10/26/2; Stérin, "In
search of falsehood" (5 Mar 2026); the chocola talk page for Felicissimo (30 Apr 2026); TyDe
2024 "Normalizable types" page; DROPS pages for Lean4Lean (TYPES 2025), the Rewster (ITP
2024) and Géran (CSL 2026); ammkrn's *Type checking in Lean 4*, "Adversarial inputs"; GitHub
issues and PRs lean4#13626, 13851, 14484, 14576, 14577, 14875, 14977, 15023, 15101, 15226,
15704, 15705, 15706, 15908.

## 3. Screened list

Screened on title and abstract (or issue text) against the hooks in SW-894 and the tickets in
the brief. 58 sources: 23 keep, 21 maybe, 14 drop.

| # | Source | Verdict | Why |
|---|---|---|---|
| 1 | Lean kernel bug reports 2026 (lean4#14484, 14576, 14875, 15101, 15100, 15704, 15705, 15706, 15908) | keep | bug classes; §5.1 |
| 2 | Lean 4.33.1 / 4.34.0 notes: #14806 non-transitive cache, #14807 `is_prop`, #14808 recursor recheck, #14849 Nat size, #14833 GMP | keep | §5.1 |
| 3 | Lean 4.35.0 notes: bundled checkers, `--paranoid`, `lake check`, `comparator`, removal of `trustCompiler` (#14953) | keep | trust UX; T6 |
| 4 | Lean kernel logic renovation, lean4#14977 (Aug 2026) | keep | §5.2, §5.4 |
| 5 | lean4#13851, no large elimination of recursive `Prop` inductives | keep | §5.2; SW-93 |
| 6 | Felicissimo, Leray, Pujet, Tabareau, Tanter, Winterhalter, Definitional Proof Irrelevance Made Accessible, LICS 2026 | keep | §5.2 |
| 7 | lean4#15023, quotients of propositions in `Sort (max 1 u)` | keep | confirms Stitchwort's carrier rule |
| 8 | Lean Kernel Arena (tests, tutorial, checkers), 2026 | keep | test bank; T2 |
| 9 | Rocq guard-checker and universe bugs, CVE-2026-72703, 72704, 72705, 72714 (advisories) | keep | §5.1 |
| 10 | Stérin, In search of falsehood (blog, Mar 2026) | keep | audit method; T1 |
| 11 | Carneiro, Lean4Lean (arXiv 2403.14064; ITP 2024; TYPES 2025; WITS 2026 keynote) | keep | verified checker; trust |
| 12 | Lean reference, "Validating proofs" (comparator, external checkers) | keep | trust levels |
| 13 | Leray, Gilbert, Tabareau, Winterhalter, The Rewster, ITP 2024 | keep | rewrite-rule typing; §5.3 |
| 14 | Rocq refman, user rewrite rules (9.1–9.3) | keep | §5.3 |
| 15 | Agda manual, rewriting and `--confluence-check` (2.6.x–2.8) | keep | §5.3 |
| 16 | Lambdapi tooling for rewrite rules (IFIP WG 1.6 talk, 2023) | keep | external confluence tools; T7 |
| 17 | Cockx, Tabareau, Winterhalter, The Taming of the Rew, POPL 2021, classic | maybe | basis of 13–15 |
| 18 | Lean eta work: lean4#2258, #15372, #15373, arena `eta-ctor-alias`, `eta-unit-like-*` | keep | §5.4; SW-55 |
| 19 | Pujet, Tabareau, Observational Equality: Now For Good, POPL 2022 | maybe | funext and quotients by computation |
| 20 | Pujet, Tabareau, Impredicative Observational Equality, POPL 2023 | maybe | same, with impredicative SProp |
| 21 | Pujet, Tabareau, Observational Equality Meets CIC, TOPLAS 2025 | maybe | indexed families under OTT |
| 22 | Felicissimo, Tabareau, quotient inductive types in OTT, TYPES 2025 slides | maybe | D785 (recursion through quotients) |
| 23 | Danielsson, Erased Postulates, Identity Types and Quotients, arXiv 2609.08578 (2026) | keep | justifies running `J` on `Quot.sound` |
| 24 | Monnier, Normalizable types, TyDe 2024 | maybe | quotients by normal form; `Map` |
| 25 | Sterling, Angiuli, Gratzer, A Cubical Language for Bishop Sets (XTT), LMCS 2022 | drop | cubical; definitional UIP by other means |
| 26 | Altenkirch, Kaposi, Shulman et al., Higher Observational TT / Narya (talks 2024–2026) | drop | univalent; Stitchwort has K |
| 27 | Bezem, Coquand, Dybjer, Escardó, Type Theory with Explicit Universe Polymorphism, TYPES 2022 | maybe | universe polymorphism design |
| 28 | Kovács, Generalized Universe Hierarchies and First-Class Universe Levels, CSL 2022 | drop | first-class levels; far from need |
| 29 | Géran, A Canonical Form for Universe Levels in Impredicative Type Theory, CSL 2026 | keep | `imax` decision; universe polymorphism |
| 30 | Sterbac, Sterling, Fuss-free cumulative universes, arXiv 2607.11329 (2026) | maybe | cumulativity, if wanted |
| 31 | Rocq cumulative universe polymorphism, TYPES 2025 abstract 21 | maybe | not read |
| 32 | Poiret et al., sort polymorphism in Rocq (2025; slides only) | drop | not found; Stitchwort has one `Prop` |
| 33 | Sozeau et al., Correct and Complete Type Checking and Certified Erasure for Coq, in Coq, JACM 2025 | maybe | verified kernel; reference |
| 34 | Adjedj, Lennon-Bertrand, Maillard, Pédrot, Pujet, Martin-Löf à la Coq, CPP 2024 | maybe | decidable conversion, formalised |
| 35 | Lamiaux, Forster, Sozeau, Tabareau, Nested Inductive Types (RocqPL 2026; Rocq 9.2) | maybe | already Stitchwort's rule; cluster 2 |
| 36 | Rocq refman, primitive objects (integers, floats, arrays, strings) | keep | natives listed as assumptions; T6 |
| 37 | ammkrn, *Type checking in Lean 4*, "Adversarial inputs" | keep | threat model |
| 38 | nanoda_lib (Rust Lean checker) and sokonanoda (arena; closure-based conversion, smalltt-inspired) | maybe | second checker; speed |
| 39 | Blanqui, Vaishnav, Encoding Lean's Type Theory in Dedukti, arXiv 2609.24604 (ICTAC 2026) | drop | translation, not checking |
| 40 | Kovács, Staged Compilation with Two-Level Type Theory, ICFP 2022 | drop | cluster 6 if anywhere |
| 41 | Kovács, Closure-Free Functional Programming in 2LTT, ICFP 2024 | drop | cluster 6 |
| 42 | Gilbert, Cockx, Sozeau, Tabareau, Definitional Proof-Irrelevance without K, POPL 2019, classic | maybe | basis of SW-93's design |
| 43 | Abel, Coquand, Failure of Normalization in Impredicative TT with Proof-Irrelevant Equality, LMCS 2020, classic | maybe | already in proof-irrelevance.md |
| 44 | Carneiro, The Type Theory of Lean, MS thesis 2019, classic | maybe | heavily cited by 4–6 |
| 45 | Agda PR 6936, recursion on proofs in `--prop` | maybe | termination through proofs |
| 46 | Agda 2.6.4 `opaque` (2023) | drop | Stitchwort's opaque defs built |
| 47 | Danielsson, Geng, Formalization of Opaque Definitions, TyDe 2025 | drop | already used by opaque-definitions.md |
| 48 | Gratzer, Sterling, Angiuli, Coquand, Birkedal, Controlling unfolding, MSCS 2025 | drop | carded in elaboration.md |
| 49 | Sestini, Bootstrapping extensionality, thesis 2023 | drop | setoid TT; not read |
| 50 | Rebound (arXiv 2509.13261, 2025) | drop | binding library, Haskell |
| 51 | lean4#15226, `#print axioms` under-reports through a cached sentinel | keep | `stitchwort axioms`; T6 |
| 52 | Rocq CVE-2020-37268, `Print Assumptions` omission (Fedora advisory) | maybe | same class as 51; title only |
| 53 | lean4#13626, kernel assumes built-in `Bool` constructor order | keep | by-name/by-position trust |
| 54 | lean4#15706, `is_def_eq` order dependence | maybe | non-transitivity again |
| 55 | lean4#15705, recursor check skips induction hypotheses | drop | Stitchwort has no recursors |
| 56 | Rocq `SProp` and definitional UIP (refman) | maybe | already in proof-irrelevance.md |
| 57 | Idris 2 QTT core | drop | Stitchwort erases by `Prop` (DESIGN §6) |
| 58 | Lean4Lean Zulip threads ("State of the Proof", level normalisation, Sep 2025) | maybe | search summary only |

## 4. Cards

**C1. Lean kernel soundness bugs, July–October 2026.** github.com/leanprover/lean4 issues
14484, 14576, 14875, 15101, 15704, 15908; release notes 4.32.2–4.35.0. *Claim:* at least
nine routes to an axiom-free `False` in the official kernel or `leanchecker` in four
months, most found by audits with AI help (OpenAI agents for #14806 and #14807; "GPT 5.6
Sol" for #14875; a largely AI-written report for #14484) **[cited]**. *Steal:* the classes,
mapped in §5.1, and the must-reject shapes. *Helps:* DESIGN.md §13; the must-reject suite.
*Cost:* small (tests), one kernel change (T4). *Full text:* issues read in full.

**C2. Lean kernel logic renovation.** lean4#14977 (Aug 2026, with Breitner). *Claim:* to
make the kernel easier to get right and to verify, the elaborator states each inductive
type's features (impredicative, projections, eta, rule K, large elimination) as flags the
kernel only checks; recursive propositions lose large elimination; quotients of propositions
move to `Type`; "proofs never have to be reduced during type checking"; `whnf` is never
called on proofs **[cited]**. *Steal:* the large-elimination change (§5.2) and the
"features as checked flags" shape, which records.md §7.1 already takes for eta. *Helps:*
SW-93, SW-803, SW-55. *Cost:* small to kernel. *Full text:* yes.

**C3. No large elimination of recursive propositions.** lean4#13851; Felicissimo et al.,
*Definitional Proof Irrelevance Made Accessible*, LICS 2026 (hal.science/hal-05474391).
*Claim:* `Acc` in a universe with definitional proof irrelevance makes type checking
undecidable; Lean restricts recursors of recursive `Prop` types to `Prop` motives and
recovers well-founded recursion through a separate, choice-backed eliminator; the LICS paper
gives two `SProp` variants, one decidable with propositional unfolding, one with definitional
unfolding that may diverge, both consistent with canonicity **[cited: issue, talk abstract;
paper not read]**. *Steal:* one extra condition in `E-PROP-ELIM`. *Helps:* SW-93, SW-803.
*Cost:* small kernel change. *Full text:* issue yes, paper no. Deep read §5.2.

**C4. Lean Kernel Arena.** arena.lean-lang.org; github.com/leanprover/lean-kernel-arena.
*Claim:* a public bank of accept, reject and "either" inputs for Lean checkers, in groups
`bugs/` (26), `corner-cases/` (27), `tutorial/`, `perf/`, `other/`, plus mathlib-scale
corpora; about 30 checkers scored on soundness first, then completeness, then speed
**[cited]**. *Steal:* the reject shapes that make sense without universe polymorphism
(nested-unused-param, k-rec-conv, eta-ctor-alias, large-elim-prop-bool, proj-of-stuck-prop,
loose-bvar-value, nested-name-capture), and the "either" category for honest corner cases
(alg-conv-trans-*, positivity-whnf, proof-param-swap). *Helps:* must-reject suite (DESIGN
§13). *Cost:* small. *Full text:* 15 test descriptions read.

**C5. Rocq guard-checker bugs found with Claude Opus 4.6.** CVE-2026-72703 (cross-calls
between bodies of a mutual fixpoint not examined when deciding uniform parameters), 72705 (a
fixpoint passed as a higher-order argument to another fixpoint), 72704 (structure of a
recursive argument not rechecked after a transport, unfixed), 72714 (a module-local "unset
universe checking" leaves a stale flag in the universe graph, unfixed) **[cited, advisory
text; PoCs not read]**. *Steal:* each as a must-reject test against `sct.rs` and
`termination.rs`. *Helps:* termination soundness. *Cost:* small. *Full text:* advisories
only.

**C6. Stérin, In search of falsehood** (tristan.st, 5 Mar 2026). *Claim:* a team of four
Claude Code agents (mathematician, computer scientist, verification expert, devil's
advocate), given lists of earlier bugs and expert hints, found 7 proofs of `False` in Rocq
and several lesser bugs in Lean, nanoda and lean4lean in about 72 hours; it rarely raised
false alarms, and was too conservative about exploitability **[cited]**. *Steal:* the method,
pointed at `crates/core` with §5.1 as the hint list. *Helps:* DESIGN §13 assurance. *Cost:*
one lane (usage quota). *Full text:* yes.

**C7. Lean4Lean.** Carneiro, arXiv 2403.14064 (v3 Sep 2025; ITP 2024; TYPES 2025;
WITS 2026 keynote). *Claim:* a complete Lean 4 checker written in Lean, 20–50% slower than
the C++ kernel, checks all of Mathlib; parts proved correct against a formalised LeanTT;
found one soundness bug; aims to vet future kernel changes **[cited, abstract]**. *Steal:*
the idea that a second checker exists to *vet kernel changes*. Stitchwort's `reference.rs` is
a second evaluator (for `conv` and reduction), not a second checker. *Helps:* future R-rules,
SW-93, SW-55. *Cost:* research. *Full text:* no.

**C8. Lean's trust ladder: `lake check`, `comparator`, `--paranoid`, `trustCompiler`
removed.** Lean reference "Validating proofs"; 4.35.0 notes #14953, #14990, #15145.
*Claim:* `lake check` replays the environment and fails on any non-standard axiom; `--paranoid`
accepts only if every bundled checker does; `Lean.reduceBool` and the `trustCompiler` axiom
were removed because they made whole-environment axiom checks "less meaningful" **[cited]**.
*Steal:* `stitchwort axioms` should also list the trusted reduction rules and natives a
definition's checking used (Rocq's `Print Assumptions` lists primitive integers and floats
for the same reason, card C24). *Helps:* DESIGN §13 "Axiom report". *Cost:* small. *Full
text:* yes.

**C9. Lean's non-transitive cache.** Lean 4.33.1 notes, #14806; arena `proj-of-stuck-prop`.
*Claim:* the kernel cached successful `is_def_eq` answers in a union-find; algorithmic
conversion isn't transitive (proof irrelevance on `Acc`), so the closure let an agent derive
`False`; fixed with a cache keyed on the pair **[cited]**. *Steal:* a rule for any future
Stitchwort conversion cache: answers per pair, never closed under transitivity. Today's
`CallMemo` (`value.rs:2286`) only ever answers "different" and lives for one outermost `conv`
**[checked]**, so it's safe. *Helps:* SW-93, SW-55. *Cost:* a sentence in docs/core.md.
*Full text:* yes.

**C10. lean4#15908: native `Nat.add` trusted by name.** *Claim:* `reduce_nat` dispatches on
the constant's name and runs before unfolding, so an environment whose `Nat.add` is a
different, well-typed definition makes the two paths disagree: `False` with no axioms
**[cited]**. *Steal:* pin Stitchwort's Nat natives to their definitions' content hashes, as
R3 and R4 already are. *Helps:* DESIGN §13 "Native arithmetic". *Cost:* small. *Full text:*
yes. §5.1.

**C11. Rewster.** Leray, Gilbert, Tabareau, Winterhalter, ITP 2024
(doi:10.4230/LIPIcs.ITP.2024.26). *Claim:* rewrite rules in Coq with a modular criterion,
based on bidirectional typing and formalised in PCUIC, that ensures each added rule preserves
typing **[cited, abstract]**. *Steal:* the criterion's shape as the written test for any
future kernel rule (after R3/R4). *Helps:* nat-add-recursion.md §9; a future `*` rule. *Cost:*
research if adopted as a feature, small as a checklist. *Full text:* no. §5.3.

**C12. Rocq user rewrite rules (refman 9.3).** *Claim:* symbols, patterns headed by a symbol,
behind `-allow-rewrite-rules`; type preservation only superficially checked (a warning);
confluence and termination not checked; VM and native reduction switched off "since these
machines don't support untyped terms" **[cited]**. *Steal:* nothing to build; it confirms that
a general user feature is far riskier than Stitchwort's two pinned rules. *Full text:* yes.

**C13. Agda confluence checking.** agda.readthedocs.io, "Rewriting". *Claim:*
`--confluence-check` enforces joinable overlaps and the triangle property per rule;
`--local-confluence-check` checks only local confluence, equivalent when rules terminate
(which isn't checked) **[cited, search summary of the manual]**. *Steal:* the triangle
property as a second argument beside nat-add-recursion.md §9.4's critical pairs. *Cost:*
small (paper check). *Full text:* summary only **[unverified]**.

**C14. Lambdapi / Dedukti tooling.** IFIP WG 1.6 2023 talk; Genestier, HOR 2019 (classic).
*Claim:* users must ensure termination, confluence and subject reduction; Lambdapi exports
rules to the XTC and HRS formats for external confluence and termination provers, and checks
subject reduction and local confluence incrementally **[cited]**. *Steal:* write R1–R4 (and
`Nat`'s constructors) as a first-order TRS and run a confluence prover once, so §9.4's
hand-checked critical pairs have a machine check. *Helps:* SW-787 soundness section. *Cost:*
small. *Full text:* abstract.

**C15. Lean eta, 2023–2026.** lean4#2258, #15372, #15373; arena `eta-ctor-alias`,
`eta-unit-like-proof-field`. *Claim:* unit-like eta only for field-less structures makes
conversion non-transitive; the fix extends "unit-like" to structures whose fields are all
proofs or unit-like, and to functions into unit-like types; eta for partially applied
constructors needs the missing arguments from the constructor's own type, and a draft took
them from the other side's type and accepted a false equation **[cited]**. *Steal:* SW-55's
admission rule must treat a record whose fields are all proofs like one with no fields.
*Helps:* SW-55, SW-789, SW-568, with SW-93. *Cost:* design-note amendment. Deep read §5.4.

**C16. Quotients of propositions.** lean4#15023. *Claim:* `Quot` of a proposition in `Prop`
breaks transitivity of the conversion algorithm (the checker must invent a representative);
Lean moves `Quot` to `Sort (max 1 u)` **[cited]**. *Steal:* nothing: Stitchwort already
requires the carrier in `Type` (`check.rs:707-716`, "the carrier of a quotient must be a type
in `Type`") **[checked]**. Record it as a deliberate rule in docs/core.md. *Cost:* none.

**C17. Danielsson, Erased Postulates, Identity Types and Quotients.** arXiv 2609.08578 (Sep
2026). *Claim:* quotients supported by treating "related values have equal classes" as an
erased postulate, with an eliminator computing only on the class constructor; transport
along erased equality proofs preserves correct computation without quotients and postulates,
and with them implemented via equality reflection **[cited, abstract]**. *Steal:* a cited
argument for what Stitchwort's runtime already does: `J` on an erased proof (one built with
`Quot.sound`) takes its base (docs/core.md, "Running a program") **[checked]**. *Helps:*
map-equality.md §7.4.5's invariant. *Cost:* none (a citation). *Full text:* no.

**C18. Observational type theory line.** Pujet, Tabareau, POPL 2022, POPL 2023 (CCobs,
decidable conversion with impredicative `SProp`), TOPLAS 2025 (indexed inductive types, cast
computing on reflexive proofs, implemented in Coq with rewrite rules); Felicissimo, Tabareau,
QITs in OTT (TYPES 2025) **[cited, abstracts]**. *Claim:* equality that computes by type
gives funext and quotient equality definitionally, with UIP. *Steal:* not now. Stitchwort
gets funext from `Quot.sound` (std `Quot.funext`) and quotients by Lean's design; OTT would
replace `J`, K-by-matching and `Eq`'s rules at once. The QIT work is the one to watch for
D785 (types recursive through a quotient). *Cost:* research. *Full text:* no.

**C19. Monnier, Normalizable types.** TyDe 2024. *Claim:* quotients with a normal form can be
eliminated without renormalising each time, by adjusting the elimination rule **[cited]**.
*Steal:* maybe, for `Map` performance if map equality by `toList` becomes costly. *Cost:*
research. *Full text:* no.

**C20. Géran, A Canonical Form for Universe Levels in Impredicative Type Theory.** CSL 2026.
*Claim:* a canonical form for the 0-imax-successor algebra, so level equivalence and order
reduce to syntactic checks **[cited]**. Carneiro called Lean's simplifier "necessarily
incomplete" (2022) and implemented Géran's algorithm in lean4lean (Sep 2025) **[unverified:
search summary of Zulip]**; arena bugs `level-imax-leq`, `level-imax-normalization`,
`closure-level-subst`, `constlevels` are all level bugs **[cited, names]**. *Steal:* when
universe polymorphism is designed, budget the level algebra as kernel work: with an
impredicative `Prop`, the Pi rule in docs/core.md ("`s₂ = Prop` gives `Prop`") becomes `imax`
once levels are variables **[inferred]**. DESIGN.md §6 calls universe polymorphism "mostly an
elaboration feature"; Lean's record says otherwise. *Helps:* DESIGN §16 Q3; effect-polymorphism
`Row u`. *Cost:* research. *Full text:* abstract.

**C21. Universe polymorphism designs.** Bezem, Coquand, Dybjer, Escardó, TYPES 2022
(level-indexed and constraint-indexed products); Sterbac, Sterling, arXiv 2607.11329 (2026,
cumulative universes without coercion machinery, with a bidirectional elaboration algorithm
and a Haskell implementation); TYPES 2025 abstract on cumulative polymorphism in Rocq **[cited,
abstracts]**. *Steal:* inputs to the design note, when there is one. *Cost:* research. *Full
text:* no.

**C22. Verified checkers for Rocq and MLTT.** Sozeau et al., JACM 2025; Adjedj et al., CPP
2024 **[cited, abstracts]**. *Claim:* certified checkers; the JACM work found an incompleteness
in Coq's official checker. *Steal:* nothing directly; reference for what a mechanised
Stitchwort kernel would cost. *Cost:* research. *Full text:* no.

**C23. lean4#13626: kernel assumes the built-in `Bool`'s constructor order.** *Claim:* a
user `Bool` with `true` first made `reduceBool` answer wrongly **[cited]**. *Steal:* the
native registration test for shapes: `native.rs` checks `Bool`'s shape (`shape_error(…,
"Bool")`, line 329) **[checked]**; confirm it checks constructor *order*, not only count, and
add a test. *Cost:* small.

**C24. Rocq primitive objects.** rocq-prover.org refman, `language/core/primitive.html`.
*Claim:* primitive integers, floats, arrays and strings are axioms the kernel computes with;
they "must be trusted and are listed by the Print Assumptions command"; float reduction
assumes IEEE 754 hardware **[cited]**. *Steal:* list Stitchwort's trusted extras in `stitchwort
axioms` output (C8). *Cost:* small.

**C25. lean4#15226: axiom report under-reports through a cache.** *Claim:* after a change,
`#print axioms` of an imported inductive could report no axioms while its constructor
reported `Classical.choice`, through an in-progress sentinel cached across modules; the
kernel wasn't involved **[cited]**. *Steal:* a test that `stitchwort axioms` gives the same
answer with the check cache cold and warm (`crates/driver/src/axioms.rs` scans checked
terms **[checked]**; whether cached declarations are scanned the same way not checked).
*Cost:* small.

**C26. ammkrn, *Type checking in Lean 4*, "Adversarial inputs".** *Claim:* a checker
should accept only what the rules allow under the operator's allowed axioms; it doesn't
protect against sound but deceptive declarations (lookalike names, redefined dependencies)
**[cited]**. *Steal:* state Stitchwort's threat model the same way in DESIGN §13: the kernel
is the boundary against false proofs; misleading statements are the reader's problem.
*Cost:* a paragraph.

**C27. Fast independent checkers.** nanoda_lib (Rust); sokonanoda on the arena ("a
(distant) fork of nanoda", "inspired by smalltt", closures in conversion checking; Mathlib in
1.4 min against the official kernel's 32.3 min) **[cited]**. Two closure-comparison bugs
(`closure-level-subst`, `pi-closure-context`) were found in such checkers. *Steal:* if
Stitchwort compares closures structurally (`same_closure`, `value.rs`), check it compares
environments fully. *Cost:* small check. *Full text:* arena pages.

## 5. Deep reads

### 5.1 What broke real kernels in 2025–2026, and Stitchwort's exposure (C1, C4–C6, C9, C10, C23, C25)

**What happened** [cited, sources in §2]. Between July and October 2026 the Lean kernel
and its replay tool took at least nine reports that each gave an axiom-free `False`, and Rocq
took four CVEs, two still open. Discovery shifted: an OpenAI agent (#14806, #14807), a
"GPT 5.6 Sol" run (#14875), an AI-drafted report (#14484), Claude Opus 4.6 with Stérin
(Rocq 72703, 72705), and humans reviewing a too-good-to-be-true Collatz proof (#14576). Lean
answered with process: bundled independent checkers, `--paranoid`, the Kernel Arena, and the
renovation (C2).

**The classes, against `crates/core`.**

| # | Class | Example | Stitchwort today | Evidence | Action |
|---|---|---|---|---|---|
| 1 | A trusted extra keyed by name, not content | lean4#15908 (`Nat.add` native), #13626 (`Bool` order), #15704 (annotation stripping by name) | R3/R4 (`NAT_ADD_HASH`, `nat_add.rs:77`), compact text (`LIST_HASH`, `CHAR_HASH`, `chars.rs:140`) and `Float` (`FLOAT_DATA_HASH`) are pinned by hash. **Nat natives are not**: `register_native` checks type and arity (`native.rs:446-453`), called from the registry binding (`elab/src/lib.rs:2735`) | [checked] | T4: pin by hash |
| 2 | A declaration kind skips a check | #14484 (opaque body not checked for free variables) | Opaque definitions are checked like any other (docs/core.md, "Opaque definitions"); an out-of-range `Var` is `E-MALFORMED` (`check.rs:245`); `Meta` is refused | [checked] | T2: raw-kernel tests per declaration kind |
| 3 | A translation drops something from checking | #14576 / arena `nested-unused-param` (nested type's phantom parameter never checked) | Nested occurrences stay as written; the kernel doesn't translate them to a mutual group (the translation exists only in `nested_oracle.rs`, a test). A field type is checked as a type, so `Data(D, args)` checks every argument | [checked: docs/core.md "Typing", "Data types"]; that no path skips it [inferred] | T2: port the shape |
| 4 | A cache closes a non-transitive relation | #14806, arena `proj-of-stuck-prop` | No cache of "equal" answers; `CallMemo` records only "different", per outermost `conv`, keyed by pointers whose values it holds | [checked: `value.rs:2259-2330`] | Write the rule into docs/core.md (C9) |
| 5 | Prop-ness decided on a stuck type | #14807 (`is_prop` on a stuck type) | Sorts are concrete (no universe variables); `E-PROP-ELIM` reads `field_sorts` fixed at declaration (`check.rs:923-929`) | [checked] | none |
| 6 | Large elimination misclassified | arena `large-elim-param`, `large-elim-prop-bool` | Rule in `check.rs:915-929`; must-reject tests for `p ∨ q`, `∃`, `HiddenType` exist (DESIGN §13). Recursive single propositions **are** allowed (§5.2) | [checked] | T3 |
| 7 | Termination across mutual or higher-order calls | Rocq 72703 (cross-calls), 72705 (fixpoint passed to a fixpoint), 72704 (after a transport) | Size change over the closure of the whole group's call graphs (`sct.rs`); every occurrence of a member must be saturated, a bare one refused; `J` results are "unknown"; recursive fields read from the declared field type (docs/core.md "Definitions" 4, "Termination") | [checked: docs] | T2: port the three shapes |
| 8 | A stale mode or flag | Rocq 72714 (universe checking left off after a module) | Modes (natives, compact text, glue) live in `Globals`; glue is turned on only around a body check (`admit_group`). No user-visible switch weakens a check [inferred] | partly [checked] | T1 hint |
| 9 | A replay or cache that trusts its input | #15101/#15100 (`leanchecker` trusts entry kinds and names); Lean's `.olean` trust | The check cache is trusted by design (DESIGN §11, `admit_trusted_*`, `check.rs:2392-2502`), checking only state and shape; `--no-cache` re-checks | [checked] | none now; a `--paranoid`-style "re-check and compare hashes" is cheap later |
| 10 | Axiom reporting gaps | #15226 (cached under-report), Rocq CVE-2020-37268 | `stitchwort axioms` scans checked terms for `Quot.sound` (`driver/src/axioms.rs:19-52`); trusted rules and natives aren't listed | [checked] | T6 |

Memory and size bugs (Lean #14838 refcount overflow, #14849 128 MB numerals, #14833 GMP
before 6.3.0) have weak Stitchwort analogues: Rust's `Rc` aborts on count overflow, and
numbers use `num-bigint` 0.5 (pure Rust, `Cargo.lock`) **[checked]**; whether a huge numeral
is bounded by `budget.rs` wasn't checked.

**Mapping summary.** Classes 2–5 are closed by how the kernel is built; 6 and 7 are covered by
design and partly by tests; 1 and 10 are real but small. The bigger lesson is class
*discovery*: every class above was found by someone looking for `False`, and Stitchwort's
kernel fuzzer looks only for panics (`crates/core/tests/fuzz.rs:1-3`) **[checked]**.

**Risks of acting.** An audit lane costs usage quota and may report "unexploitable" findings
that need a human to judge; Stérin found it conservative, not noisy **[cited]**. Pinning
natives by hash means a prelude change to `Nat.add` silently turns the native off (as it does
for R3/R4 today): tests must catch it, as `nat_add_rule.rs` does for R3/R4 **[inferred]**.

**Next step.** T2 (port the shapes, a day's work), then T1 (one audit lane with this table as
hints), then T4 and T6.

### 5.2 No large elimination from recursive propositions (C2, C3)

**What Lean does** [cited, lean4#13851 and #14977]. `elim_only_at_universe_zero` now returns
true for any recursive inductive, so `Acc.rec` and other recursors of recursive `Prop` types
only produce proofs. Non-recursive one-constructor propositions (`Eq`, `And`, `Iff`, `True`)
keep large elimination. Well-founded recursion was rebuilt first (#14892) on `Acc.rec'`,
backed by `Classical.choice`, without an iota rule. The stated motivation: "the kernel never
has to look at a proof term of a `Prop`", which makes external checkers and proof omission in
the module system reliable, and removes "a source of undecidability for definitional
equality". Four old kernel regression tests were dropped because their exploits needed
`Acc.rec` at a `Bool` motive.

**The theory** [cited, talk abstract of Felicissimo et al., LICS 2026]. Accessibility in a
universe with definitional proof irrelevance gives undecidable type checking. Two variants
in `SProp`: unfolding only propositionally (decidable), or definitionally (may diverge); a
translation from the second into the first; both consistent with canonicity.

**Stitchwort today** [checked]. The rule (`check.rs:923-929`) allows large elimination when
the proposition is alone in its group, has no nested field, has at most one constructor, and
all its fields are proofs. It doesn't ask whether a field mentions the type itself.
proof-irrelevance.md §5.1 shows `type Loop: Prop = | MkLoop (next: Loop)` with `steps: Loop
-> Nat -> Bool` is accepted **[run, per that note]**, and explains that full proof
irrelevance would make conversion undecidable through it (Carneiro's argument). `Acc` itself
is refused for another reason (non-uniform parameter). The note's answer is to make D1′
incomplete on purpose (it masks only proof positions, never two bare proof variables).

**Mapping.** Add a fifth condition: no field type of the constructor mentions `D`. With it,
Carneiro's construction has no starting point in Stitchwort, independently of how SW-93 is
built; proof-irrelevance.md §5.1 becomes a closed risk rather than an argued one, and SW-803
(a fuller rule) is safer to consider later. Well-founded recursion is unaffected: `decreasing`
uses measures, not `Acc` (well-founded-recursion.md) **[checked: no `Acc` type in
`crates/elab/src/std`]**.

**Assumptions the recommendation depends on.** (A1) No library or AoC code eliminates a
recursive proposition into data. Not checked; T3 measures it first. (A2) A recursive
proposition matched to produce *proofs* stays allowed (the restriction is on the goal's sort
only), so induction over such propositions is untouched. (A3) The restriction only rejects
programs, so it can't make anything unsound. That holds because it only adds a refusal
**[inferred]**.

**Risks.** A user who wanted `Loop`-style recursion into data loses it; they can move the
type to `Type` (it's then data, not erased). Hashes don't change for accepted programs.

**Next step.** T3: measure on std, examples, aoc, rogue; then decide (D1891).

### 5.3 Rewrite rules: what others check, and R3/R4 (C11–C14)

**What others do** [cited]. Rocq 9.x: user symbols and rules behind a flag; type
preservation only warned about; confluence and termination unchecked; VM and native compilers
turned off. The Rewster (ITP 2024) supplies a modular typing criterion, formalised in PCUIC.
Agda: `--rewriting` with an optional confluence check (joinable overlaps plus the triangle
property; termination unchecked). Lambdapi: users responsible; tools export to XTC/HRS for
external confluence and termination provers and check subject reduction automatically.

**Stitchwort** [checked: DESIGN §13, nat-add-recursion.md §9]. Exactly two rules, R3 and R4,
built into both evaluators at one place, pinned to the library's `Nat.add` by hash, with the
equations proved as `Nat.addZero` and `Nat.addSucc` and checked when they're bound. The
soundness argument is typing, four critical pairs joined by hand, and termination of the rules
alone; strong normalisation of the whole core with them is "expected, not proved".

**Mapping.** Stitchwort already does more than Rocq and Agda check for user rules: the rules
are *derivable* (their equations are theorems), which is the strongest form of the Rewster's
type-preservation condition **[inferred]**. Two cheap additions: (1) run the critical pairs
through a confluence prover (R1–R4 over `Zero`, `Succ`, `add` as a first-order TRS, the
format Lambdapi exports to), and record the tool's answer in §9.4; (2) write down, before any
third rule (a `*` rule was deferred in SW-787), the checklist the next rule must pass:
derivable equation, left-linear constructor patterns, joinable critical pairs with every
existing rule (including natives and compact text), and the triangle property if termination
can't be shown. A general user-rule feature isn't recommended: Rocq's manual shows what it
costs (untyped terms, switched-off machines) **[cited]**.

**Assumptions.** That no third rule is planned soon (SW-787's note says `*` is "no for now");
that SW-896 (inverting R4 in unification) stays in the untrusted elaborator, so it needs no
kernel criterion **[checked: SW-896 text]**.

**Next step.** T7 (small).

### 5.4 Record eta meets proof irrelevance (C15, C2)

**What Lean found** [cited]. With eta for structures and irrelevance for proofs, the
algorithm can show `p ≡ ⟨()⟩` and `q ≡ ⟨()⟩` but not `p ≡ q` when the structure's only
field is a proof, so conversion isn't transitive (arena `eta-unit-like-proof-field`). The fix
(lean4#15372, merged per #14977's checklist) widens "unit-like" to structures whose fields
are all proofs or unit-like, and to functions into unit-like types. A second lesson: eta for a
partially applied constructor must take the missing arguments from the constructor's own type
(the `eta-ctor-alias` draft bug). Lean's renovation also fixes eta to non-recursive
structures, decided once at declaration.

**Stitchwort's plan** [checked: records.md §7.1, §7.3]. Eta is a declared mode, validated at
admission: one constructor, no indices, in `Type`, non-recursive, **at least one field**. Two
rules: one-sided eta (`Ctor(D, 0, fs) ≡ n` when `fs[i] ≡ Proj(D, i, n)`) and a case on a
neutral eta record takes its branch. Zero-field records get no eta because "any two values
are equal" needs types the untyped `conv` doesn't have. SW-93's D1′ skips proof positions
when comparing two constructors (proof-irrelevance.md §7.2).

**Mapping.** Take `type R = { h: P }` with `P: Prop`, after both SW-93 and SW-55. For
neutral `x, y: R`: `x ≡ MkR x.h` (one-sided eta), `MkR x.h ≡ MkR y.h` (D1′ masks the proof
field), `MkR y.h ≡ y` (eta), but `x ≡ y` fails: both are neutral, and neither rule fires
**[inferred]**. That's the same non-transitivity Lean hit. It isn't unsound by itself (D1′'s
argument in proof-irrelevance.md §5.6 still applies), but it makes `rfl` succeed or fail with
the shape of a term, and it's the precondition for class 4 in §5.1 if a cache ever appears.
The simplest fix in Stitchwort's untyped setting is to extend condition 4: eta needs at least
one field that isn't a proof. Lean's alternative (a typed unit-like rule) needs the types of
neutrals, which `conv` doesn't have (records.md §7.1).

**Assumptions.** That SW-93 is built as D1′ (masks on constructor fields); that SW-55 keeps
records.md's untyped one-sided rule. If SW-93 isn't built, the case doesn't arise.

**Next step.** T5: a two-line amendment to records.md §7.1 and a test.

## 6. Steal next

Ranked by value over effort.

| Rank | Idea | Source | Helps | Cost |
|---|---|---|---|---|
| 1 | Port the 2026 bug shapes (Lean, Rocq, Arena) as must-reject kernel tests | C1, C4, C5 | DESIGN §13 | small (tests) |
| 2 | One adversarial audit lane on `crates/core` with §5.1 as hints | C6 | soundness assurance | one lane |
| 3 | No large elimination from recursive propositions | C2, C3 | SW-93, SW-803 | small kernel change (measure first) |
| 4 | Pin Nat natives to their definitions' content hashes | C10, C23 | trusted base | small kernel change |
| 5 | Eta only for records with a non-proof field (with SW-93) | C15 | SW-55, 789, 568 | design-note amendment |
| 6 | `stitchwort axioms` lists the trusted rules and natives used; same answer cold and warm | C8, C24, C25 | DESIGN §13 axiom report | small |
| 7 | Machine-check R1–R4 confluence; write the checklist for a third rule | C11–C14 | SW-787 follow-ups | small |
| 8 | Write "no transitive closure in any conversion cache" and "quotient carriers are in `Type`" into docs/core.md | C9, C16 | future work | a few sentences |
| 9 | Universe polymorphism: treat the level algebra (`imax`) as kernel work in the eventual note | C20, C21 | DESIGN §16 Q3 | research |
| 10 | Observational equality / QITs for funext and recursion through quotients | C18, C22 | D785 | research, not now |

## 7. Proposed tickets

Label `research` on each. Not added to the board.

**T1. Adversarial kernel audit lane.** One lane, Stérin's method: agents given
docs/core.md, DESIGN §13, `crates/core` and the bug classes of docs/research/kernel.md §5.1
as hints, asked for a checked term of `Void` (or any false equation) through the kernel's
public API or a `.sw` file, with no `assume`. Output: a list of candidate exploits, each run,
plus must-reject tests for anything real. No kernel changes in the lane. Refs: §5.1, C6.

**T2. Must-reject tests from the 2026 kernel bugs.** Hand-built kernel terms and `.sw` files
for: a nested occurrence whose phantom parameter is ill-typed (arena `nested-unused-param`);
an opaque definition whose body has an out-of-scope variable; mutual recursion where a
parameter changes only across cross-calls (Rocq 72703); a recursive function passed as a
higher-order argument to another member (Rocq 72705); a recursive call on a value transported
by `J` (Rocq 72704); a `Prop` with two constructors eliminated into `Bool` by a hand-built
`Case` (arena `large-elim-prop-bool`); a user `Bool` with constructors in the other order at
native registration (lean4#13626). Each paired with an accepted neighbour, per DESIGN §13.
Refs: §5.1.

**T3. Measure: no large elimination from recursive propositions.** Add, behind a throwaway
switch, the condition "no field of the constructor mentions `D`" to `E-PROP-ELIM`
(`check.rs:923`); run std, examples, aoc and rogue; list every rejection. If none, propose the
rule (with proof-irrelevance.md §5.1's `Loop`/`steps` as the must-reject test and a
recursive proposition matched into a proof as the accepted neighbour). Lean made this change
in 2026 (lean4#13851). Refs: §5.2; SW-93, SW-803.

**T4. Pin the Nat natives to their definitions by content hash.** `register_native`
(`native.rs:378`) checks only type and arity; R3/R4, compact text and `Float` check content
hashes. Store the expected hash per native (as `NAT_ADD_HASH`), refuse to register on a
mismatch, and test that a modified definition runs without its native. Lean's lean4#15908 is
this bug in Lean. Refs: §5.1 class 1.

**T5. records.md §7.1: eta needs a field that isn't a proof.** After SW-93 (D1′), eta for a
record whose fields are all proofs makes conversion non-transitive (§5.4). Amend condition 4
and add the test `x ≡ y` for neutral `x, y: R` with `R = { h: P }` (refused, with eta also
refused for `R`). Refs: §5.4; SW-55, SW-93.

**T6. `stitchwort axioms`: report trusted extras, and test it against the cache.** Besides
`Quot.sound`, list the trusted kernel extras a definition's checking can rely on (Nat natives,
R3/R4, compact text, `Float` primitives) in a separate section, as Rocq's `Print Assumptions`
lists primitive types and Lean removed `trustCompiler` to keep axiom checks meaningful. Add a
test that the report is the same with the check cache cold and warm (lean4#15226). Refs: C8,
C24, C25.

**T7. Machine-check R3/R4 and write the third-rule checklist.** Encode R1–R4 over `Zero`,
`Succ`, `add` as a first-order TRS, run a confluence prover (CSI or similar), and record the
result in nat-add-recursion.md §9.4. Add a short "what a new kernel rule must satisfy" list
(derivable equation, left-linear constructor patterns, critical pairs with every rule and
native, termination or the triangle property, pinned by hash). Refs: §5.3.

## 8. Decisions

**D1891. Remove large elimination from recursive propositions (T3) before SW-93 is built?**
Assumption: T3's measurement finds no use in std, examples, aoc or rogue (A1 in §5.2). It
only rejects programs, so it can't make anything unsound. [Yes, if the measurement is clean.]

**D1892. Spend one lane on an adversarial kernel audit (T1) after T2's tests land?**
Assumption: the usage quota allows it (check `~/.claude/state/usage.json`); the 2026 record
suggests such audits find real bugs in mature kernels, and Stitchwort's fuzzers look only for
panics. [Yes, one lane, after T2.]

**D1893. For SW-55, refuse eta for records whose fields are all proofs (T5), rather than
adding Lean's typed unit-like rule?** Assumption: SW-93 is built as D1′; `conv` stays untyped.
[Yes.]

## 9. Sources not reached

- PDFs couldn't be read here: no PDF text tool was available locally, and HAL pages returned
  a bot check (Anubis). So these were read as abstracts or talk pages only: Felicissimo et
  al. LICS 2026 (hal-05474391), Lamiaux et al. (hal-05366368), Lean4Lean TYPES 2025, the
  Rewster, Pujet and Tabareau's three OTT papers, TYPES 2025 abstract 21 (Rocq cumulative
  universes), Géran CSL 2026, Sterbac and Sterling 2026, Danielsson 2026.
- The Rocq sort-polymorphism paper (Poiret et al., 2025) wasn't found; only slides mention it.
- Rocq's `dev/doc/critical-bugs` file wasn't fetched; the Rocq CVEs were read through
  oss-security advisories, whose dates are inconsistent (noted by the fetch) and whose PoCs
  weren't run or read.
- Lean 4.35.0 release notes: the last 3% of the page wasn't read.
- Zulip: no thread was opened directly (lean4lean level normalisation, "Definitional
  well-founded recursion", the mini-kernel T-shirt bounty); claims from them are marked
  [unverified]. Blogs of Kovács, Cockx, Pujet and Sterling: no 2022+ posts on these topics
  turned up in search; Cockx's 2019 rewrite-rules post is out of window.
- Agda: the changelogs for 2.7 and 2.8 weren't read beyond search summaries; the confluence
  check's exact flags in 2.8 are [unverified].
- Not searched year by year: CPP, ITP, FSCD, LICS and TYPES programmes; LFMTP; Lean
  workshop programmes; Andromeda 2, cooltt and Idris 2 changelogs. A refresh should start
  with the Kernel Arena's `bugs/` directory and the Lean and Rocq issue trackers (Q10, Q11),
  which moved fastest.
