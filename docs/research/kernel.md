# Literature trawl: kernel and type theory

**Counts: screened 62; carded 27; read in full 26; not read 1 (C27; listed in §9).**

Redone 30 Oct 2026 from full texts; replaces the 29 Oct abstract-based version.

**Claims from the 29 Oct version found wrong** (each checked against the full source or our
code this time):

1. *"No cache of 'equal' answers; `CallMemo` records only 'different'"* (old §5.1, class 4).
   Wrong: `same_stuck_trees` keeps a record of pairs of calls **found equal** within one
   outermost comparison (SW-395; `crates/core/src/value.rs:2711`, the comment at
   `value.rs:2779-2822`, `known_equal` at `value.rs:2895`). The old conclusion still holds for
   a different reason: a remembered pair is reused only for an *identical* pair
   (`identical`, no evaluation), so no transitive closure is ever taken. That is exactly the
   fix Lean adopted in lean4#14806 (C21).
2. *Stérin "found 7 proofs of `False` in Rocq and several lesser bugs in Lean, nanoda and
   lean4lean"* (old C6). Wrong: the post's table gives proofs of `False` in **nanoda (2) and
   lean4lean (1)**, none in the official Lean kernel (4 other bugs there), and 7 proofs plus 3
   other bugs in Rocq (C25).
3. *"Lean is removing it (lean4#13851) because it makes definitional equality undecidable"*
   (old §1). Misattributed: #13851 gives as its motivation "to ensure the kernel never has to
   look at a proof term of a `Prop`" so external checkers can drop proof subterms. The
   undecidability reason is in #14977, which cites Felicissimo et al. for it (C20, C23).
4. *The LICS 2026 paper's two variants are "both consistent with canonicity"* (old C3).
   Imprecise: the variant with propositional unfolding "breaks the usual statement of
   canonicity" and gets only *propositional* canonicity. Only the definitional variant has
   canonicity (C1, §1).
5. *R3/R4's derivable equations are "the strongest form of the Rewster's type-preservation
   condition"* (old §5.3). Overstated: the Rewster calls "the equality … well typed when
   universally quantified" the *naive* criterion and shows it unsound under cumulativity
   (Example 1). It is adequate for R3/R4 only because Stitchwort has no cumulativity and the
   rules are first-order on `Nat` **[inferred]** (C8, §5.3).
6. The old version marked the sort-polymorphism paper "not found" (old row 32). The paper
   (Rosain et al., POPL 2026) is open on HAL and was read this time (C12).

The four errors SW-897 lesson 7 lists (Géran on Lean's level normaliser; "quality variables";
definitional inversion "about Lean with quotients"; MetaCoq "found a soundness bug") were
checked against the papers again and are wrong as stated. In the 29 Oct file on `main`,
though, they appear only in weaker forms: old C20 labelled the Lean4Lean remark **[unverified]**,
and Lean4Lean's TYPES 2025 paper in fact mentions "an experimental complete level equality
algorithm following" Géran (C4). Old C22 correctly said "incompleteness". "Quality variables"
appears only in query Q18, and the definitional-inversion paper wasn't carded. So they came
from the stopped redo's leads, not from this file.

*SW-894, cluster 1. Researched 30 October 2026 against `main` at `97399adf`. Research only: no
code changed, no tests run. Window: 2022 onwards (D1831). Older work appears only where
in-window work or our own notes rely on it, and is marked **classic**.*

Reading protocol: every card says **Full text: read (source)** or **NOT READ**. PDFs were read
with `pdftotext` from `nix shell nixpkgs#poppler-utils`. GitHub issues, PRs and repository
files were read in full through `gh` (no summarising tool). Blog posts and mailing-list
advisories were downloaded with `curl` and read as text. For a long theory paper, "read" means
the prose, definitions, examples, evaluation and conclusions were read in full and the proof
sections skimmed. Each card names the sections read. A NOT READ card supports no ranking, deep
read or recommendation. The 14 helper cards of the stopped redo were used only as a reading
guide; no claim here comes from them.

Labels: **[checked]** read in the full text of the named source, or in Stitchwort's code or
docs at the place given; **[inferred]** my reasoning, not tested; **[unverified]** not
confirmed in a full source (context only, never support for a recommendation).

## Contents

1. [Summary](#1-summary)
2. [Method](#2-method)
3. [Screened list](#3-screened-list)
4. [Cards](#4-cards)
5. [Deep reads](#5-deep-reads)
6. [Steal next](#6-steal-next)
7. [Proposed tickets](#7-proposed-tickets)
8. [Decisions](#8-decisions)
9. [Sources not reached](#9-sources-not-reached)

## 1. Summary

Stitchwort's kernel already has the shape that Lean's 2026 "kernel logic renovation" (C20) is
moving towards. Features are fixed when a declaration is admitted, the kernel has no
universe variables, and the conversion memo tables are keyed by exact pairs. The literature
read this time gives five things worth acting on, all small:

- **Proof irrelevance (SW-93, SW-803): close the recursive-proposition hole first.** Gilbert
  et al. (C2), Felicissimo et al. (C1), Abel and Coquand (C3) and Lean's #13851/#14977 agree on
  one point. A proposition that can be eliminated into data and refers to itself in a field
  (`Acc`, and Stitchwort's `Loop`) makes conversion undecidable once proofs are definitionally
  irrelevant. Stitchwort's `E-PROP-ELIM` accepts `Loop` today (`check.rs:915-929`;
  proof-irrelevance.md §5.1). Rocq's way of implementing irrelevance in an *untyped*
  conversion is relevance marks, the same idea as SW-93's D1′ masks. Rocq calls it "cheap yet
  complete" (C2 §6.1.1, C6 §4.4). §5.1, T2, D1980.
- **Record eta (SW-55, SW-789) must exclude records whose fields are all proofs once SW-93
  lands.** Rocq forbids this case for exactly this reason (C12 §6, C6 §4.4). Lean's kernel
  hit the same non-transitivity (C24, Arena `eta-unit-like-proof-field`). records.md §7.1
  condition 4 asks only for "at least one field". §5.2, T3, D1981.
- **R3/R4 (SW-787) have a published confluence argument that needs no termination.** The
  Taming of the Rew uses Stitchwort's exact four rules as its example. It shows that they
  satisfy the triangle property once a fifth, "parallel" rule is added (C9 Example 4.3), and
  that the triangle property gives confluence without normalisation. nat-add-recursion.md
  §9.4 currently rests on Newman's lemma plus citations marked **[unverified]**. §5.3, T4.
- **Bug shapes from 2026 to port as must-reject tests.** These are the Rocq guard-checker CVEs
  (C26), Lean's order-dependent cache (C21) and name-trusted `Nat.add` (C22), and the Arena's
  forged `Quot.ind` (C24). Most can't arise in Stitchwort by construction. One gap is real but
  small: the Nat natives are bound by name and checked by type only (`native.rs:379-455`).
  This is the configuration Lean4Lean's paper calls "technically unsound" (C4, footnote 18).
  §5.4, T1, T5.
- **Quotients and erasure: an external theorem for an internal invariant.** Danielsson
  (2026, C19) proves, in Agda, that with quotients and transport along erased equality proofs,
  closed programs compute the right numeral even where source-level reduction gets stuck.
  That is map-equality.md §7.4.5's "intended invariant". The assumptions differ, and §5.5
  lists them. T6.

Not recommended now: observational equality (C16, C18), universe polymorphism and
cumulativity (C12-C15), a concurrent convertibility checker (C7). Each is sound research
that no open ticket needs.

## 2. Method

**Stitchwort read first** [checked]: docs/core.md (all); `crates/core/src/check.rs` (the
`Case` and `E-PROP-ELIM` code, `Var` checking), `value.rs` (`conv`, `CallMemo`,
`same_stuck_trees`, `same_closure`, eta for functions), `native.rs` (registration),
`nat_add.rs` (header and binding), `registry.rs` (binding by name); `crates/elab/src/lib.rs`
(builtin binding); docs/proposals/proof-irrelevance.md (§0, §5.1, §7.4), records.md (§7.1,
§7.3), nat-add-recursion.md (§9.4, §9.5), map-equality.md (§7.4.4, §7.4.5, §9.1, §9.2); board
SW-93, 803, 55, 789, 568, 787, 684-689. Every `file:line` below was opened.

**Sources.** 29 PDFs already in `~/stitchwort-papers/` (extracted text; two-column files
re-extracted where garbled). One new PDF (Courant and Leroy, arXiv 2510.18418v2) was
downloaded to the session scratchpad. GitHub: lean4 issues and PRs #13851, #14484 (title
only), #14806, #14977, #15372 (title and state), #15908, and the `leanprover/lean-kernel-arena`
README plus four test descriptions, all through `gh`. Blog: tristan.st "In search of
falsehood" (curl). Advisories: oss-security 2026/q4/381 and /383 (curl).

**Web searches: 5** (of a budget of about 25), all on 30 Oct 2026:

| # | Query | Useful result |
|---|---|---|
| S1 | `hash-consing sharing conversion checking dependent type theory kernel paper 2023 2024 2025` | Courant and Leroy (lead); Rocq `HConstr`; arXiv 2401.02948 |
| S2 | `"A Lazy, Concurrent Convertibility Checker" arXiv` | arXiv 2510.18418, POPL 2026 |
| S3 | `Stérin "In search of falsehood" Rocq proofs of False Claude agents 2026` | URL of the post (tristan.st itself returned an empty page to WebFetch; curl worked) |
| S4 | `Agda Core typechecker formalised paper Liesnikov Cockx 2025` | APLAS 2024 paper (C27, not reachable) |
| S5 | `differential testing proof assistant kernels soundness bugs paper 2025 2026 arXiv type checker fuzzing` | oss-security advisories for CVE-2026-72703 and 72705; no paper |

Searches returned results every time. I stopped at five because the leads already in hand
covered the scope. Areas only lightly covered as a result: Agda and Idris kernels (no
in-window paper read), small trusted kernels as a topic, and hash-consing beyond C7.

## 3. Screened list

62 sources: 27 carded (26 read, 1 NOT READ), 15 maybe, 20 drop. A "maybe" or "drop" was
judged on title, abstract or a partial read, and supports nothing below.

| # | Source | Verdict | Why |
|---|---|---|---|
| 1 | Felicissimo, Leray, Pujet, Tabareau, Tanter, Winterhalter, Definitional Proof Irrelevance Made Accessible, LICS 2026 | card C1 | §5.1 |
| 2 | Gilbert, Cockx, Sozeau, Tabareau, Definitional Proof-Irrelevance without K, POPL 2019, classic | card C2 | §5.1 |
| 3 | Abel, Coquand, Failure of Normalization in Impredicative TT with Proof-Irrelevant Equality, LMCS 2020, classic | card C3 | §5.1 |
| 4 | Carneiro, Lean4Lean, TYPES 2025 | card C4 | §5.4 |
| 5 | Sozeau et al., Correct and Complete Type Checking and Certified Erasure for Coq, in Coq, JACM 2025 | card C5 | re-checkers |
| 6 | Lennon-Bertrand, What does it take to certify a conversion checker?, FSCD 2025 (arXiv v3 2026) | card C6 | §5.2 |
| 7 | Courant, Leroy, A Lazy, Concurrent Convertibility Checker, POPL 2026 | card C7 | conversion, sharing |
| 8 | Leray, Gilbert, Tabareau, Winterhalter, The Rewster (JAR 2026, extended ITP 2024) | card C8 | §5.3 |
| 9 | Cockx, Tabareau, Winterhalter, The Taming of the Rew, POPL 2021, classic | card C9 | §5.3 |
| 10 | Felicissimo, Winterhalter, Confluence Techniques for DTT with Typed Conversion, ICFP 2026 | card C10 | conversion theory |
| 11 | Carneiro, Coquand, Frabetti Mathieu, Lennon-Bertrand, Melliès, Weirich, Definitional Inversion, Without Normalisation, arXiv 2026 | card C11 | metatheory |
| 12 | Rosain et al., Bounded Sort Polymorphism with Elimination Constraints, POPL 2026 | card C12 | §5.2 |
| 13 | Géran, A Canonical Form for Universe Levels in Impredicative Type Theory, CSL 2026 | card C13 | universes |
| 14 | Bezem, Coquand, Dybjer, Escardó, Type Theory with Explicit Universe Polymorphism, TYPES 2022 | card C14 | universes |
| 15 | Sterbac, Sterling, Fuss-free cumulative universes, arXiv 2607.11329 (2026) | card C15 | universes |
| 16 | Pujet, Tabareau, Observational Equality: Now for Good, POPL 2022 | card C16 | quotients, funext |
| 17 | Adjedj et al., Martin-Löf à la Coq, CPP 2024 | card C17 | re-checkers |
| 18 | Pujet, Leray, Tabareau, Observational Equality Meets CIC, TOPLAS 2025 | card C18 | OTT and indices |
| 19 | Danielsson, Erased Postulates, Identity Types and Quotients, arXiv 2609.08578 (2026) | card C19 | §5.5 |
| 20 | Breitner, Adjedj, lean4#14977, kernel logic renovation (Aug 2026) | card C20 | §5.1, §5.4 |
| 21 | lean4#14806, order-independent `is_def_eq` cache (Aug 2026) | card C21 | §5.4 |
| 22 | lean4#15908, native `Nat.add` trusted by name (Oct 2026) | card C22 | §5.4 |
| 23 | lean4#13851, no large elimination of recursive `Prop` inductives | card C23 | §5.1 |
| 24 | Lean Kernel Arena (README; tests `eta-unit-like-proof-field`, `alg-conv-trans-quot`, `forged-quot-ind`, `k-rec-conv`) | card C24 | §5.2, §5.4 |
| 25 | Stérin, In search of falsehood (blog, 5 Mar 2026) | card C25 | §5.4 |
| 26 | Rocq CVE-2026-72703 and CVE-2026-72705 (oss-security advisories, Oct 2026) | card C26 | §5.4 |
| 27 | Liesnikov, Cockx, Building a Correct-by-Construction Type Checker for a Dependently Typed Core Language (Agda Core), APLAS 2024 | card C27, NOT READ | small kernels |
| 28 | Leray et al., The Rewster, ITP 2024 | maybe | superseded by row 8 |
| 29 | Pujet, Tabareau, Impredicative Observational Equality, POPL 2023 | maybe | abstract and §7 only read |
| 30 | Pujet, Tabareau, Observational Equality Meets CIC, ESOP 2024 | maybe | superseded by row 18 |
| 31 | Pujet, Computing with Extensionality Principles in Type Theory, thesis 2022 | maybe | covers rows 16, 29 |
| 32 | Carneiro, Lean4Lean, arXiv 2403.14064 (earlier version) | maybe | superseded by row 4 |
| 33 | Jiang, Hu, Contravariant Universe Subtyping, Formalized, Mechanized, arXiv 2610.14925 | maybe | cumulativity; Stitchwort has none |
| 34 | Hashing Modulo Context-Sensitive α-Equivalence, arXiv 2401.02948 | maybe | hash-consing; search summary only |
| 35 | Rocq kernel `HConstr` (hash-consed terms as cache keys), Rocq 9 API docs | maybe | search summary only |
| 36 | lean4#15372, extend unit-like criteria for eta (merged) | maybe | title and state checked; content via C24 |
| 37 | lean4#15023, quotients of propositions in `Type` | maybe | listed in C20's checklist only |
| 38 | lean4#15226, `#print axioms` under-reports through a cache | maybe | not re-read |
| 39 | lean4#13626, kernel assumes built-in `Bool` order | maybe | not re-read |
| 40 | Rocq CVE-2026-72704 and 72714 | maybe | not re-read |
| 41 | Lean 4.35 `lake check --paranoid`, bundled checkers, `con-leche` | maybe | search summary only |
| 42 | ammkrn, *Type checking in Lean 4*, "Adversarial inputs" | maybe | not re-read |
| 43 | Bezem, Coquand, Dybjer, Escardó, A GAT for TT with Explicit Universe Polymorphism, EPTCS 441 (2026) | drop | semantics of row 14 |
| 44 | Kapulkin, Li, Extensional concepts in intensional type theory, revisited, arXiv 2310.05706 | drop | semantics |
| 45 | Park, Global Choice without Excluded Middle in DTT, arXiv 2610.37498 | drop | logic, not kernels |
| 46 | Blanqui, Vaishnav, Encoding Lean's Type Theory in Dedukti, arXiv 2609.24604 | drop | translation |
| 47 | Sharing Proofs with Predicative Theories through Universe-Polymorphic Elaboration, LMCS 20(3) 2024 | drop | translation |
| 48 | Monnier, Normalizable types, TyDe 2024 | drop | quotients by normal form; not needed |
| 49 | Kovács, Generalized Universe Hierarchies, CSL 2022 | drop | first-class levels |
| 50 | Sterling, Angiuli, Gratzer, XTT, LMCS 2022 | drop | cubical |
| 51 | Higher Observational TT / Narya (talks) | drop | univalent; Stitchwort has K |
| 52 | Kovács, 2LTT staging, ICFP 2022 and 2024 | drop | cluster 6 |
| 53 | Danielsson, Geng, Formalization of Opaque Definitions, TyDe 2025 | drop | already used by opaque-definitions.md |
| 54 | Gratzer et al., Controlling unfolding, MSCS 2025 | drop | elaboration cluster |
| 55 | Lamiaux, Forster, Sozeau, Tabareau, Nested Inductive Types, PLDI 2026 | drop | nested-data-types.md covers it |
| 56 | Agda 2.6.4 `opaque`; Agda PR 6936 (recursion on proofs) | drop | built, or not needed |
| 57 | Idris 2 QTT core | drop | Stitchwort erases by `Prop` |
| 58 | Lambdapi rewrite-rule tooling (talk) | drop | C8, C9 cover the criterion |
| 59 | Agda and Rocq manuals on rewrite rules | drop | C8, C9 cover them |
| 60 | Rocq primitive objects (refman) | drop | not re-read |
| 61 | Carneiro, The Type Theory of Lean, MS thesis 2019, classic | drop | cited by C1-C4 for the `Acc` argument; not re-read |
| 62 | Hales guest post on Lean's summer 2026 bugs (secondary aggregator) | drop | secondary |

## 4. Cards

**C1. Felicissimo, Leray, Pujet, Tabareau, Tanter, Winterhalter, Definitional Proof
Irrelevance Made Accessible** (LICS 2026; hal.science/hal-05474391v4). *Claim:* the
subsingleton criterion ("introduced in Coq 7.3 in 2002") works safely in `SProp` only for
`False`. For `Eq`, Lean's strong `J` "breaks canonicity in the presence of function
extensionality … and proof normalization in the presence of impredicativity". "Elimination
of `Acc` breaks decidability of conversion regardless of function extensionality or
(im)predicativity". Lean keeps the full criterion with a heartbeat bound, so "definitional
equality becomes different from its specification (e.g., it is no longer transitive)". It
also "makes all well-foundedness proofs opaque by default since v4.19". The paper extends
CIC^obs with `Acc` in `SProp` in two theories. T=Acc has the computation rule only as a
propositional equality: decidable, but with only propositional canonicity. T≡Acc has it
definitionally: undecidable, with canonicity. Theorem 16: T≡Acc is conservative over T=Acc,
by a Winterhalter-style translation using funext and proof irrelevance. Axioms valid in the
set model (funext, propext, excluded middle) keep canonicity. In Rocq, the definitional rule
is a rewrite rule `#[local] Rewrite Rule Acc_el_def`, off by default and switched on per
theorem with `#[rewrite_rules(…)]`. Such theorems are "treated as a justified axiom". The
measurements: rewriting with the propositional rule hits a 10-minute timeout at `N = 10`
for `gcd (2^N) 2 <? 5`, because the proof terms grow exponentially. Reducing a System F
evaluator's `Prop` termination proof times out (30 min) at `n = 3`. Extraction is "an
external version of our approach": after erasure the eliminator computes as `Acc-el-def`
**[checked]**. *Steal:* Stitchwort avoids `Acc` altogether. `decreasing` runs on `Nat` fuel,
and the run body is the erased recursion (docs/core.md "Recursion on a measure"), the
extraction view the paper endorses. The lesson for SW-93 is the undecidability, which
applies to `Loop` (§5.1). *Helps:* SW-93, SW-803. *Cost:* none (design input). *Full text:*
read (§1, §2, §4 statements, §6, §7; §3 and §5 proofs skimmed; HAL PDF in
`~/stitchwort-papers/felicissimo-lics26.pdf`).

**C2. Gilbert, Cockx, Sozeau, Tabareau, Definitional Proof-Irrelevance without K** (POPL
2019, classic; HAL copy). *Claim:* singleton elimination is the wrong criterion for `sProp`.
`Acc` satisfies it, but with definitional irrelevance `Acc_rect P F x X ≡ F x (… Acc_inv …)`
holds, and "it is undecidable to know how many time this unfolding must be done. Even the
strategy that there is at most one unfolding may not terminate". Lean's closed-terms-only
irrelevance for such types breaks subject reduction (Appendix A, `fix_F_eq4 := eq.refl`
fails). The proposed criterion (§2.4) for eliminating an `sProp` inductive into any type has
three parts: (1) every non-forced constructor argument is in `sProp`; (2) the constructors'
return types are pairwise orthogonal (so `≤` qualifies and `≤bad` doesn't); (3) every
recursive argument passes a syntactic guard. It is justified by translating the type into a
fixpoint, under which `Acc` is rejected. §4.5: irrelevance is decided syntactically with
**relevance marks** on binders and context variables. "For correctness of marks, implicit
cumulativity from sProp to Type must be forbidden". §6.1.1: "Conversion in Coq is untyped so
we use relevance marks … we just insert a check for irrelevance before the reduction step".
Agda's conversion is type-directed and needs no marks (§6.5) **[checked]**. *Steal:* support
for D1′'s design (marks in an untyped `conv`). Criterion (3) is the rule that would refuse
`Loop`'s large elimination. Criteria (1)-(2) say how `E-PROP-ELIM` could later be widened
(D140 chose not to). *Helps:* SW-93, §5.1. *Cost:* small kernel change (§5.1). *Full text:*
read (§1, §2, §3 intro, §4.4, §4.5, §5 intro, §6.1, §6.5, §7, App. A; §3.1-3.7, §4.1-4.3,
§5.1-5.2 skimmed).

**C3. Abel, Coquand, Failure of Normalization in Impredicative Type Theory with
Proof-Irrelevant Propositional Equality** (LMCS 16(2:14), 2020, classic; arXiv 1911.08174).
*Claim:* with an impredicative `Prop` and `cast A A e x → x`, a rule that doesn't inspect
`e`, `Ω h = δ (ω h)` reduces to itself under the hypothesis `h : ∀ A B : Prop, A = B`. So
"equality of open terms cannot be decided just by normalization". With `propext` alone the
loop is closed and "does not even have a weak head normal form" (Lean 3.4.2). "Consistency
and canonicity is not at stake". The paper refutes Werner's conjecture 3.14 **[checked]**.
*Steal:* a check on SW-93. Stitchwort's kernel `J` computes only on `rfl` (docs/core.md:139),
and D1′ adds no computation, so this rule isn't in the kernel **[checked: docs;
proof-irrelevance.md §5.2 argues the same]**. The *runtime* does take `J`'s base on any erased
proof (docs/core.md:237), which is this rule, but it runs only closed well-typed programs
(§5.5). *Helps:* SW-93. *Cost:* none. *Full text:* read (all 5 pages).

**C4. Carneiro, Lean4Lean: Verifying a Typechecker for Lean, in Lean** (TYPES 2025, LIPIcs
TYPES.2025.2). *Claim:* this is a complete external Lean 4 checker written in Lean. Fig. 2:
it takes 44.61 s against 37.01 s on Lean (ratio 1.21), 45.74 s against 32.49 s on Batteries
(1.40) and 58.79 min against 44.54 min on Mathlib, Batteries and Lean (1.32), single-threaded.
Lean 3's kernel had no soundness bugs reported. Lean 4's kernel gained bignums, nested
inductives and primitive projections, and "some soundness bugs crept in". Unique typing and
definitional inversion (Conjectures 7 and 9) were "downgraded from theorems in LTT" because
"the proof has an error in one of the technical lemmas". The verification found a bug:
`looseBVarRange` is read from 20 bits of a cached word, its overflow check `panic!`s and then
returns 0, so a deeply nested level variable looked closed, giving `U0 ≡ U1`. It was "found
entirely theoretically, by failing to prove a theorem". §3.2.3: Lean4Lean checks that a
definition named `Nat.add` satisfies `a + 0 ≡ a` and `a + succ n ≡ succ (a + n)` before
computing with literals. Footnote 18: "The original Lean kernel does not perform these
checks. This is technically unsound, but to exploit it one would need to replace the prelude".
`reduceBool` is "unsound by design". §3.2.4 lists Lean's conversion steps (a union-find cache
of equal pairs, proof irrelevance by type, lazy delta by height, structure and unit eta).
§4.1: unfinished parts include "an experimental complete level equality algorithm following
[Géran]" **[checked]**. *Steal:* the equation check for natives (§5.4, T5). The report also
says soundness bugs "occur in areas that are insufficiently tested because the developer did
not even consider the error condition". *Helps:* trusted base. *Cost:* small. *Full text:*
read (§1, §2.1-2.2, §2.5, §3.1, §3.2.3-3.2.4, §4.2, §5, §6, §7, §8, §9; §2.3-2.4 and §4.1
program logic skimmed).

**C5. Sozeau, Forster, Lennon-Bertrand, Nielsen, Tabareau, Winterhalter, Correct and
Complete Type Checking and Certified Erasure for Coq, in Coq** (JACM 2025; HAL copy).
*Claim:* this is a type checker for PCUIC proven sound and complete, without modules,
template polymorphism and η, assuming strong normalisation and an abstract guard condition.
It is a "trusted theory base" rather than a trusted code base. "On average one critical bug
is found every year" in Coq. The completeness proof found one **incompleteness** in Coq's
kernel, for cumulative inductives from 8.11 to 8.14. It made subject reduction fail:
conversion was used where cumulativity was needed, because match return types were encoded
as Π-types. Coq 8.14 changed its case representation in response (§4.4; issue #13495). The
conversion algorithm (§6.3) works in three steps: weak-head reduce without δ, compare heads,
then unfold a blocking definition. It is defined only on well-typed terms. The development
is over 300 kLoC **[checked]**. *Steal:* nothing to build. It is the reference for what a
mechanised kernel costs. *Helps:* future verification. *Cost:* research. *Full text:* read
(abstract, §1, §4.4, §5.2 strengthening paragraph, §6.1, §6.3 opening, §9; §2-3, §5, §7
skimmed).

**C6. Lennon-Bertrand, What does it take to certify a conversion checker?** (FSCD 2025;
arXiv 2502.15500v3, 16 Jul 2026). *Claim:* injectivity of type constructors suffices for
positive soundness of a conversion checker. Term-level injectivities add negative
soundness, and normalisation adds termination (Fig. 1). "In Rocq and Lean, conversion does
not maintain any type information". An untyped checker with η is certified against a typed
specification. Untyped η has rules only for λ against λ and λ against a neutral: "there is no
η-rule when the two sides are neutrals". The preconditions (Fig. 6) require both sides to have
**the same type**: "types are still present in invariants, silently keeping the algorithm on
rails". §4.4: a definitional unit type "completely wrecks completeness of neutral
comparison" and "leaks" to types like `N → (Σ x:⊤.⊤)`. Rocq "commits to untyped conversion,
but must therefore enforce all record types to have at least one relevant field". Lean
re-infers types on failure with a unit-like criterion "currently incomplete, causing issues".
For `SProp`, Rocq uses "universe information … in a cheap yet complete way" **[checked]**.
*Steal:* Stitchwort's `conv` is this algorithm. Eta for functions is λ against anything
(`value.rs:2479-2487`), and proof-irrelevance.md §7.4's "same-type invariant" is Fig. 6's
precondition. So the paper confirms both, and gives the rule for record eta (§5.2). *Helps:*
SW-55, SW-789, SW-93. *Cost:* design-note amendment. *Full text:* read (§1, §3 untyped
part, §4 intro, §4.2-4.4, §5; §2, §3 typed rules and §4.1 skimmed).

**C7. Courant, Leroy, A Lazy, Concurrent Convertibility Checker** (POPL 2026, PACMPL 10
Art. 53; arXiv 2510.18418v2). *Claim:* the usual heuristics can "backfire". Rocq tries the
arguments of `F a ≈ F b` first, so `zero (exp2 15) ≈ zero (exp2 16)` is slow while unfolding
`zero` would settle it at once. The paper explores the three subproblems (arguments, unfold
left, unfold right) concurrently with fair interleaving. It shares computation by strong
call-by-need, and stops at the first conclusive answer. If a convertibility proof of size
`s` exists, it terminates in `O((k+1)^(2s))`, where heuristic depth-first checkers are
unbounded in `s`. Partial correctness is proved in Rocq (without the sharing extensions). In
a small OCaml prototype against Rocq 8.15.2, the "Full" variant showed `O(n^2.8)` on
`exp2 n ≈ exp2 (n-1+1)` from process explosion. The authors suggest that the checker could
emit a trace of its unfolding decisions "rechecked by a simpler, purely sequential
algorithm" **[checked]**. *Steal:* Stitchwort's kernel uses the same arguments-first order
for glued calls (docs/core.md "Glued calls"; `CallMemo`, `value.rs:2309`). The paper's test
cases are ready-made performance probes. The trace idea fits Stitchwort's split: the
untrusted elaborator could search and the kernel replay **[inferred]**. *Helps:*
proof-check-speed. *Cost:* small (tests); research (algorithm). *Full text:* read (§1, §2,
§3 intro, §9, §10, §11, §12; §4-8 skimmed).

**C8. Leray, Gilbert, Tabareau, Winterhalter, The Rewster: Type Preserving Rewrite Rules
for the Rocq Prover** (Journal of Automated Reasoning 70(7), 2026; extended ITP 2024).
*Claim:* the opening example is parallel plus, which is **Stitchwort's R1-R4 exactly**,
declared on a `Symbol`. Rewrite rules have been in Rocq since 8.20 (PR #18038). The
type-preservation criterion (PR #19290) is "yet to be integrated", and a confluence checker
is the authors' "most immediate goal". The naive check "∀x, p = r well typed" is unsound
under cumulativity (Example 1 gives `U : U`) and with non-unique pattern variable types
(Example 2). The correct criterion checks the right-hand side against the principal type
inferred from the left. Non-termination "cannot introduce proofs of ⊥" and doesn't break
subject reduction. §4's triangle criterion requires (1) closure of overlapping patterns under
unification, with the unifier's rule ordered first, and (2) `⌊p⌋ ⇛ u ⟹ u ⇛ r`. It is
decidable, and Agda already implements it. §4.3: with `SProp`, "a subpattern may only be
irrelevant if the whole pattern is". §9: with propositional instantiation "we could justify
parallel pplus using the standard notion of addition" **[checked]**. *Steal:* §5.3. *Helps:*
SW-787 follow-ups. *Cost:* doc. *Full text:* read (§1, §4, §5 opening, §7, §8, §9; §2, §3,
§5.1-5.2, §6 skimmed; HAL PDF).

**C9. Cockx, Tabareau, Winterhalter, The Taming of the Rew** (POPL 2021, classic). *Claim:*
RTT gives "subject reduction and partial decidability of type checking … without relying on
weak or strong normalization", through the triangle property, "stronger than mere confluence
and does not require termination". Example 4.3: with ρ as "the first rule that matches", the
four `+` rules fail the triangle property at `(suc m) + (suc n)`. Adding the parallel rule
`(suc m) + (suc n) → suc (suc (m + n))` fixes it. Modularity requires left-linear rules and
pairwise orthogonal blocks. Consistency holds when each block can be instantiated with
propositional equalities (Lemma 6.8, not formalised). For parallel plus it "follow[s] from
the fact that each rewrite rule already holds propositionally for the standard plus". Theorem
6.10 (not formalised): with the triangle criterion, algorithmic conversion, when it
terminates, is correct **[checked]**. *Steal:* §5.3. *Helps:* nat-add-recursion.md §9.4.
*Cost:* doc. *Full text:* read (§1, §2.1, §4.1-4.2, §6.4-6.5, §7 opening; §3, §5, §6.1-6.3,
§7.1+ skimmed).

**C10. Felicissimo, Winterhalter, Confluence Techniques for Dependent Type Theory with Typed
Conversion** (PACMPL 10 ICFP Art. 293, Aug 2026; HAL). *Claim:* this is typed confluence for
a theory with Π (no η), universes, Σ (no η), `Nat`, sums, a definitionally proof-irrelevant
universe and `Lift` (with η). It extends to Lean's strong `J` and to observational equality,
"the first time partial correctness of typing and conversion algorithms for equality with
strong J is proven". Formalised in Rocq, axiom-free. §7: η for functions needs strengthening,
which is hard with typed conversion but "does work with untyped conversion, as shown by Werner
[1994]". η for pairs is non-left-linear **[checked]**. *Steal:* background only. It explains
why Stitchwort's untyped `conv` makes function η cheap to justify. *Cost:* none. *Full text:*
read (§1, §7, §9; §2-6, §8 skimmed).

**C11. Carneiro, Coquand, Frabetti Mathieu, Lennon-Bertrand, Melliès, Weirich, Definitional
Inversion, Without Normalisation** (arXiv 2607.13662v1, Jul 2026). *Claim:* a domain-theoretic
proof technique proves injectivity and no-confusion of type constructors without
normalisation. It works even for type-in-type MLTTη, "the first to establish injectivity of
type constructors for such a system in the presence of η laws". It needs only "basic
induction on natural numbers". The extensions treated are Σ and unit with η, a fixed-point
combinator, `Nat`, a proof-relevant `Id`, and `Prop` with definitional irrelevance ("only an
extensionality rule"). It is mechanised in Agda, Lean and Rocq; the Agda version was
"entirely written by Claude, with a lot of human guidance". The authors say they are still
far from "(co-)inductive types or proof irrelevance with axiom K". **Quotients are not among
its features** (the word appears only in the domain construction, §2) **[checked]**.
*Steal:* none now. *Cost:* research. *Full text:* read (§1, the `Prop` part of §3, §4, §5;
§2 and other §3 parts skimmed).

**C12. Rosain, Díaz, Maillard, Sozeau, Tabareau, Tanter, Winterhalter, Bounded Sort
Polymorphism with Elimination Constraints** (PACMPL 10 POPL Art. 90, 2026; HAL). *Claim:* it
adds **sort variables** with elimination constraints `s1 ⇝ s2`. The word "quality" doesn't
occur (grep matches only "equality"). The metatheory is on paper: equiconsistency with a
monomorphised version, given conditions on the constraint graph. Nothing is mechanised;
examples were checked with a modified Rocq. The fixpoint rule's constraint "plays a crucial
role in preserving the decidability of conversion", because otherwise an `Acc` in `SProp`
yields `Acc_elim` into `Type` (§3). §6 found Rocq 9.0 bugs: an `AccS` with primitive
projections had its eliminator "incorrectly generated … rejected by the type checker,
effectively disabling such inductive types" (a completeness bug). Also from §6: "Previous
versions of Rocq disallow primitive projections on records when the sort of the record is
either Type or Prop and all the projections are in SProp … by eta conversion, one could
introduce proof-irrelevance to Type or Prop". The example is `Pair : Type := {fst : SProp; snd
: SProp}`. The worst-case slowdown is 5% **[checked]**. *Steal:* the `Pair` example and Rocq's
rule for §5.2. *Helps:* SW-55 after SW-93. *Cost:* doc. *Full text:* read (§1, §2 opening,
§3 Fix rule note, the subsingleton part of §5, §6, §8; §3 rules, §4, §7 skimmed).

**C13. Géran, A Canonical Form for Universe Levels in Impredicative Type Theory** (CSL
2026, LIPIcs CSL.2026.39). *Claim:* a canonical form for the 0-imax-successor algebra decides
level equivalence by syntactic equality and makes `≤` easy. Its existence and uniqueness are
proved in Rocq. The motivation is encoding CC∞∀ in λΠ-modulo (Dedukti), where equivalent
levels must be convertible. An earlier encoding failed `max(imax(x,y),x) ≡ max(x,y)`, and
Carneiro's thesis decides inequality without a canonical form. The canonisation algorithm is
"naive since level expressions are usually quite small", and it is used in a work-in-progress
Lean-to-Dedukti translator. **The paper says nothing about Lean's kernel level normaliser**
**[checked]**. *Steal:* if universe polymorphism comes (DESIGN §16 Q3), an impredicative
`Prop` makes the Pi rule `imax` once levels are variables (docs/core.md "Universes"), and this
is the decision procedure **[inferred]**. *Cost:* research. *Full text:* read (§1, §5;
§2-4 definitions skimmed; Appendix A not read).

**C14. Bezem, Coquand, Dybjer, Escardó, Type Theory with Explicit Universe Polymorphism**
(TYPES 2022; arXiv 2212.03284v5). *Claim:* a proposal of rules, with no metatheorems proved.
It has level judgments, level variables with `+` and `∨` and **no level 0** (so every
universe is polymorphic), level-indexed products `[α]A`, and constraints in contexts with
constraint-indexed products. The authors rewrote 9620 lines of HoTT/UF Agda notes without
level 0. Lean is roughly the special case with only prenex level parameters. Canonicity,
normalisation and decidability are conjectured (§7) **[checked]**. *Steal:* input to a future
universe note: explicit levels, and constraints declared rather than inferred. *Cost:*
research. *Full text:* read (§1, §6, §7; §2-5 rules skimmed).

**C15. Sterbac, Sterling, Fuss-free cumulative universes: theory and practice** (arXiv
2607.11329v1, Jul 2026). *Claim:* cumulative polymorphic universes can be presented with a
judgemental "smallness" instead of coherent lifting coercions. It is proved equivalent by
normalisation, and comes with a bidirectional elaboration algorithm and a Haskell
implementation. Production systems prefer non-cumulative hierarchies because they are easy
to specify, avoid "contention between higher-order unification and the insertion of
subtyping coercions" (Agda's cumulative mode "works very poorly"), and have broad models
**[checked]**. *Steal:* if Stitchwort ever wants cumulativity, this is the design to read
first. *Cost:* research. *Full text:* read (§1-1.2, §8; §2-7 skimmed).

**C16. Pujet, Tabareau, Observational Equality: Now for Good** (PACMPL 6 POPL Art. 32,
2022; HAL). *Claim:* TTobs adds to MLTT with definitionally irrelevant `Ω` an observational
equality with funext, propext and definitional UIP. Normalisation and canonicity are
formalised in Agda, and conversion and typing are decidable. Quotients need a proof-irrelevant
relation (`R : A → A → Ω`); `π(t) ∼ π(u)` reduces to `R t u`; `Q-elim` computes on `π`; "it
is generally impossible to extract proof-relevant information from equality in the quotient
type". The theory needs some cumulativity **[checked]**. *Steal:* nothing now. D785
(recursion through quotients) is where it would matter. *Cost:* research. *Full text:* read
(§1, §4.1, §5; §2-3 skimmed).

**C17. Adjedj, Lennon-Bertrand, Maillard, Pédrot, Pujet, Martin-Löf à la Coq** (CPP 2024;
arXiv 2310.06376). *Claim:* this is a Coq mechanisation of MLTT (Π and Σ with η, `N`, `Id`
with large elimination, one universe) proving decidable conversion and type checking, with an
executable certified checker. The logical strength is MLTT plus indexed inductives and a few
universes, about 30 kLoC. Future work (§8) includes term-directed η (Abel and Coquand) and
definitional functor laws (`map id l ≡ l`) **[checked]**. *Steal:* none now. *Cost:*
research. *Full text:* read (abstract, §1, §8; §2-7 skimmed; two-column extraction re-run on
pp. 10-12).

**C18. Pujet, Leray, Tabareau, Observational Equality Meets CIC** (TOPLAS 47(2) Art. 6,
2025; HAL). *Claim:* CICobs combines indexed inductives with observational equality via
Fordism, plus a cast that computes on reflexivity, proved not to harm decidability. It is
implemented on Coq with rewrite rules (which needed extending). "The indexed inductive types
of CICobs can contain more inhabitants than their counterparts in CIC; they only coincide
when indices are taken in a type with decidable equality". "None of the mainstream proof
assistants support observational equality as of 2023" **[checked]**. *Steal:* the caveat
about indices, if D785 ever leads to OTT. *Cost:* research. *Full text:* read (§1 opening,
§7 opening, §8; §4-6 skimmed).

**C19. Danielsson, Erased Postulates, Identity Types and Quotients** (arXiv 2609.08578v1, Sep
2026). *Claim:* in a graded type theory with erasure (Agda formalisation: Id, set quotients,
Π, Σ, unit, empty, `Nat`, a universe hierarchy, opaque definitions), quotients get an erased
`resp` and an eliminator that computes only on `[x]`. Terms can then get stuck, but programs
still compute. Extraction sends `J … u …` to `erase u`, so `J` takes its base. Theorem 10.1
"would fail, even for closed terms, if quotient types were allowed, equality reflection were
disallowed, and (say) limited erased matches were allowed for J … source-level reduction gets
stuck. However, ε ▶ ε ⊢ t :ω Nat suffices to ensure that the extracted term does not get
stuck: this follows from Theorem 11.3". Theorem 11.3: if the erased postulates can be
implemented under equality reflection, a closed `Nat` program's extraction reduces to the
numeral it equals. Erased matches on `Id` are unsafe with erased univalence, and propext
cannot be implemented as a closed term in these theories **[checked]**. *Steal:* §5.5.
*Helps:* map-equality.md §7.4.5. *Cost:* doc. *Full text:* read (§1, §3, §4, §5 opening, §8
opening, §10, §11; §6-7, §9, §12-16 and appendix not read).

**C20. lean4#14977, "Meta issue: Lean Kernel Logic renovation"** (Adjedj with Breitner, opened
31 Aug 2026, open). *Claim:* the goals are "a decidable, transitive definitional equality
algorithm" and inductive features (large elimination, K, projections, eta) "done by the
elaborator and communicated explicitly, the kernel only checks". Proofs should "never have to
be reduced during type checking", and level comparison should be complete. Recursive
predicates like `Acc` lose large elimination: "currently a source of undecidability for
definitional equality … [Felicissimo et al.] justifies that having `Acc`'s iota rule be a
propositional equality … is enough". Structures in `Prop` with non-`Prop` fields lose
projections. Checked items: unit-like criteria extended (#15372), `whnf` never called on
proofs (#15103) **[checked: gh]**. *Steal:* the direction confirms Stitchwort's choices
(features fixed at admission, records.md §7.1; no universe variables). The one difference is
recursive propositions (§5.1). *Cost:* none. *Full text:* read (issue body).

**C21. lean4#14806, "fix: make kernel `is_def_eq` caching order-independent"** (de Moura,
merged 18 Aug 2026). *Claim:* successful queries went into a union-find. Because `is_def_eq`
is "sound but incomplete, and therefore not transitive", `is_def_eq(v0, v2)` could be false
alone and true after `v0≡v1` and `v1≡v2`. Recursor construction asks more than once, and
"a recursor whose type and computation rule disagreed" gave `False`. The fix is "a plain
cache keyed on the query pair". It was reported by Daniel Selsam (OpenAI) using internal
models **[checked: gh]**. *Steal:* write the rule down. Stitchwort's memo tables are keyed
by exact pairs (`CallMemo` by cell addresses, `value.rs:2309`; the equal-pairs record by
`identical`, `value.rs:2779-2822`). *Cost:* a sentence in docs/core.md. *Full text:* read (PR
body).

**C22. lean4#15908, native `Nat.add` reduction trusts the constant's name** (reported 24 Oct
2026, closed). *Claim:* `reduce_nat` dispatches on the name `Nat.add` before unfolding. A
non-canonical `def Nat.add (_ _ : Nat) : Nat := 0`, injected by renaming in the export file,
makes `Nat.add 2 2` both `0` (by the body) and `4` (natively), giving `False` with no axioms.
`lake check --paranoid` also accepted it **[checked: gh]**. *Steal:* §5.4. Stitchwort's
natives are bound by name while the prelude loads and checked by type and arity only. R3/R4
are pinned by hash. *Cost:* small. *Full text:* read (issue description and scripts).

**C23. lean4#13851, "feat: no large elim of recursive Prop inductives in the kernel"**
(Breitner, opened 26 May 2026, open). *Claim:* "restricts `Acc.rec` and other recursors for
recursive `Prop` inductives to motives in `Prop`", keeping large elimination for `Eq`, `And`,
`Iff`, `Or`, `Unit`. The stated motivation is "to ensure the kernel never has to look at a
proof term of a `Prop`". Four kernel regression tests were dropped because their exploits went
through `Acc.rec` at a `Bool` motive. That is "a real loss of coverage" **[checked: gh]**.
*Steal:* the rule, §5.1. *Cost:* small kernel change. *Full text:* read (PR body).

**C24. Lean Kernel Arena** (github.com/leanprover/lean-kernel-arena, created Jan 2026).
*Claim:* a bank of accept, reject and "either" inputs for Lean checkers. Groups: `bugs/`
("soundness bugs … actually found"), `corner-cases/` ("outcome: either … gaps between
algorithmic and declarative conversion"), `perf/`, `tutorial/`, `other/`. Four tests read in
full: (1) `eta-unit-like-proof-field`: with unit-like eta only for fieldless structures, "both
`p` and `q` are convertible to the same canonical inhabitant … but not to each other", fixed
by counting structures whose fields are all proofs as unit-like. (2) `alg-conv-trans-quot`:
quotients of propositions break transitivity of algorithmic conversion. (3)
`forged-quot-ind`: a `Quot.ind` declared before ordinary definitions named `Quot` and
`Quot.mk` proves `False`. nanoda, nanoclo and nanobruijn accepted it, and it was found "by a
differential run". (4) `k-rec-conv`: a checker with wrong K-like reduction equates `fun x =>
x` and `fun _ => y` **[checked: gh]**. *Steal:* the "either" category for honest corner cases,
and the reject shapes that make sense without universe variables (§5.4). *Cost:* small.
*Full text:* read (README; the four test descriptions; file names of `bugs/` and
`corner-cases/`).

**C25. Stérin, In search of falsehood** (tristan.st/blog/in_search_of_falsehood, 5 Mar
2026). *Claim:* Claude Opus 4.6 was run as an agent team (mathematician, computer scientist,
verification expert, devil's advocate), given past bugs and expert tips, for about 72 hours
on a Max plan (150% of a weekly limit). Results: Rocq 7 proofs of `False` and 3 other bugs;
official Lean 0 and 4; **nanoda 2 and 0; lean4lean 1 and 0**. The Rocq bugs were "mainly in
the guard checker and module system". Lean bug 1 is an unsigned-to-`size_t` truncation
needing 2^32 fields, which `-Wconversion` would catch. The setup "tended to be too
conservative". Stated caveat: "we arguably got much more precise expert tips … in Rocq than
Lean" **[checked: curl]**. *Steal:* the method (T1 of the old register, unchanged) and the
cheap one: compile with all warnings and try to exploit each. *Cost:* one lane. *Full text:*
read.

**C26. CVE-2026-72703 and CVE-2026-72705, Rocq guard checker** (oss-security 2026/q4/381
and /383, Brossard, 25 Oct 2026). *Claim:* 72703: `find_uniform_parameters` "only inspects
self-recursive calls within each body of a mutual fixpoint". When all calls are cross-calls,
every parameter is treated as uniform, and a non-decreasing call is accepted (Rocq 8.20 to
<9.2.0; discovered by Stérin with Opus 4.6). 72705: a fixpoint passed as an argument to
another fixpoint can be applied to a non-subterm. Passing it to a plain definition is
rejected, but passing it to a fixpoint isn't. The result is `T` definitionally equal to `T →
False` (all versions before 9.2.0; "discovered by Claude Opus 4.6 … during a fuzzing
campaign") **[checked: curl]**. *Steal:* two must-reject tests (§5.4). *Cost:* small. *Full
text:* read (both advisories).

**C27. Liesnikov, Cockx, Building a Correct-by-Construction Type Checker for a Dependently
Typed Core Language** (APLAS 2024, LNCS 15194, doi 10.1007/978-981-97-8943-6_4). From the
search summary only: Agda Core, a checker in Agda that returns typing derivations, so
positive soundness holds by construction **[unverified]**. C6 §5 says the same of Agda-Core
**[checked: C6]**. **NOT READ** (§9).

## 5. Deep reads

### 5.1 Proof irrelevance: close the recursive-proposition hole before SW-93 (C1, C2, C3, C20, C23, C6)

**What the sources say** [checked]. All three papers and both Lean issues agree. If a
proposition can be eliminated into data and holds a proof of itself in a field, definitional
irrelevance lets any proof be unfolded once more, `X ≡ intro (inv X)`. Then nothing bounds
how many unfoldings conversion must try, and conversion is undecidable (C2 §2.3, C1 §1). Lean
answered with a propositional computation rule plus a choice-backed eliminator (C23), on the
strength of C1's theorem (C20). Rocq and Agda allow only `False` to eliminate from `SProp`
(C1 §1). Gilbert's criterion would refuse the case through its guard condition, (3) (C2
§2.4). Separately, a cast that reduces whenever its endpoints are convertible breaks
normalisation with an impredicative `Prop` (C3). On implementation, Rocq keeps conversion
untyped and decides irrelevance from **relevance marks** fixed at binders (C2 §4.5, §6.1.1),
"cheap yet complete" (C6 §4.4). Marks need cumulativity from `SProp` to `Type` to be
forbidden (C2 §4.5).

**Stitchwort today** [checked].
- `E-PROP-ELIM` (`crates/core/src/check.rs:915-929`) lets a `Prop` eliminate into data when it
  is alone in its group, has no nested field, has at most one constructor, and every field's
  sort is `Prop`. It doesn't ask whether a field mentions the type itself, so
  proof-irrelevance.md §5.1's `type Loop : Prop = | MkLoop (next : Loop)` with `steps : Loop
  -> Nat -> Bool` is accepted (that note marks it **[run]**,
  `docs/proposals/proof-irrelevance.md:572-575`).
- There is no definitional irrelevance yet (docs/core.md:141). `J` computes only on `rfl`
  (docs/core.md:139).
- There is no cumulativity (docs/core.md:63), which marks need.
- SW-93's D1′ skips proof positions in `conv`. proof-irrelevance.md defends `Loop` by making
  D1′ incomplete on purpose (§5.1: "must not *promise* full irrelevance").

**Mapping.**
1. *Close the hole* rather than argue around it. Add a fifth condition to `E-PROP-ELIM`: no
   field type of the constructor mentions `D`. This is Lean's #13851 rule, and the guard
   that Gilbert's criterion (3) would impose. Afterwards a recursive proposition still
   eliminates into *proofs*, so induction on it is untouched. With it, the argument in
   proof-irrelevance.md §5.1 has no starting point, whatever SW-93 or SW-803 later promise
   **[inferred]**.
2. *D1′ is the published implementation strategy.* Masks on declared proof positions in an
   untyped `conv` are Rocq's relevance marks applied to arguments and fields. C2 proves
   decidability for marks in sMLTT (Theorem 4.5, from Abel and Scherer), but not for CIC with
   impredicativity and K, so this supports the design and is not a proof for Stitchwort
   **[inferred]**.
3. *No Werner rule.* D1′ adds no computation, and `J` stays on `rfl`, so C3's loop is
   outside the kernel **[inferred from docs/core.md:139 and C3]**.
4. *Not now:* Gilbert's criteria (1)-(2) would let `≤`-like propositions with several
   constructors eliminate into data. D140 refused related widening, and nothing asks for it.

**Assumptions the recommendation depends on.** (A1) No library, example, AoC or rogue code
eliminates a recursive proposition into data. Not checked; T2 measures it first. (A2) The
restriction only adds a refusal, so it cannot make anything unsound **[inferred]**. (A3)
`decreasing` needs no `Acc`. It uses `Nat` fuel (docs/core.md "Recursion on a measure"), so
well-founded recursion is unaffected **[checked]**.

**Risks.** A user who wanted `Loop`-style recursion into data must move the type to `Type`.
Accepted programs keep their hashes (the rule only refuses).

**Next step.** T2 (measure, then the rule with `Loop`/`steps` as the must-reject test), and
decision D1980.

### 5.2 Record eta in an untyped `conv`, once proofs are irrelevant (C6, C12, C24, C20)

**What the sources say** [checked]. In an untyped checker, η has rules only where one side is
an introduction form. Two neutrals are compared structurally (C6 §3). Its correctness rests
on a same-type precondition (C6 Fig. 6). A type all of whose values are equal ("unit-like")
breaks completeness of neutral comparison (C6 §4.4). Rocq therefore requires every record to
have "at least one relevant field" (C6 §4.4), and forbade primitive projections for records
in `Type`/`Prop` whose fields are all in `SProp` (C12 §6, `Pair` example: `p ≡ {fst p; snd
p} ≡ … ≡ q`). Lean's fieldless-only unit-like rule gave a non-transitive conversion
(C24 `eta-unit-like-proof-field`), fixed in #15372 (C20's checklist).

**Stitchwort** [checked]. Function η is λ against anything (`crates/core/src/value.rs:2479-2487`),
the shape C6 certifies. SW-55's plan (records.md §7.1, condition 4 at
`docs/proposals/records.md:950`) gives eta only to records in `Type` with **at least one
field**, and justifies excluding fieldless records with the same transitivity argument
(records.md:962-966). proof-irrelevance.md §7.4 (`:1030`) states the same-type invariant that
C6 requires.

**Mapping.** After SW-93's D1′, a record `{ h : P }` with `P : Prop` is unit-like: for
neutral `x, y`, `x ≡ MkR x.h` (eta), `MkR x.h ≡ MkR y.h` (mask), `MkR y.h ≡ y` (eta), but
`x ≡ y` fails **[inferred]**. Rocq's rule removes the case: condition 4 should read "at least
one field that isn't a proof". Lean's alternative (re-infer types on failure) needs types of
neutrals, which `conv` doesn't have.

**Assumptions.** (B1) SW-93 is built as D1′ (masks on constructor fields). If it isn't, the
case doesn't arise. (B2) SW-55 keeps records.md §7.3's untyped one-sided rule.

**Next step.** T3 (records.md §7.1 amendment and a test), decision D1981.

### 5.3 R3/R4: a confluence argument that needs no termination (C9, C8)

**What the sources say** [checked]. Parallel plus is the running example of both papers. With
"first rule wins" ρ, the four rules fail the triangle property at `(suc m) + (suc n)`. Adding
`(suc m) + (suc n) → suc (suc (m + n))` restores it (C9 Example 4.3). The triangle property
gives confluence without termination, and algorithmic conversion is correct whenever it
terminates (C9 §1, Theorem 6.10, not formalised). Consistency follows when the rules hold
propositionally for the ordinary definition (C9 Lemma 6.8; C8 §8, §9). With irrelevance,
rule patterns must not have irrelevant subpatterns (C8 §4.3). The naive typing check "∀x, p
= r well typed" fails under cumulativity (C8 Example 1).

**Stitchwort** [checked]. R1/R2 are `Nat.add`'s case tree. R3/R4 apply only when that tree is
stuck (`crates/core/src/nat_add.rs:1-60`). They are bound by content hash (`nat_add.rs:77`,
check at `:216`) after checking that `Nat.addZero` and `Nat.addSucc` have the right types.
nat-add-recursion.md §9.4 argues confluence by the critical pair lemma and Newman's lemma
(termination of R1-R4 alone), and confluence with the rest of the kernel by analogy to Müller
(1992). Both citations are marked **[unverified]**, and whole-core normalisation is
"expected, not proved" (§9.5).

**Mapping.**
1. The triangle route replaces the Newman step. R1-R4 plus the parallel rule satisfy the
   triangle property (C9 Example 4.3). For `Succ m + Succ n` Stitchwort's evaluator reaches
   `Succ (Succ (m + n))` (R2 from the case tree, then R4 on the inner sum), which is the
   parallel rule's right side (**[checked]** 30 Oct by T4, up to conversion: the value is
   the compact `NatAdd(2, m + n)`; test `the_parallel_rule_is_reached`). So the evaluator never needs the
   parallel rule as code, and the argument no longer depends on termination of anything.
2. The consistency argument is already Stitchwort's: the equations are theorems (C9 Lemma
   6.8's instantiation condition).
3. Typing: Stitchwort has no cumulativity and the patterns are first-order on `Nat`, so the
   "naive" check is adequate here. The note should say why, citing C8 Example 1, instead of
   calling it the strongest form (wrong claim 5 above).
4. Gaps the papers don't close: both frameworks put rules on postulated symbols in their own
   block, while R3/R4 extend a *defined* function. Neither covers quotients, glue or natives.
   So the note keeps "argued, not proved" for the whole core, with better sources **[inferred]**.
5. Checklist for any third rule (a `*` rule was deferred): derivable equations; left-linear
   constructor patterns; no irrelevant subpatterns; triangle property with every existing rule
   (adding parallel rules as needed); orthogonality with natives and compact text.

**Next step.** T4: amend nat-add-recursion.md §9.4 (doc only).

### 5.4 What broke other kernels in 2026, against `crates/core` (C4, C21, C22, C24, C25, C26)

| Shape (source) | Stitchwort | Evidence | Action |
|---|---|---|---|
| A cache closes a non-transitive relation (C21) | Both memos keyed by exact pairs: `CallMemo` by unfolding-cell addresses (`value.rs:2309`), equal pairs by `identical` (`value.rs:2779-2822`); no union-find | [checked] | A sentence in docs/core.md "Evaluation and conversion" |
| A native trusted by name (C22; C4 fn. 18) | Natives bound by name (`registry.rs:652-656`, first binding wins) only while the prelude loads (`elab/src/lib.rs:2727`); `register_native` checks arity and type (`native.rs:379-455`, `:452`), not the body. R3/R4 are pinned by hash (`nat_add.rs:77`) | [checked] | T5: check the defining equations as Lean4Lean does, or pin by hash |
| A primitive forged by names (C24 `forged-quot-ind`) | Quotients are a term former, `Term::Quot(form, args)` (docs/core.md:46), not named declarations | [checked: docs] | none |
| Cross-calls in a mutual group not examined (C26, 72703) | Size change over the closure of the whole group's graphs (docs/core.md:158) | [checked: docs]; that it catches the PoC [inferred] | T1: port the shape |
| A recursive function passed as an argument (C26, 72705) | Every occurrence of a member must be saturated; a bare one is refused (docs/core.md:151); lambda-bound arguments are "unknown" (docs/core.md:154) | [checked: docs]; outcome [inferred] | T1 |
| Bit-level shortcut silently wrong (C4 `looseBVarRange`) | Not audited | — | T1 audit hint |
| K-like reduction too eager (C24 `k-rec-conv`) | K is a unification rule (deletion), not a reduction; `J` only on `rfl` (docs/core.md:121, :139) | [checked: docs] | T1 test |
| Only panics are looked for | `crates/core/tests/fuzz.rs:1-3`: "The kernel must never panic" | [checked] | T1 (Stérin's method; SW-687 is the fuzzing analogue) |

**Mapping summary.** Three shapes are closed by construction. Two are covered by design, to be
confirmed by tests. One (natives) is a small real gap, of the kind Lean4Lean described as
needing "to replace the prelude". Stitchwort's prelude is compiled in, so the exposure is the
same "unsupported configuration" **[inferred]**.

**Next step.** T1 then T5.

**T1 results (30 Oct 2026, D1983).** Each shape was written as a program and run; every one is
refused **[checked: run]**, in about 0.13 s of CPU each. The `.sw` files are in
`examples/soundness/`, with snapshots, and their accepted neighbours are in
`examples/accept/kernel-2026-neighbours.sw`. Because the `.sw` versions are refused by the
elaborator, `crates/core/tests/kernel_bugs_2026.rs` builds the same terms by hand and checks
that the kernel refuses them with the same code.

- *Bit-level shortcut (C4).* This was **not** closed. The previous lane's first program,
  `def wrap: Type 0 := Type 4294967295`, was accepted, because the step to the next universe
  wrapped at `u32::MAX`. It was fixed as SW-902, with tests `universe-*.sw` and
  `crates/core/tests/universe_levels.rs`.
- *72703, cross-calls only (C26).* `mutual-cross-calls-grow.sw` and
  `mutual-cross-calls-three.sw` give `E-TERMINATION`.
- *72705, a recursive function passed to a recursive function (C26).*
  `recursive-passed-to-recursive.sw` (under a lambda) and `recursive-passed-bare-to-recursive.sw`
  (bare) give `E-TERMINATION`. So do `recursive-passed-type.sw`, `type-as-own-negation.sw` and
  `type-as-own-negation-mutual.sw`, which aim at the advisory's result, `T ≡ T → False`.
- *`k-rec-conv` (C24).* `identity-is-not-constant.sw` and `j-on-hypothesis-stuck.sw` give
  `E-REFL`.
- *`eta-unit-like-proof-field` (C24).* `record-of-proof-not-convertible.sw` gives `E-REFL`:
  there is no record eta and no definitional proof irrelevance.
- *Order-dependent cache (C21).* `conversion-memo-other-argument.sw` and
  `conversion-memo-chain.sw` give `E-REFL`. Both put a pair found equal in the tree memo
  before the false pair, within one comparison. The memo records only after success
  (`value.rs:2759-2800`) and answers only a pair `identical` to one recorded
  (`value.rs:2920-2929`), and `CallMemo` only ever answers "different" (`value.rs:2319-2324`).
  So no closure is taken.
- *`forged-quot-ind` (C24).* `forged-quot.sw` and `forged-quot-ind.sw` give `E-DUPLICATE`.
  The names are reserved (`elab/src/lib.rs:208-218`), and the kernel's quotient is a term
  former (`Term::Quot`), so no declaration can stand in for it.
- *`alg-conv-trans-quot` (C24)* was already covered: `quot-of-proposition.sw` gives
  `E-UNIVERSE`.
- *Stérin's Lean bug 1 (C25),* an unsigned truncation needing 2^32 fields. It can't be tested
  in under a second. Counts and indices are `usize` (`term.rs:162`, `:168`). In
  `crates/core/src`, outside tests, the only narrowing casts are in `float.rs:392-395`, which
  format a double's digits, with exponents bounded by 1075.
- *C22 (native `Nat.add` by name)* was left out. It is under SW-898.

### 5.5 Quotients and erased transport: Danielsson's theorem for map-equality.md §7.4.5 (C19)

**What it says** [checked]. With quotients, transport along erased identity proofs, and no
equality reflection, closed source terms can get stuck. Their extraction still reduces to the
right numeral when the erased postulates can be implemented under equality reflection
(Theorem 10.1 remark, Theorem 11.3). Extraction sends `J` to its base (Fig. 1).

**Stitchwort** [checked]. map-equality.md §9.1 (`docs/proposals/map-equality.md:1210-1220`)
gives exactly this example: `J` on `Quot.sound` is stuck in the kernel, and every runner gives
`0`. §7.4.5 (`:889-915`) states "Closed quotients reach `mk`" as "an intended invariant", with
premises and tests but no external result. The runtime erases `J` on erased proofs to its
base (docs/core.md:237).

**Mapping.** Cite Theorem 11.3 as the closest published result and list where Stitchwort
differs. (D1) Erasure is by `Prop`, not by grades. (D2) `Prop` is impredicative; C19's
universes are predicative. (D3) Stitchwort has K and large elimination of one-constructor
propositions. (D4) Stitchwort's one postulate is `Quot.sound`. Whether it is implementable
under equality reflection in C19's sense isn't shown here **[inferred: likely, since its
quotient's `resp` plays the same role]**. (D5) Opaque `Quot.ind` proofs (map-equality.md
§7.4.4) correspond to erased postulates. So the invariant stays "intended", but with a named
theorem for its closest case.

**Next step.** T6 (doc only).

## 6. Steal next

Ranked by value over effort. Every row rests on sources read in full.

| Rank | Idea | Source | Helps | Cost |
|---|---|---|---|---|
| 1 | No large elimination from recursive propositions (`E-PROP-ELIM` fifth condition), measured first | C1, C2, C20, C23 | SW-93, SW-803 | small kernel change |
| 2 | Must-reject tests for the 2026 shapes (72703, 72705, `k-rec-conv`) with accepted neighbours | C24, C26 | DESIGN §13 | small (tests) |
| 3 | records.md §7.1: eta needs a non-proof field | C6, C12, C24 | SW-55, SW-789 | doc amendment |
| 4 | nat-add-recursion.md §9.4 rewritten on the triangle property; checklist for a third rule | C8, C9 | SW-787 follow-ups | doc |
| 5 | Natives: check the defining equations at binding, or pin by hash | C4, C22 | trusted base | small kernel change |
| 6 | docs/core.md: memo tables keyed by exact pairs, never closed transitively | C21 | future caches | a sentence |
| 7 | map-equality.md §7.4.5 cites Danielsson Theorem 11.3 with D1-D5 | C19 | SW-356 follow-ups | doc |
| 8 | Conversion performance probes from Courant and Leroy's table (`zero (exp2 15) ≈ zero (exp2 16)` shapes) | C7 | proof-check-speed | small (tests) |
| 9 | Universe polymorphism note inputs (explicit levels, `imax` canonical form, no cumulativity) | C13, C14, C15, C12 | DESIGN §16 Q3 | research, not now |
| 10 | Observational equality for funext and recursion through quotients | C16, C18 | D785 | research, not now |

## 7. Proposed tickets

Label `research` on each. Not added to the board.

**T1. Must-reject kernel tests from 2026 bugs, plus an audit hint list.** Write `.sw` files or
hand-built kernel terms for three cases: a mutual group whose recursion goes only through
cross-calls with a parameter that grows (72703); a member passed under a lambda to another
member that applies it to a non-subterm (72705); and a K-like conversion of `x => x` with
`_ => y` (Arena `k-rec-conv`). Pair each with an accepted neighbour, per DESIGN §13. Add
§5.4's table as the hint list for any later adversarial lane (SW-687). Refs: §5.4; C24, C26.

**T2. Measure, then refuse, large elimination from recursive propositions.** Behind a
throwaway switch, add "no field type of the constructor mentions `D`" to `E-PROP-ELIM`
(`check.rs:915-929`). Run std, examples, AoC and rogue, and list every rejection. If there are
none, make it the rule, with `Loop`/`steps` (proof-irrelevance.md §5.1) as the must-reject
test and a recursive proposition matched into a proof as the accepted neighbour. Then update
proof-irrelevance.md §5.1. Refs: §5.1; D1980.

**T3. records.md §7.1: eta needs a field that isn't a proof.** Amend condition 4. Add the
test that eta is refused for `{ h : P }`, with the transitivity example of §5.2. Refs: §5.2;
D1981.

**T4. nat-add-recursion.md §9.4: confluence by the triangle property.** Replace the Newman and
Müller step with the Taming of the Rew's Example 4.3 and the Rewster's §4. State the parallel
rule and check (by test) that the evaluator reaches its right side. Keep "argued, not proved"
for the whole core, giving the gaps of §5.3 item 4. Add the checklist for a third rule. Refs:
§5.3.

**T5. Natives: check the defining equations at binding.** At `register_native`
(`native.rs:379`), also check that the bound definition's body computes as the native on a
symbolic shape (Lean4Lean's `Nat.add` check: `a + 0 ≡ a`, `a + succ n ≡ succ (a + n)`), or
pin the body by content hash as R3/R4 are. Test that a changed body runs without its native.
Refs: §5.4; C4, C22.

**T6. map-equality.md §7.4.5 and docs/core.md: two citations.** In map-equality.md, cite
Danielsson Theorem 11.3 with differences D1-D5. In docs/core.md, add one sentence that
conversion memos are keyed by exact pairs, never closed transitively (lean4#14806). Refs:
§5.5, §5.4.

**T7. Conversion probes.** Add Courant and Leroy's cases (adapted to Stitchwort syntax) to the
proof-check-speed benchmarks, to see where the kernel's arguments-first rule for glued calls
costs time. Measurement only. Refs: C7.

## 8. Decisions

**D1980. Make "a proposition that mentions itself in a constructor field never eliminates
into data" a kernel rule (T2), before SW-93 is built?** Assumptions: (A1) no existing program
eliminates a recursive proposition into data, which T2 measures first; (A2) the rule only
adds a refusal, so it can't admit anything new; (A3) well-founded recursion uses `Nat` fuel,
not `Acc`, so `decreasing` is unaffected. **[Recommend yes.]**

**D1981. When SW-93 (proof-position masks) is built, give record eta only to records with at
least one field that isn't a proof (T3)?** Assumptions: (B1) SW-93 is built as D1′, masking
constructor fields that are proofs; (B2) SW-55 keeps records.md §7.3's untyped one-sided eta
rule. If either fails, the decision lapses. **[Recommend yes.]**

## 9. Sources not reached

**Full text not reachable.** None is promising enough for Matt to fetch by hand.

| Item | DOI | URLs tried, and what each returned |
|---|---|---|
| C27. Liesnikov, Cockx, Agda Core (APLAS 2024) | 10.1007/978-981-97-8943-6_4 | `repository.tudelft.nl/file/File_a675d3af-…` and `/file/File_59ce4449-…`: no response (curl timeout, exit 28; the same repository refused connections in earlier lanes); `repository.tudelft.nl/record/uuid:e194d108-…`: status 000; Semantic Scholar API: `openAccessPdf` status CLOSED. Not for Matt: Stitchwort's kernel isn't modelled on Agda's, and C6 already summarises the relevant point |

**Screened, not read** (rows 28-62): they support nothing here. Rows 33-35 (cumulative
subtyping, α-hashing, Rocq `HConstr`) and 36-42 (other Lean issues, CVE-72704/72714, Lean
4.35's bundled checkers) would be the first to read in a refresh.

**Not searched.** Idris 2's core and its bugs since 2022; Agda's kernel bug history (its
changelog and issue tracker); small trusted kernels as a topic (for example Andromeda,
nanoda's design); hash-consing in production kernels beyond C7. This register makes no
claim about them.

**Fetch notes.** `tristan.st` returned an empty page to WebFetch; `curl` got the HTML, which
was read as text. `pdftotext` worked on every PDF. Two-column PDFs (C17) were re-extracted
by page range to check the conclusion.
