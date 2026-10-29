# Literature trawl: elaboration

*SW-894, cluster 3. Trawled 29 October 2026 against `main` at `02eb7b62`. Research only: no
code changed. Window: 2022 onwards (D1831); older work appears only where in-window work or a
system we compare with relies on it, marked **classic**.*

Labels: **[cited]** read in the linked source (for code, the file at the path given, fetched
from the project's default branch on 29 Oct 2026); **[checked]** read in Stitchwort's code or
docs at the place given; **[inferred]** my reasoning; **[unverified]** from an abstract, a
listing or a search summary only.

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

Most open inference tickets (SW-509, 817, 847, 858, 859, 885) share one cause: Stitchwort
postpones only lambdas, only inside one application, and only after a failed try in place
(`apply_args_postponing`, `crates/elab/src/check.rs:1893`) **[checked]**. Lean 4 has one
general mechanism instead: any elaborator that needs an unknown expected type gives up and is
resumed later, and when nothing more can be learned, a fixed ladder of fallbacks runs (§5.1).
OCaml's newest design work (O'Brien, Rémy and Scherer, §5.3) does the same for record labels
and adds a rule for when a guess is allowed. Together they suggest an order for SW-805 and
SW-817: postpone first, guess from field names last.

The second theme is keeping names. Stitchwort's glued calls already do most of what Kovács
describes (§5.2), but checking against an expected type forces it (`check_inner`,
`check.rs:3094`) **[checked]**, which is where alias names are lost (SW-858). Kovács's note
names the missing piece: carry a folded and an unfolded value side by side where both are
needed.

The third is cheap unifier heuristics from Lean and Agda (§5.4): which definition to unfold
first when two different ones meet, and a "constant approximation" restricted to arguments that
only stand for scope.

## 2. Method and queries

Searches were run with the web search tool (standard mode unless marked *ext*) on 29 Oct 2026.
Rerun them as written, adding the months since the last run.

| # | Query | Kept or useful hits |
|---|---|---|
| Q1 | `Kovács "Efficient evaluation with controlled definition unfolding"` | WITS 2024 abstract, gist |
| Q2 | `"Controlling unfolding in type theory" Gratzer Sterling Angiuli Coquand Birkedal` | MSCS 2025 / arXiv 2210.05420 |
| Q3 | `"Contextual typing" Xu Oliveira ICFP 2024 bidirectional` | ICFP 2024; Frost; LCTI |
| Q4 | `"Total type error localization and recovery with holes" POPL 2024` | POPL 2024 |
| Q5 | `"Getting into the Flow" type error messages constraint-based type inference OOPSLA 2023` | OOPSLA 2023 |
| Q6 | `Libal Miller "functions-as-constructors" higher-order unification extended pattern unification 2022` | AMAI 2022 |
| Q7 | `"Bidirectional Typing with Freezing, Skeletons, and Ghosts"` | arXiv 2607.16061 |
| Q8 | `"Local Contextual Type Inference" POPL 2026 Xue Cui Jiang Oliveira` | POPL 2026; arXiv 2511.10343 |
| Q9 *ext* | `arXiv 2023 2024 2025 elaboration dependent types unification postponement metavariables paper` | 2603.01463, 2607.18455, 2511.15819 |
| Q10 | `Breitner "functional induction" Lean 4 paper ITP 2025` | Lean 4.8 release notes only |
| Q11 | `Ullrich de Moura "do unchained" ICFP 2022 Lean 4` | ICFP 2022 (effects cluster) |
| Q12 | `Fissore Tassi type class solver Coq Elpi 2023 2024` | nothing on type classes |
| Q13 | `András Kovács papers 2023 2024 2025 elaboration implicit arguments unification` | nothing new |
| Q14 | `Agda "lossy-unification" first-order unification flag Kovács smalltt` | Agda docs; twin types |
| Q15 | `type error messages dependently typed languages study 2023 2024 Agda Lean Idris unification failure explanation` | Eremondi 2019; Delft hints study |
| Q16 | `TU Delft Agda error message hints user study scope type-checking errors new users` | ITP 2026 paper |
| Q17 | `"Incremental Bidirectional Typing via Order Maintenance" Hazel OOPSLA 2025` | OOPSLA 2025 |
| Q18 | `GHC proposal 366 DuplicateRecordFields remove type-directed disambiguation record fields` | GHC proposal 366 |
| Q19 | `Agda instance search discrimination trees performance 2.7 Amélia Liao` | Agda PR 7109 |
| Q20 | `Lean 4 incremental elaboration snapshots language server 2024 blog Ullrich` | Lean 4.9 notes; arXiv 2605.25556 |
| Q21 | `dependent pattern matching elaboration paper 2023 2024 case trees "with" views overlapping patterns` | Cockx & Abel 2020; Lieverse 2024 |
| Q22 | `Fissore Tassi "Higher-order unification for free" PPDP 2024 Elpi` | DBLP record only |
| Q23 | `Lean 4 type class synthesis new algorithm 2025 instances "tabled resolution" improvements release` | Selsam 2020; Baanen 2022 |
| Q24 | `Narya proof assistant Shulman interactive holes elaboration 2024` | Narya docs, 2025 slides |
| Q25 | `"user widgets" Lean 4 ITP 2023 Nawrocki Ayers Ebner extensible user interface` | ITP 2023 |
| Q26 | `Quick Look impredicativity revisited 2024 2025 GHC argument order type inference paper` | ICFP 2020 only |
| Q27 | `TyDe 2023 2024 2025 accepted papers elaboration unification implicit` | then fetched the three TyDe programmes |
| Q28 | `TyDe 2026 accepted papers` | no programme found |
| Q29 *ext* | `ICFP 2025 OR POPL 2025 paper elaborator dependent types implicit arguments metavariables` | ExEl; Polarity |
| Q30 | `Bauer Haselwarter "equality checking for general type theories" Andromeda 2023` | LMCS version |
| Q31 | `arXiv 2024 2025 higher-order unification dependent types practical heuristics Lean Rocq "unification" approximations` | Canonical; unicoq (classic) |
| Q32 | `"error recovery" elaboration dependent types partial programs language server paper 2023 2024 2025` | sixty; Merlin (classic) |
| Q33 | `Idris 2 elaborator 2024 2025 Brady paper unification performance` | Frex 2023; Idris core talk |
| Q34 | `Liesnikov Cockx "ExEl" extensible constraints elaborator IFL` | IFL 2023 |
| Q35 | `Liesnikov Cockx "Generic bidirectional typing for dependent type theories"` | Felicissimo (not Liesnikov) |
| Q36 | `Danielsson Geng "A Formalization of Opaque Definitions for a Dependent Type Theory" Agda opaque blocks` | TyDe 2025 |
| Q37 | `Juhošová "How Novices Perceive Interactive Theorem Provers" Agda` | TyDe 2024; ICPC 2025 |
| Q38 | `Lean 4 "sharecommon" OR "hash consing" elaborator performance instantiateMVars 2024 2025 speedup` | Lean issue 5610 |
| Q39 | `"Unification Modulo Isomorphisms between Dependent Types" type-based library search` | TyDe 2025 |
| Q40 | `"Reversible coercions" Rocq Coq paper` | Rocq manual only |
| Q41 | `"Statically Contextualizing Large Language Models with Typed Holes" OOPSLA 2024` | OOPSLA 2024 |
| Q42 | `Lennon-Bertrand thesis 2022 "bidirectional typing for the calculus of inductive constructions"` | ITP 2021 only |

Direct fetches: arXiv abstracts 2603.01463, 2607.18455, 2511.15819, 2511.10343 (and the
HTML of 2511.10343, first half); TyDe programmes 2023, 2024 and 2025 on researchr; the Kovács
WITS 2024 PDF (andraskovacs.github.io/pdfs/wits24abstract.pdf); the smalltt README; the Agda
lossy-unification page; Lean 4 source files `src/Lean/Elab/App.lean`,
`src/Lean/Elab/StructInst.lean`, `src/Lean/Elab/SyntheticMVars.lean` and
`src/Lean/Meta/ExprDefEq.lean` from the default branch (raw.githubusercontent.com).

## 3. Screened list

Screened on title and abstract against the hooks in SW-894 and the tickets in the brief. 56
sources: 14 keep, 24 maybe, 18 drop. C15 and C16 are maybes carded for context.

| # | Source | Verdict | Why |
|---|---|---|---|
| 1 | Lean 4 elaborator postponement (`SyntheticMVars.lean`, `App.lean`, `StructInst.lean`), current | keep | general postponement; SW-817, 847, 885 |
| 2 | Lean 4 `isDefEq` approximations A1–A7 and lazy delta (`ExprDefEq.lean`), current | keep | unifier fallbacks; SW-815, SW-386 path |
| 3 | Agda `--lossy-unification` (docs; 2.7.0, 2024) | keep | args-first comparison of calls; already half done |
| 4 | Kovács, Efficient Evaluation with Controlled Definition Unfolding, WITS 2024 | keep | glued values; SW-858 |
| 5 | Kovács, smalltt README (rigid/flex/full unification), classic system | keep | speculative unification modes |
| 6 | O'Brien, Rémy, Scherer, Omnidirectional type inference for ML, arXiv 2025/26 | keep | suspended constraints, record label overloading; SW-805/817 |
| 7 | Xue, Oliveira, Contextual Typing, ICFP 2024 | keep | argument-order-insensitive checking; SW-859 |
| 8 | Xue, Cui, Jiang, Oliveira, Local Contextual Type Inference, POPL 2026 | maybe | System F follow-up of 7 |
| 9 | Tang, Jiang, Oliveira, Lindley, Frost / Bidirectional Typing with Freezing, Skeletons, and Ghosts, ML 2025, arXiv 2607.16061 | maybe | controls which argument informs the function |
| 10 | Libal, Miller, Functions-as-constructors HOU, AMAI 2022 | keep | pattern fragment with constructor arguments; unify fallback |
| 11 | Richter, Böhler, From Pattern Unification Towards Pattern Matching Unification, TyDe 2026 (arXiv 2607.18455) | keep | solve `?f` by case analysis; SW-815 |
| 12 | Norman, Avigad, Implementing DTT Inhabitation and Unification (Canonical-min), arXiv 2026 | maybe | complete solver; meta selection order |
| 13 | Liesnikov, Binder, Süberkrüb et al., Filling the Gaps of Polarity, arXiv 2025 | maybe | implicit arguments spec with codata |
| 14 | Liesnikov, Cockx, ExEl: an elaborator with extensible constraints, IFL 2023 | keep | constraint-and-solver architecture |
| 15 | Felicissimo, Generic bidirectional typing for dependent type theories, ESOP 2024 / arXiv 2307.08523 | maybe | modes per argument, theory |
| 16 | Fissore, Tassi, Higher-order unification for free!, PPDP 2024 | drop | Elpi-specific; not reached |
| 17 | López Juan, Danielsson, Practical dependent type checking using twin types, TyDe 2020, classic | maybe | soundness of postponed heterogeneous constraints |
| 18 | Kovács, Elaboration with first-class implicit function types, ICFP 2020, classic | maybe | postponed checking problems in a Kovács-style elaborator |
| 19 | Serrano et al., A Quick Look at Impredicativity, ICFP 2020, classic | maybe | look at all arguments before committing |
| 20 | Selsam, Ullrich, de Moura, Tabled Typeclass Resolution, 2020, classic | drop | Stitchwort has no overlap or backtracking (interfaces.md §5.5) |
| 21 | Baanen, Use and abuse of instance parameters in mathlib, CICM 2022 | drop | same |
| 22 | Agda 2.7 discrimination-tree instance index (PR 7109), 2024 | maybe | only if instance counts grow |
| 23 | GHC proposal 366, DuplicateRecordFields without ambiguous field access (shipped GHC 9.4, 2022) | keep | counter-evidence for SW-805 |
| 24 | Rocq reversible coercions (reference manual) | drop | no coercions in Stitchwort |
| 25 | Lennon-Bertrand, Complete bidirectional typing for CIC, ITP 2021 | drop | kernel-side, out of window |
| 26 | Bauer, Petković, An extensible equality checking algorithm, LMCS 2023 | drop | user-extensible conversion; not our problem |
| 27 | Gratzer, Sterling, Angiuli, Coquand, Birkedal, Controlling unfolding in type theory, MSCS 2025 | keep | local, scoped unfolding; SW-798, opaque defs |
| 28 | Danielsson, Geng, A Formalization of Opaque Definitions, TyDe 2025 | maybe | metatheory for `opaque def` |
| 29 | Lean 4.8 functional induction (release notes, 2024) | maybe | hand to proof-automation cluster |
| 30 | Zhao et al., Total Type Error Localization and Recovery with Holes, POPL 2024 | keep | error recovery, blame on holes |
| 31 | Bhanuka, Parreaux, Binder, Brachthäuser, Getting into the Flow, OOPSLA 2023 | maybe | explain errors as data flow; mixed evaluation |
| 32 | Khakimova et al. (with Cockx), Enhancing Proof Assistant Error Messages with Hints, ITP 2026 | keep | measured effect of hints |
| 33 | Juhošová (with Zaidman, Cockx), novices and ITPs, TyDe 2024, ICPC 2025 | maybe | what beginners trip on |
| 34 | Eremondi, Swierstra, Hage, Improving error messages for dependent types (replay graphs), 2019, classic | maybe | order-insensitive blame |
| 35 | Porter et al., Incremental Bidirectional Typing via Order Maintenance, OOPSLA 2025 | maybe | LSP incrementality; cluster 7 overlap |
| 36 | Blinn et al., Statically Contextualizing LLMs with Typed Holes, OOPSLA 2024 | maybe | hole context over LSP (ChatLSP) |
| 37 | Nawrocki, Ayers, Ebner, An Extensible User Interface for Lean 4, ITP 2023 | maybe | goal display as structured data |
| 38 | Narya interactive holes (docs, 2025 slides) | drop | no unification or implicits yet |
| 39 | Joram, Annus, Term Search in Rust, TyDe 2024 | maybe | filling holes by search |
| 40 | Takimoto, Moriguchi, Watanabe, Unification Modulo Isomorphisms between Dependent Types, TyDe 2025 | maybe | type-directed library search |
| 41 | Lean 4.9 incremental elaboration inside declarations (release notes, 2024) | maybe | LSP, cluster 7 |
| 42 | Shen, Shi, Keep the Proof State Live, arXiv 2026 | drop | tactic search tooling |
| 43 | Lean issue 5610, `instantiateMVars` cost, 2024 | drop | Lean-specific (delayed assignments) |
| 44 | Gould, Bowman, Syntax vs type-directed NbE performance, TyDe 2025 | maybe | cluster 1/7 |
| 45 | Idris 2 new core talk (compiling open terms to Scheme), 2024 | drop | not reached; runtime-heavy |
| 46 | Frex: dependently-typed algebraic simplification, arXiv 2306.15375 (2023) | drop | one anecdote: postponing blocked problems saved evaluation |
| 47 | Cockx, Abel, Elaborating dependent (co)pattern matching, JFP 2020, classic | maybe | first-match semantics; we already follow it |
| 48 | Lieverse, A Generic Translation from Case Trees to Eliminators, MSc 2024 | drop | we keep case trees in the kernel |
| 49 | Ullrich, de Moura, `do` Unchained, ICFP 2022 | drop | effects cluster |
| 50 | Wright, Kammar, First-class algebraic presentations with elaborator reflection, TyDe 2024 | drop | metaprogramming we don't have |
| 51 | Chen et al., Gradual Metaprogramming, TyDe 2025 | drop | off topic |
| 52 | Kovács, Staged compilation with two-level type theory, ICFP 2022 | drop | cluster 6 |
| 53 | Jang, Gaulin, Hu, Pientka, McTT, ICFP 2025 | drop | cluster 7 |
| 54 | Monnier, Normalizable types, TyDe 2024 | drop | cluster 1 |
| 55 | Paszke, Xie, Infix-extensible record types, TyDe 2023 | maybe | DESIGN §9 row-polymorphic records, later |
| 56 | Sixty (Fredriksson), query-based dependently typed compiler with error recovery, classic system | maybe | elaboration error recovery, cluster 7 |

## 4. Cards

Cost scale: **small** (a local change in `crates/elab`), **elaborator** (a design change in
`crates/elab`, no kernel change), **kernel** (changes `crates/core`), **research** (open
design or theory).

**C1. Lean 4 postponed elaboration.** `src/Lean/Elab/SyntheticMVars.lean`, `App.lean`,
`StructInst.lean` (github.com/leanprover/lean4). *Claim:* an elaborator whose expected type is
an unknown throws "postpone"; the term becomes a placeholder and is resumed later; when
nothing progresses, a fixed ladder runs (resume with postponing off, then default instances,
then report) **[cited]**. *Steal:* one postponement mechanism for record literals, let-bound
lambdas, anonymous constructors and field access, instead of the lambda-only, per-application
one. *Helps:* SW-817, SW-847, SW-885, SW-509, SW-859. *Cost:* elaborator. *Full text:* yes
(source). Deep read §5.1.

**C2. Lean 4 unifier approximations.** `src/Lean/Meta/ExprDefEq.lean`, comment block A1–A7 and
`isDefEqDeltaStep`. *Claim:* outside the pattern fragment Lean uses first-order approximation
(A5, A6) and a constant approximation (A7) only for metavariable arguments that stand for
scope (`numScopeArgs`), and compares two different definitions by unfolding the one with the
greater definitional height first ("lazy delta") **[cited]**. *Steal:* the scope-argument
restriction for constant approximation; height-ordered unfolding. *Helps:* SW-815; the
SW-386 comparison of different definitions. *Cost:* small to elaborator. *Full text:* yes. Deep
read §5.4.

**C3. Agda lossy unification.** agda.readthedocs.io/en/latest/language/lossy-unification.html.
*Claim:* for `f es₀ = f es₁`, try `es₀ = es₁` first, solving metavariables; sound but
incomplete, can pick non-unique solutions (`f ?0 = f 1` for a constant `f`); opt-in per module
or per function (`INJECTIVE_FOR_INFERENCE`) **[cited]**. *Steal:* nothing new: Stitchwort
already tries arguments first without solving anything for glued calls
(`same_arguments_solving_nothing`, `unify.rs:504`) and with solving for dictionaries
(`unify.rs:525`) **[checked]**. It's evidence that the lossy variant is a known trade, if a
performance case ever needs it. *Helps:* none now. *Cost:* small. *Full text:* yes.

**C4. Kovács, Efficient Evaluation with Controlled Definition Unfolding.** WITS 2024,
andraskovacs.github.io/pdfs/wits24abstract.pdf. *Claim:* a value form `VUnfold name spine
~unfolding` keeps every top-level name with its lazily computed unfolding; folded and
unfolded views share work; exact preservation of unfoldings needs, in places, "pairs of
values" one minimally and one maximally unfolded **[cited]**. *Steal:* the pairs, for the
expected type in `check_inner`. *Helps:* SW-858 (alias place 3), SW-859, SW-845. *Cost:*
elaborator. *Full text:* yes (2 pages). Deep read §5.2.

**C5. smalltt unification modes.** github.com/AndrasKovacs/smalltt README. *Claim:* unify in
three modes, rigid (may solve, may speculate), flex (may not solve; any needed solution
fails) and full (unfold every definition); "bounded approximation: it only performs limited
speculation, and switches to full reductions on failure"; meta solutions quoted without
unfolding **[cited]**. *Steal:* name the modes in our unifier docs; Stitchwort's
`same_arguments_solving_nothing` is the flex mode and `meta_against_call` the folded quoting
**[checked]**, so this is mostly confirmation. *Helps:* documentation of `unify.rs`. *Cost:*
small. *Full text:* yes (README).

**C6. O'Brien, Rémy, Scherer, Omnidirectional type inference for ML: principality any way.**
arXiv 2511.10343 (v2 May 2026). *Claim:* constraints may be solved in any order;
a field access or record whose type isn't known is a suspended `match` on the type's shape,
resumed when the shape is known; a suspended constraint never resumed is an error, with
defaulting left as future work; record labels resolve by context, never by guessing, so the
result is principal **[cited]** (first half of the paper read). *Steal:* the rule "resolve by
context, suspend otherwise", and its counter-position to guessing from field names. *Helps:*
SW-805, SW-817, SW-885. *Cost:* elaborator. *Full text:* yes, partly read. Deep read §5.3.

**C7. Xue, Oliveira, Contextual Typing.** ICFP 2024, doi 10.1145/3674655. *Claim:*
generalise bidirectional modes to counters of how much type information a term needs, so
known information about neighbouring terms (other arguments, record labels) flows in either
direction **[unverified]** (abstract). *Steal:* a vocabulary for "this argument needs its type
from the function's later arguments"; possibly a principled order instead of "try in place,
then postpone". *Helps:* SW-859 (argument-order dependence). *Cost:* research. *Full text:*
not read (open access in HKU repository).

**C8. Libal, Miller, Functions-as-constructors higher-order unification.** Annals of Math.
and AI 90 (2022), lix.polytechnique.fr/~dale/papers/fcu-final.pdf. *Claim:* the pattern
fragment extended to metavariable arguments built from bound variables with constructors
(no argument a subterm of another) keeps decidability and most general unifiers
**[unverified]** (abstract). *Steal:* a principled replacement for part of the "last arguments
first" fallback in `first_order` (`unify.rs:836`), which "finds *a* solution rather than the
most general one" (docs/core.md, Elaboration) **[checked]**. *Helps:* fewer surprising
solutions; SW-815 maybe. *Cost:* elaborator. *Full text:* PDF linked, not read.

**C9. Richter, Böhler, From Pattern Unification Towards Pattern Matching Unification.** TyDe
2026, arXiv 2607.18455. *Claim:* constraints from induction principles fall outside pattern
fragments; collect them and solve them with a pattern-matching compiler, inferring solutions
Rocq and Lean reject **[unverified]** (abstract). *Steal:* for SW-815 (a `_` standing for a
function argument), solve the hole by compiling the collected equations `?f c₁ = t₁, ?f c₂ =
t₂` into a match, which Stitchwort's matrix compiler already does. *Helps:* SW-815. *Cost:*
research. *Full text:* not read.

**C10. Liesnikov, Cockx, ExEl: Building an Elaborator Using Extensible Constraints.** IFL
2023, doi 10.1145/3652561.3652565. *Claim:* an elaborator where constraints and solvers are
plug-ins; metavariables are the channels between solvers (implicit arguments, type classes,
tactic arguments) **[unverified]** (abstract and TYPES 2023 slides via search). *Steal:* the
architecture as a reference if Stitchwort's obligations (`auto.rs`), row constraints
(`rows.rs`) and postponed lambdas are unified into one queue (C1). *Helps:* design note for
T1. *Cost:* research. *Full text:* ACM, not read.

**C11. GHC proposal 366, DuplicateRecordFields without ambiguous field access.**
ghc-proposals.readthedocs.io/en/latest/proposals/0366-no-ambiguous-field-access.html.
*Claim:* GHC removed type-directed resolution of ambiguous field selectors and updates
because the rules for when it worked were unclear; warning `-Wambiguous-fields` from 9.4
**[unverified]** (proposal page via search summary). *Steal:* the caution: a type picked from
field names must be predictable from the text alone. *Helps:* SW-805 (D1442). *Cost:* none.
*Full text:* reachable, read only through the summary.

**C12. Gratzer, Sterling, Angiuli, Coquand, Birkedal, Controlling unfolding in type theory.**
MSCS 35 (2025), arXiv 2210.05420. *Claim:* definitions are opaque by default and unfolded
locally and selectively; elaborated into MLTT with extension types; normalisation proved;
implemented in cooltt, and it inspired Agda's `opaque`/`unfolding` **[unverified]** (abstract).
*Steal:* a scoped `unfolding f in …` as the principled form of SW-796's "rewrite f unfolds f
one step" and of `opaque def`'s `f.unfold`. *Helps:* SW-798 (transparency levels: evidence
that local unfolding is the better-founded alternative), opaque-definitions.md. *Cost:*
elaborator (elaborates into the existing kernel, if it follows the paper) **[inferred]**. *Full
text:* arXiv, not read.

**C13. Zhao, Maroof, Dukkipati, Blinn, Pan, Omar, Total Type Error Localization and Recovery
with Holes.** POPL 2024 (distinguished paper). *Claim:* inconsistent unification constraints
are localised to type and expression holes so every program gets a type and editing services
keep working **[unverified]** (abstract). *Steal:* when a declaration fails, keep elaborating
with the failing part replaced by an error hole, so later errors and LSP hovers still work.
*Helps:* errors with several faults; the language server (docs/proposals/language-server.md).
*Cost:* elaborator. *Full text:* not read.

**C14. Khakimova et al., Enhancing Proof Assistant Error Messages with Hints: A User Study.**
ITP 2026 (LIPIcs 382), with Cockx. *Claim:* 70 students; hints on three Agda errors
(whitespace, confusable Unicode, too few arguments) improved the number of compiling
submissions and rated helpfulness; wrong hints lowered ratings but not success
**[unverified]** (thesis and paper abstracts). *Steal:* the "too few arguments" hint
Stitchwort already has (`check.rs:3931`, "one more argument") **[checked]**; the Unicode
confusables hint is worth a look for the parser. *Helps:* errors. *Cost:* small. *Full text:*
not read.

**C15. Bhanuka, Parreaux, Binder, Brachthäuser, Getting into the Flow.** OOPSLA 2023,
arXiv 2402.12637. *Claim:* present a type error as the faulty data flow, a sequence of
program locations; a quantitative study found no improvement, a qualitative one found demand
**[unverified]**. *Steal:* for SW-859-style errors ("whichever comparison solved `b` first"),
report where a metavariable got its solution. *Helps:* E-CANNOT-INFER and mismatch notes.
*Cost:* elaborator. *Full text:* arXiv, not read.

**C16. Porter et al., Incremental Bidirectional Typing via Order Maintenance.** OOPSLA 2025,
arXiv 2504.08946. *Claim:* fine-grained incremental re-typing after edits, proved equal to
re-analysis in Agda, orders of magnitude faster **[unverified]**. *Steal:* later, for the
playground and LSP. *Helps:* cluster 7. *Cost:* research. *Full text:* not read.

**C17. Lean dot notation through unfolding.** `App.lean`, `resolveLValLoop` (lines about
1678–1694). *Claim:* `e.f` postpones while `e`'s type is unknown; then tries the namespace of
the type's head; on failure unfolds the type one step and tries again **[cited]**. *Steal:* the
unfold-and-retry order matches what alias-functions.md built for places 1 and 2; with C1 a
field access on an unknown type would postpone rather than fail. *Helps:* SW-847, SW-858.
*Cost:* small once C1 exists. *Full text:* yes.

## 5. Deep reads

### 5.1 Lean 4's postponement ladder (C1, C17)

**What Lean does** [cited, source files above]. Every term elaborator gets an optional
expected type. Elaborators that can't proceed without it call `tryPostponeIfMVar` /
`tryPostponeIfNoneOrMVar`. When postponing is allowed, that throws a postpone exception; the
caller replaces the term with a fresh *synthetic* metavariable and records the syntax, the
expected type and the local context. Record literals do this (`getStructName`,
`StructInst.lean`: "This function tries to postpone execution if the expected type is not
available"), and so does field access on a value of unknown type (`resolveLValLoop`, before
anything else). `synthesizeSyntheticMVars` then resumes pending items in creation order,
repeating while any progress is made. When none is made, it runs, in order:

1. resume everything with postponing **disabled**, but errors postponed: each item must now
   commit, and one that commits may teach a type to another;
2. default instances (numeric literals default to `Nat`);
3. resume with postponing disabled and errors reported;
4. run tactic blocks;
5. report what is still stuck.

The source's own example is the let-bound case of SW-847: in `let x := ⟨1, 2⟩; Prod.fst x`,
the anonymous constructor is postponed, `Prod.fst x` teaches `x : Prod ?α ?β`, and the
constructor is then resumed against that type. The scope of a ladder is `withSynthesize`,
typically a whole declaration body or a tactic.

Lean's `fun x => …` with no binder type doesn't postpone: it makes a metavariable for `x`'s
type and elaborates the body; what postpones is the first thing in the body that needs the
type (`x.value`). So Lean postpones the *smallest* failing piece, not the whole lambda.

**How Stitchwort does it today** [checked]. `apply_args_postponing` (`check.rs:1893`): within
one application, a lambda or method section whose parameter type is unknown is first tried in
place; on failure the snapshot is restored, a placeholder metavariable is put in the argument's
slot, and the lambda is checked after the later arguments. Nothing else postpones: a record
literal (SW-817, SW-885), a let-bound lambda (SW-847, "has no later argument to postpone
against") and a tuple part all fail with `E-CANNOT-INFER` at once. Two other queues exist and
are retried at the end of a declaration: auto obligations (`lib.rs:327`) and row constraints
(`lib.rs:335`). The SW-859 note shows the try-in-place rule is itself a source of
argument-order dependence: a lambda that *succeeds* in place can solve a shared metavariable
with the unfolded type.

**Mapping.** One queue of postponed checks per declaration, each holding (expression,
expected type value, context, placeholder metavariable). `check` on a record literal, a
field access or a lambda body's `x.f` with an unknown type would postpone instead of failing.
The existing end-of-declaration step that solves obligations (`solve_obligations_until_stuck`,
`lib.rs:1083`) would become the ladder: resume postponed checks while progress is made; then
resume with postponing off; then defaults (SW-805's field-name rule would sit here, §5.3);
then obligations; then errors. The lambda-only rule in `apply_args_postponing` could become
"postpone only when the parameter type is an unknown", Lean's test, dropping the try in place.

**Risks.**
- *Changes what is accepted, in both directions* [inferred]. Today's try-in-place keeps
  "what already worked is elaborated as before" (`check.rs:1797`); Lean's "postpone if the
  type is unknown" would change which comparison solves a metavariable first, so it may fix
  some SW-859 cases and break some programs that only work by the current order. Measure on
  std, examples and aoc before deciding.
- *Error locations* [inferred]. A postponed check that finally fails reports at the end of
  the declaration; the message must still point at the term and say what type it ended up
  checked against.
- *Interaction with `auto` and rows* [inferred]. Obligations already wait for the end; a
  postponed check may now produce new obligations after that point, so the ladder has to loop
  over all three queues together, as Lean's loop does over all synthetic kinds.
- *Cost* [inferred]. Each postponement saves context and placeholder; Lean's experience is
  that this is cheap, but our snapshots (`undo::Snapshot`) are per-try, so the design must say
  whether postponed items need them.

**Next step.** A design note (T1), measured with a temporary switch on std/aoc as SW-859's
investigation did, deciding (a) which forms postpone, (b) the ladder, (c) whether try-in-place
stays for lambdas.

### 5.2 Kovács: glued values and keeping names (C4, C5)

**What it says** [cited]. Values carry `VUnfold x spine ~v`: the folded head and spine,
plus the unfolding as a lazy field that `vapp` extends alongside. Forcing peels unfoldings to
head normal form; quoting chooses folded or unfolded per use. Two sentences matter for us:
"to exactly preserve unfoldings, in some places we need to compute with *pairs of values*
where the two values are convertible, but one value is 'minimally' unfolded and the other one
is 'maximally' unfolded", and the motivation that metavariable solutions "tend to blow up in
size if definitions are unfolded all the time". smalltt's README adds the unification modes
(rigid, flex, full) and that solutions are quoted without unfolding.

**Where Stitchwort is** [checked]. Glued calls (`Value::Call`, docs/core.md "Glued calls")
are this idea for definitions with case trees applied to all their arguments; constants such
as `FreeSpace` are glued too (alias-functions.md §3.2 item 1). A metavariable against a call
is solved with the call (`meta_against_call`, `unify.rs:863`); two calls of one definition
compare arguments first without solving (`unify.rs:504`), which is smalltt's flex mode.
What's missing is the pair: `check_inner` begins `let named = expected; let expected =
force(g, expected.clone())?` (`check.rs:3093`), and the comparisons below use the forced value,
so a placeholder solved there gets the unfolded type. SW-846's `name_unknown_type`
(`check.rs:3170`) patches one case, a bare variable. The broad patch (compare with the
unforced type) broke std (alias-functions.md §3.3), plausibly because many rules below
pattern-match on the forced shape **[inferred]**.

**Mapping.** Thread both values through `check_inner`: dispatch on the forced value (as now),
but whenever a branch hands the expected type to unification *with an unknown on the other
side* (`compare`, a placeholder's type), hand it the named value. That is "pairs of values" in
Kovács's sense, restricted to the one place the trace found. It doesn't change what is equal,
only how a solution is written [inferred]: `meta_against_call` already guarantees the
solution is the same up to unfolding.

**Risks.** The std breakage of the earlier patch is unexplained; the design must find which
comparisons broke (they may rely on the solution being unfolded for a later `force`-free
match) [unverified]. Solutions that are calls cost a `force` later; the folded-calls
measurements suggest this is cheap, but they were not for this path [inferred].

**Next step.** A short design note under SW-858 (T3): list every use of `expected` in
`check_inner` and its callees, classify each as "dispatch" or "solve", rerun the failing std
files with the named value only on the "solve" uses.

### 5.3 OmniML: suspend on the shape, don't guess (C6, C11)

**What they do** [cited, first half]. Typing produces constraints; a construct whose
meaning depends on a type's shape (`e.ℓ` with record-label overloading, a record literal,
polytype unboxing) generates `match τ with branches`, suspended until `τ`'s head constructor
is known. Any order of solving gives the same result. Labels resolve from *context*: OCaml's
`let ex_3 r = (r.x, (r : point).y)` is rejected by OCaml (it commits to the latest type with
`x` when it reaches `r.x`) and accepted by OmniML (it waits for `(r : point)`). Nothing is
guessed: `let ex_1 r = r.x` is rejected by both. "A match constraint that is never
discharged is considered unsatisfiable"; the prototype can attach a default to a suspended
constraint, unformalised. They call the extra complexity real.

GHC went the same way from the other side: proposal 366 removed type-directed field
disambiguation because when it applied was unclear (C11, unverified).

**Mapping onto SW-805 and SW-817.** SW-805 (D1442, built on branch record-literal-inference)
picks a record literal's type when exactly one record type in scope has exactly those fields;
that is OCaml's closed-world rule, the one OmniML keeps for literals with every label given
and treats as resolving from the labels alone [cited]. SW-817 asks to postpone the literal
instead. OmniML and Lean's ladder (§5.1) agree on an order that answers both:

1. a literal (or field access) whose expected type is unknown is postponed;
2. if the type is learned, it's checked against it, whatever its field names;
3. only when nothing else can be learned does the field-name rule apply, as a default, with
   a note saying which type was chosen and why.

This keeps today's behaviour wherever the type is known, makes SW-817's `foldLeft { enabled =
True, total = 0 } step` work by context, and leaves the guess as a last resort that cannot
contradict information the program provides elsewhere [inferred].

*Assumption, stated in full:* step 3's default is applied only after every postponed check
that could fix the type has been resumed with postponing off. If a default were applied
earlier, a later check could find a different type and the program would be rejected for
the order of its arguments, which is SW-859's problem again.

**Risks.** The default makes adding a record type to a namespace break code that used the
default (two types now fit). Stage it so that the error names both types and suggests the
annotation [inferred]. GHC's experience (C11) is the reason to keep step 3 narrow.

**Next step.** Fold into T1 as its record-literal section, or a separate decision (D1861).

### 5.4 Unifier heuristics: scope-only constant approximation and lazy delta (C2, C3)

**What Lean does** [cited, `ExprDefEq.lean`]. Outside the pattern fragment: A5/A6
first-order approximation (`?m a₁ … aᵢ aᵢ₊₁ … = f b₁ …`: unify the trailing arguments, then
`?m a₁ … aᵢ = f`), which is Stitchwort's fallback (`first_order`, `unify.rs:836`)
**[checked]**. A7 constant approximation: `?m s₁ … sₙ = t` solved as `fun _ … _ => t`. Lean
notes it gives bogus solutions in general and applies it by default only to arguments that
"represent dependencies" on the local scope, tracked by `numScopeArgs`; its example is `let f
(x : _) := pure "hello"; f ()`, where `?m () String = IO String` should give `?m := fun _ =>
IO`. For two *different* definitions, `isDefEqDeltaStep` unfolds the one with the larger
definitional height first and only unfolds both when heights tie; with the same name it
first tries the arguments (`tryHeuristic`).

**Where Stitchwort is** [checked]. Metavariables are applied to every variable in scope
(docs/core.md, Elaboration), so most arguments of a metavariable are exactly Lean's "scope
arguments". `solve` already ignores some spine positions: those marked ignorable for auto
proofs (SW-323) and unit-typed constructors (`unify.rs:909`). There is no height: two
different definitions are compared by unfolding both (SW-386, docs/core.md "Conversion") and
no `height` appears in `crates/core` or `crates/elab`.

**Mapping.**
- *Scope-only constant approximation.* When `?m spine = t` fails as a pattern only because a
  spine position that came from "applied to the variables in scope" holds a non-variable
  (after a substitution, say), drop that position. This generalises the SW-323 rule from auto
  proofs to all metavariables [inferred]. Whether it helps SW-815 depends on which constraint
  fails there, which the ticket doesn't record; measure first.
- *Height ordering.* Give each definition a height (one more than the greatest height of the
  definitions its body mentions). When unification or `conv` meets two different calls, unfold
  only the higher one and retry the arguments-first rule. For `g x` against `f y` where `g`'s
  body is `f (h x)`, this reaches `f (h x)` vs `f y` and compares arguments, instead of
  unfolding both and comparing case trees [inferred]. Kernel `conv` would gain it too only if
  measured; it changes cost, not what's equal, as long as the fallback still unfolds both
  [inferred].

**Risks.** Constant approximation is unsound for *uniqueness*, not for typing: the kernel
re-checks every term, so a wrong guess shows up as an elaboration error elsewhere, never as a
false proof (DESIGN.md §13, principle 4) [inferred]. Heights need storing per definition and
hashing must ignore them [inferred].

**Next step.** Two measurement tickets (T4, T5), no design note until numbers exist.

## 6. Steal next

Ranked by value over effort. "Value" is how many open tickets it helps and how often users
hit them in AoC notes; "effort" is the cost scale above.

| Rank | Idea | Source | Helps | Cost |
|---|---|---|---|---|
| 1 | One queue of postponed checks with Lean's ladder | C1, C17 | SW-817, 847, 885, 509, part of 859 | elaborator (design note first) |
| 2 | Record literal type from field names only as the ladder's last default | C6, C11, C1 | SW-805, 817 | small once 1 exists |
| 3 | Named and forced expected type side by side in `check_inner` | C4, C5 | SW-858, 859, 845 | elaborator |
| 4 | Height-ordered unfolding when two different calls meet | C2 | SW-386 path; speed | small (measure) |
| 5 | Error holes: keep elaborating past a failed sub-term | C13 | several errors per run; LSP | elaborator |
| 6 | Report where a metavariable was solved in E-CANNOT-INFER / mismatch notes | C15 | SW-859-style confusion | small |
| 7 | Scope-only constant approximation | C2 | SW-815 maybe | small (measure) |
| 8 | Scoped `unfolding f in …` instead of transparency levels | C12 | SW-796, 798 | research |
| 9 | Pattern-matching unification for function holes | C9 | SW-815 | research |
| 10 | Functions-as-constructors fragment replacing part of the first-order fallback | C8 | predictability | elaborator |

## 7. Proposed tickets

Label `research` on each. Not added to the board.

**T1. Design note: one queue of postponed checks (Lean's ladder).** Record literals,
let-bound lambdas' field accesses, tuple parts and effectful record literals fail with
`E-CANNOT-INFER` when their type isn't known yet, because only lambdas postpone and only within
one application (`apply_args_postponing`). Lean postpones any elaborator whose expected type is
unknown and resumes it at the end of the declaration through a fixed ladder (resume; resume
with postponing off; defaults; tactics; report). Write a note that decides which forms
postpone, the ladder (merging today's obligations and row constraints), whether the
try-in-place rule for lambdas stays, and how errors from late failures are located. Measure a
throwaway switch on std, examples and aoc. Refs: docs/research/elaboration.md §5.1; SW-817,
SW-847, SW-885, SW-509, SW-859.

**T2. Record literal inference order: context first, field names as the last default.**
Combine SW-805 and SW-817: a record literal with unknown type is postponed; if nothing fixes
its type, the field-name rule (one record type with exactly those fields) applies as a default
after every postponed check has been resumed with postponing off, with a note naming the type
chosen. Follows OCaml's OmniML design (no guessing while context can decide) and GHC's removal
of type-directed field disambiguation (keep the guess narrow). Depends on T1. Refs: §5.3.

**T3. Design note: keep the expected type's name where unification solves against it.**
`check_inner` forces the expected type before comparing, so a placeholder solved there gets
the unfolded type (alias place 3, SW-858). Following Kovács's "pairs of values", classify each
use of `expected` in `check_inner` as dispatch (needs the forced shape) or solve (should get
the named value), and find why the earlier broad patch broke `std/List/Lemmas.sw` and
`Toolkit.sw`. Refs: §5.2; alias-functions.md §3.3; SW-858, SW-859, SW-845.

**T4. Measure: unfold the higher definition first when two different calls meet.** Add a
definitional height per definition and, in unification (and optionally `conv`), unfold only
the higher of two different calls before retrying arguments-first, falling back to unfolding
both. Measure steps on the bench, std and aoc. Lean's `isDefEqDeltaStep` does this. Refs:
§5.4.

**T5. Investigate SW-815's failing constraints against Lean's approximations.** For the AoC
day 12 and day 22 cases, log the unification problems that leave the function hole unsolved;
classify each as pattern, first-order-approximable, scope-only constant approximation (Lean's
A7 with `numScopeArgs`), or needing case analysis (Richter and Böhler, TyDe 2026). Decide from
that whether SW-815 is a small unifier change or research. Refs: §5.4, C9.

**T6. Errors: keep elaborating past a failed sub-term (error holes).** After the first error
in a declaration body, replace the failing term with a typed error hole and continue, so
later independent errors are reported and the language server keeps types and goals for the
rest. Hazel's POPL 2024 work localises every inconsistency to a hole. The kernel never sees a
declaration with an error hole. Refs: C13.

## 8. Decisions

**D1860. Make one general postponement mechanism (T1) the direction for the record-literal
and let-lambda inference tickets (SW-817, 847, 885), rather than extending the lambda-only
rule case by case?** Assumption: Lean's experience transfers, i.e. postponing on an unknown
expected type changes few currently accepted programs; T1's measurement checks it before any
code. [Yes, design note first.]

**D1861. For SW-805, apply the field-name rule only as a last default after postponement
(T2), instead of eagerly as built on branch record-literal-inference?** Assumption: T1
exists; without it, the eager rule is the only way to accept SW-817's example. [Yes if D1860
is yes; otherwise keep D1442 as built.]

**D1862. Take T3 (named expected type in `check_inner`) as the route for SW-858, ahead of
SW-859's ordering rules?** Assumption: most argument-order cases come from the forced
expected type, as SW-859's 29 Oct note found ("whichever comparison solves `b` first decides
its name"). [Yes.]

## 9. Sources not reached

- Full texts not read (abstract or summary only): Contextual Typing (ICFP 2024), Local
  Contextual Type Inference (POPL 2026), Frost (arXiv 2607.16061: the indexed text was
  garbled), Libal and Miller 2022, Richter and Böhler 2026, ExEl (ACM), Gratzer et al. 2025,
  Zhao et al. 2024, the ITP 2026 hints paper, GHC proposal 366 (read through a summary).
- OmniML (arXiv 2511.10343): only the first half of the HTML was read.
- Fissore and Tassi, PPDP 2024: no abstract or PDF found.
- TyDe 2026 programme: not found (only the call for papers); the Richter and Böhler abstract
  says it is to be presented there.
- No 2023–2026 paper by Kovács on elaboration found beyond the WITS 2024 abstract; blogs of
  Kovács, Cockx, Ullrich and de Moura were not searched individually, nor the Lean Zulip.
- Idris 2 new-core talk (2024): only a wiki abstract via search.
- Not searched: CPP, ITP and RocqPL programmes year by year; Lean workshop programmes;
  theses beyond those found by the queries. A refresh should start there.
