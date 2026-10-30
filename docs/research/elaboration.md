# Literature trawl: elaboration

**Counts: screened 64; carded 20; read in full 20; not read 0 (screened-only items are listed in
§3 and §9; none supports anything here).**

Redone 30 Oct 2026 from full texts; replaces the 29 Oct abstract-based version.

**Claims from the 29 Oct version found wrong** (each checked this time against the full source
or our code):

1. *Query Q8: "Local Contextual Type Inference, POPL 2026; arXiv 2511.10343".* Wrong ID. The
   arXiv API gives 2511.10343 as O'Brien, Rémy and Scherer, *Omnidirectional type inference
   for ML* (the old C6). No arXiv copy of the POPL 2026 paper was found.
2. *Old C14: the hints study had "70 students".* Wrong. The ITP 2026 paper is *Enhancing
   Interactive Theorem Prover Error Messages with Hints* (Khakimova, Juhošová, Reinders,
   Cockx; LIPIcs ITP.2026.5), not the title the old card gave. §4 reads "After cleaning our
   data, we recorded a total of 56 participants … (divided 32 / 24 over the variants)". The 70
   comes from the master's thesis, which I didn't read (C20).
3. *Old C11 and §5.3: GHC proposal 366 is "counter-evidence for SW-805".* Misread. The
   proposal removes the *type-directed* rules (1, 2, 5, 6) but keeps rule 4, "If there is only
   one datatype that has all the fields being updated, use that datatype". It keeps it because
   it "can be determined during name resolution rather than requiring information from
   type-checking" (C9). That is a field-name rule like SW-805's. The old card's
   "`-Wambiguous-fields` from 9.4" isn't in the proposal. The proposal names the warning but
   no release.
4. *Old C2, §5.4 and T4: Lean's unifier "compares two different definitions by unfolding the
   one with the greater definitional height first" (`isDefEqDeltaStep`).* Wrong for
   unification. In `ExprDefEq.lean` the height order (`unfoldDefEq`) applies only
   `if !t.hasExprMVar && !s.hasExprMVar`: "If `t` and `s` do not contain metavariables, we
   simulate strategy used in the kernel". With metavariables it uses
   `unfoldComparingHeadsDefEq`. `isDefEqDeltaStep` is documented as "currently used to solve
   constraints of the form `(f a).i =?= (g a).i`" (C2). So old T4's "Lean does this" doesn't
   hold where T4 wanted it.
5. *Old C3 and C5: "Stitchwort already tries arguments first without solving anything", so
   Agda's lossy unification is "nothing new" and smalltt's flex mode is "mostly
   confirmation".* Incomplete. That holds only for two *glued* calls (`unify.rs:756-763`).
   Two calls of the same definition that are *stuck* are compared argument by argument *with*
   solving (`unify.rs:929-944`), and so does `unify_solving_arguments` (`unify.rs:103`). That
   is Agda's opt-in lossy heuristic, and smalltt's README says smalltt "does not allow
   approximate meta solutions" (C4, C5; §5.2).
6. *Old §1 and §5.1: Stitchwort "postpones only lambdas, only inside one application, and only
   after a failed try in place".* Wrong already at the old base (`02eb7b62`):
   - a method section was postponed without any try ("A section is always postponed then",
     `check.rs:1795-1796` there and now);
   - a lambda that failed in place could be checked again after the application's expected
     type was compared (`late_able`, `check.rs:1938`).

   Since SW-896, unification also puts aside pairs stuck on an unknown (`unify.rs:31-41`).

*SW-894, cluster 3. Researched 30 October 2026 against `main` at `e2d60bbd`. Research only: no
code changed, no tests run. Window: 2022 onwards (D1831). Older work appears only where
in-window work or our own code relies on it, and is marked **classic**.*

Reading protocol: every card says **Full text: read (source)**. PDFs were read with
`pdftotext` from `nix shell nixpkgs#poppler-utils`. Source files, documentation pages and the
GHC proposal were fetched whole through `gh api` and read as text. Lean 4 files are at commit
`0f852cc8` of `leanprover/lean4` (master on 30 Oct 2026). For a long paper, "read" means the
sections named on the card were read in full and the rest skimmed or not read, as the card
says. For a source file it means the named functions and their comments.

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

Stitchwort's elaborator already has most of the machinery the literature describes. It has
pattern unification with pruning, glued calls, a per-declaration obligations loop, and coherent
instance search that waits rather than backtracks. Since SW-896 it also puts aside comparisons
stuck on an unknown. Four things are worth acting on:

- **One postponement queue, with Lean's ladder (§5.1).** Lean postpones any elaborator that
  needs an unknown expected type, then resumes in a fixed order (C1). It also has a body-first
  `let` (`let_delayed`, `+postponeValue`), which is SW-847's missing piece. OmniML gives a
  principled version of "suspend until the shape is known" (C8). Stitchwort postpones only
  lambda arguments within one application (`check.rs:1893`), and record literals (SW-817,
  SW-885) and let-bound lambdas (SW-847) fail at once. T1, D1990.
- **Name the lossy rule and test it (§5.2).** When two calls of the same definition are stuck,
  the unifier equates their arguments and keeps the solutions (`unify.rs:929-944`). Agda makes
  this opt-in because it "will cause Agda to ignore some possible solutions" (C4). smalltt
  forbids it (C5). The kernel re-check keeps it sound. It does not stop the elaborator
  choosing a different implicit than the user meant. Nothing in docs/core.md says so. T2.
- **SW-805's field-name rule is the one GHC kept (§5.3).** GHC kept "only one datatype has all
  the fields" because it is decided from the text alone. OmniML keeps the closed-world rule
  for a literal with every label (C8, C9). Both support the rule as built, used only when the
  expected type is unknown. T3, D1991.
- **Cheap error and performance wins (§5.4, T4-T6).** Correct hints measurably help new Agda
  users, and wrong ones did no measurable harm (C20). Stitchwort already reports every failed
  case branch (`lib.rs:4099-4107`). smalltt's three asymptotic benchmarks are ready-made
  probes (C5). Lean's `elab_as_elim` infers a motive from the expected type (C3), where our
  `T.induct` uses write it by hand.

Not recommended now: the functions-as-constructors fragment (C11), pattern-matching
unification (C12, a prototype whose solutions aren't core terms yet), complete search (C13),
contextual typing (C10, a system without unification variables), an extensible-constraints
architecture (C15), and tabled resolution (C17: Stitchwort has no overlapping instances).

## 2. Method

**Stitchwort read first** [checked]:
- docs/core.md "Elaboration" (`:277-304`) and "Evaluation and conversion" (`:226-238`),
  including "Sums stuck on an unknown" and "Comparisons put aside" (`:284-285`);
- `crates/elab/src/check.rs`: `apply_args_with` and `apply_args_postponing` (`:1781-2125`),
  `check_inner` (`:3086`), the too-few-arguments note (`:3931`);
- `crates/elab/src/unify.rs`: the header, `run`, `blocked`, `unify_step`,
  `same_arguments_solving_nothing`, `first_order`, `meta_against_call` and `solve`;
- `crates/elab/src/auto.rs` (header), `interfaces.rs` (outline) and
  docs/proposals/interfaces.md §5.5 (`:569-676`);
- `crates/elab/src/lib.rs` `finish` (`:1085`) and the branch-failure recovery (`:4099-4116`);
- `matching.rs` and `lift.rs` headers, and `crates/syntax/src/lexer.rs` Unicode handling;
- docs/proposals/opaque-definitions.md (status) and the board bodies of SW-509, 805, 815,
  817, 822, 845-847, 858, 859, 885 and 896.

**Sources.** Twelve PDFs, downloaded to the session scratchpad:
- from arXiv: 2511.10343, 2607.18455, 2603.01463, 2511.15819, 2210.05420, 2402.12637,
  2001.04301, plus 2607.16061, 2504.08946 and 2307.08523, which were opened only;
- from author pages: andraskovacs.github.io wits24abstract and wits26prez, and
  lix.polytechnique.fr fcu-final;
- from Dagstuhl: LIPIcs.ITP.2026.5;
- from hazel.org: marking-popl24;
- from Internet Archive copies of the ACM PDFs: 10.1145/3674655 and 10.1145/3652561.3652565.
  ACM itself returned 403. Semantic Scholar's API lists both as GOLD open access.

Through `gh`:
- lean4 `src/Lean/Elab/SyntheticMVars.lean`, `App.lean`, `Binders.lean` and
  `StructInst.lean`;
- lean4 `src/Lean/Meta/ExprDefEq.lean` and `SynthInstance.lean` (fetched, not used), and
  `src/Lean/Declaration.lean`;
- agda `doc/user-manual/language/lossy-unification.lagda.rst`;
- smalltt `README.md`;
- ghc-proposals `0366-no-ambiguous-field-access.rst`.

DBLP returned a bot page to scripts, and Semantic Scholar's search rate-limited. I used the
arXiv API and Semantic Scholar's DOI lookup instead, sending no personal data.

**Web searches: 5** (of a budget of about 25), all on 30 Oct 2026:

| # | Query | Useful result |
|---|---|---|
| S1 | `"Enhancing Proof Assistant Error Messages with Hints" ITP 2026 LIPIcs` | LIPIcs ITP.2026.5 PDF (C20) |
| S2 | `Xue Oliveira "Contextual Typing" ICFP 2024 pdf` | DOI only (C10 then via the Internet Archive) |
| S3 | `arXiv 2025 2026 elaboration dependent types unification postponement constraints metavariables implementation paper` | Kovács WITS 2026 slides (C7); arXiv 2605.00655 |
| S4 | `Lean 4 type class synthesis 2025 2026 new instance resolution algorithm performance paper OR release notes` | Lean 4.36.0-rc1 notes (search summary only) |
| S5 | `elaborating dependent pattern matching paper 2024 2025 Agda Lean "case trees" coverage unification` | nothing in-window beyond Lieverse 2024 (MSc) |

Searches returned results every time. I stopped at five because the old register's leads
plus S3 covered the scope. As a result, these areas are lightly covered: elaborating effects
and rows (effects.md has the in-window paper), incremental elaboration (infrastructure.md
C12, C15 and C18), and dependent pattern matching (no in-window paper found).

## 3. Screened list

64 sources: 20 carded (all read), 22 maybe, 22 drop. A "maybe" or "drop" was judged on title,
abstract, a partial read or another register, and supports nothing below.

| # | Source | Verdict | Why |
|---|---|---|---|
| 1 | Lean 4 postponement: `SyntheticMVars.lean`, `App.lean`, `StructInst.lean`, `Binders.lean` | card C1 | §5.1 |
| 2 | Lean 4 `ExprDefEq.lean`: pattern conditions, approximations A1-A7, lazy delta | card C2 | §5.2 |
| 3 | Lean 4 `@[elab_as_elim]` (`App.lean`) | card C3 | T5 |
| 4 | Agda manual, *Lossy Unification* | card C4 | §5.2 |
| 5 | Kovács, smalltt README, **classic** system | card C5 | §5.2, T4 |
| 6 | Kovács, Efficient Evaluation with Controlled Definition Unfolding, WITS 2024 abstract | card C6 | SW-858 |
| 7 | Kovács, Observing Definitional Equality, WITS 2026 slides | card C7 | §5.2 |
| 8 | O'Brien, Rémy, Scherer, Omnidirectional type inference for ML, arXiv 2511.10343v2 | card C8 | §5.1, §5.3 |
| 9 | Gundry, GHC proposal 366 | card C9 | §5.3 |
| 10 | Xue, Oliveira, Contextual Typing, ICFP 2024 | card C10 | not recommended |
| 11 | Libal, Miller, Functions-as-constructors HOU (author manuscript, AMAI) | card C11 | not recommended |
| 12 | Richter, Böhler, Towards Pattern Matching Unification, arXiv 2607.18455 | card C12 | SW-815 context |
| 13 | Norman, Avigad, Implementing DTT Inhabitation and Unification, arXiv 2603.01463 | card C13 | not recommended |
| 14 | Liesnikov, Binder, Süberkrüb, Filling the Gaps of Polarity, Programming 2025 | card C14 | §5.2 |
| 15 | Liesnikov, Cockx, ExEl, IFL 2023 | card C15 | §5.1 |
| 16 | Gratzer, Sterling, Angiuli, Coquand, Birkedal, Controlling unfolding, MSCS 2025 (arXiv v2) | card C16 | SW-796, SW-798 |
| 17 | Selsam, Ullrich, de Moura, Tabled Typeclass Resolution, 2020, **classic** | card C17 | interfaces |
| 18 | Zhao et al., Total Type Error Localization and Recovery with Holes, POPL 2024 | card C18 | §5.4 |
| 19 | Bhanuka, Parreaux, Binder, Brachthäuser, Getting into the Flow, arXiv 2402.12637 | card C19 | §5.4 |
| 20 | Khakimova, Juhošová, Reinders, Cockx, Enhancing ITP Error Messages with Hints, ITP 2026 | card C20 | §5.4 |
| 21 | Tang et al., Bidirectional Typing with Freezing, Skeletons, and Ghosts, arXiv 2607.16061 | maybe | first-class polymorphism; abstract and §1 only |
| 22 | Porter et al., Incremental Bidirectional Typing via Order Maintenance, OOPSLA 2025 | maybe | simply typed, structural edits; abstract and §1 only |
| 23 | Felicissimo, Generic bidirectional typing for dependent type theories, arXiv 2307.08523 | maybe | theory of modes; not read |
| 24 | Xue, Cui, Jiang, Oliveira, Local Contextual Type Inference, POPL 2026 | maybe | System F follow-up of row 10; not found |
| 25 | López Juan, Danielsson, Practical dependent type checking using twin types, TyDe 2020, **classic** | maybe | heterogeneous postponement; cited by C4 and C7 |
| 26 | López Juan, Practical Heterogeneous Unification for Dependent Type Checking, PhD 2021 | maybe | same |
| 27 | Sirman, Lennon-Bertrand, Krishnaswami, OTT with NbE, TYPES 2024 | maybe | cited by C7 |
| 28 | Kovács, 2ltt-impl (repository) | maybe | C7's implementation; not read |
| 29 | Lean 4.36.0-rc1 release notes, persistent instance cache (#14316, #15399) | maybe | search summary only |
| 30 | "Type Theory With Erasure", arXiv 2605.00655 | maybe | elab-zoo based; search excerpt only |
| 31 | Lean 4.9 incremental elaboration (#3940) | maybe | infrastructure.md C15 |
| 32 | rust-analyzer, Durable incrementality (2023) | maybe | infrastructure.md C12 |
| 33 | Nawrocki, Ayers, Ebner, Lean user widgets, ITP 2023 | maybe | LSP cluster |
| 34 | Juhošová et al., novices and ITPs, TyDe 2024, ICPC 2025 | maybe | cited by C20 |
| 35 | Eremondi, Swierstra, Hage, replay graphs, 2019, **classic** | maybe | order-insensitive blame |
| 36 | Gould, Bowman, syntax- vs type-directed NbE, TyDe 2025 | maybe | performance |
| 37 | Cockx, Abel, Elaborating dependent (co)pattern matching, JFP 2020, **classic** | maybe | first-match semantics, which we follow |
| 38 | Fredriksson, sixty, **classic** system | maybe | cited by C6 |
| 39 | de Moura, Avigad, Kong, Roux, Elaboration in DTT, 2015, **classic** | maybe | Lean 3 elaborator |
| 40 | Ikemori, Cong, Masuhara, Leijen, Closed Effect Rows, TFP 2022 | maybe | effects.md card; not re-read |
| 41 | Kovács, first-class implicit function types, ICFP 2020, **classic** | maybe | not read |
| 42 | Agda instance search, discrimination trees (PR 7109) | maybe | only if instance counts grow |
| 43 | Serrano et al., Quick Look, ICFP 2020, **classic** | drop | impredicativity; Stitchwort has none |
| 44 | Baanen, instance parameters in mathlib, CICM 2022 | drop | overlapping instances |
| 45 | Lean Zulip, tabled-resolution loop (Jan 2026) | drop | secondary |
| 46 | Shen, Shi, Keep the Proof State Live, arXiv 2605.25556 | drop | tactic search |
| 47 | Danielsson, Geng, opaque definitions, TyDe 2025 | drop | already used by opaque-definitions.md |
| 48 | Blinn et al., ChatLSP, OOPSLA 2024 | drop | LLM tooling |
| 49 | Joram, Annus, Term search in Rust, TyDe 2024 | drop | hole filling |
| 50 | Takimoto et al., Unification modulo isomorphisms, TyDe 2025 | drop | library search |
| 51 | Lieverse, case trees to eliminators, MSc 2024 | drop | we keep case trees |
| 52 | Ullrich, de Moura, `do` unchained, ICFP 2022 | drop | effects cluster |
| 53 | Wright, Kammar, elaborator reflection, TyDe 2024 | drop | no reflection here |
| 54 | Tang, Lindley, Rows and Capabilities as Modal Effects, POPL 2026 | drop | effects cluster |
| 55 | Paszke, Xie, infix-extensible records, TyDe 2023 | drop | later |
| 56 | Fissore, Tassi, HOU for free, PPDP 2024 | drop | not found; Elpi-specific |
| 57 | Bauer, Petković, extensible equality checking, LMCS 2023 | drop | user-extensible conversion |
| 58 | Rocq reversible coercions | drop | no coercions |
| 59 | Narya holes | drop | no implicits |
| 60 | Kovács, 2LTT staging, ICFP 2022/2024 | drop | cluster 6 |
| 61 | McTT, ICFP 2025 | drop | cluster 7 |
| 62 | Monnier, Normalizable types, TyDe 2024 | drop | cluster 1 |
| 63 | Idris 2 new core talk; Frex (2023) | drop | runtime; anecdote |
| 64 | Lennon-Bertrand, Complete bidirectional typing for CIC, ITP 2021 | drop | kernel side |

## 4. Cards

Cost scale: **small** (a local change in `crates/elab`), **elaborator** (a design change in
`crates/elab`, no kernel change), **kernel**, **research**.

**C1. Lean 4's postponement** (`SyntheticMVars.lean`, `App.lean`, `StructInst.lean`,
`Binders.lean` at `0f852cc8`).

*Claim:* an elaborator that needs its expected type calls `tryPostponeIfMVar` or
`tryPostponeIfNoneOrMVar`. When postponing is allowed, the term becomes a synthetic
metavariable, resumed later with its saved context (`resumePostponed`, SyntheticMVars:32).
Postponing sites include:
- record instances (`getStructName`: "This function tries to postpone execution if the
  expected type is not available", StructInst:1357-1365);
- dot notation on a value of unknown type (`resolveLValLoop`, App:1678-1694). It calls
  `tryPostponeIfMVar`, then tries default instances if the type is still an unknown, then
  resolves. On failure it unfolds the type one step (`unfoldDefinition?`) and retries.

`synthesizeSyntheticMVars` (SyntheticMVars:638-672) loops while a step makes progress, then
runs, in order:
1. a step `withoutPostponing` with errors postponed;
2. default instances;
3. a step `withoutPostponing` with errors reported;
4. tactic blocks;
5. a stuck report, if postponing is `.no`.

The comment's example is `let x := ⟨1, 2⟩; Prod.fst x`. `fun` does not postpone (`elabFun`,
Binders:678-690): it elaborates the body against the expected type. `let` has a body-first
mode: "If `config.postponeValue == true`, then we use the order `binders`, `typeStx`, `body`,
and `valStx`" (Binders:741-743), exposed as `let_delayed` (Binders:951-952) **[checked]**.

*Steal:* one queue (§5.1), and body-first elaboration for a let-bound lambda (SW-847). *Helps:*
SW-817, SW-847, SW-885, SW-509. *Cost:* elaborator. *Full text:* read (the functions named,
with their doc comments).

**C2. Lean 4's `isDefEq`: pattern conditions, approximations, lazy delta** (`ExprDefEq.lean`,
`Declaration.lean`). *Claim:* a pattern is `?m@C a₁ … aₙ =?= t` with five conditions
(distinct non-let free variables not in `C`, and so on). Then come the approximations:
- A1: unfold a let-variable;
- A2: quasi-patterns, which need a type check after abstraction;
- A3: non-distinct arguments, not approximated ("never used in the Lean3 stdlib");
- A5/A6: first-order approximation;
- A7: constant approximation, "may produce bad solutions", e.g. `?m Prop =?= IO Bool`.

A7 is applied by default only when the arguments are the ones that "represent dependencies",
tracked by `numScopeArgs` (ExprDefEq:820-971). Lazy delta: `unfoldDefEq` uses the reducibility
hints, unfolding the greater height (`ReducibilityHints.lt`: "if `lt h₁ h₂`, we want to
reduce declaration associated with `h₁`", `regular d₁ > d₂`, Declaration:60-66). It does so
**only when neither side has metavariables**. Otherwise `unfoldComparingHeadsDefEq` unfolds
`t`, compares if the heads now agree, and unfolds `s` next (ExprDefEq:1735-1767).
`isDefEqDeltaStep` (`:2215`) is "currently used to solve constraints of the form
`(f a).i =?= (g a).i`" **[checked]**.

*Steal:* A7's scope-argument restriction. Stitchwort's metavariables are applied to every
variable in scope (docs/core.md:281), the same situation **[inferred]**. Height ordering is a
kernel-side idea in Lean (wrong claim 4). *Helps:* SW-815 investigation. *Cost:* small
(measure first). *Full text:* read (the comment block at :820-971, `unfoldDefEq` and
neighbours at :1734-1880, `isDefEqDeltaStep` at :2200-2270; `Declaration.lean`
`ReducibilityHints`).

**C3. Lean 4's `@[elab_as_elim]`** (`App.lean:960-1120`). *Claim:* for a function whose
result is `motive x₁ … xₙ` with `motive` a parameter, "Lean first solves for `p` by matching
`p x₁ … xₙ` against the expected type, then replacing `xₙ` through `x₁` (in that order) with
variables". The "major" parameters (those reachable from the motive's arguments) are
elaborated first. The minor premises are postponed (`postponeElabTerm`, App:1314). Without the
attribute, the inferred motive can be "insufficiently general" (the `evenOddRec` example,
App:1103-1108). `rec` and `casesOn` always elaborate this way **[checked]**.

*Steal:* motive inference for `T.induct` applications. Today both uses in
`examples/accept/nested-data-induction.sw` (`:75`, `:151`) write the motive by hand. Stitchwort
already abstracts goals for `rewrite` and generalises scrutinees for `match` (matching.rs
header), the same operation **[inferred]**. *Helps:* proofs by induction (SW-199's `f.induct`).
*Cost:* elaborator. *Full text:* read (`ElabElimInfo`, its construction, the attribute's doc
comment, the argument loop).

**C4. Agda manual, *Lossy Unification*** (doc/user-manual/language/lossy-unification.lagda.rst).
*Claim:* `--lossy-unification` solves `f es₀ = f es₁` by first solving `es₀ = es₁`. It is
"sound but not complete". If `f` is constant, `f ?0 = f 1` "will end up assigning `1` to
`?0`", which "might make other constraints unsatisfiable" or mean "the solution you have in
mind might not be the one the system uses". It is opt-in per module, or per function with
`INJECTIVE_FOR_INFERENCE`, and complete when `f` is injective. The page's example (`vector :
Bit-vector (m + n)` at `0 + 1` and `1 + 0`) comes from López Juan's thesis **[checked]**.

*Steal:* the documentation and the test for Stitchwort's own lossy case (§5.2, T2). *Cost:*
small. *Full text:* read (whole page).

**C5. Kovács, smalltt README** (classic system; github.com/AndrasKovacs/smalltt).

*Claim:* glued evaluation lets one evaluator serve both fast conversion and small quoted
solutions. On approximation: "if I unify `f ?0 = f ?1` … pretend that `f` is injective …
AFAIK Coq and Lean both permit approximate solutions, and Agda does not". Smalltt "does not
allow approximate meta solutions" and has "bounded approximation". It unifies in three modes:
- *rigid*: may solve; with the same head it tries the spines in flex mode, else unfolds into
  full mode;
- *flex*: solves nothing and unfolds nothing;
- *full*: unfolds.

So it "backtracks at most once on any path". It uses paired values (`G {g1, g2}`, "least
reduced" and "more reduced") in infer, check and unify. It prefers eta-short solutions, and
freezes metas per top-level definition with approximate occurs checking.

Benchmarks (2021 versions of each system): `idTest` (`id id … id`, 40 times) and `pairTest`
(30 nested `let` pairs) finish in 0.000 s in smalltt and "TL" in Agda, Coq, Lean and Idris.
`vecTest` (960 elements) takes 0.078 s in smalltt, against 0.244 s elaboration in Lean
**[checked]**.

*Steal:* the benchmarks as probes (T4). The flex mode is the comparison point for §5.2.
*Cost:* small (measure). *Full text:* read (Design sections from "Glued evaluation" to "Meta
freezing", Benchmarks to "Elaboration asymptotics").

**C6. Kovács, Efficient Evaluation with Controlled Definition Unfolding** (WITS 2024
abstract, 2 pp.). *Claim:* values carry `VUnfold Name Spine ~Val`, a lazy choice between
folded and unfolded forms. Metavariable solutions "tend to blow up in size if definitions are
unfolded all the time". "To exactly preserve unfoldings, in some places we need to compute
with pairs of values" ("minimally" and "maximally" unfolded). The same setup is used in
smalltt, sett, cctt and sixty **[checked]**.

*Steal:* the pair for `check_inner`, which keeps `named` but compares with the forced value
(`check.rs:3093-3094`). This is SW-858's open alias place 3. *Helps:* SW-858, SW-845.
*Cost:* elaborator. *Full text:* read.

**C7. Kovács, Observing Definitional Equality** (WITS 2026 slides, 17 Jan 2026; text PDF).

*Claim:* in `(α true, (t, γ)) =? (β true, (u, true))`, postponing `α true =? β true` leaves
`(t, γ)` and `(u, true)` at different types. The existing answers are:
- block;
- "Rocq: ignore mismatched types and proceed. Unification is unsound, but the final
  elaboration output gets re-checked";
- "Agda: anti-unification. Questionable";
- heterogeneous unification (Gundry, McBride, López Juan).

The proposal: record a postponed equation as an observational proof `p : α true = β true` and
continue under `coe`, so `γ =? true` is solved. "WIP", in `2ltt-impl` **[checked]**.

*Steal:* the vocabulary for what SW-896's put-aside pairs do. Stitchwort's unifier is untyped
and goes on with the other pairs, which is the Rocq option, made safe by the kernel's re-check
(§5.2) **[inferred]**. *Cost:* none. *Full text:* read (all slides).

**C8. O'Brien, Rémy, Scherer, Omnidirectional type inference for ML: principality any way**
(arXiv 2511.10343v2, May 2026).

*Claim:* constraints are solved in any order. A construct that needs a type's shape is a
suspended `match` constraint, and "A match constraint that is never discharged is considered
unsatisfiable". For records:
- record labels resolve by context: `ex3 r = (r.x, (r : point).y)` is rejected by OCaml and
  accepted by OmniML;
- a literal with exactly one record type for its labels is typed by "closed-world
  reasoning" (`one = { x = 42; y = 1337 }`, OmniML ✓);
- `ex1 r = r.x` is rejected;
- joint resolution is refused ("overloaded projections must be elaborated sequentially, each
  in isolation"), because general overloading is "NP-hard … by a reduction from 3-SAT".

Defaults aren't formalised. The prototype can attach one to a suspended constraint. The
implementation keeps a wait list per unification variable, flushed into a global scheduler
when it is unified (§6). The related work says suspending constraints "is a standard approach
for implementing unification in dependently typed systems" (§8) **[checked]**.

*Steal:* the order "context first, closed-world rule for literals, no joint guessing" (§5.3),
and wait lists per unknown for T1. *Helps:* SW-805, SW-817. *Cost:* elaborator. *Full text:*
read (§1, §2, §6, §7, §8, §9; §3-§5 formal parts and the appendices not read).

**C9. Gundry, GHC proposal 366, DuplicateRecordFields without ambiguous field access**
(accepted 16 Nov 2020; classic as a decision, in force in-window). *Claim:* type-directed
disambiguation "works only in rather limited circumstances, has a complicated implementation,
and has proved confusing for users". Selector rules 1 and 2 and update rules 5 and 6 are
removed. "Rule 4 remains as above": "If there is only one datatype that has all the fields
being updated, use that datatype". It "can be determined during name resolution". Removal is
staged behind `-Wambiguous-fields` **[checked]**.

*Steal:* the reason a field-set rule is acceptable: it depends only on the text (§5.3).
*Helps:* SW-805. *Cost:* none. *Full text:* read (whole proposal).

**C10. Xue, Oliveira, Contextual Typing** (PACMPL 8 ICFP Art. 266, 2024; Internet Archive copy
of the ACM PDF).

*Claim:* contextual typing generalises bidirectional modes to counters (Quantitative Type
Assignment Systems). It propagates "other terms or record labels" as well as types, and
needs no "advanced mechanisms, such as unification variables". It is formalised in Agda for
STLC and for a calculus with subtyping, intersections, records and overloading. The authors'
caveat: "We only cover a small set of features" **[checked]**. C8 §8 adds that contextual
typing "still enforces a fixed order of propagation" **[checked: C8]**.

*Steal:* nothing. Stitchwort has unification variables, which make postponement cheaper than
counters **[inferred]**. *Cost:* research. *Full text:* read (abstract, §1, §6 opening, §7;
§2-§5 skimmed).

**C11. Libal, Miller, Functions-as-constructors Higher-order Unification: Extended Pattern
Unification** (author's final manuscript, lix.polytechnique.fr; the journal version of their
FSCD 2016 paper). *Claim:* the pattern fragment is extended to arguments built from bound
variables with constructors ("restricted terms"). Three restrictions apply (argument, local:
no argument a subterm of another, global), and keep decidability and most general unifiers.
It is simply typed. Functions are treated "as constructors", which "is still a sound
restriction since any solution for the restricted setting is a solution for the richer,
mathematical interpretation". "Hamana's system SOL … is the only system that has implemented
the algorithm" (§6) **[checked]**.

*Steal:* nothing now. Where Stitchwort's functions compute, an FCU solution would be *a*
solution, as `first_order`'s already is (`unify.rs:1107-1110`) **[inferred]**. *Cost:*
elaborator. *Full text:* read (§1, §3.1, §5 opening, §5.1, §6; §2, §3.2-§4 proofs not read).

**C12. Richter, Böhler, Extended Abstract: From Pattern Unification Towards Pattern Matching
Unification** (arXiv 2607.18455v1, 3 pp.).

*Claim:* `?P true = Nat, ?P false = Bool` falls outside Miller patterns, FCU and DHOP. A
prototype in "fewer than 3000 lines of Lean" collects delayed constraints and passes them to
its pattern-matching compiler. The litmus test `ind _ b 1 false` is rejected by Rocq and Lean
and accepted by the prototype. Limits:
- recursion is omitted;
- the solvable fragment is open;
- "our current system produces case trees as solutions … but does not yet translate them into
  core language terms".

The text names no venue **[checked]**.

*Steal:* not yet. It is the idea behind a possible SW-815 fallback, but it has no core-term
output and no boundary. *Cost:* research. *Full text:* read (all).

**C13. Norman, Avigad, Implementing Dependent Type Theory Inhabitation and Unification**
(arXiv 2603.01463v1). *Claim:* Canonical-min, 185 lines of Lean, is "sound and complete" for
inhabitation and unification. Stuck checks become continuations (constraints on the blocking
metavariable), and search is iterative deepening on "entropy". DTTBench (31 problems,
β-reduction only): Canonical-min 31/31, Twelf 8, sauto 6, mimer 2. Correctness is argued, not
formalised **[checked]**.

*Steal:* nothing for the elaborator. It is a proof-search reference for the automation
cluster. *Cost:* research. *Full text:* read (all).

**C14. Liesnikov, Binder, Süberkrüb, Filling the Gaps of Polarity** (The Art, Science, and
Engineering of Programming 10(3) Art. 19, 2025; arXiv 2511.15819).

*Claim:* this is implicit arguments for a language with symmetric data and codata. It uses
contextual metavariables with delayed substitutions (Abel and Pientka). Solving "only looks at
constraints of the shape α[θ] ∼ e", with outcomes simplify, fail, postpone (when the occurs
check gives a non-hard "no") or solve. A key rule: "congruence rules like Conv-Dtor keep the
condition that the head is a neutral term … and not just a blocked one … equating the
arguments could lose some of the solutions, since not all destructors are injective". "Rocq
and our system implement pruning while Lean does not". Lowering and eta for codata are not
implemented **[checked]**.

*Steal:* the blocked-versus-neutral distinction, which is exactly §5.2's question. *Cost:*
small (doc and test). *Full text:* read (abstract, §1, §8, §9, §10; §2-§7 skimmed).

**C15. Liesnikov, Cockx, ExEl: Building an Elaborator Using Extensible Constraints** (IFL
2023; Internet Archive copy of the ACM PDF).

*Claim:* the type checker raises constraints into an open datatype, and a dispatcher runs
plugin solvers after each declaration. Metavariables are "communication channels". Agda's
constraint type has "19 constructors". Its unifier is "about a hundred functions and 2200
lines". §7.1 lists three ways to treat metavariables left at the end of a definition:
- generalise them;
- leave them open, which makes elaboration "depend on the file as a whole";
- freeze them and report an error.

**[checked]**

*Steal:* the shape of T1's queue: one dispatcher for postponed checks, obligations and rows.
Stitchwort already takes the third option (`E-UNSOLVED` at zonk, docs/core.md:289). *Cost:*
research (as an architecture). *Full text:* read (§1-§3, §5.1-§5.3, §6.2 opening, §7.1, §8;
§4, §6.1, §6.3, §7.2-§7.6 skimmed).

**C16. Gratzer, Sterling, Angiuli, Coquand, Birkedal, Controlling unfolding in type theory**
(arXiv 2210.05420v2, Oct 2025; MSCS). *Claim:* definitions are opaque by default, with
`ϑ unfolds κ…` per declaration (transitive: unfolding `⊕` unfolds `+`, "necessary for subject
reduction"), `abbreviation` and `abstract`. There is also an expression-level
`unfold κ in M`, which "seems more commonly useful for end users" and is defined by hoisting
to top level. The surface is elaborated to extension types, and normalisation is proved
constructively. The cooltt change was "a net increase of 996 lines". Agda's `opaque` (2.6.4)
"simulates the necessary behaviors by instrumenting conversion checking". Glued evaluation is
"largely orthogonal and complementary" (§7.2) **[checked]**.

*Steal:* Stitchwort has built the declaration level: `opaque def`, `unfolding` lists closed
transitively, types checked with opaque definitions hidden, "No escape" (docs/core.md:161-171).
The missing pieces are expression-level `unfold f in e` and transparent abbreviations. Those
are the principled form of SW-796's "rewrite f unfolds f one step" **[inferred]**. *Helps:*
SW-796, SW-798. *Cost:* elaborator. *Full text:* read (§1, §2, §3.2, §5, §7, §8; §3.1, §4, §6
not read).

**C17. Selsam, Ullrich, de Moura, Tabled Typeclass Resolution** (arXiv 2001.04301, 2020,
classic). *Claim:* SLD-based resolution is exponential on diamonds and loops on cycles.
Tabling keeps one search tree per distinct subgoal, with generator and consumer nodes and a
resume stack. It terminates "under the bounded term-size assumption". Haskell needs no search
because overlapping instances are an error, while Coq, Lean, Agda and Scala allow overlap and
search **[checked]**.

*Steal:* nothing. Stitchwort has one instance per type, no backtracking among globals and no
tie-break (interfaces.md §5.5, `:670-674`), so diamonds and cycles don't cause search
**[checked: docs]**. Revisit only if overlapping instances arrive. *Cost:* none. *Full text:*
read (§1-§5.1 and Fig. 2; §5.2 onwards not read).

**C18. Zhao, Maroof, Dukkipati, Blinn, Pan, Omar, Total Type Error Localization and Recovery
with Holes** (PACMPL 8 POPL Art. 68, 2024; hazel.org PDF). *Claim:* the marked lambda
calculus gives every syntactically well-formed sketch a type by marking errors as non-empty
holes, using bidirectional typing plus gradual typing's unknown type. It is mechanised in
Agda. Constraint-based inference is used "exclusively to mark unfillable holes", and errors are
localised to the type hole with "partially consistent" suggestions, so no use site is blamed
arbitrarily. It is simply typed, with System F as an extension **[checked]**.

*Steal:* the principle "localise to the place that is really inconsistent, don't privilege one
use". Stitchwort already recovers at the granularity of case branches (`branch_failed`,
`lib.rs:4099-4107`) and declarations (a failed body stays declared, `lib.rs:2168-2169`). A
gradual unknown type has no counterpart in a kernel that re-checks everything **[inferred]**.
*Cost:* research. *Full text:* read (abstract, §1, Conclusion, Related work skimmed; §2-§4
skimmed).

**C19. Bhanuka, Parreaux, Binder, Brachthäuser, Getting into the Flow** (arXiv 2402.12637v1,
"Technical Report. 2024"). *Claim:* HMℓ reports a type error as the data flow that caused it,
a sequence of program locations. In a study, 119 finished and 117 were kept (40 HMℓ, 39 OCaml,
40 Helium). "the quantitative evaluation does not show that flow-based messages improve the
localization or understanding", while qualitative answers show "demand". Participants found
unexplained `?a` unification variables confusing. "occurs-check failures are much harder to
understand for users than unification failures" (§8.2) **[checked]**.

*Steal:* only weakly supported. Saying where an unknown got its type may help SW-859-style
confusion, but this study found no measurable gain. *Cost:* small. *Full text:* read (§1, §6.1
opening, §6.4-§6.5, §7, §8; §2-§5 skimmed).

**C20. Khakimova, Juhošová, Reinders, Cockx, Enhancing Interactive Theorem Prover Error
Messages with Hints** (ITP 2026, LIPIcs 382, Art. 5).

*Claim:* hints were added to three Agda 2.8.0 errors:
- Whitespace, a name that splits into names in scope;
- Confusable, a Unicode confusable of a name in scope;
- TooFewArgs, where the inferred type at a call site is a function type.

Results, in a between-subjects study of 56 participants (412 submissions):
- "correct hints can improve the success rate and time taken";
- hinted messages are "rated significantly more helpful";
- incorrect hints are "often rated as more misleading" but "do not significantly impact the
  success rate or time".

Agda "stops type checking upon encountering an error", so hints are shown by heuristic, not
by re-checking the fix **[checked]**.

*Steal:* confirmation for Stitchwort's existing hints:
- the too-few-arguments note names what's missing (`check.rs:3931`);
- non-ASCII characters outside the alias table are an error with a note
  (`lexer.rs:552-561`, `:1098-1112`), so the Confusable case can't arise in identifiers.

The lesson to keep: a hint that may be wrong cost little in this study. *Cost:* small. *Full
text:* read (abstract, §1, §2, §3 participants and cleaning, §4 results, Conclusion).

## 5. Deep reads

### 5.1 One postponement queue (C1, C8, C15)

**What the sources say** [checked]. Lean postpones *any* elaborator that needs an unknown
expected type: record instances, anonymous constructors, field access on an unknown type. It
resumes them in creation order while progress is made, then through the fixed ladder (C1). It
postpones the smallest piece that needs the type: `fun` elaborates its body at once, and what
postpones is the first thing in the body that needs a binder's type. `let_delayed`
elaborates the body before the value. OmniML gives the specification: a construct waits on
the *shape* of one type, each unknown keeps a wait list, and a wait never discharged is an
error (C8 §2.4, §6). ExEl's dispatcher runs all solvers over one constraint store after each
declaration (C15 §3).

**Stitchwort today** [checked].
- Lambda and method-section arguments postpone within one application only
  (`check.rs:1893-2125`). A section is postponed without a try. A lambda is tried in place
  and postponed on failure (`check.rs:1920-1989`, doc at `:1790-1802`). A lambda that fails
  where the application's expected type is known can be checked again after that comparison
  (`late_able`, `:1938`).
- Postponed lambdas are checked at the end of the same `apply_args_postponing` (`:2106`), not
  at the end of the declaration.
- Unification puts aside pairs stuck on an unknown, but only within one `unify` call
  (`unify.rs:31-41`).
- At the end of a declaration, `finish` (`lib.rs:1085-1090`) compares awaited helpers, solves
  obligations in rounds until stuck (`auto.rs:100`), settles row constraints and zonks.
- Nothing else waits. Record literals (SW-817, SW-885) and let-bound lambdas over pairs
  (SW-847) fail with `E-CANNOT-INFER`.

**Mapping.**
1. *A declaration-level queue of postponed checks* (expression, expected type, context,
   placeholder). `check` on a record literal, an anonymous lambda bound by `let`, or a field
   access on an unknown type would queue instead of failing. `finish` becomes the ladder:
   resume while progress is made; resume with postponing off; defaults (§5.3's field-name
   rule); obligations; rows; errors. Lean's ladder runs all its kinds in one loop (C1), so
   obligations and checks retried in separate loops would miss solutions that cross between
   them **[inferred]**.
2. *SW-847 by body-first `let`.* For `let counted := ((i, item)) => …; List.sumBy pairs
   counted`, elaborate the body with `counted : ?T` first, then the value against the solved
   `?T`. That is `let_delayed`. Lean makes it opt-in, which avoids changing elaboration order
   for every `let` **[checked: C1; inferred for us]**.
3. *Keep the in-place try for lambdas* in a first stage. Changing it changes which comparison
   solves a shared unknown, which is SW-859's argument-order problem. SW-859's rule R2
   ("postpone all") rejected `examples/accept/lambda-postponed-alias.sw` (SW-859 body).

**Assumptions the recommendation depends on.**
- (P1) Queued checks are rarely needed. Most arguments have known types when reached. Not
  measured; T1's switch measures it.
- (P2) A check resumed late reports at its own span, with the type it was finally checked
  against. Lean's `resumePostponed` restores the saved context and `withRef stx`
  (SyntheticMVars:32-60), so this is achievable **[checked: C1]**.
- (P3) Snapshots (`undo::Snapshot`) are not needed for queued items, because a queued item
  doesn't try anything before it waits. To be confirmed in the note.

**Risks.**
- Acceptance changes in both directions if the order in which unknowns are solved changes.
  The first stage must leave every currently accepted program elaborated the same, as SW-822
  did with its hash snapshot.
- New obligations created after the obligations loop has started.
- Error locations at the end of a declaration.

**Next step.** T1, a design note measured with a throwaway switch on std, examples and aoc.
Decision D1990.

### 5.2 Approximate solutions: Stitchwort's unifier is lossy for stuck calls (C4, C5, C7, C14, C2)

**What the sources say** [checked]. There are two policies for `f es₀ = f es₁`:
- *approximate*: solve `es₀ = es₁` and keep the solutions. This is Coq and Lean by default
  (C5), and Agda only with `--lossy-unification` or `INJECTIVE_FOR_INFERENCE` (C4). It is
  sound and incomplete: for a non-injective `f` it picks one solution and may make later
  constraints fail (C4);
- *exact*: try the spines without solving anything, then unfold. This is smalltt's
  rigid/flex/full (C5).

Polarity states the rule precisely: congruence on arguments is safe for a *neutral* head and
not for a *blocked* one, "since not all destructors are injective" (C14 §9.4). Where
postponing leaves sub-problems at different types, Rocq "ignore[s] mismatched types and
proceed[s]", relying on the final re-check (C7).

**Stitchwort today** [checked].
- Two *glued* calls of one definition are compared by arguments without solving
  (`same_arguments_solving_nothing`, `unify.rs:756-763`, `:1019-1035`). That is smalltt's
  flex mode.
- Two *forced* calls with the same head (`unify.rs:929-944`) have their spines pushed as
  ordinary pairs, which *may solve*. The comment says "Eta for definitions doesn't apply, so
  the spines must match". When one side is blocked on an unknown, the spines run as one batch
  and, if they fail, the calls are put aside (SW-896). If they succeed, the solutions stay.
- `unify_solving_arguments` (`unify.rs:103`) solves through arguments on purpose, for
  `List.sumBy xs ?f`.
- Folded dictionaries: "the same one's arguments first (what that solves is kept only if they
  all unify)" (`unify.rs:771-782`).
- Unification is untyped, and the kernel re-checks every declaration (docs/core.md:283, "safe
  because the kernel re-checks everything").

**Mapping.**
1. For calls stuck on a *variable* (no unknown in them), "spines must match" is right. Two
   stuck neutral calls are convertible only if their spines are, since the case-tree rule
   applies only to *different* definitions (docs/core.md:235) **[inferred]**.
2. For a call *blocked on an unknown*, it is the lossy rule. With `f (Succ n) = f n`, the
   constraint `f ?a = f x` has the solutions `x`, `Succ x`, `Succ (Succ x)`, …, and the
   unifier picks `?a := x` **[inferred, not run]**. That is sound (the kernel checks the
   result) and usually what the user meant. Agda's documentation names the cost: the program
   may elaborate to a different, well-typed meaning than the reader expects (C4).
3. Since SW-896, a blocked pair whose spines fail is put aside and the rest goes on. The rest
   may then compare values whose types differ, which is C7's "Rocq" option. That needs no
   change, but should be recorded as the reason the elaborator may not assume its pairs are
   well typed **[inferred]**.

**Assumptions.**
- (L1) No program depends on the unifier finding a *different* solution than the argument-wise
  one. Not checked; T2's tests probe it.
- (L2) The kernel re-check is the only soundness argument the elaborator needs. That is
  DESIGN.md's existing principle, cited in docs/core.md:283.

**Risks.** Making the rule exact (smalltt-style: solve nothing, then unfold) would reject or
slow programs that work today, because SW-896's `List.between` example relies on solving
`?lo := 2` from the arguments (docs/core.md:285) **[inferred]**. So the recommendation is to
document and test, not to change.

**Next step.** T2: a docs/core.md paragraph naming the rule and its incompleteness, with two
tests, one where the argument-wise solution is the intended one and one, Agda's `vector` shape,
where it is not.

### 5.3 SW-805: a field-name rule that depends only on the text (C8, C9, C1)

**What the sources say** [checked]. GHC removed every type-directed field rule but kept "only
one datatype has all the fields being updated", because it is decided during name resolution
(C9). OmniML types a record literal by "closed-world reasoning" when exactly one record type
has those labels. It suspends projections until context fixes the type and refuses to resolve
several overloaded projections jointly (C8 §2.1, §2.5). Lean's `getStructName` postpones a
record instance with no expected type. If it is resumed with postponing off, it falls back to
the type of its first source (C1).

**Stitchwort** [checked]. SW-805 (D1442) is built on branch `record-literal-inference`: a
literal's type is "exactly one record type in scope with exactly those fields" (SW-805 body).
SW-817 asks instead to postpone the literal until the argument that fixes its type is checked.

**Mapping.** The two tickets don't conflict. The field-set rule is GHC's rule 4 and OmniML's
closed-world case: a function of the literal and the scope, not of inference order. So it can
be applied at once whenever the expected type is unknown, without the order dependence that
made GHC drop rules 1, 2, 5 and 6 **[inferred]**. SW-817's postponement (T1) then helps only
where *several* types fit. The one hazard is the same as GHC's and OCaml's: adding a record
type to a namespace can make an existing literal ambiguous. The error should name both types
and suggest the annotation (OmniML's `e.T.ℓ` qualification plays this role, C8 §3) **[inferred]**.

**Assumption.** (R1) The rule looks only at names in scope at the literal, never at types
learned later. If it did, it would become type-directed and order-dependent.

**Next step.** T3 (record the justification on SW-805; add the ambiguity message test), and
D1991.

### 5.4 Errors: hints yes, flows maybe, recovery by branch already (C20, C19, C18)

**What the sources say** [checked]. In the one controlled ITP study, correct hints raised
success and speed, and incorrect hints did not measurably lower them (C20, 56 participants).
Flow-based explanations showed no quantitative gain, and unexplained `?a` notation confused
readers (C19). Total recovery needs a type for every erroneous term (C18).

**Stitchwort** [checked].
- The too-few-arguments note names the missing parameters (`check.rs:3915-3935`).
- Non-ASCII outside the alias table is an error with the alias list (`lexer.rs:1098-1112`).
- "did you mean" by edit distance exists for members (`scope.rs:1279-1293`).
- Each failing case branch is reported in one run (`lib.rs:4099-4116`), and a failed
  definition stays declared so later uses don't cascade (`lib.rs:2168-2169`).

**Mapping.** Stitchwort already has the measured win (C20's TooFewArgs and the confusables
case), and its recovery granularity (branch, declaration) avoids C18's need for a gradual
type. One cheap addition is supported by C19's qualitative data and SW-859's investigation,
but not by measurement. When `E-CANNOT-INFER` or a mismatch involves an unknown that was
solved earlier in the declaration, the message would say *which expression* solved it
("`b` became `List Nat` from the argument at 12:7"). Never show a bare `?n` (C19) **[inferred]**.

**Next step.** T6 (small; the provenance would need recording where `solve` assigns, at
`unify.rs:1184`).

## 6. Steal next

Ranked by value over effort. Every row rests on sources read in full.

| Rank | Idea | Source | Helps | Cost |
|---|---|---|---|---|
| 1 | One declaration-level postponement queue with Lean's ladder; body-first `let` for let-bound lambdas | C1, C8, C15 | SW-817, 847, 885, 509 | elaborator (design note first) |
| 2 | Document and test the lossy rule for stuck calls of one definition | C4, C5, C14, C7 | predictability; SW-896 follow-up | small |
| 3 | SW-805 justified as a name-resolution rule (GHC rule 4, OmniML closed world); ambiguity message names both types | C8, C9 | SW-805, 817 | small |
| 4 | smalltt's `idTest`, `pairTest`, `vecTest` as elaboration probes | C5 | proof-check-speed | small (measure) |
| 5 | Motive inference for `T.induct` applications from the expected type (`elab_as_elim`) | C3 | proofs by induction, SW-199 | elaborator |
| 6 | Messages say which expression solved an unknown; never a bare `?n` | C19, C20 | SW-859-style confusion | small |
| 7 | Keep both the named and the forced expected type in `check_inner` (pairs of values) | C6, C5 | SW-858, 845 | elaborator |
| 8 | Expression-level `unfold f in e` over the existing opaque/unfolding machinery | C16 | SW-796, 798 | elaborator |
| 9 | Scope-argument constant approximation (Lean A7 with `numScopeArgs`) | C2 | SW-815 (measure first) | small |
| 10 | Pattern-matching unification for function holes | C12 | SW-815 | research, not now |

## 7. Proposed tickets

Label `research` on each. Not added to the board.

**T1. Design note: one postponement queue and a ladder at `finish`.** Decide:
- which forms queue (record literals, let-bound lambdas, field access on an unknown type);
- how `finish` (`lib.rs:1085`) runs queued checks, obligations and rows in one loop, in Lean's
  order: resume; resume with postponing off; defaults; report;
- whether `let` gets an opt-in body-first mode (Lean's `let_delayed`) for SW-847;
- how a late failure is located.

Keep `apply_args_postponing`'s in-place try unchanged in stage 1. Measure a throwaway switch on
std, examples and aoc, and require unchanged hashes for accepted programs. Refs: §5.1; C1,
C8, C15; SW-817, 847, 885, 509; D1990.

**T2. Name the lossy rule and test it.** Add a paragraph to docs/core.md "Elaboration". It
should say that two calls of the same definition, stuck on an unknown, unify by their
arguments and keep what that solves (`unify.rs:929-944`). That finds *a* solution, not
necessarily the intended one. Agda makes it opt-in, smalltt forbids it, and Stitchwort keeps
it because SW-896's inference depends on it. Add two elaborator tests:
- a call where the argument-wise solution is intended;
- an `f (Succ n) = f n` or Agda `vector` shape, recording which solution is chosen.

No behaviour change. Refs: §5.2; C4, C5, C14.

**T3. SW-805: record the justification and test the ambiguity message.** On the
record-literal-inference branch, note that the rule is GHC 366's rule 4 and OmniML's
closed-world case, a function of the text and scope only. Add a test where a second record
type with the same fields makes the literal ambiguous, and check the message names both and
suggests an annotation. Refs: §5.3; C8, C9; D1991.

**T4. Elaboration asymptotics probes.** Port smalltt's `idTest` (`id id … id`, 40 times),
`pairTest` (30 nested `let` pairs through an implicit `dup`) and `vecTest` (a 960-element
indexed vector) to `.sw`. Time `stitchwort check` on each, and record the shape of solved
metavariables for `pairTest`. Measurement only. Refs: C5.

**T5. Design note: motive inference for eliminator applications.** For `T.induct _ … x`
(and `f.induct` from SW-199), infer the motive by abstracting the major premises out of the
expected type, Lean's `@[elab_as_elim]`. Reuse the generalisation that `match` and `rewrite`
already do. Elaborate the major premises first and the minor premises after. Refs: C3;
`examples/accept/nested-data-induction.sw:75`, `:151`.

**T6. Messages: say where an unknown got its type.** When `E-CANNOT-INFER` or a type mismatch
involves a metavariable solved earlier in the declaration, add a note naming the expression
and span whose comparison solved it. Record provenance at `solve` (`unify.rs:1184`) only while
an error is being reported, or behind a cheap flag. Never print a bare `?n`. Refs: §5.4; C19,
C20; SW-859.

## 8. Decisions

**D1990. Make one declaration-level postponement queue (T1) the route for SW-817, SW-847 and
SW-885, instead of extending the lambda-only rule case by case?** It is design note first, and
stage 1 must leave every accepted program elaborated identically. The assumptions, in full:
- (P1) queued checks are needed rarely enough that the cost is small, which T1's switch
  measures;
- (P2) a late failure can be reported at its own span with its final expected type, as Lean
  does;
- (P3) queued items need no snapshot, because they try nothing before waiting.

**[Recommend yes.]**

**D1991. Keep SW-805's field-name rule as built (one record type in scope with exactly those
fields, used when the expected type is unknown), justified as a name-resolution rule like GHC's
rule 4, rather than replacing it by postponement?** The assumption in full is (R1): the rule
looks only at the literal's field names and the names in scope at the literal, never at types
learned later in elaboration. If a later change made it consult inferred types, it would be
type-directed and order-dependent, and the decision would lapse. **[Recommend yes.]**

## 9. Sources not reached

**Full text not reachable.** None, so nothing for Matt to fetch. Every carded source was read.
Screened-only items whose full text I did not try to reach, because their rows didn't need
them, are rows 23-28, 30, 33-39 and 41-42 of §3. Row 24 (Local Contextual Type Inference,
POPL 2026) was looked for on arXiv, without success, and not elsewhere.

**Partly read** (supports nothing): Frost/Fresco (arXiv 2607.16061, abstract and §1) and
Porter et al. (arXiv 2504.08946, abstract and §1). Lean 4.36.0-rc1's instance-cache notes
were seen only as a search summary.

**Not searched.** In-window work on elaborating effect rows beyond effects.md's card;
incremental elaboration beyond infrastructure.md's cards; Agda's and Idris 2's elaborator
changelogs since 2022; RocqPL and Lean workshop programmes. This register makes no claim about
them.

**Fetch notes.** ACM DL returned 403 to `curl`. The Internet Archive's `id_` copies of the ACM
PDFs worked (C10, C15). DBLP returned a bot-check page. Semantic Scholar search was
rate-limited, but its DOI lookup worked. `pdftotext` worked on every PDF, including the
WITS 2026 slides, which have a text layer.
