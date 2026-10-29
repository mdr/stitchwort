# Literature trawl: inductive types and recursion

**Counts: screened 56; carded 21; read in full 19; not read 2 (listed in §9).**

*SW-894, cluster 2. Trawled 29 October 2026 against `main` at `5c25a1b5`. Research only: no
code changed, no tests run. Window: 2022 onwards (D1831); older work appears only where
in-window work or a system we compare with relies on it, marked **classic**.*

Reading protocol: every card says **Full text: read (source)** or **NOT READ**. Papers were
read with `pdftotext` from `nix shell nixpkgs#poppler-utils`. "Read" for a long theory paper
means the prose, definitions, examples, evaluation and conclusions were read in full and the
proof sections were skimmed; each such card says which sections. A NOT READ card supports no
ranking, deep read or recommendation. Release notes, module docstrings, manual pages and blog
posts were read in full as fetched.

Labels: **[cited]** read in the source the card names; **[checked]** read in Stitchwort's code
or docs at the place given; **[inferred]** my reasoning; **[unverified]** from a search
summary or a second-hand account only.

Not repeated here: kernel bug classes, large elimination from recursive propositions and the
Rocq guard-checker CVEs (kernel.md §5.1, §5.2, T2), and nested data types
(docs/proposals/nested-data-types.md, which covers Lamiaux, Forster, Sozeau and Tabareau,
PLDI 2026).

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

Stitchwort already made the big choices in this cluster, and the work since 2022 mostly
confirms them: case trees plus size-change termination, not recursors; proof-carrying fuel
for `decreasing`, not `Acc`, so tests and `rfl` compute; nested types checked as written;
`Partial` as a separate mode, not a domain theory. Lean went the same way on one of these in
2025: it removed reducible well-founded recursion altogether (4.25, #10714). Sized types are
still not practical. Chan, Li and Bowman measured at least a 5.5× slowdown on Coq's standard
library from backward-compatible size inference, "intrinsic and unavoidable" (C11). Agda's
implementation "is currently inconsistent" because Agda proves `∞ < ∞` (C12). Nothing here
argues for reopening those choices.

What is worth stealing is mostly **Lean's elaborator work from 2024-2026**, because it solves
problems that are open on Stitchwort's board:

- **Generated functional induction and case-split principles** (`f.induct`, Lean 4.8;
  `f.fun_cases`, 4.17). One generator would serve three open items: SW-199's stage 3
  `f.induct`, SW-802's per-branch lemmas (D1439), and nested-data-types.md §9's `T.induct`
  (D1823). In Stitchwort it can be a generated *theorem* by recursion that the kernel checks,
  so nothing new is trusted (§5.1, T1).
- **Automatic `attach`** (Lean 4.18, `wf_preprocess`): the elaborator rewrites `xs.map f` to
  `xs.attach.map …` itself, so a recursive call inside `map` gets its membership fact.
  Stitchwort built the pieces in stages 3a and 3b (congruence lemmas, `List.attach`,
  `List.Member`), but the user still attaches by hand (§5.2, T2).
- **Termination-measure guessing** (Lean's GuessLex): try candidate measures, then report the
  one that works (`termination_by?`), or a table of what was found per call. In Stitchwort
  this belongs in the `E-TERMINATION` message, not in the checker (§5.2, T3).
- **Derived enumerations** (Mathlib's `Fintype` handler; Lean 4.24/4.25's linear `DecidableEq`,
  `BEq` and `Ord` by constructor index): for SW-807, a derived `T.all` with linear-size
  completeness and distinctness proofs, built on the `T.%tag` that Stitchwort's derived
  `DecEq` and `Ord` already use (§5.3, T4). Stitchwort's derived `DecEq` already has the
  linear shape Lean adopted in 2025 **[checked]**.

Two "no"s are worth writing down. **Codata** (streams, coinductive types): checking
termination and productivity separately "is not enough" once inductive and coinductive types
nest (Altenkirch and Danielsson's `bad_s`, quoted by Hyvernat, C13), so a later design needs a
totality checker of its own, not a second pass. Lean added only coinductive *predicates*
(4.25). No program asks for streams, so Stitchwort should not add codata now (§5.4, D1911).
**Quotient, inductive-inductive and inductive-recursive types** have seen real progress
(Kovács, POPL 2026; Fiore, Pitts and Steenkamp, LMCS 2022). Each needs kernel work far from
any ticket, so they were screened and not carded.

## 2. Method and queries

Searches were run with the web search tool on 29 Oct 2026, then specific pages fetched. The
session's shared web-search budget ran out at Q38; after that, only direct fetches of known
URLs were possible. Rerun the queries as written, adding the months since the last run.

| # | Query or source | Kept or useful hits |
|---|---|---|
| Q1 | `Lean 4 functional induction Breitner paper 2024 2025 "functional induction" fun_induction` | Lean 4.17, 4.18 notes; Lean blog (May 2024) |
| Q2 | `Lean 4 structural recursion over nested inductive types release notes 2024 Breitner` | Zulip "nested inductives in the kernel"; Lean 4.14 notes |
| Q3 | `size-change termination dependent types 2023 2024 paper Agda termination checker improvement arXiv` | Hyvernat arXiv 2407.05715; TU Delft thesis (2026) |
| Q4 | `Rocq Equations plugin paper 2023 2024 2025 dependent pattern matching unification Cockx Sozeau` | Richter and Böhler, arXiv 2607.18455 |
| Q5 | `Rocq guard checker new implementation 2024 2025 structural recursion nested fixpoint "guard condition" paper` | Tan and Forster, TYPES 2025 |
| Q6 | `quotient inductive-inductive types 2023 2024 2025 paper computation implementation Agda Cubical "quotient inductive"` | CPP 2026 (Chen, Nordvall Forsberg, Tsai); arXiv 2511.21209 |
| Q7 | `inductive-recursive types 2024 2025 paper "induction-recursion" small induction recursion universes` | Kovács POPL 2026 |
| Q8 | `Agda sized types status 2024 2025 removal "--sized-types" unsound guardedness coinduction` | Laarakker, Otten, van den Berg, FSCD 2026 |
| Q9 | `"Delay monad" OR "partiality monad" 2023 2024 2025 paper type theory quotient-free Capretta total` | Møgelberg and Zwart, LMCS 2025 |
| Q10 | `ornaments descriptions datatype-generic programming dependent types 2023 2024 2025 TyDe paper` | nothing in window |
| Q11 | `Leroy "Well-founded recursion done right" CoqPL 2024` | CoqPL 2024 pearl |
| Q12 | `Lean 4 wf_preprocess automatic attach List.map nested recursion termination release notes` | Lean 4.18 (#6744); Breitner blog 816 |
| Q13 | `Lean 4 partial_fixpoint Breitner monotone recursion Option release 4.19` | Lean reference; Breitner blog 817 |
| Q14 | `Lean GuessLex termination_by? lexicographic order inference Breitner` | `GuessLex` docs; lean4#3906 |
| Q15 | `Escot Cockx "Practical generic programming over a universe of native datatypes" ICFP 2022` | ICFP 2022 |
| Q16 | `Ko Chen Lin Gibbons "Datatype-generic programming meets elaborator reflection" ICFP 2022` | ICFP 2022 |
| Q17 | `Chan Li Bowman "Is sized typing for Coq practical?" Journal of Functional Programming 2023` | JFP 33 e1 |
| Q18 | `Paraskevopoulou Eline Lampropoulos "Computing correctly with inductive relations" PLDI 2022` | PLDI 2022 |
| Q19 | `Lean 4 coinductive predicates keyword 2025 lattice greatest fixpoint release notes "coinductive"` | Lean 4.25 (#10333) |
| Q20 | `Larchey-Wendling Monin "Braga method" certified algorithms complex recursive schemes Coq 2022` | 2021 chapter (out of window); ITP 2023 pearl |
| Q21 | `Kovács "Canonicity for Indexed Inductive-Recursive Types" POPL 2026` | POPL 2026 |
| Q22 | `Hyvernat "size-change principle for mixed inductive and coinductive types" LMCS 2025` | LMCS 21(3:19), 21(3:20) |
| Q23 | `Lean 4 deriving LawfulBEq DecidableEq linear size enumeration release notes 2025 2026 deriving handler` | Lean 4.24 notes |
| Q24 | `Mathlib derive Fintype handler inductive enumeration "deriving Fintype" Lean 4` | `Mathlib.Tactic.DeriveFintype` |
| Q25 | `Lean Plausible deriving Arbitrary inductive types generator 2025` | Plausible `DeriveArbitrary` |
| Q26 | `Idris 2 Nat-like types compiled to integers optimisation "Nat hack" Fin representation` | Idris 2 builtins docs |
| Q27 | `Fiore Pitts Steenkamp "Quotients, inductive types, and quotient inductive types" LMCS 2022` | LMCS 18(2:15) |
| Q28 | `Lean 4 mutual structural recursion release 4.12 Breitner blog "structural recursion" mutual nested 2024` | Lean 4.11 notes |
| Q29 | `arXiv 2505.21225 custom representations of inductive families` | Theocharis and Brady 2025 |
| Q30 | `Lean 4 dot constructor ".none" leading dot identifier expected type resolution constructor namespacing Agda overloaded constructors` | Lean error explanation `invalidDottedIdent` |
| Q31 | `Breitner "functional induction" paper ITP OR CPP 2025 2026 Lean induction principles recursive functions` (extended) | no paper; ITP 2025 Lean workshop slides |
| Q32 | `Idris 2 totality checker size-change termination implementation 2023 2024 changelog coverage` | Idris 1 docs only |
| Q33 | `Agda 2.7 2.8 termination checker changes changelog "termination" "with-abstraction" 2024 2025` | Agda 2.8.0 changelog |
| Q34 | `Coq-Elpi derive equality tests induction principles containers "derive" Tassi 2023 2024 Rocq deriving` | Grégoire, Léchenet, Tassi 2023 |
| Q35 | `guarded recursion coinduction type theory 2023 2024 implementation paper streams productivity "later modality" practical` | classics only |
| Q36 | `ornaments generic programming Agda 2023 2024 2025 paper Ko Gibbons "ornament" reflection follow-up` | no paper |
| Q37 | `Haskell Symposium 2022 2023 2024 deriving paper generic deriving strategies GHC` | nothing in window |
| Q38 | `Dafny decreases clause inference default termination metric lexicographic automatic` | **not run** (search budget exhausted) |

Direct fetches (read in full): Lean module docstrings `Lean.Meta.Tactic.FunInd`,
`Lean.Elab.PreDefinition.WF.Preprocess` and `Lean.Elab.PreDefinition.WF.GuessLex`; Lean
release notes 4.17.0, 4.24.0 and 4.25.0; Lean reference "Recursive definitions" (first 200k
of 217k characters); Lean error explanation `invalidDottedIdent`; Mathlib `DeriveFintype`
docs; Idris 2 "Builtins" page; Agda 2.8.0 changelog; Breitner's blog post 816 ("Extrinsic
termination proofs", 10 Mar 2025); arXiv abstract 2607.18455. Semantic Scholar's API was used
to look for open copies of the two ICFP 2022 papers.

## 3. Screened list

Screened on title and abstract (or release-note text) against SW-894's hooks and the tickets
in the brief. 56 sources: 21 carded (19 read, 2 NOT READ), 18 maybe, 17 drop. A "maybe" was
not read and supports nothing below.

| # | Source | Verdict | Why |
|---|---|---|---|
| 1 | Lean functional induction, `f.induct` (4.8), `FunInd` docstring | card C1 | §5.1 |
| 2 | Lean `fun_cases` (4.17, #6261) | card C2 | §5.1 |
| 3 | Lean automatic attach, `wf_preprocess` (4.18, #6744) | card C3 | §5.2 |
| 4 | Breitner, "Extrinsic termination proofs" (blog, Mar 2025) | card C4 | §5.1, §5.2 |
| 5 | Lean GuessLex (after Bulwahn, Krauss, Nipkow, classic) | card C5 | §5.2 |
| 6 | Lean `partial_fixpoint` (4.17, #6355) | card C6 | §5.4 |
| 7 | Leroy, Well-founded recursion done right, CoqPL 2024 | card C7 | §5.2 |
| 8 | Lean 4.24/4.25 deriving and recursion notes | card C8 | §5.3 |
| 9 | Mathlib `DeriveFintype` | card C9 | §5.3 |
| 10 | Paraskevopoulou, Eline, Lampropoulos, Computing Correctly with Inductive Relations, PLDI 2022 | card C10 | `auto`, counterexample search |
| 11 | Chan, Li, Bowman, Is Sized Typing for Coq Practical?, JFP 2023 | card C11 | SW-199 option D |
| 12 | Laarakker, Otten, van den Berg, Constructing (Co)inductive Types via Large Sizes, FSCD 2026 | card C12 | same |
| 13 | Hyvernat, The Size-Change Principle for Mixed Inductive and Coinductive Types, LMCS 2025 | card C13 | §5.4 |
| 14 | Lean `coinductive` predicates (4.25, #10333) | card C14 | §5.4 |
| 15 | Theocharis and Brady, Custom Representations of Inductive Families, arXiv 2025 | card C15 | T5 |
| 16 | Idris 2 Nat-like optimisation (builtins docs) | card C16 | T5 |
| 17 | Richter and Böhler, From pattern unification towards pattern matching unification, TyDe 2026 | card C17 | motive inference |
| 18 | Agda 2.8.0 changelog | card C18 | SW-510 |
| 19 | Lean dotted identifiers from the expected type (reference) | card C19 | SW-510 |
| 20 | Escot and Cockx, Practical generic programming over a universe of native datatypes, ICFP 2022 | card C20, NOT READ | deriving architecture |
| 21 | Ko, Chen, Lin, Datatype-generic programming meets elaborator reflection, ICFP 2022 | card C21, NOT READ | same |
| 22 | Hyvernat, Totality for Mixed Inductive and Coinductive Types, LMCS 2025 | maybe | companion to 13 |
| 23 | Møgelberg and Zwart, What Monads Can and Cannot Do with a Few Extra Pages, LMCS 2025 | maybe | Delay with other effects |
| 24 | Kovács, Canonicity for Indexed Inductive-Recursive Types, POPL 2026 | maybe | IIR theory; not now |
| 25 | Fiore, Pitts, Steenkamp, Quotients, inductive types, and QITs, LMCS 2022 | maybe | QITs; D785 |
| 26 | Grégoire, Léchenet, Tassi, Deriving eqType instances with Coq-Elpi, 2023 | maybe | derived DecEq at scale |
| 27 | Tassi, Deriving proved equality tests in Coq-Elpi, ITP 2019 (classic) | maybe | `All`-style induction; D1823 |
| 28 | Tan and Forster, Towards formalising Rocq's guard checker, TYPES 2025 | maybe | test source |
| 29 | Allais, Builtin types viewed as inductive families, ESOP 2023 | maybe | found in C15's references; T5 |
| 30 | Plausible `deriving Arbitrary` (2025); Specimen; Chamelean | maybe | counterexample search already enumerates |
| 31 | Lean mutual structural recursion (4.11), nested (4.12-4.14) | maybe | Stitchwort already has both |
| 32 | Lean 4.24 match equations by `rfl` (#10183), functional induction robustness (#10134) | maybe | detail for T1 |
| 33 | Larchey-Wendling and Monin, Braga method (2021), ITP 2023 pearl | maybe | covered by C7 |
| 34 | Rowe, "Does Agda implement SCT?" (Agda list, Apr 2024) | maybe | docs drift |
| 35 | TU Delft thesis, Termination checking in Agda Core (2026) | maybe | repository refused connections |
| 36 | Breitner, Zulip "nested inductives in the kernel" (Jun 2024) | maybe | nested recursion through `map` |
| 37 | GHC deriving strategies, DerivingVia (classic) | maybe | "which deriving applies" |
| 38 | Breitner blog 817, F91 with `partial_fixpoint` | maybe | example for C6 |
| 39 | Erlangen BSc thesis on partiality monads (2024) | drop | thesis; 23 covers it |
| 40 | Chen, Nordvall Forsberg, Tsai, QIIRTs in Cubical Agda, CPP 2026 | drop | cubical |
| 41 | Tan, Nuyts, Devriese, computational UIP, arXiv 2511.21209 | drop | cubical |
| 42 | Pujet, IR universe for the setoid model, TYPES 2025 slides | drop | OTT (kernel.md) |
| 43 | Bove-Capretta domain predicates (classic) | drop | in well-founded-recursion.md |
| 44 | MiniAgda (2025 package) | drop | sized types |
| 45 | Carneiro on nested inductives (Zulip, Apr 2024) | drop | nested note settles it |
| 46 | Gratzer et al., IR universe generic for small families (arXiv 2202.05529) | drop | semantics |
| 47 | Higuchi, cumulative universe towers (arXiv 2506.21653) | drop | set theory |
| 48 | Utrecht thesis, generic programming with ornaments | drop | out of window |
| 49 | Dagand and McBride, Transporting functions across ornaments (classic) | drop | no in-window follow-up |
| 50 | Ko and Gibbons, Programming with ornaments, JFP 2016 (classic) | drop | same |
| 51 | Lean `wfinduct` (Breitner, reservoir) | drop | superseded by core |
| 52 | Uustalu and Veltri, delay monad and restriction categories (classic) | drop | theory |
| 53 | Guarded type theory (gDTT, guarded lambda calculus; classics) | drop | no in-window implementation found |
| 54 | Lean `noConfusion` per constructor (4.24 #10315) | drop | Stitchwort's derive has its own |
| 55 | Lean 4.24 `ctorIdx` for all inductives (#9951) | drop | folded into C8 |
| 56 | Lean ITP 2025 workshop slides (Breitner) | drop | feature list only |

## 4. Cards

**C1. Lean functional induction.** `Lean.Meta.Tactic.FunInd` docstring; Lean 4.17 notes.
*Claim:* every recursive function `f` (structural, well-founded, mutual) gets `f.induct`. Its
motive ranges over `f`'s non-fixed parameters. Its cases follow `f`'s branches, roughly its
tail positions (`if` arms and `match` arms). Each case gets one induction hypothesis per
recursive call, quantified over any binders the call depends on, plus the branch's `if`
condition and `let`s "when judged useful". Where patterns overlap, the matcher is replaced by
its "splitter", which "brings extra assumptions into scope". Mutual functions get one motive
each. The principle is built by walking the compiled body (`.brecOn` or `WellFounded.fix`).
Inductive predicates defined by `.brecOn` are not supported **[cited]**. *Steal:* generate
`f.induct` from the case tree, as a theorem by recursion that the kernel checks (§5.1).
*Helps:* SW-199 stage 3, SW-802, D1823. *Cost:* elaborator change. *Full text:* read
(docstring at lean-lang.org/doc/api/Lean/Meta/Tactic/FunInd.html; 4.17 notes). The Lean blog
post of May 2024 was not reached (§9); nothing here rests on it.

**C2. Lean `fun_cases`.** Lean 4.17 notes, #6261; FunInd docstring. *Claim:* `foo.fun_cases`
is "an automatically generated theorem that splits the goal according to the branching
structure of `foo`". It works "for all functions (not just recursive ones), and without
providing inductive hypotheses". An unfolding variant gives the motive `f`'s result in each
case (`motive x y (f x y)`), reducing through `match`, `ite` and `let` **[cited]**. *Steal:*
the proof-side answer to SW-809 ("a `match found:` in a definition can't be stepped through")
and SW-802 (days 12 and 16): one generated lemma per definition, applied as a case split.
*Helps:* SW-802, SW-809. *Cost:* elaborator change (shares T1's generator). *Full text:* read
(4.17 notes; FunInd docstring).

**C3. Lean automatic `attach`.** `Lean.Elab.PreDefinition.WF.Preprocess` docstring. *Claim:*
before building a well-founded definition, Lean marks every parameter with `wfParam` and
pushes the marker through projections and `match`. It then rewrites with a simp set
`wf_preprocess`, "typically" with two rules per higher-order function: activation,
`(wfParam xs).map f = xs.attach.unattach.map f`, and performing the call, `xs.unattach.map f =
xs.map (fun ⟨x, h⟩ => f (wfParam x))`. The split lets chains like `(xs.reverse.filter p).map f`
attach the membership proof to `xs`, and the inner `wfParam` handles doubly nested recursion
**[cited]**. Lean 4.18's notes say it makes `attach` unnecessary "in many cases"
**[unverified: search summary of the notes]**. *Steal:* auto-attach for `decreasing` (§5.2,
T2). *Helps:* SW-199 stage 3b follow-up; nested stage 3 (D1450). *Cost:* elaborator change.
*Full text:* read (docstring).

**C4. Breitner, "Extrinsic termination proofs for well-founded recursion in Lean"**
(joachim-breitner.de/blog/816, 10 Mar 2025). *Claim:* an alternative design leaves the user's
functional untouched and proves separately that it "calls only on" smaller arguments
(`callsOn`, with compositional lemmas per higher-order function). It works for termination
but not for functional induction, because the facts the induction needs exist only inside
the termination proof ("The cake is a lie"). He would probably have chosen it had functional
induction not existed already **[cited]**. *Steal:* the warning for T1. Stitchwort's
congruence-lemma route (`FCong`, stage 3a) is the same kind of extrinsic argument, used for
the respects lemma. A generated `f.induct` has no fact to give a call under a lambda unless
that call used `attach`. *Helps:* T1, T2. *Cost:* none (design input). *Full text:* read.

**C5. Lean GuessLex.** `Lean.Elab.PreDefinition.WF.GuessLex` docstring. *Claim:* candidate
measures are `sizeOf` of each parameter, `e₂ - e₁` when `e₁ < e₂` is in a call's context, and,
for mutual groups, an order on the functions. Combinations are tried until every obligation is
discharged by the user's or the default tactic, bounded (a threshold of 32 for mutual
combinations), uniform combinations first. Each measure is checked once per call (`<`, then
`≤`, equality first) in a lazily filled table. The result is a measure the user could have
written; `termination_by?` shows it, and on failure a table explains what was found about each
call. The design follows Bulwahn, Krauss and Nipkow, and Manolios and Vroon **[cited]**.
*Steal:* T3: on `E-TERMINATION`, try candidates against `auto` and suggest the `decreasing`
clause that works, or print the per-call table. *Helps:* DESIGN §5 ("the error should say
which call failed and … suggest `decreasing`"). *Cost:* elaborator change (messages only).
*Full text:* read (docstring).

**C6. Lean `partial_fixpoint`.** Lean 4.17 notes, #6355; Lean reference, "Recursive
definitions". *Claim:* the feature adds "the ability to define possibly non-terminating
functions and still be able to reason about them equationally". The return type must be in
certain monads (for example `Option`). Applications "are not definitionally equal to their
return values", but propositional equations and, for monadic functions, partial-correctness
theorems are generated. By contrast, `partial` functions are opaque constants **[cited]**.
The names `fixpoint_induct` and `partial_correctness` come from Zulip **[unverified]**.
*Steal:* the idea that a partial function can have a reasoning principle without a
termination proof (§5.4). *Helps:* partial.md. *Cost:* research. *Full text:* read (notes;
reference chapter to 200k of 217k characters; the partial-fixpoint subpage returned 404).

**C7. Leroy, Well-founded recursion done right** (CoqPL 2024; xavierleroy.org/publi/
wf-recursion.pdf). *Claim:* Coq's options for well-founded recursion are tactics, `Fix`,
`Function`, `Program Fixpoint` and Equations. Measured against four requirements (readable
definition, easy later proofs, no axioms, clean extraction), only the "legacy" `Function`
meets all four. Plain structural recursion on an `Acc` argument, with `Acc_inv` at the
recursive call, meets all four too. Properties are then proved by well-founded induction on
the *measured argument* followed by destructing the `Acc`, not by induction on the `Acc`
proof ("the usual problems with dependent induction"). Appendices: Tarski iteration, and DFS
on an acyclic graph with an `incl l (successors x)` invariant **[cited]**. *Steal:*
confirmation that option B (proof-carrying fuel, `f.%go` with `h: m x < k`) is the right
family; his proof style is what `decreasing` theorems already do. His DFS is a recursion with
no `Nat` measure, which option B can't express directly. *Helps:* SW-199. *Cost:* none.
*Full text:* read (whole pearl, 4 pages).

**C8. Lean 4.24 and 4.25: deriving and recursion.** Release notes v4.24.0 and v4.25.0.
*Claim:* `.ctorIdx` for all inductives (#9951); a `DecidableEq` construction that "avoids
quadratic overhead" (#10152, #10274), and the same for `BEq` and `Ord` (#10268, #10270);
shared same-constructor logic for `BEq`, `DecidableEq` and `Ord` (#10316); `deriving
ReflBEq, LawfulBEq` (#10351); `@[method_specs]`, generating specification theorems for
derived operations (#10302, #10346). In recursion, 4.25 "removes support for reducible
well-founded recursion, a Breaking Change" (#10714) **[cited]**. *Steal:* nothing to change
in `DecEq`: Stitchwort's `T.%decEq` already compares same-constructor pairs field by field and
sends every other pair to one default through `T.%tag` (`crates/elab/src/derive.rs:1-60`),
and `derive_ord.rs` compares tags first **[checked]**. Reuse `T.%tag` for T4. #10714 confirms
that Lean has given up on computing with `Acc`, which is option A of well-founded-recursion.md.
*Helps:* SW-807, SW-199. *Cost:* none. *Full text:* read (both pages).

**C9. Mathlib `deriving Fintype`.** `Mathlib.Tactic.DeriveFintype` docs. *Claim:* the handler
covers structures and inductive types, not "inductive types that are either recursive or that
have indices". For an enumeration (all constructors without arguments) it builds `enumList`,
proved in `ctorIdx` order and duplicate-free, and "the proofs are all linear complexity". For
other inductives it builds a proxy of nested sums, and mapping the i-th constructor costs
time proportional to i, "a source of quadratic complexity" **[cited]**. *Steal:* T4's shape:
`T.all`, proved complete and distinct in linear size by the tag. *Helps:* SW-807 (day 21's
11-deep membership proofs; something for `decide` to range over). *Cost:* elaborator change
(derive). *Full text:* read (docs page).

**C10. Paraskevopoulou, Eline and Lampropoulos, Computing Correctly with Inductive Relations**
(PLDI 2022, doi 10.1145/3519939.3523707; par.nsf.gov/servlets/purl/10407308). *Claim:* one
algorithm, instantiated three ways, derives from an inductive relation (first-order argument
types) a semi-decision procedure, an enumerator and a random generator. The checker returns
`option bool` with a fuel argument and a second fuel for calls to other checkers. Premises
with unbound variables are solved by calling a derived enumerator (`bindEC`), guided by a
user-given set of output positions (like logic-programming modes). Each derived computation
gets a machine-checked soundness and completeness proof (Ltac2, translation validation).
Completeness for negation fails in general (their `zero` predicate returns `None` forever). It
derived 97 computations from the 109 relations in Software Foundations, with under 2%
overhead against hand-written generators. A derived `Sorted` checker turns an 11 s proof
(16 s `Qed`) into 60 ms by reflection. The authors call total decision procedures a "minor
variation" but "user-unfriendly", because the termination checker can fail on code the user
didn't write **[cited]**. *Steal:* derived `Decidable` instances for user propositions
declared as data (`Le`, `Sorted`, typing judgements), so `auto` and `if h:` work on them; and
input generators that satisfy a hypothesis, so counterexample search discards fewer inputs.
In Stitchwort, fuel would make the checker a test, not a `Decidable` instance, unless the
relation's structure gives termination. *Helps:* DESIGN §6 `auto`/`Decidable`;
counterexample-search.md. *Cost:* research project. *Full text:* read (whole paper).

**C11. Chan, Li and Bowman, Is Sized Typing for Coq Practical?** (JFP 33 e1, 2023, doi
10.1017/S0956796822000120; arXiv 1912.05601v4). *Claim:* CICb∗ adds global and local
definitions, cumulativity and impredicative `Prop` to sized CIC, with size inference needing
no annotations, implemented in Coq's kernel. On `MSetList`, compilation goes from 15.1 s to
83.7 s, 77% of it in constraint solving (`solve`, `RecCheck`), which is O(|V||C|) in size
variables and constraints. Definitions are implicitly size-polymorphic, so size variables
multiply: six nested tuple aliases reach 16,382 size variables and take over 120 s. The
slowdown is "intrinsic and unavoidable" for backward-compatible inference, and nested
inductives break subject reduction with sized subtyping, so CICb∗ forbids them. The authors
conclude that sized typing "might be" practical "only if we allow ourselves to ask users to
put in a little work": explicit size quantification, filled in by elaboration. They also
criticise Coq's guard checker for inlining definitions, which they call anti-modular
**[cited]**. *Steal:* closes SW-199's option D for *inferred* sizes. Explicit sizes stay a
research route. Stitchwort's SCT doesn't inline other definitions (nested-data-types.md §9),
which avoids the modularity problem they describe. *Helps:* SW-199. *Cost:* none. *Full
text:* read (§1, §2, §6 evaluation, §8 in full; §3-5 calculus and metatheory and §7 related
work skimmed).

**C12. Laarakker, Otten and van den Berg, Constructing (Co)inductive Types via Large Sizes**
(FSCD 2026, LIPIcs 378 art. 21; arXiv 2602.18921). *Claim:* Agda's sized types are "currently
inconsistent" because of the largest size `∞`: "Agda proves ∞ < ∞", while any strict
well-order is irreflexive. They replace `∞` with parametric quantifiers over a large type of
sizes (`∃i. Indᵢ`, `∀i. CoIndᵢ`) and construct all inductive and coinductive types, not only
finitely branching ones, with consistency from a realisability model in which sizes are an
uncountable ordinal. For an implementation they still lack computing parametricity axioms, a
computing β-rule for size recursion (a naive one "breaks normalisation"), and decidable size
inequality, which would mean asking the user for proofs of `i < j` **[cited]**. *Steal:* the
state of the art: sized types for a proof assistant are still research in 2026. *Helps:*
SW-199 option D. *Cost:* none. *Full text:* read (§1-2 and §5 in full; §3 constructions and §4
realisability model skimmed; FSCD PDF from drops.dagstuhl.de).

**C13. Hyvernat, The Size-Change Principle for Mixed Inductive and Coinductive Types** (LMCS
21(3:20), 2025; arXiv 2407.05715). *Claim:* a provably correct totality checker, based on the
size-change principle, for a first-order ML-like language (`chariot`) with data and codata.
Checking termination and productivity separately is not enough with nested (co)inductive
types: `bad_s = { Head = Node bad_s; Tail = bad_s }` over `data stree = Node (stream stree)`
is terminating and productive but yields an inhabitant of every type. Types get parity-game
priorities (odd for data, even for codata). Calls are composed and collapsed with bounds `B`
(weights) and `D` (constructor depth), and every idempotent coherent loop must either output
infinitely many even-priority constructors or strip infinitely many odd ones from its input.
At least PSPACE-hard; "B = 2 and D = 2 is enough for most cases". It accepts a stream-of-lists
`sums` that Agda rejects. Dependent types and higher-order functions are future work
**[cited]**. A side note on the purely inductive part: `f (C2 x) = f (C1 x)` needs `D ≥ 1`.
Stitchwort's SCT records only `<`, `≤` and unknown, so it would reject that call
**[inferred, not run]**. *Steal:* the warning for D1911: codata needs a totality checker in
this style, not a second productivity pass. *Helps:* D1911. *Cost:* research. *Full text:*
read (§1, §4 with examples and implementation, concluding remarks in full; §2-3 semantics and
call-graph construction skimmed).

**C14. Lean coinductive predicates.** Lean 4.25 notes, #10333. *Claim:* "introduces a
`coinductive` keyword", defining coinductive predicates with `inductive`'s syntax, in mutual
blocks that may mix inductive and coinductive definitions **[cited]**. That they are greatest
fixpoints on a lattice, and that Lean has no coinductive *data* in core, come from search
summaries **[unverified]**. *Steal:* if Stitchwort ever wants coinduction, start with
coinductive *propositions*, which need no productivity checker. *Helps:* D1911. *Cost:*
research. *Full text:* read (4.25 notes).

**C15. Theocharis and Brady, Custom Representations of Inductive Families** (arXiv
2505.21225v2, May 2025). *Claim:* datatt extends MLTT so that each data type comes with an
inductive algebra (constructors, eliminator, propositional coherence) giving its runtime
representation. A modality `Repr` with `repr`/`unrepr` converts between a type and its
representation, and a translation to extensional MLTT replaces every data type by its
representation, which is formalised in Agda. Examples: `Nat` as a GMP integer (the "Nat
hack" without compiler special-casing); `Vec T n` as `{l: List T | length l = n}`, so
`forget-length` and `remember-length` compile to the identity; zero-copy deserialisation of a
record into a byte buffer. The prototype, Superfluid, compiles to JavaScript with `Nat` as
`BigInt` and `List`/`SnocList`/`Vec` as arrays, but it doesn't yet check coherence proofs and
treats one rule definitionally "at the cost of breaking decidability of equality". Idris 2
has since merged an optimisation that erases forgetful and recomputation functions for
list-, maybe- and number-like types **[cited]**. *Steal:* the question behind T5: which
Stitchwort families are a number or a list underneath (`Fin n`, `Vec a n`, `List.Member`,
`Mod n`), and are the conversions between them free at run time? *Helps:* fast-runtime.md,
JS, native. *Cost:* small (audit); research (a representation feature). *Full text:* read
(§1-7).

**C16. Idris 2 Nat-like optimisation.** idris2.readthedocs.io, "Builtins". *Claim:* a type
with two constructors after erasure, one with no arguments and one with exactly one strict
argument of the same type constructor, compiles to a big integer, so indexed `Fin` qualifies.
`%builtin Natural` forces it for other constructor orders; `%transform` makes chosen
operations (`plus`, `eqNat`) O(1). Conversion functions are optimised only in one shape, and
"it may be sensitive to seemingly insignificant changes"; `%builtin IntegerToNatural` asserts
a conversion's correctness, and that is "the programmer's responsibility" **[cited]**.
*Steal:* T5's checklist. Stitchwort already pins its own natives by content hash for the
kernel (kernel.md C10); a runtime-only representation choice is a separate, untrusted
question. *Cost:* small (audit). *Full text:* read (docs page).

**C17. Richter and Böhler, From Pattern Unification Towards Pattern Matching Unification**
(extended abstract, TyDe 2026; arXiv 2607.18455). *Claim:* constraints like `?P true = Nat,
?P false = Bool` (an omitted motive) fall outside Miller patterns, functions-as-constructors
and deterministic higher-order patterns. A prototype of under 3,000 lines of Lean collects
such delayed constraints and hands them to its dependent pattern-matching compiler as a
definition to synthesise; on failure the constraint stays unsolved. The litmus test
`ind _ b 1 false` is rejected by Rocq and Lean and accepted by the prototype. Recursion and
the boundary of the solvable fragment (indexed families, GADTs) are open **[cited]**.
*Steal:* a motive-inference fallback after unification fails (`E-MATCH-MOTIVE`, `J`
applications): try to compile the stuck constraints as a case split. *Helps:* elaboration.md's
cluster; SW-802. *Cost:* elaborator change, research-grade. *Full text:* read (whole
abstract, 2 pages).

**C18. Agda 2.8.0 changelog.** hackage.haskell.org/package/Agda-2.8.0/changelog. *Claim:*
termination "more permissive wrt non-exact clause reduction" (#7502); a postponed
`DisambiguateConstructor` typechecking problem, with a warning for an unresolved constructor
name (#7814); `with` fixes (#7789, #7651); a hint to use `--guardedness` when termination
fails, now also with `--sized-types` (#7931); opacity forgotten when checking signatures
(#7857) **[cited]**. *Steal:* for SW-510, Agda resolves an overloaded constructor by type and
*postpones* the choice while the type is unknown. That Agda allows overloaded constructor
names at all is from the manual as I remember it **[unverified]**. *Helps:* SW-510. *Cost:*
elaborator change. *Full text:* read (changelog).

**C19. Lean dotted identifiers.** Lean reference, error explanation `invalidDottedIdent`.
*Claim:* `.ctor` omits the namespace when Lean can infer it from the *expected* type. The
argument's type is never used (`.reverse (xs ++ xs)` fails without a return type), and a
universe such as `Prop` doesn't support it (`.true` on `n > 42` needs `decide`) **[cited]**.
*Steal:* for SW-510, an explicit short form resolved from the expected type, rather than
making bare constructor names ambiguous. *Helps:* SW-510. *Cost:* elaborator change. *Full
text:* read (page).

**C20. Escot and Cockx, Practical generic programming over a universe of native datatypes**
(ICFP 2022, PACMPL 6, doi 10.1145/3547644). **NOT READ** (§9). Search summary: a library of
generic programs over a description universe, specialised to native Agda datatypes "with a
simple one-liner" by reflection **[unverified]**. Supports nothing below.

**C21. Ko, Chen and Lin, Datatype-generic programming meets elaborator reflection** (ICFP
2022, PACMPL 6, doi 10.1145/3547629). **NOT READ** (§9). Search summary: metaprograms that
instantiate datatype-generic programs as and for native Agda datatypes **[unverified]**.
Supports nothing below.

## 5. Deep reads

### 5.1 Generated functional induction and case principles (C1, C2, C4)

**What Lean does** [cited: FunInd docstring, 4.17 notes]. For `f`, `f.induct` takes `f`'s
fixed parameters and a motive over the others. Each branch of `f` (an `if` arm, a `match`
arm, roughly each tail position) is a case. A case's premises are the branch's local facts
(the `if` condition, and `let`s and `have`s judged useful) and one induction hypothesis per
recursive call, quantified over any binders the call sits under. Where patterns overlap, the
matcher's splitter adds the assumptions that earlier patterns didn't match. Mutual functions
get one motive each. `f.fun_cases` does the same without induction hypotheses, for any
function; its unfolding variant gives the motive `f`'s result in each case. Both are built by
walking the compiled body (`brecOn` or `WellFounded.fix`) and building the proof alongside.

**Stitchwort today** [checked].

- Every leaf of a case tree holds by computation (equation-lemmas.md §0), so Lean's main
  reason for equation lemmas is absent. What remains is *naming the cases*: a proof about `f`
  must split the way `f` does, and an inner `match` in `f` is a generated function that source
  can't name (equation-lemmas.md §0 item 5; D231-D233 "not now").
- A theorem can recurse on the same `decreasing` measure as `f`, "which is functional
  induction without a new principle" (well-founded-recursion.md §0). D1439 (SW-802) asks for
  per-branch lemmas after days 12 and 16 hit `E-MATCH-MOTIVE`; SW-809 records the same for
  `match found:`.
- Nested types need `T.induct` with `List.All motive items`, built as mutual helper theorems
  (nested-data-types.md §9, D1823), because `sct.rs` doesn't look inside `allOf`.

**Mapping.** One generator, three outputs, all ordinary theorems the kernel checks, so nothing
new is trusted:

1. **`f.cases`** (Lean's `fun_cases`): `(x…) -> (motive: A… -> B -> Prop) -> (one premise per
   leaf of f's case tree: the leaf's pattern variables, the equations the tree learned on the
   way, the hypotheses from `if h:`, and the motive at the leaf's value) -> motive x… (f x…)`.
   Proof: the same case tree, with `premise_i …` at each leaf. It type-checks because `f x…`
   computes to the leaf there **[inferred]**. There is no recursion, so no termination
   question. A lifted inner `match` is followed into, since its tree is part of the
   definition's; that answers SW-809.
2. **`f.induct`** for a structurally recursive `f`: as `f.cases`, plus one hypothesis `motive
   y…` per recursive call `f y…` in the leaf. Proof: a theorem by the same recursion. Its
   calls have the same size-change graphs as `f`'s, so `sct.rs` accepts it for the same reason
   **[inferred]**.
3. **`f.induct` for `decreasing`**: recursion on the same measure. Each induction hypothesis
   takes the leaf's `decreasing` obligation, which `auto` already found for `f`. The proof has
   `f.%go`'s shape with the motive.
4. **`T.induct`** for a nested type is `f.induct` of the identity-like traversal. The
   generator for D1823 reuses the same code, with `D.All` hypotheses for calls under a
   container's helper.

**Assumptions the recommendation depends on.** (A1) The elaborator keeps, per leaf of a
compiled case tree, the pattern variables, the index equations learned and the `if`
conditions, or can recompute them. `cases.rs`/`matching.rs` would have to expose this; not
checked in code. (A2) A recursive call under a lambda (stage 3a callbacks, `sumBy (d => f
d)`) needs its induction hypothesis quantified over the lambda's variable *and* a fact
relating it to the input. Without `attach` there is no such fact: this is Breitner's "the
cake is a lie" (C4). So T1 should at first refuse to generate `f.induct` for calls under
lambdas that don't use `attach`, and say so. (A3) Generated theorems are made on demand (only
when named), as Lean's are, so programs that don't use them aren't slowed.

**Risks.** Hash and cache churn if they are generated eagerly; A3 avoids it. Overlapping
equations: Stitchwort compiles top-to-bottom clauses into a tree, so "earlier patterns didn't
match" is already in the tree's shape, and the risk is only in how premises are *printed*.
Mutual groups need one motive per member; `decreasing` doesn't support mutual groups yet
(SW-199), so that part waits.

**Next step.** T1: one design note covering `f.cases`, `f.induct` (structural and
`decreasing`) and `T.induct`, closing D231 (superseded), D1439 and D1823 in one place.

### 5.2 Termination: automatic attach, measure suggestions, and Acc done right (C3, C4, C5, C7, C11, C12)

**Automatic attach** [cited: Preprocess docstring]. Lean's pass is a simp set with two rules
per higher-order function, keyed on a marker for "a parameter of the function being defined".
**Stitchwort today** [checked: well-founded-recursion.md "As built (stage 3a/3b)"]: calls under
lambdas work through congruence lemmas `FCong` found beside `F`. `List.attach`, `List.Member`
and `List.memMap`/`memFilter`/`memRangeFrom` exist, and `auto` finds a decrease proof from a
lambda's own `h`. But the user writes `xs.attach.sumBy (e => …)` and names the proof
(`[decreasing := belowOfRun d.value n d.isIn]`). Day 2 kept its `if h:` guards because the
attached form was harder to read (3b item 7).

*Mapping.* When `decreasing`'s obligation for a call inside `F … (x => … f x …) xs` fails,
and `F` has an "attach rule" registered beside it (as `FCong` is), rewrite to `F … ((e:
Member) => … f e.value …) xs.attach` and retry `auto` with `e.isIn` in scope. Then state the
generated `f.unfold` in the un-attached form, using `List.mapAttach`/`sumByAttach`. Rules are
lemmas found by name (`List.sumBy.attach`) and validated like `FCong` (3a item 3), so the pass
is extensible and untrusted.

*Assumptions.* (B1) Only callbacks over lists matter for now (day 2, nested stage 3); others
keep the manual form. (B2) `auto` can turn `List.Mem x xs` and the measure into the needed `<`
for common cases (`List.size` sums); D1450 asks for this. (B3) The equation shown to users
stays the un-attached one; otherwise readability (D519) regresses.

**Measure suggestions** [cited: GuessLex docstring]. Stitchwort's SCT already accepts
lexicographic and permuted descent *structurally*, which Lean needs GuessLex for. What's
missing is the step after failure. `E-TERMINATION` should try a few `decreasing` candidates
(each `Nat` parameter, each data parameter's size where a size function exists, ordered pairs
of those), check each fully with the `decreasing` elaboration and `auto`, bounded as GuessLex
is, and print the first that works ("accepted with `decreasing (n, m)`"). Otherwise it should
print GuessLex-style per-call findings. No rule changes, only a message **[inferred]**. Risk:
a suggestion must be checked by the same `auto` that will run, or it fails when pasted; the
full check is the fix.

**Acc done right** [cited, full text]. Leroy's pearl supports option B from the other side.
His recursion is structural on an `Acc` proof that extraction erases, and his proofs go by
induction on the argument, not on the evidence. Stitchwort's fuel `k` with `h: m x < k` is the
same idea with a `Nat` in place of `Acc`, chosen so tests compute. Lean has since dropped
reducible well-founded recursion entirely (C8, #10714), and kernel.md §5.2 shows `Acc`'s large
elimination is the next thing kernels are removing. One gap his examples show is recursion on
a well-founded *relation* with no `Nat` measure (DFS over an acyclic graph); today that is
written with fuel by hand. *Assumption:* no AoC program has needed it yet (not checked).

**Sized types** [cited, full text]. Chan, Li and Bowman (C11) close option D for *inferred*
sizes. Explicit sizes are what they recommend, and Laarakker, Otten and van den Berg (C12)
show that even the theory for a consistent design is 2026 research with three open problems.
Record in well-founded-recursion.md that option D stays closed, citing both.

**Next steps.** T2 (auto-attach), T3 (suggestions).

### 5.3 Deriving: enumerations and relations (C8, C9, C10)

**Stitchwort today** [checked: `crates/elab/src/derive.rs:1-60`, `derive_ord.rs:1-50`].
Derived `DecEq`, `Ord`, `Show` and `T.ext` are generated as source and elaborated, so the
kernel checks them. `T.%tag` numbers the constructors. `T.%decEq` has one equation per
constructor plus a default that refutes by tags (`T.%differ`), so its size is linear in the
number of constructors, as Lean's 2025 construction is (C8).

**SW-807: enumerating values.** Mathlib's handler (C9) shows the cheap, linear version for
enumerations: a list of the constructors, proved complete and duplicate-free in `ctorIdx`
order. The Stitchwort mapping, for a type whose constructors have no fields:

- `T.all: List T` in declaration order;
- `T.allComplete: (x: T) -> List.Mem x T.all`, by one case split, each branch a fixed
  position in the `Or` chain (linear);
- `T.allDistinct: List.Distinct T.all`, by `T.%tag` (the tags of `T.all` are `0…n-1`), so no
  `n²` disequalities;
- and an instance of an "enumerable" interface if the library gets one (it has none today;
  `decide` over `T` would need it).

Extending to fields of finite types (a record of two enumerations) is Mathlib's quadratic
proxy; leave it until a program asks. *Assumptions:* (E1) day 21's need is enumerations only
(SW-807 says "constructor-only types"); (E2) `List.Distinct` exists (it does, for day 7;
well-founded-recursion.md 3b item 1).

**Specification lemmas.** Lean 4.25's `@[method_specs]` and `deriving LawfulBEq` (C8) generate
the laws of derived operations. Stitchwort's derived `DecEq` *is* a proof (a `Decidable`), so
it needs none. A derived `Ord`'s laws are already part of the `Ord` interface **[checked:
docs/syntax.md, Interfaces]**.

**Derived decision procedures for relations** (C10). The PLDI 2022 framework derives, from an
inductive relation, a fuelled checker, an enumerator and a generator, each proved sound and
complete. For Stitchwort this would give `Decidable (Le a b)` for user-declared propositions,
and generators that produce only inputs satisfying a hypothesis. Its reflection example
(11 s to 60 ms) is the same win `auto` gets from a `Decidable` instance. It remains a research
project. The derived checker is fuelled, so a `Decidable` instance would need a termination
argument per relation, which the authors themselves avoided as "user-unfriendly".

**Next step.** T4.

### 5.4 Codata and partiality: should Stitchwort have streams? (C6, C13, C14)

**What exists** [cited, full text]. Hyvernat (C13): checking termination and productivity
separately is not enough with nested (co)inductive types (`bad_s`); a sound checker needs
parity-game priorities and an adapted size-change principle, at least PSPACE-hard, for
first-order programs without dependent types. Lean, since 2025, has coinductive *predicates*
(C14), and `partial_fixpoint` gives possibly non-terminating functions propositional equations
and partial-correctness theorems when the result is in a suitable monad such as `Option`
(C6). Agda's sized types, its usual route to coinduction, are inconsistent (C12), and Agda now
hints `--guardedness` instead (C18).

**Stitchwort today** [checked: docs/core.md "Partial computations"; DESIGN §5]. `Partial`
functions are translated to `Effect.pfix`, opaque constants with no equations, consistent
because every `Effect.Delay op res a` can be read as a one-element set. The checker never
evaluates them, and nothing about them can be proved. Bounded work uses fuel (DESIGN §5,
"Fuel"). A stream of inputs is handled by `IO` and other abilities, not by data.

**Mapping.**

- *Codata (streams):* no ticket asks for it. Every use in AoC and rogue so far is either finite
  input or a loop that `Partial` or fuel covers. Adding it would need a totality checker in
  Hyvernat's style (which doesn't handle dependent types yet), copatterns or guarded
  constructors, and erasure and JS work. **Recommend: not now** (D1911).
- *Coinductive propositions:* cheap in Lean because predicates need no productivity checker.
  A first use would be "this `Partial` program runs forever", or bisimilarity of two
  `Effect.Delay` values; Stitchwort's one-element-set model can't state either. Not now.
- *Reasoning about `Partial` functions* (`partial_fixpoint`-style partial correctness):
  giving `Effect.pfix` equations would change the trusted part (`crates/core/src/partial.rs`)
  and its model. A user-level alternative already exists: write the function with fuel,
  returning `Option` (total), prove partial correctness of that, and run the `Partial` one.
  **Research**, no ticket.

**Assumptions.** (P1) No planned program needs infinite data structures (checked against the
board only). (P2) The `Partial` model stays a one-element set.

**Next step.** D1911 only.

## 6. Steal next

Ranked by value over effort. Every row rests on sources read in full.

| Rank | Idea | Source | Helps | Cost |
|---|---|---|---|---|
| 1 | Generated `f.cases` and `f.induct` (and `T.induct` from the same generator) | C1, C2, C4 | SW-802, SW-809, SW-199 stage 3, D1823 | elaborator change, after a design note |
| 2 | Derived `T.all` with linear completeness and distinctness proofs for enumerations | C8, C9 | SW-807 | elaborator change (derive), small |
| 3 | `E-TERMINATION` suggests a `decreasing` clause that `auto` accepts, or prints per-call findings | C5 | DESIGN §5 messages | elaborator change, small |
| 4 | Automatic `attach` for recursive calls inside list callbacks, rules beside `FCong` | C3, C4 | SW-199 stage 3b, D1450 | elaborator change |
| 5 | Constructor short form resolved by expected type (`.Quit`), postponed when unknown | C18, C19 | SW-510 | design note, then elaborator change |
| 6 | Audit runtime representations of Nat-like and list-like families (`Fin`, `Vec`, `Member`, `Mod`) | C15, C16 | fast runtime, JS, native | small (audit) |
| 7 | Record in the note that SW-199's option D (sized types) stays closed | C11, C12 | SW-199 | one paragraph |
| 8 | Motive inference by pattern-matching unification as a fallback | C17 | `E-MATCH-MOTIVE` | research |
| 9 | Derived decision procedures and generators for inductive relations | C10 | `auto`, counterexample search | research |
| 10 | Partial correctness for `Partial` functions; coinductive propositions | C6, C14 | partial.md | research, not now |

## 7. Proposed tickets

Label `research` on each. Not added to the board.

**T1. Design note: generated case and induction principles (`f.cases`, `f.induct`,
`T.induct`).** One note covering what equation-lemmas.md D231-D233, SW-802 (D1439), SW-199
stage 3 and nested-data-types.md §9 (D1823) each ask for. It should give the statement shapes
of §5.1 (premises per leaf: pattern variables, learned equations, `if h:` facts, an induction
hypothesis per recursive call), and generate them on demand as checked theorems (structural by
the same recursion, `decreasing` by the same measure). It should say what is refused at first
(calls under lambdas without `attach`; mutual `decreasing`), and redo the day 12, day 16 and
day 23 proofs with `f.cases` as evidence. Refs: §5.1; Lean `FunInd`; Breitner blog 816.

**T2. Automatic `attach` for `decreasing` calls inside list callbacks.** When `auto` can't
prove a call's obligation inside `F … (x => … f x …) xs`, and an attach rule is registered
beside `F` (found by name and validated, as `FCong` is), rewrite to the attached form, retry,
and state `f.unfold` in the un-attached form. Start with `List.map`, `sumBy`, `foldLeft` and
`filterMap`. Accept: day 2's weight without a guard and without a user `attach`; the
`examples/accept/decreasing-attach.sw` cases unchanged. Refs: §5.2; Lean `wf_preprocess`.

**T3. `E-TERMINATION` suggests a `decreasing` clause.** On failure, try bounded candidates
(each `Nat` parameter, each data parameter's size where a size function is known, ordered
pairs), check each fully with the `decreasing` elaboration and `auto`, and add the first that
succeeds to the message. Otherwise list, per recursive call, which candidates went down,
stayed equal or were unknown (GuessLex's table). No rule changes. Refs: §5.2; GuessLex.

**T4. Derive `T.all` for enumerations (SW-807).** For a type whose constructors have no
fields: `T.all`, `T.allComplete` and `T.allDistinct` (by `T.%tag`), linear in the number of
constructors. Test on day 21's type, and on a 40-constructor enumeration for check time.
Refs: §5.3; Mathlib `DeriveFintype`.

**T5. Audit: runtime representation of Nat-like and list-like families.** For `Fin n`, `Vec a
n`, `List.Member`, `Mod n` and enumerations: what the fast runtime, JS and native backends
store, and whether the conversions between them (`Fin.toNat`, `Vec.toList`, `Member.value`)
cost anything at run time. Output: a table and, if needed, tickets. Refs: C15, C16.

**T6. Design note: constructors resolved by expected type (SW-510).** Options: a short form
`.Quit` resolved from the expected type (Lean), postponed while the type is unknown (Agda's
`DisambiguateConstructor`); bare names resolved by type; or namespaced constructors
(`Action.Quit`) with an import form. Use rogue's `Quit`/`GaveUp` rename as the example. Refs:
C18, C19.

## 8. Decisions

**D1910. Write T1 as one design note covering `f.cases`, `f.induct` and `T.induct`, replacing
D231-D233's "not now" and answering D1439 and D1823 together?** Assumptions: (A1) the case
tree's per-leaf facts can be recovered; (A3) generation is on demand. [Yes.]

**D1911. Keep codata out of Stitchwort for now (no streams, no coinductive types or
propositions), and revisit only when a program needs infinite data?** Assumptions: (P1) no
planned program needs it; (P2) the `Partial` model stays a one-element set. Hyvernat's result
means a later design needs its own totality checker, not a second SCT pass. [Yes.]

**D1912. Build T4 (derived `T.all` for enumerations) as SW-807's answer, leaving types with
fields until asked?** Assumption: (E1) day 21's type is an enumeration. [Yes.]

## 9. Sources not reached

**Full text not reachable (for Matt to fetch).**

| Title | DOI | URLs tried, and what each returned |
|---|---|---|
| Escot and Cockx, Practical generic programming over a universe of native datatypes (ICFP 2022) | 10.1145/3547644 | `repository.tudelft.nl/file/File_1f762247-…` and `/record/uuid:3fe37bbd-…`: connection refused; `dl.acm.org/doi/pdf/10.1145/3547644`: an HTML page, not a PDF; Semantic Scholar API: `openAccessPdf` points to the same ACM URL |
| Ko, Chen and Lin, Datatype-generic programming meets elaborator reflection (ICFP 2022) | 10.1145/3547629 | `dl.acm.org/doi/pdf/10.1145/3547629`: an HTML page; Semantic Scholar API: points to the same ACM URL; Zenodo artefact 10.5281/zenodo.6954977 not tried |

Other gaps:

- **Web-search budget.** The session's shared limit ran out at Q38; Q38 (Dafny's default
  `decreases`) was not run. Not searched at all: Idris 2's CHANGELOG (totality), Rocq 9.x
  release notes on fixpoints, Lean 4.12/4.13 notes on nested structural recursion, F*'s
  termination, Liquid Haskell's termination metrics, `with`/views papers since 2022,
  non-empty list types in Lean/Agda libraries (SW-811), or-patterns in Lean/Agda (SW-676).
  This register makes no claim about them.
- **Fetch failures (not papers).** Lean's functional-induction blog post (redirects to the
  Internet Archive, which the fetch tool refuses); the Lean reference's partial-fixpoint
  subpage (404); the TU Delft repository (connection refused), so the Agda Core termination
  thesis was not read; Agda's manual on overloaded constructors (the data-types page doesn't
  cover it); the last 17k characters of the Lean reference's recursion chapter.
- **Screened "maybe" papers not read** (rows 22-38 of §3); they support nothing here. Of
  these, Kovács (POPL 2026), Møgelberg and Zwart (arXiv 2311.15919) and Fiore, Pitts and
  Steenkamp (arXiv 2101.02994) were downloaded and are readable if a later pass wants them.
- **PDF text.** `pdftotext` via `nix shell nixpkgs#poppler-utils` worked for every PDF that
  downloaded.
- **Venue sweeps not done** year by year: TyDe, CPP, ITP, FSCD, TYPES 2022-2026 programmes;
  Lean workshop programmes; Haskell Symposium (no in-window deriving paper surfaced). A
  refresh should start with Lean's release notes (they moved fastest), the TyDe programme and
  Breitner's blog.
