# Literature trawl: proof automation

**Counts: screened 72; carded 29; read in full 25; not read 4 (C26-C29; listed in §9, none for
Matt to fetch).** No NOT READ card supports a deep read, a ranking or a recommendation.

Redone 30 Oct 2026 from full texts; replaces the 29 Oct abstract-based version.

**Claims from the 29 Oct version found wrong** (each checked this time against the full source,
our code, or a run of the release CLI):

1. *"`stitchwort check` output is human-readable only: no JSON diagnostics or goal output in
   `docs/` or the driver"* (old C22, §5.5, T6). Wrong. `check --index FILE` (or `-`) writes JSON
   whose `diagnostics` include every error and every `?` goal, with severity `goal`
   (`crates/driver/src/nav.rs:183-190`; docs/proposals/code-navigation.md:3, "version 2 with
   diagnostics", built for SW-211). Run on a probe file, it printed
   `{"severity":"goal","code":"GOAL",…,"labels":[{…,"message":"xs: List Nat\nh: … \n⊢ List.length xs ≤ 5"}],"notes":[…counterexample…]}`.
   What is missing is narrower: the goal and its context come as one rendered string, not as
   names and types. infrastructure.md C20 found the same.
2. *"Prop connectives in Stitchwort are `if`s on `Bool`s (`logic.rs:4-11`, per simp.md)"* (old
   §5.4, risks). Wrong. `logic.rs:4-13` gives two readings. As a `Bool`, `a && b` is
   `if a then b else False`. "As a proposition: `And a b`, `Or a b` and `Not a`, each operand a
   proposition."
3. *The split equations of `cases` are "`%splitN`"* (old §5.1 mapping, §5.2, T1). Wrong name.
   They are `%case1`, `%case2`, … (`const EQUATION: &str = "%case"`, `crates/elab/src/cases.rs:65`;
   docs/syntax.md:1664).
4. *"A derived checker for an inductive proposition is a `Decidable` instance with a proof"*
   (old C19). Wrong. Paraskevopoulou et al. derive fuel-bounded *semi*-decision procedures of
   type `option bool`: "None signifies that it needs additional fuel to reach a conclusion one
   way or another" (C13, §2, Figure 1). Their soundness and completeness proofs are relative to
   that fuel. They are not `Decidable` instances.
5. *De Moura's `grind` slides were "image-only PDFs"* (old §9). Wrong.
   `leodemoura.github.io/files/grind.pdf` has a text layer. `pdftotext` extracts 1,519 words
   from it (C4). The old lane simply had no PDF tool (SW-897 lesson 1).
6. *A local hypothesis `∀ y, lookup = Some y → …` would be instantiated by "Lean's `→`
   pattern"* (old §5.1). Imprecise. `→` is an attribute modifier for library theorems. It
   "instructs `grind` to select a multi-pattern from the hypotheses of the theorem" (reference
   §16.12). Local `∀` facts in the goal become e-matching theorems through
   `mkEMatchTheoremUsingSingletonPatterns`: "We use this function to implement local forall
   expressions in a `grind` goal" (`EMatchTheorem.lean:1302-1306`, C3).

Two old **[unverified]** claims are now confirmed:
- Lean generates `f.induct` and `f.fun_cases` on demand through reserved names (C8);
- Plausible "behaves like `admit`" when it finds no counterexample (C10).

The old claim that `cases` "has no equivalence classes" is confirmed by a run (§5.1).

*SW-894, cluster 4. Researched 30 October 2026 against `main` at `aecac12a`. Research only: no
code changed and no tests run. A few probe files were checked with the release CLI in the main
checkout (built 30 Oct 11:57). The probes live in the session scratchpad, not the repo. Window:
2022 onwards (D1831). Older work appears only where in-window work or our own code relies on
it, and is marked **classic**.*

Reading protocol: every card says **Full text: read (source; sections)** or **NOT READ**. PDFs
were read with `pdftotext` from `nix shell nixpkgs#poppler-utils`. Lean, Plausible and lean-egg
sources were fetched whole from GitHub at a fixed commit and read as text:
- `leanprover/lean4` at `0f852cc8`, master on 30 Oct;
- `leanprover-community/plausible` at `129d1ba9`.

Lean reference manual pages ("latest", 4.36.0-rc2 on 30 Oct) were downloaded with `curl` and
converted to text. For a long paper, "read" means the sections named on the card were read in
full and the rest skimmed or not read, as the card says. For a source file it means the module
documentation and the functions named.

Labels: **[checked]** read in the full text of the named source, or in Stitchwort's code or docs
at the place given; **[run]** a probe checked with the release CLI on 30 Oct (§2);
**[inferred]** my reasoning, not tested; **[unverified]** not confirmed in a full source.
Unverified claims are context only and never support a recommendation.

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

Stitchwort's automation is already the kind the literature recommends for a small prover:
- untrusted search with a certificate the kernel checks (`omega`, `ring`);
- proof terms built from `match`, `J` and `fromYes` (`cases`, `auto`);
- a counterexample search that is advisory only.

Nothing read argues for trusting more. Four things are worth acting on:

- **Equalities among hypotheses, for `cases` (§5.1).** Three probes fail today **[run]**:
  - two hypotheses equating a list with `Cons` and with `Nil`;
  - `f a = c` from `a = b` and `f b = c`;
  - a local hypothesis `(y: Nat) → lookup = Some y → y < 5` applied to `lookup = Some y0`.

  Congruence closure with a proof forest settles the first two. It is Selsam and de Moura's
  algorithm, which `grind` implements (C1, C3). Instantiating local `∀` facts settles the
  third. The dependent-argument risk that worried the old version has a ready answer.
  Stitchwort has axiom K (docs/core.md:121, :142), and `Bool.uniqueEq` and `DecEq.uniqueEq`
  are in std. So C1's "subsingleton" rule makes two calls that differ only in an equation proof
  equal. T1, D2000.
- **The counterexample search misses false statements whose hypothesis is satisfied only by
  large inputs (§5.2).** `increasing xs = True → xs.length < 6` gets "none in 10000 cases" from
  `check --counterexamples` **[run]**. The search filters by hypotheses
  (docs/syntax.md:1254). It gives up only when hypotheses hold in under 10% of inputs
  (`crates/driver/src/counterexample.rs:82`). Here they hold often, but only for short lists.
  The 2026 literature now builds generators from the hypothesis itself:
  - Palamedes synthesises them from Lean `Bool` predicates (C11);
  - QuickChick orders hypotheses by "density" (C12).

  First measure (T2), then a design note (T3).
- **Case theorems from the definition (§5.3).** Lean's `f.fun_cases` and `f.induct` mirror a
  function's branches. They add an equation for each discriminant that isn't a plain parameter,
  "just as if the user wrote `match h : x with …`", and are generated on first use (C8). That
  is the shape SW-802 and SW-809 need. T4, D2001.
- **Show what search found (§5.4).** Every system that keeps proofs maintainable writes the
  found proof back as text:
  - Sledgehammer, with instantiations (C21);
  - querysmt, as a script (C18);
  - `grind?` (C2).

  For `cases` that is cheap (T5). External SMT or ATP back ends (C15-C20) are not worth their
  translation and reconstruction layers here. Even the best one leaves gaps, and Stitchwort's
  failures are about facts in scope, not about large lemma libraries.

Bearing on decide.md (D1971-D1973), in short (§5.1 has the detail):
- D1971 stands. `grind` also splits only up to a bound and is "not designed for goals whose
  search space explodes" (C2).
- The literature adds two options to D1971: propagation over `Bool` connectives before
  splitting (C2), and, for the budget case, lookahead rather than static choice of what to
  split (C6).
- Nothing read changes D1972 or D1973.

## 2. Method

**Stitchwort read first** [checked], at `aecac12a`:
- `crates/elab/src/`: the headers of `cases.rs` (and `node`, `by_hypothesis`), `auto.rs` (and
  `prove`, `from_facts`, `size_from_member`), `omega.rs`, `omega_search.rs`, `ring.rs`,
  `rewrite.rs` (and `SEARCH_BUDGET`), `congruence.rs`, `decreasing.rs`, `derive_induct.rs`,
  `logic.rs`, `counterexample/mod.rs`, `counterexample/inputs.rs` (constants and the size
  sharing at `:729-757`), and `lift.rs`'s `E-MATCH-MOTIVE` sites;
- `crates/driver/src/counterexample.rs` (verdicts) and `crates/driver/src/nav.rs` (JSON
  diagnostics);
- docs/syntax.md "Goals", "Counterexamples", `omega`, `ring`, `cases` (`:1205-1260`,
  `:1578-1672`);
- docs/core.md on axiom K (`:121`, `:142`);
- docs/proposals: decide.md (whole) and its prototypes' names, counterexample-search.md
  (§4, §10), equation-lemmas.md (§6, §7), omega.md (its prior-art section, by grep), and
  code-navigation.md (status, format);
- board: SW-608, SW-802, SW-807, SW-809, SW-199, SW-687, SW-800.

**Probes** [run]. Two files in the session scratchpad (`sw894probe/probe.sw`, `sparse.sw`) were
checked with `target/release/stitchwort check --no-cache` (with `--counterexamples --verbose`
and `--index -`). The results are quoted in §5.1 and §5.2 and in wrong claim 1.

**Sources.** These were downloaded to the session scratchpad:
- PDFs from arXiv: 1701.04391, 2209.03398, 2405.10188, 2505.14929, 2505.15796, 2506.07477,
  2508.20738, 2601.14495, 2205.00862, 2505.05758, 2610.40538, 2511.12253, 2202.04330 and
  2607.22972, plus 2610.26467 and 2304.04332, which were opened only;
- PDFs from Dagstuhl (LIPIcs.ITP.2024.10), from Lampropoulos's page (`lemonidas.github.io/pdf/`:
  ComputingCorrectly, TestingTheorems, ShrinkingEval, and MergingInductiveRelations, opened
  only), from de Moura's page (`grind.pdf`) and from TU Dresden (Rossel's MSc thesis, opened
  only);
- Lean reference: the `grind` chapter index and §16.1-16.7, 16.9-16.14;
- through GitHub: lean4 `Grind/Proof.lean`, `Grind/EMatchTheorem.lean`, `Grind/Internalize.lean`,
  `Grind/Core.lean`, `Grind/Main.lean`, `Omega/Frontend.lean`, `Omega/Core.lean`,
  `Init/Tactics.lean`, `Meta/Tactic/FunInd.lean` and `WF/GuessLex.lean`; Plausible `README.md`,
  `Tactic.lean` and `Testable.lean`; and lean-egg's README and repository metadata.

ACM DL returned 403 to `curl`. The Internet Archive had no copy of the ACM PDFs I needed (404),
and its availability API rate-limited (429). Semantic Scholar's DOI lookup worked, but its
search rate-limited. The arXiv API was used for all other lookups. No personal data was sent
anywhere.

**Web searches: 6** (of a budget of about 25), all on 30 Oct 2026:

| # | Query | Useful result |
|---|---|---|
| S1 | `Lean 4 grind tactic paper pdf de Moura Ullrich 2026 SMT-inspired` | none (Learned Interventions, C6, already found by the arXiv API) |
| S2 | `Rossel Goens "equality saturation" Lean tactic POPL 2026 pdf arXiv` | DOI and MSc thesis only (C27) |
| S3 | `"Testing Theorems Fully Automatically" QuickChick pdf` | SPLASH page only (PDF later found on the author's page, C12) |
| S4 | `"Interactive Bit Vector Reasoning using Verified Bitblasting" pdf` | DOI only (C28) |
| S5 | `Duper superposition prover Lean ITP 2024 LIPIcs pdf …` | LIPIcs PDF (C16) |
| S6 | `"grind: An SMT-inspired tactic for Lean 4" Morrison de Moura IJCAR 2026` | slides URL (C4); paper not found (C26) |

The arXiv API was queried, at no cost to the search budget, for: grind, equality saturation,
bit-blasting, QuickChick, Duper, functional induction, property testing in Lean, Aesop, e-graphs
in proof assistants, congruence closure with dependent types, Sledgehammer, hammers for Rocq,
Presburger arithmetic in proof assistants, reflection for Coq, generators from inductive
relations, SMT proof reconstruction, Mariposa, Dafny proof stability and Etna.

Every search returned results. I stopped at six because the old leads, the arXiv API and two
author pages covered the scope. As a result, these areas are lightly covered:
- Isabelle Quickcheck and Nitpick: no in-window paper found, classics not re-read;
- CoqHammer and SMTCoq: seen only through C20's and C17's comparisons;
- Rocq `lia`/micromega internals: omega.md's prior-art section already covers them, and only
  C24 is new.

## 3. Screened list

72 sources: 29 carded (25 read, 4 NOT READ), 19 maybe, 24 drop. A "maybe" or "drop" was
judged on title, abstract, a partial read or another register, and supports nothing below.

| # | Source | Verdict | Why |
|---|---|---|---|
| 1 | Selsam, de Moura, Congruence Closure in Intensional Type Theory, IJCAR 2016, **classic** | card C1 | §5.1 |
| 2 | Lean reference manual, *The `grind` tactic* (§16) | card C2 | §5.1, §5.4 |
| 3 | Lean 4 `grind` source: `Proof.lean`, `EMatchTheorem.lean`, `Internalize.lean` | card C3 | §5.1 |
| 4 | de Moura, *The grind Tactic*, slides, 18 Sep 2025 | card C4 | §5.1 |
| 5 | Flatt, Coward, Willsey, Tatlock, Panchekha, Small Proofs from Congruence Closure, FMCAD 2022 | card C5 | §5.1 |
| 6 | Wang et al., Learned Interventions Inside Lean 4's grind, arXiv 2607.22972 (ICML 2026) | card C6 | §5.1, decide.md |
| 7 | Lean 4 `omega` (docstring and frontend) | card C7 | omega context |
| 8 | Lean 4 functional induction and `fun_cases` (`FunInd.lean`, Breitner) | card C8 | §5.3 |
| 9 | Lean 4 `GuessLex.lean` (termination measures, Breitner) | card C9 | `decreasing` |
| 10 | Plausible (Lean 4 property testing) | card C10 | §5.2 |
| 11 | Goldstein, Peleg, Torczon, Sainati, Lampropoulos, Pierce, The Search for Constrained Random Generators, PLDI 2026 | card C11 | §5.2 |
| 12 | Mittelman, Goldstein, Lampropoulos, Testing Theorems, Fully Automatically, OOPSLA 2026 | card C12 | §5.2 |
| 13 | Paraskevopoulou, Eline, Lampropoulos, Computing Correctly with Inductive Relations, PLDI 2022 | card C13 | §5.2 |
| 14 | Keles, Miao, Lampropoulos, Evaluating Shrinking, Haskell 2026 | card C14 | §5.2 |
| 15 | Qian, Clune, Barrett, Avigad, Lean-auto, CAV 2025 | card C15 | §5.4 |
| 16 | Clune, Qian, Bentkamp, Avigad, Duper, ITP 2024 | card C16 | §5.4 |
| 17 | Mohamed et al., lean-smt, CAV 2025 | card C17 | §5.4 |
| 18 | Clune, Barbosa, Avigad, Hint-Based SMT Proof Reconstruction, arXiv 2601.14495 | card C18 | §5.4 |
| 19 | Zhu, Clune, Avigad, Jiang, Welleck, Premise Selection for a Lean Hammer, ICLR 2026 | card C19 | §5.4 |
| 20 | He, Zhang, Gupta, crush: Extensible Proof Automation for Lean, arXiv 2610.40538 | card C20 | §5.4 |
| 21 | Bartl, Blanchette, Nipkow, Exploiting Instantiations from Paramodulation Proofs in Isabelle/HOL, CADE-30 | card C21 | §5.4 |
| 22 | Gross, Erbsen, Philipoom, Agrawal, Chlipala, Verified Rewriting Engine, ITP 2022 | card C22 | `simp` design |
| 23 | Rossel, Goens, Bridging Syntax and Semantics of Lean Expressions in E-Graphs (2024); lean-egg README | card C23 | e-graph rewriting |
| 24 | Sakaguchi, Reflexive tactics for algebra, revisited, ITP 2022 | card C24 | `ring` |
| 25 | Ospanov, Farnia, Yousefzadeh, APOLLO, arXiv 2505.05758 (NeurIPS 2025) | card C25 | LLM loop, briefly |
| 26 | Morrison, de Moura, grind: an SMT-inspired tactic for Lean 4, IJCAR 2026 (system description) | card C26 | NOT READ |
| 27 | Rossel, Schneider, Koehler, Steuwer, Goens, Pen-and-Paper-Style Equational Reasoning by Equality Saturation, POPL 2026 | card C27 | NOT READ |
| 28 | Bhat, Böving et al., Interactive Bitvector Reasoning using Verified Bit-Blasting, OOPSLA 2025 | card C28 | NOT READ |
| 29 | Limperg, From, Aesop, CPP 2023 | card C29 | NOT READ |
| 30 | Rossel, An Equality Saturation Tactic for Lean, MSc thesis, TU Dresden 2024 | maybe | opened only; C27's background |
| 31 | Zhang et al., egglog (Better Together), PLDI 2023 | maybe | opened only; an engine, only if we build an e-graph |
| 32 | Koehler et al., Guided Equality Saturation, POPL 2024 | maybe | search summary only |
| 33 | Lean `simp?`, `simp only`, Mathlib flexible linter | maybe | not read |
| 34 | Lean `try?` (release notes 2025-26) | maybe | not read; C4 calls it "a hub for all proof automation" |
| 35 | Zhou et al., Mariposa, FMCAD 2023 | maybe | not found on arXiv; not read |
| 36 | Dafny, avoiding verification brittleness (blog 2023), `hide` (4.8) | maybe | not read |
| 37 | Blot et al., Sniper / compositional pre-processing, CPP 2023 | maybe | not read |
| 38 | Chamelean / Specimen (Plausible generators for relations) | maybe | the GitHub checkpoint holds only Plausible's README; no paper found |
| 39 | Prinz, Lampropoulos, Merging Inductive Relations, PLDI 2023 | maybe | downloaded, not read; cited by C11 |
| 40 | Etna, an evaluation platform for PBT, arXiv 2603.27002 | maybe | title only; used by C12, C14 |
| 41 | Sivaraman et al., lfind, OOPSLA 2022 | maybe | not read |
| 42 | Lemmanaid (2025); QuickSpec for Vampire induction, IJCAR 2024 | maybe | not read |
| 43 | Shi et al., QED in Context, OOPSLA 2025 | maybe | not read |
| 44 | Liquid Haskell PLEX, OOPSLA 2026 | maybe | not read |
| 45 | Lean `mvcgen` / `vcgen` | maybe | effects cluster |
| 46 | Lean Copilot, PMLR 2025 | maybe | LLM in the loop; not read |
| 47 | ProofRepairBench, ICLR 2026 | maybe | not read |
| 48 | Norman, Avigad, Canonical (ITP 2025; arXiv 2603.01463) | maybe | elaboration.md C13 read the arXiv version |
| 49 | Lean `decide`, `decide +kernel`, `native_decide`, Mathlib `Fintype` | drop | decide.md read the sources (its L1-L6, M1-M2) |
| 50 | Lean simprocs | drop | Stitchwort computes anyway |
| 51 | Lean `partial_fixpoint` | drop | `{Partial}` is a different design |
| 52 | Mathlib `linarith`, `polyrith`, `linear_combination` | drop | omega.md §4 and `ring [h]` cover them |
| 53 | Rocq `lia`, `zify`, Mczify | drop | omega.md §4 covers them; C24 is the in-window piece |
| 54 | Cohen, Crance, Mahboubi, Trocq, ESOP 2024 | drop | proof transfer; no matching friction |
| 55 | Agda 2.7 Mimer; agda-stdlib reflective solvers | drop | hole filling; already in proposals/proof-automation.md |
| 56 | Coq-Elpi tactics | drop | no tactic language (DESIGN §6) |
| 57 | Nitpick, Isabelle Quickcheck, Nunchaku, **classic** | drop | no in-window work found |
| 58 | CoqHammer (JAR 2018), SMTCoq, **classic** | drop | seen only through C17's and C20's comparisons |
| 59 | Isabelle veriT reconstruction (2019), **classic** | drop | superseded by C17, C21 |
| 60 | Mladenov, Keles, Lampropoulos, QuickerChick, arXiv 2609.16079 | drop | extraction speed; we run in-process |
| 61 | Einarsdóttir, theory exploration thesis, 2025 | drop | covered by row 42 |
| 62 | Ringer, Proof Repair, PhD 2021, **classic** | drop | library evolution |
| 63 | Graph2Tac (2024) | drop | tactic prediction; we have no tactics |
| 64 | VERINA, CLEVER, miniCodeProps | drop | benchmarks (out of scope per the brief) |
| 65 | DeepSeek-Prover-V2, Seed-Prover | drop | benchmarks |
| 66 | Verus, SOSP 2024 | drop | proof-to-code ratios; not automation design |
| 67 | Kissas, Rózsa: Certified Equational Reasoning, arXiv 2610.26467 | drop | magma-law challenge; abstract and §1 only |
| 68 | Nazrin, arXiv 2602.18767 | drop | neural tactic |
| 69 | Symbolic Search Is Not Exhausted, arXiv 2610.04275 | drop | title only |
| 70 | FVSpec, arXiv 2606.01008 | drop | benchmark |
| 71 | Planning to Hammer (Rocq), arXiv 2606.17981 | drop | LLM decomposition |
| 72 | Verified orthologic proof search, arXiv 2501.09418 | drop | orthologic; title only |

## 4. Cards

Cost scale: **small** (a local change in `crates/elab`, `crates/driver` or `std`),
**elaborator** (a design change in `crates/elab`, no kernel change), **kernel**, **research**.
Every proposal here keeps the kernel as it is.

**C1. Selsam, de Moura, Congruence Closure in Intensional Type Theory** (IJCAR 2016, arXiv
1701.04391v2, **classic**: `grind`'s congruence closure follows its scheme, C3).

*Claim:* the ideal heterogeneous congruence lemma "is not provable in ITT, even when we assume
UIP" (§3). The family `hcongr_n` is provable for each `n` from `erec`, `ofheq` and `hrefl`.
`ofheq` (from `a == b` to `a = b`) "is equivalent to the uniqueness of identity proofs (UIP)
principle … to Streicher's Axiom K" (§2.1). The procedure follows Nieuwenhuis and Oliveras:
- union-find with `repr`, `next`, `size`;
- "proof forests" (`pr`), and a congruence table with use-lists;
- two applications `f a` and `g b` are congruent if `a ≈ b` and either `f ≈ g` at the same
  type, or `f` and `g` are themselves congruent (Proposition 1).

A proof of `a == b` is built on demand: find the common element on the two paths to the root
and chain `htrans`/`hsymm` (Figure 5, `mkpr`). Extensions (§4, end): disequalities,
"injectivity and disjointness for inductive datatype constructors", and *subsingletons*. When
two subsingleton types are merged, their representative elements are merged too. That proves
`safe_log a Ha = safe_log b Hb` from `a = b` **[checked]**.

*Steal:* the whole algorithm, including the subsingleton rule for proof arguments. Stitchwort
has K (docs/core.md:121, :142). `Bool.uniqueEq` (`std/core/Decidable.sw:137`) and
`DecEq.uniqueEq` (`std/core/DecEq.sw:64`) are exactly the subsingleton lemmas for proofs of
`Nat.leq a b = True` and of equations in `DecEq` types **[checked; that they suffice is
inferred]**. *Helps:* SW-608 (1), (2), (5); §5.1. *Cost:* elaborator. *Full text:* read (§1-§4
in full including Figure 5; §5 applications; §6 related work; proofs of the theorems not read).

**C2. Lean reference manual, *The `grind` tactic*** (lean-lang.org/doc/reference/latest, §16;
4.36.0-rc2).

*Claim:* "all proofs are by contradiction". A "shared whiteboard" of facts serves cooperating
engines (congruence closure, constraint propagation, E-matching, guided case analysis, satellite
solvers), and `grind` "produces ordinary Lean proof terms for every fact it adds" (§16). The
engines:
- *Congruence closure* (§16.4). Two different constructors in a class close the goal. "No term
  is rewritten; instead, both representatives live in the same class."
- *Propagation* (§16.5) fires forward rules on the `True`/`False` buckets: connectives, "If two
  terms formed by applications of the same constructor are placed in the same equivalence
  class, then their arguments are also made equal", projections, casts, `(a, b).1 = a`. Its
  examples close `(a && !a) = false` and `if c then t else e = t` from `c = true` "purely by
  constraint propagation — no case splits".
- *Case analysis* (§16.6) "is not exhaustive". Candidates come from `splitIte`, `splitMatch`
  (default true), `splitImp` (default false, except arithmetic antecedents) and `grind cases`
  annotations. `splits := n` caps the depth per branch.
- *E-matching* (§16.7). An instance's generation is "one greater than the maximal generation of
  all the terms used to instantiate the theorem", bounded by `gen < n` and `max_insts < n`.
  "Certain combinations of theorems can lead to unbounded instantiation."
- *Linear integer arithmetic* (§16.9) is "model-based", "complete for linear integer
  arithmetic", with `+qlia` accepting rational solutions. It prints an "Assignment satisfying
  linear constraints" on failure.
- On failure, `grind` "prints the remaining subgoal followed by all the information returned by
  its subsystems" (§16.1). `grind?` "records the theorems used by `grind` and suggests a
  suitable `grind only`" (§16.2).

It is "not designed for goals whose search space explodes combinatorially … use `bv_decide`"
(§16) **[checked]**.

*Steal:* propagation before splitting; the failure report (classes, true and false facts, an
arithmetic model); the write-back form. *Helps:* §5.1, §5.4. *Cost:* elaborator. *Full text:*
read (§16 index, §16.1-§16.7, §16.9, §16.12 pattern modifiers, §16.14; §16.8, §16.10, §16.11,
§16.13, §16.15, §16.16 not read or skimmed).

**C3. Lean 4 `grind` source** (`src/Lean/Meta/Tactic/Grind/` at `0f852cc8`).

*Claim:*
- Proofs come from a proof forest on demand. `findCommon` "find[s] the common expression that
  are in the paths from `lhs` and `rhs` to the root of their equivalence class"
  (`Proof.lean:65-89`). `mkEqProofImpl` "assumes `a` and `b` are in the same equivalence class"
  (`:332-342`). That is C1's `mkpr`.
- Local `∀` facts get singleton patterns: "We use this function to implement local forall
  expressions in a `grind` goal" (`EMatchTheorem.lean:1302-1306`). Local theorems use
  `groundPatterns := false` (`:1330-1333`).
- A hypothesis `A → B` becomes a split candidate when `splitImp` is on, when `A` is arithmetic,
  or when `A` is itself a `∀` proposition, because "`grind` has few propagation rules for
  assigning `True` to a universal quantifier" (`Internalize.lean:156-170`).

**[checked]**

*Steal:* both the proof construction and the treatment of local `∀` facts for T1's stage 2.
*Cost:* elaborator. *Full text:* read (the module docs and the functions named; the rest of
the three files skimmed).

**C4. de Moura, *The grind Tactic: proof automation in Lean*** (slides, 18 Sep 2025,
leodemoura.github.io/files/grind.pdf; 8 pages with a text layer).

*Claim:*
- "Native to Dependent Type Theory: No translation to first-order or higher-order logic
  needed", "Fast startup time", "Rich diagnostics: When it fails, it tells you why".
- The architecture: preprocessing, internalisation, e-graph, satellite solvers. Rings use
  "Grobner basis". "cutsat (superseding omega, with model construction)" appears in the 4.22
  notes, not the slides.
- The roadmap: "An un-grind tool that expands a grind proof into a detailed tactic proof", and
  "Maintaining formal proofs is as hard as writing them in the first place".

**[checked]**

*Steal:* the design principles, which match Stitchwort's (no external process, explain
failure). *Cost:* none. *Full text:* read (all slides; some pages are pictures of code, which
weren't read).

**C5. Flatt, Coward, Willsey, Tatlock, Panchekha, Small Proofs from Congruence Closure**
(FMCAD 2022, arXiv 2209.03398).

*Claim:* minimal proofs are NP-complete. An `O(n^5)` algorithm is optimal for "proof tree
size", and a greedy `O(n log n)` one has "no asymptotic overhead". The greedy one does a
breadth-first shortest path with estimated congruence-edge costs, and expands `T = 10`
congruence edges (§V.A). Keeping every merge edge (a "c-graph", not a spanning tree) allows
shorter proofs (§III.A). In egg, its proofs are "only 72.8% as big as Z3's on average". It cut
an Intel RTL case study's proof replay "from 4.7 hours down to 2.3 hours" (§I) **[checked]**.

*Steal:* only if proofs grow large. The classes at one `cases` node are small **[inferred]**, so
the plain forest proof (C1) is enough first. *Cost:* small. *Full text:* read (§I, §II, §III.A,
§V.A; §IV and §VI skimmed).

**C6. Wang, Chess, Szeto, Meek, Learned Interventions Inside Lean 4's grind** (arXiv
2607.22972v2, ICML 2026).

*Claim:* `grind`'s search is "non-monotone": "a learned heuristic that helps one proof can break
another". So the learned step runs only after stock `grind` fails, "a failure-triggered cascade
that, by construction, cannot lose a proof grind already had". Two results:
- "statically predicting the correct case split is no better than random, because whether a
  split explodes is a runtime property". On the rescuable split failures, stock gets 0%, the
  models 30-53%, uniform random 57% and 1-step lookahead 100% (Table 1).
- Lookahead "makes a throwaway copy of the goal, forces that split, and runs grind on the copy
  for a bounded number of steps", then commits to the first that closes (§5).

**[checked]**

*Steal:* for `cases`, a fallback when `E-CASES-BUDGET` or `E-CASES` would be reported: try other
atoms with a small budget. It can't lose a proof that passes today **[inferred]**. *Helps:*
SW-608 (3); decide.md D1971's "split the latest variable" rule. *Cost:* small. *Full text:*
read (abstract, §1, §4 split study, §5; the e-match filter section skimmed).

**C7. Lean 4 `omega`** (`Init/Tactics.lean:1543-1573`, `Elab/Tactic/Omega/Frontend.lean`,
`Omega/Core.lean` at `0f852cc8`).

*Claim:*
- "It is not yet a full decision procedure (no "dark" or "grey" shadows)". It handles
  `x = y`, `x < y`, `x ≤ y` and `k ∣ x` and their negations. It introduces atoms for `x / k` and
  `x % k`, and case-splits natural subtraction only "if `omega` fails".
- `+splitDisjunctions`, `+splitNatSub`, `+splitNatAbs` and `+splitMinMax` "are on by default".
- The proof is built from `Justification` trees ("a delayed proof", `Core.lean:34-60`), not by
  a reflective checker.
- grind's cutsat supersedes it (C2, C4).

**[checked]**

*Steal:* nothing new. omega.md §4 already compares these, and Stitchwort chose a reflective
checker (`omega.rs:10-22`). Divisibility facts `k ∣ x` are the one input form Lean reads that
`omega`'s fact list in docs/syntax.md (`:1600`) doesn't mention **[checked]**. *Cost:* small, if
ever needed. *Full text:* read (the docstring, `Frontend.lean`'s doc comments, `Core.lean:1-90`).

**C8. Lean 4 functional induction and `fun_cases`** (`src/Lean/Meta/Tactic/FunInd.lean` at
`0f852cc8`, Breitner).

*Claim:* from a recursive definition, "a functional induction principle tailored to proofs
about that function". "For each branch of the original function, there is a case." "For every
recursive call in that branch, an induction hypothesis". "The local context of the branch
(e.g. the condition of an if-then-else; a let-binding …) is provided as assumptions". For a
`match`, "the matcher is replaced by its splitter", and "for discriminants that are not
instantiated that way, equalities connecting the discriminant to the instantiation are added
(just as if the user wrote `match h : x with …`)". `fun_cases_unfolding`'s motive "abstracts
over the function call", so each case is stated at the branch's body. All of these are
*reserved names*, derived on first use (`registerReservedNameAction`, `:1546-1566`).
`fun_cases` needs only a safe definition, so it exists for non-recursive functions too
(`isFunCasesName`, `:1536-1544`) **[checked]**.

*Steal:* `f.cases` and `f.casesUnfolding` from Stitchwort's case trees, on demand (§5.3).
*Helps:* SW-802, SW-809, days 12, 16 and 23. *Cost:* elaborator. *Full text:* read (module
documentation `:1-200`, the reserved-name registration `:1500-1568`; the construction code
skimmed).

**C9. Lean 4 `GuessLex`** (`src/Lean/Elab/PreDefinition/WF/GuessLex.lean`, Breitner).

*Claim:* when no `termination_by` is given, Lean tries measures `sizeOf xᵢ`, and "`e₂ - e₁` if
`e₁ < e₂` is found in the context of a recursive call", in lexicographic combinations. It
fills a table of `<`/`≤` per call and measure lazily, and checks `=` first because it is
cheaper. The result "could also be written manually by the user" (Bulwahn, Krauss, Nipkow,
TPHOLs 2007) **[checked]**.

*Steal:* later, a suggested `decreasing m` when a recursive definition fails termination. It
would print the measure, never apply it silently. Stitchwort's measure is always written today
(`decreasing.rs:1-33`). *Helps:* SW-199. *Cost:* small to elaborator. *Full text:* read (module
documentation `:12-58`).

**C10. Plausible** (github.com/leanprover-community/plausible at `129d1ba9`: README,
`Tactic.lean`, `Testable.lean`).

*Claim:*
- Custom types need `Shrinkable` and `SampleableExt` or `deriving Arbitrary`.
- Preconditions are guards: an input that fails one is discarded, retried up to `numRetries`
  (default 10), with `numInst` 100 tests by default (`Testable.lean:112-117`). The run gives up
  with "Gave up after failing to generate values that fulfill the preconditions {n} times"
  (`:613`).
- "If no counter-examples are found, `plausible` behaves like `admit`" (`Tactic.lean:84`).

**[checked]**

*Steal:* nothing new. Stitchwort's filtering is the same, and never closes a goal
(docs/syntax.md:1251). *Cost:* none. *Full text:* read (README; `Tactic.lean` doc comments and
config; `Testable.lean` config and `runSuite`).

**C11. Goldstein, Peleg, Torczon, Sainati, Lampropoulos, Pierce, The Search for Constrained
Random Generators** (PACMPL 10 PLDI Art. 251, 2026; arXiv 2511.12253v2).

*Claim:* the "constrained generator synthesis problem": build, offline, a generator whose
support is exactly the values satisfying a predicate written as a Lean *function*. The
generator then "does no searching at all". Deductive synthesis rules come from a denotational
semantics of generators. "Recursive predicates [are rewritten] as catamorphisms and then
match[ed] with appropriate anamorphisms." Palamedes runs on Aesop, and Lean checks the
correctness proof. The guarantee is "the correct support … but not necessarily optimal
distributions". On 32 benchmarks:
- synthesis takes "around 40ms to 50s"; "80% … in under 3 seconds";
- it fails on `isUnique` and `hasDuplicates`.

QuickChick "works more like a compiler" and is near-instant, but needs predicates as inductive
relations (§6.1-§6.2) **[checked]**.

*Steal:* the idea that a `Bool` predicate defined by structural recursion can be run backwards
into a generator. Stitchwort's hypotheses are exactly such `Bool` functions, decided at run
time (`counterexample/mod.rs:11-19`). Stitchwort needs no correctness proof, because the
search is advisory and re-checks any counterexample on the reference evaluator
(`mod.rs:24-28`) **[inferred]**. *Helps:* §5.2. *Cost:* research. *Full text:* read (abstract,
§1, §6.1-§6.3; §2-§5 skimmed, §7-§9 not read).

**C12. Mittelman, Goldstein, Lampropoulos, Testing Theorems, Fully Automatically** (PACMPL 10
OOPSLA2 Art. 321, 2026; author PDF).

*Claim:* QuickChick's effectiveness "is heavily sensitive to both the order that hypotheses
appear within a theorem, and to the order that inductive constraints appear". The paper treats
choosing generators as "a constrained scheduling problem". It ranks each step's *density*:
`Checking | Backtracking | Partial | Total`, from worst to best, and "the overall effectiveness
of a schedule is simply the worst density of any of its steps" (§3). On ETNA's BST workload it
finds all 52 mutant-theorem counterexamples "in under a tenth of a second, on par with" bespoke
and QuickChick-derived generators (§6) **[checked]**.

*Steal:* with several hypotheses, generate from the one whose generator is best and check the
rest. It is a cheap ordering rule even before full generators exist (§5.2). *Cost:* research.
*Full text:* read (abstract, §1, §3 density and schedules, §6 ETNA part; §4-§5 skimmed, the
Cedar case study skimmed).

**C13. Paraskevopoulou, Eline, Lampropoulos, Computing Correctly with Inductive Relations**
(PLDI 2022; author PDF).

*Claim:* one algorithm derives checkers, enumerators and random generators from an inductive
relation. Checkers are "semi-decision procedures" with "a standard size parameter as fuel" and
output type `option bool`. "None signifies that it needs additional fuel." Generators and
enumerators are "producers". Each derived computation gets a mechanised soundness and
completeness proof by translation validation. The derived procedures are less than 2% slower
than handwritten ones in QuickChick's benchmarks (§1, §2) **[checked]**.

*Steal:* a way to bring propositional hypotheses (`List.Sorted` as a proposition, out of scope
today, docs/syntax.md:1255) into the counterexample search: a derived three-valued checker,
whose `None` maps to the existing "inconclusive" verdict (`driver/src/counterexample.rs:76-80`)
**[inferred]**. *Cost:* research. *Full text:* read (abstract, §1, §2; §3-§6 skimmed).

**C14. Keles, Miao, Lampropoulos, Evaluating Shrinking (Experience Report)** (Haskell 2026;
author PDF).

*Claim:* it compares QuickCheck, Hedgehog and Falsify on four ETNA workloads, measuring tree edit
distance to an exhaustively found minimum. "QuickCheck-style structural shrinking is usually
faster and often competitive in final counterexample quality". "Integrated shrinking does not
automatically dominate" (§6) **[checked]**.

*Steal:* nothing to change. Stitchwort's structural shrinker (numbers toward 0, list elements
removed, `inputs.rs:798-813`) is the kind found competitive, and enumeration first makes most
counterexamples smallest anyway (docs/syntax.md:1251). *Cost:* none. *Full text:* read
(abstract, §1 opening, §6 conclusion; the measurements skimmed).

**C15. Qian, Clune, Barrett, Avigad, Lean-auto** (CAV 2025, arXiv 2505.14929v2).

*Claim:* it translates Lean 4 to higher-order logic by monomorphisation (quantifier
instantiation, λ-abstraction, universe lifting), because encoding-based translation "tends to
produce much larger outputs". Proof reconstruction exists only "for native provers" (Duper).
Other ATPs are trusted with a warning. "Lean-auto + Duper … solves 36.6% problems in our
benchmark set, which is 5.0% better than the best previous tool" (§1, §8) **[checked]**.

*Steal:* nothing now (§5.4). *Cost:* research. *Full text:* read (abstract, §1, §8, conclusion;
§3-§7 skimmed).

**C16. Clune, Qian, Bentkamp, Avigad, Duper** (ITP 2024, LIPIcs 309:10).

*Claim:* a proof-producing superposition prover for Lean, a terminal tactic and the intended
reconstruction back end of a hammer. It extends higher-order unification to dependent types.
Its performance is "comparable to Metis'" (abstract, §1) **[checked]**.

*Steal:* nothing now. *Cost:* research. *Full text:* read (abstract, §1, §4.2 opening; the
calculus and evaluation sections skimmed).

**C17. Mohamed et al., lean-smt** (CAV 2025, arXiv 2505.15796).

*Claim:* cvc5's format "specifies over 662 proof rules". lean-smt "supports around 200 of
these", through 163 theorems, tactics (a library of about 400 theorems) and reflection
(5 rules) (§3). On SMT-LIB, "Out of the 21,595 benchmarks proofs generated by cvc5, lean-smt
successfully verified 15,271 proofs (71%)", against Ethos's 98% (§4.2). Over Sledgehammer
problems it replays 98% of its proofs in under a second (§4.1) **[checked]**.

*Steal:* the cost estimate. Proof replay is a large, ongoing library even for a third of one
solver's rules. *Cost:* research. *Full text:* read (abstract, §1, §3, §4, §5).

**C18. Clune, Barbosa, Avigad, Hint-Based SMT Proof Reconstruction** (arXiv 2601.14495).

*Claim:* `querysmt` neither replays cvc5's proof nor keeps only the unsat core. It extracts
*hints*, the theory facts cvc5 derived, and "insert[s], in the Lean source file, a
self-contained proof script". `grind` proves the hints and Duper the goal from them, so "the
proof does not depend on calling an SMT solver anymore". The motivation: SMT solvers "are
notoriously unstable", so the script "results in a more stable artifact". The final scripts
average 0.7-0.8 hints. On List problems `grind` "succeeds … for 1,458 problems", but only 439
in the original environment, because tagged lemmas leaked into the benchmark (§1, §8)
**[checked]**.

*Steal:* write the found proof back as source (§5.4). Also a warning about measuring automation
whose lemma set contains the answer. *Cost:* none. *Full text:* read (abstract, §1, §2
opening, §8, §9).

**C19. Zhu, Clune, Avigad, Jiang, Welleck, Premise Selection for a Lean Hammer** (ICLR 2026,
arXiv 2506.07477v2).

*Claim:* LeanHammer combines neural premise selection, Lean-auto, Zipperposition and Duper,
inside Aesop. With LeanPremise it "solve[s] 21% more goals than existing premise selectors",
33.3% to 37.3% of test theorems, and 43.0% with ground-truth premises (§1, §5) **[checked]**.

*Steal:* nothing. Stitchwort's automation reads only facts in scope, and its library is small.
*Cost:* research. *Full text:* read (abstract, §1, §3 pipeline, §5 results).

**C20. He, Zhang, Gupta, crush: Extensible Proof Automation for Lean** (arXiv 2610.40538v1,
29 Oct 2026).

*Claim:* an SMT back end with defunctionalisation for non-dependent higher-order functions, user
extensible translation and replay, unsat-core-guided reconstruction ("existing proof automation
tactics (e.g., omega or grind)") and Alethe replay. On 754 verification conditions, crush
closes 709 (94.0%) trusting the solver and 693 (91.9%) reconstructed. `grind` closes 641
(85.0%), "is faster on all four suites", and proves 9 that crush can't. Future work: "support
dependent function types" (§1, §5, §6, §8) **[checked]**.

*Steal:* nothing now. It quantifies the gap a hammer closes over a native `grind`: about 7
points, at a solver dependency **[inferred]**. *Cost:* research. *Full text:* read (abstract,
§1, §5, §6.1-§6.2, §7, §8; §3-§4 skimmed).

**C21. Bartl, Blanchette, Nipkow, Exploiting Instantiations from Paramodulation Proofs in
Isabelle/HOL** (CADE-30, arXiv 2508.20738).

*Claim:* analysing Metis proofs yields variable instantiations, which Sledgehammer then writes
into the suggested one-liner. In run 2, "In 2 349 cases (70.0%), Sledgehammer suggested a
one-line proof with instantiated facts". In run 1, 44 more ATP proofs (1.3%) were rebuilt as
one-liners, "18.0% of cases where there was no one-line proof before". Metis time "decreased
by 84 ms (−38.0%)" (§6) **[checked]**.

*Steal:* when a search succeeds, show the instances it used, not only that it worked (§5.4).
*Cost:* small. *Full text:* read (abstract, §1, §6, §7 opening).

**C22. Gross, Erbsen, Philipoom, Agrawal, Chlipala, Accelerating Verified-Compiler Development
with a Verified Rewriting Engine** (ITP 2022, arXiv 2205.00862v4).

*Claim:* proved rewrite rules are compiled into a reflective, proven-correct rewriter.
"All existing proof-producing rewriting strategies scale at least quadratically in the number
of binders" (§1). Coq's `setoid_rewrite` "can still be cubic in the number of binders" even
with no match. Proof terms are "quadratic in the number of binders" (Appendix A.1-A.2). On
Fiat Cryptography the result is "about 10×–1000× speed-up", and the extracted engine is about
10× faster than in the kernel (§5.3) **[checked]**.

*Steal:* if `simp [rules]` (deferred, D1168) is built and has to rewrite large terms with many
`let`s, a reflective rewriter is the scalable form. *Cost:* research. *Full text:* read
(abstract, §1, §5.2-§5.3, Appendix A.1-A.2).

**C23. Rossel, Goens, Bridging Syntax and Semantics of Lean Expressions in E-Graphs** (arXiv
2405.10188, 2024), with the lean-egg README (fetched 30 Oct).

*Claim:* the paper puts Lean terms directly into egg with de Bruijn indices. That needs dynamic
rewrites for shifting, for β and η, against "Free Variable Rebinding", "Invalid Matching" and
"Bound Variable Aliasing". Proofs are erased to one constant (an over-approximation of proof
irrelevance), and the lean-egg authors are "unsure if there are cases where erased proof terms
cannot be completely reconstructed". The techniques are "partially unsound", and the result
stays sound "by virtue of Lean's proof checking". The README: "The `egg` tactic is no longer
being developed! We recommend you use Lean's `grind` tactic instead" **[checked]**.

*Steal:* nothing. It confirms that binders and definitional equality are the hard part of
e-graph *rewriting* in dependent types. A closer over the ground facts at one `cases` node
avoids them (§5.1) **[inferred]**. *Cost:* research. *Full text:* read (all six pages; README).

**C24. Sakaguchi, Reflexive tactics for algebra, revisited** (ITP 2022, arXiv 2202.04330).

*Claim:* the paper adapts Coq's reflective `ring`/`field` to MathComp. Reification recognises
operators "purely syntactically and do[es] not take conversion into account", which the paper
fixes with "keyed matching". It adds a preprocessing pass that "pushes down homomorphisms …
using the structure preservation laws, e.g., f (x + y) = f (x) + f (y)" (§1) **[checked]**.

*Steal:* nothing new. Stitchwort's `ring` reads values after computing, and already pushes
`Nat.toInt` through `+` and `*` (docs/syntax.md:1635: "`(x + y).toInt` is
`x.toInt + y.toInt`"). *Cost:* none. *Full text:* read (abstract, §1; §2-§4 skimmed).

**C25. Ospanov, Farnia, Yousefzadeh, APOLLO** (arXiv 2505.05758v5, NeurIPS 2025).

*Claim:* the loop around the model matters:
- a "Sorrifier" replaces each failing block with `sorry` until the file compiles;
- an "Auto Solver" tries built-in tactics on each `sorry`;
- only what remains goes back to the LLM, recursively.

Reported results: 84.9% on miniF2F among sub-8B models, with a sampling budget below one
hundred (abstract, §3.3-§3.5) **[checked]**.

*Steal:* Stitchwort's `?` already works as the `sorry` there: checking continues past it and
reports each goal (docs/syntax.md:1205-1232). A "try each automation word at each `?`" mode is
the Auto Solver (T5's second part). *Cost:* small. *Full text:* read (abstract, §1, §3).

**C26. Morrison, de Moura, grind: an SMT-inspired tactic for Lean 4** (IJCAR 2026, LNCS,
pp. 106-114; cited as [22] in C20). **NOT READ**: no public copy found (S1, S6; the arXiv API
has no record). C2-C4 cover the same system from its manual, its source and its author's
slides.

**C27. Rossel, Schneider, Koehler, Steuwer, Goens, Towards Pen-and-Paper-Style Equational
Reasoning in Interactive Theorem Provers by Equality Saturation** (POPL 2026,
doi 10.1145/3776667). **NOT READ**: ACM 403; Internet Archive `2025id_` and `2026id_` 404;
Semantic Scholar lists GOLD open access at the DOI, which redirects to ACM. Its own README now
points users to `grind` (C23), so it is not for Matt.

**C28. Bhat, Böving et al., Interactive Bitvector Reasoning using Verified Bit-Blasting**
(OOPSLA 2025, doi 10.1145/3763167). **NOT READ**: ACM 403; Internet Archive 404; the
theory.stanford.edu page refused the connection. decide.md already cites Lean's own docstring
on `bv_decide`'s trust. Stitchwort has no bit vectors yet, so it is not for Matt.

**C29. Limperg, From, Aesop: White-Box Best-First Proof Search for Lean** (CPP 2023,
doi 10.1145/3573105.3575671). **NOT READ**: ACM 403; Internet Archive 403. Stitchwort has no
tactic language to search over, so it is not for Matt.

## 5. Deep reads

### 5.1 A congruence-closure closer for `cases` (C1, C2, C3, C5, C6)

**What the sources say** [checked]. Congruence closure over the equations in scope, with a proof
forest, decides ground equality (C1 §4, C3 `Proof.lean:65-89`). It needs three things in
dependent type theory:
- per-arity congruence lemmas;
- UIP, to turn heterogeneous equalities back into homogeneous ones;
- for proof arguments, merging representatives of subsingleton types (C1 §4).

`grind` adds constructor clash and injectivity as propagators (C2 §16.5). It instantiates local
`∀` facts with singleton patterns (C3), bounded by generation (C2 §16.7). It splits only
candidates it has collected, to a depth bound (C2 §16.6). Choosing what to split by static
features is no better than random, and lookahead is better (C6).

**Stitchwort today** [checked; run].
- `cases`' closers (`node`, `crates/elab/src/cases.rs:212-272`), in order:
  1. computation;
  2. a hypothesis equating two constructors, both sides computed;
  3. injectivity;
  4. a hypothesis convertible with the goal (`by_hypothesis`, `:393-415`);
  5. `t`;
  6. `omega`.

  Splitting covers data that isn't recursive. At most 64 cases (`CASES`, `:62`).
- No closer combines equations. The probes (`sw894probe/probe.sw`, release CLI):
  - `(xs: List Nat) (h1: xs = Cons 1 Nil) (h2: xs = Nil): Void := cases` is `E-CASES`: "found
    nothing to split on, and nothing closes the goal". `List` is recursive, so it isn't split,
    and neither hypothesis has constructors on both sides.
  - `(f: Nat → Nat) … (h1: a = b) (h2: f b = c): f a = c := cases` is `E-CASES` too.
  - `(h: (y: Nat) → lookup = Some y → y < 5) (h2: lookup = Some y0): y0 < 5 := cases` fails in
    the case `(y0 <= 4) = False`. `omega` ignores quantified facts (docs/syntax.md:1600, "used
    by applying it").
  - `(h1: a = b) (h2: b = c): a = c := cases` checks. `omega` proves it, as `Nat` arithmetic.
- Axiom K holds (docs/core.md:121, :142). `Bool.uniqueEq` and `DecEq.uniqueEq` are in std.

**Mapping.**
1. *Stage 1, ground classes.* At each node, after `take_apart` and before `by_hypothesis`, build
   classes from:
   - hypotheses whose type is an equation, including the `%caseN` split equations;
   - the goal's sides.

   Close the goal `a = b` when the sides meet. Close any goal when two different constructors
   meet. Add the argument equations when two applications of the same constructor meet, as
   `grind`'s propagator does. That would close probes 1 and 2 **[inferred]**. The proof comes
   from the forest:
   - `Eq.trans` and `Eq.sym` along each path;
   - a congruence step by `J` per argument (Stitchwort's `Eq.cong` route; the elaborator
     already writes `J` terms in `take_apart`);
   - a constructor clash by the existing `contradiction` (`cases.rs:479`).
2. *Proof arguments.* When two calls differ only in an argument whose type is an equation
   (`Nat.leq a b = True`, or `x = y` in a `DecEq` type), equate those arguments by
   `Bool.uniqueEq` or `DecEq.uniqueEq`. That is C1's subsingleton rule, using lemmas we already
   have **[inferred]**. Other proof arguments are left alone, and congruence through them
   isn't attempted. This narrows the old version's main risk (proof irrelevance unbuilt,
   SW-93).
3. *Stage 2, local `∀` facts.* A hypothesis `(y…) → P… → l = r` (or `→ C …`, or `→ a < b`)
   becomes a pattern over its premises. Match it against the classes, instantiate once
   (generation 1), and add the conclusion as a fact. Arithmetic conclusions go on to `omega`.
   It never uses library lemmas, only what is in scope, so nothing changes when std grows. This
   is SW-608 (2) and probe 3 **[inferred]**.
4. *Propagation before splitting.* `&&`, `||`, `not` and `if` on a known `Bool` atom (C2 §16.5)
   is cheaper than a split. Today `cases` splits such an atom. Whether this saves cases on the
   AoC proofs is unmeasured.

**Bearing on decide.md.**
- D1971's two additions (a decision closer at the leaves, and a last-resort split of a finite
  variable) are independent of this closer, and compatible with it **[inferred]**.
- `grind`'s own case analysis is also bounded and "not exhaustive" (C2 §16.6). Its authors
  route combinatorial goals to `bv_decide`, as decide.md routes past-64 statements to
  `Finite.check` (decide.md §6.1). That supports D1971's "the budget is not the knob".
- C6 adds an option D1971 doesn't consider. When the last-resort split runs out of budget, try
  the other candidate atoms with a small budget before reporting. It can only turn a failure
  into a success **[inferred from C6's "cannot lose a proof"]**.
- Nothing read bears on D1972 or D1973.

**Assumptions the recommendation depends on.**
- (A1) Comparing terms in the classes by their computed form, as `cases` already compares atoms,
  is enough for the target proofs. Full conversion inside the closure is not needed. Not
  measured.
- (A2) The classes at one node are small (tens of terms), so rebuilding them per node is cheap.
  Not measured.
- (A3) `J`-based congruence steps type-check for the dependent calls that matter, given
  `uniqueEq` for equation-typed proof arguments. To be checked in the note on one `x % d`
  example with two proofs of `d != 0`.

**Risks.**
- Proof size on long chains. Use C5's greedy path only if measured.
- A closer that runs on every node adds time to every `cases` failure path, which matters for
  the 64-case budget (decide.md §2: 64 cases cost 11.7 ms).
- Stage 2 is where `grind` warns of unbounded instantiation (C2 §16.7). Generation 1 only, and
  report what was instantiated (§5.4).

**Next step.** T1, a design note, with probes 1-3 and SW-608's items as acceptance cases.
Decision D2000.

### 5.2 Counterexamples when the hypothesis is rarely satisfied by large inputs (C11, C12, C13, C10, C14)

**What the sources say** [checked]. Filtering by hypotheses is the common start: Plausible's
guards (C10) and QuickChick's `==>`. For sparse preconditions there are three routes:
- generators built from the predicate. Palamedes synthesises them from Lean `Bool` functions
  through catamorphisms and anamorphisms, and the result "does no searching at all" (C11);
- QuickChick's derived generators for inductive relations, whose effectiveness depends on
  hypothesis order, which "density" now chooses automatically (C12);
- derived checkers for propositions, three-valued with fuel (C13).

Structural shrinking is competitive (C14).

**Stitchwort today** [checked; run].
- Hypotheses are filters (docs/syntax.md:1254; `counterexample/mod.rs:11-19`).
- The verdict is "gave up" only when hypotheses hold in under 10% of the inputs tried
  (`crates/driver/src/counterexample.rs:82`). Otherwise it is "none in N cases"
  (`:94-99`).
- Random lists share their size among their elements (`inputs.rs:744-757`, SW-900), so long
  random lists have small, often equal, elements.
- The probe `sw894probe/sparse.sw`:
  - `theorem shortIncreasing (xs: List Nat) (h: increasing xs = True): xs.length < 6` is false
    (`[0, 1, 2, 3, 4, 5]`). `check --counterexamples --verbose` prints `~ shortIncreasing  none
    in 10000 cases (sizes up to 40; evidence, not a proof)`.
  - The same conclusion with `h: xs.length < 100` gets `✗ … counterexample: xs = [0, 0, 0, 0,
    0, 0]`.

  So the search misses it without saying so. Many inputs satisfy the hypothesis (short lists
  are increasing), but none large enough to falsify the conclusion **[run; the cause is
  inferred]**.
- counterexample-search.md's trigger for hypothesis-directed generators is "if 'gave up' turns
  out common" (`:566-570`). This probe never gives up, so that trigger wouldn't fire.

**Mapping.**
1. *Measure first.* Record, per theorem, the largest total size among inputs whose hypotheses
   all held, next to the largest size tried. In `--verbose`, say "hypotheses held only up to
   size k" when k is much smaller than the size reached. Then run `check --counterexamples` over
   std and aoc and count such theorems. SW-687 (mutating proven theorems, with the search as
   oracle) gives a ready corpus of false statements whose answers are known **[inferred]**.
2. *Order hypotheses* by how often each holds on small inputs. Check the most selective first,
   so discards are cheap. That is C12's density in its simplest form **[inferred]**.
3. *Generate from a structurally recursive `Bool` hypothesis.* For `p: T → Bool` defined by a
   case tree, generate a `T` by choosing, at each node, only constructors whose branch can still
   return `True`, recursing where the branch recurses. That is C11's anamorphism idea, done in
   Rust over the case tree with no proof, because the result is re-checked anyway
   (`mod.rs:24-28`). It covers `increasing`, `isBST`-style predicates and bounds.
4. *Propositional hypotheses* (out of scope today, docs/syntax.md:1255) through a derived
   fuel-bounded checker (C13), mapping "needs more fuel" to "inconclusive".

**Assumptions.**
- (G1) Theorems whose hypotheses are satisfied only by small inputs occur in std or aoc.
  Unmeasured; T2 measures it.
- (G2) A generator that satisfies one hypothesis need not be uniform to be useful. C11 makes the
  same choice: "correct support … but not necessarily optimal distributions".

**Risks.**
- Generation from predicates can loop or blow up on predicates that aren't structural. Restrict
  it to case trees with structural recursion, and keep the filter as the fallback.
- A new phase spends the 200 ms on-failure budget (`mod.rs`, `TIME_LIMIT_MS`). Run it only when
  the measure in (1) says the filter isn't reaching large inputs.

**Next step.** T2 (measure and report, small), then T3 (design note), only if T2 finds such
theorems.

### 5.3 Case theorems generated from a definition (C8)

**What the source says** [checked]. `f.fun_cases` has one case per branch of `f`'s `if`s and
`match`es. The branch's conditions and `let`s are hypotheses. Each discriminant that isn't a
plain parameter gets "equalities connecting the discriminant to the instantiation … (just as if
the user wrote `match h : x with …`)". `f.induct` adds a hypothesis per recursive call.
`fun_cases_unfolding` states each case at the branch's body by abstracting over the call.
Everything is derived on first use under a reserved name, for any safe definition (C8).

**Stitchwort today** [checked].
- equation-lemmas.md built `f.unfold` and named local definitions, and deferred Lean-style
  per-leaf lemmas (D231-D233). In Stitchwort each per-leaf lemma "is `rfl` (§2.3), so it adds
  no power, only a name" (equation-lemmas.md:606-611).
- `decreasing` definitions get `f.unfold` (`decreasing.rs:25`) but no induction principle
  (SW-199 lists `f.induct` as a remaining stage-3 item).
- Nested types get a generated `T.induct` (`derive_induct.rs:5-13`).
- A `match found:` inside a definition can't be stepped through by `rewrite` or `match`
  (`E-MATCH-MOTIVE`, `lift.rs:831`, `:1256`; SW-802, SW-809).

**Mapping.** The difference from per-leaf equations is the *hypotheses*. A theorem `f.cases`
whose branch for leaf i takes the tested equations as arguments (`found: queue.min = Some m`,
the tested `Bool`s) gives the proof the facts that a `match found:` or a `cases` split would.
And it is proved once inside `f`'s own scope, where that equation's proof is in hand
**[inferred]**. Applying it needs the motive abstracted from the goal, as `rewrite` and `match`
already do. On-demand generation fits content hashing: the theorem's type mentions `f` by hash,
as equation-lemmas.md §7 argues for `f.eq_N`.

**Assumptions.**
- (F1) The elaborated case tree records which equation each leaf tested, readably enough to
  state the branches. equation-lemmas.md §2.1-2.2 suggests it does; not checked in
  `matching.rs`.
- (F2) Today's `cases` doesn't already prove the failing day 16 and day 23 statements. `cases`
  was built on 26 Oct, after some of those notes. **The note must check this first**; if
  `cases` already does, the theorem is only a convenience.

**Risks.** Large case trees give large theorems, so generate them only when used. The motive
problems of `rewrite` (`E-REWRITE-MOTIVE`) may reappear when applying `f.cases` to a goal with
proof arguments.

**Next step.** T4, a design note revisiting D231-D233 with days 12, 16 and 23 as acceptance
cases. Decision D2001.

### 5.4 Show what search found; no external solvers (C2, C18, C21, C20, C15-C17, C25)

**What the sources say** [checked].
- `grind?` suggests `grind only [...]` (C2 §16.2).
- Sledgehammer writes a one-liner with instantiated facts in 70% of cases, and the result runs
  38% faster (C21).
- querysmt writes a self-contained script so that "the proof does not depend on calling an SMT
  solver anymore", because SMT solvers are unstable (C18).
- `grind`'s roadmap asks for "an un-grind tool that expands a grind proof" (C4).

The external-solver route is costly:
- lean-smt covers about 200 of 662 cvc5 rules after a 400-theorem library (C17);
- Lean-auto reconstructs only through Duper (C15);
- crush beats native `grind` by about 7 points on its suites, at a solver dependency (C20).

**Stitchwort today** [checked]. Every search is internal and deterministic. Every proof is
re-checked by the kernel. On failure `E-CASES` names the case by its splits, and `E-OMEGA` gives
a model. On success nothing is shown. The `Run` struct already records the atoms split and how
each case was closed (`cases.rs:69-80`, `describe` at `:105`).

**Mapping.**
1. On success, an opt-in report: the split tree and each leaf's closer for `cases`; the facts the
   certificate used for `omega`. The LSP could offer it as an expansion to explicit `match`es
   (C21, C2 `grind?`).
2. At each `?`, an opt-in "try the automation words" pass (`rfl`, `cases`, `omega`) that reports
   which one closes it. That is APOLLO's Auto Solver (C25), useful to people and agents alike.
3. No SMT or ATP back end. The evidence (C15-C20) is about large lemma libraries and solver
   theories that Stitchwort's friction doesn't involve (§5.1's failures are about facts in
   scope).

**Assumptions.** (W1) The expanded form of a `cases` proof is readable for small trees. For
large ones the shape alone is shown.

**Next step.** T5.

## 6. Steal next

Ranked by value over effort. Every row rests on sources read in full.

| Rank | Idea | Source | Helps | Cost |
|---|---|---|---|---|
| 1 | Congruence-closure closer in `cases` (ground classes, constructor clash and injectivity, `uniqueEq` for equation-typed proof arguments) | C1, C2, C3 | SW-608 (1), (5); probes 1-2 | elaborator (design note first) |
| 2 | Report "hypotheses held only up to size k" in the counterexample search, and measure it over std and aoc | C11, C12; probe | silent misses (§5.2) | small |
| 3 | Local `∀` hypotheses instantiated once against the classes (stage 2 of 1) | C3, C2 | SW-608 (2); probe 3 | elaborator |
| 4 | Generated `f.cases` (then `f.induct`) from case trees, on demand | C8 | SW-802, SW-809; days 12, 16, 23 | elaborator (design note first) |
| 5 | Lookahead over alternative atoms before `E-CASES-BUDGET` | C6 | SW-608 (3); D1971 | small |
| 6 | Opt-in report of what `cases` and `omega` used; "try automation at each `?`" | C21, C2, C18, C25 | readability; agent loops | small |
| 7 | Hypothesis-directed inputs for structurally recursive `Bool` hypotheses; order hypotheses by selectivity | C11, C12 | counterexample search | research (only if rank 2 finds cases) |
| 8 | Propagation over `Bool` connectives before splitting | C2 | fewer cases per proof | small (measure first) |
| 9 | Suggest a `decreasing` measure on a termination failure | C9 | SW-199 | small to elaborator |
| 10 | Reflective rewriting, if `simp [rules]` is ever built for large terms | C22 | D1168 | research |

Not recommended now:
- SMT or ATP back ends (C15-C20): costly translation and reconstruction, gains measured on large
  libraries.
- E-graph rewriting under binders (C23, C27): its authors moved to `grind`.
- Bit-blasting (C28, NOT READ): no program needs bit vectors yet.

## 7. Proposed tickets

Label `research` on each. Not added to the board.

**T1. Design note: a congruence-closure closer for `cases`.** Decide:
- where it sits among the closers;
- how classes compare terms (computed, as atoms are);
- the proof term: forest paths as `Eq.trans` and `Eq.sym`, congruence by `J`, clash by
  `contradiction`;
- equation-typed proof arguments through `Bool.uniqueEq` and `DecEq.uniqueEq`;
- a stage 2 that instantiates local `∀` hypotheses once, never library lemmas;
- whether `Bool` propagation runs before splitting.

Acceptance: the three failing probes in §5.1 and SW-608 items 1, 2 and 5. Measure the cost on
decide.md's 64-case prototype (`docs/proposals/decide/cases_budget.sw`). Refs: §5.1; C1-C3, C5;
D2000.

**T2. Counterexample search: say when hypotheses held only for small inputs.** Record the
largest total size among inputs where every hypothesis held. In `--verbose` (and in the
on-failure note's absence, nothing changes), print "hypotheses held only up to size k" when k is
well below the size reached. Add `sparse.sw`'s `shortIncreasing` as an example. Run `check
--counterexamples` over std and aoc and list the theorems affected. Measurement and reporting
only. Refs: §5.2; C11, C12; SW-687.

**T3. Design note, if T2 finds cases: inputs that satisfy a `Bool` hypothesis.** Cover:
- generation driven by a structurally recursive predicate's case tree;
- ordering several hypotheses by selectivity;
- the time budget;
- the fallback to filtering;
- propositional hypotheses through a derived fuel-bounded checker, as an optional part.

Refs: §5.2; C11-C13; counterexample-search.md "Later, only with a trigger".

**T4. Design note: generated case theorems (`f.cases`, then `f.induct`).** First check whether
today's `cases` already proves the day 16 and day 23 statements that got `E-MATCH-MOTIVE`. If
not, design:
- `f.cases` generated on demand from the case tree, one branch per leaf, with the tested
  equations, including a `match found:` equation, as hypotheses;
- the unfolding variant;
- `f.induct` for `decreasing` definitions;
- names (reserved suffixes) and hashing.

Revisit D231-D233 and say whether this replaces SW-802's per-leaf lemmas. Refs: §5.3; C8; SW-802,
SW-809, SW-199; D2001.

**T5. Show what automation found.** Two opt-in pieces:
- on success, `cases` reports its split tree and each leaf's closer, and `omega` the facts it
  used, offered by the LSP as an expansion;
- at each `?`, a pass that tries `rfl`, `cases` and `omega` and reports which closes it.

Nothing becomes part of a proof without being written. Refs: §5.4; C2, C18, C21, C25.

**T6. `cases`: lookahead before giving up.** When `E-CASES-BUDGET` or `E-CASES` would be
reported and more than one atom was a candidate, retry with each other candidate first, under a
small budget each. Report as today if none closes. It can't change a proof that passes today.
Measure on SW-608 item 3. Refs: §5.1; C6.

## 8. Decisions

**D2000. Make a congruence-closure closer in `cases` (T1) the next proof-automation design,
ahead of deferred `simp [rules]` (D1168)?** It is design note first, and it reads only facts in
scope, never library lemmas. The assumptions, in full:
- (A1) comparing class members by their computed form, as `cases` compares atoms now, is enough
  for the target proofs, without full conversion inside the closure;
- (A2) the classes at one `cases` node are small (tens of terms), so the closer costs little when
  it fails;
- (A3) congruence steps written with `J`, with `Bool.uniqueEq` or `DecEq.uniqueEq` equating
  equation-typed proof arguments, type-check for the dependent calls the target proofs contain.

It doesn't change D1971 (decide.md), whose additions are separate closers. **[Recommend yes.]**

**D2001. For SW-802 and SW-809, design generated case theorems (`f.cases`, Lean's `fun_cases`)
instead of per-leaf equation lemmas (D231)?** Per-leaf lemmas are `rfl` in Stitchwort and add
only a name (equation-lemmas.md §6 (a)). A case theorem adds each branch's tested equations as
hypotheses. The assumptions, in full:
- (F1) the elaborated case tree records which equation each leaf tested, readably enough to state
  the branches;
- (F2) today's `cases` does not already prove the day 16 and day 23 statements that failed with
  `E-MATCH-MOTIVE`; T4 checks this first, and if `cases` does, the decision lapses to "document
  `cases` for this".

**[Recommend yes.]**

## 9. Sources not reached

**Full text not reachable** (cards C26-C29):

| Source | DOI or reference | Tried | Result |
|---|---|---|---|
| C26 Morrison, de Moura, grind, IJCAR 2026 | LNCS, pp. 106-114 | S1, S6; arXiv API; Semantic Scholar search | not found; search rate-limited |
| C27 Rossel et al., POPL 2026 | 10.1145/3776667 | dl.acm.org/doi/pdf; web.archive.org `2025id_` and `2026id_`; Semantic Scholar (GOLD, links to the DOI); S2 | 403; 404; 404; DOI only |
| C28 Bhat, Böving et al., OOPSLA 2025 | 10.1145/3763167 | dl.acm.org/doi/pdf; web.archive.org `2025id_`, `2026id_`; theory.stanford.edu abstract page; S4 | 403; 404; connection refused |
| C29 Limperg, From, CPP 2023 | 10.1145/3573105.3575671 | dl.acm.org/doi/pdf; web.archive.org `2024id_`, `2025id_` | 403 |

**For Matt to fetch: none.** None of the four meets the bar. C26 describes a system whose manual,
source and slides were read (C2-C4). C27's own authors deprecated the tool. C28 and C29 have no
use in Stitchwort yet.

**Screened only** (support nothing): rows 30-48 of §3. Downloaded but only opened: Rossel's MSc
thesis, egglog, Merging Inductive Relations, Rózsa.

**Not searched.** ITP, CPP, IJCAR, CADE and FroCoS programmes year by year; Lean workshop
programmes; Isabelle's Quickcheck and Nitpick after 2022; Agda's and Idris 2's automation since
2022. This register makes no claim about them.

**Noticed in passing** (not research): the module comment of `crates/elab/src/cases.rs:5-8`
still shows the old word `split` (`split`, `split in t`), renamed `cases` in SW-592.
