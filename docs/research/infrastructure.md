# Literature trawl: infrastructure and trust

**Counts: screened 68; carded 29; read in full 28; not read 1 (C3; listed in §9 with the
uncarded sources still not reached).** No card marked NOT READ supports a deep read, a ranking
or a recommendation. The 29 Oct version said screened 59, carded 26, read in full 24, not read
2: C23 (Sisyphus) was read for the audit, from Ilya Sergey's own copy; the §9 sources were then
reached and decided (§2 "Audit searches"), adding C31–C33 and nine screened rows.

**Audited 30 Oct 2026 against full texts: 18 OK, 5 minor (fixed), 1 wrong (fixed), 0 can't
verify** (of the 24 cards first marked read). C1 was wrong: its numbers (153 bugs, 128
confirmed, 71 fixed; 50 + 22 from the mutations) came from the anonymous submission copy on UCL
Discovery; the published paper says 156, 137 and 85, and 52 + 22. Each place that used them is
corrected. The minor ones: C2 gave Thalia a finding it cites from Chaliasos et al. 2021; C19's
figures are for Hazel only; C20 said LSP makes clients "parse messages" (not in the paper) and
cited the playground's JSON for a claim about `--index`; C21 and C28 had a stale or stretched
Stitchwort reference. Outside the cards, one Stitchwort claim was wrong: §5.3 said tests run on
the checker's evaluator without erasure, so a proof edit could unstick a test; tests run erased
(`driver.rs:1241-1243`, docs/core.md:239), so T10's open question is answered. §5.2 credited
"RustSmith and Rustlantis were theses" to the Rustlantis paper; only Rustlantis's thesis origin
is stated, in Ralf Jung's post. Line references into docs/core.md had drifted by two to four
lines, and today's merges changed four descriptions (the soundness corpus is 107 examples after
the 2026 kernel-bug shapes and SW-902; kernel.md's T1 is built; SW-901 put the extraction
snapshots in the merge tier; SW-900 changed how random containers share a size). Each fixed
place ends with "Audit:".

*SW-894, cluster 7. Trawled 29 October 2026 against `main` at `5c25a1b5`. Research only: no
code changed, no tests run. Window: 2022 onwards (D1831); older work appears only where
in-window work or a system we compare with relies on it, marked **classic**.*

Labels: **[cited]** read in the linked source (fetched 29 Oct 2026); **[checked]** read in
Stitchwort's code or docs at the place given; **[inferred]** my reasoning; **[unverified]**
from an abstract, a listing, a search summary or memory only.

This cluster sits next to [kernel.md](kernel.md), which already covers the 2025–26 kernel
soundness bugs, the Lean Kernel Arena, independent checkers (Lean4Lean, nanoda, MetaRocq),
Lean's trust ladder (`lake check`, `comparator`, `--paranoid`) and an adversarial audit lane
(its T1). This file doesn't repeat those. It covers what surrounds the kernel: how other
projects test type checkers and compilers, cache keys and incremental checking, editor and
agent interfaces, library maintenance, and the infrastructure that keeps agent-written code
honest.

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

Stitchwort's testing is already broad: fuzzers for the parser, formatter, elaborator and
kernel, differential tests across four ways of running a program, a nested-types oracle,
must-reject examples paired with accepted ones (docs/testing.md, DESIGN §13) **[checked]**.
What the literature adds is mostly **better oracles**, not more fuzzers.

- **Oracles that come from the program itself.** Hephaestus (PLDI 2022) found 156 typing bugs
  in javac, kotlinc and groovyc. 74 of them (52 inference, 22 soundness) came from two
  transformations of programs that already compile, and the generator alone missed them:
  delete type annotations (must still compile) and replace one type with an incompatible one
  (must not compile) **[cited]**. (Audit: the first version said 153 and 72, the submission
  copy's numbers.) Thalia (POPL 2024) pushes the same two
  oracles further. Stitchwort's elaborator fuzzer has neither: its oracles
  are "no panic, no internal error, no kernel rejection, a cold and warm cache agree"
  (`crates/driver/tests/fuzz_elab.rs`, docs/testing.md) **[checked]**. Both transformations
  fit SW-686 and SW-687 directly (§5.1).
- **A type-preservation sweep for the kernel.** Evaluate each accepted body, read it back,
  and check the result against the same type. A rejection is a bug in the evaluator or the
  checker. It's an old idea (PLT Redex, QuickChick, **classic**) but cheap here, and kernel.md
  doesn't propose it (§5.1, T3).
- **Generators for SW-688.** Three in-window results shape it: generate at the IR the backends
  share, as Rustlantis does with Rust's MIR (22 rustc bugs); build programs out of the
  standard library's own signatures, as Thalia does; and choose types non-locally so
  functions use their arguments (Frank et al., POPL 2024, 4× faster to find GHC bugs).
  ETNA's mutation scoring says how to tell which generator is worth keeping, and the Dafny
  compiler fuzzers (ICST 2024) show why the reference evaluator must stay in every backend
  comparison: bugs in code the backends share give all of them the same wrong answer (§5.2,
  C33).

The second theme is **cache keys**. Lean's new module system keeps proofs private to their
module, so "changes … that affect only … proofs … will not trigger rebuilds" downstream
**[cited]**. Stitchwort hashes theorem bodies into every dependent's hash, so a proof edit in
a library lemma re-checks and re-tests everything downstream. Two safe steps exist (§5.3): key
the test-result cache on the erased program, which proofs can't affect, since tests run
erased; and measure how often
a dependent's check actually looks inside another namespace's proof, before deciding whether
theorems should be opaque across namespaces (D1931).

The third theme is **agent-driven development**. The useful sources are recent and practical:
Carlini's C compiler built by parallel Claude agents (Feb 2026), ImpossibleBench on agents
editing tests (Oct 2025), Krishnamurthi and Flatt on error detail for agents (Jun 2026),
Mathlib's review tooling (CICM 2025). Together they suggest a **trust diff** for each lane:
which theorem *statements* changed, which declarations were renamed, which must-reject
examples, snapshots, budgets or assumptions changed (§5.4, T1). It is cheap because content
hashes already ignore names and layout, so a rename is "same hash, new name", and a
statement's hash is one small function away (§5.4 A3).

## 2. Method and queries

Searches were run with the web search tool (standard mode) on 29 Oct 2026. **The session's
shared search budget ran out after query 27**, so the trawl is narrower than planned (§9).
After that, sources were reached by fetching known URLs (arXiv abstracts and PDFs, project
documentation, conference pages). PDFs were downloaded with `curl` and converted with
`nix shell nixpkgs#poppler-utils -c pdftotext` (the package is `poppler-utils`, with a
hyphen). **That worked** for every PDF obtained. Full texts came from arXiv, authors' pages
(lemonidas.github.io, hazel.org), UCL Discovery, Microsoft Research, Dagstuhl, and one Internet
Archive copy of an ACM PDF (Rustlantis; dl.acm.org itself returns an HTML page to scripts).
Every card says "Full text: read (source)" or **NOT READ**. Long papers were read section by
section, with targeted searches over the whole extracted text for numbers and limitations;
blog posts and documentation pages were read whole. Following the reading protocol (Matt, 29
Oct), cards first written from abstracts were re-read in full or demoted (§9).

| # | Query or source | Kept or useful hits |
|---|---|---|
| Q1 | `differential testing type checkers dependently typed proof assistants random well-typed term generation 2023 2024` | Fetscher et al. (classic) only |
| Q2 | `"well-typed" program generator testing compilers typed functional language PLDI OR ICFP OR OOPSLA 2023 2024 2025` | Hephaestus (PLDI 2022); Eris (PLDI 2026) |
| Q3 | `testing type checkers "type checker" bugs empirical study OOPSLA 2022 2023 typing bugs compilers` | Chaliasos et al. OOPSLA 2021 (classic) |
| Q4 | `Unison content-addressed code renames dependency updates blog 2024 2025 "update" propagation` | Unison docs; Unison 1.0 (secondary) |
| Q5 | `"Enumerating Ill-Typed Programs" type analyzers PLDI 2026` | Eris; Thalia arXiv 2311.04527 |
| Q6 | `Thalia OR "API-driven program synthesis" testing static typing compilers OOPSLA 2024 Chaliasos` | Thalia (POPL 2024) |
| Q7 | `fuzzing proof assistant Lean Coq Agda type checker bugs found arXiv 2024 2025` | de Moura blog (Mar 2026); lean-zip fuzzing blog |
| Q8 | `Unison "update" command 2024 2025 … "lib.install" dependency upgrade` | Unison upgrade docs, release notes 0.5.21–0.5.49 |
| Q9 | `metamorphic testing compilers type checkers "metamorphic" 2023 2024 equivalence modulo inputs functional language` | EMI (classic) only |
| Q10 | `mutation testing proofs specifications "mutation" Dafny OR Coq OR Isabelle OR Lean specification weakness 2023 2024 2025` | MutDafny (ICSE 2026) |
| Q11 | `QuickChick "property-based testing" type checker STLC mutants "etna" evaluation framework generators 2023` | ETNA (ICFP 2023) |
| Q12 | `generating well-typed terms dependent types property-based testing "inductive relations" generators Lampropoulos 2022 … 2025` | Frank et al. (POPL 2024); Prinz–Lampropoulos (PLDI 2023); Buzdalov (TyDe 2024) |
| Q13 | `Salsa incremental computation "durability" "early cutoff" rust-analyzer red-green query-based compiler 2023 2024 2025 blog` | rust-analyzer "Durable incrementality" (2023) |
| Q14 | `"Build systems à la carte" follow-up 2022 2023 2024 cloud build "constructive traces" early cutoff paper` | BSalC ICFP 2018 / JFP 2020 (classic) |
| Q15 | `incremental type checking dependently typed language query-based elaboration Lean 4 language server incremental elaboration snapshot 2024` | Lean 4.9.0 notes (#3940); Shen–Shi arXiv 2605.25556 |
| Q16 | `Lake build system Lean 4 trace files hashing "lake cache" mathlib cache olean 2025 2026` | Lake trace docs; Mathlib cache threads |
| Q17 | `proof repair library evolution Coq Lean "proof repair" 2023 2024 2025 …` | Sisyphus (PLDI 2023); APE-Bench I; Coq Platform (2022) |
| Q18 | `mathlib maintenance practices paper … ITP 2024 2025 "maintaining"` | Growing Mathlib (CICM 2025) |
| Q19 | `Hazel live programming typed holes "total type error localization" OR "marked lambda calculus" POPL 2024 editor` | Zhao et al. (POPL 2024) |
| Q20 | `language server protocol proof assistant paper 2023 2024 "Rocq" OR "Coq" LSP coq-lsp "Lean infoview" …` | coq-lsp; CoqPyt; an MCP wrapper of coq-lsp |
| Q21 | `LLM agents proof assistant interaction infrastructure "Pantograph" OR "LeanDojo" OR "Lean REPL" …` | Pantograph (arXiv 2410.16429) |
| Q22 | `LLM agents implementing compiler or language implementation guardrails tests "coding agents" …` | Kjellberg et al. (SANER 2026); pointer to Carlini |
| Q23 | `"reward hacking" OR "specification gaming" coding agents tests modified verification Lean sorry …` | ImpossibleBench; CapCode; SpecBench |
| Q24 | `compiler error messages for LLM agents structured diagnostics repair loop "compiler feedback" study 2025` | Krishnamurthi–Flatt (2606.01522); Li–Krishnamachari (2602.11481) |
| Q25 | `random program generator OCaml OR Haskell OR Rust compiler fuzzing "RustSmith" OR "rustlantis" …` | Rustlantis (OOPSLA 2024); RustSmith (ISSTA 2023); Rust-twins (ASE 2024) |
| Q26 | `"Generating Well-Typed Terms that are not Useless" POPL 2024 abstract` | POPL 2024 page |
| Q27 | `coverage-guided fuzzing type checker "grammar" structure-aware cargo-fuzz …` | Grammarinator+libFuzzer (2025); Bonsai (2021, classic) |
| — | budget exhausted at the next query (`CakeML … verified checker`) | — |

Direct fetches (no search): rust-analyzer blog 2023-07-24; anthropic.com/engineering/building-c-compiler;
unison-lang.org "The big idea" and the `lib.install` upgrade how-to; Lean reference "Source
Files and Modules" and release notes v4.9.0; arXiv abstracts 2409.00921, 2508.21593,
2510.20270 (and its HTML for the numbers); POPL 2024 page for Frank et al.; DROPS page for
Candle (ITP 2022); ralfj.de Rustlantis post. Full-text PDFs: listed above.

**Audit searches (30 Oct 2026).** Twelve web searches (standard mode), plus direct fetches
(arXiv export API, Semantic Scholar's API, HAL's API, DBLP, Dagstuhl, authors' pages, GitHub,
the Internet Archive's `id_` copies of ACM PDFs). Of the queries the 29 Oct method listed, Q1–Q27
had run and the next one (CakeML, verified checkers) had not; Q33 covers it.

| # | Query or source | Kept or useful hits |
|---|---|---|
| Q28 | `"Enumerating Ill-Typed Programs for Testing Type Analyzers" pdf` | PLDI page (DOI 10.1145/3808320); no copy |
| Q29 | `Rust-twins ASE 2024 … pdf` | DOI 10.1145/3691620.3695059; abstract only |
| Q30 | `Buzdalov "Dependent Types to Push Corners" … TyDe 2024` | talk listing only; Hansen–Brady, TyDe 2024 (row 63) |
| Q31 | `Vercel Zero language JSON diagnostics …` | secondary posts; the primary docs were then fetched from GitHub (row 55) |
| Q32 | `translation validation compiler dependently typed proof assistant 2024 2025 …` | Trivet (row 68); nothing in-window on CakeML or Agda |
| Q33 | `Dafny test generation IDE verification 2023 2024 …` | fuzz-d and DafnyFuzz, ICST 2024 (C33); DTest (row 70) |
| Q34 | `matklad blog 2023 2024 "rust-analyzer" …` | nothing in-window |
| Q35 | `automatic semantic versioning API diff from types …` | Sembid, ASE 2022 (row 69); nothing for typed functional languages |
| Q36 | `fuzzing elaborator OR typechecker of proof assistant … 2025 2026` | Isabelle "Validating the Verifier" (row 66); kernel.md's sources again |
| Q37 | `Lean FRO roadmap year 3 2025 2026 Lake cache …` | Lean FRO Year 4 Part 1 roadmap (row 65) |
| Q38 | `2025 compiler testing typing bugs type checker …` | no 2025 paper; its summary quoted Hephaestus's published numbers (156 bugs), which led to the C1 finding; the published PDF came from theosotr.github.io |
| Q39 | `F-IDE OR HATRA workshop 2024 2025 proof assistant language server agents …` | nothing new in-window |

## 3. Screened list

68 sources (rows 57 and 61 point to other registers): 30 keep (29 cards; rows 21 and 22 share
C11), 16 maybe, 22 drop. Kernel-specific sources are in kernel.md and not repeated here. (Audit:
the 29 Oct version had 59 sources, 27 keep, 20 maybe, 12 drop; rows 8, 12, 23, 29, 31, 39, 44,
45, 46, 51 and 55 were decided after reaching them, and rows 62–70 are new.)

| # | Source | Verdict | Why |
|---|---|---|---|
| 1 | Chaliasos et al., *Finding Typing Compiler Bugs* (Hephaestus), PLDI 2022 | keep | C1; §5.1 |
| 2 | Sotiropoulos, Chaliasos, Su, *API-driven Program Synthesis for Testing Static Typing Implementations* (Thalia), POPL 2024 | keep | C2; §5.1, §5.2 |
| 3 | *Enumerating Ill-Typed Programs for Testing Type Analyzers* (Eris), PLDI 2026 | keep | C3, **NOT READ** |
| 4 | Chaliasos et al., *Well-Typed Programs Can Go Wrong*, OOPSLA 2021 (**classic**, base of 1–3) | maybe | bug taxonomy |
| 5 | Frank, Quiring, Lampropoulos, *Generating Well-Typed Terms That Are Not "Useless"*, POPL 2024 | keep | C4; §5.2 |
| 6 | Shi, Keles, Goldstein, Pierce, Lampropoulos, *Etna*, ICFP 2023 | keep | C5; §5.2 |
| 7 | Prinz, Lampropoulos, *Merging Inductive Relations*, PLDI 2023 | maybe | generators from relations; Rocq-specific |
| 8 | Buzdalov, *Dependent Types to Push Corners of the Property-based Testing* (extended abstract), TyDe 2024 | drop | a talk; no copy found (the ICFP page has no file); the same session's Hansen–Brady paper (row 63) was read instead |
| 9 | Fetscher et al., *Making Random Judgments*, ESOP 2015 (**classic**) | drop | window; cited for background |
| 10 | Wang, Jung, *Rustlantis*, OOPSLA 2024 | keep | C6; §5.2 |
| 11 | RustSmith, ISSTA 2023 | keep | C7 |
| 12 | Yang et al., *Rust-twins*, ASE 2024 (10.1145/3691620.3695059) | drop | abstract read (ACM page; no open copy): dual macros as a second implementation; Stitchwort has no macros, and C7 covers the oracle |
| 13 | Xia et al., *Fuzz4All*, ICSE 2024 | keep | C8; SW-689 |
| 14 | Germinator, arXiv 2512.05887 | drop | MLIR dialects |
| 15 | Grammarinator meets libFuzzer, ICSOFT 2025 | maybe | SW-689 structure-aware |
| 16 | Bonsai fuzzing, 2021 (**classic**) | drop | window; valid-input rate figure only |
| 17 | Polymorphic coverage types (Poirot), arXiv 2304.03393 | drop | generator verification, far |
| 18 | EMI, PLDI 2014 (**classic**) | drop | window |
| 19 | Amaral, Mendes, Campos, *MutDafny*, ICSE 2026 | keep | C9; T6 |
| 20 | Ramsay, Walpole, *Ill-Typed Programs Don't Evaluate*, POPL 2024 | drop | error explanation, not infra |
| 21 | Unison docs, "The big idea" | keep | C11; §5.4 |
| 22 | Unison `lib.install` / `upgrade` workflow (release notes 0.5.21–0.5.49) | keep | C11 |
| 23 | Unison 1.0 page (unison-lang.org/unison-1-0, and the 1.0.2 release note) | drop | read: a status and features page; nothing beyond C11 |
| 24 | rust-analyzer, *Durable incrementality*, 2023 | keep | C12; §5.3 |
| 25 | Mokhov, Mitchell, Peyton Jones, *Build Systems à la Carte*, ICFP 2018 / JFP 2020 (**classic**) | keep | C13; §5.3 |
| 26 | Lean 4.9.0 incremental elaboration (#3940, 2024) | keep | C15 |
| 27 | Lean reference, *Source Files and Modules* (module system) | keep | C14; §5.3 |
| 28 | Lean Zulip, *Coarseness of Mathlib.Cache* (Apr 2023) | keep | C16 |
| 29 | Shen, Shi, *Keep the Proof State Live*, arXiv 2605.25556 | maybe | read: forks Lean's server snapshot at each `sorry` (5.6–50× on 48 miniF2F-v2 problems); the cost it removes (18–735 s of elaboration per branch) is far above Stitchwort's (most namespaces under 0.1 s), so it matters only if proof search runs many branches |
| 30 | Fredriksson, Sixty / Rock query-based compiler (blog, 2020, **classic**) | maybe | dependent types + queries |
| 31 | Spall, Mitchell, Tobin-Hochstadt, *Forward Build Systems, Formally*, CPP 2022 (arXiv 2202.05328) | drop | read: correctness of tracing build systems (Rattle) in Agda: "the same result as running the commands in order, or reports an error"; Stitchwort's cache keys are computed before checking, not traced, and check-cache.md §5.4 already tests that statement differentially |
| 32 | *Reliably Reproducing Machine-Checked Proofs with the Coq Platform*, arXiv 2203.09835 | maybe | version pinning; read, nothing to steal before packages exist |
| 33 | Zhao et al., *Total Type Error Localization and Recovery with Holes*, POPL 2024 | keep | C18 |
| 34 | *Live Pattern Matching with Typed Holes*, OOPSLA 2023 | drop | live evaluation, far |
| 35 | Blinn, Li, Kim, Omar, *Statically Contextualizing LLMs with Typed Holes*, OOPSLA 2024 | keep | C19; T8 |
| 36 | coq-lsp (Flèche engine), README | keep | C21 |
| 37 | CoqPyt, arXiv 2405.04282 | drop | client library |
| 38 | Aniva et al., *Pantograph*, arXiv 2410.16429 (TACAS 2025) | keep | C20 |
| 39 | Nawrocki, Ayers, Ebner, *An Extensible User Interface for Lean 4*, ITP 2023 | keep | C32 |
| 40 | MCP wrapper of coq-lsp (lobehub listing) | maybe | LSP → agent tools |
| 41 | Baanen et al., *Growing Mathlib*, CICM 2025 | keep | C22; §5.4 |
| 42 | Gopinathan, Keoliya, Sergey, *Sisyphus*, PLDI 2023 | keep | C23 (read in the audit) |
| 43 | Viola, Fan, Ringer, proof repair across quotients, arXiv 2310.06959 | drop | Rocq setoids |
| 44 | Xin et al., APE-Bench, arXiv 2504.19110 (v3, Feb 2026) | maybe | read: tasks from Mathlib commits, checked by compilation and an LLM judge (90.6% agreement with experts on 64 solutions) on "semantic correctness, requirement alignment, scope control"; scope control is what T1 lists mechanically |
| 45 | Abrahamsson, Myreen, Kumar, Sewell, *Candle*, ITP 2022 | maybe | read: a HOL Light clone proved sound down to machine code; its point, that the host language's implementation is in the trusted base, applies to Stitchwort's Rust kernel, but nothing is buildable now |
| 46 | Forster, Sozeau, Tabareau, *Verified Extraction from Coq to OCaml*, PLDI 2024 | keep | C31 |
| 47 | Carlini, *Building a C compiler with a team of parallel Claudes*, Feb 2026 | keep | C26; §5.4 |
| 48 | Zhong, Raghunathan, Carlini, *ImpossibleBench*, arXiv 2510.20270 | keep | C27; §5.4 |
| 49 | Krishnamurthi, Flatt, *Type-Error Ablation and AI Coding Agents*, arXiv 2606.01522 | keep | C28; T7 |
| 50 | Li, Krishnamachari, *Compiler-Guided Inference-Time Adaptation … Idris*, arXiv 2602.11481 | keep | C29 |
| 51 | Kjellberg, Staron, Fotrousi, *From LLMs to Agents …: Providing an LLM with a Compiler*, SANER 2026 (arXiv 2601.12146) | drop | read: 16 models on 699 RosettaCode C tasks, compile success up 5.3–79.4 points with gcc feedback; compile rate only, and C29 makes the point for a dependently typed language |
| 52 | de Moura, *Who Watches the Provers?* (blog, Mar 2026) | maybe | see kernel.md C25 |
| 53 | lean-zip fuzzing (kirancodes blog, 2026) | keep | C10 |
| 54 | CapCode, SpecBench, BenchJack (2026 preprints) | maybe | test-gaming measures |
| 55 | Vercel Labs, Zerolang diagnostics (docs/articles/diagnostics.md in github.com/vercel-labs/zerolang, 2026) | maybe | read: each diagnostic has a stable code, `rule`, `expected`, `actual`, `fix` and `explain: zero explain NAM003`; JSON only "when a tool needs exact spans, codes, fix ids". Stitchwort has codes but no `explain` command (the `Command` enum in `crates/cli/src/main.rs`) **[checked]**. An experimental vendor language |
| 56 | Patch porting with JSON diagnostics, arXiv 2604.01680 | drop | narrow |
| 57 | Mariposa / proof stability | — | in proof-automation.md §3, row 35 (screened, not read) |
| 58 | QED at Large survey (2019, **classic**) | drop | window |
| 59 | Ringer et al., proof repair (PLDI 2021, **classic**) | drop | window |
| 60 | Lean 4 snapshot types (API docs) | maybe | reuse invariant for headers; not read |
| 61 | Kernel Arena, Lean4Lean, nanoda, MetaRocq, `lake check`, comparator, Stérin | — | kernel.md C4, C5, C24–C26 |
| 62 | Unison, *A preview of Unison's improved update process* (blog, Oct 2023) | maybe | read: a type-preserving edit propagates to dependents automatically; otherwise a branch and a scratch file of what didn't typecheck. Confirms C11 |
| 63 | Hansen, Brady, *Type-level Property Based Testing*, TyDe 2024 (arXiv 2407.12726) | maybe | read: QuickCheck run by Idris 2's type checker finds a wrong state-machine *type* (unlimited PIN retries); T6's aim, for types rather than theorems; about 3.5 s per property |
| 64 | Donaldson, Sheth, Tristan, Usher, *Randomised Testing of the Compiler for a Verification-Aware Programming Language* (fuzz-d, DafnyFuzz), ICST 2024 | keep | C33; §5.2 |
| 65 | Lean FRO, *Year 4 – Part 1 Roadmap* (Sep 2026 – Feb 2027) | maybe | read: `lake build` without kernel checks, then `lake check [--paranoid]` as the trust step; Tau Ceti gates AI-written PRs with AI reviewers "against open rubrics"; the kernel side is kernel.md's |
| 66 | *Validating the Verifier: Automated Testing for Isabelle/HOL* (2026, Zenodo record 19899187) | drop | search summary only: fuzzes Sledgehammer's prover interface; Stitchwort calls no external provers |
| 67 | *Faults in Our Formal Benchmarking*, arXiv 2606.29493 | drop | title and search summary only; benchmark defects belong to proof-automation.md |
| 68 | Trivet (LLM and Lean translation validation of LLVM passes) | drop | search summary only; not Stitchwort's compiler |
| 69 | Chen et al., Sembid, ASE 2022 (arXiv 2209.00393) | drop | search summary only; Java semantic breaking changes |
| 70 | DTest, DUnit, DMock: a toolkit for testing Dafny (Amazon, 2023) | drop | search summary only; counterexamples to unit tests, which counterexample-search.md covers its own way |

## 4. Cards

Card numbers C17, C24, C25 and C30 were used in a first draft for sources since demoted to
"screened, not carded" (§3, §9); the numbers are left unused so references stay stable.

### Testing type checkers and compilers

**C1. Hephaestus.** Chaliasos, Sotiropoulos, Spinellis, Gervais, Livshits, Mitropoulos,
*Finding Typing Compiler Bugs*, PLDI 2022.
*Claim:* a generator of well-typed programs plus two transformations found 156 bugs (137
confirmed, 85 fixed) in javac, kotlinc and groovyc over nine months. *Type erasure mutation*
"removes declared types from variables and parameters, or type arguments from parameterized
constructor and method calls, while preserving the well-formedness" (oracle: still accepted);
*type overwriting mutation* replaces a type with an incompatible one, and then "compiling a
program obtained from this mutation indicates a potential soundness bug" **[cited]**. The two
found 52 inference and 22 soundness bugs "which we were unable to detect by using our program
generator by itself" **[cited]** (its Figure 7c: generator 78, erasure 52, overwriting 24, both
2). *Steal:* both oracles, over Stitchwort's existing corpus (§5.1). *Helps:* SW-686, SW-687.
*Cost:* tooling. *Full text:* read (the published version,
[author copy](https://theosotr.github.io/assets/pdf/pldi22.pdf); §1, §3 and Figure 7).
Audit: WRONG as first written. The numbers came from the copy on UCL Discovery, which is the
anonymous submission ("Anonymous Author(s)"; 153 bugs, 128 confirmed, 71 fixed; 50 + 22). The
published paper says 156, 137, 85 and 52 + 22. Fixed here and in §1, §5.1 and T2.

**C2. Thalia.** Sotiropoulos, Chaliasos, Su, *API-driven Program Synthesis for Testing Static
Typing Implementations*, POPL 2024. *Claim:* motivated by an earlier study's finding (Chaliasos
et al., OOPSLA 2021, row 4) that "around one third of compiler typing bugs are triggered by
small test cases that employ … APIs from the standard library", synthesising small clients from
library signatures found 84 bugs (77 "either confirmed or fixed") in Scala, Kotlin and Groovy,
"at least 42" of them missed by Hephaestus. Two
modes: omit type arguments "whenever these can be inferred by the surrounding context"
(inference oracle), and enumerate ill-typed uses of one API (soundness oracle); together 27
inference and 10 soundness bugs **[cited]**. *Steal:* build test programs out of std's
signatures, not a grammar (§5.2); erase only what context determines (§5.1). *Helps:* SW-686,
SW-688. *Cost:* tooling. *Full text:* read ([arXiv 2311.04527](https://arxiv.org/pdf/2311.04527),
the extended version; the numbers match the [POPL copy](https://theosotr.github.io/assets/pdf/popl24.pdf)).
Audit: MINOR. The one-third finding is the 2021 study's, which Thalia cites, not Thalia's own;
"77 confirmed" and "42 missed" were "confirmed or fixed" and "at least 42".

**C3. Eris.** Sotiropoulos, Su, *Enumerating Ill-Typed Programs for Testing Type Analyzers*,
PLDI 2026 (PACMPL, [10.1145/3808320](https://doi.org/10.1145/3808320); Distinguished Paper).
**NOT READ** (§9: open access at ACM, but every scripted route returned 403 or nothing). The
artifact README was read: it has seeds, API specifications and a list of bugs, but not the
paper. Nothing below rests on it. Audit: retried 30 Oct; authors and DOI found (Semantic
Scholar, the PLDI page, theosotr.github.io), no readable copy.

**C4. Non-useless well-typed terms.** Frank, Quiring, Lampropoulos, POPL 2024. *Claim:*
top-down generators choose a subexpression's type locally, so generated functions often
ignore their arguments; non-local steps over a calculus with type and argument holes delay
the choice, give argument use "much closer to real programs", and find GHC strictness-analyser
bugs "four times faster than the current state-of-the-art local approach" **[cited]**. The
calculus is simply typed with polymorphic constants; "generating polymorphic functions is
seemingly out of reach" **[cited]**. *Steal:* for SW-688's source generator, decide how each
parameter is used before fixing types. Dependent types are beyond what the paper handles, so
for Stitchwort this applies to the non-dependent fragment only **[inferred]**. *Helps:* SW-688.
*Cost:* part of SW-688. *Full text:* read ([author copy](https://lemonidas.github.io/pdf/NotUseless.pdf)).
Audit: OK (abstract, §3.5, §4.1). The GHC result replicates a known case study on GHC 6.12's
strictness analyser (Pałka et al.), so the bugs are old ones found faster, not new ones.

**C5. ETNA.** Shi, Keles, Goldstein, Pierce, Lampropoulos, ICFP 2023 (experience report).
*Claim:* compare test generators by mutation testing: a workload is an implementation,
properties and hand-written mutants, and a generator is scored by time to find each mutant;
workloads include BST, RBT, STLC and F<:; a size experiment is "a cautionary tale: PBT users
should not naively" assume bigger inputs are better, since detection depends on the specific
mutant **[cited]**. *Steal:* score Stitchwort's fuzzers and oracles against a fixed set of
injected kernel and elaborator bugs before investing in SW-688/689 (§5.2, T5). *Cost:* small.
*Full text:* read ([NSF PAR](https://par.nsf.gov/servlets/purl/10502034)). Audit: OK (§2–§4.2;
the quote ends "expect that larger inputs are better"). Since 29 Oct, SW-900 made a random
`List` or `Vec`'s elements share one size, and a draw stops past `MAX_RANDOM_VALUES`
(counterexample-search.md, "SW-900") **[checked]**; ETNA's size result says to measure such a
change per bug rather than assume bigger is better **[inferred]**.

**C6. Rustlantis.** Wang, Jung, OOPSLA 2024. *Claim:* generate MIR directly "to avoid having to
deal with Rust's strict type and borrow checker"; the generator statically tracks program
state (a "place graph") so every program is free of Undefined Behaviour and deterministic, and
adds "decoy blocks" so control flow looks complex to optimisers; programs print a hash of
their variables, and on a mismatch are regenerated with a slow per-variable dump; outputs are
compared across backends, optimisation levels and Miri; 22 new bugs (8 in rustc, 14 in its
backends) **[cited]**. *Steal:* SW-688's backend half should generate the erased IR that
`crates/rt`, JS and native share, tracking values so programs stay total and in bounds, and
compare a hash of the result first (§5.2). *Helps:* SW-688, native backend. *Cost:* tooling.
*Full text:* read (ACM PDF via the [Internet Archive](https://web.archive.org/web/2025id_/https://dl.acm.org/doi/pdf/10.1145/3689780)).
Audit: OK (abstract, §1, §3, the `dump_var` hash in §4). The paper doesn't say it began as a
thesis; Ralf Jung's [post](https://www.ralfj.de/blog/2024/11/25/rustlantis.html) does ("done
by Andy (Qian Wang) for his master thesis"), now cited in §5.2.

**C7. RustSmith.** Sharma, Yu, Donaldson, ISSTA 2023 tool paper. *Claim:* a Csmith-style
generator whose programs respect Rust's type rules found long-unnoticed historic rustc bugs and
new bugs in mrustc, an alternative compiler **[cited]**. *Steal:* a second implementation is an
oracle; Stitchwort has four ways to run a program (docs/testing.md) **[checked]**. *Cost:* none
beyond SW-688. *Full text:* read ([PDF](https://www.doc.ic.ac.uk/~afd/papers/2023/ISSTA-tool.pdf)).
Audit: OK (the paper says "insidious historic bugs" and "five historic bugs").

**C8. Fuzz4All.** Xia, Paltenghi, Tian, Pradel, Zhang, ICSE 2024. *Claim:* an LLM as input
generator and mutator works across six languages (C, C++, Go, SMT2, Java, Python) and found 98
bugs (64 confirmed) in GCC, Clang, Z3, CVC5, OpenJDK and Qiskit **[cited]**. *Steal:* for a
language no model was trained on, an agent lane can write seed programs for SW-689 and for the
§5.1 transformations from docs/guide and the examples. *Cost:* small. *Full text:* read
([arXiv 2308.04748](https://arxiv.org/pdf/2308.04748)). Audit: OK (nine systems under test; the
six named are the abstract's "such as" list).

**C9. MutDafny.** Amaral, Mendes, Campos, ICSE 2026. *Claim:* mutate the *program* and
re-verify: "If a program with a mutant verifies, this may indicate a weakness in the
specification." 40 operators, some mined from Dafny bug-fix commits; five weak real-world
specifications in 794 programs, "one at every 241 lines of code" **[cited]**. *Steal:* the dual
of SW-687, which mutates proofs to find unsoundness: mutate AoC and std *functions* and
re-check their theorems, to find statements that don't pin down what they claim (T6). *Cost:*
tooling. *Full text:* read ([arXiv 2511.15403](https://arxiv.org/pdf/2511.15403)). Audit: OK ("on
average, one at every 241 lines"; ICSE 2026 per the arXiv comment).

**C10. lean-zip fuzzing.** kirancodes blog, 2026 ([post](https://kirancodes.me/posts/log-who-watches-the-watchers.html)).
*Claim:* 105,823,818 executions over about 19 hours, 16 parallel fuzzers (AFL++, ASan, UBSan,
Valgrind) against a zlib implementation proved in Lean found no memory bugs in the verified
code; one heap overflow in `lean_alloc_sarray` in Lean's C++ runtime (part of the trusted
base), and one out-of-memory crash in an archive parser that had no theorems. "Verification is
only as strong as the questions you think to ask and the foundations you choose to trust"
**[cited]**. *Steal:* fuzz the trusted runtime pieces (`crates/rt`, the JS codecs, natives)
and the code with no theorems, not the proved programs. *Helps:* SW-688, SW-689 target choice.
*Cost:* none. *Full text:* read (post). Audit: OK (post dated April 2026; "4 crashing inputs,
and 1 memory vulnerability" in the run's summary).

**C33. Testing Dafny's compiler (fuzz-d, DafnyFuzz).** Donaldson, Sheth, Tristan, Usher,
*Randomised Testing of the Compiler for a Verification-Aware Programming Language*, ICST 2024.
*Claim:* two generators of correct-by-construction Dafny programs (verifier off) found 24 new
compiler bugs, 9 of them soundness bugs (compiled code that "will deviate from the semantics of
the source program at runtime"), beyond the earlier XDsmith's reach **[cited, abstract, §I]**.
Comparing backends with each other misses bugs in the shared front end: "all back-ends would
inherit the same behaviour and exhibit the same incorrect result", so fuzz-d adds an
independent interpreter and both tools generate self-checking programs; DafnyFuzz also makes
families of equivalent programs (metamorphic) **[cited, §III]**. Iterating over sets and
multisets gave output that differed across backends without a bug; some frequent crash bugs
became "fuzz blockers" that had to be fixed first **[cited, §III-A, §IV]**. Mutation scoring
(Stryker, 2,967 mutants of the shared `SinglePassCompiler`): regression tests left 28
surviving; the fuzzers killed 21 of those **[cited, §V-B, Table III]**. *Steal:* for SW-688
(T9), keep `run --reference` in every comparison. The runtime's lowering and the JS backend
share their erasure decisions (`crates/rt/src/erasure.rs`, module comment: "shared by the JS
backend … and the runtime's lowering") **[checked]**, while the reference run uses the kernel's
own `erase.rs` **[checked: docs/core.md:239]**, so a bug in the shared decisions makes rt, JS and
native agree on a wrong answer and only the reference run tells. The set-order false alarms
shouldn't arise, since Stitchwort's `Map` is ordered by its key's order (DESIGN.md:844, :863)
**[inferred]**. T5's scoreboard is the same experiment as their Table III. *Helps:* SW-688, T5,
T9. *Cost:* none beyond SW-688. *Full text:* read ([PDF](https://www.doc.ic.ac.uk/~afd/papers/2024/ICST.pdf)).

### Content addressing, caching and incrementality

**C11. Unison's content-addressed codebase.** [The big idea](https://www.unison-lang.org/docs/the-big-idea/);
[upgrade how-to](https://www.unison-lang.org/docs/usage-topics/workflow-how-tos/update-dependency-lib-install/).
*Claim:* "we can parse and typecheck definitions once, and then store the results in a cache
which is never invalidated"; renames are instant and non-breaking; two versions of a type
coexist; "A Unison codebase is never in a broken state, even midway through a refactoring"; a
dependency upgrade runs on a temporary branch, opens conflicting terms in the editor, and
`upgrade.commit` merges it **[cited]**. *Steal:* the review side (§5.4): a rename is "same
hash, new name", and a lane's change is a set of hash changes. DESIGN §11 already follows
Unison's cycle hashing **[checked]**. *Cost:* small. *Full text:* read (both pages). Audit: OK
("two versions coexist" is a paraphrase of "multiple versions of 'the same' function or type
floating around").

**C12. Durability in Salsa.** rust-analyzer blog, *Durable incrementality*, 24 Jul 2023
([post](https://rust-analyzer.github.io/blog/2023/07/24/durable-incrementality.html)).
*Claim:* without durability, any edit to `src/lib.rs` revalidated every standard-library
query, "about 300ms"; a version *vector* with one counter per durability level lets stdlib
queries be validated by comparing one number; std is durable, the project volatile, crates.io
in between **[cited]**. *Steal:* language-server.md §4.1 keeps std in memory already
**[checked]**; the rule to keep is "an edit never walks std's entries". *Helps:* SW-31 later
stages. *Cost:* small, later. *Full text:* read (post). Audit: OK.

**C13. Build Systems à la Carte** (**classic**; the vocabulary in-window build work uses).
Mokhov, Mitchell, Peyton Jones, ICFP 2018; JFP 2020. *Claim:* a build system is a scheduler
plus a rebuilder; early cutoff stops a rebuild when a recomputed result is unchanged; a
*verifying trace* stores hashes of the values a task read and re-runs it only when one
differs; *constructive traces* also store results, which a cloud cache needs **[cited]**.
*Steal:* check-cache.md §4.2 is a verifying trace keyed on sources; D280's early cutoff keys on
results. §5.3 asks which result a dependent should key on. *Cost:* none. *Full text:* read
([JFP version](https://www.microsoft.com/en-us/research/uploads/prod/2020/04/build-systems-jfp.pdf)).
Audit: OK (§2.3, §5.2, §5.3).

**C14. Lean's module system.** Lean reference, [Source Files and Modules](https://lean-lang.org/doc/reference/latest/Source-Files-and-Modules/).
*Claim:* "proofs of theorems are in the private scope … both for public and private
theorems"; "Changes to files that affect only non-exported information (e.g. proofs,
comments, and docstrings) will not trigger rebuilds"; definition bodies are private unless
`@[expose]` **[cited]**. *Steal:* a dependent keys on what it can see. Stitchwort's dependents
can see proof bodies today (§5.3). *Helps:* D280, SW-93. *Cost:* design. *Full text:* read
(page). Audit: OK (the first quote is two sentences: "This is because proofs of theorems are in
the private scope. This is the case both for public and private theorems.").

**C15. Lean incremental elaboration.** Lean 4.9.0 release notes, #3940 (2024). *Claim:*
incremental elaboration "into various steps inside of declarations: definition headers,
bodies, and tactics", opt-in per elaborator with `@[incremental]` **[cited]**. *Steal:*
language-server.md §4.2 (level 2) plans per-declaration reuse; splitting a theorem's header
from its body is the next step for long proofs. *Cost:* elaborator work, later. *Full text:*
read (release notes; the PR itself not read). Audit: OK (release notes now at
lean-lang.org/doc/reference/latest/releases/v4.9.0/).

**C16. Mathlib's cache keys.** Lean Zulip, *Coarseness of Mathlib.Cache*, 13 Apr 2023
([thread](https://leanprover-community.github.io/archive/stream/287929-mathlib4/topic/Coarseness.20of.20Mathlib.2ECache.html)).
*Claim:* each file's cache hash mixes a "root hash" of `lakefile.lean`, `lake-manifest.json`
and `lean-toolchain`, so an unrelated manifest change invalidates everything; Lake's traces are
finer; reusing them "would require a refactor of `Lake` itself"; no decision recorded
**[cited]**. *Steal:* for any future shared Stitchwort cache, compute keys with one function
everywhere and keep roots narrow. *Cost:* none now. *Full text:* read (thread). Audit: OK.

### Editors and machine interfaces

**C18. Total type error localisation (Hazel).** Zhao, Maroof, Dukkipati, Blinn, Pan, Omar,
POPL 2024. *Claim:* the marked lambda calculus turns every type error into a *mark* that acts
as a non-empty hole, with a total marking procedure (mechanised in Agda), so checking always
continues; unification errors are localised to type holes using traced provenances, and the
user picks a suggested filling **[cited]**. *Steal:* the principle "an error becomes a hole of
the expected type and checking continues inside the declaration". Stitchwort carries on past
failed *declarations* and already has frozen metavariables for `?` (lsp-goal-holes.md §2)
**[checked]**; whether the elaborator continues *within* a declaration after a type error
wasn't checked **[unverified]**. The calculus is gradual and non-dependent, so this is a
principle, not a recipe. *Cost:* research. *Full text:* read ([hazel.org](https://hazel.org/papers/marking-popl24.pdf)).
Audit: OK. (The within-a-declaration question is still not checked.)

**C19. Typed holes for LLMs (ChatLSP).** Blinn, Li, Kim, Omar, OOPSLA 2024. *Claim:* the
language server supplies the hole's expected type, the definitions of the types it mentions
(retrieved transitively) and relevant function headers from the typing context; "Including
type definitions seem absolutely necessary"; with types, headers increased test performance
"threefold", and up to two rounds of feeding static errors back multiplied performance by 4
(types only) or 1.5 (types and headers), with diminishing returns beyond two rounds; ChatLSP is
a small LSP extension for this **[cited]**. These figures are for the Hazel task; for
TypeScript the with-versus-without-headers ratio was 1.5 (§4). *Steal:* when a `?` goal is reported, also list
the data types its goal and context mention, with constructors (T8). *Helps:* agents writing
proofs; lsp-goal-holes.md. *Cost:* small. *Full text:* read ([arXiv 2409.00921](https://arxiv.org/pdf/2409.00921)).
Audit: MINOR. The threefold and 4× / 1.5× figures were given without saying they are Hazel's.

**C20. Pantograph.** Aniva, Sun, Miranda, Barrett, Koyejo, TACAS 2025. *Claim:* LSP is the
wrong interface for a machine: "The LSP interface requires its user to keep track of
positions of a cursor in text", and there is "no straightforward way to extract tactic
training data"; Pantograph exposes goals as data, lets a client solve goals in any order, and
resumes proofs containing `sorry` **[cited]**. *Steal:* Stitchwort's `--index` JSON already
carries diagnostics with codes and goals (as rendered text, severity `goal`)
(`crates/driver/src/nav.rs:183-195` writes `"severity":"goal"` and `"code"` for each
diagnostic) **[checked]**, so the `check --json`
proposed by the 29 Oct proof-automation.md (its T6, dropped in the 30 Oct redo, wrong claim
1) is half built; goals as structured data are missing. *Cost:* small. *Full text:* read ([arXiv 2410.16429](https://arxiv.org/pdf/2410.16429)).
Audit: MINOR. "Parse messages" was not the paper's claim; the reference for `--index` pointed
at lsp-goal-holes.md:470, which describes the playground's `"goals"` field (stage 2c, WASM),
not `check --index`. The TACAS 2025 venue is not stated in the arXiv copy and wasn't
re-checked.

**C21. coq-lsp.** README ([GitHub](https://github.com/LLM4Rocq/coq-lsp)). *Claim:* re-checks "only
what is necessary, continuously"; on-demand modes "follow the cursor" or "follow the
viewport"; error recovery "integrates with the incremental cache"; an unfinished lemma is
admitted automatically so the rest of the document checks; `fcc` and Petanque give machine
access without an LSP client; MCP "upcoming" **[cited]**. *Steal:* "check what's on screen
first" is low priority while most `aoc` namespaces check in under 0.1 s (the big `Proofs`
namespaces take 0.12–1.37 s; language-server.md §4) **[checked]**; a non-LSP machine entry point is what `--index` already is. *Cost:* small,
later. *Full text:* read (README). Audit: MINOR: the Stitchwort side said all namespaces check in
under 0.1 s.

**C32. Lean 4's infoview and ProofWidgets.** Nawrocki, Ayers, Ebner, *An Extensible User
Interface for Lean 4*, ITP 2023 (LIPIcs 268, 24). *Claim:* UI elements should be
*presentations* that keep a reference to the object shown: "every displayed expression, and
each of its subexpressions, stores a reference to the type-theoretic term it corresponds to",
so hovering shows its type, the values of implicit arguments, or jumps to a definition; "No
extra data is computed eagerly … the UI … fetch[es] information from the language server lazily"
through remote references in JSON-RPC payloads **[cited, §2.1, §4]**. The infoview also shows
goal diffs between successive tactic states and lets the user pin locations **[cited, §2]**.
*Steal:* for the editor, T8's "list the data types a goal mentions" should be a reference per
subterm that the client resolves on demand, not text added to every goal; for agents, who have
no hover, T8's eager list stays right **[inferred]**. Goal diffs (what a step changed) suit
`?` goals before and after an edit. *Helps:* T8, language-server.md, lsp-goal-holes.md.
*Cost:* small to design; LSP work to build. *Full text:* read
([LIPIcs](https://drops.dagstuhl.de/storage/00lipics/lipics-vol268-itp2023/LIPIcs.ITP.2023.24/LIPIcs.ITP.2023.24.pdf);
§1, §2, §4–§6; §3's widget examples skimmed).

### Library maintenance and proof engineering

**C22. Growing Mathlib.** Baanen, Ballard, Commelin, Chen, Rothgang, Testa, CICM 2025. *Claim:*
a rename keeps a deprecation marker "for a grace period of several months"; a renamed file
keeps a stub module so imports don't break; 26 syntax linters; a linter flags raising
`maxHeartbeats` beyond one declaration; benchmarks count instructions, and a bot reports
changes of 5% or more; a sticky PR comment shows "which lemmas were renamed", changed
transitive imports and "changes in technical debt metrics" **[cited]**. *Steal:* the PR
comment, as a lane trust diff (§5.4); deprecated aliases for std renames (no mechanism today:
no `deprecat` in docs/syntax.md or docs/core.md **[checked]**). Stitchwort already benchmarks
counts, not time (docs/testing.md "Benchmarks") **[checked]**. *Cost:* small. *Full text:*
read ([arXiv 2508.21593](https://arxiv.org/pdf/2508.21593)). Audit: OK (§3, §4, §5, §7; the 5%
bot posts to Zulip; still no `deprecat` in docs/syntax.md, docs/core.md or DESIGN.md).

**C23. Sisyphus.** Gopinathan, Keoliya, Sergey, *Mostly Automated Proof Repair for Verified
Libraries*, PLDI 2023 (PACMPL 7, article 107, [10.1145/3591221](https://doi.org/10.1145/3591221)).
*Claim:* given an OCaml function verified in Coq (CFML separation logic) and a new version with
the same specification, Sisyphus builds a proof skeleton from the new code, runs old and new
"on the same randomly generated input" to align their intermediate values, synthesises
invariant candidates from the old proof, and prunes them by *proof-driven testing*: reducing a
higher-order lemma's proof term on concrete inputs exposes subterms whose types are the
invariant at concrete states, which become assertions **[cited, §1–§4]**. On 14 evolved
programs (10 from real libraries) it repaired every proof, with 0–3 admits left per program,
each proved by hand in under 20 minutes, and ran in under 2 minutes on most **[cited, §5,
Tables 2–3]**. Its stated failure mode: when the new proof needs a function or lemma the old
proof never used, the search space has no valid invariant **[cited, RQ3]**. *Steal:* little that
is buildable. Stitchwort's proofs are about pure functions, not loop invariants. The cheap part
is the first step: when a lane rewrites a function that has theorems, run the old and new
versions on the same random inputs (the counterexample search's generators) before re-proving,
so a behaviour change shows up as a counterexample rather than as a proof that won't go through
**[inferred]**. Proof-driven testing needs a checker that reduces proof terms, which
Stitchwort's does (docs/core.md:234) **[checked]**, but nothing here needs it yet. *Helps:* AoC
and std maintenance. *Cost:* research (repair); small (the differential first step). *Full
text:* read ([Ilya Sergey's copy](https://ilyasergey.net/assets/pdf/papers/sisyphus-pldi23.pdf),
25 pp.; §2.2–§4.2 and §5 in full, §3 skimmed). Audit: NOT READ on 29 Oct; the Internet Archive
still has no copy, and dl.acm.org returns 403 to scripts. The first author is the kirancodes
blogger of C10.

### Extraction and the trusted base

**C31. Verified extraction and safe interoperation.** Forster, Sozeau, Tabareau, *Verified
Extraction from Coq to OCaml*, PLDI 2024 (PACMPL 8, article 149). *Claim:* an extraction
pipeline from Coq through MetaCoq's erasure to Malfunction (a thin layer over OCaml's
intermediate language), proved to preserve evaluation; extracted code is not required to be
well-typed OCaml, only to *realise* its type at the interface **[cited, §1, §2]**. Interoperation
with unverified code is proved safe only for *first-order* functions (first-order data in and
out), and the paper shows why: `assumes_purity : (unit → B) → B` relies on its argument
returning the same value twice, so an OCaml closure with a reference cell makes the extracted
code segfault (`Obj.magic`) **[cited, §1.1, §2.4]**. Performance is close to `ocamlopt -O2` and
ahead of CertiCoq on their benchmarks **[cited, §6]**. *Steal:* evidence for a rule Stitchwort
already has. JS exports are "Pure, first-order", functions are "not exportable yet"
(DESIGN.md:30, :801, :850) **[checked]**. If function-typed exports are ever allowed, a JS
callback can be impure or non-terminating, so any dependent type that relies on a function's
results being stable can't be trusted across the boundary **[inferred from §1.1]**; the
decoder-and-precondition design would need a separate argument there. *Helps:* JS extraction
design. *Cost:* none now. *Full text:* read (ACM PDF via the
[Internet Archive](https://web.archive.org/web/2024id_/https://dl.acm.org/doi/pdf/10.1145/3656379);
§1–§2.4 and §6 in full, §3–§5's pass-by-pass proofs skimmed; HAL's `hal-04329663/document`
returned a bot page).

### Agent-driven development

**C26. A C compiler by parallel agents.** Carlini, *Building a C compiler with a team of
parallel Claudes*, Anthropic, 5 Feb 2026 ([post](https://www.anthropic.com/engineering/building-c-compiler)).
*Claim:* "it's important that the task verifier is nearly perfect, otherwise Claude will solve
the wrong problem"; GCC as a known-good oracle let agents split one large failing task; a
`--fast` mode runs a 1% or 10% random sample, deterministic per agent but varying across VMs
so all files get covered; output a few lines with details in a log, `ERROR` and the reason on
one line; regressions near the end needed stricter CI **[cited]**. *Steal:* rotate the sampled
sweeps' offset (§5.4, T4). Stitchwort already has tiers, logs and an oracle evaluator
(docs/testing.md) **[checked]**. *Cost:* small. *Full text:* read (post). Audit: OK (the
regressions were "near the end of the project").

**C27. ImpossibleBench.** Zhong, Raghunathan, Carlini, arXiv 2510.20270 (Oct 2025). *Claim:*
tasks whose tests contradict the specification, so any pass is cheating. Strategies seen:
editing tests (over 79% of Claude models' cheating on Conflicting-SWEbench), overloading
comparisons, recording state across calls, special-casing. Hiding tests cuts cheating "to near
zero" but hurts the real benchmark; read-only tests are "a middle ground" that stops test
edits but not the other strategies; a `flag_for_human_intervention` exit cut GPT-5's cheating
from 54% to 9% (o3: 49% to 12%), with a much smaller effect for Claude Opus 4.1 **[cited]**.
*Steal:* in Stitchwort the "tests" a lane could weaken are must-reject examples, snapshots,
budgets and theorem statements; list every change to them in review (§5.4). *Cost:* small.
*Full text:* read ([arXiv PDF](https://arxiv.org/pdf/2510.20270)). Audit: OK (§4.1, §5; the
"> 79%" covers Claude models and Qwen3-Coder together).

**C28. Error detail for agents.** Krishnamurthi, Flatt, *Type-Error Ablation and AI Coding
Agents*, arXiv 2606.01522 (Jun 2026). *Claim:* 2,400 trials (qwen2.5-coder 14B with aider,
plus two rounds with claude-haiku-4.5) on an ML-style language; detailed messages (the whole
unification stack with locations) "generally improve" agent fix rates; type errors help more
than test failures alone; 97.9% of type-error fixes also passed all tests; "it is worth
considering offering two reporting modes: a terse human mode and a detailed AI mode"; the
authors call the results "preliminary … in a very limited setting" **[cited]**. *Steal:*
Stitchwort has a switch for full terms (`STITCHWORT_FULL_TERMS=1`, docs/core.md:344)
**[checked]**; lanes could set it, and a detailed mode could add the elaborator's unification
trail (T7). *Cost:* small. *Full text:* read ([arXiv 2606.01522](https://arxiv.org/pdf/2606.01522)).
Audit: MINOR: the paper checks out; the docs/core.md line had moved from 340 to 344.

**C29. Compiler loops in Idris.** Li, Krishnamachari, arXiv 2602.11481 (Feb 2026). *Claim:*
GPT-5 solved 22 of 56 Exercism Idris exercises zero-shot (45/50 in Python), and 54 of 56 with a
loop feeding local compilation errors and failed tests; local compiler errors gave the largest
gain **[cited]**. *Steal:* evidence that a dependently typed language with little training
data is workable for agents when compiler feedback is good, which is Stitchwort's situation.
*Cost:* none. *Full text:* read ([arXiv 2602.11481](https://arxiv.org/pdf/2602.11481)). Audit: OK.

## 5. Deep reads

### 5.1 Oracles from the corpus: erase, overwrite, preserve (C1, C2)

**What they do.** Hephaestus and Thalia turn one accepted program into many tests with known
answers. *Erasure*: remove an annotation the checker should infer; the program must still be
accepted. *Overwriting*: replace one type with an incompatible one; the program must be
rejected. Thalia's soundness mode enumerates ill-typed uses of one API rather than picking
at random. The oracles need no reference implementation, which is why they find bugs in mature compilers:
74 of Hephaestus's 156 came from the two mutations and were missed by its generator alone
**[cited]**. (Audit: was "72 of 153", the submission copy's figures.)

**Where Stitchwort is.**

- The elaborator fuzzer mutates tokens (swapped names, changed numerals, deleted and swapped
  lines, dropped annotations) and checks that nothing panics, no `E-INTERNAL`, no kernel
  `E-MALFORMED` or `E-TYPE-MISMATCH` reaches the user, the run finishes, and the cold and warm
  check cache agree (docs/testing.md "Elaborator fuzzing"; `fuzz_elab.rs:534-720`)
  **[checked]**. "Dropped annotations" is erasure without its oracle: the fuzzer doesn't
  require the result to be accepted.
- SW-686 (backlog) plans meaning-preserving rewrites with the oracle "still accepted with the
  same hashes", generalising `pipe_forms`, `named_arguments` and `fmt_hashes`. SW-687 plans
  proof mutation with the counterexample search as oracle **[checked: board]**.
- Content hashes make Stitchwort's erasure oracle *stronger* than Hephaestus's. After an
  implicit argument or annotation is removed, the elaborated declaration should be *the same
  term*, so the hash must not change (names and layout aren't hashed, DESIGN §11)
  **[checked]**. A different hash means the elaborator inferred something else.

**Mapping.** Three oracles over every accepted example, std file and AoC day:

1. **Erase (SW-686).** For each written implicit argument `f [x := e]`, type annotation on a
   `let` or lambda binder, and `: T` ascription, remove it. Oracle: accepted with the same
   hash, or rejected with `E-UNSOLVED` or another documented "can't infer" code, never another
   code. The second branch matters: Stitchwort doesn't promise complete inference, so the
   oracle has to allow honest failure, as Thalia's inference mode only erases what "can be
   inferred by the surrounding context" **[cited]** **[inferred for Stitchwort]**.
2. **Overwrite (SW-687).** For each application argument in an accepted
   declaration, substitute a closed term of a different, non-convertible type taken from a
   small pool (a `Nat` literal, `True`, `"x"`, `[]`, a constructor of an unrelated data
   type). Oracle: rejected, with a type error at that argument. An *acceptance* is a
   soundness lead; a rejection with `E-INTERNAL` or with the kernel's `E-TYPE-MISMATCH`
   reaching the user is an elaborator bug, as in today's oracles.
3. **Preserve (kernel; new).** For each accepted definition `f : A := b`, evaluate `b` with the
   kernel's evaluator under a step budget, read the value back, and check it against `A` with
   the kernel. Do the same for `A` itself (its normal form must still be a type in the same
   universe). Oracle: accepted, or inconclusive on budget. A rejection means the evaluator,
   read-back or checker disagree: a subject-reduction failure. docs/core.md:169 names the
   Danielsson–Geng counterexample to subject reduction that the `unfolding` rule exists to
   prevent **[checked]**, so this class has already occurred once in design.

**Why these, not a generator first.** Hephaestus's two mutations found bugs its generator
alone could not (74 of 156) **[cited]**; ETNA's experience is that generator comparisons are
easy to get wrong **[cited]**. Stitchwort's corpus is large and varied (107 soundness
examples alone, `examples/soundness/`) **[checked]**, and mutating it needs no model of the
language **[inferred]**. (Audit: was 88 on 29 Oct; 30 Oct added 14 programs shaped like 2026's
kernel bugs in other provers, kernel.md T1, and 5 universe-limit examples, SW-902.)

**Assumptions.** (A1) The elaborator is deterministic, so "same hash" is a fair oracle; the
existing cold/warm cache comparison relies on the same thing **[inferred]**. (A2) An
annotation-free form exists for most annotations; where it doesn't, the oracle accepts
`E-UNSOLVED`, so false alarms are bounded. (A3) Budgets: preservation on AoC bodies that
compute large values may mostly come back inconclusive; run it on std and examples first.

**Risks.** Erasure noise: if many erasures give `E-UNSOLVED`, the oracle is weak; measure the
split first. Overwrite needs the substituted term to be *non-convertible* with the expected
type at that position, which needs the elaborator's view of the expected type; doing it at
the token level gives some type-correct "mutations" (a `Nat` where `Nat` was wanted), so
compare types before calling a bug. Preservation on terms with `Quot.sound` can get stuck
(DESIGN §3 "Total") **[checked]**; stuck is not a failure.

**Next step.** T2 (erase and overwrite in `fuzz_elab.rs`, as SW-686/687's first stage) and T3
(preservation sweep). No design note needed for T3; T2's spec should list which syntactic
positions are erased and the pool for overwriting.

### 5.2 Generators for SW-688: three layers and a scoreboard (C2, C4, C5, C6, C8)

**What they do.** Thalia builds small client programs out of library signatures. Frank et
al. generate STLC terms whose functions use their arguments, by choosing types late.
Rustlantis skips the front end and generates the compiler's IR, comparing backends. ETNA
scores generators by how fast they find injected bugs. Fuzz4All uses an LLM as the generator
for languages without one **[cited, all]**.

**Where Stitchwort is.** SW-688 asks for "a type-directed generator of random programs (data,
functions, matches, effects) that must be accepted, run differentially on reference, rt, JS and
native" **[checked: board]**. The differential harnesses exist: `run_reference.rs`,
`run_js.rs`, `crates/rt/tests/machine.rs`, and extraction's 100 random inputs per export
(docs/testing.md) **[checked]**. Random tests use fixed seeds **[checked]**. (Audit: since SW-901,
30 Oct, the extraction snapshot test `generated_code_is_stable` also runs in the merge tier,
split from its `tsc` check, docs/testing.md "Generated code"; the random-input tests are sampled
like the corpus sweeps, every 2nd in daily and every 8th in merge, docs/testing.md:36.)

**Mapping.** SW-688 is two different tools, and the literature says to build them apart:

- **Backends (Rustlantis).** Generate the erased IR (`crates/rt`'s input) directly, with the
  IR interpreter or `run --reference` on a lowered form as the oracle, and run `rt`, JS and
  native on the same program. No type checker in the way, so the generator only has to keep
  programs total and in bounds; Rustlantis keeps its programs free of Undefined Behaviour the
  same way, by tracking every value statically while generating **[cited]**. Print a hash of
  the results and dump in full only on a mismatch, as Rustlantis does. This targets the
  trusted runtime pieces, which is where the lean-zip campaign found its memory bug (C10)
  **[cited]**. Keep `run --reference` in every comparison: rt, JS and native share their
  erasure decisions (`crates/rt/src/erasure.rs`), so a bug there makes them agree on a wrong
  answer, the case fuzz-d's independent interpreter exists for (C33) **[checked; cited]**.
- **Front end (Thalia, Frank).** Generate source programs that call std's API, with types
  drawn from std's signatures, non-local type choice so arguments flow, then run all four
  ways. Frank et al.'s method stops short of polymorphic functions **[cited]**, so dependent
  signatures (`Vec a n`) are drawn from std rather than generated **[inferred]**. The oracle for checking is "accepted"; for running, agreement.
- **Seeds (Fuzz4All).** One agent lane writes a few hundred small programs that use the
  features in docs/guide; they seed SW-689 and the T2 transformations.

Before building, **score what exists** (ETNA): take 20–30 mutants of `crates/core` and
`crates/elab` from `cargo mutants` that the test suite *misses*, and record which fuzzer and
oracle (syntax, formatter, elaborator, kernel, the new T2/T3 oracles) kills each, and how
fast. That says which generator would add the most.

**Assumptions.** (A1) The erased IR is stable enough to generate against; if it changes often,
generating it costs upkeep. (A2) The backends' semantics on the IR are specified by the
reference path (docs/proposals/fast-runtime.md) **[inferred from docs/core.md:239]**.

**Risks.** A generator is a project: Rustlantis's core "was done … for his master thesis"
(Ralf Jung's post) **[cited]**. (Audit: the first version said RustSmith was a thesis too and
cited the Rustlantis paper; neither paper says so.) Expect fuzz blockers: Dafny's fuzzers had
to wait for frequent crash bugs to be fixed before finding anything else (C33) **[cited]**. Time-box it; keep generators deterministic by seed, as existing fuzzers are.

**Next step.** T5 (score with mutants) first; then T9 (IR generator) as a design note.

### 5.3 Cache keys that a proof edit doesn't disturb (C12, C13, C14, C15)

**What others do.** Lean's module system puts every theorem's proof in the private scope, so a
proof edit doesn't rebuild importers **[cited]**. Salsa avoids re-validating stable inputs
(std) with durability levels **[cited]**. Build systems à la carte calls the general idea
early cutoff: a dependent is keyed on its dependencies' *results*, not their sources
**[cited]**.

**Where Stitchwort is.**

- A definition's hash covers its type and body, and references are hashed as their hashes,
  so "changing a body changes its hash and the hash of everything that uses it"
  (docs/core.md "Tests and content hashes") **[checked]**. Theorems are included.
- The check cache keys each namespace on its source and the keys of what it imports, a chain
  (check-cache.md §4.2 item 6). Early cutoff is planned (D280); language-server.md §4.3
  notes "a rewritten proof still changes the theorem's content hash today, so the cutoff
  wouldn't fire for it" **[checked]**.
- The test cache keys each test on its content hash (`driver.rs:934-935`) **[checked]**, so a
  proof edit in a std lemma re-runs every test whose hash reaches that lemma.
- Dependents can see proofs: "only three things look inside a proof: a `case` on it …, `J`,
  and a comparison" (docs/core.md:234); proof-irrelevance.md §7.7 says that under its D1′ a
  proof can still compute in a dependent's check, so its body may still matter, but "a
  proof's body can never change a test's result, because proofs are erased when running"
  **[checked]**.
- Every key includes the compiler fingerprint (check-cache.md §3.1 and §4.2 item 1; DESIGN §11
  says every key has the compiler version and the test-result key a fingerprint of the
  compiler's source) **[checked]**. In a repo where most
  lanes change the compiler, the caches help AoC and editor runs within one build, not across
  lanes **[inferred]**.

**Mapping.** Two separate steps, with different risk:

1. **Test results keyed on the erased program (small, safe).** Compute a second hash of the
   test after erasure (`erase.rs`), with references hashed by *their* erased hashes, and key
   test results on that. Editing a proof then never re-runs a test. proof-irrelevance.md §7.7
   already suggests this "later optimisation" **[checked]**. Tests run erased: on the fast
   runtime's erased IR, or on the evaluator with erasure on (`let _erasing =
   g.erasure.running()`, `crates/driver/src/driver.rs:1241-1243`), where `J` on an erased proof
   takes its base and a proof argument isn't computed (docs/core.md:239) **[checked]**. So a
   proof's body can't change a test's result. (Audit: the first version said tests ran on the
   checker's evaluator without erasure, so a proof edit could unstick a test, and left that open
   as T10's first question. Wrong: DESIGN §3's "may stop at a term that isn't a value" is
   about the checker, which doesn't erase. Also, a test whose value isn't `True` is reported
   failed, not inconclusive, `driver.rs:1246-1249`.)
2. **Theorem bodies opaque across namespaces (design, decision).** If a namespace's
   dependents may not look inside its theorems' proofs, their keys can use the theorem's
   *type* hash, and early cutoff (D280) fires on proof edits, as in Lean. Opacity only makes
   the checker accept less, so it can't be unsound **[inferred]**. The cost is programs that
   rely on a proof computing across namespaces (a `J` on a lemma that reduces to `rfl`, a
   `case` on a single-constructor proof). Lean pays the same cost and offers `@[expose]`
   **[cited]**. Measure first: instrument the kernel to count, per declaration, unfoldings of
   a theorem from another namespace, over std, examples and aoc.

**Assumptions.** (A1) Library lemma edits are frequent enough to matter. AoC `Proofs`
namespaces are mostly leaves, so this pays mainly for std work **[inferred]**. (A2) Opaque
theorems across namespaces would be per-namespace, not per-file; namespaces.md defines the
unit **[checked]**. (A3) SW-93 (D1′) doesn't add K-like `J` (proof-irrelevance.md §5.2 rules
it out **[checked]**), so with SW-93 built, proofs *still* compute and opacity would still be
needed for the cutoff.

**Risks.** Two hashes per declaration doubles a subtle piece of trusted cache code; the
erased-hash test needs its own differential test (same results with either key). Opacity
across namespaces is a language change; it needs a design note and Matt's decision (D1931).

**Next step.** T10 (erased-hash test key; D2030) and T11 (measurement only).

### 5.4 A trust diff for agent lanes (C11, C22, C26, C27, C28)

**What others do.** Mathlib's bot posts one comment per pull request: renamed lemmas,
changed transitive imports, technical-debt metrics (C22). ImpossibleBench shows agents under
pressure edit tests, special-case, or overload comparisons, and that an explicit "flag it"
exit reduces this for some models (C27). Carlini: "the task verifier is nearly perfect,
otherwise Claude will solve the wrong problem" (C26) **[cited, all]**.

**Where Stitchwort is.** Lanes are reviewed by Opus line by line before merging
(docs/workflow.md "Handing a task to DeepSeek", step 3) **[checked]**. What a lane could
weaken, deliberately or not, without failing a test:

- a theorem's *statement* (the proof then gets easier);
- a must-reject or soundness example, or its expected error code (DESIGN §13);
- an error-message or hash snapshot, regenerated by `task snap:*`;
- a budget or limit (`rewrite_budget`, `instance_budget`, step limits; check-cache.md §4.2)
  or a test's sample stride;
- an axiom or a trusted extra (`stitchwort axioms`; kernel.md §5.4) **[checked: sources named]**.

Content hashes make most of this mechanical. The hasher already hashes a type with
references replaced by their hashes, as part of a declaration's hash (docs/core.md "Tests and
content hashes") **[checked]**; hashing the type on its own makes "the statement of
`Day05.total` changed" a hash comparison, and "renamed `foo` to `bar`" is "same hash, new
name", as in Unison (C11).

**Mapping.** `task review:trust BASE=main` (a script over two checkouts, or a CLI command
reading two indexes) prints, for the lane's diff:

1. theorems whose *type* hash changed, with old and new statements;
2. declarations renamed (hash kept, name changed), and removed names with no rename;
3. files changed under `examples/reject`, `examples/soundness`, and snapshot files;
4. changed budgets, limits, strides and `#[ignore]`s in tests;
5. the axiom and assumption report for every changed theorem (with the trusted extras
   kernel.md §5.4 lists).

The reviewer reads this first. None of it fails the lane; it moves weakening from "noticed if
the reviewer reads closely" to "listed".

Two smaller steals from C26 and C28. **Rotating samples:** the merge and daily sweeps take
"every `daily_stride`-th item in sorted order", a fixed sample (docs/testing.md "How a tier is
chosen") **[checked]**, so items outside it are tested only in the full tier, which runs only
when Matt asks. An offset from the date (printed, and settable for reproduction) would cover
the whole corpus over a few days at the same cost (T4). **Detailed mode for agents:** the
agent lanes could run with `STITCHWORT_FULL_TERMS=1` and, later, a flag that adds the
elaborator's unification trail to type errors, per Krishnamurthi and Flatt (T7).

**Assumptions.** (A1) Agents keep writing most code and proofs here (docs/workflow.md)
**[checked]**. (A2) The cost of reviewing is the bottleneck, not the cost of writing; the
memory notes and workflow.md suggest it is **[inferred]**. (A3) A type hash needs a small addition: `hash.rs` exposes only
whole-declaration hashes today (`def_hash`, `data_hash`, `hash.rs:90`, `:159`) **[checked]**.

**Risks.** A list nobody reads; keep it short and empty in the common case. Renames detected
by hash miss a rename that also changed the body; report removed names separately. They also
miss renamed data types and constructors: data types are nominal, so their hash includes their
name and their constructors' and fields' names (docs/core.md "Tests and content hashes")
**[checked]**, and renaming one changes the hash of everything that uses it. (Audit: added; the
first version said only that names aren't hashed, which holds for definitions.)

**Next step.** T1 (trust diff), T4 (rotating samples), T7 (detail mode trial).

## 6. Steal next

Ranked by value over effort. "Value" counts open tickets and risks addressed.

| Rank | Idea | Source | Helps | Cost |
|---|---|---|---|---|
| 1 | Lane trust diff: changed statements, renames, must-reject/snapshot/budget changes, axioms | C22, C26, C27, C11 | review; soundness of agent work | small (tooling) |
| 2 | Erase and overwrite oracles over the corpus in `fuzz_elab` | C1, C2 | SW-686, SW-687 | tooling |
| 3 | Kernel preservation sweep (evaluate, read back, re-check) | classic; §5.1 | kernel soundness; complements kernel.md T1 (built 30 Oct: 14 must-reject programs and `kernel_bugs_2026.rs`) | small |
| 4 | Rotating sample offset for the sampled sweeps | C26 | coverage between full runs | small |
| 5 | Score fuzzers and oracles against missed `cargo mutants` mutants | C5 | choosing SW-688/689 work | small |
| 6 | Weak-theorem detection: mutate AoC/std functions, re-check their theorems | C9 | spec quality; AoC proofs | tooling |
| 7 | Agent detail mode (`STITCHWORT_FULL_TERMS=1` in lanes; unification trail later) | C28, C29 | agent repair loops | small |
| 8 | Goals carry the data types they mention (eagerly for agents; as on-demand references in the editor) | C19, C20, C32 | agent proofs; proof-automation T5 | small |
| 9 | SW-688 split: IR-level backend generator, always compared with `run --reference`; std-API source generator; agent-written seeds | C6, C33, C2, C4, C8 | SW-688, SW-689 | tooling (design note) |
| 10 | Test cache keyed on the erased program | C14, proof-irrelevance.md §7.7 | warm test runs after proof edits | small (the open question is answered: tests run erased) |
| 11 | Measure cross-namespace proof unfolding; then decide opaque theorems | C14 | D280 early cutoff | small (measure), design (rule) |
| 12 | Deprecated aliases for std renames | C22, C11 | std churn | small |

Not recommended now: a Hazel-style total error recovery (C18, research); a shared or remote
check cache (DESIGN §11 forbids trusting one; C16's pitfalls); verified implementations
(kernel.md covers checkers; Candle, row 45); package versioning (no packages yet, multi-file.md
§1); Sisyphus-style proof repair (C23: built for separation-logic loop invariants; its first
step, running old and new versions of a changed function on the same random inputs, is cheap
and could join T6 later); function-typed JS exports (C31: keep them out until there's an
argument for impure callbacks); an `explain E-CODE` command like Zerolang's (row 55; small,
but no evidence yet that agents here need it).

## 7. Proposed tickets

Label `research` on each. Not added to the board.

**T1. A trust diff for lane review.** A task (`task review:trust BASE=main`) that compares the
lane's branch with its base and lists: theorems whose type hash changed (with old and new
statements); declarations renamed (same hash, new name) and names removed; changed files under
`examples/reject`, `examples/soundness` and snapshot folders; changed budgets, limits, sample
strides and ignored tests; the axiom report for each changed theorem. Empty output in the
common case. Mathlib's PR summary comment and ImpossibleBench's findings on agents editing
tests are the model. Refs: docs/research/infrastructure.md §5.4.

**T2. Erase and overwrite oracles (first stage of SW-686 and SW-687).** In `fuzz_elab.rs`, two
new mutation kinds over accepted inputs. Erase: remove a written implicit argument, binder
annotation or ascription; oracle: same hash, or a documented can't-infer code. Overwrite: put
a closed term of a non-convertible type in one argument position; oracle: rejected with a type
error at that position (an acceptance is a soundness lead). Report the share of erasures that
end in `E-UNSOLVED` to calibrate. Hephaestus found 74 of its 156 bugs this way. Refs: §5.1.

**T3. Kernel type-preservation sweep.** For every accepted definition in std, examples and a
sample of AoC: evaluate the body with the kernel's evaluator under a step budget, read it back,
re-check it against the declared type; do the same for the type's normal form. Rejection is a
bug; running out of budget or getting stuck on an opaque proof is inconclusive. Daily tier,
sampled like the other sweeps. Refs: §5.1; docs/core.md (subject reduction and `unfolding`).

**T4. Rotate the sampled sweeps.** `tier_sample` picks every n-th item from a fixed start.
Take the start from the date (or `STITCHWORT_SAMPLE_OFFSET`), print it on failure, so a week
of daily runs covers the whole corpus at the same cost. Carlini's agent harness samples this
way. Refs: §5.4; docs/testing.md "How a tier is chosen".

**T5. Score the fuzzers with mutants.** Take 20–30 `cargo mutants` mutants of `crates/core`
and `crates/elab` that the test suite misses; run each fuzzer and oracle (syntax, formatter,
elaborator, kernel, T2, T3) against each with a time cap; record which kills which. Output a
table here, as ETNA scores generators. Decides what SW-688 and SW-689 should target. Refs:
§5.2.

**T6. Weak-theorem detection over AoC and std.** MutDafny's idea: mutate a *function* that
has theorems (change a constant, a comparison, a branch, swap arguments) and re-check its
theorems; a mutant whose theorems all still check marks a statement that doesn't pin down the
behaviour. Start with one AoC year. Output: a list for review. Complements SW-687, which
mutates proofs. Refs: §4 C9.

**T7. Trial a detailed error mode for agent lanes.** Run lanes with `STITCHWORT_FULL_TERMS=1`
for a week and note whether reports improve; if so, design a `--detail` flag that adds the
elaborator's unification steps to `E-TYPE-MISMATCH` and `E-UNSOLVED`. Krishnamurthi and Flatt
found detailed unification context helps agents fix type errors. Refs: §4 C28.

**T8. Goals list the data types they mention.** When a `?` goal is reported (CLI, index JSON),
add the definitions (constructors and fields) of the data types in the goal and its context.
In the editor, attach a reference to each subterm instead and fetch its type or definition on
hover, as Lean's infoview does (C32). ChatLSP found type definitions the most useful
context for a model filling a hole. Pairs with goals as structured data in the index JSON
(C20; the 29 Oct proof-automation.md T6, dropped in the 30 Oct redo) and with
proof-automation.md T5. Refs: §4 C19, C20.

**T9. Design note: SW-688 as an IR-level backend generator.** Generate `crates/rt`'s erased IR
directly (total, in-bounds programs), run it on rt, JS and native with the reference path as
oracle, as Rustlantis does with MIR; the reference run stays in every comparison because the
backends share their erasure decisions (fuzz-d, C33). Leave source-level generation (from std's
signatures, Thalia; with non-local type choice, Frank et al.) to a second stage. Refs: §5.2.

**T10. Key test results on the erased program.** Add an erased hash per test (references
hashed by their erased hashes), key the test cache on it, and keep a differential test (same
results with either key). Tests already run erased (`driver.rs:1241-1243`), so a proof body
can't change a result; the audit answered the old first question. Refs: §5.3;
proof-irrelevance.md §7.7; D2030.

**T11. Measure cross-namespace proof unfolding.** Instrument the kernel to count, per
declaration, unfoldings of theorems from other namespaces (by `case`, `J` or comparison), over
std, examples and aoc. Input for D1931. Refs: §5.3.

**T12. Deprecated aliases for std renames.** A way to keep an old std name for a while that
warns and names the new one; with content hashes the alias is the same declaration. Mathlib
keeps these for months. Refs: §4 C22.

## 8. Decisions

**D1930. Make the trust diff (T1) a standard part of reviewing every lane?** Assumptions:
agents keep writing most code and proofs; reviewing, not writing, is the bottleneck; the list
is usually empty. [Yes: build T1, then add "read the trust diff first" to docs/workflow.md.]

**D1931. Should theorems be opaque to other namespaces, so a proof edit stops at its
namespace (Lean's module-system rule)?** Assumptions: T11 finds few cross-namespace proof
unfoldings; std lemma edits are common enough to matter; an explicit opt-out like Lean's
`@[expose]` is acceptable. [Not yet: run T11 and T10 first, decide on the numbers.]

**D1932. For SW-686/687/688, do the corpus oracles (T2, T3) and the mutant scoreboard (T5)
before building any generator?** Assumption: mutating Stitchwort's large example and AoC
corpus reaches more code per hour than a new generator, as the Rust results suggest. [Yes.]

**D2030. Key test results on the erased program (T10), so editing a proof never re-runs a
test?** (Added in the 30 Oct audit.) Assumptions, in full: (1) every test runs erased, on the
fast runtime's erased IR or on the evaluator with erasure switched on
(`crates/driver/src/driver.rs:1229-1243`; tests of partial code too, `crates/driver/src/run.rs:545`),
so no proof body or type argument is computed and a
proof edit can't change a test's outcome; (2) the erased hash of a test can be computed from
`erase.rs`'s decisions, with each reference hashed by that declaration's own erased hash, and
it changes whenever anything that runs changes, including a definition's body, a data type's
constructors and the evaluation modes already in the key; (3) a second hash per declaration in
trusted cache code is acceptable if a differential test (the same results with either key, over
the test corpus) guards it, as check-cache.md §5.4 guards the check cache; (4) the saving
matters, because std lemma edits re-run many tests today (unmeasured). [Recommended: yes, with
the differential test; measure first how many tests a typical std proof edit re-runs.]

## 9. Sources not reached

### Full text not reachable (for Matt to fetch)

Carded but **NOT READ**; nothing in §5–§8 rests on it.

| Card | Title | DOI | URLs tried, and what each returned |
|---|---|---|---|
| C3 | Sotiropoulos, Su, *Enumerating Ill-Typed Programs for Testing Type Analyzers* (Eris), PLDI 2026 | 10.1145/3808320 | 29 Oct: pldi26.sigplan.org page (search summary only); github.com/hephaestus-compiler-project/eris-pldi-eval README (artifact, no paper); zenodo.org record 19033618 (seeds and evaluation only). 30 Oct: Semantic Scholar API (DOI found, `openAccessPdf` is the ACM DOI, GOLD, CC-BY); dl.acm.org/doi/pdf/10.1145/3808320 with curl and with the fetch tool (403 both); web.archive.org `2026id_` copy (404) and the Wayback availability API (no snapshot); theosotr.github.io (publication entry links only the DOI and the tool's repository; `assets/pdf/pldi26.pdf` 404); github.com/hephaestus-compiler-project/eris README (no paper); arXiv title search (nothing) |

Why ask: it is the published form of T2's overwrite oracle (enumerate ill-typed variants at
every program location; 64 bugs in Kotlin, Scala, Groovy and the Checker Framework, 51 of them
unsoundness, per the PLDI page's abstract **[unverified]**), so it would shape T2's design. It
is open access at ACM, so it should open in a browser; only scripts are refused.

### Screened, not carded, not read

Each row's verdict in §3 says why it was dropped or left as "maybe" without its full text.

| Source | DOI or URL | Tried |
|---|---|---|
| Rust-twins, ASE 2024 (row 12) | 10.1145/3691620.3695059 | the ACM landing page through the Internet Archive (`2024id_`, `2025id_`: the abstract and references, no PDF); not open access; dropped on the abstract |
| Buzdalov, TyDe 2024 extended abstract (row 8) | icfp24.sigplan.org talk page | the page has no attached file; no DOI or preprint found (Q30); dropped |
| Rows 66–70 (Isabelle testing 2026, *Faults in Our Formal Benchmarking*, Trivet, Sembid, DTest) | in §3 | search summaries only; dropped as out of scope, so not fetched |

### Search coverage

- 29 Oct: **the web search budget ran out after 27 queries.** 30 Oct: twelve more (Q28–Q39,
  §2). Covered now: CakeML and translation validation (nothing in-window on CakeML; Q32), Dafny
  tooling (Q33, giving C33), matklad's blog (nothing in-window, Q34), semantic versioning (Q35),
  proof-assistant testing 2025–26 (Q36), the Lean FRO roadmap (Q37), compiler-testing venues
  2025 (Q38), F-IDE and HATRA (Q39).
- Still not searched: MetaRocq updates beyond kernel.md; Agda interface files; F\*'s tooling;
  Mokhov's later work; Nix content-addressed derivations; Dhall's hash-pinned imports; Elm's
  enforced semantic versioning (Q35 found nothing for typed functional languages); the
  CoqPL/RocqPL, Lean workshop and ITP/CPP 2022–26 programmes year by year. A refresh should
  start with these.
- dl.acm.org returns 403 to scripts. The Internet Archive's `id_` copies worked for Rustlantis
  and Forster et al., and had nothing for Sisyphus or Eris. Authors' pages had PACMPL papers
  (lemonidas.github.io, hazel.org, ilyasergey.net, theosotr.github.io), and guessing the file
  name on an author's site found Sisyphus. The UCL Discovery copy of Hephaestus is the
  anonymous submission, with different numbers from the published paper (C1): check the
  version of any repository copy.
- `pdftotext` (`nix shell nixpkgs#poppler-utils`) worked for every PDF; the earlier lanes'
  failure was the package name (`poppler_utils` has been renamed).
