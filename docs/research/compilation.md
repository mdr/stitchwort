# Literature trawl: compilation and runtime

**Counts: screened 52; carded 23; read in full 22; not read 1 (C22; listed in §9 with two
screened-only items whose full text wasn't reached).**

**Audited 30 Oct 2026 against full texts: 12 OK, 8 minor (fixed), 1 wrong (fixed), 0 can't
verify** (of the 21 cards first marked read). C8 was wrong: `Array.groupBy` is the thesis
author's own example, not Lean's library function. C12, first NOT READ, was then read in an
Internet Archive copy of the ACM PDF. Each fixed card ends with "Audit:". Two file references
were wrong (`specialise.rs` for known-argument specialisation, which `opt.rs` does; "no borrow
concept", but `native_abi.rs` helpers take borrowed arguments). Both are corrected below.

*SW-894, cluster 6. Trawled 29 October 2026 against `main` at `5c25a1b5`. Research only: no
code changed, no tests run. Window: 2022 onwards (D1831); older work appears only where
in-window work or a system we compare with relies on it, marked **classic**. Effect-runtime
compilation is in [effects.md](effects.md) and isn't repeated here.*

Labels: **[checked]** read in the full text of the source named (a paper, a post, a release
note) or in Stitchwort's code and docs at the place given; **[cited]** read in a web page
fetched in full on 29 Oct 2026 (through a fetch tool that summarises, so quotes are as
returned and not re-checked letter by letter); **[inferred]** my reasoning, not tested;
**[unverified]** a claim I haven't read in a full source (used only as context, never to
support a recommendation).

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

Stitchwort has already taken most of the standard ideas. fast-runtime.md and
native-compilation.md surveyed the runtimes of Lean, Koka, Idris 2, Agda, Roc, Unison and
Effekt in October, and the machine has them **[checked]**:

- an erased IR with saturated calls and eval/apply (`crates/rt/src/machine.rs` header);
- register bytecode with moves on last use, early drops, and Perceus/Lean-style reuse
  tokens (`code.rs` header, `Unpack`, `CtorReuse`, `DropReuse`);
- small numbers inline with a `BigUint` fallback (`value.rs`);
- a simplifier that inlines, copies recursive functions for known arguments and resolves
  known constructors (`opt.rs`; `specialise.rs` is the separate empty-row specialisation of
  effect-polymorphic code);
- TRMC by destination passing (`trmc.rs`), state handlers run as loops (`fusion.rs`);
- Cranelift native code that keeps the machine's RC and reuse decisions (`crates/native`).

So the new material from 2022 to 2026 that adds most is in five places the existing notes
don't cover. Ranked by value against effort:

1. **Arrays with in-place update, specified as lists (SW-112).** Lean's runtime updates an
   array in place when it isn't shared (Ullrich and de Moura, **classic**, §7.1).
   Stitchwort already specifies `Text` as a list and runs it compactly (compact-text.md).
   The same for arrays is a design note, then a runtime change. Huisinga's thesis (2023)
   shows the risk to design against: in the thesis's own `Array.groupBy` example, every
   `push` copies the array because it also sits in a map (deep read 5.1).
2. **Measure reference counting before borrowing.** Lean infers borrowed parameters; a 2026
   paper removes 75–100% of increments against Perceus and gains 1.48× (Brandon et al.,
   OOPSLA 2026). But borrowing has costs the papers name: Koka declined Lean's inference
   because it is "not safe for space" (Lorenzen and Leijen, ICFP 2022), and it blocked 6.4%
   of in-place updates in one benchmark of the 2026 paper. Also, *removing* it made one Lean
   benchmark faster (const_fold, 0.90); the paper doesn't say why. Stitchwort clones every read that isn't the last. So:
   count increments and decrements first, then decide (deep read 5.2).
3. **Don't store forced indices.** `VCons` stores its length `n` at run time **[checked]**
   (docs/core.md; vec.md measured 5–10% per operation). Brady, McBride and McKinna
   (**classic**) drop such a field and recover it from the index the eliminator is given,
   saving 10–20% memory on vectors. That only helps where the length is already at hand
   at run time, which needs checking (deep read 5.3).
4. **Know what the dispatch loop can still give (SW-813).** Tail-call dispatch in Rust ran
   1.5–2× faster than a `match` loop natively but 1.2–4.6× *slower* in Wasm engines, and
   needs nightly Rust (Keeter 2026). CPython's version gained 1–5% against a good baseline
   (Elhage 2025); Wizard's threaded dispatch, 14% (Titzer, OOPSLA 2022). Dispatch is about
   19% of the machine's time (native-compilation.md §1.2). So the playground keeps the loop,
   and SW-813 starts from the call path (deep read 5.4).
5. **Small numbers in generated JS.** The JS backend makes every `Nat` a `bigint`. Day 2's
   brute force took 66.8 s under `--js` against 23.1 s on the machine **[checked]**
   (fast-runtime.md, stage 3). Scala.js measured `BigInt` longs 60× slower than its own
   (2018). The machine's rule (a word, else a bignum) carries over to JS (deep read 5.5).

Smaller steals: gate benchmarks on instruction counts, not seconds, on a loaded machine
(C24; SW-659); test shift natives at and past the word width (C20; SW-808); check where
reuse tokens are placed against Koka's fragility examples (C4); a "runs in place" report
(C5); unboxed scalar fields, already measured at 5× on `Set` (C13).

What doesn't transfer: monomorphisation over types (types are erased, values uniform);
laziness (First-Order Laziness, ICFP 2025); uniqueness *types* (Futhark, Granule, Linear
Haskell), since Stitchwort's reuse is dynamic and must stay invisible to proofs; lazy
reference counting (C7), which bounds pauses rather than saving time; a Wasm backend for the
playground, which still needs an explicit stack of its own for deep recursion (C19).

Three decisions for Matt (§8): D1920 (arrays: a design note), D1921 (count RC operations),
D1922 (small numbers in JS).
## 2. Method and queries

### 2.1 Stitchwort read first

README.md; DESIGN.md §13 (trusted base); docs/core.md (erasure, JS representations,
natives); docs/evaluator-speed.md; docs/proposals/fast-runtime.md (all, including stages 1–4
as built and the decisions D381–D389), native-compilation.md (§0, §1, §2.7 table, N4 as
built, D1250–D1253), native-only.md (§0), native-numbers.md, compact-text.md (summary, stage
1, the comparison table), vec.md (measurements), docs/comparisons/aoc-2024-day04-community.md
§5. Code headers: `crates/rt/src/{value,code,machine,trmc,erasure}.rs`,
`crates/native/src/n1.rs` (registers and counting), `crates/elab/src/std/Map/Raw.sw`,
`std/Vec/Vec.sw`. Tickets SW-112, 554, 562, 593, 605, 659, 662, 663, 808, 813, 814, 861,
868. bench/baseline.toml.

### 2.2 Queries (29 Oct 2026)

The session's shared web-search budget ran out after 36 queries, before the planned
sweep of Unison, Idris 2, MLKit, deforestation and benchmarking papers (§9). Fetches of
known URLs still worked. Rerun these quarterly, restricted to the new months.

| # | Query | Yield |
|---|---|---|
| Q1 | `Lorenzen Leijen reference counting frame limited reuse ICFP 2022` | ICFP 2022 paper, TR |
| Q2 | `"The Functional Essence of Imperative Binary Search Trees" PLDI 2024` | paper |
| Q3 | `Better Defunctionalization through Lambda Set Specialization PLDI 2023 Roc` | paper; Roc's use |
| Q4 | `tail-calling interpreter CPython 3.14 performance musttail dispatch` | CPython 3.14, Elhage, Jin |
| Q5 | `Lean 4 new compiler LCNF code generator 2025 release reference counting` | 4.22, 4.30 notes; FRO roadmap |
| Q6 | `wasm_of_ocaml WasmGC Vouillon performance 2024` | ML 2024 talk, Tarides posts |
| Q7 | `Lorenzen Leijen Swierstra "Fully in-Place Functional Programming" ICFP 2023 FIP` | FP² |
| Q8 | `Koka "first-class constructor contexts" … Lorenzen 2024 2025` | TRMC JFP 2025 |
| Q9 | `Roc language compiler rewrite Zig 2025 reference counting in-place List update` | secondary only |
| Q10 | `Deegen JIT-capable VM generator LuaJIT Remake Xu Kjolstad 2024 interpreter` | arXiv, OOPSLA 2026 |
| Q11 | `Titzer "fast in-place interpreter for WebAssembly" OOPSLA 2022 Wizard` | paper |
| Q12 | `Idris 2 erasure quantitative type theory compilation runtime paper 2023 2024` | Allais ESOP 2023 |
| Q13 | `Lean 4 Array in-place update reference count unique destructive update functional arrays paper` | beans; Huisinga thesis; Zulip |
| Q14 | `Hoot Guile Scheme WebAssembly GC tail calls Wingo 2024 performance` | slides, manual |
| Q15 | `"The Simple Essence of Monomorphization" OOPSLA 2025 Lutze` | paper |
| Q16 | `Effekt LLVM backend ICFP 2025 … reference counting` | Muhcu et al. (effects cluster) |
| Q17 | `Agda erasure modality "@0" compiler backend runtime irrelevance Danielsson 2023` | Agda docs |
| Q18 | `benchmarking language runtimes instruction counts noisy machines cachegrind …` | tak, rustls ci-bench, pythonspeed |
| Q19 | `JavaScript BigInt performance small integers V8 …` | V8 blog, TC39 issue |
| Q20 | `Lorenzen PhD thesis 2025 Edinburgh …` | not found |
| Q21 | `"destination calculus" OR "destination-passing" Bagrel …` | OOPSLA 2025, JFLA 2024, thesis |
| Q22 | `GHC WebAssembly backend tail calls JavaScript backend …` | IOG post, web.dev |
| Q23 | `OCaml unboxed types layouts Jane Street 2024 …` | ML 2022, ML 2023 |
| Q24 | `"Lambda the Ultimate SSA" MLIR functional CGO 2022 Lean` | paper |
| Q25 | `CertiCoq-Wasm verified WebAssembly backend Coq CPP 2025` | paper |
| Q26 | `"Verified Extraction from Coq to OCaml" PLDI 2024 …` | paper |
| Q27 | `"Being Lazy When It Counts" …` | FLOPS 2024 |
| Q28 | `"Linearity and Uniqueness: An Entente Cordiale" ESOP 2022` | paper |
| Q29 | `WebAssembly stack switching proposal phase 2025 2026 browser shipping JSPI` | intent threads (mixed) |
| Q30 | `Koka Perceus borrowing inference … Lean borrowed parameters` | Lean `InferBorrow`; OOPSLA 2026 |
| Q31–36 | wasmi register bytecode; makepad stitch; borrows OOPSLA 2026; First-Order Laziness; Rust `become`; Futhark uniqueness | as named |

Full-text routes for known titles (not searches): Semantic Scholar's API by DOI, the
authors' pages, the Internet Archive, Kent's and KIT's repositories, the HAL API.

### 2.3 Full texts

PDFs were downloaded with `curl` (Microsoft Research and some others only answer a browser
user agent) and turned into text with `nix shell nixpkgs#poppler-utils -c pdftotext -layout`
(the package name has a hyphen; `poppler_utils` is gone from nixpkgs). **This worked** for
every PDF that downloaded except Brady, McBride and McKinna 2003, whose text layer is
garbled; it was read from rendered page images. Web pages were fetched in full with a fetch
tool.

Following Matt's reading protocol, every card's source was read in full before its card was
finalised. The long texts were read in parallel by four reading sub-agents, each told to
read every line and report claims with section numbers, quotes and all numbers; I read
myself the parts each deep read rests on (the abstracts, introductions and evaluation
sections of fiptree, Allais, Deegen, CertiCoq-Wasm, Beans and Lam and Parreaux, and the
Stitchwort code). Where the extracted text garbled a figure (the borrows paper's Fig. 9,
FP²'s Fig. 11, fiptree's Fig. 4, wasmi's charts), the cards use only numbers stated in prose.

## 3. Screened list

Hooks: **A** arrays and in-place update (SW-112), **R** reference counting and memory, **I**
interpreter speed (SW-813), **E** erasure and representation, **J** JS backend, **W** Wasm
and the playground, **S** specialisation and fusion, **B** benchmarking (SW-659), **T**
trust of backends.

| # | Paper or source | Venue | Hook | Verdict |
|---|---|---|---|---|
| 1 | Ullrich, de Moura: Counting Immutable Beans (§7.1 arrays; §5.2 borrows) | IFL 2019, **classic** | A/R | **keep** (deep reads 5.1, 5.2) |
| 2 | Lean 4 new compiler (LCNF): on by default in 4.22 (Aug 2025), C emission from LCNF and reset/reuse with "exponential-code prevention" in 4.30 (May 2026) | release notes | R/S | **keep** |
| 3 | Lean 4.30: user borrow annotations `(x : @&Ty)` kept by borrow inference; `Lean.Compiler.LCNF.InferBorrow` | release notes, API docs | R | **keep** (deep read 5.2) |
| 4 | Brandon, Driscoll, Dai, Ragan-Kelley, Milano, Aiken: Fully Automatic Type Inference for Borrows with Lifetimes | OOPSLA 2026 | R | **keep** (deep read 5.2) |
| 5 | Lorenzen, Leijen: Reference Counting with Frame Limited Reuse | ICFP 2022 | R | **keep** |
| 6 | Lorenzen, Leijen, Swierstra: FP²: Fully in-Place Functional Programming | ICFP 2023 | A/R | **keep** |
| 7 | Lorenzen, Leijen, Swierstra, Lindley: The Functional Essence of Imperative Binary Search Trees | PLDI 2024 | R | **keep** (SW-814) |
| 8 | Leijen, Lorenzen: Tail Recursion Modulo Context (JFP extended version, first-class contexts) | JFP 2025 | S | maybe (TRMC built; effects.md has §6) |
| 9 | Lorenzen, Leijen, Swierstra, Lindley: First-Order Laziness | ICFP 2025 | — | drop (strict language) |
| 10 | Lam, Parreaux: Being Lazy When It Counts (constant-time RC) | FLOPS 2024 | R | maybe |
| 11 | Huisinga: static uniqueness analysis for Lean 4 | KIT master's thesis 2023 | A | **keep** |
| 12 | Allais: Builtin Types viewed as Inductive Families | ESOP 2023 | A/E | **keep** (deep reads 5.1, 5.3) |
| 13 | Brady, McBride, McKinna: Inductive Families Need Not Store Their Indices | TYPES 2003, **classic** (cited by 12) | E | **keep** (deep read 5.3) |
| 14 | Tejiščák: erasure inference (cited by 12 as [Tej20]) | ICFP 2020, **classic** | E | maybe |
| 15 | Agda run-time irrelevance (`@0`; GHC backend drops erased constructor fields) | Agda docs 2.6.1–2.8 | E | maybe |
| 16 | Brady: Idris 2, QTT in Practice | ECOOP 2021, **classic** | E | drop (Stitchwort erases by sort, not quantity) |
| 17 | Marshall, Vollmer, Orchard: Linearity and Uniqueness: An Entente Cordiale | ESOP 2022 | A | maybe; not carded (full text reached late, at kar.kent.ac.uk, and not read) |
| 18 | Futhark uniqueness types and their limits with higher-order functions (blog, 2022) | blog | A | drop (static types; Stitchwort's reuse is dynamic) |
| 19 | Roc: RC with in-place `List` update; compiler rewrite in Zig (2025) | secondary only | A/R | maybe, **[unverified]** |
| 20 | Brandon, Driscoll, Dai, Berkow, Milano: Better Defunctionalization through Lambda Set Specialization | PLDI 2023 | S | **keep** (C12; read at the audit) |
| 21 | Lutze, Schuster, Brachthäuser: The Simple Essence of Monomorphization | OOPSLA 2025 | S | drop (types are erased; no unboxed type parameters) |
| 22 | Xu, Kjolstad: Deegen, a JIT-capable VM generator (LuaJIT Remake) | arXiv 2024, OOPSLA 2026 | I | **keep** |
| 23 | Titzer: A Fast In-Place Interpreter for WebAssembly | OOPSLA 2022 | I | maybe |
| 24 | wasmi 0.32: register-based bytecode in a Rust interpreter | blog 2024 | I | **keep** |
| 25 | makepad `stitch`: a Rust Wasm interpreter dispatching by sibling calls | README 2024 | I | **keep** (with 26) |
| 26 | Keeter: A tail-call interpreter in (nightly) Rust | blog, Apr 2026 | I/W | **keep** (deep read 5.4) |
| 27 | CPython 3.14 tail-calling interpreter (Elhage; Jin "No longer sorry") | blogs 2025 | I | **keep** |
| 28 | Rust explicit tail calls (`become`), nightly; stabilisation a 2026 project goal | Rust docs, blog | I | **keep** (with 26) |
| 29 | Larose, Kaleba, Burchell, Marr: AST vs. Bytecode: Interpreters in the Age of Meta-Compilation | OOPSLA 2023 | I | maybe, **[unverified]** (search budget ran out) |
| 30 | Bhat, Grosser: Lambda the Ultimate SSA (MLIR backend for Lean) | CGO 2022 | — | drop (Cranelift chosen, D1251) |
| 31 | Copy-and-patch compilation (CPython 3.13 JIT) | OOPSLA 2021, **classic** | I | drop (native code exists) |
| 32 | Forster, Sozeau, Tabareau: Verified Extraction from Coq to OCaml | PLDI 2024 | T | maybe; not carded (full text not reachable, §9) |
| 33 | Meier, Jensen, Pichon-Pharabod, Spitters: CertiCoq-Wasm | CPP 2025 | T/W | **keep** |
| 34 | wasm_of_ocaml (Vouillon, ML 2024; first release Feb 2025) | talk, blogs | W | **keep** |
| 35 | Guile Hoot on WasmGC and tail calls (Wingo, 2023–2024) | slides, manual | W | **keep** |
| 36 | WasmGC and Wasm tail calls are Baseline (Dec 2024) | web.dev | W | **keep** (fact) |
| 37 | JSPI and stack switching in browsers, 2025–2026 | intent threads | W | maybe, partly **[unverified]** |
| 38 | GHC JS backend: Haskell stacks run by a scheduler loop | IOG blog 2023 | J/W | maybe, NOT READ (C22; 404) |
| 39 | GHC Wasm backend: tail calls opt-in | project page | W | drop |
| 40 | V8: Adding BigInts; Scala.js `Long` as `BigInt` "really, really bad" | V8 blog; TC39 issue | J | **keep** (deep read 5.5) |
| 41 | Eisenberg, Dolan, White: Unboxed Types for OCaml | ML 2022 | E | maybe (a talk abstract only; no paper exists) |
| 42 | Eisenberg: Layout Polymorphism | ML 2023 | E | drop (no type parameters at run time) |
| 43 | Bagrel, Spiwack: Destination Calculus | OOPSLA 2025 | S | drop (TRMC built) |
| 44 | Bagrel: Destination-passing style in Haskell (JFLA 2024) and thesis (2026) | JFLA, thesis | S | drop |
| 45 | Muhcu et al.: Multiple Resumptions and Local Mutable State, Directly | ICFP 2025 | — | drop here (effects.md #43) |
| 46 | Gaißert et al.: Tracing JIT for Effects and Handlers | OOPSLA 2025 | — | drop here (effects.md #44) |
| 47 | Instruction counts for CI benchmarks: tak docs; rustls `ci-bench`; pythonspeed "CI for performance" | docs, blog | B | **keep** |
| 48 | GHC issue 15333 (a trace call shifted Cachegrind counts) | issue | B | maybe (blocked by a bot page, §9) |
| 49 | Lean FRO year 3 roadmap: stack allocation, better RC, ownership-aware compilation | roadmap | R | maybe |
| 50 | Effekt thesis topic: constant-time reference counting (2026) | thesis offer | R | drop |
| 51 | Koka's mimalloc (Leijen et al. 2019), relied on by 7 and 10 | **classic** | R | drop (the CLI already uses mimalloc, evaluator-speed Q2) |
| 52 | Huet's zipper / Minamide's holes, as used by 7 | **classic** | S | drop |

52 screened: 23 keep, 14 maybe, 15 drop (audit recount of the table above; the first version
said 21, 17 and 14). 23 carded (some cards cover two or three rows).

## 4. Cards

Each card says whether its full text was read, and from where. One card is **NOT READ**
(C22): it stays as a pointer, but nothing in §5–§8 rests on it.

**C1. Ullrich and de Moura, "Counting Immutable Beans", IFL 2019 (classic).**
[arXiv 1908.05647](https://arxiv.org/abs/1908.05647). Claim: reset/reuse on the
"resurrection hypothesis" (§1); borrowed parameters inferred by a fixed point that starts
with every parameter borrowed and marks one owned when it is reset, passed to an owned
position, applied or partially applied (§5.2, Fig. 4); a tail call that would need a `dec`
after it makes the parameter owned (§5.3). Runtime: pointer fields first, then unboxed
scalars; arrays and strings built in, and `Array.write a i v` "will destructively update
and return the array a if it is not shared"; persistent values need no count (§7.1). Fig. 6
ablation (normalised time, base = 1.00): without borrowing, binarytrees 1.14, deriv 1.16,
rbmap 1.07, but const_fold 0.90 (faster); without reuse, rbmap 3.23, const_fold 1.64
**[checked]**. Steal: arrays (5.1), parameter borrowing (5.2), scalar layout (C13). Cost:
runtime change each. Full text: read (arXiv v3).

**C2. Lean 4's new code generator (LCNF).**
[4.30.0 notes](https://lean-lang.org/doc/reference/latest/releases/v4.30.0/),
[`InferBorrow`](https://lean-lang.org/doc/api/Lean/Compiler/LCNF/InferBorrow.html). Claim:
the reset/reuse pass moved to LCNF and "prevents exponential code generation unlike the old
one", with "a ~15% decrease in binary size" (#12665); user borrow annotations `(x : @&Ty)`
are kept where possible, but "the compiler prioritizes preserving tail calls over preserving
borrow annotations" (#12830); `@[export]` functions may not borrow (#13017) **[cited]**. `InferBorrow`: owned for correctness at tail calls and reset/reuse;
owned for speed when passed to an owned parameter, in a partial application, or as a
constructor argument; user annotations override the performance heuristics, not the
correctness rules **[cited]**. Steal: (a) a size counter for lowered code, since `opt.rs`
copies functions per known argument (64 copies of up to 200 nodes) **[checked]**; (b) an
annotation as the escape hatch for 5.2. Cost: small; (b) part of 5.2. Full text: read (both
pages). Audit: the #12830 quote was a paraphrase, now replaced by the release note's words.

**C3. Brandon, Driscoll, Dai, Ragan-Kelley, Milano and Aiken, "Fully-Automatic Type
Inference for Borrows with Lifetimes", OOPSLA 2026.** [DOI
10.1145/3798221](https://doi.org/10.1145/3798221). Claim: borrows with lifetimes for all
variables, inferred without annotations; where a program can't be typed, inference
"inserts a handful of reference count operations" (abstract). If every mode is owned it
"amounts to the Perceus RC technique" (§3.1). Against Perceus *without reuse*, dups fell
75–100% on 11 of 13 benchmarks, 1.48× geomean; calc and parse_json went from millions of
dups to none and ran 2.5–3× faster (§7) **[checked]**. Costs they name: "borrowing past a
mutation point may inhibit RC-1 optimizations": 6.4% of in-place array updates in unify fell
back to a copy (§7.1); reuse is not implemented; first order only (closures removed first by
lambda set specialisation, §6.1) **[checked]**. Steal: the evidence that RC is often the
largest cost left once a runtime is otherwise lean, and the warning that borrowing fights
in-place update. Cost: research project. Full text: read (Internet Archive copy of
theory.stanford.edu's PDF).

**C4. Lorenzen and Leijen, "Reference Counting with Frame Limited Reuse", ICFP 2022.**
[PDF](https://www.microsoft.com/en-us/research/uploads/prod/2023/07/flreuse.pdf). Claim:
reuse placed before RC insertion is fragile: their example `match x { Just(_) -> match y { 0
-> x; _ -> Just(y) } }` makes the token always null under the older algorithm, and inlining
`is-red` loses reuse in red-black insertion under both older algorithms (§3) **[checked]**.
Drop-guided reuse runs after dup/drop insertion and turns a `drop(x)` into a reuse when a
same-size allocation follows; it is proved frame-limited (Theorem 5). "Unrestricted borrow
inference [Ullrich and de Moura 2019]" is not a frame-limited transformation, and "such
transformations should therefore be avoided in practice" (§1); borrowing "is generally not
frame-limited", Lean's inference "is not safe for space", so "Koka currently has no
automatic borrow inference" (§4.2) **[checked]**. Up to 1.6× over Koka's old reuse (§6). Steal: (a) check where `code.rs` places `Unpack`'s token relative to
the cell's last use, against example A; (b) a test that `opt.rs`'s inlining doesn't lose
reuse. Cost: small (review and tests). Full text: read (MSR copy, fetched with a browser user
agent). Audit: the paper's words "is not frame limited" are about reuse algorithm D, not
borrow inference; the quotes are now the ones about borrowing.

**C5. Lorenzen, Leijen and Swierstra, "FP²: Fully in-Place Functional Programming",
ICFP 2023.** [TR](https://www.microsoft.com/en-us/research/uploads/prod/2023/05/fip-tr-v2.pdf).
Claim: functions passing a `fip` check can be compiled "to never (de)allocate memory or use
unbounded stack space" when their owned arguments are unique (§1); `fbip` allows freeing and
any stack depth; `fip(n)` allows n allocations (§1.3); constant stack needs every recursive
call within a recursive group to be a tail call (§2.6, Theorem 4) **[checked]**.
The uniqueness test stays dynamic: a shared argument is copied, so fip code runs from non-fip
code. The std-reuse variant cost about 1% over no reuse when nothing could be reused (§6)
**[checked]**. Steal: a *report* of which functions run in place (T8), not a type. Cost:
small (diagnostic). Full text: read (MSR TR v2, 85 pages incl. appendices). Audit: the
first quote was reworded ("and use bounded"); it is now verbatim, with section numbers.

**C6. Lorenzen, Leijen, Swierstra and Lindley, "The Functional Essence of Imperative
Binary Search Trees", PLDI 2024.** [PDF](https://homepages.inf.ed.ac.uk/slindley/papers/fiptree.pdf).
Claim: bottom-up tree algorithms from a defunctionalised CPS transform (zippers that reuse
each visited node's cell), top-down ones from first-class constructor contexts; Koka "always
outperform[s] C" on move-to-root, splay and zip trees, and red-black trees are about 25%
(top-down) and almost 50% (bottom-up) slower than C with the same allocator ("equalized" C).
For bottom-up the authors believe C wins by bailing out early on the way up; for top-down
"the reason ... is less clear" (§7) **[checked]**. Weight-balanced trees aren't treated. Steal: for SW-814, an
`insertWith` that walks down with a zipper the reuse tokens fill, so the machine runs it in
constant stack with each node reused. Rebalancing on the way up is the red-black case, the
one that gained least **[inferred]**. Cost: std change plus re-proving `balance` lemmas.
Full text: read (the PDF linked above). Audit: the early-exit reason was given for both
red-black variants; the paper gives it only for bottom-up.

**C7. Lam and Parreaux, "Being Lazy When It Counts", FLOPS 2024.**
[PDF](https://lptk.github.io/files/ctrc-2024-05-09.pdf). Claim: push a dead object on a
free list without touching its fields; drop its fields when the cell is next allocated; no
cascade, so allocation and freeing take bounded time, with no leak if every cell has one size
(32 bytes: an 8-byte header and 24 bytes of payload); larger objects are split into chained
segments (§2) **[checked]**. On par with Koka on most benchmarks, slower on nqueens and
rbtree-ck, faster on lam and life; more memory in general; Koka's 10 µs pauses on freeing
large structures disappear (§3) **[checked]**. Steal: not now. The machine's frees are a
work list (`value.rs`) and dropping was 11% of the `Set` profile (native-compilation.md
§1.2); this would bound pauses, not save time, and `Fields` are arrays of any length.
Full text: read.

**C8. Huisinga, "Static Uniqueness Analysis for the Lean 4 Theorem Prover", master's
thesis, KIT, 2023.** [PDF](https://pp.ipd.kit.edu/uploads/publikationen/huisinga23masterarbeit.pdf).
Claim: for arrays "the only alternative to an in-place update is a full copy", so users see
"huge disparities in runtime when referential uniqueness is violated by accident" (abstract,
§1). The example is an `Array.groupBy` the thesis itself writes (§2.1: "our implementation
of `Array.groupBy` is actually an example of an imperative implementation that is
unexpectedly inefficient"): after `RBMap.find?` the group array has two references, so each
`push` copies it, and "our `Array.groupBy` implementation is accidentally quadratic". The
"common solution" is an `RBMap.update` that erases the map entry before updating (§2.4)
**[checked]**. A uniqueness type system is proposed, and users must be able to "fall back to
this manual type-less mode" of runtime uniqueness (§3.1); it is implemented as a separate
checker, "not yet integrated" into Lean, with no benchmarks and no uniqueness in higher-order
functions (§5, §8) **[checked]**. Steal: the failure mode 5.1 must design against, and its
exact shape (an array stored in a `Map`). Cost: reading. Full text: read (the KIT PDF linked
above). Audit: WRONG as first written. It called this "Lean's own `Array.groupBy`" and the
erase-first fix "the workaround" in Lean's library. The thesis presents both as its own
illustration and doesn't say Lean's library has the bug.

**C9. Allais, "Builtin Types viewed as Inductive Families", ESOP 2023.**
[arXiv 2301.02194](https://arxiv.org/abs/2301.02194). Claim: a record of an efficient
runtime encoding plus a quantity-0 invariant (`record Vect n a { encoding : List a; 0 valid
: length encoding === n }`), smart constructors, and a view family so users match as if on
the inductive family; complexity "entirely predictable" (§3, §5) **[checked]**. Erasure alone
"is intrinsically limited to transformations that preserve the type's overall structure"
(§2.1), and swapping proven code for "a wildly different untrusted counterpart" is "not
scalable" (§2.2) **[checked]**. Limits: the view's computation laws hold only
propositionally; bit primitives had to be postulated (App. A). No benchmarks. Steal: (a) the
view pattern as the user's interface to an array (5.1); (b) the argument *against* trusted
natives, which Stitchwort answers by binding natives to content hashes and testing them
against their definitions (compact-text.md) **[checked]**. Full text: read.

**C10. Brady, McBride and McKinna, "Inductive Families Need Not Store Their Indices",
TYPES 2003 (classic, via C9).** Claim: *forcing*: a constructor argument that appears as a
pattern variable in the constructor's result indices needn't be stored; it is "retrieved in
constant time by pattern matching on the indices" passed to the eliminator; *detagging* and
*collapsing* go further (§3–6). Memory: "a 10-20% saving" for vector operations, over 80%
for a typechecker (§8) **[checked]**. Steal: 5.3. Cost: lowering change. Full text: read
(the text layer is garbled; read from page images rendered by the reading sub-agent).
Audit: the card named no source. The PDF is Brady's own copy,
`eb.host.cs.st-andrews.ac.uk/writings/types2003.pdf`, through the Internet Archive (the
publisher's copy is closed, per Unpaywall). The quotes were re-read from rendered pages 7, 8
and 14. Published in TYPES 2003, LNCS 3085 (2004).

**C11. Agda's run-time irrelevance.**
[docs](https://agda.readthedocs.io/en/latest/language/runtime-irrelevance.html). Claim:
`@0` values "are not present at run time"; the GHC backend compiles `_∷_` to "a datatype
where the cons constructor takes only two arguments"; Agda's analysis can sometimes erase
without annotations, but a mark "ensures that it is erased without relying on the analysis"
**[cited]**. Steal: the explicit-mark alternative to 5.3, a language change. Full text: read
(the docs page).

**C12. Brandon et al., "Better Defunctionalization through Lambda Set Specialization",
PLDI 2023.** [DOI 10.1145/3591260](https://doi.org/10.1145/3591260). Claim: every function
type carries a *lambda set* (the lambdas that can reach it), inferred by a polymorphic type
system, so specialising a higher-order function to its call site's lambdas is type
monomorphisation. Then lowering turns function values into sum types and calls into matches.
Unlike C++/Rust templates it "never falls back to traditional dynamic function
representations" (§1, §2). Inference is proved sound and complete in Isabelle/HOL. Top-level
`def`s, or strongly connected groups of them, are the unit of specialisation (§3, §6.3).
Lambda sets must be hoisted into named, memoised terms, or their size grows exponentially
(§6.1). On six benchmarks the speedup is up to 6.85× under MLton, 3.45× under OCaml and
78.93× in Morphic (abstract, §7; Fig. 11's per-benchmark bars came back scrambled, so only
these maxima are used) **[checked]**.
C3 uses it to remove closures before inferring borrows (C3 §6.1) **[checked]**. Stitchwort's
`opt.rs` does a bounded form for known arguments: it copies a recursive global with the known
argument substituted, up to 64 copies of up to 200 nodes (`Simp::specialise`) **[checked]**.
Steal: nothing ranked now. It is the general form of what `opt.rs` does for one known
function, and a direction for SW-813's closure-heavy programs (Day 19's 11 M closure calls)
if `opt.rs`'s bound proves too tight **[inferred]**. Cost: research project. Full text: read
(the ACM PDF, through its Internet Archive capture of 30 Mar 2025, found at the audit).
Audit: first NOT READ. It also named `specialise.rs`, which specialises effect-polymorphic
code to the empty row; known-argument copying is in `opt.rs`.

**C13. Unboxed scalar fields (C1 §7.1).** Claim: Lean stores scalar fields as raw bytes
after the pointer fields, and boxes them only to pass to polymorphic code **[checked]**
(C1). Stitchwort's cell is `Rc<[Value]>` of 24-byte values (`value.rs`) **[checked]**, and
native-compilation.md's hand translation of the `Set` insert to Rust took 0.68 s with the
machine's boxed numbers against 0.12 s with numbers unboxed in the nodes (§0) **[checked]**.
That note already lists the change as "later, separately". (Audit: the first version didn't
say these are timings of hand-written Rust, not of the machine.) The steal is only the layout rule: scalars after pointers, so freeing
walks a prefix. (Jane Street's "Unboxed types for OCaml", ML 2022, has no paper, only a talk
abstract and an RFC; not read.) Cost: runtime change, both runners. Full text: C1 read.

**C14. Xu and Kjolstad, "Deegen", arXiv 2411.11469v2 (OOPSLA 2026).**
[arXiv](https://arxiv.org/abs/2411.11469). Claim: each bytecode "is implemented by a
stand-alone machine function, and control transfer is implemented by tail calls", with VM
state pinned to registers through LLVM's GHC calling convention, quickening and inline
caches (§3, §6) **[checked]**. The generated Lua interpreter is 179% faster than PUC Lua and
31% faster than LuaJIT's hand-written interpreter (§8.3), with garbage collection off in all
three; there is **no ablation**, so the share of each technique is unknown; x86-64 only
**[checked]**. Steal: the checklist for SW-813 (quickening is what `Test` already is).
Neither tail calls nor pinned registers are available in stable Rust or in Wasm.
Full text: read (arXiv v2, not the camera-ready).

**C15. wasmi 0.32 (2024).** [blog](https://wasmi-labs.github.io/blog/posts/wasmi-v0.32).
Claim: moving a Rust interpreter from stack to register bytecode made it "up to 5" times
faster; recursive Fibonacci "has not significantly improved"; dispatch is a loop over a
`match`, "a black box concerning the generated machine code", which the author suspects for
its weaker Apple silicon results. CoreMark: wasmi 0.32 at 1,577 on an M2 Pro against stitch
3,056 and Wasm3 2,931 **[cited]**. Steal: evidence that the register step (done in Stitchwort)
was the big one, and that calls didn't gain from it. Full text: read (the post; chart images
not readable).

**C16. Keeter, "A tail-call interpreter in (nightly) Rust", April 2026.**
[post](https://www.mattkeeter.com/blog/2026-04-05-tailcall/). Claim (table in 5.4):
tail-call dispatch with `become` is 1.5–2× faster than a `match` loop natively and 1.2–4.6×
slower in Wasm engines; it needs nightly Rust and, on x86, `extern "rust-preserve-none"`;
x86 code still spills **[cited]**. Steal: the measurement that settles the playground
question. Full text: read.

**C17. CPython's tail-calling interpreter (Elhage; Jin, 2025).**
[Elhage](https://blog.nelhage.com/post/cpython-tail-call/),
[Jin](https://fidget-spinner.github.io/posts/no-longer-sorry.html). Claim: the first
"10-15%" was "primarily due to inadvertently working around a regression in LLVM 19";
against a good baseline it "drops to 1-5% or so" (Elhage); about 5% over computed gotos on
macOS AArch64, and 15–20% with MSVC over the *switch-case* interpreter, where Jin's guess is
that tail calls "reset compiler heuristics to sane levels" (Jin) **[cited]**. Elhage: "It's
easy to get impressive-looking results if you're comparing against a poorly-tuned baseline".
Steal: the caution for SW-813. Full text: read (both posts; Elhage's tables came back
scrambled). Audit: the MSVC figure's baseline is a switch-case loop, the same shape as the
machine's `match`, so it is the closest to Stitchwort's case of these numbers.

**C19. Wasm as a playground target: WasmGC, tail calls, Hoot, wasm_of_ocaml.**
[web.dev](https://web.dev/blog/wasmgc-wasm-tail-call-optimizations-baseline),
[Hoot 0.8 status](https://files.spritely.institute/docs/guile-hoot/0.8.0/Status.html),
[wasm_of_ocaml since 6.1](https://ocaml.org/backstage/2026-04-16-wasm-of-ocaml-what-changed-since-6-1).
Claim: WasmGC and tail calls became Baseline on 11 Dec 2024 **[cited]**. Hoot: "As of Wasm
3.0, there is no way to capture stack frames", so it keeps an explicit stack by making every
call a tail call, which "adds significant runtime overhead" **[cited]**. wasm_of_ocaml: host
GC, no custom collector; effects through JSPI (slow when used for control flow) or CPS;
native stack switching "is not yet in stable browser releases"; the only speed figure is
second-hand ("2x-8x" over js_of_ocaml at Jane Street) **[cited]**. Steal: nothing yet. A
Wasm backend would need its own stack for deep non-tail recursion, which is the machine's
advantage in the browser (D1252). Full text: read (the three pages).

**C20. Meier, Jensen, Pichon-Pharabod and Spitters, "CertiCoq-Wasm", CPP 2025.**
[PDF](https://www.cl.cam.ac.uk/~jp622/certicoq-wasm.pdf). Claim: a verified Wasm backend,
Wasm 1.0 plus tail calls, with no garbage collection (a bump pointer "never decreased",
memory capped at 1,920 MB); 63-bit integers boxed in linear memory (§2.1) **[checked]**.
Verifying the primitive-integer operations "identified a corner case which led to an
unsoundness in Coq's vm_compute" (coq/coq#19402, not described in the paper), and found that
WasmCert modelled shifts "like a C shift" where Wasm takes the amount modulo the width
**[checked]**. On Node, 42% faster than the C and Rust routes, about level with Malfunction
(§3). Steal: when SW-808's shift and bitwise natives come, test shift amounts at and past
the word width in every runner: the corner where two independent teams' semantics disagreed.
Cost: small (tests). Full text: read.

**C21. `BigInt` costs in V8.** [TC39 issue 117](https://github.com/tc39/proposal-bigint/issues/117),
[V8 blog](https://v8.dev/blog/bigint). Claim: Scala.js mapped its 64-bit `Long` to `BigInt`
and SHA-512 ran 5,630,597 µs/op against 89,810 for its own `Long`, "a whopping 60 times
slower"; a V8 engineer: "every BigInt is allocated as an object" and "a 60x performance
difference is certainly plausible" (Feb 2018) **[cited]**. The V8 blog gives the heap
representation and says the implementation is "not particularly optimized"; it has no
comparison with small integers **[cited]**. Both are from 2018, so the gap today is
unmeasured. Steal: 5.5. Full text: read (both pages).

**C22. GHC's JS backend: stacks in the backend (IOG, 2023). NOT READ.** The post returned
404 (§9). Not used.

**C24. Instruction counts as the benchmark metric.**
[tak methodology](https://tak.jdx.dev/guide/methodology),
[rustls ci-bench](https://github.com/rustls/rustls/blob/main/ci-bench),
[pythonspeed](https://pythonspeed.com/articles/consistent-benchmarking-in-ci). Claim: "Gate
on instruction counts. Report wall time without gating on it"; Cachegrind counts varied
0.008–0.027% on a quiet host and 0.011–0.021% "under heavy CPU contention", while
wall-clock medians "moved by roughly 150%" (tak) **[cited]**. tak's page says of itself
"These docs are currently AI slop and have not been fully reviewed", so its numbers are weak
evidence. Counts don't account for "cache misses and branch mispredictions", so wall time is
kept beside them (rustls) **[cited]**. Two GitHub Actions VMs gave instruction counts within
12 of 2.27 billion, while five timed runs spread 1.5% on the first VM and about 3.7% on the
second, which also ran about 5% faster (pythonspeed) **[cited]**. Stitchwort's notes
agree: native-only.md called its timings at load 21–38 "rough" and its instruction counts
"steady to 0.1%"; evaluator-speed.md read retired instructions from `/usr/bin/time -l`
**[checked]**. Steal: T1. Cost: small. Full text: read (three pages; GHC #15333 was blocked,
§9). Audit: "32 stress workers" belongs to tak's separate allocation-count experiment, not
to these figures. The pythonspeed spread was within each VM, not between VMs. tak's
disclaimer was missing.

**C25. Titzer, "A Fast In-Place Interpreter for WebAssembly", OOPSLA 2022.**
[arXiv 2205.01183](https://arxiv.org/abs/2205.01183). Claim: interpreting Wasm in place with
a side table is an order of magnitude cheaper to set up than rewriting (§4.2). Speed: the
rewriting interpreter wasm3 is fastest; the others, Wizard included, are "typically 2×-3×
slower" (§4.4.2). Tuning (§3.4): threaded dispatch 14% on average (29% at most); dropping
value tags 8%; tuned against untuned 20–60% **[checked]**. Steal: the size of the dispatch
lever measured in one more interpreter (14%), which fits 5.4. Full text: read (arXiv v1).

## 5. Deep reads

### 5.1 Arrays with in-place update, specified as lists (C1, C9, C5, C8; SW-112)

**What others do.** Lean's runtime has an array kind, and `Array.write a i v` "will
destructively update and return the array a if it is not shared"; array updates and
reset/reuse "complement each other", so `map (Array.map inc) xs` on an unshared list of
arrays updates everything in place (C1 §7.1) **[checked]**. That in Lean's logic `Array` is a
structure around a `List` I know only second-hand **[unverified]**, but compact-text.md
records the same split for Lean's `String` **[checked]**. Allais (C9) gives the general
method for a dependently typed language: a record of the efficient encoding plus an erased
invariant, smart constructors, and a view so users match as if on the inductive family
**[checked]**. Huisinga (C8) shows the failure that matters, with an `Array.groupBy` the
thesis writes as an illustration: it looks the group up in an `RBMap`, so the array has two
references and every `push` copies it, "accidentally quadratic". The thesis's fix is to erase
the map entry first (an `RBMap.update`) **[checked]**. FP² (C5) keeps the uniqueness test dynamic and costs about 1% when nothing can
be reused **[checked]**.

**How it maps onto Stitchwort.** The pattern is built once already. Compact text keeps
`Text` as a list of characters in the kernel, stores it compactly underneath, and pins each
native to the content hash of the definition it replaces, tested against that definition
(compact-text.md, stage 1, "Binding") **[checked]**. That binding is Stitchwort's answer to
Allais's objection to "a wildly different untrusted counterpart" (C9 §2.2): the native is
trusted, but checked against the definition it replaces. An array would be the same move:

- **Specification:** `type Array a = MkArray (toList: List a)` (or with `Vec a n` inside),
  with `get`, `set`, `push`, `length` defined on the list. Every `List` lemma applies.
- **Machine:** a new `Value` variant (say `Array(Rc<Vec<Value>>)`) and natives for those
  definitions, bound by content hash. `set` uses `Rc::get_mut`: in place if unique, else a
  copy, as `Unpack` already decides for cells (`code.rs`, "Moves and reuse") **[checked]**.
  The machine's moves on last use are what keep a threaded array unique **[inferred]**.
- **Native code:** the same natives through `native_abi` helpers.
- **JS:** a JS array, copied on `set`, unless the backend tracks uniqueness. It has no
  reference counts, so `set` would be O(n) there **[inferred]**. This is the largest open
  question.
- **Kernel:** nothing new. The checker runs the list definitions.

**Expected gain, with the evidence.** The AoC 2024 day 4 notes measured the direct grid
program at 0.91 s (Map) and 2.69 s (list walk) under `run` against 0.20 s for ours, and
23× and 110× slower natively on a 560 × 560 grid (§5) **[checked]**; they say "every
newcomer's first grid program will look like `MapGrid`". The notes' own guess is that an O(1)
array would bring those programs within a small factor of ours **[unverified]**. SW-112's
22 Oct note (D427) records that 2025's day 4 didn't need it **[checked]**.

**Risks.**

- *Assumption: users thread arrays linearly.* If an array is also stored in a `Map` (C8's
  exact case), each `set` silently copies it. Mitigation: a counter of copies made by `set`
  in the run statistics, and T8's "runs in place" report.
- *Assumption: JS may be slow for arrays.* If JS must match, it needs RC emulation or a
  persistent vector: more design.
- Proofs: arrays are lists to the checker, so closed computations over large arrays in
  proofs stay as slow as lists.
- Each native joins the trusted list in DESIGN.md §13, with a differential test against its
  list definition, as text's did.

**Next step.** The design note SW-112 already asks for, with this recommendation to evaluate
(ticket T6). Decision D1920.

### 5.2 Reference counting, then borrowed parameters (C1, C2, C3, C4)

**What others do, and what they warn.** Lean infers borrowed parameters by a fixed point
that starts "all borrowed" and marks a parameter owned when it is reset, passed to an owned
position, applied, or partially applied; a tail call that would need a `dec` after it makes
the parameter owned (C1 §5.2–5.3) **[checked]**. Lean's new compiler keeps the pass, and
since 4.30 lets users write `@&`, with tail calls taking priority over the annotation (C2)
**[cited]**. Brandon et al. (C3) infer borrows for all variables, not just parameters, and
remove 75–100% of increments on 11 of 13 benchmarks against Perceus without reuse, 1.48×
geomean **[checked]**.

Three costs are measured or argued in the same papers **[checked]**:

- **Borrowing blocks in-place update.** C1's heuristic keeps a parameter owned when it is
  reset, because borrowing would "prevent reset and reuse" (C1 §5.2). Lean's own ablation:
  removing borrowing made const_fold *faster* (0.90) while it slowed binarytrees (1.14) and
  deriv (1.16) (C1 Fig. 6). The paper doesn't explain const_fold; that lost reuse is the
  cause is my guess **[inferred]**. In C3, "borrowing past a mutation point may inhibit RC-1
  optimizations": 6.4% of array updates in unify fell back to a copy (§7.1).
- **Borrowing can raise peak memory.** "Unrestricted borrow inference" is not
  frame-limited, and "such transformations should therefore be avoided in practice"; it "is
  not safe for space", and "Koka currently has no automatic borrow inference" (C4 §1, §4.2).
  A borrowed list stays alive while the callee builds something else. (C3 measured this:
  only unify's peak memory rose, by 2.5%, C3 §7.1.)
- **Borrowing and reuse interact.** Lean forbids reuse through a borrow; C3 didn't
  implement reuse at all.

**How it maps onto Stitchwort.** The bytecode passes call arguments as a register list; a
register with the `MOVE` bit is moved, otherwise cloned (`code.rs`: `Ops`, `MOVE`)
**[checked]**. A clone of an `Rc` is an increment, and the callee drops its copy, a
decrement. Native code copies these decisions exactly (`n1.rs` header: "every move, clone
and drop is the bytecode's", n1.rs:87) **[checked]**. Compiled functions have no borrowed
parameters: a call's arguments are moved or cloned, and nothing in `code.rs` marks a
parameter borrowed **[checked]**. (Audit: the first version said there was "no borrow
concept" at all. But some `native_abi.rs` helpers do take arguments borrowed, for example
the text at `t`, native_abi.rs:2150, and the function value at `k`, native_abi.rs:2506.
That is a convention for runtime helpers, not borrowed parameters of user code.) Where reuse matters most (`merge`, `map`), the argument
is passed on its last use and is already moved, so borrowing wouldn't help there and would
hurt if it stopped reuse **[inferred]**. Where it would help is a structure read but not
consumed: a tree passed to `Map.Tree.get` in a loop, a list passed to `List.length` and then
used **[inferred]**.

**Expected gain.** Unknown, which is the point of the first step. Bounds: in the `Set`
profile, dropping values was 11% and allocation 7% of the time (native-compilation.md §1.2)
**[checked]**; C3 measured 1–3 ns per dup and drop pair saved in compiled code **[checked]**,
against about 6 ns per bytecode instruction on the machine. A guess for parameter borrowing
on the machine: 0–10%, possibly negative where it costs reuse **[inferred]**.

**Risks.**

- Every recorded allocation trace changes once (the native agreement tests compare traces
  with the machine's event for event, native-compilation.md N4) **[checked]**; both runners
  change together, so they still agree.
- The effect runtime holds continuations that own what they capture; a borrow must not
  escape into a `Call`'s continuation.

**Next step.** Ticket T2: count increments and decrements per run on the bench programs,
`Set` and day 4, split by whether the callee only read the value. Design only if that share
is large, with Koka's frame-limited rule and Lean's "owned if reset" rule as constraints.
Decision D1921.

### 5.3 Don't store forced indices (C10, C9, C11)

**What others do.** Brady, McBride and McKinna: a constructor argument that appears as a
pattern variable in the constructor's result indices needn't be stored; it is "retrieved in
constant time by pattern matching on the indices" given to the eliminator; for `Vect`, `::`
then stores only the element and the tail. They report "a 10-20% saving in memory usage" on
vector operations (C10 §3, §8) **[checked]**. Agda's GHC backend drops `@0` constructor
arguments (C11) **[cited]**. Allais notes that such erasure can't change a structure's shape,
only thin it (C9 §2.1) **[checked]**.

**How it maps onto Stitchwort.** Erasure is by sort: proofs and types go, relevant data
stays. docs/core.md says so: "an indexed family's computational fields are kept, forced
implicit ones like `n` in `VCons` included", and the runtime's lowering shares the same
decisions with the JS backend (`erasure.rs` header, D389; `Data::unboxed_field` is the
shared rule for one-field records) **[checked]**. vec.md measured the cost: about 5–10% per operation
against lists, "from the stored length in each `VCons`", and a naive `fromList` that is
quadratic **[checked]**.

The catch, from C10's construction: the field is recovered from the index *passed to the
eliminator*. At run time that means the length must already be a value in scope where the
`VCons` is matched. In Stitchwort an implicit `Nat` parameter is relevant, so functions over
`Vec a n` often do receive `n` **[inferred]**; where they don't (a vector in a record that
packs its length), the field must stay. So forcing *moves* the information from each cell to
the caller; it is a clear win only where the caller holds the length anyway **[inferred]**.
A second change would then be needed for the full gain: dropping a relevant parameter that
is only passed to itself in recursive calls (Tejiščák's erasure inference, cited by C9)
**[inferred]**.

**Expected gain.** At most the 5–10% vec.md measured, for programs that use `Vec`, and
10–20% of their memory by C10's measure. Small.

**Risks.** Per-use analysis (keep the field wherever some match can't rebuild it); the JS
codec must put the field back at the boundary; JS and the runtime must share the rule, as
they share `unboxed_field`, or the differential tests diverge.

**Next step.** Ticket T3: measure first (how many `VCons` cells, how often a matched `n` is
read, and whether the index is in scope at those matches), then a short note. Low priority.

### 5.4 What the dispatch loop can still give (C14–C17, C25; SW-813)

**What others do.** Three routes to a faster interpreter loop:

- *Fewer, heavier instructions.* wasmi's move from stack to register bytecode was "up to 5"
  times faster, but recursive Fibonacci "has not significantly improved" (C15)
  **[cited]**. Stitchwort is already register-based, and stage 4 added `Test` after counting
  instruction pairs; it judged other pairs "not worth it at these sizes" (fast-runtime.md
  stage 4) **[checked]**.
- *Threaded dispatch by tail calls.* Deegen generates it, with VM state pinned to registers
  through LLVM's GHC calling convention, and beats LuaJIT's interpreter by 31%; it has no
  ablation, so the share due to dispatch is unknown (C14) **[checked]**. Titzer's Wizard
  measured its own threaded dispatch at 14% on average, 29% at most (C25 §3.4)
  **[checked]**. CPython's tail-calling interpreter gained "1-5% or so" against a
  well-tuned baseline (Elhage), 5% on macOS over computed gotos and 15–20% with MSVC over
  a switch-case loop (Jin) (C17) **[cited]**.
  Keeter measured it in Rust with `become` (C16) **[cited]**:

  | Platform | `match` loop | tail calls | |
  |---|---:|---:|---|
  | M1, Fibonacci | 2.41 ms | 1.19 ms | 2.0× faster |
  | M1, Mandelbrot | 125 ms | 76 ms | 1.6× faster |
  | x86-64, Mandelbrot | 264 ms | 175 ms | 1.5× faster |
  | Firefox 149 (Wasm), Mandelbrot | 264 ms | 311 ms | 1.2× slower |
  | Chrome 146 (Wasm), Mandelbrot | 244 ms | 905 ms | 3.7× slower |
  | wasmtime, Mandelbrot | 128 ms | 595 ms | 4.6× slower |

  It needs nightly Rust, and on x86 a special calling convention.
- *Generate the interpreter* (Deegen): out of reach for a Rust code base.

**How it maps onto Stitchwort.** The machine is a `match instr` in a loop
(`machine.rs:988–992`) **[checked]**. The playground runs it as WebAssembly (D1252), and the
repository pins stable Rust 1.99 (`rust-toolchain.toml`) **[checked]**. So tail-call dispatch
would help the CLI's `run` and `test` (the machine is their default; `--native` is a feature
build, docs/testing.md) **[checked]**, would make the playground slower on Keeter's evidence,
and needs nightly. The CLI already has native code for real speed.

The profile says where the rest is: on `Set`, about 19% of the machine's time is dispatch,
and the rest of the run loop's 63% is "frame push and pop, clearing registers, and
reference counting"; 4% is growing the register vector at frame entry; a call and return
costs about 37 ns against 2.2 ns natively with the same counting (native-compilation.md
§1.2–1.3) **[checked]**. wasmi's Fibonacci result fits: register bytecode didn't help calls.

**Expected gain.** Dispatch: at most the 19%, so 1.1–1.25× even if it vanished. Titzer's
and CPython's measured 5–14% fit that, and so does CPython's 15–20% over a switch-case loop
on MSVC, the shape closest to the machine's, if only just **[inferred]**. The call path is the bigger target:
pre-sizing the register vector, not clearing registers written before read, unboxing the
common `Ret` cases **[inferred]**.

**Risks.** *Assumption: the `Set` profile is typical.* Day 19's 11 M small closure calls
(SW-813) are calls, which fits. Parse-heavy programs spend their time in the effect runtime
(SW-593, effects.md), which this doesn't touch.

**Next step.** Ticket T4: a design note for SW-813 that starts from the call path and
records why tail-call dispatch is out for now. Revisit when `become` is stable and Wasm
engines compile tail calls well. No decision needed.

### 5.5 Small numbers in generated JS (C21; `run --js`, extraction)

**What others do.** Every runtime in the October survey keeps small integers unboxed, and
Stitchwort's machine does too (`Nat(u64)`, else `BigNat`; "each number has exactly one
form", `value.rs`) **[checked]**. Koka checks for the big case on every arithmetic
operation and still beat C on trees (C6 §7) **[checked]**. The one measurement of `BigInt`
as a general integer in V8 is old: Scala.js mapped `Long` to `BigInt` and SHA-512 ran "a
whopping 60 times slower"; a V8 engineer called it "certainly plausible" because "every
BigInt is allocated as an object" (C21, 2018) **[cited]**.

**How it maps onto Stitchwort.** The JS backend makes `Nat` a `bigint` everywhere: `Zero` is
`0n`, `Succ n` is `n + 1n` (docs/core.md) **[checked]**. On the arithmetic-heavy day 2 brute
force, `--js` took 66.8 s against 23.1 s on the machine (fast-runtime.md stage 3)
**[checked]**, the one program where JS lost badly; on merge sort and day 4 JS was level.
The AoC 2024 notes find JS ahead of native on parse-heavy code (SW-593's 29 Oct note)
**[checked]**, so JS matters as a runner. The machine's rule carries over: a `Nat` is a JS
`number` (an integer below 2^53) or a `bigint` above, never both for one value, with guarded
operations falling back to `bigint` **[inferred]**. Equality stays `===` because the form is
canonical.

**Expected gain.** Unmeasured; the 2018 figure says the gap can be large, but V8 has had
eight years since. Measure first.

**Risks.**

- *Assumption: the codec keeps its boundary.* Exports decode a `Nat` from a `bigint` and
  refuse anything else (`crates/js/src/lib.rs:1357`) **[checked]**. Inside, values would be
  mixed; the codec converts at the boundary.
- Every `Nat` native and every `NumCase` (`=== 0n`) must handle both forms. A missed path is
  a wrong answer, not a crash; the differential tests are the guard, plus a test crossing
  2^53 in each operation.
- `Int` would want the same.

**Next step.** Ticket T5: profile day 2 under `--js` and time a `Nat` loop as `bigint` and as
`number` in Node 22; then a note if the gap is large. Decision D1922.

## 6. Steal next

Only cards read in full appear here. At the audit (30 Oct) every source below verified OK or
minor, except C8. C8's claim was corrected, not dropped: the copy-on-every-`push` failure is
in the thesis, but as the author's example, not Lean's library. Ranks 4 and 8 still stand,
because they rest on SW-112, the day 4 measurements and C1 as much as on C8. No re-rank.

| Rank | Idea | Helps | Cost | Source |
|---|---|---|---|---|
| 1 | Benchmarks record retired instructions and bytecode counts beside time; gate on instructions | SW-659, every speed lane | small | C24 |
| 2 | Shift and bitwise natives tested at and past the word width in every runner | SW-808 | small (tests) | C20 |
| 3 | Count reference-count operations per run (the gate for any borrowing) | SW-813, SW-814 | small | 5.2; C1, C3, C4 |
| 4 | `Array` specified as a list, in place when unique in the machine and native code, with a copy counter | SW-112, AoC grid programs | design note, then runtime change | 5.1; C1, C8, C9, C5 |
| 5 | SW-813 note: start from the call path, not dispatch; no tail-call dispatch while the playground is Wasm | SW-813 | design note | 5.4; C14–C17, C25 |
| 6 | Check `Unpack`'s token placement against Koka's fragility examples; test that inlining keeps reuse | reuse robustness, SW-814 | small (review, tests) | C4 |
| 7 | JS `Nat` as `number` below 2^53, `bigint` above (measure first) | `run --js`, extraction speed | JS backend change | 5.5; C21 |
| 8 | "Runs in place" report for std functions (FIP-style) | SW-813, SW-814 | small diagnostic | C5, C8 |
| 9 | `Map` insert as a zipper loop that reuses every node | SW-814 | std + proofs | C6 |
| 10 | Borrowed parameters, only if rank 3 shows a large share | SW-813 | runtime change | 5.2; C1, C2, C3 |
| 11 | Don't store forced indices; drop self-passed relevant arguments | `Vec` speed | lowering change | 5.3; C10, C9 |
| 12 | Size counter for lowered code (inlining and copies) | code size | small | C2 |
| 13 | Unboxed scalar fields in cells, scalars after pointers | `Set`/`Map` (measured 5× on `Set`) | runtime change, both runners | C13; native-compilation.md §0 |

## 7. Proposed tickets

Label `research`; not added to the board.

**T1. Benchmarks: record instructions, not just time.** The machine is shared and loaded
(native-only.md timed at load 21–38 and called the times rough, instruction counts steady to
0.1%). Add retired instructions (macOS `/usr/bin/time -l`, as evaluator-speed.md did; Linux
`perf stat` or Cachegrind) and the machine's bytecode-instruction count to `stitchwort-bench`
and the runtime benchmarks, gate regressions on them, and report wall time beside them, as
tak and rustls do. Counts miss cache misses and branch mispredictions (rustls's README), so
a large change still gets a timed run. This lets SW-659 go ahead without a quiet machine.

**T2. Count reference-count operations.** Add increments and decrements to the machine's
statistics (beside `alloc_trace`), split by whether the callee only read the value, and run
the bench programs, `Set` and day 4. Write a borrowed-parameters note only if that share is
large, with the constraints the papers give: owned when reset or reused (Lean, Beans §5.2),
owned at tail calls (Lean), frame-limited memory (Lorenzen and Leijen, ICFP 2022: Koka
declined Lean's inference), no borrow into an effect continuation. Evidence that it can
cost: removing borrowing sped up Lean's const_fold (0.90, cause not stated in the paper);
borrowing blocked 6.4% of in-place updates in OOPSLA 2026's unify.

**T3. Forced constructor fields.** Measure how many `VCons` cells a `Vec` program builds, how
often a matched `n` is read, and whether the length is in scope at those matches. Then a
short note on not storing a forced index (Brady, McBride and McKinna 2003), with dropping a
self-passed relevant parameter as its companion. Shared decision in `erasure.rs` for JS and
the runtime; the codec puts fields back at the boundary.

**T4. SW-813 design note: the call path.** Start from native-compilation.md §1.2–1.3 (37 ns
per call; 19% dispatch; frame push and pop, register clearing, RC). Candidates: size the
register vector once, don't clear registers written before read, unbox the common `Ret`
cases. Record why tail-call dispatch is out for now: Keeter (2026) measured it 1.5–2×
faster natively and 1.2–4.6× slower in Wasm engines, it needs nightly `become`, and measured
dispatch gains elsewhere are 1–14% (CPython against computed gotos, Wizard), 15–20%
against a switch-case loop (CPython on MSVC).

**T5. JS `Nat` representation: measure, then decide.** Profile day 2's brute force under
`--js`; time `Nat` addition and comparison as `bigint` and as `number` in Node 22. If the gap
is large, a note: canonical `number` below 2^53, `bigint` above, guarded operations, natives
and `NumCase` for both, the codec's boundary unchanged. Decision D1922.

**T6. SW-112 design note, with a recommendation.** Fold §5.1 into the note SW-112 asks for:
`Array` specified over `List` (or `Vec`), natives bound by content hash with differential
tests, `set` in place when unique (`Rc::get_mut`), a counter of copies made by `set`, a
section on Huisinga's case (an array also stored in a `Map`), and the JS choice (copying
`set`, or a persistent vector). Decision D1920.

**T7. Shift and bitwise natives: corner-case tests.** When SW-808's `Nat` xor/and/or/shift
natives are added, test shift amounts 63, 64, 65 and far beyond, and operands either side of
2^64, on the reference evaluator, the machine, native code and JS. CertiCoq-Wasm (CPP 2025)
found its Wasm formalisation modelling shifts "like a C shift" where Wasm takes the amount
modulo the width, and its verification of primitive integers turned up an unsoundness in
Rocq's `vm_compute` (rocq#19402).

**T8. A "runs in place" report, and a reuse-placement check.** For a program or a std
function, say which matches reuse their cell and which allocate, and why (shared value, size
mismatch). From FP²'s `fip` check (ICFP 2023), as a report rather than a type. Check
`code.rs`'s token placement against Lorenzen and Leijen's example A (a token taken while the
value is still live is always null), and add a test that `opt.rs`'s inlining doesn't lose
reuse (their `is-red` case). Use it on `Map.Tree.insertWith` before SW-814's fused balance.

**T9. Refresh this register quarterly**, finishing the sweep the search budget cut short and
the full texts in §9. Next: January 2027.

## 8. Decisions

- **D1920.** For SW-112, write the design note around a list-specified `Array` with in-place
  update on unique values in the machine and native code (the pattern compact text used for
  `Text`), rather than a persistent tree or a uniqueness type? **[Yes: design note T6;
  build only after it settles the JS choice.]** Assumptions: users thread arrays linearly
  most of the time; a copy counter makes the other case visible; JS may be slower.
- **D1921.** Spend a small lane on counting reference-count operations (T2), and design
  borrowed parameters only if the count shows a large share? **[Yes.]** Assumption: the
  count is cheap to add next to `alloc_trace`.
- **D1922.** Measure small `Nat`s as JS `number`s (T5) now, or leave `--js` as it is because
  native code is the CLI's speed route? **[Measure now: JS is the faster runner on
  parse-heavy programs (SW-593), so its arithmetic gap matters.]** Assumption: the 2018
  `BigInt` gap hasn't closed; T5 tests exactly that.

## 9. Sources not reached

### Full text not reachable

None of these is promising enough for Matt to fetch by hand (audit, 30 Oct). C12, first
listed here, was found at the audit in the Internet Archive's capture of the ACM PDF
(`web.archive.org/web/20250330073918id_/https://dl.acm.org/doi/pdf/10.1145/3591260`) and is
now read.

| Item | DOI | URLs tried, and what each returned |
|---|---|---|
| C22. IOG, "Stacks in the JS backend" (2023) | — | engineering.iog.io/2023-04-21-stacks-in-the-js-backend (with and without slash): 404; web.archive.org: unreachable from the fetch tool. Audit retry (30 Oct): the URL redirects (308) to the slashless form, which is a 404; the new engineering.iog.io index links no such post; Internet Archive CDX: "Temporarily Offline". Not promising enough to ask Matt for (a blog post on a backend design Stitchwort doesn't share) |
| Forster, Sozeau, Tabareau, Verified Extraction from Coq to OCaml (PLDI 2024; screened, not carded) | [10.1145/3656379](https://doi.org/10.1145/3656379) | dl.acm.org PDF: HTML page; inria.hal.science/hal-04329663/file/main.pdf: HTML (bot page); Semantic Scholar: DOI link only |
| GHC issue #15333 (screened, not carded) | — | gitlab.haskell.org issue page and API: Anubis bot page |

Reachable but not read in this pass: Marshall, Vollmer and Orchard, "Linearity and
Uniqueness: An Entente Cordiale" (ESOP 2022), at kar.kent.ac.uk/id/document/3283119 (a PDF;
arXiv 2103.06127, tried first, is a different paper). Jane Street's "Unboxed types for
OCaml" (ML 2022) has no paper, only a talk abstract and an RFC.

### Not searched

The session's shared web-search budget (200 searches across all agents) ran out after
Q36. Not searched, and so not screened: Unison's runtime since 2024; Idris 2's Chez and RefC
backends since 2023; MLKit and region inference since 2022; deforestation and fusion in
strict languages (2022–2026); Koka's benchmarks since 2024; persistent vectors (RRB) in
functional runtimes; Larose et al., "AST vs. Bytecode" (OOPSLA 2023); Lorenzen's thesis;
Roc's own docs on in-place `List` updates. Rerun these first in the quarterly refresh.

### Not confirmed

Whether Rust's `become` has been stabilised since April 2026; whether general Wasm stack
switching (beyond JSPI) ships in a stable browser (wasm_of_ocaml's April 2026 post says not
yet).
