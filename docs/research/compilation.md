# Literature trawl: compilation and runtime

*SW-894, cluster 6. Trawled 29 October 2026 against `main` at `5c25a1b5`. Research only: no
code changed, no tests run. Window: 2022 onwards (D1831); older work appears only where
in-window work or a system we compare with relies on it, marked **classic**. Effect-runtime
compilation is in [effects.md](effects.md) and isn't repeated here.*

Labels: **[cited]** read in the linked source (a paper's text, an abstract, a release note or
a blog post, fetched on 29 Oct 2026); **[checked]** read in Stitchwort's code or docs at the
place given; **[inferred]** my reasoning, not tested; **[unverified]** from a search summary
or a second-hand account only.

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
- a simplifier that inlines, specialises on known function arguments and resolves known
  constructors (`opt.rs`, `specialise.rs`);
- TRMC by destination passing (`trmc.rs`), state handlers run as loops (`fusion.rs`);
- Cranelift native code that keeps the machine's RC and reuse decisions (`crates/native`).

So the new material from 2022 to 2026 that adds most is in five places the existing notes
don't cover. Ranked by value against effort:

1. **Arrays with in-place update, specified as lists (SW-112).** Lean's `Array` is a
   structure around a `List`, run as a C array that is updated in place when its reference
   count is 1 (Ullrich and de Moura, **classic**, §7.1). Stitchwort already uses this
   pattern for `Text` (compact-text.md). Allais (ESOP 2023) shows the general form for
   indexed families. A design note, then a runtime change (deep read 5.1).
2. **Borrowed parameters.** Lean infers which parameters a function only reads and passes
   them without touching the count. Its new compiler keeps that pass and, since 4.30 (May
   2026), lets users annotate it. A 2026 paper reports 75–100% fewer increments than
   Perceus and a 1.48× geomean speedup (Brandon et al., OOPSLA 2026). Stitchwort's
   bytecode has moves but no borrows: every read that isn't the last is a `clone`
   (deep read 5.2). Runtime change, both runners.
3. **Don't store forced indices.** `VCons` stores its length `n` at run time **[checked]**
   (docs/core.md, JS representations; vec.md measured 5–10% per operation and a quadratic
   `fromList`). Brady, McBride and McKinna (**classic**, cited by Allais 2023) showed such
   fields can be recomputed from the type's index. A lowering change (deep read 5.3).
4. **Know what the dispatch loop can still give (SW-813).** Rust interpreters that dispatch
   by tail calls run 1.5–2× faster than a `match` loop natively, but 1.2–4.6× *slower* in
   WebAssembly, and need nightly Rust (Keeter 2026). Dispatch is about 19% of the
   machine's time (native-compilation.md §1.2). So the playground should keep the loop,
   and SW-813 should start with frame setup and RC, not dispatch (deep read 5.4).
5. **Small numbers in generated JS.** The JS backend makes every `Nat` a `bigint`. Day 2's
   brute force took 66.8 s under `--js` against 23.1 s on the machine **[checked]**
   (fast-runtime.md, stage 3 table). The machine's answer (a word, else a bignum) carries
   over to JS as "a `number` below 2^53, else a `bigint`" (deep read 5.5).

Smaller steals: count instructions, not seconds, on a loaded machine (§4, C24; helps
SW-659); test shift natives at the shift-width corner that made Rocq unsound in
CertiCoq-Wasm (C20; SW-808); lambda set specialisation as the general form of
`specialise.rs` (C12); unboxed scalar fields in cells, which native-compilation.md measured at
another 5× on `Set` (C13).

What doesn't transfer: monomorphisation over types (types are erased and values are
uniform, so there is nothing to specialise on); laziness (First-Order Laziness, ICFP 2025);
uniqueness *types* (Futhark, Granule), since Stitchwort's reuse is dynamic and must stay
invisible to proofs; a Wasm backend for the playground, which still lacks deep stacks
without an explicit stack of its own (C17–C19).

Three decisions for Matt (§8): D1920 (arrays: a design note), D1921 (borrows), D1922
(small numbers in JS).

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

The session's shared web-search budget ran out after 30 queries (Q30), before the planned
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

Fetched pages: the SPLASH 2026 page for the borrows paper; Keeter's blog post (numbers in
§5.4).

### 2.3 Full texts

PDFs were downloaded with `curl` and turned into text with `nix shell nixpkgs#poppler-utils
-c pdftotext -layout` (the package name has a hyphen; `poppler_utils` is gone from
nixpkgs). **This worked** for every PDF that downloaded. Read: Allais ESOP 2023 (§1–3),
Lorenzen et al. PLDI 2024 (abstract, §1, §2.3, §7), Ullrich and de Moura (§5.2, §7.1, §8),
Deegen (abstract, §1, the register-pinning section), CertiCoq-Wasm (abstract, §1, §2.1),
Lam and Parreaux FLOPS 2024 (abstract, §2.3, evaluation), Lutze et al. OOPSLA 2025
(abstract, §1), Titzer OOPSLA 2022 (abstract, §1), First-Order Laziness TR (abstract),
Destination Calculus (abstract). Failed: Microsoft Research PDFs (FP², frame-limited reuse)
return an HTML page to `curl`; the Stanford copy of the borrows paper refused the
connection; MIT's copy of LSS came back empty.

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
| 17 | Marshall, Vollmer, Orchard: Linearity and Uniqueness: An Entente Cordiale | ESOP 2022 | A | maybe |
| 18 | Futhark uniqueness types and their limits with higher-order functions (blog, 2022) | blog | A | drop (static types; Stitchwort's reuse is dynamic) |
| 19 | Roc: RC with in-place `List` update; compiler rewrite in Zig (2025) | secondary only | A/R | maybe, **[unverified]** |
| 20 | Brandon, Driscoll, Dai, Berkow, Milano: Better Defunctionalization through Lambda Set Specialization | PLDI 2023 | S | **keep** |
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
| 32 | Forster, Sozeau, Tabareau: Verified Extraction from Coq to OCaml | PLDI 2024 | T | **keep** |
| 33 | Meier, Jensen, Pichon-Pharabod, Spitters: CertiCoq-Wasm | CPP 2025 | T/W | **keep** |
| 34 | wasm_of_ocaml (Vouillon, ML 2024; first release Feb 2025) | talk, blogs | W | **keep** |
| 35 | Guile Hoot on WasmGC and tail calls (Wingo, 2023–2024) | slides, manual | W | **keep** |
| 36 | WasmGC and Wasm tail calls are Baseline (Dec 2024) | web.dev | W | **keep** (fact) |
| 37 | JSPI and stack switching in browsers, 2025–2026 | intent threads | W | maybe, partly **[unverified]** |
| 38 | GHC JS backend: Haskell stacks run by a scheduler loop | IOG blog 2023 | J/W | maybe |
| 39 | GHC Wasm backend: tail calls opt-in | project page | W | drop |
| 40 | V8: Adding BigInts; Scala.js `Long` as `BigInt` "really, really bad" | V8 blog; TC39 issue | J | **keep** (deep read 5.5) |
| 41 | Eisenberg, Dolan, White: Unboxed Types for OCaml | ML 2022 | E | **keep** (with 1 §7.1) |
| 42 | Eisenberg: Layout Polymorphism | ML 2023 | E | drop (no type parameters at run time) |
| 43 | Bagrel, Spiwack: Destination Calculus | OOPSLA 2025 | S | drop (TRMC built) |
| 44 | Bagrel: Destination-passing style in Haskell (JFLA 2024) and thesis (2026) | JFLA, thesis | S | drop |
| 45 | Muhcu et al.: Multiple Resumptions and Local Mutable State, Directly | ICFP 2025 | — | drop here (effects.md #43) |
| 46 | Gaißert et al.: Tracing JIT for Effects and Handlers | OOPSLA 2025 | — | drop here (effects.md #44) |
| 47 | Instruction counts for CI benchmarks: tak docs; rustls `ci-bench`; pythonspeed "CI for performance" | docs, blog | B | **keep** |
| 48 | GHC issue 15333 (a trace call shifted Cachegrind counts) | issue | B | **keep** (with 47, as the caveat) |
| 49 | Lean FRO year 3 roadmap: stack allocation, better RC, ownership-aware compilation | roadmap | R | maybe |
| 50 | Effekt thesis topic: constant-time reference counting (2026) | thesis offer | R | drop |
| 51 | Koka's mimalloc (Leijen et al. 2019), relied on by 7 and 10 | **classic** | R | drop (the CLI already uses mimalloc, evaluator-speed Q2) |
| 52 | Huet's zipper / Minamide's holes, as used by 7 | **classic** | S | drop |

52 screened: 25 keep, 13 maybe, 14 drop.

## 4. Cards

**C1. Ullrich and de Moura, "Counting Immutable Beans", IFL 2019 (classic).**
[arXiv 1908.05647](https://arxiv.org/abs/1908.05647). Claim: Lean's runtime "perform[s]
destructive updates when the array is not shared": `Array.write a i v` updates `a` in place
if its count is 1 (§7.1) **[cited]**. Borrowed parameters "do not update the reference
counter", inferred by a fixed point that starts from "all borrowed" (§5.2) **[cited]**.
Scalar fields are stored unboxed after the pointer fields of a constructor (§7.1)
**[cited]**. Steal: all three (deep reads 5.1, 5.2; C13). Helps SW-112, SW-813, SW-814.
Cost: runtime change each. Full text: yes (§5.2, §7.1, §8 headings).

**C2. Lean 4's new code generator (LCNF).**
[4.30.0 notes](https://lean-lang.org/doc/reference/latest/releases/v4.30.0/),
[`InferBorrow`](https://lean-lang.org/doc/api/Lean/Compiler/LCNF/InferBorrow.html). Claim:
the reset/reuse pass was ported to LCNF "with improved exponential-code prevention,
resulting in a ~15% decrease in binary size"; users can mark arguments `@&` and borrow
inference keeps the mark **[unverified]** (release notes as quoted by search; page not
opened). Steal: (a) Stitchwort's `opt.rs` copies functions per known argument (64 copies of
up to 200 nodes) and reuse paths per constructor, so a size check on lowered code is worth
having; (b) a borrow annotation as an escape hatch. Helps SW-813. Cost: small (a size
counter in the bench); (b) is part of 5.2. Full text: no.

**C3. Brandon et al., "Fully Automatic Type Inference for Borrows with Lifetimes",
OOPSLA 2026.** [SPLASH page](https://2026.splashcon.org/details/oopsla-2026/22/Fully-Automatic-Type-Inference-for-Borrows-with-Lifetimes),
[DOI 10.1145/3798221](https://doi.org/10.1145/3798221). Claim: inference for a pure
language with shared borrows and non-lexical lifetimes; where a program can't be typed as
written, inference inserts a few RC operations. Against Perceus, "reference count
increments were reduced by 75–100% on every benchmark where the baseline had" any;
geomean speedup 1.48× **[cited]** (SPLASH abstract). Steal: borrows beyond parameters
(locals that live inside a scope), after 5.2's parameter-only version. Helps SW-813. Cost:
research project. Full text: no (the Stanford PDF refused the connection).

**C4. Lorenzen and Leijen, "Reference Counting with Frame Limited Reuse", ICFP 2022.**
[MSR page](https://www.microsoft.com/en-us/research/publication/reference-counting-with-frame-limited-reuse/).
Claim: earlier reuse analyses are "fragile with respect to small program transformations,
or can cause an arbitrary increase in the peak heap usage"; drop-guided reuse is simpler,
and keeps memory alive only by a constant factor per call **[unverified]** (search
summary of the abstract). Steal: a check that `code.rs`'s reuse (a token per constructor
on a path, `DropReuse` for a known constructor) is drop-guided in their sense, and a test
that inlining in `opt.rs` doesn't remove reuse (the fragility they name). Helps SW-814.
Cost: small (a review and a test). Full text: no (PDF blocked).

**C5. Lorenzen, Leijen and Swierstra, "FP²: Fully in-Place Functional Programming",
ICFP 2023.** [ICFP page](https://icfp23.sigplan.org/details/icfp-2023-papers/10/FP-Fully-in-Place-Functional-Programming).
Claim: a linear calculus whose functions run "without (de)allocation and with constant
stack space" when their arguments are unshared; Koka checks a `fip` keyword
**[unverified]** (search summary). Steal: a *report*, not a type: say which std functions
run in place (merge sort, `map`, `Map` insert), like effects.md T5's handler report.
Helps SW-813, SW-814, and the SW-112 design (5.1). Cost: small (a diagnostic) to research
(a checked `fip`). Full text: no (PDF blocked).

**C6. Lorenzen, Leijen, Swierstra and Lindley, "The Functional Essence of Imperative
Binary Search Trees", PLDI 2024.** [PDF](https://homepages.inf.ed.ac.uk/slindley/papers/fiptree.pdf).
Claim: bottom-up tree algorithms from a defunctionalised CPS transform (zippers), top-down
ones from first-class constructor contexts; in Koka "always outperform C" on move-to-root,
splay and zip trees, and red-black trees are 25% (top-down) to 50% (bottom-up) slower than
"equalized" C (§7) **[checked]** (full text). Steal: for SW-814, write `Map.Tree.insertWith`
so the machine runs it in constant stack with every node reused: the bottom-up form is a
zipper the reuse tokens fill in place. Cost: std change plus re-proving `balance` lemmas
(SW-814 names these). Full text: yes (§1, §2.3, §7).

**C7. Lam and Parreaux, "Being Lazy When It Counts", FLOPS 2024.**
[PDF](https://lptk.github.io/files/ctrc-2024-05-09.pdf). Claim: deferring the decrements of
a freed object's fields until the memory is reused gives constant-time allocation and
freeing, with no leak if all allocations have one size; on par with Koka, sometimes faster
**[checked]** (abstract, evaluation). Steal: the machine frees with a work list
(`value.rs` header) and dropping was 11% of the `Set` profile (native-compilation.md §1.2).
Lazy freeing would bound the pause when a large structure dies. Cost: runtime change, and
uniform sizes don't fit `Value` arrays of any length. Not now. Full text: yes (parts).

**C8. Huisinga, "Static Uniqueness Analysis for Lean 4", KIT master's thesis, 2023.**
[PDF](https://pp.ipd.kit.edu/uploads/publikationen/huisinga23masterarbeit.pdf). Claim:
without in-place update "an array operation would copy the whole array"; a uniqueness type
system can remove the runtime checks where uniqueness is guaranteed **[unverified]**
(search summary). Steal: the failure mode to design against in 5.1: a silent O(n) copy
when an array is shared. Cost: reading. Full text: no.

**C9. Allais, "Builtin Types viewed as Inductive Families", ESOP 2023.**
[arXiv 2301.02194](https://arxiv.org/abs/2301.02194). Claim: an efficient runtime type can
be paired with erased invariants so that users program "as if we were using the
high-level structure", with "entirely predictable" complexity; erasure alone can't change
a list into a better structure (§2.2) **[checked]**. Steal: the view pattern for SW-112:
the kernel sees a list (or `Vec`), the runtime a native array, and the user matches through
a view. Cost: design note. Full text: yes (§1–3).

**C10. Brady, McBride and McKinna, "Inductive Families Need Not Store Their Indices",
TYPES 2003 (classic, via C9).** Claim: an index determined by a constructor's spine (the
`n` of `VCons`) needn't be stored: it is the predecessor of the index of the whole value
**[cited]** (as summarised in C9 §2.1). Steal: deep read 5.3. Cost: lowering change. Full
text: C9's account only.

**C11. Agda's run-time irrelevance.**
[docs](https://agda.readthedocs.io/en/latest/language/runtime-irrelevance.html). Claim:
`@0` arguments are absent at run time and "the GHC backend compiles [`_∷_`] to a datatype
where the cons constructor takes only two arguments" **[cited]**. Steal: a user-facing
"erase this relevant field" mark is the other route to 5.3. Stitchwort erases by sort
(proofs and types), so `@0` would be a new language feature. Cost: language change; 5.3
prefers the automatic route. Full text: the docs page (via search).

**C12. Brandon et al., "Better Defunctionalization through Lambda Set Specialization",
PLDI 2023.** [project page](https://cs.princeton.edu/~mpmilano/publication/lss/). Claim:
specialising defunctionalisation that "imposes no restrictions on how function values may
be used", by a type system tracking which lambdas flow where; up to 6.85× under MLton,
3.45× under OCaml **[unverified]** (search summary). Roc uses it. Steal: today
`specialise.rs` copies a recursive function for a *known* function argument (`map
scramble`, `merge`'s comparison), bounded at 64 copies **[checked]** (fast-runtime.md stage
4). Lambda sets would cover the rest: a closure passed through a data structure or
returned, which is where day 19's 11 M small closure calls are (SW-813, Day 19 findings
ticket). Cost: research project. Full text: no.

**C13. Unboxed scalar fields (Lean's constructor layout, C1 §7.1; Eisenberg, Dolan and
White, "Unboxed Types for OCaml", ML 2022).** [ML 2022](https://icfp22.sigplan.org/details/mlfamilyworkshop-2022-papers/13/Unboxed-types-for-OCaml).
Claim: Lean stores scalar fields as raw bytes after the pointers **[cited]**; OCaml is
adding layouts to give "the programmer more control of the memory layout" **[unverified]**.
Steal: in Stitchwort a cell is `Rc<[Value]>` of 24-byte values (`value.rs`) **[checked]**.
native-compilation.md measured `Set` insert at 0.68 s with boxed numbers and 0.12 s with
numbers unboxed in the nodes (§0) **[checked]**. That note already names the change as
"later, separately". Nothing new to steal but the layout rule (scalars after pointers, so
freeing walks only a prefix). Cost: runtime change, both runners. Full text: C1 §7.1.

**C14. Xu and Kjolstad, "Deegen", arXiv 2024, OOPSLA 2026.**
[arXiv 2411.11469](https://arxiv.org/abs/2411.11469). Claim: an interpreter generated from
per-bytecode C++ semantics, with "bytecode specialization and quickening, register pinning,
tag register optimization", is 31% faster than LuaJIT's hand-written interpreter; each
bytecode is "a stand-alone machine function, and control transfer is implemented by tail
calls", register pinning through LLVM's GHC calling convention **[checked]**. Steal:
the list of techniques, as the checklist for SW-813; specialised bytecodes are what `Test`
already is. Cost: per technique. Full text: yes (abstract, §1, the relevant section).

**C15. wasmi 0.32 (2024).** [blog](https://wasmi-labs.github.io/blog/posts/wasmi-v0.32).
Claim: moving a Rust interpreter from stack to register bytecode was "up to 5×"; "the
performance of interpreters is mostly dictated by the dispatch of instructions", so fewer,
heavier instructions win; 8-byte instruction words were the sweet spot **[unverified]**
(search summary of the post). Steal: Stitchwort's bytecode is already register-based;
`Instr` is `Copy` with fields up to three `u32`s **[checked]** (`code.rs`), so its size is
worth printing (I didn't). Cost: small (measure). Full text: no.

**C16. Keeter, "A tail-call interpreter in (nightly) Rust", April 2026.**
[post](https://www.mattkeeter.com/blog/2026-04-05-tailcall/). Claim, with numbers in deep
read 5.4: tail-call dispatch with `become` is 1.5–2× faster than a `match` loop natively
and 1.2–4.6× slower in Wasm engines **[cited]**. Steal: the measurement that settles the
playground question. Cost: none (evidence). Full text: yes (fetched).

**C17. CPython 3.14's tail-calling interpreter (Elhage; Jin, 2025).**
[Elhage](https://blog.nelhage.com/post/cpython-tail-call/),
[Jin](https://fidget-spinner.github.io/posts/no-longer-sorry.html). Claim: first reports
of 10–15% were inflated by an LLVM 19 regression in the baseline; the real gain is about
5% geomean, more on MSVC; needs `musttail` and `preserve_none` **[unverified]** (search
summary). Steal: a caution on SW-813's dispatch hopes, and on measuring against a
regressed baseline. Full text: no.

**C18. Forster, Sozeau and Tabareau, "Verified Extraction from Coq to OCaml", PLDI 2024.**
[Rocq page](https://rocq-prover.org/papers/verified-extraction-from-coq-to-ocaml). Claim:
extraction through Malfunction is proved correct for first-order data, and extracted code
"can safely interoperate" with unverified code at first-order types; at higher-order types
plain interop can give wrong results or segfaults **[unverified]** (search summary).
Steal: the same line for Stitchwort's JS codec (DESIGN.md §12 refuses functions at the
boundary? not checked). Cost: reading. Full text: no.

**C19. Wasm as the playground's target: WasmGC, tail calls, Hoot, wasm_of_ocaml.**
[web.dev, Dec 2024](https://web.dev/blog/wasmgc-wasm-tail-call-optimizations-baseline);
[Hoot 0.8 status](https://files.spritely.institute/docs/guile-hoot/0.8.0/Status.html);
[wasm_of_ocaml since 6.1](https://ocaml.org/backstage/2026-04-16-wasm-of-ocaml-what-changed-since-6-1).
Claim: WasmGC and tail calls are in all three engines **[unverified]** (search summary);
Hoot still rewrites "all calls to be tail calls and saves and restores values onto an
explicitly managed stack" for what Wasm lacks **[unverified]**; wasm_of_ocaml reports 2–8×
over js_of_ocaml at Jane Street and 10–20% of time in casts and bounds checks
**[unverified]** (second-hand). Steal: nothing yet. A Wasm backend would still need its
own stack for deep non-tail recursion, which is the machine's main advantage in the browser
(D1252). JSPI is shipping, but general stack switching wasn't confirmed (§9). Cost: new
backend. Full text: no.

**C20. Meier, Jensen, Pichon-Pharabod and Spitters, "CertiCoq-Wasm", CPP 2025.**
[PDF](https://www.cl.cam.ac.uk/~jp622/certicoq-wasm.pdf). Claim: a verified Wasm backend
using only Wasm 1.0 and tail calls, with no garbage collection (linear memory up to
1,920 MB, never freed); implementing Coq's primitive integers as Wasm instructions found
"a corner case in their implementation that led to unsoundness": a shift treated "like a C
shift", where Wasm takes the amount modulo the width (§1, §2.1) **[checked]**. Steal: when
SW-808's `Nat` xor/and/or/shift natives are built, test shift amounts at and beyond the
word width on all three backends (Rust panics or wraps, JS `bigint` doesn't, Cranelift's
`ishl` takes it modulo) **[inferred]**. Cost: small (tests). Full text: yes (§1–2.1).

**C21. V8 `BigInt` costs.** [V8 blog](https://v8.dev/blog/bigint);
[TC39 issue 117](https://github.com/tc39/proposal-bigint/issues/117). Claim: V8 keeps
31-bit integers unboxed (Smis) **[unverified]**; Scala.js tried 64-bit `Long` as `BigInt`
and the results were "really, really bad" **[unverified]** (search summary). Steal: deep
read 5.5. Cost: JS backend change. Full text: no.

**C22. GHC's JS backend: stacks in the backend (IOG, 2023).**
[post](https://engineering.iog.io/2023-04-21-stacks-in-the-js-backend). Claim: generated
code doesn't use JS calls for Haskell calls; "lightweight Haskell stacks driven by a
scheduler loop", so the JS stack doesn't grow **[unverified]**. Steal: the alternative to
`run --js`'s 2 GB worker stack if extracted JS must run in a browser with deep recursion.
Same trade as Hoot (C19): an explicit stack costs speed. Cost: JS backend change. Not
now.

**C23. Marshall, Vollmer and Orchard, "Linearity and Uniqueness: An Entente Cordiale",
ESOP 2022.** [Springer](https://link.springer.com/10.1007/978-3-030-99336-8_13). Claim:
linear and unique types in one system (Granule), with benchmarks of in-place arrays
(§4.2) **[unverified]**. Steal: the vocabulary for 5.1's "shared array copies" warning.
Cost: reading. Full text: no.

**C24. Instruction counts as the benchmark metric.**
[tak methodology](https://tak.jdx.dev/guide/methodology),
[rustls ci-bench](https://github.com/rustls/rustls/blob/main/ci-bench),
[pythonspeed](https://pythonspeed.com/articles/consistent-benchmarking-in-ci),
[GHC #15333](https://gitlab.haskell.org/ghc/ghc/issues/15333). Claim: Cachegrind instruction
counts varied 0.008–0.027% on a quiet host and 0.011–0.021% under 32-way contention, against
3.9–20.6% for wall time (tak, a practitioner's pre-v1 report) **[unverified]**; counts miss
cache and layout effects, and a trace call once shifted them in GHC **[unverified]**.
Stitchwort's own notes agree: native-only.md's timings at load 21–38 were "rough" while
"instruction counts are steady to 0.1%" **[checked]**, and evaluator-speed.md read retired
instructions from `/usr/bin/time -l` **[checked]**. Steal: SW-659 needn't wait for a quiet
machine: record retired instructions (and the machine's bytecode count) beside wall time,
gate on instructions, report time. Cost: small. Full text: the pages via search.

**C25. Titzer, "A Fast In-Place Interpreter for WebAssembly", OOPSLA 2022.**
[arXiv 2205.01183](https://arxiv.org/abs/2205.01183). Claim: interpreting Wasm bytecode in
place, without translating it to an internal format, is "on-par with interpreting a
custom-designed internal format", with faster start-up **[checked]** (abstract). Steal:
nothing for speed (Stitchwort lowers once, about 1 ms). It is evidence that translation cost
matters only for start-up. Full text: abstract and §1.

## 5. Deep reads

### 5.1 Arrays with in-place update, specified as lists (C1, C9, C5, C8; SW-112)

**What others do.** Lean's runtime has an array kind; `Array.write a i v` "will
destructively update and return the array `a` if it is not shared" (C1 §7.1) **[cited]**.
A Lean developer on Zulip says these updates come from the runtime's primitives, not from a
compiler heuristic **[unverified]**. In Lean's logic `Array α` is a structure holding a
`List α`, so proofs about arrays are proofs about lists **[unverified]**; compact-text.md
records the same split for `String` (a byte array since 4.25, "with the list view still
available") **[checked]**. Allais (C9) gives the general method for a dependently typed
language: keep the invariant-rich family for the checker, give the runtime an efficient
representation, and connect them by a view whose invariants are erased, so complexity is
"entirely predictable" (§1) **[checked]**.

**How it maps onto Stitchwort.** The pattern is already built once. Compact text keeps
`Text` as a list of characters in the kernel, stores it compactly underneath, and pins each
native to the content hash of the definition it replaces, tested against that definition
(compact-text.md, stage 1, "Binding") **[checked]**. An array would be the same move one
level down:

- **Specification:** `type Array a = MkArray (toList: List a)` (or `Vec a n` inside), with
  `get`, `set`, `push`, `length` defined on the list. Every `List` lemma applies.
- **Machine:** a new `Value` variant (say `Array(Rc<Vec<Value>>)`) and natives for those
  definitions, bound by content hash. `set` calls `Rc::get_mut`: in place if unique, else
  copy, as the machine's `Unpack` already decides for cells (`code.rs`, "Moves and reuse")
  **[checked]**. The machine's moves on last use are what make a threaded array unique
  **[inferred]**.
- **Native code:** the same natives through `native_abi` helpers.
- **JS:** a JS array, copied on `set` unless the backend tracks uniqueness. The JS backend
  has no reference counts, so `set` is O(n) there unless an array is wrapped with a
  persistent structure **[inferred]**. This is the largest open design question.
- **Kernel:** nothing new. The checker runs the list definitions; arrays in proofs are
  lists.

**Expected gain, with the evidence.** The AoC 2024 day 4 notes measured the direct grid
program at 0.91 s (Map) and 2.69 s (list walk) under `run` against 0.20 s for ours, and 23×
and 110× slower natively on a 560 × 560 grid (§5) **[checked]**. They say "every newcomer's
first grid program will look like `MapGrid`". With O(1) `get`, those programs would be within
a small factor of ours **[unverified]** (the notes' own estimate). SW-808 and SW-112's 22 Oct
note (D427) show the opposite pressure: 2025's day 4 doesn't need it.

**Risks.**

- *Assumption: users thread arrays linearly.* If they keep an old version, each `set`
  silently copies the whole array (C8's failure mode). Mitigation: a runtime counter (copies
  made by `set`) in `--stats`, and C5's "runs in place" report.
- *Assumption: the JS backend may be slow for arrays.* If JS must match, it needs an RC
  emulation or a persistent vector, which is more design.
- Proofs: an array spec over `List` makes `get` O(n) in the *checker*. Closed proofs that
  compute with large arrays would be slow, as with lists today.
- Natives are trusted code. Each joins the list in DESIGN.md §13, with a differential test
  against its list definition, as text's did.

**Next step.** The design note SW-112 already asks for, now with a concrete recommendation
to evaluate: list-specified `Array`, unique-in-place natives in the machine and native code,
and a stated choice for JS. Decision D1920.

### 5.2 Borrowed parameters (C1 §5.2, C2, C3)

**What others do.** Lean's compiler marks a parameter *borrowed* when the function only
reads it: the caller keeps its reference, and neither side touches the count (C1 §5.2). The
inference starts with every parameter borrowed and marks one owned when it is consumed
(returned, stored, passed to an owned parameter, or reset for reuse), iterating to a fixed
point **[cited]**. A reference is never reused or destructively updated through a borrow,
since its count of 1 may belong to the caller **[cited]** (IFL 2019 talk, as summarised).
Lean's new compiler kept the pass (`LCNF.InferBorrow`) and, in 4.30, lets users write `@&`
**[unverified]**. Brandon et al. (C3) infer borrows of locals as well as parameters, with
lifetimes, and report 75–100% fewer increments than Perceus and 1.48× geomean **[cited]**.

**How it maps onto Stitchwort.** The machine's bytecode passes an argument by register
list; a register with the `MOVE` bit is moved, otherwise it is cloned (`code.rs`: `Ops`,
`MOVE`) **[checked]**. A clone of an `Rc` is an increment, and the callee drops its copy at
its last use or at frame teardown, a decrement. So a value read by a callee and still
needed by the caller (a tree passed to `Map.Tree.get` inside a loop, a list passed to
`List.length` and then used) costs an increment and a decrement per call **[inferred]**.
No borrow concept exists in `crates/rt` or `crates/native` **[checked]** (grep for
`borrow`: only Rust-level comments). Native code copies the machine's decisions exactly,
"every move, clone and drop is the bytecode's" (`n1.rs` header) **[checked]**, so a
borrow pass in `code.rs` would serve both runners.

What it would take:

- a per-global bit vector "borrowed" for its parameters, computed in `code.rs` from
  liveness, by Lean's fixed point;
- at a call, a non-last-use argument to a borrowed parameter is passed without `clone`
  (the register is lent), and the callee never drops it;
- a borrowed parameter must not reach `Unpack` with a reuse token, `DropReuse`, a
  constructor field, a return, or an owned parameter, or it must be cloned first;
- tail calls: a frame that is replaced can't lend its registers. Lean treats a tail call
  that passes a borrowed value to an owned parameter by incrementing first **[cited]**.

**Expected gain.** Unmeasured here. Upper bound from the profile: the `Set` run spent 11%
dropping values and 7% allocating (native-compilation.md §1.2) **[checked]**. Increments
are cheap but each call that clones and drops a tree pays two count writes and a branch.
C3's 1.48× is over Perceus in compiled code, where RC is a larger share than in an
interpreter. A guess: 5–15% on the machine for call-heavy code that passes structures down
(`Map.get`, `List.length`), more in native code **[inferred]**. The first step is to
count: increments and decrements per run, which `alloc_trace` may already almost give.

**Risks.**

- *Assumption: allocation traces may change.* The native agreement tests compare
  allocation traces with the machine's event for event (native-compilation.md N4)
  **[checked]**. A borrow pass in `code.rs` changes both runners together, so the traces
  still agree, but every recorded trace changes once.
- Borrowing defeats reuse in a callee: a borrowed list can't be reused even when the
  caller would have passed its last reference. Lean's heuristic marks a parameter owned
  when the function resets it. The same rule is needed, or `merge` loses its in-place
  behaviour (stage 4's biggest win).
- The effect runtime holds continuations whose captured values are owned; a borrow must
  not escape into a `Call`'s continuation.

**Next step.** Ticket T2: count increments and decrements on the bench programs, then a
design note for parameter borrowing in `code.rs`, with the reuse rule and the effect rule.
Decision D1921 only on whether to spend a lane on the count.

### 5.3 Don't store forced indices (C10, C9, C11)

**What others do.** Brady, McBride and McKinna observed that a vector's length "is entirely
determined by the spine of the vector": the tail's length is the predecessor of the whole
vector's, so it needn't be stored (as summarised in C9 §2.1) **[checked]**. Agda's GHC
backend drops `@0` constructor arguments (C11) **[cited]**. Idris 2 erases by quantity.

**How it maps onto Stitchwort.** Erasure is by sort: proofs and types go, relevant data
stays. docs/core.md says so for JS, and the Rust runtime stores the same way: "an indexed
family's computational fields are kept, forced implicit ones like `n` in `VCons` included"
**[checked]** (docs/core.md, JS representations). vec.md measured the cost: option C (the
indexed `Vec`) costs "about 5–10% more per operation than lists", "from the stored length
in each `VCons`", and a naive `fromList` that stores `List.length` of the rest is quadratic,
about ten times the linear version at row size **[checked]** (vec.md, measurements). The
library avoids the quadratic one by hand.

Two changes, the second needing the first:

1. **Forced fields.** In lowering (`crates/rt/src/lower.rs`, with the shared decisions in
   `erasure.rs`), a constructor field that appears as an index variable in the
   constructor's result type (`n` in `Vec a (Succ n)`) isn't stored. A match that binds it
   gets it from the scrutinee's type index instead: for `VCons`, the predecessor of the
   length the function received. That works only where the index is itself a runtime
   value in scope.
2. **Dead relevant arguments** (Tejiščák's erasure inference, **classic**, cited by C9 §2.1):
   if no path of a function reads a parameter except to pass it to the same parameter of
   a recursive call, drop it. `Vec.map`'s implicit `n` is such a parameter **[inferred]**.
   Without this, (1) may move the cost from the cell to a call argument rather than remove
   it.

**Expected gain.** One field fewer per `VCons` (a third of its runtime fields for a cell of
`x`, `n`, `xs`), and the 5–10% vec.md measured **[checked]**, for programs that use `Vec`.
AoC day 4 (2025) is one (`settleRows` over `Vec`, SW-112's 24 Oct note) **[checked]**.
Small in absolute terms.

**Risks.**

- *Assumption: the index is in scope at run time wherever the field is matched.* Where it
  isn't (a `Vec` in a record field with its length existentially packed), the field must
  stay. So the rule is per constructor *and* per use, which is harder than it looks. A
  conservative version: drop the field only if every match in the program can rebuild it;
  else keep it.
- The JS codec represents data at the boundary. A forced field omitted in generated code
  must be put back when encoding (`VCons` crossing to JS today includes `n`?) **[unverified]**.
- Both JS and the runtime share `Data::unboxed_field` decisions (docs/core.md)
  **[checked]**; the forced-field rule must be shared the same way, or the differential
  tests diverge.

**Next step.** Ticket T3: measure first (count `VCons` cells and how often a matched `n` is
used, on day 4 and the `Vec` library tests), then a short note. Low priority.

### 5.4 What the dispatch loop can still give (C14–C17, C25; SW-813)

**What others do.** Three routes to a faster interpreter loop:

- *Fewer, heavier instructions* (register bytecode, superinstructions): wasmi's move to
  registers was "up to 5×" (C15) **[unverified]**. Stitchwort is already register-based,
  and stage 4 added `Test` (compare and jump) after counting instruction pairs; it judged
  `Switch → Unpack` and `CtorReuse → Return` "not worth it at these sizes"
  (fast-runtime.md stage 4) **[checked]**.
- *Threaded dispatch by tail calls*: each instruction is a function that tail-calls the
  next through a table. Deegen generates this with pinned registers (C14) **[checked]**.
  Keeter measured it in Rust with `become` **[cited]**:

  | Platform | `match` loop | tail calls | |
  |---|---:|---:|---|
  | M1, Fibonacci | 2.41 ms | 1.19 ms | 2.0× faster |
  | M1, Mandelbrot | 125 ms | 76 ms | 1.6× faster |
  | x86-64, Mandelbrot | 264 ms | 175 ms | 1.5× faster |
  | Firefox (Wasm), Mandelbrot | 264 ms | 311 ms | 1.2× slower |
  | Chrome (Wasm), Mandelbrot | 244 ms | 905 ms | 3.7× slower |
  | wasmtime, Mandelbrot | 128 ms | 595 ms | 4.6× slower |

  It needs nightly Rust (`become` is "an unfinished nightly feature"), and on x86 a
  special calling convention **[cited]**. CPython's version gained about 5% once a compiler
  regression in the baseline was accounted for (C17) **[unverified]**.
- *Generate the interpreter* (Deegen): out of reach for a Rust code base.

**How it maps onto Stitchwort.** The machine is a `match instr` inside a loop
(`machine.rs:988–992`) **[checked]**. The playground runs it as WebAssembly (D1252)
**[checked]**, and Stitchwort pins stable Rust 1.99 (`rust-toolchain.toml`) **[checked]**.
So: tail-call dispatch would help the CLI's `run` and `test` (the machine is still their
default; `--native` is a feature build, docs/testing.md) **[checked]**, would make the
playground *slower* on Keeter's evidence, and needs nightly. The CLI has native code for
real speed already.

The profile says where the rest is: on `Set`, about 19% of the machine's time is dispatch,
and the rest of the run loop's 63% is "frame push and pop, clearing registers, and
reference counting"; 4% is growing the register vector at frame entry (native-compilation.md
§1.2) **[checked]**. A call and return costs 37 ns against 2.2 ns natively with the same
counting (§1.3) **[checked]**. SW-813's "6.5 ns per instruction" is the average including
those.

**Expected gain.** Dispatch: at most the 19%, so 1.1–1.25× even if it vanished
**[inferred]**. Frames: the 37 ns call is the bigger target. Pre-sizing the register
vector once per run (a frame's window size is known from the code) and not clearing
registers that are written before read would attack the 4% and part of the rest
**[inferred]**. Borrowing (5.2) attacks the RC share.

**Risks.** *Assumption: the `Set` profile is typical.* Day 19's 11 M small closure calls
(SW-813) are calls, which fits. Parse-heavy programs spend their time in the effect runtime
(SW-593, effects.md), which this doesn't touch.

**Next step.** Ticket T4: a design note for SW-813 that starts from the call path (frame
setup, register clearing, the `Ret` enum's boxing for `Apply`/`Eff`), and rules out
tail-call dispatch for now, recording Keeter's Wasm numbers. Revisit when `become` is stable
and Wasm engines lower tail calls well. No decision needed.

### 5.5 Small numbers in generated JS (C21; `run --js`, extraction)

**What others do.** Every runtime in the October survey keeps small integers unboxed: Lean
(scalars), OCaml (Zarith), Koka (`int` with a small fast path, "all comparisons and
arithmetic operations include branches for the case where big integer arithmetic is
required", C6 §7) **[checked]**, and Stitchwort's machine (`Nat(u64)`, else `BigNat`;
"each number has exactly one form", `value.rs`) **[checked]**. V8 itself keeps small
integers as Smis **[unverified]**. Scala.js tried `BigInt` for 64-bit longs and backed off
**[unverified]**.

**How it maps onto Stitchwort.** The JS backend makes `Nat` a `bigint` everywhere: `Zero` is
`0n`, `Succ n` is `n + 1n` (docs/core.md, JS representations) **[checked]**. On the
arithmetic-heavy day 2 brute force, `--js` took 66.8 s against 23.1 s on the machine
(fast-runtime.md stage 3) **[checked]**: the one program where JS lost badly. On
merge sort and day 4 JS was level with the machine. The AoC 2024 notes find JS ahead of
native on parse-heavy code (SW-593's 29 Oct note) **[checked]**, so JS matters as a
runner.

The machine's rule carries over: a `Nat` is a JS `number` (an integer below 2^53) or a
`bigint` above, never both for the same value. Addition becomes `typeof`-guarded:
`(typeof a === "number" && typeof b === "number" && (s = a + b) <= MAX_SAFE) ? s :
slowAdd(a, b)` **[inferred]**. Equality stays `===` because the form is canonical.

**Expected gain.** Unmeasured. V8's integer fast paths are many times cheaper than its
`bigint` ones on small values **[unverified]**, so arithmetic loops like day 2 could come
close to the machine or past it; programs that only move numbers around gain little.

**Risks.**

- *Assumption: the codec can keep its boundary.* Exports decode a `Nat` from a `bigint`
  and refuse anything else (`crates/js/src/lib.rs:1357`) **[checked]**. Inside, values
  would be mixed; the codec would convert at the boundary, or the boundary type changes
  (a breaking change for apps).
- Every `Nat` native and every `NumCase` (`=== 0n`) must handle both forms. A missed path
  is a wrong answer, not a crash; the differential tests against the reference evaluator
  are the guard, plus a test that crosses 2^53 in each operation.
- `Int` would want the same, doubling the work.

**Next step.** Ticket T5: measure first (day 2 under `--js` with a profile, and a micro-loop
of `Nat` additions as `bigint` and as `number`), then a note. Decision D1922.

## 6. Steal next

| Rank | Idea | Helps | Cost | Source |
|---|---|---|---|---|
| 1 | Benchmarks record retired instructions and bytecode counts beside time; gate on instructions | SW-659, every speed lane | small | C24 |
| 2 | Shift natives tested at and past the word width on all three backends | SW-808 | small (tests) | C20 |
| 3 | `Array` specified as a list, in-place on unique in the machine and native code | SW-112, AoC grid programs | design note, then runtime change | 5.1; C1, C9, C5, C8 |
| 4 | Borrowed parameters in `code.rs` (count RC operations first) | SW-813, SW-814 | runtime change | 5.2; C1, C2, C3 |
| 5 | SW-813 note: start from the call path, not dispatch; no tail-call dispatch while the playground is Wasm | SW-813 | design note | 5.4; C14–C17 |
| 6 | JS `Nat` as `number` below 2^53, `bigint` above | `run --js`, extraction speed | JS backend change | 5.5; C21 |
| 7 | "Runs in place" report for std functions (FIP-style) | SW-813, SW-814 | small diagnostic | C5, C4 |
| 8 | `Map` insert as a zipper or constructor-context loop that reuses every node | SW-814 | std + proofs | C6 |
| 9 | Don't store forced indices; drop dead relevant arguments | `Vec` speed | lowering change | 5.3; C10, C9 |
| 10 | Size counter for lowered code (inlining and copies) | code size, SW-813 | small | C2 |
| 11 | Lambda set specialisation in place of the bounded copies of `specialise.rs` | day 19's closure calls | research | C12 |
| 12 | Unboxed scalar fields in cells | `Set`/`Map` (measured 5× on `Set`) | runtime change, both runners | C13; native-compilation.md §0 |

## 7. Proposed tickets

Label `research`; not added to the board.

**T1. Benchmarks: record instructions, not just time.** The machine is shared and loaded
(native-only.md measured at load 21–38 and called times rough, instruction counts steady to
0.1%). Add retired instructions (macOS `/usr/bin/time -l`, as evaluator-speed.md did; Linux
`perf stat`) and the machine's bytecode-instruction count to `stitchwort-bench` and the
runtime benchmarks, gate regressions on them, and keep wall time as a report. This lets
SW-659 run without a quiet machine. Caveat from GHC #15333: counts miss cache and layout
effects, so a large change still needs a timed run.

**T2. Count reference-count operations, then a design note on borrowed parameters.** Add
increments and decrements to the machine's statistics (beside `alloc_trace`), run the bench
programs, `Set` and day 4. If they are a large share, write the note: Lean's fixed-point
inference (Ullrich and de Moura §5.2) over `code.rs`'s liveness, lending registers at
calls, never reusing through a borrow (owned when the callee resets the parameter, so
`merge` keeps its reuse), no borrow into an effect continuation, tail calls. Both runners
get it through the bytecode. Cites Brandon et al. (OOPSLA 2026) for borrows of locals as a
later step.

**T3. Forced constructor fields and dead relevant arguments.** Measure how many `VCons` cells
a `Vec` program builds and how often a matched `n` is read, then write a short note on not
storing a forced index (Brady, McBride and McKinna; Allais ESOP 2023 §2.1) and on dropping
a parameter that is only passed to itself. Shared decision in `erasure.rs` for JS and the
runtime; the codec puts fields back at the boundary.

**T4. SW-813 design note: the call path.** Start from native-compilation.md §1.2–1.3 (37 ns
per call; 19% dispatch; frame push and pop, register clearing, RC). Candidates: size the
register vector once, don't clear registers that are written before read, unbox `Ret` for
the common cases. Record why tail-call dispatch is out for now (Keeter 2026: 1.5–2× faster
natively, 1.2–4.6× slower in Wasm engines; needs nightly `become`), and what would bring it
back.

**T5. JS `Nat` representation: measure, then decide.** Profile day 2's brute force under
`--js`; micro-benchmark `Nat` addition and comparison as `bigint` and as `number` in Node 22.
If the gap is large, write a note: canonical `number` below 2^53, `bigint` above, guarded
operations, natives and `NumCase` for both, the codec at the boundary unchanged. Decision
D1922.

**T6. SW-112 design note, with a recommendation.** Fold §5.1 into the note SW-112 asks for:
`Array` specified over `List` (or `Vec`), natives bound by hash with differential tests,
`set` in place when unique (`Rc::get_mut`), a count of copies in `--stats`, and the JS
choice (copying `set`, or a persistent vector). Decision D1920.

**T7. Shift and bitwise natives: corner-case tests.** When SW-808's `Nat` xor/and/or/shift
natives are added, test shift amounts 63, 64, 65 and far beyond, and operands either side of
2^64, on the reference evaluator, machine, native code and JS. CertiCoq-Wasm (CPP 2025) found
an unsoundness in Rocq's primitive integers from exactly this (a shift treated like C's, where
Wasm takes it modulo the width).

**T8. A "runs in place" report.** For a program or a std function, say which matches reuse
their cell and which allocate, and why (shared value, size mismatch, a borrow). From FP²'s
`fip` check (ICFP 2023), as a report rather than a type, in the spirit of effects.md T5. Use
it on `Map.Tree.insertWith` before SW-814's fused balance, and on merge sort.

**T9. Refresh this register quarterly**, and finish the sweep the search budget cut short
(§9). Next: January 2027.

## 8. Decisions

- **D1920.** For SW-112, write the design note around a list-specified `Array` with in-place
  update on unique values in the machine and native code (Lean's model, as compact text
  did for `Text`), rather than a persistent tree or a uniqueness type? **[Yes: design note
  T6; build only after it and a JS choice.]**
- **D1921.** Spend a lane on counting reference-count operations (T2), as the gate for a
  borrowed-parameters design? **[Yes: the count is small; the design only if increments
  and decrements are a large share.]**
- **D1922.** Measure small `Nat`s as JS `number`s (T5) now, or leave `--js` as it is
  because native code is the CLI's speed route? **[Measure now: JS is the faster runner on
  parse-heavy programs (SW-593), so its arithmetic gap matters.]**

## 9. Sources not reached

- **Web search budget.** The session's shared limit (200 searches across all agents) ran out
  after Q36. Not searched, and so not screened: Unison's runtime since 2024 (fast-runtime.md
  says the Chez runtime appears shelved, from a secondary source); Idris 2's Chez and RefC
  backends since 2023; MLKit and region inference since 2022; deforestation and fusion
  papers in strict languages (2022–2026); Koka's benchmark results since 2024; persistent
  vectors (RRB) in functional runtimes; Larose et al., "AST vs. Bytecode" (OOPSLA 2023);
  Kalibera and Jones (classic) on rigorous benchmarking; Lorenzen's thesis; Roc's own docs.
  Rerun these first in the quarterly refresh.
- **PDFs that didn't download.** FP² and frame-limited reuse (Microsoft Research serves an
  HTML page to `curl`); the borrows paper (theory.stanford.edu refused the connection);
  lambda set specialisation (MIT's copy came back empty). Their cards rest on abstracts.
- **Pages not opened.** Lean 4.30 release notes (quoted from search); wasmi 0.32 post; the
  CPython posts; the V8 BigInt post; wasm_of_ocaml's posts. Their claims are marked
  **[unverified]**.
- **Not confirmed.** Whether Rust's `become` has been stabilised since April 2026; whether
  general Wasm stack switching (beyond JSPI) ships in any browser.
