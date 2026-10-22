# Practical languages with proofs: a survey, and what Stitchwort might adopt

**Date:** 22 October 2026. **Ticket:** SW-327. **Kind:** research note (design-review gate:
research, write, stop for review). Nothing is implemented. Decisions D559 to D562 are in §8.

Stitchwort's mission is "to be a practical programming language in which you can prove theorems
about your programs". Several other languages share some or all of that aim, and they made
different choices about where proofs live, what does the proving, and what is trusted. This note
surveys them, then asks what each choice would mean for us. It can be read without knowing type
theory: words are explained where they first appear.

Labels, as in the other comparison notes:

- **[checked]**: read in Stitchwort's source, docs or board at the commit below;
- **[cited]**: taken from a page that the research pass fetched on 22 October 2026 (URL in
  [Sources](#sources));
- **[inferred]**: my reasoning from checked or cited facts;
- **[unverified]**: believed (from memory or a search-result snippet), not confirmed against a
  primary source.

**Method.** Stitchwort facts were checked at `a4659eba`. The web research was split into four
passes (Lean 4; F*, Dafny, SPARK and Liquid Haskell; Rust verifiers and Koka; Idris 2, Agda,
Rocq, Isabelle, ACL2, ATS and newer languages), each fetching official docs, release notes,
papers and repositories. Some primary sources didn't load: Isabelle's manuals (PDF),
acl2.org (HTTP 403), Idris 2's elaborator-reflection page (404), F*'s effects tutorial page
(404), and some Dafny reference sections (cut off). Claims that depend on them are marked
**[unverified]**. Where a source is a search snippet rather than a page that was read, it says so.

## Contents

1. [Summary](#1-summary)
2. [Where Stitchwort stands](#2-where-stitchwort-stands)
3. [The languages](#3-the-languages)
4. [Patterns across the field](#4-patterns-across-the-field)
5. [What we might adopt, topic by topic](#5-what-we-might-adopt-topic-by-topic)
6. [Ranked shortlist](#6-ranked-shortlist)
7. [Deliberate differences: what not to adopt](#7-deliberate-differences-what-not-to-adopt)
8. [Decisions for Matt](#8-decisions-for-matt)
9. [Sources](#sources)

---

## 1. Summary

**The field splits three ways on one question: who does the proving, and who is trusted?**

| Family | Languages | Who proves | What is trusted |
|---|---|---|---|
| **Solver-backed contracts** | Dafny, F*, SPARK/Why3, Liquid Haskell, Verus, Creusot, Prusti, Flux | An SMT solver (Z3, CVC5, Alt-Ergo) proves verification conditions generated from `requires`/`ensures`/refinements | The solver, the tool's encoding of the program, and the compiler |
| **Small kernel, automation outside it** | Lean 4, Rocq, Isabelle/HOL, Agda, Idris 2, Aeneas (Rust to Lean), Stitchwort | Tactics, decision procedures or plain proof terms; their output is re-checked by a small kernel | The kernel (plus whatever escape hatches a proof opts into) |
| **Executable logic** | ACL2 | A rewriting prover over a total first-order Lisp | The prover and the Lisp |

Stitchwort is in the second family, and is stricter than most members of it: `omega` is checked by
running a checker written in Stitchwort inside the kernel, not by trusting compiled code
(`docs/proposals/omega.md`) **[checked]**, and non-termination is in the type (`{Partial}`), as F*'s
`Dv` effect is and Lean's `partial` is not (`docs/compared.md` §1) **[checked]**.

**What the others have that we don't yet, and that our own evidence asks for:**

1. **Counterexamples before proofs.** Isabelle runs Quickcheck and Nitpick on a lemma's statement
   and shows a counterexample before you try to prove it **[unverified: manuals didn't load]**;
   Lean has Plausible **[cited]**. Spec bugs are a recurring finding in the deployments we found
   (Cedar, SymCrypt, verify-rust-std) **[cited]**. Stitchwort's evaluator could do this for us cheaply.
2. **Goals at holes, and editor actions on them** (Agda, Idris 2's `:casesplit`/`:proofsearch`,
   Lean's infoview). Already designed for us as LSP stage 2 (SW-31, D497) **[checked]**; Idris's
   command set is a good checklist for what comes after.
3. **Rewriting automation** (`simp` in Lean and Isabelle, ACL2's rewriter, Liquid Haskell's
   "proof by logical evaluation"). Our proofs are long mostly because of small rewriting steps
   and generic helper lemmas (day 8: 840 proof lines, 28 new Std lemmas, 17 local helpers)
   **[checked: aoc-day08-gaps.md]**.
4. **Arithmetic automation**, which every family has. Ours is `omega` stage 1; arithmetic friction
   has come up on 6 of 8 AoC days **[checked]**. Stage 2 (`-`, `max`/`min`, `/` and `%` by a
   number, `Int`) is the most-evidenced item in this note.
5. **Libraries that ship with their lemmas.** Lean's `Std.HashMap` and `TreeMap` come with lemma
   suites, and string functions are being verified in the core release stream **[cited]**.

**What we already do that the field treats as hard-won:** a kernel that re-checks every term
(Aeneas/SymCrypt calls this what makes agent-written proofs safe to accept **[cited]**);
partiality in the type (F*'s `Dv` is the closest **[cited]**); a list of every assumption a
result depends on (`stitchwort assumptions`, as Lean's `#print axioms` and Rocq's
`Print Assumptions` do) **[checked; Lean cited]**; differential testing of compiled code
against the reference evaluator (Cedar's method for Rust against its Lean model **[cited]**);
and a compiler that runs entirely in the browser (`docs/compared.md` §2) **[checked]**.

The ranked shortlist is in §6. In one line each: (1) counterexample search; (2) goal holes and
hole actions; (3) `omega` stage 2; (4) a lemma-complete Std policy; (5) a `simp`-like rewriting
term, design first; (6) `{x: T | p}` refinement sugar over records; (7) an "assurance ladder"
in the docs; (8) in-place `Array` via uniqueness, designed now and built when a program needs it.

---

## 2. Where Stitchwort stands

What matters for the comparison **[checked: DESIGN.md §2-§8, docs/syntax.md, docs/proposals/]**:

| Aspect | Stitchwort today |
|---|---|
| Trust | A small kernel (`crates/core`, about 12,000 lines of Rust including its evaluator) re-checks every elaborated term. "Every unchecked assumption is visible" (principle 3). |
| Proofs | Terms, not tactics: `rfl`, recursion as induction, `calc`, `rewrite`, `auto` (instances, hypotheses, decision procedures), `omega` (linear `Nat` arithmetic by a checked certificate). |
| Termination | Total by default; structural recursion, `decreasing <measure>` (compiled to structural recursion with hidden fuel, so the kernel is unchanged), and `{Partial}` in the type for loops that may not end. |
| Erasure | A value is erased if its type is in `Prop` or it is a type. Indices of data families are stored. No quantities. |
| Effects | Abilities: algebraic effects as data, with deep, multi-shot handlers; `IO`, `Abort`, `Each`. |
| Running | Reference evaluator (the kernel's), a fast untrusted runtime (`crates/rt`), and JS output with `.d.ts` types and boundary checks; differential tests between them. |
| Tests | `test` declarations are closed `Bool` expressions, cached by hash; property tests are "later" (DESIGN §7). |
| Tooling | Playground (WASM), `stitchwort lsp` (stage 1: errors, navigation), VS Code client; goal holes are the next stage. |

**Recurring pain points from the AoC notes** (this note's evidence for "what problem of ours does
it solve"):

| Pain | Days | Source | Ticket |
|---|---|---|---|
| Arithmetic needs lemmas by hand | 1, 2, 3, 5, 7, 8 | aoc-day08-gaps.md §7 | SW-314/315 done (stage 1); stage 2 open |
| `Decidable.toBool` leaks into goals | 2, 4, 5, 6, 8 | same | SW-206 |
| Generic Bool/List helpers written in each proof | 4, 8 (17 on day 8) | same, §4.3 | none |
| Proofs are long: 873 lines (day 2), 893 (day 4), 840 (day 8) | most | community notes §3 "Proofs" | none |
| Congruence lemmas under binders (`sumByCongr` ×4 …) | 6 | aoc-day06-community.md | D37 |
| `Array` wanted, measured as not needed | 4, 7, 8 | aoc-day08-gaps.md §6.3 | SW-112 |
| Pattern lambdas opaque to proofs | 8 | aoc-day08-gaps.md §5.1 | done (SW-319) |
| Others' proofs stop at `sorry` where ours close | 2, 3, 5, 6 | community notes | (a strength) |

The last row matters for tone: on the AoC days, the community Lean and Dafny proofs that exist
mostly prove helper facts and leave the main theorem open (`sorry`, `{:axiom}`), while ours prove
the answer for all inputs **[checked: community notes §3]**. Their proofs are shorter per fact
because of automation, which is the gap this note looks at.

---

## 3. The languages

Each entry: the core idea; what a proof looks like; how it stays practical; pain points; adoption.
Code is illustrative unless marked as quoted.

### 3.1 Lean 4

**Core idea.** A dependently typed language that is both a proof assistant and a general-purpose
language, compiled to C, with a small kernel. Current stable release 4.35.0 (12 October 2026)
**[cited]**.

**Programs.** `do` blocks with `let mut`, `for`, `break`, `continue` and early `return`, all
desugared into monadic folds (`ForIn`, `ForInStep.yield`/`done`); `for h : i in [0:xs.size]`
gives the body a proof that `i` is in range, which pays for `xs[i]` **[cited]**:

```lean
def sumTo (n : Nat) : Nat := Id.run do
  let mut total := 0
  for i in [0:n] do
    total := total + i
  return total
```

**Recursion, five ways** **[cited: Lean reference, Recursive Definitions]**: structural (the
kernel computes with it); well-founded with `termination_by`/`decreasing_by` (compiled through
`WellFounded.fix`; "frequently slow to compute with" and "work poorly in types", so you get
equation lemmas instead); `partial_fixpoint` (no termination proof; an unfolding equation, and
for `Option` results, partial-correctness theorems); `partial` (an opaque constant: only needs an
inhabited result type, can't be reasoned about); `unsafe` (anything, and it spreads to callers).
`@[implemented_by f]` swaps the compiled code while the kernel keeps the original. All compiled
code runs the recursion as written, not the `fix` encoding.

**Automation, and what each trusts** **[cited]**:

| Tactic | How | Trust beyond the kernel |
|---|---|---|
| `simp`, `rw` | rewriting with lemma sets, producing proof terms | none |
| `omega` | search in meta-code; each step's justification becomes a proof term applying small lemmas (`Lean/Elab/Tactic/Omega/Core.lean`) | none |
| `decide` | reduce a `Decidable` instance to `isTrue h` | none |
| `native_decide` | run the instance compiled | the whole compiler and every `implemented_by`; shows up in `#print axioms` |
| `bv_decide` | bit-blast to SAT (CaDiCaL), check its LRAT proof with a verified checker run compiled | the compiler (`Lean.ofReduceBool`) |
| `grind` (4.22, Aug 2025) | SMT-style: congruence closure, E-matching on `@[grind]` lemmas, case splits, theory solvers (`cutsat` for linear integers, rings, fields) | none stated; produces proof terms |

So Lean's `omega` is proof-producing but not reflective; ours replays a certificate through a
checker proved once, the way Rocq's `lia` does (`docs/proposals/omega.md`) **[checked; Lean
cited]**.

**Running fast.** Reference counting, with in-place update when a value is uniquely referenced:
`Array.set`/`push` mutate if nobody else holds the array, and copy otherwise; constructor cells
are reused ("Counting Immutable Beans", IFL 2019) **[cited]**. The new LCNF compiler backend was
completed in 4.30 (May 2026), with user borrow annotations `@&` **[cited]**. Array indexing
`a[i]` needs a proof `i < a.size`, found by `get_elem_tactic`; `a[i]?` returns an `Option` and
`a[i]!` panics **[cited]**.

**Tooling.** Lake (build tool, remote artifact cache), Reservoir (package index), `#eval` in the
editor, `#print axioms`, Plausible (property testing with shrinking) **[cited]**; infoview goal
display, `?_` holes, `exact?`/`apply?`/`simp?` suggestions **[cited: tactic index; infoview
unverified]**. Verso builds the reference manual with checked examples **[cited]**.

**Pain points** (mostly the FRO's own roadmap admissions) **[cited]**: `simp` and `grind`
performance; well-founded definitions don't compute; `cutsat` coefficients grow large; breaking
changes in most releases (about one release a month in 2026); Mathlib depends on a deprecation
system to cope with churn. `simp` brittleness across versions is widely discussed
**[unverified]**.

**Adoption** **[cited]**: AWS Cedar (an authorization language) keeps an executable Lean model
about 10× smaller than its Rust implementation, proves properties of the model, and
differential-tests the Rust against it; "no new Cedar version is released unless its model,
proofs, and differential tests are current". SampCert (differential privacy samplers, PLDI 2025);
LNSym (Arm machine code); Strata (AWS); Microsoft SymCrypt via Aeneas (§3.12). The official pages
give no user counts.

### 3.2 Idris 2

**Core idea.** A dependently typed language aimed at programming, built on quantitative type
theory: every binder has a quantity, `0` (erased: compile time only), `1` (used exactly once at
run time) or unrestricted **[cited]**. Self-hosted; backends Chez Scheme (default), Racket,
Gambit, JavaScript/Node, and C with reference counting **[cited]**. Latest release found: 0.8.0
(31 October 2025) **[cited]**.

**Totality.** Functions must be `covering` by default; `%default total` or `--total` makes
totality the default, and `partial` opts out. Only total functions are evaluated during type
checking **[cited]**. There is no user-written measure like our `decreasing`; you restructure the
function **[unverified]**.

**Editing.** The best-documented hole workflow: `:addclause` writes a skeleton with holes,
`:casesplit` splits a variable and drops cases the types rule out, `:addmissing` adds missing
clauses, `:proofsearch` fills a hole from locals, constructors and hint functions, `:makewith`
adds a `with` clause; `!` variants edit the file **[cited]**.

**Pain points** **[unverified]**: small library and community, slow checking on large projects,
long unification errors, quantity inference that surprises newcomers.

**Adoption.** About 3,100 GitHub stars **[cited]**; industrial use negligible **[unverified]**.

### 3.3 F\*

**Core idea.** "A general-purpose proof-oriented programming language": dependent types and
refinements, an effect system built on Dijkstra monads (each computation's type carries a
weakest precondition), proof obligations sent to Z3, and Meta-F* tactics for what Z3 can't do
**[cited]**.

**Effects.** `Tot` (total), `GTot`/`Ghost` (erased), `Dv` (may diverge), state effects (`ST`,
`Stack`), `ML` (anything). `Dv t` "may run forever, but if it terminates then the resulting value
has type t". `Tot` code can't call `Dv` code, there are no separate lemmas about `Dv` functions
(specs go in the type), and top-level `Dv` bindings must still be total, so a looping
`dv_false : Dv False` can't prove `False` **[cited]**. This is the closest design to our
`{Partial}`.

```fstar
let rec collatz (n:pos) : Dv (list pos) =
  if n = 1 then [n]
  else if n % 2 = 0 then n :: collatz (n / 2) else n :: collatz (3 * n + 1)
```
(quoted from the F* book **[cited]**)

**Running fast.** Extraction to OCaml, F#, and, through the Low* subset and KaRaMeL, to C and
WebAssembly **[cited]**. Low* models C memory with regions and buffers, with liveness and
disjointness obligations **[unverified]**.

**Pain points** **[unverified]**: SMT instability (resource limits, fuel settings, hint files);
generic failure messages ("could not prove post-condition"); steep learning curve; a large
trusted base (Z3, F*'s own checker, extraction, the C compiler).

**Adoption** **[cited]**: HACL* (verified crypto extracted to C) and EverCrypt ship in Firefox,
the Linux kernel and WireGuard; EverParse parsers are used in Windows Hyper-V.

### 3.4 Dafny

**Core idea.** An imperative and functional language with specifications built in: `requires`,
`ensures`, `modifies`, `reads`, loop `invariant`s and `decreases`, verified through Boogie and Z3.
The user writes annotations and lemmas; the solver fills in the reasoning ("auto-active")
**[unverified: standard description]**.

```dafny
lemma Foo(n: nat) ensures F(n) == G(n) { if n > 0 { Foo(n-1); } }   // induction is a recursive call
```

**Ghost code.** "The `ghost` modifier is used to mark entities as being used for specification
only, not for compilation to code" **[cited]**. Functions are ghost unless given a `by method`
body **[cited]**.

**Partiality.** Functions live in the logic and must terminate; methods and loops may be marked
`decreases *` ("possibly non-terminating") **[cited]**.

**Running.** Compiles to C#, Java, Go, JavaScript, Python and (contested) Rust **[unverified]**;
`{:extern}` bodies are written in the target language **[cited]**; `expect` statements are
checked at run time **[unverified]**.

**Pain points.** AWS's Dafny team calls proof brittleness ("small changes to an SMT query"
causing wildly varying results or failure) the biggest threat to adoption, finds that
verification cost predicts future instability, and proposes a CI check that rejects code which
verifies but costs too much **[cited: POPL'25 Dafny workshop abstracts]**. Dafny added `opaque`
functions and a `hide` statement to cut what the solver sees **[cited]**, and attributes such as
`{:isolate_assertions}` and `{:rlimit}` **[cited: names only]**.

**Adoption** **[cited]**: AWS Encryption SDK and related libraries written in Dafny and
translated to Java and .NET; Cedar was first modelled in Dafny before Lean **[cited: snippet;
timelines disagree]**. The Dafny AoC solutions in our community notes (Hath995) are the closest
community proofs to ours on days 1, 3 and 5 **[checked]**.

### 3.5 Liquid Haskell

**Core idea.** "Refines Haskell's types with logical predicates": `{v: Int | v > 0}`, checked by
an SMT solver, now as a GHC plugin **[cited]**. Laws are written "as Haskell functions and
verified with equational proofs. Induction is recursion, and case analysis is pattern matching"
**[cited]**.

```haskell
{-@ head :: {xs:[a] | len xs > 0} -> a @-}
{-@ appendAssoc :: xs:[a] -> ys:[a] -> zs:[a] -> {(xs ++ ys) ++ zs == xs ++ (ys ++ zs)} @-}
appendAssoc [] _ _ = ()
appendAssoc (_:xs) ys zs = appendAssoc xs ys zs
```

**Automation.** "Proof by logical evaluation" (PLE) unfolds calls to terminating user functions
"only when the verifier can prove that a single case definitely applies" **[cited: snippet of the
liquid-fixpoint docs]**. That is a narrow, predictable form of `simp`, and close to what our
kernel's conversion already does by computation **[inferred]**.

**Pain points.** The PLDI 2025 paper "Adoption Barriers for Liquid Types" names nine barriers
across developer experience, scalability and understanding the verifier **[cited: title and
abstract snippet]**; failures historically showed the condition but not which facts were missing
**[cited: Tweag 2022]**; a 2025 thesis notes the lack of goal inspection **[cited: snippet]**.

**Adoption.** Research case studies; no named production deployment found **[cited/unverified]**.

### 3.6 Agda, and agda2hs

**Core idea.** Total, dependently typed, proofs are programs, no tactics; edited interactively
with holes **[cited]**. The closest relative of Stitchwort's term-mode proofs.

**Termination.** Structural recursion and lexicographic descent; `TERMINATING` turns the check
off and is refused under `--safe`; `NON_TERMINATING` runs at run time but never reduces during
type checking **[cited]**. Well-founded recursion is written by hand with `Acc` **[unverified]**.

**Erasure.** `@0` marks run-time-irrelevant arguments; erased variables can't be used at run
time, and an erased value can be matched only when at most one case is possible **[cited]**. So
`Vec A : @0 Nat → Set` stores no length.

**agda2hs.** Compiles a restricted subset of Agda to readable Haskell, so you prove in Agda about
the code that ships ("Reasonable Agda is Correct Haskell", 2022) **[cited]**. A small, explicit
"executable fragment" with a faithful mapping, the same idea as our JS export's first-milestone
scope (DESIGN §12) **[checked; inferred link]**.

**Pain points and lessons** **[unverified]**: a standard library with deep algebraic hierarchies
(setoids, `Relation.Binary`) that is powerful but slow to check and hard to learn.

### 3.7 Rocq (formerly Coq)

**Core idea.** The Calculus of Inductive Constructions, tactic proofs, a small kernel; renamed
Rocq in 2025 **[cited: about page; version unverified]**.

**Proof by reflection: `lia`.** The pattern our `omega` follows. An untrusted oracle finds a
certificate (a Positivstellensatz refutation with cutting planes and case splits); the goal is
reified into syntax; a checker written in Rocq, with a soundness theorem, is run by the kernel's
`vm_compute`, and `reflexivity` closes the goal. `zify` first moves `nat` and others into `Z`
**[cited: micromega reference]**. `native_compute` adds the OCaml compiler to the trusted base
**[unverified]**.

**Extraction.** To OCaml, Haskell or Scheme. `Extract Constant` strings are copied verbatim and
"it is the responsibility of the user to ensure that the ML terms … do have the expected types";
inconsistent axioms "may lead to incorrect or non-terminating extracted terms" **[cited]**. The
classic trap is realising `nat` as a machine integer **[unverified]**.

**Well-founded recursion.** `Equations`/`Program Fixpoint` take a measure, discharge decrease
obligations by a default tactic, and generate unfolding lemmas because `Acc`-based definitions
don't compute well **[unverified]**. Our `decreasing` makes the same trade with `f.unfold`
(`well-founded-recursion.md`) **[checked]**.

**Adoption** **[unverified]**: CompCert (verified C compiler), Fiat-Crypto (code in BoringSSL),
Iris, MathComp.

### 3.8 Isabelle/HOL (and CakeML)

**Core idea.** An LCF-style kernel for higher-order logic (no dependent types), structured Isar
proofs, and heavy automation (`simp`, `auto`, `blast`, `metis`, `smt`) **[cited: overview]**.

**Sledgehammer.** Calls external provers (E, Vampire, Z3, cvc5, …); on success it suggests a
one-line proof (`by (metis lemma1 lemma2)`) that Isabelle re-proves in its kernel, so the external
prover is never trusted **[cited: overview says it calls external provers; reconstruction
details unverified]**. The suggestion is pasted into the source, so later checks are fast and
don't need the external tool **[unverified]**.

**Counterexamples.** Quickcheck (random, exhaustive and narrowing tests of executable statements)
and Nitpick (a finite model finder) run in the background as you state a lemma, so a false
statement is reported before you try to prove it **[unverified: manuals didn't load]**.

**Code generation.** `export_code` to SML, OCaml, Haskell and Scala **[cited]**; refinement
frameworks swap abstract sets for efficient structures and reach verified LLVM code
**[unverified]**. seL4 was verified in Isabelle **[unverified]**. CakeML (HOL4) is a verified ML
compiler that bootstraps itself, with a proof-producing translation from HOL functions **[cited]**.

### 3.9 ACL2

**Core idea.** A first-order logic of total recursive functions that *is* a subset of Common
Lisp, so definitions run at Lisp speed. Every `defun` is admitted by proving termination with a
measure (default guessed); "guards" are preconditions that, once verified, let execution use raw
Lisp primitives without checks **[unverified: acl2.org returned 403]**. Proofs are driven by a
rewriter (the "waterfall"), steered by lemmas the user proves in the right shape **[unverified]**.

**Adoption.** AMD (floating-point division, from the K5), Centaur/VIA, IBM, Intel and others are
reported **[cited: search snippets only]**. The lesson is the rewriter: users "teach" the prover by
stating lemmas as rewrite rules, which is how `simp` sets work too **[inferred]**.

### 3.10 ATS

**Core idea.** Dependent and linear types for C-level programming; the aim is to be "as efficient
as C/C++"; out-of-bounds indexing is a compile-time error **[cited]**. Indices are restricted to
simple sorts (integers, booleans) decided by a constraint solver, with proofs as separate total
functions **[unverified]**. Pain points: dense syntax, thin documentation, one main maintainer
**[unverified]**.

### 3.11 Why3 and SPARK Ada

**Core idea.** Contracts on imperative code. SPARK is an Ada subset with `Pre`, `Post`, loop
invariants and data-flow contracts; GNATprove sends conditions through Why3 to Alt-Ergo, CVC5 and
Z3 **[cited/unverified]**.

**Assurance levels** **[cited: SPARK user guide]**: *stone* (valid SPARK), *bronze* (flow
analysis: no uninitialised reads), *silver* ("the program does not raise an unexpected exception
at run time"), *gold* (key integrity properties), *platinum* ("full functional correctness",
"rarely reached and usually applied to small parts of an application").

**Specs as tests.** `-gnata` "enables verification of all invariants and contracts at run time",
so one contract text is either executed in tests or proved **[cited]**. Ghost code is marked
`Ghost` and not compiled **[cited]**.

**Adoption.** NVIDIA moving safety-critical firmware to SPARK (2019 announcement); tool
qualification under EN 50128 and ISO 26262 **[cited: AdaCore pages/snippets]**.

### 3.12 Proofs about Rust: Verus, Creusot, Prusti, Aeneas, Flux (and Kani)

All lean on Rust's ownership rules (no aliasing of mutable data) to reason about mutation almost as
if the program were pure **[cited]**.

| Tool | Approach | Mutation | Kernel-checked? | Evidence |
|---|---|---|---|---|
| Verus | Z3; `spec`/`proof`/`exec` modes, ghost linear permissions | ownership plus permission tokens | no | SOSP 2024: 6.1K lines of code, 31K of proof, across five systems **[cited]** |
| Creusot | Why3; Pearlite specs (`#[requires]`, `#[ensures]`) | "prophecies": a `&mut` has a current and a final value | no | CreuSAT (a verified SAT solver) **[cited]** |
| Prusti | Viper (permission logic) | ownership encoded as permissions | no | stale tooling **[unverified]** |
| **Aeneas** | translates safe Rust into a pure Lean (or Coq, F*, HOL4) model | "backward functions": ending a borrow returns the new value | **yes** (Lean kernel) | Microsoft SymCrypt **[cited]** |
| Flux | refinement types for Rust | strong references to unique data | no | about half Prusti's spec lines, about 10× faster **[cited]** |
| Kani | bounded model checking (CBMC) | explicit memory model | no | used in 6 of 9 completed verify-rust-std challenges **[cited]** |

**Aeneas and SymCrypt** is the most relevant data point for us **[cited: MSR blog and arXiv
2609.15648, September 2026, v1]**. Rust `fn ntt(&mut [u16; 256])` becomes
`ntt : Array U16 256#usize → Result (Array U16 256#usize)`: mutation becomes a function from old
value to new, and panics become `Result` failures. ML-KEM and SHA-3 are fully proved (237 KLOC of
Lean for 16.7 KLOC of Rust) and ship in Windows insider builds; the specs mirror the NIST
standards and are executable against test vectors; proofs found real bugs. Most proofs were
written by AI agents and accepted because the Lean kernel checks them, but humans must review
the *statements*, since agents "cheat" by weakening goals or adding assumptions. The trusted base is
listed explicitly (Charon and the Aeneas translation, the Lean kernel, `native_decide`/`bv_decide`, 122
lines of modelled intrinsics and 11 axiomatised shims).

**verify-rust-std** (AWS, Rust Foundation): after about a year, roughly 4% of `core`'s unsafe
functions have contracts, and two *specification* bugs were found **[cited: arXiv 2510.01072]**.
Specification cost, not solver power, limits coverage **[inferred]**.

### 3.13 Koka, and other effect languages

**Koka** has no proofs; it is here for effects and memory **[cited unless marked]**.

- Row-typed effects, inferred, with `total` as the empty row; handlers may resume once, never, or
  more than once.
- Handlers compile by "generalized evidence passing" (ICFP 2021) to plain lambda calculus and
  then to C, JS or WebAssembly. Tail-resumptive operations (resume once, at the end: state,
  reader) run in place without capturing a continuation **[cited: snippets]**.
- **Perceus** (PLDI 2021): precise reference counting with reuse: when a matched value is
  uniquely referenced, the new constructor reuses its memory. "Functional but in-place" (FBIP).
- **`fip`/`fbip`** (FP², ICFP 2023; keywords since Koka 2.4.2): a checked annotation that a
  function runs with no allocation and constant stack when its arguments are unique.

**Others.** OCaml 5 effects are untyped and one-shot ("multi-shot deliberately omitted"), and
one-shot is what makes its cheap fibers possible **[cited]**. Unison abilities (whose name
we share) are multi-shot, follow Frank, and use `->{}` for explicitly pure **[cited]**. Effekt
uses lexical handlers and "contextual effect polymorphism" **[cited]**.

**Lesson** **[inferred]**: reference counting with in-place reuse needs to know a value is unique.
A multi-shot continuation that may be resumed twice holds its captured values twice, so they
must count as shared. A fast path for tail-resumptive handlers is compatible with multi-shot
semantics, because it only applies where the continuation is never captured.

### 3.14 Newer entrants, briefly

- **Pie** (The Little Typer): a finished teaching language with `TODO` holes **[cited]**. A model for
  hole UX in learning material, not for programs.
- **Aya**: dependent types with cubical equality, JIT-compiles to Java (about 10× faster than its
  interpreter on a tree sort) **[cited]**. Research-stage.
- **Kind**: a "minimal proof checker", rewritten in Haskell **[cited]**. No evidence of use.
- **Narya** (higher-dimensional type theory) and **Dex** (typed array indices, no proofs)
  **[cited]**: research, low relevance.
- **Granule**: graded modal types (how many times a value is used, as a number in the type)
  **[cited: snippet]**. Relevant only if we ever want "this continuation is resumed at most once"
  in the type.
- **Nomos**: session types plus resource bounds for smart contracts **[cited: snippet]**. Low
  relevance.

---

## 4. Patterns across the field

**4.1 Trust: where each language puts its reasoning.**

| Language | Proof checker trusted | Plus |
|---|---|---|
| Stitchwort | kernel (`crates/core`) | `assume`, foreign functions, handler conjecture: all listed by `stitchwort assumptions` **[checked]** |
| Lean 4 | kernel | the compiler, if a proof uses `native_decide`/`bv_decide` (listed by `#print axioms`) |
| Rocq | kernel | `native_compute`; extraction strings |
| Isabelle | kernel | code-generator mappings |
| Agda, Idris 2 | type checker | FFI pragmas |
| F*, Dafny, SPARK, LH, Verus, Creusot, Flux | the tool and its encoding | Z3 or another solver; extraction |

**4.2 The "find outside, check inside" pattern** is how the kernel-based languages get
automation without growing the trusted base: Sledgehammer (outside prover, kernel replay), Rocq's
`lia` (outside oracle, checker inside), Lean's `omega` and `grind` (meta-code search, proof terms),
`bv_decide` (SAT solver, LRAT certificate). Our `omega` already follows it **[checked]**. Every
new piece of automation we add can follow it too.

**4.3 Solver-backed languages pay for automation with instability.** Dafny's team calls
brittleness its biggest adoption threat; F* and Dafny grew resource limits, fuel settings, opacity
and hint files to manage it **[cited/unverified as marked in §3.3-§3.4]**. Their proofs are short
when they work, and their failures say "might not hold" without saying why. Our proofs are longer
but deterministic: a term that checks today checks tomorrow, and the cache keys on content
(DESIGN §11) **[checked; contrast inferred]**.

**4.4 Specs are the weak point in every deployment.** Cedar found 4 bugs while proving and 21 by
differential and property testing **[cited]**; verify-rust-std found two specification bugs
**[cited]**; SymCrypt's humans review statements because agents weaken them **[cited]**. The
tools that help here are executable specs (SymCrypt tests specs against standard vectors),
counterexample finders (Isabelle, Lean's Plausible), and runtime-checked contracts (SPARK's
`-gnata`).

**4.5 Programs and proofs: same code, or model and implementation?** Lean (SampCert), Idris, Agda,
ACL2, Dafny and we prove things about the code that runs. Cedar proves things about a model and
differential-tests the shipped Rust against it; Aeneas proves things about a model generated from
the shipped Rust **[cited]**. Our JS export plus differential tests can support both styles: a
proved Stitchwort module can ship as JS, or be the reference that another implementation is
tested against **[inferred]**.

**4.6 Agents change the economics.** SymCrypt reports that new algorithms now take "about a week
of agent work plus days of human review" against six months for the first **[cited]**. That
favours languages where the checker is small and the statement is what humans read, which is our
design **[inferred]**.

---

## 5. What we might adopt, topic by topic

Each candidate: what it is and who has it; how it fits our architecture (small kernel, effects as
data, total by default, JS/WASM); what problem of ours it solves; rough cost; risk; verdict.
Costs are lane-days, rough **[inferred]**.

### 5.1 Automation: SMT, reflection, tactics, rewriting, `decide`

| Option | Who | Fit for us | Our problem | Cost | Risk | Verdict |
|---|---|---|---|---|---|---|
| SMT solver in the trusted path | Dafny, F*, LH, Verus | Breaks principle 4 (small kernel); no Z3 in the browser without a large WASM build **[inferred]** | proof length | large | trust, instability | **No** (D562) |
| SMT as an untrusted oracle with proof replay | Isabelle Sledgehammer, CoqHammer | Fits "find outside, check inside", but needs a reconstruction engine (a `metis`-like prover inside our terms) | proof length | very large | engineering size | Not now |
| Reflection with certificates | Rocq `lia`, our `omega` | Already the design | arithmetic (6 of 8 days) | stage 2: medium | check speed (SW-321) | **Yes: `omega` stage 2** |
| `decide` | Lean, Rocq | We have it as `auto` with a decision procedure, and `test` | none new | none | none | Have it |
| Rewriting term (`simp`-like) | Lean `simp`, Isabelle `simp`, ACL2 rewriter, LH PLE | An untrusted search that emits ordinary `rewrite`/`calc` terms; the kernel checks the result as today | long proofs; helper lemmas; `*Congr` lemmas (day 6) | large | brittleness (Lean's experience), large proof terms, check time | **Design note** (D560) |
| E-matching (`grind`) | Lean 4.22+ | Same pattern as `simp`, harder | as above | very large | as above | Later, after `simp` |

**A `simp`-like term, narrowly.** The lesson from Lean, Dafny and Liquid Haskell is that
*predictable* automation is worth more than *powerful* automation. Liquid Haskell's PLE unfolds a
definition only when exactly one case applies, and `simp only [lemma1, lemma2]` with an explicit
list is the form Lean users are told to leave in finished proofs (`simp?` prints it)
**[cited]**. A first version for us could be `simp [eqs]`: rewrite left to right with the listed
equations and the definitions' own equation lemmas (`equation-lemmas.md`, built **[checked]**),
under binders (which is what the `*Congr` lemmas do by hand), and emit an ordinary term. No global
`@[simp]` set at first: a global set is where brittleness comes from **[inferred]**.

### 5.2 Refinement types and contracts versus dependent types

Refinement types (`{v: Int | v > 0}`; LH, Flux, F*) and contracts (`requires`/`ensures`; Dafny,
SPARK, Creusot) are less expressive than full dependent types, but cheap to write for the common
cases: bounds, non-emptiness, ranges. We already express these with records that carry a proof
field (`type Dial (highest: Nat) = { position: Nat, inRange: position <= highest }`), and
`auto` discharges literal cases **[checked: docs/syntax.md]**.

- **Candidate: `{x: T | p x}` as sugar for a one-field record with a proof** (Lean's `Subtype`), with
  the obligation found by `auto`, then `omega`, at construction. Costs little (parser and
  elaborator; no kernel change, since it's a record), and it makes the common case read like a
  refinement type. Risk: a second way to write what records already say. **Verdict: yes, small.**
- **Contracts** (`requires`/`ensures` clauses) would be a second specification language beside
  types and theorems. Our AoC layout (plain program in `Aoc/DayNN/`, theorems in `Aoc.DayNN.Proofs`) already keeps specs
  apart from code, and Dafny's own AoC proofs read like ours in structure **[checked:
  aoc-day03/05-community]**. **Verdict: no.**

### 5.3 Ghost code, erasure and quantities

Everyone erases proofs; they differ in what *else* can be erased. Idris 2 (quantity `0`) and Agda
(`@0`) can erase data too, such as a vector's length **[cited]**. We erase exactly `Prop` and
types; data indices are stored (DESIGN §6) **[checked]**.

- **Candidate: `@0`-style erased data arguments.** It would let `Vec` drop its stored length and
  `decreasing`'s hidden fuel (already dropped by the runtime and JS **[checked:
  well-founded-recursion.md]**) be erased by rule rather than by special case. It's a kernel change
  (the elimination check must refuse to compute data from an erased value), and we have no measured
  cost from stored indices. **Verdict: not now; revisit if a profile shows it.**
- **Linear quantity `1`** (Idris) or permissions (Verus) for resources: our abilities already
  model resources as handled operations. **Verdict: no** (§7).

### 5.4 Mutation and arrays

| Option | Who | Fit | Our problem | Cost | Risk |
|---|---|---|---|---|---|
| `Array` with `get`/`set`, copied on write | (baseline) | library + runtime natives | SW-112: wanted on 3 days, not needed | small | slow if used naively |
| In-place update when unique (reference counting with reuse) | Lean, Koka Perceus | `crates/rt` and JS would need to know uniqueness; the kernel is unchanged (the logical model stays a list or function) | the same | large | multi-shot handlers make captured values shared; JS has no reference counts **[inferred]** |
| Checked "runs in place" annotation | Koka `fip` | an untrusted compile-time check, outside the kernel | none yet | medium | — |
| Mutation as a pure function old→new | Aeneas backward functions | our programs are already pure; this is how we'd *specify* an `Array` | — | — | — |

The AoC evidence is that `Map` and `List` versions run in under about 5 s on every day so far
(aoc-day08-gaps.md §6.3) **[checked]**. **Verdict:** keep SW-112 in backlog; when a program needs
it, model `Array a n` logically as a `Vec` (so every `Vec` lemma applies), with `set` running in
place in the fast runtime when the array is unique, as Lean does. Note now that values captured by
a multi-shot continuation must count as shared. Today handlers are folds over a finite tree of
operations (`Each`'s `fork` is resumed twice by building both branches; each-ability.md)
**[checked]**, so this only bites if the runtime later runs handlers natively (abilities.md,
option A).

**Imperative sugar** (Lean's `let mut`, `for`, `break`, early `return`, desugared to folds
**[cited]**) is the other half of "mutation" for most programmers. It would desugar to folds or to
a `State` ability with no kernel change. The cost is in proofs: Lean needed a dedicated
verification-condition generator (`mvcgen`) to make proofs about such code pleasant **[cited]**.
Our AoC notes don't show demand: day 8's `Option` sequencing "reads as well as a Lean `do`
block" (aoc-day08-gaps.md §3.4) **[checked]**. **Verdict: later; not in the shortlist.**

### 5.5 Partiality and escape hatches

| Language | Escape hatch | Visible in the type? | Reasoning about it |
|---|---|---|---|
| Stitchwort | `{Partial}` | yes, spreads to callers | none needed: tests use fuel versions **[checked]** |
| F* | `Dv` | yes | in the type only; no separate lemmas **[cited]** |
| Lean | `partial`, `unsafe`, `partial_fixpoint` | no (`partial`); `unsafe` spreads | `partial`: none; `partial_fixpoint`: unfolding equations, partial correctness for `Option` **[cited]** |
| Idris 2 | `partial` | no; not evaluated in types | none **[cited]** |
| Agda | `NON_TERMINATING` | no; not reduced in types | none **[cited]** |
| Dafny | `decreases *` on methods | yes (methods only) | specs in contracts **[cited]** |

Our design is the strictest here, and F* shows it is workable at scale **[inferred]**.
**Candidate: `partial_fixpoint`-style reasoning** (an unfolding equation for a `{Partial}`
function, plus "if it returned `x`, then …" theorems). It would need a kernel-level story for
equations about non-terminating code. Nothing in AoC has needed it: `decreasing` covered every
loop since SW-199 **[checked]**. **Verdict: no, for now.**

### 5.6 Proof irrelevance and `Subtype`

Lean has definitional proof irrelevance: any two proofs of the same `Prop` are equal for the
checker, which is what makes `Subtype` values with different proofs compare equal without
lemmas **[unverified: standard Lean behaviour, not re-fetched]**. Our design for this is
written and reviewed twice (proof-irrelevance.md, D1′; SW-93 in backlog) **[checked]**. Today
records with proof fields get `T.ext` and `DecEq.uniqueEq` as workarounds **[checked]**. 5.2's
refinement sugar would make this matter more. **Verdict:** keep SW-93 as is, and do it before or
with refinement sugar if `ext` lemmas start to show up in proofs.

### 5.7 Specs as tests

| Technique | Who | Fit for us | Cost |
|---|---|---|---|
| Unit tests beside the code | everyone; our `test` | have it (cached by hash) | — |
| `decide`/`rfl` on examples | Lean `#guard`, Idris `Refl` | have it (`test` is proof by computation, DESIGN §7) | — |
| Property tests: random inputs, shrinking | Lean Plausible, QuickCheck | DESIGN §7 "later", with cache rules already written | medium |
| **Counterexample search on theorem statements** | Isabelle Quickcheck/Nitpick | the statement's hypotheses and goal are often decidable (`DecEq`, `Ord`, `Decidable` instances); evaluate them on small and random inputs with the fast runtime | medium |
| Run contracts at run time | SPARK `-gnata`, Dafny `expect` | our JS boundary already checks decidable preconditions (DESIGN §12) | — |
| Differential testing of an implementation against a proved model | Cedar | have it between evaluators; could be offered to users for JS exports | small (docs) |

**The candidate: counterexample search.** When a theorem is stated (or when its proof fails), and
its parameters have generators (derived for data types, as `DecEq`/`Ord` are derived today) and its
hypotheses and conclusion are decidable, try small exhaustive inputs and then random ones with the
fast runtime; if one fails, report it next to the error: "`n = 3, xs = [2, 0]` makes the
hypotheses true and the goal false". It's untrusted: it never proves anything, only helps, so the
kernel is unchanged. **Problem it solves:** wrong statements and wrong lemmas, which every
deployment in §4.4 reports as a real cost, and which on our side show up as long sessions on
lemmas that turn out false (no measured count yet; the AoC friction lists would be the place to
start counting) **[inferred]**. **Risks:** time (needs a budget, reported as "inconclusive" like
tests, DESIGN §3); statements over function types or `Prop`-valued hypotheses without decision
procedures (skip them, and say so). **Verdict: yes** (D559).

### 5.8 Extraction and interop

Our story is Lean's (compile the same code; no separate extraction) plus a checked boundary
(DESIGN §12), which Rocq extraction and Isabelle's code generator lack: there, user-written
mappings are trusted verbatim **[cited]**. agda2hs and Aeneas show the value of a *restricted,
explicit* fragment with a faithful mapping **[cited]**, which our first-milestone export rules
already are **[checked]**. SymCrypt's dashboards of trusted models and shims **[cited]** suggest a
cheap feature: show `stitchwort assumptions` output in the playground and LSP for each export and
theorem. **Verdict:** no new extraction work; surface assumptions in the UI (small; fold into LSP
work).

### 5.9 Error messages

What the field reports: SMT tools say "might not hold" without saying why (Dafny, F*, LH before
2022) **[cited/unverified]**; Lean's roadmap makes "fail fast and tell the user why" a goal for
`grind` and `bv_decide` **[cited]**. Our `E-OMEGA` already lists the facts and atoms it used and
which kind of failure it hit (docs/syntax.md, `omega`) **[checked]**, which is the behaviour Lean
is aiming for. **Candidate:** make that the rule for every piece of automation: `auto`, a
future `simp`, `decreasing` (say which facts were tried, and what the goal was when they ran
out); and pair failures with a counterexample when §5.7 finds one. **Verdict: yes, as a
policy** (no separate lane).

### 5.10 IDE: goals and holes

The gold standards: Agda's hole commands, Idris 2's `:casesplit`/`:addmissing`/`:proofsearch`,
Lean's infoview **[cited/unverified as marked]**. Liquid Haskell's users name the lack of goal
inspection as a barrier **[cited: snippet]**. LSP stage 2 (`?` holes with the goal and context,
D497) is designed and next (SW-31) **[checked]**. **Candidates after it, from Idris's list:**
(1) case-split a variable at a hole, dropping impossible cases (we already compute them:
`W-UNREACHABLE`, impossible arms); (2) add missing arms (we already compute them for
`E-NONEXHAUSTIVE`); (3) "fill by `auto`/`omega`" as a code action that writes the found term (or
the word `omega`) into the source; (4) a counterexample (§5.7) shown at the hole. **Verdict: yes,
as stage 2's follow-ups** (one ticket, after stage 2).

### 5.11 Library design

| Lesson | Who | Our evidence |
|---|---|---|
| Ship data structures *with* their lemma suites, in the core library | Lean `Std.HashMap`/`TreeMap` | day 8 added 28 Std lemmas; 17 generic helpers stayed in the AoC proofs **[checked]** |
| Keep a stable core library beside the compiler; let an ecosystem library move fast | Lean (Init/Std vs Batteries/Mathlib) | we have one Std; no ecosystem yet |
| Avoid deep algebraic hierarchies early | Agda stdlib **[unverified]** | our interfaces are concrete (`Ord`, `Add`, `Mul`) **[checked]** |
| Deprecation machinery for churn | Mathlib | not needed: no users, no backwards compatibility (project rule) |
| Names that predict lemmas (`map_append`, `length_cons`) | Lean, Mathlib | our names are camelCase (`appendLength`); a written naming scheme would make lemmas findable |

**Candidate: a lemma-complete Std policy.** Each public Std function on `List`, `Map`, `Set`, `Nat`
and `Int` ships with its interaction lemmas (with `length`, `map`, `++`, membership, `get`), named
by a written scheme; each AoC day's generic helpers move to Std as part of that day's gap note.
**Cost:** small per function, ongoing. **Risk:** Std grows and its load time with it (SW-322 already
measures Std load cost) **[checked]**. **Verdict: yes** (D561).

### 5.12 Documentation and the learning curve

- **Assurance ladder** (SPARK's stone to platinum **[cited]**). A page that says what you get at
  each step: *tested* (`test`), *total* (no `{Partial}`: it returns), *safe at the boundary*
  (checked JS export), *proved* (theorems about it), and what each costs. It sells the cheap rungs,
  which carry most of the value in SPARK's own account **[cited]**. **Cost:** a page. **Verdict: yes.**
- **Checked examples in docs** (Lean's Verso) **[cited]**: our `docs/syntax.md` cites
  `examples/accept/…` files, which are tested; a check that every code block in the docs parses
  and checks would be the next step. **Verdict:** small, later.
- **A book** ("Functional Programming in Lean", F*'s "Proof-Oriented Programming") **[unverified]**:
  the AoC days, with programs and proofs, are already most of a tutorial. **Verdict:** later; out
  of scope here.

---

## 6. Ranked shortlist

By value over cost. "Planned" means a ticket or design already exists; this survey adds evidence.

| Rank | What | From | Solves (ours) | Cost | Risk | Status |
|---|---|---|---|---|---|---|
| 1 | **Counterexample search on theorem statements**, plus property tests (§5.7) | Isabelle Quickcheck/Nitpick, Lean Plausible | wrong statements and lemmas; spec bugs (§4.4) | medium (generators, budget, report) | low: untrusted, kernel unchanged | new (D559) |
| 2 | **Goal holes, then Idris-style hole actions** (§5.10) | Agda, Idris 2, Lean | proof writing speed; LH's named barrier | stage 2 medium; actions small each | low | planned (SW-31, D497); actions new |
| 3 | **`omega` stage 2**: `-`, `max`/`min`, `/` and `%` by a number, `Int` (§5.1) | Rocq `lia`, Lean `omega` | arithmetic, 6 of 8 days | medium | check speed (SW-321) | planned (omega.md) |
| 4 | **Lemma-complete Std policy** with a naming scheme (§5.11) | Lean Std | day 8's 17 helpers and 28 new lemmas | small, ongoing | Std load time | new (D561) |
| 5 | **A `simp`-like rewriting term**, explicit lemma lists, emits ordinary terms (§5.1) | Lean `simp`, LH PLE, ACL2 | long proofs; `*Congr` lemmas | large; design note first | brittleness, term size | new (D560) |
| 6 | **`{x: T \| p}` refinement sugar** over a record with a proof field, discharged by `auto`/`omega` (§5.2) | Lean `Subtype`, LH, Flux | readable bounds and invariants | small | overlap with records; wants SW-93 | new |
| 7 | **Assurance-ladder page** in the docs (§5.12) | SPARK levels | learning curve; selling the cheap rungs | a page | none | new |
| 8 | **In-place `Array` via uniqueness**, logically a `Vec` (§5.4) | Lean, Koka Perceus | SW-112 when a program needs it | large | multi-shot sharing; JS | backlog (SW-112); design notes now |

Also, as policies rather than lanes: automation failures say why (§5.9); assumptions shown in
the playground and LSP (§5.8); "find outside, check inside" for every new piece of automation (D562).

---

## 7. Deliberate differences: what not to adopt

Stated neutrally: these are choices other languages made for their goals, which conflict with ours.

| Not adopting | Who does it | Why not for us |
|---|---|---|
| An SMT solver in the trusted path | Dafny, F*, LH, Verus, Creusot, Flux | Principle 4 (small kernel); deterministic, cacheable checks; no solver binary in the browser playground **[inferred]** |
| Running compiled code to decide proofs (`native_decide`, `native_compute`) | Lean, Rocq | Adds the compiler to the trusted base; our fast runtime is deliberately untrusted (fast-runtime.md) **[checked]** |
| A separate contract language | Dafny, SPARK, Creusot | Specs are types and theorems in the same language (the AoC layout keeps program and `Proofs` namespaces apart) |
| `partial` that is invisible in the type | Lean, Idris, Agda | Principle 1 |
| Linear quantities in the kernel | Idris 2, ATS, Verus permissions | Abilities model resources; one more kernel concept for no measured need |
| Tactic scripts as the main proof form | Lean, Rocq, Isabelle | Term proofs keep one language; automation enters as terms (`omega`, `auto`, a future `simp`). Revisit only if term proofs stop scaling |
| One-shot-only continuations | OCaml 5 | Multi-shot handlers are part of the abilities design (`Each`); keep the fast path for tail-resumptive handlers instead |

---

## 8. Decisions for Matt

| ID | Decision | Recommendation |
|---|---|---|
| D559 | **Counterexample search.** When a theorem's parameters have generators and its hypotheses and goal are decidable, `check` tries small and random inputs on the fast runtime and reports a counterexample: (a) only when the proof fails (and on demand at a `?` hole), (b) on every theorem as it's stated, as Isabelle does, or (c) only in explicit `property` tests (DESIGN §7). | **(a) plus (c)**: a design note covering both, sharing generators; (b) later if (a) proves cheap |
| D560 | **Rewriting automation.** Write a design note for a `simp [eqs]` term: untrusted search that rewrites with listed equations and equation lemmas (also under binders) and emits an ordinary term; no global `@[simp]` set at first. Alternatives: an SMT oracle with proof replay (Sledgehammer-style; very large), or nothing beyond `omega`. | **Design note**, after `omega` stage 2 |
| D561 | **Std lemma policy.** Every public Std function on `List`/`Map`/`Set`/`Nat`/`Int` ships with its interaction lemmas, under a written naming scheme; each AoC gap note moves that day's generic helpers into Std. | **Yes** |
| D562 | **Automation principle.** Add to DESIGN §2: "automation finds, the kernel checks". No SMT solver or compiled code in the trusted path; every automatic proof is an ordinary term the kernel re-checks (as `omega` does now). | **Yes** |

Refinement sugar (rank 6), the assurance-ladder page (rank 7) and hole actions (rank 2's
follow-ups) are implementation details within decided directions, and can become tickets without
a decision.

---

## Sources

Fetched on 22 October 2026 by the research passes unless marked "snippet" (seen only in a search
result) in the text.

**Lean 4.** Releases: https://lean-lang.org/doc/reference/latest/releases/ (v4.12.0, v4.22.0,
v4.30.0 notes). Recursive definitions:
https://lean-lang.org/doc/reference/latest/Definitions/Recursive-Definitions/. `do` notation:
https://lean-lang.org/doc/reference/latest/Functors___-Monads-and--do--Notation/Syntax/. Tactic
reference: https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/. `grind`:
https://lean-lang.org/doc/reference/latest/The--grind--tactic/. Reference counting:
https://lean-lang.org/doc/reference/latest/Run-Time-Code/Reference-Counting/. Arrays:
https://lean-lang.org/doc/reference/latest/Basic-Types/Arrays/. Source:
https://raw.githubusercontent.com/leanprover/lean4/master/src/Lean/Elab/Tactic/Omega/Core.lean,
https://raw.githubusercontent.com/leanprover/lean4/master/src/Init/Tactics.lean,
https://raw.githubusercontent.com/leanprover/lean4/master/src/Std/Tactic/BVDecide/Syntax.lean.
Roadmaps: https://lean-lang.org/fro/roadmap/y3, https://lean-lang.org/fro/roadmap/y4-1. Cedar:
https://lean-lang.org/use-cases/cedar/, https://arxiv.org/html/2407.01688v1. Plausible:
https://raw.githubusercontent.com/leanprover-community/plausible/main/README.md. Reservoir:
https://reservoir.lean-lang.org/. Counting Immutable Beans: https://arxiv.org/abs/1908.05647.

**Idris 2.** https://idris2.readthedocs.io/en/latest/tutorial/multiplicities.html,
https://idris2.readthedocs.io/en/latest/tutorial/typesfuns.html,
https://idris2.readthedocs.io/en/latest/reference/pragmas.html,
https://idris2.readthedocs.io/en/latest/tutorial/interactive.html,
https://idris2.readthedocs.io/en/latest/backends/index.html, https://github.com/idris-lang/Idris2.

**Agda.** https://agda.readthedocs.io/en/latest/language/termination-checking.html,
https://agda.readthedocs.io/en/latest/language/runtime-irrelevance.html,
https://agda.readthedocs.io/en/latest/getting-started/what-is-agda.html,
https://github.com/agda/agda2hs.

**Rocq.** https://rocq-prover.org/about,
https://rocq-prover.org/doc/master/refman/addendum/micromega.html,
https://rocq-prover.org/doc/master/refman/addendum/extraction.html.

**Isabelle, CakeML, ACL2, ATS.** https://isabelle.in.tum.de/overview.html,
https://isabelle.in.tum.de/website-Isabelle2025/index.html, https://cakeml.org/,
https://en.wikipedia.org/wiki/ACL2 (snippet), http://www.cs.bu.edu/~hwxi/atslangweb.

**F*, Dafny, SPARK, Liquid Haskell.** https://fstar-lang.org/,
https://fstar-lang.org/tutorial/book/part4/part4_div.html,
https://fstar-lang.org/tutorial/book/part4/part4_background.html,
https://dafny.org/latest/DafnyRef/DafnyRef,
https://popl25.sigplan.org/details/dafny-2025-papers/5/Towards-Proof-Stability-in-SMT-based-Program-Verification,
https://popl25.sigplan.org/details/dafny-2025-papers/8/Helping-users-to-reduce-Brittleness-in-their-Dafny-programs-a-success-story,
https://www.amazon.science/blog/how-we-built-cedar-with-automated-reasoning-and-differential-testing (snippet),
https://docs.adacore.com/spark2014-docs/html/ug/en/usage_scenarios.html,
https://www.adacore.com/case-studies/nvidia-adoption-of-spark-new-era-in-security-critical-software-development (snippet),
https://ucsd-progsys.github.io/liquidhaskell/,
https://tweag.io/blog/2022-07-21-lh-introspection/ (snippet),
https://pldi25.sigplan.org/details/pldi-2025-papers/78/Adoption-Barriers-for-Liquid-Types (snippet).

**Rust verifiers.** https://verus-lang.github.io/verus/guide/,
https://verus-lang.github.io/verus/guide/modes.html, https://arxiv.org/abs/2303.05491,
https://www.microsoft.com/en-us/research/publication/verus-a-practical-foundation-for-systems-verification/,
https://github.com/creusot-rs/creusot, https://guide.creusot.rs/,
https://arxiv.org/abs/2206.07185, https://github.com/AeneasVerif/aeneas,
https://www.microsoft.com/en-us/research/blog/verifying-rust-cryptography-in-symcrypt-from-standards-to-code/,
https://arxiv.org/html/2609.15648, https://arxiv.org/abs/2207.04034,
https://flux-rs.github.io/flux/,
https://aws.amazon.com/blogs/opensource/verify-the-safety-of-the-rust-standard-library/,
https://arxiv.org/html/2510.01072v3.

**Effects and memory.** https://koka-lang.github.io/koka/doc/book.html,
https://www.microsoft.com/en-us/research/publication/perceus-garbage-free-reference-counting-with-reuse/,
https://www.microsoft.com/en-us/research/publication/fp2-fully-in-place-functional-programming/,
https://www.microsoft.com/en-us/research/publication/generalized-evidence-passing-for-effect-handlers-or-efficient-compilation-of-effect-handlers-to-c/,
https://ocaml.org/manual/5.3/effects.html,
https://www.unison-lang.org/docs/language-reference/abilities-and-ability-handlers/,
https://effekt-lang.org/, https://arxiv.org/abs/1611.09259.

**Newer.** https://github.com/the-little-typer/pie, https://github.com/aya-prover/aya-dev,
https://github.com/mikeshulman/narya, https://github.com/google-research/dex-lang,
https://github.com/HigherOrderCO/Kind, Granule and Nomos (snippets: ICFP 2019 Granule paper,
https://arxiv.org/abs/1902.06056).

**Stitchwort** (at `a4659eba`): `DESIGN.md` §2-§8, §12, §17; `docs/syntax.md` (`omega`,
records, interfaces); `docs/compared.md`; `docs/proposals/omega.md`, `partial.md`,
`well-founded-recursion.md`, `proof-irrelevance.md`, `language-server.md`, `fast-runtime.md`,
`vec.md`, `equation-lemmas.md`; `docs/comparisons/aoc-day0[1-8]-community.md`,
`aoc-day08-gaps.md`; `board/tickets.json` (open tickets, read only).
