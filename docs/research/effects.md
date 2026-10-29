# Effects and handlers: ideas to steal

Status: research register for SW-894, cluster 5 (effects and handlers),
29 Oct 2026. Window: papers from 2022 on (D1831); older work only where
in-window papers lean on it, marked "(classic)". No code changes.

Labels: **[cited]** (link given), **[checked]** (read in the paper's text or
in our code at `02eb7b62`), **[inferred]** (my reasoning, not tested),
**[unverified]** (seen only in a search snippet or a second-hand summary).

## 0. In brief

- Stitchwort already has thorough related-work sections for the **runtime**
  (effect-runtime.md §3, tail-resumptive-handlers.md §2) and for
  **computations as values** (computation-values.md). The new material from
  2022–2026 that adds most is on **reasoning about effectful programs**, not
  on running them.
- The best ideas to steal:
  1. **Monad laws that hold by conversion** (Yang and Wu, POPL 2026). For
     Stitchwort this would mean `bindAssoc`, `bindDone` and `foldCompBind`
     as trusted conversion rules, in the same way as the two extra `Nat.add`
     rules. That would close SW-548, and with it rogue's gap 2. It is a
     kernel change, so a decision (D1850).
  2. **Hoare reasoning that yields program equations** (Kidney, Yang and
     Wu, POPL 2024: the lemma H-elim). Stitchwort's free monad needs only
     the easy case: a short lemma beside `Effect.alwaysBind`. Small.
  3. **Specifications for handlers as predicate transformers** (Lean's
     `Std.Do`, `mvcgen` and `vcgen`, 2025–2026). A library layer, so that
     proofs compose specification lemmas instead of running a handler on
     unknown values (SW-570). Design note first (D1851).
  4. **Assert that a handler takes the fast path.** Lexa (OOPSLA 2024)
     declares tail-resumptive handlers. Stitchwort detects them, but falls
     back without a word when it can't (SW-861). Small.
  5. **TRMC through effect continuations** (Leijen and Lorenzen, POPL 2023,
     §6). Koka keeps `map` with an effectful callback in constant stack, and
     guards against resumptions used more than once. This is evidence for
     option (b) of SW-868. A runtime change.
- **Found on the way [checked]:** DESIGN.md §8 and §13 still describe
  handler termination as a tracked conjecture. abilities.md (option B) and
  docs/core.md "Abilities" say the kernel's positivity and termination
  checks now prove it on the translated program. No `conjecture` or
  `assumptions` command exists in `crates/`. What is really left to trust
  is that the translation is faithful to the semantics
  (abilities.md:35). Ticket T1.

## 1. Method

### 1.1 Stitchwort read first

README.md; DESIGN.md §8, §13, §16, §17; docs/core.md "Abilities";
docs/proposals/abilities.md (head and termination rule),
effect-runtime.md §3 and §9.1, tail-resumptive-handlers.md (summary, §1),
computation-values.md §3; `crates/elab/src/std/core/Effect.sw`,
`std/Effect/Laws.sw`, `std/Effect/Always.sw`, `crates/rt/src/trmc.rs`
(header); games/rogue/PROOFS.md ("Tried", "What would be needed"). Tickets:
SW-548, SW-555, SW-570, SW-593, SW-790–792, SW-861, SW-868, SW-890 and the
`decision` list.

### 1.2 Sources and queries (29 Oct 2026)

Rerun these each quarter, restricted to the new months.

| # | Source or query | Yield |
|---|---|---|
| S1 | yallop/effects-bibliography `README.md`, sections 2022–2026 ([raw](https://raw.githubusercontent.com/yallop/effects-bibliography/master/README.md)) | 61 entries; the main harvest |
| Q1 | `effect handlers dependent types paper 2023 2024` | Tokyo Tech group, Sekiyama–Unno, ARM |
| Q2 | `Koka effect handlers POPL 2024 OR ICFP 2024 Leijen paper` | nothing new on handlers |
| Q3 | `Effekt language paper OOPSLA 2023 2024 Brachthäuser effects` | Effekt papers |
| Q4 | `lexical effect handlers type system paper 2022 2023` | PLDI 2022, ESOP 2023, OOPSLA 2023 |
| Q5 | `Danel Ahman dependent types algebraic effects 2022 2023 2024` | only pre-2022 |
| Q6 | `interaction trees Coq 2023 2024 paper choice trees ctrees POPL` | CTrees |
| Q7 | `Pédrot effects in type theory exceptional type theory 2022 2023 paper` | only pre-2022 |
| Q8 | `F* Dijkstra monads effects paper 2022 2023 2024 indexed` | indexed effects |
| Q9 | `Flix effect system Boolean unification polymorphic effects paper Lutze Madsen` | ICFP 2023, OOPSLA 2025 |
| Q10 | `"Do unchained" Lean 4 do notation paper` | ICFP 2022 |
| Q11 | `termination of effect handlers totality type system strong normalisation` | Hamana; Ahman–Sobolev |
| Q12 | `Effekt publications 2024 2025 Tübingen` | ICFP/OOPSLA 2025 |
| Q13 | `"Interaction Tree Specifications" 2023 2024` | ECOOP 2023 ×2 |
| Q14 | `Koka "fully in-place" OR "tail recursion modulo context" 2023` | FP², TRMC |
| Q15 | `algebraic effects Agda OR Idris library 2023 2024` | Paella (HOPE 2024) |
| Q16 | `Lean 4 Std.Do mvcgen` | reference manual |
| Q17 | `"Affect" affine type and effect system POPL 2025` | Affect |
| Q18 | `Koka release notes 2024 2025 version 3` | v3.1 notes |
| Q19 | `effect handlers better type error messages effect inference rows 2023–2025` | Ikemori; Cambria; Fram |
| Q20 | `"Algebraic Effects Meet Hoare Logic in Cubical Agda"` | paper |
| Q21 | `arXiv 2025 dependent type theory algebraic effects handlers CBPV` | only pre-2022 |
| Q22 | `OCaml 5 typed effects proposal 2024 2025` | Modal Effect Types |
| Q23 | `Unison abilities handlers 2024 2025 release` | Unison 1.0, a speed claim |
| Q24 | `Frank OR Fram language effect handlers 2024 2025` | Fram (ML 2024) |
| Q25 | `"Lexical Effect Handlers, Directly"` | Lexa |
| Q26 | `"higher-order effects" OR "scoped effects" 2023 2024` | framework papers |
| Q27 | `Scala 3 capture checking capabilities effects paper 2023 2024` | Capturing Types and successors |
| Q28–30 | titles of Modal Effect Types, Yang–Wu POPL 2026, "Deciding not to Decide" | abstracts |
| Q31–33 | Ahman–Sobolev year; Ikemori TFP 2022; F* indexed effects venue | dates |

Full texts read: Kidney–Yang–Wu (POPL 2024), Yang–Wu (POPL 2026,
introduction), Lexa (OOPSLA 2024, abstract, §1–2 and §5), Zero-Overhead
Lexical Effect Handlers (abstract, §1), Modal Effect Types (abstract, §1),
TRMC (POPL 2023, §6). These PDFs were fetched with curl and turned into
text with macOS PDFKit. Lean reference pages: `mvcgen` overview, predicate
transformers (first half only), `vcgen`.

### 1.3 Couldn't reach, or couldn't confirm

- WebFetch couldn't read PDFs, so the full texts above came by curl. ACM DL
  PDFs weren't tried.
- **Unison**: a "handlers up to 2–80× faster" claim for a June 2025 release
  came from one social post. I didn't find the release notes **[unverified]**.
- **Koka v3.2** (July 2025): no release notes found. Only v3.1's "redesign
  of named effect generation" was seen **[unverified]**.
- **F\* "Programming and Proving with Indexed Effects"**: listed "in
  submission"; venue and year unknown.
- **Lean `Std.Do`**: the predicate-transformers page was truncated before the
  `WP` class and `Triple`. Their shapes below come from the overview and the
  `vcgen` page.
- effekt-lang.org/publications and se.cs.uni-tuebingen.de/publications
  weren't fetched; I took Effekt's 2024–2025 papers from search results.

## 2. Screened list

Hooks: **R** reasoning and proofs (SW-548, SW-570, rogue), **T** termination
and totality, **P** runtime performance (SW-593, SW-790–792, SW-861,
SW-868), **E** effect typing and ergonomics (rows, inference, messages),
**D** dependent types with effects.

| # | Paper | Venue | Hook | Verdict |
|---|---|---|---|---|
| 1 | Yang, Wu: Handling Higher-Order Effectful Operations with Judgemental Monadic Laws | POPL 2026 | R | **keep** (deep read 1) |
| 2 | Kidney, Yang, Wu: Algebraic Effects Meet Hoare Logic in Cubical Agda | POPL 2024 | R | **keep** (deep read 2) |
| 3 | Lean 4 `Std.Do`, `mvcgen` (4.22) and `vcgen` (experimental) | Lean docs 2025–26 | R | **keep** (deep read 3) |
| 4 | Ma, Ge, Lee, Zhang: Lexical Effect Handlers, Directly (Lexa) | OOPSLA 2024 | P | **keep** (deep read 4) |
| 5 | Leijen, Lorenzen: Tail Recursion Modulo Context: An Equational Approach | POPL 2023 (JFP 2025) | P | **keep** (deep read 5) |
| 6 | Ma, Ge, Jung, Zhang: Zero-Overhead Lexical Effect Handlers | OOPSLA 2025 | P | **keep** (with 4) |
| 7 | Tang, White, Dolan, Hillerström, Lindley, Lorenzen: Modal Effect Types | OOPSLA 2025 | E | **keep** |
| 8 | Tang, Lindley: Rows and Capabilities as Modal Effects | POPL 2026 | E | maybe |
| 9 | Ikemori, Cong, Masuhara, Leijen: Sound and Complete Type Inference for Closed Effect Rows | TFP 2022 | E | **keep** |
| 10 | Balik, Jędras, Polesiuk: Deciding not to Decide (effect inference, higher rank) | ESOP 2026 | E | maybe |
| 11 | Balik, Polesiuk: Fram, named and implicit parameters for handlers | ML workshop 2024 | E | maybe |
| 12 | Lutze, Madsen, Schuster, Brachthäuser: With or Without You: Effect Exclusion | ICFP 2023 | E | drop (Stitchwort has no need for "any effect but X" yet) |
| 13 | Lutze, Madsen: Associated Effects | PLDI 2024 | E | maybe (effects in interfaces, if Stitchwort's interfaces get effectful methods) |
| 14 | Waterloo group: System F<:BE, formalising Flix effects | OOPSLA 2025 | E | drop |
| 15 | Hamana: Modular Termination for Second-Order Computation Rules and Application to Algebraic Effect Handlers | LMCS 2022 | T | **keep** |
| 16 | Ahman, Sobolev: Strong Normalisation for Asynchronous Effects | FSCD 2026 | T | maybe |
| 17 | van Rooij, Krebbers: Affect: An Affine Type and Effect System | POPL 2025 | T/P | maybe (one-shot tracking; D1162 chose unrestricted multi-shot) |
| 18 | Tang, Hillerström, Lindley, Morris: Soundly Handling Linearity | POPL 2024 | T | drop (no linear types) |
| 19 | Chappe, He, Henrio, Zakowski, Zdancewic: Choice Trees | POPL 2023 | R | maybe |
| 20 | Silver, Westbrook, Yacavone, Scott: Interaction Tree Specifications | ECOOP 2023 | R | **keep** |
| 21 | Silver, He, Cecchetti, Hirsch, Zdancewic: Semantics for Noninterference with Interaction Trees | ECOOP 2023 | R | drop |
| 22 | Song, Foo, Chin: Specification and Verification for Unrestricted Algebraic Effects and Handling | ICFP 2024 | R | maybe |
| 23 | Song, Foo, Chin: Automated Temporal Verification for Algebraic Effects | APLAS 2022 | R | drop |
| 24 | Kawamata, Unno, Sekiyama, Terauchi: Answer Refinement Modification | POPL 2024 | R/D | maybe |
| 25 | Sekiyama, Unno: Temporal Verification with Answer-Effect Modification | POPL 2023 | R/D | drop |
| 26 | Sekiyama, Unno: Algebraic Temporal Effects | POPL 2025 | R | drop |
| 27 | de Vilhena, Pottier: A Type System for Effect Handlers and Dynamic Labels | ESOP 2023 | E | drop |
| 28 | de Vilhena et al.: A Relational Separation Logic for Effect Handlers (Blaze) | POPL 2026 | R | drop (needs mutable state, which Stitchwort lacks) |
| 29 | de Vilhena, Pottier: Verifying an Effect-Handler-Based Reverse-Mode AD Library | LMCS 2023 | R | drop |
| 30 | Sieczkowski, Piróg, Biernacki: A General Fine-Grained Reduction Theory for Effect Handlers | ICFP 2023 | R | maybe (equations between handled programs) |
| 31 | Moy, Dimoulas, Felleisen: Effectful Software Contracts | POPL 2024 | R | drop |
| 32 | Yoshioka et al.: On Model-Checking Higher-Order Effectful Programs | POPL 2024 | R | drop |
| 33 | Ullrich, de Moura: 'do' Unchained | ICFP 2022 | E | **keep** (Stitchwort is direct style already; their `for`/`return`/mutation translation is of interest) |
| 34 | Rastogi et al.: Programming and Proving with Indexed Effects (F\*) | in submission | D/R | maybe |
| 35 | SecRef\* (F\*, free monad with reification) | arXiv 2503.00404, 2025 | D/R | maybe (already in computation-values.md) |
| 36 | Paella: algebraic effects with parameters and their handlers (Idris 2) | HOPE 2024 | D | drop |
| 37 | Tsuyama, Cong, Masuhara: An Intrinsically Typed Compiler for Algebraic Effect Handlers | PEPM 2024 | D | drop |
| 38 | Cong, Kawazoe, Masuhara: A Mostly CPS, Partly ANF Translation of Dependent Types | IFL 2024 | D | drop (cluster 6) |
| 39 | Charles Univ. thesis: Combining effects with dependent types | thesis 2024 | D | drop |
| 40 | Schuster, Brachthäuser, Müller, Ostermann: A Typed CPS Translation for Lexical Effect Handlers | PLDI 2022 | P | maybe |
| 41 | Müller, Schuster, Starup, Ostermann, Brachthäuser: From Capabilities to Regions | OOPSLA 2023 | P | maybe |
| 42 | Brachthäuser et al.: Effects, Capabilities, and Boxes | OOPSLA 2022 | E | drop |
| 43 | Muhcu, Schuster, Steuwer, Brachthäuser: Multiple Resumptions and Local Mutable State, Directly | ICFP 2025 | P | drop here (already in effect-runtime.md §3) |
| 44 | Gaißert, Bolz-Tereick, Brachthäuser: Tracing JIT Compilation for Effects and Handlers | OOPSLA 2025 | P | maybe |
| 45 | Voigt, Schuster, Brachthäuser: Dynamic Wind for Effect Handlers | OOPSLA 2025 | E | drop (no resources to clean up) |
| 46 | Lutze, Schuster, Brachthäuser: The Simple Essence of Monomorphization | OOPSLA 2025 | P | maybe (cluster 6) |
| 47 | Phipps-Costin et al.: Continuing WebAssembly with Effect Handlers (WasmFX) | OOPSLA 2023 | P | maybe (only if a wasm backend wants native stacks) |
| 48 | Alvarez-Picallo et al.: Effect Handlers for C via Coroutines | OOPSLA 2024 | P | drop |
| 49 | Ghica et al.: High-level Effect Handlers in C++ | OOPSLA 2022 | P | drop |
| 50 | Xie, Cong, Ikemori, Leijen: First-class Names for Effect Handlers | OOPSLA 2022 | E | drop |
| 51 | Xie et al.: Parallel Algebraic Effect Handlers | ICFP 2024 | P | drop |
| 52 | Lorenzen, Leijen, Swierstra: FP²: Fully in-Place Functional Programming | ICFP 2023 | P | drop here (cluster 6) |
| 53 | Bach Poulsen, van der Rest: Hefty Algebras | POPL 2023 | E | drop |
| 54 | van den Berg, Schrijvers: A Framework for Higher-Order Effects & Handlers | SCP 2024 | E | drop |
| 55 | Bosman, van den Berg, Tang, Schrijvers: A Calculus for Scoped Effects & Handlers | LMCS 2024 | E | drop |
| 56 | Lindley et al.: Scoped Effects as Parameterized Algebraic Theories | ESOP 2024 | E | drop |
| 57 | Yang et al.: Structured Handling of Scoped Effects | ESOP 2022 | E | drop |
| 58 | Sekiyama, Tsukada, Igarashi: Signature Restriction for Polymorphic Algebraic Effects | JFP 2024 | E | drop (no polymorphic operations) |
| 59 | Kammar, Lindley et al.: Dynamic Threads via Algebraic Effects | POPL 2026 | — | drop |
| 60 | Plotkin, Xie: Handling the Selection Monad | PLDI 2025 | — | drop |
| 61 | Tang, Schrijvers: From High to Low: Simulating Nondeterminism and State with State | JFP 2025 | P | maybe (state-based backtracking for `Parse`) |
| 62 | Andrieux, Hillerström, Rémy et al.: Asymptotic Speedup via Effect Handlers | JFP 2024 | P | drop |
| 63 | Chu, Hoffmann, Guo: Handling Exceptions and Effects with Automatic Resource Analysis | OOPSLA 2026 | T | maybe (cost bounds for handled code) |
| 64 | Lee et al.: Handling Scope Checks | POPL 2026 | — | drop |
| 65 | Torczon et al.: Effects and Coeffects in Call-by-Push-Value | OOPSLA 2024 | — | drop |
| 66 | Elsman: Explicit Effects and Effect Constraints in ReML | POPL 2024 | E | drop |
| 67 | Cambria: Resource Abstraction for Parametrized Algebraic Effects | arXiv 2608.27798, 2026 | E | drop |
| 68 | Expressive Power of One-Shot Control Operators and Coroutines | arXiv 2609.06443, 2026 | P | drop |
| 69 | Boruch-Gruszecki, Odersky et al.: Capturing Types (Scala capture checking) | TOPLAS 2023 | E | drop |
| 70 | Odersky et al.: Scoped Capabilities for Polymorphic Effects | arXiv 2022 | E | drop |
| 71 | Boruch-Gruszecki et al.: What's in the Box (capture tracking over generic data) | OOPSLA 2025 | E | drop |
| 72 | Bhanuka, Parreaux, Binder, Brachthäuser: Getting into the Flow (type error messages) | arXiv 2024 | E | maybe (cluster 3) |
| 73 | Koka v3.1 release notes (named effect generation redesigned) | 2024 | E | drop |
| 74 | Unison 1.0 and a 2025 handler-speed claim | 2025 | P | maybe, **[unverified]** |
| 75 | OCaml 5.x manual: effects remain untyped and one-shot | 2025 | P | drop (already in effect-runtime.md) |

75 screened: 11 keep, 21 maybe, 43 drop.

## 3. Cards (kept papers)

**C1. Yang and Wu, "Handling Higher-Order Effectful Operations with
Judgemental Monadic Laws", POPL 2026.**
[arXiv 2511.05739](https://arxiv.org/abs/2511.05739). Claim: handlers can
be "carried by lawless raw monads, while the computation judgements still
satisfy the monadic laws judgementally" **[checked]** (abstract and §1).
Steal: make the monad laws hold by conversion, not by an axiom-backed lemma.
Helps SW-548, SW-570 and rogue gap 2. Cost: kernel change. Full text: yes
(introduction read; the realizability models weren't). Deep read 1.

**C2. Kidney, Yang and Wu, "Algebraic Effects Meet Hoare Logic in Cubical
Agda", POPL 2024.** [PDF](https://yangzhixuan.github.io/pdf/free.pdf),
[doi](https://doi.org/10.1145/3632898). Claim: an effect-generic Hoare logic
over free monads quotiented by equations, plus an elimination principle,
H-elim, that turns a Hoare triple into a program equation. Steal: the H-elim
pattern, which is easy for Stitchwort's unquotiented `Comp`. Helps rogue
gap 2 and SW-548. Cost: small (one std lemma). Full text: yes. Deep read 2.

**C3. Lean 4 `Std.Do`, `mvcgen` and `vcgen`.**
[mvcgen](https://lean-lang.org/doc/reference/latest/The--mvcgen--tactic/Overview/),
[vcgen](https://lean-lang.org/doc/reference/latest/The--vcgen--tactic/).
Claim: reinterpret `do` code as predicate transformers, give each function a
`@[spec]` Hoare triple, and reduce a triple to verification conditions in
which "the original program `prog` no longer occurs" **[cited]**. `vcgen`
works on "any program type `Prog` that carries a `Std.WP.WP` interpretation",
including "an inductive type of commands" **[cited]**. Steal: a
specification layer for handlers. Helps SW-570. Cost: library and design
note first; a tactic later. Full text: the docs (partly truncated). Deep
read 3.

**C4. Ma, Ge, Lee and Zhang, "Lexical Effect Handlers, Directly", OOPSLA
2024.** [PDF](https://cs.uwaterloo.ca/~yizhou/papers/lexa-oopsla2024.pdf).
Claim: compile lexical handlers to stack switching without searching for
the handler; "reducing running-time complexity from quadratic to linear in
some cases" **[checked]**. Tail-resumptive and abortive handlers are
declared, and run in place with no `under` construct **[checked]** (§5).
Steal: declared fast-path modes as assertions. Helps SW-790–792 and SW-861.
Cost: small (a diagnostic); the compilation scheme itself would be a
research project. Full text: yes. Deep read 4.

**C5. Leijen and Lorenzen, "Tail Recursion Modulo Context", POPL 2023.**
[PDF](https://www.microsoft.com/en-us/research/uploads/prod/2023/07/trmc-popl23.pdf).
Claim: TRMC generalises to any context with the right algebra. In a language
whose handlers may resume more than once, it stays sound if a context is
copied when shared, or if a second, slower version runs whenever a
multi-shot handler is in scope (§6.1–6.2) **[checked]**. Steal: the guard
for effectful `map`. Helps SW-868 option (b). Cost: runtime change. Full
text: yes (§6). Deep read 5.

**C6. Tang et al., "Modal Effect Types", OOPSLA 2025.**
[arXiv 2407.11816](https://arxiv.org/abs/2407.11816). Claim: track effects
with modalities over an ambient effect context, so that `map` needs no
effect variable. There are no hidden effect variables in error messages,
unlike Frank's "cannot unify effects e and yield, £" **[checked]** (§1).
Steal: (a) never show an inferred row variable in a message without saying
where it came from; (b) in the long run, an alternative to `{e}` on
higher-order functions. Helps effect-polymorphism.md and the messages
(errors.md). Cost: (a) is small; (b) is a research project that conflicts
with "a plain arrow means pure and total" (DESIGN §8). Full text: §1 only.

**C7. Ikemori, Cong, Masuhara and Leijen, "Sound and Complete Type Inference
for Closed Effect Rows", TFP 2022.**
[PDF](https://prg.is.titech.ac.jp/papers/pdf/tfp2022inference.pdf). Claim:
Koka closes the rows of `let`-bound functions and opens them again at use
sites; this paper formalises it and proves it sound and complete
**[unverified]** (search summary). Steal: a citation, and a check, for D1124
(an undecided row unknown becomes `Empty`). Helps effect-polymorphism.md
§5.C.1. Cost: none (reading). Full text: not read.

**C8. Hamana, "Modular Termination for Second-Order Computation Rules and
Application to Algebraic Effect Handlers", LMCS 2022.**
[LMCS](https://lmcs.episciences.org/9702). Claim: strong normalisation of a
CBPV calculus with handlers and effect theories, by semantic labelling and
the General Schema **[unverified]** (abstract). Steal: a reference for the
write-up that T1 asks for (termination of the *source* semantics, as a
second argument beside the kernel's check of the translation). Cost:
reading. Full text: not read.

**C9. Silver, Westbrook, Yacavone and Scott, "Interaction Tree
Specifications", ECOOP 2023.**
[DROPS](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ECOOP.2023.29).
Claim: a specification is an interaction tree with quantifier events
(`forall`, `exists`), and refinement between trees gives syntax-directed,
"auto-active" proofs **[unverified]** (abstract). Steal: specifications
written in the program's own language, as trees. This is an alternative to
the predicate transformers of C3 for SW-570. Cost: research project. Full
text: not read.

**C10. Ullrich and de Moura, "'do' Unchained", ICFP 2022.**
[supplement](https://kha.github.io/do-supplement/print.html). Claim: local
mutation, `for`, `break` and early `return` inside `do`, translated to
monadic code with proofs that the translation is right. A Zulip thread says
Lean's real elaborator differs **[unverified]**. Steal: if Stitchwort grows
`var`/`for` in effectful blocks, translate them to `State`/`Abort` handlers
in the same way. Cost: design note. Full text: not read.

**C11. Zero-Overhead Lexical Effect Handlers (Ma, Ge, Jung and Zhang,
OOPSLA 2025)**, kept as a pair with C4.
[PDF](https://cs.uwaterloo.ca/~yizhou/papers/zero-oopsla2025.pdf). Claim:
for exception-like effects, emit type-directed information so that the
runtime walks the stack only when an effect is raised. Mainline code pays
nothing for handlers in scope, and the strategy is chosen "for each declared
effect based on its expected invocation rate" **[checked]** (abstract).
Steal: a per-ability choice of strategy (rare `Abort` against frequent
`Parse.next`). Helps SW-593. Cost: research project. Full text: abstract
and §1.

## 4. Deep reads

### 4.1 Monad laws by conversion (from Yang and Wu, POPL 2026)

**What they do [checked].** Their calculus keeps sequencing a
judgement-level construct, and lets handlers be carried by raw monads with
no laws. The computation judgements still satisfy the monad laws
judgementally, so a program that differs from another only by how its
`let`s are nested is the same program. They argue that sequential
composition "ought to be an operation for a notion of computation" (§1.2.3).
They prove canonicity and parametricity for the recursion-free fragment.

**How it maps onto Stitchwort.** Stitchwort chose option B: computations
are data, `Effect.Comp` with `Done | Call`, and `bind` and `foldComp` are
ordinary definitions (`crates/elab/src/std/core/Effect.sw:12-28`)
**[checked]**. So the laws are propositional. `bindDone`, `bindAssoc` and
`foldCompBind` (`std/Effect/Laws.sw`) each need `Quot.funext` at the `Call`
case, because `Call`'s `rest` is a function **[checked]**. That is SW-548,
and rogue's gap 2: `f (g (p()))` and `(x => f (g x)) (p())` elaborate to
binds associated differently, and only `bindAssoc` joins them
(games/rogue/PROOFS.md, "What would be needed", 2) **[checked]**.

Stitchwort can't adopt their judgement form without option A (effects in
the kernel), which abilities.md rejected. It *can* get the same
user-visible effect: three trusted conversion rules on the library's exact
`Effect.bind` and `Effect.foldComp`, applied only when the definition is
stuck. This is the pattern already used for `Nat.add`
(`crates/core/src/nat_add.rs`, DESIGN §13) **[checked]**:

- R-assoc: `bind (bind c f) g ⟶ bind c (x => bind (f x) g)` when `c` is
  stuck;
- R-unit: `bind c Done ⟶ c` when `c` is stuck;
- R-fuse: `foldComp d k (bind c n) ⟶ foldComp (x => foldComp d k (n x)) k c`
  when `c` is stuck.

The critical pairs against `bind`'s and `foldComp`'s own clauses join
**[inferred]**, worked by hand:

- R-assoc with `c = Done x`: both sides go to `bind (f x) g`.
- R-assoc with `c = Call o r`: both sides go to
  `Call o (y => bind (r y) (x => bind (f x) g))`, using R-assoc under the
  binder.
- R-unit with `c = Call o r`: this gives `Call o (y => r y)`, which is
  `Call o r` by eta for functions (docs/core.md, conversion) **[checked]**.
- R-fuse with `c = Done x` or `Call o r` joins in the same way.
- The overlap of R-fuse with R-assoc on `foldComp d k (bind (bind c f) g)`
  needs R-fuse again under a binder. I believe it joins, but this is the
  case to check properly.

**Risks.**

- *Assumption: rules whose equations need funext are acceptable as trusted
  conversion.* The `Nat.add` rules are derivable from the definition
  without an axiom (DESIGN §13). These three need `Quot.funext`, so
  `Quot.sound`. Making them definitional means some theorems would no longer
  list `Quot.sound` in `stitchwort axioms`. They aren't proving more; their
  proofs just no longer mention the axiom. That changes what an empty axiom
  report means for effectful code. Consistency should be safe, because
  function extensionality holds in the models Stitchwort's theory already
  assumes (`Quot.sound` gives it) **[inferred]**.
- Normalisation and the conversion checker: R-assoc pushes binds to the
  right; R-fuse moves a fold inside. Both decrease a simple measure, but the
  argument for the whole system has to be written out, as nat-add-recursion
  §9 did **[inferred]**.
- The elaborator's unification must apply the same rules, or `rfl` will
  type-check in the kernel and fail in the elaborator (the drift SW-870 is
  about).
- The runtime is untouched: the machine replaces `bind` and `foldComp` with
  natives (tail-resumptive-handlers.md §1.1), and the rules only change
  which terms the checker considers equal.

**Next step.** A design note in the style of nat-add-recursion.md:
the rules, the critical pairs, the binding by content hash, the meaning of
the axiom report, and a measured check on rogue's draw-then-plan proofs.
Decision D1850. Ticket T3.

### 4.2 Hoare reasoning that yields equations (from Kidney, Yang and Wu, POPL 2024)

**What they do [checked].** Theories with equations, for example state and
nondeterminism with their laws, are encoded as quotient types in Cubical
Agda, "instead of setoids" (§1). A Hoare triple `{φ} p {ψ}` is itself an
equation between programs:
`do a ← φ; x ← p; b ← ψ x; return (x, a → b)` equals the same program with
`True` in place of `a → b`. The usual rules are derived. The new rule is
H-elim: if `{} x ← p {return (φ x)}`, and `φ x` implies `f x ≡ g x`, then
`p >>= f ≡ p >>= g` (Theorem 7.1). They say this is "surprisingly difficult
to prove constructively", and their proof needs finite arities (§7). Their
parser example uses it: they prove a Hoare triple, then derive with H-elim
the equation `(do push (print t); parse-tree n) ≡ return t`. That equation
"can be substituted … in any context", which a Hoare triple can't (§1).
The logic is for partial correctness; total correctness is future work
(§9).

**How it maps onto Stitchwort.** `Effect.Always P c` is exactly the
"pure postcondition" triple `{} x ← c {P x}` on the free monad, with
`alwaysBind` as its sequencing rule (`std/Effect/Always.sw:14-30`)
**[checked]**. H-elim's hard part comes from the quotient. On Stitchwort's
unquotiented `Comp` it is an easy induction **[inferred]**:

```
theorem Effect.bindCongAlways (P: a → Prop) (f g: a → Comp op res b)
    (same: (x: a) → P x → f x = g x):
    (c: Comp op res a) → Always P c → bind c f = bind c g
  -- Done x: same x holds
  -- Call o rest: Quot.funext on y, by the induction hypothesis at rest y
```

That is the lemma rogue's PROOFS.md says is still missing for "an
*equation* about a handled program" (gap 2): the generator proofs already
use `Always` for properties, but have no way back to equations. With 4.1 it
would no longer need the axiom. Without 4.1 it needs `Quot.funext`, like
`bindAssoc`.

What doesn't transfer: their state-aware triples rely on the equational
theory of state. Stitchwort's `State` has no equations on `Comp`; its
meaning is the handler `runState`. Hoare reasoning about state therefore
belongs to handlers, which is deep read 4.3.

**Risks.** Few. *Assumption: users state equations about computations
rather than about handled results.* If rogue's next proofs are all about
`Always`-style properties, the lemma is merely nice to have.

**Next step.** Ticket T2: add `Effect.bindCongAlways` and use it once in
rogue to state one handled-program equation. No decision needed.

### 4.3 Specifications for handlers (from Lean's `Std.Do`, `mvcgen` and `vcgen`)

**What Lean does [cited].** A monad gets a `WP` instance, which reads each
program as a predicate transformer: it maps a postcondition to the weakest
precondition that ensures it. The transformer must be conjunctive and
monotone. A `PostShape` describes the monad's state (`arg σ`) and exceptions
(`except ε`), so a postcondition has a part for each exception
([predicate transformers](https://lean-lang.org/doc/reference/latest/The--mvcgen--tactic/Predicate-Transformers/)).
Each function gets a specification lemma, registered with `@[spec]`, either
a triple (`⦃fun s => ⌜s.1 = n⌝⦄ mkFreshNat ⦃fun r s => ⌜r = n ∧ s.1 = n +
1⌝⦄`) or an equation. `vcgen` splits a triple into verification conditions
"pre ⊑ post" in which the program no longer occurs, and hands them to
`grind`. Loops need invariants
([vcgen](https://lean-lang.org/doc/reference/latest/The--vcgen--tactic/)).
`vcgen` accepts any program type with a `WP` instance, including "an
inductive type of commands … once its weakest precondition is defined in
terms of an operational semantics". That describes `Effect.Comp` plus a
handler.

**How it maps onto Stitchwort.** SW-570 and rogue's "Tried" table show the
failure this avoids **[checked]**. Proofs that unfold a handler over a
computation with unknown values run out of resources (E-RESOURCE), and
were rescued by making definitions opaque, or by `Always`, which never runs
the handler. A specification layer would make "never run the handler"
the normal route:

- **`Effect.Spec`, per handler.** A handler `h` that turns
  `{A | e} a` into `{e} r` gets a predicate transformer
  `wp_h: Comp … a → (r → Prop) → Prop` (with state: `(a → s → Prop) →
  s → Prop`). It is defined by `foldComp`, so its equations for `Done`, `Call`
  and `bind` hold by computation or by `foldCompBind`.
- **Specs for operations.** One lemma per operation of the ability, for
  example `wp_runState (Call get k) Q s = wp_runState (k s) Q s`. These are
  the `@[spec]` lemmas.
- **Adequacy.** One theorem per handler: `wp_h c Q` implies `Q` of the
  handled result. Lean has the same (`StateM.of_wp_run_eq`, named on the
  truncated page).
- **Automation, later.** A `vcgen`-like step that rewrites `wp` through
  `bind` and the spec lemmas, then leaves the conditions to `auto` and
  `omega` (proof-automation.md).

`Always` is the special case of the trivial handler: `wp` with every
operation's answer universally quantified **[inferred]**.

**Risks.**

- *Assumption: the cost is in symbolic evaluation of handlers, not in the
  property.* The rogue notes support this: two of three failures were
  definitions "cheap to run and enormous to compare" (PROOFS.md, gap 3).
- `foldComp` folds a `rest` thunk. A `wp` that recurses through it meets the
  termination problem rogue met with `Always` ("the termination check sees a
  thunk, `() => k y`"), which `AlwaysTree` solved. The layer will need a
  data version too **[inferred]**.
- Partial programs (`{Partial}`) have nothing to prove under a handler
  (partial-handlers.md §3.5), so whole-loop proofs still need fuel. The layer
  doesn't change that.

**Next step.** A design note (ticket T4, decision D1851): `wp` for `State`,
`Abort`, `Random` (rogue) and `Parse`, the adequacy theorems, and one rogue
proof redone through it, measured against today's.

### 4.4 Declared fast paths (from Lexa, OOPSLA 2024)

**What they do [checked].** A lexical handler is a value in scope, so an
operation jumps to it directly, and the resumption is captured as stacks
"without search" (§1). The authors show that Effekt's lift inference "effectively
causes the generated code to walk the stack to locate the right handler"
(§1). Handlers are *declared* tail-resumptive (`tail`) or abortive
(`abort`). Such handlers run on the parent's stack, with no new stack and no
reified resumption (§5). And: "with lexical scoping, a tail-resumptive
handler has already captured the right handlers in its lexical closure, so
it can be invoked directly without extra machinery". They contrast this with
the `under` construct that Koka's in-place clauses need (§5).

**How it maps onto Stitchwort.** Stitchwort's handlers are found
dynamically: an operation bubbles out through every fold
(tail-resumptive-handlers.md §1.1) **[checked]**. A clause runs in `out`, so
its own operations go to outer handlers (docs/core.md, `handle`)
**[checked]**. So in-place clauses do need Koka's `under` in general. That
supports SW-792's limit (empty-row handlers first): a clause at the empty row
performs nothing, so it has nothing to route **[inferred]**. Lexa's design
point is the other one: *declare* the mode. SW-791 recommends detecting it
automatically, as `fusion.rs` already does for state loops. SW-861 shows the
cost of silent detection: moving `k` into a match arm left the fast path,
and nothing said so (9.4 s against 2.2 s, measured 28 Oct) **[checked]**
(ticket text).

**Steal.** Keep automatic detection, and add an *assertion* the author can
make, in the spirit of Scala's `@tailrec`: an attribute on a handler (or a
`stitchwort check --explain-handlers` report) that fails, or warns, when the
handler isn't run as a fused loop or in place, and says which clause broke
it. That serves SW-791 (automatic stays) and SW-861 (the regression would
have been seen), and it fits attributes.md.

**Risks.** The assertion ties the language to a backend property. It has to
be phrased as "runs without capturing a resumption on all backends", or be a
report only. *Assumption: the fusion analysis in `crates/rt/src/fusion.rs`
can report why it gave up* **[unverified]**. I didn't read the function.

**Next step.** Ticket T5. A short note under attributes.md. No decision
beyond SW-791, which this supports.

### 4.5 TRMC through effect continuations (from Leijen and Lorenzen, POPL 2023, §6)

**What they do [checked].** Koka's TRMC applies to `map` with an effectful
callback. The danger is a resumption used more than once, which would see a
context with a hole that has been filled in place. Two fixes (§6.1–6.2):

- a uniqueness check at context composition: copy the chain if it is
  shared ("an extra uniqueness check … quite fast in practice"), skipped
  when the effect type is known to be linear;
- two versions of the function, with a runtime check: "in Koka, each
  handler has a flag that signifies if it may resume more than once and we
  can check efficiently at runtime if any such handler is in the current
  evaluation context". This is what Koka's JS backend does.

**How it maps onto Stitchwort.** SW-868: `List.map` with an `{IO}` callback
runs out of frames at about 2,000,000 elements on the interpreter and the
native build, because the generic-row `map` keeps its recursive call inside
`bindIn e (f x) (y => Cons y (map xs f))`. `crates/rt/src/trmc.rs` refuses
to twin such functions, and its header gives the reason: a cell must not be
reachable by a continuation that could run twice (`trmc.rs:36-48`)
**[checked]**. Koka's second fix maps onto Stitchwort's runtime as follows
**[inferred]**:

- Twin the generic-row `map` into a destination-passing version that is
  used only when no handler between the call and the top may resume more
  than once.
- Clause shape can say "resumes at most once" statically: `fusion.rs`
  already recognises tail-resumptive clauses, and the clause for `IO` is the
  runtime's own.

**Risks.** Stitchwort's resumptions are persistent and multi-shot by design
(D1162 §9.1.1). The guard must be exact, or `Each.collect` and other
multi-shot handlers would observe sharing. This is the hardest of the five.
*Assumption: effectful `map` over millions of elements matters to someone.*
SW-868's option (a) says the AoC need was the pure case.

**Next step.** Add this as option (b′) to SW-868's decision text (ticket
T6). Don't design it unless Matt picks (b).

## 5. Steal next (ranked by value against effort)

| Rank | Idea | Helps | Cost | Source |
|---|---|---|---|---|
| 1 | DESIGN.md: retire the handler-termination conjecture text; name the real gap (faithful translation) | correctness of docs; §16 Q6, Q9 | small (docs) | our code and docs [checked]; C8 |
| 2 | `Effect.bindCongAlways` (H-elim on the free monad) | rogue gap 2, SW-548 | small (std) | C2, deep read 4.2 |
| 3 | Handler fast-path assertion or report | SW-861, SW-791 | small (diagnostic) | C4, deep read 4.4 |
| 4 | Handler specifications as predicate transformers (`wp` per handler, spec lemmas, adequacy) | SW-570, rogue loop | medium (std + note), tactic later | C3, C2, deep read 4.3 |
| 5 | Monad laws as trusted conversion rules (`bind`, `foldComp`) | SW-548, rogue gap 2, proof ergonomics | kernel change | C1, deep read 4.1 |
| 6 | Messages never show a bare row unknown without saying where it came from | effect error messages | small | C6 |
| 7 | TRMC for generic-row `map`, guarded by "no multi-shot handler in scope" | SW-868 (b) | runtime, large | C5, deep read 4.5 |
| 8 | Per-ability runtime strategy (rare against frequent operations) | SW-593 | research | C11 |
| 9 | Modal effects instead of `{e}` on higher-order functions | effect-polymorphism ergonomics | research; conflicts with DESIGN §8 | C6 |

## 6. Proposed tickets (label `research`; not added to the board)

**T1. DESIGN.md: handler termination is checked by the kernel, not a
conjecture.** DESIGN.md:42, :123, :552, §8 "When handlers are trusted to
terminate", §13 "Known gaps" and §16 Q6/Q9 describe a tracked conjecture and
a `stitchwort assumptions` command. Neither exists in `crates/` (grep for
`conjecture` and `assumptions`, 29 Oct). abilities.md (option B, termination
rule) and docs/core.md "Abilities" say the kernel's positivity and
termination checks prove termination of the translated program. Rewrite
those passages to match, and name the trust that remains: that the
translation is faithful to the source semantics (abilities.md:35), tested by
comparing behaviour. Q9 (one-shot at runtime) is answered by D1162's
persistent multi-shot continuations. Hamana (LMCS 2022) is a reference if a
source-level termination argument is ever written.

**T2. Std: `Effect.bindCongAlways`, H-elim for the free monad.** If every
result of `c` satisfies `P`, and `f x = g x` whenever `P x`, then
`bind c f = bind c g`. Proved by induction on `c`, with `Quot.funext` at
`Call` (as `bindAssoc`). From Kidney, Yang and Wu (POPL 2024, Theorem 7.1),
where the quotient makes it hard; here it is easy. Use it in rogue to state
one equation about a handled program (PROOFS.md gap 2), and record what it
did or didn't unlock.

**T3. Design note: the monad laws of `Effect.bind` and `Effect.foldComp` as
trusted conversion rules.** Three rules (R-assoc, R-unit, R-fuse, deep read
4.1), applied when the definition is stuck, bound by content hash as the
`Nat.add` rules are. The note must give the critical pairs (the R-fuse and
R-assoc overlap in particular), a normalisation argument, the elaborator's
unification doing the same, and what `stitchwort axioms` then means, since
the equations need funext. Measure on rogue's draw-then-plan proofs and
SW-570's examples. Decision D1850.

**T4. Design note: specifications for handlers (`Effect.Spec`).** After
Lean's `Std.Do` and `vcgen`: a predicate transformer `wp` for each library
handler (`State`, `Abort`, `Random`, `Parse`), one spec lemma per operation,
an adequacy theorem per handler, and a data form where termination needs it
(as `AlwaysTree`). Redo one rogue proof through it and compare with today's
(time, opaque definitions needed). A `vcgen`-like tactic is a later stage.
Decision D1851.

**T5. A handler fast-path assertion or report.** An attribute on a
handler, or a `check` report, that says whether each handler runs as a fused
state loop (fusion.rs) or in place, and when not, which clause stopped it.
From Lexa's declared `tail`/`abort` handlers (OOPSLA 2024 §5). It would have
caught SW-861's silent slowdown. It complements SW-791 (detection stays
automatic).

**T6. SW-868: add Koka's guarded TRMC as option (b′).** Leijen and Lorenzen
(POPL 2023 §6.2): twin the effectful function, and choose the
destination-passing version only when no handler in scope may resume more
than once. Add to SW-868's options, with the risk that Stitchwort's
continuations are persistent and multi-shot (D1162). No design unless (b) is
chosen.

**T7. Refresh this register quarterly.** Rerun §1.2's queries for the new
months, screen, card, and update §5. Next: January 2027.

## 7. Decisions for Matt

- **D1850.** Should the monad laws of `Effect.bind` and `Effect.foldComp`
  hold by conversion (trusted rules in the kernel, as `Nat.add`'s two extra
  rules), even though their equations need funext? This would close SW-548
  and make rogue's two forms of one program convertible. **[Yes to a design
  note (T3) only; decide the kernel change after it.]**
- **D1851.** A specification layer for handlers in std (`wp` per handler,
  after Lean's `Std.Do`), aimed at SW-570 and rogue's loop? **[Yes, design
  note first (T4), after T2 lands.]**
- **D1852.** Retire the handler-termination conjecture from DESIGN.md (T1),
  and make "the translation is faithful" the tracked gap instead? **[Yes.]**
