# Effects and handlers: ideas to steal

**Counts: screened 75; carded 11; read in full 10 (all ten paper cards); not read 0. C3 is
Lean's reference manual, read in full as it stands on 30 Oct 2026; some quotes from the 29 Oct
version are no longer on the pages (see C3).** The 29 Oct version had no counts line. By its own
§1.2 it had read one card's paper in full (C2), five in part (C1 introduction, C4 and C11 the
abstract and some sections, C5 §6, C6 §1) and four not at all (C7, C8, C9, C10).

**Audited 30 Oct 2026 against full texts: 6 OK, 4 minor (fixed), 1 wrong (fixed), 0 can't
verify** (of the 11 cards; the four first marked unverified or NOT READ were read for the audit
and their claims hold). Every card now says what was read and ends with "Audit:". PDFs were read
with `pdftotext` (`nix shell nixpkgs#poppler-utils`). Lean's manual was read as text from HTML
fetched with `curl`. For a long theory paper (C1, C6), "read" means the prose, definitions,
examples and conclusions, with the proofs and appendices skimmed. Each card names the sections.

**Claims of the 29 Oct version found wrong** (each checked against the paper or our code):

1. *`Effect.bindCongAlways` "helps … SW-548" and is "the lemma rogue's PROOFS.md says is still
   missing" for an equation about a handled program* (old C2, §4.2, T2). Wrong. PROOFS.md gap 2
   says that equation (`Random.withSeed s (() => f (p())) = f (Random.withSeed s p)`) "would
   still need" `Effect.bindAssoc`. Moving a pure `f` through a handler is a fusion and
   associativity fact, not a congruence under a postcondition. H-elim's analogue doesn't touch
   `bindAssoc`'s axiom either, so it doesn't help SW-548 (C2, §4.2).
2. *"With 4.1 it would no longer need the axiom"* (old §4.2). Wrong. At `Call o rest` the
   lemma must equate `y => bind (rest y) f` and `y => bind (rest y) g`, whose bodies are only
   *propositionally* equal (by the induction hypothesis). That step needs `Quot.funext`
   whatever conversion rules for `bind` exist (`crates/elab/src/std/Effect/Laws.sw:15-18`, `bindDone`, has the same shape).
3. *The monad laws by conversion, including R-fuse, "from Yang and Wu"* (old §0 item 1, §4.1).
   Misattributed in part. The paper gets the laws judgementally *by giving up* the law that
   handling commutes with `let` (Remark 2.11, "having hdl-let would result in inconsistency"
   with lawless handlers; Contributions, §1.3). Its §6 item 6 leaves open whether a dependently
   typed language can have "all the laws judgementally". R-assoc, R-unit and R-fuse as trusted
   kernel rules are the old register's own proposal, and the paper is evidence about the
   trade-off, not support for R-fuse (§4.1).
4. *C9's link* pointed at LIPIcs.ECOOP.2023.29, which is the noninterference paper (row 21).
   Interaction Tree Specifications is LIPIcs.ECOOP.2023.30.
5. *"Found on the way": DESIGN.md still calls handler termination a conjecture* (old §0, T1,
   D1852). True on 29 Oct, now done: SW-899 rewrote DESIGN.md §1, §3, §7, §8, §13 and §16
   (`4e33920c`). T1 and D1852 are closed.

Status: research register for SW-894, cluster 5 (effects and handlers),
29 Oct 2026; audited 30 Oct 2026 against `main` at `82a79b30`. Window: papers from 2022 on
(D1831); older work only where in-window papers lean on it, marked "(classic)". No code changes.

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
  1. **Monad laws that hold by conversion** (prompted by Yang and Wu, POPL
     2026, who get them judgementally by giving up the law that handling
     commutes with `let`). For Stitchwort this could mean `bindAssoc` and
     `bindDone` as trusted conversion rules, as with the two extra `Nat.add`
     rules, or a CPS form of computations, the paper's own model, in which
     they hold by β and η (§4.1). That would close SW-548, and with it
     rogue's gap 2. It is a kernel change, so a decision (D1850).
  2. **Hoare reasoning that yields program equations** (Kidney, Yang and
     Wu, POPL 2024: the lemma H-elim). Stitchwort's free monad needs only
     the easy case: a short lemma beside `Effect.alwaysBind`, which still
     needs `Quot.funext`. Small, but it neither closes SW-548 nor gives
     rogue's gap-2 equation (audit, wrong claims 1 and 2).
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
  (abilities.md:35). Ticket T1. *Audit, 30 Oct: done as SW-899
  (`4e33920c`); DESIGN.md §8 "How handlers terminate today" now names the
  two things trusted (the termination rule for function fields, and the
  translation's faithfulness).* Hamana (C8) proves strong normalisation of
  a handler by the same argument the kernel uses, that `M[x]` is smaller
  than `get(x.M[x])` (§4.5 of that paper); it is a citation for the first
  of the two trusted items, not a proof for this kernel.

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

Full texts read (29 Oct): Kidney–Yang–Wu (POPL 2024), Yang–Wu (POPL 2026,
introduction), Lexa (OOPSLA 2024, abstract, §1–2 and §5), Zero-Overhead
Lexical Effect Handlers (abstract, §1), Modal Effect Types (abstract, §1),
TRMC (POPL 2023, §6). These PDFs were fetched with curl and turned into
text with macOS PDFKit. Lean reference pages: `mvcgen` overview, predicate
transformers (first half only), `vcgen`.

Audit (30 Oct): all ten papers fetched again with curl and read with
`pdftotext`; each card names its sections. Sources: arXiv (C1, C6), the
authors' pages (C2, C4, C5, C7, C11), LMCS (C8), DROPS (C9), and an
Internet Archive `id_` copy of the ACM PDF (C10, DOI 10.1145/3547640).
Lean's manual: `mvcgen` §18.1 and §18.2, `vcgen` §17 and §17.1–17.4,
in full. One WebSearch (the JFP version of C5). DBLP returned a bot
page; Semantic Scholar's API answered once, then returned 429.

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
- *Audit, 30 Oct:* the F\* venue was not re-checked. Unison's and Koka
  v3.2's notes were not looked for. The rows they back stay
  **[unverified]** and support nothing. Lean's pages were read in full
  this time (C3). No full text was unreachable, so nothing is for Matt to
  fetch. The 64 screened-only rows were not re-screened.

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
*Full text:* read ([arXiv PDF](https://arxiv.org/pdf/2511.05739), v1 with
appendices; §1, §2.3 and Remarks 2.11-2.12, §3.1-3.2 (the realizability
model, eq. 9), Theorems 3.3-3.6 and 4.1 as stated, §6; §4 proofs and the
appendices skimmed). *Audit: MINOR, fixed in §4.1.* The quoted claim, "the
computation judgements still satisfy the monadic laws judgementally", is in
the abstract; canonicity and parametricity are for the recursion-free
fragment (abstract; Theorem 4.1, Remark 4.14). The card left out the price:
handling does *not* commute with `let` (`hdl-let`, Remark 2.11), because
with lawless raw monads "having hdl-let would result in inconsistency". And
the calculus is System Fω with effects, not dependently typed. §6 item 6
asks whether a dependently typed language with lawful monads "can … make the
computational judgements satisfy all the laws judgementally", as an open
question. The model of computations is a CPS encoding (eq. 9),
`co H A = (h : Handler H) → (B : P) → (A → h B) → h B`, which validates the
laws. That bears on how Stitchwort might get them (§4.1).

**C2. Kidney, Yang and Wu, "Algebraic Effects Meet Hoare Logic in Cubical
Agda", POPL 2024.** [PDF](https://yangzhixuan.github.io/pdf/free.pdf),
[doi](https://doi.org/10.1145/3632898). Claim: an effect-generic Hoare logic
over free monads quotiented by equations, plus an elimination principle,
H-elim, that turns a Hoare triple into a program equation. Steal: the H-elim
pattern, which is easy for Stitchwort's unquotiented `Comp`. Helps rogue
gap 2 and SW-548. Cost: small (one std lemma). Full text: yes. Deep read 2.
*Full text:* read ([author PDF](https://yangzhixuan.github.io/pdf/free.pdf);
§1-2, §4.2-4.4, §6, §7 with Theorem 7.1 and Lemmas 7.3-7.5, §8, §9; DOI
confirmed by doi.org and Semantic Scholar). *Audit: WRONG in the steal,
fixed.* The paper's claims are as stated: quotients "instead of" setoids
(§1), the triple as an equation of programs (§1, Definition 6.1), H-elim
(Theorem 7.1) "surprisingly difficult to prove constructively" (§1), and
the parser equation (1) derived by H-elim (§7, end), "substituted … in any
context" (§1). Two details were missing: the constructive proof needs
Bishop-finite arities but the proof with excluded middle doesn't (§7,
Remark), and deriving equation (1) also needs Lemma 7.5, which assumes the
parser is total ("true for sufficiently large step-index n"). Total
correctness is future work (§9). The wrong part was "Helps rogue gap 2
and SW-548": see wrong claims 1 and 2 at the top. The lemma is still worth
having for what H-elim is for: two continuations that agree only where a
postcondition holds give the same computation.

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
*Full text:* read, the manual as published on 30 Oct 2026 (now with
4.36.0-rc2 tutorials): `mvcgen` §18.1-18.2, `vcgen` §17 and §17.1-17.4.
*Audit: MINOR, fixed.* The substance holds: `vcgen` takes any program type
with a `WP` instance, and §17.1 now says "Non-monadic types, such as the
syntax trees of a small imperative langauge, are also supported"; the
verification conditions "contain no weakest preconditions" (§17.1); the
`with` clause runs a `grind`-mode step on them (§17.3). But the three
quoted phrases ("the original program `prog` no longer occurs", "carries a
`Std.WP.WP` interpretation", "an inductive type of commands … operational
semantics") aren't on today's pages, so they can't be checked; the pages
have changed. Two details changed with them: `vcgen` lives in `Std.WP`
(with `Std.Tactic.Do`), and its soundness lemmas are `…of_run_eq_wp`
(`mvcgen`'s, in `Std.Do`, are `…of_wp_run_eq`, as §4.3 says). For `vcgen`,
`WP` requires only monotonicity; conjunctivity is a separate class,
`WPConjunctive` (§17.2). "`mvcgen` (4.22)" in row 3 wasn't checked. The
`mkFreshNat` example in §4.3 isn't on the pages read.

**C4. Ma, Ge, Lee and Zhang, "Lexical Effect Handlers, Directly", OOPSLA
2024.** [PDF](https://cs.uwaterloo.ca/~yizhou/papers/lexa-oopsla2024.pdf).
Claim: compile lexical handlers to stack switching without searching for
the handler; "reducing running-time complexity from quadratic to linear in
some cases" **[checked]**. Tail-resumptive and abortive handlers are
declared, and run in place with no `under` construct **[checked]** (§5).
Steal: declared fast-path modes as assertions. Helps SW-790–792 and SW-861.
Cost: small (a diagnostic); the compilation scheme itself would be a
research project. Full text: yes. Deep read 4.
*Full text:* read ([author PDF](https://cs.uwaterloo.ca/~yizhou/papers/lexa-oopsla2024.pdf);
§1-2, §5, §7, §8 prose; §3-4 and §6 skimmed). *Audit: OK.* The quotes are
in the abstract, §1 and §5. Not in the card, and relevant here: Lexa's
formalism has no multi-shot resumptions ("a nongoal for us"), and the
implementation allows one only if it holds "no more than one stack" and at
most one copy is installed at a time (§7.2). Stitchwort's resumptions are
unrestricted multi-shot (D1162), so the compilation scheme wouldn't carry
over as is; the declared modes would.

**C5. Leijen and Lorenzen, "Tail Recursion Modulo Context", POPL 2023.**
[PDF](https://www.microsoft.com/en-us/research/uploads/prod/2023/07/trmc-popl23.pdf).
Claim: TRMC generalises to any context with the right algebra. In a language
whose handlers may resume more than once, it stays sound if a context is
copied when shared, or if a second, slower version runs whenever a
multi-shot handler is in scope (§6.1–6.2) **[checked]**. Steal: the guard
for effectful `map`. Helps SW-868 option (b). Cost: runtime change. Full
text: yes (§6). Deep read 5.
*Full text:* read ([MSR PDF](https://www.microsoft.com/en-us/research/uploads/prod/2023/07/trmc-popl23.pdf);
§1-2, §5 prose, §6, §7 headings; proofs skimmed). The JFP version is
"Tail recursion modulo context: An equational approach (extended
version)", JFP 35 (2025) e22 (found by one WebSearch; not read).
*Audit: MINOR, fixed.* The quotes and §6.1-6.2 are as stated. The card
said "if a context is copied when shared" without the condition the paper
gives: the hybrid of §6.1 "depends on both having precise reference
counts, and having extra bits in a header" (§6.2). Stitchwort's runtime
does count references (compilation.md §1), so the hybrid, not only the
two-version fallback, is a candidate for SW-868 (b) **[inferred]**
(§4.5).

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
*Full text:* read ([arXiv PDF](https://arxiv.org/pdf/2407.11816), v3, 60
pages with appendices; §1, §2.1-2.3, §8.1-8.2 read; §3-7 skimmed). *Audit:
OK.* The Frank error and "no hidden effect variables" are in §1. Met itself
is simply typed; effect polymorphism is added back in §6 "to recover the
full power of traditional effect systems" (§1, contributions). Its rows
are scoped and allow duplicate labels (§2.1), unlike Stitchwort's
(abilities.md, "Labels"). §8.2 compares Metl, Koka and Effekt signatures
for the same programs, the quickest way in if (b) is ever considered.

**C7. Ikemori, Cong, Masuhara and Leijen, "Sound and Complete Type Inference
for Closed Effect Rows", TFP 2022.**
[PDF](https://prg.is.titech.ac.jp/papers/pdf/tfp2022inference.pdf). Claim:
Koka closes the rows of `let`-bound functions and opens them again at use
sites; this paper formalises it and proves it sound and complete
**[unverified]** (search summary). Steal: a citation, and a check, for D1124
(an undecided row unknown becomes `Empty`). Helps effect-polymorphism.md
§5.C.1. Cost: none (reading). Full text: not read.
*Full text:* read ([PDF](https://prg.is.titech.ac.jp/papers/pdf/tfp2022inference.pdf),
LNCS 13401 pp. 144-168; §1-3 in full, §4-7 prose). *Audit: OK.* The claim
holds: "close the effect row of all named functions (bound by the let/val
expression), and open the effect row when we encounter variables of a
closed function type" (§2.3), proved sound and complete with respect to
declarative rules (§1, §4-5). The motive is runtime as well as
readability: a closed row lets evidence passing find the handler "at a
fixed offset in the vector" (§1). The mechanism differs from D1124:
Koka closes at `let` generalisation, while Stitchwort sets an undecided row
unknown to `Empty` at the end of a declaration (docs/core.md, "A row
unknown"). So it is a related citation, not the same rule. Koka's rows may
repeat a label (§3.1.3); Stitchwort's may not.

**C8. Hamana, "Modular Termination for Second-Order Computation Rules and
Application to Algebraic Effect Handlers", LMCS 2022.**
[LMCS](https://lmcs.episciences.org/9702). Claim: strong normalisation of a
CBPV calculus with handlers and effect theories, by semantic labelling and
the General Schema **[unverified]** (abstract). Steal: a reference for the
write-up that T1 asks for (termination of the *source* semantics, as a
second argument beside the kernel's check of the translation). Cost:
reading. Full text: not read.
*Full text:* read ([LMCS PDF](https://lmcs.episciences.org/9702/pdf),
LMCS 18(2:18) 2022; §1, §2.6-2.7, §3 statements, §4 in full, §6). *Audit:
OK.* The abstract's claim is as stated; the calculus is `mam`, a variant of
CBPV, with one handler (global state) and the state theory (§4.2-4.4).
The handler half is SN by the General Schema alone, using the structural
subterm order "to establish that M[x] is smaller than get(x.M[x])"; the
hard part is the effect theory's equations, which fail the General Schema
and need the modular theorem (§4.3, §4.5). "Any effect handler is shown to
be SN by GS along this way" (§4.5). That is the same shape as the kernel's
rule that `rest y` is smaller than `Call o rest` (abilities.md, "The
termination rule"). T1 itself is done (SW-899).

**C9. Silver, Westbrook, Yacavone and Scott, "Interaction Tree
Specifications", ECOOP 2023.**
[DROPS](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ECOOP.2023.30).
Claim: a specification is an interaction tree with quantifier events
(`forall`, `exists`), and refinement between trees gives syntax-directed,
"auto-active" proofs **[unverified]** (abstract). Steal: specifications
written in the program's own language, as trees. This is an alternative to
the predicate transformers of C3 for SW-570. Cost: research project. Full
text: not read.
*Full text:* read (DROPS PDF, LIPIcs.ECOOP.2023.30; §1-2 in full, §3-4
prose, §6 skimmed). *Audit: MINOR, fixed.* The link pointed at
ECOOP.2023.29, which is row 21's noninterference paper. The claim holds:
`Spec_forall` and `Spec_exists` events (§3), and specifications as
"syntactic constructs enabling syntax-directed inference rules" (§1). The
trees are coinductive interaction trees and the specifications are about
possibly non-terminating programs (abstract, §1), unlike Stitchwort's
finite `Comp`; that makes it a further-off fit than C3.

**C10. Ullrich and de Moura, "'do' Unchained", ICFP 2022.**
[supplement](https://kha.github.io/do-supplement/print.html). Claim: local
mutation, `for`, `break` and early `return` inside `do`, translated to
monadic code with proofs that the translation is right. A Zulip thread says
Lean's real elaborator differs **[unverified]**. Steal: if Stitchwort grows
`var`/`for` in effectful blocks, translate them to `State`/`Abort` handlers
in the same way. Cost: design note. Full text: not read.
*Full text:* read ([Internet Archive copy of the ACM PDF](https://web.archive.org/web/2023id_/https://dl.acm.org/doi/pdf/10.1145/3547640),
PACMPL 6 ICFP, Article 109; §1-2, §5 in full, §3-4 rules skimmed).
*Audit: OK.* The abstract states the translation rules and "formally
prove[s] the correctness of the translation rules relative to a simple
static and dynamic semantics in Lean". The paper itself says Lean's built-in
version is "a more extensive implementation" than the reference macros
(§1, §5.1), so the Zulip remark adds nothing and stays unverified. The
translation targets the `StateT` and `ExceptT` transformers, not handlers;
for speed Lean then moved to CPS versions, `StateCpsT` and `ExceptCpsT`
(§5.2).

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
*Full text:* read ([author PDF](https://cs.uwaterloo.ca/~yizhou/papers/zero-oopsla2025.pdf),
PACMPL 9 OOPSLA2, Article 399; §1-2 in full, §3 rules and evaluation
skimmed). *Audit: OK.* The quote is in the abstract; §1 says rare effects
"can use the new zero-overhead implementation strategy, while effects
expected to be raised more frequently can still use existing strategies".
The scheme is for lexically scoped handlers of "exceptional effects"
(abstract).

## 4. Deep reads

### 4.1 Monad laws by conversion (from Yang and Wu, POPL 2026)

**What they do [checked].** Their calculus keeps sequencing a
judgement-level construct, and lets handlers be carried by raw monads with
no laws. The computation judgements still satisfy the monad laws
judgementally, so a program that differs from another only by how its
`let`s are nested is the same program. They argue that sequential
composition "ought to be an operation for a notion of computation" (§1.2.3).
They prove canonicity and parametricity for the recursion-free fragment.

**Audit, 30 Oct [checked].** The price of that design is stated in the
paper and was missing here: `hdl-let`, the law that handling a `let` is
the handler's bind of the handled parts, is left out, because with lawless
raw monads it "would result in inconsistency" (Remark 2.11; §1.3, §6 item
6). Their calculus has no dependent types. Its model of computations is a
CPS (impredicative) encoding, `co H A = (h : Handler H) → (B : P) → (A → h
B) → h B` (§3.2, eq. 9), in which `val` and `let-in` are λ-terms, so the
laws hold by β. Two readings for Stitchwort follow **[inferred]**:

- Stitchwort's fold is not a lawless raw monad, so their inconsistency
  argument doesn't apply to `foldCompBind`, which is a theorem here
  (`crates/elab/src/std/Effect/Laws.sw:40-55`). Making it a conversion rule is a separate question
  that the paper doesn't address.
- Their route to the laws is a representation, not rewrite rules. The
  analogue would be computations in CPS form, `(r: Type) → (a → r) →
  ((o: op) → (res o → r) → r) → r`, where `bind` is composition and the
  laws hold by β and η. The costs: such a type lives a universe up (Type 1
  for `r : Type`, since only `Prop` is impredicative), and it has no
  induction principle, so `Always`, `AlwaysTree` and every proof by
  induction on a computation would be lost. So it isn't a drop-in. It is
  worth stating in T3's note as the alternative the rules are weighed
  against.

**How it maps onto Stitchwort.** Stitchwort chose option B: computations
are data, `Effect.Comp` with `Done | Call`, and `bind` and `foldComp` are
ordinary definitions (`crates/elab/src/std/core/Effect.sw:12-28`)
**[checked]**. So the laws are propositional. `bindDone`, `bindAssoc` and
`foldCompBind` (`crates/elab/src/std/Effect/Laws.sw:12-55`) each need `Quot.funext` at the `Call`
case, because `Call`'s `rest` is a function **[checked]**. That is SW-548,
and rogue's gap 2: `f (g (p()))` and `(x => f (g x)) (p())` elaborate to
binds associated differently, and only `bindAssoc` joins them
(games/rogue/PROOFS.md, "What would be needed", 2) **[checked]**.

Stitchwort can't adopt their judgement form without option A (effects in
the kernel), which abilities.md rejected. It could get the same
user-visible effect (this is the register's proposal, not the paper's;
audit): three trusted conversion rules on the library's exact
`Effect.bind` and `Effect.foldComp`, applied only when the definition is
stuck. This is the pattern already used for `Nat.add`
(`crates/core/src/nat_add.rs`, DESIGN §13) **[checked]**, with one
difference the audit adds: DESIGN §13 calls R3/R4 "left-linear,
first-order rules on constructor patterns whose equations are derivable
from the definition". These three are higher-order (their right sides
build lambdas, and `c` is matched as any stuck term) and need funext, so
the confluence and normalisation arguments of nat-add-recursion.md §9 don't
carry over as they stand:

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
  type-check in the kernel and fail in the elaborator (a drift between
  the two conversions of the kind SW-870 is about; SW-870 itself is about
  solved metavariables).
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
`alwaysBind` as its sequencing rule (`crates/elab/src/std/Effect/Always.sw:14-30`)
**[checked]**. H-elim's hard part comes from the quotient. On Stitchwort's
unquotiented `Comp` it is an easy induction **[inferred]**:

```
theorem Effect.bindCongAlways (P: a → Prop) (f g: a → Comp op res b)
    (same: (x: a) → P x → f x = g x):
    (c: Comp op res a) → Always P c → bind c f = bind c g
  -- Done x: same x holds
  -- Call o rest: Quot.funext on y, by the induction hypothesis at rest y
```

~~That is the lemma rogue's PROOFS.md says is still missing for "an
*equation* about a handled program" (gap 2): the generator proofs already
use `Always` for properties, but have no way back to equations. With 4.1 it
would no longer need the axiom. Without 4.1 it needs `Quot.funext`, like
`bindAssoc`.~~

**Audit, 30 Oct: the struck paragraph was wrong [checked].** PROOFS.md
gap 2's example equation, `Random.withSeed s (() => f (p())) = f
(Random.withSeed s p)`, moves a pure `f` out through a handler, and
PROOFS.md says it "would still need" `Effect.bindAssoc`. That is
associativity plus fusion (`foldCompBind`), not a congruence under a
postcondition, so `bindCongAlways` doesn't give it. And the lemma needs
`Quot.funext` at `Call` in any case: the two lambdas `y => bind (rest y) f`
and `y => bind (rest y) g` are equal only by the induction hypothesis, a
propositional equation, which no conversion rule for `bind` turns into a
definitional one. What the lemma does give: where a continuation is
rewritten under a fact the computation guarantees (a roll is below its
bound, say), the two programs are equal, with the fact used and no case
split on the computation.

What doesn't transfer: their state-aware triples rely on the equational
theory of state. Stitchwort's `State` has no equations on `Comp`; its
meaning is the handler `runState`. Hoare reasoning about state therefore
belongs to handlers, which is deep read 4.3.

**Risks.** Few. *Assumption: users state equations about computations
rather than about handled results.* If rogue's next proofs are all about
`Always`-style properties, the lemma is merely nice to have.

**Next step.** Ticket T2: add `Effect.bindCongAlways` and use it once in
rogue to state one handled-program equation. No decision needed.
*Audit: T2 is narrowed (§6): it is a small std lemma for the case above,
not a route to gap 2 or SW-548, which stay with T3.*

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

*Audit, 30 Oct.* Lexa §5 confirms the `under` point from the other side:
"In languages where handlers are dynamically scoped, in-place invocation of
tail-resumptive handlers is tricky to get right … the tail-resume
optimization requires a special under construct". Stitchwort's handlers
are found dynamically, so this supports D1429 (SW-792). One thing to
re-check: since `01462c09` (28 Oct, 16 minutes after the `2b541087` that
SW-861 cites), `fusion.rs` follows a tail `k v s′` into lifted `match`es
when the backend supplies their bodies, which the machine does and JS
doesn't (fusion.rs header, "A `match` is a call of a lifted definition").
So SW-861's natural form may now be fused on the machine. That should be
measured again before T5 cites SW-861 as its motive **[inferred]**.

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
*Audit [checked]: today it can't.* Its recognisers return `Option` with no
reason (`carrier`, `done_field`, `resume`: `fusion.rs:242`, `:269`, `:482`),
so T5 needs those to say why they declined.

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
(D1162; effect-runtime.md §9.1, item 1). The guard must be exact, or `Each.collect` and other
multi-shot handlers would observe sharing. This is the hardest of the five.
*Assumption: effectful `map` over millions of elements matters to someone.*
SW-868's option (a) says the AoC need was the pure case.

**Next step.** Add this as option (b′) to SW-868's decision text (ticket
T6). Don't design it unless Matt picks (b).

*Audit, 30 Oct.* The first fix, the hybrid of §6.1, "depends on both
having precise reference counts, and having extra bits in a header"
(§6.2), and the copy follows a context path stored in each constructor
(the field index, kept in Koka's object header, §6.1). Stitchwort's
machine counts references exactly (compilation.md §1), so the hybrid is a
candidate as well as the two versions. It would copy a shared chain
instead of refusing to twin. Whether a header has room for the index
wasn't checked **[inferred]**.

## 5. Steal next (ranked by value against effort)

| Rank | Idea | Helps | Cost | Source |
|---|---|---|---|---|
| 1 | ~~DESIGN.md: retire the handler-termination conjecture text; name the real gap (faithful translation)~~ **Done (SW-899, `4e33920c`).** | correctness of docs; §16 Q6, Q9 | small (docs) | our code and docs [checked]; C8 |
| 2 | `Effect.bindCongAlways` (H-elim on the free monad). *Audit: it helps neither rogue gap 2 nor SW-548 (wrong claims 1 and 2 at the top). It is a small lemma for rewriting a continuation under a guaranteed fact.* | equations under a postcondition | small (std) | C2, deep read 4.2 |
| 3 | Handler fast-path assertion or report | SW-861, SW-791 | small (diagnostic) | C4, deep read 4.4 |
| 4 | Handler specifications as predicate transformers (`wp` per handler, spec lemmas, adequacy) | SW-570, rogue loop | medium (std + note), tactic later | C3, C2, deep read 4.3 |
| 5 | Monad laws as trusted conversion rules (`bind`, `foldComp`) | SW-548, rogue gap 2, proof ergonomics | kernel change | C1, deep read 4.1 |
| 6 | Messages never show a bare row unknown without saying where it came from | effect error messages | small | C6 |
| 7 | TRMC for generic-row `map`, guarded by "no multi-shot handler in scope" | SW-868 (b) | runtime, large | C5, deep read 4.5 |
| 8 | Per-ability runtime strategy (rare against frequent operations) | SW-593 | research | C11 |
| 9 | Modal effects instead of `{e}` on higher-order functions | effect-polymorphism ergonomics | research; conflicts with DESIGN §8 | C6 |

The audit didn't re-rank the list. With row 1 done and row 2 narrowed, the
first rows to act on are 3 (after re-measuring SW-861), 4 and 5.

### 5.1 Bearing on SW-790–792 (D1427–D1429), checked in the audit

- **SW-790 (D1427, steps C then A, B after measuring).** Nothing read here
  argues against it. Lexa (C4) and Zero-Overhead (C11) get their speed
  from knowing the handler statically (lexical scoping) and from stack
  switching. Neither applies to Stitchwort's dynamically found, multi-shot
  handlers without a redesign (C4 audit: multi-shot is a non-goal there).
- **SW-791 (D1428, detect tail-resumptive clauses automatically, or mark
  them).** Lexa *declares* `tail` and `abort` (§5). Koka's book has `fun`
  clauses that are tail-resumptive by construction
  (tail-resumptive-handlers.md §2). The audit's finding that `fusion.rs`
  can't say why it declined (§4.4) is the argument for T5's report beside
  automatic detection, not instead of it.
- **SW-792 (D1429, in-place clauses for empty-row handlers first).**
  Supported. Lexa §5 says in-place tail-resumptive handlers need Koka's
  `under` when handlers are dynamically scoped, and are simple only under
  lexical scoping. A clause at the empty row performs nothing, so it has
  nothing for `under` to route **[inferred]** (§4.4).

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
*Audit: done as SW-899 (`4e33920c`, 30 Oct). Q9 is still listed in
DESIGN.md §16, as a question for JS extraction.*

**T2. Std: `Effect.bindCongAlways`, H-elim for the free monad.** If every
result of `c` satisfies `P`, and `f x = g x` whenever `P x`, then
`bind c f = bind c g`. Proved by induction on `c`, with `Quot.funext` at
`Call` (as `bindAssoc`). From Kidney, Yang and Wu (POPL 2024, Theorem 7.1),
where the quotient makes it hard; here it is easy. Use it in rogue to state
one equation about a handled program (PROOFS.md gap 2), and record what it
did or didn't unlock.
*Audit: narrowed. It doesn't give PROOFS.md gap 2's equation, which needs
`bindAssoc` and `foldCompBind` (§4.2). Use it once where a continuation is
rewritten under a fact the computation guarantees, or drop the ticket if
no such proof exists yet.*

**T3. Design note: the monad laws of `Effect.bind` and `Effect.foldComp` as
trusted conversion rules.** Three rules (R-assoc, R-unit, R-fuse, deep read
4.1), applied when the definition is stuck, bound by content hash as the
`Nat.add` rules are. The note must give the critical pairs (the R-fuse and
R-assoc overlap in particular), a normalisation argument, the elaborator's
unification doing the same, and what `stitchwort axioms` then means, since
the equations need funext. Measure on rogue's draw-then-plan proofs and
SW-570's examples. Decision D1850.
*Audit: the note should also say that these rules, unlike R3/R4, are
higher-order. It should weigh them against Yang and Wu's route, a CPS form
of computations in which the laws hold by β and η but induction on
computations is lost (§4.1).*

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
*Audit: re-measure SW-861 first (§4.4). The recognisers in `fusion.rs`
would need to return a reason.*

**T6. SW-868: add Koka's guarded TRMC as option (b′).** Leijen and Lorenzen
(POPL 2023 §6.2): twin the effectful function, and choose the
destination-passing version only when no handler in scope may resume more
than once. Add to SW-868's options, with the risk that Stitchwort's
continuations are persistent and multi-shot (D1162). No design unless (b) is
chosen.
*Audit: list §6.1's hybrid, which copies a shared context, as a second
variant (§4.5).*

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
  *Audit: closed. SW-899 did it (`4e33920c`).*

Audit note: D1850 and D1851 stand as written. Neither needs a new number.
D1850's "would close SW-548" holds for the rules themselves. The audit
withdraws only the claim that T2 helps there.
