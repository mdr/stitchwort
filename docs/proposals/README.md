# Design notes: an index

There are 156 notes in this folder (the `*.md` files other than this one),
plus a few prototype folders beside them. A note is a design as it was
argued; it isn't kept current, so its own status line is often out of date.
This index says where each note stands. It was written on 7 November 2026
(SW-2069) by reading the notes, the board and the code at `a0cea6157`.
Nothing was built or run for it.

The optimisations these notes led to, with their measurements and the ones
dropped, are logged in [../performance/log.md](../performance/log.md).

**Statuses**

- **built**: the design (or the part of it that was decided) is in the code;
  the file named is where to start reading.
- **in progress**: some stages are built, others are on the board.
- **proposed**: design only, waiting for decisions (the open D numbers are
  given) or for its tickets to be picked up.
- **superseded**: a later note or decision replaced it; the replacement is
  named.
- **parked**: decided "not now", or tried and dropped.
- **record**: a review, survey or measurement that informed a decision. It
  has nothing of its own to build.

A status is this index's reading of the note, its tickets and a grep of the
code, not a fresh audit of every claim. "Stale" marks a note whose own
status line now says the wrong thing; the details are in
[Stale claims](#stale-claims).

## Kernel and core

| Note | What it's about | Status | Tickets |
|---|---|---|---|
| [indexed-families.md](indexed-families.md) | Data types indexed by values (inductive families) in the kernel | built: `crates/elab/src/families.rs` | SW-178 |
| [vec.md](vec.md) | Length-indexed vectors, `Vec`, and AoC 2025 day 4 over them | built: `crates/elab/src/std/Vec/` | SW-179, SW-180 |
| [mutual-recursion.md](mutual-recursion.md) | Forward references, mutual recursion and size-change termination | built: `crates/core/src/sct.rs` | SW-48, SW-50, SW-117 |
| [kernel-admission.md](kernel-admission.md) | When the kernel lets a single declaration in (finished or not) | built: `crates/core/src/check.rs` | (part of mutual-recursion) |
| [nested-data-types.md](nested-data-types.md) | Data types that hold lists of themselves, `Packets (items: List Packet)` | built, stages 1-3; stage 4 (dogfood) not done | SW-704, SW-833 |
| [map-equality.md](map-equality.md) | Equality of maps through kernel quotients | built: `crates/elab/src/quot.rs`, `crates/elab/src/std/Quot/` | SW-356, SW-362 |
| [proof-irrelevance.md](proof-irrelevance.md) | Two proofs of the same fact are equal in conversion | built (stale): `crates/core/src/value.rs` (§7.10 at :2110) | SW-93, SW-1429, SW-803 |
| [record-eta.md](record-eta.md) | Record eta in the kernel: `p = { a = p.a, b = p.b }` by conversion | in progress: stages 1, 1b merged; 2-5 open | SW-1642, SW-1766, SW-1643, SW-1851-SW-1853, SW-1645; review SW-2068 |
| [record-eta-remaining.md](record-eta-remaining.md) | Plan for record eta's stages after 1b | in progress (plan); D2630-D2634 open | SW-1849, SW-1643, SW-1851-SW-1853, SW-1645 |
| [records.md](records.md) | Declared records: representation, equality, JS form | built, stage 1; stage 2 became record-eta.md; stages 3-4 (structural records) not built | SW-55, SW-568, SW-805 |
| [closed-type-values.md](closed-type-values.md) | Stop computing a statement's big values when it's declared | proposed: §7's questions open | SW-1787, SW-1788 |
| [glued-closed-types.md](glued-closed-types.md) | Keep calls folded in a theorem's closed statement | parked (D2448); reopened by closed-type-values.md | SW-1534, SW-1596 |
| [literal-match-facts.md](literal-match-facts.md) | A literal match's catch-all arm knows the value is none of the listed ones | built (stale): merged `91eead3c9`; `crates/core/src/value.rs:157` | SW-533 |
| [nat-add-recursion.md](nat-add-recursion.md) | `m + Zero` and `m + Succ n` both compute | built | SW-787 |
| [folded-calls.md](folded-calls.md) | Glued values: keep calls folded while checking | built (stale), stages 1-4: `crates/core/src/value.rs` | SW-251, SW-256, SW-257 |
| [checker-evaluation.md](checker-evaluation.md) | The checker computes only what it needs | built, stages 1A, 1B: `crates/elab/src/bind.rs`; option (b) shelved | SW-8, SW-46, SW-59, SW-79 |
| [let.md](let.md) | `let` that holds proofs and data, with a value the checker sees | built | SW-124 |
| [stack-safe-evaluation.md](stack-safe-evaluation.md) | The evaluator as a machine, so evaluation doesn't overflow the stack | built, steps 0-4: `crates/core/src/machine.rs` | SW-83, SW-82 |
| [deep-input.md](deep-input.md) | One policy for recursion that grows with the input | proposed: D2750-D2754 (D2751 taken up by long-chains.md) | SW-1956, SW-1874, SW-1892, SW-1895, SW-1965-SW-1970 |
| [long-chains.md](long-chains.md) | Long list literals, operator chains and blocks without recursion | proposed: D2840-D2844 | SW-1993, SW-2018-SW-2021 |
| [opaque-definitions.md](opaque-definitions.md) | `opaque def`, and unfolding it on request | built, lanes 1-4: `crates/elab/src/opaque.rs`; status line says D1263, D1264, D1267 open | SW-525-SW-527 |
| [erase-proof-data.md](erase-proof-data.md) | Ghost fields: erase data only proofs use | proposed: D2900-D2905 | SW-2028, SW-2041-SW-2045 |
| [well-founded-recursion.md](well-founded-recursion.md) | `decreasing n` instead of fuel | in progress: stages 1-3d built (`crates/elab/src/decreasing.rs`); rest of stage 3 open | SW-199, SW-253 |
| [decreasing-with-hypothesis.md](decreasing-with-hypothesis.md) | A decrease proof that can use what a `match` or `if` just learned | proposed (design item for SW-199) | SW-2013, SW-2029-SW-2032 |
| [proof-check-speed.md](proof-check-speed.md) | Why AoC 2025 day 2 and day 4 proofs checked slowly | record (led to folded-calls.md) | SW-163, SW-252 |

## Elaborator

| Note | What it's about | Status | Tickets |
|---|---|---|---|
| [elaborator-state.md](elaborator-state.md) | The elaborator's state, split by lifetime | built, steps 0-6c: `crates/elab/src/state/` (stale: D2283-D2287 decided) | SW-1137, SW-1144-SW-1176 |
| [globals-split.md](globals-split.md) | Splitting `Globals` into kernel, facts and machine | built (stale), 8a-8f: `crates/core/src/env.rs`; `Globals` is gone | SW-1174, SW-1186-SW-1191 |
| [postponement.md](postponement.md) | One postponement queue in the elaborator | in progress: stages 1-3, 4.0-4.3, 5, 6, 7 built (`crates/elab/src/queue.rs`); follow-ups open | SW-817, SW-987, SW-988, SW-1010; open SW-929, SW-1008, SW-1009 |
| [postpone-fixed-point.md](postpone-fixed-point.md) | Failed proof searches that wait without hiding the failure | proposed | SW-1014, SW-2063-SW-2065 |
| [bounded-readback.md](bounded-readback.md) | The elaborator looks at goals as written and unfolds only what it needs | in progress: stages 0a, 0b, 1, 1b built; 0c, 1c, 3, 4a-c, 5, 6a, 6b, 7, M, O open | SW-1712, SW-1740, SW-1746-SW-1748, SW-1830-SW-1841 |
| [bounded-readback-remaining.md](bounded-readback-remaining.md) | Plan for bounded read-back's remaining stages | in progress (plan); D2610-D2614 open | SW-1828, SW-1830-SW-1841, SW-1631 |
| [goal-readback.md](goal-readback.md) | A size cap on reading the goal back for `match` and `rewrite` | superseded by bounded-readback.md (D1280 deferred) | SW-556 (still in backlog) |
| [folded-goals.md](folded-goals.md) | Keep definitions folded in goals | superseded (stale) by goal-as-written.md and bounded-readback.md | SW-742, SW-794, SW-1628 |
| [stuck-blockers.md](stuck-blockers.md) | Stuck values record which unknown they wait on | proposed: D2620-D2623 | SW-1845, SW-1842-SW-1844, SW-1865-SW-1868 |
| [match-generalisation-evaluation.md](match-generalisation-evaluation.md) | What to evaluate when generalising a `match` scrutinee | record (survey behind SW-1096, done) | SW-1096 |
| [decision-match-refines-bool-if.md](decision-match-refines-bool-if.md) | A `match` on a decision should refine an `if` on its `Bool` | in progress (stale): D2525-D2527 decided; warning built (`W-MATCH-DECISION-IF`, `crates/elab/src/matching.rs`), option (d3) open | SW-1694, SW-1719, SW-1720 |
| [alias-functions.md](alias-functions.md) | Should a type alias have its own functions? | built: `name_unknown_type`, `crates/elab/src/check.rs:4272` | SW-826, SW-846, SW-858; open SW-859 |
| [extending-types.md](extending-types.md) | Adding functions to another namespace's type | built | SW-825 |
| [dot-receiver.md](dot-receiver.md) | Where `x` goes in `x.f a` (rule E: first) | built: `crates/elab/src/dot.rs` | SW-228 |
| [method-sections.md](method-sections.md) | Passing a method as an argument, `_.isZero` | built (stale), SW-266 | SW-264, SW-266 |
| [interfaces.md](interfaces.md) | Interfaces (type classes), instances and `auto` | built, stages 1-7: `crates/elab/src/interfaces.rs` | SW-4, SW-184 |
| [named-arguments.md](named-arguments.md) | Named arguments and field defaults | built, stages 1-2b: `crates/elab/src/named.rs` (stale: stage 3 is signature-defaults.md, partly built) | SW-390, SW-399-SW-402 |
| [signature-defaults.md](signature-defaults.md) | Default values for function parameters | in progress (stale): stage 1 built (`crates/elab/src/defaults.rs`); 2-3 open | SW-620, SW-614; open SW-622, SW-623 |
| [syntax-node-ids.md](syntax-node-ids.md) | Syntax ids from the parser, so elaborator caches don't key on addresses | proposed: D2577-D2580 | SW-1801, SW-1803 |
| [error-kinds.md](error-kinds.md) | Internal error kinds, so code stops deciding by message text | proposed: D2770-D2773 | SW-1908, SW-1972-SW-1978 |
| [proofs-about-definitions.md](proofs-about-definitions.md) | Proofs about named definitions (parsers as the example) | built: D2341, D2342 | SW-1218, SW-1225-SW-1227, SW-1229; open SW-1228 |
| [compute-once.md](compute-once.md) | Computing a value once: computed record fields, hoisting | proposed: D2880-D2885 | SW-2014, SW-2022-SW-2027, SW-1576, SW-1602 |
| [namespaces.md](namespaces.md) | Namespaces, imports and dot notation | built, stages 0-2: `crates/elab/src/module.rs` | SW-14, SW-21, SW-123, SW-165; open SW-150 |
| [multi-file.md](multi-file.md) | Programs in several files | built, stages 1-2; the rest is unbuilt design | SW-89, SW-106, SW-132, SW-511; open SW-150 |
| [import-aliases.md](import-aliases.md) | `Spec.x` for an imported namespace; `import M (x as y)` | built, stages 1-2 | SW-804 |

## Tactics and proofs

| Note | What it's about | Status | Tickets |
|---|---|---|---|
| [calc-rewrite.md](calc-rewrite.md) | `calc` chains and the `rewrite` term | built: `crates/elab/src/calc.rs`, `crates/elab/src/rewrite.rs` | SW-136, SW-153, SW-162 |
| [rewrite-hypothesis.md](rewrite-hypothesis.md) | `rewrite p at h` | built | SW-209 |
| [rewrite-occurrence.md](rewrite-occurrence.md) | Rewriting one chosen occurrence, `rewrite p within …` | proposed: D2860-D2864 | SW-2011, SW-2033-SW-2035 |
| [goal-as-written.md](goal-as-written.md) | `rewrite` and `match` look at the goal as written first | built, stages 1-4: `crates/elab/src/rewrite/as_written.rs`, `crates/elab/src/matching/as_written.rs`; Q4 reversed by D2542; stage 5 open | SW-706, SW-1627-SW-1630; open SW-1631, SW-1589 |
| [equation-lemmas.md](equation-lemmas.md) | Equation lemmas, and lemmas about a `match` inside a definition | built, stages 1-2; the rest superseded by function-equations.md | SW-194 |
| [function-equations.md](function-equations.md) | Equations for each arm (`f.eqK`) and functional induction (`f.induct`) | built: `crates/elab/src/equations.rs`, `crates/elab/src/derive_induct.rs` | SW-1028, SW-1035, SW-1049, SW-1057, SW-1058, SW-1067 |
| [omega.md](omega.md) | `omega`: linear arithmetic by a checked certificate | built: `crates/elab/src/omega.rs`, `crates/elab/src/std/Omega/` | SW-101, SW-314, SW-315, SW-326 |
| [proof-automation.md](proof-automation.md) | Rewriting under binders, `ring`, and a controlled `simp` | built, stages 0-2 (`crates/elab/src/ring.rs`); `simp` (stage 3) deferred | SW-374; open SW-897, SW-904 |
| [simp.md](simp.md) | Automatic case splitting, and where `simp` fits | built, stage 1 as `cases`: `crates/elab/src/cases.rs` | SW-592 |
| [decide.md](decide.md) | `decide`: check every case of a finite statement | built: `crates/elab/src/derive_finite.rs` (SW-807) | SW-800, SW-807 |
| [bool-and-prop.md](bool-and-prop.md) | Whether a decidable fact lives in `Bool` or `Prop`: tests first, `Decidable` as a `Bool` with proofs, no `propext` | proposed: D3479-D3482 open | SW-2692 |
| [counterexample-search.md](counterexample-search.md) | Search for a counterexample when a proof fails | built, stages 1-2: `crates/elab/src/counterexample/`; stages 3-4 not built | SW-330, SW-436 |
| [proof-reification.md](proof-reification.md) | `match reify`: proofs that look inside a computation | built, R1-R2: `crates/elab/src/reify.rs` | SW-419, SW-420; open SW-660 |
| [tailrec.md](tailrec.md) | A checked `@[tailrec]` attribute | built: `crates/elab/src/tailrec.rs` | SW-1213, SW-1222 |

## Syntax

| Note | What it's about | Status | Tickets |
|---|---|---|---|
| [declaration-syntax.md](declaration-syntax.md) | Lean/Scala-style `def` headers in place of Haskell-style equations | built | (lanes A, B; `c2f9a04a`) |
| [lambda-syntax.md](lambda-syntax.md) | Lambdas without the backslash, `x => e` | built | SW-90, SW-170, SW-176 |
| [anonymous-lambdas.md](anonymous-lambdas.md) | Lambdas that don't name their argument, `(.id == id)` | built | SW-457 |
| [partial-lambdas.md](partial-lambdas.md) | Clause lambdas: `match \| …`, `match some \| …`, `matches \| …` | built | SW-1292, SW-1294, SW-1303, SW-1326 |
| [pattern-guards.md](pattern-guards.md) | Pattern guards, `\| p if c => e`, in every `match` | built | SW-1295, SW-1301 |
| [syntax-conveniences.md](syntax-conveniences.md) | Local definitions, `match`, patterns in `let` and lambdas, tuples | built: `crates/elab/src/patlet.rs`, `crates/elab/src/local.rs` | SW-20, SW-874 |
| [list-spread.md](list-spread.md) | Building lists with `[x, ..xs]` | built | SW-1214, SW-1220 |
| [chained-comparisons.md](chained-comparisons.md) | `low <= x <= high` | built (stale): `comparison_chain`, `crates/syntax/src/parser.rs:3946` | SW-1339, SW-1341, SW-1352 |
| [ranges.md](ranges.md) | Ranges, `a ..< b` and `a ..= b` | in progress (stale): steps 1-3 built (`crates/syntax/src/lexer.rs`, `DotDotLt`); 4-5 open | SW-1356-SW-1359; open SW-1360, SW-1361 |
| [negative-arguments.md](negative-arguments.md) | `f -2` means `f (-2)` | built | SW-840, SW-854, SW-855 |
| [negative-arguments-review.md](negative-arguments-review.md) | Independent review of the note above | record | SW-853 |
| [logic-notation.md](logic-notation.md) | `∈ ∉ → ↔ ∧ ∨ ¬ ≤ ≥ ≠ ∃` and their ASCII forms | built: `crates/elab/src/logic.rs`, `crates/elab/src/membership.rs` | SW-461 |
| [number-patterns.md](number-patterns.md) | Number patterns without `Succ` chains | built: `crates/elab/src/numbers.rs` | SW-75 |
| [fin-literals.md](fin-literals.md) | Checked `Fin` literals | built | SW-384 |
| [brace-syntax-review.md](brace-syntax-review.md) | Braces after a constructor, and record syntax as a whole | built (stale): D2481-D2485 | SW-1613, SW-1632, SW-1633 |
| [record-argument-braces.md](record-argument-braces.md) | A record literal as a constructor's argument (D1370) | superseded by brace-syntax-review.md | SW-606, SW-1322 |
| [attributes.md](attributes.md) | Attributes `@[…]`, starting with the JavaScript wire format | built, stages 1, 2, 2b: `crates/elab/src/attributes.rs` | SW-341 |
| [direct-style-grammars.md](direct-style-grammars.md) | Sequence expressions `(a; b)` and `Parse.before` | built | SW-888, SW-889; open SW-887 |
| [private-helpers.md](private-helpers.md) | Hiding std's internal helpers, `@[internal]` | proposed | SW-2008, SW-2037-SW-2040 |
| [entry-points.md](entry-points.md) | How a program declares its entry point: `@[entry]`, `main` checked where defined, or both | proposed: D3452-D3454 (recommends `main` by name, checked at definition) | SW-2550; SW-2549 |

## Effects

| Note | What it's about | Status | Tickets |
|---|---|---|---|
| [abilities.md](abilities.md) | Abilities, rows and handlers | built: `crates/elab/src/effects.rs` | SW-72, SW-74, SW-91 |
| [partial.md](partial.md) | `Partial`: code that may not finish, visible in types | built, stage 1: `crates/elab/src/partial.rs`; the rest someday/maybe | SW-71, SW-122 |
| [partial-stage-2.md](partial-stage-2.md) | `main` may be `{IO, Fail, Partial}` | built, stage 2 | SW-446, SW-448 |
| [partial-stage-3.md](partial-stage-3.md) | Partial callbacks through the one `List.map` | in progress: lane 3a built; 3b-3e open | open SW-467, SW-469, SW-470 |
| [partial-handlers.md](partial-handlers.md) | Handlers around partial code (`foldD`) | built, lanes A-D: `crates/core/src/step.rs`, `crates/rt/src/run.rs` | (lanes A-D) |
| [partial-tests.md](partial-tests.md) | Tests that run partial code with a tick limit | built | SW-449, SW-452 |
| [errors.md](errors.md) | Errors with messages: `Fail` and `Result` | built (stale): `crates/elab/src/std/Fail/`, `crates/elab/src/std/Result/` | SW-367, SW-419 |
| [effect-polymorphism.md](effect-polymorphism.md) | One function for pure and effectful callbacks (`{e}` rows) | built, stages 0-3; stage 4 is effect-runtime.md | SW-369 |
| [effectful-map.md](effectful-map.md) | Two experiments with an effect-polymorphic `List.map` | parked: neither kept; superseded by effect-polymorphism.md | SW-396 |
| [effect-polymorphic-list.md](effect-polymorphic-list.md) | The other list functions, effect-polymorphic like `map` | built (stale), lane 1 (`cd8863d99`); D1242, D1243 (lanes 2-3) not visible on the board | SW-553 |
| [effect-runtime.md](effect-runtime.md) | A linear-time, stack-safe runtime for effectful code | built, 4a-4f: `crates/rt/src/run.rs`; option B open | SW-396, SW-551; open SW-555 |
| [effect-runtime-review.md](effect-runtime-review.md) | Self-review of effect-runtime.md for an outside reviewer | record | (D1162) |
| [effect-runtime-external-review.md](effect-runtime-external-review.md) | External review of the above | record | (D1162) |
| [effect-rows-external-review.md](effect-rows-external-review.md) | External review of effect-polymorphism's row design | record | (D1142) |
| [computation-values.md](computation-values.md) | Survey: may `{Fail} A` be written as a value type? (D1141) | superseded: D1141 (d) chose arrows only and proof-only reification (proof-reification.md) | — |
| [computation-values-external-review.md](computation-values-external-review.md) | External review of the survey | record | — |
| [delayed-translate.md](delayed-translate.md) | Moving a closed computation into an open row (`widenIn`) | built (stale): `Effect.widenIn`, `crates/elab/src/std/core/Effect.sw:210` | SW-424 |
| [tail-resumptive-handlers.md](tail-resumptive-handlers.md) | Handlers that resume in tail position run without capturing | in progress (stale): steps C and A done (D2360); B open | SW-737, SW-790, SW-861, SW-738; open SW-791 |
| [each-ability.md](each-ability.md) | `Each`: list comprehensions as an ability | built: `crates/elab/src/std/Each/Each.sw` | SW-296 |
| [row-settling-order.md](row-settling-order.md) | When a call's effect row may be settled as empty | proposed (analysis) | SW-1926, SW-1581, SW-1994 |
| [terminal-io.md](terminal-io.md) | Terminal control as a library ability | built, lanes 1, 2, 4: `crates/elab/src/std/Terminal/`; D1258 still open | SW-483, SW-495-SW-497 |
| [text-and-io.md](text-and-io.md) | `Char`, `Text`, `IO` and `main` | built (stale: step 7's checking-evaluator stage is built too) | SW-57, SW-68 |

## Runtime and backends

| Note | What it's about | Status | Tickets |
|---|---|---|---|
| [fast-runtime.md](fast-runtime.md) | A fast runtime: erased IR and bytecode machine | built, stages 1-4: `crates/rt/` | SW-230-SW-233 |
| [native-compilation.md](native-compilation.md) | Running as machine code (Cranelift) | built, N1-N4: `crates/native/` | (D1250-D1253) |
| [native-only.md](native-only.md) | Native executables with no machine inside | built, mostly; IO and effect representation open | SW-559-SW-561; open SW-562, SW-593 |
| [apply-fast-paths.md](apply-fast-paths.md) | Native `Apply` of the effect runtime's own function values without a failed cache lookup or an argument `Vec` | built (A, B, D; C dropped as not worth it) | SW-2336 |
| [standalone-executables.md](standalone-executables.md) | `stitchwort build`: standalone executables | built: `crates/standalone/` | SW-528 |
| [native-numbers.md](native-numbers.md) | `Nat` arithmetic as natives | built | — |
| [compact-text.md](compact-text.md) | Compact `Text` in JS and in the checking evaluator | built (stale), all three stages | SW-36, SW-52, SW-58 |
| [js-source-maps.md](js-source-maps.md) | Source maps for generated JavaScript | built (stale): `crates/js/src/sourcemap.rs` | SW-361 |
| [backend-trust.md](backend-trust.md) | What the backends trust (one way to make an `Image`) | proposed: D2790, D2791 | SW-1893, SW-1885, SW-1989-SW-1992 |
| [run-profiler.md](run-profiler.md) | A profiler for `stitchwort run` | in progress: stage 1 built (`run --profile`, `crates/cli/src/main.rs`) | SW-1528; open SW-1634 |
| [cell-allocator.md](cell-allocator.md) | Whether cells need an allocator of our own (no: mimalloc, with a per-run cell cache inlined in native code) | proposed: D3413, D3414 | SW-2360 |
| [reuse-across-calls.md](reuse-across-calls.md) | Reusing a cell taken apart in one function where another rebuilds it (a hidden reuse-token argument), against reshaping std's `Map.Tree` | proposed: questions in §7 | SW-2384, SW-2383, SW-1812 |
| [nat-shaped-types.md](nat-shaped-types.md) | Types shaped like `Nat` after erasure (`Fin` first) as machine numbers at run time, with pinned identity natives; compared with Idris 2, Lean, Agda, Rocq, F* | proposed: questions in §9; §1.1/§2.3 wrong about `Fin`'s `n` (corrected in place) | SW-2397, SW-2398 |
| [erase-determined-fields.md](erase-determined-fields.md) | Don't store constructor fields the type's indices determine (`Fin`'s and `Vec`'s `n`) on the fast runtimes, rebuilding them at a match from the kernel's own unification; reverses half of D141; compared with Brady et al., Agda, Idris 1 and 2, Lean, Rocq | proposed: questions in §9 | SW-2406 |
| [compact-values.md](compact-values.md) | How big a run-time value should be: an 8-byte cell header, two-word values (16 bytes), or one-word tagged values with unboxed typed fields, compared with Lean, Koka, OCaml, GHC, Swift and others; most of the native/Lean gap is instructions, not memory stalls; a staged measurement plan with go/no-go points before any refactor | proposed: V0–V4 measured; V4 (§7) predicts E just under its gate, decision in §7.6 | SW-2324, SW-2429 |
| [constant-hoisting.md](constant-hoisting.md) | Expressions that use no variables (`"mul(".toList`, `Parse.text "mul("`) computed once at first use and kept if small: literal folds, pooled static data, floating closed expressions out of bodies after inlining | proposed: D3438, D3439 (includes SW-2493 §7.4, capture-free closures built once) | SW-2497 |
| [effect-runtime-allocation.md](effect-runtime-allocation.md) | Fewer objects built by the effect runtime (about 14 per operation on the parsers): one-object resumptions, the loop reusing the cells it takes apart, a perform's `bind` folded into its `Call`, no resumption for a fused state handler that can't use `k`; local changes, not operations in place (D3430) | proposed: staged plan in §4, questions in §5 | SW-2444 |
| [compiled-handler-dispatch.md](compiled-handler-dispatch.md) | A handler's step lowered to one dispatch closure (switch on the operation's tag, clauses inlined) instead of `handlePlus` and `%elim` partial applications that copy every clause per operation; a lowering rewrite, no hash changes; complements operations in place | proposed: staged plan in §7, questions in §8 | SW-2498 |
| [borrow-inference.md](borrow-inference.md) | Borrowed parameters inferred Lean-style (read-only, never stored, returned or reused), so walks like `Map.get` over a live map stop counting each node; tail calls and step/frame counts unchanged (owned copies for value uses), the machine checks borrows instead of exploiting them, native code gets the speed-up | proposed: D3440-D3442, staged plan in §6 (B0 measures first) | SW-2518 |

## Standard library and data types

| Note | What it's about | Status | Tickets |
|---|---|---|---|
| [std-library.md](std-library.md) | Splitting the prelude into a standard library | built, stages 1-2: `crates/elab/src/library.rs` | SW-148, SW-151, SW-165 |
| [prelude-slim.md](prelude-slim.md) | A slim prelude; everything else behind imports | built, stages 1-3 | SW-213, SW-225, SW-241 |
| [std-as-data.md](std-as-data.md) | std found beside the binary, not embedded | built: `crates/elab/src/std_dir.rs` | SW-1136 |
| [integers.md](integers.md) | `Int` | built: `crates/elab/src/std/Int/` | SW-3, SW-15, SW-16 |
| [float.md](float.md) | `Float` as a JavaScript number | built, stages 1a, 1b | SW-358, SW-360, SW-625 |
| [float-laws.md](float-laws.md) | Laws about `Float`'s rounding | in progress: `roundScaled` model built (`crates/elab/src/std/Float/Model.sw`); stages 3-4 open | open SW-638, SW-639 |
| [fin-arithmetic.md](fin-arithmetic.md) | Wrapping arithmetic: `Mod n` beside `Fin n` | built: `crates/elab/src/std/Mod/` | SW-229 |
| [division.md](division.md) | Division on numbers with an unknown part (`Nat.divStep`) | built, stage 1: `crates/elab/src/std/core/Division.sw` | SW-922 |
| [total-division.md](total-division.md) | `/` and `%` with no proof that the divisor isn't 0 | built (stale) | SW-1238, SW-1640, SW-1641 |
| [map-set.md](map-set.md) | `Map` and `Set` as first built | built: `crates/elab/src/std/Map/` | SW-113 |
| [maps.md](maps.md) | Maps and sets for practical use | built | SW-356 |
| [nat-map.md](nat-map.md) | A map keyed by `Nat` (Haskell's `IntMap`)? | proposed: D2595-D2601 | SW-1603, SW-1824-SW-1827 |
| [arrays.md](arrays.md) | A persistent array in std | built (stale): `crates/elab/src/std/Array/Array.sw` | SW-1473, SW-1637-SW-1639; open SW-1671, SW-1678 |
| [non-empty-lists.md](non-empty-lists.md) | `NonEmptyList a`, with `reduce` | built (stale): `crates/elab/src/std/NonEmptyList/` | SW-1337, SW-1343-SW-1346 |
| [microtypes.md](microtypes.md) | `UserId`, `Email` as distinct types over `Text` | built, stages 1-3 | SW-380 |
| [variant-fields.md](variant-fields.md) | Named fields on variants: patterns, shared access, update | built: `crates/elab/src/update_lemmas.rs`; D603, D604 open | SW-340, SW-381, SW-382, SW-581 |
| [parser-combinators.md](parser-combinators.md) | `Std.Parse`, a parser library for puzzle input | built, stage 1: `crates/elab/src/std/Parse/Parse.sw` | SW-861, SW-1107 |
| [total-parsers.md](total-parsers.md) | Parsers that are total by type | parked (D1710: not now) | SW-884, SW-891 |
| [aoc-geometry.md](aoc-geometry.md) | A 2D geometry library for `Aoc.Common` | in progress (stale): stage 1 built (`aoc/src/Aoc/Common/Plane.sw`) | SW-1617, SW-1484; open SW-1474, SW-1475, SW-1482, SW-1587, SW-1588, SW-1592 |

## Tooling and the editor

| Note | What it's about | Status | Tickets |
|---|---|---|---|
| [code-navigation.md](code-navigation.md) | A code navigation index (`check --index`) | built: `crates/elab/src/nav.rs` | SW-201, SW-211, SW-914 |
| [language-server.md](language-server.md) | A language server for `.sw` | built, stages 0-1: `crates/lsp/` | SW-31, SW-274, SW-275, SW-282; open SW-1141 |
| [lsp-goal-holes.md](lsp-goal-holes.md) | Goal holes in the editor (server stage 2) | built, 2a-2d | SW-376 |
| [lsp-failure-policy.md](lsp-failure-policy.md) | How the language server handles panics and failures | in progress: stage 1 built (SW-1820); D2741-D2744 open | SW-1955, SW-1820; open SW-1948, SW-1979-SW-1981, SW-2067 |
| [parse-recovery.md](parse-recovery.md) | Recovering from syntax errors while someone types | superseded in part by syntax-error-recovery.md (D2780-D2785; nothing built) | SW-1917, SW-1873, SW-1982-SW-1986 |
| [syntax-error-recovery.md](syntax-error-recovery.md) | Working through a broken declaration (D3563): recovery points, error nodes, gaps the checker skips without cascades | proposed: D3580 decided (Fable's split), D3581 open | SW-3161 |
| [tests-with-errors.md](tests-with-errors.md) | Checking and running tests when a project has errors or open goals: status per declaration, importers of a broken namespace | proposed: decisions D-a to D-f open | SW-2938; builds on SW-2909, SW-2932 |
| [editor-and-playground-roadmap.md](editor-and-playground-roadmap.md) | Roadmap for VS Code and the playground | built: every ticket done | SW-1111, SW-1116-SW-1121, SW-1489 |
| [playground-editor.md](playground-editor.md) | CodeMirror 6 in the playground | built: `web/editor/src/editor-entry.js` | SW-1118, SW-1375-SW-1378 |
| [playground-live-keys.md](playground-live-keys.md) | Live keys and a terminal pane in the playground | built | SW-520, SW-521 |
| [playground-projects.md](playground-projects.md) | Projects (the AoC tree) in the playground; GitHub Pages | built | SW-133, SW-173 |
| [formatter.md](formatter.md) | `stitchwort fmt` | built: `crates/fmt/` | SW-366 |
| [documentation.md](documentation.md) | Doc comments, `stitchwort doc`, coverage, checked links | built, stages 1-3: `crates/elab/src/doc_links.rs` | SW-1013, SW-1018, SW-1019, SW-1024, SW-1025, SW-1042, SW-1044 |
| [search.md](search.md) | `stitchwort search`: lemma search by type | built, stages 1-3: `crates/elab/src/search.rs` | SW-915, SW-989, SW-993 |
| [check-cache.md](check-cache.md) | A cache of checked declarations across runs | built, stages 1-3: `crates/driver/src/check_cache.rs` | SW-239, SW-240, SW-245, SW-880 |
| [check-cache-key.md](check-cache-key.md) | Check caches that survive a compiler change | parked: D2560 yes, no narrower key; SW-1741 fixed the cause instead | SW-1753, SW-1745, SW-1741 |
| [check-cache-trust.md](check-cache-trust.md) | What the check cache trusts when it skips the kernel | proposed: D2800-D2802, D2680 | SW-1971, SW-1919, SW-1925, SW-1995, SW-1996 |

## Tests and process

| Note | What it's about | Status | Tickets |
|---|---|---|---|
| [fewer-test-binaries.md](fewer-test-binaries.md) | One integration-test binary per crate | built (stale): `crates/*/tests/it/` | SW-1736, SW-1780 |
| [test-cache-key.md](test-cache-key.md) | A finer test-cache key | built (stale): `crates/driver/src/fingerprint.rs` | SW-1328-SW-1330 |
| [kernel-merge-gate.md](kernel-merge-gate.md) | A merge gate for kernel and core-language lanes | proposed: D2760-D2763 | SW-1957, SW-1963; open SW-1958-SW-1962, SW-1964 |
| [mutation-check.md](mutation-check.md) | Break the program; some proof or test must notice | proposed: D2920-D2924 | SW-1064, SW-2056-SW-2062 |
| [split-elab.md](split-elab.md) | Splitting the `elab` crate for build speed | in progress: SW-1776 in review | SW-1737, SW-1777, SW-1776 |
| [proof-irrelevance-review.md](proof-irrelevance-review.md) | Independent review of proof-irrelevance.md, draft 4 | record | SW-1268 |

## Counts

| Status | Notes |
|---|---|
| built | 102 |
| in progress | 16 |
| proposed | 19 |
| superseded | 4 |
| parked | 4 |
| record | 8 |
| **total** | **153** |

"Built" includes notes where only the decided part is built and the rest
was left as someday/maybe (partial.md, records.md, multi-file.md). Of the
102, 20 have a status line that still says otherwise (marked "stale").

## Stale claims

Places where a note says something the code or board no longer bears out.
Line numbers are the note's; code locations are at `a0cea6157`.

**Status lines that say "not built" about built work.** These mislead
most, since the status line is all a reader looks at.

1. [arrays.md](arrays.md):5 "Nothing is built": `Std.Array` is in
   `crates/elab/src/std/Array/Array.sw` (SW-1637-SW-1639).
2. [non-empty-lists.md](non-empty-lists.md):5 "No implementation yet":
   `crates/elab/src/std/NonEmptyList/` (SW-1343-SW-1346).
3. [chained-comparisons.md](chained-comparisons.md):3 "No implementation
   yet": `crates/syntax/src/parser.rs:3946` (`comparison_chain`, SW-1341).
4. [ranges.md](ranges.md):3 "No implementation yet": the `..<` token is
   `DotDotLt`, `crates/syntax/src/lexer.rs:148`; steps 1-3 done.
5. [total-division.md](total-division.md):5 "Nothing is built": SW-1640
   made `/` and `%` total.
6. [brace-syntax-review.md](brace-syntax-review.md):5 "Nothing is built":
   SW-1632 and the sweep SW-1633 are done.
7. [test-cache-key.md](test-cache-key.md):4 "Nothing is built": SW-1329 and
   SW-1330 did it; `crates/driver/src/fingerprint.rs:10`.
8. [signature-defaults.md](signature-defaults.md):4 "Nothing here is
   built": stage 1 is `crates/elab/src/defaults.rs` (SW-620).
   [named-arguments.md](named-arguments.md):6 repeats it ("Stage 3
   (signature defaults) not built").
9. [globals-split.md](globals-split.md):3 "Nothing here is built": 8a-8f
   are merged and `Globals` was deleted (`2bd54e185`).
10. [proof-irrelevance.md](proof-irrelevance.md):3 "Design only: nothing is
    built": stages 1 and 2 are done (SW-93, SW-1429), and
    `crates/core/src/value.rs:2110` cites the note's §7.10.
    [proof-automation.md](proof-automation.md):10 still calls it "not built".
11. [effect-polymorphic-list.md](effect-polymorphic-list.md):3 "Nothing is
    built": lane 1 (`cd8863d99`) made fourteen list functions take `{e}`
    callbacks.
12. [method-sections.md](method-sections.md):3 "No code has changed": built
    in SW-266 (its own "As built" section is at the end).
13. [folded-calls.md](folded-calls.md):3-4 "nothing here is implemented":
    stages 1-4 are built (its own "As built" sections).
14. [fast-runtime.md](fast-runtime.md):3 "nothing here changes the
    compiler": `crates/rt/` is the result.
15. [js-source-maps.md](js-source-maps.md):3 "exploration, with a working
    prototype": merged as SW-361; `crates/js/src/sourcemap.rs`.
16. [delayed-translate.md](delayed-translate.md):3 "stopped for review. A
    prototype … is on branch `sw-424-delayed-translate`": the PROTOTYPE
    commit `626d63d56` is an ancestor of `main`, and `Effect.widenIn` is
    live (`crates/elab/src/std/core/Effect.sw:210`,
    `crates/elab/src/effects.rs:1326`). Worth checking that this was meant.
17. [literal-match-facts.md](literal-match-facts.md):3 "built on a branch …
    waits for Matt's review before merging": merged in `91eead3c9`;
    `crates/core/src/value.rs:157`.
18. [fewer-test-binaries.md](fewer-test-binaries.md):3-4 "Rolling out the
    other crates waits for Matt's go-ahead": rolled out; `crates/core`,
    `fmt`, `lsp`, `native`, `rt` and `syntax` each have `tests/it/`.
19. [aoc-geometry.md](aoc-geometry.md):3 (draft only): stage 1 is
    `aoc/src/Aoc/Common/Plane.sw` (SW-1484).

**Decisions listed as open that are decided.**

20. [elaborator-state.md](elaborator-state.md):5 "waits for Matt's
    decisions there (§8, D2283-D2287)": decided 3 Nov (SW-1169) and built
    as 6a-6c.
21. [decision-match-refines-bool-if.md](decision-match-refines-bool-if.md):4
    "Nothing built. Open decisions: D2525 to D2527": decided 6 Nov; option
    (a) built as `W-MATCH-DECISION-IF` (`crates/elab/src/matching.rs`,
    SW-1719).
22. [folded-goals.md](folded-goals.md):3 and
    [tail-resumptive-handlers.md](tail-resumptive-handlers.md):3 "proposed,
    awaiting Matt's review": folded goals went into goal-as-written.md
    (SW-1628); the handler note was closed by D2360 (steps C and A done,
    B on SW-791).

**Later stages described as still to come.**

23. [compact-text.md](compact-text.md):3 "B2 (stage 3) awaits a further
    decision" and [text-and-io.md](text-and-io.md):3 "the checking
    evaluator's stages are later": SW-36 built B2.
24. [errors.md](errors.md):5 "stage 2 is next": SW-367 says all stages done.

**Code paths that moved.** Many notes cite files that no longer exist
under those names (85 notes cite at least one missing path; some are files
a proposal plans to add). The systematic moves:

25. Integration tests: `crates/driver/tests/*.rs` and `crates/cli/tests/*.rs`
    (e.g. `check_cache.rs`, `extract.rs`, `partial.rs`, `hash_stability.rs`)
    are now grouped into one binary per crate (`crates/driver/tests/elaboration/`,
    `crates/cli/tests/extraction/`, `crates/*/tests/it/`). Cited in about 50
    notes.
26. `crates/cli/src/lsp.rs` is now the `crates/lsp/` crate
    (counterexample-search.md:211, formatter.md:317, documentation.md:159,
    lsp-goal-holes.md:75, postponement.md:997, signature-defaults.md:610,
    playground-editor.md:291).
27. `crates/elab/src/prelude.sw` and `std/core.sw` are now
    `crates/elab/src/std/core/*.sw` (calc-rewrite.md:234, compact-text.md:178,
    integers.md:1489, let.md:173, namespaces.md:241, partial.md:70,
    std-library.md:72, fin-arithmetic.md:27, prelude-slim.md:63,
    interfaces.md:311, well-founded-recursion.md:95).
28. [playground-editor.md](playground-editor.md):145, :454, :764 cite
    `web/proto/…`, which is gone; the editor is `web/editor/`.

**Board out of step with a note.**

29. [record-eta.md](record-eta.md):3 says stages 1 and 1b are merged, but
    SW-1642 is still `doing`.
30. [goal-readback.md](goal-readback.md)'s option (d), SW-556, is still in
    the backlog, although bounded-readback.md replaced the approach.

## Notes to merge or archive

- **Reviews and records that belong in `docs/reviews/`**:
  effect-runtime-review.md, effect-runtime-external-review.md,
  effect-rows-external-review.md, computation-values-external-review.md,
  negative-arguments-review.md, proof-irrelevance-review.md. Each is linked
  from one or two places (effect-runtime-review.md from seven).
- **Superseded or parked, to archive**: effectful-map.md,
  computation-values.md, folded-goals.md, goal-readback.md,
  record-argument-braces.md, proof-check-speed.md,
  match-generalisation-evaluation.md, check-cache-key.md.
- **Merge into their parent**: map-set.md into maps.md;
  kernel-admission.md into mutual-recursion.md; bounded-readback-remaining.md
  and record-eta-remaining.md into their parents once those stages finish.
- **One status line for a family**: the five `Partial` notes (partial.md,
  partial-stage-2.md, partial-stage-3.md, partial-handlers.md,
  partial-tests.md) would read better with partial.md's status line pointing
  at the others; only partial-stage-3.md has open work. (partial-lambdas.md,
  despite its name, is about clause lambdas.)
- **Keep**: glued-closed-types.md and total-parsers.md (parked, with
  research worth keeping, and linked from live notes).

Moving a note breaks links: the code alone has about 1,370 references to
`docs/proposals/`, so an archive is best limited to the notes above, which
have few.
