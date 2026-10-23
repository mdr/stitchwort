# Design session: equality of maps (and other types whose natural equality is coarser than their representation)

**Status:** draft 3, signed off after two external reviews; implementation starts with stage 1
(kernel quotients, [§14.1](#141-stages)). 23 October 2026. Draft 1 (a state-of-the-art audit and
option analysis) had one external review, which kept option E (Lean-style quotients) as the
preferred direction on conditions; draft 2 adopted it (D786) and turned E into a precise kernel
proposal; the second review found no logical contradiction in the five rules and asked for a
focused edit before a kernel prototype, which this draft makes, applying every point (D920; no
third review). Stage 0 (D771) is built; its results are the appendix
[Stage 0 results](#stage-0-results) and are folded into the operative sections (§4.3, §8.1, §12).
Every decision is final ([§16](#16-decisions)): D770–D779 keep their numbers, D785 and D786 are
Matt's, D860–D870 are draft 2's, and draft 3 adds D921–D925. Written against commit `0805af8a`
(draft 2 was written against `1786944e`; line references from draft 2 that moved are updated where
draft 3 relies on them).

It responds to [maps.md](maps.md) draft 1 (D740–D749), whose recommendation for equality, a
canonical *meaning* plus a trusted swap-in of the tree at run time, Matt doesn't want.

Labels: **[checked]** read in the Stitchwort source at the `file:line` given; **[run]** run while
writing this, with the release build of `main` (`target/release/stitchwort`, built 23 October
2026; draft 3's runs used the build of 14:07 that day), on the snippet shown; **[cited]** read in the primary source linked (fetched 23 October
2026; for Lean and Mathlib, the `master` branch on that date); **[cited by the review]** stated by
the reviewer with a source, not re-read here; **[inferred]** my reasoning from checked or cited
facts; **[unverified]** believed, not confirmed.

## Response to review (round 2)

The second review judged draft 2 close enough for a kernel prototype after a focused edit. It found
no new logical contradiction in the five rules, judged the stage-0 work to resolve the cached-size
concern, accepted the recursive-type refusal and the projection point (draft 2's disagreement 1),
and judged the narrow constant-motive `J` rule locally sound. Every point is applied (D920).
There is no disagreement. One finding goes further than the review: its runtime concern about
erased representative arguments is a **real, pre-existing bug** in the Rust runtime and JS, with
or without quotients ([run], §7.4.3), so stage 1 fixes it first (D922).

| Review point | Change in draft 3 |
|---|---|
| §1.1 Lift erasure must distinguish data, proof (`B : Prop`) and proposition/type (`B := Prop` or `Type j`) results; §7.1's example was `B := Prop`, not `B : Prop`; a proof-valued `f` is itself a proof | §7.4 rewritten: a three-row table by result; a lift with an erased result is erased whole, as the kernel records on the checked term (D921); §7.1's example relabelled and a `B : Prop` example added; test A5 (inline proof-valued lift consumed by `J`) |
| §1.2 Representatives can be types (carrier `Type 0`); lowering must use the original function's type; `mk a` must respect `a`'s erasure | §7.4.2: the lift lowers as the core application `f q` through the existing type-directed application path (relevance from `f`'s type, never from `q`'s); `mk a` lowers as `a` does. Checked against `crates/rt/src/lower.rs` and `crates/js/src/lib.rs`: saturated calls of a definition are right, but **a definition with erased parameters used as a function value is wrong today in both backends** ([run]: `app seven` panics in `rt`, throws in JS, gives 7 in the reference), D922. Test A7: `answer` is 7 in every runner, with `f` a definition, a lambda and a variable |
| §1.3 "Closed quotients reach `mk`" is an intended invariant with premises; state it separately for the reference evaluator and Rust/JS | §7.4.5: stated as an invariant with its four premises, per runner, tested by observable results |
| §2 "A closed proof of `x = y` is `refl` or built from `Quot.sound`" is false (opaque `Quot.ind`); state the erasure contract directly; ind-only `J` test | §7.4.4 and §9.4 state the review's contract directly; test A6 (ind-only, no `sound`): stuck in the kernel, `0` when run |
| §2 An empty axiom report doesn't imply kernel canonicity; the traversal must find inline `Quot.sound` term formers | §10, D864 and D925: the report lists foundational dependencies only; it scans every checked body, theorems and proof arguments included, recognising `Term::Quot(Sound)` nodes; test A9 |
| §2 "Equality computes on closed maps" overpromises (`Map.singleton 0 n` with a stuck `n`) | §9.2: lifted operations reduce on quotient constructors; complete kernel evaluation also needs the keys, values and callbacks to reduce |
| §3 Shared premises; every check explicit; `Quot.mk a ≡ Quot.mk b` only at the same quotient type; hand-built malformed `mk`/`sound`; relation-mismatch test | §7.1: shared premises once, then the per-form rules and a numbered list of the checks every form gets (C1–C6); §7.2 qualified; R11 (relation mismatch) and R14 (malformed hand-built forms) |
| §3 The Type-only carrier rationale was too strong | §7.1: an initial-scope choice; `P : Prop` is excluded, the universe `Prop` (which is in `Type 0`) is admitted |
| §3 Term formers don't make the consequences automatic: every traversal still needs the new form | §7.7: the traversal list, by function, from the source |
| §4 `Quot.funext` covers data-valued functions only; universe levels without polymorphism | §8.7: `Quot.funext` is for (dependent) data-valued functions at `Type 0`; `Quot.funextProp` via `ProofBox`, given as a typed sketch, checked in stage 1 (A2); levels and other instances (D923) |
| §5 Folding lift definitions mustn't change conversion | §7.2: the condition, and test A8 (`rfl: observe q = Quot.lift f respects q` on an open `q`; funext through named helpers) |
| §5 Constant-motive `J` locally sound; keep separate | §9.3 and D924: a separate later proposal, with the review's four conditions |
| §5 A future dependent eliminator's beta rule is propositional | §7.1 |
| §6 R4 is an elaborator policy test; add its positive counterpart | §7.6: R4 marked elaborator-only (the only R test without a kernel judgment); A10: with a lawful `DecEq Q`, `Box (Quot.mk False) == Box (Quot.mk True)` is `True` |
| §6 Eight targeted tests | R11–R14 and A5–A8 (§7.6, §14.3); the axiom-report test is A9 |
| §7 Integrate stage 0: `Map.Raw = { tree, ordered, sized }`; §4.3, §12, D865, stages, risks; forged example is pre-stage-0; §11.2's advice; `toRaw` cost; balance assumption | §8.1, §4.3, §12.1 (example marked pre-stage-0), §11.2 (an id-keyed table, or a tree and a forest defined together), §12.2 (`Raw.fromList (toList m)` is O(n log n · c_k)), §13.3 (balance stated directly), D865, §14 |
| §8 D866 unboxing is optional and separate, with its own checks | §13.1 and D866: not a prerequisite, its own checklist; the prototype and stage 2 use the extra wrapper |

## Response to review (round 1, draft 2)

(Kept as written for draft 2. Where round 2 changed a point, the table above and the body win.)

The review kept E, preserved `==` as `DecEq`, approved stage 0, and asked for a precise kernel
specification, an explicit recursive-type policy, a stated computation contract and a complete
representative invariant before stage 1. Every point is adopted. Two disagreements, both small,
are at the end of the table.

| Review point | Change in draft 2 |
|---|---|
| §1 The direct `toList` argument is simpler and stronger than the generic decidable-relation one | Now central ([§8.2](#82-the-central-lemma-equality-is-equality-of-tolist)): `toList (mk a) ≡ Raw.toList a` by computation; `congrArg toList` one way, `Quot.sound` the other; `Map.eqIffToListEq` and `Map.toListInjective` for **any** value type. The generic argument stays as a quotient-library lemma (§8.6) |
| §1 `DecEq` by deciding list equality, quotient reasoning only in proof payloads | §8.3: the branch is chosen by `List` equality; `Decidable.toBool` computes even though the proofs use `Quot.sound` |
| §1 `Ord` lexicographic on `toList`, every law transferred; same ordering parameter on both sides | §8.4, and the requirements table §8.5 |
| §1 `Map.same` needs `[DecEq v]` (else it decides equality of arbitrary values) | §4.1 and option B corrected |
| §2 Exact typing, universes, reduction, erasure and forbidden behaviours before choosing constants or term formers | New [§7](#7-the-kernel-specification): full rules, then the choice (D860: one term-former family, level-generic like `Eq`/`J`) |
| §2 `Quot.ind` must not compute: a computing one proves propositional proof irrelevance | §7.3 gives the proof and the rule (D861) |
| §2 `Quot.mk` must never get constructor injectivity, no-confusion, matching, index decomposition, derived equality or a projection | §7.6: each forbidden behaviour, why the design excludes it, and a kernel rejection test for it; the `Bool`-by-`True` quotient is the canonical test |
| §3 Recursive maps are a substantial unresolved feature; Lean rejects nested occurrences through `Quot` | New [§11](#11-recursive-types-through-a-quotient-d785): the first version rejects them (D785, D870), with a diagnostic; why positivity alone can't fix it; the later route. Checked: today's `Map` already can't nest ([run]), so this is no regression |
| §4 Check the complete raw invariant: ordering vs cached metadata vs balance | New [§12](#12-the-representative-invariant-and-the-observation-audit): the three requirements, the observation table, and a [run] counterexample: today a forged map with the same entries reports a different `size` (D865) |
| §5 Distinguish termination, kernel reduction to data, and erased execution; don't erase `J` in the kernel | New [§9](#9-the-computation-contract): the contract, its consequences, and the wording changes to DESIGN.md, core.md and `erase.rs` (D863). Also found: under erasure `Quot.sound` must evaluate to the placeholder, or `J` on it would be stuck at run time (D862) |
| §5 D772: an accepted axiom, allowed in exports, visible in reports | [§10](#10-axiom-accounting-d772): adopted; "assumption-free" redefined; no assumption report exists today, so stage 1 adds a small axiom report (D864) |
| §6 "Zero overhead" must be qualified; check the wrapper record | [§13](#13-run-time-representation-and-performance): `Quot` erases for free, but single-field records are boxed today in both the Rust runtime and JS ([checked]), so `Map = { raw: … }` would add a box per map. D866 proposes unboxing records with one run-time field |
| §6 Codec recognition of the revised `Map`; complexity with operation names; maps as outer keys; semantic vs content hashing | §13.2–§13.5 |
| §7 A doesn't compose; C doesn't inherently exclude custom orderings; narrow the lower bound to size-unique representations; Appel–Leroy figures; canonical proof fields don't give `rfl` | §5 options A and C, §3.7, §5.1, all corrected |
| §8 Decision recommendations and the eight prototype properties | §16 adopts the recommendations; the eight properties are the gate between stage 1 and stage 2 ([§14.2](#142-the-gate-before-stage-2-the-reviews-eight-properties)) |
| *Disagreement 1.* The review lists "no unrestricted projection" as something to forbid | Under D860 there is nothing to forbid: `Quot` has no projection or eliminator besides `lift` and `ind`. The danger is only in how the library is written (a public `Map.Raw` field, an exposing `toRaw`), so it's an API-audit item (§12.2), plus a rejection test that a `case` on a quotient is refused (R2) |
| *Disagreement 2.* The review suggests the J/transport limitation needs no kernel mitigation | Agreed for now, but one narrow rule (a `J` whose motive mentions neither the endpoint nor the proof reduces to its base) is sound and would unstick the review's own example. It is not proposed; it's a question for round 2 (§15 Q6; answered: a separate later proposal, D924) |

## 0. Summary

**The question.** In Stitchwort, `==` is decidable *propositional* equality: `a == b` is `True`
exactly when `a = b` can be proved. A `Map` is a balanced search tree, and the same key–value pairs
inserted in different orders give different trees. So the equality a programmer expects ("same
pairs") is not `=`, and `Map` has no `==` at all. Records containing maps can't derive `==`, and a
real TypeScript port hit exactly that.

**What other languages do.** Four families:

1. **A Boolean `==` that is not tied to `=`**, with a separate relation for proofs: Lean's `BEq` on
   `HashMap`/`TreeMap` (with `Equiv` and `beq_iff_equiv`), Haskell, Idris 2, Scala.
2. **A setoid**: keep `=` structural, prove things up to an equivalence, rewrite with
   `Proper` morphisms: Rocq's FMaps/MMaps, Agda's standard library.
3. **A quotient** (or function extensionality) makes `=` itself mean "same pairs" while a fast tree
   runs underneath: Lean's `ExtTreeMap`/`ExtHashMap` and Mathlib's `Finmap`, Isabelle's `mapping`,
   F\*, Dafny, SPARK's functional maps, cubical Agda.
4. **A canonical representation**: only one value per set of pairs, so `=` is extensional for
   free, with no axiom: CompCert's and std++'s binary tries (Appel and Leroy 2023). This needs keys
   with an injective encoding as bits or symbols. For size-unique search trees there is an
   Ω(n^{1/3}) lower bound (Andersson and Ottmann); it doesn't cover every canonical design.

**Recommendation.** Add **Lean-style quotient types** to the kernel (option E): one family of
term formers (`Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind`, `Quot.sound`) with one computation rule,
`Quot.lift f h (Quot.mk a) ⟶ f a`, and one new axiom, `Quot.sound` ([§7](#7-the-kernel-specification)).
Then make `Map` the quotient of **today's proved weight-balanced tree**, with the invariant stage 0
strengthened (ordered *and* correctly sized), by "same entries in key order".

- It is a functional data structure written and proved in Stitchwort, and `m1 = m2` exactly when
  the maps have the same pairs: `Map.eqIffToListEq: m = n ↔ m.toList = n.toList`, for any value
  type, proved directly from the computation rule and `Quot.sound` (§8.2).
- `==` stays lawful `DecEq` (D777), decided by comparing entry lists; records with maps derive
  `==`; `Ord (Map k v)`, `Set (Set k)` and `rewrite` with `=` work.
- At run time `Quot` costs nothing. The extra record around it costs one box per map; unboxing
  single-field records is a separate, optional optimisation (D866, §13.1).

**What the first version doesn't do, deliberately.** It rejects data types that reach themselves
through a quotient (`type Tree = { children: Map Text Tree }`), with a diagnostic (D785, §11);
today's `Map` can't nest either. And closed terms that transport *data* along a quotient equality,
or along a proof made by `Quot.ind`, can be stuck in the kernel while still running correctly (§9).

**Stages.** 0: `Map.Equiv`, `toList` agreement lemmas, the invariant and API audit (**done**,
D771; the `sized` field). 1: a pre-existing erasure bug fixed (D922), then the kernel rules with
the rejection tests written first, the runtimes, the axiom report, the library lemmas, and a
prototype map that must pass the review's eight properties. 2: migrate `Map` and `Set`
([§14](#14-stages-tests-and-risks)).

## 1. The problem in Stitchwort

### 1.1 What `==` and `=` are

- `interface DecEq (a: Type) = { decide: (x: a) -> (y: a) -> Decidable (x = y) }`
  [checked: `crates/elab/src/std/core/DecEq.sw:11-12`]. `a == b` elaborates to
  `Decidable.toBool d` for a decision procedure `d` of `a = b`, found as for `if h: a = b`
  [checked: `docs/core.md:253`]. So **`==` is `True` exactly when `=` holds**, and lemmas such as
  `Decidable.toBoolSound` turn one into the other
  [checked: `crates/elab/src/std/Decidable/Decidable.sw:10`].
- Deriving: every data type or record declared in a program gets a derived `DecEq` when each data
  field has one. Proof fields are allowed if they are equations in a type with `DecEq`, which any two
  proofs satisfy equally (Hedberg) [checked: `crates/elab/src/derive.rs:9-20`]. Library types are
  skipped and get hand-written instances [checked: `derive.rs:26-27`]. Every record also gets a
  generated `T.ext` lemma: equal fields give equal records (SW-263, D503).
- `Ord` *contains* a `DecEq` and the law `equal: compare x y = Equal -> x = y`, with `flip`,
  `trans` and four laws tying `lessThan`/`lessEq` to `compare`
  [checked: `crates/elab/src/std/core/Ord.sw:23-39`]. So a lawful `Ord` needs a lawful `DecEq`.
- The Float design already settled one equality question: `==` stays the lawful `DecEq` operator on
  `Float`, and JS's `===` gets its own name (`Float.ieeeEq`). The reason given was that
  Stitchwort's operator class "isn't lawless", unlike Lean's (D683, flipped after review)
  [checked: `docs/proposals/float.md:65`, `:112-115`, `:144-147`].

### 1.2 What the kernel has

| Feature | Present? | Evidence |
|---|---|---|
| Built-in `Eq` with `J`, transport into data | yes | [checked: `docs/core.md:136-138`] |
| Axiom K (uniqueness of identity proofs by matching) | yes | [checked: `core.md:119`, `:140`] |
| Definitional proof irrelevance | **no** (a draft proposal exists, SW-93) | [checked: `core.md:139`; `docs/proposals/proof-irrelevance.md:1-9`] |
| Function extensionality | **no** | [checked: `core.md:173` "No function extensionality is needed"; `docs/syntax.md:999` (`rewrite` skips binders)] |
| Quotient types | **no** | [checked: `docs/proposals/integers.md:514`] |
| Eta for functions | yes | [checked: `core.md:201`] |
| Propositional extensionality (`propext`) | **no** (nothing provides it) | [inferred from the absence of axioms; `core.md:9-24`] |
| Universe polymorphism | **no**: each data type is at a fixed level; `Eq` and `J` are term formers whose rules work at every level | [checked: `core.md:22`; `DESIGN.md:405`; `crates/core/src/check.rs:599-642` (`J`'s motive may be in any sort)] |
| Kernel-known opaque constants | yes (`Effect.Delay` and its constants; Float's bodyless primitives are planned) | [checked: `crates/core/src/partial.rs:1-30`, `:332-361`; `float.md:108-111`] |
| Exports must be assumption-free | yes, by DESIGN.md; but there is no `assume` and no assumption report yet | [checked: `DESIGN.md:123`, `:787`; `core.md:15`; the CLI's commands are `check std-source test run eval repl lsp build` ([run] `stitchwort --help`)] |

There is no visibility control (no `private`), so any field of a library record, including
`Map`'s `.tree`, can be read by user code [checked: `docs/syntax.md` has no `private`].

### 1.3 `Map` as built

- At draft 2's commit, `Map k v [ord]` was the record
  `{ tree: Map.Tree k v, ordered: Map.Tree.Ordered ord tree }`. The tree is a weight-balanced
  binary search tree (Adams; Haskell's `delta = 3`, `ratio = 2`), each `Bin` node storing its
  subtree's size, and `ordered` was an erased proof that the keys are in order — **and nothing
  else**: not the sizes, not the balance [checked at `1786944e`: `Map.sw:14-17`, `:149-170`].
  **Stage 0 added a third erased field, `sized: Map.Tree.Sized tree`** [checked:
  `crates/elab/src/std/Map/Map.sw:177-181`]; balance is still not certified (§4.3). Rebalancing "keeps the keys in
  order whatever the sizes say" [checked: `Map.sw:27-30`]. `Set k` is a record around `Map k ()`,
  a record rather than a synonym "so that dot notation on a set finds `Set`'s functions"
  [checked: `std/Set/Set.sw:1-7`].
- Proved today: the tree operations keep `Ordered`, and `get` agrees with a search of the entry
  list (`Map.Tree.getLookup`, `Map.getInsert`, `Map.getFromList`, …)
  [checked: `Map.sw:174-336`, `:391`, `:563`, `:615`].
- **The same pairs in different orders make different trees** [run, maps.md §1.1]:
  `Map.fromList [(1, 1), (2, 2)]` is `Bin 2 Tip 1 (Bin 1 Tip 2 Tip)`, while `[(2, 2), (1, 1)]` gives
  `Bin 2 (Bin 1 Tip 1 Tip) 2 Tip`.
- So a lawful `DecEq (Map k v)` would have to call these two maps *different*. Today `Map` has no
  `DecEq`, and therefore no `==` and no `Ord`. Its `Show` prints `Map.fromList [...]` in key order,
  so it is already canonical [checked: `Map.sw:619`].
- **The user-visible failure.** `type Inventory = { owner: Text, counts: Map Text Nat }` followed by
  `x == x` fails with `E-INSTANCE-NONE: no DecEq instance for Inventory … its field counts has type
  Map Text Nat …` [run, maps.md §1.1]. The real TS port worked around it by replacing the map with
  a sorted list. One extraction example compares `Map.toList a == Map.toList b` by hand
  [checked: `examples/extract/dictionary.sw:56-57`].
- **Proofs.** AoC day 8 keeps `Circuits = { labels: Map Nat Nat, count: Nat }`
  [checked: `aoc/src/Aoc/Day08/Day08.sw:77`]. `joinSame: c.join f s = c` works only because that
  path leaves the map syntactically untouched [checked: `Proofs/Labels.sw:128-129`]. A theorem
  like "inserting the stored value changes nothing" can't be stated with `=` at all.
- **Maps can't nest recursively today.** `type Tree = { label: Text, children: Map Text Tree }` is
  refused: `E-POSITIVITY: Tree is used inside another type` [run, §11.1]. The kernel refuses every
  nested occurrence, `List Tree` included [checked: `crates/core/src/check.rs:2033-2066`].

### 1.4 Key types real programs use

A grep of `aoc/`, `examples/` and `web/` for `Map K`/`Set K` [checked, 23 October 2026] finds these
key types: `Text` (32 uses), `Nat` (25), `Int` (5), `(Nat, Nat)` (3) and `(Int, Int)` (3). Two
reject tests use `Map (Nat -> Nat)` *values*. There are no custom orderings outside the tests that
check orderings are kept apart (`map-ordering-differs.sw`).

### 1.5 What Matt wants

- "I'm happy to have a functional data structure implementation of a Map in Stitchwort that we can
  prove the behaviour about." So the tree should stay Stitchwort code with proofs, and nothing
  should be swapped in by a trusted backend step. That rules out maps.md's D741.
- **Natural equality is "the same key–value pairs".**
- Mainstream surface (Scala/TS); no backward compatibility needed; prefer real proofs over
  examples.
- Recursive maps: rejected in the first version, supported later only through a separately
  reviewed design (D785).

## 2. Words used below

- **Representation equality.** `=` on a data type compares constructors and fields. Two trees with
  the same pairs but different shapes are *not* equal.
- **Extensional equality.** Equal when every observation agrees. For maps, observations are `get`:
  `(key: k) -> m1.get key = m2.get key`. For ordered maps that is the same as
  `m1.toList = m2.toList` [inferred: keys are unique and sorted, so `toList` is determined by `get`].
- **Setoid.** A type paired with an equivalence relation (here `Map.Equiv`) that proofs use
  instead of `=`.
- **Congruence ("respects").** A function `f` respects `Equiv` if `Equiv m1 m2` implies
  `f m1 = f m2`. Rewriting with `Equiv` is only sound inside functions that respect it.
- **Quotient.** A type former `Quot A R` whose values are `A`s, but where `R`-related values are
  *equal* (`=`). A function can be applied to it only by proving that the function respects `R`.
- **Representative.** The `A` stored inside a quotient value: today's tree record, for a map.
- **Canonical representation.** Only one value of the type represents each meaning.
- **Kernel reduction / erased execution.** The kernel's evaluator computes while checking, without
  erasing proofs. Running a program (`stitchwort run`, `test`, the Rust runtime, JS) erases proofs
  and types first (§9).

## 3. State-of-the-art audit

### 3.1 Lean 4 (core `Std` and Mathlib)

- **Three equality classes.** `BEq α` is a Bool `==` that "does not have any axioms like being
  reflexive or agreeing with `=`". `LawfulBEq` adds `eq_of_beq` and `rfl`. `DecidableEq` is
  `Decidable (a = b)` [cited: [Lean reference, Basic Classes](https://lean-lang.org/doc/reference/latest/Type-Classes/Basic-Classes/)].
- **Maps.** `HashMap`, `DHashMap`, `TreeMap` and `DTreeMap` (a "size-bounded" balanced tree whose
  balancing code follows Haskell's `Data.Map` [cited: `src/Std/Data/DTreeMap/Internal/Balancing.lean:427-428`])
  bundle their well-formedness proof with the data; Lean's internal tree-map well-formedness
  predicate includes both balance and ordering [cited by the review]. `.Raw` versions unbundle it,
  because "the bundling … prevents them from being used in nested inductive types"
  [cited: [Lean reference, Maps and Sets](https://lean-lang.org/doc/reference/latest/Basic-Types/Maps-and-Sets/)].
- **Option 1 in Lean: `BEq` plus `Equiv` on ordinary maps.** `beq_iff_equiv`, congruence lemmas
  `Equiv.union_congr`, … and `equiv_iff_toList_perm`
  [cited: `src/Std/Data/HashMap/Lemmas.lean:1399-1409`, `:1456-1466`, `:3043-3045`]. For tree maps,
  `Decidable (t₁.Equiv t₂)` exists [cited: [TreeMap/DecidableEquiv](https://lean-lang.org/doc/api/Std/Data/TreeMap/DecidableEquiv.html)].
- **Option 3 in Lean: extensional maps by quotient.** `ExtDTreeMap` is a structure whose only field
  is `inner : Quotient (DTreeMap.isSetoid α β cmp)`; each operation is lifted with a respects
  proof; `DecidableEq` needs `[TransCmp cmp] [LawfulEqCmp cmp] [∀ k, LawfulBEq (β k)]`
  [cited: `src/Std/Data/ExtDTreeMap/Basic.lean`]. The extensional API specifies ascending or
  descending traversal and requires `LawfulMonad` for its monadic folds [cited by the review]. The
  hash-map version has no `toList` or `fold`, because bucket order isn't canonical
  [cited: `src/Std/Data/ExtDHashMap/Basic.lean`]. "extensional maps should be used only when needed
  for verification" [cited: Maps and Sets].
- **Mathlib.** `Multiset α := Quotient (List.isSetoid α)`; `Finmap` is "effectively a quotient of
  `AList β` by permutation", with `ext_lookup` and `DecidableEq`
  [cited: `Mathlib/Data/Multiset/Defs.lean:69-70`; `Mathlib/Data/Finmap.lean:67-76`, `:235`, `:289`].
- **The kernel side.** [cited: [Lean reference, Quotients](https://lean-lang.org/doc/reference/latest/The-Type-System/Quotients/)]:

  ```
  Quot.{u}         {α : Sort u} (r : α → α → Prop) : Sort u
  Quot.mk.{u}      {α : Sort u} (r : α → α → Prop) (a : α) : Quot r
  Quot.lift.{u, v} {α : Sort u} {r : α → α → Prop} {β : Sort v}
                   (f : α → β) (a : ∀ (a b : α), r a b → f a = f b) : Quot r → β
  Quot.ind.{u}     {α : Sort u} {r : α → α → Prop} {β : Quot r → Prop}
                   (mk : ∀ (a : α), β (Quot.mk r a)) (q : Quot r) : β q
  Quot.sound.{u}   {α : Sort u} {r : α → α → Prop} {a b : α} : r a b → Quot.mk r a = Quot.mk r b
  ```

  The kernel reduces `Quot.lift` applied to `Quot.mk`, "analogous to ι-reduction"; the reference
  gives no reduction for `Quot.ind`. Function extensionality is *proved* from `Quot.sound`, and the
  proof relies on η and on the computation rule being definitional ("a propositional version …
  would not suffice, because the reducible expression occurs in the body of a function").
  **"Types implemented as quotients may not occur around nested occurrences in inductive type
  declarations"**: a `SetTree` whose `branch` holds a quotient of `List (SetTree α)` is refused with
  "(kernel) arg #2 of 'SetTree.branch' contains a non valid occurrence of the datatypes being
  declared", and the workaround is a quotient-free type first, then a relation [cited: Quotients
  §5.2]. Lean documents that a cast can leave a closed `Nat` unreduced in the kernel while compiled
  code evaluates it [cited by the review].
- **Consistency.** Lean's theory, quotients included, has a set-theoretic model (Carneiro, *The
  Type Theory of Lean*, 2019); the Lean4Lean paper notes that this result doesn't directly cover
  every later change to Lean 4 [cited: [Lean4Lean](https://arxiv.org/html/2403.14064v3); the
  qualification cited by the review]. It is evidence for E, not a proof for Stitchwort's calculus.
- **Pain points.** Parallel lemma versions for `DecidableEq` and `BEq`
  [cited: [Init/Data/Array/DecidableEq](https://lean-lang.org/doc/api/Init/Data/Array/DecidableEq.html)].
  Ordinary and `Ext` maps are separate types, converted explicitly [inferred from the APIs].

### 3.2 Rocq

- **Standard library FMaps/MMaps.** `=` is structural; `Equal m m' := ∀ y, find y m = find y m'`
  is the setoid, with a Bool `equal` specified by `equal_1`/`equal_2`
  [cited: [FMapInterface](https://docs.rocq-prover.org/v8.9/stdlib/Coq.FSets.FMapInterface.html)].
- **Generalized (setoid) rewriting** with declared morphisms, resolved by type classes
  [cited: [Rocq manual, Generalized rewriting](https://rocq-prover.org/doc/master/refman/addendum/generalized-rewriting.html)].
- **std++ `gmap` and CompCert `PTree`: canonical, so `=` is extensional with no axiom.** Appel and
  Leroy's canonical binary tries, keyed by `positive`, with seven node constructors so an empty
  subtree can't be built [cited: [Appel & Leroy, JAR 2023](https://ar5iv.labs.arxiv.org/html/2110.05063)];
  std++'s `gmap` takes any `Countable K`, with a proof field marking valid positions
  [cited: [stdpp.pmap](https://plv.mpi-sws.org/coqdoc/stdpp/stdpp.pmap.html),
  [stdpp.gmap](https://plv.mpi-sws.org/coqdoc/stdpp/stdpp.gmap.html)].
- **What canonical tries cost.** More cases (21 for `get'`/`set'`, 49 for a naive `combine'`);
  the earlier subtype version had well-formedness proofs that grew with the number of operations
  [cited: Appel & Leroy §3-5]. **Measured:** in their dictionary benchmark (5,064 string keys),
  relative to AVL trees, canonical binary tries took 14% of the run time inside Coq but 154% after
  extraction to OCaml; red-black trees took 31% and 35%. So after extraction the canonical trie was
  about 4.4 times slower than the red-black tree. The extracted strings were lists of machine
  characters, so this predicts nothing about Stitchwort's JS strings [cited by the review].

### 3.3 Agda

- **Standard library.** `Data.Tree.AVL.Map`, no map equality
  [cited: [Data/Tree/AVL/Map.agda](https://raw.githubusercontent.com/agda/agda-stdlib/master/src/Data/Tree/AVL/Map.agda)].
- **Cubical Agda.** Funext is a theorem and higher inductive types give quotients; incompatible
  with K under `--safe` [cited: [Agda manual, Cubical](https://agda.readthedocs.io/en/latest/language/cubical.html)].
  **Not an option for Stitchwort**, whose kernel has K [checked: `core.md:140`].

### 3.4 Isabelle/HOL: an abstract type with a concrete tree in generated code

`('a, 'b) mapping` is a `typedef` over partial functions with HOL's funext; `RBT_Mapping` makes a
non-injective function from red-black trees act as the constructor in generated code
(`code_datatype Mapping`), with proved code equations such as
`HOL.equal (Mapping t1) (Mapping t2) ⟷ RBT.entries t1 = RBT.entries t2`
[cited: [Mapping](https://isabelle.in.tum.de/library/HOL/HOL-Library/Mapping.html),
[RBT_Mapping](https://isabelle.in.tum.de/library/HOL/HOL-Library/RBT_Mapping.html)]. The trust is
in the code generator (Haftmann, Krauss, Kunčar, Nipkow, ITP 2013). This is maps.md's draft-1
design: it relies on funext and a trusted refinement step, which Stitchwort lacks or rejects.

### 3.5 F\*, Dafny, SPARK, Why3

All take the verifier route: an abstract map type with extensional equality by axiom or built-in
decision (F\*'s `FiniteMap.Base` states `equal m1 m2 ==> m1 == m2`; Dafny's `map` `==` is
extensional; SPARK's `Functional_Maps."="` is "Extensional equality over maps")
[cited: [FStar.FiniteMap.Base.fsti](https://raw.githubusercontent.com/FStarLang/FStar/master/ulib/FStar.FiniteMap.Base.fsti);
[Dafny FAQ](https://dafny.org/dafny/HowToFAQ/FAQMapExtensionality);
[a-cofuma.ads](https://gnu.googlesource.com/gcc/+/6fcba9ef23e4261a6279a76890b2c1488cc14d12/gcc/ada/libgnat/a-cofuma.ads)];
Why3's `fmap` likewise [unverified].

### 3.6 Programming languages

- **Haskell `Data.Map`.** `Eq` compares sizes and then entries in key order; the `Eq` docs state an
  "Extensionality" law that `Data.Map` breaks with the public `splitRoot` ("No guarantee is made as
  to the sizes of the pieces")
  [cited: [Data.Eq](https://hackage-content.haskell.org/package/base-4.22.0.0/docs/Data-Eq.html),
  [Data.Map.Strict](https://hackage-content.haskell.org/package/containers-0.8.1/docs/Data-Map-Strict.html)].
  This is exactly how a Bool `==` coarser than the representation leaks.
- **Idris 2** `SortedMap` compares `kvList`s; **Scala** collections are equal "if and only if they
  have the same elements" [cited: maps.md §2;
  [Scala collections, Equality](https://docs.scala-lang.org/overviews/collections-2.13/equality.html)].

### 3.7 Canonical structures and lower bounds

- **The lower bound is narrower than draft 1 said.** Andersson and Ottmann: for uniquely
  represented dictionaries, "one of the operations search or update must require a cost of
  Omega(n^(1/3))" [cited: [abstract](https://user.it.uu.se/~arnea/abs/andetigh.html)]. Golovin
  distinguishes **size-unique** representations (every set of the same size has the same shape)
  from representations determined by the particular keys, and attributes that bound to the former
  [cited by the review: Golovin, CMU]. So it does **not** show that every canonical search tree must
  be slow. Sundar and Tarjan's unique binary search trees are optimal only for sufficiently sparse
  or dense sets [cited: [SIAM J. Comput. 23(1)](https://epubs.siam.org/doi/10.1137/S0097539790189733)];
  treaps with hash-derived priorities are canonical with expected O(log n), under assumptions on the
  hash [cited: maps.md §3 (a2)].
- **Tries** (binary tries, Patricia trees, Hinze's generalized tries) are canonical when empty
  sub-maps are never stored [cited: [patricia-tree README](https://ocaml.org/p/patricia-tree/0.9.0/README.html);
  [Hinze 2000](https://www.cs.ox.ac.uk/publications/publication4830-abstract.html); inferred].
- **Hash-consing** needs a global table; it doesn't fit a pure kernel evaluator [inferred].

None of this needs settling to justify keeping the proved tree; option C stays deferred (D778).

### 3.8 Summary table

| System | Programmer's `==` on maps | Is `=` extensional? How | Proofs look like | Deriving with map fields | Runtime |
|---|---|---|---|---|---|
| Lean `HashMap`/`TreeMap` | `BEq`, same pairs | no | `~m` plus congruence lemmas | `BEq` yes, `DecidableEq` no | hash table / balanced tree |
| Lean `Ext*`, Mathlib `Finmap` | `DecidableEq` | yes: quotient (`Quot.sound`) | `=` and `ext` | yes | same as non-`Ext` [inferred] |
| Rocq FMaps/MMaps | `equal` (Bool, specified) | no | setoid rewriting | n/a | AVL / RB trees |
| Rocq std++ `gmap`, CompCert `PTree` | decidable `=` | yes: canonical trie, no axiom | `=` | yes | binary trie over `positive` |
| Agda stdlib | none | no | `Setoid` | n/a | AVL |
| Isabelle `mapping` | `HOL.equal` → entries | yes: funext | `=`, Lifting/Transfer | yes | RB tree via trusted codegen |
| F\*, Dafny, SPARK | extensional | yes: axiom / built in | SMT | yes | runtime library |
| Haskell, Idris 2, Scala | entries equal | — | — | yes | balanced trees / HAMT |

**Lessons.** (1) Every system with a fast non-canonical tree *and* extensional `=` pays with a
quotient, funext or an axiom. (2) Without one, two equalities and congruence lemmas everywhere.
(3) Canonical tries avoid both, for keys with an injective encoding, with more proof cases and
measured run-time costs after extraction. (4) A Boolean `==` that isn't `=` leaks as soon as a
public function looks at the representation (`splitRoot`). (5) Lean's quotients don't support
nested recursive occurrences.

## 4. Common ground: stage 0

### 4.1 What every option needs

1. `Map.Equiv m1 m2 := m1.toList = m2.toList`, equivalent to "same `get` everywhere"
   [inferred: entries are sorted with distinct keys, by `Ordered` and `ord.equal`]. On the raw
   records it is `Map.Raw.Equiv a b := Map.Raw.toList a = Map.Raw.toList b`, a relation defined by
   equality of an ordinary value, which is what makes §8.2 short.
2. An **agreement lemma** per operation, stating it in terms of the sorted entry list, e.g.
   `insertToList: (m.insert k v).toList = Map.Spec.insert k v m.toList`. The `get` side exists
   [checked: `Map.Tree.getLookup`, `Map.sw:391`]. "Each operation then lifts in one line" is true
   only once its agreement lemma is proved, and only for operations whose result depends on the
   entries alone (§12).
3. From these, each such operation **respects** `Equiv` by rewriting.
4. `Map.same [auto d: DecEq v] (m1: Map k v) (m2: Map k v): Bool` with
   `sameIff: same m1 m2 = True <-> Equiv m1 m2`. **It needs `DecEq v`**: an unconstrained Boolean
   with that law would decide equality of arbitrary values, by comparing singleton maps (review
   §1; draft 1's option B omitted the constraint).

```
def Map.Equiv (m1: Map k v) (m2: Map k v): Prop := m1.toList = m2.toList

theorem Map.insertRespects (k: k) (x: v) (m1: Map k v) (m2: Map k v) (same: Map.Equiv m1 m2):
    Map.Equiv (m1.insert k x) (m2.insert k x) :=
  rewrite Map.insertToList k x m1, Map.insertToList k x m2, same in rfl
```

### 4.2 What stage 0 also checks (D771, as amended by the review)

- The **complete raw invariant**: ordering, cached sizes, balance (§12.1).
- The **observation audit** of the public API (§12.2).
- **Recursive behaviour today**: whether a map can appear in its own element type (it can't; §11.1).

### 4.3 Stage 0 results

Stage 0 is built (the appendix [Stage 0 results](#stage-0-results) has the detail, as its lane
wrote it). What it settles for the operative design:

- **Invariant.** `Map` is now `{ tree, ordered, sized }`: `Map.Tree.Sized` certifies every stored
  size, every operation is proved to keep it, and `Map.sizeToList: m.size = m.toList.length`
  follows. So `size` and `isEmpty` respect `Map.Equiv` and stay O(1). Balance is **not**
  certified; complexity bounds carry the assumption stated in §13.3. §8.1's `Map.Raw` is this
  record, renamed.
- **Agreement and respects lemmas** exist for every public operation (`std/Map/Spec.sw`,
  `std/Set/Spec.sw`), so each stage-2 lift has its respects proof ready.
- **Observation audit.** Every public observation depends only on the entries, except the record
  fields themselves (`.tree`, `.ordered`, `.sized`), which stage 2 hides behind the quotient.
- **Recursion.** `Map Text Tree` and `List Tree` inside `Tree` are both refused today; a tree and
  a forest defined together are what works (§11).
- `Map.same [DecEq v]` with `sameIff` is option B, available now.

## 5. Options

`Inventory` is the running example: `type Inventory = { owner: Text, counts: Map Text Nat }`.

### (A) A lawful-by-relation Boolean `Eq` for `==`, plus `Equiv` congruence

**Idea.** A new interface behind `==`, weaker than `DecEq`, with its own equivalence relation and a
proof that the Boolean decides it. Every `DecEq` type gets one with `Same := (=)`; `Map` gets one
with `Same := Map.Equiv`; deriving produces `Eq` fieldwise.

```
interface Eq (a: Type) =
  { Same: a -> a -> Prop
  , equals: a -> a -> Bool
  , sound: (x: a) -> (y: a) -> equals x y = True -> Same x y
  , complete: (x: a) -> (y: a) -> Same x y -> equals x y = True
  , refl: …, sym: …, trans: … }

instance Eq.ofDecEq [auto d: DecEq a]: Eq a := { Same = x y => x = y, … }
instance Map.instEq [auto e: DecEq v]: Eq (Map k v) := { Same = Map.Equiv, … }
```

- **It doesn't compose as written.** An inner map gets only the weaker `Eq`, not `DecEq`, so
  `Map Text (Map Text Nat)` gets no instance from `Map.instEq`; nor does a map whose values are
  records that derive only `Eq`. To fix it, the map relation must compare values by *their*
  `Same`, not by `=`: a relational lifting through entries (`Map.EquivBy (Same: v -> v -> Prop)`)
  with its own congruence lemmas for every operation (review §7). That is a concrete extra cost of
  A, and a stronger argument for E than anything about Lean's experience.
- **Language changes.** `==`/`!=` resolve to `Eq`; deriving generates `Same`, `equals` and their
  proofs; an instance-priority rule; std functions that only test equality ask for `Eq` (churn
  across `std/List`, `std/Set`).
- **Proofs** state `Same`, not `=`; `rewrite`, `if h: r1 = r2` and `auto` don't apply.
- **No `Ord (Map k v)`** unless `Ord` is weakened to a preorder, which ripples through every `Map`
  lemma that uses `ord.equal` [inferred].
- **Leaks.** `.tree` is public, so user code can distinguish `Same` maps (as `splitRoot` does).
- **Kernel/trust:** none. **Fit:** natural equality only for `==`, not `=`; against D683's
  reasoning.

### (B) No `==` on maps; `Map.same` and lemmas only

Stage 0, plus `Map.same [DecEq v]` and `sameIff` (§4.1). No language change. `Inventory` gets no
`==`. Cheap, honest, doesn't solve the port's problem. It is stage 0 of A, E or F.

### (C) A canonical structure that is also the runtime structure

**Idea.** Replace the tree with a structure that has one shape per set of pairs, as std++/CompCert
do: `DecEq` derives structurally, `=` is extensional, no axiom.

- **Keys.** A trie needs an **injective** encoding of keys into digits. An encoding that is also
  **order-preserving** is a separate, additional requirement, needed only so that traversal gives
  the requested order cheaply. Encodings for the key types in use (§1.4) exist, with details that
  aren't trivial [inferred]: `Nat` as length then big-endian bits; `Int` needs reversed magnitude
  order within the negative range; `Text` as characters plus a terminator; tuples by
  concatenation, which must be unambiguous (self-delimiting components).
- **Custom orderings** are not inherently inexpressible: descending order is a reversed traversal,
  and an arbitrary order could be had by sorting entries when ordered enumeration is asked for, at
  that cost. The accurate limitation: **an arbitrary `Ord k` dictionary doesn't supply an
  efficient order-compatible encoding**, so `Map` would take a `Key k` interface, not `Ord k`.
- **Proof cost.** 21-case `get`/`set`, 49-case `combine` with Appel–Leroy's nodes; Stitchwort has
  no tactics. A simpler trie with a "no empty node" Bool-equation invariant has unique invariant
  proofs by `DecEq.uniqueEq`. **But unique proofs give propositional equality, not `rfl`:**
  without definitional proof irrelevance, two closed maps built differently carry different proof
  terms, so `rfl` between them can fail even though the data are identical (draft 1 said `rfl`
  would work; corrected). `DecEq` and an `ext` lemma still work.
- **Performance.** Depth is key length in digits, not log n; JS digit tests are `bigint` or string
  operations [inferred]. The Appel–Leroy measurements (§3.2: ~4.4× slower than red-black trees
  after extraction to OCaml; faster inside Coq) say kernel and run time must be measured
  separately. A benchmark would be required.
- **Fit.** Meets "functional, proved, natural equality"; replaces the proved tree; needs `Key`.

### (D) Canonical meaning plus a proved tree swap-in (maps.md draft 1)

`Map` *is* a sorted entry list; backends substitute the tree. The kernel runs lists (a 10^4 build
hit the evaluation limit [run, maps.md §4.6]) and the trusted backend step is what Matt rejected.
Listed for completeness.

### (E) Quotient types in the kernel (Lean's design)

The kernel rules are [§7](#7-the-kernel-specification); the `Map` construction and its theorems are
[§8](#8-map-as-a-quotient); what it means for computation is [§9](#9-the-computation-contract).
In short: today's record becomes `Map.Raw`, `Map` is `{ raw: Quot (Map.Raw k v) Map.Raw.Equiv }`,
operations are lifted with stage 0's respects lemmas, and `Inventory` derives `==` with no deriving
change.

```
theorem restock (inv: Inventory) (h: inv.counts.get "nails" = Some 3):
    { owner = inv.owner, counts = inv.counts.insert "nails" 3 } = inv :=
  Inventory.ext _ inv rfl (Map.insertGet "nails" 3 inv.counts h)   -- generated T.ext (SW-263)
```

Costs: a kernel extension (§7, §14.4); every function out of `Map` needs a respects proof (the
library carries it); `.tree` is no longer reachable; recursive maps stay unsupported (§11); and
closed transports along map equalities can stick in the kernel (§9).

### (F) Setoid rewriting on top of A or B

An elaborator feature: `rewrite same in …` with `same: Map.Equiv m1 m2`, using registered
congruence lemmas (as Rocq's `Proper` instances; Stitchwort already finds `FCong` lemmas by name
[checked: `core.md:173`]). Only worth building if A is chosen. Under E, ordinary `rewrite` works.

### 5.1 Comparison

| | A `Eq` | B `same` | C canonical trie | D swap-in | E quotient | F setoid rewrite |
|---|---|---|---|---|---|---|
| `=` means same pairs | no | no | **yes** | **yes** | **yes** | no |
| `==` on `Inventory` | yes (not `=`) | no | yes | yes | yes | (with A) |
| `==` on nested maps | only with relational lifting | no | yes | yes | yes | (with A) |
| `Ord (Map k v)`, `Set (Set k)` | no | no | yes | yes | yes | no |
| Keeps today's proved tree | yes | yes | **no** | yes (at run time) | **yes** (with stage 0's `sized` field) | yes |
| Arbitrary `Ord k` orderings | yes | yes | only at a sorting cost | yes | yes | yes |
| Recursive maps | no (today) | no | possible (ordinary data) | no | **no in v1** (§11) | no |
| Kernel / trust change | none | none | none | backend substitution | **one term-former family + 1 axiom** | none |
| Closed `rfl` between different builds | no | no | not without proof irrelevance | yes | no (decide instead) | no |
| Kernel-time speed | O(log n) | O(log n) | O(key length) | O(n) | O(log n) | — |
| Run-time speed | today | today | unmeasured (4.4× slower than RB in OCaml, §3.2) | today | today (+1 box; D866 optional) | — |
| Size | large (language-wide) | small | large | medium–large | medium (kernel) + medium (library) | medium |

## 6. Recommendation

**Choose E (quotients), staged, with B as its stage 0** (D770), conditional, as the review asked, on
two things this draft makes explicit: the recursive-type policy (§11, decided by D785) and the
computation contract (§9).

- It is the only option that gives Matt both things he asked for: the existing proved tree, and
  `=` meaning "same pairs".
  - A gives "same pairs" only to `==`, splits `==` from `=` (the split D683 rejected for `Float`),
    and doesn't compose without a relational lifting.
  - C gives natural `=`, but throws away the proved tree, needs a `Key` interface, and has
    measured run-time costs in the one comparable extraction benchmark.
  - D needs the trusted swap-in.
- Its trust cost is the best understood in the field: Lean's quotient axiom with a published model
  (with the qualification in §3.1).
- It solves the general problem: sets, a later hash map, rationals, multisets, and funext.

**When to pick something else.** If an axiom is unacceptable: B, then A with a relational lifting
(and F later). If unrestricted kernel canonicity (every closed pure term reduces to data in the
kernel) were an essential requirement, E as proposed doesn't meet it (§9); that would be a reason
to reconsider C. Neither is the case today.

## 7. The kernel specification

This is the precise version of D773: the rules first, then the choice of representation (§7.7).
It is signed off (D920) and is the specification stage 1 implements (§14.1); nothing is built yet.

### 7.1 Typing and universes

Five forms. Implicit arguments are shown in brackets as the elaborator presents them; the kernel
sees them filled in, as for every other form [checked: `core.md:81`].

**Shared premises.** Every form carries a carrier `A` and a relation `R` (the bracketed `[A] [R]`
below), and the kernel establishes, for every occurrence of every form, before anything else:

```
Γ ⊢ A : Type i        Γ ⊢ R : A -> A -> Prop
```

The per-form rules assume these and add their own premises:

```
──────────────────────────────────────────────  (Quot)
Γ ⊢ Quot A R : Type i

Γ ⊢ a : A
──────────────────────────────────────────────  (mk)
Γ ⊢ Quot.mk [A] [R] a : Quot A R

Γ ⊢ B : s  (s = Prop or Type j, any j)    Γ ⊢ f : A -> B
Γ ⊢ h : (x: A) -> (y: A) -> R x y -> f x = f y           Γ ⊢ q : Quot A R
──────────────────────────────────────────────  (lift)
Γ ⊢ Quot.lift [A] [R] [B] f h q : B

Γ ⊢ P : Quot A R -> Prop     Γ ⊢ h : (x: A) -> P (Quot.mk [A] [R] x)     Γ ⊢ q : Quot A R
──────────────────────────────────────────────  (ind)
Γ ⊢ Quot.ind [A] [R] [P] h q : P q

Γ ⊢ x : A      Γ ⊢ y : A      Γ ⊢ r : R x y
──────────────────────────────────────────────  (sound)
Γ ⊢ Quot.sound [A] [R] [x] [y] r : Quot.mk [A] [R] x = Quot.mk [A] [R] y
```

**The checks, for the implementation.** Every checker path that meets a `Term::Quot` (inference,
checking against an expected type, and any shortcut that types a term without the general
`infer`) performs all of these; none may be left to the elaborator, because the rejection tests
build core terms by hand (R14):

- **C1 Fixed arity.** Each form has exactly its argument count (`Quot` 2, `mk` 3, `lift` 6,
  `ind` 5, `sound` 5, counting the bracketed ones); anything else is `E-MALFORMED`.
- **C2 Carrier.** `A`'s type is `Type i` for some `i`, checked on the `mk`, `lift`, `ind` and
  `sound` forms themselves, not only on a separate `Quot A R` type expression (so a hand-built
  `Quot.mk [0 = 0] [R] refl` is refused, R14).
- **C3 Relation.** `R : A -> A -> Prop`, with the codomain `Prop` exactly (a `Bool`- or
  `Type`-valued `R` is refused).
- **C4 Agreement.** In `lift` and `ind`, `q`'s type must be convertible to `Quot A R` with the
  *same* `A` and `R` as the form's own parameters; the relation is compared, not only the carrier
  (R11: a lift justified for `Bool` equality can't be applied to a `Quot Bool AllTrue`). In
  `sound`, `r`'s type is `R x y` for the form's `R`; in `ind`, `h`'s type mentions
  `Quot.mk [A] [R] x` with the form's parameters.
- **C5 Sorts and motives.** `lift`'s `B` is a type whose sort is `Prop` or some `Type j`, and `f`
  is non-dependent (`A -> B`); `ind`'s `P` returns `Prop` exactly (R6).
- **C6 Respects proof.** `lift`'s `h` has exactly the stated type for the form's `f`, `R` and `B`.

Decisions inside these rules (D861):

- **Carriers are types, never proposition inhabitants.** `A : Type i`, and `Quot A R : Type i`,
  the same level. This is an **initial-scope choice**: quotients of a proposition's proofs aren't
  needed for any planned API, so the first version restricts carriers to `Type i` and keeps every
  rule about `Prop` unchanged. (Draft 2 argued that two proofs are "interchangeable for every
  purpose"; that's not true here, because conversion compares proofs and there's no definitional
  proof irrelevance, so it isn't the reason.) The restriction excludes a **proposition**
  `P : Prop` as carrier; it doesn't exclude the **universe** `Prop`, which is a type in `Type 0`
  (`Prop: Type 0` [checked: `core.md:52`]), so `Quot Prop R : Type 0` is admitted, as is a carrier of types
  (`Quot (Type 0) R : Type 1`, §7.4). So **`Quot A R` is never a `Prop`**, and the existing
  `Prop`-elimination rule (`E-PROP-ELIM`, [checked: `core.md:110`; `check.rs:741-775`]) never
  meets a quotient.
- **No universe polymorphism is needed for the rules.** Like `Eq` and `J`, whose rules hold at
  every level [checked: `check.rs:344-369`, `:599-642`], these are rules, not constants, so `i`
  and `j` are whatever the arguments' types say. (Library *theorems* about quotients are still at
  fixed levels: §8.7, D923.)
- **`lift`'s result sort is independent of the carrier's**, and may be `Prop`. Three kinds of
  `B` are admitted, and §7.4 erases them differently:
  - **`B` a data type** (`B := Nat`): the lift computes data.
  - **`B` a proposition** (`B : Prop`, e.g. `B := 0 = 0`): the lift produces a *proof*, and `f`
    itself is a proof (a function into `Prop` is a proof of a `∀`, by impredicativity).
    Example: `Quot.lift [B := 0 = 0] (b => rfl) (x y r => rfl) q`.
  - **`B` a sort** (`B := Prop` or `B := Type j`): the lift produces a proposition or a type.
    Example: `a => p (Raw.toList a)` for a predicate `p` on entry lists respects `Raw.Equiv` by
    congruence alone, so it lifts to `Quot … -> Prop` with `B := Prop`, without `propext`.
    (Draft 2 called this "lifting into `Prop`"; it is `B := Prop`, not `B : Prop`.) Lifting into
    `Type j` with `j > i` is allowed (large elimination); it is consistent in the set model
    [inferred], and `J` already allows it for equality.
- **`lift` is non-dependent** (`B` doesn't mention `q`). A dependent eliminator into data can be
  *defined* later from `lift` and `ind` (lift a dependent pair, use `ind` to identify its first
  projection with the input, transport the second), as Lean's `Quot.rec` is, and needs a respects
  proof up to transport; it extracts nothing [inferred]. **Its beta rule would be propositional,
  not definitional**: with an opaque `ind`, the transport in its definition doesn't reduce, so not
  every computational property of Lean's derived recursor carries over (review round 2 §5). It
  isn't needed for maps and isn't proposed now.
- **`ind`'s motive is proposition-valued only.** A motive in `Type` would be dependent elimination
  into data without a respects proof, which extracts representatives (§7.6).
- **`R` is arbitrary** (any `A -> A -> Prop`, not necessarily an equivalence), as in Lean; the
  quotient by `R` is then the quotient by its equivalence closure [cited: Quotients].

### 7.2 Reduction and conversion

- **One computation rule (ι for quotients):**
  `Quot.lift [A] [R] [B] f h (Quot.mk [A] [R] a) ⟶ f a`. It fires on values: whenever `q`
  *evaluates* to a `Quot.mk`, through definitions, `let`, `case` branches or anything else, as a
  `case` does on a constructor [checked: the evaluator's policy, `crates/core/src/value.rs:5-7`].
  (The `mk`'s parameters are the lift's by C4, since the term is well typed.)
- **Nothing else computes.** `Quot.lift f h q` with `q` neutral is neutral. `Quot.ind` never
  computes (§7.3). `Quot.sound r` is a neutral proof. `J` on a `Quot.sound` or `Quot.ind` proof is
  stuck, as `J` on any non-`rfl` proof already is [checked: `core.md:137`].
- **Conversion is structural, at a common well-formed type.** When conversion compares two terms
  at the same well-formed type `Quot A R`, `Quot.mk [A] [R] a ≡ Quot.mk [A] [R] b` iff `a ≡ b`.
  More generally, two `mk`s are convertible only if their carriers, their relations *and* their
  representatives are: the parameters are compared, never dropped, so that a check across two
  quotient types can't lose them. `Quot A R ≡ Quot A' R'` iff `A ≡ A'` and `R ≡ R'`; neutral
  `lift`/`ind`/`sound` forms compare argument by argument, parameters included (the proof argument
  `h` of `lift` too, as for any other proof argument today: there's no definitional proof
  irrelevance). **No eta for quotients** (no `Quot.lift Quot.mk h q ≡ q`) and conversion never
  consults `R`'s *content*: deciding `R` is undecidable in general and propositional anyway.
- **Unfolding policy** [inferred; an implementation requirement]. A definition whose body is a
  `Quot.lift` on its argument (`Map.get k m`) should stay folded on an open `m`, as a definition
  whose case tree can't step does [checked: `value.rs:5-7`, `core.md:196`], so goals show
  `Map.get k m` rather than the lifted term. The rule: `Quot.lift` counts as a case on its
  quotient argument for "can this case tree take a step". **Condition:** keeping a definition
  folded on a neutral quotient must never stop conversion from comparing the definition with its
  body when it needs to; the policy changes only what is displayed and when things are computed,
  not what is equal. Test A8: with `def observe (q: Q') := Quot.lift f respects q`,
  `rfl: observe q = Quot.lift f respects q` is accepted for an open `q`, and `Quot.funext`'s proof
  goes through when its evaluation and rebuilding steps are named helper definitions.

### 7.3 Why `Quot.ind` must not compute

A rule `Quot.ind h (Quot.mk a) ⟶ h a` would look harmless, but it proves **propositional proof
irrelevance** for every proposition (review §2). For any `P: Prop` and `p q: P`:

1. Let `Q := Quot Bool (x y => Unit)` (everything related).
2. Let `h: (b: Bool) -> P` be `h False := p`, `h True := q` (a `case` on `Bool`, producing a proof:
   allowed).
3. `f := (z: Q) => Quot.ind [P := _ => P] h z : Q -> P` (constant motive).
4. `Quot.sound Trivial : Quot.mk False = Quot.mk True`.
5. Congruence: `f (Quot.mk False) = f (Quot.mk True)`.
6. With the rule, the two sides reduce to `p` and `q`, so `p = q`.

That isn't a contradiction: Stitchwort deliberately stays compatible with proof irrelevance (index
unification never takes proofs apart, D137 [checked: `core.md:124`]). But it would be a new logical
commitment, adopted by accident while copying Lean, whose kernel has definitional proof irrelevance
and so doesn't notice the difference. K gives uniqueness of *identity* proofs only
[checked: `core.md:140`]; this would give uniqueness of proofs of *every* proposition. So
**`Quot.ind` has no computation rule** (D861). Nothing in §8 needs it to compute (the round-2
review confirmed this for §8.2–§8.4): `ind` produces proofs, and the only things that look inside
a proof are a `case` on a one-constructor proposition, `J` and comparison
[checked: `core.md:198`]. A proof built with `ind` can block a `J`, exactly as `Quot.sound` can
(§9; test A6).

### 7.4 Erasure

Erasure of quotients is **type-directed**: what a `lift` becomes depends on its result type `B`,
and what its argument becomes depends on the *original* function's type, never on the quotient's.

#### 7.4.1 By form and result

| Form | Kernel checker | Running in the kernel's evaluator (`run --reference`, `test`) | Rust runtime (`crates/rt`) and JS |
|---|---|---|---|
| `Quot A R` | a type | erased (a type former's value is never needed) | erased |
| `Quot.mk a` | a value | a `Quot.mk` value around `a`'s value (the placeholder if `a` is erased, below) | whatever `a` lowers to: **the placeholder if `A`'s elements are erased** (`A` a sort or a type-former type, e.g. `A := Type 0`), otherwise `a`'s representation; no wrapper |
| `Quot.lift f h q`, **`B` data** (`B := Nat`) | the rule (§7.2) | the rule: `f a`, applied with the evaluator's usual erasure of `f`'s arguments by `f`'s own type; `h` erased | the core application `f q`, lowered through the existing application path (relevance from `f`'s type, §7.4.2); `h` erased |
| `Quot.lift f h q`, **`B : Prop`** (a proof) | the rule | **the placeholder** | erased: `f`, `h`, `q` aren't lowered |
| `Quot.lift f h q`, **`B` a sort** (`B := Prop`, `Type j`) | the rule | **the placeholder** | erased |
| `Quot.ind h q` | neutral | **the placeholder** | erased (a proof) |
| `Quot.sound r` | neutral | **the placeholder** | erased (a proof) |

**How the runners know which row** (D921). The kernel records it in the checked term, as it
already records whether a `let` is skipped (the checker recomputes that flag and ignores the
input's [checked: `crates/core/src/check.rs:336-342`]; it isn't hashed [checked:
`crates/core/src/hash.rs:565-568`]). Two flags, recomputed by the checker on every check with the
kernel's existing erasure test `is_erased` (a type former, or a type whose sort is `Prop`
[checked: `check.rs:2336-2338`]):

- on `lift`: **the result is erased**, `is_erased(B)`;
- on `mk`: **the representative is erased**, `is_erased(A)`.

The lowerers and the reference evaluator read the flags; they never infer types. A parameter or
field **of type `Quot A R` is never erased** (`Quot A R` is neither a proposition nor a type
former), so every relevance analysis (the definition masks, constructor fields, the boundary)
treats it as data and passes whatever `mk` produced, possibly the run-time placeholder value.

#### 7.4.2 Lowering a computational lift

A `lift` whose result isn't erased lowers exactly as the core term `f q` would, through the
backend's existing application path. That path is already type-directed by `f`:

- **`f` a definition** (`Quot.lift seven …`): the call keeps only the arguments its own type
  marks as run-time, by the definition's mask [checked: `crates/rt/src/lower.rs:550-608`;
  `crates/js/src/lib.rs:2746-2772`]. For `def seven (A: Type 0): Nat := 7`, `q` is dropped and
  `seven` is a constant, so the lift is `7`.
- **`f` a lambda**: the argument is bound, as an erased binding if it lowers to the placeholder
  [checked: `lower.rs:510-547`; JS binds every lambda parameter, `lib.rs:2627-2639`].
- **`f` any other expression** (a variable, a closure): applied to every argument, the uniform
  closure convention [checked: `lower.rs:486-502`; `lib.rs:2605-2620`]. This is correct only if
  every function *value* follows that convention, which today it doesn't (§7.4.3).

The review's example must run as `7` in every runner (A7):

```
def QTy: Type 1 := Quot (Type 0) (a b => a = b)
def seven (a: Type 0): Nat := 7
def answer: Nat := Quot.lift seven (a b h => rfl) (Quot.mk Nat: QTy)
```

#### 7.4.3 What the current eraser does, and a pre-existing bug

- **Reference evaluator** (`crates/core/src/erase.rs`): arguments are erased per definition, from
  that definition's own type (rule 1 [checked: `erase.rs:6-9`]; worked out by `of_def`
  [checked: `erase.rs:135-166`]); a lambda's argument is evaluated, which is harmless for a type.
  Once `lift` reduces to `f a`, the existing machinery is type-directed. What it lacks is the
  flags of §7.4.1 (it would evaluate a proof-valued lift rather than skip it, which terminates and
  is harmless, but isn't the specified behaviour) and the placeholder for `sound` and `ind`
  (D862).
- **Rust runtime and JS: saturated calls are right; function values with erased parameters are
  not.** A definition's erased parameters are dropped from its calling convention (a definition
  whose run-time parameters are all erased is a *constant* [checked: `lower.rs:81-119`]), and an
  unsaturated reference passes only the run-time arguments supplied so far [checked:
  `lower.rs:584-600`; `lib.rs:2759-2770`]. But code that receives the function as a value knows
  only its type, and passes every argument, erased ones as the placeholder. Run today [run]:

  ```
  def seven (a: Type): Nat := 7
  def app (f: Type -> Nat): Nat := f Nat
  def pick (a: Type) (n: Nat): Nat := n + 1
  def app2 (f: Type -> Nat -> Nat): Nat := f Nat 41
  -- app seven: reference 7; Rust runtime panics "internal error: applied Nat(7), which isn't a
  --            function" (crates/rt/src/machine.rs:269); JS throws "TypeError: v0 is not a function"
  -- app2 pick: reference 42; Rust runtime panics "internal error: expected a `Nat`, got Erased";
  --            JS throws "TypeError: Cannot mix BigInt and other types"
  ```

  This has nothing to do with quotients, but a quotient of types reaches it as soon as the lifted
  function is passed as a value (`Quot.lift g h q` inside a function with parameter
  `g: Type 0 -> Nat`). **D922 fixes it first in stage 1**: a reference to a definition that
  leaves at least one erased parameter unsupplied lowers to a closure over *all* of its remaining
  parameters (the erased ones accepted and ignored), the uniform convention, in both backends;
  saturated calls keep the direct convention. `app seven`, `app2 pick` and their lambda variants
  become regression tests in every runner.
- **Proof-valued lifts** would mostly be erased today without the flag: a theorem in `f`'s place
  lowers to the placeholder (a definition with an erased result [checked: `lower.rs:581-583`]),
  and an application whose head lowers to the placeholder is the placeholder (`lower.rs:496-497`,
  `lib.rs:2611-2615`). But a proof that reached a non-erased position as a run-time placeholder
  *value* would then be applied at run time, which panics in the Rust runtime
  [checked: `machine.rs:268-270`]. The flag removes the dependence on how `f` happens to be
  written. `J` ignores its proof in both backends [checked: `lower.rs:469-470`; `lib.rs:2732`], so
  test A5 (below) checks that nothing else evaluates the lift.

The proof-valued test (A5), with `Q := Quot Bool (x y => Unit)`, inline and through a definition:

```
def p: 0 = 0 := Quot.lift (b => rfl) (x y related => rfl) (Quot.mk False: Q)
def n: Nat := J (y proof => Nat) 0 p
def nInline: Nat := J (y proof => Nat) 0 (Quot.lift (b => rfl) (x y related => rfl) (Quot.mk False: Q))
```

Every runner gives `0` for both. In the kernel, `nInline` computes to `0` (the lift reduces to
`rfl`, then `J` takes its base), so `rfl: nInline = 0` is accepted [inferred]; `n` follows the
kernel's existing folding of definitions with an erased result, which the test pins.

#### 7.4.4 The erasure contract for equality proofs (replaces draft 2's classification)

Draft 2 justified "`J` on the placeholder takes its base" by "a closed proof of `x = y` is `refl`
or built from `Quot.sound`". That's false: an opaque `Quot.ind` makes closed proofs of `0 = 0`
that are neither (A6, below). The contract, stated directly instead of by a list of syntactic
forms:

> **Equality proofs are erased during execution. Equality transport (`J`) uses the erased
> representation of its base, subject to the language's erasure-preservation contract. In kernel
> evaluation, transport may remain stuck on opaque proofs, including proofs produced by
> `Quot.ind` and `Quot.sound`.**

Why the base is right: the preservation argument already in `erase.rs` (proofs never decide which
way a computation of data goes [checked: `erase.rs:21-34`]) plus the model: any proof of `x = y`,
whatever it's built from, means `x` and `y` denote the same value, so the motive at `y` is the
motive at `x`. When running in the reference evaluator, `Quot.sound`, `Quot.ind` and erased-result
lifts evaluate to the placeholder (D862, D921), so rule 4 applies to them.

The ind-only test (A6), with no `Quot.sound` anywhere:

```
def p: 0 = 0 := Quot.ind [P := q => 0 = 0] (b => rfl) (Quot.mk False: Q)
def n: Nat := J (y proof => Nat) 0 p
```

In the kernel `n` is stuck (`Quot.ind` doesn't compute; K proves `p = rfl` but doesn't make them
convertible), so `rfl: n = 0` is `E-REFL`; every runner gives `0`; the same with the `Quot.ind`
written inline.

#### 7.4.5 Closed quotients reach `mk`: an intended invariant

This is an **invariant the implementation must keep**, not a consequence draft 2 established. Its
premises:

1. the program is well typed, closed, and in the executable total fragment;
2. proofs, types and arguments are erased correctly (§7.4.1–§7.4.3, D922);
3. applications, closures, equality transport (`J` on the placeholder) and the permitted
   proposition eliminations (`case` on a one-constructor proposition) behave as specified;
4. no unimplemented opaque data-producing primitive is reached.

- **Reference evaluator.** Under these premises, evaluating a closed term of type `Quot A R`
  with erasure ends at a `Quot.mk` value (whose representative is the placeholder when `A`'s
  elements are erased), so a computational `lift` never sticks when running. This evaluator keeps
  the `mk` wrapper as a representation invariant.
- **Rust runtime and JS.** There is no wrapper: a value of type `Quot A R` *is* the
  representative's erased representation, and a `lift` is an application. What must hold is that
  `mk` and the lifted function agree on that representation, which they do because both use the
  same relevance analysis (§7.4.1).

The set-model account (§7.8) supports the logical rules; it doesn't by itself establish every
runtime representation choice, so the invariant is tested by **observable results** compared
across `run --reference`, `test`, `run` and `run --js`: A3, A5, A6, A7 and the prototype's
properties 1, 4 and 6 (§14).

### 7.5 Interaction with the existing rules

- **`Prop` elimination.** Untouched: quotients are never propositions (§7.1). `Quot.ind` produces
  proofs, which `E-PROP-ELIM` already allows anywhere.
- **Case trees.** `Case(x, D, …)` requires `x: D …` for a *data type* `D` [checked: `core.md:107`;
  `check.rs:663-720`]. `Quot A R` isn't one, so a `case` on a quotient is refused by the existing
  rule (`E-MALFORMED` in the kernel; the elaborator should say something friendlier, §7.6 R2).
- **Index unification.** Rules apply by the constraint's type: injectivity and conflict only "at a
  data type in `Type i`", everything else stuck [checked: `crates/core/src/unify_index.rs:224-253`].
  A constraint at type `Quot A R` is therefore **stuck** unless deletion (`lhs ≡ rhs`) or solution
  (a flexible variable) applies; `Quot.mk a = Quot.mk b` is never decomposed into `a = b` and never
  declared impossible. The `constructor` helper recognises only `Value::Ctor`, numbers and compact
  text [checked: `unify_index.rs:273-285`], so even a mistaken `Value::Data` typing couldn't
  decompose a `Quot.mk` as long as it isn't a `Value::Ctor` (§7.7). Rejection test R3.
- **Positivity.** A data type occurring inside `Quot …` is a nested occurrence, refused today
  (`Occurrence::Inside` [checked: `check.rs:2033-2066`]). The first version keeps that, with a
  dedicated diagnostic (§11). The check finds occurrences through the term's children
  (`occurs`, over `Term::for_each_child` [checked: `crates/core/src/term.rs:469`]), so the new
  form's children must include **every** argument, the relation's included: an occurrence only
  in `R` (`Quot Nat (x y => (t: T) -> Unit)` in a field of `T`) must be refused too (R13).
- **Index unification inside other constructors.** A quotient-valued index nested in an ordinary
  pair, list or record (`AtP (Quot.mk False, 0)`) is decomposed at the outer constructor as today,
  which produces the inner equation at type `Q`; that one is stuck, so the whole problem is stuck
  rather than decided (R12).
- **Termination.** A `Quot.lift` gives no structural-descent evidence (it isn't a match), like `J`
  [checked: `core.md:152`]; a recursive call inside a lifted function is checked as any call
  [inferred].
- **K / deletion.** Deletion solves a constraint only when both sides are convertible, which for
  quotients means equal representatives (§7.2). That's sound in the set model [inferred].
- **Abilities and `Partial`.** Nothing new: `Effect.Delay` is not a data type either, and a
  quotient of computations isn't proposed.

### 7.6 Forbidden behaviours and their rejection tests

The canonical test object is the **`Bool`-by-`True` quotient**, which identifies `False` and `True`:

```
def AllTrue (x: Bool) (y: Bool): Prop := Unit
def Q: Type := Quot Bool AllTrue
theorem same: (Quot.mk False: Q) = Quot.mk True := Quot.sound Trivial
```

Any mechanism that could read a representative back out of `same` proves `False = True`, so each
forbidden behaviour gets a test, directly with kernel terms and through the elaborator where
there's surface syntax. Every R test except R4 is a **kernel** rejection: the kernel must refuse
the hand-built core term, so the elaborator isn't trusted for it. **R4 is an elaborator policy
test** with no kernel judgment behind it: a lawful `DecEq` for a particular quotient may exist,
and once supplied it is used (A10). The invariant R4 protects is "never derive a quotient's
equality by comparing representatives", not "records containing a quotient never get `==`".

| # | Forbidden behaviour | Why the design excludes it | Rejection test |
|---|---|---|---|
| R1 | Constructor injectivity / no-confusion for `Quot.mk` | `Quot.mk` isn't a constructor: no `Value::Ctor`, no `case`, so the prelude's injectivity and disjointness lemmas (proved by `case` + `J` [checked: `core.md:379`]) can't be written for it | A proof of `False = True` from `same` via a projection `Q -> Bool` defined by `case`: refused at the `case` (R2). A `Quot.mk False = Quot.mk True -> Void` "no-confusion" lemma: unprovable (no test can show unprovability; R2–R4 cover each route) |
| R2 | Pattern matching that extracts the representative | `case` needs a data type (§7.5) | `def rep (q: Q): Bool := match q with \| Quot.mk b => b` refused (elaborator: a new message, "a quotient can't be matched on: use `Quot.lift` with a proof that the result respects the relation"); the core `Case` on a `Q` variable refused by the kernel (`E-MALFORMED`) |
| R3 | Index unification decomposing `Quot.mk` | Constraints at a quotient type are stuck (§7.5) | `type At: Q -> Type = \| AtF: At (Quot.mk False) \| AtT: At (Quot.mk True)`; `def only (a: At (Quot.mk False)): Nat` covering only `AtF` must be `E-INDEX-STUCK`, *not* accepted with `AtT` impossible; and a `case` whose branch would need `False = True` from `Quot.mk False = Quot.mk True` mustn't get it |
| R4 *(elaborator policy)* | Structural equality derivation on `Quot` | `derive.rs` derives only for data types with `DecEq` fields [checked: `derive.rs:9-20`]; no generic `DecEq (Quot A R)` instance is provided (none can be lawful in general) | `type Box = { q: Q }`; with no `DecEq Q` in scope, `b == b` is `E-INSTANCE-NONE` naming the field `q`. Positive counterpart A10 |
| R5 | A projection back to the stored `A` | None exists: `lift` (needs a respects proof) and `ind` (proposition motive) are the only eliminators | `Quot.lift (b => b) h` must need `h: (x y: Bool) -> AllTrue x y -> x = y`, unprovable; a term passing anything else is `E-TYPE-MISMATCH` |
| R6 | `Quot.ind` into data | `ind`'s motive must be a proposition (§7.1) | `Quot.ind [P := _ => Bool] (b => b) q` refused (`E-UNIVERSE`/`E-TYPE-MISMATCH`) |
| R7 | `Quot.ind` computing | No rule (§7.3) | `rfl: Quot.ind [P] h (Quot.mk a) = h a` refused with `E-REFL` |
| R8 | Conversion identifying related representatives | Conversion is structural (§7.2) | `rfl: (Quot.mk False: Q) = Quot.mk True` refused with `E-REFL` |
| R9 | A quotient of a proposition | Carriers are types (§7.1) | `Quot (0 = 0) (x y => Unit)` refused (`E-UNIVERSE`) |
| R10 | A data type recursive through a quotient | §11 | `type T = \| Node (kids: Quot (List T) R)` and `type Tree = { children: Map Text Tree }` refused, with the §11.2 diagnostic |
| R11 | Ignoring the relation parameter (C4) | `lift`'s and `ind`'s `q` must have type `Quot A R` for the form's own `R` | With `BoolEq x y := x = y`: `Quot.lift [Bool] [BoolEq] [Bool] (b => b) (x y h => h) (q: Quot Bool AllTrue)` (an identity lift justified for `Bool` equality, applied to the all-related quotient) is `E-TYPE-MISMATCH`; if accepted it would extract the representative |
| R12 | Decomposing a quotient index nested in another constructor | §7.5: the inner equation at type `Q` is stuck | `type AtP: (Q, Nat) -> Type = \| AtF: AtP (Quot.mk False, 0) \| AtT: AtP (Quot.mk True, 0)`; `def only (a: AtP (Quot.mk False, 0)): Nat` covering only `AtF` is `E-INDEX-STUCK`; the same with the index inside a `List Q` and inside a record `{ q: Q, n: Nat }` |
| R13 | A recursive occurrence only in the relation | Positivity sees every argument (§7.5) | `type T = \| Node (kids: Quot Nat (x y => (t: T) -> Unit))` is `E-POSITIVITY` |
| R14 | Malformed hand-built forms (C1–C6) | The kernel validates the whole form, independently of elaboration | Core terms built directly, each refused: every form with one argument too few and one too many (`E-MALFORMED`); `Quot.mk [0 = 0] [R] refl` and `Quot.sound` at a carrier `0 = 0` (C2, without a separate `Quot` type expression ever being checked); `R` returning `Bool` (C3); `Quot.sound [A] [R] [x] [y] r` with `r: R' x y` for another `R'` (C4); `lift` with a `B` that isn't a type (C5); `ind` with `P` returning `Type` (C5); `lift` with `h` for a different `f` (C6) |

**The outer record keeps ordinary record rules** (review §2). For `Map = { raw: Quot … }`, the
generated `Map.ext` and record injectivity hold: `{ raw = q1 } = { raw = q2 }` gives `q1 = q2`.
What's forbidden is the next step, from `Quot.mk a = Quot.mk b` to `a = b`, and R1–R5 and
R11–R12 cover it. The positive tests (A1–A10) are in §14.3.

### 7.7 Representation: one term-former family (D860, resolving D773)

| | Kernel-known constants (like `Effect.Delay`) | Term formers (like `Eq`/`J`) |
|---|---|---|
| Universes | fixed: without universe polymorphism, `Quot` would be at `Type 0` only, and `lift` would need one constant per result sort (`Prop`, `Type 0`, …), since there is no cumulativity [checked: `core.md:22`, `:62`] | level-generic, like `Eq` and `J` [checked: `check.rs:344-369`, `:599-642`] |
| Typing rules | the prelude declares signatures, the kernel checks them by conversion (`define_primitive` [checked: `partial.rs:329-361`]) | written in `check.rs` |
| Computation | a new special case in `value.rs`: a neutral headed by `Quot.lift`'s id whose last argument is `Quot.mk`'s neutral application | an ordinary rule on a new `Value` form |
| Forbidden behaviours | automatic: a bodyless constant is never a `Ctor` | automatic as long as `Quot.mk` isn't a `Value::Ctor` |
| Code touched | small in `core`; hashing exists (`primitive` tag [checked: `hash.rs:96-104`]) | every `match` on `Term`/`Value`: `J` appears in about 20 source files across `core`, `elab`, `rt` and `js` [checked: `grep -l 'Term::J' crates`] |

**Choice: term formers, as one family** (D860): `Term::Quot(QuotForm, args)` with
`QuotForm = Type | Mk | Lift | Ind | Sound` and a fixed argument count per form, and the matching
`Value` forms. One variant keeps the cost of threading it through the crates close to one term
former's, while the rules stay level-generic. Constants would need several `lift`s now and a
migration when universe polymorphism arrives (DESIGN.md §16 Q3 [checked: `DESIGN.md:1076`]).
Hashing gives each form its own tag, so `Quot.ind` and `Quot.sound` never collide (A4). The
surface names `Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind`, `Quot.sound` are built in, with the
implicits shown in §7.1. `Mk` and `Lift` carry D921's erasure flag, recomputed by the checker and,
like `let`'s, not hashed.

**The representation doesn't make anything automatic** (review round 2 §3). "`Quot.mk` isn't a
`Value::Ctor`" keeps the constructor-only mechanisms away from it, but the checks of §7.1 are
still needed, and so is correct handling of the new form in **every traversal** of terms and
values. From the existing `Term::J` cases in `crates/core` [checked: `grep -n 'Term::J'`], the
list for `Term::Quot` is:

| Traversal | Where (the `Term::J` case today) |
|---|---|
| sharing and dropping (`has_unique_child`, `take_children`) | `term.rs:179-187`, `:206-227` |
| substitution and shifting (`shift`) | `term.rs:372-438` |
| children, hence `subterms`, `mentions` (occurs checks) and the positivity `occurs` | `term.rs:444-517` |
| typing (`infer`, and checking against a type) | `check.rs:218-369`, beside `infer_j` (`:600-642`) |
| evaluation (`eval_step`, `resume`) | `value.rs:722-835`, `:896-1010` |
| quoting (`quote`) | `value.rs:1380-1436` |
| conversion (`same_term_layer`) | `value.rs:2058-2121` |
| content hashing (`term`) | `hash.rs:468-610` |
| termination walk | `termination.rs:256-374` |
| reference evaluator, expansion, quoting | `reference.rs:27-91`, `:168-220`, `:364-415` |
| pretty-printing | `pretty.rs:504` |

plus, outside `core`, the elaborator (names, implicits, unification, the check-cache codec), the
two lowerers (`crates/rt/src/lower.rs`, `crates/js/src/lib.rs`) and the axiom report's walk
(D925). The term-level unit tests in `term.rs` (`shift_goes_under_every_binder_and_into_every_child`,
`mentions_finds_free_occurrences_only` [checked: `term.rs:586-643`]) get `Term::Quot` cases, and R13
checks the positivity path end to end.

### 7.8 Trust contract

1. **Consistency.** Read `Quot A R` as the set of equivalence classes of `A` under the equivalence
   closure of `R`; `mk` as the class map; `lift f h` as the function on classes (well defined by
   `h`); `ind` as true because every class has a representative; `sound` as true. Propositions are
   read as empty or one-element sets, so K, impredicative `Prop`, `J` into data and the absence of
   definitional proof irrelevance are all validated [inferred; the review gives the same outline and
   stresses it isn't a verification of Stitchwort's whole calculus]. The `lift` rule holds in the
   model by definition. A computing `ind` would also hold in this model (it validates proof
   irrelevance), which is why §7.3 is about commitments, not consistency.
2. **Preservation.** `rt` and JS lower `mk a` as `a` and a computational `lift f h q` as the
   type-directed application `f q`; erased-result lifts, `ind` and `sound` are erased; the
   reference evaluator agrees (§7.4). This depends on D922's calling-convention fix. Tested by
   observable results across the runners (A3, A5–A7) plus the existing differential tests; the
   set model doesn't by itself establish the runtime representation choices (§7.4.5).
3. **What's trusted additionally**: the five typing rules and their checks C1–C6, the one
   computation rule, the erasure rows and flags, and the axiom. DESIGN.md §13's trusted list and
   core.md gain a "Quotients" section.

## 8. `Map` as a quotient

### 8.1 Definitions

```
-- Today's record (with stage 0's `sized`), renamed (§4.3, §12.1).
type Map.Raw (k: Type) (v: Type) [auto ord: Ord k] =
  { tree: Map.Tree k v
  , ordered: Map.Tree.Ordered ord tree
  , sized: Map.Tree.Sized tree
  }

def Map.Raw.Equiv (a: Map.Raw k v [ord := o]) (b: Map.Raw k v [ord := o]): Prop :=
  Map.Raw.toList a = Map.Raw.toList b

type Map (k: Type) (v: Type) [auto ord: Ord k] = { raw: Quot (Map.Raw k v) Map.Raw.Equiv }

def Map.toList (m: Map k v [ord := o]): List (k, v) :=
  Quot.lift Map.Raw.toList (a b same => same) m.raw          -- the respects proof is `same` itself

def Map.insert [auto ord: Ord k] (key: k) (value: v) (m: Map k v): Map k v :=
  { raw = Quot.lift (r => Quot.mk (r.insert key value))
                    (a b same => Quot.sound (Map.Raw.insertRespects key value a b same)) m.raw }
```

`Map` stays a record rather than a synonym for the quotient so that dot notation finds `Map`'s
functions, as `Set` does today [checked: `Set.sw:1-7`]. The ordering is a parameter of the type, so
both operands of every comparison below have the **same** `ord`; maps with different orderings are
different types, as today (`map-ordering-differs.sw`), and comparing across orderings would need a
conversion.

### 8.2 The central lemma: equality is equality of `toList`

By the computation rule, `Map.toList { raw = Quot.mk a } ≡ Map.Raw.toList a`.

- **Forward.** Given `p: m = n`, `Eq.cong Map.toList p : m.toList = n.toList`. For `m`, `n` built
  from `a`, `b` this is literally `Map.Raw.Equiv a b`. No `propext`, no `DecEq v`, no funext, no
  proof irrelevance.
- **Backward.** Given `m.toList = n.toList`: take the records apart (`match m`, `match n`; records
  are one-constructor data), then `Quot.ind` on each quotient with the motive
  `q1 => (q2: …) -> toList {raw = q1} = toList {raw = q2} -> {raw = q1} = {raw = q2}` (a
  proposition), leaving the case `Quot.mk a`, `Quot.mk b`, where the hypothesis *is*
  `Map.Raw.Equiv a b` by computation; `Quot.sound` gives `Quot.mk a = Quot.mk b`; congruence gives
  the records equal.

```
theorem Map.eqIffToListEq (m: Map k v [ord := o]) (n: Map k v [ord := o]):
    Iff (m = n) (m.toList = n.toList)
theorem Map.toListInjective [m n: Map k v [ord := o]] (h: m.toList = n.toList): m = n
theorem Map.ext [auto ord: Ord k] (m n: Map k v) (h: (key: k) -> m.get key = n.get key): m = n
    -- from toListInjective and stage 0's "sorted, distinct keys, get agrees with lookup"
```

All three hold **for any value type `v`**, including `Map Nat (Nat -> Nat)`. This is the theorem
the design rests on: the quotient identifies exactly the maps with the same entries.

### 8.3 `DecEq`

```
def Map.decEq [auto ord: Ord k] [auto d: DecEq v] (m: Map k v) (n: Map k v): Decidable (m = n) :=
  match List.decEq (m.toList) (n.toList) with       -- elements (k, v): ord.eq and d
    | Yes h => Yes (Map.toListInjective h)
    | No h  => No (p => h (Eq.cong Map.toList p))
instance Map.instDecEq [auto ord: Ord k] [auto d: DecEq v]: DecEq (Map k v) := { decide = Map.decEq }
```

The branch is chosen by comparing lists, which computes in the kernel whenever both maps reach
`Quot.mk` and their keys and values, and the comparisons on them, reduce (§9.2).
`Quot.ind` and `Quot.sound` appear only inside the `Yes` payload, so `Decidable.toBool` (that is,
`==`) computes even though the proof inside uses the axiom; nothing is transported along a quotient
equality to pick the branch. With `auto`, `Decidable.fromYes d Trivial` re-checks the decision in
the kernel [checked: `core.md:246`], and that also only needs the branch.

### 8.4 `Ord`

`compare m n := List.compareLex (Pair.compareBy ord.compare vord.compare) m.toList n.toList`
(`List.compareLex` exists, with `List.compareLexEqual` [checked:
`crates/elab/src/std/core/CompareData.sw:8-20`]). Every law of `Ord` [checked: `Ord.sw:23-39`] is
transferred through `toList`: `flip` and `trans` from the list order's, since `compare` *is* the
list comparison of the projections; `equal` as `compareLexEqual` then `Map.toListInjective`; the
relation laws by `Ord.fromCompare` [checked: `Ord.sw:44-60`]. No extensionality beyond §8.2.

### 8.5 What each piece needs

| Operation or theorem | Requirement on values | On keys |
|---|---|---|
| `Map.Equiv`, `Map.ext`, `Map.eqIffToListEq`, `Map.toListInjective` | none | the map's `Ord k` |
| `Map.same`, `DecEq (Map k v)`, `==` | `DecEq v` | the map's `Ord k` (its `eq` field) |
| `Ord (Map k v)` | `Ord v` | the map's `Ord k` |

### 8.6 The general quotient-library lemma

Kept from draft 1 as a general result (review §1 checked it): for a decidable equivalence `R`
(`r: A -> A -> Bool` with `r x y = True <-> R x y`), `Quot.mk a = Quot.mk b -> R a b`, without
`propext`. Fix `a`, lift `x => r a x` into `Bool` (it respects `R` by symmetry and transitivity),
apply it to both sides of the equation, compute, and use `r a a = True`. It proves an equality of
`Bool`s, never of propositions. For `Map` the `toList` argument (§8.2) is stronger (no
decidability) and easier to audit, so the library uses that; this lemma (`Quot.exactDec`) serves
other quotients (rationals, unordered pairs). **Level:** it is stated for `A: Type` (that is,
`Type 0`) and `R: A -> A -> Prop`; see §8.8.

### 8.7 Function extensionality (D774)

**Data-valued functions.** `Quot.funext (a: Type) (b: a -> Type) (f g: (x: a) -> b x)
(h: (x: a) -> f x = g x): f = g`, by quotienting the function type `(x: a) -> b x` (a type in
`Type 0`) by pointwise equality: evaluation at each `x` respects it, `Quot.sound` identifies the
classes, and the `lift` rule plus function eta identify the rebuilt functions with `f` and `g`
[cited: Quotients; checked eta: `core.md:201`]. It needs neither `propext` nor proof irrelevance.
It gives propositional funext, not a decision procedure; `rewrite` under binders is a separate
elaborator change. It covers functions whose results are **data** (each `b x` a type); it doesn't
cover proof-valued functions directly, because `(x: a) -> P x` with `P x : Prop` is itself a
proposition (impredicativity) and so can't be a carrier (§7.1). Lean's version is sort-general;
Stitchwort's carrier rule is narrower, so the proof-valued case needs its own construction.

**Proof-valued functions, by a data wrapper** (review round 2 §4; no new axiom, no proof
irrelevance). A typed sketch, checked in stage 1 as part of A2:

```
type ProofBox (P: Prop) = { proof: P }             -- a record: data, in Type 0, its field erased

theorem Quot.funextProp (a: Type) (P: a -> Prop) (f g: (x: a) -> P x)
    (h: (x: a) -> f x = g x): f = g :=
  let boxF: (x: a) -> ProofBox (P x) := x => { proof = f x }
  let boxG: (x: a) -> ProofBox (P x) := x => { proof = g x }
  -- 1. box the results; 2. pointwise, equal proofs give equal boxes
  let pointwise: (x: a) -> boxF x = boxG x := x => Eq.cong (p => { proof = p }: P x -> ProofBox (P x)) (h x)
  -- 3. data-valued funext on the boxed functions
  let boxes: boxF = boxG := Quot.funext a (x => ProofBox (P x)) boxF boxG pointwise
  -- 4. project pointwise; (boxF x).proof ≡ f x by projection, and x => f x ≡ f by eta
  J (k e => (x => (boxF x).proof) = (x => (k x).proof)) rfl boxes
```

Step 2's `Eq.cong` is at `P x -> ProofBox (P x)`, which needs `Eq.cong`'s domain to admit a
proposition; today `Eq.cong (f: a -> b)` has `a b: Type` [checked:
`crates/elab/src/std/core/Equality.sw:9`], so the stage-1 version uses `J` directly there as in
step 4 (`Eq` itself is allowed at a proposition: its type argument is checked as any type
[checked: `check.rs:344-353`]). The record and projection steps are [inferred] until the check.

### 8.8 Levels of the library lemmas (D923)

The kernel rules are level-generic (§7.1), but a library theorem is an ordinary definition, at a
fixed level, because there is no universe polymorphism [checked: `core.md:22`]. So:

- `Quot.funext` is for `a: Type 0` and `b: a -> Type 0`; `Quot.funextProp` for `a: Type 0`;
  `Quot.exactDec` for `A: Type 0`. That is every use planned: maps, sets, and functions between
  ordinary data.
- **Other instances** (a domain or codomain in `Type 1`, a carrier of types) are supplied by
  restating the same proof at that level, under a level-suffixed name (`Quot.funext1`), in the
  module that first needs it; each is a few lines and checked like any theorem. Universe
  polymorphism, if it comes (DESIGN.md §16 Q3), replaces the copies; nothing else depends on it.

## 9. The computation contract

### 9.1 Three properties, kept apart

Using `same: (Quot.mk False: Q) = Quot.mk True` (§7.6):

```
def n: Nat := J (y p => Nat) 0 same          -- transport 0 along `same`, constant motive
```

1. **Termination.** Evaluating `n` terminates, in every evaluator.
2. **Kernel reduction to a data constructor.** In the kernel, `n` is a closed `Nat` in normal form
   that **is not a numeral**: `J` on `Quot.sound Trivial` is stuck [checked rule: `core.md:137`;
   inferred outcome]. `rfl: n = 0` fails with `E-REFL`.
3. **Erased execution.** `stitchwort run`, `test`, the Rust runtime and JS all give `0` (`J` takes
   its base; `Quot.sound` is the placeholder, §7.4).

A stuck closed normal form is compatible with termination; it is incompatible with a blanket promise
that every closed pure term reduces to data in the kernel (§9.4). `Quot.sound` isn't the only
cause: a proof made by `Quot.ind` blocks `J` the same way, with no `Quot.sound` anywhere (§7.4.4,
A6).

### 9.2 What still computes

**Lifted operations reduce on quotient constructors. Complete kernel evaluation additionally
requires the relevant key, value and callback computations to reduce.** Closedness alone isn't
enough once stuck closed data terms exist: with §9.1's stuck `n: Nat`,
`def m: Map Nat Nat := Map.singleton 0 n` reaches `Quot.mk` and its entry list reaches its
constructors, but anything that must inspect `n` (`m == Map.singleton 0 0`, a sum of the values)
stays stuck, and a stuck *key* blocks comparison during lookup or insertion. The quotient lifts
don't repair stuck computations inside entries. Within that condition:

- Every lifted map operation: `Quot.lift f h (Quot.mk raw) ⟶ f raw`, so `get`, `insert`, `toList`,
  `size`, folds compute in the kernel exactly as today (plus one step per lift).
- `==` and `compare`: the decision chooses its branch by list comparison (§8.3).
- Proofs about such maps by decision: `Map.ext` plus a decided `==`, or `auto`.

**Executable map operations use quotient lifts. Equality proofs support reasoning; transporting
computational data along them may block kernel reduction.** (Proposed text for core.md.)

### 9.3 Practical consequences

- `rfl` between two closed maps built in different orders fails (different trees); `==`/`decide`
  replaces it, and `Map.ext` for open ones.
- Dependent programs that transport data along a map equality (`J` with a non-trivial motive, or a
  `rewrite` producing data) may get stuck in the kernel; explicit transport lemmas
  (`f m = f n` from `m = n` by `Eq.cong`) avoid it.
- Kernel conversion tests and erased-execution tests can have different expected outcomes for such
  terms; acceptance test A3 pins both.
- Proof procedures that evaluate (`auto`'s decision procedures, `rfl` on computed sides) may stick
  on inputs containing such transports.
- **`J` is not erased in the kernel** (review §5): for a motive that depends on the endpoint, the
  base and the result have different types unless the endpoints are convertible.
- **The constant-motive rule is a separate, later proposal** (D924). The round-2 review judged
  `J (y p => T) d e ⟶ d`, when neither `y` nor `p` occurs free in `T`, locally sound (both sides
  have type `T`; the propositional version is already provable by `J`), and it would unstick
  §9.1's and A6's examples. It isn't needed for maps and isn't part of stage 1. Its proposal must:
  (1) check its interaction with existing reduction, substitution, beta and eta; (2) recognise
  constancy syntactically, or by existing kernel conversion; (3) never fire on a merely
  propositional proof that the motive is constant; (4) keep tests with non-constant motives,
  because it doesn't restore general canonicity.

### 9.4 Wording changes (D863)

A search of DESIGN.md and docs/ finds no blanket "every closed term reduces to data in the kernel"
promise [checked: `grep -n -i 'canonic\|normal form\|every closed\|closed term' DESIGN.md`]. The
statements that need precise wording:

| Where | Today | Change |
|---|---|---|
| DESIGN.md:138 "Total" | "evaluating `t` reaches a value in finitely many steps" | add: "evaluating means running, with proofs and types erased (§6). The checker's evaluator, which doesn't erase, also terminates, but a closed term that transports data along an opaque equality proof (one made by `Quot.sound` or `Quot.ind`) may stop at a term that isn't a value" |
| DESIGN.md:123 "Assumption-free" | tracked assumptions only | "relative to the core theory, which includes the quotient axiom `Quot.sound`" (§10) |
| core.md:137 (`J`) | "With any other proof it's stuck." | add: "In a closed term that can still happen, with a proof made by `Quot.sound` or `Quot.ind` (see Quotients)" |
| core.md:203 and `crates/core/src/erase.rs:14-15` | "in a closed program every proof of an equation is `refl`" | §7.4.4's contract: "Equality proofs are erased during execution. `J` uses the erased representation of its base, subject to the erasure-preservation contract (any proof of `x = y` means `x` and `y` are the same value in the model). In kernel evaluation, transport may remain stuck on opaque proofs, including those made by `Quot.ind` and `Quot.sound`. When running, `Quot.sound`, `Quot.ind` and lifts with an erased result evaluate to the placeholder." No list of syntactic forms of closed proofs |
| core.md (new "Quotients" section, and the Terms table) | — | §7.1–§7.5, including C1–C6 and the erasure flags |
| core.md (`J`) and DESIGN.md "Total" | — | §9.2's sentence: lifted operations reduce on quotient constructors; complete kernel evaluation also needs keys, values and callbacks to reduce |

## 10. Axiom accounting (D772)

**`Quot.sound` is an accepted core axiom.** It doesn't block exports; its use, direct or
transitive, is visible in dependency/axiom reports. Lean likewise reports `Quot.sound` through its
axiom-listing command [cited by the review].

- **"Assumption-free"** (DESIGN.md §3) becomes: no `assume`, proof holes, trusted foreign
  functions or conjectures, **relative to the declared core theory**, which is the kernel's rules
  plus `Quot.sound`. "Proved" (DESIGN.md:153) is then "holds in the core theory".
- **What reporting exists today: none.** There's no `assume` yet, so "every checked definition is
  assumption-free" [checked: `core.md:15`], and no `stitchwort assumptions` command exists despite
  DESIGN.md:123 naming it [run: `stitchwort --help` lists `check std-source test run eval repl lsp
  build`]. So stage 1 adds a small report (D864): `stitchwort axioms <name>` lists the axioms a
  declaration depends on (today only `Quot.sound`; later `assume`s and the handler conjecture
  fold into the same walk, which becomes DESIGN.md's `assumptions`). It trusts nothing new.
- **How it finds them** (D925). `Quot.sound` is a term former (D860), not a declaration, so a
  walk that follows only named references never sees an inline `Quot.sound r` node. The walk
  scans the **checked terms** of every declaration reached, bodies *and* types, theorems and other
  erased definitions included, and every argument position, proof arguments included (`lift`'s
  `h`, the proof of a `J`), and reports a `Term::Quot(Sound)` node wherever it occurs. It can't
  reuse the runtime's `reachable` (`crates/rt/src/erasure.rs:74-108`), which deliberately skips
  the bodies of erased definitions and collects only `Term::Def`s. Results are cached by content
  hash. Test A9: a `def` whose body contains an inline `Quot.sound` (no named theorem in between)
  reports `Quot.sound`; so does a definition that only uses it through a theorem's proof; a
  definition using neither reports nothing.
- **What an empty report means.** It reports **foundational dependencies only**. An empty report
  does *not* mean the term is computationally transparent in the kernel: a term can depend on an
  opaque `Quot.ind`, have no `Quot.sound` dependency, and still not reduce to data (A6). The
  report's help text says so.
- K and `J` are rules of the core, not axioms, and aren't listed; nor are `Quot.ind` and
  `Quot.lift`, which are rules (they hold in the model without any assumption, §7.8).

## 11. Recursive types through a quotient (D785)

### 11.1 Today

`type Tree = { label: Text, children: Map Text Tree }` [run]:

```
[E-POSITIVITY] Error: `Tree` is used inside another type
 3 │ type Tree = { label: Text, children: Map Text Tree }
   │ field `children` has `Tree` inside another type
   │ Note 1: a data type's fields can contain it only directly, or as the result of a function
   │ field: whether it's safe inside another type (such as a `List`) would depend on how that type
   │ uses it, which isn't checked
```

The kernel refuses every nested occurrence, `List Tree` included [checked: `check.rs:2033-2066`];
mutual data groups are the workaround for lists [checked: the error's Note 2]. So rejecting
recursion through `Map` in the quotient version is **no regression**.

### 11.2 The first version (D870)

The kernel keeps refusing occurrences inside `Quot` (they are `Occurrence::Inside`). The elaborator
adds a diagnostic when the occurrence is inside a quotient or a type whose fields reach one
(`Map`, `Set`): "`Tree` is used inside `Map Text Tree`, which is a quotient type; data types can't
be recursive through a quotient yet. Store the nodes in a separate table addressed by ids (a
`Map Nat Node` whose nodes hold their children's ids), or define a tree and a forest together,
with the key and the child in separate constructor fields." (Draft 2 suggested "a list of pairs";
that is refused too, since `List (Text, Tree)` nests `Tree` inside another type [checked: stage 0,
§S.1].) The forest form is what `examples/accept/mutual-data.sw` does today. Rejection test R10.

### 11.3 Why a positivity tweak isn't enough, and the later route

Marking `Quot`'s carrier argument as positive would admit the declaration, but a usable recursive
type needs induction and recursion principles, and structural recursion would have to descend
*through* a quotient: a recursive function on `Tree` must be shown to respect the relation at every
level, and the termination checker would need a notion of "smaller" for a representative obtained
only inside a `lift` (review §3). Lean refuses these declarations for the same reason [cited:
Quotients §5.2]. A possible later route, to be separately designed and reviewed: define a recursive
**raw** type without quotients (`type RawTree = { label: Text, children: Map.Raw Text RawTree }`,
which itself needs nested positivity through `Map.Raw`'s record and tree, or a mutual group), define
an equivalence that relates trees with the same entries at every level, and quotient the *whole*
type once. That is a different user-facing construction with its own API; it doesn't make §11.1's
declaration work as written. Not scheduled.

## 12. The representative invariant and the observation audit

### 12.1 Ordering, cached sizes, balance

The quotient's soundness doesn't depend on the invariant, but each lifted operation's respects
proof does. Three requirements, and where each stands after stage 0:

1. **Ordering** — needed for lookup and sorted-entry lemmas. **Certified** (`ordered`)
   [checked: `crates/elab/src/std/Map/Map.sw:159-166`].
2. **Correct cached sizes** — needed by `size` and `isEmpty`. **Certified since stage 0**
   (`sized: Map.Tree.Sized tree` [checked: `Map.sw:171-181`], kept by every operation, giving
   `Map.sizeToList`). The counterexample that motivated it is **pre-stage-0** (draft 2, [run] at
   `1786944e`), kept for the record; it no longer checks (`examples/reject/map-wrong-size.sw`,
   `E-REFL`):

   ```
   -- pre-stage-0 only: the record had no `sized` field then
   def honest: Map Nat Text := Map.singleton 1 "a"
   def forged: Map Nat Text :=
     { tree = Bin 7 Tip 1 "a" Tip, ordered = Both (Both Trivial Trivial) (Both Trivial Trivial) }
   test "same entries"     := Map.toList honest == Map.toList forged    -- passed
   test "forged size is 7" := Map.size forged == 7                      -- passed
   ```

3. **Balance** — needed for the O(log n) bounds, not for correctness (rebalancing keeps order
   "whatever the sizes say" [checked: `Map.sw:27-30`]). **Not certified**; a hand-built ordered,
   correctly sized, unbalanced tree is a valid `Map.Raw`.

**The invariant is settled** (D865): `Map.Raw = { tree, ordered, sized }` (§8.1), exactly stage
0's record. Balance stays out: it isn't needed for soundness or for any respects proof, and
certifying it is a follow-up (map-set.md). The complexity claims therefore carry a stated
assumption (§13.3): **they hold for maps reachable from balanced base cases (`empty`,
`singleton`, `fromList`) through balance-preserving operations** (every public `Map` operation is
written to preserve balance, though that is not proved). They don't hold for every value: a raw
map forged unbalanced and then wrapped stays unbalanced under operations that keep shape, e.g.
`map id` (`Map.Tree.map` rebuilds the same shape). (Lean's well-formedness includes balance [cited
by the review]; adding it later changes no API.)

### 12.2 The observation table

| Operation | Requirement for the quotient API |
|---|---|
| `get`, `getOr`, `contains`, `insert`, `insertWith`, `remove`, `alter`, `adjust`, `union`, `filter`, `map`, (later) intersection, difference | result depends only on the entries: an agreement lemma with the list spec |
| `size`, `isEmpty` | cached cardinality is correct: certified by `sized` since stage 0 (§12.1) |
| `toList`, `keys`, `values`, `foldLeft` | traversal and accumulation order specified: ascending key order. `Map.Tree.foldLeft` is an in-order left fold [checked: `Map.sw:136-138`], so it equals `List.foldLeft` over `toList` for **any** callback, associative or not; a fold grouped by tree shape would not be liftable |
| effectful traversal (a future `forEach`/monadic fold) | callback order independent of shape (ascending), as Lean's `Ext` API specifies |
| `.tree`, a stored-representative `toRaw`, root/shape inspection, `splitRoot`-like functions | **must not exist on `Map`**. `Map.Raw` and `Map.Tree` stay public for code that wants the raw structure; a canonical `Map.toRaw` that *rebuilds* a representative (e.g. `Raw.fromList (toList m)`) is allowed, at `fromList`'s cost, O(n log n · c_k) (O(n) only if a linear builder for already-sorted entries is added) |
| iterators (none today) | must expose no representation-dependent state |
| `Show` | already prints `Map.fromList` in key order [checked: `Map.sw:619`] |

`Set` gets the same table through its `Map`.

## 13. Run-time representation and performance

### 13.1 "Zero overhead", qualified

- **`Quot` itself is free**: `Quot.mk` erases to its argument and `Quot.lift f h q` to `f q`
  (§7.4).
- **The extra record isn't, today.** Records are objects `{ …fields }` in generated JS
  [checked: `core.md:399`], and the Rust runtime boxes any constructor with at least one run-time
  field (`Value::Data(tag, fields)` [checked: `crates/rt/src/value.rs:36-37`; `crates/rt/src/lower.rs:740-746`]);
  a one-field record such as `SafeNat` is "a record with one field" inside generated code
  [checked: `crates/js/src/lib.rs:2846-2851`]. Today a map is one box around the tree (`{ tree }`;
  `ordered` and `sized` are erased). `Map = { raw: Quot (Map.Raw …) … }` would be
  `{ raw: { tree } }`: **one more box per map and per update**. The prototype and stage 2 accept
  this: the claim is "no quotient overhead; one extra pointer per map".
- **Unboxing records with exactly one run-time field (D866) is a separate, optional
  optimisation**, not a prerequisite for anything here. It would make `Map` exactly its tree at
  run time (and help `Set`, `SafeNat`), but it changes the representation of every such record,
  so it gets its own lane and its own checks, all of which must agree on one layout decision:
  1. **construction** (`Term::Ctor` lowering) and **constructor values** (a constructor used as a
     function, partially applied);
  2. **projection** and **pattern matching** (`case` on the record binds the field to the value
     itself);
  3. **erased fields and arguments**: "one run-time field" counts with the same relevance
     analysis everywhere (`Ctor::field_erased`), including for **polymorphic and dependent
     records**, where the count must come from one shared function, not be recounted per call
     site;
  4. **boundary codecs**: the JS wrapper must *unbox* when decoding and *rebox* when encoding, so
     `type SafeNat = { value: Nat }` with `export def bump (x: SafeNat): SafeNat` still accepts and
     returns `{ value: bigint }` while being a bare `bigint` inside; the current codecs don't do
     this by themselves (draft 2's "the codecs translate anyway" was not checked), and the fast
     per-type codecs need the same;
  5. the map literal printer and anything else that reads a record's field 0 (§13.2);
  6. differential tests (Rust runtime, JS, reference) over records with one run-time field,
     including erased-field and polymorphic cases.

### 13.2 JS boundary

The wire format is unchanged: decoding builds a map with the library's `Map.fromList` and encoding
walks `Map.toList` (`MAP_SHAPE` [checked: `crates/js/src/lib.rs:996-999`; `crates/js/src/fast.rs:289-343`]).
Two places need updating:

- **Recognition**: `Boundary::Map` is chosen for the registered builtin `Map` with arguments
  `[key, value, order]` [checked: `lib.rs:321-341`; `crates/core/src/registry.rs:203-208`]. If the
  revised `Map` keeps those parameters, recognition is unchanged; the registry entries for
  `Map.fromList`/`Map.toList` must point at the new definitions.
- **Literal printing**: `boundary_literal` reads a map value's field 0 as the tree and walks `Bin`
  nodes (`map_entries` [checked: `lib.rs:3816-3820`, `:3892-3910`]). It must go through the
  quotient (evaluate `Map.toList`, or look inside `Quot.mk`).

### 13.3 Complexity

`n` entries; `c_k`, `c_v` the cost of comparing keys and values. **Balance assumption** (§12.1):
the map is reachable from balanced base cases through balance-preserving operations; balance is
not certified, so a forged unbalanced raw map, and anything shape-preserving built from it (`map
id`), can be slower, never wrong.

| Operation | Cost | Condition |
|---|---|---|
| `get`, `contains`, `getOr` | O(log n · c_k) | balance assumption |
| `insert`, `insertWith`, `remove`, `alter`, `adjust` | O(log n · c_k) | balance assumption |
| `size`, `isEmpty` | O(1) | cached sizes correct: certified (`sized`) |
| `toList`, `keys`, `values`, `foldLeft`, `map` | O(n) | — |
| `fromList`, and a rebuilding `toRaw` (`Raw.fromList (toList m)`) | O(n log n · c_k) | O(n) for `toRaw` only with a linear builder for sorted entries, not planned |
| `union a b`, `filter` | O(\|a\| log(\|a\|+\|b\|)), O(n log n) as written today (fold of inserts [checked: `Map.sw:551-557`]) | — |
| `==` (`DecEq`), `compare` | O(n · (c_k + c_v)) time; **O(n) allocation** for both entry lists in an eager runtime, even when the first entries differ | — |
| a map as a key of an outer map | O(log N) comparisons, **each** up to O(n · (c_k + c_v)) | — |

Equality through `toList` is a reasonable first implementation. Later, an ordinary Stitchwort
function could compare two in-order traversals lazily (stopping at the first difference, with no
lists built) and be proved equal to the list specification: same proof architecture, no trusted
substitution [inferred]. Kernel-time costs add one `lift` step per operation.

### 13.4 Hashing

- **Content hashing** (`crates/core/src/hash.rs`) identifies declarations and terms, so two equal
  maps written differently can hash differently; that's correct, because it's about terms, not
  values. The new term formers get one tag each (A4).
- **Semantic value hashing** (a future `Hash` interface) must respect `=`: hash the entries
  (`toList`), never the tree shape. Then `x = y -> hash x = hash y` holds by congruence.

## 14. Stages, tests and risks

### 14.1 Stages

| Stage | Contents | Gate |
|---|---|---|
| 0 (**done**, D771) | `Map.Equiv`, agreement and respects lemmas, `Map.same [DecEq v]` with `sameIff`, the `sized` field, the invariant and API audits, the recursive check; [Stage 0 results](#stage-0-results) | passed |
| 1 | **Kernel quotients**, in the steps below: the calling-convention fix (D922); the term family with the rejection tests written first; computation; erasure and runtimes; the library lemmas and elaborator policy; the axiom report and wording; a prototype map | **first gate** (end of step 1.1): every kernel rejection test refused for its stated reason before anything is accepted. **Final gate** (end of step 1.6): all R and A tests, then the eight properties (§14.2) on the prototype |
| 2 | `Map` and `Set` become quotients: `Map.Raw` is today's record renamed (§8.1); every operation lifted with its stage-0 respects lemma; `DecEq`, `Ord`, `ext`, `insertComm`, `insertGet`; maps.md's API additions; codec and literal-printer updates (§13.2); users fixed (day 8, `dictionary.sw`, `map-set.sw`) | existing map tests, extraction tests, AoC proofs |
| separate, optional | D866 record unboxing (§13.1), with its own checks | its own lane, not a prerequisite |
| separate, later | the constant-motive `J` rule (D924); a recursive-through-quotient design (§11.3); certified balance | each its own proposal |

**Stage 1, step by step.** Each step's exit tests pass before the next step that depends on it
starts. Step 1.0 is independent of the rest and can run in parallel with 1.1–1.2; 1.5 needs only
1.1.

- **1.0 Calling convention for function values (D922).** Independent of quotients. In
  `crates/rt/src/lower.rs` (`apply_def`) and `crates/js/src/lib.rs` (`def_ref`): a reference to a
  definition that leaves at least one *erased* parameter unsupplied lowers to a closure over all
  of its remaining parameters, erased ones accepted and ignored; saturated calls, and partial
  applications whose remaining parameters are all run-time, keep today's convention.
  **Exit:** A0.
- **1.1 The form, its checks, and the rejection suite — tests first.** First write the rejection
  tests, each asserting its final error code and naming the check (C1–C6) or rule it exercises:
  R1–R3, R5–R9 and R11–R14 as kernel tests over hand-built core terms (a new
  `crates/core/tests/quot.rs`, in the style of `kernel.rs`), and each with surface syntax also as
  an `examples/soundness/` file paired with a nearby accepted program (the suite's convention,
  `examples/README.md`). Then add `Term::Quot(QuotForm, args)` and its `Value` forms with every
  traversal of §7.7's table (including the `term.rs` unit tests), its hash tags, pretty-printing,
  the check-cache codec, and the built-in surface names with their implicits; then the typing of
  §7.1 with C1–C6, in every checker path. No computation rule yet. **Exit (the first gate):**
  every listed R test is refused with its stated code and for its stated reason (not, say, an
  `E-MALFORMED` from a missing case); R7 and R8 are refused trivially here and re-run after 1.2;
  the existing kernel, elaboration and hash tests pass.
- **1.2 Computation and conversion.** The `lift` rule (§7.2) in `value.rs` (evaluation, quoting,
  conversion) and `reference.rs`; structural conversion with parameters compared; the unfolding
  policy with its condition. **Exit:** A1, A4, A8; R7 and R8 still refused; the evaluator's
  differential tests (`crates/driver/tests/differential.rs`) extended with quotient terms.
- **1.3 Erasure and the runtimes.** D921's flags (recomputed by the checker, not hashed);
  the reference evaluator's placeholders for `sound`, `ind` and erased-result lifts (D862);
  `rt` and JS lowering as §7.4.1–§7.4.2. **Exit:** A3, A5, A6, A7, each compared across
  `run --reference`, `test`, `run` and `run --js`; the erasure on/off comparisons
  (`crates/driver/tests/erasure.rs`) extended with them.
- **1.4 Library lemmas and elaborator policy.** `ProofBox`, `Quot.funext`, `Quot.funextProp`,
  `Quot.exactDec` at `Type 0` (§8.6–§8.8), in a std module loaded on use; the elaborator messages
  for R2 (matching on a quotient) and R10 (§11.2), and R4's policy. **Exit:** A2, A10; R2, R4 and
  R10 with their messages.
- **1.5 Axiom report and wording.** `stitchwort axioms <name>` per D864 and D925; the wording
  changes of §9.4 in DESIGN.md, core.md and `erase.rs` (D863); core.md's "Quotients" section.
  **Exit:** A9.
- **1.6 Prototype and the final gate.** `ProtoMap k v := { raw: Quot (Map k v) Map.Equiv }` in
  `examples/accept/`, over **today's** `Map` record as the representative (it already is
  `{ tree, ordered, sized }`, and stage 0's respects lemmas are about it), with lifted `toList`,
  `get`, `insert`, `size`, `foldLeft`, and `eqIffToListEq`, `toListInjective`, `ext`, `DecEq`,
  `Ord`. **Exit (the final gate):** the eight properties (§14.2). Only then does stage 2 start.

### 14.2 The gate before stage 2: the review's eight properties

1. **Equality computes**: equal entries inserted in different orders give `True`; a changed value
   gives `False` (in the kernel, and under `test`, `run`, `run --js` and `run --reference`).
2. **Equality composes**: `Inventory` and `Map Text (Map Text Nat)` (as `ProtoMap`) get the
   intended `DecEq` with no deriving change.
3. **Extensionality is general**: `ext` and `toListInjective` for a `ProtoMap Nat (Nat -> Nat)`,
   without `DecEq v`.
4. **Ordinary computation survives**: lifted `get`, `insert` and `size` reduce in the kernel
   (`rfl` on maps whose keys and values reduce, §9.2).
5. **Representation can't escape**: R1–R3, R5–R8 and R11–R14 refused by the kernel; R4 by the
   elaborator, with A10 passing.
6. **Computation limits are deliberate**: §9.1's transport (A3) and the ind-only transport (A6)
   are stuck in the kernel and `0` in every runner.
7. **The raw invariant is sufficient**: `size`, `isEmpty` and `foldLeft` lift with stage 0's
   respects lemmas; the forged-size map is not constructible (`map-wrong-size.sw`).
8. **Recursive declarations have a clear outcome**: R10 and R13 refused, R10 with the §11.2
   diagnostic.

### 14.3 Acceptance tests (positive)

"Every runner" means `run --reference`, `test`, `run` (Rust runtime) and `run --js`, comparing
printed output.

- **A0** (D922, step 1.0) Function values with erased parameters, in every runner: §7.4.3's
  `app seven` (7) and `app2 pick` (42); a definition whose erased parameter follows a run-time one
  (`def pickLate (n: Nat) (a: Type): Nat`, passed as `Nat -> Type -> Nat`); the same with
  lambdas in place of the definitions; and a definition partially applied past its erased
  parameter (`app3 (pick Nat)` with `def app3 (f: Nat -> Nat): Nat := f 41`, unchanged
  convention).
- **A1** `rfl: Quot.lift f h (Quot.mk a) = f a`, for `B` data in `Type 0` and `Type 1`, `B := Prop`
  and `B : Prop`; carriers in `Type 0`, `Type 1` (`Quot (Type 0) R`) and the universe `Prop`
  (`Quot Prop R : Type 0`).
- **A2** `Quot.funext`, `Quot.funextProp` (§8.7's sketch, completed) and `Quot.exactDec` check.
- **A3** §9.1's `n`: `rfl: n = 0` is `E-REFL`; `test "n" := n == 0` passes under `test`; every
  runner prints `0`; the same with `Quot.sound` written inline in a `def` (D862).
- **A4** Content hashes of `Quot.ind …` and `Quot.sound …` with the same arguments differ; the five
  forms round-trip through the check cache; a term's hash doesn't depend on D921's flags.
- **A5** §7.4.3's proof-valued lift consumed by `J`, inline and through `def p`: every runner gives
  `0`; `rfl: nInline = 0` is accepted in the kernel.
- **A6** §7.4.4's ind-only transport (no `Quot.sound`), inline and through `def p`: `rfl: n = 0` is
  `E-REFL`; every runner gives `0`.
- **A7** §7.4.2's `answer` is `7` in every runner, with the lifted function a definition
  (`seven`), a lambda (`a => 7`), and a variable: `def liftWith (g: Type 0 -> Nat) (q: QTy): Nat
  := Quot.lift g (a b h => J (b' h' => g a = g b') rfl h) q`, called as `liftWith seven (Quot.mk
  Nat)` (needs A0).
- **A8** With `def observe (q: Q') := Quot.lift f respects q`: `rfl: observe q = Quot.lift f
  respects q` is accepted for a variable `q`; `Quot.funext` proved through named helper
  definitions for its evaluation and rebuilding steps checks; goals display `observe q` folded.
- **A9** `stitchwort axioms` reports `Quot.sound` for a `def` whose body contains an inline
  `Quot.sound` node, and for one that reaches it only through a theorem's proof; reports nothing
  for a definition using neither, including A6's `n` (which uses `Quot.ind` only).
- **A10** With a lawful `DecEq Q` for `Q := Quot Bool AllTrue` (its `decide` always answers `Yes`,
  the proof by two `Quot.ind`s and `Quot.sound`) and `type Box = { q: Q }` deriving `DecEq`:
  `Box (Quot.mk False) == Box (Quot.mk True)` is `True` in the kernel (`rfl`) and in every runner.

### 14.4 By crate

- `core`: the term-former family in `term.rs`, `value.rs` (eval, quote, conv, the unfolding
  policy), `check.rs` (typing with C1–C6, the erasure flags, the positivity path), `erase.rs`,
  `hash.rs`, `pretty.rs`, `reference.rs`, `termination.rs` (§7.7's table); `unify_index.rs` needs
  nothing (stuck by default) but gets R3 and R12; a new `tests/quot.rs`.
- `elab`: built-in names and implicits, unification cases, the R2 and R10 messages, R4's policy,
  the cache codec, the std module with the §8 lemmas.
- `rt`, `js`: D922 first; lowering per §7.4 (flags, `mk` as its representative, computational
  `lift` as the application `f q`, the rest erased); later (stage 2) the map literal printer.
- `driver`/`cli`: `stitchwort axioms`; the cross-runner and erasure tests.

### 14.5 Risks

- **A new kernel extension.** Small but in the trusted base. Mitigated by the rejection tests
  first, the explicit checks C1–C6 tested on hand-built terms (R14), and two external reviews of §7.
- **Missing a decomposition route.** Some future kernel feature (a new unifier rule, record eta,
  a native) could treat `Quot.mk` as a constructor. Mitigated by R1–R3, R5–R8 and R11–R14 staying
  in the kernel test suite.
- **A traversal that forgets the new form** (§7.7): substitution, occurrence checks or conversion
  silently dropping an argument. Mitigated by the `term.rs` unit tests, R13 (relation-only
  occurrence) and the differential tests.
- **Runtime representation disagreements** across the four runners. The pre-existing D922 bug
  shows this is real; mitigated by A0, A3, A5–A7 compared across every runner, and the flags of
  D921 coming from one kernel test (`is_erased`).
- **Stuck transports surprising users** (§9), now from `Quot.ind` as well as `Quot.sound`.
  Mitigated by documentation, `decide`, explicit transport lemmas, and the later constant-motive
  proposal (D924).
- **Balance is assumed, not certified** (§12.1): only performance depends on it.
- **Recursive maps** stay unavailable; if a real program needs them before the later design, the
  workaround is an id-keyed table or a tree/forest pair (§11.2).
- *(Retired by stage 0: "invariant strengthening is real proof work"; `sized` is proved.)*

## 15. The round-2 questions and their answers

Draft 2 asked the reviewer nine questions about §7. The answers, and where draft 3 acts on them:

| # | Question | Answer (review round 2) | Draft 3 |
|---|---|---|---|
| 1 | Are the typing rules complete and sound? | Coherent; make the shared premises and every check explicit; the Type-only carrier needs a different rationale | §7.1 (premises, C1–C6, rationale) |
| 2 | Reduction, conversion, folding policy | Reasonable, if folding never stops conversion comparing a definition with its body; `mk ≡ mk` only at one quotient type | §7.2, A8 |
| 3 | Does §8 need `ind` to compute? | No | §7.3 |
| 4 | Erasure; do closed quotients reach `mk`? | No counterexample, but it's an invariant with premises; erasure must be type-directed for results and representatives; the closed-proof classification is false | §7.4, A5–A7, D921, D922 |
| 5 | Unification and K | The R tests plus restricted elimination, relation checking and no decomposition suffice; add nested-index and relation-mismatch tests | R11, R12 |
| 6 | Constant-motive `J` | Locally sound; keep it separate, with four conditions | §9.3, D924 |
| 7 | Term formers vs constants | Agreed, but every traversal still needs the new form | §7.7 |
| 8 | Plain positivity refusal | Satisfactory; fix the diagnostic's advice | §11.2, R13 |
| 9 | More kernel tests? | Eight targeted tests; R4 is a policy test | §7.6, §14.3 |

## 16. Decisions

All decisions are final (D920: draft 3 applies the second review in full and is signed off with no
third review). Each entry gives the final answer.

Decisions D770–D779, from draft 1:

- **D770: Equality approach for `Map`/`Set`.** **E (kernel quotients), with B as stage 0.** The
  conditions are met: the recursive-type policy (D785, D870) and the computation contract (§9,
  D863) are explicit. *Decided.*
- **D771: Stage 0 first**, with the full raw-invariant and public-observation audit and the
  recursive check. **Done** ([Stage 0 results](#stage-0-results)). *Decided.*
- **D772: `Quot.sound` accounting.** An accepted core axiom; permitted in exports; visible in the
  axiom report (D864, D925); "assumption-free" is relative to the core theory. *Decided.*
- **D773: Term formers vs kernel-known constants.** Resolved by D860–D862: the rules of §7, then
  term formers. *Decided.*
- **D774: `Quot.funext` in std; `rewrite` under binders separate.** Yes, at `Type 0`, with
  `Quot.funextProp` for proof-valued functions (D923); `rewrite` under binders is a separate
  ticket when needed. *Decided.*
- **D775: `Map` keeps `[auto ord: Ord k]` and today's weight-balanced tree.** Yes, with stage 0's
  invariant (D865). *Decided.*
- **D776: maps.md D740/D741/D742/D746 superseded** by D770; its API (D743), JS (D744), `Set`
  (D745), hash-map (D747) and performance (D748) decisions stand. *Decided.*
- **D777: No Boolean `Eq` interface; `==` stays `DecEq`.** *Decided.*
- **D778: A canonical `TrieMap`.** Deferred; if revisited, kernel and run time are benchmarked
  separately. *Decided.*
- **D779: External review before stage 1.** Done twice (rounds 1 and 2); no third (D920).
  *Decided.*

Matt's:

- **D785: The first quotient version rejects types recursive through a quotient/`Map`**, with a
  useful diagnostic; support later via a separately reviewed design. *Decided.*
- **D786: Write draft 2 adopting the first review.** Done.
- **D920: Write draft 3 applying every round-2 point; then the note is signed off and stage 1
  starts.** This draft.

Draft 2's, final:

- **D860: Quotients are one family of kernel term formers** (`Term::Quot(form, args)`),
  level-generic like `Eq` and `J`, every traversal updated (§7.7). *Decided.*
- **D861: The rules of §7.1–§7.2**: shared premises and checks C1–C6; carriers in `Type i` only
  (an initial-scope choice; the universe `Prop` is admitted, a proposition isn't); `lift` into any
  sort, non-dependent; `ind` with a proposition motive and **no computation rule**; one
  computation rule (`lift` on `mk`); structural conversion with parameters compared, no quotient
  eta; folding never changes conversion. *Decided.*
- **D862: Erasure when running**: `Quot.sound`, `Quot.ind` (and, per D921, erased-result lifts)
  are the placeholder in the reference evaluator; in `rt`/JS, `mk a` is `a`'s representation and
  a computational `lift` the type-directed application `f q`. *Decided, as made type-directed by
  D921.*
- **D863: The computation contract (§9) and its wording** in DESIGN.md, core.md and `erase.rs`,
  with §7.4.4's direct erasure contract replacing any classification of closed proofs and §9.2's
  qualification; `J` is not erased in the kernel. *Decided.*
- **D864: `stitchwort axioms <name>`** in stage 1, reporting foundational dependencies (today
  `Quot.sound`), found as D925 says. *Decided.*
- **D865: The representative invariant** is stage 0's `{ tree, ordered, sized }`; balance is not
  certified, and complexity claims carry the stated assumption (§12.1, §13.3). *Decided.*
- **D866: Unboxing records with one run-time field.** **Not part of this design's stages**: a
  separate, optional optimisation with its own checks (§13.1); the prototype and stage 2 use the
  extra wrapper ("no quotient overhead; one extra pointer per map"). *Decided.*
- **D867: The review's eight properties, on the prototype, gate stage 2** (§14.2). *Decided.*
- **D868: Requirements**: `Equiv`/`ext`/injectivity need nothing of `v`; `Map.same`/`DecEq` need
  `DecEq v`; `Ord` needs `Ord v`; both operands share the ordering parameter. *Decided.*
- **D869: No representation-exposing function on `Map`** (no `.tree`, no stored-representative
  `toRaw`, no shape-dependent fold); `Map.Raw`/`Map.Tree` stay public; a rebuilding `toRaw`
  costs O(n log n · c_k). *Decided.*
- **D870: Recursive occurrences through a quotient are refused by the kernel's existing nested
  rule**, occurrences in the relation included (R13), with a quotient-specific elaborator
  diagnostic recommending an id-keyed table or a tree/forest pair (implements D785). *Decided.*

New in draft 3:

- **D921: Type-directed erasure of quotient forms.** The checker records, recomputed on every
  check and not hashed (as `let`'s skip flag), whether a `lift`'s result is erased
  (`is_erased(B)`) and whether an `mk`'s representative is erased (`is_erased(A)`). Erased-result
  lifts are erased whole; a computational lift lowers as the core application `f q` through the
  existing application path, with relevance from `f`'s own type; `mk a` lowers as `a`; a
  parameter of quotient type is never erased (§7.4). *Decided.*
- **D922: Fix function values with erased parameters in `rt` and JS first** (stage 1, step 1.0):
  a definition referenced with an erased parameter still unsupplied lowers to a closure over all
  its remaining parameters. A pre-existing bug, [run] in §7.4.3; test A0. *Decided.*
- **D923: Levels of the library lemmas.** `Quot.funext`, `Quot.funextProp` and `Quot.exactDec` at
  `Type 0`; other levels by restating the proof under a level-suffixed name where first needed;
  universe polymorphism would replace the copies (§8.8). *Decided.*
- **D924: The constant-motive `J` rule is a separate, later proposal**, not part of stage 1, with
  the review's four conditions (§9.3). *Decided.*
- **D925: The axiom report scans checked terms**, bodies and types of every reached declaration,
  theorems and proof arguments included, recognising inline `Term::Quot(Sound)` nodes; it doesn't
  reuse the runtime's `reachable`; an empty report claims no kernel canonicity (§10). *Decided.*

## Sources

Stitchwort (commit `1786944e`): `crates/core/src/{check.rs,unify_index.rs,value.rs,erase.rs,hash.rs,partial.rs,registry.rs}`,
`crates/rt/src/{value.rs,lower.rs}`, `crates/js/src/{lib.rs,fast.rs}`, `crates/elab/src/derive.rs`,
`crates/elab/src/std/core/{DecEq.sw,Ord.sw,CompareData.sw}`, `std/Map/Map.sw`, `std/Set/Set.sw`,
`std/Decidable/Decidable.sw`, `docs/core.md`, `docs/syntax.md`, `DESIGN.md`,
`docs/proposals/{maps,float,integers,proof-irrelevance,calc-rewrite}.md`,
`aoc/src/Aoc/Day08/{Day08.sw,Proofs/Labels.sw}`, `examples/extract/dictionary.sw`. Draft 3
(commit `0805af8a`) additionally read `crates/core/src/{erase.rs,check.rs,term.rs,hash.rs}`,
`crates/rt/src/{erasure.rs,lower.rs,machine.rs}`, `crates/js/src/lib.rs`,
`crates/elab/src/std/core/Equality.sw`, `std/Map/Map.sw` (as changed by stage 0) and
`docs/proposals/float.md` (for the form of a signed-off note).

[run] snippets (release build of `main`): `recursive.sw` (§11.1) and `forged.sw` (§12.1), as
shown in those sections, each importing `Std (Map)` (and `Std.Map.Tree (Tip, Bin)`). Draft 3:
`ho.sw` and `ho2.sw` (§7.4.3), each importing `Std (IO, Nat)` and printing with `Nat.toText`, run
with `stitchwort run`, `run --reference` and `run --js`, `--no-cache`.

The two external reviews (round 1 of draft 1, round 2 of draft 2) were supplied as documents to the
design lanes; their points are recorded in the two "Response to review" tables.

External (fetched 23 October 2026 unless marked as cited by the review):

- Lean: [Basic Classes](https://lean-lang.org/doc/reference/latest/Type-Classes/Basic-Classes/),
  [Maps and Sets](https://lean-lang.org/doc/reference/latest/Basic-Types/Maps-and-Sets/),
  [Quotients](https://lean-lang.org/doc/reference/latest/The-Type-System/Quotients/) (signatures,
  reduction, funext, §5.2 nested occurrences), source in
  [leanprover/lean4 `src/Std/Data`](https://github.com/leanprover/lean4/tree/master/src/Std/Data),
  [TreeMap.DecidableEquiv](https://lean-lang.org/doc/api/Std/Data/TreeMap/DecidableEquiv.html),
  Mathlib [`Data/Finmap.lean`, `Data/Multiset/Defs.lean`](https://github.com/leanprover-community/mathlib4),
  [Lean4Lean](https://arxiv.org/html/2403.14064v3).
- Rocq: [FMapInterface](https://docs.rocq-prover.org/v8.9/stdlib/Coq.FSets.FMapInterface.html),
  [Generalized rewriting](https://rocq-prover.org/doc/master/refman/addendum/generalized-rewriting.html),
  std++ [pmap](https://plv.mpi-sws.org/coqdoc/stdpp/stdpp.pmap.html) and
  [gmap](https://plv.mpi-sws.org/coqdoc/stdpp/stdpp.gmap.html), Appel and Leroy,
  [Efficient Extensional Binary Tries](https://arxiv.org/abs/2110.05063) (JAR 67, 2023; benchmark
  figures cited by the review, from [xavierleroy.org](https://xavierleroy.org)).
- Golovin on uniquely represented data structures (CMU; cited by the review).
- Agda: [Cubical](https://agda.readthedocs.io/en/latest/language/cubical.html),
  [AVL Map](https://raw.githubusercontent.com/agda/agda-stdlib/master/src/Data/Tree/AVL/Map.agda).
- Isabelle: [Mapping](https://isabelle.in.tum.de/library/HOL/HOL-Library/Mapping.html),
  [RBT_Mapping](https://isabelle.in.tum.de/library/HOL/HOL-Library/RBT_Mapping.html),
  [Data Refinement in Isabelle/HOL](https://www.proof.cit.tum.de/~nipkow/pubs/itp13.html).
- F\* [FiniteMap.Base](https://raw.githubusercontent.com/FStarLang/FStar/master/ulib/FStar.FiniteMap.Base.fsti);
  Dafny [map extensionality FAQ](https://dafny.org/dafny/HowToFAQ/FAQMapExtensionality); SPARK
  [a-cofuma.ads](https://gnu.googlesource.com/gcc/+/6fcba9ef23e4261a6279a76890b2c1488cc14d12/gcc/ada/libgnat/a-cofuma.ads).
- Haskell [Data.Eq](https://hackage-content.haskell.org/package/base-4.22.0.0/docs/Data-Eq.html),
  [Data.Map.Strict](https://hackage-content.haskell.org/package/containers-0.8.1/docs/Data-Map-Strict.html);
  [Scala collection equality](https://docs.scala-lang.org/overviews/collections-2.13/equality.html).
- Lower bounds and tries: [Andersson and Ottmann](https://user.it.uu.se/~arnea/abs/andetigh.html),
  [Sundar and Tarjan](https://epubs.siam.org/doi/10.1137/S0097539790189733),
  [Hinze, Generalizing generalized tries](https://www.cs.ox.ac.uk/publications/publication4830-abstract.html),
  [patricia-tree (OCaml)](https://ocaml.org/p/patricia-tree/0.9.0/README.html).

## Stage 0 results

(As the stage 0 lane wrote it. Draft 3 folds its results into §4.3, §8.1, §11.2, §12 and D865;
where they differ, those sections win.)

**Status:** built, 23 October 2026 (D771), on top of commit `73dfec0a`. No kernel change. New
files `std/Map/Spec.sw` (agreement lemmas, `Map.Equiv`, respects lemmas, `Map.same`) and
`std/Set/Spec.sw` (the same for `Set`); one change to `std/Map/Map.sw`, the `sized` field (§S.2).
Example `examples/accept/map-equiv.sw`; reject example `examples/reject/map-wrong-size.sw`. Paths
below are under `crates/elab/src/` unless given in full.

### S.1 Types that reach themselves through a `Map` today (D785)

Both forms are **rejected today**, by the kernel's positivity check, with the same error
[run, commit `73dfec0a`]:

```
type Tree = { name: Text, children: Map Text Tree }
type Tree = | Leaf | Node (children: Map Text Tree)

[E-POSITIVITY] Error: `Tree` is used inside another type
   field `children` has `Tree` inside another type
   Note 1: a data type's fields can contain it only directly, or as the result of a function
   field: whether it's safe inside another type (such as a `List`) would depend on how that
   type uses it, which isn't checked
   Note 2: for a tree whose children are in a list, write two types defined together instead:
   a tree, and a forest of trees
```

`type Tree = { name: Text, children: List Tree }` is rejected the same way: the check refuses
*every* occurrence of the type being defined inside another type's arguments, not only maps
[checked: `crates/core/src/check.rs:2131-2145`]. So no recursion over such a tree can be written
today, structural or `decreasing`, and D785's rule (the first quotient version rejects these) is
**not a regression**. What works today is a pair of types defined together, a tree and a forest
of named children (`examples/accept/mutual-data.sw`), with structural recursion across both.

### S.2 The raw invariant (review §4)

**What `Ordered` certified.** Only key order: `Map.Tree.Within ord lo hi t` says every key is
strictly between the bounds, recursively, and nothing else [checked: `std/Map/Map.sw:159-166`].
It said nothing about the stored sizes or about balance.

**A map with a wrong size could be built.** The record's fields are public and `Tip`/`Bin` are
importable (`import Std.Map.Tree (Tip, Bin)`), so on `73dfec0a` this was accepted [run]:

```
def bad: Map Nat Text := { tree = Bin 5 Tip 1 "a" Tip, ordered = Both (Both Trivial Trivial) (Both Trivial Trivial) }
-- Map.size bad == 5, Map.toList bad == [(1, "a")]                       (tests passed)
-- with `Bin 0 …`: Map.isEmpty is True though toList has one entry      (test passed)
-- Map.toList (Map.singleton 1 "a") == Map.toList bad, but the sizes differ (test passed)
```

So `size` and `isEmpty` did **not** respect "same entries", exactly the review's conditional
concern.

**Fixed: a third field.** `Map` is now
`{ tree, ordered: Map.Tree.Ordered ord tree, sized: Map.Tree.Sized tree }`, where `Sized` says
every node's stored size is `Succ (size l + size r)` [`std/Map/Map.sw:168-182`]. Every operation
is proved to keep it (`binSized`, the four rotations, `rebuildSized`, `balanceSized`,
`insertWithSized`, `deleteMinSized`, `glueSized`, `removeSized`, `mapSized`;
`std/Map/Map.sw:349-437`), and `Map.sizeToList: m.size = m.toList.length` follows
[`std/Map/Spec.sw:262`]. The proof is erased like `ordered`; no algorithm changed, `size` is still
O(1). The hand-built map above is now refused (`examples/reject/map-wrong-size.sw`: `E-REFL`,
"`5` and `1` aren't equal").

**Balance is still not certified.** A hand-built ordered, correctly sized, unbalanced tree is a
valid `Map`. Every result is still right (the proofs never assume balance), but the O(log n) bound
holds only for maps built by the library's operations. Balance as a theorem stays a follow-up
(map-set.md); it is not needed for equality.

**Every public observation, by what it depends on** (after the fix; `Map.sw` lines are
`std/Map/Map.sw`):

| Operation | Where | Depends only on the entries? | Proof |
|---|---|---|---|
| `get`, `getOr`, `contains` | `Map.sw:600`, `:603`, `:605` | yes | `Map.getToList`: `get key m = lookupList key m.toList` |
| `insertWith`, `insert`, `singleton`, `remove`, `alter`, `adjust` | `Map.sw:587-628` | yes (result's entries) | `Map.toListInsertWith`, `…Insert`, `…Singleton`, `…Remove`, `…Alter`, `…Adjust` |
| `fromList` | `Map.sw:642` | yes | `Map.toListFromList` (and `Map.getFromList`) |
| `map` | `Map.sw:649` | yes | `Map.toListMap` |
| `filter`, `union` | `Map.sw:656`, `:660` | yes: they fold over the entries in key order | `Map.toListFilter`, `Map.toListFilterList`, `Map.toListUnion` |
| `toList`, `keys`, `values` | `Map.sw:635-639` | yes; the order is specified: strictly increasing keys | `Map.toListSorted` |
| `foldLeft` | `Map.sw:646` | yes, for any `f` (not only associative ones): the tree fold is in key order | `Map.foldLeftToList` |
| `size`, `isEmpty` | `Map.sw:630`, `:632` | **before: no** (stored size at the root); **now: yes** | `Map.sizeToList` (needs `sized`) |
| `Show` | `Map.sw:723` | yes: prints `toList` | by definition |
| JS boundary | `crates/js/src/lib.rs:2897-2924` | yes: encodes with `Map.toList`, decodes with `Map.fromList` | by definition |
| Effectful traversal, iterators | — | none exist: `Map` has no `each`/monadic fold; `Set.map`, `Set.any`, `Set.count` are `foldLeft`s | — |
| `.tree`, `.ordered`, `.sized`, `Map.Tree.*` on `m.tree` | record fields, `Map.sw:17-166` | **no**: they expose the tree (on `[(1,a)…(4,d)]` inserted forwards the root key is 2, backwards 3 [run]) | — (stage 2's quotient hides them) |
| `Set` operations | `std/Set/Set.sw` | yes, through `Map`'s | `std/Set/Spec.sw` |

Not audited: how the REPL or `eval` prints a `Map` value (they may print the record, tree and
all).

### S.3 `Map.Equiv`, agreement and respects lemmas (option B)

`Map.Equiv m n := m.toList = n.toList` [`std/Map/Spec.sw:483`]. The specification is sorted
association lists, `Map.Spec k v` (a synonym for `List (k, v)`): `insertWith`, `insert`,
`remove`, `mapValues`, `foldLeft`, `fromList`, `filter`, `union`, `alter`, `adjust`, and the
existing `Map.Tree.lookupList` for `get`. The proofs work on `toListOnto` with an accumulator,
so they need no `append` lemmas: rotations don't change the entries (the existing
`rebuildOnto`), and one lemma, `Map.Tree.pastOnto`, carries any list operation that skips smaller
keys past a whole subtree.

**Proved** (all in `std/Map/Spec.sw` unless noted):

- Agreement, one per operation: `toListEmpty`, `toListInsertWith`, `toListInsert`,
  `toListSingleton`, `toListRemove`, `toListMap`, `foldLeftToList`, `getToList`, `sizeToList`,
  `toListFromList`, `toListFilter` (fold form) and `toListFilterList`
  (`= List.filter (e => p e.fst e.snd) m.toList`), `toListUnion` (`a`'s entries inserted into
  `b`'s), `toListAlter`, `toListAdjust`; the generic `toListFold`.
- `Map.toListSorted`: the entries are in strictly increasing key order (so keys are distinct).
  It was a listed follow-up in map-set.md.
- Extensionality: `Map.equivOfGet` (the same `get` for every key gives `Equiv`, through
  `Map.Spec.extLookup` on sorted lists), and its converse `Map.getRespects`. So `Map.Equiv` is
  exactly "the same `get` everywhere", and needs no `DecEq v`.
- `Map.Equiv` is an equivalence (`equivRefl`, `equivSym`, `equivTrans`).
- Respects, each in a few lines from its agreement lemma: `get`, `getOr`, `contains`, `size`,
  `isEmpty`, `keys`, `values`, `foldLeft` (equal results); `insertWith`, `insert`, `remove`,
  `alter`, `adjust`, `map`, `filter`, `union` in both arguments (equivalent results); plus
  `Map.filterCongr` (predicates that agree pointwise give equivalent results, no funext needed).
- `Map.same [auto dv: DecEq v] (m n): Bool := m.toList == n.toList`, with `sameSound`,
  `sameComplete` and `sameIff`. Keys need no extra `DecEq`: the one inside `Ord k` is used. The
  review's point stands: without `DecEq v` there could be no such `Bool`.
- `Set`: `Set.Equiv s t := Map.Equiv s.items t.items`; `toListInsert`, `toListRemove`,
  `sizeToList`; `Set.equivOfContains` and `Set.equivOfToList` (so `Set.Equiv` is "the same keys
  in order", via `()` having one value); respects for `contains`, `toList`, `size`, `isEmpty`,
  `foldLeft`, `insert`, `remove`, `filter`, `union`, `intersect` and `difference` (both
  arguments); `Set.same` (on the key lists, so only the keys' `DecEq`) with soundness and
  completeness.

**Stated in spec form only, or not proved:**

- `union` as a *merge* of two sorted lists, and `fromList` as "sort, keeping the last value per
  key": only the fold forms are proved. They suffice for the respects lemmas; the merge form is
  a list-lemma exercise when something needs it.
- `insert` commuting for different keys and re-inserting a stored value, as `=`: impossible
  before stage 2 (different trees). As `Map.Equiv` they follow from `equivOfGet`; the swap is
  proved in the example (`insertSwap`), not in the library.
- Balance (§S.2).

**Computation.** On closed maps `toList` computes, so `Map.Equiv m n` is `rfl` for maps built in
different orders (`forwardsBackwards` in the example, whose trees differ), and
`Map.sameSound m n (rfl: Map.same m n = True)` works. Written without the ascription,
`Map.sameSound m n rfl` fails with `E-REFL`, the decision stuck at `DecEq.%decide … 10 10`
[run]; the cause is likely that the `auto` argument for `DecEq v` is not yet solved when `rfl`
is checked [unverified].

**Cost.** `Map/Spec.sw` and `Set/Spec.sw` load only when a program uses one of their names;
`Map.Spec` is declared as a type so that dot calls like `xs.filter` on a list don't pull the file
in (`std_library`'s loading test caught that). Hashes: every `Std.Map.*`/`Std.Set.*` entry of the
prelude snapshot moved (58 lines, the `Map` record has a new field), as did every definition in
the hash snapshots that uses a `Map` (`map-set`, `extract-dictionary`, `int-literals-auto`, one
in `extract-string-enums`); 152 prelude entries are new. Nothing else moved.
