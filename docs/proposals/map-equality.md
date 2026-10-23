# Design session: equality of maps (and other types whose natural equality is coarser than their representation)

**Status:** draft 2, 23 October 2026. Design only: nothing is built. Draft 1 (a state-of-the-art
audit and option analysis) had one external review, which kept option E (Lean-style quotients) as
the preferred direction on conditions; this draft adopts the review (D786) and turns E into a
precise kernel proposal. Decisions D770–D779 keep their numbers, with final recommendations;
D785 (recursive maps) is Matt's; new decisions start at D860 ([§16](#16-decisions)). Stage 0
(D771) is being built by a separate lane at the same time; its findings go in a "Stage 0 results"
section that lane adds ([§4.3](#43-stage-0-results)). Written against commit `1786944e`.

It responds to [maps.md](maps.md) draft 1 (D740–D749), whose recommendation for equality, a
canonical *meaning* plus a trusted swap-in of the tree at run time, Matt doesn't want.

Labels: **[checked]** read in the Stitchwort source at the `file:line` given; **[run]** run while
writing this, with the release build of `main` (`target/release/stitchwort`, built 23 October
2026), on the snippet shown; **[cited]** read in the primary source linked (fetched 23 October
2026; for Lean and Mathlib, the `master` branch on that date); **[cited by the review]** stated by
the reviewer with a source, not re-read here; **[inferred]** my reasoning from checked or cited
facts; **[unverified]** believed, not confirmed.

## Response to review

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
| *Disagreement 2.* The review suggests the J/transport limitation needs no kernel mitigation | Agreed for now, but one narrow rule (a `J` whose motive mentions neither the endpoint nor the proof reduces to its base) is sound and would unstick the review's own example. It is not proposed; it's a question for round 2 (§15 Q6) |

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
Then make `Map` the quotient of **today's proved weight-balanced tree**, with its invariant
strengthened as stage 0 finds necessary, by "same entries in key order".

- It is a functional data structure written and proved in Stitchwort, and `m1 = m2` exactly when
  the maps have the same pairs: `Map.eqIffToListEq: m = n ↔ m.toList = n.toList`, for any value
  type, proved directly from the computation rule and `Quot.sound` (§8.2).
- `==` stays lawful `DecEq` (D777), decided by comparing entry lists; records with maps derive
  `==`; `Ord (Map k v)`, `Set (Set k)` and `rewrite` with `=` work.
- At run time `Quot` costs nothing. The extra record around it costs one box per map unless
  single-field records are unboxed (D866, §13.1).

**What the first version doesn't do, deliberately.** It rejects data types that reach themselves
through a quotient (`type Tree = { children: Map Text Tree }`), with a diagnostic (D785, §11);
today's `Map` can't nest either. And closed terms that transport *data* along a quotient equality
can be stuck in the kernel while still running correctly (§9).

**Stages.** 0: `Map.Equiv`, `toList` agreement lemmas, the invariant and API audit (running now,
D771). 1: the kernel rules, rejection tests first, then a prototype map that must pass the review's
eight properties. 2: migrate `Map` and `Set` ([§14](#14-stages-tests-and-risks)).

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

- `Map k v [ord]` is the record `{ tree: Map.Tree k v, ordered: Map.Tree.Ordered ord tree }`. The
  tree is a weight-balanced binary search tree (Adams; Haskell's `delta = 3`, `ratio = 2`), each
  `Bin` node storing its subtree's size, and `ordered` is an erased proof that the keys are in
  order — **and nothing else**: not the sizes, not the balance
  [checked: `crates/elab/src/std/Map/Map.sw:14-17`, `:149-170`]. Rebalancing "keeps the keys in
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

*Placeholder.* The stage 0 lane (D771) adds this section with its findings: the agreement lemmas
proved, the invariant audit, the API audit and the recursive-type check. This draft doesn't
anticipate them except for the two quick [run] checks in §11.1 and §12.1, done to scope the
kernel design.

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
| Keeps today's proved tree | yes | yes | **no** | yes (at run time) | **yes** (invariant possibly strengthened) | yes |
| Arbitrary `Ord k` orderings | yes | yes | only at a sorting cost | yes | yes | yes |
| Recursive maps | no (today) | no | possible (ordinary data) | no | **no in v1** (§11) | no |
| Kernel / trust change | none | none | none | backend substitution | **one term-former family + 1 axiom** | none |
| Closed `rfl` between different builds | no | no | not without proof irrelevance | yes | no (decide instead) | no |
| Kernel-time speed | O(log n) | O(log n) | O(key length) | O(n) | O(log n) | — |
| Run-time speed | today | today | unmeasured (4.4× slower than RB in OCaml, §3.2) | today | today (+1 box unless D866) | — |
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
Everything here is a proposal; nothing is built.

### 7.1 Typing and universes

Five forms. Implicit arguments are shown in brackets as the elaborator presents them; the kernel
sees them filled in, as for every other form [checked: `core.md:81`].

```
Γ ⊢ A : Type i      Γ ⊢ R : A -> A -> Prop
──────────────────────────────────────────────  (Quot)
Γ ⊢ Quot A R : Type i

Γ ⊢ a : A
──────────────────────────────────────────────  (mk)
Γ ⊢ Quot.mk [A] [R] a : Quot A R

Γ ⊢ B : s  (s = Prop or Type j, any j)    Γ ⊢ f : A -> B
Γ ⊢ h : (x: A) -> (y: A) -> R x y -> f x = f y           Γ ⊢ q : Quot A R
──────────────────────────────────────────────  (lift)
Γ ⊢ Quot.lift [A] [R] [B] f h q : B

Γ ⊢ P : Quot A R -> Prop     Γ ⊢ h : (x: A) -> P (Quot.mk x)     Γ ⊢ q : Quot A R
──────────────────────────────────────────────  (ind)
Γ ⊢ Quot.ind [A] [R] [P] h q : P q

Γ ⊢ r : R x y      (x y : A)
──────────────────────────────────────────────  (sound)
Γ ⊢ Quot.sound [A] [R] [x] [y] r : Quot.mk x = Quot.mk y
```

Decisions inside these rules (D861):

- **Carriers are types, never propositions.** `A : Type i`, and `Quot A R : Type i`, the same
  level. A quotient of a proposition would be useless (any two proofs of `A` are already
  interchangeable for every purpose Stitchwort allows) and would add a case to every rule about
  `Prop` [inferred]. So **`Quot A R` is never a `Prop`**, and the existing `Prop`-elimination rule
  (`E-PROP-ELIM`, [checked: `core.md:110`; `check.rs:741-775`]) never meets a quotient.
- **No universe polymorphism is needed.** Like `Eq` and `J`, whose rules hold at every level
  [checked: `check.rs:344-369`, `:599-642`], these are rules, not constants, so `i` and `j` are
  whatever the arguments' types say. A carrier in `Type 1` (a later recursive design, §11.3, might
  want one) works without new machinery.
- **`lift`'s result sort is independent of the carrier's**, and may be `Prop`. Lifting into `Prop`
  is useful here without `propext`: a predicate `p (Raw.toList a)` respects `Raw.Equiv` by
  congruence alone. Lifting into `Type j` with `j > i` is allowed (large elimination); it is
  consistent in the set model [inferred], and `J` already allows it for equality.
- **`lift` is non-dependent** (`B` doesn't mention `q`). Dependent elimination into data can be
  *defined* from `lift` and `ind`, as Lean's `Quot.rec` is, and needs a respects proof up to
  transport; it extracts nothing [inferred]. It isn't needed for maps and isn't proposed now.
- **`ind`'s motive is proposition-valued only.** A motive in `Type` would be dependent elimination
  into data without a respects proof, which extracts representatives (§7.6).
- **`R` is arbitrary** (any `A -> A -> Prop`, not necessarily an equivalence), as in Lean; the
  quotient by `R` is then the quotient by its equivalence closure [cited: Quotients].

### 7.2 Reduction and conversion

- **One computation rule (ι for quotients):**
  `Quot.lift [A] [R] [B] f h (Quot.mk [A] [R] a) ⟶ f a`. It fires on values: whenever `q`
  *evaluates* to a `Quot.mk`, through definitions, `let`, `case` branches or anything else, as a
  `case` does on a constructor [checked: the evaluator's policy, `crates/core/src/value.rs:5-7`].
- **Nothing else computes.** `Quot.lift f h q` with `q` neutral is neutral. `Quot.ind` never
  computes (§7.3). `Quot.sound r` is a neutral proof. `J` on a `Quot.sound` proof is stuck, as `J`
  on any non-`rfl` proof already is [checked: `core.md:137`].
- **Conversion is structural**: `Quot.mk a ≡ Quot.mk b` iff `a ≡ b`; `Quot A R ≡ Quot A' R'` iff
  `A ≡ A'` and `R ≡ R'`; neutral `lift`/`ind`/`sound` forms compare argument by argument (the
  proof argument `h` of `lift` included, as for any other proof argument today: there's no
  definitional proof irrelevance). **No eta for quotients** (no `Quot.lift Quot.mk h q ≡ q`) and
  conversion never consults `R`: deciding `R` is undecidable in general and propositional anyway.
- **Unfolding policy** [inferred; an implementation requirement]. A definition whose body is a
  `Quot.lift` on its argument (`Map.get k m`) should stay folded on an open `m`, as a definition
  whose case tree can't step does [checked: `value.rs:5-7`, `core.md:196`], so goals show
  `Map.get k m` rather than the lifted term. The simplest rule: `Quot.lift` counts as a case on its
  quotient argument for "can this case tree take a step". This changes only when things are
  computed, not what is equal.

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
**`Quot.ind` has no computation rule** (D861). It costs nothing: `ind` produces proofs, and the only
things that look inside a proof are a `case` on a one-constructor proposition, `J` and comparison
[checked: `core.md:198`]. A proof built with `ind` can block a `J`, exactly as `Quot.sound` can
(§9).

### 7.4 Erasure

| Form | Kernel checker | Running in the kernel's evaluator (`run --reference`, `test`) | Rust runtime (`crates/rt`) and JS |
|---|---|---|---|
| `Quot A R` | a type | erased (a type former) | erased |
| `Quot.mk a` | a value | as in the checker (any representation that keeps the `lift` rule) | `a` itself |
| `Quot.lift f h q` | the rule above | the rule above; `h` is an erased argument | `f q` |
| `Quot.ind h q` | neutral | **the erased placeholder** | erased (a proof) |
| `Quot.sound r` | neutral | **the erased placeholder** | erased (a proof) |

The two bold entries are a finding of this draft (D862). The evaluator's erasure rule 4 is "`J` on
the placeholder takes its base", justified by "in a closed program every proof of an equation is
`refl`" [checked: `crates/core/src/erase.rs:14-15`]. A proof made by a theorem is already the
placeholder when running (a definition whose result is erased isn't run [checked: `erase.rs:11-13`]),
but `Quot.sound r` written inline in a `def`'s body is a term former, not a theorem. If it evaluated
to a neutral proof, `J` on it would stay stuck *at run time*. Making it the placeholder fixes that.
The justification then changes: a closed proof of `x = y` is `refl` **or built from `Quot.sound`**,
and in both cases `x` and `y` denote the same value in the model, so the base is the right result
(§9.4 has the wording).

**Closed quotient values reach `Quot.mk` when running** [inferred]: the only introduction form is
`mk`; `lift` returns `f`'s result; `J` on the placeholder returns its base; `case` and `NumCase`
return their branches. So erased evaluation of a closed `Quot A R` always ends at some `Quot.mk a`,
and `lift` never sticks at run time. In the Rust runtime and JS, `Quot.mk` is the identity, so this
is automatic.

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
  dedicated diagnostic (§11).
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
forbidden behaviour gets a kernel test (directly with kernel terms, and through the elaborator where
there's surface syntax). Each must be refused, *and* the kernel must refuse the hand-built core term,
so the elaborator isn't trusted for it.

| # | Forbidden behaviour | Why the design excludes it | Rejection test |
|---|---|---|---|
| R1 | Constructor injectivity / no-confusion for `Quot.mk` | `Quot.mk` isn't a constructor: no `Value::Ctor`, no `case`, so the prelude's injectivity and disjointness lemmas (proved by `case` + `J` [checked: `core.md:379`]) can't be written for it | A proof of `False = True` from `same` via a projection `Q -> Bool` defined by `case`: refused at the `case` (R2). A `Quot.mk False = Quot.mk True -> Void` "no-confusion" lemma: unprovable (no test can show unprovability; R2–R4 cover each route) |
| R2 | Pattern matching that extracts the representative | `case` needs a data type (§7.5) | `def rep (q: Q): Bool := match q with \| Quot.mk b => b` refused (elaborator: a new message, "a quotient can't be matched on: use `Quot.lift` with a proof that the result respects the relation"); the core `Case` on a `Q` variable refused by the kernel (`E-MALFORMED`) |
| R3 | Index unification decomposing `Quot.mk` | Constraints at a quotient type are stuck (§7.5) | `type At: Q -> Type = \| AtF: At (Quot.mk False) \| AtT: At (Quot.mk True)`; `def only (a: At (Quot.mk False)): Nat` covering only `AtF` must be `E-INDEX-STUCK`, *not* accepted with `AtT` impossible; and a `case` whose branch would need `False = True` from `Quot.mk False = Quot.mk True` mustn't get it |
| R4 | Structural equality derivation on `Quot` | `derive.rs` derives only for data types with `DecEq` fields [checked: `derive.rs:9-20`]; no generic `DecEq (Quot A R)` instance is provided (none can be lawful in general) | `type Box = { q: Q }`; `b == b` is `E-INSTANCE-NONE` naming the field `q` |
| R5 | A projection back to the stored `A` | None exists: `lift` (needs a respects proof) and `ind` (proposition motive) are the only eliminators | `Quot.lift (b => b) h` must need `h: (x y: Bool) -> AllTrue x y -> x = y`, unprovable; a term passing anything else is `E-TYPE-MISMATCH` |
| R6 | `Quot.ind` into data | `ind`'s motive must be a proposition (§7.1) | `Quot.ind [P := _ => Bool] (b => b) q` refused (`E-UNIVERSE`/`E-TYPE-MISMATCH`) |
| R7 | `Quot.ind` computing | No rule (§7.3) | `rfl: Quot.ind [P] h (Quot.mk a) = h a` refused with `E-REFL` |
| R8 | Conversion identifying related representatives | Conversion is structural (§7.2) | `rfl: (Quot.mk False: Q) = Quot.mk True` refused with `E-REFL` |
| R9 | A quotient of a proposition | Carriers are types (§7.1) | `Quot (0 = 0) (x y => Unit)` refused (`E-UNIVERSE`) |
| R10 | A data type recursive through a quotient | §11 | `type T = \| Node (kids: Quot (List T) R)` and `type Tree = { children: Map Text Tree }` refused, with the §11.2 diagnostic |

**The outer record keeps ordinary record rules** (review §2). For `Map = { raw: Quot … }`, the
generated `Map.ext` and record injectivity hold: `{ raw = q1 } = { raw = q2 }` gives `q1 = q2`.
What's forbidden is the next step, from `Quot.mk a = Quot.mk b` to `a = b`, and R1–R5 cover it.
Positive tests sit beside them: `Quot.lift f h (Quot.mk a)` is `rfl`-equal to `f a` (A1);
`Quot.funext` is provable (A2); the transport example of §9.1 is stuck in the kernel and gives `0`
under every runner (A3); two different quotient forms hash differently (A4).

### 7.7 Representation: one term-former family (D860, resolving D773)

| | Kernel-known constants (like `Effect.Delay`) | Term formers (like `Eq`/`J`) |
|---|---|---|
| Universes | fixed: without universe polymorphism, `Quot` would be at `Type 0` only, and `lift` would need one constant per result sort (`Prop`, `Type 0`, …), since `Prop` isn't a `Type 0` [checked: `core.md:22`, `:62`] | level-generic, like `Eq` and `J` [checked: `check.rs:344-369`, `:599-642`] |
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
implicits shown in §7.1.

### 7.8 Trust contract

1. **Consistency.** Read `Quot A R` as the set of equivalence classes of `A` under the equivalence
   closure of `R`; `mk` as the class map; `lift f h` as the function on classes (well defined by
   `h`); `ind` as true because every class has a representative; `sound` as true. Propositions are
   read as empty or one-element sets, so K, impredicative `Prop`, `J` into data and the absence of
   definitional proof irrelevance are all validated [inferred; the review gives the same outline and
   stresses it isn't a verification of Stitchwort's whole calculus]. The `lift` rule holds in the
   model by definition. A computing `ind` would also hold in this model (it validates proof
   irrelevance), which is why §7.3 is about commitments, not consistency.
2. **Preservation.** `rt` and JS implement `mk` as the identity and `lift f h q` as `f q`; erased
   evaluation agrees (§7.4). Tested by the existing differential tests plus A3.
3. **What's trusted additionally**: the five typing rules, the one computation rule, the erasure
   rows, and the axiom. DESIGN.md §13's trusted list and core.md gain a "Quotients" section.

## 8. `Map` as a quotient

### 8.1 Definitions

```
-- Today's record, renamed; its invariant possibly strengthened by stage 0 (§12.1).
type Map.Raw (k: Type) (v: Type) [auto ord: Ord k] =
  { tree: Map.Tree k v, ordered: Map.Tree.Ordered ord tree }

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

The branch is chosen by comparing lists, which computes in the kernel whenever both maps do.
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
other quotients (rationals, unordered pairs).

### 8.7 Function extensionality (D774)

`Quot.funext: ((x: a) -> f x = g x) -> f = g`, by quotienting functions by pointwise equality:
evaluation at each `x` respects it, `Quot.sound` identifies the classes, and the `lift` rule plus
function eta identify the rebuilt functions with `f` and `g` [cited: Quotients; checked eta:
`core.md:201`]. It needs neither `propext` nor proof irrelevance. It gives propositional funext,
not a decision procedure; `rewrite` under binders is a separate elaborator change.

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
that every closed pure term reduces to data in the kernel (§9.4).

### 9.2 What still computes

- Every lifted map operation: `Quot.lift f h (Quot.mk raw) ⟶ f raw`, so `get`, `insert`, `toList`,
  `size`, folds compute in the kernel on closed maps exactly as today (plus one step per lift).
- `==` and `compare` on closed maps: the decision chooses its branch by list comparison (§8.3).
- Proofs about closed maps by decision: `Map.ext` plus a decided `==`, or `auto`.

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
  base and the result have different types unless the endpoints are convertible. A narrow rule for
  *constant* motives would be sound and would unstick §9.1's example; it isn't proposed (§15 Q6).

### 9.4 Wording changes (D863)

A search of DESIGN.md and docs/ finds no blanket "every closed term reduces to data in the kernel"
promise [checked: `grep -n -i 'canonic\|normal form\|every closed\|closed term' DESIGN.md`]. The
statements that need precise wording:

| Where | Today | Change |
|---|---|---|
| DESIGN.md:138 "Total" | "evaluating `t` reaches a value in finitely many steps" | add: "evaluating means running, with proofs and types erased (§6). The checker's evaluator, which doesn't erase, also terminates, but a closed term that transports data along an equality proved by `Quot.sound` may stop at a term that isn't a value" |
| DESIGN.md:123 "Assumption-free" | tracked assumptions only | "relative to the core theory, which includes the quotient axiom `Quot.sound`" (§10) |
| core.md:137 (`J`) | "With any other proof it's stuck." | add: "In a closed term that can still happen, with a proof built from `Quot.sound` (see Quotients)" |
| core.md:203 and `crates/core/src/erase.rs:14-15` | "in a closed program every proof of an equation is `refl`" | "a closed proof of `x = y` is `refl` or built from `Quot.sound`; either way `x` and `y` are the same in the model, so the base is right. `Quot.sound` and `Quot.ind` evaluate to the placeholder when running" |
| core.md (new "Quotients" section, and the Terms table) | — | §7.1–§7.5 |

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
  declaration reaches through its references (today only `Quot.sound`; later `assume`s and the
  handler conjecture fold into the same walk, which becomes DESIGN.md's `assumptions`). It's a
  traversal of the checked declarations' references, cached by content hash; it trusts nothing new.
- K and `J` are rules of the core, not axioms, and aren't listed.

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
be recursive through a quotient yet. Store the children in a separate structure keyed by an id, or
use a list of pairs." Rejection test R10.

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
proof does. Three requirements, which stage 0 audits (§4.2):

1. **Ordering** — needed for lookup and sorted-entry lemmas. Certified today
   [checked: `Map.sw:167-170`].
2. **Correct cached metadata** — needed by every observation that reads it. **Not certified today**,
   and it matters [run]:

   ```
   def honest: Map Nat Text := Map.singleton 1 "a"
   def forged: Map Nat Text :=
     { tree = Bin 7 Tip 1 "a" Tip, ordered = Both (Both Trivial Trivial) (Both Trivial Trivial) }
   test "same entries"     := Map.toList honest == Map.toList forged    -- passes
   test "honest size is 1" := Map.size honest == 1                      -- passes
   test "forged size is 7" := Map.size forged == 7                      -- passes
   ```

   `Map.size` reads the root's cached size [checked: `Map.sw:526-527`], so it doesn't respect
   `Equiv` over today's record, and the O(1) `size` can't be lifted as it stands.
3. **Balance** — needed for the O(log n) bounds, not for correctness (rebalancing keeps order
   "whatever the sizes say" [checked: `Map.sw:27-30`]). Not certified today.

**So the migration may require strengthening the invariant** (D865). The minimum is cached sizes:
`Map.Raw = { tree, valid: Map.Tree.Valid ord tree }` with `Valid` = ordered *and* every node's size
correct, proved preserved by the operations (rebalancing reads sizes, so this is real proof work).
The alternative, computing `size` as the length of `toList` (O(n)), is worse. Balance is optional
for soundness: without it, complexity claims are "for maps built by the library's operations",
since anyone can build an unbalanced raw tree; with it, they hold for every map. Stage 0's audit
decides; this draft only requires that the decision be explicit. (Lean's well-formedness includes
both [cited by the review].)

### 12.2 The observation table

| Operation | Requirement for the quotient API |
|---|---|
| `get`, `getOr`, `contains`, `insert`, `insertWith`, `remove`, `alter`, `adjust`, `union`, `filter`, `map`, (later) intersection, difference | result depends only on the entries: an agreement lemma with the list spec |
| `size`, `isEmpty` | cached cardinality is correct (§12.1), or computed from entries |
| `toList`, `keys`, `values`, `foldLeft` | traversal and accumulation order specified: ascending key order. `Map.Tree.foldLeft` is an in-order left fold [checked: `Map.sw:136-138`], so it equals `List.foldLeft` over `toList` for **any** callback, associative or not; a fold grouped by tree shape would not be liftable |
| effectful traversal (a future `forEach`/monadic fold) | callback order independent of shape (ascending), as Lean's `Ext` API specifies |
| `.tree`, a stored-representative `toRaw`, root/shape inspection, `splitRoot`-like functions | **must not exist on `Map`**. `Map.Raw` and `Map.Tree` stay public for code that wants the raw structure; a canonical `Map.toRaw` that *rebuilds* a representative (e.g. `Raw.fromList (toList m)`) is allowed, at its O(n) cost |
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
  `ordered` is erased). `Map = { raw: Quot (Map.Raw …) … }` would be `{ raw: { tree } }`: **one more
  box per map and per update**.
- **Proposal (D866): unbox records with exactly one run-time field**, in the Rust runtime and in
  generated JS, as an internal representation rule (the JS boundary codecs translate anyway, so the
  wire format is unaffected). Then `Map` is exactly its tree at run time, one box fewer than today,
  and `Set` and `SafeNat` benefit too. It's a lowering change in `rt` and `js`, not the kernel.
  If it's rejected, the honest claim is "no quotient overhead; one extra pointer per map".

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

`n` entries; `c_k`, `c_v` the cost of comparing keys and values.

| Operation | Cost | Condition |
|---|---|---|
| `get`, `contains`, `getOr` | O(log n · c_k) | balance (§12.1) |
| `insert`, `insertWith`, `remove`, `alter`, `adjust` | O(log n · c_k) | balance |
| `size`, `isEmpty` | O(1) | cached sizes correct (§12.1); otherwise O(n) |
| `toList`, `keys`, `values`, `foldLeft`, `map` | O(n) | — |
| `fromList` | O(n log n · c_k) | — |
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
| 0 (running, D771) | `Map.Equiv`, `Map.Raw.Equiv`, agreement and respects lemmas, `Map.same [DecEq v]` with `sameIff`, the invariant audit (§12.1), the API audit (§12.2), the recursive check (§11.1); results in §4.3 | its own lane |
| 1a | **Kernel rejection tests first** (R1–R10, written against kernel terms, failing for the right reason before anything is accepted), then `Term::Quot` and its `Value`s, typing (§7.1), the `lift` rule (§7.2), erasure (§7.4), hashing, pretty-printing, the reference evaluator, the elaborator's names and messages, `rt` and JS lowering; A1–A4; `Quot.funext`, `Quot.exactDec` | all R and A tests pass; differential tests pass |
| 1b | `stitchwort axioms` (D864); the wording changes (D863); D866 unboxing (if accepted) | — |
| 1c | **Prototype**: `ProtoMap`, a quotient of today's record (with stage 0's invariant), in `examples/`, with `toList`, `get`, `insert`, `eqIffToListEq`, `DecEq`, `Ord` | the eight properties (§14.2) |
| 2 | `Map` and `Set` become quotients; every operation lifted with its stage-0 lemma; `DecEq`, `Ord`, `ext`, `insertComm`, `insertGet`; maps.md's API additions; codec updates (§13.2); users fixed (day 8, `dictionary.sw`, `map-set.sw`) | existing map tests, extraction tests, AoC proofs |

### 14.2 The gate before stage 2: the review's eight properties

1. **Equality computes**: equal entries inserted in different orders give `True`; a changed value
   gives `False` (kernel `test` and every runner).
2. **Equality composes**: `Inventory` and `Map Text (Map Text Nat)` get the intended `DecEq` with
   no deriving change.
3. **Extensionality is general**: `Map.ext` and `toListInjective` for a `Map Nat (Nat -> Nat)`,
   without `DecEq v`.
4. **Ordinary computation survives**: lifted `get` and `insert` reduce in the kernel (`rfl` on
   closed maps).
5. **Representation can't escape**: R1–R8 refused.
6. **Computation limits are deliberate**: §9.1's transport is stuck in the kernel and `0` in
   `run`, `test`, the Rust runtime and JS (A3).
7. **The raw invariant is sufficient**: `size` and folds respect `Equiv` (the forged map of §12.1
   is no longer constructible, or no longer distinguishable).
8. **Recursive declarations have a clear outcome**: R10 with the §11.2 diagnostic.

### 14.3 Acceptance tests (positive)

- **A1** `rfl: Quot.lift f h (Quot.mk a) = f a`, for `B` in `Prop`, `Type 0` and `Type 1`; a carrier
  in `Type 1`.
- **A2** `Quot.funext` checks; `Quot.exactDec` checks.
- **A3** §9.1's `n`: `rfl: n = 0` is `E-REFL`; `test "n" := n == 0` passes under `test`; `run` and
  JS print `0`; the same with `Quot.sound` written inline in a `def` (D862).
- **A4** content hashes of `Quot.ind …` and `Quot.sound …` with the same arguments differ; the
  five forms round-trip through the check cache.

### 14.4 By crate

- `core`: the term-former family in `term.rs`, `value.rs` (eval, quote, conv, the unfolding policy),
  `check.rs` (typing, positivity message hook), `erase.rs`, `hash.rs`, `pretty.rs`, `reference.rs`;
  `unify_index.rs` needs nothing (stuck by default) but gets R3.
- `elab`: built-in names and implicits, unification cases, the R2 and R10 messages, the cache codec.
- `rt`, `js`: lowering (`mk` identity, `lift` application, `sound`/`ind` erased); D866; the map
  literal printer.
- `driver`/`cli`: `stitchwort axioms`.

### 14.5 Risks

- **A new kernel extension.** Small but in the trusted base. Mitigated by rejection tests first and
  the round-2 review of §7.
- **Missing a decomposition route.** Some future kernel feature (a new unifier rule, record eta,
  a native) could treat `Quot.mk` as a constructor. Mitigated by R1–R8 staying in the kernel test
  suite.
- **Invariant strengthening is real proof work** (sizes through rebalancing), the main uncertainty
  in stage 2's cost.
- **Stuck transports surprising users** (§9). Mitigated by documentation, `decide`, and the
  constant-motive question.
- **Recursive maps** stay unavailable; if a real program needs them before the later design, the
  workaround is an id-keyed table.

## 15. Questions for the round-2 reviewer

Focused on the kernel rules (§7):

1. **Typing (§7.1).** Are the five rules complete and sound for this kernel: carriers only in
   `Type i`, `lift` into any sort including `Prop` and larger `Type j`, non-dependent `lift`,
   proposition-only `ind`, arbitrary `R`?
2. **Reduction and conversion (§7.2).** One rule, structural conversion, no quotient eta. Is
   anything missing that funext (§8.7) or subject reduction needs? Is treating `Quot.lift` as a case
   for the unfolding policy safe?
3. **Opaque `Quot.ind` (§7.3).** Agreed it shouldn't compute. Does any use in §8 need it to?
4. **Erasure (§7.4).** `Quot.sound` and `Quot.ind` as the placeholder when running, and the new
   justification for "`J` on the placeholder takes its base". Is the claim that closed erased
   evaluation of a quotient always reaches `Quot.mk` right?
5. **Unification and K (§7.5).** Constraints at a quotient type are stuck unless deletion or
   solution applies. Is deletion by conversion enough, and is there any route to decomposition the
   R tests miss?
6. **Constant-motive `J`.** Would `J (y p => T) d p ⟶ d` when `T` mentions neither `y` nor `p` be
   sound here (it holds in the set model and is propositionally provable)? Worth adding, or does it
   only move the problem?
7. **Term formers vs constants (§7.7).** Is one level-generic family the right call without
   universe polymorphism?
8. **Positivity (§11).** Is the plain refusal (no positivity rule for `Quot`) the right first
   version, and is the "quotient the whole raw recursive type" route the one to design later?
9. **The rejection list (§7.6).** Anything else that should be a kernel test?

## 16. Decisions

Existing decisions, final recommendations (adopting the review's table):

- **D770: Equality approach for `Map`/`Set`.** **[E, with B as stage 0]**, conditional on the
  recursive-type policy (D785, D870) and the computation contract (§9, D863), both now explicit.
- **D771: Stage 0 now**, including the full raw-invariant and public-observation audit and the
  recursive check. **[yes; running; results in §4.3]**
- **D772: How `Quot.sound` is accounted for.** **[an accepted core axiom; permitted in exports;
  visible in dependency/axiom reports (D864); "assumption-free" is relative to the core theory]**
- **D773: Quotients as term formers vs kernel-known constants.** **[resolved by D860–D862: the
  rules of §7, then term formers]**
- **D774: `Quot.funext` shipped in std; `rewrite` under binders separate.** **[yes; separate
  ticket for `rewrite`]**
- **D775: `Map` keeps `[auto ord: Ord k]` and today's weight-balanced tree.** **[yes, subject to
  strengthening the representative invariant (D865)]**
- **D776: maps.md D740/D741/D742/D746 superseded** by D770; its API (D743), JS (D744), `Set` (D745),
  hash-map (D747) and performance (D748) decisions stand. **[yes, now that E's scope and
  restrictions are explicit]**
- **D777: No `Eq` (Bool) interface; `==` stays `DecEq`.** **[yes]**
- **D778: Specialised canonical `TrieMap`.** **[defer; comparison corrected (§5 C, §3.7); kernel
  and run time benchmarked separately if revisited]**
- **D779: External review before stage 1.** **[yes: a round-2 review of §7's complete rules]**
- **D785 (Matt): the first quotient version rejects types recursive through a quotient/`Map`**,
  with a useful diagnostic; support later via a separately reviewed design. **[decided]**
- **D786 (Matt): write draft 2 adopting the review.** **[this draft]**

New:

- **D860: Quotients are one family of kernel term formers** (`Term::Quot(form, args)`),
  level-generic like `Eq` and `J`, not kernel-known constants. **[yes]**
- **D861: The rules of §7.1–§7.2**: carriers in `Type i` only; `lift` into any sort, non-dependent;
  `ind` with a proposition motive and **no computation rule**; one computation rule
  (`lift` on `mk`); structural conversion, no quotient eta. **[yes]**
- **D862: Erasure**: `mk` is the identity and `lift` application in `rt`/JS; `Quot.sound` and
  `Quot.ind` are the erased placeholder when running in the kernel's evaluator. **[yes]**
- **D863: The computation contract (§9) and its wording changes** in DESIGN.md, core.md and
  `erase.rs`; `J` is not erased in the kernel. **[yes]**
- **D864: `stitchwort axioms <name>`**, a reference walk listing axioms reached (today
  `Quot.sound`), in stage 1. **[yes]**
- **D865: The representative invariant is strengthened as stage 0's audit requires**; at least
  cached sizes must be certified for `size` to stay O(1) (§12.1); balance decided by stage 0.
  **[yes; details after stage 0]**
- **D866: Records with exactly one run-time field are unboxed** in the Rust runtime and generated
  JS (internal representation; wire format unchanged). **[yes, recommended; otherwise state "one
  extra pointer per map"]**
- **D867: The review's eight properties, on a prototype map, gate stage 2** (§14.2). **[yes]**
- **D868: Requirements**: `Equiv`/`ext`/injectivity need nothing of `v`; `Map.same`/`DecEq` need
  `DecEq v`; `Ord` needs `Ord v`; both operands share the ordering parameter. **[yes]**
- **D869: No representation-exposing function on `Map`** (no `.tree`, no stored-representative
  `toRaw`, no shape-dependent fold); `Map.Raw`/`Map.Tree` stay public. **[yes]**
- **D870: Recursive occurrences through a quotient are refused by the kernel's existing nested
  rule, with a quotient-specific elaborator diagnostic** (implements D785). **[yes]**

## Sources

Stitchwort (commit `1786944e`): `crates/core/src/{check.rs,unify_index.rs,value.rs,erase.rs,hash.rs,partial.rs,registry.rs}`,
`crates/rt/src/{value.rs,lower.rs}`, `crates/js/src/{lib.rs,fast.rs}`, `crates/elab/src/derive.rs`,
`crates/elab/src/std/core/{DecEq.sw,Ord.sw,CompareData.sw}`, `std/Map/Map.sw`, `std/Set/Set.sw`,
`std/Decidable/Decidable.sw`, `docs/core.md`, `docs/syntax.md`, `DESIGN.md`,
`docs/proposals/{maps,float,integers,proof-irrelevance,calc-rewrite}.md`,
`aoc/src/Aoc/Day08/{Day08.sw,Proofs/Labels.sw}`, `examples/extract/dictionary.sw`.

[run] snippets (release build of `main`): `recursive.sw` (§11.1) and `forged.sw` (§12.1), as
shown in those sections, each importing `Std (Map)` (and `Std.Map.Tree (Tip, Bin)`).

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
