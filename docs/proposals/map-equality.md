# Design session: equality of maps (and other types whose natural equality is coarser than their representation)

**Status:** draft 1, 23 October 2026. Design only: nothing is built. A state-of-the-art audit
followed by an option analysis, written to stand alone for an external reviewer. It responds to
[maps.md](maps.md) draft 1 (D740–D749), whose recommendation for equality, a canonical *meaning*
plus a trusted swap-in of the tree at run time, Matt doesn't want. Decisions D770–D779 are at the
[end](#8-decisions). Written against commit `2185a364`.

Labels: **[checked]** read in the Stitchwort source at the `file:line` given; **[cited]** read in
the primary source linked (fetched 23 October 2026; for Lean and Mathlib, the `master` branch on
that date); **[inferred]** my reasoning from checked or cited facts; **[unverified]** believed, not
confirmed.

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
   free, with no axiom: CompCert's and std++'s binary tries (Appel and Leroy 2023). This works only
   for keys that can be spelled as bits. For general ordered keys, balanced trees can't be
   canonical and stay O(log n) (Andersson and Ottmann's Ω(n^{1/3}) bound).

**Recommendation (§6).** Add **Lean-style quotient types** to the kernel (option E): four
primitives and one computation rule, plus one new axiom, `Quot.sound`. Then make `Map` the quotient
of **today's proved weight-balanced tree** by "same entries in key order".

- This is what Matt asked for. It is a functional data structure written and proved in
  Stitchwort, and it has natural equality: `m1 = m2` exactly when they have the same pairs.
- `==` stays lawful `DecEq`, as D683 kept it for `Float`, so deriving doesn't change: records with
  maps get `==`.
- `Map.ext`, `Ord (Map k v)`, `Set (Set k)`, and rewriting with `=` all work.
- At run time a map is the tree, with zero overhead, and nothing is swapped in by the backends.

Its first stage (agreement lemmas and `Map.Equiv`, option B) is needed by every option, so it can
start now. If the reviewer or Matt rejects a new axiom, the fallback is option A, a lawful-by-relation
Boolean `Eq` interface. It works, but it splits `==` from `=` across the whole language.

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
- `Ord` *contains* a `DecEq` and the law `equal: compare x y = Equal -> x = y`
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
| Kernel-known opaque constants | yes (`Effect.Delay`; Float's bodyless primitives are planned) | [checked: `core.md:12`; `float.md:108-111`] |
| Exports must be assumption-free | yes (`assume`, holes, trusted foreign functions, conjectures) | [checked: `DESIGN.md:123`, `:787`] |

There is no visibility control (no `private`), so any field of a library record, including
`Map`'s `.tree`, can be read by user code [checked: `docs/syntax.md` has no `private`].

### 1.3 `Map` as built

- `Map k v [ord]` is the record `{ tree: Map.Tree k v, ordered: Map.Tree.Ordered ord tree }`. The
  tree is a weight-balanced binary search tree (Adams; Haskell's `delta = 3`, `ratio = 2`), and
  `ordered` is an erased proof that the keys are in order
  [checked: `crates/elab/src/std/Map/Map.sw:1-8`, `:15`, `:167-170`]. `Set k` is a record around
  `Map k ()` [checked: `std/Set/Set.sw:7`].
- Proved today: the tree operations keep `Ordered`, and `get` agrees with a search of the entry
  list (`Map.Tree.getLookup`, `Map.getInsert`, `Map.getFromList`, …)
  [checked: `Map.sw:174-336`, `:391`, `:563`, `:615`].
- **The same pairs in different orders make different trees** [run, maps.md §1.1]:
  `Map.fromList [(1, 1), (2, 2)]` is `Bin 2 Tip 1 (Bin 1 Tip 2 Tip)`, while `[(2, 2), (1, 1)]` gives
  `Bin 2 (Bin 1 Tip 1 Tip) 2 Tip`.
- So a lawful `DecEq (Map k v)` would have to call these two maps *different*. A `DecEq` that says
  "same" can't exist, because it would have to prove two different trees equal. Today `Map` has no
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

### 1.4 Key types real programs use

A grep of `aoc/`, `examples/` and `web/` for `Map K`/`Set K` [checked, 23 October 2026] finds these
key types: `Text` (32 uses), `Nat` (25), `Int` (5), `(Nat, Nat)` (3) and `(Int, Int)` (3). Two
reject tests use `Map (Nat -> Nat)` *values*. There are no custom orderings outside the tests that
check orderings are kept apart (`map-ordering-differs.sw`). So the keys are scalars and tuples of
scalars. That matters for option C.

### 1.5 What Matt wants

- "I'm happy to have a functional data structure implementation of a Map in Stitchwort that we can
  prove the behaviour about." So the tree should stay Stitchwort code with proofs, and nothing
  should be swapped in by a trusted backend step. That rules out maps.md's D741.
- **Natural equality is "the same key–value pairs".**
- Mainstream surface (Scala/TS); no backward compatibility needed; prefer real proofs over
  examples.

## 2. Words used below, with a tiny example

- **Representation equality.** `=` on a data type compares constructors and fields. Two trees with
  the same pairs but different shapes are *not* equal.
- **Extensional equality.** Equal when every observation agrees. For maps, observations are `get`:
  `(key: k) -> m1.get key = m2.get key`. For ordered maps that is the same as
  `m1.toList = m2.toList` [inferred: keys are unique and sorted, so `toList` is determined by `get`].
- **Setoid.** A type paired with an equivalence relation (here `Map.Equiv`) that proofs use
  instead of `=`.
- **Congruence ("respects").** A function `f` respects `Equiv` if `Equiv m1 m2` implies
  `f m1 = f m2`, or `Equiv (f m1) (f m2)` when `f` returns a map. Rewriting with `Equiv` is only
  sound inside functions that respect it. `Map.insert` does; a function that reads `.tree` doesn't.
- **Quotient.** A type former `Quot A R` whose values are `A`s, but where `R`-related values are
  *equal* (`=`). A function can be applied to it only by proving that the function respects `R`.
- **Canonical representation.** Only one value of the type represents each meaning. Then
  representation equality *is* extensional equality, with nothing added to the logic.

## 3. State-of-the-art audit

### 3.1 Lean 4 (core `Std` and Mathlib)

- **Three equality classes.** `BEq α` is a Bool `==` that "does not have any axioms like being
  reflexive or agreeing with `=`". `LawfulBEq` adds `eq_of_beq` ("If `a == b` evaluates to `true`,
  then `a` and `b` are equal in the logic") and `rfl`. `ReflBEq` and `EquivBEq` sit in between.
  `DecidableEq` is `Decidable (a = b)`. `LawfulHashable` says `a == b → hash a = hash b`, "automatic
  if the `BEq` instance is lawful" [cited: [Lean reference, Basic Classes](https://lean-lang.org/doc/reference/latest/Type-Classes/Basic-Classes/)].
- **Maps.** `HashMap`, `DHashMap`, `TreeMap` and `DTreeMap` (a "size-bounded" balanced tree whose
  balancing code follows Haskell's `Data.Map` [cited: `src/Std/Data/DTreeMap/Internal/Balancing.lean:427-428`])
  bundle their well-formedness proof with the data. `.Raw` versions unbundle it, because "the
  bundling … prevents them from being used in nested inductive types"
  [cited: [Lean reference, Maps and Sets](https://lean-lang.org/doc/reference/latest/Basic-Types/Maps-and-Sets/)].
- **Option 1 in Lean: `BEq` plus `Equiv` on ordinary maps.** `HashMap` has a `BEq` instance that
  "Returns `true` if the maps contain the same key-value pairs"
  [cited: `src/Std/Data/DHashMap/Basic.lean:372-377`; `HashMap/Basic.lean:287-290`]. The relation
  `m₁ ~m m₂` (`Equiv`) relates maps with the same pairs. The lemmas connect them:
  `beq_iff_equiv [LawfulBEq α] [LawfulBEq β] : (m₁ == m₂) ↔ m₁ ~m m₂`,
  `Equiv.beq_congr`, congruence lemmas `Equiv.union_congr`, `Equiv.inter_congr`,
  `Equiv.diff_congr`, … and `equiv_iff_toList_perm`
  [cited: `src/Std/Data/HashMap/Lemmas.lean:1399-1409`, `:1456-1466`, `:3043-3045`]. For tree maps,
  `Equiv` holds "iff all the keys and values are equal" [cited: [DTreeMap Internal Queries docs](https://lean-lang.org/doc/api/Std/Data/DTreeMap/Internal/Queries.html)],
  and `Decidable (t₁.Equiv t₂)` exists [cited: [TreeMap/DecidableEquiv](https://lean-lang.org/doc/api/Std/Data/TreeMap/DecidableEquiv.html)].
- **Option 3 in Lean: extensional maps by quotient.** `ExtDTreeMap` is a structure whose only field
  is `inner : Quotient (DTreeMap.isSetoid α β cmp)`. Each operation is lifted with
  `lift (f) (h : ∀ a b, a ~m b → f a = f b)`. It "supports all operations from `Std.DTreeMap`" and
  "offers several extensionality lemmas". `DecidableEq` needs
  `[TransCmp cmp] [LawfulEqCmp cmp] [∀ k, LawfulBEq (β k)]`
  [cited: `src/Std/Data/ExtDTreeMap/Basic.lean`]. The hash-map version, by contrast, "lose[s] the
  ability to iterate freely" (no `toList` or `fold`, because bucket order isn't canonical)
  [cited: `src/Std/Data/ExtDHashMap/Basic.lean`]. Users write
  `ext_getElem? (h : ∀ k, m₁[k]? = m₂[k]?) : m₁ = m₂` [cited: `src/Std/Data/ExtHashMap/Lemmas.lean:2339-2341`].
  The reference advises: "extensional maps should be used only when needed for verification"
  [cited: Maps and Sets].
- **Mathlib.** `Multiset α := Quotient (List.isSetoid α)` (lists up to permutation)
  [cited: `Mathlib/Data/Multiset/Defs.lean:69-70`]. `Finset` is a multiset with no duplicates.
  `Finmap β` is `{ entries : Multiset (Sigma β), nodupKeys }`, "effectively a quotient of `AList β`
  by permutation", with `ext_lookup : (∀ x, s₁.lookup x = s₂.lookup x) → s₁ = s₂` and a
  `DecidableEq` [cited: `Mathlib/Data/Finmap.lean:67-76`, `:235`, `:289`].
- **The kernel side.** `Quot` is primitive. `Quot.lift f resp (Quot.mk r x)` reduces to `f x`, and
  `Quot.sound` is "the quotient axiom". Function extensionality is *proved* from it
  [cited: [Lean reference, Quotients](https://lean-lang.org/doc/reference/latest/The-Type-System/Quotients/)].
  Lean's theory, quotients and choice included, is consistent relative to ZFC plus inaccessibles
  (Carneiro, *The Type Theory of Lean*, 2019) [cited: [Lean4Lean paper](https://arxiv.org/html/2403.14064v3) summarising it].
- **Pain points.** Statements need `[BEq α] [LawfulBEq α]` or `[DecidableEq α]`, so core keeps
  parallel lemma versions (for example `Array.isEqv_self` in a `DecidableEq` and a `BEq` form)
  [cited: [Init/Data/Array/DecidableEq](https://lean-lang.org/doc/api/Init/Data/Array/DecidableEq.html)].
  `BEq` instances coming from `DecidableEq` and hand-written ones can disagree definitionally
  (the "BEq diamond") [unverified: widely discussed on Zulip, no primary source found]. Ordinary
  and `Ext` maps are separate types, converted explicitly [inferred from the APIs].
- **Deriving.** `deriving BEq` compares fields with `==`, and `deriving DecidableEq` needs
  `DecidableEq` fields [unverified: the reference lists both handlers without describing them]. So
  a structure with a `HashMap` field can derive `BEq` but not `DecidableEq` [inferred].

### 3.2 Rocq

- **Standard library FMaps/MMaps.** AVL, red-black or sorted-list maps. `=` is structural.
  `Equal m m' := ∀ y, find y m = find y m'` is the setoid, with `Equiv`/`Equivb` for values up to a
  relation and a Bool `equal` specified by `equal_1`/`equal_2`
  [cited: [FMapInterface](https://docs.rocq-prover.org/v8.9/stdlib/Coq.FSets.FMapInterface.html)].
  MMaps works the same way [unverified].
- **Generalized (setoid) rewriting.** The user declares that each function is a morphism, for
  example `Add Parametric Morphism A : (@union A) with signature (@eq_set A) ==> (@eq_set A) ==>
  (@eq_set A)`. A rewrite inside a context fails "unless f has also been declared as a morphism".
  Morphisms are resolved by type classes (Sozeau's implementation)
  [cited: [Rocq manual, Generalized rewriting](https://rocq-prover.org/doc/master/refman/addendum/generalized-rewriting.html)].
  This is the most developed "prove up to `Equiv`" tooling of any system surveyed.
- **std++ `gmap` and CompCert `PTree`: canonical, so `=` is extensional with no axiom.** Both use
  Appel and Leroy's *canonical binary tries*, keyed by `positive` (binary numbers). A non-empty trie
  node has seven constructors, `Node001` … `Node111`, one for each combination of left subtree /
  value / right subtree that is present. An empty subtree simply can't be built, so "there is only
  one value of type tree that represents this set" of bindings
  [cited: [Appel & Leroy, Efficient Extensional Binary Tries, JAR 2023](https://ar5iv.labs.arxiv.org/html/2110.05063)].
  std++'s `Pmap` "satisfies extensional equality, i.e., (∀ i, m1 !! i = m2 !! i) → m1 = m2"
  [cited: [stdpp.pmap](https://plv.mpi-sws.org/coqdoc/stdpp/stdpp.pmap.html)]. `gmap K A` takes any
  `Countable K`: keys are encoded to `positive`, and a proof field `encode <$> decode q = Some q`
  (an equation in a type with decidable equality, so its proofs are unique) marks the valid
  positions [cited: [stdpp.gmap](https://plv.mpi-sws.org/coqdoc/stdpp/stdpp.gmap.html)].
- **What canonical tries cost.** Each function has more cases: `get'`/`set'` have 21, a naive
  `combine'` 49, handled with views or tactics. The earlier fix, a subtype carrying a
  well-formedness proof, was extensional too, but "the proof of wf m grows linearly in the number of
  operations" when computing inside Coq [cited: Appel & Leroy §3-5]. The trie's iteration order is
  the *encoding's* order, not a user ordering [inferred: keys are `positive` bit strings]. In
  std++, folds over maps are specified only up to permutation [unverified].
- **`Eqdep_dec`.** Proofs of equations in a decidable type are unique (Hedberg). It plays the same
  role as Stitchwort's `DecEq.uniqueEq`.

### 3.3 Agda

- **Standard library.** `Data.Tree.AVL.Map` over a strict total order. It defines no map equality
  [cited: [Data/Tree/AVL/Map.agda](https://raw.githubusercontent.com/agda/agda-stdlib/master/src/Data/Tree/AVL/Map.agda)].
  Proofs use `Setoid` records and equational-reasoning combinators [unverified for map-specific
  lemmas].
- **Cubical Agda.** Function extensionality is a one-line theorem (`funExt p i x = p x i`) and
  higher inductive types give quotients. For example, finite multisets are `data FMSet` with a path
  constructor `comm : ∀ x y xs → x ∷ y ∷ xs ≡ y ∷ x ∷ xs` and `trunc : isSet (FMSet A)`
  [cited: [Agda manual, Cubical](https://agda.readthedocs.io/en/latest/language/cubical.html);
  [cubical/HITs/FiniteMultiset/Base.agda](https://raw.githubusercontent.com/agda/cubical/master/Cubical/HITs/FiniteMultiset/Base.agda)].
  It is incompatible with K under `--safe` [cited: Agda manual]. **Not an option for Stitchwort**,
  whose kernel has K [checked: `core.md:140`].

### 3.4 Isabelle/HOL: an abstract type with a concrete tree in generated code

This is the closest precedent for "the logic sees same-pairs equality, the program runs a tree".

- `('a, 'b) mapping` is a `typedef` over partial functions, and HOL has function extensionality,
  so `=` on mappings is extensional [cited: [HOL-Library Mapping](https://isabelle.in.tum.de/library/HOL/HOL-Library/Mapping.html)].
- **Code generation by data refinement.** `RBT_Mapping` declares
  `lift_definition Mapping :: "('a::linorder, 'b) rbt ⇒ ('a, 'b) mapping" is RBT.lookup` and then
  `code_datatype Mapping`. That makes `Mapping`, a *non-injective* function from red-black trees,
  act as the constructor in generated code. The code equations are proved theorems:
  `Mapping.lookup (Mapping t) = RBT.lookup t`,
  `Mapping.update k v (Mapping t) = Mapping (RBT.insert k v t)`, and equality
  `HOL.equal (Mapping t1) (Mapping t2) ⟷ RBT.entries t1 = RBT.entries t2`
  [cited: [RBT_Mapping](https://isabelle.in.tum.de/library/HOL/HOL-Library/RBT_Mapping.html)].
- The trust is in the code generator, which turns proved equations into code (Haftmann, Krauss,
  Kunčar, Nipkow, *Data Refinement in Isabelle/HOL*, ITP 2013; the Lifting and Transfer packages
  move definitions and theorems between the types)
  [cited: [abstract](https://www.proof.cit.tum.de/~nipkow/pubs/itp13.html)].
- **Compared with Stitchwort.** This is maps.md's draft-1 design: an abstract meaning plus a
  trusted substitution, with HOL's built-in extensionality in place of a sorted list. It relies on
  two things Stitchwort lacks: funext, and a code generator trusted to apply refinements.

### 3.5 F\*, Dafny, SPARK, Why3

- **F\*.** `FStar.FiniteMap.Base` (translated from Dafny's prelude) declares `equal m1 m2 : prop`
  (same domain, pointwise agreement) and the fact `equal m1 m2 ==> m1 == m2`, an axiom about an
  abstract type [cited: [FStar.FiniteMap.Base.fsti](https://raw.githubusercontent.com/FStarLang/FStar/master/ulib/FStar.FiniteMap.Base.fsti)].
  `FStar.Map` has the same shape and relies on functional extensionality
  [cited: maps.md §2, [FStar.Map.fsti](https://raw.githubusercontent.com/FStarLang/FStar/master/ulib/FStar.Map.fsti)].
- **Dafny.** `map<K,V>` is built in and `==` on it is extensional, but "Dafny never tries to prove
  extensionality, but it's happy to do it if you ask it to", so users assert pointwise equality
  [cited: [Dafny FAQ](https://dafny.org/dafny/HowToFAQ/FAQMapExtensionality)]. Compiled maps are
  runtime-library immutable maps [unverified].
- **SPARK.** `Ada.Containers.Functional_Maps` defines `"="` as "Extensional equality over maps",
  with a postcondition saying both maps have the same keys and the same values
  [cited: [a-cofuma.ads](https://gnu.googlesource.com/gcc/+/6fcba9ef23e4261a6279a76890b2c1488cc14d12/gcc/ada/libgnat/a-cofuma.ads)].
  These maps are for specification. Executable formal containers relate to them through model
  functions [unverified].
- **Why3** has a logical `fmap` theory with extensionality [unverified].

All four take the verifier route: the abstract map type has extensional equality by axiom or by
built-in decision, and the runtime structure is whatever the compiler picks.

### 3.6 Programming languages: Haskell, Idris 2, Scala/Kotlin, TypeScript

- **Haskell `Data.Map`.** `Eq (Map k a)` compares sizes and then entries in key order
  [cited: maps.md §2, `Data/Map/Internal.hs`]. The `Eq` documentation lists an "Extensionality"
  law: "if `x == y` = `True` and `f` is a function whose return type is an instance of `Eq`, then
  `f x == f y` = `True`" [cited: [Data.Eq](https://hackage-content.haskell.org/package/base-4.22.0.0/docs/Data-Eq.html)].
  `Data.Map` breaks it with a public function. `splitRoot` decomposes "based on the structure of the
  underlying tree", and "No guarantee is made as to the sizes of the pieces"
  [cited: [Data.Map.Strict](https://hackage-content.haskell.org/package/containers-0.8.1/docs/Data-Map-Strict.html)].
  This is exactly how a Bool `==` coarser than the representation leaks.
- **Idris 2.** `SortedMap` derives no laws, and its `(==)` compares `kvList`s
  [cited: maps.md §2, `Data/SortedMap.idr`].
- **Scala.** "Within the same category, collections are equal if and only if they have the same
  elements", for example `HashSet(1, 2) == TreeSet(2, 1)` [cited: [Scala collections, Equality](https://docs.scala-lang.org/overviews/collections-2.13/equality.html)].
  Kotlin and Java `Map.equals` likewise compare entries [unverified].
- **TypeScript/JS.** `Map` has no structural equality. `===` is identity [unverified; well known].

### 3.7 Canonical structures and the lower bound

- **No canonical O(log n) search tree for general ordered keys.** Andersson and Ottmann: for
  uniquely represented dictionaries in bounded-out-degree graphs, "one of the operations search or
  update must require a cost of Omega(n^(1/3))", with a matching O(n^{1/3}) structure
  [cited: [abstract](https://user.it.uu.se/~arnea/abs/andetigh.html)]. Sundar and Tarjan give unique
  binary search trees that are optimal only when the set is "sufficiently sparse or sufficiently
  dense" [cited: [SIAM J. Comput. 23(1), 1994](https://epubs.siam.org/doi/10.1137/S0097539790189733)].
- **Randomised canonical trees.** A treap whose priorities are a hash of the key has one shape per
  key set and expected O(log n) operations. It needs a `Hash` for every key type, and a poor hash
  degenerates it [cited: maps.md §3 (a2)].
- **Tries are canonical for keys spelled as symbols.** Binary tries (PTree/gmap), big-endian
  Patricia trees (Okasaki and Gill 1998, the basis of Haskell's `IntMap`; an OCaml implementation
  notes "inserting nodes in any order will return the same shape"
  [cited: [patricia-tree README](https://ocaml.org/p/patricia-tree/0.9.0/README.html)]), and
  *generalized tries*, which build a map over any first-order algebraic key type from maps over
  its parts (Hinze, JFP 10(4), 2000)
  [cited: [abstract](https://www.cs.ox.ac.uk/publications/publication4830-abstract.html)]. A trie
  is canonical if empty sub-maps are never stored [inferred]. Its traversal order is the order of
  the encoding, which matches a type's natural order only if the encoding is designed to
  [inferred].
- **Hash-consing** (one shared copy per distinct value, so equality becomes pointer comparison)
  needs a global table. It doesn't fit a pure kernel evaluator [inferred].

### 3.8 Summary table

| System | Programmer's `==` on maps | Is `=` extensional? How | Proofs look like | Deriving with map fields | Runtime |
|---|---|---|---|---|---|
| Lean `HashMap`/`TreeMap` | `BEq`, same pairs | no | `~m` plus congruence lemmas | `BEq` yes, `DecidableEq` no | hash table / balanced tree |
| Lean `Ext*`, Mathlib `Finmap` | `DecidableEq` | yes: quotient (`Quot.sound` axiom) | `=` and `ext` | yes | same as non-`Ext` (erased wrapper) [inferred] |
| Rocq FMaps/MMaps | `equal` (Bool, specified) | no | setoid rewriting with `Proper` | n/a | AVL / RB trees |
| Rocq std++ `gmap`, CompCert `PTree` | decidable `=` | yes: canonical trie, no axiom | `=`, `map_eq` | yes | binary trie over `positive` |
| Agda stdlib | none | no | `Setoid` | n/a | AVL |
| Cubical Agda | — | yes: HIT quotients, funext | paths | — | (needs no-K) |
| Isabelle `mapping` | `HOL.equal` → `RBT.entries` equal | yes: funext | `=`, Lifting/Transfer | yes | RB tree via trusted code generation |
| F\*, Dafny, SPARK, Why3 | extensional | yes: axiom / built in | SMT, often with an explicit nudge | yes | runtime library |
| Haskell, Idris 2, Scala | entries equal | — (no proofs) | — | yes (`deriving Eq`) | balanced trees / HAMT |

**Lessons.**

1. Every system that keeps a fast non-canonical tree *and* has extensional `=` pays with a
   quotient, funext or an axiom.
2. Systems without one keep two equalities and need congruence lemmas or setoid rewriting
   everywhere.
3. Canonical tries avoid both, but only for bit-like keys and with many more cases in proofs.
4. A Boolean "same pairs" `==` that isn't `=` leaks as soon as any public function looks at the
   representation (`splitRoot`).

## 4. Common ground: what every option needs (stage 0)

Under every option the library needs the same proofs.

1. `Map.Equiv m1 m2 := m1.toList = m2.toList`. This is equivalent to "same `get` everywhere"
   [inferred: entries are sorted with distinct keys, by `Ordered` and `ord.equal`].
2. An **agreement lemma** for each operation, stating it in terms of the sorted entry list. For
   example, `insertToList: (m.insert k v).toList = Map.Spec.insert k v m.toList`. The `get` side
   already exists [checked: `Map.Tree.getLookup`, `Map.sw:391`].
3. From these, each operation **respects** `Equiv` with no further work. If `m1.toList = m2.toList`,
   rewriting both agreement lemmas gives `(m1.insert k v).toList = (m2.insert k v).toList`
   [inferred].

```
def Map.Equiv (m1: Map k v) (m2: Map k v): Prop := m1.toList = m2.toList

theorem Map.insertRespects (k: k) (x: v) (m1: Map k v) (m2: Map k v) (same: Map.Equiv m1 m2):
    Map.Equiv (m1.insert k x) (m2.insert k x) :=
  rewrite Map.insertToList k x m1, Map.insertToList k x m2, same in rfl
```

This is the substance of maps.md's "agreement theorems" without the swap-in. The options differ only
in what they build on top.

## 5. Options

Each option shows what a user writes and what a proof looks like. `Inventory` is the running
example: `type Inventory = { owner: Text, counts: Map Text Nat }`.

### (A) A lawful-by-relation Boolean `Eq` for `==`, plus `Equiv` congruence

**Idea.** A new interface behind `==`, weaker than `DecEq`: it comes with *its own* equivalence
relation and a proof that the Boolean decides it. Every `DecEq` type gets one with `Same := (=)`.
`Map` gets one with `Same := Map.Equiv`. Deriving produces `Eq` fieldwise when some field has only
`Eq`. It is Lean's `BEq` + `Equiv` + `beq_iff_equiv`, with the laws built in.

```
interface Eq (a: Type) =
  { Same: a -> a -> Prop
  , equals: a -> a -> Bool
  , sound: (x: a) -> (y: a) -> equals x y = True -> Same x y
  , complete: (x: a) -> (y: a) -> Same x y -> equals x y = True
  , refl: (x: a) -> Same x x, sym: …, trans: … }

instance Eq.ofDecEq [auto d: DecEq a]: Eq a := { Same = x y => x = y, … }
instance Map.instEq [auto e: DecEq v]: Eq (Map k v) := { Same = Map.Equiv, … }

-- user code: derived, Same is "owner equal and counts Equiv"
def unchanged (a: Inventory) (b: Inventory): Bool := a == b

theorem restock (inv: Inventory) (h: inv.counts.get "nails" = Some 3):
    Inventory.Same { owner = inv.owner, counts = inv.counts.insert "nails" 3 } inv := …  -- not `=`
```

- **Language changes.** `==`/`!=` resolve to `Eq` (core.md:253 changes). Deriving generates
  `T.%Same`, `T.%equals` and the soundness proofs. A rule is needed for which instance wins when a
  type has both (avoid Lean's diamond: `Eq` comes from `DecEq` whenever `DecEq` exists). Generic
  std functions that only need a test (`List.contains`, `List.distinct`, `List.indexOf`, …) ask for
  `Eq` instead of `DecEq` (signature churn across `std/List`, `std/Set`, …).
- **Proofs.** About maps and records containing them, proofs state `Same`, not `=`. `rewrite` can't
  use `Same` (option F would add that). `if h: r1 = r2` and `auto` don't apply to `Inventory`.
  Every lemma about `==` on a generic `a` must say which equality it means.
- **No `Ord (Map k v)`**, so no `Set (Set k)` and no map keyed by maps, unless `Ord` is weakened to
  a preorder (`compare x y = Equal -> Same x y`). That would ripple through every `Map` lemma that
  uses `ord.equal` [inferred].
- **Leaks.** `.tree` is public (§1.2), so user code can distinguish `Same` maps. Haskell has the same
  problem [§3.6]. Congruence holds only for library functions.
- **Kernel/trust:** none. **Performance:** as today. **JS boundary:** as today. **Hashing:** a
  future `Hash` must respect `Same`.
- **Fit.** Keeps the proved tree. Natural equality only for `==`, not for `=`. It goes against the
  reasoning behind D683 (keep `==` lawful in the strong sense).

### (B) No `==` on maps; `Map.same` and lemmas only

Stage 0 plus `Map.same: Map k v -> Map k v -> Bool` with `sameIff: same m1 m2 = True <-> Equiv m1 m2`.
No language change. `Inventory` gets no `==`. The user writes
`a.owner == b.owner && Map.same a.counts b.counts` by hand. Cheap, honest, and it doesn't solve the
port's problem. It is useful as stage 0 of A, E or F.

### (C) A canonical structure that is also the runtime structure

**Idea.** Replace the weight-balanced tree with a structure that has exactly one shape per set of
pairs, as std++/CompCert do. Then `DecEq (Map k v)` is derived structurally, `=` is extensional,
and no axiom or trusted step is involved.

- **Keys.** Tries need keys spelled as symbols, so `Map` would take a `Key k` interface instead of
  `Ord k`: an injective, *order-preserving* encoding to a sequence of digits, with a proof that
  comparing encodings is `compare`. Encodings for the key types in use (§1.4) are straightforward:
  `Nat` as length then big-endian bits (numeric order), `Int` with a sign tag, `Text` as characters
  plus a terminator (lexicographic), tuples by concatenation [inferred]. Hinze's generalized tries
  are the type-directed version [§3.7].
- **Custom orderings** (`[ord := descending]`, `Ord.byKey`) aren't expressible. They would keep the
  tree, without canonical equality.
- **Proof cost.** Appel–Leroy's seven-constructor nodes give 21-case `get`/`set` and 49-case
  `combine` [§3.2]. Stitchwort has no tactics to absorb those cases. The alternative, a simple trie
  with a "no empty node" Bool-equation invariant, has unique proofs by `DecEq.uniqueEq`. That
  avoids Coq's proof-growth problem, because Stitchwort keeps applied theorems folded
  [checked: `core.md:198`] [inferred].
- **Performance** [inferred, unmeasured]. Depth is the key's length in digits, not log n. With bit
  digits, a 10-character `Text` key is about 100–200 levels deep. With character digits, each node
  needs a canonical child map over `Char`. Patricia compression cuts the depth but its invariants
  are harder to prove. In JS, every digit test is a `bigint` or string operation. A benchmark
  against the §1.2 figures of maps.md would be required.
- **Fit.** It fully meets "functional, proved, natural equality = same pairs". It replaces the
  existing proved tree, needs a new `Key` interface and deriving, and drops custom orders.

```
-- what a user writes is unchanged; Map Text Nat now needs `Key Text`, not `Ord Text`
theorem insertTwice (m: Map Text Nat): (m.insert "a" 1).insert "a" 1 = m.insert "a" 1 :=
  Map.ext (key => …)        -- or `rfl` for closed maps: both sides are the same trie
```

### (D) Canonical meaning plus a proved tree swap-in (maps.md draft 1)

`Map` *is* a sorted entry list. The backends substitute the tree, trusting a generic substitution
step and the kernel-checked agreement theorems. It has all of E's proof benefits, but the kernel
runs lists (O(n) per update; a 10^4 build hit the evaluation limit [run, maps.md §4.6]), and the
trusted backend step is the part Matt rejected. Isabelle's `code_datatype Mapping` is the
precedent [§3.4]. It is listed for completeness.

### (E) Quotient types in the kernel (Lean's design)

**Kernel additions** (four constants, one rule, one axiom):

```
Quot (a: Type) (r: a -> a -> Prop): Type
Quot.mk [r] (x: a): Quot a r
Quot.lift [r] (f: a -> b) (h: (x: a) -> (y: a) -> r x y -> f x = f y): Quot a r -> b
    -- computes: Quot.lift f h (Quot.mk x)  ⟶  f x
Quot.ind [r] [P: Quot a r -> Prop] (h: (x: a) -> P (Quot.mk x)): (q: Quot a r) -> P q
Quot.sound [r] [x y: a]: r x y -> Quot.mk x = Quot.mk y          -- the new axiom
```

**Library.** Today's record becomes `Map.Raw`, unchanged with its proofs, and `Map` is its
quotient:

```
type Map (k: Type) (v: Type) [auto ord: Ord k] = { raw: Quot (Map.Raw k v) Map.Raw.Equiv }

def Map.toList (m: Map k v): List (k, v) := Quot.lift Map.Raw.toList (a b same => same) m.raw

def Map.insert (key: k) (value: v) (m: Map k v): Map k v :=
  { raw = Quot.lift (r => Quot.mk (r.insert key value))
                    (a b same => Quot.sound (Map.Raw.insertRespects key value a b same)) m.raw }

theorem Map.ext (m1: Map k v) (m2: Map k v) (h: (key: k) -> m1.get key = m2.get key): m1 = m2
instance Map.instDecEq [auto d: DecEq v]: DecEq (Map k v)     -- compares toLists
instance Map.instOrd [auto o: Ord v]: Ord (Map k v)           -- lexicographic on toList
```

**What users get.** `Inventory` derives `==` with no deriving change. `if h: m1 = m2`, `auto`,
`rewrite` with `=`, `T.ext`, `Set (Set Nat)` and memo tables keyed by maps all work.

```
theorem restock (inv: Inventory) (h: inv.counts.get "nails" = Some 3):
    { owner = inv.owner, counts = inv.counts.insert "nails" 3 } = inv :=
  Inventory.ext _ inv rfl (Map.insertGet "nails" 3 inv.counts h)   -- generated T.ext (SW-263)
```

- **`DecEq` without `propext`.** Lean derives "equal classes ⇒ related" (`Quotient.exact`) using
  `propext`, which Stitchwort lacks. For a *decidable* relation it isn't needed. Lift
  `x => Map.Raw.equal a x` into `Bool`, which respects `Equiv` by transitivity. Then
  `Quot.mk a = Quot.mk b` gives `equal a b = equal a a = True` [inferred; the reviewer should
  check].
- **Function extensionality comes free.** Lean proves funext from `Quot.sound`, and the proof needs
  eta, which the kernel has [cited §3.1; checked `core.md:201`]. That would let `rewrite` go under
  binders, reversing a constraint recorded in calc-rewrite.md (D37) [checked: `syntax.md:999`].
- **Trust.** One new propositional axiom, standard and modelled set-theoretically. Quotients with
  UIP/K and an impredicative `Prop` are Lean's own setting [cited §3.1]. It must be counted as part
  of the core theory, not as an "assumption" that blocks exports (DESIGN.md §3) [decision D772].
- **Computation.** `Quot.sound` is an axiom, so `J` over an equality built from it is stuck in the
  kernel evaluator. A closed term that transports along such a proof won't reduce to a numeral.
  Running is unaffected, because erasure makes `J` on an erased proof take its base
  [checked: `core.md:203`]. Lean has the same limitation [inferred]. `rfl` between two closed maps
  built in different orders fails (different trees). `Map.ext` plus `decide` replaces it.
- **Erasure, JS, runtime.** `Quot.mk x` erases to `x` and `Quot.lift f h q` to `f q`, so a map is
  today's tree in `crates/rt` and JS, with zero overhead [inferred]. The JS boundary is unchanged:
  decode through `fromList`, encode through `toList` [checked: `dictionary.sw:1-5`].
- **Hashing/caching.** New term formers need hash tags, like `Delay`'s constants
  [checked: `float.md` cites `crates/core/src/hash.rs:96-104`]. A future value `Hash` on maps hashes
  `toList`, which is lawful automatically [inferred].
- **Costs and risks.**
  - Every function out of `Map` needs a respects proof. The library carries this, and §4 makes each
    one a line.
  - A user can no longer read `.tree`. That is enforced abstraction, which Stitchwort otherwise lacks.
  - Nested occurrences (a type with a `Map Text T` field inside `T`) need positivity rules through
    `Quot`. Lean's bundled maps can't be nested either [cited §3.1]. Today's record has the same
    question [unverified whether it's accepted today].
  - Kernel work: `crates/core` term, value, eval rule, hash, erase, the JS and rt backends, and the
    elaborator's knowledge of the constants.
- **Fit.** It keeps exactly the proved weight-balanced tree, and `=` is "same pairs". It needs no
  `Eq` interface and no deriving change, and it also covers `Set`, a future hash map, and other
  coarse types (rationals, unordered pairs, graphs up to relabelling).

### (F) Setoid rewriting on top of A or B

An elaborator feature: `rewrite same in …` with `same: Map.Equiv m1 m2` rewrites `m1` to `m2`
inside any context built from functions that have registered congruence lemmas, as Rocq's `Proper`
instances do [§3.2]. Stitchwort already finds congruence lemmas by name for termination
(`FCong`, [checked: `core.md:173`]), so a naming convention (`Map.insertRespects`) could register
them.

```
theorem lookupAfter (same: Map.Equiv m1 m2): ((m1.insert "a" 1).get "b") = ((m2.insert "a" 1).get "b") :=
  rewrite same in rfl          -- uses Map.insertRespects, Map.getRespects
```

No kernel change. A real elaborator project (relation-indexed rewriting, error messages for a
missing morphism). It is only worth building if A is chosen. Under E, ordinary `rewrite` already
works.

### 5.1 Comparison

| | A `Eq` | B `same` | C canonical trie | D swap-in | E quotient | F setoid rewrite |
|---|---|---|---|---|---|---|
| `=` means same pairs | no | no | **yes** | **yes** | **yes** | no |
| `==` on `Inventory` | yes (not `=`) | no | yes | yes | yes | (with A) |
| `Ord (Map k v)`, `Set (Set k)` | no | no | yes | yes | yes | no |
| Keeps today's proved tree | yes | yes | **no** | yes (at run time) | **yes** | yes |
| Custom orderings | yes | yes | **no** | yes | yes | yes |
| Kernel / trust change | none | none | none | backend substitution | **4 primitives + 1 axiom** | none |
| Language change | `==`, deriving, std signatures | none | `Key` interface + deriving | representation attribute | none for users | `rewrite` |
| Kernel-time speed | O(log n) | O(log n) | O(key length) | O(n) | O(log n) | — |
| Run-time speed | today | today | unmeasured | today | today | — |
| Proof style | `Same` + congruence | same | `=` | `=` | `=` (+ respects in library) | `Same`, rewritable |
| Size | large (language-wide) | small | large (new structure + proofs) | medium–large | medium (kernel) + medium (library) | medium |

## 6. Recommendation

**Choose E (quotients), staged, with B as its first stage.**

1. **Stage 0 (B, start now).** `Map.Equiv`, agreement lemmas for every operation (`toList` in
   terms of a sorted-list spec), the respects lemmas, and `Map.same` with `sameIff`. The same for
   `Set`. The work is needed under every option. It unblocks proofs about maps today and fills
   maps.md's lemma list (§4.4 there).
2. **Stage 1 (kernel).** `Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind`, `Quot.sound`: term formers or
   kernel-known constants, the one computation rule, erasure, hashing, and both backends. Plus
   `Quot.funext` as a library theorem, and a decision on how the axiom is reported.
3. **Stage 2 (library).** `Map` and `Set` become quotients of today's records. Each operation is
   lifted with its stage-0 respects lemma. Then `DecEq`, `Ord`, `ext`, `insertComm`, `insertGet`,
   and maps.md's API additions on top. Fix the users: day 8, `dictionary.sw` (its `same` becomes
   `a == b`) and `map-set.sw`.

**Why E over the others.**

- It is the only option that gives Matt both things he asked for together: the existing proved
  tree, and `=` meaning "same pairs".
  - A gives "same pairs" only to `==`, and splits `==` from `=` across the language. That is the
    split D683 rejected for `Float`.
  - C gives natural `=`, but throws away the tree and custom orderings, at an unmeasured speed.
  - D needs the trusted swap-in.
- Its trust cost is the best understood in the field: Lean's quotient axiom, which has a published
  model. The extra kernel code is smaller than the elaborator work A or F need [inferred].
- It solves the general problem, not just maps: sets, a later hash map, rationals as fractions,
  multisets. It also yields funext, which an earlier note had to work around.

**When to pick something else.** If adding an axiom is unacceptable, do B, then A (with F later,
if proofs up to `Same` become common). If a benchmark shows tries are competitive in JS, C could
come later as a specialised `TrieMap` for `Text`/`Nat`/`Int` keys. It isn't needed for equality.

## 7. Questions for the reviewer

1. **Soundness of E in this kernel.** Stitchwort has K, impredicative `Prop`, large elimination of
   `Eq`, no definitional proof irrelevance and no `propext` (§1.2). Is adding Lean's `Quot`
   (with `Quot.sound`) consistent here? Are any of Lean's side conditions specific to Lean's kernel
   (for example its definitional proof irrelevance, or how `Quot.lift`'s reduction interacts with
   eta)?
2. Is the **`propext`-free exactness argument** for decidable relations (§5 E) correct? Does
   anything else that `DecEq (Map k v)` or `Ord (Map k v)` needs require `propext`?
3. **Stuck `J`.** How much does the loss of canonicity (closed terms stuck on `Quot.sound`) hurt in
   practice in Lean, for programs that are also checked by evaluation? Are there mitigations, like
   Lean's `Quot.lift` computing on `Quot.mk` while `Quot.sound` stays opaque?
4. Should `Quot.sound` count as an "assumption" for Stitchwort's export rule, or as part of the core
   theory, as K and `J` are?
5. **Positivity.** What rules should allow `type T = { children: Map Text T }` through a quotient?
   How does Lean handle nested occurrences inside `Quot`? (Its bundled maps can't nest.)
6. **Option A as Lean ships it.** What are the real costs of `BEq`/`LawfulBEq`/`DecidableEq`
   coexisting (diamonds, duplicated lemmas)? Would Lean's designers do it again?
7. Is the **canonical-trie route** (C) better than we credit, for example generalized tries with a
   derived `Key`, or Patricia trees? Are there performance data for canonical tries in JS or OCaml
   against weight-balanced trees?
8. Anything we missed: Agda's or Idris's newer work, Koka/F\*/Liquid Haskell practice, Rocq's
   `SProp`-based quotients, observational type theory (where funext and quotients are built in)?

## 8. Decisions

- **D770: Equality approach for `Map`/`Set`.** (E) quotients / (A) `Eq` interface / (C) canonical
  trie / (D) swap-in (draft 1) / (B) lemmas only. **[E, with B as stage 0]**
- **D771: Stage 0 now.** `Map.Equiv`, agreement and respects lemmas, `Map.same`, independent of
  D770. **[yes]**
- **D772: How `Quot.sound` is accounted for.** Part of the core theory, like K / a tracked
  assumption that blocks exports. **[part of the core theory, listed in docs/core.md]**
- **D773: Quotients as kernel term formers vs kernel-known constants** (like `Effect.Delay`).
  **[decide during stage 1; whichever is smaller in `crates/core`]**
- **D774: `Quot.funext` shipped in std, and `rewrite` allowed under binders through it.**
  **[ship the theorem; the `rewrite` change is a separate ticket]**
- **D775: `Map` keeps `[auto ord: Ord k]` and today's weight-balanced tree.** **[yes]**
- **D776: maps.md D740/D741/D742/D746 are superseded** by D770; its API (D743), JS (D744), `Set`
  (D745), hash-map (D747) and performance (D748) decisions stand. **[yes]**
- **D777: No `Eq` (Bool) interface; `==` stays `DecEq`.** **[yes, unless D770 becomes A]**
- **D778: Specialised canonical `TrieMap`.** Not now; revisit only with a benchmark. **[defer]**
- **D779: External review of this note before stage 1.** **[yes]**

## Sources

Stitchwort (commit `2185a364`): `crates/elab/src/std/core/DecEq.sw`, `std/core/Ord.sw`,
`std/Map/Map.sw`, `std/Set/Set.sw`, `std/Decidable/Decidable.sw`, `crates/elab/src/derive.rs`,
`crates/js/src/lib.rs:315-339`, `docs/core.md`, `docs/syntax.md`, `DESIGN.md`,
`docs/proposals/{maps,float,integers,proof-irrelevance,calc-rewrite}.md`,
`aoc/src/Aoc/Day08/{Day08.sw,Proofs/Labels.sw}`, `examples/extract/dictionary.sw`.

External (all fetched 23 October 2026):

- Lean: [Basic Classes](https://lean-lang.org/doc/reference/latest/Type-Classes/Basic-Classes/),
  [Maps and Sets](https://lean-lang.org/doc/reference/latest/Basic-Types/Maps-and-Sets/),
  [Quotients](https://lean-lang.org/doc/reference/latest/The-Type-System/Quotients/), source in
  [leanprover/lean4 `src/Std/Data`](https://github.com/leanprover/lean4/tree/master/src/Std/Data)
  (`ExtDTreeMap/Basic.lean`, `ExtDHashMap/Basic.lean`, `DHashMap/Basic.lean`, `HashMap/Basic.lean`,
  `HashMap/Lemmas.lean`, `ExtHashMap/Lemmas.lean`, `DTreeMap/Internal/Balancing.lean`),
  [TreeMap.DecidableEquiv](https://lean-lang.org/doc/api/Std/Data/TreeMap/DecidableEquiv.html),
  Mathlib [`Data/Finmap.lean`, `Data/Multiset/Defs.lean`](https://github.com/leanprover-community/mathlib4),
  [Lean4Lean](https://arxiv.org/html/2403.14064v3).
- Rocq: [FMapInterface](https://docs.rocq-prover.org/v8.9/stdlib/Coq.FSets.FMapInterface.html),
  [Generalized rewriting](https://rocq-prover.org/doc/master/refman/addendum/generalized-rewriting.html),
  std++ [pmap](https://plv.mpi-sws.org/coqdoc/stdpp/stdpp.pmap.html) and
  [gmap](https://plv.mpi-sws.org/coqdoc/stdpp/stdpp.gmap.html), Appel and Leroy,
  [Efficient Extensional Binary Tries](https://arxiv.org/abs/2110.05063) (JAR 67, 2023).
- Agda: [Cubical](https://agda.readthedocs.io/en/latest/language/cubical.html),
  [cubical FMSet](https://raw.githubusercontent.com/agda/cubical/master/Cubical/HITs/FiniteMultiset/Base.agda),
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
