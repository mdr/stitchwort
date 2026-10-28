# Proposal: maps and sets for practical use

**Status:** draft 1, 23 October 2026. Design only: nothing is built. Ticket SW-356. Stops for
review (design-review gate). Decisions D740–D749 are at the [end](#7-decisions). Written against
commit `143d647e`. Follows [map-set.md](map-set.md) (SW-113, the `Map`/`Set` as built).

Labels: **[checked]** read in the Stitchwort source at the `file:line` given; **[run]** a scratch
program run on 23 October 2026 (release build of `main` from that morning, Node 22.23.3, arm64
Mac; programs kept outside the repository); **[cited]** read in the source linked; **[inferred]**
my reasoning from checked facts; **[unverified]** believed, not confirmed.

## 0. Summary

A real-world TypeScript app was being ported. One of its records had a field of type
`Map Text V`, and the record needed a derived `==`. That failed, because std `Map` has no
`DecEq`. A lane then found that `Map` *can't* have a lawful `DecEq` as it is built today: the same
entries inserted in different orders give trees of different shapes, so "equal entries" doesn't
imply "equal maps" (§1.1). The port worked around it by keeping a sorted entry list.

**Recommendation (§4):** split what a map *means* from how it *runs*.

- **What it means** is what the type checker and proofs see. A `Map` is its entries, as a
  strictly ascending list of key–value pairs with a proof that they're in order. Each set of
  entries has exactly one such list, so two maps with the same entries are equal (`=`), not just
  `==`. That gives a lawful `DecEq`, so records with map fields derive `==`. It also gives a real
  extensionality theorem, `Map.ext` ("same `get` everywhere means equal maps"), a lawful
  `Ord (Map k v)`, and simple proofs by list induction.
- **How it runs:** in the fast runtime and in exported JS, a map is today's weight-balanced tree.
  Each library operation runs as its tree version, and a theorem checked by the kernel proves the
  tree version agrees with the list version. So run-time speed and stack depth stay as they are
  today, and the only new trusted code is a small, general substitution step in the backends
  (D741).
- The API grows to cover what practical code reached for (§4.3), with the lemmas proofs need
  (§4.4).

## 1. Problems with today's `Map` and `Set`

### 1.1 Equality: no lawful `DecEq`, so no derived `==` on records with maps

- `Map k v [ord]` is the record `{ tree: Map.Tree k v, ordered: Map.Tree.Ordered ord tree }`
  over `Tip | Bin size left key value right` [checked: `std/Map/Map.sw:15-17`, `:167-170`].
  `Ordered` is a recursive `Prop` built from `Unit`, `And` and `compare a b = Less`
  [checked: `:147-164`].
- The same entries in different insertion orders give different trees **[run]**:
  `Map.fromList [(1, 1), (2, 2)]` is `Bin 2 Tip 1 (Bin 1 Tip 2 Tip)`, and
  `Map.fromList [(2, 2), (1, 1)]` is `Bin 2 (Bin 1 Tip 1 Tip) 2 Tip`, yet their `toList`s are `==`.
- `DecEq a` is `decide: (x: a) -> (y: a) -> Decidable (x = y)` [checked: `core/DecEq.sw:11-12`].
  A `DecEq` that compared `toList`s would have to answer `Yes` with a proof that those two trees
  are equal. They aren't, so no such instance exists. A tree-comparing `DecEq` is lawful but
  useless, because it calls equal-content maps different.
- What a user sees **[run]**: `type Inventory = { owner: Text, counts: Map Text Nat }`, then
  `x == x`, gives `E-INSTANCE-NONE: no DecEq instance for Inventory … its field counts has type
  Map Text Nat [ord := Text.instOrd], which has no DecEq instance`.
- Workarounds seen so far: compare `Map.toList a == Map.toList b` by hand
  [checked: `examples/extract/dictionary.sw:56-57`], or swap the map for a sorted list (the port).
  Neither works inside a derived `==` or `Ord`.
- The same blocks `Ord (Map k v)` (needed for a `Set` of maps or a map keyed by maps, e.g. a memo
  table keyed by state) and gives no useful `rfl`: `Map.fromList xs = Map.fromList ys` can't be
  proved, even for concrete lists with the same entries.
- map-set.md already listed `DecEq` as a follow-up, noting that it "needs equal trees with equal
  proofs" [checked: `map-set.md:85-88`]. The real obstacle is the first half, equal trees.

### 1.2 Balance and performance

Insertion and removal *do* rebalance: the trees are weight-balanced (Adams; Haskell's
`delta = 3`, `ratio = 2`) [checked: `Map.sw:72-83`]. Balance is a performance property and isn't
in the type. Measured, inserting keys `0 … n-1` in ascending order (the worst case for a tree
that doesn't balance) and then looking each one up **[run]**:

| n | fast runtime (`stitchwort run`) | `run --reference` | exported JS (Node) | tree depth | native JS `Map` |
|---|---|---|---|---|---|
| 10^4 | — | 3.0 s | 42 ms | 18 | — |
| 10^5 | 1.2 s | — | 433 ms | 22 | 7 ms |
| 10^6 | 11.9 s (508 MB peak) | — | 6.0 s | 26 | 66 ms |

- **Stack safety holds** because of the balancing. The depth stays under 2.5 log₂ n, so recursion
  over the tree (`get`, `insert`, `toListOnto`, `foldLeft`) is shallow in JS. Each output list is
  built by the library's stack-safe list code (SW-336, SW-346).
- **Constant factors are high.** Exported JS is about 90× slower than a native JS `Map` at 10^6.
  That's acceptable for proofs-first code but worth a later target (§4.6).
- **Bulk operations are O(n log n) through repeated `insert`:** `filter` and `union`
  [checked: `Map.sw:552-557`], and `Set.intersect` and `difference`
  [checked: `Set.sw:42-45`]. A merge would be O(n + m). (Since built: §4.6, "As built".)
- **A comparison, for the canonical alternative:** a plain sorted association list (insert by
  walking the list) at n = 10^4 took 8.5 s in the fast runtime. In exported JS it threw
  `StitchwortResourceError (Maximum call stack size exceeded)`, and in the reference evaluator it
  hit the resource limit after 241 s **[run]**. A list alone isn't a practical *runtime*
  representation, which shapes §3–4.

### 1.3 API gaps

Evidence from the code that uses maps today (`grep` over `aoc/` and `examples/`):

- **Grouping and counting** are hand-rolled with `insertWith`: `grouped` builds `Map Text (List
  Text)` with `insertWith List.append (Text.take 1 w) [w]` [checked: `dictionary.sw:66-67`], and
  word counts use `insertWith Nat.add word 1` [checked: `examples/accept/map-set.sw:9-10`]. The
  usual names are Scala's `groupBy` and a `counts` / `fromListWith`.
- **AoC day 8** keeps `labels: Map Nat Nat` and relabels with `Map.map` on every join
  [checked: `aoc/src/Aoc/Year2025/Day08/Day08.sw:77`, `:93`]. Its proofs had to restate facts about
  `fromList` of a range by hand (`lookupBelow`, `lookupRange`, through `Map.lookupLast`)
  [checked: `Day08/Proofs/Labels.sw:85-107`].
- **Earlier AoC notes** wanted a set of grid positions with ~8 million membership tests (day 4)
  and a memo table (day 3) [checked: `docs/aoc-2025.md:318-319`, `:389-395`]. Both were solved
  without maps, by other algorithms.
- **Missing from std** compared with Haskell `Data.Map` and Scala `TreeMap` (the list is in
  §4.3): `unionWith`, `intersectWith`, `filterMap`, `partition`, `mapWithKey`, `foldRight`, min
  and max entries, nearest key below or above, ranges, `any`/`all`/`count`/`find`, `keySet`,
  `fromListWith`, `groupBy`. `Set` lacks `isSubset`, `all`, `min`/`max`, `partition`.
- **Order guarantees** are stated in comments (`toList`, `keys`, `foldLeft` are "in key order")
  [checked: `Map.sw:531-543`] but not as theorems.

### 1.4 Proof support

- **Exists** [checked: `Map.sw:561-616`, `Set.sw:47`]: `getEmpty`, `getInsert`,
  `getInsertOther`, `getInsertWith`, `getMap`, `getFromList` (through `lookupLast`), and
  `Set.containsInsert`.
- **Missing:** anything about `remove`, `alter`, `adjust`, `filter`, `union`, `size` and
  `toList`; `toList` being sorted with distinct keys; membership in `toList` ↔ `get`; an
  induction principle for maps; and, most of all, **equality**. Today a proof can never conclude
  `m1 = m2` from "they agree on every key", because that's false for trees. So a statement like
  day 8's `joinSame: c.join f s = c` [checked: `Labels.sw:128`] works only when the map is
  syntactically unchanged.

### 1.5 JS boundary, printing, hashing

- **JS boundary.** `Map Text V`, in `Text`'s own order, crosses as a plain object
  `{ readonly [k: string]: V }`. Any other key type or ordering is refused, with a message
  [checked: `crates/js/src/lib.rs:321-339`, `:2983`; `dictionary.sw:1-5`]. JS enumerates
  integer-like keys first, so an output object's key order isn't the map's order
  [checked: `dictionary.sw:75-76`]. Nothing here depends on the representation.
- **`Show`** prints `Map.fromList [(1, "a"), …]` in key order [checked: `Map.sw:619-621`], so it's
  already canonical.
- **Hashing and caching.** The check cache hashes declarations, not run-time values, so a map's
  shape doesn't affect caching [inferred from `docs/proposals/check-cache.md`]. What a
  non-canonical shape *does* block: maps as keys (`Ord`), memo tables keyed by maps, and any
  future hash of a map value, which would need the same canonical form or an order-independent
  hash [inferred].

## 2. How others do it

| System | Representation | What `=` means on maps | Programmer's `==` | Sources |
|---|---|---|---|---|
| **Lean 4** | `Std.TreeMap`/`DTreeMap`: "size-bounded" balanced trees; `HashMap` | Structural on `TreeMap`; `ExtTreeMap`/`ExtHashMap` are *quotients* by `Equiv`, so `=` is extensional, with ext lemmas and a `DecidableEq` (needs `LawfulEqCmp`, `TransCmp`, `LawfulBEq`) | `BEq` (Bool, no laws) vs `LawfulBEq` (`a == b = true → a = b`, `a == a`) | [cited: [Lean reference, Maps and Sets](https://lean-lang.org/doc/reference/4.28.0/Basic-Types/Maps-and-Sets/); [ExtTreeMap](https://lean-lang.org/doc/api/Std/Data/ExtTreeMap/Basic.html); [ExtDTreeMap](https://lean-lang.org/doc/api/Std/Data/ExtDTreeMap/Basic.html) (`inner : Quotient (DTreeMap.isSetoid …)`); [basic classes](https://lean-lang.org/doc/reference/latest/Type-Classes/Basic-Classes/)] |
| **Rocq** (FMaps; MMaps similar) | AVL / red-black trees, sorted lists | Structural; `Equal m m' := ∀ y, find y m = find y m'` is a setoid relation, with `Equiv`/`Equivb` for values up to a relation | `equal cmp m m'`, specified through `Equivb` (`equal_1`, `equal_2`) | [cited: [FMapInterface](https://docs.rocq-prover.org/v8.9/stdlib/Coq.FSets.FMapInterface.html)]; MMaps [unverified] |
| **Isabelle/HOL** | `typedef ('a,'b) mapping = UNIV :: ('a ⇀ 'b) set` + `setup_lifting`; code generated through red-black trees | Extensional: a mapping *is* a partial function, and HOL has function extensionality | generated code | [cited: [HOL-Library Mapping](https://isabelle.in.tum.de/library/HOL/HOL-Library/Mapping.html); [RBT.thy](https://isabelle.in.tum.de/repos/isabelle/annotate/2803d2b8f85d/src/HOL/Library/RBT.thy)] |
| **Agda** stdlib | `Map V = AVL.Tree (const V)` over a `StrictTotalOrder` | Structural; the module defines no map equality | — | [cited: [Data/Tree/AVL/Map.agda](https://raw.githubusercontent.com/agda/agda-stdlib/master/src/Data/Tree/AVL/Map.agda)] |
| **Idris 2** | `SortedMap` over a balanced tree | Structural | `Eq` (Bool, no laws): `(==) = (==) on kvList` | [cited: [Data/SortedMap.idr](https://raw.githubusercontent.com/idris-lang/Idris2/main/libs/base/Data/SortedMap.idr)] |
| **Dafny** | built-in `map<K,V>` | Extensional, but the verifier "never tries to prove extensionality" unless asked | built-in | [cited: [Dafny FAQ](https://dafny.org/dafny/HowToFAQ/FAQMapExtensionality)] |
| **F\*** | `FStar.Map` | `equal m1 m2` (same domain, pointwise) with `lemma_equal_elim: equal m1 m2 <==> m1 == m2`, which "involves a use of functional extensionality" | — | [cited: [FStar.Map.fsti](https://raw.githubusercontent.com/FStarLang/FStar/master/ulib/FStar.Map.fsti)] |
| **Haskell** `Data.Map` | weight-balanced trees (Adams; Nievergelt–Reingold), `delta = 3`, `ratio = 2` | — (no proofs) | `Eq`: `size m1 == size m2 && …` element-wise in key order | [cited: [Data.Map.Strict docs](https://hackage-content.haskell.org/package/containers-0.8.1/docs/Data-Map-Strict.html); [Internal.hs](https://raw.githubusercontent.com/haskell/containers/master/containers/src/Data/Map/Internal.hs) lines 4301-4303, 4453-4464] |
| **Scala / TS** | `immutable.TreeMap` (red-black), `HashMap` (HAMT); JS `Map` (insertion order) | — | Scala: `==` is by entries; JS `Map` has no structural equality | [unverified] |

What this shows:

1. Systems with **quotients or function extensionality** (Lean's `Ext*`, Isabelle, F\*) make `=`
   extensional and keep a fast tree inside.
2. Systems **without them** (Rocq stdlib, Agda) keep `=` structural and give a separate
   relation (`Equal`).
3. **Programming languages** give a Bool `==` defined through `toList`, with no tie to `=`.

Lean has both: `BEq` for programs and `LawfulBEq` where proofs need the link [cited].

**Canonical representations.** No deterministic binary-search-tree representation that is unique
for its contents can do all of search, insert and delete in O(log n). Andersson and Ottmann prove
Ω(n^{1/3}) for unique representations in bounded-degree graphs, with a matching structure; Sundar
and Tarjan give related bounds and note that randomised treaps (Aragon–Seidel) reach O(log n)
expected [cited: [abstract](https://user.it.uu.se/~arnea/abs/andetigh.html);
[SIAM](https://epubs.siam.org/doi/10.1137/S0097539792241102)]. Tries (Patricia trees, as in
Haskell's `IntMap`) are unique for their contents, but only for keys made of bits or characters
[unverified for `IntMap`'s exact form].

## 3. Options for equality

**Constraints in Stitchwort.**

- There are no quotient types [checked: `integers.md:514`] and no function extensionality
  [checked: `calc-rewrite.md:182`; `core.md:173`].
- There is no definitional proof irrelevance [checked: `core.md:139`]: SW-93 is in the backlog.
- Axiom K holds [checked: `core.md:140`], and `DecEq.uniqueEq` makes any two proofs of an
  equation in a type with `DecEq` equal [checked: `DecEq.sw:55`].
- `Ord` carries a `DecEq` and the law `compare x y = Equal -> x = y`
  [checked: `core/Ord.sw:23-38`].
- Derived `==` accepts proof fields only when they are equations in a type with `DecEq`
  [checked: `crates/elab/src/derive.rs:12-20`].

### (a) A canonical representation: `=` *is* extensional

**(a1) A strictly ascending association list with an order proof.** It is canonical: with a
lawful `Ord`, two strictly ascending lists with the same `get` at every key are the same list.
The proof is by induction, comparing heads by `compare` and using `ord.equal` [inferred]. The
order proof is unique too:

- if written as a Bool equation, `ascending ord entries = True`, by `DecEq.uniqueEq`;
- if written as a `Prop` built from `compare a b = Less`, by an induction using the same lemma
  [inferred].

So `DecEq (Map k v)` follows from `DecEq` on the entry list, and `Map.ext` holds. The proofs are
plain list induction. It's simplest for proofs and slowest to run: O(n) per update, and the
measurements in §1.2 rule it out as a runtime representation.

**(a2) A treap whose priorities come from the keys** (priority = `hash k`, ties broken by key).
For a given key set it has exactly one shape, so it is canonical [cited: Sundar–Tarjan abstract
above]. Costs:

- it needs a `Hash` interface (and deriving) for every key type;
- the hash function becomes part of what a map means;
- balance is only expected, not guaranteed: poorly mixed hashes (for example `hash n = n`)
  degenerate into a list, which overflows the stack in JS;
- canonicity and the rotation proofs are harder than (a1)'s;
- maps with a custom ordering still work, but the shape depends on the hash, not on the order
  [inferred].

**(a3) A trie for particular key types** (`Nat`, `Int`, `Text`, `Char`). It is canonical, with
depth bounded by key length. But it isn't generic over `Ord`: tuple keys such as `Set (Nat, Nat)`
would need an encoding interface, and `[ord := descending]` wouldn't apply. Better kept for a
possible specialised map later.

**(a4) A tree rebuilt to a fixed shape** (for example perfectly balanced for its size). It is
canonical, but every update costs O(n) (§2's lower bound). Not practical.

### (b) Quotients or extensionality

This would mean adding quotient types to the kernel, as Lean's `Quot` does with `Quot.sound`, an
axiom from which function extensionality follows [unverified for the precise Lean axiom set], or
adding funext to the kernel. Then `Map := Quotient (Tree, Equiv)`, with `=` extensional and the
fast tree inside. Costs:

- a kernel extension and a new axiom;
- generated JS must stay free of axioms [checked: `compact-text.md`, option C's rationale];
- every function out of a quotient carries a respects-`Equiv` proof.

It's large and touches trust. Not proposed.

### (c) A lawful-by-relation `==`, separate from `DecEq`

Keep the tree. Add `Map.Equiv m1 m2 := (k: K) -> get k m1 = get k m2`, a Bool `Map.equal` with
`equal m1 m2 = True ↔ Equiv m1 m2`, and a new interface `Eq` (Lean's `BEq`) that `==` and derived
record `==` would use, with `DecEq` implying it.

- **Sound** if the soundness theorem is stated over `Equiv`.
- **But:** derived `==` on a record with a map field would no longer mean `=`. So `if h: r1 = r2`,
  `auto`, and Hedberg-based proof-field handling can't use it. `==` and `=` would split
  language-wide, and every lemma about `==` would need a "lawful" variant, as in Lean.
- It's a language and deriving change: `==` resolution, the deriving plan, notes, docs.
- Proof ergonomics: every proof about records with maps has to work up to a relation
  (setoid-style rewriting, which Stitchwort's `rewrite` doesn't support) [inferred].

### (d) Hybrid: a fast tree inside, extensional statements outside

Keep the tree as the type. Add `Map.equal` (via `toList`) and theorems stated over `Equiv`
(`getInsert`… plus "`Equiv` is preserved by `insert`"). This is cheap, but it fixes neither
derived `==` (it needs (c)) nor `=` (it needs (a) or (b)). It's today's state plus lemmas.

### (a1) + refinement: canonical meaning, tree at run time

This is the option recommended. It is (a1) for the checker, and today's tree for the runtimes, with
kernel-checked theorems that each tree operation agrees with its list operation (§4.1). It has
the same shape as [compact-text](compact-text.md): there, `Text` *means* a list of characters,
and the backends store a native string [checked: `compact-text.md` summary;
`crates/rt/src/natives.rs:1-10`]. The difference: there, the agreement is trusted and tested;
here it would be *proved*. Isabelle's `Mapping` with code generated through red-black trees is
the closest precedent [cited above].

| | Sound | Derived `==` on records with maps | `=` extensional | Proofs | Kernel speed | Runtime and JS speed | Cost |
|---|---|---|---|---|---|---|---|
| (a1) list only | yes | yes (`DecEq`) | yes | easiest | O(n) per update | O(n), stack overflow in JS at 10^4 **[run]** | small |
| (a2) treap | yes | yes | yes | hard | O(log n) expected | expected O(log n); degenerate cases | large (adds `Hash`) |
| (a3) trie | yes | yes | yes | medium | O(key length) | good | per key type |
| (b) quotient | yes | yes | yes | needs respects-proofs | O(log n) | O(log n) | kernel change and an axiom |
| (c) `Eq` class | yes | yes, but `==` ≠ `=` | no | relation-based | O(log n) | O(log n) | language-wide |
| (d) lemmas only | yes | no | no | relation-based | O(log n) | O(log n) | small |
| **(a1) + refinement** | yes, given the substitution step (§4.1) | yes (`DecEq`) | yes | easiest | O(n) per update | today's tree | medium |

## 4. Recommendation

### 4.1 Representation

The meaning, in `std/Map/Map.sw` (names are illustrative):

```
type Map (k: Type) (v: Type) [auto ord: Ord k] =
  { entries: List (k, v)
  , ascending: Map.isAscending ord entries = True   -- strictly, by `compare`
  }
```

- **The invariant is a Bool equation (D742),** so proofs of it are unique by `DecEq.uniqueEq`,
  and `DecEq (Map k v)` is "the entry lists are equal, then transport". It's written by hand
  (library types aren't derived [checked: `derive.rs:26-27`]) and needs `DecEq v`; keys already
  have one through `ord.eq`. A lemma turns the invariant into the `Prop` `List.Sorted` for
  proofs.
- **Operations are defined on lists:** `insertWith`, `remove`, `get` by walking; `fromList` by
  sorting by key and keeping the last of equal keys; `union`/`intersect`/`difference` by merging;
  `filter`/`map` directly. These are the specifications, and they also run in the reference
  evaluator.
- **At run time** (the fast runtime and exported JS), a `Map` value *is* a `Map.Tree`: the
  existing weight-balanced code, kept in Stitchwort. A representation attribute on `Map` names:
  - the tree type;
  - `toSpec = Map.Tree.toList`;
  - `fromSpec = Map.Tree.fromAscending` (O(n), from a sorted list);
  - for each operation, its tree version and an **agreement theorem**, for example:
    `Map.Tree.Ordered ord t -> toList (Map.Tree.insertWith f key value t) =
    Map.List.insertWith f key value (toList t)`.
- **What the kernel checks and what is trusted.** The kernel checks every agreement theorem and
  that each tree operation keeps `Ordered`. The backend checks that each theorem's statement has
  exactly the expected shape (as the termination checker already checks congruence lemmas'
  shapes [checked: `core.md:173`]).
- **The trusted step** is the substitution itself: "run the tree version, and convert only where
  code looks at `.entries` or builds the record". User code that matches on `m.entries` costs
  one O(n) conversion, like `MkText` today [checked: `compact-text.md` as built, "Bridges"].
- **Balance is still not proved,** as today: it's performance only.
- **`Set`** stays a record around `Map k ()` [checked: `Set.sw:7`] and inherits all of this.
- **Fallback (D741 b):** write the tree operations as trusted natives in Rust and JS, like the
  `Text` natives (D389), and test them differentially. This is quicker to start, but it means two
  hand-written implementations, both trusted.

### 4.2 Equality story

- **`==` on maps** is `DecEq`: lawful, so `if h: m1 = m2` and `auto` work.
- **Records with map fields derive `==`** with no change to deriving: the field now has an
  instance. The same goes for `Ord` once `Map.instOrd` exists (lexicographic over `entries`,
  needs `Ord v`).
- **`Map.ext: ((key: k) -> get key m1 = get key m2) -> m1 = m2`** and `Set.ext` are the main
  proof tools.
- **`rfl` between concrete maps:** two closed maps built in different orders should be equal by
  `rfl`. Both normalise to the same list, and their order proofs are closed proofs of
  `True = True`, which compute to `rfl` when compared [inferred from `core.md:198`: comparisons
  unfold folded theorems]. If not, `Map.ext` plus `decide` covers it. This is an acceptance test.

### 4.3 API

Names follow std's style (`get`/`getOr`, `foldLeft`, `filterMap`, `partition` as in `List`) and
Scala where std has no precedent. **New** items are in bold.

| Group | `Map` | `Set` |
|---|---|---|
| Build | `empty`, `singleton`, `insert`, `insertWith`, `fromList` (last wins), **`fromListWith f`**, **`groupBy (key: a -> k) xs: Map k (List a)`** (in list order), **`counts xs: Map k Nat`**, **`fromKeys (ks: Set k) f`** | `empty`, `singleton`, `insert`, `fromList`, **`unions`** |
| Look up | `get`, `getOr`, `contains`, **`find p`**, **`min`/`max: Option (k, v)`**, **`below key`/`above key`** (nearest strictly below/above, Scala `maxBefore`/`minAfter`) | `contains`, **`min`/`max`**, **`below`/`above`**, **`isSubset`**, **`disjoint`** |
| Change | `remove`, `alter`, `adjust`, **`removeAll (ks: Set k)`**, **`keepOnly (ks: Set k)`** | `remove` |
| Combine | `union` (left wins), **`unionWith f`**, **`intersectWith f`**, **`difference`** | `union`, `intersect`, `difference` |
| Transform | `map`, `filter`, **`mapWithKey`**, **`filterMap`**, **`partition`**, **`mapKeys f`** (later wins on clashes) | `map`, `filter`, **`partition`** |
| Read out | `size`, `isEmpty`, `toList`, `keys`, `values`, `foldLeft`, **`foldRight`**, **`keySet`**, **`any`/`all`/`count`**, **`range lo hi`** (lo ≤ key < hi) | `size`, `isEmpty`, `toList`, `foldLeft`, **`foldRight`**, `any`, `count`, **`all`** |
| Instances | `Show`, **`DecEq`**, **`Ord`** | `Show`, **`DecEq`**, **`Ord`** |

Everything from "Read out" comes in key order, and that is a theorem.

**Status.** Built in SW-356 stage 2.2: every bold item in the table except the `DecEq` and
`Ord` instances (built in stage 2.1). `min`, `max`, `below`, `above` are O(log n) tree walks;
`mapWithKey` is a raw tree operation; the rest are defined from `foldLeft`, `insertWith`,
`filter`, `toList` and `fromList`. The combining operations were O(m log n) until the SW-356
bulk step made them O(n + m) (§4.6, "As built"). Naming: `Set.any`, `Set.all` and `Set.count` take the set first, as the existing
`Set.any` and `Set.count` do; `Map.range lo hi` returns a map; `Map.Tree.nearestBelow` and
`nearestAbove` are internal.

### 4.4 Lemmas to ship

With list meanings, most of these are short inductions.

- **`get`:**
  - `getEmpty`, `getInsert`, `getInsertOther`, `getInsertWith` (all kept);
  - `getRemove`, `getRemoveOther`, `getAlter`, `getAdjust`;
  - `getUnion`, `getUnionWith`, `getFilter`, `getFilterMap`, `getMap`;
  - `getFromList`, `getFromListWith`, `getGroupBy`.
- **Contents:**
  - `memToList` (`Mem (k, v) (toList m) ↔ get k m = Some v`);
  - `toListSorted`, `keysDistinct`;
  - `containsKeys`;
  - `sizeToList`, `sizeInsert` (`+1` unless present), `sizeRemove`.
- **Equality:** `ext`, `insertInsert` (same key, last wins), `insertComm` (different keys),
  `removeInsert`, `insertGet` (re-inserting the stored value changes nothing).
- **Folds and induction:**
  - `foldLeftToList` (`foldLeft f z m = List.foldLeft … (toList m)`);
  - `Map.induction` (`P empty`, and `P m -> get k m = None -> P (insert k v m)`).
- **`Set`:** the same, through `contains` (`containsRemove`, `containsUnion`, `containsIntersect`,
  `containsDifference`, `containsFromList`, `ext`, `isSubsetSpec`; later `sizeSubset`, `sizeIntersectLeft`, `sizeIntersectRight`).

**Status.** Built in stage 2.2: everything above except `memToList`, `sizeInsert`, `sizeRemove`,
`Map.induction` and `Set.isSubsetSpec`, which followed in the SW-356 leftovers step. Their
statements: `Map.memToList` is `Iff (List.Mem (key, value) (toList m)) (get key m = Some value)`;
`Map.sizeInsert` gives `size (insert key value m)` as `if contains key m then size m else size m + 1`,
and `Map.sizeRemove` gives `size (remove key m)` as `if contains key m then size m - 1 else size m`;
`Map.induction [p]` takes `p empty` and a step `(key) (value) (m) -> p m -> get key m = None -> p (insert key value m)`
and gives `p m` for every map (proved by taking the first entry of `toList` off with `remove`);
`Set.isSubsetSpec` is `Iff (isSubset a b = True) ((key) -> contains key a = True -> contains key b = True)`,
with the two directions as `Set.isSubsetElim` and `Set.isSubsetIntro`.
Also built: `getInsertWithOther`, `getAlterOther`, `getAdjustOther`, `getOrCounts`, `getRange`,
`getMapKeys`, `getMapWithKey`, `getIntersectWith`, `getDifference`, `minToList`, `maxToList`,
`belowToList`, `aboveToList`, `Set.containsInsertOther` and the general `Map.getFold`.
`Set.containsFromList` states membership with `List.any (x => Map.Spec.sameKey key x) xs`,
`Map.getGroupBy` likewise compares keys with `Map.Spec.sameKey` (by the ordering's `compare`);
`Map.getOrCounts` is stated with `==`: `(Map.counts xs).getOr key 0 = xs.count (== key)`.

### 4.5 JS boundary (D744)

- **Keep** `Map Text V` (in `Text` order) as a plain object, unchanged.
- **Add** maps with `Nat`/`Int`/`Char`/`Bool` keys, in the default order, as `ReadonlyMap<K, V>`
  on input and `Map<K, V>` on output, with entries inserted in key order. JS `Map` compares
  `bigint` and `string` keys by value [unverified for the spec's SameValueZero on `bigint`; check
  before building].
- **Add** compound keys (tuples, records) as `ReadonlyArray<readonly [K, V]>`, with a duplicate
  key refused with `StitchwortInputError`. JS `Map` would compare object keys by identity, which
  is wrong.
- **Same for sets:** `ReadonlySet`/`Set` for scalar keys, arrays otherwise.
- **The representation change is invisible** at the boundary: decoding builds through `fromList`,
  encoding reads `toList`, as today [checked: `dictionary.sw:1-5`].

### 4.6 Performance targets

- **Fast runtime and JS:** no slower than today's figures in §1.2 (±10%) at 10^5 and 10^6, with
  10^6 inserts and lookups stack-safe in both.
- **Bulk operations** (`union`, `filter`, `intersect`, `difference`, `fromList` on sorted input)
  become O(n + m) or O(n) at run time, through tree versions built on `toList`/`fromAscending`
  (simple, provable) in stage 2.
- **Reference evaluator:** O(n) per update. For example 10^4 single inserts is about 5·10^7 steps;
  a measured 10^4 list build hit the limit **[run]**. That's acceptable only because the reference
  evaluator is for proofs and differential tests on small inputs [checked: `docs/testing.md:39`].
  This is a risk (§5).
- **Later and separate:** the ~90× gap to native JS `Map` is a constant-factor matter (erased
  record allocation, `bigint` comparisons), not part of this note.

**As built (SW-356, bulk step).** The bulk operations go through sorted lists, as planned:
`Map.Spec.merge both onlyLeft onlyRight xs ys` walks two ascending entry lists in step, keeping
what each function returns for keys in both, only the left, or only the right; `unionWith`,
`intersectWith` and `difference` are instances (`Map.Spec.unionWith` and friends). The result
goes back into a tree with `Map.Raw.fromSorted`, which builds a perfectly balanced tree from an
ascending list in O(n) (half the entries left, one at the root, the rest right; the proofs that
it is ordered and sized come from the list being ascending). So:

- `Map.union`, `unionWith`, `intersectWith`, `difference`, and `Set.union`, `intersect`,
  `difference`, are O(n + m). When the first map is much smaller (8 × its size ≤ the second's)
  they instead insert or look up its entries in the second map, O(n log m), so a small update to
  a big map isn't O(m). `union`, `unionWith` and `difference` do the same when the second map is
  the much smaller one, inserting or removing its entries in the first. (Haskell's `Data.Set` gets
  O(m log(n/m + 1)) for both, citing Blelloch, Ferizovic and Sun's join-based algorithms,
  <https://hackage-content.haskell.org/package/containers-0.8.1/docs/Data-Set.html>; folding over the smaller side keeps the proofs to the
  per-key `insert` and `remove` lemmas.)
- `Map.filter` and `Map.filterMap` (through `Map.Raw.mapMaybe`) are O(n): filter the entry list,
  rebuild.
- `Map.fromList` checks in one pass whether the keys are strictly ascending, and if so builds the
  tree directly, O(n); otherwise it inserts as before, O(n log n). `Set.fromList` still inserts.
- `Set.isSubset` is unchanged: it looks up each key of `a` in `b`, O(n log m), allocates nothing
  and stops at the first missing key.
- Every existing lemma still holds with its statement unchanged: `toListUnion`, `toListFilter`,
  `getUnionWith`, `getUnion`, `getIntersectWith`, `getDifference`, `getFilterMap`, `getFilter`,
  `Set.containsIntersect`, `containsDifference`, `toListFromList`, `getFromList` and the rest.
  The new raw operations have `toList` lemmas (`Map.Raw.toListUnionWith`, `toListIntersectWith`,
  `toListDifference`, `toListMapMaybe`, `toListFromSorted`) and `Equiv`-respect lemmas, and the
  map operations are lifted through `Map.liftBinary`.
- Measured **[run]**, 24 Oct: two maps of 10^5 entries each (keys `2i` and `3i`, plus one fresh
  key per repetition), ten operations per program, wall time of `stitchwort run --no-cache` (fast
  runtime) and `run --js --no-cache`, best of three, seconds, including checking and building
  both maps (the `build` row; `Map.fromList` of the sorted input now takes the O(n) path):

  | Program | Before, fast | After, fast | Before, JS | After, JS |
  |---|---|---|---|---|
  | build only | 2.27 | 1.21 | 1.50 | 1.26 |
  | `union` | 8.19 | 2.73 | 4.57 | 1.92 |
  | `unionWith Nat.add` | 8.22 | 2.59 | 5.06 | 1.86 |
  | `intersectWith Nat.add` | 7.12 | 1.91 | 4.31 | 1.57 |
  | `difference` | 9.97 | 2.07 | 6.14 | 1.58 |
  | `Set.union` + `Set.intersect` of the key sets | 13.87 | 3.81 | 7.20 | 2.34 |
  | `filter` (a quarter kept) | 5.31 | 1.59 | 3.08 | 1.34 |

  One `union` of two 10^6-entry maps runs in both the fast runtime and exported JS (no stack
  overflow): the merge is tail-recursive modulo cons, and the tree build recurses only to depth
  log₂ n.

### 4.7 Migration

- **No compatibility layer.** `Map.Tree` becomes a runtime-only helper module, `.tree` stops
  existing, and the field names change.
- **What gets updated:**
  - `examples/accept/map-set.sw`;
  - `examples/extract/dictionary.sw` (its `same` becomes `a == b`);
  - `examples/accept/int-literals-auto.sw`;
  - AoC day 8 and its proofs. `Labels.sw`'s `lookupLast` facts get simpler with `getFromList` on
    a sorted input.
- **The port** drops its sorted-list workaround and uses `Map` with derived `==`.
- `examples/accept/data-auto.sw` defines its own toy `Map` and is unaffected.

## 5. Staging, cost, risks, acceptance

**Stage 1: canonical `Map`/`Set` in the library.** About 2–3 lane-days, Opus for proofs.

- List-based `Map`/`Set` with the full API (§4.3), the lemmas (§4.4), and `DecEq`/`Ord`/`Show`
  instances.
- It isn't merged to `main` on its own, because run-time speed would regress (§1.2). It merges
  together with stage 2, or with a temporary trusted-native path (D749).

**Stage 2: refinement.** About 3–4 lane-days.

- The representation attribute; the shape check for agreement theorems; the substitution in
  `stitchwort-rt` lowering and the JS backend; and the `.entries` bridges.
- The tree operations with `Ordered`-preservation and agreement proofs: `rebuildOnto` and
  `lookupOnto` already cover much of it [checked: `Map.sw:376-419`].
- Differential tests: `run` vs `run --reference` and JS vs reference, on random maps.

**Stage 3: JS boundary for non-Text keys (§4.5).** About 1 lane-day.

**Stage 4: migration and docs.** About 1 lane-day: aoc/, examples, the language guide,
map-set.md marked superseded.

**Risks:**

1. **The agreement proofs** for `remove` (`glue`/`deleteMin`) and the merges are the heaviest new
   proofs. Mitigation: bulk operations go through `toList`/`fromAscending` first.
2. **The trusted substitution step** is new. Mitigation: it's generic and small, with a shape
   check; differential tests; and the reference evaluator stays the oracle.
3. **The reference evaluator gets slower** on big maps (O(n) per update). This affects
   `run --reference` on AoC real inputs in `run_reference.rs`. Day 8's map has 1,000 entries, so
   it's fine [inferred]. A future program with 10^5 updates would need its reference run skipped.
4. **`rfl` on concrete maps** may not reduce as hoped (§4.2). Mitigation: `Map.ext` plus a
   decision.
5. **`DecEq (Map k v)` needs `DecEq v`,** so maps of functions still have no `==`, as is correct.

**Acceptance tests:**

1. A record with a `Map Text Nat` field, and one with a `Set (Nat, Nat)` field, derive `==` and
   `Ord`. The `Inventory` example of §1.1 checks and its test passes.
2. `Map.fromList [(1, "a"), (2, "b")] == Map.fromList [(2, "b"), (1, "a")]` is `True`.
   `Map.fromList [(1, "a"), (2, "b")] = Map.fromList [(2, "b"), (1, "a")]` is proved, by `rfl` if
   §4.2 holds, otherwise by `Map.ext`. A theorem proves `insert a x (insert b y m) = insert b y
   (insert a x m)` for `a != b`, for every `m`.
3. 10^5 and 10^6 ascending and random-order inserts and lookups run stack-safely in
   `stitchwort run` and exported JS, within §4.6's targets.
4. The §4.4 lemmas are proved, with no `sorry`-style escape. Each has a unit test beside it.
5. Every AoC program prints the same output as before on real and example inputs. The existing
   `run` vs `--reference` and JS differential suites pass.
6. JS: `ReadonlyMap<bigint, V>` and entry-array round trips; a duplicate key is refused; Text-key
   objects behave exactly as today (`dictionary.sw`'s `-- run:` lines unchanged except `same`).

## 6. What this doesn't do

- **No hash maps.** Hash maps need a `Hash` interface and are canonical only as hash tries. No
  trigger yet.
- **No mutable or in-place maps.**
- **No proof of balance.**
- **No quotient types.**
- **No `Eq` (BEq-style) interface:** (c) stays open for types with no canonical form, if one
  turns up.

## 7. Decisions

- **D740 — Equality approach.** (a1) canonical meaning plus refinement / (c) a separate `Eq`
  interface / (b) quotients / (a2) treap / (d) lemmas only. **[(a1) + refinement]**
- **D741 — How maps run fast.** (a) proved refinement: tree code in Stitchwort, kernel-checked
  agreement theorems, and a generic backend substitution / (b) trusted natives in Rust and JS,
  like `Text` / (c) neither, accept list speed. **[a; b as fallback if stage 2's mechanism costs
  more than estimated]**
- **D742 — Form of the order invariant.** A Bool equation `isAscending ord entries = True`
  (unique proofs by existing lemmas) / a recursive `Prop`. **[Bool equation, with a lemma to
  `List.Sorted`]**
- **D743 — API names (§4.3),** including `groupBy`, `counts`, `fromListWith`, `unionWith`,
  `below`/`above`, `range`, `keepOnly`/`removeAll`. **[approve as listed]**
- **D744 — JS boundary for other keys (§4.5).** Scalar keys as JS `Map`/`Set`, compound keys as
  entry arrays / keep Text-only. **[scalar as `Map`, compound as arrays]**
- **D745 — `Set` stays a record around `Map k ()`** and gets `DecEq`/`Ord`/`ext` the same way.
  **[yes]**
- **D746 — No Bool `Eq` interface now;** `==` stays `DecEq`. **[defer until a type without a
  canonical form needs it]**
- **D747 — Hash maps out of scope.** **[yes]**
- **D748 — Performance targets of §4.6** (no regression at 10^5 and 10^6; stack-safe at 10^6;
  O(n + m) bulk operations). **[yes]**
- **D749 — Staging.** Stages 1 and 2 merge together, so `main` never runs list-speed maps.
  **[yes]**
