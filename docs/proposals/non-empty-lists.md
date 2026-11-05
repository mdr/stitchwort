# Non-empty lists, `NonEmpty a` (SW-1337)

**Status:** design note, 5 November 2026, for Matt's decisions (§13). No
implementation yet. Background: Matt (D2383): "how we might do non-empty
lists in the standard library so that we can have things like reduce …
having more precise types is powerful." The prompt was 2020 day 6, where
`group.people.foldLeft (Set.fromList questions) …` would be
`group.people.map .answers |> .reduce Set.intersect` if a group's people
were non-empty by type.

Claims about Stitchwort are **[checked]** when I read or ran the thing named
(on `lane/SW-1337` at `a3e7f8116`, with the release binary built from
`main`), **[estimate]** when they are my reading of what will happen. Claims
about other languages are **[verified]** where I read the library source or
its docs (listed under Sources), otherwise from memory, **unverified**.

## 1. In short

- **The problem.** Many lists in the code base can never be empty: a
  group's people, the numbers on an equation's line, a grid's rows, what
  `Parse.many1`, `sepBy1`, `lines` and `sections` return, the groups
  `List.splitBy` makes. The types don't say so, so code that needs a first
  element makes one up: `foldLeft 0 Nat.max`, `.maximum.getOrElse 0`,
  `.headOr Bits.empty`, a `| [] => False` arm that never runs, a
  "never used" `fallbackRoom`, or a proof hypothesis `xs ≠ []` carried by
  hand. The survey (§10) found about 95 such sites in aoc/ and games/rogue.
- **The change.** A library type `NonEmpty a`, a record with a first element
  and the rest: `{ head: a, tail: List a }`, as Haskell, Agda and Idris 2
  have it. Its operations are total where `List`'s return `Option`:
  `reduce`, `head`, `last`, `maximum`, `minimum`, `maxBy`, `minBy`; and the
  ones that keep a list non-empty return one again: `map`, `zip`, `sort`,
  `reverse`, `++`. `xs.toList` goes back, and `xs.toNonEmpty` (given a proof
  that `xs ≠ []`, found by `auto`) or `xs.nonEmpty` (an `Option`) goes
  forward. The parsers that read at least one value return a `NonEmpty`.
- **Brackets.** In a later stage, `[1, 2, 3]` and the pattern `[x, ..xs]`
  work for a `NonEmpty` where the type says so, and `[]` there is an error
  saying a `NonEmpty` can't be empty (§7).
- **Proofs.** `xs.toList` is `[xs.head, ..xs.tail]`, a `Cons` for every `xs`,
  so each `NonEmpty` operation's link to its `List` twin is `rfl`, and the
  `List` lemmas apply through it (§9). Nothing new in the kernel; nothing new
  in the elaborator for stage 1.
- **Size.** Stage 1, the type and its API: about half a day on Sonnet.
  Stage 2, the parsers and their `Reads` lemmas: half a day. Stage 3,
  brackets: about a day on Opus. Then sweeps of aoc/ and rogue, a few days'
  worth in small lanes (§12).

## 2. What happens today

**The `List` functions that need a first element return `Option`**
**[checked]**: `List.head`, `List.last` (crates/elab/src/std/List/Toolkit.sw:269,
:263), `List.maximum`, `List.minimum` (:96, :101), `List.maxBy`, `List.minBy`
(:631, :643), `List.maximumOf`, `List.minimumOf` (:653, :662, each defined as
`(xs.map f).maximum`). `List.headOr` takes a fallback
(core/ListOptionPair.sw:21). There is no `reduce` or `foldLeft1`. Each of the
six is written as "match `[x, ..xs]`, then `foldLeft xs x`", wrapped in
`Some`:

```
def List.maximum [auto ord: Ord a]: List a → Option a
  | [] => None
  | [x, ..xs] => Some (List.foldLeft xs x Ord.max)
```

So the `NonEmpty` versions are those `Some` branches, unwrapped.

**A proof argument works today, but only for what's visible.** A function on
`List` can take the proof Idris and Lean take, `[auto nonEmpty: xs ≠ []]`.
I wrote one in a scratch file **[checked]**:

```
def reduce (xs: List a) (f: a → a → a) [auto nonEmpty: xs ≠ []]: a :=
  match xs with
    | [] => Void.absurd (nonEmpty rfl)
    | [x, ..rest] => rest.foldLeft x f
```

`auto` finds the proof for a literal (`reduce [3, 1, 2] Nat.max`), in the
`[x, ..rest]` arm of a match, and after `if h: xs ≠ []`. It does not find it
for `reduce (xs.map f) …` with `xs ≠ []` in scope, or for `reduce [..xs, y]`:
both are `E-AUTO-STUCK`, "can't decide `List.map xs (n => n + 1) ≠ []`
here" **[checked]**. `auto` decides by computing, and doesn't look up the
lemma `map` keeps a list non-empty. So every step between where a list is
known to be non-empty and where it is used needs a lemma named by hand.

**Grid carries a proof field.** aoc/src/Aoc/Common/Grid.sw:139 is
`type Grid (a: Type) = { rows: List (List a), nonEmpty: (firstWidth rows ==
0) = False }`, with `Grid.of`'s `[auto nonEmpty: …]` (:142), and its comment
says why it's a `Bool` equation and not `≠`: "so that grids have `==` and
the counterexample search can make them" **[checked]**. A record with a
`≠ []` field gets no `==`: "its field `nonEmpty` is a proof of something
other than an equation" (`E-INSTANCE-NONE`, scratch file) **[checked]**.

**The parsers already build `[first, ..rest]`.** `Parse.many1` and
`Parse.sepBy1` (Parse/Parse.sw:394, :436) read one value, then `many` more,
and return `[first, ..Parse.many parser]`; `lines`, `sections` and `grid` are
`sepBy1` and `many1` (:451, :454, :492) **[checked]**. Their lemmas say so in
a proposition: `Parse.readsMany1`'s spec ends `∧ values ≠ []`
(Parse/Reads.sw:763), and `Parse.SepBy` begins `∃ (first: a) => ∃ (rest:
List a) => values = [first, ..rest] ∧ …` (Reads.sw:774) **[checked]**.

**`List.splitBy` documents "no group is empty"** (Toolkit.sw:387) and proves it
(`List.splitByGroups`); `Map.groupBy`'s values are never empty either
(`Map.getGroupBy`, Map/Map.sw:854, through `Map.Spec.nonEmpty`)
**[checked]**. Both return plain `List`s.

**The only non-empty type today** is `Vec a (Succ n)`: `Vec.head` and
`Vec.tail` take one (Vec/Vec.sw:19, :23) **[checked]**.

## 3. Other languages

| Language | Non-empty list | Its "reduce" | Bridges from the plain list |
|---|---|---|---|
| Haskell (base) | `data NonEmpty a = a :| [a]`, `Data.List.NonEmpty`, since base 4.9 **[verified]** | `Foldable1` (`foldMap1`, `maximum`, `minimum`), in base since 4.18 **[verified]**; `sconcat` from `Semigroup` | `nonEmpty :: [a] -> Maybe (NonEmpty a)`, `toList` **[verified]**; an `IsList` instance for list literals under `OverloadedLists`, whose `fromList` fails at run time on `[]` (unverified) |
| Idris 2 (base) | `record List1 a where constructor (:::); head : a; tail : List a`, `Data.List1` **[verified]** | `foldr1`, `foldl1 : (a -> a -> a) -> List1 a -> a`, `last`, `init`; `Functor`, `Foldable`, `Semigroup` instances **[verified]** | `forget`, `fromList : List a -> Maybe (List1 a)`; and `toList1 : (l : List a) -> {auto 0 ok : NonEmpty l} -> List1 a` **[verified]** |
| Idris 2, also | a predicate `data NonEmpty : List a -> Type where IsNonEmpty : NonEmpty (x :: xs)` (Data.List) **[verified]** | `head`, `last`, `init`, `minimum`, `foldr1`, `foldl1` on plain `List`, each with `{auto 0 ok : NonEmpty l}` **[verified]** | (it is the plain list) |
| Agda (stdlib) | `record List⁺ (A : Set a) : Set a where constructor _∷_; field head : A; tail : List A`, `Data.List.NonEmpty` **[verified]** | `foldr₁`, `foldl₁`, `last`; `map`, `zip`, `concat : List⁺ (List⁺ A) → List⁺ A` **[verified]** | `toList`, `fromList : List A → Maybe (List⁺ A)`; `wordsBy` returns `List (List⁺ A)` **[verified]** |
| Lean 4 (core) | none: the functions take a proof, `l.head hl`, `l.max hl` with `(hl : l ≠ [])`; `List.max?` returns `Option`, tied by `max?_eq_some_max` **[verified]** | `l.max hl`, `l.min hl` | (it is the plain list) |
| Lean 4 (Batteries, Mathlib) | no type yet. A January 2026 Batteries thread weighed a subtype (a list and a `≠ []` proof) against a head/tail structure, with experimental PRs for each (batteries#1607, #1609), and reached no decision **[verified]** | — | — |

Three things stand out. Every library that has a type uses the same shape,
a head and a tail, as a record (Idris, Agda) or a constructor (Haskell). Idris
has both the type and the proof-argument style, and joins them with
`toList1`. And the Lean thread names the trade-off this note faces (§4):
the head/tail shape makes "a list starting with `x`" definitional, the
subtype makes "the list inside" definitional; the second reuses `List`'s
functions directly, the first has to wrap each one.

Haskell's groupings return `[NonEmpty a]` (`group`, `groupBy`), with
`group1`, `groupBy1` returning `NonEmpty (NonEmpty a)` **[verified]**; Idris's
`split` and `splitOn` return `List1 (List a)` **[verified]**. That is the
shape `List.splitBy` and `Parse.sections` would take here.

## 4. The options

### A. A record with a head and a tail

```
--| A list with at least one element: `head`, then the rest.
type NonEmpty (a: Type) = { head: a, tail: List a }

def NonEmpty.toList (xs: NonEmpty a): List a := [xs.head, ..xs.tail]
def NonEmpty.reduce (xs: NonEmpty a) (f: a → a → {e} a): {e} a := xs.tail.foldLeft xs.head f
def NonEmpty.maximum [auto ord: Ord a] (xs: NonEmpty a): a := xs.reduce Ord.max
def NonEmpty.map (xs: NonEmpty a) (f: a → {e} b): {e} NonEmpty b := { head = f xs.head, tail = xs.tail.map f }
```

Day 6 reads:

```
type Group = { people: NonEmpty Person }

def Group.everyone (group: Group): Set Char := group.people.map .answers |> .reduce Set.intersect
```

What I checked in scratch files **[checked]**: the record, these functions,
record patterns (`| { head, tail = [y, ..ys] } => …`), a derived `==`, a data
type nested through it (`| Node (children: NonEmpty Tree)`, with recursion on
`head`), and the bridge lemmas `xs.toList.maximum = Some xs.maximum` and
`(xs.map f).toList = xs.toList.map f`, both `rfl`. A list literal against it
is `E-TYPE-MISMATCH` today, "expected `NonEmpty Nat`, but this has type
`List ?0`", which §7 changes. The derived `Show` prints the record, `{ head
= 1, tail = [2] }`; the library would give it one that prints `[1, 2]`.

- **For:** the type is the fact, so no proof travels with it and `auto`
  never has to find one. Operations are total by construction. `==`, `Show`,
  `Ord`, counterexample search and the JS boundary all work as for any
  record of data. It is what Haskell, Agda and Idris chose. Proofs see a
  `Cons` (§9).
- **Against:** every `List` operation that should keep non-emptiness has to
  be written again (one line each, mostly through `tail`), and code that
  wants the list writes `.toList`; there are no coercions (D1069), so that
  is explicit.

### B. A subtype: a list and a proof

```
type NonEmpty (a: Type) = { items: List a, nonEmpty: items ≠ [] }
```

Stitchwort has no subtype syntax (`{ x: T // p }`), but a record with a proof
field is the same thing (syntax.md, Records, `Sized`; the microtypes recipe's
`Email`) **[checked]**.

- **For:** `xs.items` is the list itself, so a `List` function applies with no
  conversion and its lemmas apply with no bridge.
- **Against:** `≠ []` gives no `==` (§2); Grid works around it with `(items
  == []) = False`, which needs `DecEq a` to state. Every operation that
  returns one needs a proof: `map` needs "map keeps a list non-empty",
  `reduce` matches with an absurd `[]` arm. Taking it apart in a proof means
  matching `items` and refuting `[]` each time. The Lean thread's point
  stands: the head isn't definitional.

### C. Functions on `List` with a proof argument

`List.reduce (xs: List a) (f) [auto nonEmpty: xs ≠ []]`, Idris's and Lean's
other style. It works today for literals, after a match and after `if h:`
(§2) **[checked]**.

- **For:** no new type, nothing to convert, nothing to re-prove.
- **Against:** the proof has to be found at each use, and `auto` finds it only
  where the list is visibly a `Cons`: after any `map`, `filter`-that-can't-
  empty, `sort` or `++`, it is `E-AUTO-STUCK` and the code names a lemma.
  The data types don't change: `Group.people` is still a `List`, so the fact
  that it isn't empty has to be stored beside it (a `Grid`-style field) or
  re-proved at each use. It removes `getOrElse` from the use, not from the
  model.

### D. `Vec a (n + 1)`

`Vec.head` already takes one **[checked]**. But the length is in the type, so
a list of unknown length is `(n: Nat, Vec a (n + 1))`, a pair to pack and
unpack, and every operation has to compute its result's length in the type
(`filter` can't). Right where the length is known and matters, as rogue's
six rooms (`Vec Area 6`, §10), wrong as the general answer.

### E. An interface

Haskell's `Foldable1` is a class over the container, `t :: Type -> Type`.
Stitchwort's interfaces take one parameter that is a type, `Pretty (List a)`
(syntax.md, Interfaces) **[checked]**, so a class over containers isn't
expressible today, and with only `NonEmpty` and `Vec (n + 1)` to cover it
wouldn't earn its place. A `Semigroup`-like interface (an associative
`combine`, no unit) would let `xs.reduce` find its function, but `Set` has two
(`union`, `intersect`) and so does `Nat` (`max`, `+`, `*`), which is why
Haskell needs `Max`, `Min` newtypes. Passing the function, as `foldLeft` does
now, reads better: `.reduce Set.intersect`.

### Comparison

| | A record | B subtype | C proof argument | D `Vec (n+1)` |
|---|---|---|---|---|
| Fact lives in | the type | a field | each use | the type, with the length |
| `==`, `Show`, counterexamples | derived | no `==` with `≠` | as `List` | as `Vec` |
| Models a field (`people`) | yes | yes | no | awkward |
| Ops that keep it non-empty | rewritten, one line each | each needs a proof | each use needs a lemma | each computes a length |
| `List` lemmas | via `toList`, `rfl` bridges | direct | direct | via `Vec.toList` |
| New language work | none (brackets later) | none | none | none |

## 5. Recommendation

**A, the record**, named `NonEmpty`, in `std/List/NonEmpty.sw`, imported as
`import Std (NonEmpty)`. Plus two bridges from `List`, which take Idris's
`toList1` idea for the places C is good at:

```
--| The list as a `NonEmpty`, where it is known not to be empty.
def List.toNonEmpty (xs: List a) [auto nonEmpty: xs ≠ []]: NonEmpty a

--| The list as a `NonEmpty`, or `None` for an empty list.
def List.nonEmpty: List a → Option (NonEmpty a)
```

so `if h: xs ≠ [] then xs.toNonEmpty.maximum else …` and `match
xs.nonEmpty with | Some ne => … | None => …` both work. I would not add
proof-argument versions of `head`, `maximum` and the rest to `List`: two
ways to say the same thing, and C's weakness (lemmas at each step) is what
the type removes.

Matt's "more precise types" is A's strength: it changes the model
(`Group.people: NonEmpty Person`), not only the call.

The name: `NonEmpty` is the plain description and Haskell's and Agda's
module name; `List1` (Idris) is shorter but needs explaining. A
`NonEmpty.of` is not needed: `{ head = x, tail = xs }` until brackets
arrive, `[x, ..xs]` after.

## 6. The API

Each mirrors the `List` function of the same name, so code changes type, not
spelling. Effect-polymorphic as `List`'s are (`f: a → {e} b`).

- **Total where `List` returns `Option`:** `head` and `tail` (the fields),
  `last`, `init` (a `List`), `reduce` (left to right, `foldLeft tail head`),
  `reduceRight`, `maximum`, `minimum`, `maxBy`, `minBy` (first wins on a tie,
  as `List.maxBy` documents), `maximumOf`, `minimumOf`.
- **Keep non-emptiness:** `map`, `mapWithIndex`, `zip`, `zipWith`, `reverse`,
  `sort`, `sortBy`, `sortWith`, `distinct`, `scanLeft` (starting from a
  value, its result always has one), `append` (`++` with a `NonEmpty` or a
  `List` on either side; one of each gives a `NonEmpty`), `cons` (`x` in
  front of a `List` gives a `NonEmpty`), `singleton`, `flatten` (of a
  `NonEmpty (NonEmpty a)`), `flatMap`.
- **Give a plain `List`:** `toList`, `filter`, `filterMap`, `take`, `drop`. These are `xs.toList.filter p` and so on, written out so dot
  notation finds them.
- **The same as on the list:** `length` (and `lengthPos: 0 < xs.length`),
  `sum`, `product`, `sumBy`, `count`, `all`, `any`, `contains`, `foldLeft`,
  `foldRight`, `get`, `getOr`, `∈`. `middle` (`xs.get (xs.length / 2)`, total)
  for day 10 and 2024 day 5.
- **Instances:** `DecEq` and `Ord` (lexicographic, as `List`'s, so equal to
  comparing `toList`s), `Show` printing `[1, 2, 3]`, and `Each` if the
  `Each` ability's lists want it [estimate].
- **Producers in std:** `List.splitBy` returns `List (NonEmpty a)` (its doc
  already says no group is empty); `Map.groupBy` returns `Map k (NonEmpty
  a)`; `Nat.digits` returns `NonEmpty Nat` (it has `Nat.digitsNonEmpty`
  today). `Text.split` can't return an empty list either, but it is `Text`,
  and the parsers are §8.

`List.maximum` and the others stay as they are: on a list that may be empty,
`Option` is the right answer.

## 7. Brackets for `NonEmpty`

Today brackets are `List` only: a literal is checked against the expected
type, and anything but a `List` falls back (crates/elab/src/check.rs:4006,
`if *d != list { return fallback_named(…) }`); list patterns resolve to the
library's `Nil` and `Cons` by identity (crates/elab/src/lib.rs:4029-4052)
**[checked]**.

Proposed, once the type exists:

- **Literals.** Where a `NonEmpty a` is expected, `[a, b, c]` is `{ head = a,
  tail = [b, c] }`, `[x, ..xs]` is `{ head = x, tail = xs }`, and a spread
  first (`[..ys, z]`) is `ys ++ [z]` with the `NonEmpty` `++`. `[]` is an
  error: "a `NonEmpty` has at least one element; this is empty" (a new code,
  `E-NONEMPTY-EMPTY`, or `E-TYPE-MISMATCH` with that note). `[..xs]` alone
  where `xs` is a `List` is the same `E-TYPE-MISMATCH` as today, with a note
  to write `xs.toNonEmpty`.
- **Patterns.** On a `NonEmpty`, `[x, ..xs]` is `{ head = x, tail = xs }`,
  `[x]` is `{ head = x, tail = [] }`, `[x, y, ..ys]` is `{ head = x, tail =
  [y, ..ys] }`; so coverage is the record's, and `[x, ..xs]` alone covers
  everything (no `[]` arm, and writing one is "can't be empty"). This needs
  the scrutinee's type where the pattern is resolved, which `lib.rs:4029`
  does not use today **[checked]**; the record and tuple patterns already
  need a known type (syntax.md, "Record patterns … when the type of what they
  match is known") **[checked]**, so the same rule applies.
- **Goals and printing.** `{ head = x, tail = [y, ..ys] }` prints as `[x, y,
  ..ys]` when it's a `NonEmpty`, as `list_literal` does for `Cons` chains
  (crates/core/src/pretty.rs) [estimate].
- **Where the type isn't known**, a literal stays a `List`, as now: `let xs :=
  [1, 2]` is a `List Nat`. No guessing.

This is Haskell's `OverloadedLists` limited to one type, and total: `[]` is
refused where Haskell's `fromList []` fails at run time. Stage 1 does not
need it; it is what makes `NonEmpty` feel like a list rather than a record
(§13, N4).

## 8. Parsers

`many1`, `sepBy1`, `lines`, `sections` and `grid` return `NonEmpty`:

```
def Parse.many1 (parser: () → {Parse} a): {Parse} NonEmpty a :=
  let first := parser()
  { head = first, tail = Parse.many parser }
```

and `grid` returns `NonEmpty (NonEmpty a)`. `Parse.repeat (atLeast := 1)`
keeps returning a `List` (its count is a value, not in the type).
`Parse.takeWhile1` returns `Text`, unchanged.

**Callers.** The survey counts about 50 uses in aoc/ and games/ (§10). Most
call `.map`, `.length`, `.sumBy`, `.foldLeft` or `.all` on the result, which
`NonEmpty` has under the same names, so they compile unchanged
[estimate]. Those that store the result in a record field typed `List` or
pass it to a function taking a `List` either add `.toList` or, better,
change the field to `NonEmpty`: that is the point (2024 day 7's `numbers`,
day 6's `answers`). Migration cost doesn't count; the end state is the
question, and in the end state a `many1` result that says it is non-empty is
the better model.

**Lemmas.** In Parse/Reads.sw, `readsMany1`'s spec drops `∧ values ≠ []` and
states `Parse.Each spec read values.toList`; `Parse.SepBy`'s `∃ first rest,
values = [first, ..rest] ∧ …` becomes a statement about `values.head` and
`values.tail` directly, one existential pair shorter. Since `values.toList`
is `[values.head, ..values.tail]` by computation, the proofs keep their shape
[estimate]. Three proof files outside std name these lemmas (`readsMany1`,
`readsSepBy1`, `readsLines`, `readsSections`, `readsGrid` or `SepBy`)
**[checked]**, plus the days whose proofs `rewrite` with them; each is a
mechanical restatement.

The alternative is to keep the five returning `List` and add `many1NonEmpty`
and so on. It saves the migration and leaves two names for one parser, and
the `List` ones would still be the ones that model the data worse.

## 9. Proofs

- **Through `toList`.** `NonEmpty.toList xs` is `[xs.head, ..xs.tail]`, a
  `Cons` for every `xs`, known or not. So `List` functions compute on it
  one step: `xs.toList.foldLeft z f` is `xs.tail.foldLeft (f z xs.head) f`,
  `xs.toList.maximum` is `Some (xs.tail.foldLeft xs.head Ord.max)`, which is
  `Some xs.maximum` by `rfl` **[checked]**. So each `NonEmpty` function gets
  one bridge lemma to its `List` twin, mostly `rfl` (`(xs.map f).toList =
  xs.toList.map f` is `rfl` **[checked]**), and through it every `List`
  lemma: `NonEmpty.maximumMem: xs.maximum ∈ xs.toList` is
  `List.maximumMem` applied to the bridge. That is the plan for std: state
  `NonEmpty` facts through `toList` and the existing `List` lemmas, adding
  direct ones only where they read better.
- **`xs.toList ≠ []`** is `List.consNotNil xs.head xs.tail` (a scratch
  file **[checked]**). `toList` is injective, and `List.toNonEmpty` and
  `toList` are inverse both ways, `rfl` from `NonEmpty` to `NonEmpty` and
  by a match on the list the other way [estimate].
- **Induction.** A `NonEmpty` isn't recursive; a proof matches `{ head, tail
  }` and inducts on `tail` as a `List`, or works on `toList`. Nothing new.
- **`ext`.** `NonEmpty.ext` is generated, since both fields are data
  (syntax.md, Records, `T.ext`) [estimate].
- **The kernel needs nothing.** It is a record of existing types. **The
  elaborator needs nothing for stages 1 and 2**; stage 3 (brackets) touches
  the literal path in check.rs, list patterns in lib.rs, and the printer.
- **The proving guide** gets a short paragraph: state facts through
  `toList`, and the list of bridge lemmas.

## 10. Sites that would read better

From a survey of aoc/ and games/rogue (solution code, not proofs). Counts are
by hand, so approximate [estimate]:

| Kind | Sites |
|---|---|
| `head`/`last`/`maximum`/`minimum`/`maxBy`/`minBy` with a made-up default (`getOrElse`, `headOr`, `None => 0`) | ~16 in solutions, ~12 `headOr` in tests |
| the same, whose `Option` is passed on (`solvePart: Option Nat`) | ~10 |
| `foldLeft` from a made-up start standing for the first element | ~13 |
| proof arguments or fields saying a list is non-empty | ~20 (Grid and four `auto` helpers, ~15 lemma hypotheses) |
| uses of at-least-one parsers | ~52, about 10 then meeting a dead `[]` case or a default |
| list matches whose `[]` arm is a dummy | ~10 of 74 `[]` arms |

The best, by how much the model improves (I read each of these; paths under
`aoc/src/Aoc/` unless given in full) **[checked]**:

1. **2020 day 6**, Year2020/Day06/Day06.sw:39, 65: `type Group = { people:
   List Person }` and `group.people.foldLeft (Set.fromList questions) (common
   person => common.intersect person.answers)`. With `people: NonEmpty
   Person`, `people.map .answers |> .reduce Set.intersect`: no made-up "all
   26 questions", which would be the wrong answer for an empty group.
   Parsing the groups with `sections (() => lines person)` instead of
   `splitBy` gives the type directly; `Person.answers` from `many1` becomes
   non-empty too.
2. **2024 day 7**, Year2024/Day07/Day07.sw:32, 63-65: `numbers` from `many1`,
   then `match equation.numbers with | [] => False | [first, ..rest] => …`.
   `numbers: NonEmpty Nat` removes the dead arm.
3. **2021 day 16**, Year2021/Day16/Day16.sw:46, 270-271: `subPackets: List
   Packet`, then `values.minimum.getOrElse 0`, `values.maximum.getOrElse 0`.
   The puzzle promises at least one sub-packet; as `NonEmpty Packet` (nested
   data through `NonEmpty` is accepted **[checked]**, §4 A) both are total.
   `Literal`'s groups (`groups != []` in Spec/Spec.sw:77 and a hypothesis in
   Proofs/Sound.sw:36) likewise.
4. **2021 day 7**, Year2021/Day07/Day07.sw:43-47: `rightmost` is
   `crabs.foldLeft 0 Nat.max` and `leftmost` starts from `rightmost crabs`,
   with a doc comment explaining what each means "when there are none". The
   crabs come from `sepBy1`; as a `NonEmpty`, `crabs.maximum` and
   `crabs.minimum`, and the caveat goes.
5. **2021 day 14**, Year2021/Day14/Day14.sw:113-121 (and Spec/Spec.sw:35):
   `match template with | [] => 0 | …` and `quantities.maximum.getOrElse 0 -
   quantities.minimum.getOrElse 0`. The template comes from `takeWhile1`;
   both defaults go.
6. **Grid**, Common/Grid.sw:131-142: `rows: List (List a)` with the field
   `nonEmpty: (firstWidth rows == 0) = False`, where `firstWidth` is
   `rows.headOr [] |> .length`. As `rows: NonEmpty (NonEmpty a)`, the field,
   `Grid.of`'s `auto`, `Grid.widthNonZero`'s proof, the rewrite in `Grid.map`
   (:191) and in `checkGrid` (:220), and the `[auto nonEmpty: …]` helpers in
   the 2021 day 9, 11 and 15 tests all go; `width` is `rows.head.length`, and
   `widthNonZero` is `lengthPos`. Rectangularity stays a proposition.
7. **2021 day 18**, Year2021/Day18/Day18.sw:104-106: `solvePart1: List Number
   → Option Nat | [] => None | [first, ..rest] => …`. Given `NonEmpty
   Number`, the sum is `numbers.reduce add`; the `Option` left is only the
   one for running out of steps.
8. **2021 day 3**, Year2021/Day03/Day03.sw:37-38: `(numbers.headOr
   Bits.empty).width`, with `bits` from `many1`. A `NonEmpty` report and
   `Bits` gives `numbers.head.width`, and `Bits.first` (Common/Bits.sw:35,
   `Option Bool`) becomes total.
9. **2021 day 10**, Year2021/Day10/Day10.sw:105: `middle (scores) :=
   scores.sort.getOr (scores.length / 2) 0`, "0 for none", and
   Proofs/Middle.sw:38 takes `(some: scores ≠ [])`. With `NonEmpty`,
   `scores.sort.middle` and no hypothesis.
10. **2024 day 5**, Year2024/Day05/Day05.sw:64:
    `update.pages.getOr (update.pages.length / 2) 0`, pages from `sepBy1`:
    the same `middle`.
11. **2024 day 21**, Year2024/Day21/Day21.sw:182: `choices.minBy
    costs.routeCost |> .getOrElse []`, where Proofs/Typing.sw:48 proves
    `routes from to != []`. `routes` returning `NonEmpty` removes the
    fallback and the proof side conditions.
12. **2025 day 9**, Year2025/Day09/Day09.sw:57: `def largest (areas: List
    Nat): Nat := areas.foldLeft 0 Nat.max`, "0 if there are none"; the same
    in 2024 day 22 (:69, Spec :102) and a 2025 day 3 test.
13. **2021 day 4**, Year2021/Day04/Day04.sw:65: `.foldLeft 0 (… Nat.max …)`
    over a board's lines (from `sections`/`lines`/`many1`) becomes `maximum`;
    the `draws.length` start of the `min` at :66 is a real answer ("never
    wins") and stays.
14. **Rogue**, games/rogue/src/Rogue/Generate.sw:57-60: `rooms.getOr index
    (rooms.headOr fallbackRoom)`, "Never used: `rooms` always has six." This
    is a `Vec Area 6` (option D's right place) or at least a `NonEmpty Area`.
    The rest of rogue's `getOrElse`s are on lists that really can be empty.
15. **2024 day 19**, Year2024/Day19/Day19.sw:29, 64-73: `Pattern.stripes`
    from `many1`, and `waysForSuffixes`, which always returns `[1]` or
    `[ways, ..later]` and is then read with `.headOr 0`.

## 11. Interactions

- **JS boundary.** A `NonEmpty a` crosses as a record `{ head, tail }` by
  default (DESIGN.md §12). An array `[a, ...a[]]` in TypeScript, checked
  non-empty on the way in, would be nicer; a later, separate decision, not
  needed for std or aoc.
- **Counterexample search** makes records of data, so `NonEmpty` values
  come for free [estimate], unlike a `≠ []` field (Grid's comment, §2).
- **`Each` and effectful `map`.** `NonEmpty.map` takes `f: a → {e} b` as
  `List.map` does; a `NonEmpty` in an `Each` block is its `toList`
  [estimate].
- **Formatter, LSP.** Nothing for stages 1 and 2; brackets (stage 3) print
  through the same path as lists.

## 12. Size and order of work

1. **The type and its API** (§6), with bridge lemmas and `List.toNonEmpty`,
   `List.nonEmpty`, in `std/List/NonEmpty.sw`; `Show`, `DecEq`, `Ord`
   instances; tests; a syntax.md section and a proving-guide paragraph.
   Sonnet, about 4 hours.
2. **std producers:** `List.splitBy`, `Map.groupBy`, `Nat.digits`, and the
   parsers `many1`, `sepBy1`, `lines`, `sections`, `grid` with their Reads.sw
   lemmas (§8), fixing the callers so everything builds. Sonnet, about 4
   hours (the callers are spread over many days, but each is mechanical).
3. **Brackets** (§7): literals, patterns, printing, the `[]` error. Opus for
   the pattern part (coverage and the scrutinee's type), about a day.
   Independent of 2; can go after 1.
4. **Sweeps:** the §10 sites, a few days per lane, starting with 2020 day 6
   and Grid (which touches 2021 days 9, 11, 15 and their proofs). Sonnet or
   DeepSeek, each with its proofs, after 2 (and after 3 if the brackets are
   wanted in the result).

## 13. Decisions for Matt

Numbered N1 to N7 here; the orchestrator gives them D numbers.

- **N1. Representation.** (a) a record `{ head: a, tail: List a }`; (b) a
  subtype record `{ items: List a, nonEmpty: items ≠ [] }`; (c) no type,
  `[auto nonEmpty: xs ≠ []]` arguments on `List` functions; (d) `Vec a (n +
  1)`. **[rec: (a)]**
- **N2. Name.** `NonEmpty` (Haskell, Agda's module), `List1` (Idris), or
  `List⁺` (Agda's type; not ASCII). **[rec: `NonEmpty`]**
- **N3. Bridges from `List`.** `List.toNonEmpty` with an `auto` proof and
  `List.nonEmpty` returning `Option`, and no proof-argument versions of
  `head`, `maximum` and the rest on `List`. **[rec: yes]**
- **N4. Brackets.** `[a, b]` literals and `[x, ..xs]` patterns for a
  `NonEmpty` where the type is known, `[]` refused there with its own error
  (stage 3); or record syntax only. **[rec: yes, as stage 3]**
- **N5. Parsers.** `many1`, `sepBy1`, `lines`, `sections` and `grid` return
  `NonEmpty`, callers updated; or new `…NonEmpty` variants beside them.
  **[rec: change them]**
- **N6. Other std producers.** `List.splitBy` → `List (NonEmpty a)`,
  `Map.groupBy` → `Map k (NonEmpty a)`, `Nat.digits` → `NonEmpty Nat`.
  **[rec: yes, in stage 2]**
- **N7. Sweeps.** Apply it to the §10 sites, the data types first (day 6's
  `Group`, Grid, 2024 day 7's `Equation`, 2021 day 16's `Packet`), with
  rogue's rooms as a `Vec Area 6`. **[rec: yes, after stage 2, a few sites
  per lane]**

And, for the orchestrator: stage 1 can start on Sonnet once N1-N3 are
settled; stage 3 waits for N4.

## Sources

Read on 5 November 2026:

- Idris 2 base, `libs/base/Data/List1.idr`: `record List1`, `(:::)` (infixr
  7), `forget`, `fromList`, `foldr1`, `foldl1`, `last`, `init`, instances.
  https://github.com/idris-lang/Idris2/blob/main/libs/base/Data/List1.idr
- Idris 2 base, `libs/base/Data/List.idr`: `data NonEmpty`, `IsNonEmpty`,
  `head`/`last`/`init`/`minimum`/`foldr1`/`foldl1` with `{auto 0 ok :
  NonEmpty l}`, `toList1`, `split` and `splitOn` returning `List1 (List a)`.
  https://github.com/idris-lang/Idris2/blob/main/libs/base/Data/List.idr
- Agda standard library, `src/Data/List/NonEmpty/Base.agda`: `record List⁺`,
  `_∷_`, `toList`, `fromList`, `foldr₁`, `foldl₁`, `map`, `zip`, `concat`,
  `wordsBy`.
  https://github.com/agda/agda-stdlib/blob/master/src/Data/List/NonEmpty/Base.agda
- Haskell base 4.22, `Data.List.NonEmpty`: `data NonEmpty a = a :| [a]`,
  `nonEmpty`, `toList`, `group`/`groupBy` returning `[NonEmpty a]`,
  `group1`, the `Foldable1` instance (since base 4.18), `IsList` instance.
  https://hackage.haskell.org/package/base/docs/Data-List-NonEmpty.html
  The run-time failure of `IsList`'s `fromList []` is from memory,
  **unverified**.
- Lean 4 core, `Init.Data.List.MinMax` (Mathlib docs): `List.max?`,
  `l.max hl` with `hl : l ≠ []`, `max?_eq_some_max`.
  https://leanprover-community.github.io/mathlib4_docs/Init/Data/List/MinMax.html
- Lean Zulip, #batteries, "Nonempty List Type", January 2026: subtype versus
  head/tail structure, batteries#1607 and #1609, no decision.
  https://leanprover-community.github.io/archive/stream/348111-batteries/topic/Nonempty.20List.20Type.html
