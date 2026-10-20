# Proposal: interfaces

**Status:** draft 2, 20 October 2026. Design only, nothing is built.
Ticket SW-4, decision D152 (Matt, 20 October 2026: write this note).
Draft 2 answers the external review of draft 1
([Changes since draft 1](#changes-since-draft-1-external-review)).
Open questions are numbered D154 to D174, and new ones D178 to D182
([§14](#14-decisions)), each with a recommendation and, for the old
ones, the reviewer's verdict.

This note can be read without knowing the codebase. Code references were
checked at commit `4c5b6fe`. Claims are labelled **checked** (with a
source or `file:line`), **inferred** (reasoned from checked facts), or
**unverified** where it matters. Sources are listed at the end, as
[L1], [H1] and so on.

## Stitchwort in brief (for a reader new to it)

Stitchwort is a strict, pure functional language with dependent types,
implemented in Rust (repository `mdr/stitchwort`). It combines:

- **Totality.** Functions terminate by default (structural recursion,
  checked by size change). Code that might not terminate says so in its
  type, as the `Partial` ability.
- **Proofs about programs.** Dependent types, a built-in equality type
  `a = b` with its eliminator `J`, an impredicative `Prop` whose proofs are
  erased at runtime, and `Type`, `Type 1`, … above it. There is no
  universe polymorphism. Data types have parameters but no indices yet
  (indexed families are being designed in parallel, in
  [indexed-families.md](indexed-families.md); this note doesn't depend on
  them).
- **Abilities** (algebraic effects, Unison-style): effects appear in types,
  e.g. `{IO} ()`, and are implemented by handlers, in direct style, with
  no monads.
- **Content-addressed caching.** Each definition is identified by a hash
  of its contents, so checks and tests whose dependencies haven't changed
  aren't re-run.
- **Extraction to JavaScript** (an ES module with TypeScript types) for
  exported, proven code.

**Architecture.** An *elaborator* turns surface syntax into core terms,
filling in implicit arguments, `auto` arguments, dot notation and so on.
A small, trusted *kernel* then re-checks every core term on its own
(types, termination, positivity, `Prop` elimination). Anything the
elaborator invents is therefore checked again, and an interface design
that needs no kernel change keeps the trusted part unchanged.

**The surface, in one example** (from the Advent of Code solutions in
the repository):

```
namespace Aoc.Day01

type Turn =
  | Left (distance: Nat)
  | Right (distance: Nat)

-- A record type with a proof field.
type Dial (highest: Nat) = { position: Nat, inRange: position <= highest }

def Turn.parse (t: Text): Maybe Turn :=
  match t.uncons with
    | Just ('L', rest) => rest.toNat.map Left
    | Just ('R', rest) => rest.toNat.map Right
    | _                => Nothing

-- Part 1: the positions after each turn that are 0.
def zerosLandedOn (start: Dial highest) (turns: List Turn): Nat :=
  turns
    |> .scanLeft Dial.move start
    |> .drop 1
    |> .count Dial.isZero

-- From the standard library (List/Toolkit.sw): a theorem whose proof is
-- an ordinary structurally recursive function.
theorem List.appendNil: (xs: List a) -> List.append xs Nil = xs
  | Nil       => rfl
  | Cons x xs => Eq.cong (Cons x) (List.appendNil xs)
```

(`highest` and `a` are used in the signatures without being bound, so
they become implicit arguments automatically.)

- Binders are written `(x: T)`; `[a: Type]` is an implicit argument,
  `[auto ok: p]` one the compiler finds (§2.1). Lambdas are `x => e`.
- **Namespaces** group definitions: `Nat.compare` lives in namespace
  `Nat`. **Dot notation** `x.compare y` looks in the namespace of `x`'s
  type. A file starts with `namespace …` and can `import Std (List)` or
  `import Aoc.Common (Range)`; explicit imports are normal and cheap.
- **The standard library** is a core file (`crates/elab/src/std/core.sw`)
  plus library files (`List/Sort.sw`, `Int/Int.sw`, …) loaded when a
  program first uses one of their names.
- **Projects** are folders of `.sw` files whose namespaces follow their
  paths, with no cycles between namespaces.

**Status and constraints.** There are no external users yet, so there
are no backwards-compatibility constraints: old forms are simply
replaced, and hash stability is not a goal. The language is used
day to day on Advent of Code 2025 solutions, several of which are proved
correct for all inputs; those are the main source of the needs below.

## Changes since draft 1 (external review)

The reviewer supported the direction (records, bundled laws, named
alternatives, the ordering in a map's type, restricted instance heads)
and asked for changes in three places: superclasses, numeric operators,
and a precise resolution algorithm. Every point, and where it's answered:

| # | Review point | Draft 2 |
|---|---|---|
| 1 | The uniqueness argument works, but three premises must be rules: ownership is by the declaring module, not the dotted name; all instance signatures of the owning module are collected first, sibling files included; aliases unfold and never create ownership | Made normative (§5.6). Aliases unfold to the underlying head; `type LocalNat = Nat` can't own `Nat` |
| 2 | Superclass filling isn't a consistent mechanism: `Ord.byKey` has no `DecEq a` to use; literals in plain `def`s omit `eq`; a non-literal instance body has nothing to fill; replacing a field of a built record can break later fields; abstract diamonds aren't covered | Redesigned (§5.8): (a) omitted superclass fields are filled when an interface record literal is elaborated, anywhere; (b) a global instance is *checked*, never changed, against the canonical parents; (c) diamonds: the full superclass closure is searched, only definitionally equal candidates merge, otherwise ambiguity naming both paths; the superclass graph must be acyclic. `Ord.byKey` takes `[auto eq: DecEq a]`. The narrower guarantee is stated exactly |
| 3 | The `Nat`/`Int` exception for operators makes generic and monomorphic code disagree under the same dictionary | `+ * < <=` now mean the resolved dictionary for every type (§5.13). A global instance written as a record literal is projected at elaboration time, so `Nat`/`Int` code elaborates to exactly today's terms: proof migration cost is zero, checked by comparing hashes. For `<`/`<=`, `Ord` gains its relations and their deciders as fields (D180), so `Nat`'s instance can carry `Nat.LessThan` itself. The discrepancy example is now a test |
| 4 | Resolution needs a precise algorithm: no depth limit of 8; local matching mustn't commit while testing; the whole instance signature must be restricted (`instance Item.show (prefix: Text)`); recursive prerequisites first check whether head matching solved them | §5.5 is now a numbered algorithm. Matching is one-way (never assigns the goal's unknowns), so order can't matter; goals with unknown inputs wait. A step budget replaces the depth limit, and running out says "stopped" (D182). §5.2 lists the complete allowed signature |
| 5 | Equality proof obligations must keep using hypotheses first; `DecEq` only for deciding | Stated (§5.12), with a stage 2 acceptance example (`h: f = g`) |
| 6 | Hashing the marker isn't enough for an elaboration cache: adding a hand-written instance suppresses a derived one without touching the caller | No elaboration cache exists today (multi-file §8.3, **checked**). Any future one must key on a per-module *instance environment fingerprint* (§9.3) |
| 7 | `Map` types distinguish whole dictionaries, not comparators; "the map holds no functions" needs qualifying; five stage-4 tests | All three in §7.5 and §12 |
| 8 | Overridable dictionary parameters must have names (`[ord := …]` needs `[auto ord: …]`) | Every library signature names them, by one convention (D181) |
| 9a | `Text.byLength` isn't lawful | Renamed `Text.byLengthThenText`, ordered by length then text (§7.3) |
| 9b | Derivation for proof-bearing records needs a boundary (the `Dial` example) | §5.11 and D179: proof fields that are equations in a type with `DecEq` are ignored, by Hedberg's theorem (already in the library as `Bool.uniqueEq`); other proof fields stop derivation |
| 9c | Derived `Show` quotes text, but `Show Text` doesn't | `Show` has two fields, `toText` and `toSource` (D178, §5.14) |
| 9d | `Text`'s laws need a bridge to `Text.compare` | `Text.instOrd` uses `Text.compare` itself (it's a JS native) and proves the laws through a stated bridge lemma (§6.2) |
| 9e | Stage numbers disagree; `Add.add Nat.add x y` passes a function as a dictionary | Fixed (§7.3, §5.13) |
| 9f | The summary says Haskell forbids orphans | Fixed: Haskell allows them with a warning; the prohibition is Rust's; the head restriction is Haskell's (§0) |

---

## Contents

0. [Summary](#0-summary)
1. [Words used here](#1-words-used-here)
2. [What exists today](#2-what-exists-today)
3. [Goals and non-goals](#3-goals-and-non-goals)
4. [How other languages do it](#4-how-other-languages-do-it)
5. [The design](#5-the-design)
6. [The library's interfaces](#6-the-librarys-interfaces)
7. [Worked examples](#7-worked-examples)
8. [Errors](#8-errors)
9. [Namespaces, imports, hashing and caching](#9-namespaces-imports-hashing-and-caching)
10. [At runtime: dictionaries, JavaScript, speed](#10-at-runtime-dictionaries-javascript-speed)
11. [The kernel](#11-the-kernel)
12. [Stages](#12-stages)
13. [Risks](#13-risks)
14. [Decisions](#14-decisions)
15. [Sources](#15-sources)

---

## 0. Summary

An **interface** describes what a type supports, such as "can be compared
for order". An **instance** says how one particular type supports it. The
compiler finds instances by type, so generic code like `List.sort` works
on any type that has an ordering, without the caller passing a comparison
function.

The recommendation, in short:

1. **An interface is a record.** `interface Ord (a: Type) = { … }`
   declares a record type, like `type Person = { … }`. Its fields are the
   operations, plus **laws**: proof fields saying the operations behave.
   The kernel needs nothing new (§5.1, §11).
2. **An instance is a named definition** of that record type, marked
   `instance`: `instance Nat.instOrd: Ord Nat := { … }` (§5.2).
3. **Functions ask for one with `auto`**, which already means "the
   compiler finds this": `def List.sort [auto ord: Ord a] (xs: List a)`
   (§5.3).
4. **One instance per type, checked when it's declared.** An instance
   must be declared in the module that declares the interface or the
   type: Rust's orphan rule (Haskell allows such "orphans", with a
   warning). Its type must be a type name applied to distinct variables:
   Haskell 98's rule. Then two instances for the same type can only meet
   inside one module, so the overlap check is local (§5.6).
5. **Finding an instance is a lookup, not a search.** Dictionaries in
   scope first, then the one global instance for that interface and type.
   Matching never guesses a type, so nothing depends on order, file
   layout or imports (§5.5).
6. **Other choices are passed by name**:
   `List.sort [ord := Nat.descending] xs` (§5.7).
7. **Superclasses** (`Ord` contains a `DecEq`) are filled in when an
   interface record is built and *checked* when a global instance is
   declared. At concrete types every route to a parent agrees; for
   abstract dictionaries, different routes are an ambiguity error, never
   a silent choice (§5.8).
8. **`==` moves onto the `DecEq` interface** (Idris 2 has the same one).
   Proof obligations still use hypotheses first. `Decidable` for other
   propositions keeps today's search (§5.12).
9. **Operators mean the dictionary, for every type.** `+`, `*`, `<`, `<=`
   use `Add`, `Mul` and `Ord`, including on `Nat` and `Int`. Because the
   library's `Nat` and `Int` instances are projected at compile time,
   existing code elaborates to the same terms as today (§5.13).
10. **`Ord`, `Add`, `Mul` and `Show`** join `DecEq` in the library (§6).
    They remove `List.sum`/`List.sumInt` and similar pairs, make
    `List.sort` generic, and give `Map`/`Set` their keys.
11. **A `Map` carries its ordering dictionary in its type**, close to
    Lean's `TreeMap` [L4]. A map can't be searched with a different order
    from the one it was built with (§7.5).
12. **Not now:** `Functor`/`Monad`, default methods, interfaces with
    several type parameters, generic number literals (§5.10, §5.15).

The build is seven stages, about 3,500 lines of Rust and 1,700 lines of
Stitchwort library (§12). `SW-113` (`Map`/`Set`) can start after stages
3 and 4.

---

## 1. Words used here

- **Interface**: a named description of operations a type supports, with
  laws. Haskell and Lean call it a *type class*, Rust a *trait*.
- **Instance**: the operations of an interface for one type. Rust: an
  `impl`. Scala: a `given`. Idris: an *implementation*.
- **Global instance**: one declared with `instance`, found by the
  compiler. A **named alternative** is a plain `def` of an interface
  type, used only when passed by name.
- **Dictionary**: an instance as a value at runtime: a record of
  functions, passed as a hidden argument. Interfaces in Haskell, Lean and
  Scala compile this way. A **dictionary parameter** is an `auto`
  parameter of interface type, such as `[auto ord: Ord a]`.
- **Law**: a fact the operations must satisfy, such as "if `x < y` and
  `y < z` then `x < z`". Here, a proof field of the record.
- **Coherence**: the program means the same thing whichever way the
  compiler finds an instance. The usual way to get it is **global
  uniqueness**: at most one instance of an interface for a type, in the
  whole program [E1].
- **Orphan**: an instance declared in a module that declares neither the
  interface nor the type (Haskell's term [H4]).
- **Owner**: the module (namespace) that declares an interface or a
  nominal type (a data type or record, not a synonym).
- **Head** of a type: its outermost type name, after unfolding synonyms.
  The head of `List (Maybe Nat)` is `List`.
- **Superclass** (or **parent**): an interface another one contains as a
  field. `Ord` contains a `DecEq`: anything you can order, you can compare
  for equality.
- **Definitionally equal**: equal by computation, as the checker compares
  terms (docs/core.md "Evaluation and conversion"). `rfl` proves it.
- **Unknown**: a metavariable, a part of a term the elaborator hasn't
  worked out yet (`?a`).

---

## 2. What exists today

### 2.1 `auto` and `Decidable`

`[auto ok: p]` asks the compiler for a proof of `p` (DESIGN.md §6). The
search (**checked**, `crates/elab/src/auto.rs:1-22`) tries:

1. a hypothesis in scope whose type is `p`;
2. a **decision procedure**: *any* definition whose result type is
   `Decidable …`, with no marker (`decision_procedures`,
   `auto.rs:269-300`). The most recently defined is tried first; in a
   project, the module's own, then the namespaces it depends on, then the
   prelude (multi-file.md §4.9.5, decision D9). The **first one that
   fits** is used. Its own `Decidable` arguments are found the same way,
   up to depth 8 (`MAX_DEPTH`, `auto.rs:37`).

The procedure found is run at compile time for `[auto …]`, and becomes
part of the program for `==`, `if x < y` and `if h: p`.

This is already an instance search, for one interface (`Decidable`), with
no instance markers and "first fit wins" (multi-file.md §4.9.2). It's
safe for `Decidable` because two procedures can't disagree on `Yes`/`No`
("answer agreement", multi-file.md §4.9.4). They can still differ in the
proof term, speed, and whether they get stuck (same section).

### 2.2 `==` and derived equality

`a == b` is `Decidable.toBool d`, where `d` is a decision procedure for
`a = b` found as above (**checked**, docs/core.md "Elaboration").
Containers take a procedure for their elements as an ordinary argument:
`List.decEq (d: (x y: a) -> Decidable (x = y))` (**checked**,
`crates/elab/src/std/core.sw:416`), as do `Pair.decEq` and
`Maybe.decEq`. `auto` has special code to build that argument, a
function, by searching under binders (`decide_under`,
`auto.rs:392-429`).

Every data type and record gets a generated `T.%decEq` when declared,
unless a field rules it out: function fields, proof fields, types defined
together, parameters other than types (**checked**,
`crates/elab/src/derive.rs:1-60`; docs/syntax.md "Records"). For a type
with parameters, the procedure takes one decision procedure per
parameter, and while it's elaborated `auto` also looks at procedures
passed as arguments (`local_deciders`, `auto.rs:175-195`).

### 2.3 Operators are wired to `Nat` and `Int`

`+ - * / %` and `< <=` are the prelude's `Nat` or `Int` functions, chosen
for a whole expression at once (**checked**,
`crates/elab/src/numbers.rs:1-11`; docs/syntax.md "Numbers"). On any
other type they're an error. `m <= n` on `Nat` is `Nat.LessEq m n`,
defined as `Nat.leq m n = True`, and `m < n` is `Nat.LessThan m n`,
`Nat.leq (Succ m) n = True` (**checked**, `core.sw:107-109`); `Int`'s are
`Int.LessEq` and `Int.LessThan` over `Int.leq` and `Int.less`
(`core.sw:731-733`). `++` is `Text.append` or `List.append`.

### 2.4 Dot notation already overloads names per type

`x.compare y` finds `Nat.compare` for `x: Nat` and `Text.compare` for
`x: Text`, by looking in the namespace of `x`'s type (docs/syntax.md
"Records"). Text interpolation `${e}` is `e.toText` the same way. This
covers code about **one known type**. It doesn't help **generic** code,
where `x: a` and `a` is a type variable: `a` has no namespace.

### 2.5 The duplication generic code would remove

**Checked** in `crates/elab/src/std`:

| Today | Why it's duplicated |
|---|---|
| `List.sum`, `List.sumBy`, `List.product` (`List/Toolkit.sw:49-57`) on `Nat`; `List.sumInt`, `List.sumIntBy` (`Int/Int.sw:6-12`) on `Int` | `+` and `0` can't be generic |
| `List.maximum`, `List.minimum` (`List/Toolkit.sw:59-63`) on `Nat` only | no generic order |
| `List.sort: List Nat -> List Nat`; `List.sortBy (cmp: a -> a -> Ordering)` (`List/Sort.sw:441-444`) | the caller passes the comparison |
| `Nat.compare`, `Int.compare`, `Text.compare` (`core.sw:466, 739, 565`), each with its own lemmas | no shared statement of "an ordering" |
| `List.decEq d`, `Pair.decEq da db`, `Maybe.decEq d` | decision procedures as function arguments |

And the next library piece, a balanced-tree `Map`/`Set` (SW-113), needs
keys with an ordering. The ticket says it waits for this note.

### 2.6 Designs this one builds on

- **Records** (docs/proposals/records.md; stage 1 built). A declared
  record is a data type with one constructor and a projection per field.
  Proof fields are erased at runtime. In JS a record is a plain object
  with no tag. Records stage 4 (planned) already uses an `auto`-found
  record, `HasField.name r Text`, as evidence that `r` has a `name` field
  (records.md §9.2).
- **Multi-file** (docs/proposals/multi-file.md, draft 4). §4.9 compares
  how Lean 4, Haskell, Agda and Idris 2 find instances, and §4.9.6 left a
  direction for this note: the same candidate rule as `Decidable`,
  explicit instance markers, ambiguity as an error for interfaces, named
  alternatives passed explicitly, and local instances from arguments.
  Its reviewer's three points on overlap are answered in §5.6 and §9.1.
- **Elaboration isn't cached.** Every command re-elaborates what it needs
  (multi-file.md §8.3, **checked**); only kernel checks, tests and JS are
  keyed by hash (DESIGN.md §11).

---

## 3. Goals and non-goals

**Goals**

- **Generic library code**: one `sum`, one `sort`, one `max`, a `Map`
  for any ordered key.
- **Predictable**: which instance is used can be worked out by reading
  two places, the interface's module and the type's module. No
  priorities, no "most specific", no import order.
- **One meaning for each operator**: `x < y` means the same whether the
  code is generic or written for `Nat`.
- **Proofs about generic code**: a theorem about `List.sort` for any
  ordered type, using the ordering's laws.
- **No kernel change** (DESIGN.md principle 4).
- **Good errors** when no instance exists, or when two would.
- **Works with JS extraction and hashing** as they are.

**Non-goals (for now)**

- Interfaces over types of types (`Functor (f: Type -> Type)`), which
  also need a larger universe (§5.15).
- Several type parameters (`Convert a b`), "output" parameters and
  functional dependencies ([L1] `outParam`).
- A numeric tower (Lean's or Haskell's `Num`, `Ring`, `Field`, …).
- Generic number literals (Lean's `OfNat`).
- Speed work beyond keeping existing code as fast as it is (DESIGN.md:
  performance isn't a goal).
- Backwards compatibility (there are no users).

---

## 4. How other languages do it

### 4.1 The comparison

| | Instances declared | Found how | Several fit | Orphans | Laws |
|---|---|---|---|---|---|
| **Haskell** | `instance Ord T where …` | By type. Haskell 2010: an instance type must be "a type constructor T applied to simple type variables", distinct, not a synonym; "A type may not be declared as an instance of a particular class more than once in the program" [H1] | Error, reported lazily at use [H5]; GHC pragmas relax it | Allowed, with a warning (`-Worphans`) [H4] | Documentation only |
| **Rust** | `impl Ord for T` | By type | Overlap is refused when declared [R1] | Refused: "a trait implementation is only allowed if either the trait or at least one of the types in the implementation is defined in the current crate" [R1] | Documentation only |
| **Lean 4** | `instance : Ord T := …` (a structure value) | By type, with backtracking; local variables first; ties by priority then "more recent instances taking precedence" [L1] | First success wins; instances are assumed "morally canonical": "any discovered instance should be considered as good as any other" [L1] | Allowed | Separate classes (`LawfulBEq`, `TransCmp`, …) [L4] |
| **Agda** | `instance` blocks; records | By type; "instance resolution does not make unforced choices between instances" [A1] | Error unless `OVERLAPPABLE`/`INCOHERENT` [A1] | Allowed; "Top-level instances must target a named type" [A1] | Proof fields of the record (the standard library's `IsDecTotalOrder` and so on) |
| **Idris 2** | `Ord Nat where …`, optionally named: `[myord] Ord Nat where …` [I1] | By type, like `auto` implicits [I2] | "Only one implementation of an interface can be given for a type - implementations may not overlap" [I1] | Allowed | Separate interfaces, or none |
| **Scala 3** | `given Ord[T] = …` | By type and lexical scope; deeper nesting wins; then specificity; equal candidates are an ambiguity error [S1] | Error unless one is preferred by nesting or specificity [S1] | Allowed (givens are ordinary values, imported explicitly) | Documentation only |
| **Rocq** | Type classes (records + `Instance`), or **canonical structures** | Classes: proof search with priorities. Canonical structures: unification hints keyed by a type's head [M1] | Classes: first by priority. Canonical: one per head | Allowed | Proof fields (Mathematical Components' hierarchies) |

### 4.2 What the comparison shows

1. **Records are a fine encoding.** Lean, Agda and Rocq all represent an
   interface as a record and an instance as a value of it. Laws are proof
   fields in Agda's and Rocq's libraries, and separate classes in Lean's.
   Agda: "Superclass dependencies can be implemented using Records and
   instance search" [A1].
2. **Two camps on coherence.** Haskell, Rust and Idris want one instance
   per type. Lean and Rocq's type classes take the first that works and
   trust that instances agree. Haskell shows what goes wrong when they
   don't: with two orphan `Ord` instances, a `Data.Set` built with one and
   searched with the other gives wrong answers [E1]. Stitchwort proofs
   can see which instance was used (the term is part of the proof), so
   "they're all the same" isn't true here.
3. **Rust checks uniqueness eagerly**, and it can because of the orphan
   rule: an `impl` for a given trait and type can only be in the crate of
   the trait or the crate of the type, and crates can't depend on each
   other in a cycle, so one of them sees the other [R1]. Stitchwort's
   namespaces have the same property: cycles between namespaces are
   refused (`E-NAMESPACE-CYCLE`, docs/syntax.md).
4. **Restricting instance types keeps search simple.** Haskell 98's and
   Idris's rule (a type name applied to distinct variables) means
   instances for the same interface overlap exactly when they have the
   same head. No unification of dependent types needed.
5. **Named alternatives** are how Idris handles "a different order for
   this one call": `sort @{myord} xs` [I1]. Stitchwort already has the
   syntax for passing an implicit argument by name: `[x := e]`.
6. **Lean's `TreeMap` puts the comparison in the type**:
   `Std.TreeMap (α: Type u) (β: Type v) (cmp: α → α → Ordering := by exact compare)`,
   and `insert` takes no comparison of its own [L4]. So a map built with
   one ordering can't be used with another.
7. **Canonical structures** (Rocq) teach unification "if you need a `T`
   for type `X`, use this one", keyed by `X`'s head [M1]. With one
   instance per head, Stitchwort's lookup is close to this in spirit, but
   done as an `auto` search, which the elaborator already has.

---

## 5. The design

### 5.1 An interface is a record

```
interface DecEq (a: Type) =
  { decide: (x: a) -> (y: a) -> Decidable (x = y) }
```

- `interface I (a: Type) = { … }` is exactly a record declaration
  (`type I (a: Type) = { … }`, docs/syntax.md "Records"), plus a flag the
  elaborator keeps: this record is an interface. The kernel sees a data
  type with one constructor, as for any record.
- **One parameter, a type** (D174). `a: Type`, so the interface itself is
  in `Type`. No universe change.
- **Fields are operations and laws.** A field whose type is a
  proposition is a law, erased at runtime like any proof field. A field
  may mention earlier fields, as record fields can.
- **A field whose type is an interface is a superclass** (§5.8). The
  superclass graph must be acyclic (`E-INTERFACE-CYCLE`).
- **Methods are generated.** For each field `f`, the elaborator defines
  `I.f: [a: Type] -> [auto i: I a] -> (the field's type)`, which
  projects the field from the dictionary it's given. The parameter's name
  `i` is the interface's name with a lower-case first letter (`decEq`,
  `ord`, `add`, `mul`, `show`), so it can be overridden by name:
  `Ord.compare [ord := Nat.descending] x y` (D181). The raw projection is
  still reachable as `d.compare` by dot notation on a dictionary `d`.
- **The interface's namespace** holds its methods and any helpers
  written later (`Ord.max`). `import Ord (compare, max)` brings them in,
  as for any namespace.

Why a record and not a new kind of declaration: records already have
literals, projections, dot notation, proof fields, erasure, JS objects and
hashing. An interface reuses all of it.

### 5.2 Instances

```
instance Nat.instDecEq: DecEq Nat := { decide = Nat.decEq }
```

- `instance` is `def` with a marker. The body is any expression of the
  interface type: a record literal, or a call such as `Ord.byKey …`.
- **Instances are named** (D156). The name lets it be passed explicitly,
  gives it a JS name and gives errors something to point at. The
  convention is `T.instI` (`Nat.instOrd`, `List.instDecEq`), after
  Lean's generated names; it's a convention, not a rule (D181). The name
  doesn't decide ownership (§5.6).
- **The complete allowed signature** (D158). An instance of an ordinary
  interface may have only:
  1. **Head variables**: implicit parameters that appear in the head and
     so are fixed by matching it (`[a: Type]` in `DecEq (List a)`,
     `[n: Nat]` in `DecEq (Vec a n)`), including a data type's `auto`
     parameter written as a variable (`Show (Map k v [ord := o])`, §7.5);
  2. **Prerequisites**: `auto` parameters whose type is an interface
     applied to one head variable (`[auto ord: Ord a]` for
     `Ord (List a)`).

  Nothing else: `instance Item.instShow (prefix: Text): Show Item` is
  `E-INSTANCE-PARAMETER`, since lookup couldn't choose `prefix`;
  `[auto ord: Ord (List a)]` for `Ord (List a)` is `E-INSTANCE-CONTEXT`.
  Each prerequisite works on a smaller type than the head, so search
  always ends (Haskell's rule for instance contexts [H1]).
- **The head**, after unfolding synonyms, must be a nominal type (a data
  type or record) applied to distinct variables: `Ord Nat`,
  `Ord (List a)`, `Ord (a, b)`. Not `Ord (List Nat)`, not `Ord a`, not
  `Ord (Nat -> Nat)` (Haskell 98 [H1], Idris [I1]). So two instances of
  one interface overlap exactly when they have the same head. A synonym
  is unfolded first: with `type Alias a = List a`, an instance for
  `Ord (Alias a)` is an instance for `Ord (List a)`, owned by `List`'s
  owner (§5.6); with `type Grid = List (List Nat)`, `Show Grid` is
  `Show (List (List Nat))`, which isn't allowed (`E-INSTANCE-HEAD`).
- **`Decidable` instances** keep their own, looser rules (§5.12).

### 5.3 Asking for an instance

A function asks for an instance with an `auto` parameter, the existing
binder for "the compiler finds this" (D157):

```
def List.sort [auto ord: Ord a] (xs: List a): List a := List.sortBy Ord.compare xs
```

A name is optional: `[auto Ord a]` is `[auto _: Ord a]`, which can't be
overridden by name. **Library functions always name their dictionary
parameters**, by D181's convention, so callers can write
`List.sort [ord := Nat.descending] xs`. Name it too when the body uses
the dictionary directly, usually for laws (`ord.trans`).

`auto` already has the right meaning in every row of DESIGN.md §6's
"four separate questions": the caller doesn't write it; it's found by
the compiler; whether it exists at runtime follows from its type (a
dictionary is data, so it's passed).

Type variables are still bound automatically: `a` above needs no
`[a: Type]` (docs/syntax.md "Automatic implicits").

### 5.4 Using methods

Inside `List.sort`, `Ord.compare x y` finds the dictionary `ord` in
scope. Outside, `Ord.compare 3 5` finds `Nat.instOrd`. With
`import Ord (compare)`, write `compare x y`.

On a known type nothing changes: `x.compare y` for `x: Nat` is still
`Nat.compare`, by dot notation. **Dot notation on a type variable**
(`x.compare y` for `x: a` with `[auto ord: Ord a]` in scope) is a
separate feature, recommended for later (D173).

### 5.5 Finding an instance: the algorithm

**When.** An `auto` argument records an obligation, as today; the
obligations of a declaration are solved after the declaration is
elaborated, when unification has done what it can (`auto.rs:51-78`).
Unsolved obligations are retried in rounds while any round makes
progress (solving one can determine another's type).

**Matching is one-way.** "Candidate `c: J U` matches goal `I T`" means:
`J` is `I`, and `U` and `T` can be made equal by solving *only the
candidate's own* unknowns (fresh unknowns for an instance's parameters).
A match never assigns an unknown of the goal. Each test runs inside an
undo transaction (`crates/elab/src/undo.rs`) and is rolled back, so
testing one candidate can't change whether another fits. This is what
makes the answer independent of the order candidates are tried in.

**Steps**, for an obligation with goal `I T` (D159):

1. **Already solved.** If unification has already solved the obligation
   (because some other type fixes it, as `Map`'s type fixes its ordering,
   §7.5), stop. Nothing is searched.
2. **Given by name**, `[ord := e]`: `e` is checked against `I T`.
3. **Wait if `T`'s inputs aren't known.** If `T`'s head is an unknown, or
   matching would need to assign a goal unknown, the obligation waits for
   a later round. At the end of the declaration, one still waiting is
   `E-INSTANCE-UNKNOWN-TYPE` ("can't tell which type's `Ord` to use;
   annotate").
4. **Dictionaries in scope.** Candidates are every variable in scope of
   interface type, and every superclass path from one, through the whole
   superclass closure (`ord.eq` for `DecEq a`; for diamonds, §5.8).
   Collect all that match. Merge candidates that are definitionally equal
   (they're the same dictionary reached two ways). If one remains, use
   it. If several remain, `E-INSTANCE-AMBIGUOUS`, naming each path
   (`o1`, `o2.base`). If any matched, stop: global instances aren't
   tried.
5. **The global instance.** Look up the one instance of `I` for `T`'s
   head (§5.6). None: `E-INSTANCE-NONE`. Otherwise match its head against
   `T`, which fixes all its head variables (§5.2). Then for each of its
   prerequisites, **first check whether matching already fixed it**
   (step 1 again: a head like `Map k v [ord := o]` fixes `o`), and
   otherwise solve it as a new obligation from step 2.
6. **Budget.** Each obligation tree has a budget of instance steps
   (large: thousands). Termination is guaranteed by §5.2's rules, but not
   any fixed depth: `DecEq (List (List … Nat))` twelve deep is fine.
   Running out is `E-INSTANCE-BUDGET`, which says resolution was
   *stopped*, not that no instance exists (D182). The legacy `Decidable`
   search keeps its depth limit of 8 (§5.12).

A dictionary in scope wins over a global instance. That's how Lean,
Scala and Idris behave, and it's what lets a function's caller choose:
`List.sort [ord := Nat.descending] xs` makes every `Ord Nat` inside that
call of `List.sort` use it.

There's **no backtracking among globals and no tie-break**: at most one
global instance can fit, so nothing depends on declaration order, file
order, load order or which namespaces were checked first.

### 5.6 One instance per type, checked locally

**The rules** (D158), all normative:

1. **Ownership is by module.** The owner of an interface is the module
   (namespace) whose file declares it; the owner of a nominal type is the
   module whose file declares it. A synonym owns nothing: `type LocalNat
   = Nat` declared in `Report` doesn't make `Report` an owner of `Nat`.
   The dotted name of a declaration doesn't matter: `Shop.Item.instOrd`
   is owned by the module its file is in.
2. **Orphan rule.** An instance of `I` for head `D` must be declared in a
   file of the module that owns `I` or the module that owns `D`. In file
   mode (no namespace line), the file is the module.
3. **No overlap.** At most one instance of `I` for each head `D`.
4. **All signatures first.** When a module is checked, the signatures
   of all its instance declarations, in all its files, are elaborated and
   registered before any instance is derived (§5.11) and before any use
   in the module is resolved. This includes instances that nothing being
   run needs (`run` checks only what a target needs, multi-file §9.1).
   Bodies are checked by the normal dependency rules.
5. **Std is closed.** A program can't add to `Std`'s namespaces
   (`E-STD-NAMESPACE`, docs/syntax.md), and `Std` owns `Ord`, `Nat`,
   `List` and the rest, so `Ord Nat`, `Show (List a)` and the like are
   only ever the library's. Another order for `Nat` is a named
   alternative (§5.7).

**Why the check is local.** Suppose `Shapes` declares `type Shape` and
`Geometry` declares `interface Area`. An instance `Area Shape` names
both, so its module depends on the other. If one were in `Shapes` and
another in `Geometry`, each module would depend on the other: a cycle,
already refused (`E-NAMESPACE-CYCLE`). So all instances of `Area` for
`Shape` are in one module (or `Shapes` and `Geometry` are the same
module), and by rule 4 checking that module sees all their signatures.
The overlap check is then a duplicate-key check on `(I, D)`. No
unification is needed. (**Inferred**, from the rules above and the
acyclic namespace graph; it's the argument Rust relies on for crates
[R1]. The reviewer agreed.)

Uniqueness is checked the same way whatever an interface's fields are,
proof-only interfaces included.

### 5.7 Other choices, by name

A plain `def` of an interface type is a **named alternative**. It's never
found automatically, but can be passed by name:

```
def Nat.descending: Ord Nat := Ord.fromCompare (x y => Nat.compare y x) … laws …

def ranked := List.sort [ord := Nat.descending] scores
```

`Ord.fromCompare` (§6.2) fills in the superclass `eq` (§5.8). For a
one-off ordering that needs no laws, today's function-argument versions
stay: `List.sortBy (x y => Nat.compare y x) scores` (D154).

### 5.8 Superclasses

`Ord` has a field `eq: DecEq a`. The reviewer showed that "the compiler
fills it when an instance is declared" doesn't work for all bodies.
Draft 2 separates three things (D160).

**(a) Filling, when a record is built.** When the elaborator checks a
record literal of an interface type and the literal leaves out a
superclass field, it fills the field by resolving the superclass at that
point (§5.5), in the literal's context. This happens for every interface
record literal: in instances, in named alternatives, in helpers. It
happens before later fields are checked, so a later field that mentions
the superclass (a law about `base.op`) is checked against the filled
value. A literal may also give the field explicitly.

```
def Ord.byKey [auto eq: DecEq a] [auto ord: Ord b] (key: a -> b)
  (inj: (x: a) -> (y: a) -> key x = key y -> x = y): Ord a :=
  { compare = (x y => Ord.compare (key x) (key y)), … }    -- `eq` filled: the parameter `eq`
```

Here `eq` is filled with the parameter `eq: DecEq a`, the only `DecEq a`
in scope (`ord.eq` is a `DecEq b`).

**(b) Checking, when a global instance is registered.** For each
superclass path `p` of a global instance `N: I (D vs)` (every path
through the closure, `eq`, and for deeper hierarchies `eq.…`), the
compiler resolves the parent at that type in the instance's own context
(its prerequisites in scope) and checks that `N.p` is **definitionally
equal** to it. It never replaces a field: a later field may depend on
it, and replacing it could make that field's proof wrong. A mismatch is
`E-INSTANCE-SUPER`: "the `DecEq Text` inside `Text.instOrd` isn't
`Text.instDecEq`". For `instance Text.instOrd := Ord.fromCompare …`, the
check computes `(Ord.fromCompare …).eq`, which is the `DecEq Text` that
resolution filled when `fromCompare` was called: `Text.instDecEq`. It
passes.

**(c) Diamonds and abstract dictionaries.** Suppose `B a` and `C a` both
contain an `A a`, and `D a` contains a `B a` and a `C a`. In a function
with `[auto d: D a]`, there are two routes to `A a`: `d.b.a` and
`d.c.a`. Nothing in `D`'s type says they're equal. Likewise
`[auto b: B a] [auto c: C a]` gives `b.a` and `c.a`. Resolution (step 4
of §5.5) collects every route through the closure, merges those that are
definitionally equal, and reports `E-INSTANCE-AMBIGUOUS` with both paths
if two distinct ones remain. The fix is to pass one by name. Asking
directly for an interface and its own parent (`[auto e: DecEq a]
[auto ord: Ord a]`) is the commonest case of this, and gets a specific
message (`E-INSTANCE-REDUNDANT`, at the signature: "`Ord a` already
contains a `DecEq a`").

**The guarantee, exactly.** For every *global* instance, each superclass
path is definitionally equal to the instance resolution finds for that
parent at that type. So where every dictionary involved comes from
global instances (all concrete types, with no named alternatives), every
route to a parent agrees by computation, and a proof can't tell them
apart. Nothing is promised for dictionaries in scope (parameters), or for
named alternatives that give a superclass explicitly: there, distinct
routes are an ambiguity error, never a silent choice. In the library,
only `Ord` has a superclass, so diamonds can't arise yet.

### 5.9 Laws, and proofs that use them

Laws are fields, so every instance proves them and every generic proof
can use them (D154). Generic code names the dictionary and uses its
fields: `ord.trans x y z h1 h2`. §7.6 and §7.7 are worked examples.

Why bundle the laws, rather than Lean's separate law classes [L4]:

- Lean splits them so that programs needn't prove anything. Stitchwort
  keeps the unproved route separate in a different way: plain function
  arguments (`List.sortBy cmp`). An *instance* always comes with its
  laws, so generic theorems never need an extra "and it's lawful"
  argument.
- Most instances won't be written by hand: the library has them for its
  types, derived instances (§5.11) build their proofs from combinators
  proved once, and `Ord.fromCompare` and `Ord.byKey` (§6.2) take only
  the essential laws.

The reviewer checked that the laws suffice: `Ord`'s three ordering laws
give a total order with no reflexivity field (`flip` at `(x, x)` forces
`compare x x = Equal`), and `Add`'s right identity follows from `comm`
and `zeroAdd`.

### 5.10 No default methods

Haskell, Rust and Idris let an interface give a default for a method.
Here that would interact with laws: an instance that overrides a default
must prove the override agrees. Instead, extra operations are **generic
functions in the interface's namespace** (D161), and building an
instance from the essentials is a helper function (`Ord.fromCompare`):

```
def Ord.max [auto ord: Ord a] (x: a) (y: a): a := match Ord.compare x y with
  | Less => y
  | _    => x
```

### 5.11 Derived instances

Today every data type and record gets `==` when declared, if its fields
allow it. That becomes a **derived `DecEq` instance**, `T.%instDecEq`
(D164). For a type with type parameters it takes `[auto decEq: DecEq a]`
instead of a function argument, so `auto.rs`'s `decide_under` and
`local_deciders` go away. Derived `Show` (stage 6) and `Ord` (stage 7,
lexicographic: constructors in declaration order, then fields in order)
follow, built from combinators whose laws are proved once.

**A module's own instance replaces the derived one.** If the module that
owns `T` declares an instance of `I` for `T`, nothing is derived for `I`
and `T`. That's today's rule ("a user's own `Shape.decEq` still takes
priority", DESIGN.md §4), restated so that there's still one instance.
Rule 4 of §5.6 makes this decidable before deriving.

**What derivation covers** (D179):

- **Data fields** with an instance of the interface (or of the type
  itself, for recursion), as today.
- **Value parameters**, newly. `Dial (highest: Nat)` gets
  `[highest: Nat] -> DecEq (Dial highest)`: `highest` is a head
  variable, and nothing needs deciding about it. Today such types get no
  `==` (`derive.rs:9-15`).
- **Proof fields whose type is an equation in a type with `DecEq`**, such
  as `inRange: position <= highest` (which is `Nat.leq position highest
  = True`, an equation in `Bool`) or `ok: List.length items = size` (in
  `Nat`). These are ignored: two values with equal data fields are equal,
  because any two proofs of an equation in a type with decidable equality
  are equal. That's Hedberg's theorem; the library already proves it for
  `Bool` (`Bool.uniqueEq`, `core.sw:299`, **checked**), and stage 2
  proves it generically (`DecEq.uniqueEq`). `Ord` ignores them the same
  way, and `Show` leaves them out (`{ position = 3 }`).
- **Any other proof field** (`sorted: IsSorted items`) stops derivation,
  with a note, since equal data needn't mean equal proofs without proof
  irrelevance. The user can write an instance (`Ord.byKey` on the data
  fields needs a proof that the key is injective, which needs exactly
  this fact). Function fields, type fields and types defined together
  stop it too, as today.

So the introduction's `Dial` gets `==`, an ordering by `position`, and
`"${dial}"` showing `{ position = 3 }`.

### 5.12 `=` through `DecEq`; `Decidable` stays special

- **Deciding `=` goes only through `DecEq`** (D162). `x == y`, `x != y`,
  `if h: x = y`, and an `[auto ok: x = y]` that has to be decided, use
  `DecEq.decide x y` from the `DecEq` instance for `x`'s type.
- **Hypotheses still come first.** For an `auto` proof obligation of an
  equation, a hypothesis in scope is used before anything is decided, as
  today. With `h: f = g` for functions `f g: Nat -> Nat`,
  `[auto ok: f = g]` is solved by `h`; it doesn't need a
  `DecEq (Nat -> Nat)`, which doesn't exist. This is a stage 2
  acceptance test.
- **Other propositions keep today's search** (`x < y` on `Nat`,
  `p && q`, `Not p`, user predicates): any definition marked `instance`
  whose result is `Decidable …`, first fit wins, in the D9 order, depth
  limit 8. That's safe for answers (multi-file §4.9.4). These overlap all
  the time (`Decidable.and` fits any `p && q`), and their propositions are
  often definitions that unfold into each other, so a uniqueness rule
  doesn't fit them. A `Decidable` instance may have any parameters
  (§5.2's restriction is for ordinary interfaces).
- **Decision procedures need the `instance` marker too** (D163):
  `instance Nat.decLessEq (m: Nat) (n: Nat): Decidable (m <= n) := …`.
  One rule for what `auto` may use. About 20 in the library
  (std-library.md §4.5); none in `aoc/src`, and about 5 example files
  (**checked** by grep, 20 October).
- **The name is `DecEq`, not `Eq`** (D155). `Eq` is already the
  namespace of the lemmas about `=` (`Eq.sym`, `Eq.trans`, `Eq.cong`; 762
  uses in the library, **checked**). Idris 2's interface for exactly this
  is `DecEq`, with one method `decEq: (x1, x2: t) -> Dec (x1 = x2)` [I3].

`DecEq` needs no laws: its one field returns a proof either way.

### 5.13 Operators: the dictionary, for every type

The reviewer's example, in draft 1's rules:

```
def before [auto ord: Ord a] (x: a) (y: a): Bool := x < y
def beforeNat [auto ord: Ord Nat] (x: Nat) (y: Nat): Bool := x < y

-- draft 1: `before [ord := Nat.descending] 1 2` is False (it uses `ord`),
-- but `beforeNat [ord := Nat.descending] 1 2` is True (`<` on Nat ignored `ord`).
```

Generalising a function's type shouldn't change what it does. So
(D165):

**The rule.** After an arithmetic or comparison expression's operand type
is decided (today's whole-expression rules, unchanged: docs/syntax.md
"Numbers"), each operator resolves its dictionary by §5.5 and means that
dictionary's field, **for every type, `Nat` and `Int` included**:

| Syntax | Means | Interface |
|---|---|---|
| `x + y` | `Add.add x y` | `Add` |
| `x * y` | `Mul.mul x y` | `Mul` |
| `x < y` | `Ord.LessThan x y` | `Ord` (a field, D180) |
| `x <= y` | `Ord.LessEq x y` | `Ord` (a field, D180) |
| `x == y`, `x != y`, `if h: x = y` | `DecEq.decide x y` | `DecEq` |
| `${e}` | `Show.toText e` | `Show` (§5.14) |
| `-`, `/`, `%`, prefix `-` | unchanged: `Nat`/`Int` only | none |
| `++` | unchanged: `Text`/`List` | none |
| `0`, `42` | unchanged: `Nat`/`Int` only | none |

So `beforeNat [ord := Nat.descending] 1 2` uses `ord` too, and both
calls give `False`. That pair is a stage 5 test.

**Known-instance projection.** When the dictionary resolved is a *global
instance whose body is a record literal*, the elaborator writes the
field's term directly instead of the method call. `Add.add
[add := Nat.instAdd] x y` becomes `Nat.add x y`. This changes nothing
about meaning: the method is a projection, and the instance's body is a
literal, so the two are definitionally equal (docs/core.md: a definition
of arity 0 always unfolds, and a case on a constructor steps), and the
kernel re-checks the result. It's what lets the library's `Nat` and `Int`
instances cost nothing.

**Why this needs a change to `Ord` (D180).** Projection gives today's
terms only if the instance's fields *are* today's functions and
relations. `Nat.instAdd.add` is `Nat.add` and `Nat.instMul.mul` is
`Nat.mul`, so `+` and `*` are no problem. But a comparison defined from
`compare` (`compare x y = Less`) isn't `Nat.LessThan x y`
(`Nat.leq (Succ x) y = True`): they're equal propositions only by a
proof, not by computation, so every existing proof that uses `<` would
change. So `Ord` carries the relations and their deciders as fields,
with laws tying them to `compare`:

```
LessThan: a -> a -> Prop,  decLessThan: (x y: a) -> Decidable (LessThan x y)
LessEq: a -> a -> Prop,    decLessEq: (x y: a) -> Decidable (LessEq x y)
```

`Nat.instOrd` sets `LessThan = Nat.LessThan`, `decLessThan =
Nat.decLessThan` and so on, and projection turns `x < y` on `Nat` into
`Nat.LessThan x y`, today's term. A user's instance gets them from
`Ord.fromCompare` without thinking about it (§6.2).

**The cost, measured.** In `crates/elab/src/std` there are 464 lines
using `+` or `*` and 206 using `<` or `<=`; in `aoc/src`, 442 and 206;
there are 698 theorems in the two together (**checked** by grep, 20
October). None of them has a dictionary parameter for `Nat` or `Int`
(**checked**: no `[auto …: Add|Mul|Ord …]` anywhere), so every one of
those operators resolves to the global instance and is projected to
today's term. **Expected proof migration: none.** This is checkable
exactly: after stage 5, every existing definition's hash must be
unchanged, except those whose terms really change (callers of
`List.sum` and the other generalised functions). A hash diff is the
stage's acceptance test ("hashes as a migration oracle"). Runtime cost
for existing code: none, since the terms and so the JS and the natives
are the same. Generic code pays one dictionary argument and one
projection per operation (§10). Compile time: one lookup per operator.

**Bootstrap.** `core.sw` uses `+` and `<` before `Add`, `Ord` and their
`Nat` instances exist. Until they're declared (only possible inside the
prelude), operators on `Nat` elaborate to the same terms projection
would give.

**The alternative**, keeping `<` and `<=` built in for `Nat` and `Int`
(D180's option B), is smaller (`Ord` keeps three laws and one function)
but keeps the discrepancy above, which would have to be documented and
tested as intended behaviour. The reviewer prefers uniform semantics,
with an exception only if migration is expensive; with projection it
isn't.

**No generic literals** (D165): `0` in generic code would need Lean's
`OfNat` class (one instance per literal value) and default instances to
decide what `let n := 0` means [L1]. Generic code writes `Add.zero` and
`Mul.one`. A literal checked against a type that isn't `Nat` or `Int` is
an error with the note "use `Add.zero`".

### 5.14 `Show` and interpolation

```
interface Show (a: Type) =
  { toText: a -> Text        -- for people: "tea" is tea
  , toSource: a -> Text      -- as source: "tea" is "tea" with its quotes
  }
```

The reviewer noticed that one method can't give both `${name}` (no
quotes) and a record shown as `{ name = "tea" }` (quotes). Rust has two
traits for this (`Display`, `Debug`); here it's two fields (D178):

- **`toText`** is what `"${e}"` inserts (D167). For `Text` it's the text
  itself; for `Char`, the character.
- **`toSource`** is how the value is written in source: `Text` in quotes
  with escapes, `Char` as `'a'`, `Int` as `-5`.
- **For everything else** (numbers, `Bool`, lists, tuples, `Maybe`,
  derived data and records), `toText` and `toSource` are the same, and
  **elements are always shown with `toSource`**. So
  `"${["a", "b"]}"` is `["a", "b"]`, `"${("x", 1)}"` is `("x", 1)`, and
  a derived record is `{ name = "tea", price = 3 }` (proof fields left
  out, §5.11).
- `Show.fromText f` builds an instance with both fields `f`, for a
  user's own type.

Today `${e}` is `e.toText` by dot notation. Keeping both would mean two
rules for one piece of syntax, so `${e}` uses `Show` only. A user's
`def Point.toText` is then wired in with
`instance Point.instShow: Show Point := Show.fromText Point.toText`.

### 5.15 `Functor`, `Monad`: not now

In Haskell, `Monad` exists mainly to sequence effects. Stitchwort does
that with abilities, in direct style (DESIGN.md §8). What's left is code
generic over containers (`fmap` on any `f`). Today `xs.map f` and
`m.map f` already work per type by dot notation, which covers what
programs here have needed (**inferred** from the AoC programs, which use
`List` and `Maybe` only).

`Functor (f: Type -> Type)` would also need a record in `Type 1` (its
field quantifies over types) and, without universe polymorphism, could
only hold `Type 0` containers. D168 recommends waiting. The reviewer
agreed.

---

## 6. The library's interfaces

All in `Std`, in core (D170). `DecEq`, `Ord`, `Show`, `Add` and `Mul`
are default names (usable without an import), like `Ordering` and
`Decidable` today.

### 6.1 `DecEq`

As in §5.1 and §5.12. Instances: `Nat`, `Int`, `Bool`, `Char`, `Text`,
`Unit`, `Ordering`, and `List a`, `Maybe a`, `(a, b)` given `DecEq` of
their parameters:

```
instance Nat.instDecEq: DecEq Nat := { decide = Nat.decEq }
instance List.instDecEq [auto decEq: DecEq a]: DecEq (List a) := { decide = List.decEq DecEq.decide }
```

`Nat.decEq` stays a function (it's a native); `List.decEq`'s
function-taking form becomes a helper. Helpers: `DecEq.uniqueEq`
(Hedberg: two proofs of `x = y` are equal, for `x y: a` with
`DecEq a`), `DecEq.sound: (x == y) = True -> x = y`.

### 6.2 `Ord`

```
interface Ord (a: Type) =
  { eq: DecEq a                                   -- superclass (§5.8)
  , compare: a -> a -> Ordering
  , LessThan: a -> a -> Prop                      -- what `<` means (§5.13)
  , LessEq: a -> a -> Prop                        -- what `<=` means
  , decLessThan: (x: a) -> (y: a) -> Decidable (LessThan x y)
  , decLessEq: (x: a) -> (y: a) -> Decidable (LessEq x y)
  -- the ordering laws
  , equal: (x: a) -> (y: a) -> compare x y = Equal -> x = y
  , flip: (x: a) -> (y: a) -> compare y x = Ordering.flip (compare x y)
  , trans: (x: a) -> (y: a) -> (z: a) -> compare x y = Less -> compare y z = Less -> compare x z = Less
  -- the relations agree with `compare`
  , lessThanOf: (x: a) -> (y: a) -> compare x y = Less -> LessThan x y
  , lessThanTo: (x: a) -> (y: a) -> LessThan x y -> compare x y = Less
  , lessEqOf: (x: a) -> (y: a) -> Not (compare x y = Greater) -> LessEq x y
  , lessEqTo: (x: a) -> (y: a) -> LessEq x y -> Not (compare x y = Greater)
  }
```

- **`equal`**: "`Equal` means equal". So a `Map` can't confuse keys.
- **`flip`**: comparing the other way round gives the opposite answer
  (`Ordering.flip Less = Greater`, `Ordering.flip Equal = Equal`). It
  implies `compare x x = Equal`.
- **`trans`**: `Less` is transitive. With the other two, `Less`-or-`Equal`
  is too.

These are Lean's `OrientedCmp`, `TransCmp` and `LawfulEqCmp`, bundled
[L4]. `LessThan` and friends are there for §5.13. A new helper
`Ordering.flip` is needed.

`LessThan` and `LessEq` are fields whose type is a function returning
`Prop`; such fields are erased at runtime (docs/core.md "Data types":
"a field is erased if its type is a proposition or a type former"), and
`a -> a -> Prop` is in `Type 0`, so `Ord a` stays in `Type`.

**Building one.** Two helpers, so that nobody writes thirteen fields:

```
-- From a comparison and its three laws. The relations are
-- `compare x y = Less` and `Not (compare x y = Greater)`, decided through
-- `DecEq Ordering`; their four laws are trivial. `eq` is filled (§5.8).
def Ord.fromCompare [auto eq: DecEq a] (compare: a -> a -> Ordering)
  (equal: …) (flip: …) (trans: …): Ord a

-- Order `a` by a key, given that the key tells values apart.
def Ord.byKey [auto eq: DecEq a] [auto ord: Ord b] (key: a -> b)
  (inj: (x: a) -> (y: a) -> key x = key y -> x = y): Ord a
```

`Ord.byKey` keeps the caller's `eq` as its superclass (draft 1 had no
`DecEq a` to give it).

**Instances.** `Nat` and `Int` are written out in full, with today's
functions and relations (`Nat.compare`, `Nat.LessThan`,
`Nat.decLessThan`, …), so that projection gives today's terms; their
laws need small new lemmas linking `Nat.compare` to `Nat.leq` (some
exist: `Nat.compareLeq`, `List/Sort.sw:398`). `Char` is
`Ord.byKey Char.toNat`. `Bool`, `Ordering`, `Maybe a` (`Nothing` first),
`(a, b)` and `List a` (lexicographic) are written with
`Ord.fromCompare`.

**`Text`** uses `Text.compare` itself, which is a registered builtin with
a native JS implementation (`crates/core/src/registry.rs:201`,
**checked**; DESIGN.md §12): building the instance with `Ord.byKey
Text.toList` would give a different, slower comparison. Its laws come
from a **bridge lemma**: `Text.compareChars xs ys` (the definition of
`Text.compare`, `core.sw:556-565`) equals `List.instOrd`'s `compare` at
`Char`, by induction on the lists. That proves `Text.compare`'s laws,
which aren't proved today (docs/core.md "Sorting": "not proved: …
totality of `Text.compare`").

### 6.3 `Add` and `Mul`

```
interface Add (a: Type) =
  { zero: a
  , add: a -> a -> a
  , zeroAdd: (x: a) -> add zero x = x
  , assoc: (x: a) -> (y: a) -> (z: a) -> add (add x y) z = add x (add y z)
  , comm: (x: a) -> (y: a) -> add x y = add y x
  }

interface Mul (a: Type) =
  { one: a
  , mul: a -> a -> a
  , oneMul: (x: a) -> mul one x = x
  , mulOne: (x: a) -> mul x one = x
  , assoc: (x: a) -> (y: a) -> (z: a) -> mul (mul x y) z = mul x (mul y z)
  }
```

`Add` is "things you can add, starting from zero, in any order" (a
commutative monoid). `Mul` is "things you can multiply, starting from
one" (a monoid; not commutative, so matrices fit). Instances: `Nat`,
`Int` for both (`Nat.instAdd := { zero = 0, add = Nat.add, … }`); a
user's `Point` or `Money` for `Add`. Nothing else for now (D166): no
`Ring`, no subtraction interface.

They replace (§2.5): `List.sum`, `List.sumBy`, `List.product`,
`List.sumInt`, `List.sumIntBy` with three generic functions;
`List.maximum`/`List.minimum` become generic through `Ord`.

### 6.4 `Show`

As in §5.14. Instances: `Nat`, `Int`, `Bool`, `Char`, `Text`, `Unit`,
`Ordering`, `List a`, `Maybe a`, `(a, b)`; derived for user types.

### 6.5 Not included

`Hash` (no hash maps planned), `Functor`/`Monad` (§5.15), numeric
literals (`OfNat`), `Append` for `++` (two instances, `Text` and `List`;
not worth an interface yet).

---

## 7. Worked examples

All in the proposed syntax. Library proofs are sketched where they're
long.

### 7.1 `DecEq` and `Ord` for `Nat` and `Text`

```
instance Nat.instDecEq: DecEq Nat := { decide = Nat.decEq }

instance Nat.instOrd: Ord Nat :=
  { compare = Nat.compare
  , LessThan = Nat.LessThan, decLessThan = Nat.decLessThan
  , LessEq = Nat.LessEq,     decLessEq = Nat.decLessEq
  , equal = Nat.compareEqual, flip = Nat.compareFlip, trans = Nat.compareTrans
  , lessThanOf = Nat.lessOfCompare, lessThanTo = Nat.compareOfLess
  , lessEqOf = Nat.leOfCompare,     lessEqTo = Nat.compareOfLe
  }

instance Text.instOrd: Ord Text :=
  Ord.fromCompare Text.compare Text.compareEqual Text.compareFlip Text.compareTrans
```

`eq` isn't written: it's filled with `Nat.instDecEq` and
`Text.instDecEq` when the records are built, and checked when the
instances are registered (§5.8).

### 7.2 Pairs and lists

```
instance Pair.instDecEq [auto decEqA: DecEq a] [auto decEqB: DecEq b]: DecEq (a, b) :=
  { decide = (p q => Pair.decEq DecEq.decide DecEq.decide p q) }

instance List.instOrd [auto ord: Ord a]: Ord (List a) :=
  Ord.fromCompare (List.compareLex Ord.compare)
    (List.compareLexEqual ord.equal)
    (List.compareLexFlip ord.flip)
    (List.compareLexTrans ord.equal ord.trans)
```

In `List.instOrd`, `fromCompare`'s `DecEq (List a)` is found by
`List.instDecEq`, whose own `DecEq a` is `ord.eq` (step 4 of §5.5). The
registration check (§5.8 (b)) compares that with resolving
`DecEq (List a)` in the instance's context, which finds the same thing.

`(1, "b") < (1, "c")`, `[[2], [1]].sort` and `"apple" < "banana"` then
work.

### 7.3 A user's record

```
namespace Shop

type Item = { name: Text, price: Nat }
```

`Shop.Item` gets `DecEq` and `Show` derived (from stages 2 and 6) and
`Ord` (from stage 7): `==`, `"${item}"` (`{ name = "tea", price = 3 }`)
and `items.sort` (by `name`, then `price`) work with no more code. To
order items by price instead, declare the instance in a file of `Shop`,
which replaces the derived one:

```
instance Item.instOrd: Ord Item :=
  Ord.byKey (i => (i.price, i.name)) Item.byPriceInjective
```

`Item.byPriceInjective` proves that the key `(price, name)` tells items
apart: equal pairs have equal components, and a record is determined by
its fields.

An instance of `Ord Item` in another module, say `Report`, is
`E-INSTANCE-ORPHAN`: "`Ord Item` must be declared in `Std` (which owns
`Ord`) or `Shop` (which owns `Item`)". `Report` can still define
`def Report.byPrice: Ord Item := …` and pass it by name.

The same for text, a named alternative ordered by length and then
alphabetically (ordering by length alone would break the `equal` law,
since different texts can have the same length):

```
def Text.byLengthThenText: Ord Text :=
  Ord.byKey (t => (t.length, t)) (s t h => Eq.cong Pair.snd h)
```

### 7.4 Generic `List.sort`

```
def List.sort [auto ord: Ord a] (xs: List a): List a := List.sortBy Ord.compare xs
```

`List.sortBy` and `List.sortWith` stay, for orderings without laws.
Today's `List.sort: List Nat -> List Nat` is this at `a := Nat`, with
`Nat.compare` in place of `Nat.leq` (the sorted result is the same list;
the theorems are restated, §7.6).

### 7.5 `Map` and `Set` (signatures for SW-113)

The ordering is part of the map's type (D169). That needs one small new
feature: **an `auto` parameter on a data type**, filled in wherever the
type is written, as for a function:

```
type Map (k: Type) (v: Type) [auto ord: Ord k] =
  { tree: Map.Tree k v
  , ordered: Map.Tree.Ordered ord tree       -- erased: a proof
  }

type Set (k: Type) [auto ord: Ord k] = Map k Unit [ord := ord]

def Map.empty [auto ord: Ord k]: Map k v
def Map.insert [auto ord: Ord k] (key: k) (value: v) (m: Map k v): Map k v
def Map.get [auto ord: Ord k] (key: k) (m: Map k v): Maybe v
def Map.toList [auto ord: Ord k] (m: Map k v): List (k, v)

theorem Map.getInsert [auto ord: Ord k] (key: k) (value: v) (m: Map k v):
  (m |> Map.insert key value |> Map.get key) = Just value

instance Map.instShow [auto showK: Show k] [auto showV: Show v]: Show (Map k v [ord := o])
```

- **Writing `Map Text Nat`** in a signature means
  `Map Text Nat [ord := Text.instOrd]`: the compiler finds the instance,
  as in §5.5. Inside a generic function, `Map k v` uses the function's own
  `ord`.
- **At a call**, `m.insert key value` with
  `m: Map Text Nat [ord := Text.instOrd]`: `insert`'s `ord` is fixed by
  `m`'s type (step 1 of §5.5), not searched, even if another `Ord Text`
  is in scope. A map built with `Map.empty [ord := Text.byLengthThenText]`
  has a different type, and passing it where `Map Text Nat` is expected
  is a type error. So the `Data.Set` bug [E1] can't happen.
- **In an instance head**, a data type's `auto` parameter is a head
  variable (`[ord := o]` above, with `o` bound implicitly), never
  searched, so `Map.instShow` covers maps with any ordering, and
  resolving `Show (Map k v [ord := existing])` keeps `existing` (step 5
  of §5.5).
- **Maps are told apart by their whole ordering dictionary**, not just by
  the comparison function. Lean's `TreeMap` is indexed by the comparator
  itself [L4]; here two dictionaries with the same `compare` but, say,
  differently written law proofs give map types that don't convert. A
  "the orderings differ" message may really mean "the dictionaries
  aren't definitionally equal". With one global instance per type and
  named alternatives that are single definitions, this is rare; it's
  accepted as an initial restriction.
- **What the map holds.** The ordering adds no runtime field to the map
  (it's a type parameter; the `ordered` proof is erased). So a map is
  data whenever its keys and values are: it can be used as `State` when
  `k` and `v` satisfy `IsData` (DESIGN.md §8). A map whose values are
  functions isn't data, as today. Whether today's `IsData` check looks at
  a parameter that appears only in erased fields is **unverified**; the
  stage 4 tests below settle it.
- The kernel sees an ordinary parameter. Only the elaborator inserts it.

**Stage 4's tests** (the reviewer's list):

| Case | Expected |
|---|---|
| A `Map Nat Nat` built with a named alternative ordering, used as `State` | Accepted |
| A map whose values are functions, used as `State` | Rejected (`IsData`) |
| An operation on an existing map while a different `Ord` for the key type is in scope | The map's own ordering is used, from its type |
| A map passed where a parameter's type names a different ordering | Type error, saying the orderings differ |
| Resolving an instance whose head fixes a map's ordering (`Show (Map k v [ord := o])`) | `o` is kept, not re-resolved |

### 7.6 A proof that uses `Ord`'s laws

Today's sorting theorem needs a "total" fact about the comparison
(**checked**, `List/Sort.sw:507-509`):

```
theorem List.sortBySorted (cmp: a -> a -> Ordering)
  (tot: (x: a) -> (y: a) -> Ordering.isLessEq (cmp x y) = False -> Ordering.isLessEq (cmp y x) = True)
  (xs: List a): List.Sorted (x y => Ordering.isLessEq (cmp x y)) (List.sortBy cmp xs)
```

With `Ord`, the fact comes from the `flip` law, once, for every type:

```
-- If `o` isn't `Less` or `Equal`, the opposite is.
theorem Ordering.flipNotLessEq: (o: Ordering) -> Ordering.isLessEq o = False -> Ordering.isLessEq (Ordering.flip o) = True
  | Less, h    => Void.absurd (Bool.trueNotFalse h)
  | Equal, h   => Void.absurd (Bool.trueNotFalse h)
  | Greater, _ => rfl

theorem Ord.leTotal [auto ord: Ord a] (x: a) (y: a)
  (h: Ordering.isLessEq (Ord.compare x y) = False): Ordering.isLessEq (Ord.compare y x) = True :=
  rewrite ord.flip x y in Ordering.flipNotLessEq (Ord.compare x y) h

theorem List.sortSorted [auto ord: Ord a] (xs: List a):
  List.Sorted (x y => Ordering.isLessEq (Ord.compare x y)) (List.sort xs) :=
  List.sortBySorted Ord.compare Ord.leTotal xs
```

`ord.flip x y` proves `compare y x = Ordering.flip (compare x y)`;
`rewrite` turns the goal into
`Ordering.isLessEq (Ordering.flip (compare x y)) = True`, which the lemma
proves. The theorem now holds for `Nat`, `Text`, pairs, lists and every
user type with an `Ord`.

### 7.7 Generic `sum`, and a proof with `Add`'s laws

```
def List.sum [auto add: Add a] (xs: List a): a := List.foldLeft Add.add Add.zero xs

def List.sumBy [auto add: Add b] (f: a -> b) (xs: List a): b :=
  List.foldLeft (acc x => acc + f x) Add.zero xs        -- `+` on `b`: Add.add, from `add`
```

`[1, 2, 3].sum` is `6: Nat`; `[3, -5, 1].sum` is `-1: Int`;
`[p, q].sum` adds `Point`s. `List.sumInt` and `List.sumIntBy` go.
`List.sum [add := Nat.instAdd] xs` computes to
`List.foldLeft Nat.add 0 xs`, today's definition, so today's `Nat` sum
lemmas still apply by computation.

A proof using the laws, given the library lemma
`List.sumCons [auto add: Add a] (x: a) (xs: List a): List.sum (Cons x xs) = x + List.sum xs`
(today's `List.sumCons`, `List/Sort.sw:77`, generalised; its proof uses
`zeroAdd`, `assoc` and `comm`):

```
theorem List.sumAppend [auto add: Add a]: (xs: List a) -> (ys: List a) ->
    List.sum (List.append xs ys) = List.sum xs + List.sum ys
  | Nil, ys => Eq.sym (add.zeroAdd (List.sum ys))
  | Cons x xs, ys =>
    calc List.sum (Cons x (List.append xs ys))
      _ = x + List.sum (List.append xs ys) := List.sumCons x (List.append xs ys)
      _ = x + (List.sum xs + List.sum ys) := Eq.cong (t => x + t) (List.sumAppend xs ys)
      _ = (x + List.sum xs) + List.sum ys := Eq.sym (add.assoc x (List.sum xs) (List.sum ys))
      _ = List.sum (Cons x xs) + List.sum ys := Eq.cong (t => t + List.sum ys) (Eq.sym (List.sumCons x xs))
```

Inside this theorem `+` is `Add.add` from the dictionary `add`, a
parameter, so it isn't projected. In the `Nil` case the goal computes to
`List.sum ys = Add.zero + List.sum ys`, which is the law `zeroAdd`,
reversed. At `Nat`, `List.sumAppend [add := Nat.instAdd]` states
today's fact about `Nat` sums, by computation.

---

## 8. Errors

Each has a stable code and an example in `examples/reject/`.

| Code | When | Message (sketch) |
|---|---|---|
| `E-INSTANCE-NONE` | No instance for a type | "no `Ord` instance for `Shop.Item`". Notes: why none was derived ("`Ord` isn't derived for `Item`: field `tag` is a function"); where one may be declared ("in `Std` or `Shop`"); a named alternative of the right type in scope, if any ("`Report.byPrice` has type `Ord Item`: pass it with `[ord := Report.byPrice]`") |
| `E-INSTANCE-UNKNOWN-TYPE` | The goal's type is still unknown at the end of the declaration | "can't tell which type's `Ord` to use here"; note: "annotate, e.g. `(xs: List Nat)`" |
| `E-INSTANCE-AMBIGUOUS` | Two distinct dictionaries in scope match | "two different `A a` dictionaries are in scope: `d.b.a` and `d.c.a`"; note: "pass one by name" |
| `E-INSTANCE-REDUNDANT` | A signature asks for an interface and its own parent on one type | "`Ord a` already contains a `DecEq a`; remove `[auto e: DecEq a]`" |
| `E-INSTANCE-OVERLAP` | A second instance for the same head | "`Ord Item` already has an instance, `Item.instOrd` (file:line)" |
| `E-INSTANCE-ORPHAN` | Instance outside the owners' modules | as §7.3; for a synonym, a note: "`LocalNat` is another name for `Nat`, which `Std` owns" |
| `E-INSTANCE-HEAD` | Head (after unfolding) not a nominal type applied to distinct variables | "an instance must be for a type name applied to variables, like `Ord (List a)`; `Ord (List Nat)` isn't" |
| `E-INSTANCE-PARAMETER` | A parameter matching can't fix | "`prefix` isn't fixed by `Show Item`; an instance can't have other parameters" |
| `E-INSTANCE-CONTEXT` | A prerequisite isn't on a head variable | "`[auto ord: Ord (List a)]`: an instance may only ask for interfaces of `a`" |
| `E-INSTANCE-SUPER` | A global instance's parent isn't the canonical one | "the `DecEq Text` inside `Text.instOrd` isn't `Text.instDecEq`" |
| `E-INSTANCE-BUDGET` | The step budget ran out | "stopped looking for `DecEq …` after N steps; this is a limit, not a missing instance" |
| `E-INTERFACE-CYCLE` | An interface is its own superclass, directly or not | names the cycle |
| `E-AUTO-NONE` | Unchanged, for `Decidable` goals | "no way to decide `f = g`"; note: "`Nat -> Nat` has no `DecEq` instance" |

`E-INSTANCE-NONE` replaces today's `E-AUTO-NONE` for `==` on a type
without equality (the notes that say why carry over from `derive.rs`).

---

## 9. Namespaces, imports, hashing and caching

### 9.1 Imports don't matter

To use `Ord T`, the program mentions `T` or has a value of type `T` from
somewhere. Either way the module that owns `T` is checked before it (a
dependency, directly or through others), and so is the module that owns
`Ord`. The one instance for `Ord T` is in one of those two (§5.6), and by
rule 4 its signature is registered when that module is checked. So the
instance found never depends on imports, on qualified names, or on
sibling files (**inferred**; the reviewer agreed, given §5.6's rules).
That settles multi-file Q1 for interfaces (D172). Imports only decide
which *names* can be written short: `import Ord (compare)`.

`Decidable` keeps D9's rule unchanged.

### 9.2 Where `Std`'s instances live

`Std`'s library files are checked only when a program uses something in
them (std-library.md). An instance in an unloaded file would be missed.
Stage 1 follows D58 for `Decidable`: **every `Std` instance is in core**
(D170). Later, std-library.md's index can list `(interface, head) → file`
and load on demand; uniqueness makes that index a simple map.

### 9.3 Hashing and caching

- **What was chosen is hashed.** Which instance was found is part of the
  elaborated term (or, after projection, its field's term is), so it's
  in the hash of the definition that uses it, like today's decision
  procedures (DESIGN.md §11).
- **An interface is a record**: its hash is a record's (nominal: names
  included).
- **The `instance` marker is hashed** (D171), like `theorem` is
  (docs/core.md "Tests and content hashes").
- **That isn't enough for an elaboration cache** (the reviewer's point).
  If `Shop` gains a hand-written `Show Item`, the derived one disappears,
  and a caller that interpolates an `Item` must be elaborated again,
  though neither its source nor `Item`'s hash changed. Today nothing goes
  wrong, because **elaboration isn't cached**: every command
  re-elaborates (multi-file.md §8.3, **checked**); only kernel checks,
  tests and JS are cached, keyed by the elaborated terms' hashes, which
  do change. **Any future elaboration cache** (DESIGN.md §11's "Source →
  elaborated declaration" layer, or multi-file's per-namespace cache)
  must include, for each module the cached result depends on, an
  **instance environment fingerprint**: which records are interfaces;
  each registered instance's name, interface and head; and which derived
  instances were suppressed. It changes whenever an instance is added,
  removed or re-headed. `Decidable` instances are already in that key
  (DESIGN.md §11: "the set of registered decision procedures"). The
  distinction to keep: the term's hash records *what was selected*; the
  cache must also know *when the available selection changes*.
- Hash stability isn't a goal. Stages 2 and 5 change the hashes of
  everything that uses `==` or the generalised functions; the test cache
  just reruns. Stage 5 also uses hashes as its oracle (§5.13).

---

## 10. At runtime: dictionaries, JavaScript, speed

- **Dictionary passing.** An instance is a record value, so it's a
  runtime argument. In JS a record is a plain object (docs/core.md
  "Erasure and JS extraction"): `Nat.instOrd` is
  `{ eq: …, compare: …, decLessThan: …, decLessEq: … }`, with the
  relations and laws left out (erased). A generic call passes it; a
  method is a property read.
- **Monomorphic code is unchanged.** Known-instance projection (§5.13)
  means `x + y` on `Nat` is `Nat.add x y` in the elaborated term, so the
  JS and its natives (`bigint` arithmetic, `Text.compare`) are exactly
  today's.
- **Natives inside dictionaries.** `Nat.instOrd.compare` *is*
  `Nat.compare`, so generic code at `Nat` still calls the native through
  the dictionary.
- **Exports.** An export's types must be concrete (DESIGN.md §12), so an
  exported function never takes a dictionary from JS. Instances are
  resolved inside. Nothing at the boundary changes. A `Map` export can
  come later (it's data, §7.5).
- **Speed of generic code.** One extra argument and one property read per
  operation. *Later, optional:* specialising generic functions for known
  dictionaries, as GHC's `SPECIALIZE` does [H6]. Not proposed now.
- **Compile time.** Global lookup is by `(interface, head)`, a map, so
  faster than today's scan of every `Decidable` definition
  (`auto.rs:269-300`).

---

## 11. The kernel

Nothing changes in what the kernel checks:

| Feature | What the kernel sees |
|---|---|
| `interface` | A record data type (one constructor, projections) |
| `instance` | A definition |
| Methods | Definitions that project a field |
| `[auto ord: Ord a]` | A `Pi` with the auto marker, as today |
| Superclass field | A field; filled in and checked by the elaborator |
| Known-instance projection | The field's term, which the kernel checks like any other |
| `Map`'s `[auto ord: Ord k]` | An ordinary data parameter |
| Laws, `LessThan`, `LessEq` | Erased fields, as today |

The one change in `crates/core` is in hashing: an `instance` flag on
definitions, hashed (D171). It doesn't affect checking.

---

## 12. Stages

Sizes are rough: Rust lines added or changed, and Stitchwort library
lines. Each stage ends with the full gate.

| # | Stage | `syntax` | `elab` | `core` | `std` (.sw) | Tests |
|---|---|---|---|---|---|---|
| 1 | **Interfaces and instances.** `interface`, `instance`, `[auto I a]` without a name, generated methods, the instance table and the module rules of §5.6 (ownership, orphans, overlap, all signatures first, synonyms), the complete-signature rules of §5.2, §5.5's algorithm (one-way matching, waiting, budget), superclass filling and checking (§5.8), `E-INSTANCE-*` errors. Test interfaces only | ~250 | ~1,200 | ~30 (flag, hash) | 0 | ~20 accept, ~16 reject; must-reject pairs for overlap, orphan, synonym-orphan (`LocalNat`), head, parameter, context, ambiguity (order of locals swapped gives the same error), diamond, cycle; a twelve-deep `DecEq (List …)`; the `Base`/`Child` record of §5.8 |
| 2 | **`DecEq` replaces `=`'s procedures.** `DecEq` and its instances; `==`/`if h: x = y` through it; hypotheses first for proof obligations; derived `T.%instDecEq` with value parameters and equation proof fields (D179); `DecEq.uniqueEq`; `decide_under` and `local_deciders` removed; `instance` marker on the remaining `Decidable` procedures | ~20 | ~500 (and ~300 removed) | 0 | ~250 | all `eqeq-*`, `if-decidable`, derive examples unchanged in behaviour; `[auto ok: f = g]` with `h: f = g` in scope; `Dial` gets `==`; AoC programs and proofs pass (3 places spell out `Nat.decEq`/`List.decEq` terms and may need edits) |
| 3 | **`Ord`.** With its laws and relation fields; `Ord.fromCompare`, `Ord.byKey`; instances for `Nat`, `Int`, `Char`, `Bool`, `Ordering`, `Text` (bridge lemma), `List`, `Maybe`, pairs; generic `List.sort` and §7.6's theorems; `List.maximum`/`minimum` generic | 0 | ~150 | 0 | ~800 (proofs: Opus) | `sort.sw` examples; new `ord-*.sw`; `Text`'s laws |
| 4 | **`auto` parameters on data types** (for `Map`, D169). Unblocks SW-113 | ~30 | ~300 | 0 | 0 | §7.5's five cases, plus `Map Text Nat` filled by search |
| 5 | **Operators through dictionaries.** `Add`, `Mul` and instances; `+ * < <=` resolved by §5.5 for every type, with known-instance projection; generic `sum`/`sumBy`/`product`; remove `sumInt`/`sumIntBy`; restate the sum lemmas generically (§7.7) | 0 | ~400 | 0 | ~400 (moved and generalised) | **hash oracle**: every existing definition's hash unchanged except callers of generalised functions; `before`/`beforeNat` (§5.13) agree; a `Point` with `+`; AoC day 2 proofs (heavy users of sum lemmas) |
| 6 | **`Show` and interpolation**; derived `Show` (`toText`/`toSource`) | 0 | ~350 | 0 | ~100 | interpolation examples; derived text for data, records (proof fields left out), lists of texts (`["a", "b"]`) |
| 7 | **Derived `Ord`** (enums and records first, then data types with fields) | 0 | ~400 | 0 | ~200 (combinator proofs) | `derive-ord-*` examples; `Dial` ordered by `position` |
| later | Dot notation through dictionaries in scope (D173); the `Std` instance index (§9.2); specialisation (§10) | | | | | |

JS: no code-generation changes are expected (records are already plain
objects, and projection keeps monomorphic terms as they are). Each stage
adds differential extraction tests for its generic functions
(`crates/cli/tests/extract.rs`, ~50 lines per stage).

**Order and parallel work.** 1 then 2 (2 deletes code that 1 makes
redundant). 3 and 4 can run in parallel after 2. SW-113 starts after 3
and 4. 5 needs 3 (for `Ord`'s relation fields). 6 and 7 are independent
of 5 and of each other. The indexed-families design
(docs/proposals/indexed-families.md) doesn't interact: an instance head
may be an indexed family applied to variables (`DecEq (Vec a n)`), and
nothing here depends on how families are checked.

---

## 13. Risks

1. **Proofs that spell out decision terms** (`Decidable.toBoolSound (Nat.decEq a 1) …`
   in `aoc/src/Aoc/Day04/Proofs/Part1.sw:125`; `List.decEq (a b => Nat.decEq a b)`
   in `Day02/Proofs/Repeated.sw:229, 290`, **checked**). After stage 2,
   `a == 1` on `Nat` is projected (§5.13) to `Nat.decEq a 1`, today's
   term; `==` on lists becomes `List.instDecEq`'s `decide`, which
   computes to the same thing. Stage 2's oracle is the full AoC proof
   suite. `DecEq.sound` (§6.1) makes such proofs shorter.
2. **Proof speed in generic lemmas at `Nat`.** Generic `List.sum` at `Nat`
   unfolds one more layer (the dictionary and the projection). Day 2's
   proofs use many sum lemmas (`List/Sort.sw:65-320`). Measure in stage
   5; if it's slow, keep `Nat`-specific lemmas as thin corollaries.
3. **Matching instance heads after unfolding.** A goal written with a
   definition (`IsTrue c`, which unfolds to `c = True`) may or may not
   reach `DecEq`, depending on how far unification unfolds. Today's
   `aoc/day02` keeps a special `decIsTrue` for this reason
   (multi-file §4.9.4). Stage 2 should look at the goal after unfolding
   definitions at its head, and keep a test for `IsTrue`.
4. **`Ord` is wide.** Thirteen fields, nine of them laws. Users meet it
   through `Ord.fromCompare`, `Ord.byKey` and derivation; only the
   `Nat`/`Int` instances are written in full. If it proves a burden,
   D180's option B is the fallback, at the price of §5.13's discrepancy.
5. **Deriving `Show` and `Ord` eagerly costs time per type**, as `DecEq`
   does today (1–6 ms per type, `derive.rs`). Acceptable; measure.
6. **Dictionaries in scope shadow globals** (D159): inside
   `List.sort [ord := Nat.descending]`, every `Ord Nat` uses it, `<` on
   `Nat` included (§5.13). That's the point, and `Map`'s design (§7.5)
   makes it harmless for data structures.
7. **Records stage 4's `HasField`** is a two-parameter interface with a
   dependency. It stays its own derived mechanism, as records.md §9.2
   describes, not an `interface` (D174).

---

## 14. Decisions

Each with a recommendation and the external reviewer's verdict on draft
1. D154–D160 and D162 block stage 1 or 2; the rest can wait for their
stage. D175–D177 are taken by other notes.

| # | Decision | Recommendation | Reviewer (draft 1) |
|---|---|---|---|
| D154 | **Laws in the interface**, as proof fields; orderings without laws stay plain function arguments (`sortBy`) (§5.9) | Bundled | Accept |
| D155 | **The equality interface is `DecEq`**, since `Eq` is `=`'s lemma namespace (§5.12) | `DecEq` | Accept |
| D156 | **Declarations**: `interface Ord (a: Type) = { … }`; `instance Nat.instOrd: Ord Nat := …`, always named (§5.1, §5.2) | As written | Accept |
| D157 | **Asking**: the `auto` binder, name optional (`[auto Ord a]`, `[auto ord: Ord a]`) (§5.3) | `auto` | Accept |
| D158 | **Coherence**: one instance per interface and head; ownership by declaring module; orphan rule; synonyms unfold and own nothing; heads a nominal type applied to distinct variables; complete signature = head variables + prerequisites on them; all of a module's instance signatures registered first; overlap checked when declared (§5.2, §5.6) | Yes | Accept, with the ownership, alias and whole-module rules made explicit (done) |
| D159 | **Resolution and alternatives**: §5.5's algorithm (one-way matching, waiting for unknown types, dictionaries in scope before globals, ambiguity only for distinct candidates, prerequisites fixed by matching kept); other choices are named alternatives passed by name (§5.5, §5.7) | Yes | Accept; specify matching and name overridable parameters (done) |
| D160 | **Superclasses**: filled when an interface literal is built; checked, never replaced, when a global instance is registered; full-closure search with definitional merging and ambiguity naming paths; acyclic superclass graph; the guarantee as stated in §5.8 | Yes (redesigned) | Revise (done) |
| D161 | **No default methods**; helpers and builders (`Ord.fromCompare`) are generic functions (§5.10) | Yes | Keep deferred |
| D162 | **`=` is decided only through `DecEq`**; proof obligations use hypotheses first; other `Decidable` goals keep D9's first-fit search (§5.12) | Yes | Accept for decisions; keep hypotheses first (done) |
| D163 | **Decision procedures need the `instance` marker** (§5.12) | Yes | Not commented on |
| D164 | **Derived instances**: `DecEq` (as today's `==`), `Show`, later `Ord`; the owner's own instance replaces the derived one; scope as D179 (§5.11) | Yes | Accept; document proof and dependent fields (done, D179) |
| D165 | **Operators**: `+ * < <=` mean the resolved dictionary for every type, `Nat` and `Int` included, with known-instance projection; `- / %` stay numbers only; no generic literals (§5.13) | Uniform (changed from draft 1) | Reconsider the exception; prefer uniform for `+ *`; make the `<` tradeoff explicit (done) |
| D166 | **Numeric interfaces**: only `Add` (commutative) and `Mul` (§6.3) | Yes | Keep deferred (no tower) |
| D167 | **`${e}` uses `Show` only** (`toText`), not dot notation (§5.14) | Yes | Not commented on |
| D168 | **`Functor`/`Monad` not now** (§5.15) | Not now | Keep deferred |
| D169 | **`Map`/`Set` carry their ordering dictionary in their type**, via `auto` parameters on data types; types differ by whole dictionary; data when keys and values are (§7.5) | In the type | Accept, with the dictionary-identity and `IsData` limits stated (done) |
| D170 | **All of `Std`'s instances in core** for now; an index later (§9.2) | Yes | Not commented on |
| D171 | **The `instance` marker is hashed**; any future elaboration cache keys on a per-module instance environment fingerprint (§9.3) | Yes | Accept with the fingerprint (done) |
| D172 | **Imports and qualified names never change which instance is found** (§9.1) | Yes | Accept, given the ownership rules |
| D173 | **Dot notation through dictionaries in scope** (`x.compare y` for `x: a`) (§5.4) | Later | Not commented on |
| D174 | **One type parameter**; no multi-parameter interfaces, output parameters or `Type -> Type` interfaces; `HasField` stays special (§5.1) | Yes | Keep deferred |
| D178 | **`Show` has two fields**, `toText` (for `${…}`) and `toSource` (source syntax, used for elements of containers and records) (§5.14) | Yes | New (answers review 9c) |
| D179 | **Derivation's boundary**: value parameters are allowed; proof fields that are equations in a type with `DecEq` are ignored (by Hedberg, `DecEq.uniqueEq`); other proof fields, function and type fields stop it (§5.11) | Yes | New (answers review 9b) |
| D180 | **`Ord` carries `LessThan`, `LessEq` and their deciders as fields**, so `<` and `<=` can be uniform with no proof migration. Option B: keep `<`/`<=` built in for `Nat`/`Int` and document the discrepancy (§5.13, §6.2) | Fields (A) | New (answers review 3) |
| D181 | **Names**: instances `T.instI` by convention; generated methods' and library functions' dictionary parameters named after the interface (`ord`, `decEq`, `add`, `mul`, `show`) so they can be overridden (§5.1, §5.3) | Yes | New (answers review 8) |
| D182 | **A step budget, not a depth limit**, for interface resolution; running out is "stopped", never "none". `Decidable` keeps depth 8 (§5.5) | Yes | New (answers review 4) |

---

## 15. Sources

Pages were read on 20 October 2026 unless marked "via multi-file.md",
meaning they were verified on 19 October for that note.

- [L1] Lean Language Reference, "Instance Synthesis":
  https://lean-lang.org/doc/reference/latest/Type-Classes/Instance-Synthesis/
  (output parameters: "Output parameters are ignored when checking
  whether an instance matches the problem"; default instances "are
  attempted in order of priority"; priorities, then "more recent
  instances taking precedence over earlier ones"; "any local variable
  whose type is a type class is a candidate"; instances assumed
  canonical: "any discovered instance should be considered as good as
  any other").
- [L4] Lean API documentation, `Std.TreeMap`:
  https://lean-lang.org/doc/api/Std/Data/TreeMap/Basic.html
  (`structure Std.TreeMap (α : Type u) (β : Type v) (cmp : α → α → Ordering := by exact compare)`;
  `insert (l : TreeMap α β cmp) (a : α) (b : β) : TreeMap α β cmp`; the
  comparator "should satisfy certain laws", `OrientedCmp` and `TransCmp`),
  and https://lean-lang.org/doc/api/Std/Data/TreeMap/Lemmas.html
  (lemmas assume `TransCmp cmp`; `LawfulEqCmp` for `cmp a b = .eq`
  implying `a = b`).
- [H1] Haskell 2010 Report, §4.3.2 "Instance Declarations":
  https://www.haskell.org/onlinereport/haskell2010/haskellch4.html
  ("The type (T u1 … uk) must take the form of a type constructor T
  applied to simple type variables u1, … uk"; distinct, not a synonym;
  "A type may not be declared as an instance of a particular class more
  than once in the program").
- [H4] GHC User's Guide, `-Worphans` (via multi-file.md [H4]):
  https://downloads.haskell.org/ghc/latest/docs/users_guide/using-warnings.html
- [H5] GHC User's Guide, overlapping instances (via multi-file.md [H5]):
  https://downloads.haskell.org/ghc/latest/docs/users_guide/exts/instances.html
- [H6] GHC User's Guide, `SPECIALIZE` pragma:
  https://downloads.haskell.org/ghc/latest/docs/users_guide/exts/pragmas.html
  (cited only as the standard example of specialisation; wording
  **unverified**).
- [E1] Edward Z. Yang, "Type classes: confluence, coherence and global
  uniqueness" (2014), via multi-file.md [E1]:
  http://blog.ezyang.com/2014/07/type-classes-confluence-coherence-global-uniqueness/
- [R1] The Rust Reference, "Implementations", trait implementation
  coherence and orphan rules:
  https://doc.rust-lang.org/reference/items/implementations.html
  ("A trait implementation is considered incoherent if either the orphan
  rules check fails or there are overlapping implementation instances";
  "a trait implementation is only allowed if either the trait or at
  least one of the types in the implementation is defined in the current
  crate").
- [A1] Agda, "Instance Arguments":
  https://agda.readthedocs.io/en/latest/language/instance-arguments.html
  ("Top-level instances must target a named type"; "instance resolution
  does not make unforced choices between instances"; `OVERLAPPABLE`,
  `INCOHERENT`; "Superclass dependencies can be implemented using Records
  and instance search"; postponement when there are several candidates).
- [I1] Idris 2 tutorial, "Interfaces":
  https://idris2.readthedocs.io/en/latest/tutorial/interfaces.html
  (`interface Eq a => Ord a`; named implementations `[myord] Ord Nat`,
  used as `sort @{myord} testList`; "Only one implementation of an
  interface can be given for a type - implementations may not overlap";
  "the arguments of an implementation must be constructors (either data
  or type constructors) or variables").
- [I2] Idris 2 tutorial, "Miscellany", auto implicits (via multi-file.md
  [I2]): https://idris2.readthedocs.io/en/latest/tutorial/miscellany.html
- [I3] Idris 2 base library, `Decidable.Equality.Core`:
  https://idris-lang.org/Idris2/base/source/Decidable.Equality.Core.html
  (`interface DecEq t` with `decEq : (x1 : t) -> (x2 : t) -> Dec (x1 = x2)`;
  seen through search results and the generated docs at
  https://idris2docs.sinyax.net/data/base/docs/Decidable.Equality.Core.html).
- [S1] Scala 3 Reference, "Changes in Implicit Resolution":
  https://docs.scala-lang.org/scala3/reference/changed-features/implicit-resolution.html
  (deeper nesting wins; "an alternative that takes some context
  parameters is taken to be less specific than an alternative that takes
  none"; equal candidates are ambiguous; from 3.5 the most general given
  is preferred).
- [M1] Assia Mahboubi and Enrico Tassi, "Canonical Structures for the
  working Coq user": https://hal.archives-ouvertes.fr/hal-00816703 (record
  page; the paper compares canonical structures with type classes and
  unification hints), and the Rocq reference manual chapter by the same
  authors:
  https://docs.rocq-prover.org/v8.17/refman/language/extensions/canonical.html
  (paper not re-read in full for this note).
