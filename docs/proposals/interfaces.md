# Proposal: interfaces

**Status:** draft 1, 20 October 2026. Design only, nothing is built.
Ticket SW-4, decision D152 (Matt, 20 October 2026: write this note).
Open questions are numbered D154 to D174 ([§14](#14-decisions)), each
with a recommendation.

This note can be read without knowing the codebase. Code references were
checked at commit `913d9bd`. Claims are labelled **checked** (with a
source or `file:line`), **inferred** (reasoned from checked facts), or
**unverified** where it matters. Sources are listed at the end, as
[L1], [H1] and so on.

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
   operations, plus **laws**: proof fields saying the operations behave
   (for `Ord`, that the order is consistent). The kernel needs nothing
   new (§5.1, §11).
2. **An instance is a named definition** of that record type, marked
   `instance`: `instance Nat.ord: Ord Nat := { … }` (§5.2).
3. **Functions ask for one with `auto`**, which already means "the
   compiler finds this": `def List.sort [auto Ord a] (xs: List a)` (§5.3).
4. **One instance per type, checked when it's declared.** An instance
   must live in the namespace of the interface or of the type (Rust's and
   Haskell's "orphan" rule), and its type is a type name applied to
   variables (Haskell 98's rule). Then two instances for the same type
   can only meet inside one namespace, so the overlap check is local.
   That answers the multi-file reviewer's objection (§5.6).
5. **Finding an instance is a lookup, not a search.** Arguments in scope
   first, then the one global instance for that interface and type
   (§5.5). No order to break ties, so nothing depends on file order,
   load order or imports.
6. **Other choices are passed by name**: `List.sort [ord := Nat.descending] xs`
   (§5.7).
7. **`==` moves onto the `DecEq` interface** (deciding `=`; Idris 2 has the
   same one). The derived `==` for data types becomes a derived `DecEq`
   instance. `Decidable` for other propositions (`<`, `&&`, …) keeps
   today's first-fit search, which is safe for it (§5.12).
8. **`Ord`, `Add`, `Mul` and `Show`** join `DecEq` in the library (§6).
   They remove `List.sum`/`List.sumInt` and similar pairs, make `List.sort`
   generic, and give `Map`/`Set` their keys. `+` and `*` on other types
   use `Add` and `Mul`; `<` uses `Ord`; `${e}` uses `Show`. `Nat` and
   `Int` arithmetic is unchanged (§5.13, §5.14).
9. **A `Map` carries its ordering in its type**, as Lean's `TreeMap` does
   [L4]: `Map Text Nat` means "ordered by `Text`'s instance". A map can't
   be searched with a different order from the one it was built with
   (§7.5).
10. **Not now:** `Functor`/`Monad` (abilities and dot notation cover the
    uses), default methods, interfaces with several type parameters,
    generic number literals (§5.10, §5.15, §6.5).

The build is seven stages, about 3,000 lines of Rust and 1,500 lines of
Stitchwort library (§12). `SW-113` (`Map`/`Set`) can start after stage 4.

---

## 1. Words used here

- **Interface**: a named description of operations a type supports, with
  laws. Haskell and Lean call it a *type class*, Rust a *trait*, Scala a
  *type class* encoded with `given`s.
- **Instance**: the operations of an interface for one type. Rust: an
  `impl`. Scala: a `given`. Idris: an *implementation*.
- **Dictionary**: an instance as a value at runtime: a record of
  functions, passed as a hidden argument. Interfaces in Haskell, Lean and
  Scala compile this way.
- **Law**: a fact the operations must satisfy, such as "if `x < y` and
  `y < z` then `x < z`". Here, a proof field of the record.
- **Coherence**: the program means the same thing whichever way the
  compiler finds an instance. The usual way to get it is **global
  uniqueness**: at most one instance of an interface for a type, in the
  whole program [E1].
- **Orphan**: an instance declared somewhere that declares neither the
  interface nor the type (Haskell's term [H4]).
- **Overlap**: two instances that could both answer the same request,
  such as one for `List a` and one for `List Nat`.
- **Head** of a type: its outermost type name. The head of
  `List (Maybe Nat)` is `List`.
- **Superclass**: an interface another one builds on. `Ord` builds on
  `DecEq`: anything you can order, you can compare for equality.
- **Namespace / module**: as in docs/syntax.md. A project's namespace
  (`Day05`) is one module, possibly in several files.

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
no instance markers and "first fit wins" (multi-file.md §4.9.2 says so).
It's safe for `Decidable` because two procedures can't disagree on
`Yes`/`No` ("answer agreement", multi-file.md §4.9.4). They can still
differ in the proof term, speed, and whether they get stuck (same
section).

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
unless a field rules it out (**checked**, `crates/elab/src/derive.rs:1-60`).
For a type with parameters, the procedure takes one decision procedure
per parameter, and while it's elaborated `auto` also looks at procedures
passed as arguments (`local_deciders`, `auto.rs:175-195`).

### 2.3 Operators are wired to `Nat` and `Int`

`+ - * / %` and `< <=` are the prelude's `Nat` or `Int` functions, chosen
for a whole expression at once (**checked**, `crates/elab/src/numbers.rs:1-11`;
docs/syntax.md "Numbers"). On any other type they're an error. `++` is
`Text.append` or `List.append`.

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
  (records.md §9.2). That's an interface in all but name.
- **Multi-file** (docs/proposals/multi-file.md, draft 4). §4.9 compares
  how Lean 4, Haskell, Agda and Idris 2 find instances, and §4.9.6 left a
  direction for this note: the same candidate rule as `Decidable`,
  explicit instance markers, ambiguity as an error for interfaces, named
  alternatives passed explicitly, and local instances from arguments.
- **The reviewer's overlap finding** (multi-file.md §4.9.6, "Input for
  that note"): (1) refusing overlapping instances project-wide when
  they're declared clashes with `run` checking only what it needs, and
  deciding whether two dependent instance types overlap may need
  unification the elaborator doesn't have; start with ambiguity found at
  use sites, or restrict instance types, as Idris does. (2) Make
  ambiguity an error for every interface, not only data-carrying ones,
  since Stitchwort doesn't treat two proofs as equal. (3) Revisit whether
  a bare qualified name brings in instances (multi-file Q1), and `auto`
  across sibling files. §5.6 and §9.1 answer all three.

---

## 3. Goals and non-goals

**Goals**

- **Generic library code**: one `sum`, one `sort`, one `max`, a `Map`
  for any ordered key.
- **Predictable**: which instance is used can be worked out by reading
  two places: the interface's namespace and the type's namespace. No
  priorities, no "most specific", no import order.
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
- Specialisation or other speed work (DESIGN.md: performance isn't a goal).
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
| **Idris 2** | `Ord Nat where …`, optionally named: `[myord] Ord Nat where …` [I1] | By type, like `auto` implicits [I2] | "Only one implementation of an interface can be given for a type - implementations may not overlap" [I1] | Allowed | Separate interfaces (`VerifiedSemigroup`-style), or none |
| **Scala 3** | `given Ord[T] = …` | By type and lexical scope; deeper nesting wins; then specificity; equal candidates are an ambiguity error [S1] | Error unless one is preferred by nesting or specificity [S1] | Allowed (givens are ordinary values, imported explicitly) | Documentation only |
| **Rocq** | Type classes (records + `Instance`), or **canonical structures** | Classes: proof search with priorities. Canonical structures: unification hints keyed by a type's head [M1] | Classes: first by priority. Canonical: one per head | Allowed | Proof fields (Mathematical Components' hierarchies) |

### 4.2 What the comparison shows

1. **Records are a fine encoding.** Lean, Agda and Rocq all represent an
   interface as a record and an instance as a value of it. Laws are proof
   fields in Agda's and Rocq's libraries, and separate classes in Lean's.
   Stitchwort has records already, and the kernel accepts them.
2. **Two camps on coherence.** Haskell, Rust and Idris want one instance
   per type, so the answer can't depend on how it was found. Lean and
   Rocq's type classes take the first that works and trust that instances
   agree. Haskell shows what goes wrong when they don't: with two orphan
   `Ord` instances, a `Data.Set` built with one and searched with the
   other gives wrong answers [E1]. Stitchwort proofs can see which
   instance was used (the term is part of the proof), so "they're all
   the same" isn't true here (reviewer's point 2).
3. **Rust is the only one that checks uniqueness eagerly**, and it can
   because of the orphan rule: the only places an `impl` for a given
   trait and type can be are the crate of the trait and the crate of the
   type, and the dependency graph between crates has no cycles, so one of
   them sees the other [R1]. Stitchwort's namespaces have the same
   property: cycles between namespaces are refused (`E-NAMESPACE-CYCLE`,
   docs/syntax.md).
4. **Restricting instance types keeps search simple.** Haskell 98's and
   Idris's rule (a type name applied to distinct variables) means
   instances for the same interface overlap exactly when they have the
   same head. No unification of dependent types needed (reviewer's point
   1).
5. **Named alternatives** are how Idris handles "a different order for
   this one call": `sort @{myord} xs` [I1]. Stitchwort already has the
   syntax for passing an implicit argument by name: `[x := e]`.
6. **Lean's `TreeMap` puts the comparison in the type**:
   `Std.TreeMap (α: Type u) (β: Type v) (cmp: α → α → Ordering := by exact compare)`,
   and `insert` takes no comparison of its own [L4]. So a map built with
   one ordering can't be used with another. This removes the `Data.Set`
   problem for maps even without global uniqueness.
7. **Canonical structures** (Rocq) are a different mechanism: unification
   is taught "if you need a `T` for type `X`, use this one", keyed by
   `X`'s head [M1]. With one instance per head, Stitchwort's lookup is
   close to this in spirit, but done as an `auto` search, which the
   elaborator already has, not as a change to unification.

---

## 5. The design

### 5.1 An interface is a record

```
interface Ord (a: Type) =
  { eq: DecEq a
  , compare: a -> a -> Ordering
  , equal: (x: a) -> (y: a) -> compare x y = Equal -> x = y
  , flip: (x: a) -> (y: a) -> compare y x = Ordering.flip (compare x y)
  , trans: (x: a) -> (y: a) -> (z: a) -> compare x y = Less -> compare y z = Less -> compare x z = Less
  }
```

- `interface I (a: Type) = { … }` is exactly a record declaration
  (`type I (a: Type) = { … }`, docs/syntax.md "Records"), plus a flag the
  elaborator keeps: this record is an interface. The kernel sees a data
  type with one constructor, as for any record.
- **One parameter, a type** (D174). `a: Type`, so the interface itself is
  in `Type`. No universe change.
- **Fields are operations and laws.** A field whose type is a
  proposition is a law. Laws are erased at runtime, like any proof field.
  A field may mention earlier fields (`compare` in `equal`), as record
  fields can.
- **Methods are generated.** For each field `f`, the elaborator defines
  `I.f: [a: Type] -> [auto inst: I a] -> (the field's type)`, which
  projects the field from the instance it's given. So `Ord.compare x y`
  finds the `Ord` instance for `x`'s type. The raw projection is still
  reachable as `inst.compare` by dot notation on the dictionary.
- **The interface's namespace** holds its methods and any helpers
  written later (`Ord.max`, `Ord.LessThan`). `import Ord (compare, max)`
  brings them in, as for any namespace.

Why a record and not a new kind of declaration: records already have
literals, projections, dot notation, proof fields, erasure, JS objects and
hashing. An interface reuses all of it.

### 5.2 Instances

```
instance Nat.ord: Ord Nat :=
  { compare = Nat.compare
  , equal = Nat.compareEqual
  , flip = Nat.compareFlip
  , trans = Nat.compareTrans
  }
```

- `instance` is `def` with a marker. The body is any expression of the
  interface type; usually a record literal.
- **Instances are named** (D156). The name decides its namespace
  (`Nat.ord` is in `Nat`), lets it be passed explicitly, gives it a JS
  name and gives errors something to point at.
- **The superclass field is filled in by the compiler** (§5.8). Writing
  `eq = …` is an error.
- **An instance may need other instances**, written as `auto` parameters:

  ```
  instance List.ord [auto Ord a]: Ord (List a) := { … }
  ```

- **What the instance is for**, its *head*, must be a data type or record
  name applied to distinct variables: `Ord Nat`, `Ord (List a)`,
  `Ord (a, b)`, `DecEq (Vec a n)`. Not `Ord (List Nat)`, not `Ord a`, not
  `Ord (Nat -> Nat)`, not a type synonym (Haskell 98 [H1], Idris [I1]).
  So two instances of one interface overlap exactly when they have the
  same head. A synonym is unfolded first: `instance Grid.show: Show Grid`
  for `type Grid = List (List Nat)` is `Show (List (List Nat))`, which
  isn't allowed (`E-INSTANCE-HEAD`).
- **An instance's own `auto` parameters must be on the head's
  variables**: `[auto Ord a]` for `Ord (List a)` is fine, `[auto Ord (List a)]`
  isn't. Each step of a search then works on a smaller type, so search
  always ends; `MAX_DEPTH` stays only as a safety net (Haskell's rule for
  instance contexts [H1]).

### 5.3 Asking for an instance

A function asks for an instance with an `auto` parameter, the existing
binder for "the compiler finds this" (D157):

```
def List.sort [auto ord: Ord a] (xs: List a): List a := List.sortBy Ord.compare xs
```

A name is optional: `[auto Ord a]` is `[auto _: Ord a]`. Name it when the
body uses the dictionary directly, usually for laws (`ord.trans`).

`auto` already has the right meaning in every row of DESIGN.md §6's
"four separate questions": the caller doesn't write it; it's found by
the compiler; whether it exists at runtime follows from its type (a
dictionary is data, so it's passed; a proof would be erased).

Type variables are still bound automatically: `a` above needs no
`[a: Type]`, since `Ord a` and `List a` use it where a type is expected
(docs/syntax.md "Automatic implicits").

### 5.4 Using methods

Inside `List.sort`, `Ord.compare x y` finds the instance: the parameter
`ord` is in scope, so it's used. Outside, `Ord.compare 3 5` finds
`Nat.ord`. With `import Ord (compare)`, write `compare x y`.

On a known type nothing changes: `x.compare y` for `x: Nat` is still
`Nat.compare`, by dot notation. **Dot notation on a type variable**
(`x.compare y` for `x: a` with `[auto Ord a]` in scope) would be
convenient but is a separate feature: D173 recommends it for later.

### 5.5 Finding an instance

When an `auto` parameter's type is `I T` for an interface `I`, after the
declaration's unification has done what it can (as for any `auto` today,
`auto.rs:51-78`):

1. **Given by name**, `[ord := e]`: used as is.
2. **Solved by unification**: if the type of something else already fixes
   it (§7.5's `Map`), nothing is searched. (This is today's
   "already determined by unification", `auto.rs:65`.)
3. **In scope**: a variable whose type is `I T`, such as the function's
   own `auto` parameter, or a superclass field of one (`ord.eq` for
   `DecEq a`, §5.8). If two different ones fit, it's `E-INSTANCE-AMBIGUOUS`
   (D159).
4. **Global**: `T`'s head must be known by now. If it's still an unknown
   (`Ord ?t`), the error is `E-INSTANCE-UNKNOWN-TYPE`, asking for a type
   annotation. Otherwise look up the one instance of `I` for that head
   (§5.6). None is `E-INSTANCE-NONE`. If it has `auto` parameters, find
   each the same way, from step 3.

A variable in scope wins over a global instance. That's how Lean, Scala
and Idris behave, and it's what lets a function's caller choose
(`List.sort [ord := Nat.descending]` makes every `Ord Nat` inside
`List.sort` use it, D159).

There's **no backtracking and no tie-break**. At most one global instance
can fit, so nothing depends on declaration order, file order, load order
or which namespaces were checked first. (`Decidable` is different, §5.12.)

### 5.6 One instance per type, checked locally

**The rule** (D158):

- **Orphan rule.** An instance of `I` for head `D` must be declared in
  the namespace (module) that declares `I` or the one that declares `D`.
  In file mode (a file with no namespace line), the file is the module.
- **No overlap.** At most one instance of `I` for each head `D`, anywhere.
- **Std is closed.** A program can't add to `Std`'s namespaces
  (`E-STD-NAMESPACE`, docs/syntax.md), so `Ord Nat`, `Show (List a)` and
  the rest are only ever the library's. A program that wants another
  order for `Nat` uses a named value (§5.7).

**Why the check is local** (answering the reviewer's point 1). Suppose
`Shapes` declares `type Shape` and `Geometry` declares `interface Area`.
An instance `Area Shape` names both, so the namespace it's in depends on
the other one. If one were in `Shapes` and another in `Geometry`, each
namespace would depend on the other: a cycle, already refused
(`E-NAMESPACE-CYCLE`). So all instances of `Area` for `Shape` are in one
namespace (or `Shapes` and `Geometry` are the same namespace), and
checking that namespace sees them all. The overlap check runs when that
namespace is checked, and `run` checking only what it needs (multi-file
§9.1) doesn't change the answer. (**Inferred**, from the orphan rule and
the acyclic namespace graph; it's the argument Rust relies on for crates
[R1].)

Within one namespace, the check needs the instances' heads, which are
known from the signatures (a name applied to variables). No unification
is needed (reviewer's point 1 again).

**Every interface, including proof-only ones** (reviewer's point 2):
uniqueness is checked the same way whatever the fields are.

### 5.7 Other choices, by name

A plain `def` of an interface type is not an instance. It's never found
automatically, but can be passed by name:

```
def Nat.descending: Ord Nat :=
  { compare = (x y => Nat.compare y x), equal = …, flip = …, trans = … }

def ranked := List.sort [ord := Nat.descending] scores
```

For a one-off ordering that needs no laws, today's function-argument
versions stay: `List.sortBy (x y => Nat.compare y x) scores` (D154).

### 5.8 Superclasses

`Ord` has a field `eq: DecEq a`. Three rules (D160):

1. **The compiler fills it**, when an instance is declared, by finding
   `DecEq` for the head as in §5.5. For `Nat.ord` that's `Nat.decEq`'s
   instance. So `Nat.ord.eq` *is* the `DecEq Nat` instance, by unfolding,
   and the two ways to reach `DecEq Nat` agree in proofs too. (Haskell
   and Idris do the same; in Lean an instance may write its own, which
   causes the "diamond" problems Lean's library works around.)
2. **In generic code**, `[auto Ord a]` gives `DecEq a` through the field
   (step 3 of §5.5), so `x == y` works in `List.sort` without asking for
   `DecEq a` separately.
3. **A signature can't ask for both** `[auto DecEq a] [auto Ord a]`: the
   two would be unrelated variables, and a proof inside couldn't show
   they agree (`E-INSTANCE-REDUNDANT`, "`Ord a` already gives `DecEq a`").

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
  types, and derived instances (§5.11) build their proofs from
  combinators proved once.

The cost: someone writing `Ord` by hand for an unusual type must prove
three small laws. `Ord.byKey` (§6.2) reduces most cases to "this key
function is injective".

### 5.10 No default methods

Haskell, Rust and Idris let an interface give a default for a method
("`/=` is `not (==)`"). Here that would interact with laws: an instance
that overrides a default must prove the override agrees. Instead, extra
operations are **generic functions in the interface's namespace** (D161):

```
def Ord.max [auto Ord a] (x: a) (y: a): a := match Ord.compare x y with
  | Less => y
  | _    => x
```

They work for every instance and need no proofs from instance writers.
An interface has only the fields it needs.

### 5.11 Derived instances

Today every data type and record gets `==` when declared, if its fields
allow it. That becomes a **derived `DecEq` instance**, `T.%decEq`
(D164). For a type with parameters it takes `[auto DecEq a]` instead of a
function argument, so `auto.rs`'s `decide_under` and `local_deciders`
go away.

The same is done for `Show` (no laws, so cheap) and, later, `Ord`
(lexicographic: constructors in declaration order, then fields in order),
built from combinators whose laws are proved once in the library.

**A module's own instance replaces the derived one.** If the module that
declares `T` also declares an instance of `I` for `T`, nothing is derived
for `I` and `T`. That's today's rule ("a user's own `Shape.decEq` still
takes priority", DESIGN.md §4), restated so that there's still one
instance. The declaration pre-pass already collects every declaration in
the module (docs/core.md, "The elaborator's groups"), and an instance's
head is visible in its signature, so this is known before deriving.

### 5.12 `Decidable` stays special; `=` moves to `DecEq`

```
interface DecEq (a: Type) =
  { decide: (x: a) -> (y: a) -> Decidable (x = y) }
```

- **`=` is decided only by `DecEq`.** `x == y`, `if h: x = y`,
  `[auto ok: x = y]` and `x != y` find the `DecEq` instance for `x`'s
  type and use `DecEq.decide x y`. So the most common `Decidable` goal is
  answered by a unique instance (D162).
- **Other propositions keep today's search** (`x < y`, `p && q`,
  `Not p`, user predicates): any definition marked `instance` whose
  result is `Decidable …`, first fit wins, in the D9 order. That's safe
  for answers (multi-file §4.9.4). These overlap all the time
  (`Decidable.and` fits any `p && q`), and their propositions are often
  definitions that unfold into each other, so a uniqueness rule doesn't
  fit them. They're a different kind of interface: open, and
  answer-agreeing.
- **Decision procedures need the `instance` marker too** (D163):
  `instance Nat.decLessEq (m: Nat) (n: Nat): Decidable (m <= n) := …`.
  One rule for what `auto` may use. About 20 in the library (std-library.md
  §4.5); none in `aoc/src`, but and about 5 example files (**checked** by grep, 20 October) need it.
- **The name is `DecEq`, not `Eq`** (D155). `Eq` is already the
  namespace of the lemmas about `=` (`Eq.sym`, `Eq.trans`, `Eq.cong`; 762
  uses in the library, **checked**). Idris 2's interface for exactly this
  is called `DecEq`, with one method `decEq: (x1, x2: t) -> Dec (x1 = x2)`
  [I3]. Lean calls its version `DecidableEq`.

`DecEq` needs no laws: its one field returns a proof either way.

### 5.13 Operators and literals

| Syntax | `Nat`, `Int` | Other types |
|---|---|---|
| `==`, `!=`, `if h: x = y` | `DecEq` (as `Nat.decEq` today) | `DecEq` |
| `+` | unchanged | `Add.add` |
| `*` | unchanged | `Mul.mul` |
| `<`, `<=` | unchanged (`Nat.LessThan` …) | `Ord.LessThan x y` (`compare x y = Less`), `Ord.LessEq` |
| `-`, `/`, `%`, prefix `-` | unchanged | error, as today |
| `++` | `Text`, `List` | error, as today |
| `${e}` | `Show.toText` | `Show.toText` (§5.14) |
| `0`, `42` | unchanged | error, with a note: "use `Add.zero`" |

(D165.) **`Nat` and `Int` keep their own path** because their operators
are natives, are typed a whole expression at a time
(docs/syntax.md "Numbers"), and existing proofs rely on the exact terms
(`Nat.add` recursing on its first argument). Their instances use the same
functions, so a generic lemma used at `Nat` computes to a statement about
`Nat.add`: `Add.add Nat.add x y` unfolds to `Nat.add x y` (**inferred**:
the instance is a definition whose body is a record literal, and the
method is a projection, both of which evaluation unfolds).

**No generic literals** (D165): `0` in generic code would need Lean's
`OfNat` class (one instance per literal value) and default instances to
decide what `let n := 0` means [L1]. Generic code writes `Add.zero` and
`Mul.one`. Literals stay `Nat` or `Int` by today's rules.

### 5.14 `Show` and interpolation

```
interface Show (a: Type) =
  { toText: a -> Text }
```

`"${e}"` becomes `Show.toText e` (D167), for any type with a `Show`
instance: `Nat`, `Int`, `Text` (as is, no quotes), `Char`, `Bool`, lists
and tuples of those, `Maybe`, and derived instances for data types and
records (`Circle 3`, `{ x = 1, y = -2 }`). A type that wants different
text declares its own instance, which replaces the derived one (§5.11).

Today `${e}` is `e.toText` by dot notation. Keeping both would mean two
rules for one piece of syntax, so this note recommends `Show` only. The
cost: a user's `def Point.toText` is no longer used by interpolation;
they write `instance Point.show: Show Point := { toText = Point.toText }`.

### 5.15 `Functor`, `Monad`: not now

In Haskell, `Monad` exists mainly to sequence effects. Stitchwort does
that with abilities, in direct style (DESIGN.md §8). What's left is code
generic over containers (`fmap` on any `f`). Today `xs.map f` and
`m.map f` already work per type by dot notation, which covers what
programs here have needed (**inferred** from the AoC programs, which use
`List` and `Maybe` only).

`Functor (f: Type -> Type)` would also need a record in `Type 1` (its
field quantifies over types) and, without universe polymorphism, could
only hold `Type 0` containers (DESIGN.md §6, "No universe polymorphism at
first"). Possible, but not cheap. D168 recommends waiting.

---

## 6. The library's interfaces

All in `Std`, in core (D170). `DecEq`, `Ord`, `Show` are default names
(usable without an import), like `Ordering` and `Decidable` today; so are
`Add` and `Mul`.

### 6.1 `DecEq`

As in §5.12. Instances: `Nat`, `Int`, `Bool`, `Char`, `Text`, `Unit`,
`Ordering`, and `List a`, `Maybe a`, `(a, b)` given `DecEq` of their
parameters. These wrap today's procedures:

```
instance Nat.decEq': DecEq Nat := { decide = Nat.decEq }      -- name to be settled in stage 2
instance List.decEq' [auto DecEq a]: DecEq (List a) := { decide = List.decEq DecEq.decide }
```

(Stage 2 renames: `List.decEq` becomes the instance, its function-taking
form becomes a private helper.)

### 6.2 `Ord`

As in §5.1. The laws say `compare` is a total order:

- `equal`: "`Equal` means equal". So `compare` never calls two different
  values equal, and a `Map` can't confuse keys.
- `flip`: comparing the other way round gives the opposite answer
  (`Ordering.flip Less = Greater`, `Ordering.flip Equal = Equal`). It
  implies `compare x x = Equal`.
- `trans`: `Less` is transitive. With the other two, `Less`-or-`Equal`
  is too.

These are Lean's `OrientedCmp`, `TransCmp` and `LawfulEqCmp`, bundled
[L4]. A new helper `Ordering.flip` is needed.

**Helpers** in the namespace: `Ord.LessThan`, `Ord.LessEq` (propositions,
decided through `DecEq Ordering`), `Ord.max`, `Ord.min`, `Ord.leTotal`
(§7.6), and two combinators for building instances:

```
-- Order `a` by a key, given that the key tells values apart.
def Ord.byKey [auto Ord b] (key: a -> b) (inj: (x: a) -> (y: a) -> key x = key y -> x = y): Ord a

-- Pairs, first component first.
instance Pair.ord [auto Ord a] [auto Ord b]: Ord (a, b)
```

Instances: `Nat`, `Int`, `Char` (by code: `Ord.byKey Char.toNat`),
`Text` (by its characters: `Ord.byKey Text.toList`, with `List.ord`),
`Bool`, `Ordering`, `List a` (lexicographic), `Maybe a` (`Nothing`
first), `(a, b)`. The `Text` instance proves the laws of `Text.compare`,
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
`Int` for both; a user's `Point` or `Money` for `Add`. Nothing else in
the hierarchy for now (D166): no `Ring`, no subtraction interface.

They replace (§2.5): `List.sum`, `List.sumBy`, `List.product`,
`List.sumInt`, `List.sumIntBy` with three generic functions, and
`List.maximum`/`List.minimum` become generic through `Ord`.

### 6.4 `Show`

As in §5.14. No laws.

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
instance Nat.decEqInst: DecEq Nat := { decide = Nat.decEq }

instance Nat.ord: Ord Nat :=
  { compare = Nat.compare
  , equal = Nat.compareEqual        -- Nat.compare x y = Equal -> x = y
  , flip = Nat.compareFlip
  , trans = Nat.compareTrans
  }

instance Text.ord: Ord Text := Ord.byKey Text.toList Text.toListInjective
```

`eq` isn't written: the compiler fills it with `Nat.decEqInst` and
`Text`'s `DecEq` instance (§5.8).

### 7.2 Pairs and lists

```
instance Pair.decEq' [auto DecEq a] [auto DecEq b]: DecEq (a, b) :=
  { decide = (p q => Pair.decEq DecEq.decide DecEq.decide p q) }

instance List.ord [auto ord: Ord a]: Ord (List a) :=
  { compare = List.compareLex Ord.compare
  , equal = List.compareLexEqual ord.equal
  , flip = List.compareLexFlip ord.flip
  , trans = List.compareLexTrans ord.equal ord.trans
  }
```

`(1, "b") < (1, "c")`, `[[2], [1]].sort` and `"apple" < "banana"` then
work, through `Pair.ord`, `List.ord` and `Text.ord`.

### 7.3 A user's record

```
namespace Shop

type Item = { name: Text, price: Nat }
```

`Shop.Item` gets `DecEq`, `Show` and (from stage 6) `Ord` derived:
`==`, `"${item}"` (`{ name = "tea", price = 3 }`) and `items.sort`
(by `name`, then `price`) work with no more code. To order items by price
instead, declare the instance in `Shop`, which replaces the derived one:

```
instance Item.ord: Ord Item :=
  Ord.byKey (i => (i.price, i.name)) Item.byPriceInjective
```

`Item.byPriceInjective` proves that the key `(price, name)` tells items
apart. It's a few lines: equal pairs have equal components, and a record
is determined by its fields.

An instance of `Ord Item` declared in another namespace, say `Report`, is
`E-INSTANCE-ORPHAN`: "`Ord Item` must be declared in `Std` (where `Ord`
is) or `Shop` (where `Item` is)". `Report` can still define
`def Report.byPrice: Ord Item := …` and pass it by name.

### 7.4 Generic `List.sort`

```
def List.sort [auto Ord a] (xs: List a): List a := List.sortBy Ord.compare xs
```

`List.sortBy` and `List.sortWith` stay, for orderings without laws.
Today's `List.sort: List Nat -> List Nat` is this at `a := Nat`, with
`Nat.compare` in place of `Nat.leq` (the sorted result is the same list;
the theorems are restated, §7.6).

### 7.5 `Map` and `Set` (signatures for SW-113)

The ordering is part of the map's type, as in Lean's `TreeMap` [L4]
(D169). That needs one small new feature: **an `auto` parameter on a data
type**, filled in wherever the type is written, as for a function:

```
type Map (k: Type) (v: Type) [auto ord: Ord k] =
  { tree: Map.Tree k v
  , ordered: Map.Tree.Ordered ord tree       -- erased: a proof
  }

type Set (k: Type) [auto ord: Ord k] = Map k Unit [ord := ord]

def Map.empty [auto Ord k]: Map k v
def Map.insert [auto Ord k] (key: k) (value: v) (m: Map k v): Map k v
def Map.get [auto Ord k] (key: k) (m: Map k v): Maybe v
def Map.toList [auto Ord k] (m: Map k v): List (k, v)

theorem Map.getInsert [auto Ord k] (key: k) (value: v) (m: Map k v):
  (m |> Map.insert key value |> Map.get key) = Just value
```

- **Writing `Map Text Nat`** in a signature means `Map Text Nat Text.ord`:
  the compiler finds the instance, as in §5.5. Inside a generic function,
  `Map k v` uses the function's own `Ord k`.
- **At a call**, `m.insert key value` with `m: Map Text Nat Text.ord`:
  `insert`'s `Ord k` is fixed by `m`'s type (step 2 of §5.5), not
  searched. A map built with `Map.empty [ord := Text.byLength]` has type
  `Map Text Nat Text.byLength`, and passing it where `Map Text Nat` is
  expected is a type error, which says the orderings differ. So the
  `Data.Set` bug [E1] can't happen, even with named alternatives.
- **The map holds no functions**, so it's plain data: it can be `State`
  (`IsData`, DESIGN.md §8) and, later, cross the JS boundary. (Storing
  the ordering *inside* the value, as Scala's `TreeMap` does, would make
  every map contain functions.)
- The kernel sees an ordinary parameter. Only the elaborator inserts it.

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

theorem List.sortSorted [auto Ord a] (xs: List a):
  List.Sorted (x y => Ordering.isLessEq (Ord.compare x y)) (List.sort xs) :=
  List.sortBySorted Ord.compare Ord.leTotal xs
```

`ord.flip x y` proves `compare y x = Ordering.flip (compare x y)`;
`rewrite` turns the goal into `Ordering.isLessEq (Ordering.flip (compare x y)) = True`,
which the lemma proves. The theorem now holds for `Nat`, `Text`, pairs,
lists and every user type with an `Ord`.

### 7.7 Generic `sum`, and a proof with `Add`'s laws

```
def List.sum [auto Add a] (xs: List a): a := List.foldLeft Add.add Add.zero xs

def List.sumBy [auto Add b] (f: a -> b) (xs: List a): b :=
  List.foldLeft (acc x => acc + f x) Add.zero xs        -- `+` on `b`: Add.add
```

`[1, 2, 3].sum` is `6: Nat`; `[3, -5, 1].sum` is `-1: Int`;
`[p, q].sum` adds `Point`s. `List.sumInt` and `List.sumIntBy` go.

A proof using the laws, given the library lemma
`List.sumCons [auto Add a] (x: a) (xs: List a): List.sum (Cons x xs) = x + List.sum xs`
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

In the `Nil` case the goal computes to `List.sum ys = Add.zero + List.sum ys`
(`List.append Nil ys` is `ys`, and the sum of `Nil` is `Add.zero`), which
is the law `zeroAdd`, reversed. `calc` already allows `=` at any type
(docs/syntax.md "`calc`"). At `Nat` this theorem gives today's fact
about `Nat` sums, by computation (§5.13).

---

## 8. Errors

Each has a stable code and an example in `examples/reject/`.

| Code | When | Message (sketch) |
|---|---|---|
| `E-INSTANCE-NONE` | No instance for a type | "no `Ord` instance for `Shop.Item`". Notes: why none was derived ("`Ord` isn't derived for `Item`: field `tag` is a function"); where one may be declared ("in `Std` or `Shop`"); a named value of the right type in scope, if any ("`Report.byPrice` has type `Ord Item`: pass it with `[ord := Report.byPrice]`") |
| `E-INSTANCE-UNKNOWN-TYPE` | `Ord ?t` with `?t` still unknown | "can't tell which type's `Ord` to use here"; note: "annotate, e.g. `(xs: List Nat)`" |
| `E-INSTANCE-AMBIGUOUS` | Two different variables in scope fit | "two `Ord a` instances are in scope: `o1` and `o2`"; note: "pass one by name" |
| `E-INSTANCE-OVERLAP` | A second instance for the same head | "`Ord Item` already has an instance, `Item.ord` (file:line)" |
| `E-INSTANCE-ORPHAN` | Instance outside the interface's or type's namespace | as §7.3 |
| `E-INSTANCE-HEAD` | Head not a type name applied to distinct variables | "an instance must be for a type name applied to variables, like `Ord (List a)`; `Ord (List Nat)` isn't" |
| `E-INSTANCE-CONTEXT` | An instance's `auto` parameter isn't on a head variable | "`[auto Ord (List a)]`: an instance may only ask for interfaces of `a`" |
| `E-INSTANCE-REDUNDANT` | `[auto DecEq a] [auto Ord a]` | "`Ord a` already gives `DecEq a`; remove `[auto DecEq a]`" |
| `E-INSTANCE-SUPER` | An instance writes the superclass field | "`eq` is filled in by the compiler" |
| `E-INSTANCE-DEPTH` | Safety net: depth over 8 | should be unreachable with §5.2's rules |
| `E-AUTO-NONE` | Unchanged, for `Decidable` goals; for `=` it points to `DecEq` | "no way to decide `f = g`"; note: "`(Nat -> Nat)` has no `DecEq` instance" |

`E-INSTANCE-NONE` replaces today's `E-AUTO-NONE` for `==` on a type
without equality (the notes that say why carry over from `derive.rs`).

---

## 9. Namespaces, imports, hashing and caching

### 9.1 Imports don't matter

To use `Ord T`, the program mentions `T`, or has a value of type `T`
from somewhere. Either way the namespace that declares `T` is checked
before it (it's a dependency, directly or through others), and so is
`Std` (where `Ord` is). The one instance for `Ord T` is in one of those
two (§5.6). So the instance found never depends on imports, on qualified
names, or on sibling files (**inferred**). That settles the reviewer's
point 3 and multi-file Q1 for interfaces (D172). Imports only decide
which *names* can be written short: `import Ord (compare)`.

`Decidable` keeps D9's rule unchanged.

### 9.2 Where `Std`'s instances live

`Std`'s library files are checked only when a program uses something in
them (std-library.md). An instance in an unloaded file would be missed.
Stage 1 follows D58 for `Decidable`: **every `Std` instance is in core**
(D170). Later, std-library.md's index can list `(interface, head) → file`
and load on demand; uniqueness makes that index a simple map.

### 9.3 Hashing

- Which instance was found is part of the elaborated term, so it's in
  the hash of the definition that uses it, like today's decision
  procedures (DESIGN.md §11).
- An interface is a record: its hash is a record's (nominal: names
  included).
- **The `instance` marker is hashed** (D171), like `theorem` is
  (docs/core.md "Tests and content hashes"). Adding or removing the
  marker changes what others elaborate to, so the planned elaboration
  cache (DESIGN.md §11, "Source → elaborated declaration") must see it.
  With uniqueness, nothing else is needed in that cache's key: the
  instance for `(I, D)` comes from namespaces that are already
  dependencies. (DESIGN.md §11 lists "the set of registered decision
  procedures" in the key; that stays for `Decidable` only.)
- Hash stability isn't a goal. Stage 2 changes the hash of everything
  that uses `==`; the test cache just reruns.

---

## 10. At runtime: dictionaries, JavaScript, speed

- **Dictionary passing.** An instance is a record value, so it's a
  runtime argument (its type is data, DESIGN.md §6). In JS a record is a
  plain object (docs/core.md "Erasure and JS extraction"): `Nat.ord` is
  `{ compare: … }`, with `eq` included and the laws left out (erased). A
  generic call passes it; a method is a property read.
- **Natives keep working.** `Nat.ord.compare` *is* `Nat.compare`, so a
  native for `Nat.compare` in the evaluator or in JS still runs.
- **Exports.** An export's types must be concrete (DESIGN.md §12), so an
  exported function never takes an instance from JS. Instances are
  resolved inside. Nothing at the boundary changes. A `Map` export can
  come later (it's data, §7.5).
- **Speed.** One extra argument and one property read per call, in code
  that isn't fast anyway. *Later, optional:* when the instance is a known
  global, the JS generator can call the method directly (what GHC's
  `SPECIALIZE` does at a larger scale [H6]). Not proposed now.
- **Compile time.** Global lookup is by `(interface, head)`, a map, so
  faster than today's scan of every `Decidable` definition
  (`auto.rs:269-300`).

---

## 11. The kernel

Nothing changes in what the kernel checks:

| Feature | What the kernel sees |
|---|---|
| `interface` | A record data type (one constructor, projections) |
| `instance` | A definition (its body a constructor application) |
| Methods | Definitions that project a field |
| `[auto Ord a]` | A `Pi` with the auto marker, as today |
| Superclass field | A field; filled in by the elaborator |
| `Map`'s `[auto ord: Ord k]` | An ordinary data parameter |
| Laws | Proof fields, erased as today |

The one change in `crates/core` is in hashing: an `instance` flag on
definitions, hashed (D171). It doesn't affect checking.

---

## 12. Stages

Sizes are rough: Rust lines added or changed, and Stitchwort library
lines. Each stage ends with the full gate.

| # | Stage | `syntax` | `elab` | `core` | `std` (.sw) | Tests |
|---|---|---|---|---|---|---|
| 1 | **Interfaces and instances.** `interface`, `instance`, `[auto I a]` without a name, generated methods, the instance table, §5.5's lookup, the orphan, overlap, head and context checks, all `E-INSTANCE-*` errors. A test interface only; nothing in `Std` uses it yet | ~200 | ~900 | ~30 (flag, hash) | 0 | ~15 accept, ~12 reject examples; must-reject pairs for overlap, orphan, head, context |
| 2 | **`DecEq` replaces `=`'s procedures.** `DecEq` and its library instances; `==`/`if h: x = y` through it; derived `T.%decEq` becomes an instance; `decide_under` and `local_deciders` removed; `instance` marker on the remaining `Decidable` procedures (D163) | ~20 | ~400 (and ~300 removed) | 0 | ~150 | all `eqeq-*`, `if-decidable`, derive examples unchanged in behaviour; AoC programs and proofs pass (the 3 places that spell out `Nat.decEq`/`List.decEq` terms may need edits) |
| 3 | **Superclasses and `Ord`.** Superclass fields filled by the compiler, `E-INSTANCE-REDUNDANT`; `Ord` with laws; instances for `Nat`, `Int`, `Char`, `Bool`, `Ordering`, `Text`, `List`, `Maybe`, pairs; `Ord.byKey`; generic `List.sort` and §7.6's theorems; `List.maximum`/`minimum` generic | 0 | ~250 | 0 | ~700 (proofs: Opus) | `sort.sw` examples; new `ord-*.sw`; Text's laws |
| 4 | **`auto` parameters on data types** (for `Map`, D169). Unblocks SW-113 | ~30 | ~250 | 0 | 0 | accept/reject examples, including the mismatched-ordering error |
| 5 | **`Add`, `Mul`, operators.** Interfaces and instances; `+`, `*`, `<`, `<=` on other types (`numbers.rs`); generic `sum`/`sumBy`/`product`; remove `sumInt`/`sumIntBy`; restate the sum lemmas generically (§7.7) | 0 | ~300 | 0 | ~400 (moved and generalised) | `list-toolkit`, `int-*` examples; a `Point` example; AoC day 2 proofs (heavy users of sum lemmas) |
| 6 | **`Show` and interpolation; derived `Show`** | 0 | ~350 | 0 | ~100 | interpolation examples; derived text for data, records, lists |
| 7 | **Derived `Ord`** (enums and records first, then data types with fields) | 0 | ~400 | 0 | ~200 (combinator proofs) | `derive-ord-*` examples |
| later | Dot notation through instances in scope (D173); the `Std` instance index (§9.2); direct method calls in JS (§10) | | | | | |

JS: no code-generation changes are expected (records are already plain
objects). Each stage adds differential extraction tests for its generic
functions (`crates/cli/tests/extract.rs`, ~50 lines per stage).

**Order and parallel work.** 1 then 2 (2 deletes code that 1 makes
redundant). 3 and 4 can run in parallel after 2. SW-113 starts after 3
and 4. 5, 6 and 7 are independent of each other. The indexed-families
design (in progress separately) doesn't interact: an instance head may
be an indexed family applied to variables (`DecEq (Vec a n)`), and
nothing here depends on how families are checked.

---

## 13. Risks

1. **Proofs that spell out decision terms** (`Decidable.toBoolSound (Nat.decEq a 1) …`
   in `aoc/src/Aoc/Day04/Proofs/Part1.sw:125`; `List.decEq (a b => Nat.decEq a b)`
   in `Day02/Proofs/Repeated.sw:229, 290`, **checked**). After stage 2,
   `a == 1` elaborates to `DecEq.decide` of the instance, which computes
   to the same thing; the proofs should still check by computation, but
   some may need the new term written. Stage 2's oracle is the full AoC
   proof suite. A generic lemma `DecEq.sound: (x == y) = True -> x = y`
   would make such proofs shorter.
2. **Proof speed.** Generic `List.sum` at `Nat` unfolds one more layer
   (the instance and the projection). Day 2's proofs use many sum lemmas
   (`List/Sort.sw:65-320`). Measure in stage 5; if it's slow, keep
   `Nat`-specific lemmas as thin corollaries.
3. **Matching instance heads after unfolding.** A goal written with a
   definition (`IsTrue c`, which unfolds to `c = True`) may or may not
   reach `DecEq`, depending on how far unification unfolds. Today's
   `aoc/day02` keeps a special `decIsTrue` for this reason
   (multi-file §4.9.4). Stage 2 should look at the goal after unfolding
   definitions at its head, and keep a test for `IsTrue`.
4. **Deriving `Show` and `Ord` eagerly costs time per type**, as `DecEq`
   does today (1–6 ms per type, `derive.rs`). Acceptable; measure.
5. **Local instances shadowing globals** (D159) could surprise: inside
   `List.sort [ord := Nat.descending]`, every `Ord Nat` uses it. That's
   the point, and `Map`'s design (§7.5) makes it harmless for data
   structures. An optional note when a local instance shadows a global
   one could come later.
6. **Records stage 4's `HasField`** is a two-parameter interface with a
   dependency (`r` and the field name determine the type). It stays its
   own derived mechanism, as records.md §9.2 describes, not an
   `interface` (D174).

---

## 14. Decisions

Each with a recommendation. D154–D160 and D162 block stage 1 or 2; the
rest can wait for their stage.

- **D154. Laws in the interface, as proof fields** (bundled), rather than
  separate law interfaces (Lean). Orderings without laws stay plain
  function arguments (`sortBy`). **Recommend: bundled** (§5.9).
- **D155. Name of the equality interface: `DecEq`**, since `Eq` is the
  namespace of `=`'s lemmas (`Eq.sym` …). Alternative: rename those
  lemmas' namespace and call the interface `Eq`. **Recommend: `DecEq`**
  (§5.12).
- **D156. Declaration syntax**: `interface Ord (a: Type) = { … }` and
  `instance Nat.ord: Ord Nat := …`, instances always named.
  **Recommend: as written** (§5.1, §5.2).
- **D157. Asking for an instance** with the existing `auto` binder,
  name optional: `[auto Ord a]`, `[auto ord: Ord a]`. Alternatives:
  Scala's `using`, Lean's bare `[Ord a]`. **Recommend: `auto`** (§5.3).
- **D158. Coherence**: one instance per interface and type head, only in
  the interface's or the type's namespace, heads a type name applied to
  distinct variables, instance contexts only on those variables, checked
  when declared. **Recommend: yes** (§5.6).
- **D159. Alternatives and local instances**: other choices are plain
  definitions passed by name; an instance variable in scope wins over a
  global instance; two different variables in scope that fit are an
  error. **Recommend: yes** (§5.5, §5.7).
- **D160. Superclasses** as a field the compiler fills in, never written
  by the instance; asking for both an interface and its superclass is an
  error. **Recommend: yes** (§5.8).
- **D161. No default methods**; extra operations are generic functions
  in the interface's namespace. **Recommend: yes** (§5.10).
- **D162. `=` is decided only through `DecEq`**; other `Decidable` goals
  keep D9's first-fit search. **Recommend: yes** (§5.12).
- **D163. Decision procedures need the `instance` marker** to be found
  by `auto` (about 20 in the library, a few in examples). **Recommend: yes**, one rule for what
  `auto` uses (§5.12).
- **D164. Derived instances**: `DecEq` (as today's `==`), `Show`, and
  later `Ord`, each replaced by the module's own instance if it declares
  one. **Recommend: yes; `Ord` in stage 7** (§5.11).
- **D165. Operators and literals**: `+ *` on non-number types use `Add`
  and `Mul`, `< <=` use `Ord`; `Nat` and `Int` unchanged; `- / %` stay
  numbers only; no generic literals (`Add.zero`, `Mul.one`).
  **Recommend: yes** (§5.13).
- **D166. Numeric interfaces**: only `Add` (commutative) and `Mul`, no
  wider hierarchy. **Recommend: yes** (§6.3).
- **D167. Interpolation `${e}` uses `Show` only**, not dot notation's
  `.toText`. **Recommend: yes** (§5.14).
- **D168. `Functor`/`Monad` not now**: abilities cover effects, dot
  notation covers per-type `map`. **Recommend: not now** (§5.15).
- **D169. `Map`/`Set` carry their ordering in their type**, via `auto`
  parameters on data types (Lean's `TreeMap`). Alternatives: an `Ord`
  argument on every operation (Haskell's `Data.Map`; relies on
  uniqueness, and the ordering invariant can't live in the map), or the
  ordering stored in the map (not plain data, so not usable as `State`).
  **Recommend: in the type** (§7.5).
- **D170. All of `Std`'s instances live in core** for now, like D58's
  decision procedures; an index later. **Recommend: yes** (§9.2).
- **D171. The `instance` marker is part of a definition's hash.**
  **Recommend: yes** (§9.3).
- **D172. Imports and qualified names never change which instance is
  found** (multi-file Q1 doesn't arise for interfaces). **Recommend: yes**
  (§9.1).
- **D173. Dot notation through instances in scope** (`x.compare y` for
  `x: a`). **Recommend: later**, after stage 7, if generic code wants it
  (§5.4).
- **D174. Interfaces take one parameter, a `Type`**; no multi-parameter
  interfaces, output parameters or interfaces over `Type -> Type`. Records
  stage 4's `HasField` stays a special case. **Recommend: yes** (§5.1,
  §13 item 6).

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
  (not re-read for this note; cited only as the standard example of
  specialisation, **unverified** wording).
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
