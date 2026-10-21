# Proposal: interfaces

**Status:** draft 3, 20 October 2026. Stages 1 to 7 are built
([As built (stage 1)](#as-built-stage-1),
[As built (stage 2)](#as-built-stage-2),
[As built (stage 3)](#as-built-stage-3),
[As built (stage 4)](#as-built-stage-4),
[As built (stage 5)](#as-built-stage-5),
[As built (stage 6)](#as-built-stage-6),
[As built (stage 7)](#as-built-stage-7)).
Review closed and decisions D154-D174, D178-D182, D186, D187 accepted as recommended (D188, Matt, 20 October 2026).
Build decisions (21 Oct 2026, Matt deferred to Claude): D194, D196-D205 accepted as recommended; D206 (derived Show for nested self-reference) not now; D207-D209 accepted (D208's unsolved-dictionary test passed: a dictionary variable in scope turns off the direct Nat/Int lowering). Instances stay folded by name (D195, As built stage 1 item 13); folding also covers helpers such as `Ord.fromCompare`, for clearer names in messages and JS. Stage 5 raised the examples benchmark by 14.6%, mostly from the larger core checked once per session; accepted for now.
Ticket SW-4, decision D152 (Matt, 20 October 2026: write this note).
Draft 2 answered the external review of draft 1
([Changes since draft 1](#changes-since-draft-1-external-review)); draft 3
answers the focused re-review of draft 2
([Changes since draft 2](#changes-since-draft-2-re-review)).
Open questions are numbered D154 to D174, D178 to D182, and D186 to D187
([§14](#14-decisions)), each with a recommendation and the reviewer's
verdicts on drafts 1 and 2.

This note can be read without knowing the codebase. Code references were
checked at commit `5619eb6`. Claims are labelled **checked** (with a
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
| 2 | Superclass filling isn't a consistent mechanism: `Ord.byKey` has no `DecEq a` to use; literals in plain `def`s omit `eq`; a non-literal instance body has nothing to fill; replacing a field of a built record can break later fields; abstract diamonds aren't covered | Redesigned (§5.8): (a) omitted superclass fields are filled when an interface record literal is elaborated, anywhere; (b) a global instance is *checked*, never changed, against the canonical parents; (c) diamonds: the full superclass closure is searched, only definitionally equal candidates merge, otherwise ambiguity naming both paths; the superclass graph must be acyclic. `Ord.byKey` takes a `DecEq a` (named `decEq` in draft 3, D181). The narrower guarantee is stated exactly |
| 3 | The `Nat`/`Int` exception for operators makes generic and monomorphic code disagree under the same dictionary | `+ * < <=` now mean the resolved dictionary for every type (§5.13). A global instance written as a record literal is projected at elaboration time, so `Nat`/`Int` operators are expected to elaborate to today's terms, with no proof rewrites; stage 5 verifies this against the pre-stage-5 baseline by comparing hashes (wording corrected in draft 3). For `<`/`<=`, `Ord` gains its relations and their deciders as fields (D180), so `Nat`'s instance can carry `Nat.LessThan` itself. The discrepancy example is now a test |
| 4 | Resolution needs a precise algorithm: no depth limit of 8; local matching mustn't commit while testing; the whole instance signature must be restricted (`instance Item.show (prefix: Text)`); recursive prerequisites first check whether head matching solved them | §5.5 is now a numbered algorithm. Matching is one-way (never assigns the goal's unknowns); goals with unknown inputs wait. (Draft 3 adds the blocked result: see the next table.) A step budget replaces the depth limit, and running out says "stopped" (D182). §5.2 lists the complete allowed signature |
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

## Changes since draft 2 (re-review)

The re-review accepted the redesigned superclasses, uniform operators and
most clarifications, and found two remaining gaps: how `if` and `auto`
decide a relation stored in a dictionary, and resolution's sensitivity to
candidates blocked on unknowns. Every point:

| # | Re-review point | Draft 3 |
|---|---|---|
| 1 | D180 puts deciders in `Ord`, but nothing says `if x < y` uses them; deciding `Ord.LessThan [ord := o] x y` must use `o`'s own `decLessThan`, never a fresh `Ord` search; the order between this, projection, unfolding, `DecEq` and the legacy search must be fixed | New §5.16, normative (D186). The order: hypotheses (for `auto` proofs); a relation method applied to a dictionary takes its paired decider from the same dictionary; `=` as written goes to `DecEq`; then the legacy search; then unfold the head definition one step and start again. Known-instance projection runs last, on the finished declaration, so it never hides the relation from these steps. The four acceptance cases are in §5.16 and stage 5 |
| 2 | Resolution can still depend on order: a candidate can be *blocked* on another obligation (the `W`/`makeOrd` example), and two candidates can be blocked from comparing (`build ?d1` vs `build ?d2`) | §5.5 rewritten: matching and comparison have three results (match, rigid mismatch, blocked). Resolution waits while a blocked candidate or comparison could change the outcome; it never falls back to a global while a blocked local could win, and never assigns outside unknowns to make candidates agree. Rigid type parameters aren't unknowns; `?candidateOrd := ?mapOrd` doesn't count as found. The `W` example is worked through |
| 3 | "Bootstrap until declared" confuses signature collection with a dictionary being usable; `Nat.addAssoc` contains `+` and `Nat.instAdd` uses `Nat.addAssoc`; `Int` too | A fixed prelude bootstrap phase with primitive lowering for `Nat` and `Int` operators and their laws, ending when the numeric dictionaries are built and checked; signature collection stays separate (§5.13, D187) |
| 4 | Superclass filling vs deferred resolution: later fields may determine the type (`Ord ?a` fixed by `compare = Nat.compare`) | A typed unknown and an instance obligation are created for an omitted parent before later fields are checked; solved at once if possible, otherwise later; the canonical-parent check runs on the completed instance, in its original context, never using the instance as evidence for itself (§5.8) |
| 5 | D179: "ignored" should mean runtime comparison only; the four proof steps; no circular evidence (`Node (child: Tree) (h: child = child)`) | Reworded, with the four steps; evidence must not depend on the derivation in progress (§5.11) |
| 6 | "Zero proof migration" is a target until the comparison runs | Reworded as expected, verified in stage 5 against the pre-stage-5 baseline, allowing for the dependency closure of generalised definitions; representative elaborated terms are checked too (§5.13, §12; the draft 1 table row too) |
| 7 | `before`/`beforeNat` return a proposition where a `Bool` is declared; `Ord.byKey`/`Ord.fromCompare` name their dictionary `eq`, against D181; D178 should promise a source-like form, not parseable text; D182's budget should last across retries | `if x < y then True else False` (§5.13); parameters renamed `decEq` (§5.8, §6.2); `toSource` is a source-like representation (§5.14); the budget is per obligation tree and cumulative across retries (§5.5) |

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
- [As built (stage 1)](#as-built-stage-1)
- [As built (stage 2)](#as-built-stage-2)
- [As built (stage 3)](#as-built-stage-3)
- [As built (stage 4)](#as-built-stage-4)
- [As built (stage 5)](#as-built-stage-5)
- [As built (stage 6)](#as-built-stage-6)
- [As built (stage 7)](#as-built-stage-7)
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
   Matching never guesses a type, and a test that depends on something
   not yet known waits instead of deciding, so nothing depends on order,
   file layout or imports (§5.5).
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
   existing code is expected to elaborate to the same terms as today;
   stage 5 checks this by comparing hashes (§5.13). `if x < y` uses the
   decider stored with the relation, from the same dictionary (§5.16).
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
Obligations that can't be settled yet **wait**, and are retried in
rounds while any round makes progress (solving one can determine
another's type).

**Unknowns and rigid variables.** An *unknown* is a metavariable that
nothing has solved yet (`?add`, `?a`). A *rigid* variable is a parameter
or bound variable: `a` in `[a: Type]`, `ord` in `[auto ord: Ord a]`. A
rigid variable is never an unknown: `ord: Ord a` matches the goal
`Ord a` at once. An *outside* unknown, for a given test, is any unknown
the test didn't create itself: the goal's, and those inside a
candidate's type or value (such as an unknown left by another pending
obligation).

**Three results.** Testing whether a candidate `c: J U` matches a goal
`I T` gives one of (D159):

| Result | Meaning |
|---|---|
| **Match** | `J` is `I`, and `U` and `T` are made equal by solving only the test's own fresh unknowns (an instance's parameters), without assigning or needing the value of any outside unknown |
| **Mismatch** | They differ in a way no solution of the outside unknowns could change: different heads, different constructors, different rigid variables, after computing |
| **Blocked** | Whether they match depends on an outside unknown: computing `U` or `T` is stuck on one, or equating them would need to assign one |

Each test runs in an undo transaction (`crates/elab/src/undo.rs`) and is
rolled back. **Comparing two candidates** (are they the same dictionary?)
has the same three results: definitionally **equal**, rigidly
**distinct**, or **blocked** on an outside unknown. Comparison never
assigns outside unknowns to make two candidates agree.

**Steps**, for an obligation with goal `I T`:

1. **Already solved.** If the obligation's unknown has been solved by
   unification to something that isn't itself an unsolved unknown (some
   other type fixes it, as `Map`'s type fixes its ordering, §7.5), stop.
   Nothing is searched.
2. **Given by name**, `[ord := e]`: `e` is checked against `I T`.
3. **Wait if `T`'s head is an unknown.**
4. **Dictionaries in scope.** Candidates are every variable in scope of
   interface type, and every superclass path from one, through the whole
   superclass closure (`ord.eq` for `DecEq a`; diamonds, §5.8). Test
   each.
   - **If any is blocked, wait.** A blocked candidate might match later,
     and then it would win over a global instance, or make the result
     ambiguous. So resolution never falls back to a global instance while
     a blocked candidate in scope could still take precedence.
   - Otherwise, compare the candidates that match, pairwise. Merge those
     that are equal. **If a comparison is blocked, wait.** If exactly one
     remains, use it. If several rigidly distinct ones remain,
     `E-INSTANCE-AMBIGUOUS`, naming each path (`d.b.a`, `d.c.a`).
   - If none match (all mismatched), go on to step 5.
5. **The global instance.** Look up the one instance of `I` for `T`'s
   head (§5.6). Test it: blocked, wait; mismatch or no instance,
   `E-INSTANCE-NONE`. On a match, its head variables are fixed (§5.2).
   Then for each prerequisite:
   - if matching fixed it to a term that isn't an unsolved unknown (a
     head like `Map k v [ord := o]` fixes `o`), keep it: it's not
     searched again;
   - if matching only equated it with an outside unsolved unknown
     (`?candidateOrd := ?mapOrd`), that is **not** a solution: the
     prerequisite waits for `?mapOrd`'s own obligation;
   - otherwise it's a new obligation, solved from step 1.
6. **Rounds.** When a round settles nothing, every waiting obligation is
   reported: `E-INSTANCE-UNKNOWN-TYPE` if `T`'s head is still unknown
   ("can't tell which type's `Ord` to use; annotate"), otherwise
   `E-INSTANCE-STUCK`, naming the unknown that blocks a candidate.
7. **Budget.** Each obligation tree (an obligation with the prerequisites
   it creates) has a budget of instance steps (large: thousands), spent
   cumulatively across all rounds: a retry doesn't get a fresh budget.
   Termination is guaranteed by §5.2's rules, but not any fixed depth:
   `DecEq (List (List … Nat))` twelve deep is fine. Running out is
   `E-INSTANCE-BUDGET`, which says resolution was *stopped*, not that no
   instance exists (D182). The legacy `Decidable` search keeps its depth
   limit of 8 (§5.12).

**Why order can't matter** (the re-review's example). Suppose a helper
`def makeOrd [auto add: Add Nat]: Ord (W (Add.zero [add := add]))`
gave a local `o`, where `W (n: Nat)` is a data type with a global
`W.instOrd: Ord (W n)`. The declaration has two obligations: `?add: Add
Nat` (from `makeOrd`) and a goal `Ord (W 0)`; so `o: Ord (W (Add.zero
[add := ?add]))`.

- If `?add` is solved first (by `Nat.instAdd`), `o`'s type computes to
  `Ord (W 0)`, `o` matches, and wins over `W.instOrd`.
- If `Ord (W 0)` is tried first, testing `o` gets stuck computing
  `Add.zero [add := ?add]`: **blocked**, so the goal waits rather than
  taking `W.instOrd`. `?add` is then solved, and next round `o` matches.

Both orders choose `o`. Two local dictionaries `build ?d1` and
`build ?d2` work the same way: their comparison is blocked until `?d1`
and `?d2` are solved, and only then are they merged or reported as
ambiguous.

A dictionary in scope wins over a global instance. That's how Lean,
Scala and Idris behave, and it's what lets a function's caller choose:
`List.sort [ord := Nat.descending] xs` makes every `Ord Nat` inside that
call of `List.sort` use it.

There's **no backtracking among globals and no tie-break**: at most one
global instance can fit, and every test is either decided by rigid
structure or waits, so nothing depends on the order obligations or
candidates are tried in, declaration order, file order, load order or
which namespaces were checked first.

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
Draft 2 separates three things (D160); draft 3 fixes when (a) happens.

**(a) Filling, when a record is built.** When the elaborator checks a
record literal of an interface type and the literal leaves out a
superclass field, then, **before checking the later fields**, it creates
a typed unknown for that field (of the parent's type, say `DecEq ?a`)
and records an instance obligation for it in the literal's context.
Later fields' types refer to that unknown, so a law about `base.op` has
a well-defined parent term even before its value is known. The
obligation is solved at once if it can be; otherwise by §5.5's rounds,
like any other. This matters because a later field can fix the type: a
literal expected at `Ord ?a` learns `?a := Nat` from
`compare = Nat.compare`, and only then can `DecEq ?a` be resolved. This
happens for every interface record literal: in instances, in named
alternatives, in helpers. A literal may also give the field explicitly.

```
def Ord.byKey [auto decEq: DecEq a] [auto ord: Ord b] (key: a -> b)
  (inj: (x: a) -> (y: a) -> key x = key y -> x = y): Ord a :=
  { compare = (x y => Ord.compare (key x) (key y)), … }    -- `eq` filled: the parameter `decEq`
```

Here `eq` is filled with the parameter `decEq: DecEq a`, the only
`DecEq a` in scope (`ord.eq` is a `DecEq b`). The superclass *field*
keeps the name `eq`; the *parameter* follows D181's convention.

**(b) Checking, when a global instance is registered.** Once the
instance's body is completely elaborated (all its obligations solved),
for each superclass path `p` of the global instance `N: I (D vs)` (every
path through the closure, `eq`, and for deeper hierarchies `eq.…`), the
compiler resolves the parent at that type in the instance's **original
context**: its declared prerequisites in scope, and nothing else. `N`
itself is never evidence for its own check, neither as a global
instance nor as a dictionary in scope. It then checks that `N.p` is
**definitionally equal** to the parent found. It never replaces a field: a later field may depend on
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
  `Nat`). **They're omitted from runtime comparison**: the generated
  `decide` compares only the data fields. **Their equality is
  established with `DecEq.uniqueEq` in the generated correctness proof**:
  any two proofs of an equation in a type with decidable equality are
  equal (propositionally, not by computation). That's Hedberg's theorem;
  the library already proves it for `Bool` (`Bool.uniqueEq`,
  `core.sw:299`, **checked**), and stage 2 proves it generically
  (`DecEq.uniqueEq`; Agda's standard library has the same construction).
  For a value `C f1 … fn` with an eligible proof field, the generated
  `Yes` proof:
  1. compares the data fields before it and gets their equalities;
  2. proves the two proof fields equal with `DecEq.uniqueEq`, after
     transporting one along the equalities from step 1 so that both have
     the same type;
  3. transports any later fields whose types depend on earlier ones;
  4. builds the equality of the whole values from these (by `J`, as
     `derive.rs` already does for data fields).

  `Ord` handles them the same way, and `Show` leaves them out
  (`{ position = 3 }`).
- **No circular evidence.** The `DecEq` used for an eligible proof field
  must not depend on the derivation in progress. In
  `Node (child: Tree) (h: child = child)`, `h` is an equation in `Tree`,
  and using `DecEq.uniqueEq` for it would need `DecEq Tree` while
  deriving `DecEq Tree`. The first version refuses this (the field isn't
  eligible, so derivation stops, with a note); accepting it would need a
  separately justified, terminating derivation, which isn't proposed.
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
- **Relations stored in a dictionary come before any search.** Deciding
  `Ord.LessThan [ord := o] x y` uses `o`'s own decider; §5.16 gives the
  full order (D186).
- **Other propositions keep today's search** (`p && q`, `Not p`, user
  predicates, and anything §5.16's earlier steps don't settle): any
  definition marked `instance`
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
def before [auto ord: Ord a] (x: a) (y: a): Bool :=
  if x < y then True else False
def beforeNat [auto ord: Ord Nat] (x: Nat) (y: Nat): Bool :=
  if x < y then True else False

-- draft 1: `before [ord := Nat.descending] 1 2` is False (it uses `ord`),
-- but `beforeNat [ord := Nat.descending] 1 2` is True (`<` on Nat ignored `ord`).
```

(`x < y` is a proposition; `if` decides it, by §5.16.)

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
instance whose body is a record literal*, and that instance has been
validated (§5.8 (b)), the elaborator replaces the method call by the
field's term. This is done on the finished declaration, when solved
unknowns are substituted in, after `if` and `auto` have built their
decisions (§5.16). `Add.add
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

**The cost, measured and expected.** In `crates/elab/src/std` there are
464 lines using `+` or `*` and 206 using `<` or `<=`; in `aoc/src`, 442
and 206; there are 698 theorems in the two together (**checked** by
grep, 20 October). None of them has a dictionary parameter for `Nat` or
`Int` (**checked**: no `[auto …: Add|Mul|Ord …]` anywhere), so every one
of those operators resolves to the global instance and is projected to
today's term, and `if x < y` on `Nat` decides it with today's
`Nat.decLessThan` (§5.16, step 2). **No proof rewrites are expected from
operator lowering.** That's an expectation, not yet a fact: it also
depends on the decision terms `if` and `auto` build, the remaining
implicit arguments, and what earlier stages changed. **Stage 5 verifies
it against the pre-stage-5 baseline**: every definition's hash must be
unchanged, except those in the dependency closure of deliberately
generalised definitions (callers of `List.sum` and the like), which are
listed and checked by hand. Representative elaborated terms (an
addition, a comparison in an `if`, an `auto` proof of `x < y`, on `Nat`
and `Int`) are compared with today's as golden tests. Runtime cost for
unchanged code: none, since the terms and so the JS and the natives are
the same. Generic code pays one dictionary argument and one projection
per operation (§10). Compile time: one lookup per operator.

**Bootstrap: a fixed prelude phase** (D187). The prelude defines
`Nat.add` and then proves `Nat.addAssoc` *using* `+`; `Nat.instAdd`
needs `Nat.addAssoc` for its `assoc` law. So `+` in `Nat.addAssoc` can't
wait for `Nat.instAdd`. The same holds for `*`, `<`, `<=`, and for
`Int`'s operations and laws (`Int.addComm`, `Int.addAssoc`,
`Int/Int.sw:165, 229`). The rule:

- **The bootstrap phase** is a fixed, marked prefix of the prelude. It
  contains `Nat`, `Int`, `Bool`, `Ordering`, their operations, the laws
  their instances need, the interfaces `DecEq`, `Ord`, `Add`, `Mul`, and
  the instances `Nat.instDecEq`, `Int.instDecEq`, `Nat.instAdd`,
  `Nat.instMul`, `Nat.instOrd`, `Int.instAdd`, `Int.instMul`,
  `Int.instOrd` (and the `DecEq` instances `Ord`'s parents need). Today
  some of those laws live in library files (`Nat/Arith.sw`,
  `Int/Int.sw`); they move into the phase.
- **Inside the phase**, operators on `Nat` and `Int` are lowered
  primitively, to exactly the terms projection gives afterwards
  (`Nat.add`, `Nat.LessThan`, `Int.add`, `Int.LessThan`, …), and `if` on
  them uses the primitive deciders (`Nat.decLessThan`, …).
- **The phase ends** when those dictionaries are built and validated:
  bodies checked, laws included, and §5.8 (b)'s parent check passed.
  After that, every operator is elaborated uniformly (§5.13's rule), and
  primitive lowering is never used again, in the rest of the prelude, in
  library files or in programs.
- **Signature collection is separate.** §5.6 rule 4 still collects every
  instance signature up front, in the prelude too, for forward references
  and overlap checks. A collected signature doesn't make a dictionary
  usable for projection; only a validated one is.
- **A check**: a stage 5 test elaborates a sample of `Nat` and `Int`
  operators both ways, primitive and uniform, and requires identical
  terms.

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
- **`toSource`** is a **source-like representation**: `Text` in quotes
  with escapes, `Char` as `'a'`, `Int` as `-5`, records as
  `{ name = "tea" }`. It's for people reading output, not a promise that
  the text parses back to the value: proof fields are left out, names
  aren't qualified, and brackets are added only where they help reading.
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

### 5.16 Deciding a relation stored in a dictionary

`Ord` holds `LessThan` and its decider `decLessThan` (D180). Putting the
decider in the record doesn't by itself make `if x < y` use it: today's
search (§2.1) looks at definitions, not at fields of a dictionary in
scope. This section is the rule that connects them (D186).

**Relation fields.** When an interface is declared, the elaborator pairs
each field `R` whose type ends in `Prop` with a field `decR` of type
`(the same parameters) -> Decidable (R …)`, if there is one. In `Ord`
the pairs are `LessThan`/`decLessThan` and `LessEq`/`decLessEq`. Any
interface may have such pairs.

**Deciding a proposition `P`** (for `if P`, `if h: P`, `&&`, `||`,
`not`, a `Bool` expected, and an `[auto ok: P]` that has to be decided),
in this order:

1. **Hypotheses** (`auto` proof obligations only, as today): one in
   scope whose type is `P` is used, and nothing is decided.
2. **A relation from a dictionary.** If `P`, as elaborated, is a
   relation method applied to a dictionary `d`, such as
   `Ord.LessThan [ord := d] x y`, the decision is the paired decider
   applied to **the same `d`**: `Ord.decLessThan [ord := d] x y`. There's
   no new `Ord` search, which could be ambiguous or find a different
   dictionary.
3. **Equality.** If `P` as written is `x = y`, use `DecEq` (§5.12).
4. **The legacy search**: `Decidable` instances whose result fits `P`,
   first fit, D9's order (§5.12).
5. **Unfold one step.** If none of these applies, and `P`'s head is a
   definition that can unfold (`Below x y`, below), unfold it once and go
   back to step 2. Relation methods themselves are never unfolded here:
   that would lose the dictionary that step 2 needs.

**Known-instance projection comes last.** Operators produce the method
form (`Ord.LessThan [ord := Nat.instOrd] x y`), and the decision is built
in that form (`Ord.decLessThan [ord := Nat.instOrd] x y`). Projection
(§5.13) runs on the finished declaration, when solved unknowns are
substituted in, so steps 2 to 5 always see the relation and its
dictionary together. Then the proposition becomes `Nat.LessThan x y` and
the decision `Nat.decLessThan x y`: today's terms. (Before projection,
the two forms are definitionally equal, so unification and type
checking are unaffected by when it happens.) Because step 3 looks only at
`P` *as written*, `Nat.LessThan x y` is never unfolded to
`Nat.leq (Succ x) y = True` and sent to `DecEq Bool`, which would build
a different term.

**Acceptance cases** (stage 5):

| Case | Expected |
|---|---|
| Generic `before` (§5.13): `if x < y` with `[auto ord: Ord a]` | Decided by `Ord.decLessThan [ord := ord] x y` (step 2), no other `Ord` search |
| A predicate behind a definition: `def Below [auto ord: Ord a] (x: a) (y: a): Prop := x < y`, then `if Below x y` | Step 5 unfolds `Below`, step 2 uses the same `ord`'s decider |
| A named alternative with its own relation: `Nat.descending` with `LessThan = (x y => Nat.LessThan y x)` and its decider; `beforeNat [ord := Nat.descending] 1 2` | `False`, decided by `Nat.descending`'s `decLessThan` |
| A concrete `Nat` conditional: `def least (x: Nat) (y: Nat): Nat := if x < y then x else y` | Exactly today's term, with `Nat.decLessThan x y`; same hash as before stage 5 |

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
def Ord.fromCompare [auto decEq: DecEq a] (compare: a -> a -> Ordering)
  (equal: …) (flip: …) (trans: …): Ord a

-- Order `a` by a key, given that the key tells values apart.
def Ord.byKey [auto decEq: DecEq a] [auto ord: Ord b] (key: a -> b)
  (inj: (x: a) -> (y: a) -> key x = key y -> x = y): Ord a
```

`Ord.byKey` keeps the caller's `decEq` as its superclass field `eq` (draft 1 had no
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
  (it's a type parameter; the `ordered` proof is erased), and it doesn't
  affect what state may hold. State may hold pure functions, so a map of
  them is accepted as `State`; what is refused is a self-storing ability,
  an operation that stores a computation using its own ability (Landin's
  knot, `E-ABILITY`), as with any other type (D203; DESIGN.md §8's
  `IsData` is gone, abilities.md). The stage 4 tests below check both.
- The kernel sees an ordinary parameter. Only the elaborator inserts it.

**Stage 4's tests** (the reviewer's list):

| Case | Expected |
|---|---|
| A `Map Nat Nat` built with a named alternative ordering, used as `State` | Accepted |
| A map whose values are pure functions, used as `State` | Accepted: state may hold pure functions (abilities.md replaced `IsData`). An operation that stores a computation using its own ability, in a map's values, is refused (`E-ABILITY`) (D203) |
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
| `E-INSTANCE-STUCK` | A candidate or comparison is still blocked when nothing more can be solved (§5.5 step 6) | "can't tell whether `o` gives `Ord (W 0)` until `?add` is known"; note: "pass the dictionary by name, or annotate" |
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
| 1 | **Interfaces and instances.** `interface`, `instance`, `[auto I a]` without a name, generated methods, the instance table and the module rules of §5.6 (ownership, orphans, overlap, all signatures first, synonyms), the complete-signature rules of §5.2, §5.5's algorithm (three-way matching and comparison, waiting, cumulative budget), superclass filling and checking (§5.8), `E-INSTANCE-*` errors. Test interfaces only | ~250 | ~1,200 | ~30 (flag, hash) | 0 | ~20 accept, ~16 reject; must-reject pairs for overlap, orphan, synonym-orphan (`LocalNat`), head, parameter, context, ambiguity (order of locals swapped gives the same error), diamond, cycle; the `W`/`makeOrd` example of §5.5 giving `o` with the obligations in either order; two `build ?d` candidates merged once solved; a prerequisite equated with an unsolved `?mapOrd` waiting, not found; a twelve-deep `DecEq (List …)`; the `Base`/`Child` record of §5.8 |
| 2 | **`DecEq` replaces `=`'s procedures.** `DecEq` and its instances; `==`/`if h: x = y` through it; hypotheses first for proof obligations; derived `T.%instDecEq` with value parameters and equation proof fields (D179); `DecEq.uniqueEq`; `decide_under` and `local_deciders` removed; `instance` marker on the remaining `Decidable` procedures | ~20 | ~500 (and ~300 removed) | 0 | ~250 | all `eqeq-*`, `if-decidable`, derive examples unchanged in behaviour; `[auto ok: f = g]` with `h: f = g` in scope; `Dial` gets `==`; AoC programs and proofs pass (3 places spell out `Nat.decEq`/`List.decEq` terms and may need edits) |
| 3 | **`Ord`.** With its laws and relation fields; `Ord.fromCompare`, `Ord.byKey`; instances for `Nat`, `Int`, `Char`, `Bool`, `Ordering`, `Text` (bridge lemma), `List`, `Maybe`, pairs; generic `List.sort` and §7.6's theorems; `List.maximum`/`minimum` generic | 0 | ~150 | 0 | ~800 (proofs: Opus) | `sort.sw` examples; new `ord-*.sw`; `Text`'s laws |
| 4 | **`auto` parameters on data types** (for `Map`, D169). Unblocks SW-113 | ~30 | ~300 | 0 | 0 | §7.5's five cases, plus `Map Text Nat` filled by search |
| 5 | **Operators through dictionaries.** The prelude bootstrap phase (D187); `Add`, `Mul` and instances; relation deciders (§5.16, D186); `+ * < <=` resolved by §5.5 for every type, with known-instance projection; generic `sum`/`sumBy`/`product`; remove `sumInt`/`sumIntBy`; restate the sum lemmas generically (§7.7) | 0 | ~400 | 0 | ~400 (moved and generalised) | **hash oracle** against the pre-stage-5 baseline: every definition's hash unchanged outside the listed dependency closure of generalised functions; golden elaborated terms for `+`, `if x < y` and `auto` proofs of `x < y` on `Nat` and `Int`; primitive and uniform lowering identical on a sample (D187); §5.16's four cases; `before`/`beforeNat` (§5.13) agree; a `Point` with `+`; AoC day 2 proofs (heavy users of sum lemmas) |
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
8. **Waiting can turn into `E-INSTANCE-STUCK`.** §5.5 waits rather than
   guess whenever a candidate is blocked. Dictionaries in scope usually
   have rigid types (they're parameters), so this should be rare; when it
   happens, the message names the unknown and suggests passing the
   dictionary by name. Stage 1's tests include the cases that should
   *not* get stuck (a rigid `ord: Ord a`, the `W` example).
9. **Projection at the end of a declaration** (§5.16) means error
   messages during elaboration show the method form
   (`Ord.LessThan [ord := Nat.instOrd] x y`), not `x < y` or
   `Nat.LessThan x y`. The printer should show the operator form for
   both.
10. **The bootstrap phase moves lemmas into core** (D187): the laws the
    `Nat` and `Int` instances need now live in `Nat/Arith.sw` and
    `Int/Int.sw`. Core grows; std-library.md's D58 measured that kind of
    growth, and stage 5 measures it again.

## As built (stage 1)

Stage 1 is built (SW-4, 21 October 2026): the syntax, the instance table
and module rules, resolution, superclasses and the errors, with test
interfaces only. The code is `crates/elab/src/interfaces.rs` (most of it),
`auto.rs` (rounds and waiting), `records.rs` (filling superclasses in
literals), `module.rs` (checking order) and `dot.rs` (fields of a
dictionary); the kernel change is the hashed `instance` flag
(`crates/core/src/globals.rs`, `hash.rs`). Surface: docs/syntax.md
"Interfaces". Tests: `examples/accept/interfaces*.sw`, the `instance-*` and
`interface-*` rejects, `examples/projects/{accept,reject}/instance-*`, and
`crates/driver/tests/interfaces.rs` (waiting, the budget, the hashed
marker). Existing hashes are unchanged (the marker is hashed only when set),
and so is every existing example's behaviour; the one visible change is the
list of keywords in the parse error for a declaration without one.

What differs from the text above, or wasn't settled by it:

1. **§5.6 rule 4 (all signatures first) is met by checking order, not by a
   separate pass.** Instance signatures can't be elaborated before the
   module's interfaces and types, which are checked in dependency order
   with everything else. Instead, every other definition and test of the
   module is checked after each instance of the module that doesn't itself
   depend on it, and an instance after another one whose interface it
   mentions or has as a superclass (by names, before anything is checked);
   an edge that would close a cycle is left out (`Elaborator::instance_edges`).
   An instance is registered, and the overlap check made, when its signature
   is checked; it's used once its body and superclass check are done. So
   the order of declarations in a file doesn't matter
   (`interfaces-order.sw`); an instance needed by a declaration it depends
   on itself is `E-INSTANCE-NONE`, with a note saying so. Of two
   overlapping instances, the one checked second gets `E-INSTANCE-OVERLAP`.
   Stage 2, which derives instances, needs to know which hand-written ones
   a module has before deriving: the names give that (each instance item's
   interface and head type name), or deriving can follow the instances in
   the same order.
2. **Methods and projections.** The record's own projections are
   `I.%f` (hidden), and the methods `I.f` (§5.1). `d.f` on a dictionary
   `d` is the projection, by dot notation; record updates and patterns use
   the projections as for any record. An interface's methods are named in
   its namespace from the start, so `import Pretty (pretty)` works in the
   file that declares it.
3. **New error codes.** `E-INTERFACE-SHAPE`: an interface without exactly
   one parameter, of type `Type`, in `Type` (D174); or a superclass field
   that isn't its interface applied to the parameter (`base: Base a`). An
   `instance` whose type isn't an interface is `E-INSTANCE-HEAD`.
4. **Dictionaries in heads, before stage 4.** Without `auto` parameters on
   data types, the `?mapOrd` case of §5.5 step 5 is tested with a data type
   that takes a dictionary as an ordinary parameter (`type Box (k: Type)
   (o: Ordered k)`): an instance head `Pretty (Box k o)` has `o` as a head
   variable, and an argument of the head whose parameter type is an
   interface, equated by matching with an unsolved unknown, makes the
   obligation wait (`interfaces-waiting.sw`, last part). Stage 4 can keep
   this rule for its `auto` parameters.
5. **Three-way tests.** A test unifies inside an undo transaction: success
   that assigned no unknown older than the test is a match (or equal), and
   success that did is blocked. A failure is a rigid mismatch if a
   structural walk finds different type or constructor names, numbers,
   sorts or rigid variables in matching positions; otherwise it's blocked if
   either side mentions an unsolved unknown, and a mismatch if not. That's
   conservative: a failure in a non-rigid position that mentions an unknown
   waits (and may end as `E-INSTANCE-STUCK`) where a finer analysis might
   say mismatch. Both sides are first read back and evaluated again with
   solutions substituted, so a definition left folded because it was stuck
   on an unknown solved since takes its step (the `W` example needs this:
   the unifier doesn't unfold a stuck application again on its own).
6. **Global matching is by head.** Since heads are a type name applied to
   distinct variables, matching a global instance is a lookup of the goal's
   head (after unfolding); its arguments become the head variables. A goal
   whose type is stuck on an unknown (a type-level function applied to one)
   waits; one stuck on anything else, or whose type is a variable or a
   function type, is `E-INSTANCE-NONE`.
7. **Rounds.** `solve_obligations` takes the obligations in creation order,
   as before; an interface obligation that waits is retried after the rest,
   while any round solves something, and the first still waiting is
   reported. With no interfaces in a program nothing changes. Proof
   obligations are still solved immediately, in order, as before.
8. **Superclass filling "at once"** (§5.8 (a)) runs resolution on the new
   obligation and the prerequisites it makes straight away, each try in a
   transaction; whatever can't be settled stays an obligation for the
   rounds. The superclass check (b) resolves in a context of all the
   instance's parameters: its prerequisites, and its head variables, which
   are only dictionaries in the stage 4 case.
9. **Budget.** 10,000 steps per obligation tree (the obligation and the
   prerequisites it creates), one per try and one per dictionary in scope
   tested, cumulative across rounds and not refunded by undo
   (`Elaborator::instance_budget` sets it, for tests).
10. **Ambiguity names paths sorted**, so swapping the order of the
    dictionaries in scope gives the same message
    (`instance-ambiguous-swapped.sw`).
11. **Not in stage 1, as planned:** library interfaces and instances
    (none in `Std` yet; the `Std` owner rule is in place), `Decidable`
    instances (D163: `instance` with a `Decidable` result is
    `E-INSTANCE-HEAD` for now), derivation, relation fields (§5.16),
    operators (§5.13). The legacy search's `prove` called on an interface
    goal (a decision procedure with an interface `auto` parameter) records
    an obligation rather than resolving at once, so a decision run at
    compile time can't use it yet: stage 2's concern. Record field names
    are lowercase, so §6.2's `LessThan` and `LessEq` fields need records to
    allow uppercase field names, or other names, by stage 3.
12. **A `let` of a function with an `auto` parameter**, `let o := makeOrd`,
    keeps its polymorphic type, as for any bare name, so `o` isn't a
    dictionary in scope; the examples annotate it
    (`let o: Pretty (W …) := makePretty`).
13. **An instance found is inlined.** An obligation's solution is a value,
    and a definition evaluates to its body once it has its arguments, so
    `Pretty.instNat` ends up in the elaborated term as its record literal,
    not by name (as an argument-less decision procedure already does), and
    `Pretty.instList [p := …]` likewise. Meaning and checking are the same,
    and a changed instance changes its users' hashes either way; but terms
    and generated JS are bigger, and a dictionary is built at each use
    rather than shared (`examples/extract/interfaces.sw`). §9.3's "which
    instance was found is part of the term" holds through the body. Stage
    5's projection works on the literal anyway; keeping the name would need
    a way to solve a metavariable with a folded definition.

    **Resolved** (D195, 21 October): **dictionaries stay folded by name.**
    The elaborator marks every definition whose result, after its
    parameters, is an interface (instances, derived ones included, named
    alternatives like `descending`, and helpers like `Ord.fromCompare` and
    `Show.fromText`; not the generated methods or projections) with the
    core's `Def::fold` flag. Such a definition, once it has all its
    arguments, evaluates to itself, a neutral `Nat.instAdd` or
    `Pretty.instList Pretty.instNat`, instead of its body; it unfolds only
    when something takes it apart: a `case` (a projection, `ord.compare`),
    or a comparison the name can't settle (conversion and unification try
    the same dictionary's arguments first, and otherwise compare both sides
    unfolded). So a metavariable solved by resolution holds the name, with
    no new kind of solution: what it's solved with is the folded value, and
    zonking quotes it as the name. What's equal is unchanged (unfolding on
    demand is still δ-reduction), so the flag isn't hashed; programs that
    run unfold at once, as before (`docs/core.md`, "Dictionaries stay
    folded by name"). The effects:
    - **Terms** name the dictionary: `Pretty.pretty [p := Pretty.instList
      [p := Pretty.instNat]] xs`, and a head's dictionary is kept by name
      (`Map.instPretty [o := descending]`). Stage 2's `==` projection
      unfolds the dictionary it found, so `x == y` on the library's types
      is the same term as before (`Nat.decEq x y`, and `List.decEq (x y =>
      Nat.decEq x y)` on lists: the `eqeq-containers` hashes didn't move).
      Tests: `crates/driver/tests/interfaces.rs`
      (`found_instances_are_named_in_terms`,
      `a_named_dictionary_equals_its_record`).
    - **Messages**: stage 4's mismatch is now "expected `Map Nat Nat [ord :=
      Ordered.instNat]`, but this has type `Map Nat Nat [ord :=
      descending]`" (it showed both record literals, the second a 90-column
      lambda).
    - **JS** defines each dictionary once and refers to it:
      `$Main$dsortedDown = (v0) => $Main$dTree$dtoList($Main$ddescending)(…)`
      rather than the record written out twice in the function, and
      `Show.toText(Std.List.instShow(Std.Text.instShow))` rather than a
      300-character record (`examples/extract/*.js` snapshots).
    - **Hashes**: 910 definitions' hashes in the hash snapshots changed, all
      ones that pass a dictionary along rather than project from it: in the
      prelude, the ten `Ord` instances (their `eq` is now
      `Nat.instDecEq` and so on, by name) and `List.sortSortedNat`; derived
      `%instOrd`, `%compare`, `%equal`, `%flip`, `%trans`, `%unfold`,
      `%show`, `%instShow` of types whose fields use dictionaries; derived
      `%decEq` of types with equation proof fields (`DecEq.uniqueEq`'s
      dictionary); and tests and definitions that pass one
      (`List.maximum`, `Pretty.pretty`, interpolation). AoC answers and every
      example's behaviour are unchanged.
    - **Cost**: the examples benchmark goes from 555.2 M to 551.2 M steps,
      85.1 M to 84.9 M visits and 566.5 M to 563.5 M allocations (−0.7%,
      −0.3%, −0.6%); `extract-js` rises 2.6% (32,390 to 33,248 steps), since
      the extracted programs now include the dictionaries' definitions.
      Stage 5, which passes dictionaries far more often, is where it counts.

## As built (stage 2)

Stage 2 is built (SW-4, 21 October 2026): `DecEq` and its instances in
the core, `=` decided through it, derived instances with value
parameters and equation proof fields, `DecEq.uniqueEq`, the `instance`
marker on decision procedures, and `decide_under` and `local_deciders`
gone. Code: `crates/elab/src/derive.rs` (rewritten), `interfaces.rs`
(`decide_eq`), `auto.rs`, `bind.rs`, `module.rs`; the library in
`crates/elab/src/std/core.sw` (end) and `Vec/Vec.sw`. Tests:
`examples/accept/eqeq-deceq.sw`, `eqeq-proof-fields.sw`, the
`eqeq-*` rejects, `decidable-not-instance.sw`. The AoC programs and proofs
check and pass unchanged.

What differs from the text above, or wasn't settled by it:

1. **Which instances.** `DecEq` instances in the core for `Nat`, `Int`,
   `Bool`, `Char`, `Text`, `Ordering`, and `List a`, `Maybe a`, `(a, b)`
   given their elements'; `Unit` is a proposition here, so it has none. The
   function-taking procedures (`List.decEq d` and so on) stay, as what the
   instances are made of: `List.instDecEq` is
   `{ decide = List.decEq (x y => DecEq.decide x y) }`.
2. **Decision-time projection.** When the dictionary found for an equation
   is a record literal (a global instance, unfolded from its name: stage 1
   item 13) whose
   `decide` is a definition, applied or not, the decision is that field
   applied to the two sides: `x == y` on `Nat` is `Nat.decEq x y`, and on
   `List Nat` is `List.decEq (x y => Nat.decEq x y) xs ys`, exactly the
   terms the search used to build. So `==` on the library's types
   elaborates as before. A `decide` that's a lambda (`Vec`'s) isn't
   projected (the kernel can't infer the type of an applied lambda); nor is
   a dictionary in scope: those give `DecEq.decide [decEq := d] x y`. This
   is a small, early piece of §5.13's projection.
3. **Where an equation goes.** An equation as written (`x = y`, `==`,
   `!=`, `if h: x = y`, a `Bool` expected) goes straight to `DecEq`
   (§5.16 step 3). `auto`'s goals and the search's recursive goals are
   values, where "as written" is lost, so there the search runs first and an
   equation it doesn't decide goes to `DecEq` after. The procedures for `=`
   aren't instances any more, so the only ones that can fit an equation are
   those for propositions that unfold to one (`Nat.decLessThan` for
   `Nat.leq (Succ m) n = True`): §5.16's step 4 before step 5, in effect.
   `if x < y` and `auto` proofs of `x < y` are unchanged.
4. **Bootstrap.** Until the core has declared `DecEq`, the search uses every
   procedure returning `Decidable …`, as before D163, so the core's own uses
   of `==` before it still work. The core and library files are checked in
   their own order, without stage 1's instance edges: their uses of syntax
   (`if` needs `Bool.ifThenElse`, `<=` needs `Nat.LessEq`) aren't references
   the edges could see, and they're written instances-last anyway.
5. **D163 and hashes.** A definition marked `instance` whose result is
   `Decidable …` is a decision procedure: none of §5.2's and §5.6's rules
   apply, and it isn't in the instance table. Its marker **is** hashed, like
   every other instance's (D171, D198). Stage 2 first left it out, to keep
   the hashes of everything that uses `<`, `&&` or `!=` unchanged; D198
   reversed that, because the marker changes what the search may find, so
   it belongs in the hash, and no hash stability is owed (there are no
   users). The one-off change reached every definition that uses one of
   the core's marked procedures, directly or through another definition.
6. **Derived instances.** `T.%decEq: [params] -> [auto decEq: DecEq a] -> (r
   s: T …) -> Decidable (r = s)` and `instance T.%instDecEq … := { decide =
   T.%decEq }`, for data types and records alike (records no longer get
   `R.decEq`; they now get `DecEq` with parameters too). The parameters are
   bound with hole types (`[%p0: _]`), filled by unification, so value
   parameters need no printing of types. With several dictionaries they're
   named `decEqA` and so on, after the parameters.
7. **Equation proof fields** (D179). For each, a helper `T.%C%P%k:
   (params) -> (fields before) -> Prop` is generated as a core term, so the
   source can state the field's type. The `Yes` proof is: for any proofs `z`
   of the proof fields' types (the `a`s' data), `C a… = C a…[z]`, by `J`s
   along `DecEq.uniqueEq a_k z_k`; then one `J` per data field, its motive
   quantified over the proof fields (their types change with the field);
   then applied to the `b`s' proofs. Proof fields may depend on the
   parameters and the data fields before them, not on other proof fields;
   data fields still may not depend on earlier fields. The
   no-circular-evidence check (an equation in a type mentioning `T`) is
   there, but no data type can reach it today: such a field is refused by
   positivity first (`T` inside `=`). A proof field that isn't an equation,
   or one in a type without `DecEq`, stops derivation, with a note.
8. **A module's own instance replaces the derived one** by names: when `T`
   is checked, if an instance item of the module names `DecEq` as its
   interface and `T` as its head's type name, nothing is derived. A head
   written through a synonym isn't seen, and the two instances then
   overlap (`E-INSTANCE-OVERLAP`).
9. **Errors.** `==`, `!=` and `if` on a type without `DecEq` are
   `E-INSTANCE-NONE`, with derivation's note ("`==` isn't derived for `T`:
   …"), or "functions can't be compared". The note on where an instance
   could go leaves out `Std`, which a program can't add to. The error is
   placed at the condition or comparison as a whole (stage 1 placed it at
   the equation inside `x < 3 && g = h`).
10. **The library and D58.** A library file may declare instances of the
    core's interfaces for its own types: they're registered when the file
    loads, which happens before any value of the type exists, so `auto`
    never depends on what's loaded (D58's concern, for procedures). `Vec`
    has one, by `Vec.toListInjective`: `{ decide = u v => if h: Vec.toList u
    = Vec.toList v then Yes … else No … }`. Derivation for indexed families
    isn't built (it didn't fall out: the generated proofs would need the
    indices' equations too), and `Fin` has no instance yet.
11. **Hashes.** Existing hashes change only where `==`, `!=` or
    `if h: x = y` on a declared type is elaborated through its derived
    instance, where the derived procedures themselves changed, and in the
    core where `DecEq` and its instances were added; see the stage 2
    report for the list.

## As built (stage 3)

Stage 3 is built (SW-4, 21 October 2026): `Ord` with its laws and
relation fields, `Ord.fromCompare`, `Ord.byKey`, instances, generic
`List.sort`, `List.maximum` and `List.minimum`, and §7.6's theorems. The
library is at the end of `crates/elab/src/std/core.sw`, with
`List/Sort.sw` (sorting), `List/Toolkit.sw` (maximum, minimum) and
`Vec/Vec.sw` (`Vec.instOrd`). Tests: `examples/accept/ord-instances.sw`,
`ord-proofs.sw`, `sort.sw`, `examples/reject/ord-none.sw`. AoC and the
bench counts are unchanged.

What differs from the text above, or wasn't settled by it:

1. **Field names** (D200): record fields are lowercase, so the relations
   are `lessThan` and `lessEq`, their deciders `decLessThan` and
   `decLessEq`. The rest is as §6.2: `eq`, `compare`, and the laws
   `equal`, `flip`, `trans`, `lessThanOf`, `lessThanTo`, `lessEqOf`,
   `lessEqTo`. Helpers: `Ord.max`, `Ord.min`, `Ord.compareSelf`,
   `Ord.leTotal`.
2. **Instances and their laws.** `Nat` and `Int` are written out with
   today's functions and relations (`Nat.compare`, `Nat.LessThan`,
   `Nat.decLessThan`, …), so stage 5's projection can give today's terms;
   their laws are proved by recursion on both numbers (`Nat.compareSucc` is
   `rfl`), in the core, since D170 puts the instances there. `Char`,
   `Bool` and `Ordering` compare by a number (`Char.toNat`, `Bool.toNat`,
   `Ordering.index`) through `Ord.fromCompare`, not `Ord.byKey`, so that
   `Char.compare` is literally the comparison inside `Text.compare`.
   Lists use `List.compareLex`, whose laws are proved once from the
   elements' (with `Ordering.andThenTrans` for transitivity), and pairs
   and `Maybe` the same way. `Text.instOrd` uses `Text.compare` itself; the
   bridge lemma `Text.compareCharsLex` says it's `List.compareLex
   Char.compare` on the characters, which gives its laws (not proved
   before). `Vec.instOrd` is `Ord.byKey Vec.toList Vec.toListInjective`,
   in `Vec.sw` (stage 2's rule for library files' own types).
3. **Generalised definitions.** `List.sort`, `List.sortPerm`,
   `List.sortSorted`, `List.sortLength`, `List.maximum` and
   `List.minimum` now take `[auto ord: Ord a]`; `List.sortSortedNat` keeps
   the `List.Sorted Nat.leq` form. `List.sort []` and `List.maximum []`
   with nothing else to say what the elements are need an annotation
   (`([]: List Nat)`): three examples got one. Their hashes, and their
   users' (the `sort`, `list-toolkit`, `eqeq-containers` and `pipe`
   examples), changed; nothing else did.
4. **Dictionaries found during checking.** A comparison that fails now
   first finds any outstanding instance whose type is fully known, then
   compares again (`check::compare`, `Elaborator::solve_ready_instances`).
   Without it, `List.sortPerm xs (Nat.equal 3)` checked against
   `(xs.sort).occurrences … = …` failed: the proof's dictionary was still
   an unknown, and a projection stuck on it doesn't compute. Finding an
   instance whose type has no unknowns can't depend on when it's done
   (§5.5), so this doesn't change what's found. Inside the library a few
   proofs still name the dictionary (`[ord := Nat.instOrd]`) where the
   comparison is made by `rfl` or a match rather than `compare`.
5. **Not done here**, as planned: `<` and `<=` through `Ord` (stage 5),
   derived `Ord` (stage 7).

## As built (stage 4)

Stage 4 is built (SW-4, 21 October 2026): `auto` parameters on data types,
records and synonyms, with a test interface (`Ordered`) standing in for
stage 3's `Ord`. Code: `crates/elab/src/data_auto.rs` (applications of a
type, checks, the mismatch note), `check.rs` (a data type's application goes
there; trailing implicits where a type is expected), `autobind.rs`,
`derive.rs`, `lib.rs`; the parser (`crates/syntax/src/parser.rs`,
`parser/declarations.rs`); and in the core, a per-type `auto_params` list,
hashed only when one is set, and printed (`globals.rs`, `check.rs`,
`hash.rs`, `pretty.rs`). Surface: docs/syntax.md "Interfaces". Tests:
`examples/accept/data-auto.sw` (§7.5's cases, `Map Text Nat` filled by
search, a synonym, derived `==`, state), `examples/extract/data-auto.sw`,
the `data-auto-*` rejects, two tests in `crates/driver/tests/interfaces.rs`
(waiting on an unknown ordering; the hash), and a parser test. Existing
hashes and examples are unchanged.

§7.5's five cases, as tested in `data-auto.sw` and the rejects:

| Case | Result |
|---|---|
| A `Map Nat Nat` with a named alternative ordering, as `State` | Accepted ("a map as state") |
| A map whose values are functions, as `State` | See item 1: pure functions accepted; computations using the ability itself refused (`data-auto-knot.sw`, `E-ABILITY`) |
| An operation on an existing map with another `Ordered Nat` in scope | The map's ordering, from its type ("the map's own ordering") |
| A map passed where the parameter names another ordering | `E-TYPE-MISMATCH`, with a note that the dictionaries differ (`data-auto-ordering-differs.sw`) |
| `Pretty (Map k v [ord := o])` resolved for a map with `descending` | `o` kept: the instance sees `descending` ("the head's ordering is kept") |

What differs from the text above, or wasn't settled by it:

1. **There's no `IsData`.** §7.5 and its test table assume DESIGN.md §8's
   `IsData`, but abilities.md replaced it with the kernel's own checks
   (positivity, termination): state may hold pure functions, and only an
   operation storing a computation that uses its own ability (Landin's
   knot) is refused. So the second case is tested as both halves: a map of
   pure functions as `State` is accepted ("functions as state"), and an
   ability storing a map of its own computations is refused
   (`E-ABILITY`), through the map's parameters. The ordering dictionary
   (a record of functions, as a type parameter) affects neither.
2. **Surface.** `[auto ord: Ord k]` among a type's parameters, in any
   position, always named (so it can be given by name; a nameless `[auto
   Ord k]` or an implicit `[a: Type]` there is `E-PARSE`). It must ask for
   an interface: `E-DATA-AUTO` otherwise (D157's proofs, `[auto ok: p]`,
   aren't allowed on types). An interface can't have one (it has exactly
   one parameter, `E-INTERFACE-SHAPE`). Types defined together must have
   the same ones (`E-MUTUAL-PARAMETERS`). Indexed families may have them.
3. **Writing the type.** In `D args`, an `auto` parameter takes a named
   argument written in its place among the positional ones,
   `Map k v [ord := o]`; otherwise it's a new obligation, as for a
   function's `auto` argument, so §5.5 applies unchanged: step 1 when an
   existing map's type fixes it (no new rule was needed), dictionaries in
   scope, then the global instance. A named argument out of place, or naming
   no `auto` parameter, is `E-UNKNOWN-NAME`.
4. **Synonyms** take `auto` parameters as a definition does:
   `type Set (k: Type) [auto ord: Ord k] = Map k () [ord := ord]` is
   `def Set (k: Type) [auto ord: Ord k]: Type := …`. For `Set Nat` to find
   `ord`, an application where a type is expected now inserts trailing
   implicit and `auto` arguments (`check_type`); before, that was
   `E-NOT-A-TYPE`, so nothing that checked changes. Dot notation through a
   synonym needs the synonym's type: `Map.empty |> .add 2` looks in `Map`,
   so the example writes `Set.add`.
5. **Instance heads.** In an instance's signature an `auto` parameter of a
   data type must be written as a variable, `Pretty (Map k v [ord := o])`;
   left out it's `E-INSTANCE-HEAD`, saying what to write, rather than
   searched (which could only fail, or make the instance specific). Making it
   a head variable automatically would need the elaborator to add a binder,
   and wasn't needed. `o` is bound automatically: a named argument for a
   type's `auto` parameter that is an unknown lowercase name counts as a
   value argument for automatic implicits (a name of the module, like a
   named alternative `[ord := descending]`, means that declaration, with no
   warning). Matching keeps `o`, and a head argument equated with an unknown
   waits, by stage 1 item 4's rule, now tested with an `auto` parameter too.
6. **Derived `==`** writes the parameter by name in the generated
   signatures (`T %p0 [ord := %p1]`); maps compare by their fields only.
7. **Printing.** A type with `auto` parameters prints them by name,
   `Map Nat Nat [ord := …]`. But a found instance is inlined (stage 1 item
   13), and a named alternative unfolds when the type is evaluated, so the
   mismatch message shows record literals, not `Ordered.instNat` and
   `descending`; the note says it's the dictionaries that differ. The same
   happens in generated JS: where a map's type supplies the ordering, the
   dictionary is written out at each use (`examples/extract/data-auto.sw`'s
   `sortedDown`), though `descending` is still defined. Keeping the names
   would need stage 1 item 13's fix. (Since made: the message and the JS
   now name `Ordered.instNat` and `descending`.)
8. **Hash.** Which parameters are `auto` is hashed (a tag, only when one
   is), like a constructor's implicit fields: it changes how every use of
   the type elaborates. Types without them hash as before.
9. **Left for SW-113.** `Map`'s real representation (a balanced tree with
   an erased `Ordered` proof, §7.5), switching from the test interface to
   stage 3's `Ord`, `Map.instShow` (stage 6), and a JS boundary for maps
   (§10). Nothing in the elaborator should need to change for those.

## As built (stage 5)

Stage 5 is built (SW-4, 21 October 2026): `Add` and `Mul` with their
`Nat` and `Int` instances, the bootstrap phase, `+ * < <=` through
dictionaries with known-instance projection, relation deciders (§5.16),
generic `List.sum`, `List.sumBy` and `List.product`, and the sum lemmas
restated generically. Code: `crates/elab/src/numbers.rs` (operators),
`interfaces.rs` (`method_call`, relation pairs and deciders, finding ready
dictionaries), `auto.rs` and `bind.rs` (§5.16 step 2), `check.rs`,
`dot.rs` and `rewrite.rs` (dictionaries found early, below). Library: the
end of `crates/elab/src/std/core.sw`, `List/Toolkit.sw`, `List/Sort.sw`,
`Int/Int.sw`. Tests: `crates/driver/tests/operators.rs` (golden terms,
primitive against uniform lowering, §5.16's cases, a user's instance
projected), `examples/accept/operators.sw` (a `Point` with `+`, generic
`+ * <`, `before` and `beforeNat` agreeing, `descending`, `Below`),
`examples/accept/int-sum.sw`, the `operators-*` rejects. Surface:
docs/syntax.md, "Numbers" and "Interfaces".

What differs from the text above, or wasn't settled by it:

1. **The bootstrap phase** is the core up to the `Add` and `Mul`
   instances, which are now at its end, after the `Ord` instances (stage
   3). The laws they need moved into the core: `+` and `*` on `Nat`
   (`Nat.addZero` … `Nat.mulAssoc`, from `Nat/Arith.sw`; `Nat.oneMul` from
   `List/Sort.sw`), `+` on `Int` (`Int.addZero` … `Int.addAssoc`, from
   `Int/Int.sw`), and new: `*` on `Int` (`Int.oneMul`, `Int.mulOne`,
   `Int.mulAssoc`, the last by signs and sizes: `Int.mulSigned` writes a
   product as a sign, `Bool.xor` of the signs, and the product of the
   sizes). Moving a declaration doesn't change its hash. An operator on
   `Nat` or `Int` goes through its interface once that interface's
   instance for the type is valid; before, and everywhere in the core
   before them, it's the built-in operation. Operators on other types
   need `Add`, `Mul` and `Ord` all declared, so before that they're the
   old error.
2. **Projection is made when the operator is elaborated, not on the
   finished declaration**, as stage 2 item 2 did for `==`: if the
   dictionary found at once is a global instance (found by name, stage 1
   item 13) whose body is a record literal whose field is a definition,
   applied or not, the operator is that field applied to the operands
   (`Nat.add x y`, `Point.add p q`). Otherwise it stays the method,
   `Add.add [add := d] x y`: for a dictionary in scope, one not found yet,
   and a field that's a lambda (`Ord.fromCompare`'s relations: `x < y` on
   `Text` is `Ord.lessThan [Text] [Text.instOrd] x y`, the instance by
   name). A dictionary found later isn't
   projected afterwards. §5.16's point stands: a relation method applied to
   a dictionary is decided by the paired decider from the same dictionary;
   only for a projected global instance is the relation already
   `Nat.LessThan x y`, decided by today's search (`Nat.decLessThan x y`).
3. **Direct lowering after the phase.** On `Nat` and `Int`, with no
   dictionary of the operator's interface in scope (directly or as a
   superclass), §5.5 can only find the library's instance, whose fields are
   the built-in operations, so the elaborator builds the projection's term
   directly, without resolving (one scan of the context per operator). With
   a dictionary in scope it resolves, so `[auto ord: Ord Nat]` makes `<`
   that order (`beforeNat`). `Elaborator::uniform_operators` (for tests)
   always resolves; the tests compare the two on a sample and on every
   definition of the library files and the AoC project (same hashes).
   "In scope" is §5.5's own test for a candidate: a variable whose type is
   the interface applied to anything, settled or not. So a local `d: Add
   ?t` whose `?t` a later use fixes, or `let d: Add Nat := pick` whose
   value still has a dictionary to find, makes `+` resolve, wait for `?t`
   and choose `d`; it never falls back to `Nat.add`
   (`operators.rs`, `a_local_dictionary_not_yet_settled_is_used`; without
   the later use it's `E-INSTANCE-STUCK`). An `auto` argument still to be
   found isn't a candidate in §5.5 (only variables are), so it doesn't
   count. Nor does a variable whose type isn't known to be an interface
   yet (`d => …` with no annotation): §5.5 skips it too, so the two still
   agree.
4. **Relation pairs** (§5.16) are found by name: a field `r` whose type
   ends in `Prop` and a field `decR` whose type ends in `Decidable`
   (`lessThan`/`decLessThan`). The decider's type isn't compared further;
   the kernel checks the terms. Step 2 is made on the proposition as
   written (a relation method applied to a dictionary, `bind.rs`) and on
   what it computes to (a relation projection stuck on a variable, as
   `Below x y` unfolds to, `auto.rs`), before the search, for `if`, `&&`,
   `Bool` expected and `auto` alike. Step 5 needs nothing new: a definition
   like `Below` unfolds when its proposition is evaluated.
5. **Dictionaries found early.** At the end of an application (and of a
   dot-notation call, which makes its implicit arguments itself), its own
   dictionaries (its `auto` arguments, not those of the applications in its
   arguments) are found at once if their type is fully known, and an
   equation's type stuck on one is computed again; `rewrite` does the same
   for the dictionaries in its goal first. Without it, a generic lemma used
   at `Nat` (`List.sumByCons f x xs` in a `calc`, or as a `rewrite` rule)
   states its
   sides with `Add.%add ?d …` stuck on the unknown dictionary, and they
   don't compute to the `Nat` sums they're compared with (stage 3's retry in
   `check::compare` only covers comparisons made there). It can't change
   what's found, since that depends only on the type, except where
   unification could still solve the unknown: an argument of a type in the
   application's type (`Tree k [ord := ?d]`, stage 4) is left alone. The
   compare retry now also recomputes a side stuck on a dictionary found
   earlier.
6. **Obligations stay in the list.** `solve_tree` used to remove an
   obligation and put it back if it wasn't solved. `undo.rs` restores the
   list by its length, so removing one made before a transaction that was
   then undone lost it (`E-UNSOLVED`: seen as `let m := xs |> .sumBy f`
   followed by `if m != 0`). A solved obligation now stays, and is skipped
   later, as `prove_now` already did.
7. **Errors.** A literal against another type keeps its message, with a
   note to write `Add.zero` or `Mul.one` where the type has `Add`. A group
   with `-`, `/`, `%` or a prefix minus, or on a type without the
   instance an operator needs, gives the old message (`` `+` gives a `Nat`
   or an `Int` ``, `` `<` works on `Nat` and `Int` ``), with a note naming
   the missing instance. `E-INSTANCE-NONE` from an operator's own
   resolution notes which method the operator is. `<` and `<=` now work on
   `Text`, lists and the other `Ord` types, so `t < 1` with `t: Text` is a
   literal mismatch, not an operator error (`int-text-operand.sw`).
8. **The library.** `List.sum`, `List.sumBy` and `List.product` are
   generic (§7.7's definitions). Restated generically, with the laws:
   `List.sumFrom`, `List.sumCons`, `List.sumByFrom`, `List.sumByCons`,
   `List.sumByAppend`, `List.productFrom`, `List.productCons`, and new
   `List.sumAppend` (§7.7's proof, as a chain of `Eq.trans`, which checks a
   little faster than the `calc`) and `Add.addZero`. The other sum
   lemmas keep their `Nat` statements (they use `Nat` facts: `keepIf`,
   `mulDistribLeft`, `<=`, subtraction), now about `List.sumBy [add :=
   Nat.instAdd]`, and their proofs are unchanged. `List.sumInt`,
   `List.sumIntBy`, their examples and `List.sumIntFrom` are gone (no AoC
   program used them); `int-sum.sw` uses the generic functions.
9. **The hash oracle** (the prelude with every library file, and the AoC
   project, against `main` before stage 5: `hash_stability`'s ignored
   `dump` test, with `HASH_DEPS` for each definition's references): 261
   definitions changed, all in the dependency closure of the ten
   generalised definitions (`List.sum`, `sumBy`, `product`, `sumFrom`,
   `sumCons`, `sumByFrom`, `sumByCons`, `sumByAppend`, `productFrom`,
   `productCons`): 65 in the library, 196 in AoC (days 1 to 6, programs
   and proofs). None outside it; 5 removed, 40 added. Every `Nat` and `Int`
   operator, `if x < y` and `auto` proof elsewhere has its old hash, and
   the golden terms in `operators.rs` were checked against the compiler
   before stage 5. Among the examples, sum and product users changed, and
   one other definition: `ord-instances.sw`'s `test "decided"`
   (`Decidable.toBool (Ord.decLessThan "a" "b")`), whose implicit
   proposition is now computed (`Less = Less`) rather than
   `Ord.%lessThan [Text] {…} "a" "b"`: its dictionary is now found when
   `Ord.decLessThan "a" "b"` is elaborated. Same meaning, smaller term.

   **Re-run with named instances** (stage 1 item 13 resolved), against
   `main` with named instances and without stage 5: the same result. 261
   changed, every one in the closure (65 library, 196 AoC); 5 removed, 40
   added; nothing outside it. Among the examples, the same files changed as
   before, and `test "decided"` still changes, for the reason above (item
   5, not an operator): before, its implicit proposition was
   `Ord.%lessThan [Text] Text.instOrd "a" "b"` (the instance by name now,
   where it used to be its record), left as zonked because the dictionary
   was still an unknown when the proposition was computed; now the
   dictionary is found at the end of `Ord.decLessThan "a" "b"`, so the
   proposition computes to `Less = Less`. The golden terms and the
   primitive-against-uniform comparisons (sample, library, AoC) pass
   unchanged; one expectation changed, `textBefore`'s dictionary, now
   `Text.instOrd` by name rather than its record.
10. **Cost.** `cd aoc && stitchwort check`: 1.99 s before, 2.07 s after
    (best of five, +4%). In evaluation steps (`stitchwort-bench`): loading
    the core goes from 651k to 803k (+23%): 107k for the laws moved into
    it, 43k for the new ones (`Int.mulAssoc` is 19k); the `check-closed-*`
    benchmarks, which are mostly the core, are +2.5%, the rest unchanged.
    The `examples` benchmark on the same 437 files goes from 484M to 562M
    steps (+16%): each example's session pays for the core and for the
    library's sum lemmas, which cost more now. The new generic ones are
    dearer than the `Nat` ones they replace (`List.sumFrom` 9k to 28k,
    `List.sumByFrom` 12k to 34k, `List.sumAppend` is new at 34k), and
    every `Nat` sum carried the inlined `Nat.instAdd` record (stage 1 item
    13), which was elaborated and checked again at each use: `List.sum xs`
    cost 566 steps against 301 for `List.foldLeft Nat.add 0 xs`, so the
    `Nat` sum lemmas were 20% to 50% dearer. Naming the record's proof
    field (`zeroAdd = Nat.zeroAdd` for `x => rfl`) didn't help.

    **With named instances** (stage 1 item 13 resolved), measured against
    `main` with named instances and without stage 5:
    - `def s (xs: List Nat): Nat := List.sum xs`, in a session with the
      library loaded (so loading isn't counted): 71 steps before stage 5
      (when `sum` was `Nat`'s), 558 with stage 5 and inlined records,
      **233** with stage 5 and named instances; `List.foldLeft Nat.add 0
      xs` is 293. The dictionary is one name, checked once where it's
      defined.
    - The `examples` benchmark on the same 447 files: 551.2 M steps before,
      631.7 M after (+14.6%); 638.4 M with folding switched off (an
      experiment, not kept), so naming saves 1% here: the examples hardly
      use sums. Most of the rise is the core: a session's prelude goes from
      708k to 861k steps (+153k: the laws moved into the bootstrap phase
      and the new `Int` ones), paid once per example, about 68 M of the
      80 M. The `check-closed-*` benchmarks are +2.1%.
    - `cd aoc && stitchwort check`, best of five, three rounds: 2.09 to
      2.10 s before, 2.11 to 2.21 s after (+1% to +5%; the timings on this
      machine were bimodal).

## As built (stage 6)

Stage 6 is built (SW-4, 21 October 2026): `Show` with `toText` and
`toSource`, its instances, `${e}` through `Show`, and derived `Show` for
data types and records. Code: `crates/elab/src/derive_show.rs` (new,
modelled on `derive.rs`), `interfaces.rs` (`show`, the note on
`E-INSTANCE-NONE`), the parser (`interpolated_str`), and the library at the
end of `crates/elab/src/std/core.sw`, with `Vec/Vec.sw` and `Fin/Fin.sw`.
Surface: docs/syntax.md "Interfaces" and the interpolation paragraph.
Tests: `examples/accept/show.sw` (35 tests), `examples/reject/show-none.sw`,
`examples/extract/show.sw` (agrees with the reference evaluator in JS), the
existing `interpolation.sw`. AoC answers and the bench counts are unchanged.

What differs from the text above, or wasn't settled by it:

1. **Where `${e}` is decided.** The parser makes `${e}` the application
   `Std.Show.toText e` (it was the field `e.toText`), so the elaborator
   needed no new rule: `Show.toText` is the generated method with an `auto`
   dictionary, found as any other (§5.5). `x.toText` by dot notation still
   works as a function call, on the types that have a `toText` definition
   (`Nat`, `Int`, `Char`, `Text`, `Bool`, now `Ordering`); `${e}` no longer
   looks at it, so a user's `def Point.toText` needs
   `instance Point.instShow: Show Point := Show.fromText Point.toText`
   (D167). No existing example or AoC program had one.
2. **Instances.** In the core: `Nat`, `Int`, `Bool`, `Char`, `Text`,
   `Ordering`, `List a`, `Maybe a`, `(a, b)` (§6.4 lists `Unit` too, but
   `Unit` is a proposition here, so it can't be a `Show` argument).
   `Vec a n` is in `Vec/Vec.sw` (shown as a list, `[1, 2]`) and `Fin n` in
   `Fin/Fin.sw` (its number). `Text.toText`, `Char.toText` and
   `Bool.toText` moved from `Text/Text.sw` into the core, since the
   instances are made from them; their names and bodies are the same.
3. **Format.** `toText` and `toSource` are equal except for `Text` (`tea`
   against `"tea"`) and `Char` (`a` against `'a'`). Quoted text escapes `\`,
   the quote, line feed, tab and carriage return, and a `$` only when a `{`
   follows (so the result is a valid literal that doesn't interpolate).
   Lists are `[a, b]`, pairs `(a, b)` (three or more nest, as they are:
   `(1, ('c', "s"))`), `Maybe` is `Nothing` and `Just x`.
4. **Brackets.** A constructor argument is put in brackets when its
   `toSource` has a space and doesn't already start with `[`, `(`, `{`, `"`
   or `'`, or when it starts with `-`: `Just (Just 1)`, `Just (-5)`,
   `Just [1, 2]`, `Just { name = "tea", price = 3 }`. That's a test on the
   text, in `Show.arg`, because the interface has no precedence argument; a
   user's own instance that prints something with spaces and no brackets
   gets some added, which is the point.
5. **Derived `Show`.** `T.%show` and `T.%instShow` (generated source, as
   derived `DecEq`), for data types and records with data fields that are
   `T` itself (a recursive call) or have `Show`, given `[auto show: Show a]`
   for each type parameter the fields use (`showA`, … when there are
   several). Constructors are `Name f1 f2` (`Dot`, `Rect 3 4`); a record is
   `{ name = "tea", price = 3 }`, `{}` with no data fields; proof fields are
   left out. Not derived, with a note on `E-INSTANCE-NONE` saying why: a
   function field, a type field, a field whose type depends on an earlier
   one, `T` inside another type (`Node (List (Tree a))`), indexed families,
   mutual types, propositions. (`Show` for a type with `T` inside another
   type would need the instance being derived; `Vec` and `Fin` are by
   hand.) A module's own instance replaces the derived one by names, as for
   `DecEq`, and the library's types are skipped.
6. **Hashes.** Only the nine tests of `interpolation.sw` changed hashes
   (their terms now go through `Show.toText`). Everything else in the
   snapshots is added: the `Show` definitions in the prelude, and
   `T.%show`/`T.%instShow` for each declared type (so, one pair for each
   data type and record in the hash examples). No other definition's hash
   changed (the AoC programs are not in the hash snapshots; their
   answers, which `dev/t aoc` checks as printed text, are the same).
7. **Cost.** Every declared type now elaborates two more definitions when
   it's declared, as `DecEq` does (§13, risk 5); not measured separately,
   and the bench counts are unchanged.
8. **Not done here**, as planned: `Map.instShow` (SW-113), derived `Ord`
   (stage 7).

## As built (stage 7)

Stage 7 is built (SW-4, 21 October 2026): derived `Ord` for enumerations,
records and data types with fields, with value parameters and proof
fields as derived `DecEq` has them. Code: `crates/elab/src/derive_ord.rs`
(new), `derive.rs` (its field plan and its proof that equal fields give
equal values, now shared), `interfaces.rs` (`ord`, the note on
`E-INSTANCE-NONE`); the lemmas the proofs are made of are at the end of
the `Ord` part of `crates/elab/src/std/core.sw`. Surface: docs/syntax.md
"Interfaces". Tests: `examples/accept/derive-ord-enum.sw`, `-record.sw`
(§7.3's `Item`, `Dial` ordered by `position`, a list of records sorted
with `List.sort`), `-data.sw`, `-params.sw`, `-own.sw` (a module's own
instance), `examples/reject/derive-ord-none.sw`, and
`examples/extract/derive-ord.sw` (agrees with the reference evaluator in
JS). AoC answers are the same.

What differs from the text above, or wasn't settled by it:

1. **What's generated.** `T.%compare` (one equation per constructor, its
   data fields compared left to right with `Ordering.andThen`, and a last
   equation for different constructors, `Nat.compare` of their tags), its
   laws `T.%equal`, `T.%flip` and `T.%trans`, and `instance T.%instOrd :=
   Ord.fromCompare T.%compare T.%equal T.%flip T.%trans`, as source, like
   derived `DecEq` and `Show`. A field of type `T` itself is a recursive
   call (and its laws recursive calls of the laws); any other data field
   uses `Ord.compare` and `Ord`'s laws. Type parameters get `[auto ord: Ord
   a]` (`ordA`, … when several), for the same parameters derived `DecEq`
   asks `DecEq` of.
2. **Combinator proofs.** Each constructor's case of a law is one lemma
   per data field, proved once in the core: `Ordering.thenEqual` (splits
   `andThen c d = Equal`), `Ordering.thenFlip`, `Ord.thenTrans` and
   `Ordering.thenTransBy` (for a recursive field). Their comparisons are
   implicit, found from the proofs' types: written out as arguments, an
   `Ord.compare x y` left its dictionary unknown when the argument was
   compared with the lemma's type, and the comparison failed. `equal`
   rebuilds the value from the fields' equations with derived `DecEq`'s
   proof (proof fields by `DecEq.uniqueEq`), now shared
   (`derive::fields_equal`).
3. **Different constructors.** The last equation of each law covers every
   pair of different constructors, so it's checked once per pair, as
   derived `DecEq`'s `T.%differ` is: `equal` refutes `Nat.compare i j =
   Equal` by `Nat.equalFalse … rfl`, `flip` is `Nat.compareFlip` of the
   tags. `trans` uses `Ordering.byTagTrans`: transitivity of `andThen`
   with the tags first, where the rest is only needed when all three tags
   are equal, which `Ordering.notBothEqual … rfl` refutes in each case
   left. The case tree doesn't look at the third value when the first two
   differ, so that equation goes through `T.%unfold: T.%compare r s =
   Ordering.andThen (Nat.compare (T.%tag r) (T.%tag s)) (T.%compare r s)`,
   which is `rfl` in every case. An **enumeration** is just its tags:
   `T.%compare r s = Nat.compare (T.%tag r) (T.%tag s)`, `flip` and `trans`
   are `Nat`'s, and only `equal` has a case per constructor. Records and
   types with one constructor have no tags.
4. **`Ord` needs `T`'s `DecEq`** (its `eq`, found by `Ord.fromCompare`).
   So `Ord` isn't derived where `DecEq` isn't (the note gives `==`'s
   reason), nor where the module declares its own `DecEq` for `T`: that
   instance isn't checked yet when `T` is declared (it depends on `T`), so
   the note asks for an `Ord` instance as well. Otherwise the reasons are
   derived `DecEq`'s, with "has no `Ord` instance" for a data field
   (`derive-ord-none.sw`: a field whose type has its own `DecEq` and no
   `Ord`). `E-INSTANCE-NONE` for `Ord` of a function type now says
   "functions can't be ordered" (`ord-none.sw`'s snapshot gained the note).
5. **A module's own instance replaces the derived one** by names, as for
   `DecEq` and `Show`; the library's types are skipped.
6. **Hashes.** No existing hash changed. The snapshots gained the eight
   lemmas in the prelude and, for each data type and record in the hash
   examples that gets one, `T.%compare`, `T.%equal`, `T.%flip`,
   `T.%trans`, `T.%instOrd` (and `T.%unfold` with two constructors or
   more, not an enumeration).
7. **Cost** (§13, risk 5). The examples benchmark on the same 440 files,
   before and after: 497.9 M to 527.2 M steps (+5.9%), 74.6 M to 78.1 M
   visits (+4.7%), 510.6 M to 536.7 M allocations (+5.1%), 28.3 s to 30.0 s
   (+6%); peak heap unchanged. (The new examples add 28 M steps more.)

---

## 14. Decisions

Each with a recommendation and the external reviewer's verdict on draft
1. D154–D160 and D162 block stage 1 or 2; the rest can wait for their
stage. The last column is the re-review of draft 2 (only the decisions
it discussed). D175–D177 are taken by other notes.

| # | Decision | Recommendation | Reviewer (draft 1) | Re-review (draft 2) |
|---|---|---|---|---|
| D154 | **Laws in the interface**, as proof fields; orderings without laws stay plain function arguments (`sortBy`) (§5.9) | Bundled | Accept | – |
| D155 | **The equality interface is `DecEq`**, since `Eq` is `=`'s lemma namespace (§5.12) | `DecEq` | Accept | – |
| D156 | **Declarations**: `interface Ord (a: Type) = { … }`; `instance Nat.instOrd: Ord Nat := …`, always named (§5.1, §5.2) | As written | Accept | – |
| D157 | **Asking**: the `auto` binder, name optional (`[auto Ord a]`, `[auto ord: Ord a]`) (§5.3) | `auto` | Accept | – |
| D158 | **Coherence**: one instance per interface and head; ownership by declaring module; orphan rule; synonyms unfold and own nothing; heads a nominal type applied to distinct variables; complete signature = head variables + prerequisites on them; all of a module's instance signatures registered first; overlap checked when declared (§5.2, §5.6) | Yes | Accept, with the ownership, alias and whole-module rules made explicit (done) | Accept; distinguish signature collection from bootstrap availability (done, D187) |
| D159 | **Resolution and alternatives**: §5.5's algorithm (three-way matching and comparison: match, rigid mismatch, blocked; waiting whenever a blocked test could change the result; dictionaries in scope before globals; ambiguity only for rigidly distinct candidates; prerequisites fixed by matching kept; equating with an unsolved unknown isn't a solution); other choices are named alternatives passed by name (§5.5, §5.7) | Yes | Accept; specify matching and name overridable parameters (done) | Add blocked matching and blocked comparison (done, §5.5) |
| D160 | **Superclasses**: an omitted parent gets a typed unknown and an obligation before later fields are checked, solved at once or later;  checked, never replaced, when a global instance is registered; full-closure search with definitional merging and ambiguity naming paths; acyclic superclass graph; the guarantee as stated in §5.8 | Yes (redesigned) | Revise (done) | Accept; clarify deferred filling of parents (done, §5.8) |
| D161 | **No default methods**; helpers and builders (`Ord.fromCompare`) are generic functions (§5.10) | Yes | Keep deferred | – |
| D162 | **`=` is decided only through `DecEq`**; proof obligations use hypotheses first; other `Decidable` goals keep D9's first-fit search (§5.12) | Yes | Accept for decisions; keep hypotheses first (done) | Resolved |
| D163 | **Decision procedures need the `instance` marker** (§5.12) | Yes | Not commented on | – |
| D164 | **Derived instances**: `DecEq` (as today's `==`), `Show`, later `Ord`; the owner's own instance replaces the derived one; scope as D179 (§5.11) | Yes | Accept; document proof and dependent fields (done, D179) | – |
| D165 | **Operators**: `+ * < <=` mean the resolved dictionary for every type, `Nat` and `Int` included, with known-instance projection; `- / %` stay numbers only; no generic literals (§5.13) | Uniform (changed from draft 1) | Reconsider the exception; prefer uniform for `+ *`; make the `<` tradeoff explicit (done) | Accept |
| D166 | **Numeric interfaces**: only `Add` (commutative) and `Mul` (§6.3) | Yes | Keep deferred (no tower) | – |
| D167 | **`${e}` uses `Show` only** (`toText`), not dot notation (§5.14) | Yes | Not commented on | – |
| D168 | **`Functor`/`Monad` not now** (§5.15) | Not now | Keep deferred | – |
| D169 | **`Map`/`Set` carry their ordering dictionary in their type**, via `auto` parameters on data types; types differ by whole dictionary; data when keys and values are (§7.5) | In the type | Accept, with the dictionary-identity and `IsData` limits stated (done) | – |
| D170 | **All of `Std`'s instances in core** for now; an index later (§9.2) | Yes | Not commented on | – |
| D171 | **The `instance` marker is hashed**; any future elaboration cache keys on a per-module instance environment fingerprint (§9.3) | Yes | Accept with the fingerprint (done) | – |
| D172 | **Imports and qualified names never change which instance is found** (§9.1) | Yes | Accept, given the ownership rules | – |
| D173 | **Dot notation through dictionaries in scope** (`x.compare y` for `x: a`) (§5.4) | Later | Not commented on | – |
| D174 | **One type parameter**; no multi-parameter interfaces, output parameters or `Type -> Type` interfaces; `HasField` stays special (§5.1) | Yes | Keep deferred | – |
| D178 | **`Show` has two fields**, `toText` (for `${…}`) and `toSource` (a source-like representation, not promised to parse, used for elements of containers and records) (§5.14) | Yes | New (answers review 9c) | Accept; say source-like, not parseable (done) |
| D179 | **Derivation's boundary**: value parameters are allowed; proof fields that are equations in a type with `DecEq` (not the one being derived) are omitted from runtime comparison, their equality proved with `DecEq.uniqueEq` (Hedberg); other proof fields, function and type fields stop it (§5.11) | Yes | New (answers review 9b) | Accept; specify the proof steps and non-circular evidence (done) |
| D180 | **`Ord` carries `LessThan`, `LessEq` and their deciders as fields**, so `<` and `<=` can be uniform with no expected proof migration (verified in stage 5). Option B: keep `<`/`<=` built in for `Nat`/`Int` and document the discrepancy (§5.13, §6.2) | Fields (A) | New (answers review 3) | Accept the record; add the decider rule (done, D186) |
| D181 | **Names**: instances `T.instI` by convention; generated methods' and library functions' dictionary parameters named after the interface (`ord`, `decEq`, `add`, `mul`, `show`) so they can be overridden (§5.1, §5.3) | Yes | New (answers review 8) | Accept; apply to helper parameters (done) |
| D182 | **A step budget, not a depth limit**, for interface resolution; running out is "stopped", never "none". `Decidable` keeps depth 8 (§5.5) | Yes | New (answers review 4) | Accept; cumulative across retries (done) |
| D186 | **Deciding a relation**: a relation field applied to a dictionary is decided by its paired decider from the same dictionary; the order is hypotheses, dictionary relation, `DecEq` for `=` as written, legacy search, unfold one step; known-instance projection last (§5.16) | Yes | – | New (answers re-review 1) |
| D187 | **A fixed prelude bootstrap phase**: primitive lowering of `Nat` and `Int` operators until their dictionaries are built and validated; signature collection stays separate (§5.13) | Yes | – | New (answers re-review 3) |

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
