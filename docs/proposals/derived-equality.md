# Derived `==`, `<` and `${…}` for every data type (SW-3354, SW-3358)

**Status:** draft 1, 15 November 2026. Stage 2 built (SW-3370, §5.6). Open
decision: D3609 ([§7](#7-decision-for-matt)). Code read at `ae7a3b341`.
Migration cost is not counted (D2303).

**Stage 1 built (SW-3369, 15 November 2026):** the std skip is lifted for
`DecEq`, `Ord`, `Show` and `Finite`; `R.ext` for std records stays skipped.
`Files`' and `Key`'s hand-written instances and plumbing are gone, as are
`Path`'s and `Disk`'s; `Std.Builtin.UnitType` also gained a derived `Finite`.

How claims are marked: **[measured]** run today with the release CLI on the
probes in the lane's scratchpad (reproduced in §3); **[checked]** read in the
code at the place given; **[inferred]** my reasoning, not run; **[cited]**
from outside sources, with the link given (checked 15 November 2026,
SW-3387).

## 1. In plain words

**The problem.** A type declared in a program gets `==`, `<` and `${…}`
for free, but three kinds of type get none, and then a user has to write
them by hand:

- **Types that refer to each other**, as every syntax tree's do (an
  expression holds blocks, which hold statements, which hold expressions).
  The toy formatter's tree has no `==`, so its tests compare text dumps,
  and the self-hosted formatter's 94 node kinds would need a hand-written
  instance per kind (tools/toyfmt/NOTES.md, friction 1).
- **A type nested inside another type of the program**, such as the toy
  tree's `List (Spaced Statement)`: only `List`, `Option` and pairs are
  looked through.
- **The standard library's own types.** `Std.Files` spends about 60 lines
  on hand-written `==` for `FileKind`, `Entry`, `FileInfo` and `FileError`,
  with public plumbing (`FileKind.position`, `FileError.parts`, …) that
  shows in the API docs; `Key` has the same. Std types nobody wrote one
  for, such as `Terminal.Size`, simply have no `==` [measured].

There is also a cost problem: the derived `<` for a type with many
constructors is quadratic. A 94-constructor type with one field takes
**13 s** to declare, almost all of it the derived order [measured, §3].

**The change.** Keep derivation automatic, as it is today, and make it
cover all three: mutual groups, nesting through any earlier data type, and
std types outside the core. Rebuild the derived order (and the equality's
proofs) so their size grows linearly with the number of constructors.

**What it should do.** The formatters' `parse source == tree` checks work
with no extra code; Files loses ~60 lines and `Key` ~90; every std type
gets `==`, `<` and `${…}` where its fields allow; a 94-kind node type
drops from about 13 s to under a second [estimated, §5.6].

## 2. What exists today [checked]

Every data type and record a program declares gets, when it is declared
(`crates/elab/src/derive.rs`, `derive_ord.rs`, `derive_show.rs`,
`derive_finite.rs`, `derive_ext.rs`): a `DecEq` instance (`T.%instDecEq`,
built test first from `T.%same`, with proofs `T.%sameSound` and
`T.%sameComplete` and the readings `T.%sameReads`, so `(a == b) = True`
reads as `a = b`), an `Ord` instance (`Ord.fromCompare` of `T.%compare` and
its laws), a `Show`, a `Finite` for non-recursive finite types, and `R.ext`
for records. All are generated as source and elaborated like user code, so
the kernel checks them and nothing in the kernel is involved. A module's
own instance replaces the derived one. Names contain `%`, so they never
clash with the user's.

So the lemmas exist already: `==` agrees with `=` through `DecEq.sound`,
`DecEq.complete` and the readings, and `<` has `Ord`'s laws. The types this
note adds get the same instances, so no new lemma names.

**Nested types** (nested-data-types.md §10): `type Packet = | Number (value:
Nat) | Packets (items: List Packet)` can't hand `T.%same` to `List`'s
instance, since termination refuses an unapplied recursive function. So
each container `T` sits in becomes a *member* (`List Packet` is
`T.%m1%`), with its own `tag`, `same` and proofs specialised to it, all
defined together with `T`'s. Every call is then on a field matched out of
an argument, which the termination checker accepts. `Elaborator::members`
(`derive.rs:334`) finds them.

**The three limits**, each a single test in the code:

| Limit | Where | Note shown today |
|---|---|---|
| Mutual group | `data.group().len() > 1` in `field_plan_for` (`derive.rs:451`), and the same test in `derive_show.rs:115`, `derive_ext.rs:50`, `derive_finite.rs:156`, `derive_decide.rs:64` | "`Tree` is defined together with other types, which `==` isn't derived for yet" |
| Container other than `List`, `Option`, pairs | `known_container` (`derive.rs:244`) | "the field `items` of `Block` contains `Stmt` inside `Spaced`, and `==` is derived for a type inside `List`, `Option` and pairs only" |
| Std types | `self.unit.loading_prelude` in `derive_data_eq` (`derive.rs:258`), `derive_ord.rs:69`, `derive_ext.rs:48` | `E-INSTANCE-NONE`, no reason given |

Nothing in principle stops the first two: the plan and the member search
are built for one type at a time, and a group is the same construction
over several. Lean's experience bears this out (§4). The std skip has a
recorded reason only for `R.ext` (records.md: the lazy-loading index
lists names from source, so a generated `Mod.ext` would be a name the index
doesn't promise). Instances aren't looked up by name (their names have
`%`), and a value of a std type can't exist before its file is loaded, so
that reason doesn't apply to them [inferred; stage 1 confirms]. Std has 19
hand-written `DecEq` instances; 7 are core (`Nat`, `Text`, `List`, …, which
stay: they're native or come before `DecEq` exists), the rest are in
`Files` (6), `Key`, `Fin`, `Vec`, `Array`, `Map`, `Set`, `Float`,
`SafeNat`, `SafeInt` [checked by `grep`].

## 3. What it costs today [measured]

One run each, `check --no-cache`, `STITCHWORT_TIMINGS=1`, the type's row
(the type with everything derived for it), Speedwell at load 8 to 25.
Constructors are `K0 (m: Nat) | K1 | … | Kn-1`, unless said.

| Type | Elab + kernel | Steps |
|---|---|---|
| 24 constructors | 0.8 s | 10 M |
| 47 constructors | 3.1 s | 39 M |
| 94 constructors | 13.2 s | 158 M |
| 47, own `Ord` (so only `DecEq`, `Show` derived) | 0.16 s | 1.7 M |
| 94, own `Ord` and `Show` (only `DecEq`) | 0.65 s | 6.7 M |
| 94, no fields at all (an enumeration) | 2.0 s | 18 M |
| 20 constructors, each `(a: Nat) (b: Text) (c: List Node)` | 1.0 s | 13 M |
| 94 constructors, each as above | 22 s | — |

Steps grow as n²: doubling the constructors quadruples them. About 95% is
the derived `Ord`: its last equations cover every pair of different
constructors, and each law's case tree is checked once per pair (`trans`
compares three values). `DecEq` has the same shape (its `differ` lemma
already avoids most of it) but stays cheap. An enumeration uses the
cheaper tag-only path. The self-hosted formatter's 94-kind node type would
cost 13 to 22 s every time its namespace is rechecked; the check cache
hides this only when nothing in it changed.

## 4. Other languages, briefly

| Language | How | Mutual / nested types |
|---|---|---|
| Haskell | Opt-in `deriving (Eq, Ord, Show)`, or standalone deriving ([GHC user guide](https://downloads.haskell.org/ghc/latest/docs/users_guide/exts/deriving_extra.html)) | Free: no termination check |
| Rust | Opt-in `#[derive(PartialEq, Eq, PartialOrd, Ord, Debug)]`; the derived impl bounds each type parameter, `impl<T: PartialEq> PartialEq for Foo<T>` ([Rust reference, derive](https://doc.rust-lang.org/reference/attributes/derive.html)) | Free: no termination check |
| Lean 4 | Opt-in `deriving DecidableEq, BEq, Ord, Repr` ([reference manual](https://lean-lang.org/doc/reference/latest/Type-Classes/Deriving-Instances/)) | Mutual since lean4#2591 (merged 3 Oct 2023, [PR](https://github.com/leanprover/lean4/pull/2591)); a July 2024 reply said it "uses wellfounded recursion and is, thus, quite slow" ([Zulip](https://leanprover-community.github.io/archive/stream/270676-lean4/topic/DecidableEq.20and.20List.20in.20inductive.20type.html)), but the current handler uses `termination_by structural` for recursive types and a linear-size construction from 10 constructors up. Nested types: `mkDecEq` returns false, "nested inductive types are not supported yet" ([`DecEq.lean`](https://github.com/leanprover/lean4/blob/3770b3dcb8b1b3340e0252760dc68e8e61daef06/src/Lean/Elab/Deriving/DecEq.lean)); still reported in October 2025 ([Zulip](https://leanprover-community.github.io/archive/stream/113488-general/topic/DecidableEq.20for.20Tree.html)) |
| Idris 2 | No `deriving` clause; elaborator reflection with `%runElab derive`: `Show`, `Functor`, `Foldable` and `Traversable` are in `base` ([`libs/base/Deriving`](https://github.com/idris-lang/Idris2/tree/main/libs/base/Deriving)); `Eq` and `Ord` come from libraries (elab-util's `Derive.Eq`; idris2-sop's `derive "T" [Generic, Eq, Ord, DecEq]`) | Library-dependent [unverified: not tested on mutual or nested types] |
| Koka | Written by hand: the standard library defines `(==)` and `show` for `maybe`, `either` and `list` as ordinary functions taking the element's as implicit parameters ([`lib/std/core/maybe.kk`](https://github.com/koka-lang/koka/blob/ca5ccd373fb64da49fe5a765c14ac0bbe047a07c/lib/std/core/maybe.kk)); the compiler's `Syntax`, `Kind` and `Type` sources have no deriving (grep at the same commit) | – |
| Roc | `Eq` and `Hash` derived automatically for types that aren't opaque; an opaque type opts in with `implements [Eq, Hash]` ([Zulip, "Auto-Derived Abilities"](https://roc-lang.github.io/zulip-export/stream/231634-beginners/topic/.E2.9C.94.20Auto-Derived.20Abilities.html)); `Eq` is not derived for types holding functions or floats ([roc#4290](https://github.com/roc-lang/roc/pull/4290)). `Inspect` [unverified] | Automatic |
| F#, Elm, Gleam | Automatic structural equality: F# records and unions ([records](https://learn.microsoft.com/en-us/dotnet/fsharp/language-reference/records): "Like union and structure types, records have structural equality semantics"), with `[<ReferenceEquality>]`, `[<NoEquality>]` and `[<NoComparison>]` to opt out ([records](https://learn.microsoft.com/en-us/dotnet/fsharp/language-reference/records), [unions](https://learn.microsoft.com/en-us/dotnet/fsharp/language-reference/discriminated-unions)); Elm "uses structural equality on tuples, records, and user-defined union types" ([`Basics.elm`](https://github.com/elm/core/blob/1.0.5/src/Basics.elm)); Gleam "Equality is checked structurally" ([tour](https://tour.gleam.run/everything/)). F# also derives comparison [unverified: the pages fetched state it only through `comparison` constraints and the F# spec] | Automatic (F#: mutually recursive unions with `and`, [unions](https://learn.microsoft.com/en-us/dotnet/fsharp/language-reference/discriminated-unions)) |

Opt-in languages make the cost and the choice of a structural order
visible; automatic ones treat structural equality as what data means.
Stitchwort's derived instances are proved, so they can be unwanted but not
wrong, and an own instance replaces one.

## 5. The design (end state)

### 5.1 Automatic, everywhere

Every data type and record, in a program or in std outside the core, gets
`==`, `<`, `${…}` (and `Finite`, `ext` as today) when its fields allow, with
no syntax. A module's own instance replaces the derived one. `stitchwort
doc` and the API docs list a type's derived instances, so what a type
supports is visible without a `deriving` line (D3609 asks this).

### 5.2 Std

The `loading_prelude` skip becomes "the core, before the interfaces
exist", which `interfaces::dec_eq(self).is_none()` already expresses.
Hand-written instances that the derived one equals are deleted:
`Files`' five (and `FileKind.position`, `ofPosition`, `fromPosition`,
`FileError.parts`, `ofParts`, `fromParts`, `Entry.ext`, `FileInfo.ext`),
`Key`'s, and `Path.instOrd` (the derived order is the same: parts, then
relative before absolute). `Path.ext` stays as written (documented API).
`R.ext` for std records stays skipped until the index lists generated
names; a small follow-up, not needed here.

### 5.3 Mutual groups

The plan is made once for the whole group. Members are every type of the
group (sharing the group's parameters, as groups already do), then every
container found from any of their fields, as `members` finds them now.
Then, for all members at once: each one's `tag` and field projections; one
block of mutually defined tests (`Expr.%same`, `Item.%same`,
`Expr.%m1%same` for `List Item`, …); one block of mutually defined proofs;
and for each type of the group its `decide`, instance and readings. `Ord`
and `Show` follow the same plan. For the toy tree (`Expr`, `Item`,
`Statement`, `Body`):

```text
Expr.%same (Call f as) (Call g bs) = Expr.%same f g && Expr.%m1%same as bs
Expr.%m1%same [x, ..xs] [y, ..ys]  = Item.%same x y && Expr.%m1%same xs ys
Item.%same { value = e, … } { value = d, … } = Expr.%same e d && …
```

A container member is named under the group type whose field first finds
it. Records in a group get `R.ext` too (it needs no recursion).

### 5.4 Nesting through any earlier data type

`known_container` becomes: any data type of an earlier group, without
indices and not a quotient, that the kernel's positivity check already let
the type be nested in (`Spaced`, a user's `Pair3`, a std record). Its
member is built from its constructors exactly as `List`'s is. For `==`
this is always right: any two decisions of `x = y` give the same `Bool`,
so the member's structural test agrees with the container's own instance,
whatever that is. For `<` and `${…}` the member must agree with the
container's own instance, so a container whose module declared its own
`Ord` (or `Show`) gets none, with a note naming it. `Vec` and other
indexed containers stay refused.

### 5.5 Termination

Nothing new. Every call in the generated tests and proofs is on a field
matched out of an argument, of a sibling type or of a container member,
which the termination checker already accepts for groups
(examples/accept/mutual-data.sw) and for nested helpers (the toy
formatter's `itemDocs`, `dumpItems`). Recursion through `List.map` on a
field (friction 2, nested fixpoints) would let members go, but isn't
needed for this and is a separate ticket.

### 5.6 Linear cost: compare tags, then rebuild

Today `T.%compare r s` matches both arguments, and its catch-all covers the
n² − n pairs of different constructors, each checked in every law. Instead:

```text
T.%rebuild : Nat → T → T         -- rebuild k s = C_k (T.%C_k%0 d s) … for tag k
T.%eta     : (s: T) → T.%rebuild (T.%tag s) s = s        -- n cases, each rfl
T.%compare r s = Ordering.andThen (Nat.compare (T.%tag r) (T.%tag s))
                   (T.%fields r s)   -- matches r only; reads s's fields by projection
```

When the tags differ, `Nat.compare` decides and `Nat`'s laws do the work.
When they're equal, `T.%eta` turns `s` into the same constructor as `r`, so
each law is proved by matching on `r` alone: n cases, not n² (`trans`
likewise). `T.%same` is rebuilt the same way, and `T.%differ` goes. Term
size and checking time become linear [inferred]: the 94-constructor probe
should land near the enumeration's path or below, under 1 s [estimated].
Lean's `DecEq.lean` and `Ord.lean` handlers import `Lean.Meta.Constructions.CtorIdx` and
`CasesOnSameCtor`, and `mkMatchNew` compares constructor indices and then
matches the fields of two values of the same constructor; it is used from 10
constructors up (option `deriving.decEq.linear_construction_threshold`,
"avoids the quadratic code size") [cited, [`DecEq.lean`](https://github.com/leanprover/lean4/blob/3770b3dcb8b1b3340e0252760dc68e8e61daef06/src/Lean/Elab/Deriving/DecEq.lean), read].

**As built (stage 2, SW-3370).** Two changes from the sketch above. The
comparison is `if Nat.equal (T.%tag r) (T.%tag s) then T.%fields r s else
Nat.compare (T.%tag r) (T.%tag s)`, not `Ordering.andThen`: a run is
strict, so `andThen` would compare the fields of values of different
constructors. And the rebuild can't use default field values (a field's
type needn't be inhabited): `T.%view s t h` takes `h: T.%tag s = t`, and
for `t` a constructor's position builds it from projections `T.%C%k%at s
h`, whose other branches refute `h`; `T.%etaAt s t h : T.%view s t h = s`
is a `J` over `T.%eta`, n cases of `rfl`. The tags' cases are core lemmas
(`Ordering.tagsEqual`, `tagsFlip`, `tagsTrans`, `DecEq.tagsSame`). 94
constructors went from 12.3 s to 0.17 s [measured; docs/performance/log.md].

### 5.7 Hashes and checking time

New hashes for every newly derived declaration, and every derived
instance's hash changes once with §5.6. Std files grow (cached on disk
after the first check). Benchmark counts move: down for types with many
constructors, up for std files that newly derive. Not counted (D2303).

## 6. Stages

| Stage | What | Model, estimate | Unblocks |
|---|---|---|---|
| 1 | Std types derive: lift the `loading_prelude` skip for `DecEq`, `Ord`, `Show`, `Finite`; delete the hand-written instances and plumbing of §5.2; check that the lazy index and check cache find derived std instances; a test that `Terminal.Size` and `FileError` get `==` | Sonnet, 2 h | SW-3354, Files cleanup |
| 2 | Linear derived `Ord` and `DecEq` (§5.6); profile first, then rebuild; the 94-constructor probe as a test with a step budget | Opus (generates kernel terms), 4 h | The real formatter's 94 kinds |
| 3 | Mutual groups and any earlier-group container (§5.3, §5.4) for `DecEq`, `Ord`, `Show`, `R.ext`; examples: Tree/Forest, the toy tree's shape with `Spaced`, a parameterised group, a container with its own `Ord` (refused, with note); docs/syntax.md and the guide's `==` section | Opus, 6 h | SW-3358, toyfmt friction 1 |
| 4 | Toy formatter: replace dump comparisons with `==` in its tests | Sonnet, 30 min | Toyfmt stage A/D checks |

Stage 1 can run beside 2 and 3. Stage 2 goes before 3, so 3 extends the
construction that stays. About 12.5 lane hours in all [estimated].

**Risks.** Stage 1: a std type whose structural `==` isn't what its docs
promise (a quotient's raw representation, `Map.Tree`): those are internal,
and the quotients themselves stay refused. Stage 3: a group's plan fails if
any one type's fields can't be compared; then the whole group gets none,
and the note must name the type and field that stopped it.

## 7. Decision for Matt

**D3609: Keep `==`, `<` and `${…}` automatic for every data type (std
included), rather than asking users to opt in with a `deriving` line?**
[rec: yes, automatic]

- *The problem.* Today derivation is automatic for program types and
  absent for std types and for types that refer to each other. Extending
  it raises the question whether it should stay automatic or become
  opt-in, as in Haskell, Rust and Lean (`deriving (Eq, Ord, Show)`), where
  the line says what the type supports and avoids paying for unused
  instances.
- *The change.* Automatic, as now: every type that can have them gets them,
  and an own instance replaces one. The two costs of opt-out are answered
  separately: checking time by the linear rebuild (13 s to under 1 s for 94
  constructors, estimated) and visibility by listing derived instances in
  `stitchwort doc` and the API docs. The alternative is a `deriving` line on
  every type that wants them, about every data type in `aoc/`,
  `games/rogue` and std.
- *What it should do.* Nobody writes or forgets a `deriving` line, a
  newcomer's `if move == Up` just works, as it does today, and syntax trees
  and std types join in. Since every derived instance is proved, the worst
  an unwanted one can do is cost checking time, which §5.6 makes small.
