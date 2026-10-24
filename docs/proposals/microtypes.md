# Proposal: microtypes (`UserId`, `OrderId`, `Email` as distinct types over `Text`)

**Status:** draft 1, 23 October 2026. Decisions D1064 to D1070 ([§8](#8-decisions)), decided by
Matt on 23 October: D1064 (a), D1065 as recommended, D1066 **(i) only** (a plain alias; no
`js.flavor`, no brand), D1067 (built, D866), D1068 (i), D1069 (i), D1070 (i). Stages 1 to 3 (SW-380; stage 2 is D866) are built: see
[As built](#as-built-stage-1-the-js-boundary) and [stage 3](#as-built-stage-3-recipe-and-conveniences). Written against commit `09c2a4fa`. Related:
[attributes.md](attributes.md) (the closed set of `js.*` attributes),
[records.md](records.md) (records, and their planned eta rule),
[map-equality.md](map-equality.md) §13.1 and D866 (unboxing records with one run-time field),
[maps.md](maps.md), and SW-356 (maps and sets as quotients; stage 2 in progress).

Claims about Stitchwort cite files at that commit and are **[checked]** against the source, or
**[run]**: tried with `target/release/stitchwort` (built from that commit's line) or with
`tsc` 7.0.2 `--strict`. Claims about other languages are **[unverified]**: from memory, with a
link to where they can be checked, not re-read while writing this.

## Contents

0. [Summary](#0-summary)
1. [The need](#1-the-need)
2. [What exists today](#2-what-exists-today)
3. [What a microtype needs](#3-what-a-microtype-needs)
4. [How other languages do it](#4-how-other-languages-do-it)
5. [Options for Stitchwort](#5-options-for-stitchwort)
6. [Recommendation](#6-recommendation)
7. [Stages](#7-stages)
8. [Decisions](#8-decisions)
9. [Sources](#9-sources)
10. [As built (stage 1: the JS boundary)](#as-built-stage-1-the-js-boundary)
11. [As built (stage 3: recipe and conveniences)](#as-built-stage-3-recipe-and-conveniences)

## 0. Summary

A *microtype* is a tiny type that wraps one value to give it a meaning the checker enforces: a
`UserId` and an `OrderId` are both text, but passing one where the other is expected should be
an error. Stitchwort can almost do this today: a **one-field record** `type UserId = { value:
Text }` is a distinct type, and gets `==`, `<`, `${…}` and use as a `Map` key for free. What it
can't do is be *cheap* and *invisible at the JavaScript boundary*: it is a heap box in both
runtimes, and it crosses to TypeScript as `{ value: string }`, which an app that already passes
plain strings can't use.

The recommendation is to keep the one-field record as *the* way to write a microtype, and add
two things around it, neither of which changes the language's logic:

1. **A boundary attribute, `@[js.unboxed]`**, on a record with exactly one run-time field: it
   crosses as that field's JS form (`string`), under its own name in the `.d.ts`, optionally
   *flavoured* (`string & { readonly __flavor?: "UserId" }`) so TypeScript also keeps
   `UserId` and `OrderId` apart while still accepting plain strings. A `Map UserId V` then
   crosses as a plain object, like `Map Text V`.
2. **Internal unboxing (the existing, undecided D866)**: the Rust runtime and the generated JS
   represent any record with one run-time field as that field, so a `UserId` *is* a string at
   run time. This also removes the extra box SW-356 stage 2 puts around every `Map` and `Set`.

No new keyword, no change to the kernel. A `newtype` declaration form is left as a later
convenience if the record spelling turns out to be clumsy (D1070).

## 1. The need

The motivating case is a real-world TypeScript app port: a Stitchwort program, called from an
existing TypeScript app, that works on several kinds of record each identified by a string id.
Today every id is `Text`, so a function that looks up an order by its id will accept a user's
id without complaint, and the proofs about "ids are kept" or "ids are distinct" don't say
*which* ids. The app's own TypeScript already keeps its id kinds apart with *flavoured* string
types ([§4](#4-how-other-languages-do-it)), so the port is, in this one respect, less safe than
what it replaced.

Neutral examples used below:

```
type UserId = { value: Text }
type OrderId = { value: Text }
type Email = { value: Text, valid: Email.isValid value = True }
```

## 2. What exists today

### 2.1 Type synonyms: no safety

`type Grid = List (List Nat)` is `def Grid: Type := List (List Nat)`: "a transparent name,
interchangeable with what it stands for" [checked: `docs/syntax.md:237`]. So with
`type Email = Text`, a function taking `Text` accepts an `Email` and the other way round
[run: `def k: Text := h e` with `h: Text -> Text` and `e: Email` checks]. A synonym documents
intent and gets its own namespace (`Email.domain`), but the checker never tells two synonyms of
`Text` apart.

### 2.2 One-field records: distinct, but boxed

"Two record types with the same fields are different types" [checked: `docs/syntax.md:262`].
So `type UserId = { value: Text }` and `type OrderId = { value: Text }` are distinct:

```
def o: OrderId := { value = "o" }
def f (u: UserId): Text := u.value
def g: Text := f o      -- E-TYPE-MISMATCH: expected `UserId`, but this has type `OrderId`
```

[run]. Everything else a microtype wants is already derived when the record is declared:

| What | Today, for `type UserId = { value: Text }` | Evidence |
|---|---|---|
| `==`, `!=` | derived `DecEq`, comparing `value` | [checked: `docs/syntax.md:294`]; [run: `alice == ({ value = "u1" }: UserId)`] |
| `<`, sorting | derived `Ord`, by `value` (so the same order as `Text`) | [checked: `docs/syntax.md:462`]; [run: `alice < bob`] |
| `${u}` | derived `Show`, but it prints `{ value = "u1" }`, not `u1` | [checked: `docs/syntax.md:464`]; [run] |
| `Map UserId V` key | works inside Stitchwort (needs `Ord`, derived) | [run: `Map.get alice scores == Some 3`] |
| Construction | `{ value = t }`, which needs a known expected type | [checked: `docs/syntax.md:288`] |
| Unwrapping | `u.value` | |
| Proofs: projection | `({ value = t }: UserId).value = t` is `rfl` | [run] |
| Proofs: rebuild | `{ value = u.value } = u` is **not** `rfl` (no eta for records yet); it's `UserId.ext { value = u.value } u rfl` | [run]; [checked: `docs/syntax.md:295`, `docs/proposals/records.md:716-720`] |
| Invariant | a proof field, `valid: Email.isValid value = True`, erased at run time and checked on JS input | [checked: `docs/core.md:104`, `:204`] |

Two gaps inside Stitchwort: the `Show` output is the record's, and a `Show` that prints just the
text is a one-line instance, as the library writes for `SafeNat`
[checked: `crates/elab/src/std/Int/Safe.sw:72`]:

```
instance UserId.instShow: Show UserId := Show.fromText (u => u.value)
```

### 2.3 Run-time cost

- **Rust runtime** (`stitchwort run`): any constructor with at least one run-time field is
  `Value::Data(tag, Fields(Rc<[Value]>))`, a heap cell [checked: `crates/rt/src/value.rs:39-40`],
  and a record is lowered like any constructor, keeping its non-erased fields
  [checked: `crates/rt/src/lower.rs:814-821`]. A `UserId` is one cell holding the `Text`.
- **Generated JS**: "a record is `{ …fields }`, with no tag" [checked: `docs/core.md:437`].
  [run] `export def wrap (t: Text): UserId := { value = t }` compiles to
  `const $Main$dwrap = (v0) => ({ value: v0 });`, and the derived `==` reads `v0.value` and
  `v1.value` before comparing the strings. One object per id, and one property read per use.
- Proof fields cost nothing in either ([checked: `docs/core.md:204`, "A record carrying
  `ok = …` costs nothing at run time"]), so `Email` with its `valid` field is the same single box.

map-equality.md already measured this for `Map` and wrote it down as D866: "single-field
records are boxed today in both the Rust runtime and JS", with a checklist for unboxing them
[checked: `docs/proposals/map-equality.md:1409-1440`, `:1903-1905`]. D866 was decided as
"not part of that design's stages", so it is still open.

### 2.4 At the JavaScript boundary

A record "is a plain object with its fields as keys" [checked: `docs/syntax.md:297`]. [run]:

```ts
export type UserId = { readonly value: string };
export declare function wrap(t: string): UserId;
export declare function countBy(ids: readonly UserId[]): { [k: string]: bigint };
```

So an app holding the string `"u1"` must write `{ value: "u1" }` to call in, and unwrap every id
coming out. And a `Map UserId V` can't be exported at all: "only maps from `Text` cross, as
plain objects" [checked: `crates/js/src/lib.rs:336-343`; run: `E-EXPORT` on
`export def keyed (m: Map UserId Nat): Nat`].

There is one precedent for a one-field record that crosses as its bare value: the library's
`SafeNat` and `SafeInt`, records `{ value: Nat, fits: … }` that cross as a JS `number`
[checked: `docs/syntax.md:299-317`]. But that is a special codec for those exact declarations,
recognised by content hash ("A program's own record called `SafeNat` is an ordinary record"
[checked: `docs/syntax.md:317`; `crates/js/src/lib.rs:2967-2972`]), not something a program can
ask for.

### 2.5 Attributes

The `js.*` attributes are a closed set [checked: `crates/elab/src/attributes.rs:55-87`]:
`js.tag`, `js.enum`, `js.name`, `js.optional`. None applies to a record type: the code has a
`Place::Record` "no tag, so nothing yet applies to it" [checked:
`crates/elab/src/attributes.rs:94-95`, `:150-168`]. And by design an attribute never changes
anything inside Stitchwort: "Patterns, field access, `show`, `==` and proofs use the Stitchwort
names, and attributes aren't part of content hashes" [checked: `docs/syntax.md:430`;
`crates/elab/src/attributes.rs:8-11`]. attributes.md listed ReScript's `@unboxed` as a non-goal
for *unions* [checked: `docs/proposals/attributes.md:263`]; a single-field record is a much
simpler case (no branch to choose).

### 2.6 A library pattern that works today

A phantom tag also works with no language change [run]:

```
type Tagged (tag: Type) (a: Type) = { value: a }
type UserTag = | MkUserTag
type UserId = Tagged UserTag Text
```

It is distinct from `Tagged OrderTag Text`, and `u.value` works through the synonym. But it is
still boxed, crosses as `Tagged<UserTag, string>` (`{ readonly value: a }`, where TypeScript
ignores the unused `tag`, so the two kinds are interchangeable there) [run], and every
`Tagged` shares one instance per interface: an instance head must be the type name applied to
distinct variables [checked: `docs/syntax.md:470-471`], so `UserId` can't have its own `Show`.

## 3. What a microtype needs

| Need | Today (one-field record) |
|---|---|
| N1. Distinct when checking: `OrderId` is not a `UserId`, and neither is `Text` | **yes** |
| N2. No run-time cost: a `UserId` is a string at run time, in both runtimes | no: one box (§2.3) |
| N3. Crosses to TypeScript as the underlying type, `string`, not `{ value: string }` | no (§2.4) |
| N4. A TypeScript form that keeps kinds apart *and* accepts the app's existing plain strings | no |
| N5. Derived `==`, `<`, `${…}` | yes; `${…}` prints the record form |
| N6. A `Map` key, inside and across the boundary | inside yes; across no |
| N7. Easy to build and take apart | `{ value = t }` (needs a known type), `u.value` |
| N8. Proofs can see through it when wanted | projection by `rfl`; rebuilding by `T.ext` |
| N9. Optional invariant (`Email` must be valid), checked on JS input | yes, as a proof field |

**For N3/N4, the TypeScript side has three shapes** [run, `tsc` 7.0.2 `--strict`]:

| Generated type | App passes a plain `string` in | App gets a `string` out | Another kind (`OrderId`) in |
|---|---|---|---|
| plain: `type UserId = string` | accepted | yes | accepted (no protection) |
| branded: `string & { readonly __brand: "UserId" }` | **refused** (`TS2345`), the app must cast | yes (a brand is a `string`) | refused |
| flavoured: `string & { readonly __flavor?: "UserId" }` | accepted | yes | refused (`TS2345`) |

The brand's property is required, so nothing but a cast produces one; the flavour's is optional,
so a plain string is one, but two flavours with different values clash. A branded value is
also accepted where a flavour is expected [run]. **For an app that already passes raw strings,
the flavour is the one that adds safety without forcing casts.** There is one catch: TypeScript
compares by property name, so the generated flavour only keeps an app's *own* flavoured kinds
apart if it uses the same property name. With a different name, every kind passes, both ways,
silently [run: an app's `string & { _kind?: "OrderId" }` is accepted where the generated
`string & { __flavor?: "UserId" }` is expected]; with the same name, the app's `UserId` is
accepted and its `OrderId` refused, in both directions [run]. So the property name should be the
program's choice. Nothing at run time can check a brand or a flavour (they don't exist at run
time), so decoding checks only that the value is a string (and any proof field's validator).

## 4. How other languages do it

| System | Form | Distinct? | Run-time cost | Deriving | Where it gets out |
|---|---|---|---|---|---|
| Haskell | `newtype UserId = UserId Text` | yes | none: guaranteed erased [Haskell 2010 §4.2.3] | `deriving (Eq, Ord, Show)`; `deriving newtype` reuses `Text`'s instances | `coerce` turns `[UserId]` into `[Text]` for free, guarded by *roles* [Breitner et al. 2014] |
| Rust | tuple struct `struct UserId(String);` | yes | none (same layout); `#[repr(transparent)]` *guarantees* the layout for FFI [RFC 1758] | `#[derive(PartialEq, Eq, Ord, Hash, Debug)]` | `.0`; serde's `#[serde(transparent)]` serialises as the inner value |
| Scala 3 | `opaque type UserId = String` | outside its defining scope only; inside, it *is* `String` | none: erased to `String` [Scala 3 reference, "Opaque Type Aliases"] | write `given`s by hand | the defining object's functions |
| F# | units of measure (`float<m>`), only on numeric types, erased; or a single-case union `type UserId = UserId of string` | yes | units: none; union: a box unless `[<Struct>]` [F# docs] | structural equality and comparison are automatic | pattern `(UserId s)` |
| TypeScript | brand or flavour on an intersection (§3) | only by the phantom property | none | n/a | a cast, or none (flavour) |
| Unison | `unique type UserId = UserId Text` | yes: a unique type gets a fresh identity even with the same shape; `structural type` doesn't [Unison docs] | a box | automatic | pattern |
| Lean 4 | `structure UserId where val : String deriving DecidableEq, Ord, Hashable, Repr` | yes | none: the compiler represents a structure with one relevant field as that field [Lean FFI docs] | `deriving` | `.val`; proofs use `UserId.ext`/`congrArg` |
| ReScript | `@unboxed type userId = UserId(string)` (also on one-field records) | yes | none: compiled to the bare value [ReScript docs]; OCaml's `[@@unboxed]` is the same idea [OCaml manual] | n/a | pattern |

What to take from it:

- **Everyone separates "distinct type" from "how it's stored".** Rust and Lean use their
  ordinary single-field struct and promise (or are allowed) to store it unboxed; ReScript and
  OCaml ask for it with an attribute; Haskell made it a separate keyword because its `data` is
  lazy and can't be unboxed in general. Stitchwort's records are strict, so it is in the Rust and
  Lean position: no new keyword is *needed* for N1 and N2.
- **The boundary form is a separate choice again**: serde's `transparent` and ReScript's
  `@unboxed` are attributes on the type, exactly what Stitchwort's `js.*` attributes are.
- **Lean is the closest relative** (dependent types, strict, structures, a kernel with
  structure eta): its answer is "write a structure, derive, and let the compiler unbox it".
- **Scala's opaque types** give "transparent inside, opaque outside" at the price of a scope
  rule in the type checker; §5 (b2) explains why that is costly here.
- **Haskell's `coerce`** (free `List UserId -> List Text`) needs roles in the type system; it is
  out of scope, and `xs.map (u => u.value)` is the price (D1069 notes it).

## 5. Options for Stitchwort

### (a) One-field records, an `@[js.unboxed]` attribute, and internal unboxing

```
@[js.unboxed]
type UserId = { value: Text }

@[js.unboxed, js.flavor "__flavor"]
type OrderId = { value: Text }

@[js.unboxed]
type Email = {
  value: Text,
  valid: Email.isValid value = True
}
```

```ts
export type UserId = string;
export type OrderId = string & { readonly __flavor?: "OrderId" };
export type Email = string;
```

- **Inside Stitchwort nothing changes**: it is the record of §2.2, with all its derived
  instances and its `ext` theorem. That is the attributes rule (§2.5) kept, not bent.
- **At the boundary**, `js.unboxed` is allowed only on a record with exactly one field that has a
  property in JS (proof fields don't count, as for other attributes [checked:
  `docs/syntax.md:428`]), whose type itself crosses. Decoding decodes the field's type and runs
  the record's proof-field validators (so an invalid `Email` string is refused with
  `StitchwortInputError`, as `SafeNat` refuses an out-of-range number); encoding writes the
  field. The `.d.ts` names the type (`export type UserId = string;`), so signatures read
  `(u: UserId)` even in the plain form. `js.flavor "KEY"` (only with `js.unboxed`) adds the
  optional phantom property `KEY` with the type's name as its value.
- **Map keys**: `Map K V` crosses as a plain object when `K` is `Text` or an unboxed record over
  `Text` whose `Ord` is the derived one. That order compares the one field with `Text`'s order
  (§2.2), so the keys are sorted exactly as a `Map Text V`'s; the check in
  `crates/js/src/lib.rs:336-352` (`is_text_order`) learns this one extra case. The `.d.ts` is
  `{ readonly [k: string]: V }`, as today: TypeScript allows a flavoured string as an index
  signature's key type only through `Record<UserId, V>`, which is assignable to it [run: line 9
  of the flavour test].
- **Run time**: with only the attribute, the codec wraps and unwraps at the boundary (one object
  per id per call) and the box stays inside. Internal unboxing (D866, map-equality.md §13.1's
  six-point checklist) removes it: the Rust runtime's and the JS backend's lowering of a
  constructor, a projection and a `case` on a record with one run-time field all use the field
  itself. That is a representation change for *every* such record (`SafeNat`, `Float`, `Mod`,
  `Map`, `Set`), which is why it is its own stage with differential tests; it is invisible to
  the kernel and the evaluator used for proofs.
- **Language complexity**: one attribute (two with `js.flavor`) in an existing closed registry,
  one boundary case, one runtime optimisation. No syntax, no kernel change, no hash change
  (attributes aren't hashed, D598).
- **Proofs**: unchanged. `u.value` computes on a literal; rebuilding needs `UserId.ext`
  until records get eta (records.md stage 2 [checked: `docs/proposals/records.md:929-955`],
  which would make `{ value = u.value } = u` hold by `rfl`). Lemmas written for any key type with
  `DecEq`/`Ord` apply unchanged; lemmas written for `Text` keys need generalising (or a
  `.value` on each side).
- **Quotient maps (SW-356 stage 2)**: `Map` becomes `{ raw: Quot (Map.Raw k v) … }` [checked:
  `docs/proposals/map-equality.md:1053-1076`], itself a record with one run-time field, so D866
  pays for itself twice: microtypes become free, and the quotient's extra box disappears. Keys
  of a microtype type need nothing new from the quotient work: its lemmas are stated for any `k`
  with `Ord`, and a microtype has the derived one. The boundary change above touches the same
  recognition code stage 2 updates [checked: `docs/proposals/map-equality.md:1442-1452`], so it
  should land after it.

### (b1) A `newtype` declaration, as sugar for (a)

```
newtype UserId = Text
```

meaning `@[js.unboxed] type UserId = { value: Text }`, plus a `Show` that prints the inner
value, and perhaps `UserId.mk` and `UserId.get`. Shorter, and it lets the derived `Show` differ
from a record's without breaking "attributes don't change semantics" (it's a different
declaration, not an attribute). Costs: a keyword, a parser and formatter case, docs, and a
second way to write the same thing; its `Show` choice and field name become rules to learn.
Nothing it gives is out of reach of (a) plus a one-line instance. Worth doing only if (a) turns
out clumsy in real code (D1070).

### (b2) An opaque or sealed synonym (Scala's `opaque type`)

```
opaque type UserId = Text     -- `Text` inside this namespace, a distinct type outside
```

Zero cost and string-shaped at the boundary *automatically*, since it is `Text`. But in a
dependently typed checker "distinct outside, equal inside" is a rule every part of the
elaborator must respect: unification, instance search (which unfolds synonyms
[checked: `docs/syntax.md:470`]), dot notation (which unfolds nicknames [checked:
`docs/syntax.md:289`]), `match`, the export checker, messages, and the cache. The kernel would
still unfold it, so a proof written outside could see `UserId = Text` by `rfl` while the
elaborator says they differ: two notions of "equal" of the kind proof-irrelevance.md worked
hard to remove [checked: `docs/proposals/proof-irrelevance.md:1452`]. Instances would need a
rule for "type name" that a synonym doesn't have today (a synonym owns nothing [checked:
`docs/syntax.md:471`]). A large, cross-cutting change for what (a) gets with records the
language already has. Not recommended.

### (c) A library pattern only, no language change

§2.6's `Tagged`, or one-field records with a hand-written codec in TypeScript. Costs nothing to
build, but meets neither N2 nor N3, and `Tagged` loses per-kind instances. It is what a program
can do *today*, and (a)'s records are a strict improvement on it, so the note's examples should
show the record form, not `Tagged`.

### Comparison

| | (a) records + attribute + D866 | (b1) `newtype` sugar | (b2) opaque synonym | (c) library only |
|---|---|---|---|---|
| N1 distinct | yes | yes | outside its namespace | yes |
| N2 no run-time cost | after D866 | after D866 | yes | no |
| N3/N4 plain or flavoured `string` | yes | yes | plain (flavour needs more) | no |
| N5 `${…}` prints the text | one-line instance | yes | yes (it's `Text`'s) | one shared instance |
| N6 map key across the boundary | yes (one new case) | yes | yes | no |
| N8 proofs see through | `.value`, `ext` (eta later) | same | by `rfl`, inside and (surprisingly) outside | `.value`, `ext` |
| Language change | one attribute, one optimisation | + keyword | elaborator-wide scope rule | none |
| Kernel change | none | none | none, but a split notion of equality | none |

## 6. Recommendation

**(a)**, in three stages, with (b1) held back until the record form has been used in a real
program. Concretely:

1. `@[js.unboxed]` on a record with one JS field: crosses as that field, named in the `.d.ts`.
2. `@[js.flavor "KEY"]` with it: the flavoured TypeScript form, property name chosen by the
   program so it can match an app's existing convention. No branded form for now: a brand can't
   be checked at run time and makes every app call site cast; an app that wants brands can
   still pass branded values in (they're accepted where a flavour is expected [run]).
3. `Map K V` crosses as a plain object when `K` is an unboxed record over `Text` with its
   derived order.
4. D866, internal unboxing of every record with one run-time field, in its own lane after
   SW-356 stage 2.
5. Document the microtype recipe in `docs/syntax.md` (record, attribute, one-line `Show`), with
   an `examples/extract/` program and its `.d.ts` checked by `tsc`.

A complete microtype would then read:

```
@[js.unboxed, js.flavor "__flavor"]
type UserId = { value: Text }

instance UserId.instShow: Show UserId := Show.fromText (u => u.value)

export def ownerOf (orders: Map OrderId UserId) (o: OrderId): Option UserId := Map.get o orders
```

```ts
export type UserId = string & { readonly __flavor?: "UserId" };
export type OrderId = string & { readonly __flavor?: "OrderId" };
export declare function ownerOf(orders: { readonly [k: string]: UserId }, o: OrderId): UserId | undefined;
```

## 7. Stages

One lane per stage. Each ends with `docs/syntax.md` updated and the new examples in
`examples/extract/` and `examples/reject/`.

| Stage | What | Lane | Depends on |
|---|---|---|---|
| **1. Boundary** | `js.unboxed` and `js.flavor` in the registry (a new `Record` target in `crates/elab/src/attributes.rs`), their checks (`E-ATTRIBUTE`: not a record, not exactly one JS field, field type doesn't cross, `js.flavor` without `js.unboxed`, an empty or `__proto__` key); a `Boundary` case in `crates/js/src/lib.rs` and the fast codecs in `crates/js/src/fast.rs` (decode the field and run the validators, encode the field); the `.d.ts` alias; `Map K V` with such a key; the literal printer; tests including `tsc` assignability (plain string in, other flavour refused) | **Opus** (two codec paths and the map rule must agree) | SW-356 stage 2 merged (it changes the same map recognition) |
| **2. Unboxing (D866)** | Records with exactly one run-time field are their field, in `crates/rt` (lowering of constructor, projection, `case`, partially applied constructor) and in the JS backend, following map-equality.md §13.1's checklist: one shared "how many run-time fields" function, polymorphic and dependent records, codecs re-boxing types *without* `js.unboxed`, the map literal printer; differential tests (reference evaluator, Rust runtime, JS) over such records, erased-field and polymorphic cases included; a timing of `Map`-heavy programs before and after | **Opus** | stage 1 not required; after SW-356 stage 2 so `Map`'s representation changes once |
| **3. Recipe and conveniences** | `docs/syntax.md` "Microtypes" section; an example with `UserId`, `OrderId`, a validated `Email` and a `Map OrderId UserId` export; the one-line `Show`; a short note of how lemmas stated for `Text` keys are generalised to any key with `Ord` | **Sonnet** | stage 1 |

## 8. Decisions

- **D1064: The approach.** Options: (a) one-field records with `@[js.unboxed]` and internal
  unboxing; (b1) a `newtype` keyword (sugar for (a)); (b2) opaque synonyms, distinct outside
  their namespace; (c) no language change, a library pattern. **[Recommend (a)]**: it meets every
  need with an attribute and an optimisation, and no new rule in the checker (§5).
- **D1065: The attribute's name and scope.** Options: `js.unboxed` (ReScript's and OCaml's
  word); `js.transparent` (serde's and Rust's); `js.as "string"`. Scope: only records with exactly
  one JS field, any field type that crosses (also `SafeNat`, `Float`, `Bool`, a `js.enum`
  type), with or without type parameters. **[Recommend `js.unboxed`, any crossing field type,
  no type parameters in stage 1]** (the word ReScript and OCaml use, and attributes.md's for the union version; a
  parameterised microtype is rare, and allowing it later adds nothing that breaks).
- **D1066: The TypeScript form.** Options: (i) plain alias, `type UserId = string`;
  (ii) flavoured, with a property name the program chooses (`js.flavor "KEY"`); (iii) branded;
  (iv) all three. **[Recommend (i) by default, (ii) on request, (iii) not now]**: the flavour
  is the only form that adds safety and still accepts plain strings (§3, [run]); a brand forces
  casts and can't be checked at run time.
- **D1067: Internal unboxing (D866).** Options: (i) build it now, as stage 2 of this note;
  (ii) build it as part of SW-356 stage 2; (iii) leave the box. **[Recommend (i), after SW-356
  stage 2 merges]**: it is what makes microtypes free, and also takes away the quotient's extra
  box per map, but it changes every one-field record's representation, so it gets its own lane
  and tests rather than riding in the quotient work (which D866 already decided).
- **D1068: Microtype keys across the boundary.** Options: (i) `Map K V` crosses as a plain object
  for an unboxed record over `Text` with its derived order; (ii) also for any order the program
  supplies (the codec would sort by it); (iii) only `Map Text V`, the program converts.
  **[Recommend (i)]**: it is the common case, and its order provably agrees with `Text`'s; (ii)
  can follow if needed.
- **D1069: Conversions between containers.** Options: (i) none: `xs.map (u => u.value)`, O(n),
  as now; (ii) a Haskell-style `coerce` with roles; (iii) after D866, an optimisation that turns
  `map` of a projection of an unboxed record into the identity. **[Recommend (i)]**: (ii) is a
  type-system feature far beyond this need; (iii) can be measured later.
- **D1070: A `newtype` declaration later.** Options: (i) not now, revisit once a real program
  has used the record form for a while; (ii) add it in stage 3; (iii) never. **[Recommend (i)]**:
  (b1) only saves the attribute and the `Show` line, and adds a second spelling to teach.

## 9. Sources

Not re-read while writing this note (**[unverified]**); each link is where the claim can be
checked.

- Haskell 2010 Report, §4.2.3 "Datatype Renamings":
  https://www.haskell.org/onlinereport/haskell2010/haskellch4.html
- J. Breitner, R. Eisenberg, S. Peyton Jones, S. Weirich, "Safe Zero-cost Coercions for
  Haskell", ICFP 2014 (`Data.Coerce`, roles).
- GHC User's Guide, "Deriving via" and `GeneralizedNewtypeDeriving`:
  https://downloads.haskell.org/ghc/latest/docs/users_guide/
- The Rust Book, "Using the Newtype Pattern"; RFC 1758, `#[repr(transparent)]`:
  https://rust-lang.github.io/rfcs/1758-repr-transparent.html ; serde's `#[serde(transparent)]`:
  https://serde.rs/container-attrs.html
- Scala 3 Reference, "Opaque Type Aliases":
  https://docs.scala-lang.org/scala3/reference/other-new-features/opaques.html
- F# Language Reference, "Units of Measure" and "Discriminated Unions" (single-case, `[<Struct>]`):
  https://learn.microsoft.com/dotnet/fsharp/language-reference/
- TypeScript branding and flavouring: "Nominal Typing" in *TypeScript Deep Dive*
  (https://basarat.gitbook.io/typescript/main-1/nominaltyping); Atomic Object, "Flavoring:
  Flexible Nominal Typing for TypeScript" (2018). The assignability table in §3 is [run] here.
- Unison, "Unique and structural types":
  https://www.unison-lang.org/docs/fundamentals/data-types/unique-and-structural-types/
- Lean 4: `structure` and `deriving` (Theorem Proving in Lean 4, "Structures and Records"); the
  representation of structures with one relevant field: "Foreign Function Interface",
  https://lean-lang.org/lean4/doc/dev/ffi.html
- ReScript, unboxed variants and records: https://rescript-lang.org/docs/manual/latest/variant ;
  OCaml manual, "Unboxed types" (`[@@unboxed]`).

## As built (stage 1: the JS boundary)

Built in SW-380, after D866 (stage 2 of §7, so a microtype already *is* its field inside
generated code) and SW-356 stage 2.1 (`Map` and `Set` are quotients). `js.flavor` is not built
(D1066 is the plain alias only), and stage 3's recipe is in `docs/syntax.md` ("Microtypes").

**The attribute.** `js.unboxed`, no argument, in the closed registry
(`crates/elab/src/attributes.rs`) with a new target, `Record`: the first attribute a record type
takes. `E-ATTRIBUTE` on a data type with constructors (with a note), a constructor, a field, a
record with type parameters (D1065: none in stage 1), with no field that has a property (only
proofs or types), with two or more, whose field is written `Option _`, together with `js.name`
on its field (it has no key), with an argument, or twice. `JsRepr` gained `unboxed: bool`
(`crates/core/src/js_repr.rs`), cached with the namespace (check-cache `FORMAT` 11); an unboxed
record's key is never checked for clashes, since it has no property.

**Two refusals at export (`E-EXPORT`)**, where the elaborator can't see enough: an `Option`
behind a synonym (`type MaybeText = Option Text`), and a chain of unboxed records that comes back
to itself (`type T = { value: T }`), which would cross as nothing. Whether the field's type
crosses at all is the boundary's ordinary question, as for any record.

**Why not an `Option` field** (a narrowing of D1065's "any field type that crosses"): an
`Option T` crosses as `T | undefined`, and an `Option` of the record would cross as
`T | undefined | undefined`, so `None` and `Some { value = None }` would be the same JS value.
`Option (Option T)` avoids that by making the inner one the tagged data type
(`Boundary::payload`); doing the same through unboxed records would need that rule taught to
both codecs and the `.d.ts`, for a microtype nobody has asked for. Leaving out the attribute
gives the object form, which works.

**Codec.** `Boundary` keeps an unboxed record as `Data(d, [])` (so the `.d.ts` names it), and
each place that reads a type's form asks `repr.unboxed`:

- the general codec: `define(…, unboxed, bare)` marks it; `decode` treats it like an `Option`,
  a frame with no step in the path, decoding the field's type and then running the record's
  proof checks on the result; `encode` simply continues at the field's type (the value is
  already the field's, D866); `shallow` sees through it;
- the fast codecs (`crates/js/src/fast.rs`): the decoder is the field's decoder plus the checks
  (`throw FAIL` on a failure, so the general decoder gives the message), the encoder the
  field's; `shallow` agrees with the runtime's;
- the literal printer used by the differential tests: the field's literal.

**Map keys (D1068).** `Boundary::Map` gained the key's form: `Text`, or `Data(K, [])` for a
`js.unboxed` record over the prelude's `Text` whose order argument is `K.%instOrd`, the derived
instance (derive_ord.rs; a program can't write a name with `%`, so a program's own instance or
`[ord := …]` is never it). The derived compare is `Text`'s compare of the one field, and inside
generated code the key is the string, so the map is built and read with the same `MAP_SHAPE`
(`Map.fromList` and `Map.toList` at `Text.instOrd`) as a `Map Text V`, giving the same tree.
A key's proof fields are checked (``m.nobody: the key's proof field `valid` (…) doesn't hold``).
In the runtime, `map(t)` became `map(t, k = TEXT)`, cached per key type. Messages:

- a key that is neither: "`Map Nat Nat` can't cross the JS boundary: only maps from `Text`, or
  from a `js.unboxed` record over `Text`, cross, as plain objects" (also a record without the
  attribute, and a microtype over `Nat`);
- a microtype key in another order: "`Map UserId Nat [ord := reversed]` can't cross the JS
  boundary: a map from `UserId` crosses only in `UserId`'s derived order, which is `Text`'s,
  and this map has another".

**`.d.ts`.** `export type UserId = string;` (the field's type, readonly-free as in every
declaration: `type Tags = string[]`), used by name everywhere, map keys included:
`{ readonly [k: UserId]: V }`, which TypeScript accepts as an index signature because the alias
is `string`. tsc 7.0.2 `--strict --exactOptionalPropertyTypes` accepts an app passing plain
strings and `Record<string, bigint>` in, and assigning results to `string` and
`Record<string, bigint>`; as D1066 accepts, it also accepts an `OrderId` where a `UserId` is
expected.

**Tests.** `examples/extract/microtypes.sw` (run lines, the random differential cases with keys
and proofs, the snapshot, tsc on the `.d.ts`); `microtypes_cross_as_their_field` (node: every
position, the refusals and their paths, map keys and their proofs, the general decoder after a
getter that throws once); `microtypes_are_plain_aliases_in_typescript` (tsc); rejects
`examples/reject/attribute-unboxed-*.sw` (10) and `examples/reject/microtype-*.sw` (4: a custom
order, a key without the attribute, a microtype key over `Nat`, an `Option` behind a synonym).
Hashes don't move (attributes aren't hashed, D598); every existing `.js` snapshot changes only
in the runtime text.

## As built (stage 3: recipe and conveniences)

Built in SW-380 stage 3. No compiler change.

- **Recipe.** `docs/syntax.md` "Microtypes" now ends with the four steps (declare, validate with
  a proof field and a smart constructor returning `Option` or `{Fail}`, use as a `Map` key,
  export). The example is `examples/extract/microtype-orders.sw` (`UserId`, `OrderId`, a
  validated `Email`, exports over `Map OrderId UserId`), with run lines, tests, and the usual
  extract snapshots, whose `.d.ts` the extract test already checks with `tsc`.
- **The one-line `Show`.** Already available and enough: derived `Show` prints
  `{ value = "u1" }`, and `Show.fromText (u => u.value)` makes `${u}` print `u1`. A derived
  one-line form for `js.unboxed` records was not added; it would change what `${...}` prints for
  a record by an attribute whose job is the JS boundary.
- **Lemmas for `Text` keys, for any key.** A microtype key uses the derived `Ord`, which
  compares the one field. The `Map` lemmas in the library (`Map.getToList`, `Map.ext`,
  `Map.memToList`, ...) are already stated for any `[auto ord: Ord k]`, so they apply to
  `Map OrderId V` unchanged. A lemma a program proved for `Map Text V` generalises by replacing
  `Text` with a type variable `k` and adding `[auto ord: Ord k]`; the proof goes through if it
  used only the `Ord` laws (`compare`, `trans`, `flip`) and not facts about `Text`. Where it
  did use a `Text` fact, the microtype's own order is that fact through the field, because the
  derived `compare` is `Text`'s compare of `value`.
- **`js.flavor`** remains not built (D1066: plain alias only).
