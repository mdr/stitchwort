# Proposal: named fields on variants (patterns, shared access, shared update)

**Status:** draft 1, 23 October 2026, for review. Ticket SW-340, decision D587.
Nothing is built. The questions for the user are D593 to D595
([§11](#11-decisions-for-the-user)).

Labels, as in the other notes:

- **[checked]**: read in the Stitchwort source or docs at the `file:line` given
  (commit `1f7efee2`), or in a source listed at the end ([R1], [H1] and so on);
- **[run]**: a Stitchwort program checked or built on 23 October 2026 with the
  release CLI built from main that morning (scratch files, not committed; quoted
  where used);
- **[inferred]**: my reasoning from checked facts;
- **[unverified]**: believed, not confirmed.

## Contents

0. [Summary](#0-summary)
1. [The problem](#1-the-problem)
2. [Stitchwort today](#2-stitchwort-today)
3. [How other languages do it](#3-how-other-languages-do-it)
4. [Feature 1: named-field constructor patterns](#4-feature-1-named-field-constructor-patterns)
5. [Feature 2: shared-field access](#5-feature-2-shared-field-access)
6. [Feature 3: shared-field update](#6-feature-3-shared-field-update)
7. [Before and after](#7-before-and-after)
8. [The alternative: a record with a `kind` variant](#8-the-alternative-a-record-with-a-kind-variant)
9. [Interactions](#9-interactions)
10. [Implementation sketch and cost](#10-implementation-sketch-and-cost)
11. [Decisions for the user](#11-decisions-for-the-user)
12. [Risks](#12-risks)
13. [What I couldn't verify](#13-what-i-couldnt-verify)
14. [Sources](#14-sources)

## 0. Summary

A data type with several constructors that share fields (an id, a position, a
timestamp in every case) leads to the same three chores again and again:
positional patterns that count underscores, a hand-written getter per shared
field with one arm per constructor, and a hand-written "setter" per shared field
that rebuilds each constructor. Records already solve all three for
one-constructor types. This note extends the record forms to variants:

1. **Named-field constructor patterns.** `| Slide { id, .. } => id`,
   `| Slide { text = t, .. } => …`, anywhere a pattern goes. They mean exactly
   the positional pattern with `_` for the fields left out, so coverage and
   exhaustiveness don't change. Rust and Scala 3.7 have this; Haskell has it for
   record-syntax constructors.
2. **Shared-field access.** `a.id` works when **every** constructor has an
   explicit field `id` of the **same type** (a type that may mention the type's
   parameters and other shared fields, nothing else). It's a generated
   function `Annotation.id`, like a record's projection, so dot notation,
   `.id` sections, pipes, hover and lemmas all treat it like any other
   function. There are never partial accessors: Haskell's experience
   (`-Wpartial-fields`, runtime errors) is what this rule avoids.
3. **Shared-field update.** `{ a | start = t }` on a variant rebuilds the same
   constructor with `start` replaced, under the same conditions as access and
   the records' rule for dependent fields (`E-RECORD-UPDATE`).

**Costs** (rough, [§10](#10-implementation-sketch-and-cost)): feature 1 is
small (no parser change: the parser already produces the right tree; about
80 lines in the pattern compiler plus tests). Features 2 and 3 are medium
(about 250 and 200 lines in the elaborator), none touches the kernel, and
the JS representation doesn't change at all.

**Recommendations:** build all three, in order 1, 2, 3, as one lane each.
The three decisions: how `C { … }` is told apart from today's `C` applied to
a record pattern (D593); whether shared accessors are generated for every
data type, including one-constructor types like `Pair`, whose hand-written
`Pair.fst` and `Pair.snd` they would replace (D594); and whether a bare
`{ id, .. }` (no constructor) should match a variant by its shared fields
(D595).

## 1. The problem

A program models a document's annotations. Each kind has its own data, and
all of them have a reference number, an id and a start time:

```
type Annotation =
  | Heading (ref: Nat) (id: Text) (start: Int)
  | Slide (ref: Nat) (id: Text) (start: Int) (text: Text)
  | CardGroup (ref: Nat) (id: Text) (start: Int) (duration: Nat) (cards: List Card)

def Annotation.id: Annotation -> Text
  | Heading _ id _       => id
  | Slide _ id _ _       => id
  | CardGroup _ id _ _ _ => id

def withStart (t: Int): Annotation -> Annotation
  | Heading r id _        => Heading r id t
  | Slide r id _ x        => Slide r id t x
  | CardGroup r id _ d cs => CardGroup r id t d cs
```

This came up in a real port of a TypeScript program whose data was exactly
this shape: a TS discriminated union in which every member carries the same
base fields. With three shared fields the program needs three getters and up
to three setters, each with an arm per constructor, each to be edited when a
constructor or a field is added, and every positional pattern counts
underscores. TypeScript itself needs none of this ([§3.5](#35-typescript)).

## 2. Stitchwort today

**Constructor fields are always named.** A constructor's fields are binders,
`| Cons (head: a) (tail: List a)` (`CtorDecl.fields: Vec<Binder>`,
`crates/syntax/src/ast.rs:672`) **[checked]**, so every field already has a
name to use.

**Records** are one-constructor data types with a flag, and get literals,
`e.f`, updates and patterns (`docs/syntax.md` §Records,
[records.md §6.5](records.md#65-as-built-stage-1)) **[checked]**:

- **Projections.** Each field gets a generated definition `R.f`, a one-branch
  `Case`, registered as a member of `R`'s namespace (`records.rs:74`
  `projections`) **[checked]**. In a later field's type, earlier fields are
  their projections, which is how `Sized.ok: (r: Sized) -> length (Sized.items
  r) = Sized.size r` is typed.
- **`e.f`** is ordinary dot notation: it looks up `f` in the namespace of
  `e`'s type and finds the projection there like any `T.f` function
  (`dot.rs:321` `find`) **[checked]**. On a variant it fails:
  `a.id` with `a: Annotation` is `E-UNKNOWN-FIELD`, "`Annotation` has no field
  or function `id`" **[run]**.
- **Update** `{ e | f = … }` builds the constructor, taking the fields not
  replaced from projections of the base, which is bound to a variable first so
  it runs once; a later field whose type mentions a replaced one must be
  replaced too, `E-RECORD-UPDATE` (`records.rs:477` `update`) **[checked]**.
- **Patterns** `{ f = p, g, .. }` are resolved by the type of what they match
  and turned into the positional constructor pattern with `_` for the fields
  left out (`records.rs:243` `record_pattern`) **[checked]**. So coverage is
  the ordinary constructor's.
- **A user's `def Person.name`** next to the record's field `name` is
  `E-DUPLICATE`, "`Person.name` is already defined" **[run]**.

**`C { … }` already parses.** In a pattern, a constructor's arguments are
patterns and a record pattern is one, so `| W { name, .. } => name` is `W`
applied to one record pattern. With `type Wrap = | W (p: Person)` this checks
today **[run]**. With a two-field constructor, `| T2 { name, .. }` is
`E-ARITY`, "`T2` has 2 fields, but this pattern has 1" **[run]**. The same
form in an expression, `Cons { row = r, column = c }`, is a constructor
applied to a record literal, and it's common: `Some { value = n, fits = h }`
(`std/Int/Safe.sw:20`), `xs.map (Cons { row = 0, column = c })` (a partial
application, `examples/accept/record-literal-in-partial-ctor.sw:11`)
**[checked]**.

**At the JS boundary** a variant is a tagged object whose keys are the field
names. For the type above the `.d.ts` is **[run]**:

```ts
export type Annotation =
  | { readonly tag: "Heading"; readonly ref: bigint; readonly id: string; readonly start: bigint }
  | { readonly tag: "Slide"; readonly ref: bigint; readonly id: string; readonly start: bigint; readonly text: string };
```

A field called `tag` is `$tag` (DESIGN.md §12, Names) **[checked]**.

## 3. How other languages do it

### 3.1 Rust

Enum variants can be "struct-like", `Move { x: i32, y: i32 }`, and a struct
pattern matches them by name: `Message::Move { x, .. }`, with `x` short for
`x: x` and `..` ignoring the rest; without `..` every field must be listed
[R1] **[checked]**. Tuple-like variants can even be matched by index in braces,
`ChangeColor { 0: red, 1: green, 2: _ }` [R1] **[checked]**. There is **no**
shared-field access: `m.x` on an enum isn't allowed, so Rust code writes the
getter by hand or moves the shared fields into a struct around the enum
**[unverified]** (common practice, not a reference rule). Functional update
`..base` is for structs only: "A struct expression that constructs a value of a
struct type can terminate with the syntax `..`" [R2] **[checked]**.

### 3.2 OCaml

Constructors can take an "inline record", `Point of { x: float; y: float }`;
matching binds it as a pseudo-value that "can only be used with the dot-notation
to extract or modify fields or to build new constructor values" and "cannot
escape the scope of the binding" [O1] **[checked]**. Update names the
constructor, `Point { p with x = … }` (the manual's example) [O1] **[checked]**.
No access across constructors: field names belong to one constructor's inline
record **[unverified]**.

### 3.3 Haskell

Record syntax works for every constructor of a type, and a label may appear in
several constructors if "the typing of the field is the same in all cases after
type synonym expansion" (Haskell 2010 §4.2.1) [H1] **[checked]**. The selector
is then a function on the whole type, which fails at run time on a constructor
without the field. GHC warns about exactly this: `-Wpartial-fields` "warns about a
record field f that is defined in some, but not all, of the constructors",
`-Wincomplete-record-selectors` and `-Wincomplete-record-updates` warn about
uses [H2] **[checked]**. Update `e { f = v }` keeps the constructor; "an
execution error occurs when the value being updated does not contain all of the
specified labels" (§3.15.3) [H3] **[checked]**. Patterns `C { f = p }` name a
constructor's fields; `C {}` matches any `C` (§3.17) [H3] **[checked]**.
`OverloadedRecordDot` gives `e.x` through `HasField` [H4] **[checked]**.

So Haskell has all three features, and their known flaw is partiality. A label
in *every* constructor with the same type is safe in Haskell too; this proposal
keeps only that safe case.

### 3.4 Scala

A case class has a generated `copy` for updates [S1] **[checked]**. A sealed
trait with an abstract `val id: String`, implemented by each case class, gives
`a.id` on the trait **[unverified]** (standard Scala, not found stated on the
page fetched). Updating a shared field across cases needs a match
(`case s: Slide => s.copy(start = t)` per case) **[unverified]**. Since Scala
3.7, named patterns work on case classes: `case City(name = n, zip = 1026,
population = pop)`, "not all fields of the selector need to be matched", and
"either all elements of a tuple or constructor pattern are named or none are
named" [S2] **[checked]**.

### 3.5 TypeScript

A discriminated union is a union of object types with a common literal
property [T1] **[checked]**. Reading a property that only some members have is
an error ("Property 'radius' does not exist on type 'Shape'") until the union is
narrowed [T1] **[checked]**; a property every member has can be read directly
**[inferred]** from TS's union rules, not stated on that page. A spread update
`{ ...a, start: t }` on a union keeps the union **[unverified]**. This is the
behaviour features 2 and 3 copy, and it's what users porting TS code expect.

### 3.6 Dependently typed languages

Lean generates projections for structures (one constructor) only: "projection
functions are generated for each field" [L1] **[checked]**; for inductives with
several constructors the reference mentions only the recursor and helpers
[L1] **[checked]**. Lean patterns accept named arguments and `..`
(`.node (left := l) ..`) **[unverified]**; the reference does say an ellipsis
makes "all further arguments ... universal patterns" [L2] **[checked]**. Idris 2
records are one-constructor, with `r.field` and `{ field := v } r` updates that
may change a field's type when the result is well typed [I1] **[checked]**.
Agda's records are one-constructor too **[unverified]**. None of the
dependently typed languages I checked gives shared-field access on
multi-constructor types; Haskell is the precedent, minus its partiality.

### 3.7 Elm and PureScript

Elm's custom types have positional arguments only; named fields come from a
record argument, `Circle { radius : Float }`, matched as `Circle { radius }`
**[unverified]** (the Elm records page returned nothing usable). PureScript has
Haskell-style record update `p { x = v }` on records [P1] **[checked]**;
whether its data constructors can declare record fields I didn't confirm
**[unverified]**.

## 4. Feature 1: named-field constructor patterns

### 4.1 Syntax and meaning

```
| Slide { id, .. }                  => id
| Slide { text = t, start, .. }     => …
| CardGroup { cards = Cons c _, .. } => …     -- nested: a constructor after `=` takes
                                                -- its arguments without brackets, as in records
| Heading { ref, id, start }        => …     -- every field named: no `..`
```

`C { f₁ = p₁, f₂, .. }` is the positional pattern `C q₁ … qₙ` where `qᵢ` is
the pattern given for field `i`, the variable `fᵢ` for a punned field, and `_`
for a field left out. Fields may be named in any order, each once; without
`..`, every explicit field must be named (`E-RECORD-FIELD`, as for records);
an unknown name is `E-UNKNOWN-FIELD`, listing `C`'s fields.

It works everywhere a pattern does (arms, `match`, `let`, lambdas) and nests in
any pattern, because it's just another way to write a constructor pattern.
**Coverage, exhaustiveness and unreachable-arm warnings are unchanged**: they
see the positional pattern.

**Implicit fields** (indexed families' `[n: Nat]`) keep their own syntax,
`VCons [n := k] _ _`, and are skipped by braces, as they are by positional
patterns. Braces name explicit fields only.

**Expressions are not part of this.** `Slide { ref = 1, id = "a", … }` as a
way to *build* a constructor by field names would collide with today's
`Cons { row = r, column = c }`, a constructor partially applied to a record
literal ([§2](#2-stitchwort-today)), which is common and meaningful in
expressions. Patterns have no partial application, so they don't have this
problem (see 4.2). Named construction can come later with its own spelling
if wanted; it isn't needed for the boilerplate this note is about.

### 4.2 Telling `C { … }` from `C` applied to a record pattern (D593)

Today `W { name, .. }` is `W` applied to a record pattern, and it checks when
`W`'s one field is a record ([§2](#2-stitchwort-today)). The new form must not
change that by accident. **Recommended rule:** the parser keeps producing what
it does today (a constructor applied to one record pattern), and the pattern
compiler decides:

> `C { … }`, with the braces as `C`'s only argument, names `C`'s fields when
> `C` has **any number of explicit fields but one**. When `C` has exactly one
> explicit field, the braces are that field's pattern, as today.

Why this is safe and enough **[inferred]**:

- For a constructor with two or more explicit fields, `C { … }` alone is
  `E-ARITY` today ([§2](#2-stitchwort-today), **[run]**). The new meaning only
  takes over programs that don't check now. With zero fields, `Done { .. }` is
  also an arity error today and becomes "match `Done`".
- For a one-field constructor, naming its field adds nothing over the
  positional pattern (`Divider { id }` vs `Divider id`), so nothing is lost by
  keeping today's meaning. And for a constructor wrapping a record
  (`| Circle CircleData`, the planned JS-flattened wrapper from records.md's
  decisions), `Circle { radius, .. }` reading the record's fields is exactly
  the natural meaning.
- `C { … } p` (braces followed by more arguments, as in `Cons { lead = …, .. }
  rest` in `examples/accept/records.sw:32`) is positional, as today.
- The rule looks at `C`'s declaration, never at types inferred during
  checking, so it's predictable and needs no expected type.

When a one-field constructor's field isn't a record and the braces name it
(`Divider { id }` with `Divider (id: Text)`), today's error is
`E-NOT-A-RECORD`; it gets a note: "`Divider` has one field, so `{ … }` here
matches that field; write `Divider id`".

**Alternatives** for D593:

- **(b) Braces after a constructor always name its fields**, and a record
  pattern as a one-field constructor's argument needs brackets:
  `W ({ name, .. })`. One rule, no exception, but every existing
  `Some { from, to }`-style pattern changes, and the parser has to keep the
  brackets it currently drops (`parser.rs:946`: `( p )` returns `p`)
  **[checked]**. Patterns and expressions then read differently
  (`Some { value = n, fits = h }` in an expression is still the record argument).
- **(c) Spacing**: `Slide{ id }` (no space) for named fields, as `f()` and `e.f`
  already depend on spacing. Too easy to misread; not recommended.

### 4.3 Navigation

Each field name in `C { f = … }` notes a use of `C`'s field `f`, so hover shows
its type and go-to-definition goes to the field's binder in `C`'s declaration.
Records note fields through `note_field` (`nav.rs:365`), which today targets the
generated projection's span, the whole type (`records.rs:74`, `span =
data.span`) **[checked]**. Per-field spans of constructor binders have to be
kept for this (the parser has them; whether the elaborator stores them per
field I haven't checked).

## 5. Feature 2: shared-field access

### 5.1 Which fields are shared

A field name `f` is **shared** by data type `T` when:

1. **Every constructor** of `T` has an **explicit** field named `f` (an
   implicit field `[n: Nat]` doesn't count, D594 discusses one-constructor
   types). A type with no constructors has no shared fields.
2. In every constructor, `f`'s declared type **mentions only `T`'s parameters
   and fields that are themselves shared** (and declared before `f` in each
   constructor, so the order of shared fields agrees). It may not mention a
   constructor's own other fields, nor implicit fields (in an indexed family,
   these are how a field's type would depend on the index).
3. Those types are **the same type** in every constructor: equal by
   conversion after putting the parameters and the shared fields in as the
   same variables. So `List a` and a nickname for it agree, as in Haskell's
   "same after type synonym expansion" [H1]; `Nat` and `Int` don't.
4. **Elimination is allowed**: `T` is in `Type` (or higher), or `T` is a
   proposition and `f` is a proof field, by the rule records already follow
   (`E-PROP-ELIM`). A multi-constructor proposition gives no data accessors.

Cases, checked against the rule **[inferred]**:

| Situation | Shared? |
|---|---|
| `id: Text` in every constructor | yes, `Annotation.id: Annotation -> Text` |
| `label: a` in every constructor of `Shape (a: Type)` | yes, `Shape.label: [a] -> Shape a -> a` |
| `n: Nat` and `xs: Vec Nat n` in every constructor | both: `T.xs: (x: T) -> Vec Nat (T.n x)`, the record projections' trick |
| `xs: Vec Nat len` where `len` is in one constructor only | `xs` isn't; `n` and the rest may be |
| `id: Text` in two constructors, `id: Nat` in a third | no |
| `ok: start <= stop` (a proof) where `start`, `stop` are shared | yes, a proof accessor, erased in JS |
| `ok: start <= limit` where `limit` is one constructor's own field | no |
| a field of an indexed family whose type is a parameter's | yes; the accessor takes the indices implicitly: `T.f: [ps] [is] -> T ps is -> F` |
| a field whose type mentions an implicit field (`x: Fin n` in `VCons`) | no |

Nothing is reported when a name isn't shared: a type may have same-named
fields with different types on purpose. The explanation comes at a use
(5.3).

### 5.2 Elaboration: a generated function

For each shared field, the elaborator generates **`T.f`**, an ordinary
definition by one `Case` with a branch per constructor, each returning that
constructor's field:

```
Annotation.id: Annotation -> Text
  | Heading _ id _        => id
  | Slide _ id _ _        => id
  | CardGroup _ id _ _ _  => id
```

It's registered as a member of `T`'s namespace exactly as a record's projection
is (`records.rs:74` registers `R.f` with `mark_member`) **[checked]**. So,
with no change to dot notation **[inferred]** from `dot.rs:321`:

- `a.id` is `Annotation.id a`;
- `annotations.map .id`, `a |> .id` and `Annotation.id` written in full work;
- chained access works (`a.start.toText`).

**Why a function rather than a `match` at each use:** the function has a name,
so goals show `Annotation.id a` (or `a.id` once messages print projections
that way, a records TODO); a lemma can state facts about it; hover and
go-to-definition have something to point at; and it's what records do, so
there is one mechanism. A `match` at the use site would be a different
anonymous helper at every use, which a proof can't name
([equation-lemmas.md §0](equation-lemmas.md) describes that exact problem)
**[checked]**.

**Typing dependent shared fields.** Exactly as record projections: in the type
of `T.xs`, an earlier shared field `n` is `T.n x`. In each branch the
expected type `Vec Nat (T.n x)`, refined by the constructor, computes to
`Vec Nat n` because `T.n (C … n …)` reduces to `n`. This is what
`Sized.ok` relies on today **[checked]**.

### 5.3 Errors

`a.f` where some constructors have `f` but `f` isn't shared:
`E-UNKNOWN-FIELD` with a note saying why, instead of today's "has no field or
function":

```
`Annotation` has no shared field `text`
note: only `Slide` has `text`; match on `a` to read it: `| Slide { text, .. } => …`
```

or "`id` is `Text` in `Heading` and `Slide` but `Nat` in `CardGroup`", or
"`xs`'s type mentions `len`, which only `Slide` has".

### 5.4 Names and clashes

`T.f` is a member of `T`'s namespace, written in full as `Annotation.id`. A
user's own `def Annotation.id` in the same module is `E-DUPLICATE`, as for
records ([§2](#2-stitchwort-today), **[run]**), with a note that `id` is a
shared field. That also means a program that wrote the getter by hand (as in
§1) deletes it. Constructors are uppercase and fields lowercase, so `T.f`
never clashes with a constructor. Field names already belong to the type's
hash ([§9.6](#96-hashes)).

### 5.5 Proofs

- **Computation.** `(Slide 1 "a" 0 "t").id` is `"a"` by `rfl`: the accessor's
  `Case` computes on a constructor.
- **On an unknown value** `a.id` stays `Annotation.id a`, as any function on an
  unknown does. A proof that needs to see through it splits `a` (`match a
  with`), after which each branch's `a.id` computes. That is the normal proof
  style already; no new lemmas are needed for it.
- **Equation lemmas.** None generated (as for record projections and per
  D231 not to generate Lean-style equation lemmas yet,
  [equation-lemmas.md](equation-lemmas.md)) **[checked]**. `Annotation.id.unfold`,
  if wanted, is the general mechanism's business, not this feature's.
- **No eta.** Records' stage 2 eta doesn't apply: a variant isn't determined by
  its shared fields.

## 6. Feature 3: shared-field update

### 6.1 Syntax and rules

`{ a | start = t }` with `a: Annotation` gives the same constructor with
`start` replaced; several fields may be given, `{ a | start = t, ref = 0 }`.
Rules, by analogy with records:

- Every field named must be **shared** (5.1). A field only some constructors
  have is `E-UNKNOWN-FIELD` with the note from 5.3, suggesting a `match`.
- **Dependent fields** (`E-RECORD-UPDATE`): checked per constructor. In each
  constructor, every later field whose type mentions a replaced field must be
  replaced too. If that later field is shared, the user gives it
  (`{ x | n = 3, xs = [1, 2, 3] }`); if it's one constructor's own field, the
  update is impossible and the error says so: "`Slide`'s `items` mentions
  `len`, so `len` can't be updated on every `Annotation`".
- **The base runs once, first**, then the new field expressions in the order
  written, as records (`records.md` §6.1) **[checked]**.
- **The result type** is `a`'s type. For indexed families (`T ps is`),
  updates are left out in this proposal: a replaced field could be one an
  index is computed from in some constructor, and the result type then
  differs per constructor. Access (feature 2) has no such problem.

### 6.2 Elaboration

The new values are elaborated first, in the outer context, each checked
against the shared field's type (with earlier replaced shared fields
substituted, for dependent ones). Then the update is a `Case` on the base with
one branch per constructor, rebuilding that constructor from its own fields
and the new values:

```
{ a | start = t }
  ≈  (%v %t => match %v with
        | Heading r i _         => Heading r i %t
        | Slide r i _ x         => Slide r i %t x
        | CardGroup r i _ d cs  => CardGroup r i %t d cs) a t
```

with `%v` and `%t` hidden (the records' `%record` device, `records.rs:477`)
**[checked]**, so neither the base nor `t` is copied into the branches. This
is a term built directly (an annotated lambda around a `Case`, as `update`
does today), not a lifted `match` helper, so it needs no name.

**In proofs**, `{ a | start = t }.start = t` holds after splitting `a`; on a
known constructor both sides compute. Generated lemmas such as
`Annotation.start_update` are not proposed now ([§12](#12-risks)).

## 7. Before and after

Before: §1. After:

```
type Annotation =
  | Heading (ref: Nat) (id: Text) (start: Int)
  | Slide (ref: Nat) (id: Text) (start: Int) (text: Text)
  | CardGroup (ref: Nat) (id: Text) (start: Int) (duration: Nat) (cards: List Card)

-- No getters: `a.id`, `a.ref`, `a.start` are generated.
def withStart (t: Int) (a: Annotation): Annotation := { a | start = t }

def textOf: Annotation -> Option Text
  | Slide { text, .. } => Some text
  | _                  => None

def cardCount: Annotation -> Nat
  | CardGroup { cards, .. } => cards.length
  | _                       => 0

def ids (xs: List Annotation): List Text := xs.map .id
def shift (d: Int) (xs: List Annotation): List Annotation :=
  xs.map (a => { a | start = a.start + d })
```

Adding a constructor or a field no longer touches any getter, setter or
underscore-counting pattern.

## 8. The alternative: a record with a `kind` variant

The same data can be modelled today, without new features:

```
type AnnotationKind =
  | Heading
  | Slide (text: Text)
  | CardGroup (duration: Nat) (cards: List Card)

type Annotation = { ref: Nat, id: Text, start: Int, kind: AnnotationKind }
```

`a.id` and `{ a | start = t }` work now, and a match reads
`| { kind = Slide text, .. } => …`. It's a good model when the program owns
its data. It's weaker in three ways:

1. **JS interop.** At the boundary it's `{ ref, id, start, kind: { tag:
   "Slide", text } }`: nested. A TS program, an API or a stored document whose
   data is the flat union `{ tag: "Slide", ref, id, start, text }` (the common
   TS idiom, and the shape the port in §1 had to keep) can't be described
   this way; it needs a hand-written conversion on each side of the boundary,
   which defeats the codecs.
2. **The type no longer says "one of three things".** `Annotation` is now a
   record whose last field varies, so a function about slides takes an
   `Annotation` and matches `kind`, and anything with "a slide's fields" has
   to be written as the record plus a proof about `kind`.
3. **Shared fields can't depend on the kind**, and the shared/own split is
   fixed in the type: moving a field from "every kind" to "some kinds" means
   restructuring every use.

The other route already planned, **a constructor wrapping a record**
(`| Slide SlideData`, flattened in JS per the records note's decisions)
**[checked]**, keeps JS flat, but each record repeats the shared fields, so
`a.id` still needs a hand-written getter. It combines well with this
proposal: if every wrapped record has `id`, see D593's one-field rule
(`Slide { id, .. }` reads the wrapped record) and §12 (shared fields through
a wrapper are not proposed).

## 9. Interactions

### 9.1 JS boundary codecs

**Nothing changes in the representation.** Fields already cross under their
names, so shared fields are just keys every member of the union has. TS users
can already write `a.id` on the generated union type ([§2](#2-stitchwort-today),
**[run]**), so features 2 and 3 make the Stitchwort side match what the TS side
already allows.

- **Generated code.** `Annotation.id` could compile to `x.id` without a
  `switch`, since every constructor stores `id` under the same key. An
  optional optimisation, not a requirement.
- **Optional-field codecs (SW-339, D582).** An `Option T` shared field
  becomes an optional property in every member alike; nothing specific to
  shared fields **[inferred]**, since SW-339 works per field.
- **Choosable discriminants (later).** If a type chooses `kind` as its
  discriminant key, a field called `kind` needs the same escaping `tag` gets
  today (`$tag`, DESIGN.md §12) **[checked]**, shared or not. A shared field
  must never be used as the discriminant implicitly; that's the TS idiom of a
  literal-typed common property, which Stitchwort expresses with the tag.
- **`.d.ts`**: optionally, a named base type
  (`export type AnnotationBase = { readonly ref: bigint; readonly id: string;
  readonly start: bigint }`) for TS code that wants to name it. Not proposed
  now.

### 9.2 Derived `==`, `Ord`, `Show`

Unchanged: they work constructor by constructor, and shared fields are
ordinary fields of each constructor. `Show` keeps printing variants
positionally (`Slide 1 "a" 0 "t"`); printing `Slide { ref = 1, … }` would be
a separate choice and would make output longer.

### 9.3 Navigation and the language server

- Hover on `a.id`: `Annotation.id: Annotation -> Text`, with a line "shared
  field of `Heading`, `Slide`, `CardGroup`".
- Go to definition: the `id` binder in the first constructor (records go to
  the type today, 4.3). Find references could include every constructor's `id`
  binder.
- Completion after `a.`: shared fields listed with the type's functions.
- In `Slide { id, .. }`: the field name goes to `Slide`'s `id`.

### 9.4 Namespaces and `T.f` functions

A shared field is a member `T.f`, as a record field is, so there's one lookup:
dot notation finds `T.f` whether it's generated or written. They can't both
exist (`E-DUPLICATE`, 5.4). Nicknames work as today: `p: Price` with
`Price = Annotation` tries `Price.id`, then `Annotation.id`.

### 9.5 Existing code

No backwards compatibility is needed, but feature 2 changes some programs:

- Hand-written getters with a shared field's name (`def Annotation.id` in §1)
  become `E-DUPLICATE`; delete them.
- With D594 (a), every one-constructor data type gets accessors too, so the
  library's hand-written `Pair.fst` and `Pair.snd` (`std/core/Data.sw:89`)
  **[checked]** go, replaced by the generated ones. `Pair.fst` is a registry
  builtin looked up by name (`registry.rs:223`, `Fst = "Pair.fst"`)
  **[checked]**, used by tuple `let` projections (`patlet.rs:180`) and the
  printer (`pretty.rs:526`); the registry must find the generated definition.
- Feature 1 changes no program that checks today (4.2).

### 9.6 Hashes

A data type's hash already covers its field names (records.md §12, as built)
**[checked]**, and which fields are shared is computed from the declaration,
so the type's hash doesn't change. Generated accessors are definitions hashed
like any other. An update compiles to an inline term, hashed as part of the
definition using it.

## 10. Implementation sketch and cost

All in `crates/elab`; no kernel, parser or JS-representation change.
Line counts are rough guesses **[inferred]**.

**Feature 1: small (about 80 lines, plus tests).**
In `pattern_ctor`'s `Pattern::Ctor` branch (`lib.rs:2814`), when the arguments
are exactly one `Pattern::Record` and the constructor's explicit field count
isn't one, build the `CtorPattern` from the named fields: generalise
`record_pattern` (`records.rs:243`) to take a `(DataId, ctor)` and skip
implicit fields; reuse `check_field_names` for that constructor. Errors: the
existing ones, plus the one-field note (4.2). `let`/lambda patterns need
nothing (a constructor pattern there is already a `match`). Nav: note each
field name. Tests: accepted examples in arms, `match`, `let`, lambda and
nested; rejects for an unknown, repeated or missing field; the one-field rule
both ways; coverage the same as the positional form.

**Feature 2: medium (about 250 lines, plus tests).**
After a data group is admitted, compute the shared fields (5.1): walk the
constructors' telescopes with parameters and shared fields as common
variables, check what each type mentions, compare with the kernel's
conversion. Generate `T.f` per shared field, generalising `projections`
(`records.rs:74`) from one branch to one per constructor. Register as
members; the lazy-loading index must list them (§12). Improve the dot
lookup's unknown-member error (`dot.rs:594`) with 5.3's notes. Replace
`Pair.fst`/`Pair.snd` (D594). Tests: the 5.1 table as accepts/rejects,
`rfl` on constructors, a proof by cases, `.id` sections, a dependent shared
field, a proof field, a parameterised type, an indexed family.

**Feature 3: medium (about 200 lines, plus tests).**
Generalise `update` (`records.rs:477`): accept a non-record data type
whose named fields are all shared; elaborate the new values first; check
`E-RECORD-UPDATE` per constructor; build the annotated lambda around a
multi-branch `Case`. Refuse indexed families. Tests: the before/after
example, effects order in a computation, a dependent pair of shared fields,
the per-constructor dependency reject, update of a proof field with its data.

## 11. Decisions for the user

**D593. How is `C { … }` in a pattern told apart from `C` applied to a
record pattern?**
(a) **Recommended:** by `C`'s declaration: braces as the only argument name
`C`'s fields unless `C` has exactly one explicit field, where they're that
field's pattern, as today. No program that checks today changes meaning.
(b) Braces after a constructor always name its fields; a record pattern as
an argument is written in brackets, `W ({ name, .. })`.
(c) Spacing: `Slide{ id }` names fields. Not recommended.

**D594. Which data types get shared-field accessors?**
(a) **Recommended:** every data type, by the one rule in 5.1, including
one-constructor types: `Pair` gets `Pair.fst` and `Pair.snd` generated and
the hand-written ones are deleted; `Char` gets `Char.code`. One rule, nothing
to remember.
(b) Only types with two or more constructors; one-constructor types keep
hand-written functions (and should be records if they want field syntax).

**D595. Should a bare `{ id, .. }` (no constructor) match a variant by its
shared fields?** `let { id, start, .. } := a`, `| { id, .. } => …`,
`annotations.map ({ id, .. } => id)`: an irrefutable pattern binding shared
fields by their accessors (records' pattern `let` already works this way,
`patlet.rs`). It's the pattern form of feature 2, small once 2 exists.
(a) Yes, in the feature 2 lane. (b) **Recommended:** not now; `a.id`
covers the need, and it can be added later without changing anything else.

## 12. Risks

- **The one-field exception (D593 (a))** is a rule users can trip over:
  `Divider { id }` on a one-field constructor reads the field as a record.
  The error note (4.2) is the mitigation.
- **Lazy loading of the library.** The library's index lists names from
  source, which is why `R.ext` isn't generated for library records
  (records.md §6.5) **[checked]**. Shared accessors are generated, and
  whether a name is shared depends on types (rule 3), which source text alone
  can't decide. The index must either list candidates by name (fields present
  in every constructor) and let elaboration confirm them, or elaborate the
  declaration. Record projections already exist for library records, so a
  mechanism is there to extend; the implementing lane must check it.
- **Registry builtins** (`Pair.fst`, D594 (a)) are found by name; generated
  definitions must be found the same way, before anything that uses them.
- **Accidental sharing.** A type whose constructors happen to share a field
  name and type gets an accessor whether or not the author meant it. Harmless
  (it's a total function), but it can take a name a user wanted for
  something else; then `E-DUPLICATE` says why.
- **Performance.** One generated definition per shared field per type; for
  large libraries a few more definitions to check and hash. Small.
- **Not proposed** and possibly asked for later: named construction
  (`Slide { ref = 1, … }`, 4.1), shared fields through a wrapped record
  (`| Slide SlideData`), updates on indexed families, generated update
  lemmas, and the `.d.ts` base type.

## 13. What I couldn't verify

- Whether `HasField` in GHC is solved for partial fields; the pages fetched
  don't say.
- Lean 4's named arguments in constructor patterns (`(left := l)`); the
  reference pages fetched only mention ellipses.
- Scala sealed traits with abstract `val`s giving `a.id` (standard practice,
  not found on the fetched page).
- TypeScript: reading a property every union member has, and spread updates
  on unions, are from knowledge of TS, not a quoted source.
- Elm's and PureScript's constructor-with-record-argument patterns.
- Rust: "no shared-field access on enums" is from knowledge; the reference
  has no rule permitting it.
- Whether the elaborator keeps per-field spans of constructor binders (4.3).

## 14. Sources

- [R1] The Rust Reference, Patterns, Struct patterns.
  https://doc.rust-lang.org/reference/patterns.html#struct-patterns
- [R2] The Rust Reference, Struct expressions, functional update syntax.
  https://doc.rust-lang.org/reference/expressions/struct-expr.html
- [O1] OCaml manual, Inline records. https://ocaml.org/manual/5.2/inlinerecords.html
- [H1] Haskell 2010 Report, chapter 4, §4.2.1 Labelled Fields.
  https://www.haskell.org/onlinereport/haskell2010/haskellch4.html
- [H2] GHC User's Guide, Warnings (`-Wpartial-fields`,
  `-Wincomplete-record-selectors`, `-Wincomplete-record-updates`).
  https://downloads.haskell.org/ghc/latest/docs/users_guide/using-warnings.html
- [H3] Haskell 2010 Report, chapter 3, §3.15 and §3.17.
  https://www.haskell.org/onlinereport/haskell2010/haskellch3.html
- [H4] GHC User's Guide, `OverloadedRecordDot` and `HasField`.
  https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/overloaded_record_dot.html,
  https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/hasfield.html
- [S1] Scala 3 Book, Domain modeling tools (case class `copy`).
  https://docs.scala-lang.org/scala3/book/domain-modeling-tools.html
- [S2] Scala 3 Reference, Named tuples (named patterns on case classes, standard
  since 3.7). https://docs.scala-lang.org/scala3/reference/other-new-features/named-tuples.html
- [T1] TypeScript Handbook, Narrowing, Discriminated unions.
  https://www.typescriptlang.org/docs/handbook/2/narrowing.html
- [L1] Lean Language Reference, Inductive types (structures and projections).
  https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/
- [L2] Lean Language Reference, Pattern matching (ellipses).
  https://lean-lang.org/doc/reference/latest/Terms/Pattern-Matching/
- [I1] Idris 2 documentation, Types and functions (records).
  https://idris2.readthedocs.io/en/latest/tutorial/typesfuns.html
- [P1] PureScript documentation, Records.
  https://github.com/purescript/documentation/blob/master/language/Records.md
