# Proposal: named fields on variants (patterns, shared access, shared update)

**Status:** draft 2, 23 October 2026. Ticket SW-340: the note is D587, this
revision D602. Draft 1 went to an external expert review; draft 2 folds it in
([Response to review](#response-to-review-draft-2)). Decided: D593 (b),
D594 (a), D595 (b). Open: D603 to D605
([§11](#11-decisions-for-the-user)). Feature 1 is built
([§4.4](#44-as-built-feature-1)); features 2 and 3 aren't.

Labels, as in the other notes:

- **[checked]**: read in the Stitchwort source or docs at the `file:line`
  given (re-checked at commit `d20db948`), or in a source listed at the end
  ([R1], [H1] and so on) that I read;
- **[cited]**: stated, with a primary source, by the external review of
  draft 1; I haven't fetched the source myself;
- **[run]**: a Stitchwort program checked on 23 October 2026 with the release
  CLI built at `d20db948` (scratch files, not committed; quoted where used);
- **[inferred]**: my reasoning from checked facts;
- **[unverified]**: believed, not confirmed.

## Contents

0. [Summary](#0-summary)
- [Response to review (draft 2)](#response-to-review-draft-2)
1. [The problem](#1-the-problem)
2. [Stitchwort today](#2-stitchwort-today)
3. [How other languages do it](#3-how-other-languages-do-it)
4. [Feature 1: named-field constructor patterns](#4-feature-1-named-field-constructor-patterns)
5. [Feature 2: shared-field access](#5-feature-2-shared-field-access)
6. [Feature 3: shared-field update](#6-feature-3-shared-field-update)
7. [Before and after](#7-before-and-after)
8. [The alternative: a record with a `kind` variant](#8-the-alternative-a-record-with-a-kind-variant)
9. [Interactions](#9-interactions)
10. [Implementation sketch, cost and acceptance cases](#10-implementation-sketch-cost-and-acceptance-cases)
11. [Decisions for the user](#11-decisions-for-the-user)
12. [Risks, and lazy loading](#12-risks-and-lazy-loading)
13. [What I couldn't verify](#13-what-i-couldnt-verify)
14. [Sources](#14-sources)

## 0. Summary

A data type with several constructors that share fields (an id, a position, a
timestamp in every case) leads to the same three chores again and again:
positional patterns that count underscores, a hand-written getter per shared
field with one arm per constructor, and a hand-written "setter" per shared field
that rebuilds each constructor. Records already solve all three for
one-constructor types. This note extends the record forms to variants:

1. **Named-field constructor patterns.** `| Circle { id, .. } => id`,
   `| Circle { text = t, .. } => …`, anywhere a pattern goes. Braces right
   after a constructor **always** name that constructor's fields (D593 (b));
   a record pattern given as a constructor's positional argument is written in
   brackets, `W ({ name, .. })`. They mean exactly the positional pattern with
   `_` for the fields left out, so coverage doesn't change.
2. **Shared-field access.** `a.id` works when **every** constructor has an
   explicit field `id` of the **same type** (a type that may mention the
   type's parameters and other shared fields, nothing else). It's a generated
   function `Shape.id`, like a record's projection, so dot notation, `.id`
   sections, pipes, hover and proofs treat it like any other function. Every
   data type gets them by the one rule, including one-constructor types such
   as `Pair` (D594 (a)). There are never partial accessors: Haskell's
   experience (`HasField` on a partial field fails at run time) is what this
   rule avoids.
3. **Shared-field update.** `{ a | start = t }` on a variant rebuilds the same
   constructor with `start` replaced. It's elaborated as a `match` on the base
   through the existing `match` machinery, which already generalises the
   replacements' types the way dependent fields need ([§6.2](#62-elaboration)).

A bare `{ id, .. }` matching a variant is deferred (D595 (b)).

**Costs** (rough, [§10](#10-implementation-sketch-cost-and-acceptance-cases)):
feature 1 is small (a parser grouping node for `( p )`, then about 80 lines in
the pattern compiler). Generating the projections is the easy part of feature
2; the risk is in deciding eligibility robustly and in making generated names
work with the library's lazy loading and the check cache. Feature 3's risk is
the dependent case, which reusing `match` keeps small. No kernel change; the
JS representation doesn't change.

**Recommendation:** build in order 1, 2, 3, one lane each, with the acceptance
cases of [§10.4](#104-acceptance-cases) as the bar.

## Response to review (draft 2)

The external review of draft 1 recommended going ahead with the design,
changing D593 and tightening §6.2 and §12. The user adopted its three
recommendations (D593 (b), D594 (a), D595 (b)). Point by point, what changed:

| # | Review point | What changed in draft 2 |
|---|---|---|
| 1 | D593 (a)'s one-field exception can **silently** change a working pattern's meaning when a field is added | Agreed; the counterexample is in [§4.2](#42-braces-always-name-fields-d593-b). Adopted (b): braces after a constructor always name its fields; a record argument is `W ({ … })`; the parser keeps the brackets. Chose braces over Lean's `(name := p)` (4.2, with reasons). The pattern/expression asymmetry is documented, and named construction's spelling is put up as D605 so the pattern grammar is settled knowing it. |
| 2 | Dependent updates need a dependent motive; the naive translation is ill-typed | Agreed that the obligation is real; **partly disagree** that the generator must build the motive. Stitchwort's `match` already generalises: variables whose types mention the scrutinee are copied with those occurrences abstracted (`matching.rs:10`), and the kernel's `case` substitutes the constructor through the whole context (`check.rs:653`). The review's `Sized` example checks today when written as a `match` **[run]**. So §6.2 now elaborates updates through that machinery. Separately, draft 1's "annotated lambda around a `Case`" was **wrong**: `case` may only appear at the top of a definition (`check.rs:1208`), so an update has to be a lifted `match` anyway. |
| 2b | Dependency order vs written order vs evaluation order | Imported the records' exact rule ([§6.3](#63-orders-dependency-written-evaluation)): fields may be written in any order; types are checked in dependency order; effects run base first, then replacements in the order written. Records do this today **[run]**. |
| 3.1 | Common **dependency** order, not identical declaration order | [§5.1](#51-which-fields-are-shared) rule 2 rewritten: names map to positions per constructor; shared fields are generated in a topological order; eligibility failures propagate. |
| 3.2 | Say plainly that indexed families get limited support | [§5.1.2](#512-scope-indexed-families-universes-mentions): no inferring from index refinements; the `Box` example. |
| 3.3 | Universe/higher-kinded parameters compared as rigid | 5.1.2. Stitchwort has no universe variables (`Sort::Type(u32)`, `term.rs:22`), so only fixed levels and higher-kinded parameters arise; both are rigid. |
| 3.4 | Decide what "mentions" means | Syntactic, on the elaborated declared type, as records already do (`term.rs:444`); reasons in 5.1.2. Put to the user as D603 because it decides which accessors exist. |
| 4 | Update dependency closure over the whole telescope, incl. implicit and proof fields, transitive | [§6.1](#61-syntax-and-rules) rewritten; reject names the constructor and the chain; no definitional proof irrelevance (`docs/core.md:139`). |
| 4b | Prop test: `Evidence.witness` allowed; `Claims.P`, `Claims.witness` not | In 5.1's table and the acceptance cases. The one-constructor versions behave so today **[run]**. The review's binders `P`, `Q` aren't valid Stitchwort names (binders are lowercase **[run]**), so the note writes `p`, `q`. |
| 5 | Lazy loading: candidates, not premature reservations | [§12.1](#121-lazy-loading-candidates-then-confirmation): candidate index → elaborate the owner → confirmed or not; a written `T.f` wins when `f` isn't eligible; demand-order independence; an inconclusive conversion is an error, not "not shared"; the check cache's key covers the compiler build, and the entry must carry the new side table. |
| 5b | `Pair` needs a deliberate integration check | [§12.2](#122-pair-checklist), with the registry binding a generated definition doesn't get today (`lib.rs:2017`). `Pair` is in the always-loaded core, so "first demand before `Pair` is loaded" can't happen today; the test is kept as a first use from tuple lowering. |
| 6 | Named functions, uniform generation: agree; "accidental sharing is harmless" too casual | Reworded in 5.4 and §12. One generation path for records and variants (§10). |
| 7 | Defer bare `{ id, .. }` on variants; it's not "small" | D595 (b) recorded; the "small once 2 exists" claim removed (§11). |
| 8 | §8 overstates the expressiveness gap: the two encodings are isomorphic | Agreed; [§8](#8-the-alternative-a-record-with-a-kind-variant) rewritten around the flat JS shape, direct constructor patterns, removing boilerplate and consistency with records. §7's evolution claim qualified. |
| 9 | Language survey corrections | [§3](#3-how-other-languages-do-it) and §13: Haskell `HasField` partiality stated (hedge removed); Lean named patterns; Scala 3.7 named patterns and abstract trait members; TypeScript reworded (common reads give unions; spread doesn't keep the union's invariant); Koka and C# added. |
| 10 | Eleven acceptance cases | [§10.4](#104-acceptance-cases), with Stitchwort spellings. |
| 11 | Revise costs: projections easy; dependent updates and candidate resolution carry the risk | §0 and §10 revised. |

**Where I disagree** (both minor):

- **The motive (point 2).** The review's concern is about a primitive
  eliminator that doesn't rewrite captured variables. Stitchwort's `case` is a
  case tree on a variable, and refines the types of **every** variable in
  scope, including ones bound before the match (`check.rs:653-662`,
  `refine_branch` at `check.rs:873`) **[checked]**; the elaborator's `match`
  also abstracts expression scrutinees out of other variables' types
  (`matching.rs:321` `generalised`) **[checked]**. The review allowed for this
  ("if the existing dependent-match machinery already performs the necessary
  generalisation, reuse it"); it does, so §6.2 reuses it, and the generator
  never builds a motive by hand.
- **Order of dependent replacements (point 2b).** The review's simplest
  contract requires dependent replacements in dependency order. Records
  already accept any written order (`{ r | xs = …, n = 1 }` checks **[run]**),
  so requiring an order on variants only would make the two differ. The
  review's alternative, "a translation that preserves written evaluation
  order", is what records do, and §6.3 adopts it.

## 1. The problem

A program models a document's shapes. Each kind has its own data, and
all of them have a reference number, an id and a start time:

```
type Shape =
  | Dot (ref: Nat) (id: Text) (start: Int)
  | Circle (ref: Nat) (id: Text) (start: Int) (text: Text)
  | Polygon (ref: Nat) (id: Text) (start: Int) (duration: Nat) (points: List Point)

def Shape.id: Shape -> Text
  | Dot _ id _           => id
  | Circle _ id _ _      => id
  | Polygon _ id _ _ _   => id

def shiftTo (t: Int): Shape -> Shape
  | Dot r id _           => Dot r id t
  | Circle r id _ x      => Circle r id t x
  | Polygon r id _ d cs  => Polygon r id t d cs
```

This came up in a port of a TypeScript program whose data was exactly
this shape: a TS discriminated union in which every member carries the same
base fields. With three shared fields the program needs three getters and up
to three setters, each with an arm per constructor, each to be edited when a
constructor or a field is added, and every positional pattern counts
underscores. TypeScript itself needs none of this ([§3.5](#35-typescript)).

## 2. Stitchwort today

**Constructor fields are always named.** A constructor's fields are binders,
`| Cons (head: a) (tail: List a)` (`CtorDecl.fields: Vec<Binder>`,
`crates/syntax/src/ast.rs:672`) **[checked]**, so every field already has a
name to use. Implicit fields are written in square brackets,
`| Chain [a b c: Nat] (first: …) (next: …)` (`aoc/src/Aoc/Day08/Proofs/Spec.sw:52`)
**[checked]**.

**Records** are one-constructor data types with a flag, and get literals,
`e.f`, updates and patterns (`docs/syntax.md` §Records,
[records.md §6.5](records.md#65-as-built-stage-1)) **[checked]**:

- **Projections.** Each field gets a generated definition `R.f`, a one-branch
  `Case`, registered as a member of `R`'s namespace (`records.rs:74`
  `projections`) **[checked]**. In a later field's type, earlier fields are
  their projections, which is how `Sized.ok: (r: Sized) -> length (Sized.items
  r) = Sized.size r` is typed. A field gets no projection when it's data in a
  proposition, or when its type mentions a field that has none
  (`records.rs:82`) **[checked]**.
- **`e.f`** is ordinary dot notation: it looks up `f` in the namespace of
  `e`'s type and finds the projection there like any `T.f` function
  (`dot.rs:321` `find`) **[checked]**. On a variant it fails:
  `a.id` with `a: Shape` is `E-UNKNOWN-FIELD`, "`Shape` has no field
  or function `id`" **[run]** (draft 1).
- **Update** `{ e | f = … }` builds the constructor, taking the fields not
  replaced from projections of the base, which is bound to a variable first so
  it runs once; a field whose type mentions a replaced one must be replaced
  too, `E-RECORD-UPDATE` (`records.rs:477` `update`) **[checked]**. The new
  values are checked in **declaration** order whatever order they're written
  in (`records.rs:533` `update_fields`) **[checked]**, so
  `{ r | xs = VCons 7 VNil, n = 1 }` checks **[run]**. In a computation,
  effects run base first, then the replacements in the order written
  (`effects.rs:1696`, `examples/accept/records-effects.sw`) **[checked]**.
  One limitation, documented in records.md §6.5: with a base that isn't a
  variable, the new fields are checked knowing only that the base is *some*
  record, so `{ pick b r | xs = ys }` with `ys: Vec Nat (pick b r).n` is
  refused ("expected `Vec Nat %record.n`") **[run]**.
- **Patterns** `{ f = p, g, .. }` are resolved by the type of what they match
  and turned into the positional constructor pattern with `_` for the fields
  left out (`records.rs:243` `record_pattern`) **[checked]**. So coverage is
  the ordinary constructor's.
- **A user's `def Person.name`** next to the record's field `name` is
  `E-DUPLICATE`, "`Person.name` is already defined" **[run]** (draft 1).

**`match` generalises.** A `match` that isn't a whole equation's right-hand
side is lifted into a generated definition `owner.%matchN`. A scrutinee that
isn't a plain variable is generalised: a new variable stands for it, and
variables in scope whose types mention it get copies with those occurrences
replaced (`matching.rs:10-19`, `generalised` at `matching.rs:321`)
**[checked]**. The kernel's `case` then substitutes the constructor value for
the matched variable through the whole context (`check.rs:653-662`)
**[checked]**. So this checks **[run]**, and with `A 0 ys` in the first arm
it's refused with "expected `Vec Nat 0`, but this has type `Vec Nat n`"
**[run]**, showing `ys`'s type was refined:

```
def replaceXs (b: Bool) (a: Sized) (ys: Vec Nat (Sized.n (pick b a))): Sized :=
  match pick b a with
    | A n _ => A n ys
    | B n _ => B n ys
```

**`C { … }` in a pattern** is today `C` applied to one record pattern, so with
`type Wrap = | W (person: Person)`, `| W { name, .. } => name` checks
**[run]**. With a two-field constructor it's `E-ARITY`, "`W2` has 2 fields, but
this pattern has 1" **[run]**. Brackets are dropped by the parser: `( p )`
returns `p` (`parser.rs:946-950`) **[checked]**, so `W ({ name, .. })` is the
same tree **[run]**. In the repository's `.sw` files the form occurs in a
pattern once: `| Cons { lead = { name, .. }, .. } rest => name`
(`examples/accept/records.sw:32`) **[checked]** (by grep). The same form in an
expression, a constructor applied to a record literal, is more common, about
fifteen uses, such as `Some { value = n, fits = h }` (`std/Int/Safe.sw:20`) and
`xs.map (Cons { row = 0, column = c })`
(`examples/accept/record-literal-in-partial-ctor.sw:11`) **[checked]**.
`show` prints a record inside a constructor the same way,
`Some { name = "tea", price = 3 }` (`examples/accept/show.sw:62`)
**[checked]**.

**At the JS boundary** a variant is a tagged object whose keys are the field
names. For the type above the `.d.ts` is **[run]** (draft 1):

```ts
export type Shape =
  | { readonly tag: "Dot"; readonly ref: bigint; readonly id: string; readonly start: bigint }
  | { readonly tag: "Circle"; readonly ref: bigint; readonly id: string; readonly start: bigint; readonly text: string };
```

A field called `tag` is `$tag` (DESIGN.md §12, Names) **[checked]**.

## 3. How other languages do it

### 3.1 Rust

Enum variants can be "struct-like", `Move { x: i32, y: i32 }`, and a struct
pattern matches them by name: `Message::Move { x, .. }`, with `x` short for
`x: x` and `..` ignoring the rest; without `..` every field must be listed
[R1] **[checked]**. Tuple-like variants can be matched by index in braces,
`ChangeColor { 0: red, 1: green, 2: _ }` [R1] **[checked]**. Field access
`e.f` is defined for structs and unions only, and functional update `..base`
for struct types only [R2] **[checked]**, [cited]: there is no shared-field
access or update on enums, so Rust code writes the getter by hand or moves the
shared fields into a struct around the enum.

### 3.2 OCaml

Constructors can take an "inline record", `Point of { x: float; y: float }`;
matching binds it as a pseudo-value that "can only be used with the dot-notation
to extract or modify fields or to build new constructor values" and "cannot
escape the scope of the binding" [O1] **[checked]**. Update names the
constructor, `Point { p with x = … }` [O1] **[checked]**. Field names belong to
one constructor's inline record; there's no access across constructors
**[unverified]**.

### 3.3 Haskell

Record syntax works for every constructor of a type, and a label may appear in
several constructors if "the typing of the field is the same in all cases after
type synonym expansion" (Haskell 2010 §4.2.1) [H1] **[checked]**. The selector
is then a function on the whole type, which fails at run time on a constructor
without the field. GHC warns about this: `-Wpartial-fields`,
`-Wincomplete-record-selectors`, `-Wincomplete-record-updates` [H2]
**[checked]**. `OverloadedRecordDot` gives `e.x` through `HasField` [H4]
**[checked]**, and `HasField` is solved for a partial field too: the GHC guide
shows a `HasField` use that fails when given a constructor without the field
[H4] [cited]. Update `e { f = v }` keeps the constructor; "an execution error
occurs when the value being updated does not contain all of the specified
labels" (§3.15.3) [H3] **[checked]**. Patterns `C { f = p }` name a
constructor's fields; `C {}` matches any `C` (§3.17) [H3] **[checked]**.

So Haskell has all three features, and their flaw is partiality. A label in
*every* constructor with the same type is safe in Haskell too; this proposal
keeps only that case, for access and update alike.

### 3.4 Scala

A case class has a generated `copy` for updates [S1] **[checked]**. A trait
with an abstract member, `val id: String`, implemented by each case class,
gives `a.id` on the trait; it's the abstract member that gives the access, not
sealing [S2] [cited]. Updating a shared field across cases needs a match
(`case s: Circle => s.copy(start = t)` per case) **[unverified]**. Since Scala
3.7, named patterns work on case classes: `case City(name = n, zip = 1026,
population = pop)`, "not all fields of the selector need to be matched", and
"either all elements of a tuple or constructor pattern are named or none are
named" [S2] **[checked]**.

### 3.5 TypeScript

A discriminated union is a union of object types with a common literal
property [T1] **[checked]**. Reading a property that only some members have is
an error until the union is narrowed [T1] **[checked]**. A property every
member has can be read directly, and the members' types need not agree: the
result is their union, so `u.value` with `value: string` in one member and
`value: number` in another is `string | number` [T2] [cited]. Stitchwort's
rule is stricter on purpose: different types mean no accessor
([§5.1](#51-which-fields-are-shared)).

For updates, object spread copies properties and later ones override [T3]
[cited]; TypeScript doesn't check that the result keeps the union's invariant:
`{ ...u, value: 0 }` on a `u` tagged `"A"` (where `A`'s `value` is a string)
gives an `"A"` with a number. What feature 3 copies is narrower: replacing
`start` with a value valid for that field in **every** member keeps the result
a valid member of the original union. Porting TS code, that's the update users
write.

### 3.6 Dependently typed languages

Lean generates projections for structures (one constructor) only: "projection
functions are generated for each field" [L1] **[checked]**; for inductives with
several constructors the reference mentions only the recursor and helpers
[L1] **[checked]**. Lean patterns accept named constructor arguments with an
ellipsis, `| Term.lambda (name := n) .. => some n` [L2] [cited]; the reference
says an ellipsis makes "all further arguments ... universal patterns" [L2]
**[checked]**. Lean's `match` generalises dependent context variables into its
motive [L2] [cited], which is what Stitchwort's `match` does too (§2).
Idris 2 records are one-constructor, with `r.field` and `{ field := v } r`
updates that may change a field's type when the result is well typed [I1]
**[checked]**; its documentation describes generating record setters on demand
during elaboration and translating them to case blocks [I1] [cited]. Agda's
records are one-constructor too **[unverified]**.

**Koka** generates an accessor function for each named field of a datatype and
treats dot selection as function application, illustrating a list-head
accessor [K1] [cited]. That's the architecture of feature 2 (a generated
function, found by dot notation), though without its totality rule.

None of the dependently typed languages I checked gives shared-field access on
multi-constructor types; Haskell is the precedent, minus its partiality.

### 3.7 C#

C# records can inherit from a base record. A `with` expression on a reference
typed as the base record, replacing a property the base declares, keeps the
object's run-time subtype and its other properties [C1] [cited]. The mechanism
is inheritance and copying, but what a user sees is feature 3: the variant is
kept and a common field replaced.

### 3.8 Elm and PureScript

Elm's custom types have positional arguments only; named fields come from a
record argument, `Circle { radius : Float }`, matched as `Circle { radius }`
**[unverified]**. PureScript has Haskell-style record update `p { x = v }` on
records [P1] **[checked]**; whether its data constructors can declare record
fields I didn't confirm **[unverified]**. In both, `Circle { radius }` is the
constructor applied to a record pattern, which is draft 1's reading of the
braces and not D593 (b)'s.

## 4. Feature 1: named-field constructor patterns

### 4.1 Syntax and meaning

```
| Circle { id, .. }                 => id
| Circle { text = t, start, .. }    => …
| Polygon { points = Cons c _, .. } => …   -- nested: a constructor after `=` takes
                                           -- its arguments without brackets, as in records
| Dot { ref, id, start }            => …   -- every field named: no `..`
| W { person = { name, .. }, .. }   => …   -- a field that is a record: a record pattern after `=`
```

`C { f₁ = p₁, f₂, .. }` is the positional pattern `C q₁ … qₙ` where `qᵢ` is
the pattern given for field `i`, the variable `fᵢ` for a punned field, and `_`
for a field left out. Fields may be named in any order, each once; without
`..`, every explicit field must be named (`E-RECORD-FIELD`, as for records);
an unknown name is `E-UNKNOWN-FIELD`, listing `C`'s fields. Braces take no
further arguments: `C { … } p` is an error saying to write `C ({ … }) p` if a
record argument was meant.

It works everywhere a pattern does (arms, `match`, `let`, lambdas) and nests in
any pattern, because it's another way to write a constructor pattern.
**Coverage, exhaustiveness and unreachable-arm warnings are unchanged**: they
see the positional pattern.

**Implicit fields** keep their own syntax, `VCons [n := k] _ _`, and are
skipped by braces, as they are by positional patterns. Braces name explicit
fields only. Writing both (`C [n := k] { … }`) isn't in the first version.

### 4.2 Braces always name fields (D593 (b))

**The rule (decided):** braces written directly after a constructor in a
pattern name that constructor's fields, whatever the constructor's arity. A
record pattern as a constructor's positional argument is written in brackets:

```
type Person = { name: Text, age: Nat }
type Wrap = | W (person: Person)

| W { person = { name, .. }, .. } => name   -- names W's field `person`
| W ({ name, .. })                => name   -- W's one argument, a record pattern
| W p                             => p.name -- as before
```

**Why not draft 1's one-field exception.** Draft 1 kept today's reading
(braces are the record argument) for one-field constructors. The review found
a case where that **silently** changes what a working pattern selects. Start
from `type Wrap = | W (person: Person)` and

```
def nameOf: Wrap -> Text
  | W { name, .. } => name          -- (a): reads person.name
```

Now add a field: `type Wrap = | W (person: Person) (name: Text)`. Under (a)
`W` has two fields, so the unchanged pattern now names `W`'s own `name`: it
still checks, still returns `Text`, and can return a different value. No error
message can help, because there's no error. And `..` is exactly what tells a
reader that adding fields leaves the pattern's meaning alone. Under (b) the
first pattern was always `W { name, .. }` = "`W`'s field `name`" (an error
until `W` has one, `E-UNKNOWN-FIELD`), and the record-argument form
`W ({ name, .. })` becomes `E-ARITY` when the field is added. Neither changes
meaning silently **[inferred]**. Draft 1 also said naming a sole field "adds
nothing"; the review is right that it does add something: a named pattern
keeps selecting the same field when fields are added.

**What changes for existing code.** One pattern in the repository:
`| Cons { lead = { name, .. }, .. } rest => name` (`examples/accept/records.sw:32`)
becomes `| Cons ({ lead = { name, .. }, .. }) rest => name`. Expressions
don't change (see the asymmetry below).

**The parser must keep the brackets.** Today `( p )` returns `p`
(`parser.rs:946-950`) **[checked]**, so `W ({ … })` and `W { … }` are one tree
(**[run]**, §2). The parser gets a grouping node, `Pattern::Group(p, span)`
(or keeps `( record )` distinct some other way), and the pattern compiler
reads `Ctor(C, [Record …])` as named fields and `Ctor(C, [Group(Record …)])`
as a positional record argument. Elsewhere `Group(p)` means `p`. **[inferred]**

**Spelling: braces, not Lean's `(name := p)`.** Lean writes named constructor
arguments as `Term.lambda (name := n) ..` [L2] [cited], and Stitchwort
already uses `[n := k]` for implicit fields, so `Circle (id := i) ..` would
fit. It would also leave the braces' meaning alone, with no bracket rule. I
chose braces anyway:

- **Same look as records.** `{ id, start, .. }` is already how a record is
  matched; `Circle { id, start, .. }` reads as "a `Circle`, with these fields",
  and a user who knows record patterns knows this one. Rust, Haskell and OCaml
  (§3) spell it with braces too.
- **Punning.** `Circle { id, .. }` binds `id`. `(id)` already means a bracketed
  variable pattern, so a punned `:=` form would need something else, and
  `Circle (id := id) (start := start) ..` is long. Short punned patterns are the
  point of feature 1.
- **Matches the JS shape.** The value crosses as `{ tag: "Circle", id, … }`; a
  TS user's destructuring `{ id, ... }` and this pattern look alike.
- **The cost is small**: one existing pattern changes, and the parser keeps one
  grouping node. The user's preference for mainstream (Scala/TS) surface
  style also points to braces (Scala 3.7's `City(name = n)` is the other
  mainstream option, and Stitchwort's brackets are for application).

`(name := p)` stays a reasonable later addition for mixing named and positional
arguments in one pattern, which braces don't do.

**Patterns and expressions differ, for now.** In an expression,
`Some { value = n, fits = h }` is still `Some` applied to a record literal
(about fifteen uses, §2), and so is `show`'s output. So `C { f = x }` names
`C`'s fields in a pattern but builds a record argument in an expression. This
is a known learning cost of the first version; the error notes say it (a
pattern `C { … }` whose names are those of `C`'s record argument's fields gets
"`C`'s fields are `…`; to match its record argument write `C ({ … })`"). How
named **construction** should be spelt later is D605 ([§11](#11-decisions-for-the-user)):
the natural choice is the same rule in expressions (braces after a constructor
name its fields; `Some ({ value = n, fits = h })` for a record argument), which
would end the asymmetry at the cost of those fifteen expressions and
`show`'s format. Settling it now means the pattern grammar is chosen knowing
where expressions are going.

Whitespace as the discriminator (`Circle{ id }`) stays rejected: too easy to
misread.

### 4.3 Navigation

Each field name in `C { f = … }` notes a use of `C`'s field `f`, so hover shows
its type and go-to-definition goes to the field's binder in `C`'s declaration.
Records note fields through `note_field` (`nav.rs:365`), which today targets the
generated projection's span, the whole type (`records.rs:74`, `span =
data.span`) **[checked]**. Per-field spans of constructor binders have to be
kept for this (the parser has them; whether the elaborator stores them per
field I haven't checked).

### 4.4 As built (feature 1)

Built as 4.1 to 4.3 say, with these choices where the note left room or
didn't match the code:

- **No grouping node.** Instead of `Pattern::Group`, the parser decides:
  wherever a constructor takes arguments (arms, `match`, `let`, tuples,
  lists, brackets, after a field's `=`), braces right after it give a new
  node `Pattern::CtorFields { ctor, fields, rest, span }` (`ast.rs`,
  `Parser::ctor_args`), and `C ({ … })` stays `Ctor(C, [Record …])`, since
  the record pattern inside brackets is parsed as an ordinary argument. The
  two are distinguishable without the elaborator ever seeing brackets.
- **A record pattern as a later argument needs brackets too.**
  `MkEntry r { name, .. }` is `E-PARSE` ("a record pattern as an argument of
  `MkEntry` is written in brackets"), so every positional record argument is
  bracketed, not just the first. Nothing in the repository wrote one.
  `C { … } p` is `E-PARSE` with the note to write `C ({ … }) …` (4.1).
- **Elaboration** (`records.rs`, `ctor_fields_pattern`): the constructor is
  found by name (the matched type isn't needed, unlike a record pattern); the
  result is the positional pattern for the explicit fields, and
  `ctor_pattern_args` then fills implicit fields with `_` as for any
  positional pattern. `C { }` and `C { .. }` are allowed (`C {}` in Haskell).
- **Errors.** Unknown name: `E-UNKNOWN-FIELD`, "`Circle` has no field
  `colour`", noting "`Circle`'s fields are `ref`, `id`, `text`"; with the
  4.2 note added when the constructor has one field holding a record that has
  every name given. An implicit field's name: `E-UNKNOWN-FIELD`, "`n` is an
  implicit field of `VCons`", noting the positional `VCons [n := p] …`. A
  field given twice, or left out without `..`: `E-RECORD-FIELD`, as for
  records, the latter naming the constructor.
- **The §12.3 warning** is `W-RECORD-ARGUMENT`: braces after a one-field
  constructor whose field's type (at the matched type) is a record having
  every field named, as in `Some { value = n, .. }` on an `Option Item` whose
  `Item` has a `value`. The pattern keeps its meaning (`Some`'s field).
- **Navigation.** The walk records each constructor field's binder span by
  the constructor's span (`field_spans`, as for records); a field name in
  `C { f = … }` is noted against the constructor, and the index turns it into
  a `field` symbol at the binder, named `T.C.f`, whose type is the field's
  declared type in terms of the parameters and earlier fields (`Nat`,
  `Vec a n`). So the per-field spans 4.3 asked about come from the syntax
  walk; the elaborator needn't store them.
- **Existing code.** Only `examples/accept/records.sw:32` changed, to
  `Cons ({ lead = { name, .. }, .. }) rest` (grep of every `.sw` file,
  including `aoc/`, `std` and the docs' snippets). Hashes of existing code
  don't change.

Examples: `examples/accept/ctor-field-patterns.sw`;
`examples/reject/ctor-fields-*.sw` and `ctor-record-argument-unbracketed.sw`,
which include acceptance case 1 (the bracketed form becomes `E-ARITY` once
`W` gains a field) and coverage equal to the positional form
(`ctor-fields-nonexhaustive.sw`, and `sameStart` by `rfl` in the accept
example).

## 5. Feature 2: shared-field access

### 5.1 Which fields are shared

Per constructor, map each field name to its position. A field name `f` is
**shared** by data type `T` (with parameters `ps`) when:

1. **Every constructor** of `T` has an **explicit** field named `f`. An
   implicit field `[n: Nat]` doesn't count. A type with no constructors has no
   shared fields.
2. **Dependencies are shared.** In each constructor, the fields that `f`'s
   declared type mentions (D603: syntactically, 5.1.2) are only explicit
   fields that are themselves shared. Parameters may be mentioned freely; a
   constructor's own other fields and implicit fields may not. The
   dependency graph is the union over constructors of "`f` mentions `g`". If
   it has a cycle through `f`, `f` isn't shared. **Constructors may declare
   shared fields in different orders**, as long as each telescope is itself
   well formed: `| A (x: Nat) (label: Text)` and `| B (label: Text) (x: Nat)`
   share both; `| A (n: Nat) (xs: Vec Nat n) (label: Text)` and
   `| B (label: Text) (n: Nat) (xs: Vec Nat n)` share all three.
3. **Same type.** Take the shared fields in a deterministic topological order
   of that graph (ties broken by the first constructor's declaration order).
   For each `f` in turn, in a context of the parameters and one variable per
   earlier shared field, each constructor's declared type for `f`, with its
   dependencies mapped to those variables by name, is **the same type** in
   every constructor: equal by the kernel's conversion with the parameters
   and the variables rigid. So `List a` and a nickname for it agree, as in
   Haskell's "same after type synonym expansion" [H1]; `Nat` and `Int` don't.
4. **Elimination is allowed**: `T` is in `Type` (or higher), or `T` is a
   proposition and `f` is a proof field (its type is a proposition), by the
   rule records already follow (`E-PROP-ELIM`, `records.rs:83`)
   **[checked]**.
5. **Failures propagate.** A field whose type mentions a field that fails any
   rule fails too (rule 2 says this for "not shared"; it applies equally to
   failing 3 or 4). Records already propagate this way: a field whose type
   mentions a field with no projection gets none (`records.rs:82`)
   **[checked]**.

The generator then defines `T.f` for each shared field in that topological
order, so an earlier one is available for a later one's type (5.2).

Cases, checked against the rule **[inferred]** except where marked:

| Situation | Shared? |
|---|---|
| `id: Text` in every constructor | yes, `Shape.id: Shape -> Text` |
| `label: a` in every constructor of `Shape (a: Type)` | yes, `Shape.label: [a] -> Shape a -> a` |
| `n: Nat` and `xs: Vec Nat n` in every constructor | both: `T.xs: (x: T) -> Vec Nat (T.n x)`, the records' trick |
| the same, declared in different orders in different constructors | both, generated `n` then `xs` |
| `xs: Vec Nat len` where `len` is in one constructor only | `xs` isn't; `n` and the rest may be |
| `id: Text` in two constructors, `id: Nat` in a third | no |
| `ok: start <= stop` (a proof) where `start`, `stop` are shared | yes, a proof accessor, erased in JS |
| `ok: start <= limit` where `limit` is one constructor's own field | no |
| `xs: Vec Nat n` where `n` is shared but ineligible | no (propagation) |
| a field whose type mentions an implicit field (`x: Fin n` in `VCons`) | no |
| `type Evidence (q: Prop): Prop = \| A (witness: q) \| B (witness: q)` | `Evidence.witness: [q] -> Evidence q -> q`: a proof out of a proof, allowed |
| `type Claims: Prop = \| A (p: Prop) (witness: p) \| B (p: Prop) (witness: p)` | neither. `p` stores a proposition as a *value* (its type `Prop` lives in `Type`), so it isn't a proof field and can't be taken out of a proposition (rule 4); `witness` mentions `p` (rule 5) |

The last two rows behave this way for one-constructor records today:
`e.witness` on `type Evidence (q: Prop): Prop = { witness: q }` checks;
`c.p` and `c.witness` on `type Claims: Prop = { p: Prop, witness: p }` are both
`E-PROP-ELIM` **[run]**. (Today's message for `witness` says "`witness` is
data", which is wrong for a proof field whose type mentions `p`; the variant
version should say "`witness`'s type mentions `p`, which can't be taken out of
a proof".)

Nothing is reported when a name isn't shared: a type may have same-named
fields with different types on purpose. The explanation comes at a use (5.3).

#### 5.1.2 Scope: indexed families, universes, "mentions"

**Indexed families** get accessors for fields that satisfy the same uniform
rule, with the indices taken implicitly (`T.f: [ps] [is] -> T ps is -> F`
where `F` mentions only parameters and shared fields). **Inferring an
accessor's result type from what each constructor's indices say is not
included.** Two total accessors are therefore left out:

```
type Box: Type -> Type =
  | N (value: Nat): Box Nat
  | B (value: Bool): Box Bool
```

`Box.value: [a: Type] -> Box a -> a` would be total, but `Nat` and `Bool`
aren't the same type in the common context, so rule 3 refuses it. (Writing it
by hand would also hit the kernel's rule that type formers are never taken
apart in index unification, `E-INDEX-STUCK`, `docs/core.md:124` **[checked]**.)
Likewise, if each constructor of an indexed family has `[n: Nat] (xs: Vec Nat n)
: Fam n`, an accessor `Fam.xs: [n] -> Fam n -> Vec Nat n` is possible in
principle, but `xs` mentions an implicit field, so rule 2 refuses it. Widening
this later needs one well-typed motive for the whole accessor, not only
branches that are each fine (the review's caution); "unify the indices in
each branch" isn't enough.

**Universes and higher-kinded parameters** need nothing special. Stitchwort's
universes are fixed levels, `Sort::Type(u32)`, with no universe variables
(`term.rs:22`) **[checked]**, so there is no level to instantiate. Parameters
such as `(f: Type -> Type)` or `(a: Type 1)` keep their binders in the
accessor's type, and in rule 3 they're rigid variables: conversion must never
instantiate a parameter to make two constructors' types agree. The kernel's
conversion compares values and doesn't solve unknowns, so this holds as long
as the generator compares with the kernel's `conv` (`value.rs:1551`), not the
elaborator's unifier **[inferred]**.

**"Mentions" is syntactic (D603).** A field type can mention a constructor's
own field and yet reduce to a type that doesn't, say `Ignored len` with
`def Ignored (n: Nat): Type := Nat`. I recommend the syntactic reading, on the
declared type as elaborated (not normalised): `Ignored len` mentions `len`, so
the field isn't shared. Reasons: it's what records already mean by "mentions"
(`Term::mentions`, `term.rs:444`, used for projections at `records.rs:82` and
for `E-RECORD-UPDATE` at `records.rs:492`) **[checked]**, so one word means one
thing across features; a user can see it in the declaration; it never runs
out of budget (no reduction), so it adds no "inconclusive" outcome (§12.1);
and the fix is easy (write `Nat`). A reduced reading would find more accessors,
and could be adopted later without breaking programs, since it only adds
accessors (an added accessor can collide with a written `T.f`, though: §12.1).

### 5.2 Elaboration: a generated function

For each shared field, the elaborator generates **`T.f`**, an ordinary
transparent definition by one `Case` with a branch per constructor, each
returning that constructor's field:

```
Shape.id: Shape -> Text
  | Dot _ id _         => id
  | Circle _ id _ _    => id
  | Polygon _ id _ _ _ => id
```

It's registered as a member of `T`'s namespace exactly as a record's projection
is (`records.rs:74` registers `R.f` with `mark_member`) **[checked]**. So,
with no change to dot notation **[inferred]** from `dot.rs:321`:

- `a.id` is `Shape.id a`;
- `shapes.map .id`, `a |> .id` and `Shape.id` written in full work;
- chained access works (`a.start.toText`).

**One generation path.** Records' `projections` (`records.rs:74`) becomes the
one-constructor case of this generator, so a record's fields aren't generated
twice and records and variants can't drift apart **[inferred]**.

**Why a function rather than a `match` at each use:** the function has a name,
so goals show `Shape.id a` (or `a.id` once messages print projections that
way); a lemma can state facts about it; hover and go-to-definition have
something to point at; and it's what records do. A `match` at the use site
would be a different anonymous helper at every use, which a proof can't name
([equation-lemmas.md §0](equation-lemmas.md)) **[checked]**.

**Typing dependent shared fields.** As record projections: in the type of
`T.xs`, an earlier shared field `n` is `T.n x`. In each branch the expected
type `Vec Nat (T.n x)`, refined by the constructor, becomes `Vec Nat (T.n (C …
n …))`, which reduces to `Vec Nat n`, so returning the stored `xs` checks. This
is what `Sized.ok` relies on today **[checked]**, and it needs neither proof
irrelevance nor eta for variants (the review agrees).

### 5.3 Errors

`a.f` where some constructors have `f` but `f` isn't shared: first ordinary
member lookup (a written `T.f` is a valid dot-call target whether or not `f` is
a field), and only if that finds nothing, `E-UNKNOWN-FIELD` with a note saying
why, instead of today's "has no field or function":

```
`Shape` has no shared field `text`
note: only `Circle` has `text`; match on `a` to read it: `| Circle { text, .. } => …`
```

or "`id` is `Text` in `Dot` and `Circle` but `Nat` in `Polygon`", or
"`xs`'s type mentions `len`, which only `Circle` has", or "`xs`'s type mentions
`n`, which isn't shared: …" (propagation, naming the root cause).

### 5.4 Names and clashes

`T.f` is a member of `T`'s namespace, written in full as `Shape.id`.

- **`f` shared:** a user's own `def Shape.id` is `E-DUPLICATE`, as for
  records ([§2](#2-stitchwort-today)), with a note that `id` is a shared field.
  A program that wrote the getter by hand (as in §1) deletes it.
- **`f` not shared** (same name, different types, or not in every
  constructor): there's no generated `T.f`, and a written `def T.f` is
  allowed, and found by dot notation as usual. The library index must not
  reserve the name early (§12.1).

Constructors are uppercase and fields lowercase, so `T.f` never clashes with a
constructor. Field names already belong to the type's hash
([§9.6](#96-hashes)).

Automatic generation means a type's shared field labels are part of its public
API: renaming a field in one constructor removes an accessor. That's logically
safe (every accessor is total) but it can take, or give back, a member name.
Deterministic duplicate checking and the notes above are the first version's
answer; tooling shows generated members (hover, completion, §9.3) so they
aren't invisible.

### 5.5 Proofs

- **Computation.** `(Circle 1 "a" 0 "t").id` is `"a"` by `rfl`: the accessor's
  `Case` computes on a constructor, so `T.f (C … v …) = v` holds by reduction.
- **On an unknown value** `a.id` stays `Shape.id a`, as any function on an
  unknown does. A proof that needs to see through it splits `a`, after which
  each branch's `a.id` computes. That is the normal proof style already; no new
  lemmas are needed.
- **Equation lemmas.** None generated (as for record projections and per
  D231, [equation-lemmas.md](equation-lemmas.md)) **[checked]**. Generated
  equations could later help a simplifier; they aren't a prerequisite.
- **No eta.** Records' stage 2 eta doesn't apply: a variant isn't determined by
  its shared fields.

## 6. Feature 3: shared-field update

### 6.1 Syntax and rules

`{ a | start = t }` with `a: Shape` gives the same constructor with
`start` replaced; several fields may be given, `{ a | start = t, ref = 0 }`.

- Every field named must be **shared** (5.1). A field only some constructors
  have is `E-UNKNOWN-FIELD` with the note from 5.3, suggesting a `match`.
- **Dependency closure.** For each constructor, the fields that must be
  replaced are the smallest set that contains the named fields and contains
  every field of that constructor's **whole telescope**, explicit or implicit,
  data or proof, whose type mentions a field in the set. It's transitive:
  replacing `n` forces `xs: Vec Nat n`, which forces `ok: Valid xs`. The update
  is allowed only if, in every constructor, every field in that set is named by
  the user. A forced field that's shared is just one the user must also give
  (`{ x | n = 3, xs = …, ok = … }`); a forced field that's one constructor's
  own, or implicit, can't be given through this syntax, so the update is
  refused, naming the constructor and the chain:

  ```
  error[E-RECORD-UPDATE]: `n` can't be updated on every `Labelled`
  note: in `A`, the implicit field `h: n = 0` mentions `n`
  ```

  for

  ```
  type Labelled =
    | A (n: Nat) [h: n = 0] (label: Text)
    | B (n: Nat) [h: n = 0] (label: Text)
  ```

  where `n` and `label` are shared (accessors exist) but `{ a | n = 1 }` is
  refused and `{ a | label = "x" }` is fine. Records' check (`records.rs:487`)
  refuses any kept field that mentions a replaced one, which is the same as
  requiring this set to be closed **[inferred]**; variants apply it per
  constructor, over implicit fields too.
- **Proofs count.** Stitchwort has no definitional proof irrelevance: "two
  different proof terms aren't automatically equal" (`docs/core.md:139`)
  **[checked]**. A replaced proof field can make a later field's type wrong (if
  that type mentions the proof), so proof fields are in the closure like any
  other. Running erases proofs; checking doesn't.
- **The result type** is `a`'s type. For indexed families (`T ps is`),
  updates are left out: a replaced field could be one an index is computed from
  in some constructor. A later extension has a clean criterion (the review's):
  after substitution, every rebuilt constructor application must have the
  original result type, indices included, by conversion; "the closure doesn't
  occur in the constructor's result indices" is a sufficient check. It must use
  the closure, not just the fields the user named. Access (feature 2) has no
  such problem.

### 6.2 Elaboration

The review's example shows what's needed:

```
type Sized =
  | A (n: Nat) (xs: Vec Nat n)
  | B (n: Nat) (xs: Vec Nat n)

def replaceXs (a: Sized) (ys: Vec Nat (Sized.n a)): Sized := { a | xs = ys }
```

In `A`'s branch the rebuilt `A n ys` needs `ys: Vec Nat n`, but `ys` has type
`Vec Nat (Sized.n a)`. A primitive eliminator that only refines the goal would
reject it; the review's fix abstracts the replacement into the case's motive:

```
(case v return (Vec Nat (Sized.n v) -> Sized) of
   | A n oldXs => newXs => A n newXs
   | B n oldXs => newXs => B n newXs) w
```

and for several replacements, a telescope of them (`(z => (n': Nat) ->
Vec Nat n' -> … -> T)`).

**Stitchwort's `match` already does this**, so the update is elaborated as a
`match` and the motive is never built by hand. The kernel's `case` is a case
tree on a *variable*, and in each branch it substitutes the constructor for
that variable in the types of **every** variable in scope, not only the goal
(`check.rs:653-662`; `substitute` at `check.rs:1073`) **[checked]**. A lifted
`match` turns everything it uses into the helper's parameters, ordered by
their types' dependencies (`lift.rs:15-23`) **[checked]**, so the helper for
`replaceXs` is, in effect,

```
replaceXs.%match1 (v: Sized) (w: Vec Nat (Sized.n v)): Sized :=
  case v of
    | A n _ => A n w        -- here w: Vec Nat n
    | B n _ => B n w
```

whose parameter list *is* the review's motive telescope. When the base is an
expression, `match` generalises it: occurrences of the expression in the
types of variables in scope are replaced by the new scrutinee variable
(`matching.rs:321` `generalised`) **[checked]**. The `pick b a` example in §2
checks today, and its negative control shows `ys` refined to `Vec Nat n`
**[run]**. Draft 1's "annotated lambda around a `Case`" was not possible: the
kernel refuses `case` anywhere but the top of a definition or of a branch
(`check.rs:1208`, `check.rs:1984`) **[checked]**.

The translation, for `{ base | f₁ = e₁, …, fₖ = eₖ }` on `T` (pure code; §6.3
for effects):

1. Check that every `fᵢ` is shared and compute the closure (6.1) per
   constructor; refuse as there.
2. Take the replaced fields in the shared fields' topological order (5.1 rule
   3). For each, check `eᵢ` against `T.fᵢ`'s field type in which a replaced
   earlier field is its new value's variable and a kept earlier one is
   `T.g base`. Bind it: `let %fᵢ: Fᵢ := eᵢ` (hidden names, like the records'
   `%record`).
3. Elaborate `match base with | C₁ x… => C₁ … | …` through the existing
   `match` path (`matching.rs`), with one synthetic alternative per
   constructor that rebuilds it from its own fields and the `%fᵢ`. The `match`
   copies each `%fᵢ` whose type mentions the base with the base abstracted
   (let-bound variables become plain hypotheses in the alternatives,
   `matching.rs` at the `copied` loop) **[checked]**, and the kernel refines
   them in each branch.

So `base` is evaluated once (it's the scrutinee, passed to the helper once),
each `eᵢ` once (bound by `let`), and neither is copied into the branches. The
review's motive form and this one are the same term up to lifting
**[inferred]**.

What could still go wrong, and the acceptance cases cover it
([§10.4](#104-acceptance-cases)): the `match` machinery's own limits, such as
"the type of one scrutinee mentions another" (`matching.rs:351`), don't arise
with one scrutinee, but a replacement whose type mentions the base in a way the
occurrence test misses would be refused with a type mismatch rather than
accepted. Such a refusal is safe; the cases test the forms that matter.

**Records could use the same path** and would then accept `{ pick b r | xs = ys }`,
which today's records refuse (§2, **[run]**). That's D604.

**In proofs**, `{ a | start = t }.start = t` holds after splitting `a`; on a
known constructor both sides compute. The usual update laws are provable by
cases; they needn't hold by computation on an unknown value. Generated lemmas
such as `Shape.start_update` aren't proposed now.

### 6.3 Orders: dependency, written, evaluation

Three orders are in play, and the rule is records' exactly:

- **Written order** is free: `{ a | xs = newXs, n = newN }` and
  `{ a | n = newN, xs = newXs }` mean the same. Records accept this today:
  `{ r | xs = VCons 7 VNil, n = 1 }` checks **[run]**.
- **Typing order** is the shared fields' dependency order (5.1's topological
  order): `newXs` is checked against `Vec Nat newN` whichever is written first,
  because step 2 above checks replacements in that order. Records do the same
  in declaration order (`records.rs:533` `update_fields`) **[checked]**, which
  for one constructor is a dependency order.
- **Evaluation order** is observable only in a computation. There, as records
  do, the base runs first and then each replacement that performs operations,
  **in the order written**, each bound to a variable (`effects.rs:1696`
  `comp_compound`, already shared by record literals and updates)
  **[checked]**; the pure update above is then built from those variables. In
  pure code, evaluation order isn't observable.

One consequence, the same as for records: an effectful replacement is checked
as a variable holding its result, so a dependent replacement whose expected
type mentions *another* effectful replacement sees only that variable, not
its value. That's fine for the usual case (`newXs` whose type is `Vec Nat newN`
with `newN` the variable) **[inferred]**.

## 7. Before and after

Before: §1. After:

```
type Shape =
  | Dot (ref: Nat) (id: Text) (start: Int)
  | Circle (ref: Nat) (id: Text) (start: Int) (text: Text)
  | Polygon (ref: Nat) (id: Text) (start: Int) (duration: Nat) (points: List Point)

-- No getters: `a.id`, `a.ref`, `a.start` are generated.
def shiftTo (t: Int) (a: Shape): Shape := { a | start = t }

def textOf: Shape -> Option Text
  | Circle { text, .. } => Some text
  | _                   => None

def pointCount: Shape -> Nat
  | Polygon { points, .. } => points.length
  | _                      => 0

def ids (xs: List Shape): List Text := xs.map .id
def shift (d: Int) (xs: List Shape): List Shape :=
  xs.map (a => { a | start = a.start + d })
```

Adding a constructor or a field no longer touches any getter, setter or
underscore-counting pattern, **as long as the sharing and dependency
conditions keep holding**. They can stop holding: a new constructor without
`start`, or with `start: Nat`, removes `Shape.start`; a new constructor with
its own proof about `start` (`(early: start < 0)`) keeps `a.start` but makes
`{ a | start = t }` impossible (6.1's closure). Each is a compile error at the
uses, not a silent change.

## 8. The alternative: a record with a `kind` variant

The same data can be modelled today, without new features:

```
type ShapeKind =
  | Dot
  | Circle (text: Text)
  | Polygon (duration: Nat) (points: List Point)

type Shape = { ref: Nat, id: Text, start: Int, kind: ShapeKind }
```

`a.id` and `{ a | start = t }` work now, and a match reads
`| { kind = Circle text, .. } => …`. The two models are **isomorphic**: with
`B` the shared fields and `D`, `C`, `P` the kinds' own data, `(B × D) + (B × C)
+ (B × P)` and `B × (D + C + P)` carry the same information (the review's
point, and draft 1 overstated the difference). The record still says "one of
three kinds"; a function only about circles needs a separate payload type or a
refinement in either model; and in a dependently typed language a record *can*
make later fields depend on the kind, by putting `kind` first and giving a
later field type `F kind`. Nor is "fields that vary by kind" an advantage of
this proposal: shared fields must have the same type everywhere (5.1).

The reasons to prefer variants with shared fields are practical:

1. **The flat JS shape.** At the boundary the record is `{ ref, id, start,
   kind: { tag: "Circle", text } }`: nested. A TS program, an API or a stored
   document whose data is the flat union `{ tag: "Circle", ref, id, start,
   text }` (the common TS idiom, and the shape the port in §1 had to keep)
   can't be described this way; it needs a hand-written conversion on each side
   of the boundary, which defeats the codecs.
2. **Direct constructor patterns.** `| Circle { text, .. }` instead of
   `| { kind = Circle text, .. }`, and the kinds are the type's constructors,
   not a second type to name and import.
3. **No boilerplate.** The getters, setters and underscore-counting patterns of
   §1 go, without restructuring the data.
4. **Consistency with records.** `a.id`, `{ a | start = t }` and named-field
   patterns already work on records; variants get the same forms by the same
   rules.

The other route already planned, **a constructor wrapping a record**
(`| Circle CircleData`, flattened in JS per the records note's decisions)
**[checked]**, keeps JS flat, but each record repeats the shared fields, so
`a.id` still needs a hand-written getter. With D593 (b) its pattern is
`Circle ({ radius, .. })`. Shared fields *through* a wrapper aren't proposed.

## 9. Interactions

### 9.1 JS boundary codecs

**Nothing changes in the representation.** Fields already cross under their
names, so shared fields are just keys every member of the union has. TS users
can already write `a.id` on the generated union type ([§2](#2-stitchwort-today)),
so features 2 and 3 make the Stitchwort side match what the TS side allows.

- **Generated code.** `Shape.id` could compile to `x.id` without a `switch`,
  but only where the backend's *internal* representation stores every
  constructor's `id` under the same key. The codec's flat external shape
  doesn't establish that, and erased fields, escaped names (`$tag`) and special
  codecs need their normal treatment. An optional later optimisation, not part
  of this proposal.
- **Optional-field codecs (SW-339, D582).** An `Option T` shared field
  becomes an optional property in every member alike; nothing specific to
  shared fields **[inferred]**, since SW-339 works per field.
- **Choosable discriminants (later).** If a type chooses `kind` as its
  discriminant key, a field called `kind` needs the same escaping `tag` gets
  today (`$tag`, DESIGN.md §12) **[checked]**, shared or not. A shared field
  must never be used as the discriminant implicitly.
- **`.d.ts`**: optionally, a named base type (`export type ShapeBase =
  { readonly ref: bigint; readonly id: string; readonly start: bigint }`).
  Not proposed now.

### 9.2 Derived `==`, `Ord`, `Show`

Unchanged: they work constructor by constructor. `Show` keeps printing variants
positionally (`Circle 1 "a" 0 "t"`) and a record argument as today
(`Some { name = "tea", price = 3 }`); if D605 (a) is adopted when named
construction is built, the latter becomes `Some ({ name = "tea", price = 3 })`.

### 9.3 Navigation and the language server

- Hover on `a.id`: `Shape.id: Shape -> Text`, with a line "shared field of
  `Dot`, `Circle`, `Polygon`".
- Go to definition: the `id` binder in the first constructor. Find references
  could include every constructor's `id` binder.
- Completion after `a.`: shared fields listed with the type's functions.
- In `Circle { id, .. }`: the field name goes to `Circle`'s `id`.
- The printer shows `Pair.fst x` as `x.fst` through the registry, and a
  record's projections by looking for a *record* with that field
  (`pretty.rs:527` `projection_field`) **[checked]**; it needs widening to
  generated accessors on any data type.

### 9.4 Namespaces and `T.f` functions

A shared field is a member `T.f`, as a record field is, so there's one lookup:
dot notation finds `T.f` whether it's generated or written. When `f` is
shared they can't both exist (`E-DUPLICATE`, 5.4); when it isn't, the written
one is simply there. Nicknames work as today: `p: Price` with `Price = Shape`
tries `Price.id`, then `Shape.id`.

### 9.5 Existing code

No backwards compatibility is needed, but these change:

- Hand-written getters with a shared field's name (`def Shape.id` in §1)
  become `E-DUPLICATE`; delete them.
- With D594 (a), every one-constructor data type gets accessors, so the
  library's hand-written `Pair.fst` and `Pair.snd` (`std/core/Data.sw:89`)
  **[checked]** go, replaced by generated ones (checklist in §12.2), and
  `Char` gains `Char.code` and the proof accessor `Char.valid`
  (`std/core/Char.sw:15`) **[checked]**; `Char.toNat` can stay or become a
  synonym. Any other `def T.f` on a one-constructor type with a field `f`
  becomes `E-DUPLICATE` and is deleted; the lane lists them.
- Feature 1 (D593 (b)): the one pattern `Cons { lead = …, .. } rest`
  (`examples/accept/records.sw:32`) gets brackets.

### 9.6 Hashes

A data type's hash already covers its field names (records.md §12, as built)
**[checked]**, and which fields are shared is computed from the declaration,
so the type's hash doesn't change. Generated accessors are definitions hashed
like any other; an update's lifted helper is hashed like any lifted `match`.
The hash alone doesn't say which generated members a type has (that's the
elaborator's policy); the check cache handles that through its key (§12.1).

## 10. Implementation sketch, cost and acceptance cases

All in `crates/elab` plus one parser node; no kernel or JS-representation
change. Line counts are rough guesses **[inferred]**.

### 10.1 Feature 1: small

About 30 lines in the parser (`Pattern::Group` for `( p )`, transparent
everywhere but a constructor's argument) and 80 in `pattern_ctor`'s
`Pattern::Ctor` branch (`lib.rs:2814`): when the arguments are exactly one
ungrouped `Pattern::Record`, build the `CtorPattern` from the named fields
(generalise `record_pattern`, `records.rs:243`, to take a `(DataId, ctor)` and
skip implicit fields; reuse `check_field_names`). Errors: the existing ones,
plus "braces take no further arguments" and the record-argument note (4.2).
Update `examples/accept/records.sw:32`. Nav: note each field name.

### 10.2 Feature 2: medium; the risk is eligibility and loading

- **Generation (easy, ~100 lines).** Generalise `projections`
  (`records.rs:74`) from one branch to one per constructor; records become its
  one-constructor case.
- **Eligibility (~150 lines, moderate).** After a data group is admitted: per
  constructor, names to positions; the dependency graph (syntactic mentions);
  topological order; comparison with the kernel's `conv`, parameters and
  earlier shared fields as rigid variables; rule 4; propagation; keep *why* a
  field failed, for 5.3's notes. A budget error from `conv` is propagated as an
  error, never read as "not the same" (§12.1).
- **Loading, cache, registry, printer (~200 lines, the main risk).** The
  candidate index and its resolution (§12.1); a side table of shared fields
  and failure reasons in the check cache's entry (format bump); binding
  generated `Pair.fst`/`Pair.snd` in the registry (§12.2); the printer (9.3);
  the dot lookup's unknown-member error (`dot.rs:594`).

### 10.3 Feature 3: medium; the risk is the dependent case

Generalise `update` (`records.rs:477`): for a non-record data type, check
names and the per-constructor closure, check and `let`-bind replacements in
dependency order, then elaborate a synthetic `match` through `matching.rs`
(6.2), about 150 lines. Using `match` keeps the dependent typing in code that
already handles it; the remaining risk is the forms the occurrence test might
miss, which the acceptance cases probe. Refuse indexed families. If D604 is
adopted, records' `update` moves to the same path.

### 10.4 Acceptance cases

The design is complete when these pass, in addition to draft 1's (the 5.1
table as accepts/rejects, `rfl` on constructors, a proof by cases, `.id`
sections, a parameterised type, the before/after example, coverage of
named-field patterns equal to the positional form). The first eleven are the
review's [cited], in Stitchwort terms:

| # | Case | Expected |
|---|---|---|
| 1 | `W { person = { name, .. }, .. }` and `W ({ name, .. })` on `W (person: Person)`; then add `(name: Text)` to `W` | the first keeps reading `person.name`; the second becomes `E-ARITY`; nothing changes meaning silently |
| 2 | `\| A (x: Nat) (label: Text)` and `\| B (label: Text) (x: Nat)` | `T.x` and `T.label` both generated |
| 3 | `{ a \| xs = ys }` with `ys: Vec Nat (Sized.n a)`, keeping `n`; also with a base that isn't a variable | accepted (6.2) |
| 4 | Replace `n` where `xs: Vec Nat n` and `ok: Valid xs` are shared | closure reaches all three; giving only `n`, or `n` and `xs`, is `E-RECORD-UPDATE` naming the next link |
| 5 | `Labelled` (6.1): replace `n` used by the implicit `[h: n = 0]` | refused, naming `A` and `h`; `{ a \| label = … }` accepted |
| 6 | `Evidence (q: Prop): Prop` with `witness: q` in two constructors | `Evidence.witness` generated |
| 7 | `Claims: Prop` with `(p: Prop) (witness: p)` in two constructors | no `Claims.p` (no data out of a proof) and no `Claims.witness` (propagation) |
| 8 | `\| A (id: Nat) \| B (id: Text)` plus a written `def T.id` | the written `T.id` works, by dot call too; no `E-DUPLICATE`; same in a library file loaded lazily |
| 9 | A program whose first use of `Pair.fst` is from tuple lowering (`let (x, y) := p`) | the accessor is found through the registry; output prints `p.fst` |
| 10 | Cold load vs cached load of a library file with shared fields, and different first demands (`T`, `T.f`, a constructor, another member) | the same generated members, diagnostics and name resolution in every case |
| 11 | `{ base() \| b = next(), a = next() }` on a variant in a computation | base once, then replacements once each, in the order written |
| 12 | `Box: Type -> Type` with `value: Nat` / `value: Bool` (5.1.2) | no `Box.value`; the note says the types differ |
| 13 | `label: Ignored len` (`Ignored n` reduces to `Nat`) with `len` in one constructor | not shared (D603's syntactic reading) |
| 14 | A shared-field comparison that runs out of budget | a resource error at the declaration, not a missing accessor |

## 11. Decisions for the user

**Decided (23 October 2026):**

- **D593 (b).** Braces after a constructor in a pattern always name its
  fields; a record pattern as a positional argument is written `W ({ … })`.
  Spelling: braces, not `(name := p)` (4.2).
- **D594 (a).** Accessors for every data type by the one rule, including
  one-constructor types (`Pair`, `Char`); hand-written `Pair.fst`/`Pair.snd`
  are deleted.
- **D595 (b).** A bare `{ id, .. }` matching a variant is deferred. A
  binding-only form would be irrefutable, but the record-pattern grammar also
  allows refutable sub-patterns (`{ n = Zero, .. }`), which need their own
  translation, coverage and dependent-refinement rules; and such a pattern
  names no constructor, unlike `Circle { id, .. }`. It needs its own
  specification, not "small once feature 2 exists" (draft 1's claim,
  withdrawn).

**Open:**

**D603. What does "a field's type mentions a field" mean for eligibility?**
(a) **Recommended:** syntactically, in the declared type as elaborated, as
records already mean it (`term.rs:444`): `label: Ignored len` mentions `len`
even if `Ignored len` reduces to `Nat`. Predictable, never runs out of budget,
one meaning across records and variants.
(b) After reduction: finds more accessors, at the cost of a reduction per
field (which can run out of budget) and of availability depending on how
definitions compute.

**D604. Should record update use variant update's translation?**
(a) **Recommended:** yes, in the feature 3 lane: records' `{ e | … }` becomes
a `match` on `e` like variants', so `{ pick b r | xs = ys }` with
`ys: Vec Nat (pick b r).n` is accepted (refused today, §2). One update path;
no program that checks today stops checking **[inferred]**.
(b) No: records keep their inline constructor-of-projections term, and the
two differ in that case.

**D605. How will named construction be spelt, when it's built?** (Not built
now; settled so the pattern grammar fits.)
(a) **Recommended:** the same rule as patterns: `Circle { ref = 1, id = "a",
… }` names `Circle`'s fields in an expression too, and a record argument is
`Some ({ value = n, fits = h })`. Patterns and expressions then agree; about
fifteen existing expressions and `show`'s format change.
(b) Expressions keep braces as the record argument permanently, and named
construction, if ever, gets another spelling (such as Lean's
`Circle (ref := 1) …`). No existing code changes; the asymmetry stays.

## 12. Risks, and lazy loading

### 12.1 Lazy loading: candidates, then confirmation

The library's index lists every name a file declares, generated ones included,
from source text, and enters each as a pending name in the one name table;
resolution and dot notation read that table and never depend on what's loaded
(`library.rs:1-27`) **[checked]**. It already lists record fields as members
(`library.rs:500-528`) **[checked]**. Whether a variant's field is shared
depends on types (rule 3), which the source text can't decide. So:

1. **Index candidates by name.** For each data declaration, a field name
   present as an explicit field in every constructor is a *candidate* `T.f`,
   indexed with a reference to its owner `T`. A candidate is marked as such,
   distinct from a declared name.
2. **A candidate forces its owner.** Any lookup that reaches a candidate
   (`T.f` written in full, or a dot call `x.f` that names `T`'s file) loads the
   owner's file, as references to pending names already do, and then resolves
   again.
3. **Elaboration confirms.** Admitting `T` computes the final set of shared
   fields (5.1). A confirmed `f` replaces the candidate with the generated
   definition, and ordinary duplicate checking applies (a written `T.f` in the
   same file is then `E-DUPLICATE`). An unconfirmed candidate is removed.
4. **A written `T.f` wins when `f` isn't shared.** The index lists both a
   written `def T.f` and a candidate for the same key without complaint; after
   loading, only the written one exists, and no duplicate error is raised.
5. **Demand-order independence.** The outcome is a function of the file's
   contents only: whatever is demanded first (`T`, `T.f`, a constructor or an
   unrelated member), the owner's file is elaborated as a whole and produces
   the same set. Because a candidate always forces loading before any decision
   uses it, nothing is decided from a candidate that later disappears.
6. **Inconclusive is not "not shared".** The kernel's conversion returns a
   resource error, not `false`, when it runs out of budget (`budget.rs:5-8`)
   **[checked]**. The generator must propagate it as an error at the type's
   declaration. Three outcomes stay separate: ineligible (with a reason),
   elaboration failure, inconclusive. Otherwise which names exist would depend
   on the budget. With D603 (a) only rule 3's conversion can run out.

**The check cache.** An entry holds the kernel's definitions and the
elaborator's side tables, including names declared and record info
(`cache/mod.rs:6-14`) **[checked]**, so generated accessors come back as
definitions and names. The shared-field table (with failure reasons, for 5.3)
is a new side table: it must be written to entries, and adding it bumps
`FORMAT` (`cache/mod.rs:67`) **[checked]**. A change to the generation policy
is covered by the key, which includes the compiler build ("its version and a
fingerprint of its source", `cache/mod.rs:80-82`) **[checked]**, so an old
entry made under another policy is a miss. Replay binds built-ins through
`bind_builtin_def` (`lib.rs:2050`) **[checked]**, which must include generated
ones (12.2). Acceptance case 10 checks cold vs cached.

### 12.2 `Pair` checklist

`Pair` is declared in the always-loaded core (`std/core/Data.sw:87`)
**[checked]**, so it's never lazily loaded; but its accessors are compiler
built-ins, found by identity through the registry (`registry.rs:223`,
`Fst = "Pair.fst"`) **[checked]**. Replacing the hand-written ones must keep:

- **Registry binding.** Written prelude definitions are bound when admitted
  (`after_definition`, `lib.rs:2017`, `bind_builtin_def`) **[checked]**;
  generated projections go straight to the kernel (`records.rs:126`)
  **[checked]** and aren't bound. The generator must bind them, in the prelude
  and on cache replay, before any later prelude code uses a tuple pattern.
- **Parameters and universes.** `Pair (a: Type) (b: Type): Type`: the
  generated `Pair.fst: [a] [b] -> Pair a b -> a` has the same implicit
  parameters as the hand-written one (auto-bound implicits) **[inferred]**.
- **Receiver position.** The pair is the only explicit argument, as now.
- **Reduction.** A one-branch `Case`, as the hand-written case tree.
- **Uses.** Tuple `let` projections (`patlet.rs:180`), the printer
  (`pretty.rs:529`), the runner (`std/core/Data.sw:4` says it uses
  `Pair.fst`) **[checked]**, and 32 mentions in the library sources (by grep).
- **Test:** a program whose first use of `Pair.fst` is from tuple lowering
  (acceptance case 9).

### 12.3 Other risks

- **The pattern/expression asymmetry (D593 (b))** until D605 is built: users
  may copy an expression such as `Some { value = n, fits = h }` into a pattern,
  meaning the record argument. As a pattern it names `Some`'s fields, and
  `Option`'s one field happens to be called `value` (`std/core/Data.sw:83`)
  **[checked]**, so `fits` is `E-UNKNOWN-FIELD` and the note (4.2) says to
  bracket. The dangerous variant is `Some { value = n, .. }`, which *checks*,
  binding `n` to the whole record; usually a later use of `n` at the field's
  type then fails, but not always **[inferred]**. This only arises when a
  constructor's own field and its record argument's field share a name; the
  lane should make the pattern compiler warn when braces after a one-field
  constructor whose field is a record name a field of that record.
- **Accidental sharing.** A type whose constructors happen to share a field
  name and type gets an accessor whether or not the author meant it. Logically
  safe (total), but it takes a member name; `E-DUPLICATE` with a note says why,
  and tooling shows generated members.
- **Performance.** One generated definition per shared field per type, plus
  the comparisons; for large libraries a few more definitions to check and
  hash. Small.
- **Not proposed** and possibly asked for later: named construction (D605),
  bare variant record patterns (D595), shared fields through a wrapped record
  (`| Circle CircleData`), updates on indexed families, accessors from index
  refinements (5.1.2), generated update lemmas, the `.d.ts` base type, and the
  `x.id` optimisation.

## 13. What I couldn't verify

- Claims marked [cited] come from the review's sources, which I didn't fetch:
  GHC `HasField` on partial fields, Lean's named-argument patterns and match
  motives, Scala's abstract trait members, TypeScript's common-property union
  reads and spread semantics, Koka's accessors, C# `with` on base references,
  Idris 2's on-demand setters, Rust's field-projection rule.
- Scala: updating a shared field across cases needs a match per case.
- OCaml: no access across constructors' inline records.
- Elm's and PureScript's constructor-with-record-argument patterns; Agda's
  records.
- Whether the elaborator keeps per-field spans of constructor binders (4.3).
- That `match`'s occurrence test catches every form a replacement's type takes
  when the base is a complex expression (6.2); the acceptance cases test it.

## 14. Sources

- [R1] The Rust Reference, Patterns, Struct patterns.
  https://doc.rust-lang.org/reference/patterns.html#struct-patterns
- [R2] The Rust Reference, Struct expressions, functional update syntax; Field
  access expressions. https://doc.rust-lang.org/reference/expressions/struct-expr.html,
  https://doc.rust-lang.org/reference/expressions/field-expr.html
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
  since 3.7); Scala 3 Book, traits with abstract members.
  https://docs.scala-lang.org/scala3/reference/other-new-features/named-tuples.html
- [T1] TypeScript Handbook, Narrowing, Discriminated unions.
  https://www.typescriptlang.org/docs/handbook/2/narrowing.html
- [T2] TypeScript Handbook, Everyday Types (union types; common members).
  https://www.typescriptlang.org/docs/handbook/2/everyday-types.html
- [T3] TypeScript 2.1 release notes, object spread and rest.
  https://www.typescriptlang.org/docs/handbook/release-notes/typescript-2-1.html
- [L1] Lean Language Reference, Inductive types (structures and projections).
  https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/
- [L2] Lean Language Reference, Pattern matching (ellipses, named arguments,
  motives and generalisation).
  https://lean-lang.org/doc/reference/latest/Terms/Pattern-Matching/
- [I1] Idris 2 documentation, Types and functions (records); record
  elaboration. https://idris2.readthedocs.io/en/latest/tutorial/typesfuns.html
- [K1] The Koka Programming Language (book), structs and accessors.
  https://koka-lang.github.io/koka/doc/book.html
- [C1] Microsoft Learn, C# records (`with` expressions, inheritance).
  https://learn.microsoft.com/en-us/dotnet/csharp/language-reference/builtin-types/record
- [P1] PureScript documentation, Records.
  https://github.com/purescript/documentation/blob/master/language/Records.md
