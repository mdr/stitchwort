# Proposal: records

**Status:** draft 1, 15 October 2026. Open: nothing here is decided or
implemented. This is DESIGN.md milestone 8 ([§9](../../DESIGN.md#9-records)),
which sketches records but leaves their representation, their equality and
their JS form open.

This note is meant to be read without knowing the codebase: §1 describes the
parts of Stitchwort it touches, checked against the source at commit
`67d88e5`. Claims about other systems cite their sources ([Sources](#sources));
anything not checked against a source is marked **unverified**, and
[What I couldn't verify](#what-i-couldnt-verify) lists the gaps.

## Contents

0. [Summary](#0-summary)
1. [Background: Stitchwort today](#1-background-stitchwort-today)
2. [Goals and non-goals](#2-goals-and-non-goals)
3. [How other systems do it](#3-how-other-systems-do-it)
4. [The design axes](#4-the-design-axes)
5. [Recommendation](#5-recommendation)
6. [Stage 1: declared records, by translation](#6-stage-1-declared-records-by-translation)
7. [Stage 2: projections and eta in the kernel](#7-stage-2-projections-and-eta-in-the-kernel)
8. [Stage 3: anonymous structural records](#8-stage-3-anonymous-structural-records)
9. [Stage 4: functions over "any record with field `x`"](#9-stage-4-functions-over-any-record-with-field-x)
10. [Later, maybe: adding and removing fields](#10-later-maybe-adding-and-removing-fields)
11. [JavaScript and TypeScript](#11-javascript-and-typescript)
12. [Content hashes](#12-content-hashes)
13. [Trusted code](#13-trusted-code)
14. [Testing plan](#14-testing-plan)
15. [Questions for the user](#15-questions-for-the-user)
16. [Open questions for the reviewer](#16-open-questions-for-the-reviewer)
17. [What I couldn't verify](#what-i-couldnt-verify)
18. [Sources](#sources)

## 0. Summary

**In plain words.** A record is a bundle of named values, like
`{ name = "Alice", age = 30 }`. The plan builds records in four steps, each
useful on its own:

1. **Declared records** (`type Person = { name : Text, age : Nat }`). `Person`
   is its own type, as a `class` or `interface` name is. Fields can depend on
   earlier fields (`{ items : List Nat, sorted : IsSorted items }`), proofs
   are erased, and in JavaScript a `Person` is a plain object
   `{ name: "Alice", age: 30n }` with a matching TypeScript type. This needs
   no change to the trusted kernel: a declared record is translated into a
   data type with one constructor, which the kernel already understands.
2. **Better proofs about records.** A small kernel addition makes the
   checker know that a record is *nothing but* its fields, so
   `{ p | age = p.age } = p` is true by computation, and functions that
   take records apart never get stuck on an unknown record. Lean, Agda and
   Rocq all have this rule ("eta for records").
3. **Anonymous records** written straight into a type,
   `divMod : Nat -> Nat -> { quotient : Nat, remainder : Nat }`, with no
   declaration. Two anonymous record types with the same fields are the
   same type, whatever order the fields are written in.
4. **Functions over any record with a field**:
   `greet : { name : Text | r } -> Text` accepts a `Person`, an `Employee`,
   or an anonymous record, as long as it has a `name : Text`. It may read
   fields and update them, but not add or remove them. Elm made the same
   choice; adding and removing fields is left for later, if ever needed.

At the JavaScript boundary, none of this needs stage 4: a decoder already
ignores extra properties, so an export taking a `Person` accepts any object
with at least `name` and `age`.

**For the reviewer.**
- Stage 1 is an encoding: a nominal record is a single-constructor,
  parameterised data type with named fields; projections are generated
  case-tree definitions. The kernel is unchanged apart from hashing field
  names.
- Stage 2 adds primitive projections `Proj(D, i, t)` and **eta for
  non-recursive records in `Type`**, implemented as in Lean 4's kernel:
  untyped one-sided eta in conversion (a constructor of `D` against a
  neutral compares fieldwise with projections), and a `Case` on a neutral
  of such a type takes its only branch with projections as fields
  (Lean's `toCtorWhenStructure`). The justification is the standard
  model of Σ with surjective pairing, and Abel and Coquand's untyped
  algorithmic equality for it [P1]; the restriction to non-recursive
  records follows Lean [L3] and Agda's default [A1], and is what keeps
  unfolding terminating.
- Stage 3 interns each anonymous record type as a canonical generated data
  type keyed by its **sorted label set** (and the universe levels of its
  fields), parameterised by the field types. Equality up to field order then
  is ordinary conversion. Two kernel changes: such types are hashed by
  their labels rather than a module and name (Dhall's canonical sorted
  encoding [H1] is the precedent), and positivity looks through them,
  which is safe because their fields are exactly their parameters.
- Stage 4 is Ohori-style "kinded" record polymorphism [R4], compiled by
  evidence passing: `{ name : Text | r }` elaborates to a type variable `r`
  with a constraint `Has.name r Text` whose evidence is a getter and a
  setter, found the way `auto` finds proofs. No rows or lacks predicates
  in the kernel. It doesn't support extension or restriction, so the
  existing ability rows' unenforced lacks constraints and declaration-order
  canonicalisation (`TODO.md`) don't arise for records.
- Dependent fields are allowed only in declared records. Anonymous records
  and `Has` constraints are non-dependent, as DESIGN §9 already separates
  them.

## 1. Background: Stitchwort today

Stitchwort is a small, strict, pure, total, dependently typed language
written in Rust. A large elaborator (`crates/elab`) turns surface syntax into
a small core, which a separate kernel (`crates/core`) re-checks. Only the
kernel is trusted. Checked programs extract to JavaScript (`crates/js`), whose
main use is library functions called from a JS/TS application, so idiomatic
objects and accurate `.d.ts` files matter a lot.

What records will touch:

- **Core terms** (`crates/core/src/term.rs`, [docs/core.md](../core.md)):
  variables, `Def`, `Data(D, params)`, `Ctor(D, c, fields)`, universes,
  `Pi`/`Lam`/`App`, `Case`, `NumCase`, equality with `J`. **There is no
  projection term.** The only way to take a value apart is `Case`, and a
  `Case` may only appear at the top of a definition's body, on a variable,
  forming a case tree (so there's no `match` expression).
- **Data types** have parameters but no indices. Each constructor's fields
  form a telescope: a field's type may mention the parameters and earlier
  fields. Each field already has a name (`Ctor::fields : Vec<(Name, Term)>`
  in `globals.rs`). Strict positivity is checked, and nested occurrences
  (`List D` inside `D`) are refused for now (`TODO.md`, "Nested recursive
  types").
- **Conversion** (`value.rs`, `conv`) is untyped normalisation by evaluation.
  It has eta for functions, and for partially applied definitions, but no
  eta for data types. Neutral terms are a head with a spine of applications
  and `J`s.
- **Unfolding.** A definition applied to all its arguments unfolds only if
  its case tree can take a step all the way to a leaf, so `length xs` with
  unknown `xs` stays folded. That's what keeps conversion terminating.
- **Termination** is size-change: an argument is `<` a parameter if it was
  bound as a field of a `Case` on that parameter (or on something smaller),
  `≤` if it is the parameter, and unknown otherwise ([docs/core.md
  §Definitions](../core.md#definitions)).
- **Admission** ([kernel-admission.md](kernel-admission.md)): each
  declaration is pending, final or failed, and may only refer to final ones.
  Mutually recursive data types are coming ([mutual-recursion.md](mutual-recursion.md)
  §7), as groups that share one parameter telescope.
- **Ability rows** (`crates/elab/src/effects.rs`,
  [abilities.md](abilities.md)) are the language's only row polymorphism
  today, and are purely an elaboration device. `{A, B | e}` becomes a chain
  of `Plus`es in the core, sorted by the abilities' declaration order, ending
  in `NoOp` or in `sigOp e` for a row variable `e : Sig`. Rows in different
  orders are related by explicit, kernel-checked coercions (`SigMap`,
  `translate`). Two known issues (`TODO.md`): **"lacks" constraints on row
  variables aren't enforced** (only reachable with a hand-written `Sig`), and
  **row order is fixed by declaration order**, so `IO` (declared in the
  prelude) always sorts first.
- **Hashes** (`crates/core/src/hash.rs`). Data types are nominal: a data
  type's hash covers its name, universe, parameters, its constructors' names
  and its field *types*, but **not its field names**.
- **JavaScript** (`crates/js/src/lib.rs`, DESIGN §12). Every data value is
  an object with a `tag` (`{ tag: "MkPair", fst: …, snd: … }`), erased
  fields omitted. Decoders read only an object's own properties, read each
  property once, **ignore extra properties**, and refuse arrays where an
  object is expected. A field's key is its name with each prime written `$`,
  and a field called `tag` or `__proto__` gets a `$` in front.
- **Syntax** ([docs/syntax.md](../syntax.md)). There's no `.` token yet.
  `{` after an arrow starts an ability row; DESIGN §4 reserves `{ name : Type }`
  (top-level entries of that form) for record types. Implicit arguments are
  `[x : A]`, supplied by name as `[x := e]`; `[auto x : P]` is found from
  explicit evidence, a hypothesis in scope, or a decision procedure.

## 2. Goals and non-goals

**Goals**

- **Writing records is pleasant.** Literals `{ name = "Alice", age = 30 }`,
  access `p.name`, update `{ p | age = p.age + 1 }`, punning `{ name, age }`,
  and record patterns.
- **Records look like records in JS and TS.** A record is a plain object
  with its fields as keys, no `tag`; the `.d.ts` says exactly what's accepted
  and returned. This is the main use case.
- **Data bundled with its guarantees.** DESIGN's `SortedList`: later fields
  may depend on earlier ones, proof fields are erased, and an update must
  re-establish them.
- **Proofs about records are easy.** Facts that are "obviously" true about
  records hold by computation where Lean, Agda and Rocq make them hold.
- **Structural, row-polymorphic records**, from the project's original goals:
  record types that need no declaration, and functions over any record with
  at least certain fields.
- **The kernel stays small**, and every addition to it is justified the way
  [kernel-admission.md](kernel-admission.md) and
  [number-patterns.md](number-patterns.md) justify theirs.

**Non-goals (for now)**

- Adding or removing fields (`{ p with email = … }` producing a wider type),
  record concatenation, first-class labels (Ur/Web's `#name` values [R6]).
- Subtyping between record types. Width subtyping is what TypeScript does
  [T1]; here, stage 4's constraints play that role inside Stitchwort, and
  decoders ignoring extra properties play it at the boundary.
- Inheritance (`structure B extends A`, Lean [L1]), manifest fields
  (Pollack [P2]), copatterns (Agda [A1]), coinductive records.
- Optional fields (`age?: bigint`) at the boundary; see question U5.

## 3. How other systems do it

### 3.1 Records in dependently typed languages

**Agda** [A1]. A `record` declaration is a data type with one constructor
plus a module of projections, usable prefix (`Person.name p`) or postfix
(`p .name`). "Record types enjoy η-equality by default … with the exception
of coinductive records", and keywords `eta-equality`/`no-eta-equality`
override it. For recursive records, "η-equality is not always safe … as it
could lead to infinite η-expansion"; for coinductive ones it "could easily
make Agda loop". Pattern matching on an inductive record without eta isn't
allowed by default. Internally, Agda replaces matches on record constructors
by projections [A2] (the source module `Agda.TypeChecking.RecordPatterns`:
"replaces pattern matching on record constructors with uses of projection
functions"), so a record pattern never blocks reduction.

**Lean 4** [L1, L2, L3]. `structure` is a single-constructor inductive type
with generated projections; "Structures do not add any expressive power to
Lean; all of their features are implemented in terms of code generation"
[L1], and "structures may be recursive" [L1]. The reference lists eta for
"single-constructor types" as part of definitional equality [L2]. In the
kernel [L3]:
- `Expr.proj` is a primitive projection. `infer_proj` checks that the
  projected value's type is the named structure ("`I_name != proj_sname(e)`
  → invalid projection"), that it has one constructor, and that a projection
  out of a `Prop` structure yields a proof.
- `try_eta_struct_core` decides `t ≡ mk s₁ … sₙ` by checking
  `t.i ≡ sᵢ` for each field, **only for non-recursive structures**
  (`is_non_rec_structure`), after checking that the two sides' types agree.
- `to_cnstr_when_structure` makes a recursor on a non-constructor value of a
  non-recursive, non-`Prop` structure reduce, by first expanding the value to
  `mk e.1 … e.n`.
- `is_def_eq_unit_like` makes any two values of a structure with no fields
  equal, which needs their types.

Lean4Lean's account of the kernel [L5] notes that structure eta was once
only a propositional equality, and that making it definitional means the
kernel must unfold structures when needed.

A 2026 Lean vulnerability, CVE-2026-72844 [L4], included that "the Lean 4
kernel does not verify that the structure named in a projection expression
matches the type of the value being projected" (with a separate check
missing for nested inductives); combined, they allowed an axiom-free proof of
`False`. The `I_name != proj_sname(e)` checks quoted above are the fix as it
stands at the commit cited. It's a direct warning for stage 2 here.

**Rocq** [Q1]. `Record`/`Structure` "cannot be recursive"; recursive records
are declared with `Inductive`. With primitive projections, "the defined type
has eta-conversion definitionally, in most cases", the `match` on it is
disabled ("one must use its defined primitive projections"), and recursive
or coinductive records get primitive projections but "eta-conversion is
disallowed". A practical motivation was size: non-primitive projections out
of nested Σ-types carry their whole parameter types as arguments and "grow in
size very quickly" when unfolded [Q2]. Eta for coinductive records is known
to break subject reduction in Rocq [Q3] (**unverified** beyond that
discussion).

**Idris 2** [I1]. `record Point where constructor MkPoint; x : Double …`,
generated projections, postfix `.field` that "binds tighter than function
application", and nested update syntax `{ topLeft.x := 3 }`. Whether Idris 2
has eta for records is **unverified**.

**Dependent records in theory.** Records as Σ-types with labels (Pollack
[P2], who adds manifest fields and shows they're definable with
induction-recursion; Coquand, Pollack and Takeyama's logical framework with
dependently typed records [P3]; Betarte's type checking of dependent record
types with subtyping [P4]). Eta for Σ ("surjective pairing") is what makes a
record definitionally equal to the tuple of its projections; Abel and
Coquand [P1] give an *untyped* algorithmic equality for a logical framework
with surjective pairs, proved sound and complete, which matters here because
Stitchwort's conversion is untyped.

### 3.2 Row polymorphism and its relatives

- **Wand** [R1] introduced row variables for records; **Rémy** [R2] made
  inference principal with presence/absence *flags* on fields.
- **Gaster and Jones** [R3] use qualified types with **lacks predicates**
  (`r \ l`: row `r` has no `l`) to rule out duplicate labels, and compile them
  by evidence passing: "the predicates correspond to runtime label offsets"
  (Leijen's summary [R5]).
- **Ohori** [R4] gives record type variables a *kind* listing the fields they
  must have, without extension, and compiles field access to vector indexing
  using type information ("records are represented as vectors whose elements
  are accessed by direct indexing"). This is the closest precedent for
  stage 4.
- **Leijen** [R5] allows **duplicate labels** with scoping, so extension
  needs no lacks predicate; rows are "equivalent up to permutation of distinct
  labels". He criticises lacks predicates because "each use of a label leads to
  a lacks predicate, which in turn can lead to large types". Koka's effect
  rows use the same idea [K1].
- **Morris and McKinna** [R7] abstract over "row theories" with qualified
  types, giving principal types to concatenation.
- **Ur/Web** [R6] has type-level records of kind `{Type}`, first-class names,
  concatenation `++`, and **disjointness constraints** `[[nm] ~ r]` that are
  "always inferred". Ur deliberately has type-level computation without
  dependency.
- **PureScript** [S1, S2]: `{ … }` is sugar for `Record` applied to a row;
  rows have kind `Row k`, are "unordered … with duplicates"; records
  "correspond to JavaScript objects". Row polymorphism: `{ foo :: Int | r }`.
- **Elm** [S3] has extensible record *types* (`{ a | name : String }`) but
  removed field addition and deletion in 0.16 (secondhand sources: confusing,
  hurt error messages, rarely used). Exactly stage 4's scope.
- **OCaml** [S4] object types `< get_x : int; .. >`, where the ellipsis
  "behaves as a type variable"; Garrigue's polymorphic variants [S5] are the
  dual for sums.
- **GHC's `HasField`** [S6]: `class HasField x r a | x r -> a` with
  `getField :: r -> a`, solved automatically for record types, and
  user-definable "virtual" fields. Read-only.
- **TypeScript** [T1] is structural with width subtyping, except that
  object *literals* "may only specify known properties".
- **Dhall** [H1], a total language with built-in structural records, decides
  equivalence by comparing binary encodings, in which record fields are
  sorted, so field order never matters. The same encoding is what Dhall
  hashes.

**What I couldn't find:** a dependently typed language with Wand/Rémy-style
row polymorphism over *dependent* records in its trusted core. The
dependent-records literature above is about closed, ordered telescopes; the
row literature is about non-dependent types. DESIGN §9 keeps the two apart,
and so does this note.

## 4. The design axes

Each axis lists the options, then which is recommended (detail in §5–§11).

### 4.1 Nominal or structural?

| | Nominal (declared): `type Person = { name : Text, age : Nat }` makes a new type | Structural (anonymous): `{ name : Text, age : Nat }` is a type in its own right |
|---|---|---|
| Two declarations with the same fields | different types | the same type |
| Field order | as declared; may depend on earlier fields | irrelevant (if non-dependent) |
| Like | Lean, Agda, Rocq, Idris, Rust, Haskell | PureScript, Elm, TypeScript, Dhall, OCaml objects |
| TS output | a named type `Person` | an inline object type |
| Error messages | short (`Person`) | the whole field list, unless aliases are tracked |
| Kernel | already supported (a data type) | needs canonical forms (§8) |

DESIGN §9 today says "`type Person = …` just gives it a name" (structural),
while DESIGN §4's `type SortedList = { items …, sorted … }` reads naturally as
a declared type with an invariant. The two clash once both exist: an alias can
always be written as an ordinary definition, `Person : Type; Person = { … }`
(definitions may already have uppercase names, `docs/syntax.md`), so `type`
can mean "new type", consistently with `type … = | …` data types.

**Recommendation:** both, in that order. `type X = { … }` declares a nominal
record (stage 1); anonymous `{ … }` types are structural (stage 3); an alias is
a definition. This changes DESIGN §9's sentence, so it's question U1.

### 4.2 Dependent fields

Declared records are telescopes, as data constructors already are, so
dependent fields come for free in stage 1. Structural records with dependent
fields would need ordered telescopes compared label by label, giving two
equality rules for one syntax (order-insensitive without dependency,
order-sensitive with it). **Recommendation:** dependent fields only in
declared records, matching DESIGN §9's split.

### 4.3 Kernel representation

| Option | Kernel change | Eta | Structural equality | Positivity for records inside recursive types |
|---|---|---|---|---|
| **K1** Encode as one-constructor data types, projections as generated case-tree definitions | none | no | n/a (nominal only) | as data types |
| **K2** K1 plus primitive projections and eta for non-recursive records | small (§7) | yes | n/a | as data types |
| **K3** Structural types as interned generated data types keyed by sorted labels | hashing, a positivity case (§8) | via K2 | ordinary conversion | needs the positivity case |
| **K4** Native record types `{l : A, …}`, record values and projection in the kernel (like Dhall [H1]) | large: typing, conversion up to order, hashing, positivity, termination, extraction | built in | built in | built in |
| **K5** Labelled Σ-telescopes over type-level strings (`Field "name" Text (Field "age" Nat End)`), Pollack-style [P2] | none, or type-level text | via Σ | needs sorting at type level | nested occurrences |

**Recommendation:** K1, then K2, then K3. K4 does everything K1–K3 do, with
more trusted code and nothing extra. K5 makes unification and error messages
work on encoded types and pays for type-level text comparison; its strength,
first-class labels, is a non-goal.

### 4.4 Row polymorphism

| Option | What `{ name : Text \| r }` means | Supports | Kernel | Relation to ability rows |
|---|---|---|---|---|
| **R1** None | not allowed | closed records only | none | n/a |
| **R2** `Has` constraints (Ohori [R4], Elm [S3], GHC `HasField` [S6]) | `r` is the whole record type; `[has : Has.name r Text]` is evidence: a getter and a setter | read, same-type update, on nominal *and* structural records | none (evidence is an ordinary data type) | independent |
| **R3** Rows with lacks predicates, split representation and explicit coercions (Gaster–Jones [R3]) | `r` is the rest of the row; `{ name : Text \| r }` lacks `name` in `r` | also extension and restriction | none (coercions re-checked), but needs row values like `Sig` | the same machinery as abilities; would have to fix their lacks-constraint gap |
| **R4** Kernel rows (Ur's kinds and disjointness [R6], Morris–McKinna [R7]) | a row kind in the core | everything, incl. concatenation | large | would replace the ability encoding |

**Recommendation:** R2 as stage 4. It covers the original goal ("any record
with at least field `x`"), works for declared records too, and needs no lacks
constraints, so neither of the ability rows' known issues is inherited. R3 is
the documented path if extension is ever wanted (§10).

### 4.5 Eta

Without eta, `p` and `{ name = p.name, age = p.age }` aren't the same by
computation, a function that matches on a record parameter is stuck while the
record is unknown, and an update that changes nothing isn't `rfl`. Lean, Agda
(by default) and Rocq (with primitive projections) all have eta for
non-recursive records. **Recommendation:** add it in stage 2, for
non-recursive records in `Type` only (§7).

### 4.6 Field access and inference

`p.name` needs to know `p`'s type. Options: (a) require it to be known when
`p.name` is elaborated (Lean's dot notation needs the head symbol; stage 1);
(b) postpone; (c) with R2, emit a `Has.name ?t ?a` obligation and solve it at
the end of the declaration, as `auto` obligations already are, which gives
inference for lambdas like `map (\p -> p.name) people` (stage 4).

### 4.7 Pattern matching

Record patterns `{ name = n, age = a }`, punned `{ name, age }`, and partial
`{ name, .. }`, compiled to the single-branch `Case` the kernel already has.
With stage 2's eta, such a `Case` never blocks (Lean's
`to_cnstr_when_structure` [L3]; Agda's translation to projections [A2]).

## 5. Recommendation

1. **Stage 1, declared records by translation (no kernel change except
   hashing field names).** `type Person = { … }`, dependent fields, generated
   projections, literals, update with dependent re-establishment, patterns,
   `p.name` on known types, untagged JS objects and a named TS type.
2. **Stage 2, primitive projections and eta for non-recursive records in
   `Type`.** A small, well-precedented kernel addition (§7). Could be merged
   with stage 1 if preferred; doing it second keeps stage 1 free of trusted
   changes while the surface and JS forms settle.
3. **Stage 3, anonymous structural records** as interned canonical data
   types (§8). Non-dependent.
4. **Stage 4, `Has` constraints** for `{ name : Text | r }` (§9).
5. **Not planned:** extension and restriction (§10), kernel rows, first-class
   labels.

Stages 1 and 2 are what proofs and the JS use case need most. Stages 3 and 4
are the "structural, row-polymorphic" goal; neither depends on the other, so
their order is a matter of taste (question U3).

## 6. Stage 1: declared records, by translation

### 6.1 Surface

```
type Person = { name : Text, age : Nat }

alice : Person
alice = { name = "Alice", age = 30 }

birthday : Person -> Person
birthday p = { p | age = p.age + 1 }

describe : Person -> Text
describe { name, age } = name ++ " is " ++ natToText age

-- Parameters and dependent fields, as for data types.
type Sized (a : Type) = { items : List a, size : Nat, ok : length items = size }

IsSorted : List Nat -> Prop
type SortedList = { items : List Nat, sorted : IsSorted items }
```

- **Literals** are checked against an expected record type (bidirectional
  checking already supplies one in arguments, annotated `let`s and
  signatures). Every field must be given exactly once, in any order. If
  field expressions perform abilities, they run in the order written, as
  arguments run left to right. Without an expected type
  (`let p = { name = "A", age = 3 }`), stage 1 says "can't tell which record
  type this is; add `: Person`". Stage 3 changes this: such a literal gets an
  anonymous record type (question U6).
- **Access** `p.name` binds tighter than application (`f p.name` is
  `f (p.name)`), as in Idris [I1]. `p`'s type must be a known record type
  when `p.name` is elaborated; otherwise `E-CANNOT-INFER` with a hint. A
  lexer change adds `.` (there's no `.` token today; generated names like
  `State.elim` are never written in source). `(.name)` is the accessor
  function, written `\p -> p.name` until sections exist.
- **Update** `{ p | f₁ = e₁, … }`. The elaborator computes, from the
  declaration, which later fields' types mention each updated field,
  transitively, and requires each of those to be updated too:

  ```
  { s | items = [2, 1] }                          -- E-RECORD-UPDATE: `sorted`
                                                  -- depends on `items`
  { s | items = xs', sorted = proofAbout xs' }    -- fine
  ```

  This is DESIGN §9's rule; it's a convenience, since the kernel re-checks the
  constructor application anyway.
- **Patterns** `{ name = n, age = a }`, `{ name, age }` (punning), and
  `{ name, .. }`, nested inside other patterns.
- **Recursive and mutually recursive records** are allowed by the data-type
  rules: e.g. once mutual data types exist, `type Tree = | Leaf | Node Info`
  with `type Info = { label : Text, left : Tree, right : Tree }`. A record
  whose field has its own type directly (`{ value : Nat, next : Node }`) has
  no values at all; a useful self-reference goes through another type
  (`next : Maybe Node`), which is a nested occurrence that positivity refuses
  today (`TODO.md`), or through a function field. So in practice recursion
  goes through a mutual group.
- **Universe**: as for data, `type Person : Type 1 = { … }` when a field is
  a type; `: Prop` records (like `And`) are allowed and follow the `Prop`
  elimination rule (one constructor, so projections into proofs are fine; a
  data-valued field disqualifies, exactly as for `HiddenType`).

### 6.2 What the kernel sees

`type Person = { name : Text, age : Nat }` elaborates to

```
type Person : Type =
  | Person.mk (name : Text) (age : Nat)        -- field names kept

Person.name : Person -> Text
Person.name (Person.mk n a) = n

Person.age : Person -> Nat
Person.age (Person.mk n a) = a
```

with `Person.mk` and the projections not nameable in source. Projections with
dependent result types work today: `SortedList.sorted : (s : SortedList) ->
IsSorted (SortedList.items s)` is defined by a case that refines `s` to
`SortedList.mk i p`, against which `SortedList.items s` computes to `i`.

The elaborator records which data types are records (and their field order)
for the JS generator and for messages; the kernel needs nothing new, except
that the record flag and field names must be hashed (§12).

### 6.3 What stage 1 can't do

- `{ p | age = p.age } = p` isn't `rfl` (it's `Person.mk (Person.name p)
  (Person.age p)` against a neutral `p`). It's provable once per type
  (`etaPerson p : p = …` by matching `p`), and the elaborator could generate
  that lemma; stage 2 removes the need.
- A definition that matches on an unknown record stays folded.
- `.name` on an unknown type needs an annotation.

### 6.4 Termination

Unchanged. Matching a record parameter binds its fields as `<` the
parameter, as for any constructor. A recursive call on a *rebuilt* record is
unknown: `sum { list = Cons x xs, acc } = sum { list = xs, acc = acc + x }`
is refused today, because the new record isn't a field of the old one. The
fix is to treat a non-recursive record parameter as its fields for
size-change (each field a separate column), which is sound because a record
is determined by its fields; question R4 for the reviewer. Until then, users
pass the fields as separate arguments.

## 7. Stage 2: projections and eta in the kernel

### 7.1 Which records

An **eta record** is a data type that:
1. has exactly one constructor and no indices (Stitchwort has none anyway);
2. lives in `Type i`, not `Prop`;
3. is **non-recursive**: its data group (once mutual data types exist) is
   just itself, and no field type mentions it.

The kernel decides this from the declaration, so the elaborator's "record"
flag is not trusted for it; any single-constructor data type meeting 1–3
gets eta (Lean does the same for every non-recursive structure [L3]; Agda
for every record [A1]). `Pair`, `Sig`, `SigMap` and `UnitType` would become
eta types, which only makes more conversions succeed; whether that changes
any existing elaboration (unification solving more) needs the full test suite
(question R2).

Condition 3 is what keeps unfolding finite (§7.4). Condition 2 avoids two
questions: eta for a `Prop` record would equate proofs that are otherwise
distinguishable (there's no definitional proof irrelevance), and
projecting data out of a proof must stay forbidden (Lean checks this in
`infer_proj` [L3]).

### 7.2 New core forms

- `Proj(D, i, t)`: field `i` of `t`, where `t : D ps` and `D` is an eta record.
- `Elim::Proj(D, i)` on neutral spines, so `Proj` of a stuck value is
  neutral.

**Typing** (`infer`): infer `t`'s type, reduce it to `Data(D', ps)`, and
**require `D' = D`** (the Lean bug [L4]), `D` an eta record and `i` in range.
The type is field `i`'s declared type with the parameters `ps` and
`Proj(D, j, t)` for each earlier field `j` substituted. This is the dependent
Σ rule for the second projection, generalised to a telescope.

**Evaluation:** `Proj(D, i, Ctor(D, 0, fs)) ⟶ fs[i]`; on a neutral, push
`Elim::Proj(D, i)`. A `Proj` whose `D` doesn't match the constructor's data
type is stuck (as Lean's `reduce_proj_core` refuses [L3]); only an ill-typed
term could reach that.

### 7.3 Eta in conversion

Two rules, both reading `D` from the term, so the untyped conversion needs no
types:

1. **One-sided eta.** `Ctor(D, 0, fs) ≡ n`, for `D` an eta record and `n` not
   a constructor, holds when `fs[i] ≡ Proj(D, i, n)` for every field `i`
   (and symmetrically). This is Lean's `try_eta_struct_core` [L3] without its
   type comparison, which an untyped checker can't do. It's justified because
   conversion is only ever asked about two values of the same type (the
   checker compares an inferred type with an expected one, and recurses into
   parts at corresponding positions), and it's the shape of Abel and
   Coquand's untyped algorithm for surjective pairs [P1]. Whether every call
   site of `conv` in this kernel really respects "same type" needs checking
   (question R1).
2. **A `Case` on a neutral eta record takes its only branch**, with the
   fields bound to `Proj(D, i, x)` (Lean's `to_cnstr_when_structure` [L3]).
   Since `Case(x, D, …)` names `D`, again no types are needed. This makes
   record patterns non-blocking, so a definition whose case tree splits only
   records always unfolds.

**What it leaves out.** Eta for a record with **no fields** (`{}`, any two
values equal) needs to know a neutral's type, as Lean's
`is_def_eq_unit_like` [L3] does; an untyped checker can't. So `{}` gets rule
1 (a neutral equals `Ctor(D, 0, [])`) but two neutrals of type `{}` aren't
equal. That's incompleteness, not unsoundness. Two neutrals of a record type
with fields are compared structurally, as now; they're equal under eta only if
their projections are, which structural comparison of neutrals doesn't try
(e.g. `f x ≡ g x` where both are stuck but their projections would compute
to equal values). Whether Lean's kernel closes this gap wasn't checked.

### 7.4 Why unfolding still terminates

Unfolding a definition now also proceeds through `Case` nodes on neutral eta
records (rule 2). Each such step replaces a neutral `x : D` by projections of
type the fields' types. Because `D` is non-recursive, and the only way back to
`D` is through another data type that `D` doesn't mention (otherwise they'd
be a group, condition 3), a chain of record-only expansions ends after at
most the nesting depth of record types. A `Case` on a neutral non-record
value still blocks. This is the argument Agda gives for disabling eta on
recursive records ("could lead to infinite η-expansion" [A1]); a test with a
record inside a recursive data type checks it (§14).

### 7.5 Termination checking

A projection of the parameter or of a descendant is a **descendant** (`<`):
`Proj(D, i, x)` is a field of the value `x`, by eta, so it's a strict
subterm, as the fields bound by a `Case` on `x` already are. With stage 2,
record patterns still compile to `Case` (their fields are classified as
today), and `p.field` in expressions becomes `Proj`, classified by this rule.

### 7.6 Soundness argument

- **Consistency.** In the set-theoretic model where `D ps` is the set of
  tuples of its fields, `Proj` is the coordinate function, and every element
  is the tuple of its coordinates, so both eta rules hold. Nothing else in
  the model changes. (This is the standard argument for Σ with surjective
  pairing; for the kernel as implemented it's an argument, not a proof.)
- **Type preservation.** Rule 2 replaces `x` by `Ctor(D, 0, Proj…)` in a
  branch whose checking already assumed `x = Ctor(D, 0, fields)`, with
  fields of the right types by the `Proj` typing rule.
- **Decidability.** §7.4.
- **The danger case** is a `Proj` naming one type applied to a value of
  another, which is exactly the Lean CVE [L4]: typing checks `D' = D`, and
  evaluation refuses mismatches.

### 7.7 Stage 1 code under stage 2

The elaborator stops generating `Person.name` as a case tree and emits
`Proj(Person, 0, p)`. Hashes of everything using records change once; that's
acceptable (DESIGN §11: backwards compatibility isn't a goal).

## 8. Stage 3: anonymous structural records

### 8.1 Surface

```
divMod : (n d : Nat) -> [auto ok : d != 0] -> { quotient : Nat, remainder : Nat }
divMod n d = { quotient = n / d, remainder = n % d }

-- The same type, written in another order:
check : { remainder : Nat, quotient : Nat } -> Bool
check r = r.remainder < 10

test "order doesn't matter" = check (divMod 7 3)

-- An alias is a definition:
Point : Type
Point = { x : Nat, y : Nat }
```

Fields of an anonymous record may not depend on each other (§4.2). Field
types may be any types, including declared records and other anonymous
records.

### 8.2 Representation: canonical generated data types

For each set of labels `{l₁ < … < lₙ}` (sorted by name) and universe levels
`(k₁, …, kₙ)` of their types, the elaborator interns one data type

```
type Rec{quotient,remainder} (a : Type 0) (b : Type 0) : Type 0 =
  | Rec{quotient,remainder}.mk (quotient : a) (remainder : b)
```

with a parameter per field (in label order), and translates
`{ remainder : Nat, quotient : Nat }` to `Rec{quotient,remainder} Nat Nat`.
Then:
- **Equality up to field order** is ordinary conversion: both orders produce
  the same `Data(Rec{…}, [Nat, Nat])`.
- **Eta, projections, patterns, termination**: as for any non-recursive
  record (stage 2), since the generated type has no self-reference.
- **Universe levels** are part of the key because Stitchwort has no universe
  polymorphism: `{ elem : Type }` and `{ elem : Nat }` are different generated
  types (`Type 1` versus `Type 0` parameter). When universe polymorphism
  arrives, the levels become parameters. A `Prop`-valued field is a parameter
  of type `Prop` and is erased as usual.
- **Prelude interning.** Generated types belong to no module. Each is created
  once per program, on first use, and admitted like any data type.

### 8.3 Kernel changes

1. **A structural-record flag** on a data declaration, which the kernel
   checks when the type is declared: one constructor whose fields are exactly
   the parameters, in order, field `i` of type parameter `i`; labels strictly
   sorted; no other content. The kernel builds the declaration itself from
   the label list and levels, so there is nothing to compare.
2. **Hashing** (§12): such a type is hashed by its labels and levels, not by
   a module and name, so the same anonymous type gets the same hash wherever
   it's written.
3. **Positivity through structural records.** `type Expr = | Lit Nat | Add
   { left : Expr, right : Expr }` mentions `Expr` as a parameter of
   `Rec{left,right}`, a nested occurrence, which positivity refuses today. For
   a flagged structural record, positivity can treat `Rec{…} A₁ … Aₙ` as if
   its fields `A₁ … Aₙ` appeared directly, which is sound because replacing
   the field `(r : Rec{…} A₁ … Aₙ)` with fields `A₁ … Aₙ` gives an isomorphic
   declaration that positivity already accepts. This is a special case of the
   general nested-inductive analysis (Rocq and Agda check the container's
   parameter positivity; Lean translates nested types into mutual ones
   [mutual-recursion.md §7.1]), so it can be replaced by that analysis if it
   arrives. Termination also has to follow: a field of the anonymous record
   inside a matched `Add` is a descendant (it already is, as a field of a
   field).

### 8.4 Anonymous literals

With stage 3, a literal with no expected type gets an anonymous type
(`let p = { name = "A", age = 3 }` has type `{ age : Nat, name : Text }`).
Using it where a `Person` is expected is then a type error, since `Person` is
nominal; the message should suggest annotating the literal. This is the main
cost of having both kinds (question U6). Converting automatically isn't
proposed.

### 8.5 Alternative: native record types (K4)

The kernel could have `RecordType([(label, A)])`, `RecordValue` and `Proj`
directly, as Dhall does [H1]. It would need its own typing rules, conversion
up to label order, eta, positivity and termination cases, hashing and
extraction, all trusted. K3 gets the same behaviour from existing data-type
machinery plus §8.3's three changes, so K4 isn't recommended.

## 9. Stage 4: functions over "any record with field `x`"

### 9.1 Surface

```
greet : { name : Text | r } -> Text
greet x = "Hello, " ++ x.name

birthday : { age : Nat | r } -> { age : Nat | r }
birthday p = { p | age = p.age + 1 }

-- Works on declared and anonymous records alike:
test "greet" = greet alice == "Hello, Alice"
test "greet anon" = greet { name = "Bob", shoeSize = 9 } == "Hello, Bob"
```

The type variable `r` stands for **the whole record type**, constrained to
have the listed fields. (In Gaster–Jones or PureScript, `r` would be "the
other fields". With no extension or restriction the difference isn't
observable, and Elm's `{ r | name : String }` reads the same way.) Several
annotations mentioning the same `r` combine their fields.

### 9.2 Translation

For each label `name` used this way, the elaborator interns (like §8.2)

```
type Has.name (t : Type) (a : Type) : Type =
  | Has.name.mk (get : t -> a) (set : a -> t -> t)
```

and translates

```
greet : [r : Type] -> [auto has : Has.name r Text] -> r -> Text
greet x = "Hello, " ++ Has.name.get has x

birthday : [r : Type] -> [auto has : Has.age r Nat] -> r -> r
birthday p = Has.age.set has (Has.age.get has p + 1) p
```

**Finding the evidence**, in `auto`'s order (DESIGN §6):
1. supplied explicitly, `[has := …]`;
2. a hypothesis in scope with that type (inside another polymorphic
   function, its own `has`);
3. **derived** when `r` is a known record type with a field `name : A`:
   `get = \x -> Proj(R, i, x)` and `set = \v x -> R.mk … v …` (the other
   fields by projection). `A` is determined by `r` and `name` (GHC's
   functional dependency `x r -> a` [S6]), so derivation can solve an unknown
   `a`.

Derivation is refused for a field that a later field depends on (setting it
would break the later field), and for a field whose own type depends on
earlier fields (its type isn't a fixed `A`). So `Has.items SortedList _` has
no evidence; `SortedList` is used through its own functions.

**Inference of `.name` on unknown types** (§4.6 (c)): when `x`'s type is an
unknown `?t`, `x.name` elaborates to `Has.name.get ?h x` with an obligation
`Has.name ?t ?a`, solved after the declaration like other `auto` obligations,
once `?t` is known. A leftover unsolved `?t` is `E-UNSOLVED` as now. When `t`
turns out to be a known record, the elaborator can simplify `get` of derived
evidence to a plain `Proj` (it's equal by computation anyway).

### 9.3 Laws (optional)

Evidence could also carry erased proofs of the lens laws (`get (set v x) =
v`, `set (get x) x = x`, `set v (set w x) = set v x`), so that proofs about
polymorphic functions can use them. For derived evidence each is `rfl` under
stage 2's eta (the second is exactly eta). Without them, a proof about
`birthday` holds only per concrete type. Whether to include them is
question R6.

### 9.4 Why not rows here

R2 needs nothing from the ability-row machinery: no row variable of a row
kind, no lacks constraints (a `Has` constraint never adds a field, so
duplicates can't arise), no canonical order of an open row (the record type
`r` is opaque), and no coercions. The cost is the non-goal: no `{ r | +email
= … }`.

### 9.5 Exports

A row-polymorphic function isn't exportable (DESIGN §12: an export's types
must be concrete). It doesn't need to be: an export taking `{ name : Text }`
already accepts any JS object with a `name`, because decoders ignore extra
properties (§11).

## 10. Later, maybe: adding and removing fields

If a real program needs `{ r | +email = e } : { email : Text | r }` or
removal, the route is R3, shared with abilities:
- an anonymous record's type becomes `Rec ρ` for a *row value* `ρ` (a
  prelude type, as `Sig` is for abilities), with a split form
  `{ l : A | ρ }` for open rows;
- **lacks constraints** `ρ lacks l` (Gaster–Jones [R3]) on row variables,
  enforced when they're instantiated, or Leijen's duplicate labels [R5]
  instead;
- explicit, kernel-checked permutations between an open row and the closed,
  sorted form, as `SigMap` does for abilities.

That is exactly the work the ability rows still owe (`TODO.md`: lacks
constraints not enforced; declaration-order sorting). Doing it once for both
would also be the time to sort ability rows by something stable (their
names, or hashes) rather than declaration order, which records would need
from the start: label order must not depend on which file declared what.

## 11. JavaScript and TypeScript

### 11.1 Representation

| Stitchwort | Inside generated JS | At the boundary (TS) |
|---|---|---|
| `type Person = { name : Text, age : Nat }` | `{ name, age }`, no `tag` | `export type Person = { readonly name: string; readonly age: bigint }` |
| `type Sized (a : Type) = { … }` | the same | `Sized<A>`, as parameterised data types are today |
| anonymous `{ quotient : Nat, remainder : Nat }` | the same | `{ readonly quotient: bigint; readonly remainder: bigint }`, inline |
| an alias `Point = { x : Nat, y : Nat }` | the same | inline (or `export type Point = …` if the generator keeps alias names: a nicety) |
| proof fields (`sorted`, `ok`) | omitted | omitted |
| `Has.name r A` evidence | an object `{ get, set }` | never at the boundary |

A record is the only single-constructor data shape that loses its `tag`:
ordinary data types like `Pair` keep it, so existing `.d.ts` files don't
change.

`Proj(D, i, x)` compiles to `x.key`, and a record `Case` to destructuring.
Extracted JS performance isn't a goal, but plain property access is also the
fastest form.

### 11.2 Keys

DESIGN §12's field rule applies: a field's key is its name with each prime as
`$`, and `__proto__` becomes `$__proto__` (in an object literal it would set
the prototype). The `tag` rule exists because data objects use a `tag` key;
records don't, so **a record field named `tag` keeps the key `tag`**
(question U4). Field names are identifiers starting with a letter, so no key
is integer-like, and JS keeps keys in insertion order.

**Key order** in encoded objects (visible to `Object.keys` and
`JSON.stringify`): declared order for declared records; label order for
anonymous ones, since their type has no other order (question U2).

### 11.3 Decoding and validation

A record decoder is the existing data decoder without the tag: the input must
be a non-array object; each field is read once, as an own property, in
declared order; a missing field is refused with its path
(`order.customer.name: missing`); extra properties are ignored. Since TS
allows extra properties on non-literal values [T1], this is TS's own width
subtyping.

**Proof fields in inputs.** A `SortedList` passed *in* has no `sorted`
property: the decoder must re-establish it, so a record field whose type is a
proposition needs a registered decision procedure, run after decoding, exactly
like an export's `[auto]` precondition (DESIGN §12 rule 3). A proof field with
no decision procedure makes any export that takes the record `E-EXPORT`. As
outputs, proof fields are just omitted. (DESIGN §12 doesn't yet say this for
data types with proof fields; the same rule should apply to them.)

### 11.4 Equality

`==` on a record needs a decision procedure for `=` on its type. Stage 1
should derive one field by field when every field has one. Records with proof
fields are the catch: two `SortedList`s with equal `items` are equal only if
their `sorted` proofs are equal too, and without proof irrelevance that can't
be decided in general. So either the derived procedure is offered only for
records without proof fields, or it decides equality of the data fields and
says so in its type. To settle in implementation; question R7.

## 12. Content hashes

- **Field names must be hashed.** Today a data type's hash omits field names
  (`hash.rs`, `data_hash`). For records they're semantics: `p.name` resolves
  by them, and JS keys are made from them, so renaming a field changes the
  generated `.d.ts`. The same is already true of constructor fields at the
  boundary, so DESIGN §11's planned generated-JS cache (keyed by definition
  hash) would serve stale code after a field rename today. **Recommendation:**
  include field names in every data type's hash, and the record flag too
  (it changes the JS representation). This is a fix independent of records.
- **Nominal records** are hashed like data types (module and name, per
  DESIGN §11).
- **Anonymous record types** (§8) are hashed by their sorted labels, universe
  levels and the record-flag marker, with no name or module, so equal types
  have equal hashes. Dhall hashes its records the same way, from an encoding
  with sorted fields [H1].
- **`Has.name`** types likewise by label.
- **`Proj(D, i, t)`** hashes `D`'s hash, `i` and `t`; the label is
  determined by `D` and `i`.
- **Canonical order is by Stitchwort name.** Sorting by name equals sorting
  by JS key, since primes (`'`) and their `$` replacement both sort below
  digits, letters and `_` in ASCII; only `__proto__` moves, which affects
  nothing because order is computed on Stitchwort names.

## 13. Trusted code

| Stage | Kernel change | Trusted? | Size (estimate) |
|---|---|---|---|
| 1 | Hash field names and the record flag | the hasher (for caching only) | a few lines |
| 2 | `Proj` term and spine elimination; its typing rule (with the `D' = D` check); evaluation; one-sided eta in `conv`; `Case` on a neutral eta record; the eta-record predicate; the termination rule for `Proj`; hashing, quoting, printing | yes | 200–300 lines |
| 3 | Structural-record flag and its well-formedness check; label-based hash; positivity through flagged types | yes | ~100 lines |
| 4 | none | no | 0 |

Outside the kernel but trusted for the JS guarantee (DESIGN §12): the record
encoders and decoders, the proof-field validators, and the key mapping.

## 14. Testing plan

**Stage 1**
- Accept: the DESIGN §4 examples (`alice`, `birthday`, `greet` at a concrete
  type, `SortedList.insert`), dependent `Sized`, record patterns and punning,
  a record in a mutual group (once groups exist), a `Prop` record used to
  produce a proof.
- Must reject: an update of `items` without `sorted` (DESIGN §13's existing
  row, `E-RECORD-UPDATE`), a literal missing a field or with an extra or
  duplicate one, `p.nmae`, `.name` on an unknown type, a `Prop` record with a
  data field matched to produce data (`E-PROP-ELIM`), each paired with an
  accepted neighbour.
- Extraction: records with awkward names (`tag`, `__proto__`, primes,
  `constructor`) added to `awkward_names_never_collide`; differential tests
  through the boundary; `tsc` on the `.d.ts`; an input object with extra,
  inherited, getter-backed and missing properties; a `SortedList` input whose
  list isn't sorted (refused) and is (accepted).
- Hashes: renaming a field changes the type's hash.

**Stage 2** (raw-kernel tests, as in `crates/core/tests/admission.rs`)
- `Proj(D, i, t)` with `t : E`, `E ≠ D`, both with one constructor and
  compatible field counts (the Lean CVE shape [L4]); `i` out of range; `Proj`
  on a `Prop` record; `Proj` on a recursive single-constructor type; `Proj` on
  a two-constructor type. All refused with `E-MALFORMED` or a type error.
- `rfl : { p | age = p.age } = p`, `rfl : p = Person.mk p.name p.age`, and
  matching on an unknown record reduces; their analogues for a recursive
  record are refused (no eta), and checking them terminates.
- Unfolding through records inside a recursive type
  (`type T = Leaf | Node R`, `R = { kid : T, n : Nat }`) on a neutral
  terminates.
- Every existing example still checks, with no snapshot changes beyond
  hashes (`Pair` and `Sig` become eta types).

**Stage 3**
- `{ a : Nat, b : Nat }` and `{ b : Nat, a : Nat }` convert and hash equally;
  `{ a : Nat }` and `{ a : Type }` differ; `type Expr = Lit Nat | Add { left :
  Expr, right : Expr }` is accepted, and `Bad = MkBad { f : Bad -> Void }` is
  refused (`E-POSITIVITY`, through the record).

**Stage 4**
- `greet` on a declared, an anonymous and a wider anonymous record;
  `birthday` preserves other fields (differential, and with a proof per
  concrete type); missing field `E-AUTO-NONE`-style error naming the field;
  `Has.items SortedList` refused; `map (\p -> p.name) people` infers.

## 15. Questions for the user

Plain-language choices that are a matter of taste:

- **U1. What does `type Person = { name : Text, age : Nat }` mean?** (a) A new
  type of its own, like a class name: a `Person` is never mixed up with
  another record that happens to have the same fields, error messages say
  `Person`, and TypeScript gets a named `Person` type. (b) Just a nickname
  for "a record with exactly these fields". DESIGN currently says (b); this
  note recommends (a), with nicknames written as ordinary definitions
  (`Person = { … }`).
- **U2. Field order in the JSON your app sees.** For declared records, the
  declared order. For anonymous records, alphabetical (the only order the type
  has), or as written in the function's return type (which would make two
  equal types encode differently)?
- **U3. Which first, after stages 1–2: anonymous records, or functions over
  "any record with a `name`"?** They're independent.
- **U4. A record field called `tag`.** Keep it as `tag` in JS (recommended,
  since records have no tag of their own), or write `$tag` as data types do,
  for uniformity?
- **U5. Optional fields.** Should a `Maybe Text` field appear in TypeScript as
  an optional property (`email?: string`) instead of `{ tag: "Nothing" } |
  { tag: "Just", value: … }`? It reads better for app code, but `Maybe (Maybe
  a)` can't be represented that way (DESIGN chose tagged `Optional` for the
  same reason). Not proposed for now.
- **U6. An unannotated record literal**, `let p = { name = "A", age = 3 }`:
  until stage 3 it's an error asking for a type; after stage 3 it's an
  anonymous record, which then can't be used where a `Person` is expected
  without an annotation. Fine, or should a literal wait to see where it's
  used?
- **U7. Is reading and updating enough, or do you want to add and remove
  fields** (`{ p | +email = e }`)? Elm removed adding and removing as rarely
  used; supporting it is the larger §10.

## 16. Open questions for the reviewer

- **R1. Untyped eta.** Is one-sided eta (§7.3 rule 1) sound and adequate in a
  conversion that never sees types, given that every caller compares values of
  the same type? Are there `conv` calls in elaboration (unification with
  metavariables, `auto` matching hypotheses) where the two sides needn't be
  same-typed, so that eta could equate ill-typed things?
- **R2. Eta for existing types.** Every non-recursive single-constructor
  `Type` data type becomes an eta type (`Pair`, `Sig`, `SigMap`, `UnitType`).
  Lean does the same. Should it instead be opt-in per declaration (Agda's
  `no-eta-equality`) to keep unification predictable?
- **R3. Unfolding.** Is §7.4's argument enough, with mutual groups in the
  picture, that `Case`-on-neutral expansion can't make conversion diverge?
- **R4. Size-change for record arguments.** Is flattening a non-recursive
  record parameter into its fields for the size-change graph (§6.4) sound,
  and how does it interact with `Proj` as `<` (§7.5)?
- **R5. Positivity through structural records** (§8.3). Is "fields are
  exactly the parameters" the right invariant for treating `Rec{…} A₁ … Aₙ` as
  transparent, or should this wait for general nested positivity?
- **R6. `Has` evidence.** Should evidence carry lens laws? Should users be
  allowed to supply their own evidence (GHC's "virtual fields" [S6]), given
  that a polymorphic function's behaviour then depends on it but no
  soundness property does?
- **R7. Decidable equality and proof fields** (§11.4).
- **R8. Prop records** have no eta here. Is there a case for eta on `Prop`
  records whose fields are all proofs, without definitional proof
  irrelevance?

## What I couldn't verify

- **Idris 2:** whether records have eta, and how dependent record update is
  checked; its record documentation [I1] doesn't say.
- **Lean:** the reference pages fetched [L1, L2] say little about kernel
  eta; the kernel behaviour above is read from the C++ source at one commit
  [L3], not from a specification. Whether Lean's elaborator, as opposed to its
  kernel, handles two neutral structures by eta wasn't checked. The CVE
  description [L4] is from a vulnerability database page, not the Lean
  advisory itself.
- **Agda:** that record patterns are still translated to projections in
  current versions; the source module [A2] is from Agda 2.8.0, and the manual
  [A1] doesn't say.
- **Rocq:** the subject-reduction problem with coinductive eta [Q3] is from
  an issue discussion; the 8.5 history of primitive projections wasn't read.
- **Papers read only in part:** Ohori [R4] (abstract and introduction; the
  index-passing compilation is as the abstract describes it), Gaster–Jones
  [R3] (not read; described via Leijen [R5]), Wand [R1] and Rémy [R2] (via
  Leijen [R5]), Morris–McKinna [R7], Pollack [P2], Coquand–Pollack–Takeyama
  [P3], Betarte [P4], Garrigue [S5] (abstracts only). Abel–Coquand [P1] from
  its abstract: that their untyped algorithm covers exactly §7.3's
  one-sided rule is my reading, not a quoted result.
- **Elm** 0.16's reasons for removing field addition are from secondhand
  sources [S3]; the release notes weren't read.
- **No soundness proof** for stage 2 in this kernel: §7.6 is an argument.
- **Not found:** a dependently typed system with row-polymorphic dependent
  records in its trusted core (§3.2).

## Sources

- [A1] Agda manual, *Record Types*. <https://agda.readthedocs.io/en/latest/language/record-types.html>
- [A2] Agda 2.8.0 source, `Agda.TypeChecking.RecordPatterns`. <https://hackage-content.haskell.org/package/Agda-2.8.0/docs/src/Agda.TypeChecking.RecordPatterns.html>
- [L1] Lean language reference, *Inductive Types* (structures, anonymous constructors). <https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/>
- [L2] Lean language reference, *The Type System* (definitional equality, eta for single-constructor types). <https://lean-lang.org/doc/reference/latest/The-Type-System/>
- [L3] Lean 4 kernel source at commit `88539871b4133140b0d5e9beb4cd446bcc0d2f40`: `src/kernel/type_checker.cpp` (`infer_proj`, `reduce_proj_core`, `try_eta_struct_core`, `is_def_eq_unit_like`), `src/kernel/inductive.h` (`to_cnstr_when_structure`), `src/kernel/inductive.cpp` (`expand_eta_struct`). <https://github.com/leanprover/lean4/tree/88539871b4133140b0d5e9beb4cd446bcc0d2f40/src/kernel>
- [L4] CVE-2026-72844 (Lean 4 kernel: projection structure not checked against the projected value's type; nested inductive arguments unchecked). <https://fieldguide.lutrasecurity.com/CVE-2026-72844/>; fix commit <https://github.com/leanprover/lean4/commit/a39eab69e1eee9ad38f4efe507907b1026a77808>
- [L5] M. Carneiro, *Lean4Lean: Verifying a Typechecker for Lean, in Lean*, §5.1 (structure eta). <https://arxiv.org/abs/2403.14064>
- [Q1] Rocq reference manual, *Record types* (primitive projections). <https://rocq-prover.org/doc/master/refman/language/core/records.html>
- [Q2] J. Gross, A. Chlipala, D. I. Spivak, *Experience Implementing a Performant Category-Theory Library in Coq*, ITP 2014. <https://arxiv.org/abs/1401.7694>
- [Q3] Coq issue #5288 (coinductive eta and subject reduction). <https://github.com/coq/coq/issues/5288>
- [I1] Idris 2 reference, *Records*. <https://idris2.readthedocs.io/en/latest/reference/records.html>
- [P1] A. Abel, T. Coquand, *Untyped Algorithmic Equality for Martin-Löf's Logical Framework with Surjective Pairs*, Fundamenta Informaticae 77(4), 2007 (TLCA 2005). <https://www.cse.chalmers.se/~abela/lfsigma.pdf>
- [P2] R. Pollack, *Dependently Typed Records in Type Theory*, Formal Aspects of Computing 13(3–5), 2002. <https://www.inf.ed.ac.uk/publications/report/0746.html>
- [P3] T. Coquand, R. Pollack, M. Takeyama, *A Logical Framework with Dependently Typed Records*, TLCA 2003; Fundamenta Informaticae 65, 2005. <https://www.inf.ed.ac.uk/publications/report/0742.html>
- [P4] G. Betarte, *Type Checking Dependent (Record) Types and Subtyping*, JFP 10(2), 2000. <https://www.cambridge.org/core/services/aop-cambridge-core/content/view/1793E1F504A8B156B7A3EF9F17A42549/S0956796899003627a.pdf>
- [R1] M. Wand, *Complete Type Inference for Simple Objects*, LICS 1987; *Type Inference for Record Concatenation and Multiple Inheritance*, Information and Computation 93, 1991 (as cited in [R5]).
- [R2] D. Rémy, *Type Inference for Records in a Natural Extension of ML*, in *Theoretical Aspects of Object-Oriented Programming*, MIT Press, 1993 (as cited in [R5]).
- [R3] B. R. Gaster, M. P. Jones, *A Polymorphic Type System for Extensible Records and Variants*, Technical Report NOTTCS-TR-96-3, University of Nottingham, 1996. <https://web.cecs.pdx.edu/~mpj/pubs/polyrec.html>
- [R4] A. Ohori, *A Polymorphic Record Calculus and Its Compilation*, ACM TOPLAS 17(6), 1995. <https://www.cs.tufts.edu/~nr/cs257/archive/atsushi-ohori/record-calc.pdf>
- [R5] D. Leijen, *Extensible Records with Scoped Labels*, TFP 2005 (draft revision 76). <https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/scopedlabels.pdf>
- [R6] A. Chlipala, *Ur: Statically-Typed Metaprogramming with Type-Level Record Computation*, PLDI 2010. <https://adam.chlipala.net/papers/UrPLDI10/>
- [R7] J. G. Morris, J. McKinna, *Abstracting Extensible Data Types: Or, Rows by Any Other Name*, POPL 2019. <https://dl.acm.org/doi/10.1145/3290325>
- [K1] D. Leijen, *Koka: Programming with Row Polymorphic Effect Types*, MSFP 2014. <https://arxiv.org/abs/1406.2061>
- [S1] PureScript documentation, *Records*. <https://github.com/purescript/documentation/blob/master/language/Records.md>
- [S2] PureScript documentation, *Types* (rows, records as JS objects). <https://github.com/purescript/documentation/blob/master/language/Types.md>
- [S3] Elm 0.16 removal of field addition and deletion (secondhand): Elm Discourse, *Remove 1 record field* <https://discourse.elm-lang.org/t/remove-1-record-field/7169>; elm/compiler issue #1283 <https://github.com/elm/compiler/issues/1283>
- [S4] OCaml manual, *Objects in OCaml*. <https://ocaml.org/manual/5.2/objectexamples.html>
- [S5] J. Garrigue, *Programming with Polymorphic Variants*, ML Workshop 1998. <https://caml.inria.fr/pub/papers/garrigue-polymorphic_variants-ml98.pdf>
- [S6] GHC User's Guide, *Record field selector polymorphism* (`HasField`). <https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/hasfield.html>
- [T1] TypeScript Handbook, *Type Compatibility*. <https://www.typescriptlang.org/docs/handbook/type-compatibility.html>
- [H1] Dhall standard at commit `56b0997a4800bfc815ea221529a6bb2bfd6723dc`: `standard/equivalence.md` (equivalence by binary encoding) and `standard/binary.md` (record types and literals encoded with sorted fields). <https://github.com/dhall-lang/dhall-lang/tree/56b0997a4800bfc815ea221529a6bb2bfd6723dc/standard>
