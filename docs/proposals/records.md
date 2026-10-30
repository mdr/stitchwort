# Proposal: records

**Status:** draft 2, 16 October 2026. The user has answered the questions
in [§15](#15-questions-for-the-user) (see [Decisions](#decisions-16-october-2026)
below), and an external review of draft 1.1 has been adopted (see
[Changes since draft 1.1](#changes-since-draft-11) and
[the review's answers](#the-reviews-answers)). Stage 1 is approved; stage 2
waits on nothing but implementation of §7's contract. **Stage 1 is built**
([§6.5](#65-as-built-stage-1)). This is DESIGN.md milestone 8
([§9](../../DESIGN.md#9-records)), which sketches records but leaves their
representation, their equality and their JS form open.

This note is meant to be read without knowing the codebase: §1 describes the
parts of Stitchwort it touches, checked against the source at commit
`67d88e5`. Claims about other systems cite their sources ([Sources](#sources));
anything not checked against a source is marked **unverified**, and
[What I couldn't verify](#what-i-couldnt-verify) lists the gaps.

## Contents

- [Decisions (16 October 2026)](#decisions-16-october-2026)
- [Changes since draft 1.1](#changes-since-draft-11)
- [The review's answers](#the-reviews-answers)
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

## Decisions (16 October 2026)

The user's answers to §15, which the rest of this note should be read in
the light of:

- **U1, declared records are new types.** `type Person = { … }` makes a type
  of its own: `Person` and `Pet` differ even with identical fields. A
  nickname would be an ordinary definition, `Point = { … }`. (DESIGN §9's
  wording "just gives it a name" changes accordingly.)
- **U2, key order.** Anonymous records, once they exist, produce JS objects
  with keys in sorted order, so one type always has one shape. Declared
  records keep their declared order.
- **U3, stages 3 and 4 deferred.** Anonymous records (§8) and functions over
  "any record with field `x`" (§9) are deferred. Stages 1 and 2 must be built
  so that both stay possible: records represented so that two with the same
  fields could later be recognised as the same anonymous type, and fields
  looked up by name generically.
- **U4, a record field called `tag` keeps the key `tag`** in JS (records have
  no constructor tag). Dangerous keys such as `__proto__` are still escaped.
- **U5, `Maybe` stays tagged** at the boundary. A separate `Optional` type
  (already planned in DESIGN §12) is the route to optional JS properties
  (`age?: bigint`); it can refuse ambiguous cases like `Optional (Optional a)`.
- **U6, a record literal with no expected type is an error** suggesting an
  annotation (`({ x = 0, y = 0 } : Point)`). When anonymous records arrive,
  this case becomes an anonymous record, so no working program changes
  meaning. No guessing from field names.

  *As built (SW-805, D1442, D1991): reversed.* Where nothing says a
  literal's type, it is the one record type visible by its short name whose
  fields are exactly the literal's, with its parameters inferred; none or
  several is still `E-CANNOT-INFER`, naming the candidates
  (`records::infer_literal`). "Nothing says" is the expected type being an
  unknown, and no construct around the literal that would take the type
  from another part: the sides of `==` and the other comparisons, `a ++ b`,
  and a `calc`'s first term try that part with the rule held back, and use
  the rule only if the construct then fails (`records::last_resort`). So
  every program that elaborated before elaborates to the same terms and
  hashes. Without that, `f 1 == Some ({ value = v })` took the right side's
  type from the field names and checked `f 1` against it (the comparison
  infers literal-free sides first), changing two hashes of
  `examples/accept/safe-fields.sw`, and rejecting the comparison where the
  field names name a different type from `f`'s
  (`examples/accept/record-literal-inferred.sw`). The rule is a
  name-resolution rule, like GHC proposal 366's rule 4: it looks only at the
  literal's field names and the names in scope at the literal, never at
  types learned later in elaboration (R1, `docs/research/elaboration.md`
  §5.3); holding it back changes only whether it is used.
- **U7, reading and updating only.** Adding and removing fields are deferred
  with the row work; if ever wanted, build the "lacks" machinery once and
  share it with ability rows.
- **Unions of records:** multi-constructor data types with named fields
  already give TypeScript discriminated unions. Planned extensions: a
  constructor wrapping a declared record, flattened in JS
  (`| Circle CircleData` → `{ tag: "Circle", radius }`), and a per-type
  discriminant key and tag strings (`{ kind: "circle", … }`) to match
  existing JS APIs. Untagged unions are not planned; anonymous unions are
  deferred with anonymous records.

So the proposal under review is **stages 1 and 2**: declared records by
translation into one-constructor data types, then projections and eta in the
kernel, plus the hash fix for field names (§12).

## Changes since draft 1.1

Draft 2 adopts the external review of draft 1.1 (16 October 2026). In
short: **stage 1 is approved** as written, with an explicit evaluation
order and an equality policy; **stage 2 needs an enforceable contract**
before it's built. What changed:

- **Eta's same-type assumption is now a stated contract that the code
  keeps** ([§7.3](#73-eta-in-conversion)). Draft 1.1 justified untyped eta
  by "conversion is only ever asked about two values of the same type"
  without checking it. Draft 2 lists every call site of the kernel's `conv`
  and the elaborator's `unify`, recommends one design (eta-aware conversion
  is called only with an established common type, and every recursive step
  keeps that invariant), names the one elaborator path where it doesn't
  hold (`first_order`) and switches eta off there, and adds the tests the
  review asks for.
- **Zero-field types get no eta at all**, neither the conversion rule nor
  the non-blocking `Case` rule ([§7.1](#71-which-records)). Draft 1.1's
  asymmetric "`{}` equals any neutral, but two neutrals differ" is gone.
- **Eta is a mode of a declaration, not a property inferred for every
  type** ([§7.1](#71-which-records)): on by default for eligible *new*
  record declarations, off for existing data types (`Pair`, `Sig`,
  `SigMap`), which can be migrated one at a time, deliberately. The kernel
  checks eligibility itself, separately from record syntax and from the JS
  representation; the mode is fixed at admission and is part of the type's
  hash. No eta for `Prop` records.
- **Eligibility is decided on the completed kernel group**, not on the
  record declaration by itself ([§7.1](#71-which-records)).
- **The termination-of-unfolding argument has two parts**
  ([§7.4](#74-why-unfolding-still-terminates)), and is tested on
  `Box (List Nat)` and nested `Box`es, which really exercise eta through a
  type that contains a recursive one.
- **The Agda comparison is corrected**
  ([§3.1](#31-records-in-dependently-typed-languages)): Agda gives eta to
  inductive records, recursive ones included, by default, and warns about
  unguarded ones. The restriction here is stricter than Agda's.
- **Structural descent through records is by stable field paths**
  ([§6.4](#64-termination), [§7.5](#75-termination-checking)): one record
  layer flattened, dependent fields kept as a telescope; a rebuilt record is
  never a descendant, and `loop r = loop { r | list = r.list }` is refused.
  It's a later termination-checker feature, not part of stage 1 or 2.
- **Deferred features** ([§8.6](#86-what-stages-1-and-2-must-keep-possible),
  [§9.2](#92-translation)): a generic *field description* (labels, order,
  types, dependencies, erasure, how to access a field) kept separate from
  nominal identity; `Has` split into `HasField` (read) and `CanSetField`
  (same-type replacement), so a read-only function can accept a
  `SortedList`.
- **`==` policy** ([§11.4](#114-equality)): derived only when a checked
  decision for the *whole record* can be built (proof fields through
  proof-uniqueness lemmas, dependent fields through transport); otherwise
  the user writes the procedure. A data-only comparison may exist, under
  another name, but never as `Decidable (r = s)`.
- **Evaluation order** ([§6.1](#61-surface)): each supplied field
  expression runs once, in source order, and the constructor is then
  assembled in declaration order; an update evaluates its base once, first.
- **Hashes** ([§12](#12-content-hashes)): field names for *every* data
  type, the record (representation) flag, and the eta mode; caches must not
  be reused across a change in kernel semantics.
- **TypeScript** ([§11.1](#111-representation)): the generated aliases are
  structural, as all TS object types are; a Stitchwort-nominal `Person`
  isn't nominal in TS. Exportability stays narrower than well-formedness
  ([§11.3](#113-decoding-and-validation)).

**Where draft 2 departs from the review:** nowhere of substance. Two
refinements: (1) besides the contract, the elaborator's `first_order`
fallback, which does compare arguments that needn't share a type, gets eta
switched off rather than a local type check (unification has no types to
check there); (2) of the review's two options for empty records (a
type-aware case, or excluding them), draft 2 takes exclusion, since the
kernel's conversion has no types to be aware of.

## The review's answers

| Question | Review's answer | Draft 2 |
|---|---|---|
| R1. Untyped eta | Viable only with an enforced same-type contract, or a local type check in the eta rule. Test different records with the same layout, different instantiations of one record, metavariables before and after their types are solved | Contract (§7.3), with the call-site survey; eta off in `first_order`; tests in §14 |
| R2. Eta for existing types | Default for eligible new records; deliberate migration of `Pair`, `Sig`, `SigMap`; kernel-checked eligibility separate from syntax and JS; mode immutable and part of identity and caches | Adopted (§7.1, §12) |
| R3. Unfolding | Restriction is good; decide it from the completed group; test `Box (List Nat)` and nested `Box`; argue in two parts | Adopted (§7.4) |
| R4. Size change for records | Flatten into stable field paths, one layer, dependent fields as a telescope; rebuilt records aren't descendants; refuse `loop r = loop { r \| list = r.list }`; a later feature | Adopted (§6.4, §7.5) |
| R5. Positivity through structural records | Not addressed (stage 3 is deferred) | Unchanged |
| R6. `Has` laws, user evidence | Split reading from same-type replacement; the lens laws don't say other fields are unchanged; user evidence needs a stated contract; defer | Adopted (§9.2, §9.3) |
| R7. `==` and proof fields | Derive only a checked decision for the whole record; proof uniqueness, not data-only comparison; transport for dependent fields | Adopted (§11.4) |
| R8. `Prop` eta | None for this milestone; eta for a proof record isn't proof irrelevance | Adopted (§7.1) |
| (not asked) Evaluation order | Field expressions in source order, then assemble; base once | Adopted (§6.1) |
| (not asked) Hashes | Field names for all data types, representation flag, eta mode; no cache reuse across semantic changes | Adopted (§12) |
| (not asked) TypeScript | Aliases are structural; exportability narrower than well-formedness | Adopted (§11) |

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
  non-recursive records in `Type` with at least one field**, as a
  kernel-validated mode of the declaration (default for new records, opt-in
  for existing types), implemented as in Lean 4's kernel: untyped one-sided
  eta in conversion (a constructor of `D` against a neutral compares
  fieldwise with projections), and a `Case` on a neutral of such a type
  takes its only branch with projections as fields (Lean's
  `toCtorWhenStructure`). Dropping Lean's type check is justified by a
  **same-type contract** on every conversion call (§7.3), surveyed call by
  call. The model is Σ with surjective pairing, and Abel and Coquand's
  untyped algorithmic equality for it [P1]; the restriction to
  non-recursive records follows Lean [L3] (Agda is more permissive [A1]),
  and is half of what keeps unfolding terminating (§7.4).
- Stage 3 interns each anonymous record type as a canonical generated data
  type keyed by its **sorted label set** (and the universe levels of its
  fields), parameterised by the field types. Equality up to field order then
  is ordinary conversion. Two kernel changes: such types are hashed by
  their labels rather than a module and name (Dhall's canonical sorted
  encoding [H1] is the precedent), and positivity looks through them,
  which is safe because their fields are exactly their parameters.
- Stage 4 is Ohori-style "kinded" record polymorphism [R4], compiled by
  evidence passing: `{ name : Text | r }` elaborates to a type variable `r`
  with a constraint `HasField.name r Text` whose evidence is a getter
  (and a separate `CanSetField` for updates), found the way `auto` finds
  proofs. No rows or lacks predicates
  in the kernel. It doesn't support extension or restriction, so the
  existing ability rows' unenforced lacks constraints and declaration-order
  canonicalisation (`TODO.md`) don't arise for records.
- Dependent fields are allowed only in declared records. Anonymous records
  and `HasField` constraints are non-dependent, as DESIGN §9 already separates
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
override it. That default includes **recursive inductive records**
("Inductive record types … have η-equality enabled by default"), which may
then be matched and recursed on; but "η-equality is not always safe for
recursive records as it could lead to infinite η-expansion", so Agda warns
about *unguarded* records with eta (`UnguardedEtaRecord`), a check its
manual calls imperfect. For coinductive records eta "could easily make Agda
loop" and isn't allowed. Pattern matching on an inductive record without
eta isn't allowed by default. (Draft 1.1 wrongly said Agda's default
excludes recursive records; this note's restriction is stricter than
Agda's.) Internally, Agda replaces matches on record constructors
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
| **R2** `HasField`/`CanSetField` constraints (Ohori [R4], Elm [S3], GHC `HasField` [S6]) | `r` is the whole record type; `[has : HasField.name r Text]` is evidence: a getter (a setter is a separate `CanSetField`, §9.2) | read, same-type update, on nominal *and* structural records | none (evidence is an ordinary data type) | independent |
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
non-recursive records in `Type` with at least one field, on by default for
new record declarations and opt-in for existing types (§7).

### 4.6 Field access and inference

`p.name` needs to know `p`'s type. Options: (a) require it to be known when
`p.name` is elaborated (Lean's dot notation needs the head symbol; stage 1);
(b) postpone; (c) with R2, emit a `HasField.name ?t ?a` obligation and solve it at
the end of the declaration, as `auto` obligations already are, which gives
inference for lambdas like `map (p => p.name) people` (stage 4).

### 4.7 Pattern matching

Record patterns `{ name = n, age = a }`, punned `{ name, age }`, and partial
`{ name, .. }`, compiled to the single-branch `Case` the kernel already has.
With stage 2's eta, such a `Case` never blocks for an eta record (Lean's
`to_cnstr_when_structure` [L3]; Agda's translation to projections [A2]).
Record patterns are part of stage 1; they're resolved by the type of what
they match, like `p.name`.

## 5. Recommendation

1. **Stage 1, declared records by translation (no kernel change except
   hashing field names).** `type Person = { … }`, dependent fields, generated
   projections, literals, update with dependent re-establishment, patterns,
   `p.name` on known types, untagged JS objects and a named TS type.
2. **Stage 2, primitive projections and eta for non-recursive records in
   `Type` with fields**, under the same-type contract of §7.3. A small,
   well-precedented kernel addition (§7). Doing it second keeps stage 1 free
   of trusted changes while the surface and JS forms settle.
3. **Stage 3, anonymous structural records** as interned canonical data
   types (§8). Non-dependent.
4. **Stage 4, `HasField` and `CanSetField` constraints** for
   `{ name : Text | r }` (§9).
5. **Not planned:** extension and restriction (§10), kernel rows, first-class
   labels.

Stages 1 and 2 are what proofs and the JS use case need most. Stages 3 and 4
are the "structural, row-polymorphic" goal; neither depends on the other, so
their order is a matter of taste (question U3).

## 6. Stage 1: declared records, by translation

### 6.1 Surface

```
type Person = { name : Text, age : Nat }

def alice : Person := { name = "Alice", age = 30 }

def birthday (p : Person) : Person := { p | age = p.age + 1 }

def describe : Person -> Text
  | { name, age } => name ++ " is " ++ natToText age

-- Parameters and dependent fields, as for data types.
type Sized (a : Type) = { items : List a, size : Nat, ok : length items = size }

def IsSorted : List Nat -> Prop
type SortedList = { items : List Nat, sorted : IsSorted items }
```

- **Literals** are checked against an expected record type (bidirectional
  checking already supplies one in arguments, annotated `let`s and
  signatures). Every field must be given exactly once, in any order.
  Without an expected type (`let p = { name = "A", age = 3 }`), stage 1
  says "can't tell which record type this is; add `: Person`". Stage 3
  changes this: such a literal gets an anonymous record type (U6).
- **Evaluation order.** Each supplied field expression is evaluated exactly
  once, **in the order written**; then the constructor is assembled in
  declaration order. So with `type R = { a : Nat, b : Nat }`,
  `{ b = readNumber (), a = readNumber () }` reads `b` first. Elaboration
  checks fields in declaration order (later fields' types mention earlier
  fields), which is a separate matter from the order they run in, and
  doesn't change it. In pure code the order isn't observable (the language
  is pure and total), so the literal compiles straight to the constructor.
  In a computation, fields that perform operations are run first, in source
  order, into variables, exactly as effectful arguments of a call are
  (`docs/core.md`, Abilities), and the constructor is built from those
  variables. A field run that way may not have a type mentioning another
  field: its type has to be known before the fields after it run.
- **Access** `p.name` binds tighter than application (`f p.name` is
  `f (p.name)`), as in Idris [I1]. **Resolution:** the elaborator infers
  `p`'s type and reduces it; if it's a declared record `R ps` with a field
  `name`, `p.name` is `R.name [ps] p` (stage 2: `Proj`). If the type is a
  record without that field, `E-UNKNOWN-FIELD`, listing the fields. If it's
  not a record (a data type, a function), `E-NOT-A-RECORD`. If it isn't
  known yet (an unsolved unknown, as in `p => p.name` with no expected
  type), `E-CANNOT-INFER`, suggesting an annotation (`(p : Person) =>
  p.name`); stage 4 can turn this case into a `HasField` obligation instead
  (§4.6). Field names are looked up in the record's own declaration only:
  two record types may have fields of the same name, and nothing is guessed
  from field names. A lexer change adds `.`, valid only directly between an
  expression and a field name, with no spaces (`p.name`, `(f x).name`,
  `p.address.city`). Generated names like `State.elim` are never written in
  source.
- **Update** `{ p | f₁ = e₁, … }`. The elaborator computes, from the
  declaration, which later fields' types mention each updated field,
  transitively, and requires each of those to be updated too:

  ```
  { s | items = [2, 1] }                          -- E-RECORD-UPDATE: `sorted`
                                                  -- depends on `items`
  { s | items = xs', sorted = proofAbout xs' }    -- fine
  ```

  This is DESIGN §9's rule; it's a convenience, since the kernel re-checks
  the constructor application anyway. **The base is evaluated once**, before
  the new field expressions: when it isn't a variable, it's bound to one
  first, and the fields that aren't replaced are projections of that
  variable. The base expression is never copied into each projection.

  **An update can change the record's type parameters** (added 23 October
  2026), as Haskell's record update does: a parameter can change only if
  every field whose type mentions it is replaced, and no other parameter's
  type depends on it. With `type Timed (a: Type) = { start: a, end: a, label:
  Text }` and `t: Timed Int`:

  ```
  { t | start = Int.toNat t.start, end = Int.toNat t.end }   -- a `Timed Nat`
  { t | start = Int.toNat t.start }                          -- E-RECORD-UPDATE: the kept `end` has type `a`
  ```

  Checked against an expected type `Timed Nat`, the base's own type is
  learnt first (inferred, then undone); if it already is the expected type
  the update is elaborated as before, otherwise each parameter that differs
  must be one only replaced fields mention, or the error names the kept
  field that fixes it. With no expected type, the update is first elaborated
  as before, at the base's parameters (so `{ t | start = 5 }` stays a `Timed
  Int`); only if that fails do the parameters only replaced fields mention
  become new unknowns, which the new fields settle. The term is the same
  constructor application either way, since constructors carry no type
  arguments, so no hash moves. (A variant's fields will be updated by
  `match` (docs/proposals/variant-fields.md); that is a different form and
  doesn't use this rule.)
- **Patterns** `{ name = n, age = a }`, `{ name, age }` (punning), and
  `{ name, .. }` (the rest ignored), nested inside other patterns. Like
  `p.name`, a record pattern is resolved by the type of what it matches, so
  that type must be known: a parameter's type from the signature, or a
  field's type from the constructor matched around it.
- **Equality** `==`: see §11.4.
- **Recursive and mutually recursive records** are allowed by the data-type
  rules: e.g. `type Tree = | Leaf | Node Info` with
  `type Info = { label : Text, left : Tree, right : Tree }`, one data group.
  A record whose field has its own type directly (`{ value : Nat, next :
  Node }`) has no values at all; a useful self-reference goes through
  another type (`next : Maybe Node`), which is a nested occurrence that
  positivity refuses today (`TODO.md`), or through a function field. So in
  practice recursion goes through a mutual group.
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

with `Person.mk` and the projections not nameable in source. Projections
with dependent result types work today: `SortedList.sorted : (s :
SortedList) -> IsSorted (SortedList.items s)` is defined by a case that
refines `s` to `SortedList.mk i p`, against which `SortedList.items s`
computes to `i`. A projection out of a `Prop` record into data isn't
generated, since the kernel would refuse it (`E-PROP-ELIM`).

The elaborator records which data types are records, for the JS generator
and for messages. That flag is a *representation* choice (no `tag` in JS);
it's hashed (§12), but the kernel never relies on it for soundness. Stage 2's
eta eligibility is a separate, kernel-checked property (§7.1).

### 6.3 What stage 1 can't do

- `{ p | age = p.age } = p` isn't `rfl` (it's `Person.mk (Person.name p)
  (Person.age p)` against a neutral `p`). It's provable once per type
  (`etaPerson p : p = …` by matching `p`); stage 2 removes the need.
- A definition that matches on an unknown record stays folded.
- `.name` on an unknown type needs an annotation.

### 6.4 Termination

Unchanged in stage 1: no new principle. Matching a record parameter binds
its fields as `<` the parameter, as for any constructor; `p.field` is a call
of a generated definition, so its result is *unknown* for size change, and a
recursive call on a rebuilt record is unknown too. So
`sum { list = Cons x xs, acc } = sum { list = xs, acc = acc + x }` is
refused, and users pass the fields as separate arguments.

**Later (not stage 1 or 2): field paths.** The fix is to treat a known record
parameter as its fields for size change, each field a separate,
**stable field path** (`r.list`, `r.acc`), justified by the correspondence
with passing those fields as separate arguments, not merely by "a record is
determined by its fields". For `sum` the graph is then

```
caller.list → callee.list : <
caller.acc  → callee.acc  : unknown
```

and it's accepted. The record built for the call is *not* a descendant of
the parameter: only its components are compared, path by path. So
`loop r = loop { r | list = r.list }` is refused: its `list` component is
unchanged (`≤`), and nothing is `<`. Only one record layer is flattened at
first, with dependent fields kept as a telescope (a later field's path is
still a column, its type mentioning earlier columns); deeper flattening can
follow. Descent is only ever taken from certified provenance (a field of an
actual parameter, or of a known descendant), never from a term's type
happening to be a record, or from eta relating it to another term.

### 6.5 As built (stage 1)

Built on 16 October 2026, as §6.1–§6.4 describe, with these details and
limits.

**Surface.**

```
type Person = { name : Text, age : Nat }             -- or one field per line
type Sized (a : Type) = { items : List a, size : Nat, ok : length items = size }

alice : Person
alice = { name = "Alice", age = 30 }                  -- any order; `{ name, age }` puns
birthday : Person -> Person
birthday p = { p | age = p.age + 1 }
describe : Person -> Text
describe { name, age } = name ++ " is " ++ natToText age
firstLead (Cons { lead = { name, .. }, .. } rest) = name
```

- **Declaration.** `type R (params) : sort = { field : T, … }` is a data type
  with one constructor, `R.mk`, whose fields are the record's. `{}` is a
  record with no fields. A field name given twice is `E-DUPLICATE`.
- **Literal** `{ f = e, … }`, with punning `{ f }`. Checked against the
  expected type; with none, `E-CANNOT-INFER` suggesting `(… : Person)`. An
  unknown field is `E-UNKNOWN-FIELD` (listing the fields), a missing or
  repeated one `E-RECORD-FIELD`. Against a type that isn't a record,
  `E-NOT-A-RECORD`.
- **Access** `e.f`, written with no spaces around the `.` (otherwise
  `E-PARSE`), binds tighter than application and chains (`t.lead.name`,
  `(f x).age`). **Resolution:** the elaborator infers `e`'s type and reduces
  it. A declared record with a field `f` gives the projection `R.f` applied
  to the record's parameters and `e`; a record without `f` is
  `E-UNKNOWN-FIELD`; any other known type is `E-NOT-A-RECORD`; an unknown
  type (a lambda's parameter with nothing to say what it is) is
  `E-CANNOT-INFER`, suggesting `(p : Person) => p.name`. Field names are
  looked up only in the record's own declaration, never across records.
  `R.f` can't be written in source: there, `Person.name` is field access on
  `Person`, which isn't a record.
- **Update** `{ base | f = e, … }`: checked against the expected type, or
  its type inferred from `base`. A non-replaced later field whose type
  mentions a replaced one is `E-RECORD-UPDATE`.
- **Patterns** `{ f = p, g, .. }`, nested anywhere a pattern can be,
  resolved by the type of what they match: a parameter's type from the
  signature, or a field's type from the constructor matched around it (the
  pattern compiler now carries each column's type where it's known). A
  constructor pattern after `=` takes its arguments without parentheses
  (`{ items = Cons x xs, .. }`). A field left out without `..` is
  `E-RECORD-FIELD`.
- **In a function type's result**, `{` starts an ability row
  (`Nat -> {IO} Nat`), so a record literal there needs parentheses:
  `(p : Person) -> ({ p | age = p.age } = p)`.
- **`Prop` records** are allowed; their proof fields have projections, their
  data fields don't, and reading one is `E-PROP-ELIM`.

**What the kernel sees.** As §6.2: the data type, flagged as a record
(`Data::record`, set by `declare_data_group_as`, fixed at declaration;
`define_data_group` refuses a record without exactly one constructor), and
one generated definition per field, `R.f : [params] -> R params -> T`, by a
one-branch case, in which earlier fields are projections
(`Sized.ok : (r : Sized) -> length (Sized.items r) = Sized.size r`). The
kernel uses the flag only for hashing; nothing in checking depends on it.

**Evaluation order** (§6.1). In pure code a literal is the constructor,
fields in declaration order (the order isn't observable). In a
computation, the elaborator runs an update's base, then each field
expression that performs operations, in the order written, binding each
result to a variable (the mechanism effectful arguments already use), and
then builds the record from those variables: `{ b = next (), a = next () }`
reads `b` first (`examples/accept/records-effects.sw`). An update whose
base isn't a variable binds it to one first (`(r => R.mk … (R.f r) …)
base`), so the base is evaluated once and never copied into each
projection. One consequence: in `{ e | … }` with `e` not a variable, the
new fields are checked knowing only that the base is *some* `R`, not that
it's `e`.

**`==`** (§11.4). For a record `R` with no parameters whose fields are all
data, none depending on another, and each with a decision procedure for
`=` when `R` is checked, the elaborator derives `R.decEq : (r s : R) ->
Decidable (r = s)`, an ordinary definition (generated as source and
checked like user code): it matches both records, decides each field with
`if h : a = b`, proves equality by transporting along each field's proof
in turn, and refutes with `cong R.f`. `==` finds it like any decision
procedure. Otherwise nothing is derived, and `==` on `R` is `E-AUTO-NONE`
with a note saying why (a proof or type field, a dependent field,
parameters, or a field type without a decision procedure). Proof-field
records via proof-uniqueness lemmas and dependent fields via transport are
left to the user for now; there's no data-only `sameData`.

**`R.ext`** (SW-263, D503, `derive_ext.rs`). Each record gets a generated
extensionality lemma, like Lean's `@[ext]`: `theorem R.ext [params] (x: R)
(y: R) (f1Eq: x.f1 = y.f1) … : x = y`, one hypothesis for each data field and
none for proof fields. It's source, elaborated as any theorem, so the kernel
re-checks it; the proof is `derive::fields_equal`, the one `==` uses, each
data field's `J` carrying the proof fields along, whose own equality is
`DecEq.uniqueEq` (there's no definitional proof irrelevance, SW-93). So it
exists for the records `==` can be derived for, except that data fields need
no `DecEq` and may be functions, types of fields containing `R` are fine, and
a data field may not depend on an earlier field (the hypothesis `x.f = y.f`
wouldn't be well typed). A proof field must prove an equation in a type with
`DecEq` that mentions neither `R` nor a type parameter (a proof of an `Or`
has two different proofs). Records with no data fields get `R.ext x y: x = y`
(`{}` too). Parameters, value parameters and `auto` parameters are binders.
Not generated for interfaces, `Prop` records, records in a mutual group or
with indices; then `R.ext` is an unknown name. A module declaring its own
`R.ext` (found by the names of its items) keeps it, with no error. The library's records are skipped (the lazy-loading index lists names
from source, so a generated one would be unpromised): `Std.Mod` keeps its hand-written `Mod.ext`. A generated one is at the record's position, for
hover and go-to.

**Termination.** No new principle (§6.4): a record pattern binds its fields
as `<` the record, like any constructor; `p.f` is a call, so unknown for
size change. The `sum` example is refused; field-path descent is later.

**JavaScript.** A record is a plain object without a tag, keys in declared
order, the same inside the generated code and at the boundary. Keys follow
DESIGN §12 except that a field `tag` keeps the key `tag` (`record_key`);
`__proto__` is still `$__proto__`. A record case reads its fields with no
`switch`. The `.d.ts` has a named alias, structural like every TS object
type:

```ts
export type Person = { readonly name: string; readonly age: bigint };
export type Box<a> = { readonly value: a };
export type SortedList = { readonly items: readonly bigint[] };  // `ok` omitted
```

Decoding is the existing strict decoder without the tag (own properties
only, each read once, extra ones ignored, arrays refused). **Proof fields
coming in:** when an export's parameter or result contains a record with
a proof field, the elaborator finds a decision procedure for the field's
proposition (in the context of the parameters and earlier fields), which
the kernel type-checks (`add_field_validator`, stored on the data type),
and the decoder runs it on each decoded object of that type, refusing the
input (`s: proof field `ok` (`length items = size`) doesn't hold`) if it
doesn't say `Yes`. A proof field without one makes the export `E-EXPORT`.
A record with a type-valued field still can't cross. Ordinary data types
with proof fields are still refused at the boundary, as before.

**Hashes** (§12). Every data type's hash now covers its fields' names and
the record flag. This changed the hash of every data type (and everything
using one); the pinned hashes of `List`, `Char`, the text natives and the
prelude's `add` were updated after checking that, with field names left
out, the old values still came out.

**Tests.** Parser tests (declarations, literals, updates, punning, access
precedence and spacing, patterns); `crates/driver/tests/records.rs` (the
record flag is hashed, a record has exactly one constructor, the kernel
checks field validators, generated projection types, derived `==` on every
field); `crates/cli/tests/caching.rs` (renaming or reordering a field
changes the hash, layout doesn't); `examples/accept/records.sw` and
`records-effects.sw`; thirteen rejects (`record-*`,
`export-record-unchecked-proof`), each with an accepted neighbour;
`examples/extract/records.sw` with differential runs, random inputs
(proof fields judged by the reference evaluator), `tsc`, and
`records_cross_the_boundary_strictly`; records added to
`awkward_names_never_collide`. Manual mutations, each caught: running a
literal's effectful fields in reverse (two `records-effects` tests fail);
dropping the decoder's proof-field checks (`records_cross_the_boundary_strictly`
and the random differential test fail); disabling `E-RECORD-UPDATE` (the
reject then fails for the wrong reason, a type mismatch, so the kernel's
check backs the rule).

**Not done in stage 1.** Proof-uniqueness and transport for `==`;
`(.name)` sections; anonymous record types (`{ x : Nat }` as a type isn't
parsed); validators for ordinary data types' proof fields; printing `R.f r`
as `r.f` in messages (records themselves print as literals); a generated
`etaR` lemma.

**What stage 2 needs from this.** Replace the generated projections of eta
records by `Proj` (keeping them for records without eta, §8.6), add the
eta mode next to the record flag in `declare_data_group_as` and the hash,
and add §14's stage-2 tests. The elaborator's `RecordInfo` (projections per
field, and why `==` wasn't derived) is the start of §8.6's field
description.

## 7. Stage 2: projections and eta in the kernel

### 7.1 Which records

Eta is a **mode** a data declaration is admitted with, separate from the
record flag (JS representation) and from record syntax:

- **New record declarations** (`type R = { … }`) ask for eta by default.
  Another syntax may ask for it on an ordinary single-constructor data type,
  and `no-eta` may turn it off for a record (spelling to settle).
- **Existing data types** (`Pair`, `Sig`, `SigMap`, `UnitType`) keep no eta
  until they're migrated deliberately, one at a time, each after its tests
  pass. `Pair` gaining eta wouldn't change its JS form: it keeps its `tag`.

The kernel **validates** a requested eta mode when the data group is
admitted, from the completed, immutable group, and refuses the declaration
(`E-ETA`) unless the type:
1. has exactly one constructor and no indices (Stitchwort has none anyway);
2. lives in `Type i`, not `Prop`;
3. is **non-recursive**: its data group is just itself, and no field type
   mentions it;
4. has **at least one field**.

The mode is fixed at admission, never changed afterwards, and hashed (§12).

Condition 3 is what keeps unfolding finite (§7.4). It's read from the
kernel's group, so `type T = Leaf | Node R` with `R = { kid : T, n : Nat }`
puts `R` in a recursive group and refuses eta for it, however `R` was
written. Condition 2: eta for a `Prop` record isn't needed for this
milestone, and projecting data out of a proof must stay forbidden (Lean
checks this in `infer_proj` [L3]). (Eta for a proof record wouldn't amount
to proof irrelevance: rebuilding a proof from its projections doesn't
equate arbitrary proofs of its fields.) Condition 4: eta for a record with
no fields means any two values are equal, which needs the values' types
(Lean's `is_def_eq_unit_like` [L3]). The untyped conversion here can't see
them, and the half-measure in draft 1.1 (`{}` equal to any neutral, two
neutrals unequal) isn't transitive. So zero-field types get neither eta
rule, including the non-blocking `Case`.

### 7.2 New core forms

- `Proj(D, i, t)`: field `i` of `t`, where `t : D ps` and `D` has eta.
  Records without eta keep their generated projections (§7.7, §8.6).
- `Elim::Proj(D, i)` on neutral spines, so `Proj` of a stuck value is
  neutral.

**Typing** (`infer`): infer `t`'s type, reduce it to `Data(D', ps)`, and
**require `D' = D`** (the Lean bug [L4]), `D` eligible and `i` in range.
The type is field `i`'s declared type with the parameters `ps` and
`Proj(D, j, t)` for each earlier field `j` substituted. This is the
dependent Σ rule for the second projection, generalised to a telescope.

**Evaluation:** `Proj(D, i, Ctor(D, 0, fs)) ⟶ fs[i]`; on a neutral, push
`Elim::Proj(D, i)`. A `Proj` whose `D` doesn't match the constructor's data
type is stuck (as Lean's `reduce_proj_core` refuses [L3]); only an
ill-typed term could reach that.

### 7.3 Eta in conversion

Two rules, both reading `D` from the term:

1. **One-sided eta.** `Ctor(D, 0, fs) ≡ n`, for `D` with eta and `n` not a
   constructor, holds when `fs[i] ≡ Proj(D, i, n)` for every field `i`
   (and symmetrically). This is Lean's `try_eta_struct_core` [L3] without
   its type comparison, and the shape of Abel and Coquand's untyped
   algorithm for surjective pairs [P1].
2. **A `Case` on a neutral eta record takes its only branch**, with the
   fields bound to `Proj(D, i, x)` (Lean's `to_cnstr_when_structure` [L3]).
   Since `Case(x, D, …)` names `D`, no types are needed. This makes record
   patterns non-blocking.

Rule 1 drops Lean's type check, so it's only sound if the two sides have
the same type. Draft 2 makes that a **contract**, rather than an assumption:

> **Contract.** The kernel's `conv(a, b)` is only called on two values of
> one established type `A` (or on two types), and every pair it compares
> along the way is at corresponding positions of structures whose earlier
> positions have already compared equal, so they have one type too.

**The call sites** (at commit `9ab274e`):

| Caller | Compares | Same type because |
|---|---|---|
| kernel `check`, `Refl ⇐ a = b` (`check.rs`) | the two sides of an `Eq(A, a, b)` | the kernel built that `Eq` by inferring `a : A` and checking `b ⇐ A` |
| kernel `check`, fallback (`check.rs`) | an inferred type with an expected type | both are types; a type is never a constructor value, so rule 1 can't fire at the top, only inside |
| elaborator `same_header` (`lib.rs`) | two data groups' parameter types | both are types |
| `conv`'s own steps (`value.rs`) | `Pi` domains then codomains; `Data` arguments; `Ctor` fields; `Eq` type then sides; neutral spines with the same head; eta for functions and partly applied definitions | each pair sits at the same position of a telescope (parameters, fields, spine of one head) whose earlier positions compared equal first (the work list goes left to right and stops at the first difference), so the pair has one type |

Why the last row is enough: `conv` returns one boolean, the conjunction of
every comparison it makes. A pair at a later telescope position might have
different types if an earlier position differs, but then the earlier
comparison is `false` and so is the result; a `true` result means every
comparison made had one type. The eta step itself keeps the invariant:
`Ctor(D, 0, fs) : A` forces `A ≡ D ps`, so `n : D ps`, and `fs[i]` and
`Proj(D, i, n)` both have field `i`'s type once the earlier fields agree. A
heterogeneous comparison inside a `false` result is harmless: the budget
bounds it, and it changes nothing. There's no conversion cache today; any
future one must store only results of top-level, contract-respecting calls.

**The elaborator's unification** (`unify.rs`) is untrusted (the kernel
re-checks), but a wrong solution there still means a confusing error, so it
gets the same rules with two additions:

- its top-level calls compare a found type with an expected type
  (`check.rs`, `effects.rs`), a hypothesis's type with a goal (`auto.rs`),
  or a metavariable with a value found for it at its own type (`auto.rs`);
  all respect the contract;
- **metavariables are solved before eta is tried**, so `?m ≡ Ctor(D, …)`
  assigns `?m` rather than splitting into `Proj(D, i, ?m)` problems;
- the **`first_order` fallback** (`?m … x ≡ f … y` tried as `x ≡ y`,
  then `?m … ≡ f …`) compares arguments whose types needn't agree, since
  `?m`'s type may still be unknown. **Eta is off inside it.** This is the
  one place the contract fails, so it doesn't rely on it.

A local type-compatibility check in the eta rule (the review's alternative)
would need the type of the neutral side, which the untyped conversion
doesn't have; that's why draft 2 takes the contract.

Tests (raw-kernel and elaborator; §14): two nominal records with identical
layouts (`Person` and `Pet`, both `{ name : Text, age : Nat }`): a
`Ctor(Person, …)` against a neutral `Pet` is never equal, and
`Proj(Person, 0, pet)` is refused; two instantiations of one parameterised
record (`Box Nat` and `Box Bool`) don't convert, and a `Box Nat` literal
doesn't check against `Box Bool`; a metavariable whose type is still unknown
against a record literal, before and after its type is solved, gives the
same accepted programs, and ill-typed comparisons produce no accepted
solution.

### 7.4 Why unfolding still terminates

In two parts.

1. **Record-only expansion can't go on forever.** Rule 1 replaces a
   comparison of `Ctor(D, 0, fs)` with comparisons of its fields, which are
   strictly smaller terms. Rule 2 takes one `Case` node of a finite case
   tree; it creates no `Case` nodes. Following projections of a neutral
   `x : D ps` reaches, after as many steps as the *instantiated* type's
   record nesting, a field whose type isn't an eta record, where a `Case`
   blocks as before. That depth is finite for any given value because its
   type is a finite term: `Box (Box (Box Nat))` has three layers even though
   it uses one declaration three times. Non-recursiveness of the declaration
   alone wouldn't be the whole argument: it's the instantiated type that
   bounds the depth.
2. **Recursive unfolding is governed by size change, as before.** A
   recursive definition whose case tree only splits eta records now unfolds
   on unknown arguments. Each recursive call that the termination checker
   accepts makes some argument `<` a parameter, through fields of matched
   values; for an unknown argument, that's a chain of projections, each a
   field of the previous one. By part 1 such a chain ends at a non-record
   field, where the next `Case` blocks. A call on a rebuilt record never
   counts as `<` (§6.4), so a definition can't keep re-wrapping an unknown
   value. (This is an argument, not a proof.)

Tests: `type Box (a : Type) = { value : a }`. On a neutral `b : Box (List
Nat)`, a definition matching `{ value = Nil }` / `{ value = Cons x xs }`
takes the outer record match and then **blocks** on `b.value`; the same at
`Box (Box (Box (List Nat)))`; and `type T = Leaf | Node R`,
`R = { kid : T, n : Nat }` (no eta for `R`, which is in a recursive group),
checking terminates.

Agda, by comparison, allows eta for recursive inductive records by default
and warns about unguarded ones [A1]. Condition 3 here is stricter.

### 7.5 Termination checking

A projection of a parameter, or of a known descendant, is a **descendant**
(`<`): `Proj(D, i, x)` is a field of the value `x`. This is the provenance
rule: descent comes from `x` being a parameter or descendant, never from a
term's type being a record or from eta relating it to something else. With
stage 2, record patterns still compile to `Case` (their fields are
classified as today), and `p.field` in expressions becomes `Proj`,
classified by this rule. Flattening a record parameter into field paths
(§6.4) is a separate, later feature.

### 7.6 Soundness argument

- **Consistency.** In the set-theoretic model where `D ps` is the set of
  tuples of its fields, `Proj` is the coordinate function, and every element
  is the tuple of its coordinates, so both eta rules hold. Nothing else in
  the model changes. (The standard argument for Σ with surjective pairing;
  for the kernel as implemented it's an argument, not a proof.)
- **Type preservation.** Rule 2 replaces `x` by `Ctor(D, 0, Proj…)` in a
  branch whose checking already assumed `x = Ctor(D, 0, fields)`, with
  fields of the right types by the `Proj` typing rule.
- **Same types.** §7.3's contract, kept by every call site.
- **Decidability.** §7.4.
- **The danger case** is a `Proj` naming one type applied to a value of
  another, which is exactly the Lean CVE [L4]: typing checks `D' = D`, and
  evaluation refuses mismatches.

### 7.7 Stage 1 code under stage 2

For eta records the elaborator stops generating `Person.name` as a case
tree and emits `Proj(Person, 0, p)`. Hashes of everything using records
change once; that's acceptable (DESIGN §11: backwards compatibility isn't a
goal). Records without eta (recursive or `Prop` ones, or `no-eta`) keep
their generated projections.

## 8. Stage 3: anonymous structural records

### 8.1 Surface

```
def divMod (n d : Nat) [auto ok : d != 0] : { quotient : Nat, remainder : Nat } :=
  { quotient = n / d, remainder = n % d }

-- The same type, written in another order:
def check (r : { remainder : Nat, quotient : Nat }) : Bool := r.remainder < 10

test "order doesn't matter" := check (divMod 7 3)

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

### 8.6 What stages 1 and 2 must keep possible

Stages 3 and 4 are deferred (U3), so stages 1 and 2 keep a **field
description** for every record, generic and separate from its nominal
identity:

- the labels, in declaration order;
- each field's type, and which earlier fields it depends on;
- which fields are erased (proofs and types);
- **how to access a field**: a generated projection (stage 1, and later for
  records without eta: recursive ones, `Prop` ones, `no-eta` ones) or a
  primitive `Proj` (stage 2 eta records). Generic field lookup (`p.name`,
  stage 4's derived evidence) chooses whichever the record has, and nothing
  may assume every record has primitive projections.

A declared record's identity is its declaration (module and name, §12); the
description is what an anonymous record with the same fields would share
with it. Stage 3 builds its canonical types from descriptions; stage 4's
derived `HasField` evidence reads them.

## 9. Stage 4: functions over "any record with field `x`"

### 9.1 Surface

```
def greet (x : { name : Text | r }) : Text := "Hello, " ++ x.name

def birthday (p : { age : Nat | r }) : { age : Nat | r } := { p | age = p.age + 1 }

-- Works on declared and anonymous records alike:
test "greet" := greet alice == "Hello, Alice"
test "greet anon" := greet { name = "Bob", shoeSize = 9 } == "Hello, Bob"
```

The type variable `r` stands for **the whole record type**, constrained to
have the listed fields. (In Gaster–Jones or PureScript, `r` would be "the
other fields". With no extension or restriction the difference isn't
observable, and Elm's `{ r | name : String }` reads the same way.) Several
annotations mentioning the same `r` combine their fields.

### 9.2 Translation

Reading and replacing a field are **separate capabilities**. For each label
`name` used this way, the elaborator interns (like §8.2)

```
type HasField.name (t : Type) (a : Type) : Type =
  | HasField.name.mk (get : t -> a)

type CanSetField.name (t : Type) (a : Type) : Type =
  | CanSetField.name.mk (set : a -> t -> t)
```

`{ name : Text | r }` asks only for `HasField.name r Text`; a function that
updates `name` (`{ x | name = … }` with `x : r`) asks for `CanSetField` as
well. So

```
def greet [r : Type] [auto has : HasField.name r Text] (x : r) : Text := "Hello, " ++ HasField.name.get has x

def birthday [r : Type] [auto has : HasField.age r Nat]
  [auto set : CanSetField.age r Nat] (p : r) : r := CanSetField.age.set set (HasField.age.get has p + 1) p
```

This matters for records with invariants: a function that only reads `items`
can accept a `SortedList`, since reading never breaks `sorted`; only
replacing `items` on its own would.

**Finding the evidence**, in `auto`'s order (DESIGN §6):
1. supplied explicitly, `[has := …]`;
2. a hypothesis in scope with that type (inside another polymorphic
   function, its own `has`);
3. **derived** when `r` is a known record type with a field `name : A`,
   from its field description (§8.6): `get` is the field's access
   implementation; `set` rebuilds the record with the other fields by
   access. `A` is determined by `r` and `name` (GHC's functional dependency
   `x r -> a` [S6]), so derivation can solve an unknown `a`.

`HasField` is derived for any field whose type doesn't depend on earlier
fields (otherwise its type isn't a fixed `A`). `CanSetField` is derived
only when, in addition, no later field depends on it: setting it alone
would break the later field. So `HasField.items SortedList (List Nat)` is
derived and `CanSetField.items SortedList (List Nat)` isn't; a function
that changes `items` uses `SortedList`'s own functions, or a dependent
update.

**Inference of `.name` on unknown types** (§4.6 (c)): when `x`'s type is an
unknown `?t`, `x.name` elaborates to `HasField.name.get ?h x` with an
obligation `HasField.name ?t ?a`, solved after the declaration like other
`auto` obligations, once `?t` is known. A leftover unsolved `?t` is
`E-UNSOLVED` as now. When `t` turns out to be a known record, the elaborator
can simplify `get` of derived evidence to the field's access implementation
(it's equal by computation anyway).

### 9.3 Laws (optional)

Evidence could also carry erased proofs of the lens laws (`get (set v x) =
v`, `set (get x) x = x`, `set v (set w x) = set v x`), so that proofs about
polymorphic functions can use them. For derived evidence each is `rfl`
under stage 2's eta (the second is exactly eta). The three laws don't say
that *other* named fields are unchanged by `set`; derived setters do keep
them, but user-supplied evidence (GHC's "virtual fields" [S6]) would need a
clearly stated contract saying so, or a law per other field. Whether to
include laws, and whether to allow user evidence, stays open with stage 4
(R6).

### 9.4 Why not rows here

R2 needs nothing from the ability-row machinery: no row variable of a row
kind, no lacks constraints (a `HasField` constraint never adds a field, so
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
| `HasField.name r A` evidence | an object `{ get }` | never at the boundary |

A record is the only single-constructor data shape that loses its `tag`:
ordinary data types like `Pair` keep it, so existing `.d.ts` files don't
change, and stage 2 giving `Pair` eta (§7.1) wouldn't change them either.

**Nominal in Stitchwort isn't nominal in TypeScript.** `Person` and `Pet`
are different Stitchwort types, but their TS aliases are structural, like
every TS object type [T1]: if both are `{ readonly name: string; readonly
age: bigint }`, TS accepts a `Pet` where a `Person` is expected. That
matches the boundary's own behaviour (decoders accept any object with the
right properties), so nothing is lost; the `.d.ts` mustn't suggest
otherwise. Branding (`Person & { readonly __brand: "Person" }`) would be a
separate requirement, not planned.

`Proj(D, i, x)` compiles to `x.key`, and a record `Case` to reading its
fields. Extracted JS performance isn't a goal, but plain property access is
also the fastest form.

### 11.2 Keys

DESIGN §12's field rule applies: a field's key is its name with each prime
as `$`, and `__proto__` becomes `$__proto__` (in an object literal it would
set the prototype). The `tag` rule exists because data objects use a `tag`
key; records don't, so **a record field named `tag` keeps the key `tag`**
(U4). Field names are identifiers starting with a letter, so no key is
integer-like, and JS keeps keys in insertion order.

**Key order** in encoded objects (visible to `Object.keys` and
`JSON.stringify`): declared order for declared records; label order for
anonymous ones, since their type has no other order (U2).

### 11.3 Decoding and validation

A record decoder is the existing data decoder without the tag: the input
must be a non-array object; each field is read once, as an own property, in
declared order; a missing field is refused with its path
(`order.customer.name: missing`); extra properties are ignored. Since TS
allows extra properties on non-literal values [T1], this is TS's own width
subtyping.

**Proof fields in inputs.** A `SortedList` passed *in* has no `sorted`
property: the decoder must re-establish it, so a record field whose type is
a proposition needs a decision procedure, run after decoding, exactly like
an export's `[auto]` precondition (DESIGN §12 rule 3). A proof field with no
decision procedure makes any export that takes the record `E-EXPORT`. As
outputs, proof fields are just omitted. (The same rule applies to ordinary
data types with proof fields.) That the validator can rebuild *a* proof
doesn't make it the proof: neither conversion nor `==` may treat every
original proof as equal to the rebuilt one.

**Exportability is narrower than well-formedness.** A record can be
well-typed without having a JS codec. The existing rules (concrete types
only; each field's type must itself be exportable) apply to records as to
other data types. In particular a record with a type-valued field
(`{ elem : Type, … }`), a function field, or a data field whose type depends
on an earlier data field is well-formed but can't cross the boundary
(`E-EXPORT`), even though its proof fields might be validated.

### 11.4 Equality

`a == b` is `toBool d` for a decision procedure `d : Decidable (a = b)`.
For records, the rule is:

> **Derive `==` only when the generator can build a checked decision for
> the whole record**, `(r s : R) -> Decidable (r = s)`. Otherwise the user
> writes one, and until then `==` on `R` is `E-AUTO-NONE` with a note
> saying why it wasn't derived.

- **Data fields** need a decision procedure for their type.
- **Proof fields** (`sorted : IsSorted items`): two records with equal data
  can still differ in their proofs, and there's no definitional proof
  irrelevance. A derivation may still go through if, for the proof field's
  proposition `P`, a **proof-uniqueness lemma** `(p q : P) -> p = q` is
  available (Hedberg's argument gives one for `x = y` at a type with
  decidable equality, as the prelude's `canonConst`/`fromCanon` do for
  `Bool`). `Decidable P` alone isn't enough: deciding whether `P` holds
  says nothing about whether two proofs of it are equal.
- **Dependent fields**: after an earlier field is shown equal, the later
  field must be *transported* along that equality into the other record's
  type before it's compared. Comparing fields independently isn't a
  decision for a telescope.
- A function comparing only the data fields is fine to have, under another
  name (`sameData`), with a `Bool` result or a decision of a weaker
  proposition; it must never masquerade as `Decidable (r = s)`.

Stage 1 implements the simplest derivable case and refuses the rest with a
message (see "As built").

## 12. Content hashes

- **Field names are hashed, for every data type.** Today a data type's hash
  omits field names (`hash.rs`, `data_hash`). Field names already change
  generated JS keys and `.d.ts` files for ordinary constructors, so DESIGN
  §11's planned generated-JS cache (keyed by definition hash) would serve
  stale code after a field rename today; for records they're semantics too
  (`p.name` resolves by them). This fix is independent of records and comes
  with stage 1.
- **The record flag is hashed**, since it changes the JS representation.
- **The eta mode** (stage 2) is hashed: two declarations that differ only in
  it are different types with different conversion.
- **Caches must not outlive a change of semantics.** Stage 2 changes
  conversion for code whose declarations are unchanged (once a type is
  migrated to eta, say), and the test cache key today is the compiler's
  version number plus the test's hash, not the compiler's code
  (`docs/core.md`). Each such change must bump a *kernel-semantics version*
  that's part of every cache key (or the eta mode must be in the hash, which
  covers migrations, plus a version bump for the rule change itself).
- **Nominal records** are hashed like data types (module and name, per
  DESIGN §11).
- **Anonymous record types** (§8) are hashed by their sorted labels,
  universe levels and the record-flag marker, with no name or module, so
  equal types have equal hashes. Dhall hashes its records the same way, from
  an encoding with sorted fields [H1].
- **`HasField.name`, `CanSetField.name`** types likewise by label.
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
| 2 | `Proj` term and spine elimination; its typing rule (with the `D' = D` check); evaluation; one-sided eta in `conv`; `Case` on a neutral eta record; the eta mode and its eligibility check on the completed group; the termination rule for `Proj`; hashing, quoting, printing | yes | 200–300 lines |
| 3 | Structural-record flag and its well-formedness check; label-based hash; positivity through flagged types | yes | ~100 lines |
| 4 | none | no | 0 |

Outside the kernel but trusted for the JS guarantee (DESIGN §12): the record
encoders and decoders, the proof-field validators, and the key mapping.
The elaborator's record flag is not trusted for anything but the JS form.

## 14. Testing plan

**Stage 1**
- Accept: the DESIGN §4 examples (`alice`, `birthday`, `greet` at a
  concrete type, `SortedList.insert`), dependent `Sized`, record patterns
  and punning, a record in a mutual group, a `Prop` record used to produce a
  proof.
- Must reject: an update of `items` without `sorted` (DESIGN §13's existing
  row, `E-RECORD-UPDATE`), a literal missing a field or with an extra or
  duplicate one, `p.nmae`, `.name` on an unknown type, a literal with no
  expected type, a `Prop` record with a data field matched to produce data
  (`E-PROP-ELIM`), each paired with an accepted neighbour.
- Evaluation order: a literal whose fields are written out of declaration
  order, each performing an operation (`simulate` with scripted input
  shows which ran first); an update whose base performs an operation, which
  runs once.
- `==`: derived for a record of decidable data fields (true and false
  cases); refused, with its note, for a record with a proof field, a
  dependent field, parameters, or a field type with no procedure.
- Extraction: records with awkward names (`tag`, `__proto__`, primes,
  `constructor`) added to `awkward_names_never_collide`; differential tests
  through the boundary; `tsc` on the `.d.ts`; an input object with extra,
  inherited, getter-backed and missing properties; a `SortedList` input
  whose list isn't sorted (refused) and is (accepted); a record that's
  well-formed but not exportable.
- Hashes: renaming a field changes the type's hash, for a record and for an
  ordinary data type; making a data type a record changes it too.

**Stage 2** (raw-kernel tests, as in `crates/core/tests/admission.rs`, and
elaborator tests)
- `Proj(D, i, t)` with `t : E`, `E ≠ D`, both with one constructor and
  compatible field counts (the Lean CVE shape [L4]); `i` out of range;
  `Proj` on a `Prop` record; on a recursive single-constructor type; on a
  two-constructor type. All refused with `E-MALFORMED` or a type error.
- Eta mode refused (`E-ETA`) for a recursive record, one in a recursive
  group (`T = Leaf | Node R`, `R = { kid : T, n : Nat }`), a `Prop` record,
  a zero-field record, a two-constructor type.
- The contract (§7.3): `Person` and `Pet` with identical layouts never
  convert, in either direction, through eta; `Box Nat` against `Box Bool`;
  a metavariable of unknown type against a record literal, before and after
  its type is solved; an ill-typed comparison yields no accepted solution.
- `rfl : { p | age = p.age } = p`, `rfl : p = Person.mk p.name p.age`, and
  matching on an unknown record reduces; their analogues for a record
  without eta are refused, and checking them terminates.
- Unfolding (§7.4): on a neutral `b : Box (List Nat)`, a definition
  matching `{ value = Nil }` takes the record match and blocks on the list;
  the same through `Box (Box (Box (List Nat)))`; with `T`/`R` above,
  checking terminates.
- Every existing example still checks, with no snapshot changes beyond
  hashes. `Pair`, `Sig`, `SigMap` are migrated separately, each with the
  full suite.

**Field paths** (later; §6.4): `sum { list = Cons x xs, acc } =
sum { list = xs, acc = acc + x }` accepted; `loop r = loop { r | list =
r.list }` refused.

**Stage 3**
- `{ a : Nat, b : Nat }` and `{ b : Nat, a : Nat }` convert and hash
  equally; `{ a : Nat }` and `{ a : Type }` differ; `type Expr = Lit Nat |
  Add { left : Expr, right : Expr }` is accepted, and `Bad = MkBad { f : Bad
  -> Void }` is refused (`E-POSITIVITY`, through the record).

**Stage 4**
- `greet` on a declared, an anonymous and a wider anonymous record;
  `birthday` preserves other fields (differential, and with a proof per
  concrete type); missing field `E-AUTO-NONE`-style error naming the field;
  `HasField.items SortedList` derived, `CanSetField.items SortedList`
  refused; `map (p => p.name) people` infers.

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

Answered by the review of draft 1.1; see [the review's
answers](#the-reviews-answers). Kept as asked:

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

- **Agda** (checked for draft 2): the manual [A1], fetched on 16 October
  2026, confirms that inductive records, recursive ones included, have eta
  by default, with an `UnguardedEtaRecord` warning.
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
