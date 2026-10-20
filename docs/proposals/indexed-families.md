# Proposal: indexed data types (inductive families)

**Status:** draft 1, 20 October 2026. Waiting for review (design-review gate). Nothing is
built. Ticket SW-178. Matt decided D133 and D135 (20 October): indexed data types go into
the kernel before `Vec` (docs/proposals/vec.md, parked). The open questions are D136 to
D153 in [§12](#12-decisions-wanted).

This note can be read without knowing type theory. [§1](#1-words) explains the words it
uses. Claims about Stitchwort were checked against the source on `main` at `9ccb120`.
Labels, as in the other notes:

- **[checked: S]**: read in source S (listed in [Sources](#sources)), or in the Stitchwort
  source at the `file:line` given;
- **[run]**: a Stitchwort program run with the release CLI on 20 October 2026;
- **[inferred]**: my reasoning from checked facts, not stated in a source;
- **[unverified]**: believed, but not confirmed.

## Contents

0. [Summary](#0-summary)
1. [Words](#1-words)
2. [Stitchwort today](#2-stitchwort-today)
3. [What we want to write](#3-what-we-want-to-write)
4. [How other systems do it](#4-how-other-systems-do-it)
5. [Three ways to build it](#5-three-ways-to-build-it)
6. [The kernel rules](#6-the-kernel-rules)
7. [The surface language](#7-the-surface-language)
8. [Examples](#8-examples)
9. [Soundness tests](#9-soundness-tests)
10. [Build plan](#10-build-plan)
11. [What else changes](#11-what-else-changes)
12. [Decisions wanted](#12-decisions-wanted)
13. [Sources](#sources)

## 0. Summary

- **Recommendation: native indices in the kernel, matched by case trees with a small,
  fixed unifier** (option A in §5). This is Agda's design, which Stitchwort's kernel
  already resembles: it checks case trees directly (not eliminators), refines the whole
  context by substitution in each branch, and decides termination by size change on those
  case trees. Lean's and Rocq's kernels use eliminators instead; Stitchwort's doesn't
  have them.
- **What the kernel learns.** A data type gets an *index telescope* after its parameters
  (`Vec (a: Type): Nat -> Type`). Each constructor states its result type
  (`VCons …: Vec a (Succ n)`). In a `case`, each branch first unifies the scrutinee's
  indices with the constructor's, using four textbook rules: two different constructors
  are never equal (the branch is impossible); equal constructors have equal fields; a
  variable equal to a term is replaced by it; an equation that already holds is dropped.
  Anything else is refused. An impossible branch has no body.
- **Axiom K is accepted.** Dropping an equation that already holds is Streicher's axiom
  K. Lean has it, and so does Agda by default; Stitchwort's adopted proof-irrelevance
  design (D1′) already implies it. Univalence, the reason to avoid K, isn't planned
  (§6.5).
- **The known traps are avoided.** No injectivity of type formers (Agda's 2010
  inconsistency). No recursion through solved indices (Agda issue #6654). The
  universe check still applies to every constructor field (§6.6, §6.7).
- **Kept as today, on purpose:** `Prop` elimination stays at "at most one constructor and
  every field a proof". DESIGN.md §6's extra index clause waits (D140). Indices are data
  and are kept at run time; erasing them is a later optimisation (D141). The built-in `=`
  and `J` stay.
- **Surface:** indices go after the colon of the header. Each constructor states its
  result type. An index variable a constructor uses is bound as an implicit field.
  Matching needs no new syntax: impossible arms are left out (or written `()`), and an
  arm that can never match is a warning. Write `Succ n`, not `n + 1`, in an index:
  `+` counts down its *first* argument, so `n + 1` doesn't compute when `n` is unknown
  **[run]** (D145).
- **Cost:** about 1,000 to 1,300 lines in `crates/core` with its tests, 200 in
  `crates/syntax`, 1,000 to 1,400 in `crates/elab`, and 100 in `crates/js`, in five stages
  (§10). `Vec`'s representation (D126) is decided after this lands (SW-179).

## 1. Words

- **Data type with parameters.** `type List (a: Type)`. The parameter `a` is the same in
  the type and in every constructor: a `Cons` of a `List Nat` holds a `List Nat`.
- **Index.** An argument of a type that *can differ* between constructors, and inside a
  constructor's fields. In `Vec a n`, `a` is a parameter and `n` (the length) is an
  index: `VNil` has length 0, and `VCons x xs` has length one more than `xs`.
- **Inductive family.** A data type with indices. The textbook name; "indexed data type"
  means the same.
- **Unification.** Solving equations between terms, to find what the variables must be.
  Matching `v: Vec a (Succ k)` against `VNil` asks `Succ k = 0`, which has no solution, so
  that case can't happen.
- **Absurd (impossible) case.** A constructor that can't fit the scrutinee's indices.
- **Case tree.** The kernel's form of pattern matching: nested `case`s on variables
  (docs/core.md, "Case trees").
- **Eliminator (recursor).** A single built-in function per data type that does one-step
  pattern matching and recursion together. Lean and Rocq kernels use these.
- **Motive.** The result type of an eliminator, as a function of what is matched (and of
  the indices).
- **J.** The eliminator for equality: transport a value along `a = b`. Stitchwort has it
  built in.
- **Axiom K.** "Every proof of `a = a` is `rfl`" (as an eliminator). **UIP** (uniqueness of
  identity proofs) is the same idea stated as "any two proofs of `a = b` are equal".
- **Fording.** Turning an index into a parameter plus an equation field:
  `VNil (e: n = 0)` instead of `VNil: Vec a 0`. Named after Henry Ford's "any colour, so
  long as it's black" (Conor McBride's term **[unverified]**).
- **Forced field.** A constructor field that the result type's indices determine, like
  `n` in `VCons [n] …: Vec a (Succ n)`.
- **Large index.** An index whose type is bigger than the data type's universe, like
  `Type` in `Ty: Type -> Type`.

## 2. Stitchwort today

- **Data types have parameters, no indices.** docs/core.md:21 **[checked]**. `Data(D, params)`
  holds a type applied to all its parameters; `Ctor(D, c, fields)` gets its parameters from
  the expected type (docs/core.md:32-33). The surface rejects `type Vec (a: Type): Nat ->
  Type = …` (docs/proposals/vec.md §1).
- **Equality is built in.** `Eq(A, a, b)`, `Refl`, and `J(P, d, p)`, which computes on
  `rfl` only (docs/core.md "Equality"). It's in `Prop`, and it may eliminate into data.
- **No K yet, but planned implicitly.** The kernel "has `J`, but no axiom K and no
  definitional proof irrelevance" (docs/proposals/compact-text.md:171). Matt adopted D1′ of
  docs/proposals/proof-irrelevance.md (19 October, SW-93, on hold); that note says D1′ "is
  enough to *derive* propositional proof irrelevance and a computing K" and that "UIP
  itself is no cost here" **[checked: proof-irrelevance.md:1-40, 297-307]**.
- **Case trees refine the whole context.** In a branch, the matched variable *is* the
  constructor value, substituted into the goal and into every variable's type and value,
  *including variables bound before it* (docs/core.md:109; `check_case` and `substitute`,
  `crates/core/src/check.rs:571-710, 795-812`) **[checked]**. This is the machinery the
  unifier's "solution" step needs.
- **Absurd patterns.** A case with no branches is accepted only for a type with no
  constructors (docs/core.md:110).
- **`Prop` elimination.** At most one constructor, every field a proof, alone in its
  group (`crates/core/src/check.rs:616-660`) **[checked]**. docs/core.md:108 already
  notes that the index clause of DESIGN.md §6 "doesn't arise yet".
- **Positivity.** A type may appear in its fields only as itself applied to exactly its
  own parameters, or as the result of a function type (docs/core.md:99).
- **Termination.** Size change over case trees. "An argument's relation comes only from the
  terms, never from types", and `J` counts as unknown: "transport never yields a part"
  (`crates/core/src/termination.rs:19-35`) **[checked]**. A field of a matched
  constructor is smaller than the match, whatever its type.
- **Erasure when running.** A `case` on an erased proof "takes the first branch with
  placeholder fields" (`crates/core/src/erase.rs:15`), safe because of the `Prop`
  elimination rule.
- **Numbers.** `Nat` is native. `k + x` for a literal `k` is kept as `Succ` applied `k`
  times. `+` counts down its first argument (DESIGN.md §6). So `1 + n` is `Succ n`, but
  `n + 1` is stuck: `theorem t2 (n: Nat): n + 1 = Succ n := rfl` fails with `E-REFL`, and
  `1 + n = Succ n` and `Succ n + m = Succ (n + m)` pass **[run]**.
- **The elaborator's pattern compiler** (`compile` in `crates/elab/src/lib.rs:1954-2140`)
  is untyped: it splits on the first constructor column and reports `E-NONEXHAUSTIVE`
  when a constructor has no rows. The kernel re-checks the resulting tree
  (`check_tree`, `crates/elab/src/lib.rs:2649`). `match` is compiled into the case tree or
  lifted into a generated definition, generalising its scrutinees
  (`crates/elab/src/matching.rs`).
- **Constructor fields** are explicit binders only (`CtorDecl { name, fields: Vec<Binder> }`,
  `crates/syntax/src/ast.rs:615`), and constructors have no written result type.

## 3. What we want to write

```
type Vec (a: Type): Nat -> Type =
  | VNil: Vec a 0
  | VCons (x: a) (xs: Vec a n): Vec a (Succ n)

def head: Vec a (Succ n) -> a
  | VCons x _ => x                       -- no VNil arm: it can't happen

def append: Vec a n -> Vec a m -> Vec a (n + m)
  | VNil, ys       => ys
  | VCons x xs, ys => VCons x (append xs ys)
```

plus `Fin n` (numbers below `n`), and propositions defined by rules, like `Le m n` and
`Even n`. §8 has the full examples.

## 4. How other systems do it

| System | Kernel | How a match on a family is checked | K | `Prop` large elimination |
|---|---|---|---|---|
| **Lean 4** | Eliminators (`rec`, `casesOn`) whose motive takes the indices | The elaborator generalises the indices, then unifies the equations with `noConfusion` (constructors differ, or are injective) and `Eq` casts **[unverified: from Lean's `cases` tactic]** | Yes: "K-like reduction" in the kernel | At most one constructor; each constructor argument's type is "either a `Prop`, a parameter, or an index" **[checked: L1]** |
| **Agda** | Case trees, checked with unification | Unification in the checker: solution, injectivity, conflict, cycle, deletion **[checked: A1, A3]** | Yes by default; `--without-K` forbids deletion **[checked: A1]** | Separate `Prop` sort, opt-in |
| **Rocq** | `match … as … in … return` | The `in` clause names the indices, which "have to be variables" **[checked: R1]**; the user (or the Equations plugin) does the rest | Not built in, consistent | Only "singleton" (one constructor, all arguments in `Prop`) or empty **[checked: R1]** |
| **Idris 2** | Case trees | Unification in the elaborator | Yes **[unverified]** | Not applicable: no `Prop`; quantities instead |

**Lean.** The kernel eliminator for `Vec` takes a motive over the length and the vector,
so the kernel never unifies. The cost moves to the elaborator, which produces `Eq` casts.
These casts compute even on open proofs thanks to "K-like reduction": for a
subsingleton like `Eq`, the kernel replaces a variable proof by `rfl` when the indices
agree (ammkrn's "Type checking in Lean 4": "if the major premise is a free variable of
type `Eq Char 'a'`, the kernel can substitute `Eq.refl Char 'a'`") **[checked: L2]**.
Without that rule, Lean's encoding of matches would get stuck on casts.

**Agda.** Pattern matching is checked as case trees, with unification inside the checker.
Cockx and Abel's "Elaborating dependent (co)pattern matching" (ICFP 2018, JFP 2020)
describes the elaboration from clauses to well-typed case trees, now Agda's
implementation **[checked: C3]**. Under `--without-K`, the unifier "cannot make use of
the deletion rule to solve equations of the form `x = x`" **[checked: A1]**. When an
index is a function application, Agda says "I'm not sure if there should be a case for
the constructor …, because I get stuck when trying to solve the following unification
problems"; Cockx advises using "only variables and constructors in the indices"
**[checked: A3]**.

**Rocq.** `match v in Vec _ n return P n v with …` writes the motive by hand. Indices in
the `in` clause must be variables **[checked: R1]**. Dependent pattern matching with
unification lives in the Equations plugin (Sozeau), outside the kernel **[unverified]**.

**Idris 2.** Indexed families are the normal way to write `Vect`. Erasure is by
*quantity*: an implicitly bound name is erased ("If … a name is implicitly bound … the
argument is erased"), and a function that needs the length at run time must say so,
`vlen: {n: Nat} -> Vect n a -> Nat` **[checked: I1]**. Brady, McBride and McKinna's
"Inductive families need not store their indices" (TYPES 2003) shows how forced
constructor fields can be dropped at run time **[checked: abstract only, B1]**.

**The theory.** Coquand (1992) introduced dependent pattern matching with unification.
It proves K, which Hofmann and Streicher showed doesn't follow from `J` alone
**[checked: abstracts, C1]**. Goguen, McBride and McKinna ("Eliminating dependent pattern
matching", 2006) translate such matching into eliminators plus K, which is the standard
argument that it is sound **[checked: abstract, G1]**. Cockx, Devriese and Piessens
("Eliminating dependent pattern matching without K", JFP 2016) give the restricted rules
for systems without K **[checked: title and venue, C2]**.

**Two Agda bugs worth learning from.**

1. *Injective type formers* (2010). Agda treated `F a = F b → a = b` for type formers as a
   unification rule. With excluded middle that was inconsistent, and Altenkirch said
   only "intensionally injective" constructors such as `List`'s should be injective
   **[checked: A4]**. Stitchwort's rule: injectivity only for *constructors of data
   types*, never for `Data`, `Pi` or `Sort` (§6.3).
2. *Large indices and forcing* (issue #6654, 2023). `data Bad: ((P: Set) → P → P) → Set`
   with constructor `b: (f: …) → Bad f` let `no-bad (b x) = no-bad (x _ bad)` pass the
   termination checker, because `f` was a forced field and not counted. That proves `⊥`.
   Agda 2.6.4 made constructors check the universe of every field "even when these values
   are forced by the indices", added `--large-indices` (off by default), and notes that
   with it on, "forced constructor arguments should not be used for termination checking"
   **[checked: A2, A5]**. Stitchwort already checks every field's universe and has no
   forcing; this note keeps it so and adds no descent through solved indices (§6.7, D143).

## 5. Three ways to build it

### A. Native indices; case trees unify (recommended)

The kernel stores the index telescope and each constructor's result indices. `case`
unifies, with a fixed set of rules, and marks impossible branches. The elaborator
unifies too, to find impossible arms and give good errors, but the kernel re-checks
everything.

### B. Native indices; the kernel case needs variable indices (Lean/Rocq style)

The kernel `case` only accepts a scrutinee whose indices are distinct variables (Rocq's
`in` clause, Lean's `casesOn` motive). Everything else the elaborator does with equations,
`noConfusion` lemmas and `J` casts.

### C. Fording: no indices in the kernel

`Vec a n` becomes a parameterised type with equation fields:

```
type Vec (a: Type) (n: Nat) =
  | VNil (e: n = 0)
  | VCons [m: Nat] (x: a) (xs: Vec a m) (e: n = Succ m)
```

### Comparison

| | A: unify in case trees | B: variable indices only | C: Fording |
|---|---|---|---|
| Kernel change | Indices + unifier (~350 lines, trusted) | Indices + "distinct variables" check (~150 lines) | **Still needs one**: `Vec a m` in a field breaks today's positivity rule (exactly the own parameters), so `n` must become a *non-uniform parameter*, which is an index in all but name |
| Common case (`append` on `Vec a n`) | Plain substitution, no casts | Plain substitution, no casts | A cast (`J` on `e`) in every branch |
| `zipWith` (second vector's length is `Succ m`, not a variable) | Unifier solves `Succ m = Succ m'` | Elaborator must generalise and cast; `xs'` arrives through `J` | Casts |
| Structural recursion | Fields are fields: descent as today | Recursive calls on cast values are "unknown" (`J`, termination.rs:33): **refused** unless the termination checker learns to see through casts | Same problem as B |
| Computation in types | Values hold no proofs | Casts compute only on `rfl` (no K-like reduction): proofs about open vectors get stuck | Casts in every value; stuck on open proofs |
| Errors | Unifier knows the equations, so messages can name them | Errors come from generated casts | Users see `e` fields |
| Erasure/JS | Same as other data | Same | Equation fields erased; same values as A |
| Fits today's kernel | Yes: `substitute` and context refinement already do the work | Partly | No (needs non-uniform parameters anyway) |

**Why A.** The deciding facts are Stitchwort-specific. Its kernel checks case trees, not
eliminators, and its termination checker reads descent only from case-tree terms, never
through `J`. B and C both put `J` between a recursive call and the field it recurses on,
which today's termination checker refuses (termination.rs:33) **[checked]**. Fixing that
would mean teaching the trusted termination checker about casts, which is harder to get
right than four unification rules. B and C also leave casts that get stuck in proofs
about open vectors, which Lean avoids with K-like reduction, itself a kernel rule. A's
trusted addition is small, well studied (Coquand 1992; Goguen–McBride–McKinna 2006;
Cockx), and justified by translation to eliminators plus K. It also reuses the existing
refinement machinery almost unchanged.

**What A costs in trust.** The unifier is new trusted code. It's kept small: four rules,
no postponement, no higher-order cases, and "stuck" always means "refuse" (§6.3). The
elaborator calls the same function, so there's one implementation to test (D149).

## 6. The kernel rules

### 6.1 Declarations

`declare_data_group(params, indices, sort, names)`: the parameter telescope as today, then
an *index telescope* per member, checked in the context of the parameters. `D`'s type is
`(params) -> (indices) -> sort`.

`define_data_group`: each constructor has its fields, as today, and its **result
indices**: terms in the context of the parameters and the fields, checked against the
index telescope. The result's parameters aren't written: they are always exactly the
type's own parameters (as in Lean, Agda and Rocq). A type with no indices has no result
indices, which is today's case unchanged.

A record (`declare_data_group_as`) can't have indices (`E-MALFORMED`); the elaborator
never asks for one (D148).

### 6.2 Typing

- `Data(D, args)`: `args` is the parameters then the indices, each checked against its
  telescope. Its type is `D`'s universe.
- `Ctor(D, c, fields) ⇐ D ps is`: the fields are checked as today, with `ps` substituted;
  then the constructor's result indices, with `ps` and the fields substituted, must be
  convertible with `is` (`E-TYPE-MISMATCH` otherwise).
- `Ctor` of a type *without parameters* still infers: its type is `D` applied to its
  result indices (so `FZero` infers `Fin (Succ n)` once `n` is given).
- **Universes.** Every *field* is checked against `D`'s universe as today (docs/core.md:98),
  including fields that the indices determine. Index *types* aren't constrained: an index
  isn't stored in the value, so `Ty: Type -> Type` is allowed (Lean allows this) (D142).
  This is the line Agda 2.6.4 drew after issue #6654 **[checked: A2]**.
- **Positivity.** In a field's type, a member of the group may appear only as `D ps js`,
  with `ps` exactly its own parameters (as now) and **no member of the group anywhere in
  `js`**, or as the result of a function type whose inputs don't mention the group. A
  constructor's result indices must not mention the group either.

### 6.3 `case` with unification

`Case(x, D, branches) ⇐ G`, where `x: D ps is`. For constructor `c` with fields `f₁ … fₖ`
and result indices `js`, the branch is checked like this:

1. Bind the fields, as today. Make the equations `is₁ = js₁, …, isₘ = jsₘ` (left to right,
   with `js` evaluated with `ps` and the fields).
2. **Unify**, taking the first equation each time, with both sides evaluated:
   - **Deletion.** The sides are convertible: drop it.
   - **Solution.** One side is a variable `y` of the context (a plain variable, not one with
     a value), and the other side `t` doesn't mention `y`, and neither do the types of the
     variables in `t`, transitively (occurs check). The two sides' types must be
     convertible (checked; true when the earlier equations are solved). Substitute `t`
     for `y` everywhere: in the context, in the remaining equations and in the goal, exactly
     as `substitute` does for `x` today. When both sides are variables, it doesn't matter
     which is replaced: both stay in scope, one standing for the other.
   - **Injectivity.** Both sides are the same constructor of a data type: replace the
     equation with equations between their fields (their parameters are equal by typing).
   - **Conflict.** Different constructors of the same data type: the branch is
     **impossible**.
   - **Numbers.** A number is `Succ` of its predecessor, and `k + x` is `Succ` applied `k`
     times, for injectivity and conflict (`3 = Succ m` gives `2 = m`; `0 = Succ m`
     conflicts; `5 = 7` conflicts). A compact text range expands one cell, as conversion
     does.
   - **Anything else is stuck: the kernel refuses the case** (`E-INDEX-STUCK`; the
     elaborator reports it first). In particular there is no injectivity for type formers
     (`Data`, `Pi`, `Sort`): `List a = List Nat` at type `Type` is stuck, not `a = Nat`.
     Stuck includes a function application that doesn't compute (`n + m` with `n`
     unknown), and an occurs-check failure (`n = Succ n`; Agda's "cycle" rule would make
     it impossible, D143).
3. **Possible branch:** check its body with `x` replaced by `c f₁ … fₖ` (as today) and the
   solutions applied.
4. **Impossible branch:** it has no body (`Branch.body` becomes optional). A body on an
   impossible branch, or no body on a possible one, is `E-MALFORMED`: the elaborator decides
   which, and the kernel checks it.
5. **The `Prop` rule** (§6.4) is checked as today, with one change: a case where every
   branch is impossible may produce anything.

The kernel records nothing new in the term apart from which branches are impossible.
Hashing covers that (§6.9).

**Why it's sound** **[inferred, from G1 and C3]**. The rules use only facts true of
values of data types: different constructors are never equal, equal constructor values
have equal fields, a variable equal to a term can be replaced by it, and an equation that
already holds can be dropped (K). Goguen, McBride and McKinna's translation turns exactly
these steps into eliminators plus K, so a case tree using them proves nothing that
eliminators plus K couldn't. Operationally: a case only reduces when `x` is a constructor
value `c us`. Its type `D ps is` then makes `is ≡ js[us]`, so the substitutions the branch
was checked under hold for the actual values, and an impossible branch is never reached.
The existing refinement already substitutes into variables bound before `x`, and the
solution step does the same for `y`.

**Dependent indices.** A family like `Sub: (n: Nat) -> Fin n -> Type` has an index whose
type mentions an earlier index. Equations are taken in order, and each must have
convertible sides' types when it's taken (that's the homogeneity check in "Solution"). If
an earlier one is stuck, the case is refused. This is stricter than Agda's postponement,
and simpler (D137).

### 6.4 `Prop` elimination

Unchanged in stage 1: a proposition matched to produce data must be alone in its group,
have at most one constructor, and have only proof fields. One addition: **a case whose
branches are all impossible may produce anything**, at any universe, because it is never
reached. This makes `notEvenOne` (§8.4) and "`Le (Succ n) 0` is impossible" usable in
programs. The same holds today for a type with no constructors.

DESIGN.md §6 allows one more case: a data field that "appears among the indices of the
constructor's result type". Lean's rule is the same in substance ("either a `Prop`, a
parameter, or an index") **[checked: L1]**. It's sound, but running it needs care. With
erasure, a `case` on an erased proof binds placeholder fields (erase.rs:15), so a data
field read from the proof would have to be computed from the scrutinee's index instead,
and the term doesn't carry the scrutinee's type. **Recommendation: leave it out for now**
and say so in DESIGN.md §6. Nothing planned needs it, since `=` is built in (D140).

### 6.5 Axiom K

The deletion rule is K. With it, a user can prove K for their own equality family:

```
type Same (x: a): a -> Prop =
  | Refl: Same x x

theorem sameK (p: Same x x): p = Refl
  | Refl => rfl            -- equations: x = x (deleted)
```

and through `J`, K for the built-in `=` too **[inferred]**. That's consistent. It
holds in the model where every proposition has at most one proof, which is the model the
adopted proof-irrelevance design relies on (proof-irrelevance.md:297-307). Lean has K
(K-like reduction), and Agda has it by default. K only conflicts with univalence (homotopy
type theory), which Stitchwort doesn't plan. Without deletion, `Le n n` couldn't be
matched against `LeRefl` (both equations solve to `n = n`) without extra steps, and K
would arrive anyway with D1′. **Recommendation: accept K (D138).**

### 6.6 Universes and large indices

Allowed: `type Ty: Type -> Type = | TNat: Ty Nat | TList (t: Ty b): Ty (List b)`, whose index
is a type. What makes it safe is unchanged rules: every field is checked against the
universe, and nothing is "forced". Unification at type `Type` only ever deletes (§6.3),
because type formers aren't injective. So matching `t: Ty (List Nat)` against `TList`
is stuck (`List Nat = List b`), and is refused. Matching `t: Ty c` (a variable) works:
`c := List b`.

### 6.7 Termination

Unchanged. A field of a matched constructor is smaller than the match, whatever its type
(docs/core.md:153), so `xs` and the implicit `n` in `VCons [n] x xs` are smaller than
the vector. A recursive function field is one whose type is a function returning a group
member at *any* indices.

**Not added: descent through solved indices.** In the branch where `n` (a parameter)
was solved as `Succ m`, `m` is *not* counted as smaller than `n`. That is Agda's
"forced-argument recursion", which caused issue #6654 when combined with large indices
and impredicativity. Stitchwort has impredicative `Prop`. Recursion on the vector already
gives the same evidence (D143).

### 6.8 Evaluation, conversion, erasure, JavaScript

- **Values.** `Value::Data(D, args)` carries parameters and indices; a constructor value
  carries its fields, forced ones included. Conversion is unchanged: indices are just more
  arguments. Nothing is added to conversion, so it's no slower. Fording would add a proof
  to every value and a `J` to every match.
- **Unfolding.** A case reduces when its scrutinee is a constructor; it can never be one
  of the impossible ones (by typing).
- **Running with erasure.** Constructor fields of a data family are data, so they're
  computed and stored (D141). A `case` on an erased proof takes its only *possible* branch;
  if every branch is impossible, the program is wrong and the run fails loudly
  (`unreachable`). The erasure argument in erase.rs still holds, because the `Prop` rule
  is unchanged.
- **JavaScript.** A family's values are `{ tag, …fields }`, as for any data type, with forced
  fields like `n` stored. An impossible branch compiles to nothing; a case with no possible
  branch throws. Exporting a function whose inputs or result mention an indexed family is
  `E-EXPORT` for now: decoding would have to check the indices (D147).

### 6.9 Hashing

A data type's hash covers its index telescope and each constructor's result indices; a
case covers which branches are impossible. Hashes change for every data type, since the
layout changes. That's fine: hash stability isn't a goal, and the hash snapshot is
regenerated.

### 6.10 Data groups

Members of a group share parameters and universe (as now), but each has its own index
telescope, so `Even` and `Odd` (§8.4) can be defined together. Lean allows different indices
in a mutual block **[unverified]**. The elaborator's `E-MUTUAL-PARAMETERS` still compares
parameters only.

## 7. The surface language

### 7.1 Declarations

```
type Vec (a: Type): Nat -> Type =
  | VNil: Vec a 0
  | VCons (x: a) (xs: Vec a n): Vec a (Succ n)
```

- **Parameters before the colon, indices after.** This is Lean's and Agda's convention,
  and it extends today's `type D (params): sort`. The indices can be named for messages:
  `type Vec (a: Type): (len: Nat) -> Type`.
- **Each constructor states its result type** after `:`, which must be the type applied to
  its parameters exactly as declared (`Vec a`, not `Vec Nat`) and then indices. For a type
  without indices it's optional, and today's form keeps working.
- **Implicit fields.** `[n: Nat]` may be written in a constructor's fields. An unknown
  lowercase name in a constructor (here `n`) is bound as an implicit field at the front,
  like the automatic implicits in signatures. One change to that rule for constructors:
  uses in the result type's indices don't count against it (`Succ n` is fine), as long as
  some use fixes its type (`xs: Vec a n`) (D144). A name used only in the result
  (`FZero: Fin (Succ n)`) gets its type from the index's type, `Nat`.
- **Write `Succ n` (or `1 + n`), not `n + 1`.** `+` counts down its first argument, so
  `n + 1` doesn't compute when `n` is unknown **[run]**, and a constructor declared with
  it could never be matched on a `Vec a (Succ k)`. The declaration is still allowed:
  `type Plus: Nat -> Nat -> Nat -> Prop = | MkPlus: Plus m n (m + n)` is useful, because
  a scrutinee's index variable can be solved as `m + n`. But matching that gets stuck on it
  says why (§7.4) (D145).

### 7.2 Building values

`VCons x xs` fills `n` by unification, as any implicit argument. `VCons [n := k] x xs`
names it. `VCons` alone is a function, as constructors are today.

### 7.3 Matching

No new syntax. In `def head: Vec a (Succ n) -> a`, `n` is an implicit parameter, in scope
by name in every arm. Matching `VCons x _` solves the constructor's own `n` as the
signature's `n`.

- **Implicit fields in patterns** are skipped by default. To name one, write it as in a
  call: `VCons [n := k] x xs` binds `k`. Positional `[k]` isn't allowed, so adding an
  implicit field never shifts a pattern (D146).
- **Impossible arms are left out.** When a constructor has no arm, the compiler unifies; if
  it's impossible, the branch is marked impossible and nothing is reported. If the
  missing arm is possible, it's `E-NONEXHAUSTIVE` as today, naming the constructor and
  the indices it would have.
- **A missing arm can be impossible because of another argument.** In `get: Vec a n ->
  Fin n -> a`, the `VNil` case has no arm. In that branch `n` is 0, so every `Fin 0`
  constructor is impossible. The compiler tries splitting the other columns whose types
  are families, one level deep, and accepts if one of them has no possible constructor
  (Lean and Agda accept this `get` **[unverified for Lean]**) (D146).
- **`()`** says "this argument's type has no possible constructor". Today it needs a type
  with no constructors; now it also accepts `Even 1` (§8.4). Otherwise `E-NOT-EMPTY`.
- **An arm that can never match** (`| VNil => …` for a `Vec a (Succ n)`) is the warning
  `W-UNREACHABLE` and is dropped. Agda reports these too **[unverified]**.
- **`match`** works as now. A lifted `match` takes the index variables its scrutinees'
  types mention, as it already takes the variables types depend on. A scrutinee whose
  type has an index that is neither a variable nor a constructor form can get stuck:
  the message says to match on the index first, or to use a helper with a signature.

### 7.4 Error messages

```
[E-INDEX-STUCK] can't tell whether `VNil` can be here
  `v` has type `Vec a (n + m)`, and `VNil` has length `0`.
  Matching needs `n + m = 0`, but `n + m` doesn't compute while `n` is unknown.
  Note: match on `n` first, so the length computes.

[E-INDEX-STUCK] can't tell whether `VCons` can be here
  `v` has type `Vec a (Succ k)`, and `VCons` was declared with length `n + 1`.
  Note: `+` counts down its first argument, so `n + 1` doesn't compute while `n` is
  unknown. Declare the constructor with `Succ n` (or `1 + n`).

[W-UNREACHABLE] this arm can never match
  `VNil` has length `0`, but this vector has length `Succ n`.

[E-NONEXHAUSTIVE] missing case: no arm matches `VCons x xs`
  here the vector has type `Vec a (Succ k)`.

[E-INDEX-STUCK] can't tell whether `TList` can be here
  Matching needs `List b = List Nat`, and types aren't taken apart by matching.
  Note: matching works when the index is a variable, as in `Ty c`.
```

## 8. Examples

### 8.1 `Vec`

```
type Vec (a: Type): Nat -> Type =
  | VNil: Vec a 0
  | VCons (x: a) (xs: Vec a n): Vec a (Succ n)

def head: Vec a (Succ n) -> a
  | VCons x _ => x

def tail: Vec a (Succ n) -> Vec a n
  | VCons _ xs => xs

def map (f: a -> b): Vec a n -> Vec b n
  | VNil       => VNil
  | VCons x xs => VCons (f x) (map f xs)

def zipWith (f: a -> b -> c): Vec a n -> Vec b n -> Vec c n
  | VNil, VNil             => VNil
  | VCons x xs, VCons y ys => VCons (f x y) (zipWith f xs ys)

def append: Vec a n -> Vec a m -> Vec a (n + m)
  | VNil, ys       => ys                         -- goal Vec a (0 + m), which is Vec a m
  | VCons x xs, ys => VCons x (append xs ys)     -- goal Vec a (Succ k + m) = Vec a (Succ (k + m))

def replicate: (n: Nat) -> a -> Vec a n
  | Zero, _   => VNil
  | Succ k, x => VCons x (replicate k x)

def fromList: (xs: List a) -> Vec a (List.length xs)
  | Nil       => VNil
  | Cons x xs => VCons x (fromList xs)

def toList: Vec a n -> List a
  | VNil       => Nil
  | VCons x xs => Cons x (toList xs)

theorem mapAppend (f: a -> b): (xs: Vec a n) -> (ys: Vec a m) ->
    map f (append xs ys) = append (map f xs) (map f ys)
  | VNil, ys       => rfl
  | VCons x xs, ys => Eq.cong (r => VCons (f x) r) (mapAppend f xs ys)
```

What happens in `zipWith`, branch by branch **[inferred]**: splitting the first vector
gives `n := 0` or `n := Succ k`. In the first, the second vector is `Vec b 0`, and
`VCons` would need `0 = Succ m'`: a conflict, so that branch is impossible and needs no
arm. In the second, `VNil` would need `Succ k = 0` (impossible), and `VCons` needs `Succ k =
Succ m'`, so `m' := k`. The recursive call gets `xs` and `ys`, both fields, so termination
is as for lists. In `head`, `VNil` is impossible (`Succ n = 0`). `append` needs no
unification beyond `n := 0` or `n := Succ k`, and its goals compute because `+` counts down
its first argument. `mapAppend` follows the same shape (it's `List.mapAppend`'s proof).

### 8.2 `Fin` and `get`

```
type Fin: Nat -> Type =
  | FZero: Fin (Succ n)
  | FSucc (i: Fin n): Fin (Succ n)

def get: Vec a n -> Fin n -> a
  | VCons x _, FZero    => x
  | VCons _ xs, FSucc i => get xs i
```

There's no `VNil` arm: there, `n` is 0, and both `Fin 0` constructors conflict. No
`auto` proof of `i < n` is needed; the type of `i` is the proof. `Fin.toNat`, and
`Fin.ofNat (i: Nat) [auto ok: i < n]: Fin n`, connect it to the `Nat` and `auto` style
of vec.md §5.

### 8.3 `Le` as an inductive predicate

```
type Le: Nat -> Nat -> Prop =
  | LeZero: Le 0 n
  | LeSucc (h: Le m n): Le (Succ m) (Succ n)

theorem leTrans: Le a b -> Le b c -> Le a c
  | LeZero, _            => LeZero
  | LeSucc h1, LeSucc h2 => LeSucc (leTrans h1 h2)

theorem leToLeq: Le m n -> m <= n
  | LeZero    => Nat.zeroLe n
  | LeSucc h  => leToLeq h          -- Succ m <= Succ n computes to m <= n
```

In `leTrans`'s second arm, the second proof has type `Le (Succ n) c`. `LeZero` conflicts
(`Succ n = 0`), and `LeSucc` solves its `m` as `n` and `c := Succ n'`. The prelude's `<=`
stays the `Bool` form (docs/core.md "Numbers"); `Le` is the proof-by-rules form, useful
when a proof goes by induction on the derivation.

### 8.4 `Even`, an absurd case, and `auto`

```
type Even: Nat -> Prop =
  | EvenZero: Even 0
  | EvenTwo (h: Even n): Even (Succ (Succ n))

theorem notEvenOne: Not (Even 1)
  | ()                                   -- 0 = 1 and Succ (Succ n) = 1 both conflict

theorem evenInv: Even (Succ (Succ n)) -> Even n
  | EvenTwo h => h

def decEven: (n: Nat) -> Decidable (Even n)
  | 0             => Yes EvenZero
  | 1             => No notEvenOne
  | Succ (Succ k) => match decEven k with
      | Yes h => Yes (EvenTwo h)
      | No r  => No (h => r (evenInv h))

def half (n: Nat) [auto ok: Even n]: Nat := …    -- body omitted; `auto` uses decEven
```

`decEven` returns `Decidable`, so `auto` uses it (docs/core.md "Auto arguments").

### 8.5 AoC flavour: grids that are rectangular by their type

Days 4 and 6 carry "rectangular" as a precondition on `List (List …)` today (vec.md §1;
day 6's `paddedGridRectangular`). With families the shape is in the type:

```
type Grid = { height: Nat, width: Nat, rows: Vec (Vec Bool width) height }

def ofList: (n: Nat) -> List a -> Maybe (Vec a n)     -- Nothing if the length differs
  | 0, Nil              => Just VNil
  | Succ k, Cons x xs   => Maybe.map (rest => VCons x rest) (ofList k xs)
  | _, _                => Nothing

def transpose [w: Nat]: Vec (Vec a w) h -> Vec (Vec a h) w
  | VNil          => replicate w VNil
  | VCons row rows => zipWith (x xs => VCons x xs) row (transpose rows)

def cell (g: Grid) (r: Fin g.height) (c: Fin g.width): Bool := get (get g.rows r) c
```

`transpose` uses `w` at run time: an implicit parameter isn't erased (DESIGN.md §6, "Four
separate questions"). Day 6's columns become `transpose rows`, with no padding lemma.
Whether day 4 uses this or the list-and-length record is D126 (vec.md), decided in SW-179.

## 9. Soundness tests

Each must-reject example comes with an accepted one nearby (DESIGN.md §13), and declares
its error code. Kernel-level tests are built through the Rust API as the other kernel tests
are; the surface ones go in `examples/reject` and `examples/accept`.

| # | Must be rejected | Code | Paired accepted example |
|---|---|---|---|
| 1 | A `case` marking a possible branch impossible (`VCons` for a `Vec a n`), built directly | `E-MALFORMED` (kernel) | The same case with a body |
| 2 | A body on an impossible branch, built directly | `E-MALFORMED` (kernel) | The branch marked impossible |
| 3 | `()` on a `Vec a n` | `E-NOT-EMPTY` | `()` on `Even 1` |
| 4 | Matching `v: Vec a (n + m)` with `n` unknown | `E-INDEX-STUCK` | The same after matching `n`; `append` |
| 5 | A constructor declared `Vec a (n + 1)`, matched on `Vec a (Succ k)` | `E-INDEX-STUCK` | Declared `Vec a (Succ n)` |
| 6 | Type former injectivity: matching `t: Ty (List Nat)` against `TList` | `E-INDEX-STUCK` | Matching `t: Ty c` |
| 7 | Occurs check: `type Loop: Nat -> Nat -> Type = \| MkLoop: Loop m (Succ m)`, matching `l: Loop n n` | `E-INDEX-STUCK` | Matching `l: Loop n k` |
| 8 | Negative occurrence through an index-varying field: `\| MkBad (f: Bad 0 -> Void): Bad 1` | `E-POSITIVITY` | `Vec` |
| 9 | The family in an index: `type Bad: Type -> Type = \| MkBad: Bad (Bad Nat)` | `E-POSITIVITY` | `Ty` |
| 10 | Wrong parameters in a constructor result: `\| Weird: Vec Nat 0` in `Vec (a: Type)` | `E-TYPE-MISMATCH` | `VNil: Vec a 0` |
| 11 | Agda #6654 in `Type`: `type Bad: ((p: Type) -> p -> p) -> Type = \| B (f: (p: Type) -> p -> p): Bad f` | `E-UNIVERSE` (the field is too large) | The same in `Type 1` |
| 12 | Agda #6654 in `Prop`: the same family in `Prop` (allowed, impredicative), and `noBad: Bad x -> Void \| B f => noBad (f _ bad)` | `E-TERMINATION` (`f` returns `p`, not `Bad`) | Structural recursion on a proof of `Le` (`leToLeq`, §8.3) |
| 13 | Descent only through a solved index: `def down [n: Nat]: Vec Bool n -> Nat \| VNil => 0 \| VCons [n := m] _ _ => down [m] (replicate m True)` (`m` is one less than `n`, but that isn't evidence) | `E-TERMINATION` | The same recursing on `xs` |
| 14 | `Prop` elimination through an index field: `type IsSucc: Nat -> Prop = \| MkIsSucc: IsSucc (Succ n)`, `pred: IsSucc k -> Nat` reading `n` | `E-PROP-ELIM` | `IsSucc k -> k != 0` |
| 15 | `Prop` elimination with two constructors: `Le m n -> Bool` by matching | `E-PROP-ELIM` | `Le (Succ n) 0 -> Nat` (every branch impossible) |
| 16 | A missing arm that is possible: `zipWith` without the `VCons, VCons` arm | `E-NONEXHAUSTIVE` | §8.1 `zipWith` |
| 17 | A record with indices, built directly | `E-MALFORMED` (kernel) | A record with parameters |
| 18 | Exporting `head` | `E-EXPORT` | Exporting a `List Nat -> Nat` function that uses `Vec` inside |

Also, not a rejection: `sameK` (§6.5) is **accepted**, documenting the K decision. Driver
tests run each §8 example with and without erasure and compare results, as
`crates/driver/tests` does for natives.

## 10. Build plan

Kernel work is Opus (spec and implementation, or careful review), per the model tiers.
Sizes are rough and include tests.

| Stage | What | Crates | Size |
|---|---|---|---|
| 1 | **Kernel declarations.** Index telescopes in `declare_data_group`; result indices in `define_data_group`; `Data`/`Ctor` typing with indices; positivity and universe rules (§6.2); records refuse indices; hashing; printing. Kernel tests 8-11, 17 | `core` (globals, check, hash, pretty, registry) | 400-500 |
| 2 | **Kernel `case`.** The unifier (new `core/src/unify_index.rs`, public so the elaborator can call it); impossible branches (`Branch.body: Option`); `Prop` rule addition; evaluation, erasure (`unreachable`), termination (impossible branches have nothing). Kernel tests 1, 2, 4-7, 12-15 and `sameK` | `core` | 600-800 |
| 3 | **Syntax and declarations.** `type D (ps): I -> s =`; constructor result types; implicit fields `[n: T]` and automatic ones (D144); building values with implicit fields; `E-INDEX-STUCK` hints | `syntax` (~200), `elab` (~300) | 500 |
| 4 | **Matching.** Typed splitting in `compile`: impossible branches, the one-level search for missing arms (D146), `[n := k]` patterns, `()` for families, `W-UNREACHABLE`, `match` lifting over indices, messages (§7.4). Surface tests 3, 4, 5, 6, 16 | `elab` (`lib.rs`, `matching.rs`, `lift.rs`) | 700-900 |
| 5 | **Running and JS; docs.** Driver tests with and without erasure; JS for impossible branches; `E-EXPORT` for families (test 18); examples `examples/accept/indexed-families.sw`; docs/core.md, docs/syntax.md, DESIGN.md §6 and §13 | `js` (~100), `driver`, docs | 300 |

Stages 1 and 2 can be one lane; 3 and 4 depend on 2. Each stage's tests are the
must-reject rows above for its part. After stage 5, SW-179 decides `Vec`'s representation
(vec.md D126 and the rest) with a real choice between options A and C there.

## 11. What else changes

- **DESIGN.md §6.** "Dependent pattern matching: for the POC, patterns are kept simple"
  becomes a pointer to this note. The `Prop` index clause is marked "not yet" (D140).
  §13's must-reject table gains rows 4, 6, 11, 12 and 13.
- **docs/core.md.** The table row "Parameters but no indices" changes; "Data types" and
  "Case trees" gain §6.2 and §6.3; "Equality" mentions K.
- **docs/proposals/vec.md.** Option C becomes available; its §4 C paragraph and D133 are
  answered.
- **Proof irrelevance (SW-93).** Independent. D1′ masks proof positions in conversion;
  this note adds no proofs to values, so the two don't interact **[inferred]**.

## 12. Decisions wanted

- **D136. Approach.** (A) native indices, with unification in kernel case trees
  (recommended); (B) native indices, kernel cases only on variable indices, and the
  elaborator casts with `J`; (C) Fording, with equation fields and no indices.
- **D137. Unification rules in the kernel.** Exactly deletion, solution (with an occurs
  check that covers types), injectivity and conflict for data constructors and numbers;
  equations taken in order; anything stuck refuses the case (recommended). The
  alternative is to add Agda's postponement and cycle rule now.
- **D138. Axiom K.** Accept it: the deletion rule stays, and K becomes provable
  (recommended, consistent with D1′ and Lean). Or forbid deletion, as Agda's
  `--without-K` does.
- **D139. Type formers are never injective in matching** (recommended; Agda's 2010
  inconsistency). Matching on `Ty (List Nat)` against `TList` is refused.
- **D140. `Prop` elimination.** Keep today's rule, plus "every branch impossible produces
  anything" (recommended). DESIGN.md §6's index clause waits until something needs it.
- **D141. Indices at run time.** Store forced fields (like `n` in `VCons`) and keep
  implicit index parameters at run time, as DESIGN.md §6 says (recommended). Erasing
  forced fields (Brady–McBride–McKinna) or Idris-style quantities come later.
- **D142. Large indices.** Allow index types of any size (`Ty: Type -> Type`), with every
  field still checked against the universe (recommended, as Lean). Or require index types
  to fit the type's universe, as Agda does by default.
- **D143. No descent through solved indices, and no cycle rule.** `m` from `n := Succ m` isn't
  smaller than `n` for termination, and `n = Succ n` is stuck rather than impossible
  (recommended; Agda issue #6654).
- **D144. Constructor syntax.** Indices after the header's colon; each constructor states
  its result type; unknown lowercase names in a constructor are implicit fields at the
  front, and uses in the result's indices don't disqualify them (recommended).
- **D145. `n + 1` in indices.** Write `Succ n` or `1 + n`, with a targeted hint when `n + 1`
  gets stuck (recommended). Alternatives: make `+` count down its second argument, as
  Lean's does (rewrites many proofs); or a trusted native rule `x + k ≡ Succ^k x`
  (breaks "a native computes exactly its definition").
- **D146. Patterns.** Implicit fields are skipped, or named `VCons [n := k] x xs` (no
  positional form). Impossible arms are left out, found by unification, with a one-level
  search over other family-typed arguments. `()` works for families. An arm that can never
  match is the warning `W-UNREACHABLE` (recommended).
- **D147. JavaScript.** Functions whose exported type mentions an indexed family are
  `E-EXPORT` for now (recommended). Boundary codecs that check indices come later.
- **D148. Records and groups.** Records can't have indices. Data groups may give each
  member its own indices, so `Even`/`Odd` can be mutual (recommended).
- **D149. One unifier.** The elaborator calls the kernel's unifier (a public function in
  `crates/core`) to find impossible branches, and the kernel runs it again when checking
  (recommended). The alternative, a second implementation in `crates/elab`, gives
  two to keep in step and no extra safety: the kernel's run is the one that counts.
- **D153. Built-in `=`.** Keep `Eq` and `J` built in, not redefined as a family. Without
  universe polymorphism, a family would only cover one universe (recommended).

## Sources

Stitchwort (at `9ccb120`): DESIGN.md §2, §6, §13; docs/core.md; docs/syntax.md;
docs/proposals/vec.md, proof-irrelevance.md, compact-text.md, mutual-recursion.md;
`crates/core/src/check.rs`, `termination.rs`, `erase.rs`, `globals.rs`;
`crates/elab/src/lib.rs`, `matching.rs`; `crates/syntax/src/ast.rs`.

- **L1.** Lean Language Reference, "Inductive Types", §"Parameters and Indices" and
  §"Subsingleton Elimination":
  <https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/>. Quotes:
  "Indices may vary among the occurrences of the type constructor"; a subsingleton has
  "at most one constructor" and "each of the constructor's parameter types is either a
  `Prop`, a parameter, or an index".
- **L2.** ammkrn, "Type Checking in Lean 4", Reduction, K-like reduction:
  <https://ammkrn.github.io/type_checking_in_lean4/type_checking/reduction.html>.
- **A1.** Agda documentation, "Without K":
  <https://agda.readthedocs.io/en/latest/language/without-k.html>.
- **A2.** Agda 2.6.4 changelog (`--large-indices`, `--forced-argument-recursion`, issue
  #6654): <https://hackage.haskell.org/package/Agda-2.6.4/changelog>.
- **A3.** Agda mailing list: "A sticky refusal" (2015),
  <https://lists.chalmers.se/pipermail/agda/2015/008000.html>; "Cannot apply injectivity"
  (2017, Cockx's advice), <https://lists.chalmers.se/pipermail/agda/2017/009739.html>.
- **A4.** Agda mailing list, "Agda with excluded middle is inconsistent" (2010):
  <https://lists.chalmers.se/pipermail/agda/2010/001529.html>,
  <https://lists.chalmers.se/pipermail/agda/2010/001531.html>.
- **A5.** Agda issue #6654, "Forcing analysis is inconsistent for large indices":
  <https://github.com/agda/agda/issues/6654>.
- **R1.** Rocq reference manual, "Inductive types and recursive functions" (`match … as …
  in … return`; "Empty and singleton elimination"):
  <https://rocq-prover.org/doc/master/refman/language/core/inductive.html>.
- **I1.** Idris 2 documentation, "Multiplicities":
  <https://idris2.readthedocs.io/en/latest/tutorial/multiplicities.html>.
- **B1.** E. Brady, C. McBride, J. McKinna, "Inductive Families Need Not Store Their
  Indices", TYPES 2003, LNCS 3085 (abstract):
  <https://research-portal.st-andrews.ac.uk/en/publications/inductive-families-need-not-store-their-indices/>.
- **G1.** H. Goguen, C. McBride, J. McKinna, "Eliminating Dependent Pattern Matching", in
  *Algebra, Meaning and Computation*, 2006, doi:10.1007/11780274_27 (abstract):
  <https://research-portal.st-andrews.ac.uk/en/publications/eliminating-dependent-pattern-matching/>.
- **C1.** T. Coquand, "Pattern matching with dependent types" (1992), and Hofmann–Streicher
  on K, as summarised in C2's abstract.
- **C2.** J. Cockx, D. Devriese, F. Piessens, "Eliminating dependent pattern matching
  without K", JFP 2016: <https://www.cambridge.org/core/product/4BC4EA2D02D801E5ABED264FE5FB177A>.
- **C3.** J. Cockx, A. Abel, "Elaborating dependent (co)pattern matching: No pattern left
  behind", JFP 30 (2020), e2 (ICFP 2018): <https://research.chalmers.se/en/publication/515222>.
