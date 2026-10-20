# Proposal: indexed data types (inductive families)

**Status:** implemented (stages 1-5, SW-178; see [As built](#as-built)). Draft 3, 20 October 2026. Drafts 1 and 2 each had an external review; draft 3
makes the second review's changes ([below](#changes-since-draft-2-re-review)), and draft
2 made the first's ([further down](#changes-since-draft-1-external-review)). The
re-review approves the architecture; its one required change before kernel work (the
`Prop` guard in the unifier, D137) is made. Review closed (D185, Matt, 20 October: no further review needed). Decisions D136-D149, D153 and D184 accepted as recommended (Matt, 20 October). Built, all five stages ([As built](#as-built)). Ticket SW-178. Matt decided D133 and D135 (20 October): indexed
data types go into the kernel before `Vec` (docs/proposals/vec.md, parked). The open
questions are D136 to D149, D153 and D184 in [§12](#12-decisions-wanted).

This note can be read without knowing type theory. [§1](#1-words) explains the words it
uses. Claims about Stitchwort were checked against the source on `main` at `9ccb120`
(draft 1), `5625c05` (draft 2) and `10000a5` (draft 3; `crates/` unchanged in what this
note cites).
Labels, as in the other notes:

- **[checked: S]**: read in source S (listed in [Sources](#sources)), or in the Stitchwort
  source at the `file:line` given;
- **[run]**: a Stitchwort program run with the release CLI on 20 October 2026;
- **[inferred]**: my reasoning from checked facts, not stated in a source;
- **[unverified]**: believed, but not confirmed.

## Changes since draft 2 (re-review)

1. **`Prop` guard in the unifier (required, D137).** Draft 2 let injectivity and conflict
   fire at any data type, so also at an inductive *proposition*. With two proof
   constructors `A`, `B: P`, the unifier would call `A = B` impossible, while the adopted
   proof irrelevance (D1′) proves `A = B`; transporting along it would then prove false.
   And `Hide 0 = Hide 1` at `Hidden: Prop` would decompose into `0 = 1`, recovering what
   the proposition hides. Now injectivity and conflict require the constraint's type to be
   an inductive type in `Type i`; deletion by conversion and well-typed solution stay for
   proofs; any other equation between proofs is stuck. Behaviour before and after D1′ is
   spelled out, and a later "delete any `Prop` constraint" rule is the new D184 (§6.3.2).
   Four regressions are added (tests 22-25).
2. **Dependent automatic constructor fields (D144).** `| Mk (n: Nat): Dep n i` would put
   `i: Fin n` in front of `n`. Policy: automatic fields still go at the front, ordered by
   their dependencies on each other; one whose type mentions a written field is refused,
   asking for an explicit binder (§7.1, test 26).
3. **Coverage builds a nested case (D146).** For `get`, `VNil` is *possible*; it's the
   `Fin 0` argument that is empty. The search now says it synthesises a case on that
   argument with every branch impossible, and keeps that reason separate from a
   constructor that itself conflicts. Kernel pair: test 27 (§7.3).
4. **Run-time cost of stored fields (D141).** `fromList` elaborates `VCons [n :=
   List.length xs] …`, so it is quadratic. An analogue run today shows it: 2.8 s for 4,000
   elements, 10.8 s for 8,000, 0.11 s without the length field **[run]**. §8.1 now gives a
   linear worker. Proof fields of a `Type` family are still erased as usual; driver tests
   cover a family with both kinds. "So it's no slower" is replaced by the narrower claim
   (§6.8).
5. **Termination (D143).** A recursive function field is classified from the
   positivity-checked declaration, before any parameter instantiation or refinement. Test
   12 is rewritten to reach the termination check for sure (`IdP`, an explicit empty
   proposition).
6. **Smaller points.** §6.3.4 says the index problem and its solutions never mention the
   matched variable. §6.3.6 cites Cockx–Devriese–Piessens, "Unifiers as Equivalences",
   for injectivity under K, and limits "different constructors are never equal" to data in
   `Type`. D142 is described as a conservative initial policy. D149's oracle compares the
   *effects* of substitutions, tells constructors, opaque applications and type formers
   apart, and comes with direct invariant checks. D147 refuses an indexed family anywhere
   in an export's serialized form (records, containers, aliases; test 28).
7. **Editorial.** §6.6 no longer says unification at `Type` "only ever deletes" (it also
   solves variables). §6.10's `Even`/`Odd` now has an example. Source L3's URL is fixed.
   §10's line counts are labelled rough, with the invariants and tests as the completion
   criteria.
8. **Decisions** gain the re-review's verdicts (§12). New: D184.

## Changes since draft 1 (external review)

The reviewer kept option A ("fix the small kernel unifier instead") and asked for these
changes before any kernel work. All are made.

1. **D142 reversed (critical).** Draft 1 allowed `Ty: Type -> Type`. That contradicted its
   own rule that every constructor field is checked against the universe: `TList (t: Ty b):
   Ty (List b)` has a hidden field `b: Type`, which is too large for a `Type 0` family. Draft
   1's claim that Lean allows this was wrong: Lean puts `WithIndex: Type u → Type (u + 1)`
   one universe up *because* its argument is an index **[checked: L3]**. Now an index's type
   obeys the same universe bound as a field (§6.2, §6.6), so `Ty: Type -> Type` is
   `E-UNIVERSE` and `Ty: Type -> Type 1` is the supported form. Genuinely large indices
   would need a design of their own.
2. **Typed, homogeneous constraints (critical).** §6.3 now unifies constraints
   `{ type, lhs, rhs }` and keeps one invariant before every rule: both sides have
   definitionally equal types in the current refined context. Constructor injectivity
   takes the fields in telescope order, solving each before forming the next field's
   constraint; if the next field's types can't be made equal, the problem is stuck
   (§6.3.2).
3. **Context refinement made precise (major).** A fixed rule decides which variable a
   solution replaces (the one bound later), and §6.3.4 says how the branch context stays
   well-formed when an outer variable is solved by a term with new constructor fields: the
   kernel's context is already *semantic* (a list of values indexed by level, not a
   telescope that must be in order), and the elaborator's lifting already orders captures by
   dependency. Draft 1's "it doesn't matter which is replaced" is gone.
4. **D143 reworded (major).** A stored constructor field is a structural subterm of the
   value (allowed, as today). A decrease derived from an index equation like `n = Succ m`
   is not allowed. Draft 1 called the second "forced-argument recursion", which is Agda's
   name for something else (§6.7).
5. **Minor.** §6.5: K/UIP is incompatible with univalent and higher-dimensional
   interpretations such as HoTT and cubical type theory (not "only univalence"). D149:
   one production unifier, plus a tiny reference unifier as a test oracle. D144: every
   automatically bound constructor variable is a real implicit field and passes the
   positivity and universe checks, result-only ones included. D146 and D140: only a
   conflict makes a constructor impossible; a stuck one is never omitted, and the
   one-level search is intentionally incomplete.
6. **Three new kernel tests** (§9, rows 19-21): dependent constructor injectivity with its
   stuck variant; an outer hypothesis `h: P n` refined to a well-formed `h: P (Succ m)`;
   rejecting `Ty: Type -> Type`. Test 9 is folded into 21, since the universe rule now
   rejects its example first.
7. **Sizes.** Stage 2 grows by about 200 lines (typed constraints, the reference
   unifier and its generated tests); §10.
8. **Decisions** carry the reviewer's verdicts (§12). D150 to D152 were never part of this
   note: decision numbers are shared across all of Stitchwort's work, and those went to
   other decisions while draft 1 was written. This note's last decision is D153.

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
13. [As built](#as-built)
14. [Sources](#sources)

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
  Every equation is *typed*, and both sides always have the same type; a constructor's
  fields are compared one at a time, in order. Proofs are never taken apart: the
  constructor rules apply only at types in `Type`, never `Prop`. Anything else is refused. An impossible
  branch has no body.
- **Axiom K is accepted.** Dropping an equation that already holds is Streicher's axiom
  K. Lean has it, and so does Agda by default; Stitchwort's adopted proof-irrelevance
  design (D1′) already implies it. K only rules out univalent and higher-dimensional
  readings of equality (HoTT, cubical type theory), which aren't planned (§6.5).
- **The known traps are avoided.** No injectivity of type formers (Agda's 2010
  inconsistency). No decrease derived from an index equation (Agda issue #6654). An
  index's type obeys the same universe bound as a field, so `Ty: Type -> Type` is refused
  and `Ty: Type -> Type 1` is the form to write (§6.6, §6.7).
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
- **Cost (rough):** about 1,250 to 1,550 lines in `crates/core` with its tests, 200 in
  `crates/syntax`, 1,050 to 1,450 in `crates/elab`, and 100 in `crates/js`, in five stages
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
  `Type` in `Ty: Type -> Type`. Not allowed in this design (§6.6).
- **Homogeneous equation.** One whose two sides have the same type. `i = j` with
  `i: Fin (Succ n)` and `j: Fin (Succ m)` isn't, until `n = m` is solved.

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
   forcing. This note keeps it so, applies the same bound to index types (§6.6, D142),
   and derives no decrease from index equations (§6.7, D143).

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

**What A costs in trust.** The unifier is new trusted code. It's kept small: four rules
on typed, homogeneous equations, no postponement, no higher-order cases, and "stuck"
always means "refuse" (§6.3). The elaborator calls the same function, so there's one
production implementation; a much simpler reference unifier checks it in tests (D149).

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
  including fields that the indices determine and implicit ones bound automatically. Every
  *index type* is checked by the same rule: an index whose type is in `Type i` needs
  `D: Type j` with `i ≤ j`, or `D: Prop` (`E-UNIVERSE` otherwise). So `Vec: Nat -> Type` is
  fine, `Ty: Type -> Type` is refused, and `Ty: Type -> Type 1` is accepted (§6.6, D142).
  This is Lean's rule **[checked: L3]**, and the line Agda 2.6.4 drew after issue #6654
  **[checked: A2]**.
- **Positivity.** In a field's type, a member of the group may appear only as `D ps js`,
  with `ps` exactly its own parameters (as now) and **no member of the group anywhere in
  `js`**, or as the result of a function type whose inputs don't mention the group. A
  constructor's result indices must not mention the group either.

### 6.3 `case` with unification

`Case(x, D, branches) ⇐ G`, where `x: D ps is`. For each constructor `c` with fields
`f₁ … fₖ` and result indices `js`, the kernel works out whether the branch is possible, and
under what substitution, then checks it.

#### 6.3.1 Constraints

A **constraint** is `{ type, lhs, rhs }`: three values. Unification works through a
**stack of telescopes**. A telescope entry holds a list of binders (each binder's type is a
term in the context of the earlier binders), the values the binders stand for on the left
and on the right, and how many have been solved.

The problem for a branch starts as one telescope entry: the index telescope of `D`, with
`ps` for the parameters, `is` on the left and `js` (evaluated with `ps` and the fields) on
the right.

**The invariant.** Before *every* rule is applied, the constraint's `lhs` and `rhs` both
have type `type`, up to conversion, in the current refined context. Every conversion the
unifier asks for is therefore between two values of one type, which is also the
precondition of D1′'s masked conversion (proof-irrelevance.md §7.4).

**Forming the next constraint.** Take the top telescope entry. If all its binders are
solved, pop it. Otherwise, for its next binder `B`, evaluate `B`'s type twice: with the
earlier left values (`typeL`) and with the earlier right values (`typeR`), in the current
refined context. If `typeL ≢ typeR`, the problem is **stuck**. Otherwise the constraint is
`{ typeL, lhsₖ, rhsₖ }`, which satisfies the invariant. Because an entry's binders are
taken one at a time, and a binder's constraint is only formed once all earlier ones are
solved, `typeL ≡ typeR` holds whenever the earlier left and right values have been made
equal, which is exactly when the earlier constraints were solved.

#### 6.3.2 The rules

Each rule takes the constraint just formed, with both sides evaluated in the current
refined context:

- **Deletion.** `lhs ≡ rhs`: the binder is solved.
- **Solution.** One side is a flexible variable `y` and the other side is `t` (§6.3.3 says
  which side when both are variables). The **occurs check**: `y` doesn't occur in `t`, nor
  in the type of any variable of `t`, nor, transitively, in the types of the variables
  those types mention. If it passes, substitute `t` for `y` (§6.3.4) and the binder is
  solved. If it fails, the problem is **stuck** (not impossible; D143).
- **Injectivity.** `type` is a data type `D' qs rs` **whose universe is `Type i`, not
  `Prop`**, and both sides are the same constructor `c'` of `D'`, with fields `us` and
  `vs`. The binder counts as solved, and a
  new telescope entry is pushed: `c'`'s fields, with `qs` for `D'`'s parameters, `us` on the
  left and `vs` on the right. So the fields are compared in telescope order, each one's
  constraint formed (and its types compared) only after the earlier fields are solved.
  Their parameters need no constraint: both sides have type `D' qs rs` by the invariant.
  The outer telescope's next binder is formed only after the pushed entry is popped, so
  its types compare the *solved* fields.
- **Conflict.** `type` is a data type **in `Type i`, not `Prop`**, and the sides are
  *different* constructors of it. The branch is **impossible**, and unification stops.
- **Numbers.** For `type` = `Nat`, a number is `Succ` of its predecessor, and `k + x` is
  `Succ` applied `k` times, for injectivity and conflict: `3 = Succ m` gives `2 = m`;
  `0 = Succ m` and `5 = 7` conflict. A compact text range expands one cell, as conversion
  does.
- **Anything else is stuck.** Stuck means the kernel **refuses the case**
  (`E-INDEX-STUCK`; the elaborator reports it first). Stuck includes:
  - a type former on either side (`Data`, `Pi`, `Sort`): `List a = List Nat` at type
    `Type` is stuck, never `a = Nat` (D139);
  - a function application that doesn't compute (`n + m` with `n` unknown);
  - an occurs-check failure (`n = Succ n`);
  - an equation between two proofs (its `type` is in `Prop`) that isn't settled by
    Deletion or Solution, whether or not the proofs are built from constructors;
  - a next binder whose `typeL ≢ typeR`.

The problem is **solved** when the stack is empty: the branch is possible, under the
substitutions made. If a conflict was found, it's impossible. Only a conflict makes a
branch impossible; a stuck problem is never treated as impossible (D140, D146).

**Why proofs are never taken apart.** Stitchwort reads propositions as having at most
one proof (DESIGN.md §6, and the adopted D1′, which derives propositional proof
irrelevance). Take

```
type P: Prop = | A | B
type Hidden: Prop = | Hide (n: Nat)
```

If Conflict fired at `P`, the unifier would call `A = B` impossible, and a function
`SameP A B -> FalseP` (with `type SameP (x: P): P -> Prop = | R: SameP x x`) would be
accepted by an empty match. Under D1′, `A = B` is provable, so `J` turns `R: SameP A A`
into a `SameP A B`, and that function proves `FalseP`. If Injectivity fired at `Hidden`,
`Hide 0 = Hide 1` would become `0 = 1`, a conflict, recovering the number the proposition
hides. So the guard is on the type of the *equation being solved*, at every constraint,
including those injectivity pushes for a constructor's fields. It doesn't stop matching on
`Le` or `Even`: their index equations are between numbers, at type `Nat`. Agda's unifier
likewise skips equations at irrelevant or `Prop` types before its other rules
**[unverified: per the re-review]**.

**Before and after D1′.**

- *Stage 1 (no D1′).* A proof equation is settled only by Deletion (the two proofs are
  convertible, e.g. both `h`) or Solution (one side is a proof variable, e.g. `h := A`).
  Otherwise it is stuck and the case is refused. Example: with `type T: Type = | MkT (h: P)
  (n: Nat)`, `MkT A 0 = MkT B 1` at `T` decomposes (`T` is in `Type`), reaches `A = B` at
  `P`, and is **stuck**. It is not impossible, even though the `Nat` fields would
  conflict, because the proof field comes first (test 25). `MkT h 0 = MkT A 1` solves
  `h := A`, then `0 = 1` conflicts: impossible, correctly.
- *With D1′.* D1′ skips proof-typed *arguments and fields* when comparing values, so
  Deletion succeeds more often: `MkT A 0 = MkT B 0` is deleted whole. But D1′ doesn't
  compare at the root, so the equation `A = B` at `P` on its own is still not convertible,
  and stays stuck. Neither version derives a contradiction by telling proof constructors
  apart. A further rule, "an equation at a type in `Prop` is deleted", would be sound once
  D1′ makes all proofs of a proposition equal, and would make `MkT A 0 = MkT B 1` an
  ordinary conflict. It's D184, for when D1′ lands; without D1′ it would break the
  homogeneity invariant, since types mentioning `A` and `B` wouldn't compare equal.

#### 6.3.3 Which variable a solution replaces

A **flexible variable** is a context entry that still stands for itself: a parameter of
the definition, or a field bound by this or an enclosing case, not yet replaced by a
constructor or a solution. The matched `x` isn't flexible (it's replaced after
unification), and there are no `let`s, since a case is never under one.

The policy is fixed, so the elaborator (which calls the same function, D149) and the kernel
always agree:

1. If exactly one side is a flexible variable, solve it.
2. If both are, solve the one bound **later** (higher level) as the earlier one. If its
   occurs check fails, try the other way. If both fail, stuck.
3. If neither is, use the other rules.

Why "later": the later one is usually a field of the constructor being matched, a name
the user didn't choose. Replacing it keeps the definition's own variables, which the
signature, the goal and the error messages use. In `head: Vec a (Succ n) -> a`, matching
`VCons [m] …` gives `Succ n = Succ m`, then `n = m`, and `m` (bound later) becomes `n`.

The choice can change the shape of the refined context, which names the goal shows, and
whether a later occurs check passes. It can't change soundness: either orientation gives a
most general solution **[inferred]**. That's why it's fixed rather than left open.

#### 6.3.4 The refined context stays well-formed

**The issue.** With `n: Nat`, `h: P n` and `v: Vec a n`, splitting `v` as `VCons [m] x xs`
solves `n := Succ m`. Inside the branch, `h` must have type `P (Succ m)`. But `m` is a new
field, bound *after* `h`. Read as an ordered telescope, the context now has an earlier
entry whose type mentions a later one.

**The choice: a semantic context, as the kernel already has.** The kernel's context isn't
an ordered telescope of terms. It is two vectors of *values* indexed by level: `env` (what
each variable stands for) and `types` (each variable's type). Types are quoted back to
terms only at the current depth, where every level in use is in scope. `check_case` today
substitutes the constructor value, whose fields are bound after `x`, into the types and
values of variables bound *before* `x` (`crates/core/src/check.rs:679-689`, the `substitute`
calls), and docs/core.md:109 relies on it ("`rest: res o` is bound before `o` is matched").
Solutions use the same mechanism, in this order for each branch:

1. bind the constructor's fields, so the branch's depth includes them (today the fields
   are bound just after the substitution; a solution's `t` can mention them, so binding
   moves first);
2. run unification at that depth; each solution `y := t` runs `substitute` with `t` over
   `env`, `types`, the goal and the values on the telescope stack, and sets `env[y] := t`;
3. substitute `x := c f₁ … fₖ`, as today (well-typed now, since `is ≡ js` holds).

In the example, `types[h]` becomes the value `P (Succ m)`, mentioning `m`'s level. Quoted
at the branch's depth, it is a well-scoped term. `h` keeps its level and `n` keeps a slot
whose value is `Succ m`, like the gap a `let` leaves (docs/core.md:167).

**The invariant that makes this safe.** Among the variables still flexible, "the type of
`a` mentions `b`" is acyclic. It holds before the first case (the definition's parameters
form a telescope) and each step keeps it: a field's type only mentions the parameters of
`x`'s type and earlier fields, and a solution `y := t` can only add edges from variables
whose types mentioned `y` to the variables of `t`; the transitive occurs check refuses
exactly the solutions where `t`'s variables' types lead back to `y`. The matched `x` takes
no part in this: the index problem never mentions it (`x`'s type `D ps is` can't, and the
fields' types mention only `ps` and earlier fields), and `x` isn't flexible, so no
solution mentions it either. The final step `x := c f₁ … fₖ` therefore substitutes a
value built from the fields into a context and goal where every solution is already in
place, and adds no edge back into the index problem. So the variables can
always be put in some order where each type mentions only earlier ones. Nothing in the
kernel needs that order, but anything that rebuilds a telescope can find it.

**Who does rebuild a telescope, and how.** Only the elaborator:

- A lifted `match` or local definition takes its captures "ordered by their types'
  dependencies, keeping context order where possible" (`crates/elab/src/lift.rs:20`,
  `841-881`), and refuses a cycle. That already handles today's nested patterns, and by
  the invariant it never meets a cycle from a solution.
- Metavariables are applied to the variables in scope except those a case branch replaced
  (docs/core.md "Elaboration"). Solved variables are excluded the same way.
- Error messages list the context in dependency order.

The alternatives were rebuilding and reordering the telescope after each solution (what a
named-variable kernel would do), or rebinding affected outer variables as copies after the
fields (what the elaborator does for generalised `match` scrutinees). Both add code to the
trusted kernel to produce a structure it never reads. The semantic context needs none,
and test 20 (§9) pins the example above.

#### 6.3.5 Checking the branch

- **Possible branch:** its body is checked in the refined context against the refined goal.
- **Impossible branch:** it has no body (`Branch.body` becomes optional). A body on an
  impossible branch, or no body on a possible one, is `E-MALFORMED`: the elaborator decides
  which, and the kernel checks it.
- **The `Prop` rule** (§6.4) is checked as today, with one change: a case where every
  branch is impossible (by conflict) may produce anything.

The kernel records nothing new in the term apart from which branches are impossible.
Hashing covers that (§6.9).

#### 6.3.6 Why it's sound

**[inferred, from G1, C3 and U1]** The rules use only facts true of values of data types
in `Type`: different constructors of such a type are never equal, equal constructor
values have equal fields (taken in order, so each field equation is between values of
one type), a variable equal to a term can be replaced by it, and an equation that already
holds can be dropped (K). For proofs only the last two are used, and they hold in any
reading of `Prop`, including the proof-irrelevant one (§6.3.2). Goguen, McBride and
McKinna's translation turns exactly these steps on homogeneous equations into
eliminators plus K, so a case tree using them proves nothing that eliminators plus K
couldn't. For the injectivity step on an *indexed* constructor, where the fields'
equations are taken in telescope order, Cockx, Devriese and Piessens give the general
statement: constructor injectivity holds for an indexed family when its index telescope
satisfies K ("Unifiers as Equivalences", §4.3, Lemma 6 **[unverified: section and lemma
number as cited by the re-review]**). K is accepted (D138), so that condition holds. Operationally: a case only reduces when `x` is a constructor
value `c us`. Its type `D ps is` then makes `is ≡ js[us]`, so the substitutions the branch
was checked under hold for the actual values, and an impossible branch is never reached.

**Dependent indices.** A family like `Sub: (n: Nat) -> Fin n -> Type` has an index whose
type mentions an earlier index. That's the same telescope rule as for constructor fields:
the second index's constraint is formed only once the first is solved, and is stuck if the
types still differ. This is stricter than Agda, which postpones stuck equations and comes
back to them, and simpler (D137).

### 6.4 `Prop` elimination

Unchanged in stage 1: a proposition matched to produce data must be alone in its group,
have at most one constructor, and have only proof fields. One addition: **a case whose
branches are all impossible may produce anything**, at any universe, because it is never
reached. Impossible means a conflict was found (§6.3.2); a stuck branch never counts,
since the case is refused outright. This makes `notEvenOne` (§8.4) and "`Le (Succ n) 0` is impossible" usable in
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
(K-like reduction), and Agda has it by default. K/UIP is incompatible with univalent and
higher-dimensional interpretations of equality, such as homotopy type theory and cubical
type theory (Agda refuses `--cubical` together with `--with-K` **[unverified]**).
Stitchwort plans neither. Without deletion, `Le n n` couldn't be
matched against `LeRefl` (both equations solve to `n = n`) without extra steps, and K
would arrive anyway with D1′. **Recommendation: accept K (D138).**

### 6.6 Universes: no large indices

An index's type obeys the same universe bound as a constructor field (§6.2). A family
indexed by types must live one universe up:

```
type Ty: Type -> Type =                  -- refused: E-UNIVERSE
  | TNat: Ty Nat
  | TList (t: Ty b): Ty (List b)         -- the field `b: Type` is too large for `Type`

type Ty: Type -> Type 1 =                -- accepted
  | TNat: Ty Nat
  | TList (t: Ty b): Ty (List b)
```

Two things would be wrong with the first one, and both are refused. Its index type `Type`
lives in `Type 1`, bigger than the family's `Type`. And `TList` has a hidden implicit field
`b: Type` (D144), which the unchanged field rule already refuses: draft 1 allowed the first
while keeping that rule, which contradicted itself. Lean has the same rule: its
`WithIndex: Type u → Type (u + 1)` is one universe up because the `Type u` argument is an
index, not a parameter **[checked: L3]**. This isn't only about what's stored at run time;
with the rest of this design (stored fields, fields as structural subterms, impredicative
`Prop`), it's what keeps the universes sound.

This is Stitchwort's **conservative initial policy**, not a claim that no design could
allow larger indices. The cost: without universe polymorphism, a `Ty a: Type 1` can't go
in a `List`, which holds `Type 0`. Genuinely large indices (Agda's `--large-indices`) would
need their own design, covering forcing, erasure, termination and universe soundness.

Matching on `Ty`: at type `Type`, unification can delete (convertible types) or solve (a
type variable), but never decompose, because type formers aren't injective (§6.3.2). So
matching `t: Ty (List Nat)` against `TList` is stuck (`List Nat = List b`) and refused.
Matching `t: Ty c` (a variable) works: `c := List b`.

### 6.7 Termination

Two different things, kept apart (D143):

- **Allowed, as today: stored fields are structural subterms.** A field of a matched
  constructor is smaller than the match, whatever its type (docs/core.md:153). The
  implicit `n` in `VCons [n] x xs` is a real stored field, so it is smaller than the
  vector, and so is `xs`. A **recursive function field** is one whose *declared* type is a
  function returning a group member at any indices. That classification is made once,
  from the positivity-checked constructor declaration, before any parameter is
  instantiated or any branch refined, and never from a field's type as it looks in a
  branch. So a generic field `f: (p: Prop) -> p -> p` never becomes a recursive function
  field, even where `f` is applied with `p` set to the type being defined (`is_recursive_fn`
  already reads the declared field term, `g.data(d).ctors[c].fields`, at
  `crates/core/src/termination.rs:245, 344-348` **[checked]**; the kernel work keeps it
  there, and must not switch to the refined value).
- **Not allowed: a decrease derived from an index equation.** In the branch where the
  definition's parameter `n` was solved as `Succ m`, the termination checker does *not*
  learn `m < n`. It still reads relations only from the terms (termination.rs:19), and a
  solution is a fact about types. Recursion on the vector gives the same evidence where
  it's needed.

Issue #6654 is why the second stays out. Agda's counterexample recursed on a field whose
own value was not a subterm in any real sense (the forced function `f`, applied to make a
new `Bad`), and Agda counted it because the index determined it. Stitchwort's version of
that example is test 12, refused because `f`'s declared type returns `p`, not `Bad`. The
issue's discussion names restricting descent to proper recursive arguments as one repair,
and shows why a generic function can hide the recursive use; that's why the
classification is made from the declaration **[checked: A5]**.

**No cycle rule either.** `n = Succ n` is stuck, not impossible (§6.3.2). Agda's cycle
rule would accept more, and can come later (D143).

### 6.8 Evaluation, conversion, erasure, JavaScript

- **Values.** `Value::Data(D, args)` carries parameters and indices; a constructor value
  carries its fields, forced ones included. Conversion gains no new equality rules: its
  existing machinery compares the extra index arguments like any others. That doesn't make
  it free: comparing two `Data` values now also compares their indices, which may need
  computing, so cost depends on the terms compared. Fording would add a proof to every
  value and a `J` to every match.
- **Unfolding.** A case reduces when its scrutinee is a constructor; it can never be one
  of the impossible ones (by typing).
- **Running with erasure.** A family's *computational* fields, including forced implicit
  ones like `n` in `VCons`, are computed and stored (D141). Its *proof* fields follow the
  existing erasure rule (`Ctor::field_erased`): in `type Certified: Nat -> Type = |
  MkCertified (n: Nat) (ok: IsPrime n): Certified n`, `ok` is erased even though
  `Certified n` is data. Driver tests run such a family with and without erasure.
  Stored fields cost work: an implicit field is computed from whatever the elaborator
  inferred for it, which can be expensive (`fromList`, §8.1).
  A `case` on an erased proof takes its only *possible* branch;
  if every branch is impossible, the program is wrong and the run fails loudly
  (`unreachable`). The erasure argument in erase.rs still holds, because the `Prop` rule
  is unchanged.
- **JavaScript.** A family's values are `{ tag, …fields }`, as for any data type, with forced
  fields like `n` stored. An impossible branch compiles to nothing; a case with no possible
  branch throws. Exporting a function is `E-EXPORT` for now if an indexed family appears
  **anywhere in the serialized form** of its inputs or result: directly, through a type
  synonym, inside a container (`List (Vec Nat 3)`), or in a record field. Decoding would
  have to check the indices. §8.5's `Grid` is the example: `Grid -> Grid` must be refused,
  since decoding `rows` would have to check every row's length (D147, test 28).

### 6.9 Hashing

A data type's hash covers its index telescope and each constructor's result indices; a
case covers which branches are impossible. Hashes change for every data type, since the
layout changes. That's fine: hash stability isn't a goal, and the hash snapshot is
regenerated.

### 6.10 Data groups

Members of a group share parameters and universe (as now), but each has its own index
telescope. For example (a variant of §8.4's `Even`, defined together with `Odd`):

```
type Even: Nat -> Prop =
  | EvenZero: Even 0
  | EvenSucc (h: Odd n): Even (Succ n)

type Odd: Nat -> Prop =
  | OddSucc (h: Even n): Odd (Succ n)
```

Lean allows different indices in a mutual block **[unverified]**. The elaborator's `E-MUTUAL-PARAMETERS` still compares
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
  (`FZero: Fin (Succ n)`) gets its type from the index's type, `Nat`. Either way the
  name becomes a **real implicit field** of the constructor, in the kernel declaration,
  and passes the positivity and universe checks like any written field. That's what
  refuses `b` in `TList` for a `Ty: Type -> Type` (§6.6).
- **Where automatic fields go.** At the front, before the written fields, as in
  signatures. Among themselves they're ordered by dependency (one whose type mentions
  another comes after it), and a cycle is an error. An automatic field whose type would
  mention a **written** field can't go at the front, so it's refused with a message asking
  for an explicit binder:

  ```
  type Dep: (n: Nat) -> Fin n -> Type =
    | Mk (n: Nat): Dep n i               -- refused: `i: Fin n` would need `n`, a written field
    | Mk (n: Nat) [i: Fin n]: Dep n i    -- accepted: written out, after `n`
  ```

  ```
  [E-IMPLICIT-FIELD] `i` needs to be written as a field
    `i` is used only in the result, so its type is `Fin n` from `Dep`'s indices, and that
    mentions the field `n`. Automatic fields go before the written ones.
    Note: write `[i: Fin n]` after `(n: Nat)`.
  ```

  Placing automatic fields among the written ones by their dependencies would accept
  more, at the cost of a less predictable order of implicit fields; it can come later
  (D144, test 26).
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
  unification finds a **conflict**, the branch is marked impossible and nothing is
  reported. Only a conflict permits leaving an arm out. If the missing arm is possible,
  it's `E-NONEXHAUSTIVE` as today, naming the constructor and the indices it would have.
  If unification is stuck, the constructor stays possible: it is never quietly treated as
  impossible, and the case can't be built at all (`E-INDEX-STUCK`, which the kernel would
  also give).
- **A missing arm can be empty because of another argument.** This is a different reason
  from the one above, and the compiler keeps them apart. In `get: Vec a n -> Fin n -> a`,
  the `VNil` case has no arm, but `VNil` is *possible* for a `Vec a n`: it solves `n := 0`.
  What's empty is the other argument, now `i: Fin 0`. The compiler tries splitting the
  other columns whose types are families, one level deep. If one has only conflicting
  constructors, it **synthesises a case on that argument**, with every branch impossible,
  as the `VNil` branch's body:

  ```
  case v of
    VNil         => case i of           -- VNil: possible, so it has a body
                      FZero => impossible     -- Fin 0 = Fin (Succ k): conflict
                      FSucc => impossible     -- likewise
    VCons x xs   => case i of
                      FZero   => x
                      FSucc j => get xs j
  ```

  So the kernel sees `VNil.body = Some(inner case)`, and both inner branches have no body.
  Marking `VNil` itself impossible would be wrong (unification succeeds there), and the
  kernel refuses that tree (`E-MALFORMED`, test 27). Lean and Agda accept this `get`
  **[unverified for Lean]**. The search is intentionally incomplete: an emptiness that
  needs two levels of splitting isn't found, and the user writes the split (or a `()`) by
  hand (D146).
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

**`fromList` as written is quadratic.** `VCons` has a stored implicit field `n` (D141),
and the elaborator fills it by unification: the expected type `Vec a (List.length (Cons
x xs))` computes to `Vec a (Succ (List.length xs))`, so the second arm elaborates to
`VCons [n := List.length xs] x (fromList xs)` **[inferred]**. Running it computes
`List.length` of every suffix: n(n-1)/2 steps for n elements. An analogue that runs today,
a list type with a stored field `SCons (List.length xs) x (fromList xs)`, takes 2.8 s for
4,000 elements, 10.8 s for 8,000 (four times as long for twice as many), and 0.11 s for
8,000 with the field set to `0` **[run]**. The linear version passes the length down, so
each field is a number already computed:

```
def fromListN: (n: Nat) -> (xs: List a) -> List.length xs = n -> Vec a n
  | 0, Nil, _              => VNil
  | Succ k, Cons x xs, ok  => VCons [n := k] x (fromListN k xs (Nat.succInj ok))
  | 0, Cons _ _, ok        => Void.absurd (Nat.succNotZero ok)
  | Succ _, Nil, ok        => Void.absurd (Nat.zeroNotSucc ok)

def fromList (xs: List a): Vec a (List.length xs) := fromListN (List.length xs) xs rfl
```

(The lemma names stand for the prelude's constructor injectivity and disjointness lemmas
**[unverified: exact names]**; the proofs are erased at run time.) The general lesson for
D141: a stored implicit field costs whatever its inferred term costs. SW-179 should
compare `Vec` representations with the linear conversions, and measure at AoC sizes.

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
| 6 | Type former injectivity: matching `t: Ty (List Nat)` against `TList` (with `Ty: Type -> Type 1`, §6.6) | `E-INDEX-STUCK` | Matching `t: Ty c` |
| 7 | Occurs check: `type Loop: Nat -> Nat -> Type = \| MkLoop: Loop m (Succ m)`, matching `l: Loop n n` | `E-INDEX-STUCK` | Matching `l: Loop n k` |
| 8 | Negative occurrence through an index-varying field: `\| MkBad (f: Bad 0 -> Void): Bad 1` | `E-POSITIVITY` | `Vec` |
| 10 | Wrong parameters in a constructor result: `\| Weird: Vec Nat 0` in `Vec (a: Type)` | `E-TYPE-MISMATCH` | `VNil: Vec a 0` |
| 11 | Agda #6654 in `Type`: `type Bad: ((p: Type) -> p -> p) -> Type = \| B (f: (p: Type) -> p -> p): Bad f` | `E-UNIVERSE` (the field is too large) | The same in `Type 1` |
| 12 | Agda #6654 in `Prop`, isolating termination: `type FalseP: Prop` (no constructors); `def IdP: Prop := (p: Prop) -> p -> p`; `type Bad: IdP -> Prop = \| B (f: IdP): Bad f`; `def idP: IdP := p h => h`; `def bad: Bad idP := B idP`; `theorem noBad [x: IdP]: Bad x -> FalseP \| B f => noBad [idP] (f (Bad idP) bad)`. Everything is a proof matched into a proof, so typing and `Prop` elimination pass, and the index equation `x = f` at `IdP` is a variable solution | `E-TERMINATION` (`f`'s declared type returns `p`, not `Bad`, so `f (Bad idP) bad` isn't smaller) | Structural recursion on a proof of `Le` (`leToLeq`, §8.3) |
| 13 | Descent only through a solved index: `def down [n: Nat]: Vec Bool n -> Nat \| VNil => 0 \| VCons [n := m] _ _ => down [m] (replicate m True)` (`m` is one less than `n`, but that isn't evidence) | `E-TERMINATION` | The same recursing on `xs` |
| 14 | `Prop` elimination through an index field: `type IsSucc: Nat -> Prop = \| MkIsSucc: IsSucc (Succ n)`, `pred: IsSucc k -> Nat` reading `n` | `E-PROP-ELIM` | `IsSucc k -> k != 0` |
| 15 | `Prop` elimination with two constructors: `Le m n -> Bool` by matching | `E-PROP-ELIM` | `Le (Succ n) 0 -> Nat` (every branch impossible) |
| 16 | A missing arm that is possible: `zipWith` without the `VCons, VCons` arm | `E-NONEXHAUSTIVE` | §8.1 `zipWith` |
| 17 | A record with indices, built directly | `E-MALFORMED` (kernel) | A record with parameters |
| 18 | Exporting `head` | `E-EXPORT` | Exporting a `List Nat -> Nat` function that uses `Vec` inside |
| 19 | Dependent constructor injectivity, stuck variant. `type W: Type = \| Mk (n: Nat) (i: Fin (Succ n))`, `type Q: W -> Type = \| MkQ: Q (Mk (Succ m) j)`, matching `q: Q (Mk (g k) i)` with `g` opaque. The first fields give `g k = Succ m` (stuck). The unifier must stop there, never comparing `i: Fin (Succ (g k))` with `j: Fin (Succ (Succ m))` (which would "solve" `j := i` at the wrong type) | `E-INDEX-STUCK` (kernel) | `type P: W -> Type = \| MkP: P (Mk m j)` matching `p: P (Mk n i)`: `m := n` first, then `j := i` at `Fin (Succ n)` |
| 20 | A refined outer hypothesis read at the wrong type: with `[n: Nat] (h: P n) (v: Vec a n)`, the `VCons [n := m] _ _` branch using `h` where a `P m` is expected | `E-TYPE-MISMATCH` (kernel) | The same branch using `h` where `P (Succ m)` is expected, with `h`'s type quoted at the branch's depth as the well-scoped `P (Succ m)`; and the same through a lifted `match` (captures ordered `m` before `h`) |
| 21 | Large index: `type Ty: Type -> Type = \| TNat: Ty Nat \| TList (t: Ty b): Ty (List b)` (also covers draft 1's test 9, whose example this rule now refuses first) | `E-UNIVERSE` | `type Ty: Type -> Type 1 = …` |
| 22 | `Prop` conflict: `type P: Prop = \| A \| B`, `type SameP (x: P): P -> Prop = \| R: SameP x x`, `theorem noAB: SameP A B -> FalseP \| ()`. The equation `B = A` is at `P: Prop`, so it never conflicts | `E-INDEX-STUCK` | The same with `type P: Type = \| A \| B` (`SameP` still a `Prop` family): accepted, by conflict at `P: Type` |
| 23 | `Prop` injectivity: `type Hidden: Prop = \| Hide (n: Nat)`, a family indexed by `Hidden`, and an empty match needing `Hide 0 = Hide 1` | `E-INDEX-STUCK` (never decomposed into `0 = 1`) | The same with `Hidden: Type`: accepted, by injectivity then conflict |
| 24 | (accept side only) Ordinary data still works: tests 22 and 23 in `Type` | - | Unit tests of the unifier at both universes, before and after D1′ (and D184 if adopted) |
| 25 | Proof field before data: `type T: Type = \| MkT (h: P) (n: Nat)` (`P: Prop` as in 22), an empty match needing `MkT A 0 = MkT B 1` | `E-INDEX-STUCK` (stuck at `A = B`, never "impossible" from the later `0 = 1`) | `MkT h 0 = MkT A 1` with `h` a variable: `h := A`, then `0 = 1`: impossible, accepted |
| 26 | Dependent automatic field: `type Dep: (n: Nat) -> Fin n -> Type = \| Mk (n: Nat): Dep n i` | `E-IMPLICIT-FIELD` | `\| Mk (n: Nat) [i: Fin n]: Dep n i` |
| 27 | `get` (§8.2) with the `VNil` branch marked impossible, built directly | `E-MALFORMED` (kernel: `VNil` unifies with `Vec a n`) | `VNil`'s body a case on `i: Fin 0` with both branches impossible (§7.3) |
| 28 | Exporting `Grid -> Grid` (§8.5: `Vec` inside a record); exporting `List (Vec Nat 3) -> Nat`; exporting through a synonym `type Row = Vec Bool 5` | `E-EXPORT` | Exporting a `List Nat -> Nat` function that uses `Vec` inside |

Also, not a rejection: `sameK` (§6.5) is **accepted**, documenting the K decision. Driver
tests run each §8 example with and without erasure and compare results, as
`crates/driver/tests` does for natives, plus an indexed family with both a computational
field and a proof field (`Certified`, §6.8), so erasure of the proof field and retention
of the data field are both exercised.

## 10. Build plan

Kernel work is Opus (spec and implementation, or careful review), per the model tiers.
Line counts are rough planning estimates, including tests. A stage is **done when its
invariants hold and its tests pass**, not when it reaches a size: in particular the `Prop`
guard (tests 22-25), dependent fields and binders (19, 26), and context refinement (20, 27).

| Stage | What | Crates | Size |
|---|---|---|---|
| 1 | **Kernel declarations.** Index telescopes in `declare_data_group`; result indices in `define_data_group`; `Data`/`Ctor` typing with indices; positivity and universe rules (§6.2); records refuse indices; index types under the field universe rule (§6.6); hashing; printing. Kernel tests 8, 10, 11, 17, 21 | `core` (globals, check, hash, pretty, registry) | 400-500 |
| 2 | **Kernel `case`.** The unifier on typed constraints with the telescope stack (new `core/src/unify_index.rs`, public so the elaborator can call it; §6.3); the orientation policy and the bind-unify-substitute order in `check_case`; impossible branches (`Branch.body: Option`); `Prop` rule addition; evaluation, erasure (`unreachable`), termination (impossible branches have nothing). A **reference unifier** in the tests (D149): terms over a toy signature that tells apart data constructors (in `Type` and in `Prop`), opaque applications and type formers (`Nat`, `Fin`, `W`, `P`, `Hidden`), naive substitution, no levels. Generated bounded problems (depth ≤ 3, dependent fields and proof fields included) go through both; the outcome (solved, conflict, stuck) must agree, and for solved ones the *effect* of the two substitutions on the original variables and constraints, normalised, must agree (equivalent substitutions can differ as maps). Separately, direct checks on the production unifier: every reported solution makes the original equations convertible; the refined context is well formed; the occurs check catches an occurrence hidden in another variable's type, including transitively; refined types quoted at branch depth are well scoped. Those last two need levels, so they are kernel tests, not oracle comparisons. Kernel tests 1, 2, 4-7, 12-15, 19, 20, 22-25, 27 and `sameK` | `core` | 850-1,050 |
| 3 | **Syntax and declarations.** `type D (ps): I -> s =`; constructor result types; implicit fields `[n: T]` and automatic ones, ordered by dependency, with `E-IMPLICIT-FIELD` (D144, test 26); building values with implicit fields; `E-INDEX-STUCK` hints | `syntax` (~200), `elab` (~300) | 500 |
| 4 | **Matching.** Typed splitting in `compile`: impossible branches, the one-level search for missing arms, synthesising the nested empty case (D146, §7.3), `[n := k]` patterns, `()` for families, `W-UNREACHABLE`, `match` lifting over indices, messages (§7.4). Surface tests 3, 4, 5, 6, 16 | `elab` (`lib.rs`, `matching.rs`, `lift.rs`) | 700-900 |
| 5 | **Running and JS; docs.** Driver tests with and without erasure, including `Certified`; JS for impossible branches; `E-EXPORT` for families anywhere in the serialized form (tests 18, 28); examples `examples/accept/indexed-families.sw`; docs/core.md, docs/syntax.md, DESIGN.md §6 and §13 | `js` (~100), `driver`, docs | 300 |

Stages 1 and 2 can be one lane; 3 and 4 depend on 2. Each stage's tests are the
must-reject rows above for its part; stage 2 isn't done until tests 19, 20, 22-25 and 27
and the reference-unifier checks pass. Totals: `core` about 1,250-1,550 lines (draft 1:
1,000-1,300; typed constraints, the `Prop` guard and the reference unifier), `elab` about
1,050-1,450 (the dependency ordering of automatic fields and the nested empty case), the
rest unchanged. After stage 5, SW-179 decides `Vec`'s representation
(vec.md D126 and the rest) with a real choice between options A and C there.

## 11. What else changes

- **DESIGN.md §6.** "Dependent pattern matching: for the POC, patterns are kept simple"
  becomes a pointer to this note. The `Prop` index clause is marked "not yet" (D140).
  §13's must-reject table gains rows 4, 6, 11, 12, 13, 19, 21, 22 and 25.
- **docs/core.md.** The table row "Parameters but no indices" changes; "Data types" and
  "Case trees" gain §6.2 and §6.3; "Equality" mentions K.
- **docs/proposals/vec.md.** Option C becomes available; its §4 C paragraph and D133 are
  answered.
- **Proof irrelevance (SW-93).** Independent. D1′ masks proof positions in conversion;
  this note adds no proofs to values. The unifier only ever compares two values of one
  type (§6.3.1), which is the precondition D1′ documents for its masked conversion. And
  the unifier never takes proofs apart (§6.3.2), so nothing it concludes contradicts
  D1′'s proof irrelevance. Before D1′ some proof equations are stuck; after it, more are
  deleted; neither tells proof constructors apart. So either can land first
  **[inferred]**. If D184 is adopted, its rule lands with or after D1′, never before.

## 12. Decisions wanted

This note's decisions are D136 to D149, D153 and D184. D150 to D152 were never part of
it: decision numbers are shared across all of Stitchwort's work, and those three went to
other decisions while draft 1 was being written. Draft 3 adds D184; the numbers between
D153 and D184 went to other notes.

"Review 1" is the external verdict on draft 1, "Review 2" the verdict on draft 2. Every
change either review asked for is already in the recommendations below.

| # | Question | Recommendation (draft 3) | Review 1 | Review 2 |
|---|---|---|---|---|
| D136 | Approach | A: native indices, unification in kernel case trees | Agree with changes (made) | Agree |
| D137 | Kernel unification rules | Four rules on typed homogeneous constraints, telescope-ordered injectivity; injectivity and conflict only at types in `Type`; proof equations otherwise stuck; stuck refuses | Agree with changes (made) | Agree after the `Prop` guard and its regressions (made: §6.3.2, tests 22-25) |
| D138 | Axiom K | Accept | Agree | Agree |
| D139 | Type former injectivity | Never | Agree | Agree |
| D140 | `Prop` elimination | Today's rule, plus "every branch conflicts" (conflict as now guarded) | Agree | Agree |
| D141 | Indices at run time | Keep computational fields, forced implicit ones included; proof fields erased as usual; cost documented | Agree | Agree with changes (made: §6.8, §8.1) |
| D142 | Large indices | Not in stage 1: index types obey the field universe bound (conservative initial policy) | Disagree with draft 1 (reversed) | Agree |
| D143 | Termination and cycles | Stored fields are subterms; no decrease from index equations; recursive fields classified from the declaration; no cycle rule | Agree with wording change (made) | Agree with changes (made: §6.7, test 12) |
| D144 | Constructor syntax | Automatic fields are real implicit fields, at the front, ordered among themselves; refused if they depend on a written field | Agree with changes (made) | Agree after choosing the policy (made: policy 2, test 26) |
| D145 | `n + 1` | `Succ n` / `1 + n`, with a hint | Agree | Agree |
| D146 | Patterns | Omission only by conflict; one-level search synthesises the nested empty case; incomplete by design | Agree with changes (made) | Agree with changes (made: §7.3, test 27) |
| D147 | JS boundary | `E-EXPORT` for a family anywhere in the serialized form | Agree | Agree with changes (made: §6.8, test 28) |
| D148 | Records and groups | No indexed records; per-member indices in groups | Agree | Agree |
| D149 | One unifier | One production unifier; a reference oracle comparing effects; direct invariant checks | Agree with changes (made) | Agree with changes (made: §10) |
| D153 | Built-in `=` | Keep | Agree | Agree |
| D184 | `Prop` deletion after D1′ | New; see below | - | - |

- **D136. Approach.** (A) native indices, with unification in kernel case trees
  (recommended); (B) native indices, kernel cases only on variable indices, and the
  elaborator casts with `J`; (C) Fording, with equation fields and no indices.
- **D137. Unification rules in the kernel.** Exactly deletion, solution (with an occurs
  check that covers types, transitively, and the fixed orientation of §6.3.3),
  injectivity and conflict for constructors and numbers **at types in `Type`, never at a
  proposition**; an equation between proofs that deletion or solution doesn't settle is
  stuck (§6.3.2). Constraints are typed and
  homogeneous before every rule; a constructor's fields are unified in telescope order,
  each formed only after the earlier ones are solved; a field whose two types still differ
  is stuck; anything stuck refuses the case (recommended). The alternative is to add
  Agda's postponement and cycle rule now.
- **D138. Axiom K.** Accept it: the deletion rule stays, and K becomes provable
  (recommended, consistent with D1′ and Lean). Or forbid deletion, as Agda's
  `--without-K` does.
- **D139. Type formers are never injective in matching** (recommended; Agda's 2010
  inconsistency). Matching on `Ty (List Nat)` against `TList` is refused.
- **D140. `Prop` elimination.** Keep today's rule, plus "a case whose branches all
  conflict produces anything" (recommended). Only a conflict, never a stuck problem,
  shows a branch is empty. DESIGN.md §6's index clause waits until something needs it.
- **D141. Indices at run time.** Keep computational fields, forced implicit ones (like `n`
  in `VCons`) included, and keep implicit index parameters at run time, as DESIGN.md §6
  says; proof fields are erased by the existing rule (recommended). A stored implicit
  field costs whatever its inferred term costs: `fromList` as written is quadratic, and the
  library uses a linear worker (§8.1). Erasing
  forced fields (Brady–McBride–McKinna) or Idris-style quantities come later, as a
  separate change with its own argument that the representations agree.
- **D142. No large indices in stage 1.** An index's type obeys the universe bound for
  constructor fields: `Vec: Nat -> Type` is fine, `Ty: Type -> Type` is `E-UNIVERSE`, and
  `Ty: Type -> Type 1` is the form to write (recommended; Lean's rule). This is a
  conservative initial policy; genuinely large indices would be a separate design. (Draft 1 recommended allowing them; the review
  showed that contradicted the field rule, and that Lean doesn't allow them.)
- **D143. Termination and cycles.** A stored constructor field, implicit ones included, is
  a structural subterm of the value, as today. No decrease is ever derived from an index
  equation: after `n := Succ m`, `m` isn't smaller than `n`. A recursive function field is
  classified from the positivity-checked declaration, never from a refined or
  instantiated type. And `n = Succ n` is stuck
  rather than impossible (recommended; test 13 and Agda issue #6654's test 12).
- **D144. Constructor syntax.** Indices after the header's colon; each constructor states
  its result type; unknown lowercase names in a constructor become real implicit fields at
  the front, checked for positivity and universes like written ones, including names used
  only in the result type; uses in the result's indices don't disqualify a name.
  Automatic fields are ordered by their dependencies on each other; one whose type would
  mention a written field is refused (`E-IMPLICIT-FIELD`), asking for an explicit binder
  (recommended). The alternative is placing automatic fields among the written ones.
- **D145. `n + 1` in indices.** Write `Succ n` or `1 + n`, with a targeted hint when `n + 1`
  gets stuck (recommended). Alternatives: make `+` count down its second argument, as
  Lean's does (rewrites many proofs); or a trusted native rule `x + k ≡ Succ^k x`
  (breaks "a native computes exactly its definition").
- **D146. Patterns.** Implicit fields are skipped, or named `VCons [n := k] x xs` (no
  positional form). An arm may be left out only when unification finds a conflict; a
  stuck constructor stays possible (and the case is `E-INDEX-STUCK`). Separately, a
  possible constructor whose branch leaves another argument empty gets a synthesised
  case on that argument with every branch impossible; the one-level search for it is
  intentionally incomplete. `()` works for families.
  An arm that can never match is the warning `W-UNREACHABLE` (recommended).
- **D147. JavaScript.** An export is `E-EXPORT` for now if an indexed family appears
  anywhere in the serialized form of its inputs or result: directly, through synonyms,
  in containers or in record fields (recommended). Boundary codecs that check indices come later.
- **D148. Records and groups.** Records can't have indices. Data groups may give each
  member its own indices, so `Even`/`Odd` can be mutual (recommended).
- **D149. One unifier, checked by a reference.** The elaborator calls the kernel's unifier
  (a public function in `crates/core`) to find impossible branches, and the kernel runs it
  again when checking. A second production implementation would only be more to keep in
  step. But the unifier is trusted, so the tests carry a small reference unifier, simple
  enough to read in one sitting, that tells data constructors (in `Type` and in `Prop`),
  opaque applications and type formers apart. The two are compared on bounded generated
  problems: the outcome (solved, conflict, stuck), and for solved ones the normalised
  effect of the substitutions on the original variables and constraints. Direct kernel
  tests check what the oracle can't, since it has no levels: solutions make the original
  equations convertible, the refined context is well formed, the occurs check sees through
  types transitively, and quoting at branch depth stays in scope (recommended).
- **D153. Built-in `=`.** Keep `Eq` and `J` built in, not redefined as a family. Without
  universe polymorphism, a family would only cover one universe (recommended).
- **D184. Deleting `Prop` equations once D1′ lands.** After D1′ (proof irrelevance)
  is built, add a unifier rule: a constraint whose type is a proposition is deleted, since
  any two proofs of it are then equal. That makes `MkT A 0 = MkT B 1` (§6.3.2) an ordinary
  conflict instead of stuck. Recommended: yes, as part of D1′'s stage, with tests 22-25
  rerun: 22 and 23 still fail, but as `E-NOT-EMPTY` (the equation is deleted, so the
  branch is possible), and 25's empty match is accepted by the later `0 = 1` conflict.
  None of them is ever decided by a conflict between proofs. Not
  before D1′: without it, types that mention the two proofs wouldn't compare equal, and
  the homogeneity invariant would break. The alternative is to leave proof equations stuck
  for good.

## As built

**Stages 1 and 2 (kernel), SW-178.** Built as specified, with these choices
and differences. None changes a rule above.

- **API.** `declare_indexed_data_group(params, sort, [DataDecl { name, span,
  record, indices }])`; `declare_data_group` and `declare_data_group_as` are
  that with no indices. `CtorDecl` gained `result` (empty without indices),
  `Data` gained `indices`, `Ctor` gained `result`, and `Branch.body` is an
  `Option`. The unifier is `unify_index::unify` over a `Scope` (values and
  types by level, extra values to refine, and the rigid matched variable).
- **Hashes (§6.9).** The note expected every data type's hash to change.
  They don't: the index telescope, the result indices and an impossible
  branch are hashed only when present, so a type without indices and a case
  without impossible branches hash exactly as before, and the hash snapshot
  is unchanged. Their layout is still unambiguous: the number of indices is
  hashed before the constructors, which then have exactly that many result
  indices.
- **Test 10.** A kernel constructor's result has no parameters to get
  wrong (§6.1), so "`Weird: Vec Nat 0` in `Vec (a: Type)`" is a surface
  test for stage 3. The kernel test refuses a result index of the wrong type
  (`E-TYPE-MISMATCH`), and the wrong number of result indices
  (`E-MALFORMED`).
- **Test 20** is a kernel test, through a type annotation: the `VCons`
  branch's `(h: P m)` is `E-TYPE-MISMATCH`, whose message shows `h`'s
  refined type quoted at the branch's depth as `P (Succ m)`, and `(h: P
  (Succ m))` is accepted. The lifted-`match` variant is the elaborator's
  (stage 4).
- **Order in `check_case`.** The branch-arity check now comes before the
  `Prop` rule, which needs to unify each branch to know whether all are
  impossible (it does so only for a proposition matched into data). The
  matched variable's substitution (step 3 of §6.3.4) is applied to the
  slots bound before the fields and to the goal: the fields' types and the
  solutions never mention it. For a type without indices this computes
  exactly what it did before.
- **"Types differ" is a guard.** With only the four rules, a binder's
  constraint is formed after the earlier ones are solved, which makes their
  sides convertible, so the left and right types always agree and no test
  reaches `Reason::TypesDiffer`. It stays, as §6.3.1 says, for D184 and
  anything else that might solve a constraint without making its sides
  convertible.
- **Evaluation.** A well-typed value never reaches an impossible branch.
  If an ill-typed term does while checking, the definition stays folded;
  while running (with erasure), it panics with `unreachable`, as §6.8 asks.
- **The reference oracle** (`crates/core/tests/unify_index.rs`) compares
  outcomes and effects on 4,000 generated problems over `Nat`, `Fin`, a `W`
  with a dependent field, `P` and `Hidden` in `Prop`, a `Type` with a proof
  field first, an opaque `g` and type formers. Disabling the `Prop` guard
  fails it; making the occurs check non-transitive doesn't (its generated
  contexts can't express the hidden dependency), which the direct test
  `the_occurs_check_looks_through_types_transitively` catches.
- **Left for stages 3-5:** tests 3, 16, 18, 26 and 28; the surface
  syntax; the elaborator calling `unify_index::unify`; the nested empty
  case search; driver tests with and without erasure (`Certified`); JS
  (impossible branches already compile to `throw`, and the switch's
  fall-through is unchanged).

**Stages 3 and 4 (syntax, declarations, matching), SW-178.** Built as
§7 describes, in `crates/syntax` (`Decl::Data.indices`, `CtorDecl.implicit`
and `.result`, `Pattern::Named`) and `crates/elab/src/families.rs`.
Differences and choices:

- **Automatic implicit fields only for types with indices.** An unknown
  name in a constructor of a type without indices is still
  `E-UNKNOWN-NAME`, as before, rather than an implicit field (which would
  usually be `E-UNIVERSE`, a worse message for a typo). Written `[n: T]`
  fields and result types work for any data type.
- **Ordering automatic fields.** They're tried in the order of first use,
  then every other order (up to four fields); the first that checks wins.
  This is "ordered by their dependencies" without building the dependency
  graph from unsolved metavariables. `E-IMPLICIT-FIELD` is found by trying
  the automatic fields after the written ones.
- **Signatures.** §7.3's `head: Vec a (Succ n) -> a`, `append: … -> Vec a
  (n + m)` and §8.3's `leToLeq: Le m n -> m <= n` need `n`, `m` bound
  automatically, though `Succ n`, `n + m` and `m <= n` are value uses,
  which today's rule refuses. Built: a name used anywhere in an index of a
  family is bound whatever its other uses are, unless it's a name the module
  declares (no `W-MODULE-NAME` either then). The same extension applies in
  constructors (§7.1's "uses in the result type's indices don't count
  against it").
- **Codes.** A record with indices is the new `E-RECORD-INDICES`; a
  constructor of a type with indices without a result type is
  `E-TYPE-MISMATCH`. `W-UNREACHABLE` arms are dropped unchecked, and the
  warning is only given for an arm no other branch reached.
- **Test 22 at the surface** is `()` on `SameP A B`: a stuck constructor
  makes `()` `E-INDEX-STUCK`, as the table says, not `E-NOT-EMPTY`. In the
  one-level search for a missing arm, a stuck column just isn't empty.
- **Test 20's lifted variant** is `keep` in `examples/accept/indexed-families.sw`:
  `same (match v with …)` is lifted to `keep.%match1`, whose captures put
  `n` before `h`, and `h: p n` is refined in the `VCons` branch.
- **Unification in the elaborator** runs on the context with solved
  metavariables substituted (the kernel's conversion doesn't look inside
  them); an unsolved one is never flexible, so a problem mentioning one is
  stuck.
- **`==` isn't derived** for a type with indices yet.
- **Surface tests** 3, 4, 5, 6, 10, 16 and 26 are `examples/reject/index-*.sw`
  and `implicit-field-dependent.sw`; 12, 13, 21 and 22 are also surface
  soundness examples (`examples/soundness/index-*.sw`, `large-index.sw`).
  Left for stage 5: tests 18 and 28 (`E-EXPORT`), driver tests with and
  without erasure (`stitchwort test` already runs the accept example's tests
  with erasure), and JS.

**Stage 5 (running, JavaScript, docs), SW-178.** As specified, with these
notes.

- **`E-EXPORT` (tests 18, 28).** One check in `crates/js`' `boundary`: a
  data type with indices is refused wherever the boundary walk reaches it,
  so directly, through a synonym (the type is evaluated first), inside
  `List` or another container, and in a record's field (the message names
  the field, ``parameter `g`: `Grid`'s field `rows`: `Vec` is an indexed
  family ...``). The message names the family, not the applied type, since a
  field's type can mention earlier fields. `examples/reject/export-indexed-*.sw`
  are the four forms; the accepted counterpart is `examples/extract/vec-inside.sw`,
  whose `-- run:` lines go through the JS differential test, `head`'s
  impossible `VNil` branch included (it generates no case; the fall-through
  `throw` is unchanged).
- **Driver tests** (`crates/driver/tests/indexed_families.rs`): the `Vec`
  functions with and without erasure; `Certified` and a `CVec` with a forced
  field beside a proof field, whose proof costs 9.7 million steps without
  erasure and 389 with it, with every result unchanged; and `fromList`
  counted in evaluation steps rather than seconds: the linear version
  takes 720,385 steps for 8,000 elements and 1,440,385 for 16,000 (2.00x),
  and the quadratic one 3.96x for a doubling (the guard that the
  measurement tells them apart). `erasure.rs` also runs
  `examples/accept/indexed-families.sw` both ways, as it does every accepted
  example. The note's lemma names in `fromListN` are
  `Nat.succInjective`, `Nat.succNotZero` and `Nat.zeroNotSucc`.
- **Docs:** `docs/core.md` (erasure and JS), `docs/syntax.md`, DESIGN.md §6
  (the index clause of `Prop` elimination is deferred, D140), §12 and §13.
- **Left:** SW-179 (`Vec`'s representation), `==` for indexed families, and
  exporting a family with a decoder that checks its indices.

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
- **L3.** *Functional Programming in Lean*, "Indices, Parameters, and Universe Levels":
  <https://lean-lang.org/functional_programming_in_lean/Programming-with-Dependent-Types/Indices___-Parameters___-and-Universe-Levels/>.
  `inductive WithIndex : Type u → Type (u + 1)`, one universe up because the argument is
  an index; a parameter wouldn't raise it. The Lean Language Reference, "Universe
  Levels" (in L1's page): "All other constructor parameters must be smaller than the type
  constructor's universe."
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
- **U1.** J. Cockx, D. Devriese, F. Piessens, "Unifiers as Equivalences: Proof-Relevant
  Unification of Dependently Typed Data", ICFP 2016 (record and abstract):
  <https://researchportal.vub.be/en/publications/unifiers-as-equivalences-proof-relevant-unification-of-dependentl/>.
  §4.3, Lemma 6 (generalised injectivity for indexed constructors when the index telescope
  satisfies K) as cited by the re-review **[unverified: not read in full]**. Journal
  version: "Proof-relevant unification: Dependent pattern matching with only the axioms of
  your type theory", JFP 28 (2018).
