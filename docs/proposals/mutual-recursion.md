# Proposal: forward references and mutual recursion

**Status:** draft 2, 15 October 2026. Revised after an external review of
draft 1; awaiting confirmation before implementation. Not implemented.

This note is meant to be read without knowing the codebase. The first section
describes the parts of Stitchwort it touches; everything said there was
checked against the source as of commit `14649d5`. Claims about other systems
cite their sources ([Sources](#sources)); anything not verified is marked
**unverified**. Where this draft says something was *run*, the probe was a
throwaway test, not committed.

## Contents

0. [Changes since draft 1](#0-changes-since-draft-1)
1. [Background: how things work today](#1-background-how-things-work-today)
2. [The problem](#2-the-problem)
3. [How other systems do it](#3-how-other-systems-do-it)
4. [Options for the surface language](#4-options-for-the-surface-language)
5. [What the kernel sees: admission](#5-what-the-kernel-sees-admission)
6. [Termination for a group of functions](#6-termination-for-a-group-of-functions)
7. [Mutually recursive data types](#7-mutually-recursive-data-types)
8. [Interactions](#8-interactions)
9. [Trusted code](#9-trusted-code)
10. [Staging](#10-staging)
11. [Recommendation](#11-recommendation)
12. [The review's answers, and where this draft stands](#12-the-reviews-answers-and-where-this-draft-stands)
13. [Sources](#sources)

## 0. Changes since draft 1

The review supported option 2 (whole-module scope) with size-change
termination (criterion S) and the conservative data-type restrictions, and
required three revisions before implementation: a kernel check that group
dependencies are closed over finished declarations, a precise policy for
partial applications, and an honest account of `auto` and scheduling. All
three are adopted. In order of the sections they touch:

- **§1** records two facts found while checking the review against the code:
  the raw kernel API today *accepts* the review's split-cycle example and its
  pending-datatype example (both run as throwaway tests). The elaborator never
  makes those calls, so no source program is affected, but it means the
  admission protocol in §5 fixes an existing gap in the kernel, not only a
  future one.
- **§5 is rewritten** around an explicit admission protocol: four declaration
  states (pending, final, opaque assumption, failed), the invariant that
  every dependency of a group is a group member or a *final* declaration, the
  same discipline for data types (an unfinished data type is never treated as
  empty), and the rule that failed groups publish nothing. The review's two
  raw-kernel examples are must-reject tests. Draft 1's "signatures may not
  mention a sibling" becomes a special case of the invariant.
- **§6.3 (new): partial applications.** Recursive occurrences of group
  members must be saturated in the checked core; users write `\x -> g child
  x`. No eta-expansion pass. Measured: no accepted example or prelude
  definition uses a partial or bare self-call today.
- **§6.4 (new): the soundness argument** is restructured into the review's
  three obligations (call coverage, valid size relations, well-founded
  semantics). Function-valued fields are justified semantically, citing Abel
  & Altenkirch with the caveat that it isn't a ready-made proof here. Draft
  1's "every unfolding peels a constructor" is withdrawn (the `countdown`/
  `step` wrapper disproves it) in favour of the infinite-call-path argument,
  and evaluation is separated from normalisation of open terms.
- **§6.5 (new): the graph algorithm is specified**: one graph per call site,
  never merged; composition only of matching functions and dimensions;
  nonempty paths only; unknown entries preserved; the one-incoming-arc
  invariant; witness paths by parent links; exhaustion inconclusive. **§6.6
  (new): its tests**, with an independent finite reference implementation as
  the oracle in place of draft 1's "brute-force search for non-decreasing
  call sequences".
- **§6.7** (was §6.4) corrects the `Prop` wording: only elimination into
  *data* is restricted to subsingletons.
- **§7**: one shared parameter telescope checked once; headers depend only
  on final declarations; immutable group metadata; the `Pred` alias wording
  and the "sibling constructors are induction-induction" overstatement fixed.
- **§8.1**: `auto` uses only candidates already checked, stated as a
  deliberate limitation with the review's counterexample; three-way
  diagnostics; the claim that moving code can't change which proof is found
  is dropped. Module names keep priority over implicit type variables, with
  a two-site diagnostic; the dependency pre-pass is binder-aware. Option 2 is
  described as order-independent *name visibility*.
- **§8.4**: hashing covers every reference form, hashes full declarations and
  group metadata, publishes only final hashes; pure source order is an
  acceptable fallback; collision wording qualified; tests listed.
- **§8.6**: one JS calling convention per definition, used at every site.
- **§10**: three milestones, with draft 1's prerequisite error fixed (stage 2
  promised `Tree`/`Forest` examples before data groups existed).
- **§12**: the review's answers to the nine questions, and the points where
  this draft goes beyond or doesn't follow the review.

## 1. Background: how things work today

Stitchwort is a small, strict, pure, total, dependently typed language
written in Rust. A large elaborator (`crates/elab`) turns surface syntax into
a small core language, and a separate kernel (`crates/core`) re-checks every
declaration from scratch. Only the kernel is trusted. The guarantee the user
cares most about: **a function whose type doesn't mention `Partial` really
terminates, including everything it calls.** (`Partial` itself isn't
implemented yet, so today *every* definition must pass the termination
checker.)

**Declarations are checked strictly in order.** `elaborate_module`
(`crates/elab/src/lib.rs`) walks the file top to bottom. A name is entered in
the name table only when its declaration is reached, so a definition can use
only itself and what came before it. A definition is a signature
(mandatory) immediately followed by its equations.

**The kernel admits a definition in two steps** (`crates/core/src/check.rs`):

1. `declare_def` checks the signature is a type and adds the definition
   *without a body*.
2. `define_def` checks the body against the signature. While it does, the
   definition still has no body, so a recursive reference to it is an opaque
   constant that never unfolds. Then the termination checker runs, and only
   if it passes is the body installed. If anything fails, the definition
   stays bodiless (opaque) for the rest of the file, and the file can't be
   extracted or produce guarantees.

A data type is admitted the same way: `declare_data` (parameters and
universe) adds it with no constructors and `ctors_defined: false`, then
`define_ctors` checks and installs the constructors.

**What the kernel does *not* check today.** The kernel records a
definition's state only as `body: Option<…>` (`crates/core/src/globals.rs`):
`None` means both "not defined yet" and "checking failed". Nothing in
`define_def` or `define_ctors` asks whether the declarations a body or field
refers to are finished, and `define_def` doesn't refuse an `id` that already
has a body (read from the code, not probed). The elaborator never exploits
this: it calls `declare_def` and `define_def` back to back
(`crates/elab/src/lib.rs`, lines 320–321 and 763–778), and `declare_data`
and `define_ctors` with only that type's own fields elaborated in between
(lines 677–713). But through the raw API, two throwaway tests at `14649d5`
showed:

- the review's **split cycle** is accepted: `declare f`, `declare g`,
  `define_def f (\n. g n)` (no self-call, so termination passes), then
  `define_def g (\n. f n)` (no self-call either): both `Ok`, and `f 0` loops;
- the review's **pending data type** is accepted: `declare_data D`, then
  `impossible : D -> Void` defined as `\x. case x of {}` (zero branches
  match zero constructors *so far*), then `define_ctors D [MakeD]`: all
  `Ok`, and `impossible MakeD : Void` type-checks.

This is related to a known issue in `TODO.md`: **"A failed declaration stays
declared without a body, so later declarations in the same module can use
it. Safe only because a module with any error is rejected as a whole."** The
same is true of a data type whose constructors fail to check: it stays
declared with no constructors, so a later `case` on it with zero branches
would check (inferred from the code above, not probed). Today soundness of
these cases rests on the driver rejecting the whole module, not on the
kernel. §5 moves it into the kernel.

Definitions are **case trees**: `case` appears only at the top of a body and
at the top of each branch, always on a variable. The evaluator unfolds a
definition only when it's applied to all its parameters *and* its case tree
can take a step (every case it reaches is on a constructor). That's what
keeps conversion checking from unfolding `length xs` forever when `xs` is
unknown.

**The termination checker** (`crates/core/src/termination.rs`, about 250
lines) is structural recursion on one argument. It walks the body (including
under lambdas, inside types and inside arguments of other calls) and
classifies each argument of each recursive call relative to the
definition's parameters:

- a variable bound as a field of a constructor matched (directly or through
  further matches) out of parameter `i` is *smaller than* parameter `i`;
- a constructor applied to exactly the fields of such a match (`Succ n` in
  the branch where `m` was matched as `Succ n`) is classified as the matched
  value was: smaller if `m` was a descendant, *not* smaller if `m` was the
  parameter itself;
- a *recursive function field* (a field whose declared type is a function
  returning the matched data type, like `rest : res o -> Comp op res a`)
  applied to arguments is smaller;
- anything else, including `J` (transport), lets, other functions and an
  unapplied self-reference, is unknown.

It accepts if **one parameter position `i` is smaller in every recursive
call**. It only records "smaller", never "equal", so it can't express
lexicographic orders: Ackermann's function is rejected today (§6.8, example
4). Only calls to the definition itself are analysed; a call to any other
definition is "anything else". The rules and their soundness argument are
written up in [abilities.md](abilities.md#the-termination-rule); the
must-reject suite (`examples/soundness/`) has the tricky cases (a recursive
call hidden inside an accepted call's argument, a self-reference passed to a
helper, rebuilding a different field, a function that merely returns the
same type as a field).

**Data types** have parameters but no indices (`docs/core.md`). The kernel
declares a data type (parameters and universe) before its constructors, so
constructors can mention it. It then checks each field:

- **Strict positivity**: the type may occur only as itself applied to exactly
  its own parameters, or as the result of a function type whose domains
  don't mention it. *Nested* occurrences such as `List D` are rejected.
- **Universes**: a field in `Type i` needs the data type in `Type j`, `i ≤
  j` (or in `Prop`). Universes are numbered, with no polymorphism or
  cumulativity.
- **No later declarations**: a field may not mention any definition declared
  after the data type, or any data type with a later index. This is a
  positivity guard: something declared later could mention the type and hide
  a negative occurrence behind a definition (`E-POSITIVITY`, "declared
  later").

There are no generated eliminators. Recursion and induction are written as
recursive definitions over case trees, checked by the termination checker.
Matching on a proof (`Prop`) to produce *data* is allowed only for
subsingletons (at most one constructor, all fields proofs); matching on a
proof to produce another proof is unrestricted (`check.rs`, the
`E-PROP-ELIM` check applies only when the result isn't a proposition).

**Content hashes** (`crates/core/src/hash.rs`, BLAKE3) identify every
checked declaration, and test results are cached by them. A reference to
another declaration is hashed as that declaration's hash (computed
recursively, on demand), and a reference to itself as a fixed `self` marker.
The reference forms are `Def(id)`, `Data(d, args)`, `Ctor(d, c, args)` (the
data type's hash plus the constructor index) and `Case(x, d, branches)` (the
data type's hash). `def_hash` returns `None` for a bodiless definition;
`data_hash` of a data type with no constructors yet returns a hash but
doesn't cache it. Definition names aren't hashed; data type and constructor
names are (data types are nominal). DESIGN.md §11 already says that mutually
recursive groups are to be hashed "as a unit, with members referring to each
other by their index within the group", following Unison, but nothing
implements it, because no cycles can occur yet. Today a cycle would make
`def_hash` recurse until the depth guard stops it with `E-RESOURCE`.

**Abilities** (effects) are translated into ordinary data before the kernel
sees them: an effectful function's type is a function into the prelude's
`Comp` tree type, and handlers are folds over `Comp`, checked by the same
positivity and termination rules ([abilities.md](abilities.md)).

**JS extraction** (`crates/js`) emits each reachable definition as `const f =
(v0) => …` in declaration order, which today is also dependency order. A
definition with no runtime parameters whose body is a case tree (like
`absurd`) is emitted as a function of no arguments, a *thunk*, and called as
`f()` wherever it's referenced; that fact is derived twice, once when the
definition is emitted (`Gen::def`) and once at references (`is_thunk`,
`def_ref`). A function's tail calls *to itself* become a loop; other
recursion uses a JS stack frame per call, and running out of stack throws a
clean `StitchwortResourceError`. The boundary codecs no longer recurse
(commit `0ff6af3`). The kernel's own evaluator is a stack-safe machine in
which tail calls add no frames
([stack-safe-evaluation.md](stack-safe-evaluation.md)).

## 2. The problem

None of these can be written today:

```
-- Functions that call each other
even : Nat -> Bool
even 0        = True
even (Succ n) = odd n

odd : Nat -> Bool            -- `odd` isn't in scope in `even`
odd 0        = False
odd (Succ n) = even n
```

```
-- Data types that contain each other: a tree whose nodes hold a forest,
-- and a forest that's a list of trees
type Tree : Type =
  | Node (label : Nat) (kids : Forest)     -- `Forest` isn't declared yet

type Forest : Type =
  | FNil
  | FCons (first : Tree) (rest : Forest)

-- …and functions over them
size : Tree -> Nat
size (Node _ ks) = 1 + sizeForest ks

sizeForest : Forest -> Nat
sizeForest FNil          = 0
sizeForest (FCons t ts)  = size t + sizeForest ts
```

The natural single type `type Rose = Node (label : Nat) (kids : List Rose)`
is a *nested* occurrence and is rejected by positivity, and the mutual
`Tree`/`Forest` encoding that every proof assistant offers as the
alternative needs both mutual data types and mutual functions. Less
dramatically, having to order a file bottom-up (helpers first) is a
nuisance even when nothing is recursive.

So there are three separate features:

- **A. Forward references** without cycles: `main` at the top, helpers
  below. No new soundness question, only elaboration order.
- **B. Mutually recursive functions.** Needs a termination criterion for a
  group, an admission protocol that can't be split (§5), and cycle hashing.
- **C. Mutually recursive data types.** Needs positivity for a group, and
  rules for universes and elimination.

Two related features are **out of scope** (§7.5): *inductive-recursive*
definitions (a data type defined together with a function on it, the
function used in the type's own constructors, as in a Tarski universe
`U`/`El`) and *inductive-inductive* ones (a type defined together with a
family indexed by it, like contexts and types-in-a-context). *Nested*
inductives (`List Rose`) are a later step, not part of this proposal.

## 3. How other systems do it

| System | Functions | Data types | Termination for a group | Notes |
|---|---|---|---|---|
| **Agda** | `mutual` block; or *forward declarations* (all signatures, then definitions; "the span of the mutual block will be automatically inferred"); or `interleaved mutual` [A1] | Split `data D : …` (declaration) from `data D where …` (definition) [A1] | Size-change style: call matrices, completed call graph, "each idempotent call-matrix from a function to itself must have a decreasing argument" (Abel & Altenkirch's foetus plus Lee, Jones & Ben-Amram) [A2, A3] | A signature may mention an earlier member (`f : A; g : B[f]`). Supports induction-recursion and induction-induction [A1]. Positivity analyses how other type formers use their parameters, so `Rose = node (List Rose)` is accepted [A4] |
| **Idris 2** | `mutual` block: "first all of the type declarations are added, then the function bodies"; also forward declarations [I1] | Same `mutual` block | Size-change: matrix entries Smaller / Equal / Unknown [I2] | The tutorial says of totality checking: "Do not rely on it for your proofs yet!" [I3]. Open positivity holes, one specifically with forward declarations [I4] |
| **Lean 4** | `mutual … end`. "The declarations in a mutual block are not in scope in each others' signatures, but they are in scope in each others' bodies" [L1] | `mutual` inductives: "must have the same parameters", "must be in the same universe" [L2]; nested inductives are translated into extra mutual types [L2] | Structural recursion over mutual or nested types since v4.11 [L3]; otherwise well-founded recursion with `termination_by` measures, which must all have the same type across the group [L1] | Well-founded definitions are "irreducible by default" [L1]. Mutual inductive predicates "only eliminate into Prop" (kernel source) [L4] |
| **Rocq** | `Fixpoint … with …`; one decreasing argument per function (`{struct x}`, or tried left to right) [R1] | `Inductive … with …`; "the parameters must be strictly the same for each inductive type" [R1] | Guard condition: every call to a member must pass a syntactically smaller argument in that member's decreasing position [R1] | Induction principles for mutual types come from `Scheme` [R1]. Nested positivity is checked by looking inside the outer type's constructors [R1] |
| **Unison** | Automatic: definitions in a codebase, cycles found by the tool | Same | — (not total) | A cycle hashes as `#x.n`: `x` hashes the cycle, `n` is the member's index, ordered "by sorting all the members of the cycle by their individual hashes (with the cycle removed)" [U1]. Ties are an error, not broken [U2] |
| **Haskell** | Automatic: "a declaration group is a minimal set of mutually dependent bindings", processed "in dependency order"; a type signature cuts the dependency [H1] | Same | — | The model for whole-module, order-independent name visibility |

**Size-change termination** (SCT) [S1]: "a program terminates on all inputs
if every infinite call sequence … would cause an infinite descent in some
data values". Each call is summarised by a small graph saying, for each
parameter of the caller and each argument of the callee, whether the
argument is *strictly smaller* than, *at most* (≤), or of unknown size
relative to the parameter. The graphs are closed under composition (a path of
calls composes into one graph), and the program is accepted if every
composed graph from a function to itself that is *idempotent* (composing it
with itself gives itself) has some parameter strictly decreasing to itself.
Lexicographic orders, permuted arguments and indirect (mutual) calls are
"all handled automatically" [S1]. Deciding it is PSPACE-complete in general
[S1], but the graphs are tiny in practice. Abel & Altenkirch [S2] develop a
*semantic* structural ordering for generalised inductive types (including
infinitely branching ones) and higher-order functions, and prove that terms
accepted by their call-matrix analysis (foetus) normalise; their setting is
simply typed. Wahlstedt [S3] proves normalisation of a dependent type theory
with first-order parameterised data types, given that the call relation is
well-founded, which is what SCT establishes. Hyvernat [S4] refines SCT for
constructor-based languages. None of these is a ready-made proof for
Stitchwort's core (§6.4).

**Soundness bugs worth learning from:**

- **Rocq #21682** (2026, CVE-2026-72703 [R3]): a proof of `False` because a
  guard-condition helper "only inspects SELF-recursive calls … completely
  ignores CROSS-calls between different bodies" of a mutual fixpoint [R2].
  *Lesson:* every call between any two members must be in the analysis, and
  any per-function shortcut must be justified for the group.
- **Agda #8699** (fixed 2026): the termination checker descended into
  irrelevant / `Prop` constructor arguments, giving `⊥` under `--safe` [A5].
  *Lesson:* the structural order must only use sub-parts that really exist in
  the values the evaluator computes with, and must agree with conversion.
- **Agda #7751** (fixed 2025): a mutually defined non-positive type hidden
  behind a module application [A5]; **Idris 2 #1988** (open): a negative
  occurrence hidden behind an equality [I4]. *Lesson:* positivity must see
  every occurrence, including through anything that could unfold to one.
- **Idris 2 #1771** (open): `data Fix f = MkFix (f (Fix f))` with `f x = x ->
  x` loops under `%default total`, because nested occurrences were allowed
  without checking how the outer type uses its parameter [I4]. *Lesson:*
  nested inductives need a real variance analysis; until then reject them,
  as Stitchwort does.
- **Agda #6059** (fixed): a non-terminating function accepted because the
  call-matrix code silently dropped elements [A5]. *Lesson:* the
  matrix/graph code is trusted and needs its own tests.
- **Rocq, 2014**: the guard condition was inconsistent with propositional
  extensionality, because "the subterm relation used by the guard checker
  … [was] not defined quite the right way on dependent pattern matching"
  [R4] (quoted from a search summary; the original page refused the fetch).
  Stitchwort's analogue would be treating the result of transport (`J`) as
  a sub-part; it doesn't (§1), and this proposal keeps it that way.
- **Agda, 2013**: termination was checked only after type-checking a whole
  mutual block, during which unchecked clauses could unfold, so a
  non-terminating definition could make the type checker loop [A6]. Not a
  soundness bug, but a design choice this proposal avoids (§5).

## 4. Options for the surface language

### Option 1: an explicit `mutual` block

```
mutual
  even : Nat -> Bool
  even 0        = True
  even (Succ n) = odd n

  odd : Nat -> Bool
  odd 0        = False
  odd (Succ n) = even n
```

This is Lean, Idris and (in old style) Agda. It fits the current layout rule
(a declaration at column 0, continued by indented lines). Inside the block
the names are all visible; outside it, order still matters.

- **For:** small elaborator change; the group the user writes is the group
  the kernel checks; an accidental cycle is impossible outside a block;
  no change to the meaning of existing files.
- **Against:** doesn't give plain forward references (feature A); users
  must know to write `mutual`, and the error for forgetting it is "unknown
  name", which doesn't say what to do (it can, with a hint).

### Option 2: order-independent name visibility, with automatic grouping

Every top-level name is visible everywhere in the module. The elaborator
builds a dependency graph from the source, splits it into **strongly
connected components** (SCCs: maximal sets of declarations that all reach
each other), and checks them in dependency order. Each SCC of size > 1, or
a declaration referring to itself, is a recursive group. This is Haskell's
rule [H1] and, in effect, Unison's.

What becomes order-independent is **which names a declaration can refer
to explicitly**. Not every elaboration behaviour becomes order-independent:
implicit decision-procedure search (`auto`) still depends on what has been
checked at the point of use (§8.1), and adding a top-level definition can
change the meaning of an implicitly bound type variable elsewhere (§8.1).

- **For:** gives features A, B and C with no new syntax; the most natural
  for a non-expert ("write things in any order"); every definition already
  has a mandatory signature, so — unlike Haskell — no type *inference*
  crosses definitions, and grouping affects only checking order,
  termination and hashing.
- **Against:** a bigger elaborator change (a pre-pass to resolve names; see
  §8.1 for things whose meaning depends on order today); an accidental
  cycle shows up as a termination error rather than "unknown name", so the
  message must show the cycle; error recovery is per group, so one bad
  member makes the whole group fail.

### Option 3: Agda-style forward declarations

Allow a signature on its own, with its equations later (`odd : Nat -> Bool`
near the top, `odd 0 = …` further down). Groups are inferred from where
signatures and definitions sit. This is the most flexible but the hardest to
explain, and conflicts with today's rule that equations immediately follow
their signature (`E-MISSING-DEFINITION`). Not recommended.

### The kernel doesn't care, and doesn't trust

Whichever option is chosen, the kernel receives **explicit groups** and
trusts nothing about how they were found. That claim needs a check draft 1
didn't state: the kernel must refuse a group that depends on an unfinished
declaration outside it (§5.2), otherwise a cycle can be split across two
"groups" that each look non-recursive. With that check, a group bigger than
necessary is still checked soundly (calls between members that don't form a
cycle produce no loops in the termination analysis); it just recovers from
errors less precisely and invalidates caches more widely (§8.4). A group
*smaller* than necessary is refused.

## 5. What the kernel sees: admission

### 5.1 Declaration states

Every global declaration (definition or data type) is in exactly one of four
states, recorded explicitly in place of today's `body: Option<…>` /
`ctors_defined: bool`:

| State | Meaning | Unfolds / has constructors? | Can be depended on by a final declaration? | Hash, cache, extraction |
|---|---|---|---|---|
| **Pending** | Declared (signature, or parameters and universe, checked); its body or constructors may still arrive, but only as part of one group admission | No | Only from inside the group that finishes it | None |
| **Final** | Admitted with everything it depends on (§5.2) | Definitions: yes, by the case-tree rule. Data: constructors available | Yes | Yes |
| **Opaque assumption** | A permanently bodiless declaration that the kernel tracks as an assumption (a future `postulate`, say). **Nothing creates one today**; the state is reserved so it can never be confused with pending | Never | Yes, and every guarantee for a dependent names it as an assumption | Yes |
| **Failed** | Its group was submitted and refused, or it depends on a failed declaration. Kept only so the elaborator can keep going and report more errors | No | No | None |

Transitions are one-way: pending → final (by a successful group admission),
pending → failed. A final declaration's content and state never change.
**In particular, nothing changes from opaque to executable without its
dependents being re-checked**: the only declarations that ever gain a body
are pending ones, and §5.2 ensures nothing outside their group has been
admitted on the assumption that they're opaque.

The transitions are driven only by the kernel's own admission functions;
the elaborator can't set a state.

### 5.2 The admission invariant

> **Every dependency of a submitted group is either a member of that group
> or a final declaration.** A pending or failed declaration outside the
> group is never treated as an assumption-free dependency.

"Dependency" means every reference anywhere in what the group submits:
signatures, annotations, types inside bodies, proof terms, bodies,
constructor fields, data parameters, and export validators. The reference
forms are those the hasher already enumerates: `Def`, `Data`, `Ctor` and
`Case` (§1). Implicit dependencies count too: a `Nat` literal depends on the
builtin `Nat` type, and natives on the prelude definitions they accelerate;
these must be final when registered (they are, since the prelude is checked
first, but the registration functions should check it rather than assume it
— whether they do today is **unverified**).

The check is a walk over the submitted terms looking at each reference's
state; it doesn't need to follow references further, because **closure is
transitive by induction on admission order**: each final declaration was
itself admitted under this invariant, so everything it reaches is final.
That's what makes the guarantee "a final definition terminates, together
with everything it can reach" hold for the whole reachable set, not just the
group's own calls.

What it rules out:

- **The split cycle** (the review's example; accepted by today's raw
  kernel, §1):

  ```
  declare f : Nat -> Nat
  declare g : Nat -> Nat
  define_group [f] with  f n = g n     -- refused: `g` is pending and not in the group
  define_group [g] with  g n = f n
  ```

  The first admission is refused (`E-MALFORMED`: "refers to `g`, which isn't
  finished and isn't in this group"; no correct elaborator produces it).
  Submitted as one group, `[f, g]` is checked properly and rejected by the
  termination check (§6.8 example 10).
- **Depending on a failed declaration.** A group referring to a failed
  declaration may still be checked, so the user sees its own errors, but its
  result is *failed*, never final, whatever happens. This replaces the
  driver-level "a module with any error is rejected as a whole" (the
  `TODO.md` known issue, §1) with a kernel-level fact; the driver rule stays
  as a second line of defence.
- **Re-defining a final declaration.** Every member of a submitted group
  must be pending. (Today `define_def` doesn't check this; read from the
  code.)

Draft 1's `E-MUTUAL-SIGNATURE` rule ("a member's signature may not mention a
sibling") becomes a special case: signatures are checked when the members are
declared, at which point every sibling is pending, so **a signature may
refer only to final declarations**. The error code can stay, for a clearer
message when the elaborator gets it wrong.

### 5.3 Function groups

`define_group(members, bodies)` replaces `define_def` (a single definition is
a group of one):

1. **Members are pending.** Each was added by `declare_def`, whose signature
   referred only to final declarations (§5.2). Lean has the same "not in each
   other's signatures" rule [L1]; Agda allows it [A1]. Allowing it would let
   a type depend on how an unchecked sibling computes — a step towards
   induction-recursion for functions — and gains little.
2. **Dependency check** (§5.2) on every body.
3. **Saturation check** (§6.3): every occurrence of a member in a body is
   applied to at least that member's arity, where a member's arity is the
   number of leading lambdas of its submitted body. All bodies are submitted
   together, so every arity is known before any body is checked.
4. **Check every body** against its signature, **with every member
   opaque**. `even 2` doesn't compute while `odd` is being checked. This is
   today's rule for a single recursive definition, extended to the group. It
   means the type checker can never unfold an unchecked definition, so it
   can't loop on one (the Agda 2013 problem, [A6]).
5. **Termination check on the whole group** (§6).
6. **Finalise atomically**: install every body, set every member final. If
   any step fails for any member, *no* body is installed and every member
   becomes failed. Nothing computed while checking (hashes, cached test
   results) is published (§5.6).

The cost of step 4: a body whose *type-checking* needs a sibling to compute
fails. In practice that's a proof about `even` written in the same group as
`even`, which belongs in a later declaration anyway (§6.8 example 9). Lean
does the same, as far as can be told: its reference only says the elaborator
builds a "pre-definition in which recursion is still present" (**not
verified** in more detail).

Theorems (`theorem` definitions) can be group members: a proof by mutual
induction is a group of mutually recursive theorems, checked by the same
termination rule (§6.8 example 8). There are no generated induction
principles to worry about (Rocq needs `Scheme` for these [R1]).

### 5.4 Data-type groups

1. **Declare the group** with one call, `declare_data_group(params, sort,
   names)`: the shared parameter telescope is checked **once**, in one
   properly scoped context, and every member gets that telescope by
   construction (§7.3). The parameters may refer only to final declarations;
   they can't refer to members, which don't exist yet. Each member's group
   identity (the group and its index in it) is fixed here, as immutable
   kernel metadata (§7.3). Members are pending.
2. **Define all constructors** of all members in one call, with positivity
   checked against the whole group (§7.1), the dependency check (§5.2: a
   field may refer to final declarations and to the *types* of group
   members), and no references to any member's *constructors* or `case` on
   a member (§7.2).
3. **Finalise atomically.** Constructor availability, exhaustiveness and
   matching all read the *final* state, not a separate flag: until then, a
   member has no constructors to build, isn't a valid `case` target (so no
   case — not even an empty one — can be checked against it), and has no
   hash. "Mark them all defined at once" governs all of these, not just a
   status flag.

**An unfinished data type is never treated as an empty one.** The review's
example is a must-reject raw-kernel test (accepted today, §1):

```
declare_data D : Type                       -- pending, no constructors yet
declare impossible : D -> Void
define_group [impossible] with
  impossible x = case x of {}                -- refused: `D` is pending
define_ctors D [MakeD : D]
-- had it been accepted: `impossible MakeD : Void`
```

The refusal comes from §5.2 (the body refers to pending `D`), and, as a
second line, from the `case` rule (a pending data type isn't a `case`
target). Its accepted neighbour defines `impossible` after `D` is final, and
is rejected as non-exhaustive (`E-NONEXHAUSTIVE`).

**Mixed groups** — data types and definitions in one cycle — are rejected
(`E-MUTUAL-KIND`, say). Such a cycle is either induction-recursion (a
constructor mentions a function on the type being defined) or a function
that the data type's fields depend on; both are out of scope (§7.5). The
invariant already rules them out: a field can't refer to a pending
definition, and a definition can't refer to a pending data type.

### 5.5 Must-reject raw-kernel tests

Built directly on core terms (`crates/core/tests/kernel.rs` style), each with
the expected error code, and each paired with an accepted neighbour:

1. The split cycle, `define_group [f]` then `[g]` (§5.2). Neighbour: `[f, g]`
   with a decreasing call, accepted.
2. The pending data type `impossible : D -> Void` (§5.4).
3. A group that refers to a *failed* declaration: checked, result failed, no
   hash, not usable by a later final declaration.
4. Re-defining a final definition: refused.
5. A group whose member isn't pending (declared in another group, or
   final): refused.
6. A signature referring to a pending declaration: refused.
7. A constructor field referring to a pending definition, or to a sibling's
   constructor: refused.
8. A data group whose shared parameters refer to a member: impossible to
   express with `declare_data_group`, so no test; instead a test that a
   member can't be added to an existing group after declaration.
9. Incorrect partitions of a correct program: a cycle `f → g → h → f`
   submitted as `[f, g]` then `[h]`, or as `[f]` then `[g, h]`: refused.
   Neighbour: `[f, g, h]`, accepted.
10. Budget exhaustion during a group's termination check (§6.5): the
    members end up failed, not final; no hash.

Tests 1 and 2 fail today (§1). Writing them first makes milestone 1 (§10)
start from a red test.

### 5.6 Failed groups publish nothing

A failed group, and anything depending on it, may stay visible to the
elaborator for error recovery (so `E-UNKNOWN-NAME` doesn't cascade), but:

- no hash is computed or stored for it (`def_hash` / `data_hash` refuse
  anything not final; today `data_hash` of a pending data type returns an
  uncached hash, which must stop);
- no test result is cached under any key derived from it;
- it can't be extracted to JS;
- no "checked" result for the module is reported.

## 6. Termination for a group of functions

### 6.1 What to extend, and the two candidate criteria

Today's walker classifies each argument of each self-call as "smaller than
parameter `i`" or unknown, and needs one position that is smaller in every
call. For a group it must look at every call from any member to any member
(Rocq #21682 is what happens otherwise [R2]). Two criteria are possible:

**Criterion R (Rocq-style, "every call decreases").** Choose one decreasing
parameter `d(f)` for each member `f`. Every call from `f` to `g` must pass,
at position `d(g)`, something strictly smaller than `f`'s parameter `d(f)`.
The kernel searches for a choice of `d` (there are at most ∏ arity(f)
choices; small groups only, with a budget). This is the smallest change to
today's code.

**Criterion S (size-change).** For each call, build a size-change graph:
for each argument position `j` of the callee, an arc from caller parameter
`i` labelled `<` (the argument is a strict sub-part of parameter `i`) or `≤`
(it *is* parameter `i`, or rebuilds it). Close the set of graphs under
composition; accept if every idempotent graph from a member to itself has a
`<` arc from some parameter to itself [S1, A2].

S accepts strictly more than R, including things today's checker rejects
for a single function:

| Program | Today | R | S |
|---|---|---|---|
| `even`/`odd` | (can't write) | yes | yes |
| `size`/`sizeForest` | (can't write) | yes | yes |
| A wrapper that calls a sibling with the same argument (`countdown n = step n`, `step (Succ n) = countdown n`) | (can't write) | **no**: `countdown`'s call doesn't decrease | yes |
| Ackermann (lexicographic) | no | no | yes |
| Swapped arguments `f (Succ x) y = f y x` | no | no | yes |

**Recommendation: S**, as the review agreed. It's what Agda and Idris use
[A2, I2], and it handles the patterns people actually write (wrappers,
helpers with an accumulator, lexicographic recursion) without annotations.
Everything R accepts, S accepts.

### 6.2 Classifying arguments (extending `termination.rs`)

Each argument of a call to a group member is classified relative to the
*caller's* parameters, exactly as today, plus one new relation:

| Argument | Relation to caller parameter `i` | New? |
|---|---|---|
| Parameter `i` itself | `≤` | **new** (today: unknown) |
| The constructor of a recorded match of parameter `i`, rebuilt exactly (§ below) | `≤` | **new** (today: unknown) |
| A field of a match on parameter `i` or on a descendant | `<` | as today |
| The constructor of a recorded match of a *descendant* of `i`, rebuilt exactly | `<` | as today |
| A recursive function field of such a match, applied (`rest y`) | `<` | as today, but "recursive" now means *returns any type in the matched type's data group* (§7) |
| Anything else (other functions, `J`, lambda-bound variables, lets) | none (unknown) | as today |

**Reconstruction is `≤` only when it is the same value.** In the branch
where `m` was matched as `Succ n`, the term `Succ n` *is* `m`: inside that
branch the kernel has substituted the constructor value for `m` everywhere
(`check.rs`, `check_case`), so this is equality, not "similar size". The
implementation must stay tied exactly to the recorded match: the same data
type, the same constructor, the same parameters, and exactly the field
variables that match bound, in order. Rebuilding a known descendant keeps
`<`; rebuilding the original parameter gives only `≤`. Nothing broader:
not a value provably equal to `m`, not the result of transport, not a
different constructor of the same size (`soundness/` already has "rebuilding
a different field").

Unchanged rules that matter for soundness:

- **Every occurrence is a call.** Calls inside arguments of other calls,
  under lambdas and inside types are all collected (`soundness/
  hidden-recursive-call.sw`).
- **Relations come from terms, never from refined types**, and `case` is
  only on parameters or fields of earlier matches (the "fresh-wrapper
  invariant", [abilities.md](abilities.md#the-termination-rule)).
- **`J` never yields a sub-part** (the Rocq 2014 lesson, [R4]).
- **A variable is related to at most one parameter** (it was matched out of
  exactly one), so each extracted graph has at most one arc into each callee
  position. This is a representation invariant, tested (§6.6), not assumed.

### 6.3 Partial applications: saturated recursive occurrences

**Policy.** In the checked core, every occurrence of a group member inside
the group's bodies must be the head of an application with at least as many
arguments as the member's arity (its submitted body's leading lambdas,
counting implicit ones). Otherwise the group is refused, with an error that
says what to write:

```
[E-TERMINATION] `g` is used here without all its arguments
  f (Node l k) = mapForest (g k) xs
                            ^^^^^ `g` takes 2 arguments; it's given 1
  = write `\x -> g k x` so the call can be checked
```

There is **no automatic eta-expansion pass**, as the review advised: an
automatic transformation has to keep the supplied arguments' evaluation
behaviour (a strict language evaluates `g (expensive y)` once; `\x -> g
(expensive y) x` evaluates it on every call) and must neither lose nor
invent structural provenance by introducing aliases. The elaborator may
*suggest* the eta-expanded form in the message; it doesn't apply it. Calls
from *outside* the group (a later definition passing `even` to `filter`) are
unaffected: the group is final by then.

**Why this policy rather than closure-aware partial applications.** The
review offered two options: keep partial applications with call-dependency
edges that track the originating invocation and captured arguments, or
require saturation. Saturation is recommended because:

- *It makes call extraction exact.* With `\x -> g child x`, the whole call
  `g child x` is a syntactic call site inside `f`'s body. Its graph relates
  `child` to `f`'s parameters, and `x` (lambda-bound) to nothing. That is
  precisely the "originating invocation and captured argument" relation the
  review asks for, recorded by the existing walker with no new concept.
- *It costs nothing today.* A throwaway probe in `termination.rs` reported
  every under-applied or bare self-reference while the CLI example suite ran
  (`cargo test --release -p stitchwort-cli --test examples`, which loads the
  prelude and checks every file in `examples/`): there were **no
  under-applied self-calls**, and the only bare self-references were in two
  must-reject files, `soundness/higher-order-recursion.sw` (`viaHelper`) and
  `soundness/cell-result.sw` (`CellRes`). Both would still be rejected, now
  by the saturation rule (their snapshots' error text would change).
- *It is easy to relax later*, by adopting the closure-aware model, without
  breaking anything accepted now.

It doesn't remove the need for the higher-order argument of §6.4: a
saturated call under a lambda still runs whenever, and however often, the
lambda is called. It makes the *extraction* of calls simple enough to check
by reading.

**Tests** (each must-reject paired with an accepted neighbour):

1. *A callback invoked repeatedly*: `f (Node l k) = applyTwice (\x -> g k x)
   l`, where `applyTwice` is a final helper. Accepted when `g`'s call on `k`
   decreases; the neighbour passing `\x -> g (Node l k) x` is rejected.
2. *A callback retained after its creator returns*: `f` returns a record (or
   a `Comp` continuation) containing `\x -> g k x`, and a later, final
   definition calls it. Accepted when it decreases; rejected when it rebuilds
   the parameter.
3. *The omitted argument was the only decreasing position*: `g : Nat -> Tree
   -> Nat`, in a cycle with `f`, decreasing only on its second argument, and
   `f t = h (g 0)`. Rejected by saturation; the eta-expanded `f t = h (\x ->
   g 0 x)` is also rejected, by termination (`x` is lambda-bound, so no arc
   into position 1). The accepted neighbour omits the *other* argument:
   `f (Node _ k) = h (\n -> g n k)`, where `k` is smaller.
4. *A bare member reference* (the mutual version of
   `soundness/higher-order-recursion.sw`; §6.8 example 12): rejected by
   saturation.
5. *An alias between members*, `f = g` with `g` a member of arity 1:
   rejected by saturation; `f n = g n` is the accepted neighbour.
6. *Effectful continuations*: the `ping`/`pong` example (§6.8 example 7),
   whose calls are saturated inside `bind` continuations, stays accepted.

### 6.4 Why the check is enough: three obligations

The review's central distinction: "the SCT algorithm accepts these graphs"
is a theorem about graphs; "these graphs faithfully justify every recursive
use the kernel admits" is a claim about Stitchwort. Draft 1 ran the two
together. The argument has three parts, each of which Stitchwort must
establish separately:

| Obligation | What must hold | Where it's established |
|---|---|---|
| **Call coverage** | Every potentially recursive use of a group member is a recorded call site: under lambdas, inside arguments, inside types, through continuations. | The walker visits every subterm (§6.2); saturation (§6.3) means there are no partially applied uses to account for; admission (§5.2) means no use reaches a member through an unfinished declaration outside the group. |
| **Valid size relations** | Every recorded `<` or `≤` is true of the values involved, under every substitution the core can make (branch refinement, conversion, instantiation of parameters). | Relations come from the recorded matches (provenance), never from types or equalities (§6.2). A field of a match is a field of that value whatever is substituted for other variables, so the relations are stable under substitution. Reconstruction is tied to the exact match. |
| **Well-founded semantics** | The relations can't descend forever through well-typed values. | The semantic argument below, which is not yet a proof. |

**The well-founded semantics, in outline.** This is a sketch of the
standard route, for the reviewer to check, not a proof:

1. Every value of a data type is built by finitely or infinitely branching
   but *well-founded* generation: a value is constructed from components
   that are themselves values constructed earlier in the inductive
   definition. For a function-valued field such as `kids : Nat -> Forest`,
   the intended relation is "`kids n` is below the enclosing `Tree`, for
   every admissible `n`". That is a statement about the **semantic
   inductive structure** — the order in which the strictly positive
   definition generates values — not about the Rust heap: `kids` is a
   closure, and calling it can build a fresh `Forest` that was never
   allocated inside the `Tree`. The order is ranked by (possibly infinite)
   ordinals rather than by any count of nodes. Abel & Altenkirch develop
   exactly this kind of semantic structural ordering for generalised
   inductive types and higher-order functions [S2]; their setting is simply
   typed and their analysis isn't Stitchwort's, so it is a guide to the
   shape of the proof, not a ready-made one.
2. The argument must not *assume* that functions stored in data are total
   while establishing termination. The usual way out is a reducibility
   (logical-relations) argument: define "good" values by induction on types,
   where a good function maps good arguments to terminating, good results,
   and a good data value has good fields. Then prove, by well-founded
   induction, that every call of a group member on good arguments
   terminates with a good result.
3. The induction is over the **static call relation**: the pair
   (member `f`, its arguments) is related to (member `g`, arguments `w`) if
   `f`'s body, on those arguments, contains a call site to `g` that would
   receive `w` — for *some* values of any lambda-bound variables in scope
   at the site. SCT, by the size-change theorem [S1], is what shows this
   relation has no infinite chains: an infinite chain would be an infinite
   path through call sites, and every idempotent loop has a strict
   self-arc, so some parameter would descend infinitely often in the order
   of step 1, which is impossible.
4. Because the induction is over call sites, not over the runtime stack,
   **delayed calls are covered**: a closure `\x -> g k x` created by one
   invocation of `f` and called much later, or many times, by a final
   helper is a call `g k x` whose relation to *that invocation of `f`* is
   the recorded one. The closure is good because, for every good `x`, the
   call is below the current one in the induction. Outside code applied to
   good functions is good because it was itself admitted (and §5.2 makes
   sure it was admitted without assuming anything about this group). Draft
   1's "outside code terminates, so a divergent run must make infinitely
   many nested group calls" took the goodness of the group's closures for
   granted; this is the version the review asked for.

Wahlstedt's thesis [S3] does steps 2–3 for a dependent type theory with
first-order parameterised data. **Infinitely branching data (function
fields, as in `Comp`) is not covered by [S3]**, and [S2] covers it only for
a simply typed language: this is the remaining gap, the same one
[abilities.md](abilities.md#the-termination-rule) already records for the
single-function rule.

**Evaluation versus normalisation.** Two different things must terminate:

- *Evaluation* of a closed term to a value (running a program, `auto`
  running a decision procedure at compile time). Steps 1–4 are about this.
- *Normalisation under binders*, used by conversion checking: terms with
  free variables (neutral values), evaluated under lambdas and in refined
  branch contexts. The argument must also cover open terms and the
  substitutions the core makes. The standard route extends the same
  reducibility argument with "neutral terms are good" (as in
  normalisation-by-evaluation proofs); this has **not** been worked out for
  Stitchwort.

**What draft 1 said, corrected.** Draft 1 claimed conversion terminates
because "a definition unfolds only when its case tree can take a step, so
each unfolding along a cycle peels a real constructor off a value". That is
false for the wrapper example the proposal itself accepts:

```
countdown n = step n
```

Unfolding `countdown x` (no `case`, so it unfolds even on an unknown `x`)
exposes `step x` without peeling anything; the decrease happens elsewhere in
the cycle. The correct statement: an infinite chain of relevant unfoldings
would induce an infinite path through call sites, and the checked size-change
relations would force an impossible infinite descent. The case-tree blocking
rule is still useful — it stops a constructor-inspecting definition from
unfolding on an unknown argument, so `step x` stays stuck — but it is not an
independent proof of normalisation once non-decreasing wrapper edges are
allowed.

**Trusted reasoning.** Draft 1 called the closure algorithm "the one
genuinely new piece of trusted reasoning". That understated it: extending
call extraction and structural provenance across a group (calls to *any*
member; "recursive function field" meaning any type in the data group;
saturation) is trusted reasoning too, even though it reuses existing code.
§9 lists it.

### 6.5 The graph algorithm

Representation and rules, fixed before coding:

- **A graph** is `(from: member, to: member, arcs)`, where `arcs` has one
  entry per parameter position of `to` (its arity), each entry either
  *unknown* or `(position of from, label)` with label `<` or `≤`. This
  encodes the one-incoming-arc invariant (§6.2) in the type. Graphs between
  members of different arities are not square; nothing assumes they are.
- **One graph per call site.** Distinct call sites — including the
  alternatives in different branches of a `case` — give distinct graphs,
  **never merged**. One branch decreasing argument 0 and another decreasing
  argument 1 doesn't mean either decreases both; merging their arcs into one
  optimistic graph would accept the alternating-growth program (§6.8
  example 11).
- **Extraction once per spine, visiting every argument.** For an
  application whose head is a member, record one graph for the whole spine,
  then walk every argument (they may contain calls), but don't walk the head
  again: recording the head as a bare reference too would add a spurious
  empty graph. Today's walker already does this for self-calls.
- **Unknown stays unknown.** A missing argument or missing relation is
  never turned into `≤` by a default value, truncation or indexing past the
  end. Saturation (§6.3) means every callee position has an argument; an
  argument with no relation is *unknown*.
- **Composition** `G₁ ; G₂` is defined only when `G₁.to == G₂.from` (and so
  the dimensions match); it has `from = G₁.from`, `to = G₂.to`, and for each
  position `k` of `G₂.to`: if `G₂` maps `k` to `(j, l₂)` and `G₁` maps `j` to
  `(i, l₁)`, then `(i, l)` with `l = <` if either label is `<`, else `≤`;
  otherwise unknown. Composition preserves the one-incoming-arc invariant.
- **Closure over nonempty paths only.** Start from the call-site graphs;
  repeatedly compose a graph in the set with a call-site graph on the right,
  adding new results, until nothing new appears. Never add identity graphs
  (zero-length paths): an identity graph is idempotent with no strict arc,
  so it would reject every recursive function, harmless or not.
- **The check.** For every graph `G` in the closure with `G.from == G.to`
  and `G ; G == G`, require some `k` with `arcs[k] == (k, <)`. Otherwise
  reject.
- **Size.** Between members of arities `m` and `n` there are at most
  `(2m + 1)^n` distinct graphs (draft 1's `3^(m·n)` was for unrestricted
  arcs), and the closure is a set, so it terminates.
- **Budget.** Each composition is counted against the operation's resource
  budget. Exhaustion is `E-RESOURCE`, "inconclusive": the group fails as a
  whole (§5.3 step 6). Nothing is partially accepted.
- **Witnesses.** For the error message, each graph in the closure stores a
  parent link — the graph it was composed from and the call site added —
  not a copied path. The path for a rejected graph is rebuilt by following
  links. Copying paths can use a lot of memory before the budget's graph
  limit is reached.

### 6.6 Testing the algorithm independently

Agda #6059 [A5] (call matrices silently dropping elements) is why the graph
code needs its own tests, separate from the example programs:

- **An independent reference implementation** as the oracle, in the test
  code: graphs as explicit sets of arcs `(i, j, label)`, allowing *any*
  number of arcs per position (so it doesn't share the production
  representation's invariant), composed by the textbook definition, and
  saturated until no new graph appears. It is compared with production on:
  - **all** call-graph sets up to a small size (say two members of arity
    ≤ 2 and up to three call sites, exhaustively);
  - random sets somewhat larger (three members, arity ≤ 3, up to six call
    sites).

  This replaces draft 1's "brute-force search for non-decreasing call
  sequences": running small inputs, or searching paths up to some length,
  can't establish that an SCT decision is right.
- **Properties:** composition is associative where defined; the verdict is
  invariant under renaming members and under permuting argument positions
  consistently; it is *conservative under weakening* (turning a `<` into
  `≤`, or removing an arc, or adding a call site, never turns a rejection
  into an acceptance); extraction and composition preserve the
  one-incoming-arc invariant.
- **Unit cases:** composition of non-square graphs (arities 1, 2 and 3 in
  one chain); a graph with every entry unknown; the identity is *not* in the
  closure of a group with no calls.
- **Known programs:** every example in §6.8, both directions.

### 6.7 Arguments that are types or proofs

Implicit parameters (types, proofs) are parameter positions like any other.
A type can never be strictly smaller (there's no `case` on types), so it can
only carry `≤` arcs, which are harmless. A proof can be matched. Matching a
proof to produce *another proof* is allowed for any proposition; matching a
proof to produce *data* is restricted to subsingletons (`E-PROP-ELIM`, §1).
Either way, the fields of a matched proof are genuine sub-parts of a value
the kernel's evaluator really computes with: Stitchwort has no definitional
proof irrelevance, which is what went wrong in Agda #8699 [A5]. So
proof-to-proof recursion over the permitted constructors is handled by the
same rules. **If proof irrelevance is ever added, recursion on proofs must be
revisited.**

### 6.8 Worked examples

Must be **accepted**:

1. `even`/`odd` (§2). Graphs: `even → odd: 0 <→ 0`, `odd → even: 0 <→ 0`.
   Every loop composes to `0 <→ 0`.
2. `size`/`sizeForest` (§2): every call is on a field. (Needs data groups;
   milestone 3.)
3. A wrapper that doesn't decrease, with a helper that does:

   ```
   countdown : Nat -> Nat
   countdown n = step n           -- 0 ≤→ 0

   step : Nat -> Nat
   step 0        = 0
   step (Succ n) = countdown n    -- 0 <→ 0
   ```

   The only loop composes to `<`. (Rejected by criterion R.)
4. Ackermann, a single function that today's checker rejects (checked with
   a release build of the CLI for draft 1: `E-TERMINATION` on `ack m 1`):

   ```
   ack : Nat -> Nat -> Nat
   ack Zero     n        = Succ n
   ack (Succ m) Zero     = ack m 1                 -- {0 <→ 0}
   ack (Succ m) (Succ n) = ack m (ack (Succ m) n)  -- outer {0 <→ 0}; inner {0 ≤→ 0, 1 <→ 1}
   ```

   Every idempotent graph has `0 <→ 0` or `1 <→ 1`.
5. Swapped arguments (today: rejected, checked the same way):

   ```
   f : Nat -> Nat -> Nat
   f Zero     y = y
   f (Succ x) y = f y x           -- {0 <→ 1, 1 ≤→ 0}
   ```

   The graph isn't idempotent; composed with itself it is `{0 <→ 0, 1 <→ 1}`,
   which is idempotent and decreasing. (It terminates: two steps shrink both
   numbers.)
6. A recursive function field returning a *sibling* type (milestone 3):

   ```
   type Tree : Type =
     | Node (label : Nat) (kids : Nat -> Forest)

   type Forest : Type =
     | FNil
     | FCons (first : Tree) (rest : Forest)

   firstLabel : Tree -> Nat
   firstLabel (Node l kids) = l + forestHead (kids 0)    -- `kids 0` <
   forestHead : Forest -> Nat
   forestHead FNil        = 0
   forestHead (FCons t _) = firstLabel t
   ```
7. Effectful mutual recursion. The recursive call sits in a continuation
   after translation to `Comp` (`bind (get ()) (\s -> …)`), i.e. under a
   lambda, where calls are already collected; the call is saturated:

   ```
   ping : Nat -> {State Nat} ()
   ping 0        = ()
   ping (Succ n) =
     put (get () + 1)
     pong n

   pong : Nat -> {State Nat} ()
   pong 0        = ()
   pong (Succ n) = ping n
   ```
8. Mutually recursive theorems, about `even` and `odd` defined *earlier*:

   ```
   theorem evenNotOdd : (n : Nat) -> even n = not (odd n)
   evenNotOdd 0        = rfl
   evenNotOdd (Succ n) = oddNotEven n

   theorem oddNotEven : (n : Nat) -> odd n = not (even n)
   oddNotEven 0        = rfl
   oddNotEven (Succ n) = evenNotOdd n
   ```

   Their types mention `even`/`odd`, which are in an earlier, final group, so
   they compute: `even (Succ n) = not (odd (Succ n))` reduces to `odd n = not
   (even n)`.

Must be **rejected**:

9. A proof placed *inside* the group of the functions it's about. With
   `mutual` blocks (option 1), writing `theorem evenTwo : even 2 = True` in
   the same block as `even` and `odd` is refused (`E-MUTUAL-SIGNATURE`): its
   signature mentions a pending sibling. With automatic grouping (option 2)
   it only lands in the group if `even` or `odd` calls it. Either way the fix
   is to keep it out of the cycle, which forward references make free.
10. Calls that only pass arguments along:

    ```
    ping : Nat -> Nat
    ping n = pong n               -- 0 ≤→ 0
    pong : Nat -> Nat
    pong n = ping n               -- 0 ≤→ 0
    ```
11. **Each call shrinks something, but not the same thing** — the trap for a
    naive "every call has some smaller argument" rule, and for merging
    graphs:

    ```
    f : Nat -> Nat -> Nat
    f Zero     y = y
    f (Succ x) y = g x (Succ y)   -- {0 <→ 0}; `Succ y` is new, so no arc
    g : Nat -> Nat -> Nat
    g x Zero     = x
    g x (Succ y) = f (Succ (Succ x)) y   -- {1 <→ 1}; `Succ (Succ x)` is new
    ```

    `f 1 0 → g 0 1 → f 2 0 → g 1 1 → f 3 0 → …` runs forever. The loop
    `f → g → f` composes to the empty graph, which is idempotent with no
    `<` arc.
12. A member passed to a helper, so the call is hidden (the mutual version of
    `soundness/higher-order-recursion.sw`), written with `List` so it needs
    no data group:

    ```
    walk : List Nat -> Nat
    walk ts = applyTo walkList ts        -- bare reference: refused by saturation (§6.3)
    walkList : List Nat -> Nat
    walkList Nil         = 0
    walkList (Cons _ ts) = walk ts
    ```

    Even eta-expanded (`applyTo (\x -> walkList x) ts`), the call
    `walkList x` relates `x` to nothing, so the loop has no strict arc.
13. Rebuilding the parameter, across the group (the mutual version of
    `reject/rebuild-parameter.sw`): `a (Succ n) = b (Succ n)` and
    `b (Succ n) = a (Succ n)` give `≤` arcs only.
14. A hidden call inside an accepted call's argument, across the group:
    `a (Succ n) = b n (a (Succ n))` — the inner call `a (Succ n)` is a
    `≤`-only loop on `a`.
15. The `Ping` handler that restarts its computation (DESIGN.md §8), split
    across two functions:

    ```
    bad : (() -> {Ping} a) -> a
    bad prog =
      handle prog () with
        | return x     -> x
        | ping u => k  -> again prog
    again : (() -> {Ping} a) -> a
    again prog = bad prog
    ```

    Both calls pass `prog` unchanged: `≤` only.
16. A member whose signature mentions a sibling:

    ```
    f : (n : Nat) -> g n = g n     -- `g` is in the same group
    g : Nat -> Nat                 -- …because `g`'s body calls `f`
    ```

    `E-MUTUAL-SIGNATURE` (§5.2).

Plus the raw-kernel tests of §5.5 and the partial-application tests of §6.3.
For the must-reject suite, each of 10–16 is paired with an accepted
neighbour (from 1–8, or the handler that only resumes `k`), as
`examples/README.md` requires.

## 7. Mutually recursive data types

### 7.1 Positivity

The rule is today's, with "the data type" replaced by "any type in the
group": in each field of each constructor of each member, group members may
occur only as a member applied to exactly the group's parameters, or as the
result of a function type whose domains mention no member. So:

```
-- Rejected (E-POSITIVITY): `Bad1` occurs to the left of an arrow, through `Bad2`
type Bad1 : Type =
  | MkBad1 (f : Bad2 -> Void)

type Bad2 : Type =
  | MkBad2 (b : Bad1)
```

Without the group-wide check, `Bad1` would look positive (it only mentions
`Bad2`), and `Bad2` would look positive (it only mentions `Bad1`), and
together they give a proof of `Void`, exactly like `type Bad = MkBad (Bad ->
Void)`. This pair goes in the must-reject suite, paired with `Tree`/`Forest`.

Also kept:

- **The "declared later" rule.** Under the admission invariant it is
  redundant: a definition declared after the data group that mentions a
  member would refer to a pending declaration and be refused (§5.2), and one
  that doesn't mention it can't hide a negative occurrence. It stays anyway,
  as a cheap second line of defence, now reading the group's metadata rather
  than comparing declaration indices (§7.3).
- **No occurrence through a definition.** `positive` doesn't unfold
  definitions, so a field whose type is a definition applied to a member is
  rejected, as it is today for a single type. This rejects some safe
  aliases: with `Box a = a` or `Stream a = Nat -> a`, a field `(b : Box
  Tree)` is positive once unfolded, and accepting it would need positivity to
  unfold definitions (the Agda and Idris bugs above show the danger of
  getting that wrong). An *unsafe* alias such as `Pred a = a -> Bool` is
  different: `(p : Pred Tree)` unfolds to `Tree -> Bool`, a negative
  occurrence, and must be rejected whatever the rule. (Draft 1 used `Pred`
  as its example of something unfolding would accept; it isn't.)
- **Nested occurrences** (`List Tree`) stay rejected. Lean translates them
  into extra mutual types [L2]; Agda [A4] and Rocq [R1] analyse how the outer
  type uses its parameter. Either is a separate proposal. The Idris bug
  #1771 [I4] shows what happens without the analysis.

### 7.2 Constructors that mention siblings

A field may mention a sibling *type*, but not a sibling's *constructors* (or
a `case` on one). For example `type T = Node (f : F) (ok : f = FNil)` is
refused (`E-MUTUAL-CONSTRUCTOR`, say): while the group is pending, no
member's constructors are available (§5.4), so this falls out of the
admission rules.

This is a restriction on the supported declaration form, chosen because this
milestone deliberately avoids dependencies between a type's fields and its
siblings' constructors. Draft 1 said such references are a step towards
induction-induction; some are, but a constructor reference is not
automatically an inductive-inductive definition, and the example above might
well be sound. It's excluded for simplicity, not because every excluded
example is known to be unsound.

### 7.3 Universes, parameters, group metadata and elimination

- **One shared parameter telescope.** All members take the same parameters,
  and the kernel checks them **once**, in one properly scoped context
  (`declare_data_group`, §5.4), instead of checking each member's parameters
  separately and then comparing them. Comparing binder names, or comparing
  dependent parameter types one at a time, is exactly where a subtle
  mismatch would hide. Lean [L2] and Rocq [R1] both require the same
  parameters. It's what makes "applied to exactly its own parameters"
  meaningful for a sibling.
- **Headers depend only on final declarations and the parameters**, never
  on members of their own group (§5.4).
- **Immutable group metadata.** Each member records its group (the list of
  members) and its index in it, set when the group is declared and never
  changed. Positivity, the "recursive function field" classification in the
  termination checker (§6.2), exhaustiveness and hashing (§8.4) read this
  metadata. None of them infers group membership from source placement or
  from declaration indices (today's `defs_before` and data-index
  comparisons).
- **Same universe.** All members live in the same universe (Lean's rule
  [L2]; Rocq appears to allow a different sort per type [R1], going by its
  typing rule, **not verified** from an explicit statement). The field rule
  is unchanged: a field in `Type i` needs the data type in `Type j`, `i ≤ j`.
  With one universe for the group, a sibling field is always allowed.
  Relaxing this later breaks nothing.
- **`Prop` groups: no elimination into data.** Today a `Prop` type with at
  most one constructor whose fields are all proofs can be matched to
  produce data (subsingleton elimination). Lean's kernel switches this off
  for any mutual group of more than one type: "Mutually recursive inductive
  predicates only eliminate into Prop" [L4]. Adopt the same rule as an
  explicitly **conservative** restriction: the Lean source confirms the
  comparison, not that the restriction is necessary in a core with
  different conversion and proof-relevance rules. Matching on a proof in a
  `Prop` group to produce another proof is unaffected (§6.7).
- **Matching** is per type and unchanged: a `case` on a `Tree` has one
  branch per `Tree` constructor, and is allowed only once the group is final
  (§5.4). There are no eliminators to generate; recursion over the group is a
  function group (§6), and induction over it is a theorem group.

### 7.4 Exhaustiveness and `()`

Unchanged, per type, but only against a final data type (§5.4).

### 7.5 Out of scope

- **Induction-recursion**: a type and a function on it defined together,
  where constructors use the function — the standard example is a universe
  `U` with `El : U -> Type` and a constructor `pi : (a : U) -> (El a -> U) ->
  U`. Its consistency needs a strong set-theoretic model (Dybjer & Setzer
  [D1]). Agda supports it [A1]; Lean and Rocq don't (**not verified** from
  an explicit statement). Rejected by the admission invariant (a field can't
  refer to a pending definition) and the mixed-group rule.
- **Induction-induction**: a type `A` and a family `B : A -> Type` defined
  together (contexts and types-in-context). Stitchwort has no indexed data
  types, so it can't even be written; the "no sibling constructors" rule
  (§7.2) also blocks some nearby forms. Theory: Nordvall Forsberg [D2].
- **Nested inductives** (`Rose = Node (List Rose)`): later, separately
  (§7.1).
- **Mutual abilities** (an ability whose operations mention a data type that
  mentions the ability): rejected. It would be Landin's knot (DESIGN.md §8),
  and the translated declarations would fail positivity anyway.

## 8. Interactions

### 8.1 Elaboration order, and things that depend on it today

With option 2, the elaborator first collects every top-level name
(definitions, data types and their constructors, abilities and their
operations), reporting duplicates, then builds the dependency graph, then
checks SCCs in dependency order, breaking ties by source position (so
checking order is deterministic). Within a group: signatures first (in source
order), then bodies; for data, the shared parameters and universe first, then
constructors.

**The dependency pre-pass is binder-aware.** It collects the *resolved free
references* of each declaration, not raw identifier occurrences:

- a locally bound name (a pattern variable, a lambda or `let` binder, an
  explicit or implicit type parameter) creates no dependency on a top-level
  declaration spelled the same way;
- a constructor in a pattern or expression creates a dependency on the data
  type that owns it;
- an ability operation creates a dependency on its ability;
- an explicitly written decision procedure (in place of `auto`) is an
  ordinary reference and creates an ordinary edge.

Three things in the elaborator depend on order today and need decisions:

- **Implicitly bound type variables.** An unknown lowercase name in a
  signature, used only where a type is expected, becomes an implicit
  parameter (`length : List a -> Nat`). "Unknown" currently means "not
  defined *so far*" (`autobind.rs` checks the name table as it stands). With
  whole-module scope, a definition named `a` anywhere in the file turns
  every signature's `a` into a reference to it. **Decision:** names in the
  module take priority (the simple rule, confirmed acceptable by the
  review). This is **not semantically neutral**: adding a top-level
  definition `a` changes `length : List a -> Nat` from a polymorphic
  signature to one about that definition, which may still type-check. So
  whenever a name that would otherwise have been bound implicitly resolves
  to a module definition, the elaborator warns, pointing at **both** sites
  (the signature's use and the definition), and suggests the explicit binder
  `length : [a : Type] -> List a -> Nat`. If the signature then fails to
  check, the error carries the same note.
- **`auto` arguments and `==`** search for decision procedures among
  definitions, trying the most recently defined first (today: every
  definition with a body, `crates/elab/src/auto.rs`). **Decision for the
  initial implementation:** search only declarations that are **final at
  the point of checking and earlier in the source**, most recent first. This
  is a **deliberate limitation**: explicit references get forward-dependency
  scheduling, but implicit decision-procedure discovery only uses candidates
  already available when the use is checked. Being written above the use is
  *not* enough. The review's example:

  ```
  decisionProcedure … = laterHelper …      -- first in the source
  client … = … auto …                      -- second
  laterHelper … = …                        -- third
  ```

  The graph has `decisionProcedure → laterHelper` but no edge from `client`
  to `decisionProcedure` (the `auto` is not a reference yet). `client` and
  `laterHelper` are both ready first; the source-position tie-break checks
  `client` first, so `decisionProcedure`, though above it, isn't final yet
  and isn't searched. So the candidate set, and which proof is found, *can*
  change when code moves; draft 1's claim that it can't is withdrawn.

  When `auto` finds nothing, `E-AUTO-NONE` distinguishes three cases for a
  module definition with a matching result type:
  1. *below the use* in the source: "move it above `client`, or pass it
     explicitly";
  2. *above the use but not yet checked*, because it waits on dependencies:
     name the dependency chain (`decisionProcedure` uses `laterHelper`, which
     is checked after `client`) and suggest passing it explicitly;
  3. *in the same unfinished group* as the use: it can't run while the
     group is being checked, so it can't be used; suggest moving the proof
     out of the cycle.

  Passing the procedure explicitly creates an ordinary dependency edge, so it
  is scheduled first, unless that edge closes a cycle, which is case 3.
  A more coherent long-term policy (eligibility by source position, with the
  scheduler checking an eligible candidate on demand and reporting cycles) is
  possible later; it isn't needed for the first implementation.
- **Ability order in rows.** Rows are sorted by the order abilities were
  declared in. That order should be source order, assigned in the pre-pass,
  not checking order.

Hidden dependencies: elaboration inserts references the source doesn't
mention (prelude operators, `bind`, `translate`, decision procedures). The
prelude is a separate, earlier module, and decision procedures are limited to
final declarations as above, so none of these can create a cycle the
pre-pass didn't see. If one did, the kernel would refuse it (§5.2).

With option 1 (`mutual` blocks), only the first bullet changes, and only
inside a block.

### 8.2 Implicit arguments across a group

Every definition has a full signature, and signatures may not mention
pending declarations, so all signatures are elaborated (and their
metavariables solved) before any body. A body sees a sibling only through its
finished type, so no unification problem spans two members, and zonking
stays per declaration. This is the main reason the change is simpler here
than in Haskell, where binding groups exist for type inference [H1].

### 8.3 Error messages

- **Termination** names the cycle and each call, rebuilt from the witness
  links (§6.5):

  ```
  [E-TERMINATION] can't show that `f` and `g` terminate
    f (Succ x) y = g x (Succ y)      -- f passes a smaller first argument
    g x (Succ y) = f (Succ (Succ x)) y   -- g passes a smaller second argument
    = going round f → g → f, no argument gets smaller
  ```
- **An accidental cycle** (with automatic grouping) can be confusing: the user
  didn't mean `f` and `g` to be mutually recursive. The termination message
  shows the path, so the unintended call is visible.
- **An unsaturated member** (§6.3) says what to write.
- **A member fails to check**: every member fails (§5.1); later errors that
  only happen because a member failed should be avoided as today (the
  definitions stay in scope, without bodies, for diagnostics only).
- **`auto` found nothing**: the three cases of §8.1.
- **Module name over a type variable**: the two-site warning of §8.1.
- **`E-MUTUAL-SIGNATURE`, `E-MUTUAL-KIND`, `E-MUTUAL-CONSTRUCTOR`** (names
  provisional). With option 1, `E-UNKNOWN-NAME` for a name defined further
  down should suggest `mutual`; with option 2 that error can't happen.

### 8.4 Content hashes and the test cache

Following DESIGN.md §11 and Unison [U1]:

1. For a group of `k ≥ 2` members, hash each member with references to group
   members replaced by one fixed marker (no index): its **shape hash**.
2. Order the members by shape hash. Data types are nominal and their names
   are hashed anyway, so data groups can simply be ordered by name. For
   definitions, ties are possible (two members identical up to which sibling
   they call). Unison makes a tie an error [U2]; that's unfriendly, so break
   ties by kernel declaration order.
3. The **group hash** covers `k`, the group's metadata, and each member in
   that order, with references to members hashed as `("member", index)`.
4. Each member's hash is `H("member", group hash, index)`, cached under the
   member's key as today.

**Simpler fallback.** Pure source-order indexing (skip steps 1–2) is also
safe. It loses cache hits when declarations move. If shape hashing
complicates the implementation, start with source order.

A single self-recursive definition keeps today's `self` marker, so existing
hashes don't change.

Requirements:

- **Every reference form.** `Def`, `Data`, `Ctor` and `Case` (§1) must all
  hash an internal reference as `("member", index)`, and a constructor
  reference as the member index *and* the constructor index, so
  `Ctor(Forest, 0)` and `Ctor(Forest, 1)` differ. No reference form —
  including the data type mentioned by a `case`, and implicit builtin
  dependencies — may fall back to asking for an unfinished member's hash
  (today that would recurse until the depth guard fires).
- **Full declarations and group metadata.** Signatures, bodies, the shared
  parameters, the universe, constructor names and fields, the `theorem`
  flag, and anything affecting elimination or extraction (for data: the
  group's size, which decides subsingleton elimination for `Prop` groups).
  *Observation, not part of this proposal:* today's `def_hash` doesn't hash
  the `export` flag or the export validators. That seems right while hashes
  key only test results, which don't depend on them; if anything ever caches
  extraction by hash, it must be revisited. (**Unverified** whether anything
  does.)
- **Publish only final hashes.** Shape hashes and any hash computed while
  bodies are absent are internal to the hashing of one group and never
  stored in the hash table. `def_hash` and `data_hash` refuse anything not
  final (§5.6).

Why tie-breaking by source order is safe: a cached result is reused only if
the hash matches. Hashing the group's full content in an unambiguous
serialisation, in some fixed order, means different contents always give
BLAKE3 different *inputs*; a collision between different inputs is
cryptographically unlikely, not impossible (the hash is fixed-width). A
different order for the same content only gives a different hash: a cache
miss, never a wrong hit. Canonical ordering is purely about cache hit rates.

Every member's hash covers the whole group, so changing one member
invalidates the cached results of tests that use any member. That's
necessary: their behaviour may have changed.

**Tests:** two members with tied shapes (the hash is deterministic across
runs); reordering members with distinct shapes (hashes unchanged) and with
tied shapes (documented: may change); changing only one member's signature
(every member's hash changes); changing one constructor of one data-group
member (every member's hash changes); references to two constructors of the
same sibling (distinct); a single self-recursive definition (hash unchanged
from today, against the existing `crates/core/tests/hash.rs` snapshots); a
failed group (no hash).

### 8.5 Abilities

Effectful functions are ordinary functions into `Comp`, so effectful mutual
recursion is just mutual recursion (§6.8 example 7). The handler rules
(DESIGN.md §8, abilities.md) are enforced by positivity and termination
after translation, so the group versions are covered: a handler whose
clause calls back into the handler through a helper is a `≤`-only loop
(§6.8 example 15).

### 8.6 JavaScript

- **One calling convention per definition**, computed once from the
  definition and its group, and used by **every** site: declaration
  emission, ordinary references, applications, first-class uses (a member
  passed as a value) and export wrappers. Today the "thunk" fact is derived
  twice, from the body's shape, in `Gen::def` and in `is_thunk` (§1); no site
  may infer the convention from the occurrence's remaining syntax. The
  conventions:
  - *Value*: no runtime parameters, not in a recursive group, not a case
    tree: `const f = …;`, computed when the module loads, referenced as `f`.
  - *Thunk*: no runtime parameters, and either a case tree or **a member of
    a recursive group**: `const f = () => …;`, referenced as `f()`.
  - *Function*: runtime parameters: `const f = (v0) => …;`, referenced as
    `f`, applied as `f(a)`.

  The rule that every group member is a thunk or a function (never a value)
  is what stops a member whose parameters are all erased (types or proofs)
  from calling a sibling during module loading, before the sibling is
  defined (a JS `ReferenceError`). That pitfall is read from
  `crates/js/src/lib.rs`, **not run**.
- **Order of emission.** Emit in the kernel's order (SCC dependency order);
  inside a group any order works, since a member only looks a sibling up
  when called. Top-level values outside the group that use its results come
  after the group.
- **Tests:** direct calls between members; uses of a member partially
  applied *outside* the group (inside, saturation applies); a member whose
  only parameters are erased; a member returning a function; a top-level
  value outside the group computed from a member at load time; an export
  wrapper for a member.
- **Mutual tail calls aren't loops**, and that's not a prerequisite. Only a
  function's tail calls to itself become loops. `even 100000` recurses
  100 000 deep and throws a clean `StitchwortResourceError` (a resource
  error, never a wrong answer); there should be a test that it does. A later
  improvement: compile a group whose members tail-call each other into one
  loop with a "which function" variable, or a trampoline (js_of_ocaml does
  the latter, per [stack-safe-evaluation.md](stack-safe-evaluation.md)). The
  kernel's own evaluator already has no problem: tail calls add no frames
  there.
- **Boundary types.** Exporting a function on `Tree`/`Forest` needs codecs
  for both; `collect_datas` stops at types it has seen, so mutual references
  don't loop. The codecs no longer recurse (§1). Keep a test with a deep
  `Tree`/`Forest` value: traversing the *type* graph terminating and
  traversing a deep *value* without overflowing are separate properties.

## 9. Trusted code

Everything in the elaborator (name pre-pass, SCC computation, `mutual`
parsing, error messages, scheduling, `auto` eligibility) is untrusted: the
kernel re-checks, and refuses groups that aren't closed (§5.2). New or
changed trusted code:

| Where | What | Size (estimate) |
|---|---|---|
| `globals.rs`, `check.rs` | Declaration states; the dependency check over every reference form; failed-taint; refusing re-definition | ~80 lines |
| `check.rs` | `define_group`: saturation; bodies checked with all members opaque; atomic finalisation | ~60 lines |
| `termination.rs` | Graph extraction for calls to any group member, with the new `≤` relation tied to the recorded match; "recursive function field" over the data group | ~80 lines changed |
| `termination.rs` | Composition, closure and the idempotent-loop check, with budget and witness links | ~120 lines, new |
| `check.rs` | `declare_data_group` (one telescope, immutable metadata); group-wide positivity; no sibling constructors; no subsingleton elimination for groups; `case` only on final types | ~80 lines |
| `hash.rs` | Cycle hashing, only for final groups | ~60 lines (trusted for cache correctness, not for proofs) |
| `crates/js` | One calling convention; emission order | small (the extractor is trusted, DESIGN.md §13) |

The trusted *reasoning* is in three places, not one: the admission invariant
(§5.2), call extraction and provenance across a group (§6.2–6.3), and the
closure algorithm (§6.5). The well-founded-semantics argument (§6.4) is the
justification for all three and is a sketch, not a proof.

## 10. Staging

0. **Optional, any time: acyclic forward references** (feature A). Only the
   elaborator changes (the pre-pass and dependency-order checking); the
   kernel sees the same sequence of admissions as today. It doesn't need to
   wait for the kernel work, and the kernel work doesn't need to wait for it.
1. **Kernel admission and SCT, no surface change.**
   - Declaration states, the admission invariant, failed-taint, refusing
     re-definition (§5). The raw-kernel tests of §5.5 (1 and 2 fail today).
   - The graph algorithm (§6.5) with its independent tests and reference
     oracle (§6.6), *before* it is wired into the kernel.
   - SCT used for single definitions (groups of one): Ackermann and swapped
     arguments become accepted; the whole example suite must still pass.
   - The saturation rule (§6.3); the two `soundness/` snapshots that change
     wording are reviewed.
2. **Function groups and forward references** (option 2). `define_group` for
   groups of more than one, atomic checking, cycle hashing (§8.4),
   scheduling and the `auto` diagnostics (§8.1), the JS calling convention
   (§8.6). Incorrect partitions tested directly through the kernel API
   (§5.5 test 9). Examples: 1, 3, 5, 7–16 of §6.8, all using only data types
   that exist today (`Nat`, `List`, `Comp`); none needs a data group. (Draft
   1 promised `size`/`sizeForest` and example 6 here, before data groups
   existed; they move to milestone 3, and example 12 is rewritten over
   `List`.)
3. **Mutual data types.** `declare_data_group` with one telescope, group-wide
   positivity, immutable metadata, atomic finalisation, then elaborator
   support. Adds `Tree`/`Forest`, `size`/`sizeForest`, example 6, `Bad1`/
   `Bad2`, the pending-datatype test at the surface level, and the deep
   `Tree`/`Forest` codec test.
4. **Later, separately:** nested inductives (via translation to mutual
   groups, as Lean does, or a variance analysis); closure-aware partial
   applications (§6.3); mutual tail calls as loops in JS; `decreasing`
   measures (DESIGN.md §5) for a group; `auto` eligibility by source position
   with on-demand scheduling (§8.1).

## 11. Recommendation

- **Option 2: order-independent explicit name visibility.** Every top-level
  name is visible throughout its module; the elaborator groups declarations
  into strongly connected components with a binder-aware pre-pass and
  checks them in dependency order. `auto` discovery and ability order keep
  their order-dependence (§8.1); module names take priority over implicit
  type variables, with a two-site warning.
- **The kernel enforces group completeness**: every dependency of a group is
  a member or final; four declaration states; failed groups publish nothing
  (§5).
- **Saturated recursive occurrences** in the checked core; no eta-expansion
  pass (§6.3).
- **Size-change termination** for groups and single definitions, with the
  algorithm specified and independently tested (§6.5–6.6), and the
  soundness argument split into its three obligations (§6.4).
- **Data-type groups** with one shared telescope, one universe, immutable
  metadata, group-wide strict positivity, no sibling constructors in fields,
  and no elimination into data for `Prop` groups. Nested, inductive-recursive
  and inductive-inductive types stay out.
- **Cycle hashing** with deterministic tie-breaking, or pure source order.
- **Stage it** as in §10, kernel first.

## 12. The review's answers, and where this draft stands

| # | Question (draft 1) | Review's recommendation | Draft 2 |
|---|---|---|---|
| 1 | Is the termination argument sufficient for this kernel? | The graph criterion is right; strengthen the language-level justification for higher-order values, delayed calls and normalisation of open terms. | Restructured into three obligations (§6.4); delayed calls covered by induction over call sites; normalisation of open terms separated and marked not yet worked out. |
| 2 | Is reconstruction safely `≤`? | Yes, when it reconstructs the exact matched value with provenance kept; it's equality. | Adopted, tied to the exact recorded match; nothing broader (§6.2). |
| 3 | Permit partially applied group members? | Not justified by the current argument. Closure-aware edges, or saturation first. | Saturation, no eta-expansion pass (§6.3). |
| 4 | Refuse sibling references in signatures? | Yes initially; a simplification, not inherent. | Kept, now a consequence of the admission invariant (§5.2). |
| 5 | Same universe for data groups? | Keep it. | Kept (§7.3). |
| 6 | No data elimination from mutual `Prop` groups? | Keep, as explicitly conservative. | Kept, described as conservative (§7.3). |
| 7 | Source-order tie-breaking for hashes? | Acceptable; full indexed group content must still be hashed. | Adopted, plus pure source order as a fallback (§8.4). |
| 8 | Module names over implicit type variables? | Acceptable with a clear diagnostic and an explicit-binder escape hatch; it changes the meaning of some source. | Adopted with a two-site warning and the explicit-binder suggestion (§8.1). |
| 9 | Criterion R first? | Not necessary; test S independently before integrating it. | S, with the algorithm tested on its own first (§6.6, §10 milestone 1). |

**Where this draft goes beyond the review.**

- The review said it was "not claiming the implementation accepts" the split
  cycle. Through the raw kernel API it does, and the pending-datatype
  example too (§1). Neither is reachable from source today.
- The draft makes `E-MUTUAL-SIGNATURE`, the mixed-group rule and the "no
  sibling constructors" rule consequences of the admission invariant rather
  than separate checks, and notes that the "declared later" positivity guard
  becomes redundant under it (kept anyway). These inferences are the
  author's, not the review's, and deserve a second look.
- A data group is declared with one call taking one telescope, rather than
  per-member declarations compared afterwards.

**Disagreements with the review.** None of substance. Two points where the
draft deliberately stops short:

- The review's "most coherent long-term policy" for `auto` (eligibility by
  source position, scheduled on demand) is deferred to §10 stage 4; the
  review itself called the simpler policy defensible for now.
- The review asks that function-valued fields be justified semantically.
  §6.4 gives the outline and the reference, but **no proof**, and the open
  gap (infinitely branching data in a dependent core; normalisation of open
  terms) is stated rather than closed. It may stay a documented gap, as it
  already is for the single-function rule.

**Still deserving a second review before implementation:** the §6.4
outline (in particular step 4's claim that induction over call sites covers
callbacks invoked repeatedly or after their creator returns); the claim
that §5.2's check need not follow references transitively; and the
saturation rule's definition of arity as "leading lambdas of the submitted
body" (§5.3 step 3).

## Research gaps

- Lean's treatment of mutual bodies during elaboration (opaque local
  variables?) is inferred, not confirmed from its documentation.
- Whether current Agda still unfolds unchecked clauses of a mutual block
  during type checking (confirmed only for 2013).
- Rocq's per-type sorts in a mutual block is a reading of the typing rule,
  not an explicit statement.
- The exact wording of the SCT criterion ("every idempotent graph has a
  decreasing self-arc") was taken from lecture notes and Agda's source, not
  re-read in the POPL paper. Abel's 1998 foetus paper and Ben-Amram's later
  soundness work were not read. The description of [S2] as a semantic
  structural ordering for generalised inductive types and higher-order
  functions follows the review and the paper's abstract; the paper's proofs
  were not checked against §6.4.
- The 2014 Rocq/propositional-extensionality explanation is quoted from a
  search summary (the mailing-list page refused the fetch).
- Elm's and PureScript's automatic grouping was not checked.
- Checked by the orchestrator on 15 October 2026 by opening the pages:
  Rocq #21682 ("Guard checker soundness bug: cross-calls in nested mutual
  fixpoints", closed 4 March 2026 by PR #21684, labelled "kind:
  inconsistency"); CVE-2026-72703 (Mend.io entry for the same bug, fixed in
  Rocq 9.2.0); Agda #8699 ("Termination checker descends into irrelevant
  (and Prop-typed) constructor arguments of dot patterns", closed 29 August
  2026 by PR #8707, proves `⊥` under `--safe`).
- Claims about Stitchwort's JS emission for group members with only erased
  parameters (§8.6) come from reading the code, not from running it.
- Whether the native-registration functions check that the definitions they
  name are finished (§5.2) was not checked.
- Run for draft 2 (throwaway tests, not committed, at `14649d5`): the
  split-cycle and pending-datatype raw-kernel sequences (§1, both accepted
  today); the partial/bare self-call probe over the CLI example suite
  (§6.3). Read but not run: `define_def` not refusing an already-defined id;
  a failed data type staying declared with no constructors.

## Sources

- [A1] Agda manual, *Mutual Recursion*.
  <https://agda.readthedocs.io/en/latest/language/mutual-recursion.html>
- [A2] Agda source documentation, `Agda.Termination.Termination` ("In the
  completed call graph, each idempotent call-matrix from a function to
  itself must have a decreasing argument").
  <https://hackage-content.haskell.org/package/Agda-2.8.0.2/docs/Agda-Termination-Termination.html>
- [A3] Agda manual, *Termination Checking*.
  <https://agda.readthedocs.io/en/latest/language/termination-checking.html>
- [A4] Agda manual, *Positivity Checking*.
  <https://agda.readthedocs.io/en/latest/language/positivity-checking.html>
- [A5] Agda issues #8699, #7751, #6059, #5910 (label `false`).
  <https://github.com/agda/agda/issues/8699>,
  <https://github.com/agda/agda/issues/7751>,
  <https://github.com/agda/agda/issues/6059>,
  <https://github.com/agda/agda/issues/5910>
- [A6] Agda mailing list, 2013, on termination being checked after a mutual
  block is type-checked.
  <https://lists.chalmers.se/pipermail/agda/2013/005762.html>
- [I1] Idris 2 tutorial, *Types and Functions* (mutual blocks, forward
  declarations).
  <https://idris2.readthedocs.io/en/latest/tutorial/typesfuns.html>
- [I2] Idris 2 source, `Core/Termination/SizeChange.idr`.
  <https://github.com/idris-lang/Idris2/blob/main/src/Core/Termination/SizeChange.idr>
- [I3] Idris 2 tutorial, *Theorem Proving* (totality).
  <https://idris2.readthedocs.io/en/latest/tutorial/theorems.html>
- [I4] Idris 2 issues #1771, #1988, #2333.
  <https://github.com/idris-lang/Idris2/issues/1771>,
  <https://github.com/idris-lang/Idris2/issues/1988>,
  <https://github.com/idris-lang/Idris2/issues/2333>
- [L1] Lean reference, *Recursive Definitions*.
  <https://lean-lang.org/doc/reference/latest/Definitions/Recursive-Definitions/>
- [L2] Lean reference, *Inductive Types* (mutual and nested).
  <https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/>
- [L3] Lean v4.11.0 release notes (mutual structural recursion).
  <https://lean-lang.org/doc/reference/latest/releases/v4.11.0/>
- [L4] Lean 4 kernel, `src/kernel/inductive.cpp` (`elim_only_at_universe_zero`;
  same-universe and same-parameters checks).
  <https://github.com/leanprover/lean4/blob/f03441b0ede34323c9cefed4c98368a3c07491dd/src/kernel/inductive.cpp>
- [R1] Rocq reference manual, *Inductive types and recursive functions*
  (`Fixpoint … with`, guard condition, mutual inductives, nested
  positivity, `Scheme`).
  <https://rocq-prover.org/doc/master/refman/language/core/inductive.html>
- [R2] Rocq issue #21682 (cross-calls ignored in a mutual fixpoint; proof of
  `False`), and follow-ups #21797, #22382.
  <https://github.com/rocq-prover/rocq/issues/21682>
- [R3] CVE-2026-72703 entry.
  <https://mend.io/vulnerability-database/CVE-2026-72703/>
- [R4] Coq 8.4pl4 announcement and M. Dénès on the Agda list (2014),
  propositional extensionality and the guard condition.
  <https://coq.inria.fr/news/coq-84pl4-is-out.html>,
  <https://lists.chalmers.se/pipermail/agda/2014/006517.html>
- [U1] Unison language reference, *Hashes*.
  <https://www.unison-lang.org/docs/language-reference/hashes>
- [U2] Unison source, `unison-hashing-v2/src/Unison/Hashing/V2/ABT.hs`
  (`doHashCycle`, `IncompleteElementOrderingError`).
  <https://github.com/unisonweb/unison/blob/8494fe347a1e8cdbb5e02aa22423c976fdfa50b0/unison-hashing-v2/src/Unison/Hashing/V2/ABT.hs>
- [H1] Haskell 2010 Report, §4.5.1 *Dependency Analysis*.
  <https://www.haskell.org/onlinereport/haskell2010/haskellch4.html>
- [S1] C. S. Lee, N. D. Jones, A. M. Ben-Amram, *The Size-Change Principle
  for Program Termination*, POPL 2001.
  <https://khoury.northeastern.edu/~pete/courses/Formal-methods/2008-Fall/readings/lee01sizechange.pdf>
- [S2] A. Abel, T. Altenkirch, *A Predicative Analysis of Structural
  Recursion*, JFP 12(1), 2002 (foetus; semantic structural ordering for
  generalised inductive types and higher-order functions, simply typed).
  <https://www.cse.chalmers.se/~abela/foetuswf.pdf>
- [S3] D. Wahlstedt, *Dependent Type Theory with First-Order Parameterized
  Data Types and Well-Founded Recursion*, PhD thesis, Chalmers, 2007.
  <https://research.chalmers.se/en/publication/45188>
- [S4] P. Hyvernat, *The Size-Change Termination Principle for
  Constructor Based Languages*, LMCS 10(1:11), 2014.
  <https://arxiv.org/abs/1306.3833>
- [S5] A. Abel, *Termination Checking with Types*, RAIRO-ITA 38(4), 2004
  (sized types; an alternative to SCT not proposed here).
  <https://www.numdam.org/item/ITA_2004__38_4_277_0>
- [D1] P. Dybjer, A. Setzer, *A Finite Axiomatization of
  Inductive-Recursive Definitions*, TLCA 1999.
  <https://research.chalmers.se/en/publication/17647>
- [D2] F. Nordvall Forsberg, *Inductive-inductive definitions*, PhD thesis,
  Swansea, 2013.
  <https://cronfa.swan.ac.uk/Record/cronfa43083>
