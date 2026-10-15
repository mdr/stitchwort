# Proposal: forward references and mutual recursion

**Status:** proposed, 15 October 2026, for external review. Not implemented.

This note is meant to be read without knowing the codebase. The first section
describes the parts of Stitchwort it touches; everything said there was
checked against the source as of commit `8793ac3`. Claims about other systems
cite their sources ([Sources](#sources)); anything not verified is marked
**unverified**.

## Contents

1. [Background: how things work today](#1-background-how-things-work-today)
2. [The problem](#2-the-problem)
3. [How other systems do it](#3-how-other-systems-do-it)
4. [Options for the surface language](#4-options-for-the-surface-language)
5. [What the kernel sees](#5-what-the-kernel-sees)
6. [Termination for a group of functions](#6-termination-for-a-group-of-functions)
7. [Mutually recursive data types](#7-mutually-recursive-data-types)
8. [Interactions](#8-interactions)
9. [Trusted code](#9-trusted-code)
10. [Staging](#10-staging)
11. [Recommendation](#11-recommendation)
12. [Questions for the reviewer](#12-questions-for-the-reviewer)
13. [Sources](#sources)

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
lexicographic orders: Ackermann's function is rejected today (§6.5, example 4). The
rules and their soundness argument are written up in
[abilities.md](abilities.md#the-termination-rule); the must-reject suite
(`examples/soundness/`) has the tricky cases (a recursive call hidden inside
an accepted call's argument, a self-reference passed to a helper, rebuilding
a different field, a function that merely returns the same type as a field).

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

**Content hashes** (`crates/core/src/hash.rs`, BLAKE3) identify every
checked declaration, and test results are cached by them. A reference to
another declaration is hashed as that declaration's hash (computed
recursively, on demand), and a reference to itself as a fixed `self` marker.
Definition names aren't hashed; data type and constructor names are (data
types are nominal). DESIGN.md §11 already says that mutually recursive
groups are to be hashed "as a unit, with members referring to each other by
their index within the group", following Unison, but nothing implements it,
because no cycles can occur yet. Today a cycle would make `def_hash` recurse
until the depth guard stops it with `E-RESOURCE`.

**Abilities** (effects) are translated into ordinary data before the kernel
sees them: an effectful function's type is a function into the prelude's
`Comp` tree type, and handlers are folds over `Comp`, checked by the same
positivity and termination rules ([abilities.md](abilities.md)).

**JS extraction** (`crates/js`) emits each reachable definition as `const f =
(v0) => …` in declaration order, which today is also dependency order. A
function's tail calls *to itself* become a loop; other recursion uses a JS
stack frame per call, and running out of stack throws a clean
`StitchwortResourceError`. The kernel's own evaluator is a stack-safe
machine in which tail calls add no frames
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
  group, and cycle hashing.
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
| **Haskell** | Automatic: "a declaration group is a minimal set of mutually dependent bindings", processed "in dependency order"; a type signature cuts the dependency [H1] | Same | — | The model for whole-module, order-independent declarations |

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
[S1], but the graphs are tiny in practice. Abel & Altenkirch's foetus [S2]
is the same idea with call matrices, and proves that structurally recursive
terms normalise; Wahlstedt [S3] proves normalisation of a dependent type
theory with first-order parameterised data types, given that the call
relation is well-founded, which is what SCT establishes. Hyvernat [S4]
refines SCT for constructor-based languages.

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

### Option 2: whole-module scope with automatic grouping

Every top-level name is visible everywhere in the module. The elaborator
builds a dependency graph from the source, splits it into **strongly
connected components** (SCCs: maximal sets of declarations that all reach
each other), and checks them in dependency order. Each SCC of size > 1, or
a declaration referring to itself, is a recursive group. This is Haskell's
rule [H1] and, in effect, Unison's.

- **For:** gives features A, B and C with no new syntax; the most natural
  for a non-expert ("write things in any order"); every definition already
  has a mandatory signature, so — unlike Haskell — no type *inference*
  crosses definitions, and grouping affects only checking order,
  termination and hashing.
- **Against:** a bigger elaborator change (a pre-pass to resolve names; see
  §8.1 for things whose meaning depends on order today); an accidental
  cycle shows up as a termination error rather than "unknown name", so the
  message must show the cycle; error recovery is per group, so one bad
  member makes the whole group opaque.

### Option 3: Agda-style forward declarations

Allow a signature on its own, with its equations later (`odd : Nat -> Bool`
near the top, `odd 0 = …` further down). Groups are inferred from where
signatures and definitions sit. This is the most flexible but the hardest to
explain, and conflicts with today's rule that equations immediately follow
their signature (`E-MISSING-DEFINITION`). Not recommended.

### The kernel doesn't care

Whichever option is chosen, the kernel receives **explicit groups** and
trusts nothing about how they were found (§5). A group that's bigger than
necessary is still checked soundly (calls between members that don't form a
cycle produce no loops in the termination analysis); it just recovers from
errors less precisely and invalidates caches more widely (§8.4).

## 5. What the kernel sees

### Function groups

A new kernel entry point, alongside `declare_def` / `define_def`:

1. **Declare every member** with `declare_def`, in order. Each signature is
   checked as today. **New check:** a member's signature may not mention any
   member of its own group (`E-MUTUAL-SIGNATURE`, say). Lean has the same
   rule [L1]; Agda allows it [A1]. Allowing it would let a type depend on how
   an unchecked sibling computes — a step towards induction-recursion for
   functions — and gains little.
2. **Check every body** against its signature, **with no member's body
   installed**. Inside the group, every member is an opaque constant: `even
   2` doesn't compute while `odd` is being checked. This is today's rule for
   a single recursive definition, extended to the group. It means the type
   checker can never unfold an unchecked definition, so it can't loop on one
   (the Agda 2013 problem, [A6]).
3. **Run the termination check on the whole group** (§6).
4. **Install all bodies at once.** If any step fails for any member, *no*
   body is installed, and every member stays opaque. That keeps the
   invariant "a definition with a body has passed the termination check
   together with everything it can reach".

The cost of step 2: a body whose *type-checking* needs a sibling to compute
fails. In practice that's a proof about `even` written in the same group as
`even`, which belongs in a later declaration anyway (§6.5 example 9). Lean
does the same, as far as can be told: its reference only says the elaborator
builds a "pre-definition in which recursion is still present" (**not
verified** in more detail).

Theorems (`theorem` definitions) can be group members: a proof by mutual
induction is a group of mutually recursive theorems, checked by the same
termination rule (§6.5 example 8). There are no generated induction
principles to worry about (Rocq needs `Scheme` for these [R1]).

### Data-type groups

1. **Declare every member** with `declare_data` (parameters and universe), so
   all of their names exist.
2. **Check the group's shape:** every member has the same parameter
   telescope (same types, up to conversion) and the same universe (§7.3).
3. **Define all constructors**, with positivity checked against the whole
   group (§7.1).
4. Mark them all defined at once.

**Mixed groups** — data types and definitions in one cycle — are rejected
(`E-MUTUAL-KIND`, say). Such a cycle is either induction-recursion (a
constructor mentions a function on the type being defined) or a function
that the data type's fields depend on; both are out of scope (§7.5). The
kernel needs no special check for this: a field may already only mention
definitions declared before the data type (§1), and that rule stays.

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

**Recommendation: S.** It's what Agda and Idris use [A2, I2], its
literature has normalisation proofs for dependent type theories with
first-order data [S3], and it handles the patterns people actually write
(wrappers, helpers with an accumulator, lexicographic recursion) without
annotations. The extra trusted code is the composition-and-closure
algorithm, about a page of Rust over small matrices (§9). R would be a
reasonable first step if the reviewer prefers the smallest possible change;
everything R accepts, S accepts, so moving from R to S later breaks nothing.

### 6.2 Classifying arguments (extending `termination.rs`)

Each argument of a call to a group member is classified relative to the
*caller's* parameters, exactly as today, plus one new relation:

| Argument | Relation to caller parameter `i` | New? |
|---|---|---|
| Parameter `i` itself | `≤` | **new** (today: unknown) |
| A constructor rebuilding parameter `i` exactly (`Succ n` where parameter `m` was matched as `Succ n`) | `≤` | **new** (today: unknown) |
| A field of a match on parameter `i` or on a descendant | `<` | as today |
| A constructor rebuilding a descendant | `<` | as today |
| A recursive function field of such a match, applied (`rest y`) | `<` | as today, but "recursive" now means *returns any type in the matched type's data group* (§7) |
| Anything else (other functions, `J`, lambda-bound variables, an unapplied or under-applied reference's missing arguments) | none | as today |

Unchanged rules that matter for soundness:

- **Every occurrence is a call.** Calls inside arguments of other calls,
  under lambdas and inside types are all collected (`soundness/
  hidden-recursive-call.sw`).
- **A bare reference to a member** (passed to a helper) is a call with no
  arcs, so any cycle through it fails (`soundness/higher-order-recursion.sw`).
  A partial application keeps arcs for the arguments it does supply, as
  today.
- **Relations come from terms, never from refined types**, and `case` is
  only on parameters or fields of earlier matches (the "fresh-wrapper
  invariant", [abilities.md](abilities.md#the-termination-rule)).
- **`J` never yields a sub-part** (the Rocq 2014 lesson, [R4]).

A variable is only ever related to one parameter (it was matched out of
exactly one), so each graph has at most one arc into each callee position.

### 6.3 The check

1. Collect a graph for every call site from a member `f` to a member `g`.
2. Repeatedly compose graphs along paths (`f → g` then `g → h` gives
   `f → h`; an arc `i → k` exists if `i → j` and `j → k` do, labelled `<` if
   either is `<`), until no new graph appears. The set is finite: between
   two functions of arities `m` and `n` there are at most `3^(m·n)` graphs.
3. For every graph `G` from a member to itself with `G ∘ G = G`, require an
   arc `i → i` labelled `<`. Otherwise reject, reporting the cycle of calls
   that produced `G` (keep one witness path per graph).

The closure is counted against the operation's resource budget, so a
pathological group ends with `E-RESOURCE` ("inconclusive", not accepted),
never with an acceptance.

**Why this is enough** (the argument the reviewer should check): suppose an
evaluation of a group member never finishes. Code outside the group was
admitted earlier and terminates, so the run must make infinitely many
nested calls between group members, each through some call site, i.e. an
infinite path in the call graph. By the size-change theorem [S1], if every
idempotent loop has a strict self-arc, any infinite path forces some
parameter's value to descend strictly infinitely often, never increasing
in between. Every value of a data type is a well-founded tree (strict
positivity; function fields make it infinitely branching but still
well-founded), and "is a sub-part of" on these trees is well-founded, *across
types*: a `Forest` inside a `Tree` inside a `Forest` is just a deeper node
of one tree. So no infinite descent exists, and the evaluation finishes.
Wahlstedt's thesis [S3] is the closest published proof for a dependent
type theory; it covers first-order parameterised data types, so **recursive
function fields (infinitely branching trees, as in `Comp`) are not covered
by it** — the same gap that [abilities.md](abilities.md#the-termination-rule)
already records for the single-function rule.

The same property keeps **conversion checking** terminating: a definition
unfolds only when its case tree can take a step, so each unfolding along a
cycle peels a real constructor off a value.

### 6.4 Arguments that are types or proofs

Implicit parameters (types, proofs) are parameter positions like any other.
A type can never be strictly smaller (there's no `case` on types), so it can
only carry `≤` arcs, which are harmless. A proof can be matched (only for
subsingleton propositions, by the `Prop` elimination rule), and its fields
are then genuine sub-parts of a value the kernel's evaluator really
computes with: Stitchwort has no definitional proof irrelevance, which is
what went wrong in Agda #8699 [A5]. **If proof irrelevance is ever added,
recursion on proofs must be revisited.**

### 6.5 Worked examples

Must be **accepted**:

1. `even`/`odd` (§2). Graphs: `even → odd: 0 <→ 0`, `odd → even: 0 <→ 0`.
   Every loop composes to `0 <→ 0`.
2. `size`/`sizeForest` (§2): every call is on a field.
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
   a release build of the CLI: `E-TERMINATION` on `ack m 1`):

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
6. A recursive function field returning a *sibling* type:

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
   lambda, where calls are already collected:

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

   Their types mention `even`/`odd`, which are in an earlier group, so they
   compute: `even (Succ n) = not (odd (Succ n))` reduces to `odd n = not
   (even n)`.

Must be **rejected**:

9. A proof placed *inside* the group of the functions it's about. With
   `mutual` blocks (option 1), writing `theorem evenTwo : even 2 = True` in
   the same block as `even` and `odd` is refused (`E-MUTUAL-SIGNATURE`): its
   signature mentions a sibling, and in any case `rfl` couldn't see `even 2`
   compute while `even` is opaque. With automatic grouping (option 2) it
   only lands in the group if `even` or `odd` calls it. Either way the fix
   is to keep it out of the cycle, which forward references make free.
10. Calls that only pass arguments along:

    ```
    ping : Nat -> Nat
    ping n = pong n               -- 0 ≤→ 0
    pong : Nat -> Nat
    pong n = ping n               -- 0 ≤→ 0
    ```
11. **Each call shrinks something, but not the same thing** — the trap for a
    naive "every call has some smaller argument" rule:

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
    `soundness/higher-order-recursion.sw`):

    ```
    walk : Forest -> Nat
    walk ts = applyTo walkForest ts      -- bare reference: no arcs
    walkForest : Forest -> Nat
    walkForest FNil         = 0
    walkForest (FCons _ ts) = walk ts
    ```
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

    `E-MUTUAL-SIGNATURE`.

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

- **The "declared later" rule**, now in *kernel* order: a field may mention
  group members (as types) and anything declared before the group, never a
  definition declared after the group's first member. With automatic
  grouping, kernel order is dependency order, so a definition the field uses
  (a type synonym, say) is always declared first, and one that mentions the
  data type is always declared after.
- **No occurrence through a definition.** `positive` doesn't unfold
  definitions, so `(p : Pred Tree)` with `Pred a = a -> Bool` is rejected,
  as it is today for a single type. (Unfolding would be needed to accept it;
  the Agda and Idris bugs above show the danger of getting this wrong.)
- **Nested occurrences** (`List Tree`) stay rejected. Lean translates them
  into extra mutual types [L2]; Agda [A4] and Rocq [R1] analyse how the outer
  type uses its parameter. Either is a separate proposal. The Idris bug
  #1771 [I4] shows what happens without the analysis.

### 7.2 Constructors that mention siblings

A field may mention a sibling *type*, but not a sibling's *constructors* (or
a `case` on one). For example `type T = Node (f : F) (ok : f = FNil)` is
refused (`E-MUTUAL-CONSTRUCTOR`, say): `FNil` doesn't exist yet while `T`'s
fields are checked, and allowing it is a step towards induction-induction.

### 7.3 Universes, parameters and elimination

- **Same parameters.** All members take the same parameters (same types, in
  order). Lean [L2] and Rocq [R1] both require this. It's what makes "applied
  to exactly its own parameters" meaningful for a sibling.
- **Same universe.** All members live in the same universe (Lean's rule
  [L2]; Rocq appears to allow a different sort per type [R1], going by its
  typing rule, **not verified** from an explicit statement). The field rule is unchanged: a field in `Type i` needs
  the data type in `Type j`, `i ≤ j`. With one universe for the group, a
  sibling field is always allowed. Relaxing this later breaks nothing.
- **`Prop` groups: no elimination into data.** Today a `Prop` type with at
  most one constructor whose fields are all proofs can be matched to
  produce data (subsingleton elimination). Lean's kernel switches this off
  for any mutual group of more than one type: "Mutually recursive inductive
  predicates only eliminate into Prop" [L4]. Adopt the same rule: it's
  conservative, and with no indices `Prop` groups are of little use anyway.
- **Matching** is per type and unchanged: a `case` on a `Tree` has one
  branch per `Tree` constructor. There are no eliminators to generate;
  recursion over the group is a function group (§6), and induction over it is
  a theorem group.

### 7.4 Exhaustiveness and `()`

Unchanged, per type.

### 7.5 Out of scope

- **Induction-recursion**: a type and a function on it defined together,
  where constructors use the function — the standard example is a universe
  `U` with `El : U -> Type` and a constructor `pi : (a : U) -> (El a -> U) ->
  U`. Its consistency needs a strong set-theoretic model (Dybjer & Setzer
  [D1]). Agda supports it [A1]; Lean and Rocq don't (**not verified** from
  an explicit statement). Rejected by the "declared later" rule and the
  mixed-group rule.
- **Induction-induction**: a type `A` and a family `B : A -> Type` defined
  together (contexts and types-in-context). Stitchwort has no indexed data
  types, so it can't even be written; the "no sibling constructors" rule
  (§7.2) blocks the nearest approximation. Theory: Nordvall Forsberg [D2].
- **Nested inductives** (`Rose = Node (List Rose)`): later, separately
  (§7.1).
- **Mutual abilities** (an ability whose operations mention a data type that
  mentions the ability): rejected. It would be Landin's knot (DESIGN.md §8),
  and the translated declarations would fail positivity anyway.

## 8. Interactions

### 8.1 Elaboration order, and things that depend on it today

With option 2, the elaborator first collects every top-level name
(definitions, data types and their constructors, abilities and their
operations), reporting duplicates, then builds the dependency graph from
the names each declaration mentions, then checks SCCs in dependency order,
breaking ties by source position (so checking order is deterministic and
matches source order whenever there's a choice). Within a group:
signatures first (in source order), then bodies; for data, parameters and
universes first, then constructors.

Three things in the elaborator depend on order today and need decisions:

- **Implicitly bound type variables.** An unknown lowercase name in a
  signature, used only where a type is expected, becomes an implicit
  parameter (`length : List a -> Nat`). "Unknown" currently means "not
  defined *so far*" (`autobind.rs` checks the name table as it stands). With
  whole-module scope, a definition named `a` anywhere in the file would turn
  every signature's `a` into a reference to it. **Proposal:** names in the
  module take priority (the simple, order-independent rule), and the
  elaborator warns when a module-level definition shadows what would
  otherwise be a type variable. **Open question** for the reviewer/user.
- **`auto` arguments and `==`** search for decision procedures among all
  definitions, trying the most recently defined first. With forward
  references, "defined" must mean "already checked"; a sibling in the same
  group can't be used anyway (it's opaque, so it can't run at compile time).
  **Proposal:** search only declarations that are *both already checked and
  earlier in the source*, most recent first. That's exactly today's
  behaviour, and moving code around can't silently change which proof is
  found. The cost is that a decision procedure must be written above its
  uses; the `E-AUTO-NONE` message should say so when one exists below.
- **Ability order in rows.** Rows are sorted by the order abilities were
  declared in. That order should be source order, assigned in the pre-pass,
  not checking order.

Hidden dependencies: elaboration inserts references the source doesn't
mention (prelude operators, `bind`, `translate`, decision procedures). The
prelude is a separate, earlier module, and decision procedures are limited
to already-checked declarations as above, so none of these can create a
cycle the pre-pass didn't see.

With option 1 (`mutual` blocks), only the first bullet changes, and only
inside a block.

### 8.2 Implicit arguments across a group

Every definition has a full signature, and signatures may not mention
siblings, so all signatures are elaborated (and their metavariables solved)
before any body. A body sees a sibling only through its finished type, so
no unification problem spans two members, and zonking stays per
declaration. This is the main reason the change is simpler here than in
Haskell, where binding groups exist for type inference [H1].

### 8.3 Error messages

- **Termination** names the cycle and each call:

  ```
  [E-TERMINATION] can't show that `f` and `g` terminate
    f (Succ x) y = g x (Succ y)      -- f passes a smaller first argument
    g x (Succ y) = f (Succ (Succ x)) y   -- g passes a smaller second argument
    = going round f → g → f, no argument gets smaller
  ```
- **An accidental cycle** (with automatic grouping) can be confusing: the user
  didn't mean `f` and `g` to be mutually recursive. The termination message
  shows the path, so the unintended call is visible.
- **A member fails to check**: every member stays opaque; later errors that
  only happen because a member is opaque should be avoided as today
  (the definitions stay in scope, without bodies).
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
3. The **group hash** covers `k` and each member in that order, with
   references to members hashed as `("member", index)`.
4. Each member's hash is `H("member", group hash, index)`, cached under the
   member's key as today.

A single self-recursive definition keeps today's `self` marker, so existing
hashes don't change.

Why tie-breaking by source order is safe: the hash must never be the *same*
for different content (that would reuse a wrong cached result). Hashing the
group's full content in some fixed order guarantees that whatever the order.
A different order for the same content only gives a different hash: a cache
miss, never a wrong hit. Canonical ordering is purely about cache hit rates
when code is moved around.

Every member's hash covers the whole group, so changing one member
invalidates the cached results of tests that use any member. That's
necessary: their behaviour may have changed.

### 8.5 Abilities

Effectful functions are ordinary functions into `Comp`, so effectful mutual
recursion is just mutual recursion (§6.5 example 7). The handler rules
(DESIGN.md §8, abilities.md) are enforced by positivity and termination
after translation, so the group versions are covered: a handler whose
clause calls back into the handler through a helper is a `≤`-only loop
(§6.5 example 15).

### 8.6 JavaScript

- **Order of emission.** JS emits definitions "in declaration order (which is
  dependency order)". With forward references that's no longer true, so
  emit in the kernel's order (SCC dependency order). Inside a group, any
  order works: `const even = (v0) => … odd(…) …` only looks `odd` up when
  called, after the whole module has run.
- **A pitfall:** a definition with no runtime parameters is emitted as a
  value computed when the module loads (`const f = …;`), unless its body is
  a case tree. A group member whose parameters are all erased (types or
  proofs) and whose body is a call to a sibling (`f p = g p`, with `g`
  matching on a subsingleton proof `p`) would then call `g` during module
  loading, before `g` is defined (a JS `ReferenceError`). **Rule:** every
  member of a recursive group is emitted as a function, even with no
  runtime parameters (as `absurd` already is). Not tested; it follows from
  reading `crates/js/src/lib.rs`.
- **Mutual tail calls aren't loops.** Only a function's tail calls to itself
  become loops. `even 100000` recurses 100 000 deep and throws a clean
  `StitchwortResourceError` (no wrong answer, as today for non-tail
  recursion). A later improvement: compile a group whose members tail-call
  each other into one loop with a "which function" variable, or use a
  trampoline (js_of_ocaml does the latter for mutual tail calls, per
  [stack-safe-evaluation.md](stack-safe-evaluation.md)). The kernel's own
  evaluator already has no problem: tail calls add no frames there.
- **Boundary types.** Exporting a function on `Tree`/`Forest` needs codecs
  for both; `collect_datas` already stops at types it has seen, so mutual
  references don't loop. The codecs' own recursion is being made iterative in
  a separate lane (JS boundary hardening); it should be tested with a mutual
  pair.

## 9. Trusted code

Everything in the elaborator (name pre-pass, SCC computation, `mutual`
parsing, error messages) is untrusted: the kernel re-checks. New or changed
trusted code:

| Where | What | Size (estimate) |
|---|---|---|
| `check.rs` | `define_group`: signatures don't mention siblings; bodies checked with all members opaque; atomic install | ~60 lines |
| `termination.rs` | Graph extraction for calls to any group member, with the new `≤` relation; "recursive function field" over the data group | ~80 lines changed |
| `termination.rs` | Composition, closure and the idempotent-loop check, with budget | ~120 lines, new |
| `check.rs` | Data groups: same parameters and universe; group-wide positivity; no sibling constructors; no subsingleton elimination for groups | ~60 lines |
| `hash.rs` | Cycle hashing | ~60 lines (trusted for cache correctness, not for proofs) |
| `crates/js` | Emission order; group members always functions | small (the extractor is trusted, DESIGN.md §13) |

The closure algorithm is the one genuinely new piece of trusted reasoning.
Agda #6059 [A5] (call matrices silently dropping elements) says it needs its
own unit tests, independent of the example programs: composition tables,
idempotence, and a randomised comparison against a brute-force search for
non-decreasing call sequences on small groups.

## 10. Staging

1. **Kernel: function groups and size-change termination.** `define_group`
   and the new checker, used at first only for *single* definitions (a group
   of one). This alone lets Ackermann and swapped arguments through, and
   exercises the closure code with today's whole example suite. Hashing is
   unchanged for groups of one.
2. **Surface: forward references and function groups** (option 2, or option
   1's `mutual`), with cycle hashing and the JS emission rules. Adds
   examples 1–3, 5–16 to the suites.
3. **Data-type groups**: kernel checks, then elaborator support. Adds
   `Tree`/`Forest` and `Bad1`/`Bad2`.
4. **Later, separately:** nested inductives (via translation to mutual
   groups, as Lean does, or a variance analysis); mutual tail calls as loops
   in JS; `decreasing` measures (DESIGN.md §5) for a group.

Each stage is useful on its own, and stage 1 has no surface change at all.

## 11. Recommendation

- **Option 2: order-independent modules.** Every top-level name is visible
  throughout its module; the elaborator groups declarations into strongly
  connected components and checks them in dependency order. Things whose
  meaning depends on order today (`auto` search, ability order) keep source
  order; implicitly bound type variables need a decision (§8.1).
- **The kernel checks explicit groups**: all signatures first (none may
  mention a sibling), then all bodies with every member opaque, then
  termination for the group, then all bodies installed at once.
- **Size-change termination** for groups (and single definitions), extending
  today's analysis with a "same size" relation. Every call between any two
  members is analysed.
- **Data-type groups** with the same parameters and universe, group-wide
  strict positivity, no sibling constructors in fields, and no elimination
  into data for `Prop` groups. Nested, inductive-recursive and
  inductive-inductive types stay out.
- **Cycle hashing** as DESIGN.md §11 already promises, with deterministic
  tie-breaking.
- **Stage it** as in §10, kernel first.

If the reviewer prefers less change at once, the fallback is option 1
(`mutual` blocks) with criterion R. Both are subsumed by the recommendation,
so nothing written under them breaks if it's adopted later.

## 12. Questions for the reviewer

1. **The termination argument (§6.3).** Is the size-change criterion sound
   for *this* kernel: strict evaluation, case trees, refinement of the
   context in branches, `Prop` with subsingleton elimination, and recursive
   function fields (infinitely branching data, not covered by [S3])? Is the
   "conversion still terminates" argument (unfold only when a case can step)
   adequate for groups?
2. **The `≤` relation.** Is it sound to treat a constructor rebuilding the
   parameter (`Succ n` where the parameter was matched as `Succ n`) as `≤`,
   given that inside the branch the parameter *evaluates* to that
   constructor value?
3. **Partial application.** Today a partially applied self-call keeps the
   relations for the arguments it supplies, and the closure may be called
   later from anywhere (even after the caller returns). Is the call-graph
   argument still valid for such delayed calls, or should group members be
   required to be fully applied?
4. **Signatures mentioning siblings** are refused (as in Lean). Is anything
   important lost?
5. **Same universe for a data group** (Lean) versus per-type sorts (Rocq):
   any reason to prefer Rocq's rule here?
6. **No subsingleton elimination for `Prop` groups** (Lean's kernel): needed
   for soundness, or just conservative? (We'd keep it either way.)
7. **Hashing:** is tie-breaking by declaration order acceptable given that
   identity only matters for caching here?
8. **Implicitly bound type variables under whole-module scope** (§8.1):
   module names take priority, plus a warning. Acceptable?
9. **Criterion R first?** Is there a reason to prefer the smaller criterion
   R for the first implementation, despite rejecting wrappers?

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
  soundness work were not read.
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
  Recursion*, JFP 12(1), 2002 (foetus).
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
