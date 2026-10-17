# Proposal: syntax conveniences (`where`, `match`, patterns in `let` and lambdas, tuples)

**Status:** draft 2, 17 October 2026. Design only: nothing here is built.
The user agreed with every recommendation of draft 1 (§8); an external
reviewer then reviewed draft 1, and draft 2 adopts that review in full
(the [Review response](#review-response) maps each finding to where it's
addressed). It answers `TODO.md`'s "Syntax conveniences" item and row 7 of
[aoc-2025.md §10](../aoc-2025.md#10-capabilities-stitchwort-needs-prioritised),
whose evidence is items 4 to 6 of
[aoc-2025.md §9](../aoc-2025.md#9-friction-found-while-writing-the-five-programs).
Item 3 there (`else` at the start of a line) is already fixed
([syntax.md, "`if` across lines"](../syntax.md#layout)).

This note is meant to be read without knowing the codebase. §1 describes the
parts of Stitchwort it touches, checked against the source at commit
`00e769a` (namespaces stages 0 to 2, including dot notation, are merged).
Claims about other languages cite their sources ([Sources](#sources));
anything not checked against a source is marked **unverified**.

**The one-sentence version of draft 2:** every convenience here is
translated into ordinary definitions that the existing kernel checks with
no exemptions, and the hard part is not the kernel but saying precisely
which outer variables a helper needs, in which order helpers are admitted,
what type a `match` gets, and how a speculative type comparison is undone.
Draft 1 called these "just sugar" without pinning those down; draft 2 pins
them down.

## Contents

0. [Summary](#0-summary)
1. [Background: what the compiler does today](#1-background-what-the-compiler-does-today)
2. [Lifting: the shared machinery](#2-lifting-the-shared-machinery)
3. [`where` clauses and local functions](#3-where-clauses-and-local-functions)
4. [`match` expressions](#4-match-expressions)
5. [Patterns in `let` and in lambdas](#5-patterns-in-let-and-in-lambdas)
6. [Tuples](#6-tuples)
7. [Knowing more expected types (result type first)](#7-knowing-more-expected-types-result-type-first)
8. [Implementation plan](#8-implementation-plan)
9. [Questions for the user](#9-questions-for-the-user)
- [Review response](#review-response)
- [Sources](#sources)

## 0. Summary

Five changes, all in the parser and elaborator. **None changes the kernel**
(the small trusted checker). One, pairs as arrays at the JavaScript
boundary, changes the **trusted boundary contract**, and is specified as a
separate change of its own (§6.3).

| Feature | Example | How it's built |
|---|---|---|
| `where` | `solve ls = go 0 ls` / `where go : …` | each local function becomes a top-level definition, `solve.go`, taking the outer variables it needs as extra arguments ("lambda lifting", §2) |
| `match` | `match xs with \| Nil -> 0 \| Cons x _ -> x` | in tail position on a variable: more splitting in the enclosing case tree. Otherwise a generated top-level definition with one equation per alternative (§4) |
| pattern `let` | `let (q, r) = divMod n 7` | a `match` with one alternative; the pattern must cover its whole type (else `E-LET-REFUTABLE`) |
| pattern lambda | `\(a, b) -> a + b` | `\p -> let (a, b) = p` … |
| tuples | `(Nat, Text)`, `(1, "a")`, `(a, b, c)` | `Pair`, `MkPair`; three or more nest to the right |
| result type first | `maybeThen m (\x -> Just { dir = TL, amount = n })` checked against `Maybe Rot` | compare the application's result type with the expected type before checking its arguments, as a transaction with one fallback (§7) |

**The guarantee lifting gives** (review finding 1): *lifting preserves the
kernel's ordinary obligations; generated declarations and every call
between them are checked by the kernel with no exemptions.* In particular
there is no rule saying "generated helpers terminate". A lifted helper is
an ordinary function with extra parameters, and the size-change checker
sees the actual calls. That captured arguments are passed unchanged is
useful information to the checker (it records "equal"), but it isn't a
termination argument on its own: an unchanged argument also describes a
loop that never gets smaller. §4.5 has the test pair that shows the
difference.

Order (unchanged, the user's decision): tuples, then result type first,
then `match`, then pattern `let` and lambdas, then `where` (§8).

## 1. Background: what the compiler does today

File references are to the source at `00e769a`.

- **The kernel only allows a pattern match at the top of a definition.**
  A definition's body is a *case tree*: a nest of `Case` nodes, each
  splitting a variable in scope at that point (a parameter, or a field
  matched out by an earlier split) by constructor, with ordinary
  expressions at the leaves. A `Case` can't appear inside a lambda or as an
  argument (`crates/core/src/check.rs`, `case_only_in_tree`). There's no
  `let` in the core language either. So a `match` in the middle of an
  expression can't become a kernel `Case` in place; at a leaf of the tree,
  on a variable, it can (§4.3).
- **Pattern matching refines types by substitution.** When the tree splits
  `xs` into `Cons y ys`, the compiler replaces `xs` by `Cons y ys` in the
  goal and in the types of the other variables (`crates/elab/src/lib.rs`,
  `check_tree`). Data types have parameters but no indices, so there's no
  index unification.
- **The pattern compiler works on any context.** `compile` (`lib.rs`) takes
  the de Bruijn levels of the values each column matches, so it can split
  any variable in scope; `check_tree` checks the result against a goal.
- **The compiler already generates top-level definitions** with names
  source can't write: an ability's constructors and eliminator
  (`State.%get`, `State.%res`, `State.%elim`), a record's constructor
  (`Person.%mk`), and a partial group's `f.Request`, `g.recur` and others
  ([namespaces.md §9, "As built"](namespaces.md#9-staging)). The `%`
  marks a generated name.
- **The kernel admits definitions in two steps** (`check.rs`):
  `declare_def` checks a signature, which may refer only to *final*
  declarations, and makes the definition *pending*; `define_group` checks
  the bodies of a group of pending definitions together and makes all of
  them final, or (on any error) all of them failed.
- **Termination is checked by the kernel**, per group
  (`crates/core/src/termination.rs`, size-change graphs in `sct.rs`). An
  argument counts as smaller only when it's a field matched out of a
  parameter. Inside a group, every use of a member must have all its
  arguments (`E-TERMINATION`, "used here without all its arguments").
- **Groups are found before elaboration** (`crates/elab/src/module.rs`): a
  syntactic pre-pass computes each declaration's references and splits the
  module into strongly connected components (groups that call each other).
  For a group, all signatures are elaborated, then all bodies, then the
  kernel admits them with one `define_group`. A signature may not mention
  a member of its own group (`E-MUTUAL-SIGNATURE`). Metavariables
  (unknowns) and pending `auto` obligations are per body: `clear_metas`
  empties both before each body.
- **`let x = e` is a function applied to `e`**, `(\x -> body) e`, so `x` is
  computed once but is *opaque* in types.
- **Checking is bidirectional.** An application whose head isn't a
  constructor is *inferred* and its type compared with the expected one at
  the end (`check.rs`, `fallback`).
- **The unifier is not atomic on failure** (verified, §7.3): `unify`
  (`crates/elab/src/unify.rs`) solves metavariables in place as it walks
  the two types left to right and returns "no" without undoing them. The
  `auto` search already has an undo for this (`auto.rs`, `attempt`, which
  copies the metavariable table and restores it on failure).
- **Parser and lexer:** `case`, `of` and `match` aren't keywords; `where`
  is, but only `ability … where` uses it. `(a, b)` is a parse error. A
  qualified name is one token only after an uppercase component
  (`List.map`, `Geometry.Shape.area`); after a lowercase component, `.` is
  dot notation (`crates/syntax/src/lexer.rs`). So `sumTo.go` today parses
  as `sumTo` followed by `.go`, which dot notation looks up in the
  namespace of `sumTo`'s *type* (`crates/elab/src/dot.rs`).
- **JavaScript** (`crates/js/src/lib.rs`): each top-level definition is a
  curried JS function named by `def_name`, which applies the injective
  encoder `encode` to the full name (`.` → `$d`, `%` → `$g`, `'` → `$p`).
  A definition whose case tree calls *itself* in tail position becomes a
  loop (`self_tail_loop`); calls between different definitions are
  ordinary JS calls, even in tail position. A data value is
  `{ tag: "Ctor", field: … }`, so a pair is `{ tag: "MkPair", fst, snd }`
  inside the generated code and at the export boundary.

## 2. Lifting: the shared machinery

`where` functions and non-tail `match`es both become generated top-level
definitions ("helpers"). This section specifies the parts they share; §3
and §4 add what's particular to each.

### 2.1 Capture: which outer variables a helper takes

A helper is elaborated in the context it was written in, then *lifted*:
the outer variables it needs become extra leading parameters, and every
use passes them. "Needs" is defined on **elaborated** terms, by
**variable identity** (the variable's position in the context, its de
Bruijn level), never by spelling, so shadowing and repeated names can't
change which binding is captured.

The capture set `C(d)` of a local declaration `d` is the **smallest** set
of outer variables closed under these four rules (review finding 2):

1. **Direct uses.** Every outer variable free in `d`'s elaborated
   signature and body, after the metavariables solved so far are
   substituted in. This includes the inferred result type of a `match`,
   implicit arguments the elaborator inserted, and `auto` evidence it
   found: those are part of the elaborated term, so a scan of the
   elaborated term sees them even though the source doesn't mention them.
2. **Types of captures.** If `v` is in `C(d)`, every outer variable free in
   `v`'s type is too. (Capturing `ok : i < length xs` captures `i` and
   `xs`.)
3. **Local helpers called.** If `d` refers to another local helper `d'`,
   then `C(d') ⊆ C(d)`, because the translated call `owner.d' c₁ … cₖ`
   must pass `d'`'s captures.
4. **Values used.** A `where` value (§3.4) is an outer variable like any
   other; using it captures it, and rule 2 then captures what its type
   mentions.

For helpers that call each other, rule 3 makes the sets depend on each
other, so they're computed together as a **fixed point**: start from rules
1 and 2 for each helper, then repeatedly add the captures of the helpers
each one calls (and the variables their types mention), until nothing
changes. This always stops, since the sets only grow and are bounded by
the context. Only then are the lifted signatures, and so the arities,
fixed.

The review's example:

```
outer : Nat -> Nat
outer offset = first 0
  where
    first : Nat -> Nat
    first x = second x

    second : Nat -> Nat
    second x = offset + x
```

`C(second) = {offset}` by rule 1; `first` calls `second`, so by rule 3
`C(first) = {offset}` too, although `first` never mentions `offset`. The
result:

```
outer.first : Nat -> Nat -> Nat
outer.first offset x = outer.second offset x
outer.second : Nat -> Nat -> Nat
outer.second offset x = offset + x
outer offset = outer.first offset 0
```

**Order of the captured parameters:** by context position (the order the
variables were bound). The context is already a telescope (each variable's
type mentions only earlier ones), so this order is always well formed.
§4.4 refines this for a `match`, whose scrutinee may be generalised.

**Implicit and `auto` captures keep their kind** in the helper's
signature (an implicit `[a : Type]` stays implicit, `[auto h : P]` stays
`auto`), so a user writing `sumTo.go` from outside (§3.6) fills them in as
usual. But **every generated call passes them explicitly**, as the
captured variable itself: `outer.go [a := a] [h := h] …` in effect. A
generated call never searches for evidence again, because a new search
could choose a different proof or decision procedure than the one in
scope (review finding 2).

**Captures are only what's used** (the user's decision 4). Lemmas about
`f.go` may need updating when `go` starts using another outer variable.

### 2.2 Generated declarations: when each one is admitted

Discovering a helper is not the same as admitting it (review finding 3).
Admission follows the kernel's existing rules (§1: a signature may refer
only to final declarations; a group is admitted all at once), and a
helper joins its owner's group **only if it's actually in a cycle with
it**.

Each declaration being elaborated (the *owner*: a top-level definition, or
the group of them the pre-pass found) goes through these steps:

1. **Collect.** While elaborating the owner, each helper is recorded as a
   *draft*: its key (§2.4), its elaborated context, its type and body (or
   equations), its source span, and the declarations it refers to. A
   draft is not yet known to the kernel.
2. **Resolve.** Compute the captures (§2.1) and rewrite every reference to
   a draft into the lifted call. Substitute solved metavariables; an
   unsolved one in a draft's type or body is `E-CANNOT-INFER` at the
   draft's span, as for any definition.
3. **Order.** Compute dependencies across the owner's members and the
   drafts together: an edge from each to everything it refers to. Split
   them into strongly connected components.
4. **Admit in dependency order**, each component through the existing
   path: `declare_def` for each signature, then one `define_group` for the
   component. A component containing an owner member is the owner's
   group, extended with the drafts in its cycle. The existing checks
   apply unchanged: `E-MUTUAL-SIGNATURE` if a signature mentions a pending
   member of its own component, saturation inside a group, termination for
   the whole component.

Two cases need a helper to be **final before the owner is even
elaborated further**, and they're why steps 1 to 4 run in more than one
place rather than once at the end:

- **A `match` in a signature** (`f : (n : Nat) -> match n with …`). The
  helper must be final before `f`'s signature can be declared, since a
  signature may only refer to final declarations. So steps 1 to 4 run as
  soon as the signature is elaborated: the helper is admitted on its own
  (it can't refer to `f`, which isn't declared yet; if it tries, that's
  `E-MUTUAL-SIGNATURE`, as for any signature mentioning a member of its
  own group), then `f`'s signature is declared.
- **A `where` block with a lemma about a local function.** A lemma about
  `go` needs `go` final, so that its type can compute with `go` unfolded.
  So a `where` block is processed in its own dependency order (§3.3): each
  local component that doesn't reach the owner is elaborated and admitted
  immediately, before the next local component and before the owner's
  right-hand side. A local component that does call the owner stays a
  draft and joins the owner's group at the end.

Everything else (a `match` in a body, local functions in a cycle with the
owner) is admitted at the end of the owner's body, after its
metavariables are solved.

**Failure part-way.** If any step fails, the owner fails, with that error.
Helpers already admitted stay in the kernel's table as final definitions
(the kernel can't un-admit; they were fully checked, so this is harmless),
but **no helper's name is bound in the module's scope until its owner is
final**. While the owner is elaborated, `go` resolves to its draft or its
admitted definition through the equation's local scope only. So a failed
owner leaves nothing usable from outside: `f.go` from another declaration
reports `f` as failed, exactly as `f` itself would. If the owner's
`define_group` fails, the kernel marks every pending member failed,
including the drafts that joined the group.

**The module pre-pass** (§1) needs only small changes: references inside
a `where` block count as references of the owner (so a local `go` that
calls the top-level `h` makes the owner depend on `h`); a written
`f.go` from another declaration is a certain edge to `f`; and helpers are
never targets of dot notation's speculative edges (§3.6).

This is the shape Lean describes: local definitions are first lifted into
the enclosing elaboration block, after which the actually recursive groups
are identified and processed separately [L1].

### 2.3 What lifting does to calls

- **A saturated call stays saturated.** A source call `go a b` with all of
  `go`'s arguments becomes `owner.go c₁ … cₖ a b`, also with all its
  arguments.
- **A function value stays a function value.** `map go xs` becomes
  `map (owner.go c₁ … cₖ) xs`: the captures are applied, `go`'s own
  parameters aren't. If `go` is in a cycle with the owner, the kernel's
  saturation rule refuses this (`E-TERMINATION`, "used here without all
  its arguments"), exactly as it would refuse the same program written
  with top-level definitions. If `go` only calls itself, it's in its own
  group, and the use is fine. Lifting never makes a program pass or fail
  this rule differently from its top-level equivalent (review finding 8).
- **JavaScript:** a direct call needs no environment object, since the
  captures are ordinary arguments. But a partially applied helper, like
  `owner.go c₁ … cₖ` passed to `map`, is a JS closure for the remaining
  arguments, as any partial application of a curried function is. So the
  claim is "no environment object is built for a direct call", not "no
  closures" (draft 1 overstated it).

### 2.4 Names

- **A `where` function's key** is the owner's key followed by its name:
  `sumTo.go`, `Geometry.Shape.area.go`. Its kernel path follows the same
  rule as other definitions' paths.
- **A `match` helper's key is unspellable**: `sumTo.%match1`,
  `sumTo.%match2`, …, numbered in source order within the owner (so edits
  elsewhere in the file don't renumber them). The `%` puts them in the
  namespace lane's space of generated names (`State.%res`), so a user's
  local function named `match1` (`sumTo.match1`) can't collide with one.
  The number is display and identity metadata, never something source can
  refer to.
- **Nested helpers** extend the key: a `match` inside `sumTo`'s local `go`
  is `sumTo.go.%match1`.
- **JavaScript names** come from the existing `def_name`/`encode` (§1):
  dots become `$d` and `%` becomes `$g`, injectively. This note doesn't
  prescribe a spelling of its own (draft 1's "`$$`" was the encoding before
  namespaces).
- **Hashes:** a helper is hashed like any definition. Editing `solve` may
  change `solve.go`'s captures and so its hash; hash-stability tests should
  include a `where` and a `match`.

How a user *writes* `f.go` is in §3.6, alongside dot notation.

### 2.5 Error messages

- Inside the owner, errors name the helper as the user wrote it: "`go`, in
  `solve`'s `where` block", or "this `match`". The key `solve.%match1` is
  never shown.
- **Captures are hidden only when they really are the original
  bindings**: when printing a term in the owner's equation context, a
  lifted call `solve.go c₁ … cₖ a b` whose capture arguments are exactly
  the captured variables themselves (same identities) is printed `go a b`.
  Anywhere else (outside the owner, or where some capture argument is
  something else, as after a pattern match substituted it), the full call
  and the helper's full type are printed, so the user sees something they
  could write (review finding 10).
- Spans point at the original source, which the generated equations keep.

## 3. `where` clauses and local functions

### 3.1 Syntax

A `where` block follows an equation, indented, and holds local
declarations, indented further:

```
solve : List Text -> Nat
solve ls = go 0 ls
  where
    go : Nat -> List Text -> Nat
    go acc Nil         = acc
    go acc (Cons l ls) = go (acc + score l) ls

    score : Text -> Nat
    score l = textLength l * weight

    weight = 3
```

**Allowed in a `where` block** (review finding 7: an explicit list, not
"anything allowed at top level"):

| Form | Example | Notes |
|---|---|---|
| a function: signature and equations | `go : Nat -> Nat` / `go 0 = …` | a signature is required (`E-WHERE-SIGNATURE`) |
| a plain value, with or without a signature | `weight = 3`, `limit : Nat` / `limit = n * 2` | §3.4 |
| a `theorem`: signature and equations | `theorem goAcc : …` | may capture outer variables, like a function |
| a `test` | `test go 3 0 == 6` | only when closed after elaboration (§3.5) |

**Not allowed**, each `E-WHERE-FORM` naming the form: `type` (data,
records), `ability`, `import`, `export`, a nested `where` inside a local
function's equation (a later addition if wanted), and a qualified name
(`go.x`, `Std.go`). Pattern bindings at the start of a `where`
(`(a, b) = …`) aren't proposed (§5.2).

Scoping:

- **It belongs to one equation** and sees that equation's variables:
  parameters, pattern variables and named implicit parameters. In
  `f (Cons x xs) = … where …`, the block can use `x` and `xs`. This is the
  rule in Haskell [H1, §4.4.3], Agda [A2] and Idris 2 [I1].
- **It can't see the equation's `let`-bound names** (they're bound later,
  inside the body).
- **Order doesn't matter** inside the block, as at top level.
- **A signature may mention outer variables**, including dependently:
  inside `get (xs : List a) (i : Nat)`, a local
  `check : (j : Nat) -> j <= i -> Bool` is fine.
- **A lowercase name in a local signature that's already in scope means the
  outer thing.** In `go : List a -> Nat` inside a function over `List a`,
  `a` is the outer `a`, not a fresh type variable (Haskell's default is the
  opposite, a known trap; the rule is in GHC's user guide [H2]). A name not
  in scope is bound automatically, as today.
- **Names are unique within the whole definition** (the user's decision
  2): two equations can't each have their own `go` (`E-DUPLICATE`).

### 3.2 What it means

Each local function is lifted (§2): `solve.go`, `solve.score`, with
captures computed by §2.1 and admitted by §2.2.

```
-- written
index : (xs : List a) -> (target : a) -> (eq : a -> a -> Bool) -> Maybe Nat
index xs target eq = go 0 xs
  where
    go : Nat -> List a -> Maybe Nat
    go i Nil         = Nothing
    go i (Cons y ys) = if eq y target then Just i else go (i + 1) ys

-- what the compiler makes of it
index.go : [a : Type] -> (target : a) -> (eq : a -> a -> Bool) -> Nat -> List a -> Maybe Nat
index.go target eq i Nil         = Nothing
index.go target eq i (Cons y ys) = if eq y target then Just i else index.go target eq (i + 1) ys

index xs target eq = index.go [a := a] target eq 0 xs
```

Captures are computed after the equation's patterns are known: in
`f (Cons x xs) = …`, the context holds `x` and `xs`, not the original
argument, because matching substituted it.

### 3.3 Order of elaboration inside a block

1. The equation's patterns are compiled, giving its context.
2. The block's declarations get a dependency graph of their own (which
   local names each refers to, plus an edge to the owner if it refers to
   the owner or to anything in the owner's group). It's split into
   components.
3. Components are processed in dependency order (source order breaks
   ties). A component that doesn't reach the owner is elaborated, lifted
   and admitted right away (§2.2), so later components, including lemmas
   about it, see it final. A component that reaches the owner is elaborated
   and lifted, and stays a draft until the owner's group is admitted.
4. Plain values become `let`s (§3.4), and the right-hand side is
   elaborated.

### 3.4 Plain values

A plain value (`weight = 3`, no parameters) is **not** lifted. It becomes a
`let` at the start of the equation's right-hand side, so it's computed
once per call of the equation (the user's decision 3), and is opaque in
types like any `let`. A value that must compute in types can be a function
of `()` or move to top level.

**Cycles** (review finding 7). A value can't be initialised by a cycle
that leads back to it, including a cycle through a local function:

```
outer n = cached
  where
    cached = helper n

    helper : Nat -> Nat
    helper x = cached
```

Lifting `helper` would make `cached` one of its arguments, so computing
`cached` would need `outer.helper cached n` before `cached` exists. Rule:
**any cycle in the block's dependency graph that contains a plain value is
`E-WHERE-RECURSIVE-VALUE`**, naming the cycle (`cached → helper →
cached`). That covers a value mentioning itself directly. Cycles made only
of functions are ordinary mutual recursion (§3.5).

**Evaluation order.** The values' `let`s are placed in dependency order
(a value after the values and functions it uses), with source order
breaking ties, so the order is deterministic. They're placed at the leaf
of the owner's case tree for that equation, so they run **after the
equation has been selected, once per call of the owner**, and never once
per use or once per call of a lifted helper (a helper receives the value
as an argument). In an effectful owner, an initialiser may perform the
owner's abilities, and does so in that order, before the right-hand side.

### 3.5 Recursion, termination, abilities, tests

- **Recursion and mutual recursion are allowed**, among local functions
  and between a local function and the owner (Lean allows both [L1]); §2.2
  decides the groups. `go` calling only itself is its own group, admitted
  before the owner; `go` calling the owner back joins the owner's group.
- **Termination**: the kernel checks the lifted calls with no exemption
  (§0). A captured variable is passed unchanged, which the size-change
  checker records as "equal", so it never spoils a decreasing argument; a
  local function recursing on a field of a captured variable works,
  since the captured variable is an ordinary parameter of the lifted
  definition.
- **The group rules apply as written** in
  [syntax.md](../syntax.md#declaration-order), with §2.3's statement of
  saturation.
- **`Partial`**: a local function can be partial
  (`go : Nat -> {Partial} Nat`) if the owner is too, or if it isn't in a
  cycle with the owner. A group mixing partial and total members is
  `E-PARTIAL-MIXED`, as today. Captures are passed unchanged, which the
  partial translation's uniformity rule (`E-PARTIAL-NONUNIFORM`) wants.
- **Abilities**: a local signature may list abilities; the owner's row
  variable (`e` in `{State Nat | e}`) is captured like a type variable when
  the local signature mentions it.
- **Local `test`** (review finding 7): allowed only when it's **closed
  after elaboration**, i.e. its capture set (§2.1) is empty. It then runs
  as an ordinary top-level test, after its owner is final. A test that
  captures a parameter (`test n == 0` inside `f n`) is
  `E-WHERE-TEST-OPEN`: it can't run once, since `n` stands for every
  number, and running it on each call would add runtime assertions, which
  is a different feature. A fact about every `n` is a local `theorem`.

### 3.6 Proofs, `f.go`, and dot notation

**Inside the owner**, a local lemma can state facts about a local function
and be used by the owner's right-hand side:

```
sumTo : Nat -> Nat
sumTo n = go n 0
  where
    go : Nat -> Nat -> Nat
    go 0        acc = acc
    go (Succ k) acc = go k (acc + Succ k)

    theorem goAcc : (k a : Nat) -> go k a = go k 0 + a
    goAcc … = …
```

`go` doesn't call the owner, so it's admitted first (§3.3) and the lemma's
type computes with `go` unfolded. A lemma that `go` itself uses can't
mention `go` in its type (that would put the lemma's signature in `go`'s
cycle: `E-MUTUAL-SIGNATURE`).

**Outside**, a top-level theorem can name the lifted function:

```
theorem sumToGo : (k a : Nat) -> sumTo.go k a = sumTo.go k 0 + a
```

`go` captures nothing here, so `sumTo.go` has just `go`'s own parameters.
In general the captures come first, explicit ones written, implicit and
`auto` ones filled in (§2.1). This is how Lean works (`where` functions are
ordinary constants `f.go`; **unverified** against the reference text,
which the fetch tool cut short, but it's the documented behaviour of
`where` in *Functional Programming in Lean*). `stitchwort` should be able
to print a helper's full type (a small `show` addition).

**How `f.go` is resolved** (review finding 10, coordinated with
namespaces as built). The lexer reads `sumTo.go` as `sumTo` followed by
`.go`, the same tokens as dot notation (§1). Dot notation today looks for
`go` in the namespace of the receiver's *type*; for a function `sumTo :
Nat -> Nat` that type has no namespace, so `sumTo.go` is an error today
(`E-NO-NAMESPACE`). The rule adds one step before dot notation:

> In `x.go`, if `x` (a bare name, or a qualified name like
> `Geometry.Shape.area`) resolves, by the usual levels of
> [namespaces.md §4.4](namespaces.md#44-what-a-short-name-means), to a
> **top-level definition** (not a local variable), and that definition has
> a local function `go`, then `x.go` is that local function. Otherwise it's
> dot notation, as today.

- A **local variable** `x` always means dot notation, since level 1
  (local binders) never resolves to a top-level definition.
- **Nothing that works today changes meaning**: the new step only applies
  when `x` is a top-level definition with a local `go`, and the program
  could only have used `x.go` as dot notation if `x`'s type has a
  namespace with a `go`. In that rare case (a nullary `x : Shape` with
  both a local `go` and `Shape.go` existing) the local function wins, and
  the dot-notation meaning stays writable as `Shape.go x`. The local
  function has no other spelling, which is why it wins.
- **Helpers are never found by dot notation.** A type-valued definition
  (`PairType : Type`, `PairType = (Nat, Text)`) owns a namespace for dot
  notation's nickname view; its local functions must not appear in it.
  The pre-pass's speculative edges for `.go` likewise skip helper keys,
  so a `where` doesn't create spurious cycles.
- **Declarations can't collide with helper keys.** A declaration's name
  can't have a lowercase qualifier (the lexer splits it), so no source
  declaration is called `sumTo.go`. A definition with an uppercase name
  can: `PairType.go` is one token, and a top-level declaration
  `PairType.go` next to a definition `PairType` with a local `go` is
  `E-DUPLICATE` (checked in `scope.rs` when the owner's local names are
  reserved, before elaboration).
- `match` helpers (`f.%match1`) are never nameable.

## 4. `match` expressions

### 4.1 Syntax

```
describe : List Nat -> Text
describe xs =
  match xs with
    | Nil        -> "empty"
    | Cons x Nil -> "one"
    | _          -> "many"
```

- `match e with` followed by alternatives `| pattern -> expression`, lined
  up like a handler's clauses (the user's decision 1). On one line:
  `match xs with | Nil -> 0 | Cons x _ -> x`.
- **Several scrutinees**: `match a, b with | Zero, _ -> … | Succ m, Zero -> …`.
- **Naming the equation**: `match h : e with` (the user's decision 5, §4.6).
- **Patterns** are the equation patterns: constructors, variables, `_`,
  numbers, records, tuples (§6), `()`.
- `match` and `with` become keywords.

There are two translations. The first applies whenever it can, because
it's simpler and better at run time; the second is general.

### 4.2 Which translation

A `match` is compiled **into the enclosing case tree** (§4.3) when all of
these hold:

1. it's the **whole right-hand side** of an equation, or the whole
   right-hand side of an alternative of a `match` that is itself compiled
   this way;
2. every scrutinee is a **variable of the equation**: a parameter, a
   pattern variable, or a named implicit parameter (not a `let` or `where`
   value: those are bound by a `let`, which isn't part of the tree);
3. no scrutinee has a named equation (`h :`);
4. the equation has no `where` values (their `let`s come before the
   right-hand side, so the `match` isn't at the tree's leaf; local
   *functions* are fine).

Otherwise it's **lifted** into a helper (§4.4).

### 4.3 Compiled into the enclosing case tree

The alternatives are given to the existing pattern compiler as more
splitting at the equation's leaf: `compile` with the scrutinee variables'
levels as its columns, then `check_tree` against the equation's goal. The
result is exactly the tree the user would get by writing the patterns in
the equation itself, and the kernel checks it as such. No helper is
generated, so there's no motive to infer: refinement is the existing
substitution (§1).

```
theorem appendNil : (xs : List a) -> append xs Nil = xs
appendNil xs =
  match xs with
    | Nil       -> rfl
    | Cons y ys -> cong (Cons y) (appendNil ys)
```

compiles to the same tree as the two equations `appendNil Nil = rfl` and
`appendNil (Cons y ys) = …`. In the `Cons` branch the goal is
`append (Cons y ys) Nil = Cons y ys`.

This also settles review finding 8's tail-call concern for the common
case: `count n = match n with | Zero -> 0 | Succ k -> count k` is one
definition calling itself in tail position, which the JS generator's
`self_tail_loop` makes a loop, exactly as for equations.

### 4.4 Lifted into a helper

```
-- written, inside  f : (n : Nat) -> List Nat -> Nat
f n xs = 1 + match xs with
               | Nil      -> n
               | Cons x _ -> x + n

-- made
f.%match1 : Nat -> List Nat -> Nat
f.%match1 n Nil        = n
f.%match1 n (Cons x _) = x + n

f n xs = 1 + f.%match1 n xs
```

The helper takes its captures (§2.1) and its scrutinees, and has one
equation per alternative, compiled by the existing pattern compiler, so
exhaustiveness (`E-NONEXHAUSTIVE`), number and record patterns, `()` and
the `E-PROP-ELIM` rules are reused unchanged. This is what Lean does
("auxiliary matching functions") [L2] and Idris 2 does for `case` [I2].

**The helper's type** is a telescope (a list of parameters, each type
allowed to mention earlier ones) followed by a result type, the *motive*.
It's built by one rule (review finding 4):

> Build a **well-formed telescope** containing the captures and the
> scrutinee parameters, **ordered by type dependencies**, keeping the
> original order wherever the dependencies allow. Then check the result as
> a type, and check that the helper's type, instantiated with the actual
> captures and scrutinees, matches the original expected type.

Concretely:

1. **Variable scrutinees** (`match xs with`, `xs` an equation variable)
   aren't generalised: `xs` is simply one of the captures, at its own
   position, and its alternatives split that parameter. Anything whose
   type mentions `xs` was bound after `xs` in the context (the context is
   a telescope), so it's already after `xs` in the helper's parameters, and
   the pattern compiler refines its type when `xs` is split. With
   `n : Nat` and `q : P n` in scope, a `match n` that uses `q` gets
   `(n : Nat) -> (q : P n) -> R n`, and matching `n` refines both `q`'s
   type and the result.
2. **Expression scrutinees** (`match length xs with`) get a new parameter
   `s`. Occurrences of the expression in the expected type and in the
   captures' types are replaced by `s` (the *occurrence test*, below). `s`
   is placed after every capture its own type mentions; a capture whose
   type contained a replaced occurrence moves after `s`; everything else
   keeps its context order. If that's impossible (a cycle: `s`'s type
   needs `q`, `q`'s type now needs `s`), it's `E-MATCH-MOTIVE`.
3. The motive is checked as a type, and the helper's instantiated type is
   compared with the expected type (by the ordinary conversion check). If
   either fails, it's `E-MATCH-MOTIVE`, at the `match`. **A motive is never
   accepted just because each branch happened to check**: the helper's
   type is checked first, and the branches against it.

**The occurrence test** (draft 1 left this unspecified). First, solved
metavariables are substituted in. Then a subterm is an occurrence of the
scrutinee `e` exactly when it is **syntactically the same elaborated
term** (same definitions, same variables, same implicit arguments), with
no unfolding of definitions and **no solving of metavariables**. An
unsolved metavariable is never an occurrence, and the test never assigns
one, so an unrelated `?m` in the expected type can't be set to `n` just
because the test passed by it. This is predictable and cheap; it misses
occurrences that are only equal after computation (`xs ++ Nil` for
`xs`), which the escape route below covers. Lean's version is more
aggressive (keyed matching up to reducible unfolding; **unverified** in
detail [L2]); a more aggressive test can be added later as an explicit,
transactional step (§7.3's transaction).

A metavariable that stays unsolved in the motive needs no special case:
the helper's type must have none left when it's admitted (§2.2, step 2),
and if it's solved later to mention the scrutinee expression, that's only
less generalisation, never unsoundness, because step 3 compares the
helper's instantiated type with the expected type.

**Limitations of the first version** (each `E-MATCH-MOTIVE`, with a note
pointing to the escape route):

- the **same variable twice** as a scrutinee (`match n, n with`);
- **overlapping expression scrutinees**, one a subterm of the other
  (`match n, f n with` where `n` is itself an expression, or
  `match f n, g (f n) with`). A variable scrutinee next to an expression
  that mentions it (`match n, f n` with `n` a variable) is fine: `f n` is
  generalised and `n` is an ordinary capture;
- an **expression scrutinee whose type mentions another expression
  scrutinee** (dependent multiple scrutinees). Variable scrutinees may
  depend on each other freely (rule 1 handles them).

**The escape route** is an explicit top-level helper with a written
dependent signature, which is always possible and is exactly what the
`match` would have generated. Naming the equation (`h :`) doesn't always
repair an ill-typed motive and isn't promised to; a general explicit
motive (Lean's `(motive := …)`) stays deferred until someone needs it.

**A `match` in a type** (in a signature) is lifted the same way, and
admitted before the signature (§2.2).

**When the `match` isn't checked against a type** (`let y = match …` with
no annotation), the first alternative's type is inferred and used for all
of them; it mustn't mention that alternative's pattern variables
(`E-CANNOT-INFER`, with a note suggesting an annotation otherwise).

**Equality of two `match`es**: two textually identical lifted `match`es
in different places are different definitions, so they're equal by
computation only when their scrutinees are constructors. Agda documents
the same for pattern lambdas ("pattern lambdas are *generative*") [A1].
A `match` compiled into the tree (§4.3) is part of its definition and has
no such issue.

### 4.5 Termination: the test pair

Review finding 1's pair, both lifted (the `1 +` keeps them out of tail
position, so §4.3 doesn't apply):

```
count : Nat -> Nat
count n = 1 + match n with
                | Zero   -> 0
                | Succ k -> count k
```

`count` passes its parameter `n` unchanged to `count.%match1`, which calls
`count k` on a field of it. The composed cycle `count → count.%match1 →
count` decreases, so it's **accepted**.

```
loop : Nat -> Nat
loop n = 1 + match Succ n with
               | Zero   -> 0
               | Succ k -> loop k
```

`loop` passes the new value `Succ n` to `loop.%match1`. Its field `k` is
smaller than the helper's own input, but nothing shows it's smaller than
`loop`'s `n` (it's equal), so the cycle doesn't decrease and is
**rejected** (`E-TERMINATION`, naming `loop` and "this `match`"). Both go
in the test suite. The tail-position versions of each (`count n = match n
with …`) are tested too: `count` is compiled into the tree (§4.3) and
accepted; `loop`'s scrutinee is an expression, so it's lifted and
rejected.

### 4.6 `match h : e with`: naming the equation

Without a name, a branch doesn't learn anything about the original
expression: in `match length xs with | 0 -> …`, the `0` branch doesn't
know `length xs = 0`. Idris 2 has exactly this issue with `case` [I2];
Lean's fix is `match h : e with` [L2], adopted here (the user's decision
5). Specification (review finding 5):

- **The equation parameter keeps the original expression.** The helper
  gets one more parameter after the scrutinee `s`: `h : e = s`, where `e`
  is the original elaborated expression. It's added **after** the motive
  is built and is excluded from abstraction, so it can't be turned into
  `s = s`. The call passes `rfl`. Splitting `s` refines `h`'s type, so the
  `Zero` branch gets `h : length xs = Zero`:

  ```
  aux : (xs : List a) -> (s : Nat) -> length xs = s -> R s
  -- call site:
  aux xs (length xs) rfl
  ```
- **Naming a variable scrutinee generalises it.** `match h : xs with`
  treats `xs` as an expression: a new `s` is matched and `xs` stays an
  ordinary capture, so `h : xs = Cons y ys` is informative. (Without the
  name, rule 1 of §4.4 applies and `xs` itself is refined.) A named
  `match` is always lifted (§4.2, condition 3).
- **Only homogeneous equality.** `h : e = s` is formed at `s`'s type in the
  helper's telescope. It's accepted only if `e`'s type is the same type
  there (by conversion); otherwise it's `E-MATCH-EQUATION`. Stitchwort
  never manufactures an equality between terms of different types (that
  would need heterogeneous equality or a transport). With the §4.4
  limitations this can only happen in combinations the first version
  rejects anyway.
- **Number patterns are unchanged**: in `match h : n with | 0 -> … | m ->
  …`, the second branch gets `h : n = m`, not `n ≠ 0`. Naming the equation
  gives an equality with the matched value, not the exclusions that
  control flow established (as for equations,
  [syntax.md](../syntax.md#declarations)).

### 4.7 Effects

A `match` in an effectful block (review finding 5):

- **Every scrutinee is evaluated once, left to right, before anything
  else**, and bound to a fresh variable; the `match` then matches those
  variables. Reordering the helper's parameters into a well-formed
  telescope (§4.4) moves *values*, never *operations*: the operations
  have already run, in source order.
- So **an effectful scrutinee is never put in an equation**. In
  `match h : readLine () with`, the computation `readLine ()` isn't a
  value of `Maybe Text`, so it can't appear in `h`. It runs once, its
  result is bound (say `r`), and `h : r = Nothing` relates the *bound
  result* to the pattern. Since `r` is opaque, as for any `let`, this is
  useful mainly when the branches pass `h` on. (Writing the binding
  explicitly, `let r = readLine ()` then `match h : r with`, means the
  same.)
- Branches that perform abilities give a helper with a row (the owner's,
  its row variable captured), through the effect translation of ordinary
  effectful definitions. Most bugs will be here, so it gets its own tests.

### 4.8 Kernel, evaluation, JavaScript

- **Kernel:** no change. Allowing `Case` anywhere would touch conversion,
  the termination checker and the JS generator, all trusted code, for no
  gain in what can be expressed. Lean and Idris 2 both lift.
- **Evaluation:** a lifted `match` costs one extra call; one compiled into
  the tree costs nothing extra.
- **JavaScript, tail calls** (review finding 8). A `match` compiled into
  the tree keeps self tail calls as loops (§4.3). A **lifted** `match` in
  tail position whose branch calls the owner (`f → f.%match1 → f`) is a
  pair of mutual tail calls, which aren't loops (`TODO.md`, "Mutual tail
  calls aren't loops"). Deep recursion through it can reach the JS stack
  limit where the equivalent equations wouldn't. That's a documented
  limitation of this version, in `syntax.md` next to `match`, with a
  regression test (§4.9). The case that matters most in practice, a tail
  `match` on a parameter, isn't affected.
- An auxiliary definition used once could later be inlined by the
  generator as a `switch` in place, if a benchmark shows the calls matter.

### 4.9 Errors and tests

New errors: `E-MATCH-MOTIVE` (the motive can't be built, or is ill typed,
or a §4.4 limitation), `E-MATCH-EQUATION` (§4.6). `E-NONEXHAUSTIVE` is
reported at the `match`, listing the missing patterns, and says "this
`match`", never `f.%match1`.

Tests:

- **Accept:** `appendNil` (compiled into the tree); the same proof with a
  non-tail `match` (lifted, variable scrutinee); a variable scrutinee
  with a dependent hypothesis `q : P n` refined in each branch; an
  expression scrutinee generalised in the goal; `match h : length xs` with
  `h` used in a branch; `count` in both forms (§4.5); the AoC programs'
  `rndStep`/`rndJoin`/`combineStep` helpers rewritten as `match`; a
  `match` inside a `where` function (`f.go.%match1`); a `match` in a
  signature; number and record patterns; a `match` in an effectful block
  with abilities in its branches; a local function named `match1` next to
  a `match` (no collision).
- **Reject:** `loop` in both forms; a non-exhaustive `match`; each §4.4
  limitation (repeated, overlapping, dependent expression scrutinees),
  with the note naming the escape route; a heterogeneous `h :`
  (`E-MATCH-EQUATION`); a motive that only "works" branch by branch
  (an expression scrutinee whose generalisation makes a capture's type
  ill formed), which must be `E-MATCH-MOTIVE`, not accepted.
- **Occurrence test:** an expected type with an unrelated unsolved `?m`
  stays unsolved after the `match` (non-assigning); an occurrence that's
  only equal by computation isn't abstracted (documented behaviour).
- **Effects:** two effectful scrutinees with observable effects run once
  each, in source order, also when the telescope reorders them;
  `match h : readLine ()` gives `h` about the bound result.
- **JS:** a snapshot of `count`'s tail form as a loop; **a deep-recursion
  regression test**: `count 1000000` in tail form runs in constant stack;
  the lifted tail form (`match h : n with …`, which is lifted because it's
  named) at the same depth fails with the boundary's existing
  out-of-resources error (the `RangeError` handling in `crates/js`), not
  a crash, and the test is updated when mutual tail calls become loops.

## 5. Patterns in `let` and in lambdas

### 5.1 Syntax and the rule

```
let (q, r) = divMod n 7
let { pos, atZero, .. } = acc
let MkPair a b = p
foldl (\acc (k, v) -> acc + v) 0 entries
map (\{ name, .. } -> name) people
```

**The one authoritative rule** (review finding 9): a pattern binding is
accepted when **the ordinary one-alternative `match` is exhaustive under
the existing coverage rules**. Otherwise it's `E-LET-REFUTABLE` (the
user's decision 6):

> `E-LET-REFUTABLE`: this pattern doesn't match every `List Nat`
> (`Nil` isn't covered). Use `match` to say what happens otherwise.

What that accepts, in practice (an explanation, not a second definition):
variables, `_`, records, tuples, and constructors of types with exactly
one constructor, nested freely; also a type with one constructor plus
impossible ones (the `()` cases the checker already discharges).

- **Coverage is by type, not by the value.** `let Just x = Just 3` is
  **rejected**, deliberately, though the right-hand side visibly builds a
  `Just`: the checker covers `Maybe Nat`, not the expression. This is a
  test with a fixed expected result, so the two elaboration paths
  (`let` and `match`) can't drift apart.
- **Exhaustive isn't the only check.** The binding then goes through the
  ordinary kernel checks like any `match`, so `E-PROP-ELIM` still applies:
  a pattern that covers every constructor of a proposition still can't
  extract data from a proof into a non-proof result.

How other languages choose (all partial languages, where a crash is
possible): OCaml allows a refutable `let` and raises `Match_failure` at run
time [O1]; Haskell's `let` patterns are lazy and fail when a variable is
used [H1, §3.12]; Elm allows only single-constructor types, tuples and
records [E1]; Agda allows only record constructors in `let` [A2]. A total
language can't crash, so a compile-time error is the only fit.

### 5.2 What it means

`let pat = e` followed by the rest of the block is
`match e with | pat -> rest`, one alternative (§4). A lambda
`\pat -> body` is `\x -> let pat = x` … `body` (Haskell defines lambda
patterns this way [H1, §3.3]). Several pattern parameters are several
`let`s.

**Why `match` and not projections** (Agda's choice for records [A2])?

- a projection's result has *unknown* size for termination until records
  stage 2 ([records.md §6.4](records.md#64-termination)), whereas matching
  gives "smaller", so `let Node x kids = t` then recursing on `kids` would
  be refused;
- ordinary one-constructor data types have no projections;
- types refine: after `let (a, b) = p` the checker knows `p` is `(a, b)`
  when `p` is a variable, as for any `match`.

**Effects:** in an effectful block, `let (a, b) = readPair ()` runs
`readPair ()` once, first (§4.7); the rest of the block is the single
alternative.

**Not proposed:** pattern bindings in a `where` block or at top level
(`(a, b) = …`), which would define two names from one computation and need
a different translation; multi-alternative pattern lambdas (Haskell's
`\case`): `\x -> match x with …` is as short.

### 5.3 Parsing

- `let` takes a pattern instead of a name. A lowercase name is a variable
  pattern; `let x : T = e` and `let (a, b) : (Nat, Nat) = e` work.
- In a lambda, `\(x : T) -> …` is an annotated parameter, while `\(a, b)`,
  `\(MkPair a b)` and `\{ … }` are patterns, told apart by a lowercase
  name followed by `:` right after `(`.

### 5.4 Errors and tests

- `E-LET-REFUTABLE` (for `let` and lambdas), naming a missing case.
- Tests: tuple, record and nested single-constructor patterns; a refutable
  pattern in each position; `let Just x = Just 3` (rejected, by design); a
  number pattern; a one-constructor-plus-impossible-cases type (accepted);
  a pattern that covers a proposition but extracts data (`E-PROP-ELIM`);
  a pattern `let` in an effectful block; `let (a, b) = …` in a proof
  whose goal mentions the scrutinee variable; termination through
  `let Node x kids = t`; golden parser tests next to records' `\{` and
  ability rows.

## 6. Tuples

### 6.1 Syntax and meaning

| Written | Means |
|---|---|
| `(A, B)` where a type is expected | `Pair A B` |
| `(a, b)` where a value is expected | `MkPair a b` |
| `(p, q)` in a pattern | `MkPair p q` |
| `(a, b, c)` | `(a, (b, c))`, so `Pair A (Pair B C)` |
| `()` | unchanged: the unit type and its value |
| `(e)` | unchanged: grouping |

- **Three or more nest to the right**, as in Idris 2 [I1] and Lean. One
  type, `Pair`, covers every size; a pattern `(a, b, c)` just works.
- **No one-element tuple**: `(e,)` is a parse error.
- **Annotations**: `(e : T)` keeps meaning an annotation; `(a, b : T)` is a
  parse error with a note ("to annotate one component, write
  `(a, (b : T))`; to annotate the pair, `((a, b) : T)`").
- **Function types**: `(x : A) -> B` stays a binder; `(A, B) -> C` is a
  function from a pair.
- `(a, b)` finds `Pair`/`MkPair` **by identity** (the built-in registry,
  [namespaces.md §4.7](namespaces.md#47-operators-and-other-built-in-syntax)),
  so a user's own `Pair` doesn't change it.

**"Where a type is expected" is decided by elaboration, not by where the
text is** (review finding 11). The parser makes one `Tuple` node; the
elaborator decides:

- **Checked against a known type:** if the expected type (after
  unfolding) is a universe (`Type`, `Prop`, …), it's a type tuple: each
  component is checked as a type, giving `Pair A B`. Otherwise it's a
  value tuple: `MkPair a b` checked against the expected type.
- **Inferred** (no expected type): the first component is inferred; if
  its type is a universe, it's a type tuple, otherwise a value tuple.
- **In a pattern:** always `MkPair`.

So `PairType : Type` / `PairType = (Nat, Text)` is a type tuple because the
body is checked against `Type`, and a domain `(A, B) -> C` because a
function type's domain is checked as a type. The inferred case isn't a
guess based on how the components look: `Pair`'s parameters are
`(a : Type) (b : Type)` (`prelude.sw`), with no universe polymorphism
([DESIGN.md, Universes](../../DESIGN.md#universes)), so a *value* pair of
types (`MkPair Nat Text`, which would need `Type : Type`) is ill typed,
and the type reading is the only one that can check.

**Universe and `Prop` restrictions are `Pair`'s, unchanged.** A component
must be in `Type`; `Prop` isn't a subtype of `Type` here (the unifier
compares universes exactly, `unify.rs`, `Sort` case; DESIGN.md has
`Prop : Type 0` and no cumulativity), so neither a pair with a
proposition as a component type nor a pair containing a proof is
possible. A dependent pair (`(n : Nat ** n < 5)` in Idris [I1]) is a
separate feature; a declared record with a dependent field covers it.

### 6.2 Relation to anonymous records

Records' stage 3 (anonymous records, deferred,
[records.md U3](records.md#decisions-16-october-2026)) would make
`{ quotient : Nat, remainder : Nat }` a type without declaring it.
Treating tuples as records with numeric labels, as Standard ML does
(**unverified**, from memory of the Definition), isn't recommended:
positional pairs nest well and are what the prelude and proofs already
use. Tuples as `Pair` don't block stage 3, and stage 3's literals use
braces, so there's no syntax clash. With dot notation merged, `p.fst`
already works for pairs (`Pair.fst`).

### 6.3 The JavaScript boundary: a separate, trusted change

The user chose pairs as flattened JS arrays (decision 7). This **changes
the trusted boundary contract** (DESIGN.md §12): draft 1's "nothing changes
what the JavaScript generator understands" was true of the generated code
but not of the boundary, and the review is right that it needs its own
specification and tests. It's built as a separate change, after the
syntax, and reviewed as boundary code.

**The contract.** At an export's inputs and outputs, a value of type
`Pair A B` is a readonly JS array, TypeScript `readonly [A', …]`, with
**right-nested pairs flattened**. One description, the *spine* of a pair
type, drives decoding, encoding and the `.d.ts` alike:

- the spine of `Pair A B` is `A` followed by the spine of `B` if `B` is
  (after the boundary's usual evaluation of types, so a nickname that
  reduces to `Pair` counts) a `Pair`, and just `A, B` otherwise;
- the first component is never flattened: `((a, b), c)` is `[[a, b], c]`;
- so `Pair Nat (Pair Nat Nat)` written as a nested pair on purpose is
  `[n, m, k]`, the same as `(Nat, Nat, Nat)`: the rule follows the type,
  not the spelling.

**Decoding** follows DESIGN.md's rules for objects at the boundary
([Objects at the boundary](../../DESIGN.md#objects-at-the-boundary)):

- the input must satisfy `Array.isArray` (an array-like object with a
  `length` is refused) and have exactly the spine's length;
- each index is read **once**, and must be an **own** element: a hole
  (`[1, , 3]`) or an element inherited from `Array.prototype` is refused,
  with the path to it (`arg0[1]`);
- elements are decoded into fresh internal values that the wrapper owns
  (`MkPair` objects nested to the right), so later mutation of the input
  array can't affect the result;
- the decoder's existing explicit stack is used for the spine, so a long
  spine doesn't recurse.

**Encoding** builds a fresh array from the spine, treated like the
boundary's other outputs (lists are already arrays), also without
recursion.

**Cache invalidation.** Verified: there's no cache of generated JS today,
and the test-result cache's compiler fingerprint covers the syntax, core,
elaborator and driver sources (`crates/driver/build.rs`, `SOURCES`), not
`crates/js`. The change adds a boundary representation version to the
generated module's header comment; any cache of generated code or of
results from running it (the playground, or a future JS test cache) must
include it or `crates/js` in its key. The change's checklist includes
checking this in the playground.

**Round-trip tests**, both directions (`encode(decode(j))` gives back `j`
for valid input; `decode(encode(v))` gives back `v`):

- a right-nested triple and quadruple;
- a left-nested `((a, b), c)` (stays nested);
- a nickname whose second component reduces to `Pair` (flattened);
- `Pair` inside a list and a record, and a list of 100,000 pairs;
- a deep spine: a generated program with a 1,000-component tuple type
  (no stack overflow either way);
- **malformed input:** wrong length (short and long), not an array, an
  array-like object, a hole, an inherited element, a component of the
  wrong type (path in the message);
- mutation after decoding doesn't change the result;
- `.d.ts` snapshots for each type above.

## 7. Knowing more expected types (result type first)

### 7.1 The problem

```
type Rot = { dir : Dir, amount : Nat }

parse : Nat -> Maybe Nat -> Maybe Rot
parse n m = maybeThen m (\x -> Just { dir = TL, amount = n + x })   -- E-CANNOT-INFER
```

A record literal with no known type is an error
([records.md U6](records.md#decisions-16-october-2026)), and that stays.
But here the type is knowable: `parse`'s result is `Maybe Rot` and
`maybeThen : Maybe a -> (a -> Maybe b) -> Maybe b`, so `b = Rot`. The
compiler doesn't see it because it checks the arguments first, left to
right, and compares the result type with `Maybe Rot` only at the end
(`fallback`).

### 7.2 The proposal

When an application is **checked** against an expected type, compare the
type of the application as written with the expected type **before**
checking the explicit arguments, when that type doesn't depend on their
values. This is Lean 4's `propagateExpectedType`, which "will do nothing
if the resultant type depends on the remaining arguments" [L3].
Constructors already get this (`ctor_app`); this extends it to every
function. The user decided to build it (decision 8).

**The type of the application actually written** (review finding 6) is
computed by walking the head's type over the arguments as written, the way
elaboration will:

- an implicit parameter not given by name gets a fresh metavariable, as
  `insert` does;
- a named argument (`[x := …]`) fills its parameter (its value isn't
  checked yet, so it's treated like an explicit argument below);
- each positional argument consumes the next explicit parameter;
- after the last written argument, trailing implicit parameters are
  inserted only where `insert` would insert them. Fewer arguments than
  parameters (a partial application) leaves a function type, and that's
  the result compared, not the codomain after every parameter.

**The dependency test.** The parameters for written (explicit or named)
arguments are instantiated with **fresh variables**, not metavariables,
and the result type is checked for mentions of them. If it mentions any,
propagation is skipped (`(n : Nat) -> Vec n` applied to a written `3`).
Fresh variables keep the test honest: with metavariables in their place,
the result would mention metavariables, not variables, and a test looking
for variables would find nothing and wrongly let it through. Propagation
is also skipped if a remaining parameter is `auto` (Lean does the same
[L3]), since solving the result first could change what the search finds.

### 7.3 The transaction (verified in code)

**The unifier is not atomic on failure.** `unify` (`unify.rs`) keeps a work
list and, as it goes, solves metavariables in place
(`g.solve_meta`, called from `solve` and `prune`; `prune` also creates new
metavariables). When a later pair fails it returns `Ok(false)`, and the
solutions made before stay. The review's example, `Pair ?a Bool` against
`Pair Nat Nat`: the data types' arguments are pushed left to right, `?a`
is solved to `Nat`, then `Bool` against `Nat` fails, and `?a = Nat`
survives. So an undo is required, not optional.

**What state is involved.** The elaborator's inference state is:

- the metavariable table, `Globals::metas` (`crates/core/src/globals.rs`),
  including metavariables created during the attempt;
- pending `auto` obligations, `Elaborator::obligations` (`lib.rs`); these
  two are exactly what `clear_metas` resets;
- warnings collected for the current declaration
  (`Elaborator::warnings`);
- the local context (`Ctx::mark` / `Ctx::reset`).

There are no universe metavariables or universe constraints (the unifier
compares universes exactly), and no comparison caches that change during
unification (`Globals::hashes` holds hashes of finished declarations
only).

**The transaction**, a generalisation of `auto.rs`'s `attempt`: snapshot
the metavariable table (a copy, as `attempt` does), the obligations, the
number of warnings and the context mark; run the step; if it returns "no",
restore all four. **Running out of resources is not "no"**: it's an error,
which is passed on without restoring and stops elaboration, and the budget
it used isn't refunded (the budget is a separate counter, deliberately not
part of the snapshot). `attempt` is then reimplemented on top of the
transaction, so there's one undo.

**A pre-existing gap the transaction also fixes.** `fallback` (`check.rs`)
calls `unify` and, on "no", tries `effects::coerce`, which unifies again;
the first attempt's partial solutions are still there when the coercion
runs. `effects::coerce` itself restores only the context mark. Both should
use the transaction. This is small and goes in step 2 (§8), with a test
whose first unification fails part-way.

### 7.4 When propagation succeeds but is wrong: one fallback

Undoing a failed comparison isn't enough (review finding 6): with
coercions, an early comparison can **succeed** and still be the wrong
choice. Example: `unbox : [a : Type] -> Box a -> a`, applied to a
`Box PureFn` where a `PartialFn` is expected. Today, `a` is inferred as
`PureFn` from the argument and the result is coerced to `PartialFn`.
With propagation, `a` is solved to `PartialFn` first, then the argument
must be a `Box PartialFn`, and there's no coercion from `Box PureFn` to
that. A program that works today would fail. (This is a regression in
inference, not in soundness: nothing wrong is accepted.)

**The policy: one bounded retry through the old path.** If propagation
succeeded and the application then fails anywhere (any error except
running out of resources), the whole application is rolled back to the
snapshot taken before propagation, and elaborated again **the old way**
(arguments first, `fallback` at the end), with propagation turned off for
that application and everything inside it. If the old way succeeds, its
result is used; if it fails, **its** error is reported.

- So every program accepted today is still accepted, with the same
  elaboration, and every program rejected today gets the same message
  (the reject-suite snapshots stay identical). Propagation only adds
  programs.
- The cost is bounded: a retry disables propagation below it, so each
  application is elaborated at most twice per propagating ancestor that
  fails; in the worst case that's quadratic in nesting depth, and the
  ordinary resource budget covers it. No search beyond the one retry.
- Lean treats propagation as a heuristic too, with exclusions for
  coercion-sensitive cases [L3]; a retry is simpler than predicting those
  cases here.

### 7.5 What it fixes and what it doesn't

Fixed: `maybeThen m (\x -> Just { dir = TL, amount = x })` where the
result type is known; `map (\x -> { x = x, y = 0 }) xs` checked against
`List Point`; `foldr (\r acc -> …{ … }…) { … } rs` with the literal before
anything fixes its type.

Not fixed, by design (U6): `let r = maybeThen m (\x -> Just { … })` with
nothing saying what `r` is: still `E-CANNOT-INFER`.

Possible later, not proposed: checking lambda arguments after the others
(Lean postpones some [L3]).

### 7.6 Tests

- The three examples above.
- The unifier: `Pair ?a Bool` against `Pair Nat Nat` inside a transaction
  leaves `?a` unsolved; the same with a metavariable created by pruning
  during the attempt; an attempt that runs out of resources is an error,
  and the budget isn't refunded.
- The `unbox` example: accepted, through the retry.
- A row-order coercion and a total-for-partial coercion in an argument
  position (both accepted as today).
- The dependency test: a dependent result (skipped); a partial
  application (compares the remaining function type); a named implicit
  argument; a trailing `auto` parameter (skipped).
- `fallback`'s unify-then-coerce with a part-way failure.
- Error snapshots of the whole `examples/reject` suite before and after:
  identical.
- Kernel: none. JS: none.

## 8. Implementation plan

"Opus" marks design-heavy work (soundness, the elaborator's core,
trusted boundary code); "Sonnet" marks mechanical work (parsing,
desugaring to existing forms, tests, docs). Each step is its own lane and
merge, in this order (the user's decision 9).

**Step 1. Tuples (§6.1).**
- Sonnet: parser and AST (`Expr::Tuple`, `Pattern::Tuple`), elaboration
  by context (type or value, §6.1) to `Pair`/`MkPair` by identity, golden
  parser tests (`()`, `(e)`, `(a, b)`, `(a, b, c)`, `((a, b), c)`,
  `(a, b) -> c`, `(x : A) -> B`, `(a, b : T)` and `(e,)` as errors,
  tuples nested in constructor and record patterns), elaboration tests
  (`PairType = (Nat, Text)`, an inferred type tuple, a user `Pair` not
  affecting `(a, b)`, a proof component refused), `syntax.md`.

**Step 1b. Pairs as arrays at the boundary (§6.3)**, a separate merge
after step 1.
- Opus: the codec and `.d.ts` from one spine description, the
  representation version, DESIGN.md §12's contract text.
- Sonnet: the round-trip and malformed-input tests, `.d.ts` snapshots.

**Step 2. Result type first (§7).**
- Opus: the transaction (generalising `attempt`), fixing `fallback` and
  `effects::coerce` to use it, the application's written result type and
  dependency test, the retry.
- Sonnet: tests, the reject-suite comparison.

**Step 3. Lifting machinery and `match` (§2, §4).** The core.
- Opus: §2 in full: capture fixed point on elaborated terms, drafts,
  dependency order and admission (with the signature case), failure
  handling, scope binding after the owner is final; §4.2 to §4.4: the
  in-tree compilation and the lifted helper with its telescope, occurrence
  test and motive checks; §4.6 `match h :`; §4.7 effect sequencing.
- Sonnet: parser (`match … with`, alignment like `handle`), error
  messages hiding generated names (§2.5), tests of §4.9, JS snapshots and
  the deep-recursion test, `syntax.md` (including the tail-call
  limitation).
- Checkpoint inside the step (the review's recommendation): first the
  capture fixed point and admission graph with variable scrutinees and the
  in-tree path; then named equations on pure scrutinees and effect
  sequencing; only then expression generalisation.

**Step 4. Pattern `let` and lambdas (§5).** Mostly desugaring to step 3.
- Sonnet: parser, desugaring, `E-LET-REFUTABLE` from the one-row
  exhaustiveness check, tests.
- Opus: review of the effectful-block case.

**Step 5. `where` (§3).** Reuses step 3, adds declarations.
- Opus: scoping (§3.1), the block's own dependency order and immediate
  admission (§3.3), plain values and `E-WHERE-RECURSIVE-VALUE` (§3.4),
  closed local tests, `f.go` resolution against dot notation and the
  `E-DUPLICATE` reservation (§3.6, in `dot.rs` and `scope.rs`).
- Sonnet: parser and layout (`where` only at the right indentation, golden
  tests; `ability … where` is on the declaration's first line, so it
  doesn't collide), `E-WHERE-*` errors, name printing, tests, docs.

Why this order: tuples and propagation are independent and cheaper;
`match` is the general mechanism that pattern `let`/lambdas and `where`
reuse; `where` adds a block with its own declarations, ordering and
names. Namespaces are now merged, so `f.go` is part of step 5 rather than
a follow-up. AoC's friction item 5 says `match` and pattern `let` remove
"most of" the helper definitions, so most of the benefit arrives at step 4.

### Test plan for `where` (step 5)

- **Accept:** an accumulator `go`; a local function using an outer
  variable; a local signature mentioning an outer variable dependently
  (`j <= i`); the `outer`/`first`/`second` capture example (§2.1);
  captured `auto` evidence passed explicitly (a test where a fresh search
  would find a different procedure); shadowing (an inner binder named
  like a captured variable doesn't change what's captured); mutual
  recursion between two local functions and between a local function and
  the owner; **an independent local helper** (admitted before the owner);
  **a local lemma about an already-final helper**; a local partial
  function; a local function performing an ability of the owner's row;
  values in dependency order with observable effects; a closed local
  `test`; `sumTo.go` named from a top-level theorem;
  `Geometry.Shape.area.go`.
- **Reject:** a missing local signature; a duplicate name across two
  equations; a non-decreasing local recursion (the error naming `go`); a
  local lemma used inside its own subject's cycle (`E-MUTUAL-SIGNATURE`);
  `cached = helper n` / `helper x = cached` (`E-WHERE-RECURSIVE-VALUE`);
  a local `test` that captures a parameter (`E-WHERE-TEST-OPEN`); each
  disallowed form (`E-WHERE-FORM`); `map go xs` with `go` in a cycle with
  the owner (`E-TERMINATION`, saturation); a top-level `PairType.go` next
  to a local `go` of `PairType` (`E-DUPLICATE`).
- **Failure part-way:** a group of the owner and a local function where
  the local function's body fails: nothing from the owner is usable from
  another declaration, and `owner.go` reports the owner as failed.
- **Compare:** rewrite top-level helpers of the example programs into
  `where` blocks mechanically; `test` results and JS behaviour must be
  identical (a cheap oracle).
- **JS:** a snapshot of `solve.go` as a loop, with its encoded name.

## 9. Questions for the user

**Decided (16 October 2026):** the user agreed with every recommendation
below (1 to 9): `match e with`; local names unique across the definition;
a `where` value computed once; capture only the variables used;
`match h : e with` in the first version; a refutable `let`/lambda pattern is
the compile-time error `E-LET-REFUTABLE`; pairs as flattened JS arrays (a
separate change); the result-type-first change is built; the order in §8.
Draft 2 keeps all of them.

1. **`match e with` or `case e of`?** Decided: `match … with | …`.
2. **Local function names unique per definition?** Decided: yes.
3. **`where`-bound plain values computed once?** Decided: yes, opaque in
   types; §3.4 adds the cycle and order rules.
4. **Captured variables: only those used?** Decided: yes (Lean's choice);
   §2.1 makes "used" precise.
5. **`match h : e with` in the first version?** Decided: yes; §4.6.
6. **Refutable patterns are errors?** Decided: yes; §5.1.
7. **Pairs at the JS boundary as flattened arrays?** Decided: yes, as a
   separate change (§6.3).
8. **Expected-type propagation?** Decided: yes, with §7.3's transaction
   and §7.4's retry.
9. **Order**: tuples → propagation → `match` → pattern `let`/lambda →
   `where`. Decided.

**New in draft 2** (each has a recommendation; the design above assumes
it):

10. **A tail-position `match` on a variable is compiled into the
    enclosing case tree (§4.3)**, rather than always lifted.
    Recommendation: yes. It keeps self tail calls as loops in JS, gives
    proofs the ordinary equation refinement, and generates nothing.
11. **On a propagation retry, report the old path's error (§7.4)**, so
    messages for rejected programs never change. Recommendation: yes. The
    alternative (reporting the propagated error, often "this argument has
    the wrong type") could be clearer, but would change messages and need
    a rule for which error wins.
12. **In `f.go`, a definition's local function wins over dot notation
    (§3.6)** when both exist. Recommendation: yes: the dot-notation
    meaning stays writable as `T.go f`, the local function has no other
    spelling.
13. **No nested `where` (inside a local function's equations) in the
    first version (§3.1).** Recommendation: yes; it's a compatible
    addition later.

## Review response

The external review of draft 1 (17 October 2026) had eleven findings.
Draft 2 adopts all of them; none was disputed.

| # | Finding | Kind | Where addressed |
|---|---|---|---|
| 1 | Termination argument: no lifting exemption; "captures unchanged" isn't the argument | note | §0 (the guarantee), §3.5, §4.5 (the `count`/`loop` pair) |
| 2 | Capture needs a fixed point across local calls; pass evidence explicitly; capture by identity | must-fix | §2.1 (four rules, fixed point, explicit evidence, identity), test plan in §8 |
| 3 | Discovering a helper isn't admitting it; specify generated-definition scheduling | must-fix | §2.2 (collect, resolve, order, admit; signature case; lemma case; failure), §3.3 |
| 4 | Motive: one telescope rule; a specified non-assigning occurrence test; limitations | must-fix | §4.4 (telescope rule, occurrence test, limitations, escape route), §4.9 |
| 5 | `match h :` keeps the original expression; homogeneous only; effectful scrutinees | must-fix | §4.6, §4.7 |
| 6 | Propagation must be transactional; successful propagation can overconstrain; compute the written application's type | must-fix | §7.2, §7.3 (verified non-atomic, the transaction, a pre-existing gap in `fallback`), §7.4 (one retry) |
| 7 | `where` values: cycles, order, once per call; local `test`; allowed forms | must-fix | §3.1 (table), §3.4, §3.5 |
| 8 | Saturation and "no closures" overstated; tail-position `match` loses loops | should-fix | §2.3, §4.3 (in-tree compilation), §4.8, §4.9 (deep-recursion test) |
| 9 | One definition of irrefutable; Prop elimination; `let Just x = Just 3` | should-fix | §5.1, §5.4 |
| 10 | Naming with namespaces: `f.go` vs dot notation, unspellable match helpers, JS encoder, diagnostics | should-fix | §2.4, §2.5, §3.6 |
| 11 | Tuples: type-or-value by context; the boundary is a trusted change with round-trip tests | note | §6.1, §6.3, step 1b in §8 |

Things checked in the code while addressing the review, and what they
changed:

- **The unifier isn't atomic on failure** (`unify.rs`): confirmed, so the
  transaction is a prerequisite (§7.3). The same check found that
  `fallback`'s unify-then-coerce already depends on partial solutions
  surviving a failed unification, which the transaction fixes too.
- **`auto.rs` already has an undo** (`attempt`), which the transaction
  generalises rather than duplicating.
- **The JS loop is only for self tail calls** (`self_tail_loop`): this is
  what made in-tree compilation of tail `match`es (§4.3) worth adding,
  rather than only documenting the limitation.
- **The pattern compiler takes arbitrary context levels as columns**
  (`compile`), which is what makes in-tree compilation an elaborator-only
  change.
- **The kernel's two-step admission** (`declare_def`, `define_group`) and
  per-body metavariable reset (`clear_metas`) shaped §2.2: independent
  helpers can be admitted early only once their own metavariables are
  solved.
- **The lexer splits `sumTo.go`** into a name and dot notation, and no
  declaration can have a lowercase qualifier: so `f.go` needs a
  resolution step before dot notation, and helper keys under a lowercase
  owner can't collide with source declarations (§3.6).
- **No generated-JS cache exists**, and the test cache's fingerprint omits
  `crates/js` (§6.3).
- **`Prop` isn't a subtype of `Type`**, so tuples can't hold proofs
  (§6.1), settling draft 1's **unverified** remark.

## Sources

- [A1] Agda documentation, "Lambda abstraction" (pattern lambdas translated
  to a fresh function definition; "pattern lambdas are *generative*"):
  <https://agda.readthedocs.io/en/latest/language/lambda-abstraction.html>
- [A2] Agda documentation, "Local definitions: let and where" (`let` patterns
  only for record constructors, translated to projections; `where` sees the
  clause's pattern variables):
  <https://agda.readthedocs.io/en/latest/language/let-and-where.html>
- [E1] Exercism, Elm track, "Pattern matching" (destructuring for
  single-variant custom types, tuples and records):
  <https://exercism.org/tracks/elm/concepts/pattern-matching>
- [H1] Haskell 2010 Report, chapter 3 (§3.3 lambda patterns via `case`;
  §3.12 lazy `let` patterns) and §4.4.3:
  <https://www.haskell.org/onlinereport/haskell2010/haskellch3.html>
- [H2] GHC User's Guide, `ScopedTypeVariables`:
  <https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/scoped_type_variables.html>
  (not re-fetched for this draft).
- [I1] Idris 2 documentation, "Types and Functions" (tuples as nested pairs;
  `where` sees the outer scope; dependent pairs `**`):
  <https://idris2.readthedocs.io/en/latest/tutorial/typesfuns.html>
- [I2] Idris 2 issue #3271 (a `case` is extracted to a helper function, and
  the scrutinee's relation to the branch is lost, unlike `with`):
  <https://github.com/idris-lang/Idris2/issues/3271>
- [J1] T. Johnsson, "Lambda lifting: transforming programs to recursive
  equations", FPCA 1985 (standard reference; not re-fetched).
- [L1] Lean Language Reference, "Recursive definitions", §7.6.1 "Mutual
  recursion" (`where` and `let rec` lifted with captured variables as
  parameters into the enclosing elaboration block, after which the actually
  recursive groups are processed; may not mention each other in their
  signatures):
  <https://lean-lang.org/doc/reference/latest/Definitions/Recursive-Definitions/>
- [L2] Lean Language Reference, "Pattern matching" (auxiliary matching
  functions; motive from occurrences of discriminants in the expected type;
  generalisation; explicit motives; `match h : e with`):
  <https://lean-lang.org/doc/reference/4.23.0/Terms/Pattern-Matching/>
- [L3] Lean 4 source, `src/Lean/Elab/App.lean`, `propagateExpectedType` and
  its doc comment (skipped when the result depends on remaining arguments,
  or with optional/auto parameters; a heuristic with exclusions):
  <https://github.com/leanprover/lean4/blob/master/src/Lean/Elab/App.lean>
- [O1] OCaml manual, "Expressions" (`let` and `function`: "If one of the
  matchings fails, the exception Match_failure is raised"):
  <https://ocaml.org/manual/5.2/expr.html>
