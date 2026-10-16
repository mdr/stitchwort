# Proposal: syntax conveniences (`where`, `match`, patterns in `let` and lambdas, tuples)

**Status:** draft 1, 16 October 2026. Design only: nothing here is built.
It answers `TODO.md`'s "Syntax conveniences" item and row 7 of
[aoc-2025.md §10](../aoc-2025.md#10-capabilities-stitchwort-needs-prioritised),
whose evidence is items 4 to 6 of
[aoc-2025.md §9](../aoc-2025.md#9-friction-found-while-writing-the-five-programs).
Item 3 there (`else` at the start of a line) is already fixed
([syntax.md, "`if` across lines"](../syntax.md#layout)).

This note is meant to be read without knowing the codebase. §1 describes the
parts of Stitchwort it touches, checked against the source at commit
`ea9a68f`. Claims about other languages cite their sources
([Sources](#sources)); anything not checked against a source is marked
**unverified**.

The namespaces lane (qualified names `List.map`, `import List (map)`, the
prelude moving into `Std`, later dot notation) is being built in parallel.
This note doesn't depend on any of its unmerged code, but it is written to
fit it: §2.6 says where they touch.

## Contents

0. [Summary](#0-summary)
1. [Background: what the compiler does today](#1-background-what-the-compiler-does-today)
2. [`where` clauses and local functions](#2-where-clauses-and-local-functions)
3. [`match` expressions](#3-match-expressions)
4. [Patterns in `let` and in lambdas](#4-patterns-in-let-and-in-lambdas)
5. [Tuples](#5-tuples)
6. [Optional: knowing more expected types (record literals in lambdas)](#6-optional-knowing-more-expected-types)
7. [Recommended order and implementation plan](#7-recommended-order-and-implementation-plan)
8. [Questions for the user](#8-questions-for-the-user)
- [Sources](#sources)

## 0. Summary

Five changes, all in the parser and elaborator. **None changes the kernel**
(the small trusted checker), and none changes what the JavaScript generator
has to understand.

| Feature | Example | How it's built |
|---|---|---|
| `where` | `solve ls = go 0 ls` / `where go : …` | each local function becomes a hidden top-level definition, `solve.go`, taking the outer variables it uses as extra arguments ("lambda lifting") |
| `match` | `match xs with \| Nil -> 0 \| Cons x _ -> x` | becomes a hidden top-level definition with one equation per alternative, using the existing pattern compiler |
| pattern `let` | `let (q, r) = divMod n 7` | a `match` with one alternative; the pattern must always match (else `E-LET-REFUTABLE`) |
| pattern lambda | `\(a, b) -> a + b` | `\p -> let (a, b) = p` … |
| tuples | `(Nat, Text)`, `(1, "a")`, `(a, b, c)` | `Pair`, `MkPair`; three or more nest to the right |
| (optional) expected types | `maybeThen m (\x -> Just { dir = TL, amount = n })` checked against `Maybe Rot` | use the expected result type of an application *before* checking its arguments, as Lean does |

The common idea is **lifting**: a local function or a `match` turns into an
ordinary top-level definition, which the kernel, the termination checker,
the evaluator and the JavaScript generator already handle. Lean 4 does the
same for `where`, `let rec` and `match` [L1, L2]; Agda for pattern lambdas
[A1]; Idris 2 for `case` [I2].

Recommended order: tuples, then the lifting machinery with `match`, then
pattern `let` and lambdas (cheap once `match` exists), then `where`; the
expected-type change can go in at any point (§7).

## 1. Background: what the compiler does today

These facts shape everything below. File references are to the source at
`ea9a68f`.

- **The kernel only allows a pattern match at the top of a definition.**
  A definition's body is a *case tree*: a nest of `Case` nodes, each
  splitting one of the definition's variables by constructor, with ordinary
  expressions at the leaves. A `Case` can't appear inside a lambda or as an
  argument (`crates/core/src/check.rs`, `case_only_in_tree`). There's no
  `let` in the core language either. So a `match` in the middle of an
  expression **can't** be translated into a kernel `Case` in place: it has
  to become a separate definition, or the kernel has to change.
- **Pattern matching refines types by substitution.** When the tree splits
  `xs` into `Cons y ys`, the compiler replaces `xs` by `Cons y ys` in the
  goal type and in the types of the other variables
  (`crates/elab/src/lib.rs`, around `check_tree`). That's how a proof by
  cases learns which case it's in. Data types have parameters but no
  indices, so there's no index unification to do.
- **The pattern compiler isn't tied to a name.** `Elaborator::body` takes a
  definition's type and its equations; the parts that do the work, `compile`
  and `check_tree`, work on any context. The `Partial` translation already
  reuses `body` for definitions it generates.
- **The compiler already generates hidden top-level definitions** with
  dotted names that source code can't write: an ability `A` produces `A.res`
  and `A.elim` (built as *surface* declarations and sent through the normal
  path), a partial group produces `f.Request`, `g.recur` and others, and a
  record type `T` produces projections `T.field`.
- **Termination is checked by the kernel**, per group of definitions that
  call each other (`crates/core/src/termination.rs`, using the size-change
  graphs in `sct.rs`). An argument counts as smaller only when it's a field
  matched out of a parameter; a lambda-bound variable's size is unknown.
  Inside a group, every use of a member must be given all its arguments.
- **Mutual recursion is found automatically**: `module.rs` splits the module
  into strongly connected components (groups of definitions that call each
  other) and checks each group together. A type may not mention a member of
  its own group (`E-MUTUAL-SIGNATURE`).
- **`let x = e` is a function applied to `e`**, `(\x -> body) e`, so `x` is
  computed once but is *opaque* in types: the checker doesn't know `x` is
  `e`.
- **Checking is bidirectional**: `check(expr, expected)` pushes a known type
  inwards; `infer(expr)` works one out. A lambda or a record literal can only
  be checked, not inferred (`E-CANNOT-INFER`). An application whose head
  isn't a constructor is *inferred* and its type compared with the expected
  one at the end (`check.rs`, `fallback`); arguments are checked left to
  right, each against its parameter type with earlier arguments filled in.
- **Parser:** `case`, `of` and `match` aren't keywords; `where` is, but only
  `ability … where` uses it. `(a, b)` is a parse error. A lambda's
  parameters are names or `_` (or `(x : T)`). `let` takes a name only.
  `()` already means the unit type `UnitType` and its value `UnitValue`, and
  is a pattern.
- **JavaScript:** a data value is an object `{ tag: "Ctor", field: … }`
  using the constructor's field names; a record is an object without `tag`.
  `Pair` is an ordinary data type, so a pair is
  `{ tag: "MkPair", fst: …, snd: … }`, inside the generated code and at the
  export boundary alike (the TypeScript type is `Pair<A, B>`). Each top-level
  definition is a curried JS function; a lambda is a JS arrow function; a
  call to itself in tail position becomes a loop. A `Case` outside a
  definition's top makes the generator panic.

## 2. `where` clauses and local functions

### 2.1 Proposed syntax

A `where` block follows an equation, indented, and holds declarations
written exactly as at top level, indented further:

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

- **It belongs to one equation** and sees that equation's variables:
  parameters, pattern variables and named implicit parameters. So in
  `f (Cons x xs) = … where …`, the `where` block can use `x` and `xs`. This
  is the rule in Haskell [H1, §4.4.3], Agda [A2] and Idris 2 [I1].
- **It can't see the equation's `let`-bound names** (they're bound later,
  inside the body).
- **Order doesn't matter** inside the block, as at top level.
- **Functions need a signature.** Anything with parameters needs a type,
  as at top level, because Stitchwort can't infer a lambda's type (`TODO.md`,
  "Inferring a bare lambda's type"). A plain value (`weight = 3`) doesn't.
- **The signature may mention outer variables**, including dependently:
  inside `get (xs : List a) (i : Nat)` a local
  `check : (j : Nat) -> j <= i -> Bool` is fine, and so is using the outer
  `a` in `go : List a -> Nat`.
- **A lowercase name in a local signature that's already in scope means the
  outer thing.** In `go : List a -> Nat` inside a function over `List a`,
  `a` is the outer `a`, not a fresh type variable. Haskell gets this wrong
  by default (its local `a` is a new variable unless the
  `ScopedTypeVariables` extension is on), and it's a famous trap
  (**unverified** as to how often it bites; the rule itself is in GHC's
  user guide [H2]). A name not in scope is bound automatically as today.
- **Names must be unique within the whole definition** (not just the
  equation): two equations can't each have their own `go`. This keeps
  `solve.go` (§2.6) unambiguous. (Question 2.)
- **`theorem` and `test` are allowed in a `where` block**: a lemma used only
  by this function lives next to it.

### 2.2 What it means: lambda lifting

Each local function becomes a hidden top-level definition, named after the
enclosing one: `solve.go`, `solve.score`. Every outer variable it uses
becomes an extra parameter at the front, in the order the outer variables
were bound (so later ones may depend on earlier ones). Uses inside the
equation pass them along. This standard transformation is called **lambda
lifting** [J1]; Lean 4 does exactly this for `where` and `let rec`
("lifted out of their context, introducing parameters for captured free
variables as necessary") [L1].

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

index xs target eq = index.go target eq 0 xs
```

- **Implicit and `auto` parameters are captured too** (`a` above), as
  implicit parameters, filled in at each call as usual.
- **Captured variables whose types depend on earlier ones** keep their
  order, so the lifted type is well formed: capturing `i` and
  `ok : i < length xs` gives `index.go : … (xs : List a) -> (i : Nat) ->
  (ok : i < length xs) -> …`. If a captured variable's type mentions an
  outer variable that the function doesn't use, that variable is captured
  too.
- **Which outer variables a captured variable's type mentions** after the
  enclosing equation's patterns are known: in `f (Cons x xs) = …`, the
  context holds `x` and `xs`, not the original argument, because matching
  substituted it.
- **Plain values** (`weight = 3`, no parameters) are not lifted: they become
  `let`s at the start of the equation's body (after the functions they use).
  So each is computed once per call of the equation, as a Haskell
  programmer would expect, rather than once per use. The cost is that,
  like any `let`, the value is opaque in types, and it's computed even if
  the branch that uses it doesn't run (Stitchwort is strict). A value that
  must compute in types can be written as a function of `()` or moved to
  top level. (Question 3.)
- **A local function may use another local function or value** of the same
  block; a value used by a lifted function is captured like any other outer
  variable.

### 2.3 Recursion, mutual recursion and termination

Once lifted, local functions are ordinary top-level definitions, so the
existing machinery decides everything:

- **Recursion and mutual recursion are allowed**: among local functions,
  and between a local function and the enclosing one (Lean allows both
  [L1]). The module's strongly-connected-components pass (`module.rs`)
  simply sees more definitions. `go` calling only itself is its own group,
  checked before `solve`; `go` calling `solve` back puts both in one group.
- **Termination**: the size-change checker sees the lifted calls. Captured
  variables are passed unchanged, which it records as "equal", so they
  never spoil a decreasing argument. A local function recursing on a field
  of a captured variable works too, since the captured variable is a
  parameter of the lifted definition and matching it produces smaller
  fields.
- **The group rules apply as written in [syntax.md](../syntax.md#declaration-order)**:
  inside a cycle, a member must be given all its arguments (`map go xs` is
  refused if `go` and the enclosing function call each other, but not if
  `go` only calls itself), and a type can't mention a member of its own
  cycle (`E-MUTUAL-SIGNATURE`). Lean has the same restriction ("they may not
  mention each other in their type signatures") [L1]. The lifted call is
  generated fully applied, so lifting itself never trips the first rule.
- **`Partial`**: a local function can be partial (`go : Nat -> {Partial} Nat`)
  if the enclosing function is too, or if it isn't in a cycle with it.
  A group mixing partial and total members is `E-PARTIAL-MIXED` as today.
  Captured variables are passed unchanged, which is what the partial
  translation's uniformity rule (`E-PARTIAL-NONUNIFORM`) wants.
- **Abilities**: a local function's signature may list abilities; the
  enclosing function's row variable (`e` in `{State Nat | e}`) is captured
  like a type variable when the local signature mentions it.

### 2.4 Proofs that mention local functions

**Inside the enclosing function.** A `theorem` in the `where` block can
state facts about a local function and be used by the enclosing equation:

```
sumTo : Nat -> Nat
sumTo n = go n 0
  where
    go : Nat -> Nat -> Nat
    go 0        acc = acc
    go (Succ k) acc = go k (acc + Succ k)
```

A lemma `theorem goAcc : (k a : Nat) -> go k a = go k 0 + a` in the same
block is fine: `go` doesn't call it, so it's checked after `go`, and its
type computes with `go` unfolded. It can't be used by `go` itself if it
mentions `go` (that would put the lemma's type in `go`'s cycle:
`E-MUTUAL-SIGNATURE`).

**Outside.** A lemma about `sumTo` usually needs a lemma about `go`, because
`sumTo n` unfolds to `sumTo.go n 0`. With qualified names (namespaces lane),
the lifted function is reachable as `sumTo.go`, and a top-level theorem can
say:

```
theorem sumToGo : (k a : Nat) -> sumTo.go k a = sumTo.go k 0 + a
```

This is how Lean works: `where` functions are ordinary constants named
`f.go` that proofs can mention (the naming is **unverified** against the
reference text, which the fetch tool cut short, but it's the documented
behaviour of `where` in *Functional Programming in Lean* and common in
Mathlib). The captured variables appear as explicit leading arguments, in
the order of §2.2; implicit and `auto` ones are filled in as usual.
`stitchwort` should be able to print a lifted function's full type (an
`E-TYPE-MISMATCH` mentioning it would show it anyway; a `show` command is a
small addition).

**A fragility to know about:** what a lifted function captures depends on
what its body uses. If an edit makes `go` use one more outer variable, the
lemma's statement `sumTo.go k a` gains an argument and breaks. Capturing
*all* the equation's variables would avoid that, at the price of unused
parameters (which JS would still pass). Lean captures only what's used [L1].
Recommendation: only what's used, as Lean (question 4).

Before namespaces land, `sumTo.go` can't be written in source, so an
outside lemma must be stated about `sumTo` itself, or the helper stays at
top level. That's acceptable for a first version.

### 2.5 JavaScript

Nothing new for the generator: `solve.go` is a top-level definition like
any other and is emitted as `const solve$$go = …` (dots become `$$`). Two
consequences:

- **No closures are allocated** for local functions, unlike a lambda.
- **A local function's self tail calls become loops**, exactly as for top
  level, which is what the "accumulator `go`" pattern needs. Calls *between*
  `go` and the enclosing function are mutual tail calls, which aren't loops
  yet (`TODO.md`, "Mutual tail calls aren't loops"): unchanged.

Lifted definitions are never exported, and don't appear in the `.d.ts`.

### 2.6 Names and namespaces

- **Inside the equation**, `go` is a local binder: the namespaces note puts
  local binders first when resolving a short name
  ([namespaces.md §4.4](namespaces.md#44-what-a-short-name-means)), so a
  local `go` hides a top-level `go`, with no warning.
- **Outside**, it's `solve.go`. With namespaces, a definition's name is also
  a namespace for its local functions, as in Lean. A definition
  `Geometry.Shape.area` has local functions `Geometry.Shape.area.go`. The
  namespaces lane should reserve this: a declaration may not be called
  `solve.go` if `solve` has a local `go` (`E-DUPLICATE`).
- **Dot notation** isn't affected: `x.go` looks in the namespace of `x`'s
  *type*, never in a function's namespace.

### 2.7 Error messages

Errors inside a local function must speak the user's language:

- name it `go` (or "`go`, in `solve`'s `where` block"), never `solve.go`
  with extra arguments;
- when a type mentions a lifted call, print `go k a`, hiding the captured
  arguments, inside the enclosing function, and the full `solve.go k a`
  outside it;
- report spans in the original source, which the generated equations keep.

New errors: `E-WHERE-SIGNATURE` (a local function with parameters but no
signature), `E-DUPLICATE` for a name used twice in one definition's `where`
blocks, and `E-WHERE-RECURSIVE-VALUE` for a plain value that refers to
itself.

### 2.8 Risks

- **Hashes.** A lifted definition is hashed like any other. Its name is
  stable (it's the user's own `go`), so editing an unrelated part of the
  file changes nothing; editing `solve` may change `solve.go`'s captured
  parameters and so its hash. Fine, but tests of hash stability should
  include a `where`.
- **Layout.** `where` must be recognised only at the right indentation. A
  golden-test parser suite is needed (the `where` of `ability … where`
  doesn't collide: it's on the declaration's first line).
- **Generating types for captured variables.** The ability code builds
  *surface* declarations, but a captured variable's type is only known as an
  elaborated term (it may come from inference). So lifting must work on
  elaborated terms, or the surface syntax needs a way to carry an
  already-elaborated type. This is the main design work (§7).

### 2.9 Test plan

- Accept: an accumulator `go`; a local function using an outer variable; a
  local function whose type mentions an outer variable dependently
  (`j <= i`); mutual recursion between two local functions and between a
  local function and the enclosing one; a local lemma; a local partial
  function; a local function performing an ability of the enclosing row.
- Reject: a missing local signature; a duplicate name across two equations;
  a non-decreasing local recursion (with the error naming `go`); a local
  lemma used inside its own subject's cycle (`E-MUTUAL-SIGNATURE`).
- Compare: for a set of generated programs, rewrite top-level helpers into
  `where` blocks mechanically; the results of `test` and the JS outputs'
  behaviour must be identical (a cheap oracle).
- JS snapshot: `solve.go` as a loop.

## 3. `match` expressions

### 3.1 Proposed syntax

```
describe : List Nat -> Text
describe xs =
  match xs with
    | Nil       -> "empty"
    | Cons x Nil -> "one"
    | _         -> "many"
```

- `match e with` followed by alternatives `| pattern -> expression`, lined
  up like a handler's clauses. On one line:
  `match xs with | Nil -> 0 | Cons x _ -> x`.
- **Several scrutinees** at once: `match a, b with | Zero, _ -> … | Succ m, Zero -> …`.
- **Patterns** are exactly the equation patterns: constructors, variables,
  `_`, numbers, records (`{ name, .. }`), tuples (§5), `()`.
- **Why `match … with`, not `case … of`?** It reads like the existing
  `handle … with | …`, and like Lean. `syntax.md` currently says "a `case`
  expression"; either would work. Either way the word becomes a keyword,
  so no user definition can be called `match` (or `case`). (Question 1.)

### 3.2 What it means: an auxiliary definition

A `match` becomes a hidden top-level definition with one equation per
alternative, then the `match` is replaced by a call to it. The definition
takes the captured outer variables (as for `where`, §2.2) and then the
scrutinees:

```
-- written, inside  f : (n : Nat) -> List Nat -> Nat
f n xs = 1 + match xs with
               | Nil       -> n
               | Cons x _  -> x + n

-- made
f.match1 : Nat -> List Nat -> Nat
f.match1 n Nil        = n
f.match1 n (Cons x _) = x + n

f n xs = 1 + f.match1 n xs
```

This is what Lean does ("translated to applications of recursors via
auxiliary matching functions") [L2] and what Idris 2 does for `case` [I2].
The auxiliary definitions are numbered within the enclosing definition, so
edits elsewhere in the file don't renumber them. The equations go through
the existing pattern compiler, so exhaustiveness (`E-NONEXHAUSTIVE`), number
patterns, record patterns, `()` and the `E-PROP-ELIM` rules are reused
unchanged.

**The result type.** The auxiliary definition needs a type, so `match`
needs to know its result type:

- **When it's checked** against an expected type (the usual case: an
  equation's right-hand side, a function argument, an annotated `let`),
  that's the result type, with the scrutinee generalised (next section).
- **When it's inferred** (e.g. `let y = match …` with no annotation), the
  first alternative's type is inferred and used for all of them; it mustn't
  mention that alternative's pattern variables (`E-CANNOT-INFER` with a note
  suggesting an annotation otherwise).

### 3.3 Dependent `match`: refining types in proofs

The interesting case is a proof, or a function whose result type mentions
the thing being matched. Example:

```
theorem appendNil : (xs : List a) -> append xs Nil = xs
appendNil xs =
  match xs with
    | Nil       -> rfl
    | Cons y ys -> cong (Cons y) (appendNil ys)
```

In the `Cons` branch the goal must become
`append (Cons y ys) Nil = Cons y ys`, or `cong …` won't fit. The rule that
makes this work is Lean's: **every occurrence of a scrutinee in the expected
type, and in the types of other variables, is abstracted** [L2] ("The
pattern match elaborator automatically determines the motive by finding
occurrences of the discriminants in the expected type"). A *motive* is just
this abstracted type: the result type as a function of the scrutinee.

Concretely, when the scrutinee is a variable `xs` of the enclosing equation:

1. the auxiliary definition takes `xs` itself as its scrutinee parameter
   (it's not captured separately);
2. other captured variables whose types mention `xs` come *after* it (so
   matching on `xs` refines their types too, by the existing substitution);
3. its result type is the expected type, which mentions `xs`.

```
appendNil.match1 : [a : Type] -> (xs : List a) -> append xs Nil = xs
appendNil.match1 Nil         = rfl
appendNil.match1 (Cons y ys) = cong (Cons y) (appendNil ys)
appendNil xs = appendNil.match1 xs
```

The pattern compiler substitutes `Cons y ys` for `xs` in the goal, exactly
as for an equation. So **`match` refines types in proofs just as equations
do**, and the recursive call `appendNil ys` is checked by size change through
the pair `appendNil → appendNil.match1 → appendNil`: `xs` is passed as is,
then `ys` is a field matched out of it, so the composed call is smaller.

When the scrutinee is an **expression** (`match length xs with …`), its
occurrences in the expected type are replaced by the new parameter (found by
the same conversion check `unify` uses, as Lean does syntactically
**unverified** in detail). Facts about the original expression are lost in
the branches, a known pitfall: the branch for `0` doesn't learn
`length xs = 0`. Idris 2 has exactly this issue with `case` [I2]. Lean's fix
is to name the equation: `match h : e with`, which gives `h : e = p` in each
branch [L2]. That is cheap here too: the auxiliary definition takes one more
parameter `h : e = s` after the scrutinee `s`, the call passes `rfl`, and
matching `s` refines `h`'s type. Recommendation: build `match h : e with` in
the same stage, since proofs will need it (question 5).

A `match` in a *type* (in a signature) is lifted the same way and computes
whenever its scrutinee is a constructor, like any definition.

### 3.4 Kernel, evaluation, JavaScript

- **Kernel**: no change. The alternative would be allowing `Case` on any
  variable anywhere in a term. That would touch conversion, the termination
  checker and the JS generator (which today panics on a nested `Case`), all
  in trusted code, for no gain in what can be expressed. Lean and Idris 2
  both lift instead.
- **Equality of two `match`es**: two textually identical `match`
  expressions in different places are different definitions, so they're not
  equal by computation unless their scrutinees are constructors. Agda
  documents the same for pattern lambdas ("pattern lambdas are
  *generative*") [A1]. Rarely matters; worth a sentence in the docs.
- **Evaluation**: one extra call per `match`.
- **JavaScript**: one extra curried call. An auxiliary definition used once
  (always the case for `match`) could be inlined by the generator as a
  `switch` in place, later, if a benchmark shows the calls matter.

### 3.5 Interaction with records and numbers

- **Record patterns** need the scrutinee's type to be known. It is: the
  scrutinee is inferred first. (`match p with | { name, .. } -> name`.)
- **Number patterns** follow the equation rules
  ([syntax.md](../syntax.md#declarations)): `| 0 -> … | n -> …` learns
  nothing about `n` in the second branch; mixing with `Zero`/`Succ` counts
  down. Nothing new.

### 3.6 Errors, risks, tests

- Errors: `E-NONEXHAUSTIVE` reported at the `match`, listing the missing
  patterns; the name `f.match1` never shown (say "this `match`").
- Risk: the motive. Abstracting occurrences of an expression scrutinee can
  produce an ill-typed motive (the classic problem with dependent pattern
  matching). When that happens, report it plainly and suggest matching on a
  variable or naming the equation (`h :`). Lean offers `(motive := …)` for
  this; we can wait until someone needs it.
- Risk: effects. A `match` inside an effectful block whose branches perform
  abilities gives an auxiliary definition with a row (the enclosing one, with
  its row variable captured). This reuses the effect translation of ordinary
  effectful definitions, but it's where most bugs will be.
- Tests: the AoC programs' `rndStep`/`rndJoin`/`combineStep` helpers
  rewritten as `match`; `appendNil` and a proof needing generalisation of a
  hypothesis; a `match h :` proof; a non-exhaustive `match`; a `match` in
  an effectful block with abilities in its branches; a `match` in a type;
  number and record patterns; a `match` inside a `where` function; a JS
  snapshot.

## 4. Patterns in `let` and in lambdas

### 4.1 Syntax and the rule: the pattern must always match

```
let (q, r) = divMod n 7
let { pos, atZero, .. } = acc
let MkPair a b = p
foldl (\acc (k, v) -> acc + v) 0 entries
map (\{ name, .. } -> name) people
```

A pattern in a `let` or a lambda must be **irrefutable**: it matches every
value of its type. That means it's built only from variables, `_`, records,
tuples, and constructors of types that have exactly one constructor
(nested freely). Anything else (`let Cons x xs = ys`, `let 0 = n`,
`\(Just x) -> …`) is an error:

> `E-LET-REFUTABLE`: this pattern doesn't match every `List Nat`
> (`Nil` isn't covered). Use `match` to say what happens otherwise.

The check is the existing exhaustiveness check on a one-row match, so
"irrefutable" means exactly "the one alternative covers everything", and a
type with one constructor plus impossible ones (`()` cases) counts.

How other languages choose here, all for partial languages where a crash is
possible: OCaml allows a refutable `let` and raises `Match_failure` at run
time (with a warning) [O1]; Haskell's `let` patterns are lazy and fail only
when a variable is used [H1, §3.12]; Elm allows only single-constructor
types, tuples and records [E1]. A total language can't crash, so Elm's rule
(an error) is the only fit; Agda also allows only record constructors in
`let` [A2].

### 4.2 What it means

`let pat = e` followed by the rest of the block is
`match e with | pat -> rest`, with one alternative (§3). A lambda
`\pat -> body` is `\x -> let pat = x` … `body` (Haskell defines its lambda
patterns this way [H1, §3.3]). Several pattern parameters are several
`let`s.

**Why `match` and not projections** (`let p = e; let q = fst p; let r = snd p`,
as Agda does for records [A2])? Projections are cheaper in JS, but:

- a projection's result has *unknown* size for termination until records
  stage 2 ([records.md §6.4, §7.5](records.md#64-termination)), whereas
  matching gives "smaller", so `let Node x kids = t` then recursing on
  `kids` would be refused;
- ordinary one-constructor data types (not records) have no projections;
- types refine: after `let (a, b) = p` the checker knows `p` is
  `(a, b)` when `p` is a variable, as for any `match`.

The JS cost (one call) can be removed later by the inlining of §3.4.

**Effects:** in an effectful block, `let (a, b) = readPair ()` runs
`readPair ()` once, first; the rest of the block (which may perform
abilities) is the single alternative.

**`let` in `where` and at top level**: not proposed. Top-level
`(a, b) = …` would define two names from one computation, which needs
a different translation and isn't asked for.

### 4.3 Parsing

- `let` takes a pattern instead of a name. A plain lowercase name is still a
  variable pattern, and `let x : T = e` keeps working; `let (a, b) : (Nat, Nat) = e`
  is allowed too.
- In a lambda, `\(x : T) -> …` is an annotated parameter, while `\(a, b)`,
  `\(MkPair a b)` and `\{ … }` are patterns. They're told apart by a
  lowercase name followed by `:` right after `(`.
- Multi-alternative pattern lambdas (Haskell's `\case`, Agda's
  `λ { … }` [A1]) are not proposed: `\x -> match x with …` is as short
  and keeps one way of doing it.

### 4.4 Errors, risks, tests

- New: `E-LET-REFUTABLE` (for `let` and lambdas), naming a missing case.
- Risk: small once `match` exists. The parser change for lambdas needs
  golden tests next to records' `\{` (a lambda over a record pattern) and
  ability rows.
- Tests: tuple, record and nested single-constructor patterns; a refutable
  pattern in each position; a number pattern; a pattern `let` in an
  effectful block; `let (a, b) = …` in a proof whose goal mentions the
  scrutinee variable; termination through `let Node x kids = t`.

## 5. Tuples

### 5.1 Proposal

| Written | Means |
|---|---|
| `(A, B)` in a type | `Pair A B` |
| `(a, b)` in an expression | `MkPair a b` |
| `(p, q)` in a pattern | `MkPair p q` |
| `(a, b, c)` | `(a, (b, c))`, so `Pair A (Pair B C)` |
| `()` | unchanged: the unit type and its value |
| `(e)` | unchanged: grouping |

- **Three or more nest to the right**, as in Idris 2 ("represented as nested
  pairs") [I1] and Lean. One type, `Pair`, with one set of lemmas and
  functions (`fst`, `snd`, `swap`, `zip`), covers every size; a pattern
  `(a, b, c)` just works. The alternative, separate types per size (Haskell,
  or Elm, which allows only up to three [E2]), needs a type and functions
  per size and gives no help in proofs.
- **No one-element tuple**: `(e)` is grouping and `(e,)` is a parse error.
- **Annotations**: `(e : T)` keeps meaning an annotation, and `(a, b : T)`
  is a parse error with a note: "to annotate one component, write
  `(a, (b : T))`; to annotate the pair, `((a, b) : T)`".
- **Function types**: `(x : A) -> B` is a binder and stays one;
  `(A, B) -> C` is a function from a pair.
- **No new kind of type**: the tuple syntax only stands for `Pair`.
  So a tuple of a `Prop` and data isn't possible while `Pair`'s parameters
  live in `Type` (**unverified** whether `Prop ⊆ Type` holds in the checker);
  a dependent pair (`(n : Nat ** n < 5)` in Idris [I1]) is a separate
  feature, and a declared record with a dependent field already covers it.

Since `Pair` is the built-in meaning of `(a, b)`, the elaborator finds it by
identity (the namespaces lane's stage 0 "built-ins bound by identity"), not
by name, so a user's own `Pair` doesn't change what `(a, b)` means.

### 5.2 JavaScript

Today a pair crosses the boundary as `{ tag: "MkPair", fst, snd }`. Once
tuples are the normal way to return two things, JS callers will meet them
often. Options:

1. **Keep it.** No work; `result.fst`, `result.snd.fst` for a triple.
2. **Arrays at the boundary**: a pair is a readonly two-element array
   `[a, b]`, TypeScript `readonly [A, B]`. A pair whose second component's
   type is itself a pair is flattened: `(Nat, Text, Bool)` is
   `readonly [bigint, string, boolean]`. This is what a TS programmer
   expects from a function returning a tuple.

Flattening is well defined because an export's types are concrete: the
codec for `Pair A B` checks whether `B` is a `Pair`. The catch is that
`Pair Nat (Pair Nat Nat)` written on purpose as a nested pair also becomes
`[n, m, k]`, since it's the same type as `(Nat, Nat, Nat)`. That's
consistent but may surprise; a `Pair` inside the *first* component stays
nested (`((a, b), c)` is `[[a, b], c]`). Inside the generated code nothing
changes: pairs stay tagged objects, and only the boundary codec converts.
Decoding checks `Array.isArray` and the exact length, following
[DESIGN.md §12's rules for objects at the boundary](../../DESIGN.md#objects-at-the-boundary).

Recommendation: **2**, as a separate small change after the syntax (it
changes the boundary contract, so it needs the user's agreement, question 7).

### 5.3 Relation to anonymous records

Records' stage 3 (anonymous records, deferred, [records.md U3](records.md#decisions-16-october-2026))
would make `{ quotient : Nat, remainder : Nat }` a type without declaring
it. Standard ML treats tuples as records with numeric labels (`(a, b)` is
`{1 = a, 2 = b}`; **unverified**, from memory of the Definition of
Standard ML). Doing that here would make tuples flat and anonymous records
and tuples one feature. It's not recommended: positional pairs nest well,
are what the prelude and proofs already use, and anonymous records'
generated types are keyed by sorted field names, which numbers would
fit only awkwardly. Tuples as `Pair` don't block stage 3, and stage 3's
literals use braces, so there's no syntax clash. (Stage 3 would want sorted
JS keys; tuples would be arrays. Different, but each predictable.)

With namespaces and dot notation, `p.fst` will work for pairs as for
records (`fst` moving into `Std.Pair`), so tuples don't need field syntax
of their own.

### 5.4 Risks and tests

Small. Golden parser tests: `()`, `(e)`, `(a, b)`, `(a, b, c)`,
`((a, b), c)`, `(a, b) -> c`, `(x : A) -> B`, `(a, b : T)` (error),
`(e,)` (error), tuples in patterns nested in constructors and records.
Elaboration tests: the three forms of `(a, b)`; a triple pattern; a user
`Pair` not affecting `(a, b)`. JS snapshot and boundary round trip if
option 2 is chosen, including a 1,000-deep right-nested value (the codec
must not recurse).

## 6. Optional: knowing more expected types

### 6.1 The problem

```
type Rot = { dir : Dir, amount : Nat }

parse : Nat -> Maybe Nat -> Maybe Rot
parse n m = maybeThen m (\x -> Just { dir = TL, amount = n + x })   -- E-CANNOT-INFER
```

The user decided that a record literal with no known type is an error
([records.md U6](records.md#decisions-16-october-2026)), and that stays.
But here the type *is* knowable: `parse`'s result is `Maybe Rot`, and
`maybeThen : Maybe a -> (a -> Maybe b) -> Maybe b`, so `b` must be `Rot`.
The compiler doesn't see it because of the order it works in (§1): it
checks the arguments first, left to right (`m` fixes `a`, then the lambda is
checked against `a -> Maybe ?b` with `b` still unknown), and compares the
result `Maybe ?b` with `Maybe Rot` only at the end.

### 6.2 Proposal: compare the result type first

When an application is *checked* against an expected type, compare the
function's result type with it **before** checking the explicit arguments,
whenever the result type doesn't depend on those arguments' values. For
`maybeThen`, `Maybe ?b` against `Maybe Rot` solves `b = Rot`, and the
lambda's body is then checked against `Maybe Rot`, so the record literal has
its type.

This is Lean 4's `propagateExpectedType`, which it does "as soon as we find
the first explicit" argument, and which "will do nothing if the resultant
type depends on the remaining arguments" (or contains optional/auto
parameters) [L3]. Constructors already get this treatment in Stitchwort
(`ctor_app` uses the expected type up front), which is why
`Just { … }` checked against `Maybe Rot` works; the proposal extends it to
every function.

Conditions, adapted:

1. **Only in check mode** (an expected type is known).
2. **The result type mustn't mention the explicit arguments** still to be
   checked (a dependent result like `(n : Nat) -> Vec n` is skipped).
3. **If the comparison fails, ignore it** and continue as today, so the error
   reported stays the one at the end. This matters because the final check
   isn't plain equality: a function whose row lists abilities in another
   order is accepted by a coercion (`effects::coerce` in `fallback`), and a
   total function fits where a partial one is expected. Propagation must not
   turn those into errors. **Open point:** whether `unify` can leave
   unknowns partly solved when it returns "no" (I didn't check `unify.rs`
   closely). If it can, the early comparison needs a trial mode that undoes
   its solutions on failure.

### 6.3 What it fixes, and what it doesn't

Fixed (the literal's type becomes known from the context):

- `maybeThen m (\x -> Just { dir = TL, amount = x })` where the result
  type is known: a signature, an argument position, an annotation;
- `map (\x -> { x = x, y = 0 }) xs` checked against `List Point`;
- `foldl step { pos = 50, atZero = 0, passes = 0 } ls` works *today*
  (left to right, `step` fixes the accumulator type first), but
  `foldr (\r acc -> …{ … }…) { … } rs` with the literal before anything
  fixes its type will work only with propagation.

Not fixed, by design (U6):

- `let r = maybeThen m (\x -> Just { dir = TL, amount = x })` with no
  annotation and nothing else saying what `r` is: still `E-CANNOT-INFER`,
  with the existing note suggesting `(… : Rot)`.

Possible later, not proposed: checking lambda arguments *after* the other
arguments (Lean postpones some arguments [L3]), so `maybeThen (\x -> …) m`
style APIs also learn `a` from `m`.

### 6.4 Effects on messages and risks

- Some errors move from "the whole application has the wrong type" to "this
  argument has the wrong type", which is usually clearer. Rule 3 keeps
  cases where the early comparison fails unchanged.
- Risk: solving an unknown too early with the wrong solution. With rule 3
  and no subtyping beyond rows, the solution is one the final check would
  have forced anyway; tests should cover rows (the coercion and the
  total-for-partial cases) specifically.
- Tests: the three examples above; an application whose expected type
  differs only by row order; a partial/total mismatch; a dependent result
  type (skipped); error-message snapshots before and after on the whole
  `examples/reject` suite (they should be identical except where improved).
- Kernel: none. JS: none.

## 7. Recommended order and implementation plan

"Opus" marks thinking-heavy parts (design decisions, soundness, the
elaborator's core); "Sonnet" marks mechanical parts (parsing, desugaring
to existing forms, tests, docs).

**Step 1. Tuples (§5).** Smallest, independent, immediately useful.
- Sonnet: parser and AST (`Expr::Tuple`, `Pattern::Tuple`), desugaring to
  `Pair`/`MkPair` by identity, golden tests, `syntax.md`.
- Sonnet (later, if question 7 says yes): JS boundary codec for pairs as
  arrays with right-nested flattening, `.d.ts`, round-trip tests.

**Step 2. Expected-type propagation (§6).** Independent; small but touches
inference.
- Opus: the change in `check.rs` (application in check mode), conditions 1
  to 3, the trial-unification question.
- Sonnet: tests and the reject-suite message comparison.

**Step 3. Lifting machinery and `match` (§3).** The core of the work.
- Opus: a "lift" routine: given the current context, the free variables an
  expression uses and an expected type, compute the captured variables
  (closing over the variables their types mention), order them (those
  depending on the scrutinee after it), abstract scrutinee occurrences (the
  motive), build the auxiliary definition's type as an elaborated term, run
  the pattern compiler on the alternatives, and register the definition
  with the module's grouping so termination sees it. Decide how this
  interacts with group checking: an auxiliary definition is created while
  checking its enclosing definition's body, so it must join that
  definition's group (it can call the enclosing function, and vice versa).
  Effects: auxiliary definitions with rows.
- Opus: `match h : e with`.
- Sonnet: parser (`match … with`, alignment rules like `handle`), error
  messages hiding auxiliary names, tests, JS snapshots, `syntax.md`.

**Step 4. Pattern `let` and lambdas (§4).** Mostly desugaring to step 3.
- Sonnet: parser, desugaring, `E-LET-REFUTABLE` from the one-row
  exhaustiveness check, tests.
- Opus: review the effectful-block case (the rest of the block as the
  alternative).

**Step 5. `where` (§2).** Reuses step 3's lifting, adds declarations.
- Opus: scoping (equation variables, local signatures seeing outer names,
  the type-variable rule of §2.1), how local definitions join the module's
  dependency graph (strongly connected components across the boundary
  between local and top-level), plain values as `let`s, proofs in `where`.
- Sonnet: parser and layout, `E-WHERE-*` errors, name printing, tests, docs.
- After namespaces lands: make `f.go` writable, with the `E-DUPLICATE`
  reservation of §2.6 (a small follow-up in that lane's code).

Why this order: tuples and propagation are cheap and independent; `match` is
the general mechanism that `let`/lambda patterns and `where` reuse; `where`
is last because it also needs the module-level dependency graph to see
local definitions, and because `f.go` only becomes nameable from outside
once namespaces are merged. AoC's friction item 5 says `match` and pattern
`let` remove "most of" the helper definitions, so most of the benefit
arrives at step 4.

## 8. Questions for the user

**Decided (16 October 2026):** the user agreed with every recommendation
below (1 to 9): `match e with`; local names unique across the definition;
a `where` value computed once; capture only the variables used;
`match h : e with` in the first version; a refutable `let`/lambda pattern is
the compile-time error `E-LET-REFUTABLE`; pairs as flattened JS arrays (a
separate change); the result-type-first change is built; the order in §7.
The note goes to the external reviewer before implementation.

1. **`match e with` or `case e of`?** Recommendation: `match … with | …`,
   matching `handle … with | …` and Lean. Either reserves the word.
2. **Local function names unique per definition** (rather than per
   equation)? Recommendation: yes, so `f.go` always means one thing in
   proofs and messages.
3. **`where`-bound plain values: computed once (`let`-like, opaque in
   types) or definitions (transparent in types, recomputed at each use)?**
   Recommendation: computed once, like Haskell's sharing; a value that must
   compute in types goes to top level.
4. **Captured variables: only those used, or all of the equation's?**
   Recommendation: only those used (Lean's choice). Lemmas about `f.go` may
   need updating when `go` starts using another outer variable.
5. **`match h : e with`** (naming the equation between the scrutinee and the
   pattern) in the first version? Recommendation: yes; it's cheap and proofs
   about `match` on an expression need it.
6. **Refutable patterns in `let`/lambdas are errors** (`E-LET-REFUTABLE`),
   never a runtime failure? Recommendation: yes (Elm's rule; the only one
   that keeps totality).
7. **Pairs at the JS boundary as arrays, with right-nested pairs
   flattened** (`(Nat, Text, Bool)` is `[bigint, string, boolean]`)?
   Recommendation: yes, as a separate change after the syntax. It changes
   the boundary for existing `Pair` exports.
8. **Expected-type propagation (§6)**: build it? Recommendation: yes,
   before or alongside `match`; it removes the `mkRot` workaround in the
   common cases without changing the U6 rule.
9. **Order**: tuples → propagation → `match` → pattern `let`/lambda →
   `where`? Recommendation: yes; `where` waits for namespaces to be merged
   so that `f.go` is nameable in proofs.

## Sources

- [A1] Agda documentation, "Lambda abstraction" (pattern lambdas translated
  to a fresh function definition; "pattern lambdas are *generative*"):
  <https://agda.readthedocs.io/en/latest/language/lambda-abstraction.html>
- [A2] Agda documentation, "Local definitions: let and where" (`let` patterns
  only for record constructors, translated to projections; `where` sees the
  clause's pattern variables; named `module M where` blocks):
  <https://agda.readthedocs.io/en/latest/language/let-and-where.html>
- [E1] Exercism, Elm track, "Pattern matching" (destructuring for
  single-variant custom types, tuples and records):
  <https://exercism.org/tracks/elm/concepts/pattern-matching>
- [E2] Elm Discourse, "Purpose of 3-tuples" (tuples limited to three
  elements since 0.19): <https://discourse.elm-lang.org/t/purpose-of-3-tuples/5764>
- [H1] Haskell 2010 Report, chapter 3 (§3.3 lambda patterns via `case`;
  §3.12 lazy `let` patterns; §3.13 `where` over guards) and §4.4.3:
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
  parameters, mutually recursive with the enclosing definition, may not
  mention each other in their signatures):
  <https://lean-lang.org/doc/reference/latest/Definitions/Recursive-Definitions/>
- [L2] Lean Language Reference, "Pattern matching" (auxiliary matching
  functions; motive from occurrences of discriminants in the expected type;
  generalisation; `match h : e with`):
  <https://lean-lang.org/doc/reference/4.23.0/Terms/Pattern-Matching/>
- [L3] Lean 4 source, `src/Lean/Elab/App.lean`, `propagateExpectedType` and
  its doc comment:
  <https://github.com/leanprover/lean4/blob/master/src/Lean/Elab/App.lean>
- [O1] OCaml manual, "Expressions" (`let` and `function`: "If one of the
  matchings fails, the exception Match_failure is raised"):
  <https://ocaml.org/manual/5.2/expr.html>
