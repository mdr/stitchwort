# Proposal: Lean/Scala-style declarations

**Status:** draft 2, 18 October 2026. Draft 1 went to external review
(verdict: proceed); this draft adopts every must-fix and should-fix as
specification, and records the user's decisions taken after the review
(items 10 to 15 in §7; [Review response](#review-response) maps each
finding to its section). **Lane A (the parser) is built**
([what was built](#lane-a-what-was-built)); the converter, the checker, the
conversion of the code base, and the removal of the old syntax are not.
Answers `TODO.md`'s "Declaration syntax" item: the user decided (18 Oct)
to **replace** Haskell-style declarations (a signature line `f : A -> B`,
then equations `f x = …`) with the Lean/Scala style (typed parameters
written inline, `def add (x : Nat) (y : Nat) : Nat := …`, and cases listed
under one header). This note is the detailed design and the migration plan.
Claims about other languages cite [Sources](#sources); anything not checked
against a source is marked **unverified**. Facts about Stitchwort were
checked against the source at `88dfd7f`.

**The one-sentence version:** every new form is translated by the parser
into the signature-plus-equations it replaces, so the elaborator, kernel
and pattern compiler barely change; comparing content hashes before and
after the conversion is the main test that the migration is right, with
the few deliberate changes listed in advance (§5.4).

**Hashes are not a design constraint.** The user decided (18 Oct) that,
with no users yet, the design isn't bent to keep hashes stable. Where the
new syntax deliberately lowers differently (only exact-arity arms, §2.4),
the expected hash changes are listed and those declarations are compared
structurally instead (§5.4). Hash comparison is only a test oracle for the
migration, not something to preserve.

**No transition period.** The user decided (18 Oct) that a file is read
wholly in one syntax. The parser has a syntax option (`Syntax::Old`, the
default for now, or `Syntax::New`); there are no mixed declarations and no
mixed files. The switch happens in one commit later (§5.6).

## Contents

0. [Summary: before and after](#0-summary-before-and-after)
1. [What other languages do](#1-what-other-languages-do)
2. [The design](#2-the-design)
3. [Does anything of the old style stay?](#3-does-anything-of-the-old-style-stay)
4. [Errors, printing and the playground](#4-errors-printing-and-the-playground)
5. [Migration](#5-migration)
6. [Implementation plan](#6-implementation-plan)
7. [Questions for the user](#7-questions-for-the-user)
- [Review response](#review-response)

## 0. Summary: before and after

A one-line function:

```
-- before
total : Nat -> List Text -> Nat
total k lines = (lines.map (joltage k)).sum

-- after
def total (k : Nat) (lines : List Text) : Nat := (lines.map (joltage k)).sum
```

A function defined by cases. The arguments it takes apart go after the
colon, and each case is an **arm** starting with `|`, with one pattern for
**every** argument after the colon, separated by commas (as `match`
already does):

```
-- before
length : List a -> Nat
length Nil         = 0
length (Cons x xs) = Succ (length xs)

-- after
def length : List a -> Nat
  | Nil       => 0
  | Cons x xs => Succ (length xs)
```

Named parameters and cases together. Named parameters are the same in every
arm; the arms match what comes after the colon:

```
def total (k : Nat) : List Text -> Nat
  | Nil       => 0
  | Cons l ls => joltage k l + total k ls
```

A theorem, proved by cases:

```
-- before
theorem appendNil : (xs : List a) -> List.append xs Nil = xs
appendNil Nil         = rfl
appendNil (Cons x xs) = Eq.cong (\ys -> Cons x ys) (appendNil xs)

-- after
theorem appendNil : (xs : List a) -> List.append xs Nil = xs
  | Nil       => rfl
  | Cons x xs => Eq.cong (ys => Cons x ys) (appendNil xs)
```

An effectful function, a value, a test, an export:

```
def main () : {IO, Partial} () := report (solve (IO.readAllLines ()))

def example : List Text := ["987654321111111", "811111111111119"]

test "parse" := parseBank "102" == [1, 0, 2]

export def identityNat (n : Nat) : Nat := n
```

The changes, all of them:

| | Before | After |
|---|---|---|
| a definition | `f : T` then `f p… = e` | `def f params : T := e`, or `def f params : T` then `\| p, … => e` arms |
| a theorem | `theorem f : T` then equations | `theorem f params : T := e`, or arms |
| the body | `= e` | `:= e` (`=` is only equality now) |
| an arm's patterns | fewer than the arguments allowed | exactly one per argument after the colon |
| `let` | `let x = e` | `let x := e` |
| a test | `test "n" = e` | `test "n" := e` |
| export | `export` before the signature, same line or alone | `export def …` / `export theorem …` |
| arms of `match` and `handle` | `\| p -> e` | `\| p => e` |
| a handler's operation clause | `\| op x => k -> e` | `\| op x, k => e` |
| a lambda | `\x -> e` | `\x => e` |
| a unit parameter | `main : () -> …` / `main u = …` | `def main () : … := …` |

Unchanged: types (`(x : A) -> B`, `[x : A] -> B`, `[auto h : P] -> B`,
`{IO} A`), `type` declarations (data and records), `ability` declarations,
`import`, record literals `{ name = e }`, named implicit arguments
`f [x := e]`, `if`, dot notation, qualified names (`def List.sum …`),
patterns, layout of blocks.

## 1. What other languages do

**Lean 4** is the model. A header is "zero or more parameters, followed by
a colon and a type" [L1]. Parameters before the colon are in scope in the
body; names bound in the type after the colon are only in scope in the type
[L1]. Binders are `(x : A)` explicit, `{x : A}` implicit, `[C]` instance
implicit, `⦃x : A⦄` strict implicit [L1]. The body follows `:=`, or the
definition is a list of `| pattern => …` arms with no `:=` [L2]. Named
parameters and arms mix [L2, L3]:

```lean
def add (n : Nat) : (k : Nat) → Nat
  | 0 => n
  | k' + 1 => 1 + add n k'
```

`theorem` has the same syntax as `def`, but its statement must be a
proposition (and it's irreducible) [L4]. Local helpers go in a `where`
after the body, and may use the header's parameters (`a` below) [L5]:

```lean
def replicate (n : Nat) (a : α) : List α :=
  loop n []
where
  loop : Nat → List α → List α
  | 0, as => as
  | n+1, as => loop n (a::as)
```

Termination hints (`termination_by`, `decreasing_by`) go after a body and
before `where`, one per function [L6]. Unbound names in a signature become
implicit parameters by default ("auto-bound implicits"); the manual warns
that "misspelled identifiers or missing imports can end up as unwanted
implicit parameters", and offers a stricter mode accepting only single
letters followed by digits [L1]. Mathlib turns auto-binding off [L7]; plain
Lean projects keep it on [L8]. Data types are `inductive T where | c …` and
records `structure P where x : Float …` [L3, L9]; functions in a type's
namespace are declared `def Point.modifyBoth …`, which enables dot
notation [L9]. Lean writes `→` for function types and `=>` in `fun x => …`
and match arms [L10] (that ASCII `->` is accepted for `→` is from memory,
**unverified**).

**Scala 3** writes `def max[T](x: T, y: T)(using ord: Ord[T]): T = …` [S1]:
inline parameters, `=` before the body (Scala has no `=` in types, so no
clash), `using` for compiler-supplied parameters (like our `[auto …]`).
Data types are `enum` with `case` lines [S2]; records are `case class`
[S3]; `extension (c: Circle) def circumference …` adds dot-notation
methods [S4]. Indentation is significant by default, with optional
`end f` markers suggested for long regions [S5]. Scala uses `=>` for
lambdas, `case … =>` arms and function types alike [S6].

**Idris 2 and Agda** keep the separate signature. Agda: "a function is
defined by first declaring its type followed by a number of equations
called clauses" [A1]; Idris "requires type declarations for all
functions" [I1]. Neither documents *why* (we found no official statement),
so the following is our inference, **speculative**: each clause can bind
different names for an argument, or none (`plus Z y`, `plus (S k) y`);
Agda's dot patterns (`root .(m * m) (sq m) = m`) and `with` clauses
rewrite the left-hand side per clause [A1, A2]; and a name in the
signature (`(n : Nat)`) often isn't the name a clause wants. Lean solves
the same problem by putting whatever is taken apart after the colon,
where names in the type are documentation only. Stitchwort has no dot
patterns or `with`, so Lean's answer fits.

**Effects in headers.** Koka writes the effect between the colon and the
result: `fun square2(x : int) : console int { … }` [K1]. F\* likewise:
`let id (a:Type) (x:a) : Tot a = x`, with `Dv` for code that may not
terminate [F1, F2]. Unison and Roc keep separate signature lines;
Unison attaches abilities to the arrow (`a ->{g, Abort} a`) [U1], and Roc
marks an effectful function type with `=>` instead of `->` [R1]. So an
effect row right after the header's colon, `def tick () : {State Nat} Nat`,
has precedent (Koka, F\*), and Stitchwort's rows already sit there in
types.

**Readability.** The common complaint about separate signatures is that
`replace :: Text -> Text -> Text -> Text` doesn't say which argument is
which [G1]. Mainstream languages (Gleam [G2], Rust, Swift, Kotlin,
TypeScript) all write `name(param: Type)`. We found no study, only
opinion.

## 2. The design

### 2.1 Keywords and the grammar

- **`def`** starts every definition: functions, values, type-valued
  functions (`def Not (p : Prop) : Prop := p -> Void`). Same as Lean and
  Scala, and as the user's example. `def` becomes reserved; no existing
  `.sw` file uses it as a name (checked with `git grep`).
- **`theorem`** replaces `def` for propositions; otherwise identical, as
  in Lean [L4]. Its rule (the type must be a proposition) is unchanged.
- **`test "name" := e`**: unchanged except `:=`.
- **`export`** becomes a modifier on the same line: `export def f …`,
  `export theorem …`. The rule "a line holding only `export` belongs to
  the next declaration" goes.
- **`main`** is an ordinary `def main () : {IO} () := …`. No keyword.
- `type`, `ability`, `import`, `where`, `match`, `handle`, `let`, `if`:
  unchanged.

**The grammar** (layout rules in §2.10 say where lines may break and how
far they're indented):

```
definition ::= "export"? ("def" | "theorem") name binder* ":" type body
body       ::= ":=" expr whereBlock?
             | arm+ whereBlock?
arm        ::= "|" pattern ("," pattern)* ("=>" expr)?
binder     ::= "(" lname+ ":" type ")"
             | "[" lname+ ":" type "]"
             | "[" "auto" lname ":" type "]"
             | "(" ")"
whereBlock ::= "where" helper+
helper     ::= ("def" | "theorem") name binder* ":" type body
test       ::= "test" string ":=" expr
```

- `name` may be qualified (`List.sum`), as a signature's name can be
  today.
- An arm may leave out `=> expr` only if one of its patterns is the absurd
  `()` (today's rule for equations, `crates/syntax/src/parser.rs`,
  `equation`).
- `type` ends at the first token that can't continue it: `:=`, or a `|`
  that starts a line outside any brackets (§2.10, rule L4). A `|` inside
  `{ … }` belongs to the bracketed construct (an open row
  `{State s | e} B`, a record update), as today.

**The parser commits early.** Once it has read `def`, `theorem` or
`export`, it is parsing a declaration header with this grammar: it never
backtracks and retries the tokens as an expression or an old-style
equation. A malformed binder is reported as a malformed binder ("expected
`)` to close the parameter `(x : Nat`"), not as "unexpected `(`" further
on. A file is read wholly in one syntax, chosen by the parser's option
(§5.6), so the parser never has to decide between old and new
declarations.

### 2.2 `:=` for definitions; `=` only for equality

The user's example used `=` (`def add (x : Nat) (y : Nat) : Nat = …`). We
recommend `:=` instead, because the header and the body now share a line,
and in a dependently typed language the type often contains `=`:

```
theorem zeroPlus (n : Nat) : 0 + n = n = rfl     -- which `=` starts the body?
theorem zeroPlus (n : Nat) : 0 + n = n := rfl    -- clear
```

With `=` for both, `def p : a = b = c` has two readings (type `a`, body
`b = c`; or type `a = b`, body `c`), and both make sense in Stitchwort,
where a definition may return a proposition. The old style never hit this,
because the signature was on its own line. The parser already meets the
same problem in `let x : T = e`: it parses `T` in a mode that stops at the
first `=` (`no_equals`, `crates/syntax/src/parser.rs`), so
`let h : a = b = p` can't be written without brackets. Lean uses `:=` for
exactly this reason; Scala can use `=` because its types never contain
`=`.

**The rule, as users are told it:** definitions and bindings of values
(`def`, `theorem`, `test`, `let`, local definitions) use `:=`; equality
propositions use `=`. The older structural syntaxes keep their `=`:
`type` declarations and record fields. (Draft 1's slogan "`:=` gives a
name its value; `=` is equality" invites the question why
`{ age = 10 }` doesn't use `:=`; this phrasing doesn't.)

`:=` already appears in Stitchwort for named implicit arguments,
`f [x := e]`, so it isn't a new token.

Why `type` and record fields keep `=`: nothing after them can contain an
equality type ambiguously, and changing them would be churn without a
benefit (question 3):

- **`type` declarations**: `type List (a : Type) : Type = | Nil | …` and
  `type Person = { name : Text, age : Nat }`. The `=` is followed by `|` or
  `{`, never an expression.
- **Record fields**: `{ name = "Alice" }` and `{ p | age = 1 }`. A field
  name is never followed by a type there.

### 2.3 The header: typed parameters

```
def name binder* : ResultType := body
def name binder* : ResultType
  | arm…
```

A binder is one of the forms types already use, written without the arrow:

| Binder | Meaning | Becomes, in the signature | Pattern in each equation |
|---|---|---|---|
| `(x : A)`, `(x y : A)` | explicit parameters | `(x : A) -> …` | the variable `x` |
| `[x : A]`, `[x y : A]` | implicit parameters | `[x : A] -> …` | none (bound by name) |
| `[auto h : P]` | evidence found by `auto` | `[auto h : P] -> …` | none (bound by name) |
| `()` | a parameter of type `()` that isn't used | `() -> …` | `_` |

- **Types are required** on named parameters: the header *is* the
  signature. (Lean allows untyped binders; we don't need them, and the
  reviewer agreed: required types keep auto-binding, expected types and
  dependent scope predictable.)
- **Order is kept**: binders become the signature's arrows in the order
  written, so `def cong (f : a -> b) [x y : a] (p : x = y) : f x = f y`
  is exactly today's `(f : a -> b) -> [x y : a] -> x = y -> f x = f y`.
- **Brackets mean what they mean in types.** Readers coming from Lean
  should note that our `[x : A]` is Lean's `{x : A}`, and our
  `[auto h : P]` is closest to Lean's `[inst : C]` or Scala's `using`.
  We keep our brackets: they're used in every type already.
- **`()`** is new and small: `def tick () : {State Nat} Nat := …` instead
  of `tick : () -> {State Nat} Nat` / `tick u = …`. It's common because
  abilities need a function to delay a computation. **It lowers to the
  wildcard pattern `_`**, the simpler of the two choices (the user left
  it to the implementer): no new AST node, no change to the elaborator,
  and no clash with an absurd arm (`def f () : Void -> a` / `| ()` would
  misread a header `()` lowered to the `()` *pattern* as a second absurd
  pattern, since `()` without a body means "absurd" in every position,
  `crates/elab/src/lib.rs` near the comment "`()` with a right-hand side
  is the unit pattern"). So `def f () : Nat := 0` is today's `f _ = 0`,
  while `def f : () -> Nat` / `| () => 0` is today's `f () = 0`, which
  splits on the unit value. Both are fine and they compute the same
  thing; their core terms (and hashes) differ, which is accepted. No
  existing equation uses a `()` pattern with a body (`git grep` finds 13
  equations with a `()` pattern, all absurd), so this changes no hash.
- **The result type may start with an ability row**: `: {IO, Partial} ()`.
  A `{` straight after the header's colon starts a row, as it does after
  an arrow today. A definition that isn't a function, `def current :
  {State Nat} Nat := …`, is today's `current : {State Nat} Nat`.

**The translation, exactly.** The parser builds, for each definition:

1. a `Decl::Signature` whose type is the binders turned into arrows in
   front of the written result type: one complete type;
2. one `Decl::Equation` per arm (or one for a `:=` body), whose patterns
   are the header's explicit parameters as variables (`_` for `()`),
   followed by the arm's patterns.

An equation made from an arm carries a small marker, `Decl::Equation`'s
`arm: Option<usize>` (how many of its patterns are the header's
parameters). Only the exact-arity rule (§2.4) uses it. `Signature` has no
marker.

**Auto-bound implicits run over the whole reconstructed type.** Today,
`Elaborator::signature` (`crates/elab/src/lib.rs`) calls
`autobind::auto_bound` once on the signature's complete type
(`Decl::Signature`'s `ty`), and binds the names it finds as implicit
parameters at the front, in order of first use. Because the parser
builds that complete type before the elaborator sees anything, the new
syntax gets exactly the same discovery and order. The invariant for
implementers: **parse the whole header, lower it to the complete type,
then run the existing auto-binding once over that type; never auto-bind a
binder on its own.** There is no per-binder elaboration path, and lane A
must not add one. Lane A's tests compare each of these with its old form
(same lowered AST, same hash):

| Where the auto-bound name first appears | Example |
|---|---|
| the first parameter's type | `def f (x : a) (xs : List a) : Nat := …` |
| only a later parameter's type | `def f (n : Nat) (xs : List a) : Nat := …` |
| only the result type | `def f (n : Nat) : List a := …` |
| an auto binder | `def f (x : a) [auto h : P a] : Nat := …` |
| under another dependent binder | `def f (x : a) (p : P a x) : R a x p := …` |
| after the colon, with arms | `def f (k : Nat) : List a -> Nat` / arms |

The `W-MODULE-NAME` warning's note ("start the type with `[a : Type] ->`")
is reworded for headers: "add `[a : Type]` as the first parameter".

Lean has the same default and the same known risk (a typo becomes a
parameter) [L1]; restricting auto-binding is a separate decision
(question 6).

### 2.4 Cases: arms under the header

```
def pick : Nat -> List Nat -> Nat -> List Nat -> (Nat, List Nat)
  | Zero,   ds,          d, after => (d, after)
  | Succ w, Nil,         d, after => (d, after)
  | Succ w, Cons x rest, d, after =>
    if Nat.leq (d + 1) x then pick w rest x rest else pick w rest d after
```

- **Arms match every explicit argument after the colon**, one pattern
  each, separated by commas, left to right, as in Lean [L2] and as in
  today's `match xs, ys with`. Each arm becomes one of today's equations,
  with the header's named parameters as variables in front. So the
  pattern compiler, exhaustiveness check (`E-NONEXHAUSTIVE`), number
  patterns, absurd patterns and the size-change termination check all see
  what they see today.
- **Exact arity** (the user's decision after review finding 5): every arm
  has exactly as many patterns as the type after the colon has explicit
  arguments. To return a function from an arm, write it as a lambda;
  usually it is clearer to add the argument as a pattern:

  ```
  def f : Nat -> Nat -> Nat
    | Zero,   y => y              -- not `| Zero => y => y`
    | Succ x, y => Succ (f x y)
  ```

  "Explicit arguments after the colon" is counted the way the arity check
  counts today (`crates/elab/src/lib.rs`, the loop after "Bind the
  parameters"): explicit arrows of the type, after unfolding definitions
  (so `def add : BinOp` / `| x, y => …` works when `BinOp` is
  `Nat -> Nat -> Nat`), up to the first thing that isn't a function type,
  such as an ability row (`Nat -> {IO} (Nat -> Nat)` has one). The check
  is today's `E-ARITY`, now also failing when an arm has *fewer* patterns;
  it applies to arms only. A `:=` body has no arity rule: `def f (x : Nat)
  : Nat -> Nat := y => x + y` is fine. A definition with arms but no
  explicit argument after the colon is `E-ARITY` too ("arms need an
  argument after the colon to match; use `:=`").
- **Implicit and auto arguments after the colon are not matched**; they're
  in scope by name in every arm (§2.5).
- **Named parameters can't be matched in arms.** They're the same in every
  arm. To take a named parameter apart, either move it after the colon,
  or make the body a `match` on it. A `match` that is the whole body, on
  parameters, already compiles into the definition's case tree (syntax-
  conveniences §4.3, `matching::in_tree`), so this costs nothing:

  ```
  theorem appendNil (xs : List a) : List.append xs Nil = xs :=
    match xs with
      | Nil       => rfl
      | Cons y ys => Eq.cong (zs => Cons y zs) (appendNil ys)
  ```

  This is a matter of taste; both forms are allowed. The converter (§5)
  writes the arms form, since it is a one-for-one copy of the equations.
  The reviewer noted a usability trap inherited from Lean: putting a
  parameter before the colon and then wanting to match it. `E-ARM-PARAMETER`
  (§4) catches it with the fix.
- **An absurd arm has no body**: `def absurd : Void -> a` / `| ()`. As
  today.
- **Termination clauses**, when they come (DESIGN.md §4's planned
  `decreasing b`), go after the last arm or the body, as in Lean [L6].

Why not let arms bind names for header parameters (`def pick (w : Nat) …`
then `| Zero, … =>` matching `w`)? Then `w` in the body would mean
"the original argument" in some arms and be shadowed in others, which is
exactly what the Idris/Agda style avoids. Lean's split keeps one simple
rule: before the colon, a name that never changes; after it, patterns.

### 2.5 Which names are in scope where

The split by binder kind, stated once (review finding 2):

**In the header and the type** (lexical, left to right): each binder's
names are in scope in the later binders' types and in the result type.
A name bound inside the type after the colon (`(x : A) ->`, `[x : A] ->`,
`[auto h : P] ->`) is in scope in the rest of that type, and shadows an
earlier name, as in any type today.

**In a body or an arm:**

| Bound by | In scope in arms / `:=` body? | In `where` helpers? |
|---|---|---|
| a header binder, explicit, implicit or auto | yes, by its name | yes |
| `()` in the header | no name | no |
| an auto-bound type variable (§2.3) | yes, by name, as today | yes |
| an implicit or auto binder after the colon | yes, by its name in the type | no |
| an explicit binder after the colon, `(x : A) ->` | **no**: type-local; the arm's pattern names the argument | no |
| an arm's pattern variables | yes, in that arm | no |

The "after the colon" rows hold for every implicit or auto binder on the
type's spine, wherever it sits between the explicit arguments
(`(xs : List a) -> (i : Nat) -> [auto ok : i < List.length xs] -> a`
puts `ok` in scope), as today (`docs/syntax.md`: "Implicit and auto
parameters are in scope by name in every equation, wherever they appear
in the signature"). In the type, a type-local name like `i` above stands
for whatever the arm's pattern matched.

The reviewer's example, `def f : (x : Nat) -> [p : P x] -> [auto h : Q x
p] -> R x` with arm `| y => …`: in the arm, `y` is the argument; `p` and
`h` are in scope by name; `x` is not in scope (it names the argument only
inside the type, where `R x` means `R y` for this arm).

**Shadowing.** Innermost first: an arm's pattern variables; then implicit
and auto names from after the colon; then the header's names; then
auto-bound type variables; then the module's names. This is what the
lowering already does: implicit names are bound when the parameters are
introduced, and pattern variables (including the header's explicit
parameters, which are variable patterns) are bound afterwards, at each
case of the match (`crates/elab/src/lib.rs`: `cx.bind` in the parameter
loop; `cx.alias` for pattern variables in `check_tree`).

That same evidence shows one case where the lowering would not be
lexical: a header parameter `(x : Nat)` followed by an implicit `[x :
Bool]` after the colon would resolve `x` in the body to the header's
`x` (a pattern variable, bound later), although the implicit is written
later. So: **the names of the header's binders and of the implicit and
auto binders after the colon must all differ** (`E-DUPLICATE-PARAMETER`,
§4). Arms' pattern variables may reuse any of them (they are innermost
in both the lowering and the reading). An explicit binder after the
colon may reuse a header name, because it's type-local:

```
def f (x : Nat) : (x : Nat) -> P x
  | y => …
```

Here `P x` refers to the second `x` (the nearer binder in the type), so
the result type is `P y` in the arm; in the arm's body, `x` is the header
parameter. Legal, unambiguous, and the converter never writes it (§5.3).

### 2.6 Dependent types and theorems

A result type may mention named parameters, as Lean allows [L1]:

```
def replicate (n : Nat) (x : a) : Vec a n := …
theorem appendLength (xs ys : List a) :
    List.length (List.append xs ys) = List.length xs + List.length ys :=
  match xs with
    | Nil       => rfl
    | Cons z zs => Eq.cong Succ (appendLength zs ys)
```

or, with arms, after the colon:

```
theorem appendLength : (xs ys : List a) ->
    List.length (List.append xs ys) = List.length xs + List.length ys
  | Nil,       ys => rfl
  | Cons z zs, ys => Eq.cong Succ (appendLength zs ys)
```

In the second form `xs` and `ys` in the type only name things for the
statement; each arm binds its own names (as in Idris and Agda).

### 2.7 Effects and `Partial`

```
def report : (Nat, Nat) -> {IO} ()
  | (a, b) =>
    print ("Part 1: " ++ Nat.toText a)
    print ("Part 2: " ++ Nat.toText b)

def collatzSteps : Nat -> {Partial} Nat
  | 1 => 0
  | n => 1 + collatzSteps (next n)

def mk (n : Nat) : Nat -> {Partial} Nat := …   -- total; returns a partial function
```

The rule "a partial function is partial once it has the parameters its
equations name" (docs/syntax.md, `Partial`) becomes easier to see: it's
the named parameters plus the arms' patterns, and with exact arity, arms
always name every argument up to the row. Nothing about rows changes.

### 2.8 Data types, records, abilities: unchanged

`type` declarations already have Lean-style typed parameters
(`type List (a : Type) : Type = | Nil | Cons (head : a) (tail : List a)`),
and records look like Scala's `case class` or Lean's `structure` in
content. An ability's operations are declarations without bodies, like a
Lean structure's fields:

```
ability State (s : Type) where
  get : () -> {State s} s
  put : s -> {State s} ()
```

No change here (question 4, decided). Switching to Lean's
`inductive … where` or Scala's `enum` would be churn without a reading
benefit, and `type` reads plainly to a non-specialist.

### 2.9 `where` and namespaces

**Decided 18 October 2026: no `where`; local `def`s in blocks instead, see
syntax-conveniences.md §3.** The rest of this section, and the `where`
rows and grammar elsewhere in this note, record the design as it stood
before that decision; the namespaces paragraph at the end still holds.

`where` (syntax-conveniences step 5, not built; lane G) is written in the
new style, and attaches to the **whole definition**, as in Lean [L5].
Its exact layout is rule L7 in §2.10. In both body forms:

```
def solve (ls : List Text) : Nat := go 0 ls
  where
    def go (acc : Nat) : List Text -> Nat
      | Nil       => acc
      | Cons l ls => go (acc + score l) ls

    def score (l : Text) : Nat := textLength l * weight

    def weight : Nat := 3

def total (k : Nat) : List Text -> Nat
  | Nil       => 0
  | Cons l ls => scaled l + total k ls
  where
    def scaled (l : Text) : Nat := k * textLength l
```

- A `where` comes after the **entire** body: after the `:=` expression,
  or after the last arm. It can't come between two arms (an arm after a
  `where` is an error, rule L7).
- It sees the **header's named parameters** (`k` above; Lean's `loop`
  uses the header's `a` [L5]), but not the arms' pattern variables, nor
  implicit or auto names from after the colon (§2.5's table).
- A `where` written inside an arm's body, a nested `match` or a lambda is
  an error (`E-WHERE-PLACEMENT`): no nested construct takes a `where`
  today. If one ever does, it gets its own rule; the outer `def` never
  claims it.

This changes one rule in syntax-conveniences §3.1, which made a `where`
belong to one equation and see its pattern variables (the Haskell, Agda,
Idris rule). **A consequence, intended:** a helper written under
§3.1's old rule, `f (Cons x xs) = … where …` using `x`, becomes a helper
that takes `x` (and `xs`) as parameters, or the arm uses `let`. Nothing
in the code base has a `where` yet, so the converter never meets this;
it matters for anyone porting code written against the earlier proposal.
Everything else in §3 (lifting, captures, `f.go` names, plain values as
`let`s, order) is unchanged. We keep the `def`/`theorem` keyword inside
`where`; Lean leaves it out [L5] (question 7, decided).

Namespaces don't change: `def List.sum (xs : List Nat) : Nat := …`
declares `sum` in `List`'s namespace, as `List.sum : …` does today, and
dot notation still finds the first parameter of the type (`xs.sum`).

### 2.10 Layout: where arms, bodies and `where` begin and end

These rules are normative (review finding 3); lane A writes them into
`docs/syntax.md`. They extend today's layout (`crates/syntax/src/parser.rs`,
the module comment and `split_decls`, `block`, the `limit`/`allow`
fields) rather than replacing it.

**Today, for reference (verified):** a top-level declaration starts at
column 0 and every later line indented further belongs to it
(`split_decls`). The lexer drops comments, so comments and blank lines
take no part in layout; tabs are rejected. An expression that starts on a
new line is a block at that line's column. `match` alternatives and
handler clauses that start lines must line up: the first sets the
column, and a line-starting `|` at another column ends that `match`
(`match_expr`, `handle`). An ability's operations use the same "first
line sets the column" mechanism (`limit` and `allow`).

**The rules.** Let *D* be the column of the declaration's first keyword
(`def`, `theorem` or `export`): 0 at top level, the helper's column
inside a `where`.

- **L1. Comments and blank lines** are ignored by every rule below,
  wherever they are and however they're indented (as today; a comment at
  column 0 between two arms does not end the declaration, since the
  lexer never produces a token for it).
- **L2. The header** may continue on further lines, each indented more
  than *D*, as a long signature can today.
- **L3. A `:=` body** is on the header's line after `:=`, or is a block
  starting on the next line, indented more than *D* (as an equation's
  right-hand side today). Its column *B* (used by L7) is the block's
  column; for a body that starts on the header's line, it is the
  leftmost column of the lines the body continues on, or unbounded if it
  has none.
- **L4. Arms.** After a complete type, a `|` that **starts a line**,
  outside any brackets, begins the arms. Its column *A* must be more than
  *D*. Every arm's `|` starts a line at exactly column *A*. The first arm
  may not share the header's line ("arms start on their own lines"); a
  short case analysis that fits on one line is a `:=` body with a
  `match`.
- **L5. An arm's body** may continue on later lines indented more than
  *A*; a body that starts on its own line is a block at that line's
  column, as today. **A line starting at column *A* or less ends the
  arm.** Implementation: while parsing an arm, the parser's `limit` is
  *A*, as `block` and `ability` already do. Consequences:
  - a `match` or `handle` inside an arm must indent its own `|`s more
    than *A*; a line-starting `|` at column *A* is always the
    definition's next arm, never the nested `match`'s (the nested
    `match` stops at the `limit`, as it already stops at a `|` at
    another column);
  - a line-starting `|` between *D* and *A* (exclusive) is an error:
    "this `|` doesn't line up with the arms at column *A*".
- **L6. The end.** The arms (or the body) end at the first line that
  starts at column *D* or less: the next declaration, or, inside a
  `where`, the next helper or the end of the `where`. A line-starting
  token at column *A* that is neither `|` nor `where`, or one between
  *D* and *A*, is an error.
- **L7. `where`.** A `where` starts a line, at a column *W* with
  *D* < *W* ≤ *B*, where *B* is *A* in the arm form and as in L3 in the
  `:=` form. So it lines up with the arms (the usual style) or sits
  between the declaration and them. A block (an arm's or a `:=` body's)
  stops at a line-starting `where` at or left of its column, as it stops
  at a line-starting `|` today. The helpers start on the lines after
  `where`, all at one column *H* > *W*, each a `def` or `theorem` to which
  these rules apply with *D* = *H*. The `where` ends at the first line
  starting left of *H*; if that line is still right of *D* (an arm, say)
  it's an error: "arms can't follow `where`; it belongs after the last
  arm". A line-starting `where` right of *B* (inside an arm or a nested
  block) is `E-WHERE-PLACEMENT`.
- **L8. Inside brackets** (`( )`, `[ ]`, `{ }`), layout doesn't end
  anything (today's behaviour for rows and records).

**Golden parser tests** (lane A), each compared with the AST of the old
form where one exists:

1. a header spread over several lines (the reviewer's `def f :` / `A ->` /
   `B` / `| p => …`), and one whose type ends in an open row
   `{State s | e} B` followed by arms;
2. an arm whose body is a `match` with its `|`s indented further, followed
   by another arm of the definition;
3. the same with `handle`, and with a `match` inside a handler clause
   inside an arm (three levels of `|`);
4. a nested `match` whose `|`s are at the arms' column: they're read as
   the definition's arms (and the test shows the resulting error or AST);
5. a `|` between *D* and *A*; a first arm on the header's line; a token
   at column *A* that isn't `|`;
6. comments (at column 0, at *A*, at the end of a line) and blank lines
   between arms, and between an arm's lines;
7. an arm body that's a multi-line block (`print` lines, as in §2.7);
8. `where` after a `:=` body (inline and block), after arms, between arms
   (error), inside an arm (error), and at column 0 (it's a new,
   malformed declaration).

Tests 1 to 7 are done, in `crates/syntax/tests/declarations.rs`. Test 8
changed: `where` is a reserved word. After a body or the last arm it is
`E-PARSE` "`where` after a definition isn't supported yet"; anywhere else
it is a plain parse error. `E-WHERE-PLACEMENT` and the real `where` stay
with lane G.

### 2.11 Lambdas, `let`, `match`, handlers: `=>` for "then do this"

> **Since SW-90:** lambdas no longer start with a backslash (`x => e`, `x y => e`);
> the `\x => …` forms below are historical. See [lambda-syntax.md](lambda-syntax.md).

One meaning per arrow (question 2, decided): **`->` is only the function
type; `=>` separates a pattern or parameter from what follows** (in arms,
`match`, handlers and lambdas). This is Lean's split [L10]. Scala uses
`=>` for both [S6], which is the confusion we'd avoid.

```
\x => x + 1
\(a, b) => a + b
match xs with
  | Nil => 0
  | Cons x _ => x
handle prog () with
  | return x  => [x]
  | choose u, k => List.append (k True) (k False)
let (q, r) := (n / 7, n % 7)
```

Why now: in a header like `def f : Nat -> Nat` followed by `| 0 -> 1`,
two arrows with different meanings sit a line apart. And the planned
annotated lambda parameter (`TODO.md`: `\(x : T) -> …` is refused today)
would look exactly like a dependent function type `(x : T) -> B`; with
`\(x : T) => …` it doesn't.

**Handler clauses.** Today's operation clause is `| op x => k -> body`;
it becomes `| op x, k => body` (question 5, decided). The parser reads
the operation's argument with its pattern parser, then expects `,`, then
the continuation's name, then `=>`. The argument is an atomic pattern, as
today (`handle` calls `pattern`, not `alt_pattern`), so a constructor
with arguments needs brackets; any comma inside brackets or braces
belongs to the pattern, never to the clause. Splitting at the first
comma token would be wrong. Parser tests (lane A):

| Clause | Argument pattern | Continuation |
|---|---|---|
| `\| op (a, b), k => …` | the tuple `(a, b)` | `k` |
| `\| op (), k => …` | `()` | `k` |
| `\| op { x, .. }, k => …` | the record pattern | `k` |
| `\| op ((a, b), c), k => …` | nested tuple | `k` |
| `\| op [a, b], k => …` | list pattern | `k` |
| `\| op (Just x), k => …` | constructor pattern | `k` |
| `\| op a, b, k => …` | error: "an operation takes one argument; bracket a tuple: `(a, b)`" | |
| `\| op x => …` | error: "name the continuation: `\| op x, k => …`" | |

The `return` clause stays a separate case in the AST (`Clause::Return`,
`crates/syntax/src/ast.rs`; verified), recognised by the `return`
keyword token, not by a name's spelling: `| return x => body`.

`alt_pattern` (the pattern of an arm or `match` alternative) today stops a
constructor's arguments at `,` or `->`; it must stop at `=>` too.

**Cost**: every lambda, `match`, `handle` and `let` in the code base
changes (about 350 lines with a lambda in `.sw` files alone). All of it is
done by the converter (§5), and none of it changes a core term.

## 3. Does anything of the old style stay?

No form of the old declaration style needs to stay. The cases where the
separate signature helps (different names per clause, matching on every
argument) are covered by putting the arguments after the colon, which is
the old signature's type copied as it is. The pieces that look like the
old style and stay are not declarations of definitions:

- **ability operations** (`get : () -> {State s} s`): there's no body,
  so there's nothing to put inline.
- **types written with arrows** after the colon, which is the same
  notation as before.

An old-style declaration becomes an error with a fix-it (§4).

## 4. Errors, printing and the playground

New or changed messages (wording is a draft):

| Code | When | Message |
|---|---|---|
| `E-OLD-DECLARATION` | after the switch (lane E): `f : T` or `f x = e` at column 0 | "declarations start with `def`: `def f : T`" (with the arms the equations would become, if they're next to it) |
| `E-DEF-EQUALS` | `=` where `:=` is expected after a header, `test` or `let` | "a definition's body follows `:=`; `=` is equality" |
| `E-ARITY` (reworded) | arms with different numbers of patterns | "this arm has 2 patterns, but the first one has 3" |
| `E-ARITY` (reworded, and now for fewer too) | an arm without a pattern for each argument | "`f` takes 2 arguments after the colon, but this arm has 1 pattern"; note "to return a function, add the argument as a pattern, or write a lambda" |
| `E-ARITY` | arms but no explicit argument after the colon | "arms need an argument after the colon to match; use `:=`" |
| `E-NONEXHAUSTIVE` (reworded) | | "missing case: no arm matches `Cons _ Nil`"; note "add an arm…" |
| `E-ARM-PARAMETER` (new) | an arm with more patterns than arguments after the colon when the header has named explicit parameters, or `:=` and arms both given | "named parameters can't be matched in arms: move `w` after the colon, or use `match w with`" |
| `E-DUPLICATE-PARAMETER` (new) | two header binders, or a header binder and an implicit/auto binder after the colon, with one name (§2.5) | "`x` is already a parameter of `f`" |
| `E-WHERE-PLACEMENT` (new, lane G) | `where` inside an arm or nested expression, or before an arm (L7) | "a `where` belongs to the whole definition: put it after the last arm, lined up with the arms" |
| `E-PARSE` (new wordings) | layout errors L4–L7, malformed binders, handler clauses (§2.11) | as quoted in those sections |
| `E-MISSING-SIGNATURE`, `E-MISSING-DEFINITION` | | can't happen in the new syntax (a header always has a type, and `def f : T` with neither `:=` nor arms is a parse error); removed in the switch commit |

Today's messages that say "equation" (`crates/elab/src/lib.rs`:
`E-ARITY`, `E-NONEXHAUSTIVE`, "this equation needs `= …`";
`crates/elab/src/matching.rs`; `lift.rs`'s note "write the helper as a
top-level definition with its own signature") are reworded to say "arm"
or "definition". `E-MUTUAL-SIGNATURE` keeps its name; its message says
"`f`'s type" already. Error spans keep pointing at the right place, since
the synthesised patterns carry the spans of the header's binders.

**Printing.** `crates/core/src/pretty.rs` prints core types as
`(x : A) -> B`, which stays correct (types don't change). Anything that
prints a definition's type (the REPL, error messages) prints it as a type,
not as a header; no change is needed (**unverified** beyond
`pretty.rs`: lane A checks for any printer of declarations).

**Playground colouring** (`web/index.html`, `KEYWORDS` near line 994): add
`def` (and `import`, already missing). The rule "a name at the start of a
line, or after `theorem`, is a defined name" (near line 1030) becomes "a
name after `def` or `theorem`". `:=` and `=>` need no colour of their own.
The six built-in examples in `web/index.html` are converted with the rest.

## 5. Migration

### 5.1 What there is

| Where | Files | Lines | Signatures |
|---|---|---|---|
| prelude (`crates/elab/src/prelude.sw`) | 1 | 1852 | 209 |
| `examples/accept` | 51 | 4339 | 510 |
| `examples/extract` | 22 | 1511 | 214 |
| `examples/reject` | 138 | 1036 | 161 |
| `examples/soundness` | 46 | 527 | 70 |
| `aoc/` | 3 | 242 | 31 |
| playground examples (`web/index.html`) | 6 blocks | ~190 | 21 |
| Rust tests with inline sources (approx.) | ~26 files | | ~286 |
| Markdown code blocks (approx.) | ~140 blocks | | ~172 |

(Counts by `grep` for lines like `name :` at column 0, at `69112b7`;
approximate for Rust and Markdown.)

### 5.2 A one-off converter, using spans, not a printer

A converter in Rust does almost all of it. It **rewrites text at token
spans**, not by printing the AST, because:

- the lexer throws away comments, and there is no surface printer
  (`crates/syntax` has none); printing from the AST would lose every
  comment and every hand-aligned column;
- span edits leave bodies exactly as written, and only touch headers,
  equation left-hand sides and a few tokens.

It runs before the old syntax is removed, reading old files with
`Syntax::Old` (lane A), and is deleted after the migration. Its guiding policy,
from the review: **the goal is a conversion that means the same, not the
prettiest headers on day one. Whenever a nicer form needs any judgement
about names, it writes the all-arms form**, which is always a direct copy
of the old signature and equations. A later, scope-aware refactoring tool
can lift columns into named parameters.

### 5.3 The converter's rules

Per file, from the parsed module, for each signature with its equations
(grouped as `collect` in `crates/elab/src/module.rs` does):

1. **Arity.** Ask the elaborator (from the old file, already loaded for
   the checks in §5.4) how many explicit arguments the definition's type
   has, counted as the arity check counts them (§2.4). Call it *n*; the
   equations have *k* patterns each.
2. **Named parameters.** Going from the left, column *i* (i < *k*)
   becomes a named header parameter `(v : A)` only if **all** of these
   hold, and the run stops at the first column where one fails:
   - every equation has the **same** plain variable `v` in that column
     (no renaming is ever done: equations that use different names, or a
     `_` in some of them, keep the column in the arms);
   - the signature's arrow for that column is unnamed, or named `v`, or
     named something else that isn't used anywhere in the rest of the
     type (then the header just uses `v`);
   - `v` doesn't occur free in the later binders' types or the result
     type (so the new binder can't capture a type variable or a global:
     `f : a -> a` / `f a = a` keeps the arm form);
   - `v` isn't the name of an implicit or auto binder anywhere in the
     signature (§2.5's distinct-names rule).

   A column of type `()` whose pattern is `_` in every equation, or the
   same variable not used in any body, becomes `()` instead; a variable
   that's used becomes `(u : ())`.
3. **Form.** If there is one equation and every one of its *k* columns
   became a named parameter (including *k* = 0, a value), the definition
   gets a `:=` body: the remaining *n − k* arguments stay after the colon
   as they were, with no arity rule. Otherwise the remaining columns
   become arms after the colon; with more than one equation, the run of
   rule 2 stops before the last column, so at least one is left to
   match.
4. **Exact arity for arms.** If the arm form has fewer patterns than *n*
   minus the named parameters, each arm is completed, arm by arm:
   - if the arm's body is a lambda whose first parameters are written as
     plain names (`y z => …`, not a pattern lambda), its parameters are
     moved into the arm's patterns, as many as are missing, by deleting
     them from the lambda (and the lambda, if none are left) and
     appending them after the arm's patterns. This is safe without any
     renaming: those names were in scope in exactly the lambda's body,
     which is now the arm's body. Example: `| Zero => y => y` becomes
     `| Zero, y => y`;
   - otherwise (and for the rest still missing) fresh variables are
     appended and the body is applied to them: `| Succ x => g x` becomes
     `| Succ x, a1 => (g x) a1` (brackets omitted when not needed). A
     fresh name is one that occurs nowhere in the declaration's text, so
     it can't capture or be captured;
   - an absurd arm gets `_`s.

   These are the declarations whose core terms change on purpose
   (§5.4). The converter prints the list.
5. **Header text.** Split the signature's type text at its top-level
   arrows: the named columns' arrows and the implicit or auto binders
   before them (as written) become binders; the rest stays after the
   colon, verbatim. If the split can't be done with confidence (an arrow
   inside a `match` or a bracketed expression that isn't a binder, a
   comment inside the part that moves), it uses the all-arms form.
6. **Tokens** at spans the parser identifies: `=` → `:=` after headers,
   `let` and `test`; `->` → `=>` in lambdas, `match` and `handle` arms;
   `| op x => k ->` → `| op x, k =>`; `| return x ->` → `| return x =>`;
   the `export` line joined to its `def`.
7. **Everything else is kept**: comments between equations move to just
   above the arm they preceded.

**Renaming is never done by text substitution.** The rules above avoid
renaming altogether: a column becomes a named parameter only when every
equation already uses the name, and the arm form otherwise binds
whatever names the equations bound. If a later tool wants to rename, it
must rename only the occurrences that resolve to that specific binder
(the parsed AST has the spans), never every token spelled the same; the
reviewer's example is two equations `f x = let y := …` and `f y = let x
:= …`, where a textual swap would capture the inner `x`.

### 5.4 Checking it: several layers, hashes the strongest

Content hashes cover each definition's whole elaborated declaration
(type, body, and the hashes of everything it refers to) and leave out
names, binder names and source locations (DESIGN.md §11,
`crates/core/src/hash.rs`). So **identical hashes are the strongest
evidence available that a converted file means the same as the
original**, but not proof: invalid programs have no hashes, a dropped
declaration has no hash to differ, tests and exports may sit outside
them, both sides share one elaborator and one hasher, and data types'
names are part of their identity. So the gate (lane B builds the
checker; lanes C and D run it) is all of these, over **every** `.sw` file
and playground example (including `aoc/`, which `hash_stability` doesn't
cover), comparing the old text and the new text loaded in fresh
sessions:

1. **Same declarations, in the same order, of the same kinds**: names,
   and for each whether it's a definition or theorem, data type,
   ability, test; and its `export` flag. A missing or extra declaration
   fails.
2. **Same hashes**, for every declaration not on the expected-change
   list (below) and not depending on one.
3. **Same dependencies**: for each definition, the set of declarations
   it refers to, by name. (This and layer 4 also cover the
   expected-change list, whose hashes differ.)
4. **Same local structure**: each definition's elaborated type and body
   printed with references to other declarations *by name* (not hash),
   so a change in one declaration doesn't show up in all its
   dependents. Equal for everything not on the list; for those on it,
   the **types** must be equal and the bodies' difference is printed for
   review. (A term printer that prints references by name: `pretty.rs`
   may do; **unverified**, lane B checks.)
5. **Same exports and tests**: the list of exported names, and the list
   of tests by name and order.
6. **Same test results**: `stitchwort test` output, every file.
7. **Same errors** for `examples/reject` and `examples/soundness`: the
   same primary error code from the same declaration, not merely "both
   fail". (Positions move, so message snapshots are reviewed, not just
   accepted.) Expected differences: reject examples whose point is a
   form that no longer exists (an arm with too few patterns, a missing
   signature) are listed and rewritten or retired by hand in lane E.
8. **Parser-level equivalence** (lane A, in unit tests): for each new
   form, the lowered AST equals the old form's AST, spans and the new
   arm markers aside. This is the direct check, before elaboration,
   that the lowering is what §2.3 says.

`crates/driver/tests/hash_stability.rs` pins the hash of every
declaration in the prelude, `examples/accept` and `examples/extract`;
the test file itself doesn't change. After conversion, its snapshot
changes must be exactly the expected-change list plus their dependents
(the checker prints that set; a reviewer compares it with `cargo insta`'s
diff), then accepted, and `git add`ed.

**The expected-change list** (hashes differ, on purpose):

- **E1.** Definitions completed for exact arity (§5.3 rule 4), and every
  declaration that depends on them. The checker computes the dependent
  set. How many there are isn't known yet (it needs the elaborator's
  argument counts); lane B reports the count before lane C.
- That is the only one. The header `()` lowers to `_` (§2.3), and no
  existing equation uses a `()` pattern with a body, so it moves no hash.
  Binder names aren't hashed, so taking names from the equations moves
  none.

Anything else that moves stops the lane, which reports it.

### 5.5 What's done by hand

- Rust tests with inline sources (~26 files): the converter can be run on
  string literals that the test passes to the parser, but it's simpler for
  a Sonnet lane to run it on each extracted snippet and paste back.
- Markdown: the converter on each fenced block that parses; prose that
  quotes syntax (`` `f x = …` ``) by hand. Historical proposals
  (`docs/proposals/*.md` for features already built) get a one-line note
  at the top saying they use the old syntax, rather than being rewritten;
  `docs/syntax.md`, `DESIGN.md` §4, `docs/core.md`'s examples,
  `docs/aoc-2025.md` and `docs/testing.md` are rewritten.
- Parser unit tests that test the old forms are replaced by tests of the
  new ones.

### 5.5a The converter as built (lane B)

`crates/convert` (library and binary `stitchwort-convert`; **deleted** after
the docs were converted, see git history, commit before the one that removes it). It reads a file with today's parser and lexer
(`stitchwort_syntax::lex` is now public for it) and edits the text at
token spans, following §5.3; every edit is located by the parsed tree and
checked against the token it replaces, and anything unexpected fails the
whole file with a reason.

```
stitchwort-convert                  # dry run: prelude, examples/, aoc/, web/index.html
stitchwort-convert PATH…            # dry run over files / directories
stitchwort-convert --write [PATH…]  # convert in place (the switch commit)
stitchwort-convert --print FILE     # one file, converted, to stdout
stitchwort-convert --stdin          # a snippet (Rust test source, Markdown block): stdin → stdout
```

`--stdin` reads the snippet as a module, or, failing that, as an
expression; on failure it prints nothing and exits 1 with the reason.

Choices the note left open, as implemented:

- **Arity** (§5.3 rule 1) comes from the elaborator when the file checks:
  the definition's explicit `Pi`s after `force`, up to the first non-`Pi`.
  For files that don't check (reject and soundness examples) it's the
  arrows written in the signature.
- **Arm patterns** are the equations' patterns as written, except that a
  constructor pattern with arguments loses its outer brackets
  (`| Cons x xs, ys =>`). So arms must read patterns as `match`
  alternatives do (`alt_pattern`). Columns the equations lined up are
  lined up again; `,` follows each pattern.
- **Layout**: arms start at column 2 (`  | `). If any later line of an
  equation starts at column 2 or less, every later line of the
  definition's equations moves right by 2 (rule L5). A type continued on
  lines at column 2 or less is indented 2 more in the arm form. A header
  binder whose type started a line in the signature starts a line in the
  header.
- **Handler clauses** keep their `=>` where the `->` was, so lined-up
  clauses stay lined up: `| print t, k    => …`.
- **Fresh names** for exact arity are `a1`, `a2`, …, skipping any lower-case
  name in the file. The body is bracketed unless it's a name, an
  application or already bracketed; a body starting on its own line is
  written `=> (`, the block, `) a1` (no file in the repository needs it).
- **Comments** between a signature and its single equation move above the
  `def` in the `:=` form. A comment inside a moved part of a signature
  gives the all-arms form; one inside an equation's left-hand side fails
  the file.

Dry run after merging lane A (all inputs; web/index.html counts its 6 examples):
276 of 280 convert; 1689 definitions (1002 `:=`, 687 with arms, 842 of
all with named header parameters) and 519 tests.

**For lane A and the switch lane:**

1. **Signatures without equations.** The prelude's six primitives
   (`Effect.Delay`, `now`, `lift`, `bindD`, `mapSig`, `pfix`, near the end
   of `prelude.sw`) have no equations; the converter writes them as a
   header with no body, `def Effect.Delay : (op : Type) -> … -> Type`. The
   grammar (§2.1) has no such form: the new parser must accept a
   bodiless `def` (in the prelude at least), or the switch lane picks
   another form.
2. **Expected hash changes (E1)**: 7 arms in 5 definitions, before
   dependents: `Effect.sigRes` (applied to `a1`), `Effect.noReply`
   (absurd, `_` added) in the prelude; `sizeNotZero`
   (`examples/accept/mutual-data.sw`, applied to `a1`); `evenShift` and
   `oddShift` (`examples/extract/mutual.sw`, one arm each moving a
   lambda's `x`, one applied to `a1`).
3. **Files the converter can't read** (deliberately malformed; convert by
   hand): `examples/reject/char-surrogate.sw`,
   `else-left-of-its-if.sw`, `tuple-annotation.sw`,
   `tuple-one-element.sw`.
4. **AST equivalence** is checked on every conversion
   (`stitchwort_convert::check_ast_equivalence`, using lane A's
   `stitchwort_syntax::equivalence::shape` per declaration): the output,
   read with `Syntax::New`, must lower to the input's tree. Allowed
   differences: the equations of the definitions in item 2; a header
   `()` where the equations bound an unused variable (`_` vs the
   variable); headers without a body (item 1, left out of the check);
   and an explicit binder whose name the rest of the type doesn't use,
   compared as a plain arrow (`(n : Nat) -> B` vs `Nat -> B`; binder
   names aren't hashed). A file that fails it isn't converted. All 276
   inputs above pass, so the dry run is also the repository-wide
   equivalence test.
5. **Parser fix** (lane A's code, found by item 4): with `export`, D
   (§2.10) is `export`'s column, not `def`'s; arms under `export def` at
   column 2 were refused.
6. `crates/driver/src/run.rs`'s two source strings (`MAIN_CALL` and the
   one in `simulate`) are expressions; `--stdin` converts them.

### 5.6 The transition: no transition window, no hybrids

The user decided (18 Oct) that there is no period in which a file may
mix the two syntaxes, and no mixed declarations. Both parsers coexist
only in the code. The parser takes a syntax option, `Syntax::Old` (the
default until the switch) or `Syntax::New`, and reads a whole file in
that one syntax. So there are no states that the final language lacks,
and nothing like `E-MIXED-DECLARATION` is needed.

The switch is one commit, later: the converter (lane B1) rewrites every
file, the parser's default flips to the new syntax (`Syntax::default` in
`crates/syntax/src/parser.rs`, one line), and the old parser is deleted.
Until then, `--syntax new` (or `STITCHWORT_SYNTAX=new`) reads a file in the
new syntax, and the converter, checker and conversion lanes work against
that option.

## 6. Implementation plan

The parser changes in one crate (`crates/syntax`, 3814 lines). The
elaborator changes in messages and the exact-arity check; also in
`crates/elab/src/lib.rs` where it builds `Decl::Equation` values itself
for abilities, which only need the arm marker. Each lane stays well under
500k tokens.

| Lane | Model | What | Size |
|---|---|---|---|
| A. Parser | Opus | **Built** (see [Lane A: what was built](#lane-a-what-was-built)): the grammar of §2.1 with early commitment; binders and `()` → `_`; `:=`; arms with layout rules L1–L6 and L8; `=>` in lambdas, `match`, `handle`; the arm marker; exact arity for arms; `E-DUPLICATE-PARAMETER`; `E-DEF-EQUALS`; golden layout tests 1–7; parser-level old/new AST equality. A syntax option selects the syntax per file. Layout rules into `docs/syntax.md` as a draft section | done |
| B1. Converter | Opus | the span-based converter as a temporary binary, with §5.3's rules (no renaming; fall back to all arms); prints the exact-arity list; run on 5 sample files with diffs shown. Reuses the AST-equivalence harness | ~250k |
| B2. Checker | Sonnet, Opus review | the multi-layer check of §5.4 (layers 1–7) as a temporary binary over all files and playground examples, reading the new text with `Syntax::New`; computes the dependents of the expected-change list | ~150k |
| C. Convert `.sw` | Sonnet | prelude, `examples/*`, `aoc/`, playground examples, converted and checked against the option. Gate: the checker clean; `hash_stability` changes exactly the expected set; `nix flake check` passes | ~150k |
| D. Convert Rust and docs | Sonnet (two lanes if needed) | inline test sources (including the driver's own strings, see lane A notes); `docs/syntax.md`, DESIGN.md §4, core.md, testing.md, aoc-2025.md; historical-note banners | ~200k each |
| E. Reject examples and messages | Opus | `E-OLD-DECLARATION`, `E-ARM-PARAMETER`; reword "equation" messages; reject examples for each new error; retire reject examples for forms that no longer exist (§5.4 layer 7). The old parser's deletion is part of the switch commit, not this lane | ~100k |
| F. Playground | Sonnet | keywords, defined-name rule, browser test | ~80k |
| G. `where` (step 5) | Opus | as syntax-conveniences §3, with §2.9's changes; layout rule L7 and golden test 8; `E-WHERE-PLACEMENT`; its own test plan there | separate |

**The switch is one commit:** the converter run on everything, the
parser's default flipped to `Syntax::New`, and the old parser deleted
(this folds in the deletion that lane E had in draft 1). Lanes B1 to D
prepare it; they don't change the default.

Order: A, then B1 and B2 in parallel, then C and D in parallel, then the
switch commit, then E and F, then G. C is the point where we learn whether the translation is
exact; if anything outside the expected-change list moves, the lane
stops and reports it.

### Lane A: what was built

- **The option.** `Syntax::{Old, New}`, with `parse_module_in` and
  `parse_expression_in`, in `crates/syntax`. `Syntax::default()` is `Old`.
- **The driver.** `Session.syntax`. The prelude and the driver's own
  expressions (such as `MAIN_CALL` and `simulate`'s source) are parsed in
  `Syntax::default()`, so the switch commit must convert those strings too.
- **The CLI.** A global `--syntax old|new` flag and the `STITCHWORT_SYNTAX`
  environment variable.
- **The equivalence harness.** `stitchwort_syntax::equivalence` has
  `shape`, `parse_shape`, `compare` and `assert_equivalent`. Spans and the
  arm marker are ignored. The converter lane reuses it.
- **Exact arity** is checked in the elaborator (`body_term` in
  `crates/elab/src/lib.rs`), for arms only. It counts explicit arrows after
  unfolding, and stops at an ability row.
- **`E-DUPLICATE-PARAMETER`** is checked in the parser, over the header
  binders and the implicit and auto binders on the result type's spine. Only
  the spine as written is checked, not through definitions.
- **`E-DEF-EQUALS`** is built in the parser for `test`, `let`, and a header
  whose type swallowed an `=` body.
- **`def` is now a keyword** in both syntaxes.
- **Blocks** now end at a line-starting `|`, `where` or `:=`. This is
  harmless in the old syntax, where none of them can start a statement.
- **Stack use.** The new forms are in `#[inline(never)]` functions in
  `crates/syntax/src/parser/declarations.rs`, to keep the expression
  parser's stack frames small. The `check-nested-parens` benchmark is
  unchanged.
- **Tests.** `crates/syntax/tests/declarations.rs` (60) and
  `crates/driver/tests/declaration_syntax.rs` (16).

**Done afterwards (lane E, with the tidy-up):** `E-ARM-PARAMETER` for an arm
with more patterns than arguments after the colon when the header names
parameters (reject example `arm-matches-parameter.sw`; the `:=`-plus-arms
parse error keeps its `E-PARSE` code and its note); `E-MISSING-SIGNATURE`
removed; "equation" messages reworded to "arm"; playground colouring.

**Left for later lanes (as of lane A):**

- `E-ARM-PARAMETER`. Today `:=` followed by arms is a parse error ("a
  definition has a `:=` body or arms, not both"), and more patterns than
  arguments still gives the old `E-ARITY` wording.
- `E-OLD-DECLARATION`. Today an old-style declaration is a plain `E-PARSE`,
  "definitions start with `def`".
- Rewording the remaining "equation" messages.
- `W-MODULE-NAME`'s note for headers (§2.3).
- Playground colouring (lane F).
- `where` (lane G).

### The switch: what was done

- **Converted** with `stitchwort-convert --write`: the prelude, `examples/`,
  `aoc/` and the playground's examples (276 inputs); by hand: the four
  malformed reject examples (same errors) and the snippets in Rust sources
  and the web tests. In `examples/extract/names.sw`, five exports keep the
  all-arms form by hand, so their signatures keep the binder names (`this`,
  `undefined`, …) whose JS spelling the example tests: rule 2 had taken the
  header names from the equations, which changes the exported parameter
  names in the generated `.d.ts`.
- **The parser** reads only the new syntax; `Syntax`, `--syntax`,
  `STITCHWORT_SYNTAX`, `parse_*_in` and `Session.syntax` are gone. A
  declaration starting with a name is `E-OLD-DECLARATION`; `->` where `=>`
  belongs gets a note. A header with neither `:=` nor arms parses as a
  signature alone: the elaborator admits it only as a prelude primitive and
  otherwise reports `E-MISSING-DEFINITION` ("`f` has no body").
- **The old parser** lives on in `crates/convert/src/old_parser*` (a copy,
  used by the converter only), with the old-vs-new equivalence tests
  (`crates/convert/tests/declarations.rs`, `declaration_hashes.rs`).
- **The printer** prints lambdas as `x => body`.
- **Hashes.** Besides E1 (the five definitions of §5.5a and their
  dependents), one more kind of change: a partial definition that calls
  itself gets a generated `….Request` data type whose constructor's field
  names are the parameter names in its type, and data types' field names
  are hashed. Where the converter named a header parameter (`def fib (n :
  Nat) : {Partial} Nat`, was `fib : Nat -> {Partial} Nat`), the field gets
  that name, so `Request` and its dependents change: `IO.readLinesFrom` in
  the prelude, `addLines` (adder.sw), and `fib`, `firstFrom`, `spin`,
  `stepper` (partial.sw). Every other hash is unchanged.

## 7. Questions for the user

**Decided (18 October 2026):** the user agreed with every recommendation
below (1 to 9) before the review, and after it decided three more
(10 to 12). **Decided (18 Oct), after lane A:** three more (13 to 15).

1. **`:=` before a body, instead of `=`** (§2.2)? **Yes.**
2. **`=>` for arms, lambdas and handlers, `->` only for function types**
   (§2.11)? **Yes**, in the same migration.
3. **`let x := e`, and keep `=` in `type` declarations and record fields**
   (§2.2)? **Yes** to both.
4. **Keep `type` and `ability` declarations as they are** (§2.8)? **Yes.**
5. **Handler clause `| op x, k => body`** (§2.11)? **Yes.**
6. **Auto-bound implicits: keep as today** (§2.3)? **Keep for now**;
   Lean's stricter mode is a separate change later.
7. **`def` and `theorem` keywords inside `where`** (§2.9)? **Keep them.**
8. **A `where` belongs to the whole definition and sees the header's
   parameters, not arms' pattern variables** (§2.9)? **Yes.**
9. **Migration by a span-based converter, checked by hashes** (§5, §6)?
   **Yes**, with the multi-layer gate of §5.4. (Item 13 replaces "both
   syntaxes accepted during the migration".)
10. **Stable hashes** are not a design constraint (no users yet); hash
    comparison stays the migration's test, with expected changes listed.
11. **Exact arity**: arms match every explicit argument after the colon
    (§2.4).
12. **Header `()`**: the implementer's choice; this draft picks `_`
    (§2.3).
13. **No transition period.** No file mixes both syntaxes and there are
    no mixed declarations, so `E-MIXED-DECLARATION` and the both-syntaxes
    decision table are dropped. The parser has a syntax option
    (`Syntax::Old`, the default, or `Syntax::New`) and reads a file wholly
    in one. The switch is one later commit: the converter rewrites every
    file, `Syntax::default` flips, the old parser is deleted (§5.6).
14. **`E-DUPLICATE-PARAMETER`** as proposed in §2.5. Built.
15. **Hashes are not a design constraint** (no users). Hash comparison is
    only a migration test oracle (§5.4).

No questions remain open in this draft.

## Review response

The external review (verdict: proceed, no kernel or type-theoretic
blocker) and where each finding is answered:

| # | Finding | Kind | Response | Where |
|---|---|---|---|---|
| 1 | Auto-binding over the whole reconstructed signature | must-fix | Adopted as an invariant; verified that today's auto-binding already runs once over the complete type; six test cases | §2.3 |
| 2 | Scope of binders after the colon; shadowing | must-fix | Table by binder kind; shadowing order matching the lowering; `E-DUPLICATE-PARAMETER` for the one non-lexical case found in the code | §2.5 |
| 3 | Layout of arms and `where` as grammar | must-fix | Rules L1–L8 and eight golden test groups | §2.10 |
| 4 | One desugaring for header `()` | should-fix | `()` lowers to `_` (user: implementer's choice); the difference from `\| () =>` is stated; no hash moves | §2.3 |
| 5 | Fewer arm patterns than arguments | should-fix | Exact arity (user's decision); converter completes arms by moving lambda parameters or adding fresh ones | §2.4, §5.3 rule 4 |
| 6 | `where` attachment in both body forms | should-fix | Both forms shown; after the whole body only; nested `where` is an error; the helper-parameter consequence documented | §2.9, §2.10 L7 |
| 7 | Hashes are not the whole gate | must-fix | Eight-layer gate; hashes "the strongest evidence", not proof; expected changes listed and compared structurally | §5.4 |
| 8 | No renaming by text substitution | must-fix | The converter never renames; all-arms fallback whenever names disagree or could capture | §5.2, §5.3 |
| 9 | No hybrid old/new declarations | should-fix | Guaranteed because a file is read in one syntax only (the parser's option); `E-MIXED-DECLARATION` dropped (item 13) | §5.6 |
| 10 | `def`/`theorem`/`export def` commit early; written grammar | should-fix | Grammar written; the transition decision table was later dropped (item 13) | §2.1 |
| 11 | The before/after-colon split is sound | note | Kept; untyped binders still not added | §2.3, §2.4 |
| 12 | Phrase `:=` vs `=` less categorically | note | Rule reworded | §2.2 |
| 13 | Handler clause tests; return arm distinct in the AST | note | Test table; `Clause::Return` already separate (verified) | §2.11 |
| 14 | The migration plan | note | Converter made more conservative, as suggested | §5.2 |

## Sources

- [L1] Lean Language Reference, "Headers and Signatures":
  <https://lean-lang.org/doc/reference/latest/Definitions/Headers-and-Signatures>
- [L2] Lean Language Reference, "Definitions":
  <https://lean-lang.org/doc/reference/latest/Definitions/Definitions/>
- [L3] *Functional Programming in Lean*, "Additional Conveniences" (named
  arguments and patterns in one definition; `def Nat.double`; `namespace`):
  <https://lean-lang.org/functional_programming_in_lean/Getting-to-Know-Lean/Additional-Conveniences/>
- [L4] Lean Language Reference, "Theorems":
  <https://lean-lang.org/doc/reference/latest/Definitions/Theorems/>
- [L5] *Theorem Proving in Lean 4*, "Induction and Recursion" (`where`
  with `replicate`/`loop`; `termination_by`):
  <https://lean-lang.org/theorem_proving_in_lean4/induction_and_recursion.html>
- [L6] Lean release notes v4.6.0 (placement of `termination_by` before
  `where`): <https://lean-lang.org/doc/reference/latest/releases/v4.6.0/>
- [L7] Mathlib `lakefile.lean` (`autoImplicit, false`):
  <https://raw.githubusercontent.com/leanprover-community/mathlib4/master/lakefile.lean>
- [L8] Lean release notes v4.18.0 (`autoImplicit true` is "the default in
  plain Lean projects, but not in mathlib"):
  <https://lean-lang.org/doc/reference/latest/releases/v4.18.0/>
- [L9] *Functional Programming in Lean*, "Datatypes and Patterns" and
  "Structures":
  <https://lean-lang.org/functional_programming_in_lean/Getting-to-Know-Lean/Datatypes-and-Patterns/>,
  <https://lean-lang.org/functional_programming_in_lean/Getting-to-Know-Lean/Structures/>
- [L10] Lean Language Reference, "Functions" (types) and "Terms/Functions"
  (`fun x => …`):
  <https://lean-lang.org/doc/reference/latest/The-Type-System/Functions/>,
  <https://lean-lang.org/doc/reference/latest/Terms/Functions>
- [S1] Scala 3 reference, "Using Clauses":
  <https://docs.scala-lang.org/scala3/reference/contextual/using-clauses.html>
- [S2] Scala 3 book, "Algebraic Data Types":
  <https://docs.scala-lang.org/scala3/book/types-adts-gadts.html>
- [S3] Scala 3 book, "Domain Modeling Tools" (`case class`):
  <https://docs.scala-lang.org/scala3/book/domain-modeling-tools.html>
- [S4] Scala 3 book, "Extension Methods":
  <https://docs.scala-lang.org/scala3/book/ca-extension-methods.html>
- [S5] Scala 3 reference, "Optional Braces":
  <https://docs.scala-lang.org/scala3/reference/other-new-features/indentation.html>
- [S6] Scala 3 book, "Anonymous Functions" and "Function Variables":
  <https://docs.scala-lang.org/scala3/book/fun-anonymous-functions.html>,
  <https://docs.scala-lang.org/scala3/book/fun-function-variables.html>
- [A1] Agda documentation, "Function Definitions" (clauses; dot and absurd
  patterns):
  <https://agda.readthedocs.io/en/latest/language/function-definitions.html>
- [A2] Agda documentation, "With-Abstraction":
  <https://agda.readthedocs.io/en/latest/language/with-abstraction.html>
- [I1] Idris 2 documentation, "Types and Functions":
  <https://idris2.readthedocs.io/en/latest/tutorial/typesfuns.html>
- [K1] Koka book: <https://koka-lang.github.io/koka/doc/book.html>
- [F1] F\* tutorial, part 1:
  <https://fstar-lang.org/tutorial/book/part1/part1_getting_off_the_ground.html>
- [F2] F\* tutorial, "Computation Types and Tot", and "Div":
  <https://fstar-lang.org/tutorial/book/part4/part4_computation_types_and_tot.html>,
  <https://fstar-lang.org/tutorial/book/part4/part4_div.html>
- [U1] Unison documentation, "Using abilities, part 1":
  <https://www.unison-lang.org/docs/fundamentals/abilities/using-abilities-pt1/>
- [R1] Roc language reference, "Functions":
  <https://roc-lang.org/docs/main/langref/functions/>
- [G1] Gabriella Gonzalez, "Naming function arguments in Dhall":
  <https://haskellforall.com/2021/08/naming-function-arguments-in-dhall>
- [G2] Gleam for Erlang users:
  <https://gleam.run/cheatsheets/gleam-for-erlang-users>
