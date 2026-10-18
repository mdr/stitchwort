# Proposal: Lean/Scala-style declarations

**Status:** draft 1, 18 October 2026. For review; nothing is built.
Answers `TODO.md`'s "Declaration syntax" item: the user decided (18 Oct)
to **replace** Haskell-style declarations (a signature line `f : A -> B`,
then equations `f x = …`) with the Lean/Scala style (typed parameters
written inline, `def add (x : Nat) (y : Nat) : Nat := …`, and cases listed
under one header). This note is the detailed design and the migration plan.
Claims about other languages cite [Sources](#sources); anything not checked
against a source is marked **unverified**. Facts about Stitchwort were
checked against the source at `69112b7`.

**The one-sentence version:** every new form is translated by the parser
into the signature-plus-equations it replaces, so the elaborator, kernel
and pattern compiler don't change, and every core term (and its content
hash) stays the same, which is how we check that the migration is right.

## Contents

0. [Summary: before and after](#0-summary-before-and-after)
1. [What other languages do](#1-what-other-languages-do)
2. [The design](#2-the-design)
3. [Does anything of the old style stay?](#3-does-anything-of-the-old-style-stay)
4. [Errors, printing and the playground](#4-errors-printing-and-the-playground)
5. [Migration](#5-migration)
6. [Implementation plan](#6-implementation-plan)
7. [Questions for the user](#7-questions-for-the-user)

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
colon, and each case is an **arm** starting with `|`, with one pattern per
argument, separated by commas (as `match` already does):

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
  | Cons x xs => Eq.cong (\ys => Cons x ys) (appendNil xs)
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

### 2.1 Keywords

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

`:=` already means "this name gets this value" in Stitchwort: named
implicit arguments, `f [x := e]`. So the rule becomes: **`:=` gives a name
its value; `=` is equality.** It applies to `def`, `theorem`, `test`,
`let` and local definitions in `where`.

Two places keep `=` because nothing follows them that could contain an
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

| Binder | Meaning | Becomes, in the signature |
|---|---|---|
| `(x : A)`, `(x y : A)` | explicit parameters | `(x : A) -> …` |
| `[x : A]`, `[x y : A]` | implicit parameters | `[x : A] -> …` |
| `[auto h : P]` | evidence found by `auto` | `[auto h : P] -> …` |
| `()` | a parameter of type `()` that isn't used | `() -> …` |

- **Types are required** on named parameters: the header *is* the
  signature. (Lean allows untyped binders; we don't need them.)
- **Order is kept**: binders become the signature's arrows in the order
  written, so `def cong (f : a -> b) [x y : a] (p : x = y) : f x = f y`
  is exactly today's `(f : a -> b) -> [x y : a] -> x = y -> f x = f y`.
- **Auto-bound implicits work as today**: in `def mapList (f : a -> b) :
  List a -> List b`, `a` and `b` are bound automatically, since they're
  free and used only as types (`crates/elab/src/autobind.rs`). Lean has
  the same default and the same known risk (a typo becomes a parameter)
  [L1]; Stitchwort's `W-MODULE-NAME` warning already covers one case of
  it. Restricting auto-binding is a separate decision (question 6).
- **Brackets mean what they mean in types.** Readers coming from Lean
  should note that our `[x : A]` is Lean's `{x : A}`, and our
  `[auto h : P]` is closest to Lean's `[inst : C]` or Scala's `using`.
  We keep our brackets: they're used in every type already.
- **`()`** is new and small: `def tick () : {State Nat} Nat := …` instead
  of `tick : () -> {State Nat} Nat` / `tick u = …`. It's common because
  abilities need a function to delay a computation. It translates to an
  unused variable parameter, so it adds no case split (`def f () := e` is
  today's `f _ = e`).
- **The result type may start with an ability row**: `: {IO, Partial} ()`.
  A `{` straight after the header's colon starts a row, as it does after
  an arrow today. A definition that isn't a function, `def current :
  {State Nat} Nat := …`, is today's `current : {State Nat} Nat`.

The translation is mechanical: the binders become arrows in front of the
result type, giving today's `Decl::Signature`; the named explicit
parameters become variable patterns in every equation. Implicit and auto
parameters are in scope by name in the body, as they are in equations
today.

### 2.4 Cases: arms under the header

```
def pick : Nat -> List Nat -> Nat -> List Nat -> (Nat, List Nat)
  | Zero,   ds,          d, after => (d, after)
  | Succ w, Nil,         d, after => (d, after)
  | Succ w, Cons x rest, d, after =>
    if Nat.leq (d + 1) x then pick w rest x rest else pick w rest d after
```

- **Arms match the explicit arguments after the colon**, one pattern each,
  separated by commas, left to right, as in Lean [L2] and as in today's
  `match xs, ys with`. Each arm becomes one of today's equations, with the
  header's named parameters as variables in front. So the pattern compiler,
  exhaustiveness check (`E-NONEXHAUSTIVE`), number patterns, absurd
  patterns and the size-change termination check all see what they see
  today, unchanged.
- **Implicit and auto arguments after the colon are not matched**; they're
  in scope by name in every arm, as today ("Implicit and auto parameters
  are in scope by name in every equation", docs/syntax.md).
- **Named parameters can't be matched in arms.** They're the same in every
  arm. To take a named parameter apart, either move it after the colon,
  or make the body a `match` on it. A `match` that is the whole body, on
  parameters, already compiles into the definition's case tree (syntax-
  conveniences §4.3), so this costs nothing:

  ```
  theorem appendNil (xs : List a) : List.append xs Nil = xs :=
    match xs with
      | Nil       => rfl
      | Cons y ys => Eq.cong (\zs => Cons y zs) (appendNil ys)
  ```

  This is a matter of taste; both forms are allowed. The converter (§5)
  writes the arms form, since it is a one-for-one copy of the equations.
- **The number of patterns** must be the same in every arm, and at most the
  number of explicit arrows after the colon (fewer is allowed, as today: the
  definition then returns a function). A wrong count is today's `E-ARITY`,
  reworded to say "arm".
- **An absurd arm has no body**: `def absurd : Void -> a` / `| ()`. As
  today.
- **Layout**: arms start on lines after the header, indented, their `|`s
  lined up. An arm's body may continue on further-indented lines, or be a
  block, as an equation's right-hand side can today.
- **Termination clauses**, when they come (DESIGN.md §4's planned
  `decreasing b`), go after the last arm or the body, before `where`, as in
  Lean [L6].

Why not let arms bind names for header parameters (`def pick (w : Nat) …`
then `| Zero, … =>` matching `w`)? Then `w` in the body would mean
"the original argument" in some arms and be shadowed in others, which is
exactly what the Idris/Agda style avoids. Lean's split keeps one simple
rule: before the colon, a name that never changes; after it, patterns.

### 2.5 Dependent types and theorems

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

A long header may continue on the next line, indented, after any token,
as a long signature does today.

### 2.6 Effects and `Partial`

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
the named parameters plus the arms' patterns. Nothing about rows changes.

### 2.7 Data types, records, abilities: unchanged

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

We recommend no change here (question 4). Switching to Lean's
`inductive … where` or Scala's `enum` would be churn without a reading
benefit, and `type` reads plainly to a non-specialist.

### 2.8 `where` and namespaces

`where` (syntax-conveniences step 5, not built) is written in the new
style, and attaches to the **whole definition**, as in Lean [L5]:

```
def solve (ls : List Text) : Nat := go 0 ls
  where
    def go (acc : Nat) : List Text -> Nat
      | Nil       => acc
      | Cons l ls => go (acc + score l) ls

    def score (l : Text) : Nat := textLength l * weight

    def weight : Nat := 3
```

This changes one rule in syntax-conveniences §3.1, which made a `where`
belong to one equation and see its pattern variables (the Haskell, Agda,
Idris rule). With arms there's one `where` per definition, after the last
arm. It sees the **header's named parameters** (Lean's `loop` uses the
header's `a` [L5]) but not the arms' pattern variables. A helper that
needs one takes it as an argument, or the arm uses `let`. Everything else
in §3 (lifting, captures, `f.go` names, plain values as `let`s, order) is
unchanged. We keep the `def`/`theorem` keyword inside `where`; Lean
leaves it out [L5] (question 7).

Namespaces don't change: `def List.sum (xs : List Nat) : Nat := …`
declares `sum` in `List`'s namespace, as `List.sum : …` does today, and
dot notation still finds the first parameter of the type (`xs.sum`).

### 2.9 Lambdas, `let`, `match`, handlers: `=>` for "then do this"

We recommend one meaning per arrow: **`->` is only the function type;
`=>` separates a pattern or parameter from what follows** (in arms, `match`,
handlers and lambdas). This is Lean's split [L10]. Scala uses `=>` for
both [S6], which is the confusion we'd avoid.

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

The handler's operation clause is today `| op x => k -> body`, already
using `=>` (for "and the continuation is"). With `=>` as the arm arrow it
becomes `| op x, k => body`: the operation's argument and the
continuation, separated by a comma like two patterns. (Alternatives:
`| op x resume k => …`, closer to Koka; question 5.)

**Cost**: every lambda, `match`, `handle` and `let` in the code base
changes (about 350 lines with a lambda in `.sw` files alone). All of it is
done by the converter (§5), and none of it changes a core term. If the
user prefers, this part can be left out with no effect on the rest
(question 2).

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
| `E-OLD-DECLARATION` | `f : T` or `f x = e` at column 0 | "declarations start with `def`: `def f : T`" (with the arms the equations would become, if they're next to it) |
| `E-DEF-EQUALS` | `=` where `:=` is expected after a header or `let` | "a definition's body follows `:=`; `=` is equality" |
| `E-ARITY` (reworded) | arms with different numbers of patterns | "this arm has 2 patterns, but the first one has 3" |
| `E-ARITY` (reworded) | too many patterns | "`f` takes 2 arguments after the colon, but this arm has 3 patterns" |
| `E-NONEXHAUSTIVE` (reworded) | | "missing case: no arm matches `Cons _ Nil`"; note "add an arm…" |
| `E-ARM-PARAMETER` (new) | an arm's pattern count would reach into the named parameters, or `:=` and arms both given | "named parameters can't be matched in arms: move `w` after the colon, or use `match w with`" |
| `E-MISSING-SIGNATURE`, `E-MISSING-DEFINITION` | | can't happen any more (a header always has a type, and `def f : T` with neither `:=` nor arms is a parse error) |

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

(Counts by `grep` for lines like `name :` at column 0; approximate for
Rust and Markdown.)

### 5.2 A one-off converter, using spans, not a printer

A converter in Rust can do almost all of it. It should **rewrite text at
token spans**, not print the AST, because:

- the lexer throws away comments, and there is no surface printer
  (`crates/syntax` has none); printing from the AST would lose every
  comment and every hand-aligned column;
- span edits leave bodies exactly as written, and only touch headers,
  equation left-hand sides and a few tokens.

What it does, per file, from the parsed module:

1. **Group** each signature with its equations (as `collect` in
   `crates/elab/src/module.rs` does).
2. **Choose the form.** Explicit parameters that are a plain variable in
   *every* equation, counted from the left until the first column that
   isn't, become named parameters (taking the first equation's name, and
   renaming in the other equations if they differ; renaming changes no
   hash, since binder names aren't hashed, `crates/core/src/hash.rs`).
   A single equation with only variables becomes `def f (x : A) … : T :=
   body`. Otherwise the rest become arms.
3. **Write the header** by splitting the signature's type text at its
   top-level arrows: the first *k* explicit arrows become binders (with the
   equation's variable names; a `(x : A)` already named in the type is
   renamed to match), implicit and auto binders before them move into the
   header as written, and the rest stays after the colon. Where this
   can't be done with confidence (a named parameter's name also used in
   the type with another meaning, an arrow inside a `match` in the type),
   it uses the all-arms form, which is always a direct copy.
4. **Rewrite tokens** at spans the parser identifies: `=` → `:=` after
   headers, `let` and `test`; `->` → `=>` in lambdas, `match` and
   `handle` arms; `| op x => k ->` → `| op x, k =>`; the `export` line
   joined to its `def`.
5. **Keep everything else**: comments between equations move to just
   above the arm they preceded.

It runs before the old syntax is removed, using the parser that accepts
both (§6, lane A). It is deleted after the migration.

### 5.3 Checking it: the hashes must not move

A pure syntax change must produce the same core terms. Since content
hashes cover each definition's whole elaborated declaration (type, body,
everything it refers to) and leave out names and source locations
(DESIGN.md §11, `crates/core/src/hash.rs`), **identical hashes are strong
evidence that a converted file means the same as the original.**

- `crates/driver/tests/hash_stability.rs` pins the hash of every
  declaration in the prelude, `examples/accept` and `examples/extract`.
  After conversion, `cargo insta test` must show **no snapshot changes**.
  The test file itself doesn't change.
- The converter lane adds a one-off check over **every** `.sw` file and
  playground example (including `aoc/`, which the test doesn't cover):
  load the old text and the new text in fresh sessions and compare every
  declaration's hash. For `examples/reject` and `soundness`, compare the
  error codes instead (their positions move, so the snapshots of the
  messages are reviewed, not just accepted).
- Test results (`stitchwort test`) must be identical too.
- Known possible exception: today's `tick () = …` uses the `()` pattern,
  while the header's `()` translates to an unused variable. If the
  pattern compiler treats the two differently, those hashes change. The
  converter then keeps `| () => …` for those, or the lane lists them for
  review; it must not just accept them.

### 5.4 What's done by hand

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

## 6. Implementation plan

The parser changes in one crate (`crates/syntax`, 3749 lines); the
elaborator only in messages, and in `crates/elab/src/lib.rs` where it
builds `Decl::Signature`/`Decl::Equation` values itself for abilities
(which keep working, since the AST doesn't change). Each lane stays well
under 500k tokens.

| Lane | Model | What | Size |
|---|---|---|---|
| A. Parser | Opus | `def`/`theorem`/`test`/`export def` headers, binders, `()`, `:=`, arms, `=>` in lambdas/`match`/`handle`, the handler clause; all translated to today's `Signature` + `Equation`s. **Both** syntaxes accepted for now. Parser tests: each new form parses to the same AST (spans aside) as its old form. Layout rules written into `docs/syntax.md` as a draft section. | ~250k |
| B. Converter | Sonnet, Opus review | the span-based converter (§5.2) as a temporary binary; the all-files hash comparison (§5.3); run on 5 sample files with diffs shown | ~250k |
| C. Convert `.sw` | Sonnet | prelude, `examples/*`, `aoc/`, playground examples. Gate: zero `hash_stability` snapshot changes, all-files check clean, `nix flake check` passes | ~150k |
| D. Convert Rust and docs | Sonnet (two lanes if needed) | inline test sources; `docs/syntax.md`, DESIGN.md §4, core.md, testing.md, aoc-2025.md; historical-note banners | ~200k each |
| E. Remove the old syntax | Opus | delete old-form parsing; `E-OLD-DECLARATION`, `E-DEF-EQUALS`, `E-ARM-PARAMETER`; reword "equation" messages; reject examples for each new error | ~150k |
| F. Playground | Sonnet | keywords, defined-name rule, browser test | ~80k |
| G. `where` (step 5) | Opus | as syntax-conveniences §3, with §2.8's change; its own test plan there | separate |

Order: A, then B, then C and D in parallel, then E and F, then G. C is the
point where we learn whether the translation is exact; if a hash moves,
the lane stops and reports it.

## 7. Questions for the user

**Decided (18 October 2026):** the user agreed with every recommendation
below (1 to 9). The note goes to external review before implementation.

1. **`:=` before a body, instead of `=`** (§2.2)? Recommendation: **yes**.
   With the type on the same line, `theorem zeroPlus (n : Nat) : 0 + n = n
   = rfl` can't be read reliably by people or by the parser. `:=` is Lean's
   choice for the same reason, and Stitchwort already uses `:=` for named
   arguments.
2. **`=>` for arms, lambdas and handlers, `->` only for function types**
   (§2.9)? Recommendation: **yes**, in the same migration, since the
   converter does it at no extra risk. It can be dropped without
   affecting anything else.
3. **`let x := e`, and keep `=` in `type` declarations and record fields**
   (§2.2)? Recommendation: **yes** to both: `let` has the same ambiguity
   as `def`; `type` and records don't.
4. **Keep `type` and `ability` declarations as they are** (§2.7)?
   Recommendation: **yes**; they already have typed parameters.
5. **Handler clause `| op x, k => body`** (§2.9)? Recommendation: **yes**
   (the shortest change); the alternative is `| op x resume k => body`.
6. **Auto-bound implicits: keep as today** (§2.3)? Recommendation: **keep
   for now**, and consider Lean's stricter mode (single letters only) as a
   separate change later. Lean's own manual warns that typos become
   parameters [L1], and Mathlib turns it off [L7], but every `List a ->`
   in the code base relies on it.
7. **`def` and `theorem` keywords inside `where`** (§2.8)? Recommendation:
   **keep them** (unlike Lean), so a helper can move between top level and
   `where` unchanged.
8. **A `where` belongs to the whole definition and sees the header's
   parameters, not arms' pattern variables** (§2.8, a change to
   syntax-conveniences §3.1)? Recommendation: **yes**, as Lean.
9. **Migration by a span-based converter, checked by unchanged hashes,
   with both syntaxes accepted only during the migration** (§5, §6)?
   Recommendation: **yes**.

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
