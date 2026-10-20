# Lambdas without the backslash (SW-90), draft 1

**Date:** 20 October 2026. **Ticket:** SW-90 (related: SW-19, annotated lambda parameters;
D89 asked for this note). **Decisions:** D92 to D100, all open.
**Status:** design only, for Matt and an external review. Nothing is implemented.

Claims about Stitchwort are marked **[checked]** when I read or ran the thing named (line
numbers are for `main` at `6257b9d`), and **[estimate]** when they are guesses. Claims about
other languages cite [Sources](#sources); anything I couldn't check against an official
source is marked **unverified**.

## Contents

0. [The short version](#0-the-short-version)
1. [Lambdas today](#1-lambdas-today)
2. [How other languages write lambdas](#2-how-other-languages-write-lambdas)
3. [The options](#3-the-options)
4. [The proposed syntax](#4-the-proposed-syntax)
5. [Parsing it](#5-parsing-it)
6. [Every place it could be ambiguous](#6-every-place-it-could-be-ambiguous)
7. [Near-misses and their messages](#7-near-misses-and-their-messages)
8. [Migration](#8-migration)
9. [Risks](#9-risks)
10. [Decisions](#10-decisions)

## 0. The short version

Write lambdas the way Scala, TypeScript and C# do:

| Today | Proposed |
|---|---|
| `\x => x + 1` | `x => x + 1` |
| `\acc x => acc + x` | `(acc, x) => acc + x` |
| `\(x: Nat) => x + 1` (SW-19, being built) | `(x: Nat) => x + 1` |
| `\(x: Nat) (y: Nat) => x + y` | `(x: Nat, y: Nat) => x + y` |
| `\(a, b) => a + b` (one pair, taken apart) | `((a, b)) => a + b` |
| `\acc (k, v) => acc + v` | `(acc, (k, v)) => acc + v` |
| `\{ name, .. } => name` | `({ name, .. }) => name` |
| `\() => e` | `() => e` |
| `\_ => 0` | `_ => 0` |

The rule in one sentence: **a lambda is either one bare name (or `_`) before `=>`, or a
bracketed list of parameters separated by commas, exactly like the patterns of an arm.** An
arm `| acc, (k, v) => …` and a lambda `(acc, (k, v)) => …` then take their arguments the same
way, which today's `\acc (k, v) => …` doesn't (it separates parameters by spaces, while arms
use commas).

The one real change of meaning is `(a, b) => e`: today `\(a, b) => e` takes one pair; in
the new syntax `(a, b) => e` takes two arguments, as it does in every mainstream language.
Taking a pair apart needs its own brackets, `((a, b)) => e`, as TypeScript writes
`([a, b]) => …` and Kotlin `{ (a, b) -> … }`. That form is rare here (12 lambdas in the whole
repository **[checked]**).

The parser decides cheaply: a lambda starts with a lower-case name or `_` followed by `=>`,
or with a `(` whose matching `)` is followed by `=>`. Matching brackets are found from a table
built once per declaration, so there's no backtracking and no slowdown on deeply nested
brackets. This is the same test the parser already uses to tell `(x: A) -> B` (a function
type) from `(x: A)` (an annotation), with one more arrow to look for.

Nothing after the parser changes: the new forms produce exactly the syntax trees the old
ones do, so elaborated terms and content hashes stay the same. About 1,700 lambdas in the
repository change (§8); a one-off rewriting tool, checked by comparing syntax trees before and
after, does the `.sw` files and the code blocks in the docs.

**Recommendation:** adopt it (option B), with no transition period: `\` becomes an error that
shows the new form (D92 to D100, §10).

## 1. Lambdas today

**[checked]** against `docs/syntax.md` and `crates/syntax/src/parser.rs`:

- **Form.** `\` then one or more parameters separated by spaces, then `=>`, then the body
  (`parser.rs:1320`, `fn lambda`). A parameter is a name, `_`, or a pattern starting with
  `(`, `{`, a constructor or a number: `\x (a, b) => …`, `\{ name, .. } => name`.
- **Patterns.** A lambda with a pattern parameter becomes a lambda over a fresh name
  (`%arg0`) whose body is a one-alternative `match`, which must cover every value
  (`docs/syntax.md`, "Patterns in `let` and lambdas").
- **No types on parameters yet.** `\(x: T) => …` is refused with "a lambda's parameter can't
  have a type here" (`parser.rs:1340`). SW-19 is adding it now.
- **Where a lambda may start.** Only at the start of an expression (`expr_inline`,
  `parser.rs:1601`) or right after `|>` (`pipe_chain`, `parser.rs:1763`). It isn't an atom,
  so as an argument it needs brackets: `List.map (\x => x + 1) xs`.
- **How far it reaches.** The body is a whole expression (`self.expr()`), so it extends as
  far right as it can, as in Haskell. After `|>`, a lambda takes the rest of the pipeline:
  `x |> \y => f y |> g` is `x |> \y => (f y |> g)`.
- **`=>` already means "the patterns end here, what follows is the result"** in arms,
  `match`, handlers and lambdas; `->` is only the function type. This was decided in the
  declaration-syntax proposal (§2.11), which also gave a reason for keeping `\`: with `\`, the
  annotated lambda `\(x: T) => …` doesn't look like the function type `(x: T) -> B`. §6.2
  revisits that.
- **Three readings of `(` today.** `(x: Nat) -> B` is a function type, found by scanning to
  the matching `)` and looking for `->` (`is_pi_binder`, `parser.rs:1659`); `(x: Nat)` without
  the arrow is an annotation (test `parenthesised_names_without_an_arrow_are_annotations`);
  `(a, b)` is a tuple or tuple type; `(e)` is grouping.
- **The printer** shows a lambda as `\x => body`, one parameter at a time
  (`crates/core/src/pretty.rs:337`).

## 2. How other languages write lambdas

### 2.1 Summary

| Language | One parameter | Several | Typed | Taking a pair apart |
|---|---|---|---|---|
| Scala 3 | `x => e` | `(x, y) => e` | `(x: Int) => e` | `{ case (x, y) => e }`, or untupling: `(x, y) => e` where a function of a pair is expected |
| TypeScript / JavaScript | `x => e` | `(x, y) => e` | `(x: number) => e` (TS) | `([x, y]) => e` |
| C# | `x => e` | `(x, y) => e` | `(int x, string s) => e` | not shown (unverified) |
| Kotlin | `{ x -> e }` or `{ it … }` | `{ x, y -> e }` | `{ x: Int, y: Int -> e }` | `{ (x, y) -> e }` |
| Swift | `{ x in e }` | `{ x, y in e }` | `{ (x: Int) -> Int in e }` | not checked |
| Lean 4 | `fun x => e` | `fun x y => e` | `fun (x : Nat) => e` | `fun (x, y) => e` |
| Haskell | `\x -> e` | `\x y -> e` | not in Haskell 2010 | `\(x, y) -> e` |
| Agda | `λ x → e` or `\ x → e` | `λ x y → e` | `λ (x : A) → e` | `λ { (x , y) → e }` |
| Idris 2 | `\x => e` | `\x, y => e` | `\x : Int => e` | `\(x, y) => e` |
| Gleam | `fn(x) { e }` | `fn(x, y) { e }` | not checked | not checked |
| Unison | `x -> e` | `x y -> e` (in brackets as an argument) | not shown | `cases (x, y) -> e` |

There are two families. **Mainstream languages** (Scala, TypeScript, C#, Kotlin, Swift) put
several parameters in one list with commas, and `(a, b)` there means two parameters. **The
functional and proof languages** (Haskell, Lean, Agda, Idris, Unison) put parameters side by
side with spaces, and `(a, b)` there means one pair taken apart. Stitchwort today is in the
second family.

### 2.2 Scala 3

The grammar's lambda rule is `Expr ::= FunParams ('=>' | '?=>') Expr`, with
`FunParams ::= Bindings | id | '_'`, `Bindings ::= '(' [Binding {',' Binding}] ')'` and
`Binding ::= (id | '_') [':' Type]` [S1]. So a parameter list holds names with optional types,
**not patterns**: to take a pair apart the classic way is a partial-function block,
`xs.map { case (x, y) => x + y }` [S1, S3]. Scala 3 added *parameter untupling*: a lambda with
n parameters is accepted "if the expected type for checking `f` is a fully defined function
type of the form `TupleN[T1, ..., Tn] => R`" [S4], so `xs.map((x, y) => x + y)` works on a
list of pairs [S3]. The placeholder `_ * 2` is short for `x => x * 2` [S2]. Scala writes
dependent function *types* with the same arrow as lambdas, `(e: Entry) => e.Key` [S5], and
tells them apart by whether a type or a term is expected.

### 2.3 TypeScript and JavaScript

`param => expression`, `(param1, paramN) => expression`, and destructuring "always require
parentheses": `([a, b] = [10, 20]) => …`, `({ a, b } = …) => …` [J2]. There may be no line
break between the parameters and `=>` [J2].

**How the parser decides.** The ECMAScript grammar uses a *cover grammar*: an arrow function's
parameters are `ArrowParameters : BindingIdentifier | CoverParenthesizedExpressionAndArrowParameterList`,
and "the interpretation of CoverParenthesizedExpressionAndArrowParameterList is refined using
the following grammar: ArrowFormalParameters : ( UniqueFormalParameters )" [J1]. In plain
words: the parser reads `( … )` as if it might be either, and once it sees `=>` it re-reads
the same tokens as parameters. The ArrowFunction rule also says `[no LineTerminator here]`
before `=>` [J1].

The TypeScript compiler (now written in Go) decides with a three-way answer, *true*, *false*
or *unknown* [J3]. `() =>` and `(a:` are definitely a lambda ("If we have something like
"(a:", then we must have a type-annotated parameter in an arrow function expression"); `(`
followed by something that can't start a parameter is definitely not; `([` and `({` are
*unknown*, "this could be the start of a binding pattern", and the parser tries a lambda and
backs off if it fails, remembering positions where it failed so it doesn't try twice [J3].

Two JavaScript pitfalls worth avoiding: `callback || () => {}` is a syntax error ("parentheses
are necessary to avoid `callback || ()` being parsed as the arguments list") [J2], and
`() => { foo: 1 }` returns `undefined` because `{` after `=>` starts a block [J2].

### 2.4 C#

`x => x * x`, `(x, y) => x == y`, `() => …`; types `(int x, string s) => s.Length > x`, and
"input parameter types must be all explicit or all implicit" [C1]. `(_, _) => 42` discards
both [C1].

### 2.5 Kotlin and Swift

Kotlin: "a lambda expression is always surrounded by curly braces",
`{ x: Int, y: Int -> x + y }`; with one parameter it can be left out and called `it`; a pair
is taken apart with brackets, `{ (_, value) -> … }` [K1]. Swift: `{ (parameters) -> return
type in statements }`, with types inferred from context and `$0`, `$1` as short names [W1].
Both put the parameters *inside* the braces, which is how they avoid any ambiguity with
brackets.

### 2.6 Lean 4

`fun x => e`, `fun x : T => e`, and with brackets `fun (x : T) => e`; `↦` may replace `=>`
[L1]. "Function abstractions may also use pattern matching syntax as part of their parameter
specification" [L1], so `fun (a, b) => …` takes a pair apart (that exact example isn't on the
page: unverified as a quotation, but it follows from the sentence). `fun | 0 => true | _ =>
false` matches with alternatives [L2]. `(· + 1)` is short for `fun x => x + 1` [L1]. The
keyword means there's never a question where a lambda starts.

### 2.7 Haskell, Agda, Idris 2

Haskell 2010: `\ apat1 … apatn -> exp`, and lambdas, `let` and `if` "extend as far to the
right as possible" [H1]. If a lambda's pattern doesn't match, the result is undefined [H1].
Agda: `\ x → x + x` or `λ`, typed `\ (A : Set)(x : A) → x`, pattern lambdas
`λ { true x → x ; false _ → false }` and `λ where`, and the absurd lambda `λ ()` [A1].
Idris 2: `\x => val`, several parameters with commas, `\x, y, z => val`, types
`\x : Int => x * 2`, patterns `\(x, y) => x + y` [I1]. Stitchwort's current `\x => e` is
Idris's.

### 2.8 Gleam and Unison

Gleam keeps a keyword and braces, `fn(x) { … }`, and has a capture shorthand,
`some_function(..., _, ...)` [G1, G2]. Unison: `elem -> elem + 1`; "a lambda with two
arguments is represented by separating the function arguments with spaces"; patterns use
`cases`: `cases (a, b) -> a Nat.+ b` [U1]. Unison has no keyword or backslash, like the
proposal, but uses `->` for both lambdas and function types.

### 2.9 What to take from this

1. **`x => e` and `(x, y) => e` are by far the most widely read lambda forms** (Scala, C#,
   TypeScript and JavaScript). That's Matt's preferred style, and also what Stitchwort's arms
   already look like (`| x, y => …`).
2. **Bracketed parameter lists need a decision rule**, and the two known ones are a cover
   grammar (JavaScript) and lookahead with speculative parsing (TypeScript). Stitchwort's
   parser has all tokens in a vector already, which allows a simpler, exact rule (§5).
3. **No mainstream language lets `(a, b) => …` mean "one pair"**: pair destructuring always
   has its own brackets (`([a, b]) =>`, `{ (a, b) -> }`) or a `case`. Scala's untupling is a
   type-directed convenience on top.

## 3. The options

### Option A: keep `\`

`\x => e`, `\acc x => e`, `\(x: T) => e` once SW-19 lands.

- For: no migration. Familiar to Haskell and Idris readers. The parser can't confuse a
  lambda with anything, and errors are easy to word.
- Against: unfamiliar to most programmers; `\` looks like noise to people who haven't met
  Haskell. It needs escaping in Rust strings, JSON and Markdown tables: the board's own
  ticket for SW-19 says `\\(y: Nat)` **[checked]**. It is the one place where parameters are
  separated by spaces while arms separate them by commas.

### Option B: Scala/TypeScript style, no `\` (recommended)

`x => e`, `(acc, x) => e`, `(x: T) => e`, `((a, b)) => e`. Details in §4.

- For: matches Matt's stated style and the most widely used languages. Lines up with arms
  (`(acc, (k, v)) => …` versus `| acc, (k, v) => …`). Also lines up with the function type:
  `(x: Nat) -> P x` and a value of it, `(x: Nat) => proof`, differ only in the arrow (§6.2).
  Code written by people (and, I'd expect, by language models; **unverified**) coming from
  TypeScript, Scala or C# is more likely to be right first time.
- Against: a one-off migration of about 1,700 lambdas (§8). `(a, b) => e` changes meaning
  for anyone used to Haskell, Lean or Idris (it's two arguments, not a pair); §7 gives that
  case its own error message. Several parameters cost brackets and commas:
  `\w _ => w R c` becomes `(w, _) => w R c`, which matters in proof motives. A lambda
  returning a lambda in an arm reads as a chain of `=>`: `| return x => st => MkPair x st`.

### Option C: both, during a transition

Accept `\x => e` and `x => e` for a while.

- For: nothing breaks on the day.
- Against: two ways to write the same thing, in docs and in examples that people copy.
  Matt chose "no transition period" for the declaration syntax (declaration-syntax
  proposal, status line), and the same reasoning holds: there are no outside users, and one
  commit can convert everything. Keeping `\` only to produce a helpful error gives the
  benefit without the cost (D96).

### Option D: a keyword, `fun x => e`

Lean, OCaml and F# style (Gleam: `fn`).

- For: a lambda always starts with a word, so parsing and error messages are as easy as with
  `\`, and it's searchable. Fits next to `def`. Lean users would feel at home, and Lean is the
  closest relative among proof languages.
- Against: it isn't the Scala/TypeScript style Matt prefers; it's longer than either today's
  `\` or option B, and lambdas are frequent (about 1,300 of the 1,700 are one-parameter
  lambdas, often inside an argument list).

### Option B′: no `\`, but parameters side by side (Lean without `fun`)

`x => e`, `acc x => e`, `(a, b) => e` meaning one pair. Not recommended, but worth recording
because migrating would be just "delete the `\`".

- Against: `g x => e` would quietly be a lambda with two parameters, `g` and `x`, when the
  writer meant `g (x => e)`; nothing in the syntax tells the two apart, and the mistake
  surfaces later as a confusing type error, or not at all. And `(a, b) => e` would mean the
  opposite of what Scala and TypeScript readers expect.

## 4. The proposed syntax

```
lambda   ::= head "=>" expr
head     ::= name | "_"                       -- one parameter, no brackets
           | "(" ")"                          -- one parameter, the unit value
           | "(" param ("," param)* ","? ")"
param    ::= name+ ":" type                   -- typed: `x: Nat`, or `x y: Nat` (D95)
           | pattern                          -- as in an arm: `x`, `_`, `(a, b)`, `{ name, .. }`,
                                              -- `MkPair a b` (no brackets needed), `[]` …
```

- **Several parameters are curried**, as today: `(acc, x) => e` is `acc => x => e`, and is
  called `f acc x`. Its syntax tree is the same as today's `\acc x => e` (`Expr::Lam` with
  two names).
- **Patterns** are those of an arm, so a constructor takes its arguments without brackets
  (`(MkPair a b, c) => …`) and a pair needs its own brackets (`((a, b), c) => …`), exactly as
  in `| MkPair a b, c =>` and `| (a, b), c =>`. As today, a pattern parameter must cover its
  type (a lambda can't fail).
- **`() => e`** is a function taking the unit value, called `f()`. That's what TypeScript
  readers expect from `() => e` and `f()`, and it is today's `\() => e`.
- **`(x) => e`** is allowed and means `x => e` (TypeScript and Scala allow it too).
- **Typed parameters** (SW-19's feature, D95): `(x: Nat) => e`, `(x: Nat, y: Nat) => e`,
  mixed `(acc, x: Nat) => e`, and later types may mention earlier names:
  `(a: Type, x: a) => x`. `(x y: Nat) => e` is accepted as one item, mirroring the function
  type `(x y: Nat) -> B` and definition headers.
- **The body** is an expression and reaches as far right as possible, as today. `{` after
  `=>` is a record literal, never a block (Stitchwort's blocks are made by layout), so
  JavaScript's `() => { foo: 1 }` trap doesn't exist.
- **What SW-19 becomes.** Whatever syntax tree SW-19 builds for `\(x: T) => e` is kept; only
  the surface changes: `\(x: T) => e` is written `(x: T) => e`, and SW-19's
  `\(x: T) (y: U) => e` is written `(x: T, y: U) => e`. Its tests and examples go through the
  same rewrite as everything else (§8). The `E-CANNOT-INFER` hint it adds ("annotate the
  parameter, `\(p: Person) => p.name`") changes to `(p: Person) => p.name`.

Out of scope: implicit lambdas (`[a: Type] => …`), a match-lambda with several alternatives
(Lean's `fun | … | …`, Scala's `{ case … }`), and placeholder shorthands like Scala's `_ * 2`
(method sections, `.name`, already cover the most common case). None of them is made harder by
this syntax. Stitchwort has no `do` notation (DESIGN.md: effects are written in direct style)
and this changes nothing there.

## 5. Parsing it

### 5.1 The rule

At the two places a lambda may start today (the start of an expression, and right after
`|>`), the parser checks:

1. a lower-case name or `_`, and the next token is `=>`: a one-parameter lambda; or
2. `(`, and the token after its **matching** `)` is `=>`: a lambda with a parameter list.

Anything else is parsed as before. Once it has decided, it parses the parameter list with a
dedicated function (each item: `name+ :` type, found by the same lookahead
`is_implicit_binder` uses, or a pattern), then `=>`, then the body. No re-reading, no
backtracking.

This is the test `is_pi_binder` already makes for `(x: A) -> B` (`parser.rs:1659`), with
`=>` in place of `->`. Together they give `(` four readings, decided by what follows the
matching `)`:

| After the matching `)` | `(x: Nat)` | `(a, b)` |
|---|---|---|
| `->` | function type `(x: Nat) -> …` | tuple type `(A, B) -> …` |
| `=>` | lambda | lambda with two parameters |
| anything else | annotation | tuple |

### 5.2 Why not a cover grammar

JavaScript parses `( … )` as an expression and reinterprets it as parameters when `=>`
appears [J1]. That works when every parameter form is also an expression. In Stitchwort it
isn't: `{ name, .. }`, `[x, ..rest]`, `(-1)` and a constructor applied to patterns are
patterns with no matching expression (or a different one), so a cover grammar would need a
third kind of syntax tree for "either". TypeScript's speculative parsing [J3] avoids that but
needs save, rewind and a cache of failures. Stitchwort's lexer produces every token of a
declaration before parsing starts (`self.tokens`), so looking ahead to a bracket's partner is
direct.

### 5.3 Cost: the matching-bracket table

A naive scan from each `(` to its partner is slow on deeply nested brackets: the benchmark
`check-nested-parens` parses `((…(0)…))` 12,000 deep (`crates/bench/src/programs.rs:165`
**[checked]**), and scanning from every `(` would be over 100 million token steps
**[estimate]**. Instead, the parser builds a table from each `(` to the index of its partner
once per declaration, in one pass with a stack (a `Vec<u32>` the size of the token vector).
Each check is then one lookup. The table lives on the parser, not on the call stack, so the
nesting limits (which are measured in stack) don't move. `is_pi_binder` should use it too.

### 5.4 Size of the change

**[estimate]**, one lane: about 200 lines of parser code (the check, the parameter-list
parser, the new errors in §7), about 60 removed (the `\` path, kept only as the error), the
printer (one function), and 40 or so parser tests. The syntax tree, elaborator, kernel and JS
back end don't change.

## 6. Every place it could be ambiguous

Each case below names the competing reading and how the rule in §5.1 settles it.

### 6.1 `x => e` against arms, `match` and handlers

`| p => e` in arms, `match` and `handle` is read by the pattern parser, which stops at `=>`;
the lambda check is never asked there. A lambda *inside* an arm's result is fine and
unambiguous, because the first `=>` has already ended the patterns:

```
handle prog() with
  | return x => st => MkPair x st
  | get(), k => st => k st st
```

On one line, `match n with | Zero => x => x | Succ k => f k`: the lambda's body `x` stops at
`|`, as `\x => x` does today. A lower-case name followed by `=>` at the start of an expression
is never anything else today: a stray `=>` after an expression is a parse error now
(**[checked]** with the built compiler: `:= n => n` gives "expected the end of the
declaration, but found `=>`", and the same after an arm's result or `List.map x`), so rule 1
takes nothing away.

### 6.2 `(x: T) => e` against `(e: T)` and `(x: T) -> B`

Stitchwort has the annotation `(e: T)` (`({ x = 0, y = 0 }: Point)`, `(5: Int)`) and the
dependent function type `(x: T) -> B`. All three start `( name :`, and the token after the
matching `)` decides (§5.1). The declaration-syntax proposal (§2.11) kept `\` partly so that
`\(x: T) => e` wouldn't look like `(x: T) -> B`. Without `\` they now differ only in the
arrow. I think that is a feature, not a risk: a function and its type look alike, and the
arrow says which is which.

```
def twice: (n: Nat) -> Nat := (n: Nat) => n + n
```

Scala uses the *same* arrow for both and tells them apart by context [S5]; Lean uses `fun`
for the value and `→` for the type [L1]. Stitchwort would sit between. The risky mistake is
typing the wrong arrow, and §7 gives both directions their own message.

### 6.3 Tuples and tuple patterns

`(a, b)` followed by `=>` is two parameters; anywhere else it's a tuple (or a tuple type
before `->`). `((a, b)) => e` is one pair parameter; `((a, b))` elsewhere is just a tuple in
redundant brackets. `(a, b) -> T` stays a function type from a tuple. A tuple annotation
inside a parameter list, `((a, b): (Nat, Nat)) => …`, follows `let (a, b): (Nat, Nat) := e`
if SW-19's annotation covers patterns; otherwise it's an error naming the alternative.

### 6.4 `|>`

`pipe_chain` (`parser.rs:1763`) checks for `\` today; it would use the new check instead.
`xs |> ys => List.append ys [0] |> List.sum` keeps today's meaning: the lambda takes the rest
of the pipeline. `xs |> (acc, x) => …` works the same way.

### 6.5 Application: `f x => e`

A lambda isn't an argument without brackets, today or in the proposal: `List.map (x => x + 1)
xs`. When the parser reads `List.map x => …`, it parses the application `List.map x`, then
finds `=>` where an expression has ended. That's an error with a specific message (§7),
the same choice JavaScript makes for `callback || () => {}` [J2]. Rule 1 only fires at the
start of an expression, so `f x =>` never quietly becomes a lambda with parameters `f` and
`x` (the danger of option B′). The same applies after any operator: `a + x => e`,
`a || x => e` are errors, with the hint to bracket the lambda.

### 6.6 `if`, `let`, blocks, records

- `if c then x => a else y => b`: each branch's lambda body stops at `else` (or the end), as
  `\x => a` does today.
- `let f := x => x + 1` and `let f: Nat -> Nat := x => x + 1` work as expected; `let (a, b)
  := e` is a `let` pattern, not a lambda (it uses `:=`).
- A block whose last line is `(a, b) => a + b` returns that function.
- Record fields: `{ f = x => x + 1 }` and updates `{ r | f = x => … }` work, since a field
  value is an expression.
- `calc` steps start with `_`, but are always `_ =`, `_ <=` or `_ <`; `_ =>` is lexed as `_`
  then `=>`, so `_ => e` (a lambda ignoring its argument) can't be confused with a step.

### 6.7 Layout

A lambda's body may start on the next line, as today. `=>` itself may begin a continuation
line, indented further than the line the lambda starts on, like any operator in a
continuation; at or left of the block's column it starts a new statement and the lookahead
doesn't see it (the same "stop" rule `at_pipe` uses, `parser.rs:1733`). JavaScript forbids a
line break before `=>` [J1]; Stitchwort doesn't need to, because its layout rules already say
where a statement ends.

### 6.8 Unclosed brackets

`(a, b => e` has no matching `)`, so it isn't a lambda by the rule; it's parsed as a tuple and
fails at `=>` with "expected `)`". The message gets a note when the unclosed `(` is followed
by `=>` inside: "a lambda's parameter list is closed before `=>`: `(a, b) => e`".

## 7. Near-misses and their messages

| Written | What happens | Message (draft) |
|---|---|---|
| `\x => e`, `\acc x => e` | `\` is still a token, only to give this error | `E-OLD-LAMBDA` "lambdas are written without `\`"; note with the exact rewrite, built from the old parameter parser: "write `(acc, x) => e`" (and `((a, b)) => e` for `\(a, b) => e`) |
| `x y => e` | `=>` after the application `x y` | "a lambda with several parameters lists them in brackets: `(x, y) => e`" |
| `List.map x => e` | `=>` after `List.map x` | "to pass a lambda as an argument, put it in brackets: `List.map (x => e)`" (the same check as the row above: when the head isn't a plain name, only this note; when it is, both notes) |
| `(a, b) => e` where a function of a pair is expected | the elaborator checks a two-parameter lambda against `Pair A B -> C` and fails at `b` | the type error, plus a note: "this lambda takes two arguments; to take one pair apart, write `((a, b)) => e`" (the parser marks lambdas written with a comma list so the note can be specific) |
| `((a, b)) => e` where two arguments are expected | the pattern `(a, b)` against `A` | the type error, plus: "this lambda takes one pair; for two arguments write `(a, b) => e`" |
| `(x: Nat) -> x + 1` where a value is expected | parses as a function type whose result `x + 1` isn't a type | the not-a-type error, plus: "a function value is written with `=>`: `(x: Nat) => x + 1`" |
| `x -> x + 1` (Unison, Kotlin, Haskell habit) | the function type `x -> …` | the same note: "a lambda uses `=>`" |
| `def f: (n: Nat) => Nat` | a lambda where a type is expected | `E-NOT-A-TYPE`, plus "a function type uses `->`" |
| `(x: Nat) (y: Nat) => e` (header habit) | `(x: Nat)` then `(` | "a lambda's parameters go in one list: `(x: Nat, y: Nat) => e`" (found by continuing the bracket lookahead across adjacent groups) |
| `() => e` where `Nat -> …` is expected | the unit pattern against `Nat` | the type error, plus "`()` is the unit value; for a parameter you don't use, write `_ => e`" |

## 8. Migration

### 8.1 How many lambdas

Counted with a regular expression for `\` followed by parameters and `=>` on one line, over
the files git tracks **[checked]**; approximate, since it can't see a lambda whose `=>` is on
another line, and in Rust it counts lambdas inside test strings:

| Where | Lambdas | Files |
|---|---|---|
| Library (`crates/elab`, `.sw`) | 551 | 9 |
| Advent of Code (`aoc/`, `.sw`) | 447 | 8 |
| `examples/` (`.sw`) | 274 | 77 |
| Rust test and benchmark sources (syntax 70, driver 51, elab 29, core 18, bench 13, cli 7, js 4, web 3) | 195 | 41 |
| Docs (`docs/proposals` 112, `syntax.md` 43, `aoc-2025.md` 31, others 20, `DESIGN.md` 8) | 214 | 17 |
| `board/tickets.json` | 15 | 1 |
| Playground examples (`web/index.html`) | 6 | 1 |
| Editor grammars (`editors/`) | 0 | 0 |
| **Total** | **about 1,700** | |

By kind: 1,303 have one plain name, 339 several plain names, 52 a pattern (12 of them a tuple,
7 a record), and 8 an annotation (in tickets, tests and docs ahead of SW-19). Separately, 29
snapshot files (`crates/cli/tests/snapshots/*.snap`) show lambdas in quoted source or printed
terms; they're regenerated, not edited.

### 8.2 Is a mechanical rewrite safe?

There's no formatter (the CLI has `check`, `test`, `run`, `eval`, `repl` and `build`
**[checked]**), and the old declaration converter crate was removed after its migration. A
plain text substitution is **not** safe: deleting the `\` from `\(a, b) => e` gives
`(a, b) => e`, which now takes two arguments, and `\acc x => e` would become the error
`acc x => e`. The rewrite has to know the parameter list.

Proposed tool (a throwaway dev binary, like the declaration converter was):

1. Lex each file; for each `\` token, run today's `lambda` parameter parser to get the
   parameters' source ranges.
2. Replace the text from `\` to `=>` with the new head: one plain name stays bare (`x =>`);
   otherwise `(` + the parameters' original text joined by `, ` + `)`, where a parameter that
   is a pair pattern, or a constructor applied to arguments in brackets (`(Just x)`), keeps
   its brackets as written: `\acc (k, v)` → `(acc, (k, v))`, `\(a, b)` → `((a, b))`.
3. **Check:** the old parser on the old text and the new parser on the new text must give the
   same syntax tree, compared without positions by `crates/syntax/src/equivalence.rs`
   (`shape`), which was built for exactly this in the declaration-syntax switch. Any
   difference stops the tool on that file.

The `.sw` files (1,272 lambdas) and the docs' ```` ``` ```` code blocks go through the tool.
Rust test strings, inline code in prose, the board and the playground's six are done by hand
or by a reviewed search-and-replace; anything missed in a test string fails loudly, because
`\` becomes `E-OLD-LAMBDA` (§7), except tests that expect a parse error, which need a look
each.

### 8.3 Hashes

A definition's hash covers its elaborated type and body; binder names, local variable names
and source positions aren't hashed (`docs/core.md`, "Tests and content hashes";
`crates/core/src/hash.rs` header comment **[checked]**). The rewrite produces the same syntax
trees (checked in step 3), so the same elaborated terms, so the same hashes. As with the
declaration switch, comparing every declaration's hash before and after is the end-to-end
check that the migration changed nothing. (The test cache will still rerun everything once,
because its key includes a fingerprint of the compiler's source; that's expected.)

### 8.4 Printer, editors, playground

- **Printer** (`crates/core/src/pretty.rs:337`): print `x => body`, and gather nested lambdas
  into one list, `(x, y) => body`, which is shorter than `x => y => body` and is what people
  write (D100). Snapshots change with it.
- **VS Code grammar** (`editors/vscode/syntaxes/stitchwort.tmLanguage.json`): `=>` is already
  an operator; `\` is in its operator character class and can stay or go. No new rule is
  needed: parameters are coloured as names, as they are in arms.
- **Playground highlighter** (`web/index.html`, the hand-written tokenizer): no change; `\` is
  coloured as an operator by its fallback branch. Its six example lambdas are rewritten.
- **Docs**: `docs/syntax.md` (the expression table, "Patterns in `let` and lambdas", the
  pipe and method-section sections), DESIGN.md §4, and the declaration-syntax proposal's
  §2.11 gets a pointer to this note.

### 8.5 Order of work

1. SW-19 lands first (annotated parameters with `\`). This note doesn't block it.
2. One lane: the parser change, `E-OLD-LAMBDA` and the other messages, the printer, the
   rewriting tool; then the tool run over the repository, hashes compared, in one commit
   (as the declaration switch was).
3. Docs and the remaining hand edits in the same lane; the tool is deleted afterwards.

## 9. Risks

- **The meaning of `(a, b) => e` flips** for readers from Haskell, Lean or Idris, and for
  this codebase's own habits. Mitigation: the two notes in §7 are specific, and the rewrite
  tool never produces the wrong reading (step 3).
- **Proof motives get a little longer**: `J (\y' p' => f x = f y') rfl p` becomes
  `J ((y', p') => f x = f y') rfl p`. Measurable but small; about 340 lambdas have several
  parameters.
- **A lambda returning a lambda** in an arm reads as a chain of `=>`. Brackets help where it
  matters: `| return x => (st => MkPair x st)`.
- **Stray `=>` errors** now need to tell three intentions apart (§7). Getting the wording
  right is most of the parser work; it's tested with a reject example per row of §7.
- **Unverified:** that language models write the Scala/TypeScript form more reliably than
  `\x => e`. It's plausible from how much more common the form is, but I haven't measured it.

## 10. Decisions

| ID | Question | Recommended answer |
|---|---|---|
| D92 | Which lambda syntax: keep `\` (A), Scala/TS arrows (B), both for a while (C), a keyword `fun` (D)? | **B**: `x => e`, `(x, y) => e`, `(x: T) => e` |
| D93 | What does `(a, b) => e` mean? | **Two (curried) parameters**, as in Scala, TypeScript and C#; a pair taken apart is `((a, b)) => e` |
| D94 | Should `(a, b) => e` also be accepted where a function of a pair is expected (Scala 3's parameter untupling)? | **Not now**: a specific error note instead (§7); revisit if `((a, b))` turns out to be common (12 uses today) |
| D95 | Typed parameters | `(x: Nat, y: Nat) => e`; typed and untyped may be **mixed**; `(x y: Nat) => e` **accepted** (mirrors `(x y: Nat) -> B`); separate groups `(x: Nat) (y: Nat) => e` are an error with the fix |
| D96 | What happens to `\x => e`? | **An error, `E-OLD-LAMBDA`, showing the exact new form**; no transition period, one switch commit (as for declarations) |
| D97 | Allow `x y => e` without brackets? | **No**: an error with the fix `(x, y) => e`; so `f x => e` can never silently become a two-parameter lambda |
| D98 | How the parser decides | **Lookahead to the matching `)`** using a matching-bracket table built once per declaration; no cover grammar, no backtracking; `is_pi_binder` uses the same table |
| D99 | How to migrate | A throwaway rewriting tool driven by the old parameter parser, with every file's syntax trees compared before and after (`equivalence::shape`), and every declaration's hash compared; Rust strings, prose and the board by hand |
| D100 | How the printer shows lambdas | `x => body`, with nested lambdas gathered: `(x, y) => body` |

## Sources

- [S1] Scala 3 reference, "Scala 3 Syntax Summary" (`Expr`, `FunParams`, `Bindings`,
  `Binding`, `CaseClause`): <https://docs.scala-lang.org/scala3/reference/syntax.html>
- [S2] Scala 3 book, "Anonymous Functions":
  <https://docs.scala-lang.org/scala3/book/fun-anonymous-functions.html>
- [S3] Scala 3 reference, "Parameter Untupling":
  <https://docs.scala-lang.org/scala3/reference/other-new-features/parameter-untupling.html>
- [S4] Scala 3 reference, "Parameter Untupling - More Details":
  <https://docs.scala-lang.org/scala3/reference/other-new-features/parameter-untupling-spec.html>
- [S5] Scala 3 reference, "Dependent Function Types":
  <https://docs.scala-lang.org/scala3/reference/new-types/dependent-function-types.html>
- [J1] ECMAScript Language Specification, §15.3 "Arrow Function Definitions" (ArrowFunction,
  ArrowParameters, Supplemental Syntax):
  <https://tc39.es/ecma262/multipage/ecmascript-language-functions-and-classes.html#sec-arrow-function-definitions>
- [J2] MDN, "Arrow function expressions" (syntax, line break before arrow, precedence, object
  literals): <https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Functions/Arrow_functions>
- [J3] TypeScript compiler (Go port), `internal/parser/parser.go`,
  `isParenthesizedArrowFunctionExpression`, `nextIsParenthesizedArrowFunctionExpression`,
  `parsePossibleParenthesizedArrowFunctionExpression`, at commit `89d5d5b`:
  <https://github.com/microsoft/typescript-go/blob/main/internal/parser/parser.go>
- [C1] Microsoft Learn, "Lambda expressions and anonymous functions" (C# reference):
  <https://learn.microsoft.com/en-us/dotnet/csharp/language-reference/operators/lambda-expressions>
- [K1] Kotlin docs, "Higher-order functions and lambdas":
  <https://kotlinlang.org/docs/lambdas.html>
- [W1] *The Swift Programming Language*, "Closures" (source of the book):
  <https://github.com/swiftlang/swift-book/blob/main/TSPL.docc/LanguageGuide/Closures.md>
- [L1] Lean Language Reference, "Functions" (terms):
  <https://lean-lang.org/doc/reference/latest/Terms/Functions>
- [L2] Lean Language Reference, "Pattern Matching":
  <https://lean-lang.org/doc/reference/latest/Terms/Pattern-Matching/>
- [H1] Haskell 2010 Report, chapter 3 "Expressions":
  <https://www.haskell.org/onlinereport/haskell2010/haskellch3.html>
- [A1] Agda documentation, "Lambda Abstraction":
  <https://agda.readthedocs.io/en/latest/language/lambda-abstraction.html>
- [I1] Idris 2 documentation, "Types and Functions":
  <https://idris2.readthedocs.io/en/latest/tutorial/typesfuns.html>
- [G1] Gleam language tour, "Anonymous functions":
  <https://tour.gleam.run/functions/anonymous-functions/>
- [G2] Gleam language tour, "Function captures":
  <https://tour.gleam.run/functions/function-captures/>
- [U1] Unison docs, "Lambda syntax":
  <https://unison-lang.org/docs/fundamentals/values-and-functions/_lambda-syntax>
