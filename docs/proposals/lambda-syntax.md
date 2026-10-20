# Lambdas without the backslash (SW-90), draft 2

**Date:** 20 October 2026. **Ticket:** SW-90 (related: SW-19, annotated lambda parameters,
now on `main`; D89 asked for this note). **Decisions:** D92 to D100 (D91 folded in, §4.3).
**Status:** Matt reviewed draft 1 on 20 October 2026 and decided the direction (below). This
draft is the design for that direction; D97's heuristic (§7) and the details of D98 and D99 are
for review. Nothing is implemented.

Claims about Stitchwort are marked **[checked]** when I read or ran the thing named (line
numbers are for `main` at `db3d043`), and **[estimate]** when they are guesses. Claims about
other languages cite [Sources](#sources); anything I couldn't check against an official
source is marked **unverified**.

## Changes since draft 1

Draft 1 recommended Scala/TypeScript lambdas with comma-separated parameter lists,
`(acc, x) => e`. Matt's review (20 October 2026):

1. **Stay in the ML/Lean family; drop the backslash** (D92). Comma lists are rejected: they'd
   be out of step with application, which is `f x y`, and with definition headers, which are
   groups side by side, `def add (x: Nat) (y: Nat)`. Lambdas become `x => e`, `x y => e`,
   `(x: Nat) (y: Nat) => e`, `x (y: Nat) => e`, `_ => e`, with parameter groups exactly as in
   headers (SW-19's `header_param`). Unison is a precedent: `x y -> e`, with application by
   juxtaposition [U1].
2. **`(a, b) => e` keeps today's meaning**: one parameter, a pair taken apart, as
   `\(a, b) => e` is now. D93 (draft 1's "two parameters") is superseded; D94 (Scala-style
   untupling) is moot.
3. **Typed parameters are header groups** (D95): `(x: Nat) (y: Nat) => e` and `(x y: Nat) =>
   e`. No comma lists.
4. **No compatibility path at all** (D96): no `E-OLD-LAMBDA`, no transition. After the switch,
   `\x => e` is an ordinary parse error. (Matt: "WE DO NOT HAVE BACKWARDS COMPAT ISSUES".)
5. **Bare runs are allowed** (D97): `x y => e` without brackets. The risk that a forgotten
   bracket (`map x => x + 1`) parses as a two-parameter lambda is accepted, and mitigated by
   a note and a warning. §7 designs the heuristic and measures how often it fires.
6. **Parsing** (D98) is "a run of parameters, then `=>`", using draft 1's matching-bracket
   table; §5 states it precisely for this form, with its interactions.
7. **Migration** (D99) becomes "delete the `\`", since the meaning is unchanged. §8 checks
   that this is really safe; it is, for every `\` in the repository's `.sw` code.
8. **Printer** (D100): `x y => body`.
9. **Implicit parameters** (D91) are folded in: `[a: Type] (x: a) => x` fits the new form
   (§4.3).

Sections 0, 3 to 10 are rewritten for this. The research (§2) is kept, with its conclusions
(§2.9) updated.

## Contents

0. [The short version](#0-the-short-version)
1. [Lambdas today](#1-lambdas-today)
2. [How other languages write lambdas](#2-how-other-languages-write-lambdas)
3. [The options](#3-the-options)
4. [The syntax](#4-the-syntax)
5. [Parsing it (D98)](#5-parsing-it-d98)
6. [Every place it could be ambiguous](#6-every-place-it-could-be-ambiguous)
7. [Forgotten brackets (D97)](#7-forgotten-brackets-d97)
8. [Migration (D99)](#8-migration-d99)
9. [Risks](#9-risks)
10. [Decisions](#10-decisions)

## 0. The short version

Delete the backslash. Nothing else about lambdas changes:

| Today | New |
|---|---|
| `\x => x + 1` | `x => x + 1` |
| `\acc x => acc + x` | `acc x => acc + x` |
| `\(x: Nat) => x + 1` | `(x: Nat) => x + 1` |
| `\(x: Nat) (y: Nat) => x + y` | `(x: Nat) (y: Nat) => x + y` |
| `\x (y: Nat) => x + y` | `x (y: Nat) => x + y` |
| `\(a, b) => a + b` (one pair, taken apart) | `(a, b) => a + b` (the same) |
| `\{ name, .. } => name` | `{ name, .. } => name` |
| `\_ => 0` | `_ => 0` |
| (not possible today) | `[a: Type] (x: a) => x` (§4.3) |

**The rule:** at the start of an expression, a run of one or more parameters (lower-case
names, `_`, and bracketed groups or patterns) followed by `=>` is a lambda. A lambda's
parameters are written the way a definition's header writes them, and the lambda is applied
the way every function is, `f x y`.

**Parsing** looks along the run, skipping each bracketed group in one step with a table of
matching brackets built once per declaration, and checks for `=>` at its end. No backtracking.
A lambda may appear without brackets only as a whole expression (after `:=`, `=>`, `then`,
`else`, `|>`, an opening bracket, a comma, a record field's `=`, or at the start of a line in a
block), never as an argument or an operand; that's already so today.

**Migration is deleting every `\` token.** All 1,273 `\` tokens in the repository's `.sw`
code sit at the start of an expression (after `(`, `:=`, `=>`, `|>`, `in`, or at the start of
a block line), so no lambda ends up in a position where it would parse differently
**[checked]**. A tool deletes them and confirms each file's syntax trees are unchanged;
elaborated terms and hashes are therefore unchanged too.

**The one new risk** is a forgotten bracket around an argument lambda: `map x => x + 1 xs`
becomes a lambda with parameters `map` and `x`. It's a parse error when the function is
qualified or reached by dot notation (`List.map x => …`, `xs.map x => …`), which is the
common case. When it is a bare name, a warning fires if the lambda's first parameter hides a
function and isn't used; on today's code that would fire 0 times in 223 multi-parameter
lambdas (§7).

## 1. Lambdas today

**[checked]** against `docs/syntax.md` and `crates/syntax/src/parser.rs` at `db3d043`:

- **Form.** `\`, then one or more parameters side by side, then `=>`, then the body
  (`fn lambda`, `parser.rs:1339`). A parameter is a name, `_`, an annotated group `(x: A)` or
  `(x y: A)` (SW-19, read by the definition header's `header_param`,
  `parser/declarations.rs:279`, after `annotated_param_ahead`, `parser.rs:1436`), or a pattern
  starting with `(`, `{`, a constructor or a number: `\x (a, b) => …`, `\{ name, .. } => name`.
- **Patterns.** A lambda with a pattern parameter becomes a lambda over a fresh name
  (`%arg0`) whose body is a one-alternative `match`, which must cover every value.
- **Typed parameters** (SW-19) become `Expr::TypedLam`, one per name; a run of untyped ones is
  one `Expr::Lam`.
- **Where a lambda may start.** Only at the start of an expression (`expr_inline`,
  `parser.rs:1646`) or right after `|>` (`pipe_chain`, `parser.rs:1808`). It isn't an atom, so
  as an argument it needs brackets: `List.map (\x => x + 1) xs`.
- **How far it reaches.** The body is a whole expression, so it extends as far right as it
  can. After `|>`, a lambda takes the rest of the pipeline.
- **`=>` means "the patterns end here, what follows is the result"** in arms, `match`,
  handlers and lambdas; `->` is only the function type (declaration-syntax proposal §2.11).
- **Readings of `(`**: `(x: Nat) -> B` is a function type, found by scanning to the matching
  `)` and looking for `->` (`is_pi_binder`, `parser.rs:1704`); `(x: Nat)` without it is an
  annotation; `(a, b)` is a tuple or tuple type; `(e)` is grouping.
- **Implicit parameters.** When a term is checked against `[a: Type] -> …`, the checker
  introduces the implicit parameter itself, under a hidden name (`check.rs:1211`,
  `bind_hidden`), so `x => x` checks against `[a: Type] -> a -> a`, but its body can't name
  `a`. A lambda can't write `[a: Type]` today.
- **The printer** shows `\x => body`, one parameter at a time (`crates/core/src/pretty.rs:335`).

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
side, and `(a, b)` there means one pair taken apart. Stitchwort stays in the second family,
and with this change joins Unison in having neither a keyword nor a backslash.

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

Two JavaScript pitfalls: `callback || () => {}` is a syntax error ("parentheses are necessary
to avoid `callback || ()` being parsed as the arguments list") [J2], and `() => { foo: 1 }`
returns `undefined` because `{` after `=>` starts a block [J2].

### 2.4 C#

`x => x * x`, `(x, y) => x == y`, `() => …`; types `(int x, string s) => s.Length > x`, and
"input parameter types must be all explicit or all implicit" [C1]. `(_, _) => 42` discards
both [C1].

### 2.5 Kotlin and Swift

Kotlin: "a lambda expression is always surrounded by curly braces",
`{ x: Int, y: Int -> x + y }`; with one parameter it can be left out and called `it`; a pair
is taken apart with brackets, `{ (_, value) -> … }` [K1]. Swift: `{ (parameters) -> return
type in statements }`, with types inferred from context and `$0`, `$1` as short names [W1].
Both put the parameters *inside* the braces, which is how they avoid any ambiguity.

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
Agda: `\ x → x + x` or `λ`, typed `\ (A : Set)(x : A) → x`, implicit `λ {A : Set} (x : A) →
x`, pattern lambdas `λ { true x → x ; false _ → false }` and `λ where`, and the absurd lambda
`λ ()` [A1]. Idris 2: `\x => val`, several parameters with commas, `\x, y, z => val`, types
`\x : Int => x * 2`, patterns `\(x, y) => x + y` [I1].

### 2.8 Gleam and Unison

Gleam keeps a keyword and braces, `fn(x) { … }`, and has a capture shorthand,
`some_function(..., _, ...)` [G1, G2]. Unison: `elem -> elem + 1`; "a lambda with two
arguments is represented by separating the function arguments with spaces"; as an argument
it's in brackets, `List.map (elem -> elem + 1) a`; patterns use `cases`:
`cases (a, b) -> a Nat.+ b` [U1]. Unison has no keyword or backslash and applies functions by
juxtaposition, which makes it the closest precedent for this design. How Unison's parser
finds where a lambda starts I haven't checked (unverified); it uses `->` for both lambdas and
function types, where Stitchwort has two arrows to tell them apart.

### 2.9 What to take from this

1. **The ML family puts parameters side by side**, matching application `f x y`; Stitchwort
   already does, and its definition headers do too. Matt chose to keep that (D92).
2. **Dropping the lambda's leading marker has a precedent in Unison**, and in the mainstream
   family for single names (`x => e`). The cost is that the parser must find the lambda by
   looking ahead to `=>`; Stitchwort's parser has all of a declaration's tokens in a vector,
   so that's direct (§5).
3. **A forgotten bracket around an argument lambda** is the known hazard of marker-free
   lambdas: JavaScript makes `callback || () => {}` an error [J2]. In Stitchwort, a bare-name
   head followed by names and `=>` is a valid lambda, so the error can't always be at parse
   time (§7).

## 3. The options

### Option A: keep `\`

- For: no migration; a lambda always starts with one token.
- Against: `\` looks like noise to people who haven't met Haskell, and needs escaping in Rust
  strings, JSON and Markdown (the board's ticket for SW-19 says `\\(y: Nat)` **[checked]**).

### Option B: ML/Lean family without `\` (Matt's decision, D92)

`x => e`, `x y => e`, `(x: Nat) (y: Nat) => e`, `(a, b) => e` (a pair). Details in §4.

- For: lambdas look like definition headers and like application. Typed lambdas line up with
  function types: `(x: Nat) -> P x` and a value of it, `(x: Nat) => proof`, differ only in the
  arrow. The migration is mechanical and changes no meaning (§8).
- Against: a forgotten bracket can make a bare-name call into a lambda (§7). A lambda
  returning a lambda in an arm reads as a chain of `=>`: `| return x => st => MkPair x st`.

### Option B-comma: Scala/TypeScript lists (draft 1; rejected)

`(acc, x) => e`, with `((a, b)) => e` for a pair. Rejected by Matt: comma lists would be out
of step with `f x y` and with `def add (x: Nat) (y: Nat)`.

### Option C: both, during a transition (rejected)

No backwards-compatibility constraints exist (D96).

### Option D: a keyword, `fun x => e` (not chosen)

Lean, OCaml, F# style. Easy to parse and search for, but longer, and not the style Matt
prefers.

## 4. The syntax

### 4.1 Grammar

```
lambda ::= param+ "=>" expr
param  ::= name | "_"                          -- `x`, `_`
         | "(" name+ ":" type ")"              -- typed, as in a header: `(x: Nat)`, `(x y: Nat)`
         | "[" name+ ":" type "]"              -- implicit (§4.3): `[a: Type]`
         | "[" "auto" name ":" type "]"        -- auto (§4.3)
         | "(" pattern ")" | "(" ")"           -- a pattern in brackets: `(a, b)`, `(MkPair a b)`, `()`
         | "{" record-pattern "}"              -- `{ name, .. }`
```

- **Exactly today's parameters**, minus the `\`. The groups are those of a definition header
  (`header_param`), so `(x y: Nat)` is two parameters of type `Nat`, as in
  `def add (x y: Nat)` (D95). Typed and untyped parameters mix freely: `x (y: Nat) => …`.
- **A pattern parameter is in brackets** (`(a, b)`, `(MkPair a b)`) or a record pattern. Bare
  constructors and numbers, which today's `\` accepts (`\Zero => …`), aren't parameters in the
  new rule: the repository has none **[checked]**, they could never cover their type anyway
  except for one-constructor types, and `(Unit) => …` still works. This keeps the rule simple
  (a run starts only with a lower-case name, `_` or a bracket).
- **List patterns** (`[a, b]`) aren't parameters: a list pattern can't cover `List a`, so it
  would be refused anyway, and `[` is kept for implicit groups. `([a, b]) => …` is still
  accepted by the bracketed-pattern rule, and refused by the coverage check as today.
- **`(a, b) => e` is one pair**, as today. Several parameters are curried: `x y => e` is
  `x => y => e`, the same `Expr::Lam(["x", "y"], …)` as `\x y => e`.
- **The body** is an expression and reaches as far right as possible, as today. `{` after
  `=>` is a record literal, never a block, so JavaScript's `() => { foo: 1 }` trap doesn't
  arise.

### 4.2 Where a lambda may appear without brackets

Only as a **whole expression** in its position, exactly where `\` lambdas may appear today:
after `:=`, `=>` (arms, alternatives, handlers, another lambda), `then`, `else`, `|>`, `(`,
`,` (tuples, lists), a record field's `=`, a named argument's `:=` (`f [x := y => y]`), `in`
(`rewrite … in`), and at the start of a line in a block. Never as an application argument
(`f (x => e)` needs its brackets), and never as an operand (`a || (x => e)`).

### 4.3 Implicit parameters (D91, folded in)

`[a: Type] (x: a) => x` fits the form with no extra rules: a `[ name+ :` group is a parameter,
read by `header_param` as in `def id [a: Type] (x: a): a := x`, and `[auto h: P]` likewise. The
lookahead already exists (`is_implicit_binder`, `parser.rs:1671`), and the run rule in §5
tells `[a: Type] (x: a) => x` from the function type `[a: Type] -> a -> a` by what follows
the run.

What it needs beyond the parser **[estimate]**: an implicit flag on `Expr::TypedLam` (or a
sibling node); checking it against `[a: Type] -> …` binds `a` by name instead of the hidden
name used today (`check.rs:1211`); inferring it gives an implicit function type. It isn't
needed by the migration (no code writes it today), so it can be a small follow-up ticket after
the switch, or part of the same lane if it's cheap. Until then, `[a: Type] … =>` is a parse
error naming the follow-up.

## 5. Parsing it (D98)

### 5.1 The rule

At a **lambda position**, which is the start of an expression (`expr_inline`) or right after
`|>` (`pipe_chain`), the parser scans forward from the current token:

1. A **parameter token** is a lower-case name; `_`; `(`; `{`; or `[` when followed by
   `name+ :` or `auto name :` (an implicit group). For `(`, `{` and `[`, the scan jumps to the
   matching closing bracket in one step.
2. It repeats while the next token is a parameter token on the same logical line (not at or
   left of the enclosing block's column, the "stop" rule `at_pipe` uses, `parser.rs:1778`).
3. If at least one parameter was scanned and the token after the run is `=>`, this is a
   lambda. Otherwise nothing has been consumed, and the expression is parsed as before.

Once it has decided, the parser reads the parameters with today's code (`fn lambda` without
the `\`: names, `header_param` for typed groups, `pattern` for the rest), then `=>`, then the
body. No re-reading and no backtracking.

Why this never changes the meaning of an expression that's valid today: a `=>` right after a
complete expression is always a parse error today. **[checked]** with the built compiler:
`:= n => n` gives "expected the end of the declaration, but found `=>`", and so do `| x =>
Nat.succ x => 1` in an arm and `List.map x => x xs`. Patterns before `=>` in arms, `match` and
handlers are read by the pattern parser, which never consults this rule.

### 5.2 The matching-bracket table

Scanning from every `(` to its partner would be slow on deeply nested brackets: the benchmark
`check-nested-parens` parses `((…(0)…))` 12,000 deep (`crates/bench/src/programs.rs`
**[checked]**), and a naive scan from every bracket would be over 100 million token steps
**[estimate]**. Instead, the parser builds a table from each opening bracket (`(`, `[`, `{`)
to the index of its partner once per declaration, in one pass with a stack (a `Vec<u32>` the
size of the token vector). Each jump is one lookup.

**Cost of the scan.** It stops at the first token that isn't a parameter token, and jumps over
brackets, so at each lambda position it costs the length of the leading run of names and
groups. An application's arguments aren't lambda positions (they're atoms), so a long
`f a b c …` is scanned once, from its start. Total work is linear in the declaration's tokens
**[estimate]**. The table lives on the parser, not the call stack, so the nesting limits
(measured in stack) don't move. `is_pi_binder` should use the table too.

### 5.3 Why not a cover grammar

JavaScript parses `( … )` as an expression and re-reads it as parameters when `=>` appears
[J1]. Here, `{ name, .. }`, `(-1)`, `[a: Type]` and typed groups have no expression reading,
so a cover grammar would need a third kind of syntax tree. TypeScript's speculative parse
[J3] needs save, rewind and a failure cache. With every token already lexed, the scan in §5.1
is simpler.

### 5.4 Size of the change

**[estimate]**, one lane: the scan and table (about 80 lines), `lambda` called without the
`\` (a few lines), the lexer's `\` token removed (so `\` becomes "unexpected character"), the
parse-error notes and the warning in §7 (about 120 lines across parser and elaborator), the
printer, and 30 or so tests. The syntax tree, kernel and JS back end don't change.

## 6. Every place it could be ambiguous

### 6.1 Arms, `match` and handlers

`| p => e`: the pattern parser reads `p` and stops at `=>`; the lambda rule is never asked.
A lambda in an arm's result follows the first `=>`:

```
handle prog() with
  | return x => st => MkPair x st
  | get(), k => st => k st st
```

One-line `match n with | Zero => x => x | Succ k => f k`: the lambda body `x` stops at `|`,
as today. `| Nil => f x | …`: the scan sees `f x` then `|`, so not a lambda.

### 6.2 `(x: T) => e` against `(e: T)` and `(x: T) -> B`

The run rule decides by the token after the run: `(x: Nat) => …` is a lambda,
`(x: Nat) -> B` a function type (the scan stops at `->`, then `is_pi_binder` applies), and
`(x: Nat)` alone an annotation. A function and its type look alike, which I think is a
feature:

```
def twice: (n: Nat) -> Nat := (n: Nat) => n + n
```

### 6.3 Tuples and tuple patterns

`(a, b) => e` takes one pair; `(a, b)` elsewhere is a tuple; `(a, b) -> T` a function type.
`acc (k, v) => e` takes two arguments, the second a pair. All as today.

### 6.4 `|>`

`pipe_chain` applies the same rule. `xs |> ys => List.append ys [0] |> List.sum` keeps today's
meaning: the lambda takes the rest of the pipeline.

### 6.5 Application and operators

`f x => e` at the start of an expression is a lambda with parameters `f` and `x`. That is the
accepted risk of D97, handled in §7. Inside an application it can't arise (arguments are
atoms), and after an operator (`a + x => e`, `a || x => e`) the operand isn't a lambda position,
so it's a parse error at `=>`, as today.

### 6.6 `if`, `let`, blocks, records, sections, `calc`

- `if c then x => a else y => b`: each branch is a lambda position; the body stops at `else`
  as today. `if c then f x else g` isn't a lambda (the run ends at `else`).
- `let f := x y => x + y` is a lambda; `let (a, b) := e` is a `let` pattern (it uses `:=`).
- A block line `i hi => …` is a lambda (two such lines exist in `aoc/src/day02/part2proof.sw`
  and `examples/accept/abilities-edge.sw` after deletion). A block line starting `f x` and
  continuing with something other than `=>` is an ordinary statement.
- Records: `{ name, .. } => name` is a lambda; `{ x = 0 }` without `=>` is a record literal;
  `{ f = x => x + 1 }` has a lambda as a field value.
- Method sections start with `.`, which isn't a parameter token: `.name` is never a lambda
  parameter, and `xs.map x => …` is a parse error (§7).
- `calc` steps are `_ = …`, `_ <= …`, `_ < …`; `_ =>` is a different token, so `_ => e` (a
  lambda ignoring its argument) can't be confused with a step.

### 6.7 Layout

The run must be on one logical line with its `=>`: a `=>` that starts a continuation line
(indented further) counts, one at or left of the block's column starts a new statement, as for
any operator. The body may start on the next line, as today.

### 6.8 Unclosed brackets

`(a, b => e` has no matching `)`, so the scan doesn't see a lambda, and the tuple parse fails
at `=>` with "expected `)`".

## 7. Forgotten brackets (D97)

### 7.1 When it's a parse error, and when it isn't

The mistake is writing an argument lambda without its brackets: `List.map x => x + 1` for
`List.map (x => x + 1)`. Whether the parser catches it depends on the **head** of the
expression (its first token):

- **A qualified name, dot notation, a constructor, a literal or `(`-expression followed by
  something that isn't a run:** not a lambda by §5.1, so it's a parse error at `=>`. The
  message gets a note: "to pass a lambda as an argument, put it in brackets: `List.map (x =>
  …)`". This covers `List.map x => …`, `xs.map x => …`, `J x => …`, `Eq.cong y => …`.
- **A bare lower-case name** (`map x => x + 1`, `go acc x => …`, `allResults u => …`): a valid
  lambda whose first parameter is the function's name.

How often is the head a bare name? Of the 1,201 lambdas in `.sw` code written as `(\`, the
token just before the bracket is a qualified name or dot access 616 times, a constructor 120,
a bare lower-case name 124, and a closing bracket, literal or other token the rest
**[checked]** (a script over the `.sw` files, with strings and comments removed). So roughly
half of today's argument lambdas follow a qualified or dotted function, where a forgotten
bracket is a parse error, and about a tenth follow a bare name. (For the 292 preceded by a
closing bracket, the head of the application wasn't measured.)

### 7.2 The heuristic for the silent case

A forgotten bracket at a bare-name head produces a lambda whose **first parameter has the
same name as a function in scope**, and that parameter is almost never used in the body (it
was meant to be the function being called). Proposed:

- **Warning `W-LAMBDA-SHADOW`** when all of these hold:
  1. the lambda has two or more parameters, the first a plain name (not `_`, not a group);
  2. that name, in the scope around the lambda, refers to a function: a top-level definition,
     an import, an ability operation, or a local variable whose type is a function type;
  3. the first parameter isn't used in the body.

  Message: "this lambda's first parameter `map` hides the function `map`, and isn't used";
  note: "if you meant to pass a lambda to `map`, put it in brackets: `map (x => …)`; to keep
  the parameter, rename it or write `_`".
- **A note on errors.** When conditions 1 and 2 hold (whether or not 3 does) and an error is
  reported inside the lambda or at it (for example "this is a function, but the expected type
  is `List Nat`", or the body's `x + 1 xs` failing), the error gets the same note.

**How often it fires.** Over today's `.sw` code (223 lambdas with two or more parameters;
scope approximated as the same file's top-level definitions and its `import`s, not local
function-typed variables) **[checked]**:

| Condition | Lambdas |
|---|---|
| 1: two or more parameters, first a name | 223 |
| 1 and 2: the first parameter names a function in the file | 1 (`\r acc =>` in `examples/accept/expected-types.sw`) |
| 1 and 3: the first parameter is unused | 8 |
| 1, 2 and 3: **the warning** | **0** |

So on correct code the warning would never have fired, and the error note could only appear
on one lambda, and only if it had an error. For the mistake it targets (`map x => x + 1`),
all three conditions hold. **[estimate]**: it misses the case where the forgotten function's
name is *used* in the body by coincidence, or where the function is in scope only as a local
not of function type; I expect both to be rare.

The warning is the elaborator's (it needs scope and use); the parser needs nothing new for
it, since every lambda is now a run.

## 8. Migration (D99)

### 8.1 How many lambdas

Counted with a regular expression for `\` followed by parameters and `=>` on one line, over the
files git tracks at `db3d043` **[checked]**; approximate (it misses a `=>` on another line, and
in Rust it counts lambdas inside test strings):

| Where | Lambdas | Files |
|---|---|---|
| Library (`crates/elab/src/std`, `.sw`) | 552 | 9 |
| Advent of Code (`aoc/`, `.sw`) | 447 | 8 |
| `examples/` (`.sw`) | 290 | 80 |
| Rust test and benchmark sources (syntax 78, driver 51, elab 31, core 18, bench 13, cli 7, js 4, web 3) | 205 | 42 |
| Docs (`docs/proposals` 162, `syntax.md` 46, `aoc-2025.md` 31, others 20, `DESIGN.md` 8) | 267 | 18 |
| `board/tickets.json` | 15 | 1 |
| Playground examples (`web/index.html`) | 6 | 1 |
| Editor grammars (`editors/`) | 0 | 0 |
| **Total** | **about 1,780** | |

By kind: 1,319 one plain name, 350 several names, 69 with a pattern, 44 with a typed group.
In `.sw` code alone (strings and comments removed) there are **1,273 `\` tokens**. 29 snapshot
files (`crates/cli/tests/snapshots/*.snap`) show lambdas in quoted source or printed terms;
they're regenerated, not edited.

### 8.2 Is "delete the `\`" safe?

The meaning of every parameter list is unchanged, so the question is only whether each lambda,
without its `\`, is still found as a lambda in the same place. It is, if every `\` is at a
lambda position (§5.1). **[checked]** with a script over the `.sw` files (strings and comments
removed), the token before each of the 1,273 `\` is:

| Before the `\` | Count |
|---|---|
| `(` | 1,201 |
| `:=` | 37 |
| `=>` | 21 |
| `|>` | 7 |
| `((` (a bracket right after another) | 3 |
| `in` (`rewrite … in`) | 2 |
| start of a block line (after a `let`) | 2 |

All are lambda positions. **No `\` follows an argument or operand** (an unbracketed argument
lambda, `f \x => e`, is a parse error today, so there are none to worry about). And every
parameter list starts with a lower-case name, `_`, `(` or `{` (17 start with `(`, 1 with `{`,
1 with `_`, none with a constructor or number), so all are runs by §5.1.

**The tool** (throwaway, like the declaration converter was):

1. For each `.sw` file, lex with today's lexer and delete the text of every `\` token (the
   lexer, not a text search, so `\n` and `\u{…}` inside text and character literals are never
   touched).
2. Parse the old text with the old parser and the new text with the new parser, and compare
   the syntax trees without positions (`crates/syntax/src/equivalence.rs`, `shape`, built for
   the declaration switch). Any difference stops the tool on that file. Given §8.2's survey
   none is expected, so this is the safety net, not the plan.
3. Compare every declaration's content hash before and after across the library, `aoc/` and
   `examples/`: a definition's hash covers its elaborated type and body, not names or
   positions (`docs/core.md`, "Tests and content hashes" **[checked]**), so it must be
   identical.

**Not by the tool:** Rust test strings (a Stitchwort lambda in a normal Rust string is `\\x`, and
`\\n` there may be a Stitchwort escape, so these are edited by a reviewed search for `\\`
followed by parameters and `=>`, then the tests are run: a missed one is now an "unexpected
character" error and fails loudly, except in tests that expect a parse error, which get a
look each); the docs' code blocks and inline code (search and replace, reviewed; historical
documents such as `docs/history.md` and the declaration-syntax proposal keep the old form
where they describe it); the board's tickets (left as written, since they record history; the
open ones that quote syntax are edited by hand); the playground's six.

### 8.3 Printer, editors, playground

- **Printer** (`crates/core/src/pretty.rs:335`): `x y => body`, gathering nested lambdas into
  one run (D100). Snapshots change with it.
- **VS Code grammar** (`editors/vscode/syntaxes/stitchwort.tmLanguage.json`): `=>` is already
  an operator; `\` can be dropped from its operator character class. No new rule is needed.
- **Playground highlighter** (`web/index.html`): no change; its six example lambdas are
  rewritten.
- **Docs**: `docs/syntax.md` (the expression table, "Patterns in `let` and lambdas", pipes,
  method sections, the SW-19 annotation hint), DESIGN.md §4, and a pointer from the
  declaration-syntax proposal's §2.11.

### 8.4 Order of work

One lane: the scan and table, `\` removed from the lexer, the printer, the tool run and the
hand edits, hashes compared, all in one commit (as the declaration switch was). Then the
warning and notes of §7 (same lane or straight after). Implicit lambda parameters (§4.3) as a
small follow-up.

## 9. Risks

- **Forgotten brackets at a bare-name head** (§7). Mitigated, not removed; the measurement
  says the warning is quiet on correct code.
- **Readers from TypeScript or Scala** may write `(acc, x) => …` expecting two parameters; it
  takes a pair. When such a lambda is checked against a function whose first parameter isn't
  a pair, the type error gets a note: "`(acc, x)` is one pair; for two parameters write `acc x
  => …`" **[estimate]**: cheap, since the elaborator knows the pattern came from a lambda.
- **A lambda returning a lambda** in an arm reads as a chain of `=>`; brackets help where it
  matters: `| return x => (st => MkPair x st)`.
- **Unverified:** how Unison's parser finds lambdas, and whether it has the same
  forgotten-bracket issue.

## 10. Decisions

| ID | Question | Answer |
|---|---|---|
| D91 | Implicit lambda parameters `[a: Type]` | **Folded in** (§4.3): the syntax `[a: Type] (x: a) => x` falls out of the run rule; the elaborator part is a small follow-up (recommended), not needed for the switch |
| D92 | Which lambda syntax? | **Decided (Matt)**: ML/Lean family without `\`: `x => e`, `x y => e`, `(x: Nat) (y: Nat) => e` |
| D93 | What does `(a, b) => e` mean? | **Superseded**: one pair parameter, as today |
| D94 | Scala-style untupling | **Moot** |
| D95 | Typed parameters | **Decided (Matt)**: header groups, `(x: Nat) (y: Nat)`, `(x y: Nat)`, mixed with untyped |
| D96 | What happens to `\x => e`? | **Decided (Matt)**: nothing special; `\` is removed from the lexer, so it's an ordinary "unexpected character" error |
| D97 | Bare runs `x y => e` | **Decided (Matt)**: allowed. Open for review: the mitigation in §7.2, `W-LAMBDA-SHADOW` plus a note on errors (recommended as written) |
| D98 | How the parser decides | **Decided (Matt)**: a run of parameter tokens, then `=>`, with the matching-bracket table. Open for review: the precise rule in §5.1 (recommended as written, including: no bare constructors or numbers as parameters, `[` only for implicit groups) |
| D99 | How to migrate | **Decided (Matt)**: the tool. Open for review: §8.2, deleting `\` tokens by lexing, checking syntax trees and hashes; Rust strings and docs by reviewed search (recommended as written) |
| D100 | How the printer shows lambdas | **Decided (Matt)**: `x y => body` |

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
