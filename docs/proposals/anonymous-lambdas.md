# Lambdas that don't name their argument: `bookings.find (.id == id)`?

**Status:** design note, 25 October 2026. Nothing is implemented. The
decisions are D1192–D1196 (§9). The counts are in §5 and the appendix.

## 1. The short answer

The motivating code:

```
def bookingAt (bookings: List Booking) (time: Float): Option Booking :=
  bookings.find (booking => overlaps booking time)

def findBooking (id: Text) (bookings: List Booking): Option Booking :=
  bookings.find (booking => booking.id == id)
```

The wish is something like `bookings.find (_.id == id)`.

**The recommendation: make a section reach to the end of its expression,
and add Haskell-style operator sections.** No `_`, `it` or `$0`.

```
def bookingAt (bookings: List Booking) (time: Float): Option Booking :=
  bookings.find (overlaps (time := time))        -- works today (§2.2)

def findBooking (id: Text) (bookings: List Booking): Option Booking :=
  bookings.find (.id == id)                      -- new: the section reaches past `==`
```

Plus `line.toList.findIndex (== 'S')` for the `c => c == 'S'` lambdas that AoC
has.

The reasons, in brief:

- `.id` already means `x => x.id` (method sections, D505/D506). `(.id == id)`
  is the same idea taken one step further: leave out the value at the *start*
  of the expression. Nothing new to learn, and no new character.
- The other designs all need an answer to "where does the function end?".
  Scala's answer is a known source of bugs (§3.1). Lean's answer (the nearest
  brackets) is fine, but the obvious ASCII marker, `_`, is already the hole
  Stitchwort's proofs use about 300 times (§4.2).
- Measured over the repository (§5), the shapes these two rules cover
  (`x.f … op e` and `x op e`) are the main gap left after what sections, named
  arguments and plain partial application already cover. A general
  placeholder would add the rest: 279 single-use lambdas of other shapes, 212
  of them in the standard library, mostly in proofs.

Today `(.id == id)` is a type error (checked, §2.1), so the change gives
meaning to code that has none now.

## 2. What Stitchwort has today

### 2.1 Method sections (D505, D506)

`.f args` is `x => x.f args` ([syntax.md, Method sections](../syntax.md#method-sections);
[method-sections.md](method-sections.md)). `xs.map .name`, `|> .count .isZero`,
`ls.map (.split ',')`. As an argument a section takes no arguments of its own
(`.count .isZero` is `.count` applied to `.isZero`). After `|>` it's rewritten
to the dot call itself (`xs |> .drop 1` is `xs.drop 1`). Where the receiver is
the function's last explicit parameter it's the partial application
(`.isZero` is exactly `Dial.isZero`), so proofs that restate the program still
match (D506).

A section is parsed as a lambda whose parameter is the hidden name `%section`
(`section_start` and the `Expr::Lam` built after it in
`crates/syntax/src/parser.rs`; `SECTION` in `crates/syntax/src/ast.rs`).

What a section does **not** do today: carry on past an operator. Checked
with `target/release/stitchwort` built from `main` on 25 October:

```
bookings.find (.id == id)

[E-TYPE-MISMATCH] Error: type mismatch
 4 │   bookings.find (.id == id)
   │                  ─┬─    ─┬
   │                   ╰───────── this is a function, but the expected type is `Text`
   │                          ╰── this comparison is on `Text` because of this
```

`_.id` is a hole followed by a field access (SW-266). The error's note is
wrong advice for this case, since it suggests `.id`, which doesn't compile
here:

```
bookings.find (_.id == id)

[E-CANNOT-INFER] Error: can't tell what the value is, so can't look up `.id`
   │                    ╰─── `_` is a hole for the compiler to fill in, not a parameter
   │ Note: to pass the function `x => x.id`, write the method section `.id`, as in `xs.map .id`
```

(The message is in `find` in `crates/elab/src/dot.rs`; the example is
`examples/reject/section-underscore.sw`.)

### 2.2 Leaving out parameters by naming the others (SW-399, SW-404)

`f (x := e)` leaves out the explicit parameters before `x` and makes a
function of them ([syntax.md, Named arguments](../syntax.md#named-arguments)).
So Matt's first line already has a short form, **checked** on the same build
(`Booking` with `Float` fields and `overlaps (booking: Booking) (time: Float): Bool`):

```
bookings.find (overlaps (time := time))     -- checks
```

Moving `overlaps` into `Booking`'s namespace gives the section form too:
`def Booking.overlaps (booking: Booking) (time: Float)`, then
`bookings.find (.overlaps time)`. That works under today's dot rule and
under rule E.

### 2.3 Partial application, operators, lambdas

- Functions are curried, so `(c => charAt line c)` is just `charAt line`
  ([guide ch. 4](../guide/04-functions.md)).
- There are **no operator sections**: `(== 'S')` is
  `E-PARSE: expected an expression, but found ==` (checked).
- Lambdas are `x => e`, `x y => e`, `_ => e`, with typed groups
  `(x: Nat)`, implicit groups `[a: Type]` (SW-170) and patterns in brackets,
  `(a, b) => …`, `{ name, .. } => …` ([lambda-syntax.md §4](lambda-syntax.md)).
  There's no `\case`: `x => match x with …` is the spelling
  ([syntax-conveniences.md](syntax-conveniences.md), "multi-alternative pattern
  lambdas").
- `$` and `#` aren't tokens outside text (`$` only starts `${` in
  interpolation; `$0` is "unexpected character `$`", checked). `@` starts
  attributes, `?` is a goal, `%` is remainder.

### 2.4 Rule E (D303, being built)

Under rule E, `x.f a` is `T.f x a` (the receiver is the first explicit
parameter) and `x |> g a` is `g x a`. Sections follow the dot, so `.f a` is
`x => T.f x a` ([dot-receiver.md §4 E](dot-receiver.md)). Two consequences
here:

- Every lambda of the shape `t => Int.mul t c` becomes the section
  `.mul c`, because `t` is the first argument. The repository has about 100
  of these (§5).
- Value *first* is handled by sections, and value *later* by plain partial
  application (`seen.contains` is `Set.contains seen`, a function waiting for
  the element) or by named arguments (`overlaps (time := time)`). What's left
  is mainly operators: `x == 'S'`, `x.id == id`.

## 3. What other languages do

Every design answers two questions:

1. **Where does the function end?** (Its *boundary*.)
2. **How is the missing value marked?** (Its *marker*.)

| Language | Marker | Boundary | Several uses | Nesting |
|---|---|---|---|---|
| Scala | `_` | smallest enclosing expression that properly contains it | each `_` is a new parameter | inner expressions bind their own |
| Lean 4 | `·` (or `.`) | the surrounding brackets | each `·` is a new parameter | inner brackets make their own function |
| Kotlin, Groovy | `it` | the lambda's braces `{ }` | same parameter every time | inner `it` is the inner lambda's |
| Swift | `$0`, `$1` | the closure's braces `{ }` | numbered, reused freely | inner closure's own |
| Elixir | `&1`, `&2` | `&( … )` | numbered | not stated in the docs |
| Clojure | `%`, `%1`, `%&` | `#( … )` | numbered | **not allowed** |
| Raku | `*` | the surrounding expression, with exceptions | each `*` a new parameter | |
| Gleam, Koka | `_` | the one call it's an argument of | one | |
| F# 8 | `_.` | one "atomic" expression | one | |
| Haskell, Idris | none | the brackets of an operator section `(+ 1)` | one | |
| Swift key paths, Haskell `(.field)` | none | the leading `\.` / `.` | one | |
| **Stitchwort today** | none | the section `.f args` | one | |
| C#, JS/TS, Rust, OCaml, Roc | none (write a lambda) | | | |

### 3.1 Scala: `_`

The rule: "An expression e of syntactic category Expr binds an underscore
section u, if … (1) e properly contains u, and (2) there is no other
expression of syntactic category Expr which is properly contained in e" and
also contains u. The spec's examples: `_ + 1` is `x => x + 1`, `_ * _` is
`(x1, x2) => x1 * x2`, `_.map(_ + 1)` is `x => x.map(y => y + 1)`
([Scala 2.13 spec §6.23](https://scala-lang.org/files/archive/spec/2.13/06-expressions.html#placeholder-syntax-for-anonymous-functions)).
The Scala 3 book states the practical rule as: "use the `_` symbol instead of
a variable name when the parameter appears only once"
([Scala 3 book, anonymous functions](https://docs.scala-lang.org/scala3/book/fun-anonymous-functions.html)).

- **Several uses:** each `_` is a *new* parameter, so `_ + _` takes two.
- **Nesting / the pitfall:** `f(_.str)` is `f(x => x.str)`, not
  `x => f(x.str)`, and `if _.str.length > 3 then …` puts the lambda inside the
  comparison; the reply on the Scala forum: "`_` always expands in its
  enclosing scope"
  ([Scala users, "placeholder inference often breaks in simple scenarios"](https://users.scala-lang.org/t/placeholder-inference-often-breaks-in-simple-scenarios/10761)).
- **Types:** the lambda takes its parameter type from the expected type; when
  the expansion lands somewhere unexpected the error is "Missing parameter
  type" (same thread).
- **Complaints:** in the Rust discussion of copying it, one participant called
  it "arguably one of the worst mistakes of that language", and another said
  the scoping rule "is as clear as mud"
  ([Rust internals, "Placeholder Syntax - Revisited"](https://internals.rust-lang.org/t/placeholder-syntax-revisited/18190)).
- **Scala 3** keeps the rule but moves `_`'s *other* meanings away from it:
  wildcard types become `?` ("The syntax of wildcard arguments in types is
  changing from `_` to `?`",
  [Scala 3, wildcards](https://docs.scala-lang.org/scala3/reference/changed-features/wildcards.html)),
  and "The syntax `m _` is no longer needed and will be deprecated"
  ([Scala 3, eta expansion](https://docs.scala-lang.org/scala3/reference/changed-features/eta-expansion.html)).

### 3.2 Kotlin and Groovy: `it`

Kotlin: "If the compiler can parse the signature without any parameters, the
parameter does not need to be declared and `->` can be omitted. The parameter
will be implicitly declared under the name `it`": `ints.filter { it > 0 }`
([Kotlin, lambdas](https://kotlinlang.org/docs/lambdas.html#it-implicit-name-of-a-single-parameter)).
One parameter only; its type comes from the expected function type; `it` is
an ordinary name, so it can be used any number of times. The boundary is the
braces of a lambda, which Kotlin always writes.

Complaint: nesting. The official conventions say "In lambdas which are short
and not nested, it's recommended to use the `it` convention … In nested
lambdas with parameters, always declare parameters explicitly"
([Kotlin coding conventions](https://kotlinlang.org/docs/coding-conventions.html)),
and a static-analysis rule warns that a reader loses track of which value is
meant "especially when dealing with nested functions"
([Klocwork KT.EXPLICIT_IT_LAMBDA_PARAMETER](https://help.klocwork.com/2024/en-us/reference/kt.explicit_it_lambda_parameter.htm)).

Groovy: a closure without an explicit parameter list "always defines an
implicit parameter, named `it`"; `{ -> 42 }` declares none
([Groovy, closures](https://groovy-lang.org/closures.html)).

### 3.3 Swift: `$0` and key paths

"The type of the shorthand argument names is inferred from the expected
function type", and "the highest numbered shorthand argument you use
determines the number of arguments that the closure takes"
([Swift book, Closures](https://raw.githubusercontent.com/swiftlang/swift-book/main/TSPL.docc/LanguageGuide/Closures.md)).
The boundary is the closure's braces `{ $0.email }`. Swift also accepts a bare
operator where a function is expected: `names.sorted(by: >)` (same page).

Key paths (SE-0249): `users.map(\.email)` stands for `users.map { $0[keyPath: \User.email] }`;
it works for key path *literals* only, where a `(Root) -> Value` function is
expected
([SE-0249](https://github.com/apple/swift-evolution/blob/main/proposals/0249-key-path-literal-function-expressions.md)).
This is the same shape as a Stitchwort section.

Complaint found: an early Swift Evolution thread on `$0` meaning either the
first argument or the tuple of all of them
([swift-evolution, "Make $0 always refer to a closure's first argument"](https://forums.swift.org/t/proposal-make-0-always-refer-to-a-closure-s-first-argument/1140)).
I found no official style rule against `$0`.

### 3.4 Elixir `&(&1 …)`, Clojure `#(… % …)`

Elixir: `&(&1 * 2)` is `fn x -> x * 2 end`, `&Enum.take(&1, 5)` partially
applies, `&(&1 + &2 + &3)` takes three; the body "must contain at least
`&1`", and blocks aren't allowed
([Elixir, Kernel.SpecialForms `&`](https://elixir.hexdocs.pm/Kernel.SpecialForms.html)).
The `&( )` is the explicit boundary.

Clojure: `#( )` with `%` (= `%1`), `%n`, `%&`; "#() forms cannot be nested";
meant for "very short one-off mapping/filter fns"
([Clojure reader](https://clojure.org/reference/reader)).

Both use an explicit marker on the *outside* so the boundary is never in
doubt, and numbered markers so several uses are clear.

### 3.5 Raku: the Whatever star

A `*` in an expression makes the whole surrounding expression a closure:
`4 * * + 5` is `-> $x { 4 * $x + 5 }`, `*.uc` calls a method, and `* + *`
takes two arguments. There are exceptions where `*` stays a plain value
(`1, *, 2`; ranges `1 .. *`; `$x = *`; `1 xx *`), and a star stored in a
variable isn't turned into a closure
([Raku, Whatever](https://docs.raku.org/type/Whatever)). The exceptions list
is the complaint: the reader must know which operators "curry".

### 3.6 Gleam and Koka: `_` in one call

Gleam: `fn(a) { some_function(..., a, ...) }` "can be written as
`some_function(..., _, ...)`", "a shorthand syntax for creating anonymous
functions that take one argument"
([Gleam tour, function captures](https://tour.gleam.run/functions/function-captures/)).
The boundary is the call the `_` is a direct argument of.

Koka 3.2.0 (17 July 2025): "underscore is now used to automatically
eta-expand arguments", e.g. `[1].map(inc(_))`
([Koka book, news](https://koka-lang.github.io/koka/doc/book.html)). I didn't
find its exact scope rule.

The TC39 partial-application proposal (Stage 1) is the same idea:
`f~(?, x)`, with `?` allowed only "at the top level of the argument list", so
`f~(x + ?)` is invalid
([proposal-partial-application](https://github.com/tc39/proposal-partial-application)).
It marks the call with `~` as well, so the reader sees that it's partial.

### 3.7 Lean 4: `·` in brackets

The parser's doc comment: "A placeholder for an implicit lambda abstraction's
variable. The lambda abstraction is scoped to the surrounding parentheses.
For example, `(· + ·)` is equivalent to `fun x y => x + y`. Tuple notation and
type ascription notation also serve as scopes." It's declared as
`unicodeSymbol "·" "."`, so `.` is accepted as the ASCII spelling
([Lean source, `Parser/Term.lean`, `cdot`](https://github.com/leanprover/lean4/blob/master/src/Lean/Parser/Term.lean)).
Nesting: `(h (· + 1) ·)` is `fun x => h (fun y => y + 1) x`
([Lean reference, Functions](https://lean-lang.org/doc/reference/latest/Terms/Functions/)).
Lean's form of the request would be `(·.id == id)`. That follows from the rule
and Lean's dot notation, but I haven't run it in Lean.

- **Several uses:** each `·` is a new parameter (as in Scala).
- **Types:** the made function is an ordinary `fun`, checked against what's
  expected.
- **Pitfall:** the same as Scala's, but visible: `(f (g ·))` makes the
  function at the *inner* brackets.

### 3.8 Haskell, Agda, Idris: operator sections

Haskell 2010: `(op e) = \x -> x op e` and `(e op) = \x -> e op x`, but
"(- exp) is not a section, but an application of prefix negation"; the
Prelude's `subtract` stands in for the missing section
([Haskell 2010 report §3.5](https://www.haskell.org/onlinereport/haskell2010/haskellch3.html)).
`\case { p1 -> e1; … }` is `\fresh -> case fresh of { … }`
([GHC, LambdaCase](https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/lambda_case.html)).
With OverloadedRecordDot, `(.b) a` is `a.b`, for fields only
([GHC, OverloadedRecordDot](https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/overloaded_record_dot.html)).
Haskell has no general placeholder.

Agda writes operators with their holes in the name (`_+_`, `if_then_else_`),
so sections fall out: you can use "other *sections* of the full name, for
instance leaving one or two underscores"
([Agda, mixfix operators](https://agda.readthedocs.io/en/latest/language/mixfix-operators.html)).

Idris: "`\x => val` constructs an anonymous function", and "`(*2)` is
shorthand for a function which multiplies a number by 2", with `(2*)` the
other way round
([Idris tutorial, types and functions](https://docs.idris-lang.org/en/latest/tutorial/typesfuns.html)).

The boundary is the brackets, and the operator says where the value goes.
There's no scope question.

### 3.9 F# 8: `_.Name`

`_.Name` replaces `(fun x -> x.Name)`, restricted to an atomic expression
("an expression which has no whitespace unless enclosed in method call
parentheses"), and it can't be mixed with a `_` discard in the same scope
(warning FS3570)
([Announcing F# 8](https://devblogs.microsoft.com/dotnet/announcing-fsharp-8)).
That's Stitchwort's `.name` with an extra `_`.

### 3.10 Languages without one

- **C#:** lambdas only. `(_, _) => 42` discards; "if only a single input
  parameter is named `_`, the compiler treats `_` as the name of that
  parameter" for backwards compatibility
  ([C# lambda expressions](https://learn.microsoft.com/en-us/dotnet/csharp/language-reference/operators/lambda-expressions)).
- **JS/TS:** `param => expression` only
  ([MDN, arrow functions](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Functions/Arrow_functions)).
- **Rust:** `|x| x.name`; the placeholder proposal above drew the objections
  quoted in §3.1 and "This one *definitely* doesn't seem worth it, since it's
  not even shorter"
  ([Rust internals](https://internals.rust-lang.org/t/placeholder-syntax-revisited/18190)).
- **OCaml:** `fun p1 … pn -> e` and `function p1 -> e1 | …` only
  ([OCaml manual, expressions](https://ocaml.org/manual/5.2/expr.html)).
- **Roc:** `|args| …`; the tutorial describes no placeholder
  ([Roc tutorial](https://github.com/roc-lang/roc/blob/main/docs/mini-tutorial-new-compiler.md)).

### 3.11 The JS pipeline "topic token"

Hack-style pipes write the value's place explicitly: `value |> foo(%) + 1`.
The body must use the topic ("`value |> foo + 1` is invalid syntax"), and `%`
"could instead be `^`, or many other tokens"; the token isn't final
([proposal-pipeline-operator](https://github.com/tc39/proposal-pipeline-operator)).
The bikeshed thread lists `^^`, `<^`, `##`, `#_`, `@@` and `%%` as
favourites, rejects `##` as confusing next to private fields, and one TC39
member calls a plain identifier such as `$` or `it` "an eternal nonstarter"
([issue #91](https://github.com/tc39/proposal-pipeline-operator/issues/91)).
Lesson: once a language has used up its ASCII punctuation, picking a marker
is hard. Stitchwort's pipe doesn't need a topic (it puts the value first,
rule E). The problem only comes up inside function arguments.

### 3.12 What to take from the survey

- **A placeholder needs a visible boundary.** The designs nobody complains
  about have one: braces (Kotlin, Swift), an outer marker (Elixir, Clojure),
  brackets around an operator (Haskell), or a leading dot (Swift key paths,
  F#, Stitchwort). Scala's and Raku's implicit boundaries are what draw the
  complaints.
- **Short forms are for short functions.** Clojure, Kotlin and Scala's own
  docs all say so.
- **Late additions stayed small:** F# 8 (`_.Name`), Swift 5.2 (`\.email`),
  GHC (`(.field)`), Koka and TC39 (one call's arguments).

## 4. What any design must fit in Stitchwort

### 4.1 Where a lambda may appear

A lambda is a whole expression only: after `:=`, `=>`, `then`, `else`, `|>`,
an opening bracket or a comma. As an argument it needs brackets
([lambda-syntax.md §4.2](lambda-syntax.md)). So any short form used as an
argument will be in brackets anyway: `xs.find (…)`. That makes Lean's
"brackets are the boundary" nearly free here, and Scala's rule would add
nothing except for unbracketed positions.

### 4.2 `_` is taken

`_` already has six meanings ([method-sections.md §4](method-sections.md)):
wildcard pattern, `.._` in list patterns, unused lambda parameter `_ => e`,
**a hole the compiler fills in**, the previous expression in a `calc` step
(`_ = b := h`), and `if _: c`. The hole is the problem. A token count (see
the appendix) finds about **300 holes used as arguments in 31 files**, all
in proofs and examples, as in `Bool.andLeft _ _ hc` and
`rewrite List.lengthAppend _ _`. Under any rule where `_` inside brackets
makes a function, `(Bool.andLeft _ _ hc)` would become a two-parameter
function. Usually that gives a type error, which is hard to read.
Scala avoids this only because it has no holes. F# has the small version
(FS3570).

### 4.3 Sugar, types, implicits, effects

Whatever the spelling, it should be **exactly a lambda**: `(.id == id)` is
`x => x.id == id`, the same term and hash as the hand-written lambda. Binder
names don't count towards a term's identity; variables are de Bruijn
indices, according to the comment at the top of `crates/core/src/hash.rs`.
Consequences:

- **Checking** is a lambda's: the parameter's type comes from the expected
  function type, from a pipe's left side, or from an annotation, and in an
  application the function is checked after the other arguments if its
  parameter type isn't known yet. This is what sections do today
  ([syntax.md, Method sections, "Checking"](../syntax.md#method-sections)).
  `.id` needs `x`'s type to find the namespace, as now.
- **Dependent expected types** (`(r: Booking) -> P r`) and **implicit**
  ones (`[a: Type] -> a -> Bool`) work as for `x => …`. Implicit parameters
  in front are introduced silently (lambda-syntax.md §4.3). A function that
  must *name* an implicit parameter is written as a lambda,
  `[a: Type] (x: a) => …`.
- **Proofs:** a proof that writes the lambda out (`c => c == 'S'`) and a
  program that writes `(== 'S')` give the same term, so `match`
  generalisation still finds it. This is the problem D506 had to solve for
  `Pair.snd` against `.snd`. That problem doesn't arise here.
- **Effects:** an operand runs each time the function is called, as in the
  lambda: `(.id == readId())` reads once *per element*. Swift key paths
  evaluate subscript arguments once, when the function is made (SE-0249),
  and so does a Stitchwort named-argument call
  (`overlaps (time := now())` runs `now()` once, syntax.md "Run order"). That
  difference follows from "it's just a lambda" and should be stated in the
  docs.

## 5. How often each shape occurs

A script (method in the appendix) found every lambda written directly inside
round brackets, `(x => …)` or `(a b => …)`, in `aoc/`, `examples/` and the
standard library (`crates/elab/src/std/`), and sorted them by shape.

| | AoC programs | AoC specs | AoC tests | AoC proofs | examples | std | **all** |
|---|---:|---:|---:|---:|---:|---:|---:|
| bracketed lambdas | 48 | 38 | 32 | 557 | 600 | 1,759 | **3,034** |
| one parameter | 38 | 31 | 32 | 427 | 465 | 1,343 | **2,336** |
| … used exactly once | 29 | 25 | 9 | 284 | 303 | 1,036 | **1,686** |
| … used more than once | 9 | 6 | 20 | 127 | 55 | 160 | **377** |
| … not used | 0 | 0 | 3 | 16 | 107 | 147 | **273** |
| two or more parameters | 10 | 7 | 0 | 130 | 135 | 416 | **698** |

Single-use parameters, by where the parameter sits:

| Shape (single use) | Example | AoC programs | all | Shortest form |
|---|---|---:|---:|---|
| `x.f …`, no operator | `(tile => tile.x)` | 8 | 72 | `.x` **today** |
| last argument | `(c => charAt line c)` | 1 | 273 | `charAt line` **today** |
| `x` alone | `(hit => hit)` | 1 | 59 | none |
| `x.f … op e` | `(line => line.trim != "")` | 2 | 6 | `(.trim != "")`: **option (a)** |
| `x op e` | `(char => char == 'S')` | 4 | 221 | `(== 'S')`: **operator section** |
| `e op x` | `(t => k + t)` | 0 | 72 | `(k +)`: **operator section** |
| anywhere else, top level of the body | `(column => parseNumber column.init)` | 3 | 279 | placeholder only |
| *subtotal: top level of the body* | | 19 | 982 | |
| inside inner brackets | `(i => Nat.pow 10 (template.blockLength * i))` | 7 | 502 | Scala and Lean bind the inner brackets; `it`/`$0` would need an outer marker |
| body has a nested lambda | `(id => db.fresh.any (range => range.contains id))` | 3 | 202 | |

Of the 279 "placeholder only", 101 are `T.f x …` with `x` first
(`(t => Int.mul t c)`, mostly std): under rule E those are sections
(`.mul c`), so about 180 remain that only a general placeholder would
shorten. Most of those are in std, a lot of it proofs. Two-parameter lambdas
with each parameter used once, in order (`(splitter beam => splitter && beam)`):
159, of which 28 are exactly `a op b`.

What this says:

- **The AoC programs already have 8 lambdas that could be sections today**
  (Day 9 `tiles.map (tile => tile.x)` is `tiles.map .x`; Days 8, 9 and
  `Common/Range.sw` `(part => part.trim.toNat)` is `(.trim.toNat)`; Day 5
  `(range => range.contains id)`; Day 6 `(op => op.apply numbers)`; Day 4
  `(row => row.sumBy .count)`). That's a style clean-up, not a language
  change.
- **Matt's exact shape, `x.f … op e`, is rare in this repository** (6 in
  all), but it's the shape of filter and find predicates in ordinary
  application code, which the AoC programs mostly avoid. The operator
  shape `x op e` is common (221).
- **Options (a) plus operator sections cover 299 lambdas (6 + 221 + 72).** A
  general placeholder shortens another ~180 single-use lambdas after rule E,
  plus 113 multi-use ones if the marker can repeat (`it`, `$0`). Most of
  those are in std proofs.

## 6. The options

Each option shows Matt's two lines, the AoC lines it changes, and its costs.
"Cost" is a rough size for one lane, as an **[estimate]**.

### (a) Sections reach to the end of their expression

**The rule.** A section that *starts* an expression takes the whole
expression, operators included: `(.id == id)` is `x => x.id == id`,
`(.trim != "")` is `x => x.trim != ""`, `(.fst + 1)` is `x => x.fst + 1`.
"Starts an expression" means where a lambda may start without brackets
(§4.1): after `(`, `,`, `:=`, `=>`, `then`, `else`, `|>`, a named argument's
`:=` and a record field's `=`. An expression ends at a closing bracket, a
comma, `then`/`else`, or the end of the line's expression, as for a lambda's
body. **As an argument a section still takes nothing**: `.count .isZero` and
`f .a == b` (which is `(f .a) == b`) keep their meaning.

The value is used once, at the start. A later section in the same
expression is a separate function: `(.isEmpty || .isZero)` is
`x => x.isEmpty || (.isZero)`, which is a type error with a note (below).

```
bookings.find (overlaps (time := time))                  -- today, §2.2
bookings.find (.id == id)

lines.takeWhile (.trim != "")                              -- Day 5
block.headOr (0, []) |> .fst + 1                           -- Day 6, was |> (indexed => indexed.fst + 1)
```

**After `|>`.** A pipe step is an expression start, so `xs |> .sum == 6` is
`xs |> (x => x.sum == 6)`, which the pipe rewrite already turns into
`xs.sum == 6`. Both ways of reading it give the same value. This removes the
section case of the trap in [guide ch. 4](../guide/04-functions.md#pipes)
(`[1, 2, 3, 4] |> .filter (…) == [2, 4]` would check and mean what it
says). `xs |> List.filter p == ys` is still the error it is today, with its
note.

**Readability.** It extends a rule readers already know. The boundary is
whatever ends the expression, normally the brackets you'd write anyway. The
form can't express "value in the middle" (`parseNumber x.init`), but
`(.init |> parseNumber)` can: the pipe is an operator like the others.

**Parsing conflicts.**

- *Today's meaning.* At an expression start, `.f … op e` today parses as
  `(.f …) op e`, comparing or adding a *function*. That always fails for
  `==`, `!=`, `<`, `+`, `++`, `&&`: functions have no `DecEq`, order or
  arithmetic (syntax.md: `List (Nat -> Nat)` has no `DecEq`). Only `=`
  (an equation between functions, a proposition) could mean something today.
  A grep for a section at an expression start followed by a top-level
  operator found no such code in `aoc/`, `examples/`, std or the guide,
  except the guide's deliberate error example above.
- *`_` holes, `(x := e)`, record update:* untouched; no new token.
- *Sections on a continuation line* keep their layout error.

**Elaboration.** Parser only. Today the section's `Lam(%section, body)` is
built around the dot chain. Under (a) it's built around the operator
expression instead, when the section is at an expression start. The pipe
rewrite's search for the `%section` slot (the loop around `Expr::Field` on
`SECTION` in `parser.rs`) also walks down left operands. D506's
partial-application rule applies only to a bare `.f args` body, so an
operator section stays a lambda.

**Errors.**

- Unknown receiver type: the existing `E-CANNOT-INFER` ("can't tell what
  `.id` is applied to"), with the note showing `x => x.id == id`.
- A second section in the operands (`(.isEmpty || .isZero)`): keep the type
  error, and add a note: "a section's value is used once, at its start; to
  use it twice, write `x => x.isEmpty || x.isZero`".
- `_.id == id`: fix today's note to suggest `.id == id` (the whole
  expression), not `.id`.

**Rule E and types.** `.id` is looked up in `x`'s type namespace, and
`x.f a` puts `x` first. Under E every "value first" call is a section, so
(a) handles `(t => Int.add t b > 3)` as `(.add b > 3)`.

**Cost.** About 60 lines of parser, the notes, about 8 accept/reject
examples, syntax.md and the guide's Sections paragraph. The formatter has to
print the section with its operators. Half a lane.

### (a+) Operator sections, Haskell style

**The rule.** In brackets, a binary operator with its left operand missing
is a function of that operand: `(== 'S')` is `x => x == 'S'`, `(+ 1)` is
`x => x + 1`, `(= False)` is `x => x = False`. With the right operand
missing it's the other way: `(k +)` is `x => k + x`. **`-` is excluded** as
a right section, as in Haskell: `(- 1)` and `(-1)` stay the number. Write
`(.sub 1)`, which under rule E is `x => Nat.sub x 1`. Prefix `!` isn't a
binary operator.

Seen together with (a): "in a section, the value at the start is left out".
`(.id == id)` leaves out the `x` before `.id`; `(== id)` leaves out the `x`
before `==`.

```
bookings.find (.id == id)                                       -- (a)
line.toList.findIndex (== 'S')                                    -- Day 7, was (char => char == 'S')
Vec.tabulate manifold.width (== manifold.start)                   -- Day 7
labels.count (== circuits.labelOf box)                            -- Day 8
```

**Readability.** Familiar from Haskell and Idris. The operator shows where
the value goes. The `(- 1)` exception is the only trap, and Haskell
documents the same one.

**Conflicts.** `(` followed by a binary operator is a parse error today
(checked), so nothing changes meaning. `(e op)` is also an error today.
`(-` stays negation. `->` isn't included (it's a type), and neither is `|>`
(`(|> f)` would just be `f`).

**Elaboration.** Parser only: `Lam(%section, Binary(op, Var(%section), e))`.
It's checked like a section, so `(== 'S')` needs the parameter's type from
what's expected. With `==`, whether the type can come from the right operand
when nothing is expected is **[unverified]**; the deferred-checking rule in
§4.3 normally means the expected type is known.

**Errors.** Unknown type: the section `E-CANNOT-INFER`, phrased for the
operator ("can't tell what `(== 'S')` compares"). `(- 1)` used where a
function is expected: the usual type error, plus a note "`(- 1)` is the
number −1; for `x => x - 1` write `(.sub 1)`".

**Cost.** About 40 parser lines, examples, docs. Small.

**Bare operator as a function**, `(&&)` for `a b => a && b` (Haskell; Swift
`sorted(by: >)`): 28 two-parameter lambdas are exactly this, two of them in
Day 7. Nearly free once (a+) exists. Kept separate as D1195.

### (b) Scala-style `_`

```
bookings.find (overlaps _ time)
bookings.find (_.id == id)
lines.takeWhile (_.trim != "")
line.toList.findIndex (_ == 'S')
Vec.zipWith (_ && _) row beams
```

**Conflicts: fatal.** `_` is a hole (§4.2). `(Bool.andLeft _ _ hc)`, written
about 300 times in proofs, would turn into a two-parameter function. Making
it work means giving holes a new spelling, and the obvious one, `?`, is
already goals. `_ => e`, `calc`'s `_ =` and wildcard patterns add more
places where a reader has to decide which `_` is meant. Scala itself is
moving its other `_` meanings away (§3.1). The scope rule is the
best-documented complaint in the survey.

**Elaboration** would be a lambda, as for every option. **Cost** of the
syntax alone is moderate, but renaming holes would touch every proof.
**Not recommended.**

### (c) Lean-style marker in brackets

The boundary is the nearest enclosing round brackets, a tuple component, or
a named argument's value. Each marker is a new parameter. The marker can't
be `_` (§4.2) and can't be `·`, because syntax is ASCII (syntax.md: "Names
are ASCII"). Lean's own ASCII form `.` would collide with sections. Taking
`#` as the stand-in:

```
bookings.find (overlaps # time)
bookings.find (#.id == id)
columns.map (parseNumber #.init)                    -- Day 6, was (column => parseNumber column.init)
List.range template.copies |> .sumBy (Nat.pow 10 (template.blockLength * #))
                                     -- Day 2: WRONG, # binds at (template.blockLength * #)
```

The Day 2 line shows Lean's pitfall: any inner bracket becomes the
function's boundary, and 502 of the 1,686 single-use lambdas have the
parameter inside inner brackets.

**Readability.** Fine for short cases. `#` means nothing to a reader coming
from Scala or TypeScript. **Conflicts:** none, since `#` is free.
**Errors:** "`#` is only allowed inside brackets, which become the function".
**Cost:** a lexer token, a pass when closing a bracket that wraps it in a
lambda, the errors, the docs, the formatter, LSP hover. About a lane.

### (d) Kotlin-style `it`, with brackets as the boundary

`it` is a keyword meaning the parameter of the function made at the nearest
enclosing brackets. It can be used several times, always meaning the same
value (Kotlin's meaning, not Lean's).

```
bookings.find (overlaps it time)
bookings.find (it.id == id)
columns.map (parseNumber it.init)                                 -- Day 6
problems.sumBy (evaluate it.operator it.rowNumbers)               -- Day 6, two uses
Map.fromList (List.range boxes |> .map ((it, it)))                -- Day 8: the tuple needs its own brackets
```

**Readability.** The most readable marker for a Scala/TS/Kotlin reader. It
reads as English. But Kotlin's `it` belongs to a lambda's braces, and
Stitchwort has no such braces (`{` is a record), so the boundary has to be
the brackets, and the Day 2 pitfall of (c) applies. Kotlin's own
conventions warn about `it` in nested lambdas (§3.2). It also gives a second
way to write a section (`it.id` against `.id`), and the docs would have to
say which to prefer.

**Conflicts.** `it` becomes a reserved word. No `.sw` file in the repository
uses `it` as a name (grep: it appears only in comments and text). It doesn't
collide with `_`, `.f`, `|>`, `(x := e)` or record update.

**Cost.** Keyword, bracket pass, errors ("`it` outside brackets"; "`it`
inside a lambda that names its parameter"), formatter, LSP, docs. About a
lane, plus the guide.

### (e) Swift-style `$0`, `$1`

```
bookings.find (overlaps $0 time)
bookings.find ($0.id == id)
Vec.zipWith ($0 && $1) row beams                                  -- Day 7
```

Numbered markers handle both repeated use and several parameters. `$` is
free outside text, but inside an interpolation `"${$0.name}"` it reads
badly. The brackets would be the boundary, as in (c) and (d), with the same
pitfall. Swift has braces to bound `$0`; here they'd be round brackets.
Readers from TS or Scala don't know `$0` (it's Swift and shell). **Cost:**
as (c).

### (f) Nothing beyond what exists

Use sections, named arguments, plain partial application, and lambdas for
the rest:

```
bookings.find (overlaps (time := time))           -- or (.overlaps time) with Booking.overlaps
bookings.find (booking => booking.id == id)
tiles.map .x                                      -- Day 9 clean-up, today
```

**Cost:** none, plus the 8 AoC clean-ups and fixing the `_.name` note.
**Gap:** the operator shapes, which are 299 lambdas including Matt's
`.id == id`.

## 7. Side by side

| | (a) section to end | (a+) operator sections | (b) `_` | (c) `#` in brackets | (d) `it` in brackets | (e) `$0` | (f) nothing |
|---|---|---|---|---|---|---|---|
| Matt's line 2 | `(.id == id)` | (with a) | `(_.id == id)` | `(#.id == id)` | `(it.id == id)` | `($0.id == id)` | lambda |
| Matt's line 1 | `(overlaps (time := time))` today | | `(overlaps _ time)` | `(overlaps # time)` | `(overlaps it time)` | `(overlaps $0 time)` | as (a) |
| Lambdas shortened (of 2,336 one-parameter) | 6 | 293 | ~982 | ~982 | ~1,095 | ~1,095 | 0 new |
| New token | no | no | reuses `_` | `#` | keyword `it` | `$0…` | no |
| Breaks existing code | no | no | **~300 holes** | no | no | no | no |
| Boundary pitfall | none (start of expression) | none | Scala's | inner brackets | inner brackets | inner brackets | none |
| Second spelling for `.id` | no | no | yes | yes | yes | yes | no |
| Cost **[estimate]** | ½ lane | small | large | 1 lane | 1 lane | 1 lane | none |

(The "~982" counts single-use lambdas whose parameter is at the top level of
the body; "~1,095" adds the 113 multi-use ones whose uses are all there.)

## 8. Recommendation

Do (a) and (a+) together, as one small lane after rule E lands. They
extend the one short form Stitchwort already has, use no new token, change
the meaning of nothing that compiles today, and cover Matt's
`.id == id` and the `== 'S'` lambdas in AoC. For Matt's first line, use
the named-argument form that works today, or put `overlaps` in `Booking`'s
namespace and write `.overlaps time`.

Don't add a general placeholder now. The remaining ~180 single-use lambdas
it would shorten are mostly in std proofs, where a named parameter costs
five characters. Each spelling has a cost: (b) breaks holes, and (c)–(e)
add a new token, the inner-bracket pitfall, and a second way to write
sections. If real programs later show many `f x.g y` lambdas, (d) `it` in
brackets is the candidate: it's the most readable for a Scala or TS reader
and doesn't collide with anything.

The 8 AoC lambdas that are sections today can be rewritten whenever the
next AoC lane touches those days.

## 9. Decisions

1. **D1192** — Should a section that starts an expression take the whole
   expression, operators included, so that `(.id == id)` is
   `x => x.id == id` and `xs |> .sum == 6` is `xs.sum == 6`? As an argument a
   section would still take nothing. [Recommend: yes]
2. **D1193** — Add Haskell-style operator sections, `(== 'S')` and `(k +)`,
   with `-` excluded as a right section so `(- 1)` stays the number?
   [Recommend: yes, in the same lane as D1192]
3. **D1194** — Fix the `_.name` note so it suggests the whole section
   (`.id == id` where operators follow), and rewrite the 8 AoC lambdas that
   are sections today (§5)? [Recommend: yes; the note with D1192, the AoC
   clean-up in the next AoC lane]
4. **D1195** — A bare operator in brackets as a two-argument function,
   `(&&)` for `a b => a && b` (28 sites, 2 in Day 7)? [Recommend: yes if
   D1193 is accepted, since it's nearly free; otherwise no]
5. **D1196** — No general placeholder (`_`, `#`, `it`, `$0`) for now; `_`
   is ruled out for good because of holes; if one is ever wanted, `it` in
   brackets (option d) is the candidate. [Recommend: yes]

## Appendix: how the counts were made

- **Lambdas.** A Python script tokenised every `.sw` file under `aoc/`,
  `examples/` and `crates/elab/src/std/` (comments, text and characters
  removed). It found every `(` followed by a run of lower-case names or `_`
  and then `=>`, and took the body up to the matching `)`. A parameter's uses
  are the body's tokens with its name not preceded by `.`. "Top level" means
  not inside further brackets (`(`, `[`, `{`) and no `=>` in the body.
  Shapes: `x .` first with no top-level binary operator (section today);
  `x .` first with one (option a); `x` then a binary operator (operator
  section); `e op x` at the end (left section); `x` as the body's last token
  with no top-level operator (partial application); `T . f x …` with `T`
  upper-case (a section under rule E). Lambdas after `:=`, `|>` or at a line
  start aren't counted, and neither are typed parameters `((x: T) => …)`.
  Areas: `aoc/**/Proofs*` proofs, `**/Spec*` specs, `**/Tests*` tests, the
  rest of `aoc/` programs. The counts are approximate: a name used as a
  record field pun (`{ x, y }`) counts as a use, and nested
  brackets are judged by tokens, not by a parse.
- **Holes.** The same tokeniser counted `_` tokens preceded by a name, `)` or
  `]`, skipping lines that start with `|` (arms) and parameter runs ending
  in `=>`: 300 in 31 files (18 AoC proof files, 3 std, 10 examples).
- **Checks against the compiler** used `target/release/stitchwort` built from
  `main` (25 October 2026) on scratch files: `(.id == id)`, `(_.id == id)`,
  `(== 'S')`, `$0` (errors quoted in §2), and `overlaps (time := time)`
  (checks).
- **The scripts aren't committed.** They're one-off measurements, like those
  in [method-sections.md §7](method-sections.md) and
  [dot-receiver.md, appendix](dot-receiver.md).

## Sources

Language references and discussions are linked where they're used, in §3.
In this repository: [syntax.md](../syntax.md) (Method sections, Named
arguments, Pipe forward, Expressions);
[method-sections.md](method-sections.md) (D504–D507);
[dot-receiver.md](dot-receiver.md) (D302, rule E);
[lambda-syntax.md](lambda-syntax.md) (lambda forms, implicit parameters);
[guide ch. 4](../guide/04-functions.md);
`crates/syntax/src/parser.rs` (`section_start`), `crates/elab/src/dot.rs`
(`find`, `section_partial`), `crates/core/src/hash.rs` (what a hash
ignores).
