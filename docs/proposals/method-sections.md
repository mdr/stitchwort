# Passing a method as an argument: `_.isZero`? (D504)

**Status:** design note, 22 October 2026 (SW-264). No code has changed. The
decisions are D505–D507 (§8).

## 1. The short answer

AoC day 1 (`aoc/src/Aoc/Day01/Day01.sw`) reads:

```
def zerosLandedOn (startingDial: Dial n) (turns: List Turn): Nat :=
  turns
    |> .scanLeft Dial.move startingDial
    |> .drop 1
    |> .count Dial.isZero
```

The wish was to write `.count _.isZero`, meaning `.count (d => d.isZero)`, so
that a wrapper type like `Dial` doesn't force `Dial.` in front of every
function passed along.

**Stitchwort can already do this**, spelt without the `_`: a *method
section* `.isZero` is `x => x.isZero`, and it is allowed as an argument, not
only at the start of a pipe step ([syntax.md, "Method
sections"](../syntax.md#method-sections)). This compiles and runs today, with
the same answers (1076 and 6379 on the real input) and with day 1's proofs and
tests still passing:

```
def zerosLandedOn (startingDial: Dial n) (turns: List Turn): Nat :=
  turns
    |> .scanLeft .move startingDial
    |> .drop 1
    |> .count .isZero

def zerosPassed (startingDial: Dial n) (turns: List Turn): Nat :=
  turns
    |> .scanLeft .move startingDial
    |> .zipWith .zerosDuring turns
    |> .sum
```

(Checked with `target/release/stitchwort` built 22 October, on a scratch copy
of `aoc/`: `run Aoc.Day01.main`, `check`, `test Aoc.Day01.Proofs`,
`test Aoc.Day01.Tests`.)

Day 1 spells out `Dial.` only because the SW-262 rewrite that introduced the
`Dial` record replaced the old bare names with qualified ones
(commit `60664bc3`: `|> .count isZero` became `|> .count Dial.isZero`). The
section form wasn't considered, not rejected.

So this note is mostly about whether anything *more* is needed: a `_`
placeholder, as in Scala and F#, for the cases a section can't express. My
recommendation is no (§7), plus one small change to how sections elaborate so
they don't disturb proofs (§5).

## 2. How method sections work today

From [syntax.md](../syntax.md#method-sections), and the parser
(`section_start`, `section_at` in `crates/syntax/src/parser.rs`) and
elaborator (`crates/elab/src/dot.rs`):

- `.f args` is `x => x.f args`: dot notation with the receiver left out.
  Chains work: `.name.length` is `x => x.name.length`.
- **Space rule.** A section starts after a space, a bracket, or at the start of
  an expression. `p.name` is a field access; `f p .name` is `f p (.name)`.
- **As an argument a section takes no arguments of its own**, so
  `.count .isZero` is `.count` applied to the section `.isZero`, never
  `.count.isZero` (a chain) or `.isZero` swallowing something after it. A
  section with arguments needs brackets: `ds.map (.addNat 3)`.
- **In a pipe**, `xs |> .drop 1` is rewritten by the parser to exactly
  `xs.drop 1`; no lambda is made.
- **Receiver type.** A section is checked like a lambda, so the type of `x`
  must be known: from the expected function type, from a pipe's left side, or
  from an annotation. In an application, a section whose parameter type isn't
  known yet is checked *after* the other arguments, so `List.map .name people`
  works.

How `.count .isZero` finds `Dial.isZero` in day 1, step by step:

1. `turns |> .scanLeft .move startingDial |> .drop 1` has type
   `List (Dial n)`; the pipe fixes the receiver of `.count` to that list.
2. `List.count` takes a predicate `a -> Bool` and a `List a`. With
   `a := Dial n`, the section `.isZero` is checked against `Dial n -> Bool`.
3. So its `x` has type `Dial n`, whose head `Dial` names the namespace:
   `x.isZero` is `Dial.isZero x`.

`.scanLeft .move startingDial` works the same way: `.move` is checked against
`Dial n -> Turn -> Dial n`, and `x.move` with nothing after it is the partial
application `Dial.move x`, a `Turn -> Dial n`.

When the type isn't known, the error already says what to do:

```
[E-CANNOT-INFER] Error: can't tell what `.length` is applied to
 2 │ def g: Nat := (.length) "abcd"
   │                ───┬───
   │                   ╰───── the type of the value this section takes isn't known here
   │ Note: `.length …` is `x => x.length …`, and `length` is looked up in the namespace of
   │ `x`'s type, so that type must be known: pipe a value into it (`xs |> .length …`), pass
   │ it where a function of a known type is expected, or annotate it, as in
   │ `(.length …: List Nat -> List Nat)`
```

## 3. What other languages do

| Language | Method as a function | Placeholder for any expression |
|---|---|---|
| Scala | `_.isZero` | `_ + 1`, `f(_, 3)`, `_ + _` (two parameters) |
| F# 8 | `_.IsZero` | none |
| Kotlin | `Dial::isZero` (unbound reference) | `it` in a one-parameter lambda `{ it.isZero }` |
| Swift | key path `\.isZero` | `$0` in closures `{ $0.isZero }` |
| Lean 4 | `(·.isZero)` | `(· + 1)`, `(h · 1 ·)` |
| Haskell | `(.isZero)` with OverloadedRecordDot (fields only) | operator sections `(+ 1)` |
| Gleam | none | `f(_, 3)` (one `_`, one call) |
| Elixir | `&(&1.is_zero)` | `&(&1 + 1)`, `&f(&1, 3)` |
| **Stitchwort** | **`.isZero`** | none |

**Scala** `_` placeholders expand to a lambda at the *innermost enclosing
expression* that isn't just `_` itself [Scala spec 6.23; Rust internals
thread]. That rule is short to state but bites in practice: `println(_.toString)`
inside `xs.foreach(…)` expands to `println(x => x.toString)`, not
`x => println(x.toString)` [Tencent], and `_ + _` is a *two*-argument
function. Type inference for the expanded lambda also fails in simple-looking
cases ("missing parameter type for expanded function") [Scala users forum].
`_` in Scala also means wildcard patterns, wildcard imports and default
initialisation, so the one character carries several meanings.

**F# 8** added `_.Prop` precisely for pipelines: "This can come especially
handy in a sequence of `|>` pipelined calls", e.g. `List.distinctBy _.Name`,
`List.map _.Head.Name` [F# 8]. It is restricted to an *atomic* expression
(no spaces, except inside method-call parentheses), so `_.Foo + 1` is not
allowed. It clashes with `_` as a discard: `fun _ -> 5 |> _.ToString()` gets
warning FS3570 [F# 8]. F#'s design is the closest to what was asked for, and
it is deliberately as small as Stitchwort's section.

**Kotlin** has the implicit name `it` for a one-parameter lambda
(`list.count { it.isZero }`) and *callable references*: `Dial::isZero` is an
unbound reference to a member, taking the receiver as its first argument
[Kotlin lambdas, Kotlin reflection]. Style guides warn against `it` in nested
lambdas, where it's unclear which `it` is meant [Klocwork].

**Swift** (SE-0249, Swift 5.2) lets a key path literal stand in for a function
where one is expected: `users.map(\.email)` [SE-0249]. Like a Stitchwort
section, it only works where a function type is expected: `(\String.count)("Hey")`
doesn't compile [Swift forums].

**Lean 4** writes `(· + 1)` for `fun x => x + 1`; several `·` are several
parameters, and the brackets delimit the function (nested brackets start a new
one) [Lean functions; Lean 3 changes]. So Lean's form of the request is
`(·.isZero)`. Lean also has *leading-dot identifiers*, `.some` or `.cons`,
whose namespace comes from the **expected type** rather than from a receiver
[FPIL]; that's a different feature that happens to look like Stitchwort's
section (§6.4). Lean's generalised field notation `x.f` looks `f` up in the
namespace of `x`'s type, as Stitchwort's dot does [Lean function application].

**Haskell** with OverloadedRecordDot has `(.field)`: "`(.b) a` is the same as
`a.b`" [GHC]. It is fields only, not functions. Plain Haskell's operator
sections `(+ 1)` cover the "operator with one side missing" case.

**Gleam** captures `f(_, 3)` as `fn(a) { f(a, 3) }`: one `_`, directly in one
call [Gleam tour]. **Elixir**'s capture `&(&1.name)` numbers its parameters
[Elixir]. **Koka** has `x.f(y)` meaning `f(x, y)`; I didn't find a placeholder
form there.

What this tells us: the languages that added a *method-only* shorthand late
(F# 8, Swift 5.2, GHC's `(.field)`) all chose something as small as
Stitchwort's section, tied to an expected function type, and avoided general
placeholders. The general placeholders (Scala `_`, Lean `·`, Elixir `&1`) need
a scope rule, and Scala's is the standard example of one that surprises people.

## 4. Candidate spellings

| Spelling | Meaning | Fits Stitchwort? |
|---|---|---|
| `.isZero` (today) | `x => x.isZero` | Yes; exists, tested, documented |
| `_.isZero` (Scala, F#) | same | Clashes with `_` (below); adds nothing over `.isZero` |
| `it.isZero` (Kotlin) | same, plus `it + 1` etc. | `it` would become a reserved word; nesting is unclear |
| `Dial::isZero` (Kotlin) | `Dial.isZero` | That's just `Dial.isZero`, which we have |
| `(·.isZero)` (Lean) | same | Non-ASCII; names and syntax are ASCII |
| `\.isZero` (Swift) | same | Unfamiliar outside Swift; `\` is unused for good reason |

`_` already has five meanings in Stitchwort:

- a wildcard pattern (`| _ => …`, `.._` in list patterns);
- an unused lambda parameter (`_ => e`);
- **a hole the compiler fills in**, in any expression (`List.sumByCongr _ _ …`
  in day 7's proofs; `[highest: _]`);
- the "previous expression" at the start of a `calc` step (`_ = b := h1`);
- the unnamed condition proof in `if _: c`.

The hole is the real conflict. Today `_.isZero` already parses, as a hole
followed by a field access, and fails like this:

```
[E-CANNOT-INFER] Error: can't tell what the value is, so can't look up `.isZero`
 5 │ def a: Nat := ds |> .count _.isZero
   │                            ────┬───
   │                                ╰───── its type isn't known yet here
```

Making `_.isZero` a lambda would mean `_` sometimes means "a value the compiler
finds" and sometimes "the parameter of a lambda the compiler makes", decided by
what follows it. Worse, `f _ x` and `f (_ + 1) x` would read alike while one
fills in an argument and the other makes a function. F# hit a small version of
this with discards (FS3570). Since `.isZero` already means what `_.isZero`
would, there's no reason to pay that cost.

**Cheap improvement (part of D505):** when the value before a `.name` is a bare
hole `_`, the error should suggest the section: "to pass `x => x.isZero`, write
`.isZero`".

## 5. Proofs: a section is an ordinary lambda, almost

A section elaborates to an ordinary lambda, so proofs see nothing new:
`.isZero` is `x => Dial.isZero x`. The kernel has eta (`f` and `x => f x` are
equal; `crates/core/src/value.rs`, "Eta: `f` and `x => f x` are equal"), so
`List.count .isZero xs` and `List.count Dial.isZero xs` are equal by `rfl`.

But *equal* isn't *the same term*, and one place in the checker compares terms
as written. Rewriting day 4's `next.any Pair.snd` to `next.any .snd` broke
`Aoc/Day04/Proofs/Part2.sw` line 137:

```
match e: Vec.any Pair.snd next with
```

The `match` generalises its scrutinee: it looks for `Vec.any Pair.snd next` in
the goal and replaces it by `True`/`False` in each branch ([syntax.md,
`match`](../syntax.md#match)). After the change, the goal contains
`Vec.any (x => x.snd) next` instead, so nothing was replaced and the branch's
proof no longer fit (E-TYPE-MISMATCH; the expected type shows
`Vec.any … (x => x.snd) …`). Writing the proof's scrutinee as
`Vec.any .snd next` too fixed it, and the whole `aoc/` project then checked.
My reading that the generalisation step is what compares syntactically
(rather than conversion lacking eta) rests on the eta code above plus the fix
working; I haven't traced it in the elaborator.

This will recur whenever a proof restates a program's expression, which AoC
proofs do a lot. The fix belongs in the section, not in every proof: **when a
section is `.f` followed by arguments `a…` and the receiver lands in the last
place, elaborate it to the partial application `T.f a…` instead of the
lambda** (`.snd` is `Pair.snd`, `.isZero` is
`Dial.isZero`). Then `xs.any .snd` and `xs.any Pair.snd` are the same term and
switching between them is free, for proofs too. Where the receiver isn't last
(`.sub 3` is `x => Nat.sub x 3`, `.addNat 3` is `x => Mod.addNat x 3`), it stays a lambda, as it must. That is D506.

Effects, implicits and the pipe are unchanged: the pipe form `xs |> .f a` is
already rewritten to `xs.f a` with no lambda.

## 6. The cases a section doesn't cover

### 6.1 Methods with arguments

`_.addNat 3` in Scala is `(.addNat 3)` here: brackets, because as an argument
a section takes no arguments. Tested: `ds.map (.addNat 3)` works. In a pipe
step it's `|> .map (.addNat 3)`.

### 6.2 A call in the middle of a chain

`d => (d.addNat 1).isZero` has no section form: `(.addNat 1).isZero` is a
field access on the section itself, and fails with "can't tell what `.addNat`
is applied to". Scala writes `_.addNat(1).isZero`; that works there because a
call's arguments are bracketed. Here the lambda stays the right spelling. No
AoC program has this shape today.

### 6.3 Operators and non-receiver positions

```
line.toList.findIndex (c => c == 'S')            -- day 7
Vec.tabulate manifold.width (c => c == manifold.start)
Vec.zipWith (s b => s && b) row beams
….count (x => x)
```

Scala would write `_ == 'S'` and `_ && _`; Lean `(· == 'S')` and `(· && ·)`;
Haskell `(== 'S')` and `(&&)`. These are the only places in the AoC programs
(outside proofs) where a placeholder would help, and each lambda is already
short. Proofs use many lambdas, but those are of the shape
`d => Bool.toNat (splitterAt l d && …)`, too large for any placeholder rule.

Options, if this ever grows: Haskell-style operator sections `(== 'S')`,
`(+ 1)`, which have no scope question since the brackets are the function; or
Lean's `·` with an ASCII stand-in. Both are new syntax for a few characters.
D507 recommends waiting.

### 6.4 Functions that *produce* the type: `Range.parse`

```
lines.filterMap Range.parse          -- day 5; also Turn.parse, Bank.parse
```

`.parse` here would look in `Text`, the receiver's type, and fail:

```
[E-UNKNOWN-FIELD] Error: `Text` has no field or function `parse`
```

Lean's leading dot resolves `.parse` from the *expected* type's namespace
instead. With `Text -> Option Range` expected, Lean would need to look through
the arrow and the `Option` to reach `Range`; I couldn't confirm from Lean's
documentation that it does this for function types, so I'm not relying on it.
Adding it to Stitchwort would give `.parse` two meanings depending on whether
the receiver's namespace has it, which is the "silently picks something else"
trap D302 worked to remove. `Range.parse` is clear, and these are constructors
of the domain type in all but name. Not proposed.

## 7. How much it helps in AoC

Sites in the AoC programs (not proofs) that pass a qualified function of the
element's own type, and their section form. All were changed on a scratch copy
and checked (`check` on the whole `aoc/` project, and the day's tests):

| Day | Before | After |
|---|---|---|
| 1 | `\|> .scanLeft Dial.move startingDial` (twice) | `\|> .scanLeft .move startingDial` |
| 1 | `\|> .count Dial.isZero` | `\|> .count .isZero` |
| 1 | `\|> .zipWith Dial.zerosDuring turns` | `\|> .zipWith .zerosDuring turns` |
| 3 | `\|> .map Fin.toNat \|> Nat.fromDigits` | `\|> .map .toNat \|> Nat.fromDigits` |
| 3 | `t.toList \|> .filterMap Char.toDigit` | `t.toList \|> .filterMap .toDigit` |
| 4 | `row.sumBy Cell.count` | `row.sumBy .count` |
| 4 | `next.any Pair.snd` | `next.any .snd` (needs D506, or the proof edit of §5) |
| 5 | `lines.filterMap Text.toNat` | `lines.filterMap .toNat` |
| 5 | `merge db.fresh \|> .sumBy Range.size` | `merge db.fresh \|> .sumBy .size` |
| 6 | `column.all Char.isSpace` | `column.all .isSpace` |
| 6 | `lines.map Text.toList` | `lines.map .toList` |
| 6 | `cells.filterMap Char.digitValue` | `cells.filterMap .digitValue` |
| 6 | `columns.filterMap (column => column.last.flatMap Operator.parse)` | `columns.filterMap (.last.flatMap Operator.parse)` |

Day 5's part 2, before and after:

```
def solvePart2 (db: Database): Nat := merge db.fresh |> .sumBy Range.size
def solvePart2 (db: Database): Nat := merge db.fresh |> .sumBy .size
```

Day 3's joltage:

```
def joltage (k: Nat) (bank: Bank): Nat := bank |> .best k |> .map Fin.toNat |> Nat.fromDigits
def joltage (k: Nat) (bank: Bank): Nat := bank |> .best k |> .map .toNat |> Nat.fromDigits
```

Sites that stay qualified because the function makes the type rather than
using it (§6.4): `Turn.parse`, `Range.parse` (days 2 and 5), `Bank.parse`,
`Operator.parse`, and `Nat.fromDigits` as a pipe's last step.

So 14 sites across five days get shorter today with no language change,
and the only real gap (operators, §6.3) is four short lambdas in day 7.

## 8. Recommendation and decisions

Use the method section Stitchwort already has. Don't add `_.isZero`: it means
exactly what `.isZero` means and would collide with `_` as a hole. Make
sections elaborate to the plain function when they can, so swapping
`Pair.snd` for `.snd` never disturbs a proof. Leave operator placeholders until
there's more demand.

- **D505** — Spell "pass a method" as the existing section `.isZero`, not a new
  `_.isZero`; rewrite the 14 AoC sites of §7 to sections, and make the error
  for `_.name` suggest `.name`. [Recommend: yes]
- **D506** — A section whose receiver lands in the function's last place
  elaborates to the partial application (`.snd` is `Pair.snd`, `.isZero` is
  `Dial.isZero`; `.addNat 3` stays `x => Mod.addNat x 3`), not a lambda, so proofs that restate the
  program keep matching; other sections stay lambdas. [Recommend: yes]
- **D507** — No general placeholder for now (no Scala `_ + 1`, Kotlin `it`,
  Lean `·`, Haskell `(+ 1)`, or Lean-style `.parse` from the expected type);
  revisit if later AoC days collect many `c => c == x` lambdas, starting with
  Haskell-style operator sections. [Recommend: defer]

## As built (SW-266)

D505 (the `_.name` error now says to write `.name`) and D506 are built. The
rule lives in `section_partial` (`crates/elab/src/dot.rs`), called from the
lambda case of `check` (`crates/elab/src/check.rs`): for a section `.f a…`
checked against `A -> B` with `A`'s namespace known, if the receiver's place
in `T.f` is its last explicit parameter and exactly the written arguments come
before it, the section is `apply_args (T.f) [a…]`, then the trailing implicit
arguments, compared with the expected type. Any failure restores the context
and the section is elaborated as the lambda, as before. Chains, named
arguments, and a receiver that isn't last stay lambdas. Day 4's
`next.any .snd` now checks with `Proofs/Part2.sw` unchanged. Examples:
`examples/accept/method-section-partial.sw`, `examples/reject/section-underscore.sw`.

## Sources

- [Scala 2.13 spec, 6.23 Placeholder Syntax for Anonymous Functions](https://scala-lang.org/files/archive/spec/2.13/06-expressions.html#placeholder-syntax-for-anonymous-functions)
- [Rust internals, "Placeholder Syntax - Revisited"](https://internals.rust-lang.org/t/placeholder-syntax-revisited/18190) (quotes the Scala scope rule)
- [Tencent Cloud, "missing parameter type for expanded function"](https://cloud.tencent.com/developer/article/1085160) (the `println(_.toString)` pitfall)
- [Scala users, "_ placeholder inference often breaks in simple scenarios"](https://users.scala-lang.org/t/placeholder-inference-often-breaks-in-simple-scenarios/10761)
- [Announcing F# 8](https://devblogs.microsoft.com/dotnet/announcing-fsharp-8) (`_.Prop` shorthand, atomic-expression rule, FS3570)
- [Kotlin, lambdas: `it` and callable references](https://kotlinlang.org/docs/lambdas.html#it-implicit-name-of-a-single-parameter); [Kotlin reflection](https://kotlinlang.org/docs/reflection.html)
- [Klocwork rule KT.EXPLICIT_IT_LAMBDA_PARAMETER](https://help.klocwork.com/2024/en-us/reference/kt.explicit_it_lambda_parameter.htm)
- [Swift SE-0249, Key Path Expressions as Functions](https://github.com/apple/swift-evolution/blob/main/proposals/0249-key-path-literal-function-expressions.md); [acceptance thread](https://forums.swift.org/t/accepted-se-0249-key-paths-expressions-as-functions/22287); [Swift forums, calling a key path directly](https://forums.swift.org/t/key-paths-as-function-why-doesnt-this-code-work/52249)
- [Lean reference, Functions (`·`)](https://lean-lang.org/doc/reference/latest/Terms/Functions/); [Lean 4, changes from Lean 3](https://lean-lang.org/lean4/doc/lean3changes.html); [Lean reference, Function Application (field notation)](https://lean-lang.org/doc/reference/latest/Terms/Function-Application); [Functional Programming in Lean, Additional Conveniences (leading dot)](https://lean-lang.org/functional_programming_in_lean/Monads/Additional-Conveniences/)
- [GHC user guide, OverloadedRecordDot](https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/overloaded_record_dot.html)
- [Gleam tour, function captures](https://tour.gleam.run/functions/function-captures/)
- [Elixir, `&` capture operator](https://hexdocs.pm/elixir/Kernel.SpecialForms.html#&/1)
- [Koka book](https://koka-lang.github.io/koka/doc/book.html)
- In this repository: [syntax.md, Method sections](../syntax.md#method-sections);
  [dot-receiver.md](dot-receiver.md) (D302, where the receiver goes);
  [lambda-syntax.md](lambda-syntax.md) (lambda forms).
