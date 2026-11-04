# Keeping only the cases that match: Scala's `collect` in Stitchwort (SW-1292)

**Status:** design note, 4 November 2026. Matt decided in D2370: the
spellings are `match | …`, `match some | …` (this note's earlier `match?`,
renamed throughout) and `matches | …`, with `some` a keyword only between
`match` and `|`; P4, P5, P6, P8 and P10 as recommended; guards follow in
SW-1295. Stages 1 and 2 are SW-1294. The text below still has the
original recommendations in §10. Background: Matt (4 Nov): "one of the nicest features of Scala is
that you can do a map with a partial function that's based on your match,
and you can just emit things that don't match ... if we could figure out a
way to steal that sort of vibe". D2368 (Matt): a `match` whose result is
`Option` does **not** default its missing cases to `None`; the exhaustiveness
check stays, and partiality, if any, is explicit and visible.

Claims about Stitchwort are **[checked]** when I read or ran the thing named
(on `main` at `3206df528`), **[estimate]** when they are guesses.

## 1. In short

**The problem.** Picking out the values of one shape from a list, and taking
them apart as you go, takes three ideas in Stitchwort today: a lambda, a
`match` inside it, and an `Option` with a catch-all `None`:

```
def illegalOf: Scan → Option Bracket
  | Corrupted illegal => Some illegal
  | Unclosed _ => None

example.filterMap (line => illegalOf (scan [] line))
```

Scala says it in one: `lines.map(scan).collect { case Corrupted(illegal) => illegal }`.

**The change.** Two small pieces of syntax, both shorthand for an ordinary
`match`:

1. **`match` with no value in front of the arms is a function** (a *clause
   lambda*): `match | Add => … | Multiply => …` is
   `x => match x with | Add => … | Multiply => …`. It is total, and checked
   like any `match`.
2. **`match some` is the same, but it keeps only what matches**: each arm's
   result is wrapped in `Some`, and the values no arm matches give `None`.
   `match some | Corrupted illegal => illegal` is
   `x => match x with | Corrupted illegal => Some illegal | _ => None`, a
   `Scan → Option Bracket`. The word `some` is the visible mark D2368 asks for: a
   plain `match` never drops a case.

So the example becomes

```
example.map (scan []) |> .filterMap (match some | Corrupted illegal => illegal)
```

and `illegalOf` goes away.

**What it should do.** Anything that takes an `a → Option b` takes a
`match some`: `filterMap` (Scala's `collect`), `findMap` (Scala's
`collectFirst`), `Map.filterMap`, `Option.flatMap`. A `match some` can also be a
definition's whole body, which turns the AoC lookup tables (`| '+' => Some
Add … | _ => None`) into lists of what they recognise. Proofs see an ordinary
`match`, so nothing new is needed in the kernel, and the `filterMap` lemmas
that exist already apply.

The same mechanism with `False` in place of `None` gives the Boolean side
(Scala's `PartialFunction.cond`): **`matches | p => c`** is true where an arm
says so and false for everything else, and an arm may leave its result out
to mean `True`, so `xs.filter (matches | [_, 'x', .._])` keeps the lists
whose second element is `'x'` (§7).

A third piece, **guards** (`| (position, here) if here == wanted => position`),
is what makes about half the real examples work (§3); it is a feature of
`match` in general, and §6 sketches it.

## 2. What Scala has

**[checked]** against the Scala 3 API page for `PartialFunction` [S1]:

- `PartialFunction[A, B]` is "a unary function where the domain does not
  necessarily include all values of type `A`". `isDefinedAt(x)` says whether
  `x` is in the domain, and "it is the responsibility of the caller to call
  `isDefinedAt` before calling `apply`": `apply` outside the domain may throw,
  or may not.
- `lift` "turns this partial function into a plain function returning an
  `Option` result"; `Function.unlift` goes back. `orElse` tries a fallback
  where the first is undefined; `andThen` composes; `applyOrElse` applies or
  falls back, and for a `{ case … }` literal "the compiler generates an
  `applyOrElse` implementation which avoids double evaluation of pattern
  matchers and guards".
- The literal `{ case p => e … }` is a partial function **when the expected
  type is `PartialFunction`**, and a total function (a `MatchError` at run
  time for a missing case) when it is an ordinary function type [S2]. So
  partiality is decided by the callee: `collect` and `collectFirst` take a
  `PartialFunction`, `map` doesn't.

What a total, proof-checked language can take from this: `apply` outside the
domain can't exist (it would need a proof that `isDefinedAt` holds), so the
useful part of `PartialFunction` is exactly its `lift`, `A => Option[B]`.
Stitchwort already has that type, and the functions that consume it
(`List.filterMap`, `List.findMap`, `Map.filterMap`, `Option.flatMap`,
**[checked]** in `crates/elab/src/std`). What is missing is only the
*literal*: a short way to write an `a → Option b` as the cases you want.

Elsewhere: Lean has `fun | p => e | q => f` (total) [L1]; Haskell has
`\case` (total) and list comprehensions, where a pattern that fails to match
a generator skips the element (`[c | Corrupted c <- scans]`) [H1]; OCaml has
`function | p -> e`; Elixir's `for {:ok, v} <- xs` also skips. Nobody but
Scala makes a match literal partial by its expected type.

## 3. Where it would be used (aoc/, games/rogue)

I searched the programs (not the `Proofs/` directories) for `filterMap`,
`findMap`, `| _ => None`, `if … then Some … else None` and filter-then-map
chains, and read each site **[checked]**. Before and after, real code:

**1. Day 10 (2021), the test helper above.** A two-arm function that exists
only to be passed to `filterMap`:

```
-- before
def illegalOf: Scan → Option Bracket
  | Corrupted illegal => Some illegal
  | Unclosed _ => None
test "the example's first illegal characters" :=
  example.filterMap (line => illegalOf (scan [] line)) == [Curly, Round, Square, Round, Angle]

-- after
test "the example's first illegal characters" :=
  example.map (scan []) |> .filterMap (match some | Corrupted illegal => illegal) == [Curly, Round, Square, Round, Angle]
```

**2. Day 8 (2024), antennas on the grid.** The `Option` is taken apart by
`.map` inside the lambda; a pattern says it directly:

```
-- before
cells.withIndex.filterMap (((column, cell)) =>
  cell.map (frequency => ({ frequency, position = { row, column } }: Antenna)))

-- after
cells.withIndex.filterMap (match some | (column, Some frequency) => ({ frequency, position = { row, column } }: Antenna))
```

**3. Day 9 (2024) spec, the checksum.** `pair.fst`, `pair.snd` and a nested
`.map` become one pattern:

```
-- before
blocks.withIndex |> .filterMap (pair => pair.snd.map (id => pair.fst * id)) |> .sum
-- after
blocks.withIndex |> .filterMap (match some | (index, Some id) => index * id) |> .sum
```

**4. Day 3 (2024) spec, the last do() or don't().** The helper `setting`
spells out the `None` for `Mul`; inline, only the two that matter remain:

```
-- before
def setting: Instruction → Option Bool
  | Mul left right => None
  | Do => Some True
  | Dont => Some False

def enabledAfter (earlier: List Instruction): Bool :=
  match earlier.filterMap setting |> .last with …

-- after
def enabledAfter (earlier: List Instruction): Bool :=
  match earlier.filterMap (match some | Do => True | Dont => False) |> .last with …
```

(Whether this one should change is taste: the named `setting` documents the
puzzle. The point is that it can.)

**5. Day 22 (2024), the first five prices of each window.** As a definition
whose whole body is a `match some`:

```
-- before
def sale (prices: List Nat): Option (Changes, Nat) :=
  match prices with
    | [a, b, c, d, e, ..rest] => Some ({ first = change a b, second = change b c, third = change c d, fourth = change d e }, e)
    | _ => None

-- after
def sale: List Nat → Option (Changes, Nat) := match some
  | [a, b, c, d, e, .._] => ({ first = change a b, second = change b c, third = change c d, fourth = change d e }, e)
```

**6. Lookup tables (Day 6 2025, Day 16 2021, Day 24 2024, the roguelike's
keys).** Each arm loses its `Some`, and the table loses its last line:

```
-- before
def operationOf: Nat → Option Operation
  | 0 => Some Sum
  | 1 => Some Product
  | 2 => Some Minimum
  | 3 => Some Maximum
  | 5 => Some GreaterThan
  | 6 => Some LessThan
  | 7 => Some EqualTo
  | _ => None

-- after
def operationOf: Nat → Option Operation := match some
  | 0 => Sum
  | 1 => Product
  | 2 => Minimum
  | 3 => Maximum
  | 5 => GreaterThan
  | 6 => LessThan
  | 7 => EqualTo
```

and `Wire.zBit` (`match wire with | Z bit => Some bit | _ => None`) becomes
`def Wire.zBit: Wire → Option Nat := match some | Z bit => bit`.

**7. Day 15 (2024), positions of one kind of tile (needs guards, §6).** A
filter and a map that take the same pair apart twice become one step:

```
-- before
rows.gridCells
  |> .filter (((position, here)) => here == wanted)
  |> .map ((((row, column), here)) => ({ rows = row.toInt, columns = column.toInt }: Cell))

-- after
rows.gridCells
  |> .filterMap (match some | ((row, column), here) if here == wanted => ({ rows = row.toInt, columns = column.toInt }: Cell))
```

Day 6 (2024, `positionsOf`) and Day 20 (2024, `onlyTile` and the track) have
the same filter-then-map shape on `(position, tile)` pairs.

**8. Day 18 (2021), every ordered pair (needs guards).**

```
-- before
numbers.withIndex |> .filterMap (((j, y)) => if i == j then None else Some (x, y))
-- after
numbers.withIndex |> .filterMap (match some | (j, y) if j != i => (x, y))
```

**9. Day 7 (2024), a total clause lambda.** A lambda whose body is a `match`
on its parameter loses the name it never needed:

```
-- before
operators.any (operator =>
  match operator with
    | Add => last <= target && canMake operators first (target - last) earlier
    | Multiply => …)

-- after
operators.any (match
  | Add => last <= target && canMake operators first (target - last) earlier
  | Multiply => …)
```

Days 19 and 21 (2024) test helpers (`letters.toList.map (letter => match
letter with …)`) are the same.

**Not a fit, and why.** The roguelike's `marksIn`
(`filterMap (monster => if monster.position.row == row then Some (…) else
None)`) gains nothing: the pattern is a plain variable, so the guard is the
whole test and `match some | monster if monster.position.row == row => (…)` is no
shorter. `Instruction.decode` (Day 17) has arms that are themselves `Option`s
(`Combo.decode operand |> .map Adv`), so `match some` would give an
`Option (Option …)`; it stays a `match`. `filterMap (block => block)` (Day 9,
Day 24) is "keep the `Some`s", which wants a named `List.somes`, not syntax.
`filterMap` with a named function (`filterMap position.step`,
`filterMap autocompleteScore`) is already as short as it gets.

**Count.**

| Shape | Sites | Needs guards |
| --- | --- | --- |
| `filterMap`/`findMap` with an inline lambda that takes a pair or `Option` apart (examples 2, 3, 8) | 3 | 1 |
| a helper defined only to be passed to `filterMap` (examples 1, 4, 5) | 3 | 0 |
| filter then map on a pattern (example 7 and its siblings) | 4 | 4 |
| `Option` lookup tables ending in `_ => None` (example 6) | 10 | 0 |
| a `match` on a value with `Some` arms and `_ => None` (`seat`, `letterAlong`, `readPacket`, …; `e \|> match some \| …`, P8) | 6 | 0 |
| lambdas whose body matches their parameter (example 9) | 4 in programs, 8 in proofs | 0 |
| not a fit (above) | about 8 | |

So about **10 sites** would use the partial form in pipelines (5 without
guards, 5 more with them), **10 lookup tables** would use it as a definition
body, 6 `match`es on a value could be `e |> match some | …` (P8), and
**12 lambdas** would use the total clause form; the Boolean form adds 6 sites
here and 13 in std (§7). For comparison, the
repository has 43 `filterMap`/`findMap` calls in its programs, most of them
with a named function, which is already the short form.

## 4. The designs

Four designs, plus one considered and set aside. In each, the running example
is Day 10's `.filterMap (… Corrupted illegal => illegal …)`.

### A. Clause lambdas only (total)

`match | p => e | q => f` is a lambda. Partial uses spell out the `Some`s and
the catch-all:

```
example.map (scan []) |> .filterMap (match | Corrupted illegal => Some illegal | _ => None)
```

- **Reads**: better than today (no `line =>`, no `match line with`), but the
  `Some` and `_ => None` are noise on every partial use, which is the case
  Matt asked about.
- **Parser**: today `match` must be followed by a value and `with`
  (`match_expr`, `crates/syntax/src/parser.rs:2447`) **[checked]**, so `match`
  followed directly by `|` is free syntax. Several parameters are written as
  a definition's arms write them: `match | acc, Do => … | acc, Dont => …` is
  a two-parameter lambda, and every arm must have the same number of
  patterns (the existing "this alternative has 2 patterns" error).
- **Exhaustiveness**: the ordinary check, unchanged.
- **Proofs**: an ordinary lambda over a `match` (see §5).

### B. Clause lambdas plus a marked partial form, `match some` (recommended)

A, plus `match some | p => e | …`: the arms' results are wrapped in `Some`, and a
final `_ => None` arm is added.

```
example.map (scan []) |> .filterMap (match some | Corrupted illegal => illegal)
```

- **Reads**: as short as Scala's, and the mark is on the function itself, so
  a reader sees that some values give nothing without knowing what
  `filterMap` does. It works with any consumer of `a → Option b`, including
  user code, with no change to their types.
- **Type**: `a → Option b` (or `a → b → Option c` with two patterns per arm).
  A `let corrupted := match some | Corrupted c => c` can be named and reused.
- **Exhaustiveness**: the arms are checked as a `match` whose last arm is
  `_ => None`, so there is no missing case to report. If the written arms
  already cover every value, the `None` is never reached; the compiler-made
  arm has no source position, so today's `W-REDUNDANT` (`redundant.rs`, which
  skips arms with `Span::NOWHERE`) **[checked]** wouldn't say so. I propose a
  warning, `W-MATCH-TOTAL`: "every value matches an arm, so this never gives
  `None`; write `match` and `map`" (P5).
- **What it can't say**: an arm can't decline once its pattern has matched,
  except through a guard (§6). An arm whose result is already an `Option`
  gives `Option (Option b)`; write a plain `match` there (Day 17's `decode`).

### C. Partial because the callee says so, as in Scala

A, plus a type `PartialFn a b` (perhaps written `a ⇀ b`), defined as
`a → Option b`. A clause lambda checked against a `PartialFn` is partial (arms
wrapped, `_ => None` added); checked against anything else it is total.
`List.collect: List a → PartialFn a b → List b` is `filterMap` under the
name Scala uses.

```
example.map (scan []) |> .collect (match | Corrupted illegal => illegal)
```

- **Reads**: exactly Scala's vibe. But the same `match | …` text means a total
  function in `.map` and a partial one in `.collect`, so whether cases may be
  missing depends on a type the reader can't see at the lambda. That is the
  silence D2368 rules out for `Option` results, moved one step away.
- **Checker**: type-directed elaboration. The checker has to see
  `PartialFn` before it unfolds to `a → Option b` when it checks the clause
  lambda; if expected types reach the lambda already unfolded, `PartialFn`
  would have to be a wrapper type or carry an attribute **[estimate]**: I
  haven't checked how long the elaborator keeps a definition's head on an
  expected type. Every std function that should accept one (`findMap`,
  `Map.filterMap`, `Option.flatMap`, Parse helpers) is retyped.
- **Name**: `collect` is taken in spirit by `Each.collect` (Scala's
  `for`/`yield`, `docs/syntax.md` "Each") **[checked]**; `List.collect` beside
  it would mean something else.

### D. A `PartialFn` type with `isDefinedAt`, `apply`, `orElse`, `lift`

A record of a domain test and a function, as Scala's class is.

- `apply` needs a proof that `isDefinedAt x` holds, so every use is
  `pf.apply x (proof)` or goes through `lift`, which is `a → Option b` again.
  Two descriptions of one function (the test and the function) must agree,
  and proofs have to carry that agreement. Scala's reason for the split
  (avoiding running the patterns twice) doesn't arise when the literal is
  compiled straight to `Option`.
- `orElse` is the one combinator worth having, and it is one line on plain
  functions: `def Function.orElse (f: a → Option b) (g: a → Option b): a →
  Option b := x => (f x).orElse (g x)`. More arms in one `match some` usually say
  it better.
- **Not recommended**: it adds a type and an apparatus for what `Option`
  already says.

### E. Set aside: patterns that skip, in `Each`

Haskell's and Elixir's comprehensions skip an element whose pattern fails.
Stitchwort's `Each.collect` (`for`/`yield`) could do the same with a
refutable binding, `let Corrupted c := each scans else skip` **[estimate]**.
It reads well in long multi-generator searches, but it is a heavier form for
the one-line pipelines in §3, needs refutable `let` (refused today,
`E-LET-REFUTABLE`), and puts `Each` in proofs where `filterMap` lemmas exist.
Not pursued here.

### Side by side

| | A | B `match some` | C callee | D record |
| --- | --- | --- | --- | --- |
| Day 10 example | `match \| Corrupted c => Some c \| _ => None` | `match some \| Corrupted c => c` | `.collect (match \| Corrupted c => c)` | `PartialFn.mk …` |
| partiality visible at the lambda | yes (written out) | yes (`some`) | no (in the callee's type) | yes |
| works with any `a → Option b` consumer | yes | yes | only retyped ones | via `lift` |
| new in the checker | none (parser desugar) | none (parser desugar) | type-directed rule | a type |
| proofs see | a `match` | a `match` | a `match` | a record and a proof obligation |
| size | small | small (on top of A) | medium | medium |

## 5. How B works

### 5.1 Syntax

```
clause-lambda ::= "match" "|" arms          -- total
                | "match some" "|" arms         -- partial: a → Option b
arms          ::= arm ("|" arm)*            -- as in `match … with`
arm           ::= pattern ("," pattern)* guard? "=>" expr
guard         ::= "if" expr                 -- §6, a later stage
```

- **Desugaring, in the parser**: `match | p1, q1 => e1 | p2, q2 => e2` is
  `%a %b => match %a, %b with | p1, q1 => e1 | p2, q2 => e2`, with hidden
  names as today's pattern lambdas use (`%arg0`, lambda-syntax.md §1)
  **[checked]**. `match some` also wraps each `ei` in `Some` and adds
  `| _, _ => None` with no source position. The syntax tree keeps a flag so
  the formatter and printer give back what was written.
- **Where it may stand**: wherever a lambda may (lambda-syntax.md §4.2):
  after `:=`, `=>`, `then`, `else`, `|>`, an opening bracket, a comma. As an
  argument it needs brackets, like any lambda: `xs.filterMap (match some | …)`.
  After `|>` it needs none, so `scan [] line |> match | Corrupted _ => 0 |
  Unclosed s => score s` matches on a pipeline's value, a small bonus.
- **`match some`, lexically**: `some` is a keyword only between `match` and
  `|`. The parser reads `match` `some` `|` as the partial form; `match some
  with` still matches on a variable named `some`, and `some` elsewhere is an
  ordinary name. Only the token after `some` decides, with no backtracking.
  Likewise `matches` is a keyword only when a `|` follows it. (D2370.)

- **Layout**: arms on their own lines line up, as `match … with` arms do
  (`match_expr` checks the `|` column) **[checked]**; inside brackets layout
  ends nothing, so

  ```
  |> .filterMap (match some
      | Corrupted illegal => illegal
      | Unclosed [] => Round)
  ```

  works as a bracketed `match` does today.
- **As a definition's whole body**: `def f: A → Option B := match some | …`
  should mean exactly the arms form `def f: A → Option B` then
  `| … => Some …` and `| _ => None`, so that it is part of the definition's
  case tree and gets the same generated equations as written arms, not a
  lifted `%match` (P4). `def f: A → B := match | …` is then the arms form
  with an extra word, and the formatter can drop it.

### 5.2 The `|` ambiguities

These are the ones `match … with` already has; nothing new is introduced.

- **Or-patterns against the next arm, on one line.** Before `=>`, a `|` on
  the same line continues an or-pattern (`| 'h' | 'a' => …`); after the
  result, a `|` starts the next arm, as in one-line `match n with | Zero => 0
  | Succ k => k` **[checked]** (`alternatives`, `or_bar_ahead`).
- **A `match` inside an arm, on one line, takes the arms after it.**
  `match | A x => match x with | B => 1 | C => 2 | D => 3`: the inner `match`
  takes `| D => 3`. Today's rule; bracket the inner one, or put arms on lines.
  The same holds for a clause lambda in an arm's result.
- **A lambda in an arm's result** ends at the next `|`, as today
  (lambda-syntax.md §6.1).
- **`|>`, `||`, rows**: `|>` and `||` are tokens of their own, and a `|` in
  `{State s | e}` is inside braces. None start an arm.
- **`(| …)` is not used**: a bracket that starts with `|` would have read
  nicely, but `(||)` is the operator section for `||`, and a keyword in front
  keeps the reader's "a match starts here" cue. So the form is
  `(match | …)`, not `(| …)`.

### 5.3 Types and inference

Checked against a function type, the hidden parameters take its domain and
the arms are checked against its codomain (for `match some`, against `b` where
the codomain is `Option b`; anything else is a type mismatch saying
"`match some` makes an `Option`"). With no expected type (`let f := match | A =>
1 | B => 2`), the parameters start unknown and the patterns fix them, as for
`let f := x => match x with …` **[estimate]**; where they don't (a record
pattern), it is the existing `E-CANNOT-INFER` with its note.

### 5.4 Abilities in arms

The arms may perform whatever the expected function type's row allows:
`filterMap`'s `f: a → {e} Option b` lets them use the caller's abilities,
as an ordinary lambda's body does (`docs/syntax.md`, lambdas) **[checked]**.
Patterns perform nothing. A guard (§6) runs where an `if` condition would.

### 5.5 What proofs see

An ordinary `match`: the kernel sees nothing new. In detail:

- A clause lambda passed as an argument is a lambda over a lifted `match`
  (`owner.%matchN`, `docs/syntax.md` "Proving things about a definition
  with an inner `match`") **[checked]**. On a constructor it computes, so
  `f (Corrupted Round) = Some Round` is `rfl`; on an unknown value the proof
  matches on it, as today.
- The `filterMap` lemmas apply unchanged **[checked]**:
  `List.memFilterMapIntro` (`x ∈ xs → f x = Some y → y ∈ xs.filterMap f`),
  `List.memFilterMapElim`, `List.filterMapCong`, `List.filterMapAppend`,
  `List.allFilterMap`, `List.findMapIsHeadFilterMap`. I propose one more,
  the two halves as one statement:
  `theorem List.memFilterMap: y ∈ xs.filterMap f ↔ ∃ x, x ∈ xs ∧ f x = Some y`.
- A spec and a program that both write the same `match some` make two generated
  functions; those are compared by their bodies (SW-386, D1091), so they are
  equal by `rfl` unless the `match` calls the definition it is in. Naming the
  function (a local `def`, or a definition whose body is the `match some`) is the
  way round, as for any inner `match`.
- As a definition's body (§5.1, P4), it is the arms form, so the generated
  equations and `f.induct` are what they are for written arms.

## 6. Guards

Five of the ten pipeline sites (§3) are "this shape, and this condition".
Without guards a `match some` can only test shapes, and those sites stay a filter
followed by a map. Guards were proposed before (SW-237, pruned in October
without a note), so this section is a sketch, enough to decide whether they
come with this work.

- **Syntax**: `| p if c => e`, as Scala and Rust write it (OCaml says
  `when`). `if` after a pattern can't be confused with an `if` expression,
  which never follows a pattern.
- **Meaning**: the arm is chosen when `p` matches and `c` is true; when `c`
  is false, the arms below are tried. In a `match some`, falling past the last
  arm gives `None`.
- **Compiling**: in the case tree, a guarded arm becomes an `if c` whose
  `else` continues with the arms below it, matched against the same values,
  as pattern-match compilers usually do it [M1] **[estimate]** for the
  elaborator's `Tree`. The kernel sees an ordinary `if`, which is a `match`
  on a `Bool`.
- **Exhaustiveness**: a guarded arm covers nothing, since the guard may be
  false. So a plain `match` needs an unguarded arm for those values too, and
  `E-NONEXHAUSTIVE` lists them as today. In `match some` the hidden `_ => None`
  covers them, which is why guards and `match some` fit so well together.
- **Proofs**: inside the arm, `c` holds: the guard is an `if`, so a `match
  h: c with` in a proof, or `if h: c` style, gives `h: c = True` there, and
  `False` below.

Guards could be allowed only in `match some` at first (where coverage is never
affected), or in every `match` and definition arm at once (P3).

## 7. The Boolean side: `matches`

Matt (4 Nov, added to the brief): "maybe you're matching something and you
just want to provide the match pattern for the true branch ... if it doesn't
match any of the patterns it's by default false ... so it can do both,
optional and then truthful stuff." Scala has this as
`PartialFunction.cond(x) { case P => true }` (and `condOpt`, the `Option`
version) [S1]; Rust as `matches!(x, P if g)`; C# and Kotlin as `x is P`.

**The change.** The same mechanism as `match some`, with `False` where `match some`
has `None`, and nothing to wrap:

- `matches | p => c | q => d` is `x => match x with | p => c | q => d | _ => False`.
  Each arm's result is a `Bool`, used as it is.
- An arm may leave out its result, which then is `True`:
  `matches | Incomplete` is `x => match x with | Incomplete => True | _ => False`.
- With `|>`, it tests one value, as Scala's `cond(x)` does:
  `Key.next [27] |> matches | Incomplete`. (Likewise `e |> match some | …` is
  Scala's `condOpt(e)`.)

```
xs.filter (matches | [_, 'x', .._])          -- Matt's example
lines.count (matches | Corrupted _)
```

**Why a word of its own rather than `match some` with a `Bool` result.** One
spelling whose default follows the result type (`None` for an `Option`,
`False` for a `Bool`) was considered. It would make
`let isDont := match some | Dont => True` an `Instruction → Option Bool`, since
nothing says which is meant, and in `.filter (match some | …)` the reader has to
know `filter`'s type to know what the arms do. Two spellings say it at the
lambda: `match some` keeps values, `matches` tests. The implementation is the same
desugaring with a different hidden arm. I don't propose a general
"default value" (`0` for `Nat`, `[]` for lists): a silent `0` is exactly the
missing-case bug D2368 guards against.

**Guards are less needed here.** An arm's result is already a condition:
`matches | ['#', ..digits] => digits.length == 6` says what
`| ['#', ..digits] if digits.length == 6 => True` would. (They differ only
when a later arm could also match; then a guard falls through and a result
doesn't.)

**One-line arms.** On one line, a `|` before `=>` continues an or-pattern, as
today (§5.2), so `matches | A | B => e` is `(A | B) => e`, and
`matches | A | B` is true for both. Arms with different results go on their
own lines:

```
matches
  | (False, False)
  | (True, True) => diagonalDiffers
```

**Before and after, real code** **[checked]**:

```
-- Day 3 (2024) spec
def isDont: Instruction → Bool
  | Dont => True
  | Mul left right => False
  | Do => False
-- after
def isDont: Instruction → Bool := matches | Dont
```

```
-- Day 4 (2020), and the same in its spec (`hairColor`)
def hairColorValid (value: Text): Bool :=
  match value.toList with
    | ['#', ..digits] => digits.length == 6 ∧ digits.all isHexDigit
    | _ => False
-- after
def hairColorValid (value: Text): Bool :=
  value.toList |> matches | ['#', ..digits] => digits.length == 6 ∧ digits.all isHexDigit
```

```
-- Day 12 (2024)
def Garden.isCorner (garden: Garden) (position: Position) (vertical: Direction) (horizontal: Direction): Bool :=
  match garden.sameAcross position vertical, garden.sameAcross position horizontal with
    | False, False => True
    | True, True => (position.diagonal vertical horizontal |> .flatMap garden.plantAt) != garden.plantAt position
    | _, _ => False
-- after
def Garden.isCorner (garden: Garden) (position: Position) (vertical: Direction) (horizontal: Direction): Bool :=
  (garden.sameAcross position vertical, garden.sameAcross position horizontal) |> matches
    | (False, False)
    | (True, True) => (position.diagonal vertical horizontal |> .flatMap garden.plantAt) != garden.plantAt position
```

```
-- std, Terminal/Key.sw: five tests of this shape
test "Key: a lone ESC is incomplete" :=
  match Key.next [27] with
    | Incomplete => True
    | _ => False
-- after
test "Key: a lone ESC is incomplete" := Key.next [27] |> matches | Incomplete
```

```
-- std, Text/Basics.sw (and `isLineFeedCode`, `isCarriageReturnCode`, `Ordering.bothEqual`)
def Char.isWhitespaceLow: Nat → Bool
  | 133 => True
  | 160 => True
  | 5760 => True
  | _ => False
-- after
def Char.isWhitespaceLow: Nat → Bool := matches | 133 | 160 | 5760
```

Also Day 20 (2024) and Day 18 (2021) tests (`| Ok track => … | Err message
=> False`, `| Ok _ => False | Err _ => True`), and std's `Map.Spec.isLess`
and `Map.Spec.sameKey` (`Ord.compare a b |> matches | Less`).

**Count.** In aoc/ and games/: 6 sites (`isDont`, `hairColorValid` and
`hairColor`, `isCorner`, two tests). In std: 13 (five `Key` tests,
`bothEqual`, `isLess`, `sameKey`, the two line-ending codes and three
whitespace tables). Not a fit: tables whose default is `True`
(`fitsOperation`'s `| _, _ => True`, Day 16 2021), which would be
`not (matches | …)` and read worse; and Boolean matches whose other arms
compute something (Day 6 2024's `| None => False` among others), which stay
a `match`. I found no pipeline `filter`/`count`/`any` in the programs whose
lambda matches on its argument (the search of §3); the pipeline use Matt
describes is natural, but today's code reaches for `.isSome`, `==` and named
predicates there, so most uses would be definitions and tests.

**Proofs.** As for `match some`: an ordinary `match` returning `Bool`, whose
hidden last arm is `_ => False`. `isDont Do = False` is `rfl`; the `filter`,
`count` and `any` lemmas apply unchanged. As a definition's whole body it is
the arms form (P4), so `isDont`'s generated equations stay as they are, and
the Day 3 proofs that use `instructions.any isDont` keep working.

**Warnings.** As `W-MATCH-TOTAL` for `match some` (P5): a `matches` whose arms
cover every value never gives `False` by default; "this covers every case:
write `match`".

## 8. Other uses

- **`findMap` is `collectFirst`**: `lines.findMap (match some | Header title =>
  title)`. Its doc comment already names Scala's `collectFirst` **[checked]**.
- **`Map.filterMap`** takes `k → v → Option w`: a two-pattern `match some`,
  `m.filterMap (match some | key, Some v if key > 2 => v)`.
- **`Option.flatMap`**: `parsed.flatMap (match some | Ok v => v)`.
- **Several partial functions tried in turn** (Scala's `orElse`): more arms
  in one `match some`, or the one-line `Function.orElse` of §4.D if it turns out
  to be wanted.
- **Parsing**: `Std.Parse` has no combinator taking `a → Option b` today
  **[checked]** (`satisfy` takes a `Char → Bool`), but a
  `Parse.charMap (what: Text) (f: Char → Option a)` would make
  `Parse.charMap "a hex digit" (match some | '0' => 0 | … )` one step instead of
  `satisfy` then a lookup (Day 16 2021 does both today).
- **Folds and the like, total**: `foldLeft 0 (match | acc, Do => … | acc,
  Dont => …)`, `any (match | Add => … | Multiply => …)` (example 9).

## 9. Recommendation

**Design B**: clause lambdas (`match | …`, total and checked like any
`match`), and `match some | …` for "keep what matches", which wraps each result
in `Some` and gives `None` for the rest. Both are parser desugarings into an
ordinary `match`, so the checker, the kernel and proofs see nothing new, and
`match some` works with every existing `a → Option b` function: `filterMap` is
Stitchwort's `collect` and `findMap` its `collectFirst`, with no new names.
`matches | …` is the Boolean side (Scala's `cond`): the same desugaring with
`False` for the rest, and an arm's result `True` when left out.
Guards (`| p if c => e`) follow as a separate stage, since five of the
ten pipeline sites need them; they are a change to the match compiler.

Not C, because it makes the same text total in one call and partial in
another (the silence D2368 rejects), and needs a type-directed rule and a
retyped library. Not D, because in a total language a partial function's
useful content is its `Option` form, which exists.

### Staged plan

1. **Clause lambdas, `match | …`** (Sonnet; small to medium, ~1 lane, est.
   2 h): parser desugaring with a flag on the syntax tree; printer and
   formatter round-trip; the definition-body case (P4) put into the case
   tree; docs (`docs/syntax.md` `match`, guide chapter 4); accept and reject
   examples (arity mismatch, nested one-line `match`).
2. **`match some`** (Sonnet; small, est. 1 h, can share stage 1's lane): the
   `Some` wrapping and hidden catch-all, the "`match some` makes an `Option`"
   mismatch note, `W-MATCH-TOTAL` (P5), docs, examples; the
   `List.memFilterMap` lemma (P6).
2b. **`matches`** (Sonnet; small, est. 45 min, same lane as stage 2): the
   contextual keyword (P9), body-less arms (P10), the hidden `_ => False`,
   the warning, docs and examples.
3. **Migration of §3's sites** (DeepSeek or Sonnet; small, est. 45 min): the
   five pipeline sites and ten tables that don't need guards, the six
   aoc and 13 std `matches` sites (§7), and the total clause lambdas, where they read better (P7). Proofs over the
   changed definitions rerun; the tables keep their equations if P4 holds.
4. **Guards** (Opus for the design check, then Sonnet; medium, est. 3–4 h):
   a short note revising SW-237 if Matt wants guards in every `match` (P3),
   then the match compiler's `if` node, coverage, `E-NONEXHAUSTIVE` and
   `W-REDUNDANT` with guarded arms, a proof example; then the five guarded
   sites.

## 10. Decisions for Matt

Numbered P1 to P10 here; the orchestrator gives them D numbers.

- **P1. Direction: design B** (clause lambdas, plus `match some` that keeps what
  matches), rather than C (partial because the callee is `collect`) or D (a
  `PartialFn` type). **[rec: B]**
- **P2. How the partial form is spelled.** `match some` (Lean, Swift and Kotlin
  use `?` for "maybe"; one token after `match`); or `match some` (says what
  it makes, longer); or a final arm the reader writes, `| _ => none`
  (explicit, but that is design A). **[rec: `match some`]**
- **P3. Guards: when, and where.** (a) with this work, only in `match some`,
  where they never affect coverage; (b) a separate stage, in every `match`,
  clause lambda and definition arm, with guarded arms covering nothing; (c)
  not now. **[rec: (b), after stages 1 and 2; five of the ten sites wait
  for it]**
- **P4. `def f: A → Option B := match some | …` as a definition's body**, meaning
  exactly the arms form with `Some`s and `| _ => None`, so the ten lookup
  tables can use it and keep their equations; `:= matches | …` likewise
  for the Boolean tables (§7). **[rec: yes]**
- **P5. A warning when a `match some` covers every value** (`W-MATCH-TOTAL`,
  "this never gives `None`; use `match` and `map`"). **[rec: yes]**
- **P6. Names: no `List.collect`.** `filterMap` and `findMap` stay the names,
  with their docs saying they are Scala's `collect` and `collectFirst`;
  `collect` already means `Each.collect`. Add `List.memFilterMap` (the `↔`
  form of the two existing lemmas). **[rec: yes, both]**
- **P7. Migrate the existing sites** (§3, stage 3), including turning
  single-use helpers like `illegalOf` and `setting` into inline `match some`s
  where the helper's name doesn't document anything the puzzle needs.
  **[rec: yes, the five pipeline sites and the tables; leave `setting`,
  whose doc comment quotes the puzzle]**
- **P8. No separate `match some e with | …` form for a value.** `e |> match some | …`
  already says it (Scala's `condOpt`), for the six sites like Day 5 2020's
  `seat` (`match (row …, column …) with | (Some row, Some column) => Some …
  | _ => None`); some of those read better still as `Option.map2`.
  **[rec: no separate form]**
- **P9. The Boolean side, `matches | …`** (§7): the same mechanism as
  `match some` with `False` for the values no arm matches, spelled with its own
  word rather than `match some` with a default chosen by the result type.
  `matches` is a contextual keyword (only before `|`), since proofs use it as
  a variable name (Day 7 and Day 23 2024); the one clash is a one-line arm
  whose result is a variable named `matches`. **[rec: yes, `matches`, in
  stage 2; no general default for other types]**
- **P10. Arms without a result in `matches` mean `True`**
  (`xs.filter (matches | [_, 'x', .._])`, `matches | 133 | 160 | 5760`).
  On one line a `|` before `=>` stays an or-pattern, so arms with different
  results go on their own lines. **[rec: yes]**

## Sources

- [S1] Scala 3 API, `scala.PartialFunction`:
  <https://www.scala-lang.org/api/3.x/scala/PartialFunction.html> (read
  4 Nov 2026; quotations above are from it).
- [S2] Scala Language Specification, "Pattern Matching Anonymous Functions"
  (§8.5 in Scala 2's, kept in Scala 3):
  <https://www.scala-lang.org/files/archive/spec/2.13/08-pattern-matching.html#pattern-matching-anonymous-functions>
  (not reread for this note: from memory, **unverified**).
- [L1] Lean 4, `fun` with alternatives: cited in lambda-syntax.md §2.6 [L2].
- [H1] Haskell 2010 report, list comprehensions (§3.11): a failed pattern
  match in a generator skips the element. From memory, **unverified**.
- [M1] Luc Maranget, "Compiling pattern matching to good decision trees"
  (ML Workshop 2008): guards as tests whose failure continues with the
  remaining rows. From memory, **unverified**.
