# Shorter grammar code in direct style (SW-883)

**Status:** research note, 29 October 2026; §6's recommendation is built.
Sequence expressions `(a; b)` (§4.2, D1700) and `Parse.before` (§4.1,
D1701, `before` only: no `after` or `between`) were added in SW-888, and
day 3's `mul(` rule is now §5.1's one line. The rules as built are in
docs/syntax.md (Layout, "A sequence"), with
`examples/accept/sequence-expression.sw` and `examples/reject/sequence-*.sw`.
One detail the note left open: a `;` straight after a `let`'s value starts
the `let`'s body even when the value ends in a lambda or an `if`, so
`(let f := x => x + 1; f 2)` keeps its meaning. SW-888 doesn't cover D1702
(a warning for a dropped function value) or D1703 (discard markers). The
questions for Matt were D1700 to D1703 (§7).

AoC 2024 day 3's `mul(` rule takes six lines where Lean's applicative parser
takes one ([aoc-2024-day03-community.md](../comparisons/aoc-2024-day03-community.md) §4).
Matt asked (D1661) what it would take to write something like
`Mul (shortNumber()) (char ','; shortNumber())`, with the leading `text "mul("`
and trailing `char ')'` handled somehow. This note says what works today, what
other direct-style languages do, and what the options cost.

Labels, as in the other notes:

- **[checked]**: read in Stitchwort's source or docs at `4178fdb9`, or run
  with the release `stitchwort` built from `main` on 29 October. The
  experiments are in [direct-style-grammars/](direct-style-grammars/):
  `args.sw` and `rewrites.sw` pass `stitchwort test`, and `gaps.sw` is
  meant to be refused;
- **[cited]**: taken from a page or source file fetched on 29 October 2026
  (URLs in [Sources](#sources));
- **[inferred]**: my reasoning from checked or cited facts;
- **[unverified]**: from memory, not confirmed against a primary source.

## Contents

1. [Summary](#1-summary)
2. [What works today](#2-what-works-today)
3. [How others write it](#3-how-others-write-it)
4. [Options](#4-options)
5. [Rewrites side by side](#5-rewrites-side-by-side)
6. [Recommendation](#6-recommendation)
7. [Decisions for Matt](#7-decisions-for-matt)
8. [Also found](#8-also-found)
9. [Sources](#sources)

## 1. Summary

**Most of Matt's line already works.** Effectful calls are allowed as
arguments, and arguments run left to right. The docs specify that order, and
it holds for constructor arguments, tuple parts, list items, record fields (in
the order written) and named arguments (where written) **[checked]**. So
`Mul (shortNumber()) (shortNumber())` is a parser today. It is what Idris
writes as `[| Mul shortNumber shortNumber |]` and Lean as
`Mul (← shortNumber) (← shortNumber)`. Direct style gives idiom brackets for
free.

**What's missing is Lean's `*>` and `<*`:** "run this for its effect, keep the
other value". Today, inside an argument, that takes an expression `let`:
`Mul (shortNumber()) (let () := char ','; shortNumber())` works
**[checked]**. The bare `(char ','; shortNumber())` is `E-PARSE`, "expected
`)`, but found `;`" **[checked]**. `;` is used only by `let` (docs/syntax.md:15).

**Recommendation** (§6): two small steps that work together.

1. **`(a; b)` as a sequence expression**: run `a`, then give `b`'s value.
   It is the same tree as the two lines `a` and `b` of a block, so only the
   parser and the docs change. The elaborator already has `Expr::Seq`. This
   is OCaml's `;`, Scala's and Koka's `{ a; b }`, and Effekt's
   `{ number(); 1 }`.
2. **`Parse.before`**: `value |> before ")"` reads `)` after the value is
   built, for the trailing `<*`.

Day 3's rule then becomes one line:

```
() => Mul (text "mul("; shortNumber()) (char ','; shortNumber()) |> before ")",
```

against Lean's `string "mul(" *> Insn.Mul <$> int <* string "," <*> int <* string ")"`.

Options I considered and don't recommend: discard markers inside argument
lists (`Mul ~(text "mul(") (shortNumber()) …`), tuple patterns, a pure
`drop` function, and ports of `ApplicativeDo`, idiom brackets or Elm's
`|.`/`|=` (§4).

## 2. What works today

### 2.1 Effectful arguments

`MkTwo (any()) (any())` on `"ab"` gives `MkTwo 'a' 'b'` (`args.sw`,
"arguments run left to right" **[checked]**). The same holds for:

| Form | Example | Order | |
|---|---|---|---|
| constructor arguments | `MkTwo (any()) (any())` | left to right | **[checked]** |
| tuple parts | `(any(), any())` | left to right | **[checked]** |
| list items | `[any(), any(), any()]` | left to right | **[checked]** |
| record fields | `{ y = any(), x = any() }` on `"ab"` | as written: `y` is `'a'` | **[checked]** |
| named arguments | `pair (second := …) (first := …)` | as written | **[checked]** |
| dot calls | `nat().toInt`, `(after "X" nat).toInt` | receiver first | **[checked]** (`rewrites.sw`) |
| the left of `\|>` | `Mul … \|> before ")"` | left side first | **[checked]** (`rewrites.sw`) |

The native backend keeps the order too. `stitchwort build` of a parser that
uses `drop` (§4.5) prints `Mul 12 345` and the same error as `run`
**[checked]** (an experiment, not committed).

### 2.2 The order is specified

docs/syntax.md:664 **[checked]**: "Effectful code is written in direct style.
Arguments are evaluated left to right, named ones where they are written
([Named arguments]), and the lines of a block in order. An argument that
performs runs before the call, whether or not the function uses it." The
namespaces proposal says the same for dot calls: "the receiver once, then the
written arguments left to right, then arranged in parameter order"
(docs/proposals/namespaces.md:134, §4.8.2 **[checked]**).

The spec is stronger than OCaml's. There, "the order in which the
expressions expr, argument 1, …, argument n are evaluated is not specified"
**[cited]**, so OCaml code that relies on it is wrong. Scala's spec: "The
application f(e1, ..., en) evaluates f and then each argument e1, …, en from
left to right, except for arguments that correspond to a by-name parameter"
**[cited]**. Stitchwort is like Scala.

### 2.3 Sequencing inside an expression

| Written | Today | |
|---|---|---|
| `(char ','; shortNumber())` | `E-PARSE` "expected `)`, but found `;`" | **[checked]** |
| `(let () := char ','; shortNumber())` | works | **[checked]** |
| `(let _ := char ','; shortNumber())` | works | **[checked]** |
| a block on new lines inside brackets, as an argument (below) | works | **[checked]** |
| `(text "mul(", shortNumber(), char ',', shortNumber(), char ')')` matched by `let (_, left, _, right, _)` | works | **[checked]** |
| the same with `()` in place of the `_`s | `E-NOT-EMPTY` "`()` has values, so this argument can't be `()`" | **[checked]** (§8) |

The block form is:

```
Mul
  (shortNumber())
  (
    char ','
    shortNumber()
  )
```

That is Unison's "wherever Unison expects an expression, a block can be
introduced with the `let` keyword" **[cited]**, and Koka's layout rule, under which "any block that
is indented is automatically wrapped with curly braces" **[cited]**. It
works, but it spends four lines on what Matt wants to write in one.

The parser is close to accepting `(a; b)` already. A block's expression
statement followed by the rest of the block becomes `Expr::Seq(e, rest)`
(`crates/syntax/src/parser.rs:1793` **[checked]**). `let x := e; body` on one
line is the expression `let`, which `let_body` (`parser.rs:1870-1894`) builds
into the same tree as the block form. Nothing builds a `Seq` from `;`.

### 2.4 The formatter

The formatter keeps the author's line breaks and has no line width yet
(docs/proposals/formatter.md, D1013, D1014 **[checked]**). It already spaces
`;` as `a; b` (`crates/fmt/src/spacing.rs:102-108` **[checked]**).
`stitchwort fmt` turned
`(let ()   :=  text "mul(";let m:=Mul …;m)` into
`(let () := text "mul("; let m := Mul …; m)`. It re-indented a badly
indented block in brackets to the layout shown above. It left the 140-column
one-liners alone **[checked]**. It put a multi-line record literal as
`def robotSemicolon(): {Parse} Robot := {` followed by one field per line
(`rewrites.sw` **[checked]**). So the forms below stay readable as long as
the author breaks the lines. It won't break a long one for you.

### 2.5 What goes wrong (`gaps.sw`)

1. **A record literal with an effectful field fails to infer outside the
   result position.** `usePosition { x = shortNumber(), y = 0 }`,
   `({ x = shortNumber(), y = 0 }, 1)` and
   `{ position = { x = shortNumber(), y = 0 }, speed = 0 }` are all
   `E-CANNOT-INFER` "can't tell which record type this literal is". The same
   literal as the whole body, annotated, or with pure fields checks
   **[checked]**. Likely cause **[inferred]**: the effects pass rebuilds the
   literal with its effectful parts bound first, then checks the rebuilt
   literal against the expected type only if it has one
   (`crates/elab/src/effects.rs:3910-3926`). It seems not to pass the
   field's or argument's type down to the parts. This blocks the most natural
   Day 14 rewrite (§5.2) unless the inner records are annotated. It is a bug
   whichever option is chosen.
2. **An effectful argument's value is unknown to the checker.**
   `sized (shortNumber()) (Vec.replicate 2 0)` is "expected `Vec Nat x`, but
   this has type `Vec Nat 2`" **[checked]**. The same is true of
   `let k := ask()` (docs/syntax.md:14). It isn't a problem for grammars, but
   it is the one place where dependent types and effectful arguments meet.
3. **A statement that names a parser without calling it is silently
   dropped.** `shortNumber` on a line of its own, missing its `()`, checks
   and reads nothing, with no warning **[checked]**. This is the mistake that
   Unison's yap README warns about: `_ = some (text " ")` "will never
   execute", so the library added `discard!` "to get the type system on your
   side" **[cited]**. OCaml warns for it (warning 5,
   `ignored-partial-application`: "expression whose result has function type
   and is ignored" **[cited]**). Any option that adds statements inside
   expressions makes this mistake easier to make.
4. A statement whose value isn't `()` is dropped silently too
   (`shortNumber()` as a line, `args.sw` "a dropped value" **[checked]**).
   This one is fine: parsers often read something only to skip it. OCaml
   warns here as well (warning 10, `non-unit-statement` **[cited]**). I don't
   think Stitchwort should.

## 3. How others write it

| Language | `mul(a,b)` style | Skip-and-keep | Source |
|---|---|---|---|
| Lean 4, applicative | `string "mul(" *> Mul <$> int <* string "," <*> int <* string ")"` | the operators `*>` and `<*` | mniip's solution (day 3 note) **[checked]** |
| Lean 4, `do` | `Mul (← int) (← int)` | statements in `do` | "Multiple occurrences of ← are processed from left to right, inside to outside"; `do f (← e1) (← e2)` is `let x ← e1; let y ← e2; f x y` **[cited]** |
| Idris 2 | `[\| Mul int int \|]` | none built in | `[\| f a1 … an \|]` "is translated into `pure f <*> a1 <*> … <*> an`" **[cited]** |
| Haskell `ApplicativeDo` | a `do` block, run with `<$>`/`<*>` "as far as possible" | statements | **[cited]** |
| Elm `elm/parser` | `succeed Point \|. symbol "(" \|= float \|. symbol "," \|= float \|. symbol ")"` | `\|.` "parse this, but ignore the result", `\|=` "keep" | **[cited]** |
| Koka `std/text/parse` | `Cons(p(), many{ sep(); p(); })` in `sep-by1` | `{ a; b }` | **[cited]** |
| Effekt | `Var(ident())`; `or { number(); 1 } { … }` | `{ a; b }` blocks, `;` between statements | parser case study **[cited]** |
| Unison (yap) | `op = do Op expr() plusOrMinus() expr()` | block statements; `discard!` for a result you don't want | **[cited]** |
| OCaml | | `e1; e2` "evaluates expr1 first, then expr2, and returns the value of expr2" | **[cited]** |
| Scala | | `{ s1; …; sn; e }` | **[cited]** |

What I take from this **[inferred]**:

- **The direct-style languages (Koka, Effekt, Unison) all pass effectful
  calls as arguments.** Yap's `do Op expr() plusOrMinus() expr()` has
  exactly the shape of Matt's `Mul (shortNumber()) (shortNumber())`. None of
  them has an applicative layer. Yap says `<$>` "and friends do exist for
  those who really like … applicative style, but frequently using a
  direct-style `do` expression leads to more straightforward code"
  **[cited]**.
- **Every one of them skips with a block statement and `;`.** Koka's
  `many{ sep(); p(); }` is Matt's `(char ','; shortNumber())` with braces.
  None has a "discard" marker inside argument lists. Elm's `|.` is the
  closest, and it is an applicative pipeline, not direct style.
- **Lean's `(← e)` and Idris's idiom brackets are what Stitchwort already
  does without a marker.** Stitchwort runs an effectful argument where it is
  written, so neither has anything to add.

## 4. Options

For each: a sketch, the cost, the pitfalls, and how it fits with the rest of
the language. "Order obvious" means the source order is the order the parse
runs in.

### 4.1 Library only: `after`, `before`, `between`

```
def after (prefix: Text) (parser: () → {Parse} a): {Parse} a    -- prefix *> parser
def before (value: a) (suffix: Text): {Parse} a                  -- value <* suffix, used with |>
def between (open: Text) (close: Text) (parser: () → {Parse} a): {Parse} a

Mul (after "mul(" shortNumber) (after "," shortNumber) |> before ")"
between "mul(" ")" (() => Mul (shortNumber()) (after "," shortNumber))
```

All three work today (`rewrites.sw` **[checked]**). They give the same
values and the same error messages as the six-line rule.

- **Cost:** three definitions and tests in `crates/elab/src/std/Parse/Parse.sw`,
  and a paragraph in docs/guide/08-abilities.md. No language change.
- **Effects visible, order obvious:** yes. `before` works only because `|>`
  runs its left side first, as every argument does. That is specified
  (§2.2), but it is subtle.
- **Pitfalls:** `after` takes a parser, not a value, so a parser with
  arguments needs a lambda: `after "Button A: " (() => offset "+")`. That
  gives two ways to write "this, then that" (`after` and a block). `after`
  covers only literal text. A skipped `newline()` or `spaces()` still needs a
  block or a `let`.
- **Interactions:** none with dependent types, implicit or named arguments.
  `before` takes its value first so that it works with `|>` (docs/syntax.md:1323).

### 4.2 Sequence expressions: `(a; b)`

```
Mul (text "mul("; shortNumber()) (char ','; shortNumber()) |> before ")"
```

`(s1; s2; …; e)` runs each `s` in turn, then gives `e`'s value. It is
exactly the block with those lines. It is allowed wherever an expression
`let` is: after `(`, `:=`, `=>`, `then`, `else`, a comma, or at the start of
a block line. It mixes with `let`: `(let x := a; check x; f x)`.

- **Cost:**
  - *Parser:* small. Where `statement()` (`parser.rs:1812`) and
    `expr_inline` (`parser.rs:2704`) now look for a `;` after a `let`, also
    look for one after an expression statement. Build `Expr::Seq`, which is
    what the two lines would give. Missing-body errors as for `let`. No
    program changes meaning, since `;` has no other use (docs/syntax.md:15
    **[checked]**).
  - *Elaborator and effects:* none **[inferred]**. `Expr::Seq` is already
    handled in `check.rs`, `effects.rs`, `module.rs`, `numbers.rs`, `nav.rs`
    and `autobind.rs` **[checked]**.
  - *Hashes:* the same as the block form, since the tree is the same
    **[inferred]**.
  - *Formatter:* spacing already done (§2.4). Its equivalence check compares
    trees, so it needs nothing new **[inferred]**.
  - *Docs and tools:* a bullet in docs/syntax.md's Layout section next to the
    expression `let`, the guide's `Parse` section, an accept example and a
    reject example (missing body), and the playground's and VS Code's
    tokenizers if they treat `;` specially **[unverified]**.
- **Effects visible, order obvious:** yes. `;` means "for its effect" in
  every language in §3. The order is the reading order.
- **Pitfalls:**
  - The function-value mistake of §2.5 (3): `(char; shortNumber())`, with
    `char` missing its argument, would be accepted and would read nothing,
    as `char` alone on a block line is today **[checked]**.
    That is the case for a warning (D1702).
  - Like the `let` body, a sequence ends at a comma: `(let x := 1; x, 2)` is
    `((let x := 1; x), 2)` **[checked]**. So `(text "a"; nat(), 2)` is a pair
    whose first part is the sequence. That is consistent, but `(a; b, c)`
    could be misread as `a; (b, c)`. The formatter or the guide can push
    such sequences into their own brackets.
  - In pure code `(a; b)` drops `a`, so a pure `a` is dead code. It could
    warn, but that rarely matters.
- **Interactions:**
  - *Dependent types:* none new. A sequence's value is its last part's,
    known or opaque just as on a block line (§2.5 (2)). A proof or type
    after `;` is checked as in a block.
  - *Implicit arguments:* none.
  - *Named arguments:* `pair (second := char ','; nat())` would parse, as
    `pair (second := let y := 1; y)` does today **[checked]**, and run where
    written.
  - *`!`:* none. `!` is `not` (docs/syntax.md:1117), and `(done(); !failed)`
    is a sequence whose value is `!failed`.

### 4.3 Discard markers in argument lists

```
Mul ~(text "mul(") (shortNumber()) ~(char ',') (shortNumber()) ~(char ')')
```

A marked argument runs in its place and isn't passed. This is Elm's `|.` in
direct style, and the shortest form: one line, in grammar order. `~` is
free: the lexer has no `~` token **[checked]**. `!` is taken (`not`).

- **Cost:** the parser (a prefix form in argument position), and the
  elaborator's application spine, which must skip marked arguments while
  keeping their place in the order things run in (`effects.rs`'s argument
  walks, `call_performs`). Error messages that count arguments, the
  formatter's argument layout, and the docs also change **[inferred]**.
- **Effects visible, order obvious:** order yes. The argument list stops
  matching the parameter list, though, so a reader has to count the
  unmarked arguments to see which parameter `shortNumber()` fills.
- **Pitfalls and interactions:** what does `f ~(a)` mean as a partial
  application? Does a leading marked argument count for `|>`, which passes
  "the first explicit argument"? How does it mix with `(x := e)` and with
  inserted implicit arguments, or with a dot call's receiver? Each needs a
  rule, and none of the direct-style languages in §3 has one to copy
  **[inferred]**.
- **Verdict:** not now. `(a; b)` gets the same line within a few characters
  without the counting problem.

### 4.4 Tuple patterns (works today)

```
let (_, left, _, right, _) := (text "mul(", shortNumber(), char ',', shortNumber(), char ')')
Mul left right
```

Tested in `rewrites.sw` **[checked]**: same values, same errors. No cost.
It is Prolog DCG-like, and fine for a flat line format. But the reader
pairs `_`s with positions, `()` can't be written for the skipped parts
(§2.5, §8), and it is two lines, not one. It's a trick to know, not a
recommendation.

### 4.5 A pure `drop` (works today)

```
def drop (ignored: ()) (value: a): a := value
Mul (drop (text "mul(") (shortNumber())) (drop (char ',') (shortNumber()))
```

This works because arguments run before the call (`args.sw` **[checked]**,
also natively). But a pure function that sequences effects is a puzzle for
the reader. It shouldn't go in the library.

### 4.6 `ApplicativeDo`, idiom brackets, Lean's `(← e)`, Elm's `|.` and `|=`

None of these fits **[inferred]**:

- Idiom brackets and `(← e)` make effectful arguments possible in languages
  where effects are monadic values. In Stitchwort they already are (§2.1).
- `ApplicativeDo` exists so that a `do` block can be run with `Applicative`
  alone, for types that can't be monads or for parallel and static analysis.
  Stitchwort has no `do`, and an ability's handler gets the continuation, so
  there's nothing to recover.
- `|.`/`|=` and `<*`/`*>` are user-defined operators over a parser type.
  Stitchwort has no user operators (D1207, docs/proposals/logic-notation.md:707
  **[checked]**), and its parsers are functions, not values to combine
  (docs/proposals/parser-combinators.md §4).

## 5. Rewrites side by side

Every Stitchwort version here, apart from the plain `;` one, is in
`rewrites.sw` and passes. The `;` versions were tested by writing `let () :=`
before each statement **[checked]**: the proposed form is that with the
`let () :=`s removed.

### 5.1 Day 3, `mul(44,46)`

| | Code |
|---|---|
| Lean (mniip) | `string "mul(" *> Insn.Mul <$> int <* string "," <*> int <* string ")"` |
| today | 6 lines: `text "mul("`, `let left := shortNumber()`, `char ','`, `let right := shortNumber()`, `char ')'`, `Mul left right` |
| today, expression `let` | `Mul (let () := text "mul("; shortNumber()) (let () := char ','; shortNumber()) \|> before ")"` (needs `before`) |
| library (§4.1) | `Mul (after "mul(" shortNumber) (after "," shortNumber) \|> before ")"` |
| library, `between` | `between "mul(" ")" (() => Mul (shortNumber()) (after "," shortNumber))` |
| `;` (§4.2) + `before` | `Mul (text "mul("; shortNumber()) (char ','; shortNumber()) \|> before ")"` |
| tuple (§4.4) | `let (_, left, _, right, _) := (text "mul(", shortNumber(), char ',', shortNumber(), char ')')` then `Mul left right` |
| discard markers (§4.3) | `Mul ~(text "mul(") (shortNumber()) ~(char ',') (shortNumber()) ~(char ')')` |

In context, under the recommendation:

```
def instruction(): {Parse} Instruction :=
  oneOf [
    () => Mul (text "mul("; shortNumber()) (char ','; shortNumber()) |> before ")",
    () => pick [("do()", Do), ("don't()", Dont)]
  ]
```

`rewrites.sw`'s `instruction` is this with `let () :=`, and it gives
`[Mul 2 4, Dont, Mul 5 5, Do, Mul 11 8]` on the puzzle's example
**[checked]**.

### 5.2 Day 14, `p=0,4 v=3,-3` (`aoc/src/Aoc/Year2024/Day14/Day14.sw:55`)

Today, nine lines:

```
def robotLine(): {Parse} Robot :=
  text "p="
  let x := nat()
  text ","
  let y := nat()
  text " v="
  let dx := int()
  text ","
  let dy := int()
  { position = { x, y }, velocity = { x = dx, y = dy } }
```

Library:

```
def robotLine(): {Parse} Robot :=
  { position = ({ x = after "p=" nat, y = after "," nat }: Position), velocity = ({ x = after " v=" int, y = after "," int }: Velocity) }
```

With `;`:

```
def robotLine(): {Parse} Robot := {
  position = ({ x = (text "p="; nat()), y = (char ','; nat()) }: Position),
  velocity = ({ x = (text " v="; int()), y = (char ','; int()) }: Velocity)
}
```

The `: Position` and `: Velocity` are there only because of the
inference gap in §2.5 (1). Once that is fixed, it would be:

```
def robotLine(): {Parse} Robot := {
  position = { x = (text "p="; nat()), y = (char ','; nat()) },
  velocity = { x = (text " v="; int()), y = (char ','; int()) }
}
```

Lean, for comparison, would be about
`Robot.mk <$> (Pos.mk <$> (string "p=" *> nat) <*> (string "," *> nat)) <*> (Vel.mk <$> (string " v=" *> int) <*> (string "," *> int))`
**[inferred]**, not taken from a real solution.

Record fields run in the order they're written, not the order they're
declared (§2.1). Here those are the same. A grammar that writes fields in a
different order from the input would read wrong.

### 5.3 Day 13, the claw machine (`aoc/src/Aoc/Year2024/Day13/Day13.sw:30`)

`offset`, today five lines:

```
def offset (sign: Text): {Parse} Offset :=
  text "X${sign}"
  let x := nat()
  text ", Y${sign}"
  let y := nat()
  { x = x.toInt, y = y.toInt }
```

Library, and `;`:

```
def offset (sign: Text): {Parse} Offset := { x = (after "X${sign}" nat).toInt, y = (after ", Y${sign}" nat).toInt }

def offset (sign: Text): {Parse} Offset := { x = (text "X${sign}"; nat().toInt), y = (text ", Y${sign}"; nat().toInt) }
```

`clawMachine`, today nine lines (`text`, `let`, `newline()` three times,
then the record). With `;`:

```
def clawMachine(): {Parse} Machine := {
  buttonA = (text "Button A: "; offset "+"),
  buttonB = (newline(); text "Button B: "; offset "+"),
  prize = (newline(); text "Prize: "; offset "=")
}
```

The library version needs `(let () := newline(); after "Button B: " (() => offset "+"))`.
That is worse than either, because `after` takes only text and only a parser
with no arguments (§4.1). For a three-line record like this, today's block is
about as clear as the `;` form, and I would leave Day 13's `clawMachine` as
it is **[inferred]**.

## 6. Recommendation

**Adopt `(a; b)` (§4.2) and add `Parse.before` (§4.1). Leave out `after` and
the rest.** The reasons:

1. It is the form Matt sketched, and the one Koka, Effekt and OCaml use. It
   keeps every effect in reading order and visible as a statement.
2. It costs a parser change and docs. The tree, the elaborator, effects,
   hashes and the formatter's spacing already exist (§2.3, §4.2).
3. It is general. It works for `char`, `newline()`, `spaces()` and parsers
   with arguments, where `after` works only for literal text and needs a
   lambda for anything else.
4. `before` is the one piece `;` can't do: keep the value, then read the
   closing text. It is three lines of library code. Without it, Day 3 would be
   `(text "mul("; let m := Mul (shortNumber()) (char ','; shortNumber()); char ')'; m)`.

**First step:** one Sonnet lane:

- the parser change, as an expression-statement twin of `let_body`;
- `examples/accept/sequence-expression.sw` (values, a parser, a sequence
  after a comma, a named argument) and `examples/reject/sequence-missing-body.sw`;
- docs/syntax.md's bullet;
- `Parse.before` with a test in `Parse.Tests`.

Then rewrite Day 3's rule and Day 14's `robotLine` as the corpus proof. Day
14's needs the annotations until the §2.5 (1) bug is fixed. Rewriting more of
`aoc/` should wait until Matt has seen those two.

## 7. Decisions for Matt

- **D1700:** Add `(a; b)`, meaning "run `a`, then `b`'s value", wherever an
  expression `let` may go, with the same tree as the block lines? [rec: yes]
- **D1701:** Add `Parse.before (value) (suffix: Text)`, used as
  `… |> before ")"`, and not `after` or `between`? [rec: yes, `before` only;
  `between` only if a second grammar needs it]
- **D1702:** Warn when a statement's value is a function, as in `shortNumber`
  without its `()`, or `char` without its argument (OCaml's warning 5)? It is
  silently dropped today (§2.5 (3)), and `;` makes it easier to write. [rec:
  yes, a separate backlog ticket; no warning for a dropped non-`()` value]
- **D1703:** Leave out discard markers (`~(e)` inside argument lists) for
  now? [rec: yes]

## 8. Also found

Worth tickets whatever is decided. I haven't edited the board.

1. **Bug:** an effectful record literal as an argument, a tuple part or a
   nested field is `E-CANNOT-INFER` (§2.5 (1), `gaps.sw`).
2. **Small:** `()` inside a tuple pattern is `E-NOT-EMPTY` "`()` has values,
   so this argument can't be `()`", while `let () := e` on its own works
   (`gaps.sw`, `unitInTuple`). Either accept it or say "write `_`".
3. **Docs:** `natDigits 1 3` on `1234` reports "got '1'", not "got '1234'"
   (`rewrites.sw`, "day 3: the same errors" **[checked]**). That is a
   little odd next to its doc comment: "All the digits there are read first,
   so "1234" is too long".

## Sources

All fetched on 29 October 2026 and saved under the session's scratchpad.

- Koka, `std/text/parse`:
  <https://gh.ali360.cloudns.ch/koka-lang/koka/blob/dev/lib/std/text/parse.kk>
  (`sep-by1`: `Cons(p(), many{ sep(); p(); })`)
- Koka book, layout rule: <https://koka-lang.github.io/koka/doc/book.html>
- Effekt, parser case study:
  <https://gh.ali360.cloudns.ch/effekt-lang/effekt/blob/master/examples/casestudies/parser.effekt.md>
  (published at <https://effekt-lang.org/docs/casestudies/frontend>)
- Unison, Blocks and statements:
  <https://www.unison-lang.org/docs/language-reference/blocks-and-statements/>
- Unison, `@dfreeman/yap` README (via the Share API):
  <https://share.unison-lang.org/@dfreeman/yap>
- Elm, `elm/parser` README ("Parser Pipelines"):
  <https://gh.ali360.cloudns.ch/elm/parser/blob/master/README.md>
- OCaml manual, Expressions (sequence; order of function application):
  <https://ocaml.org/manual/5.3/expr.html>
- OCaml manual, the compiler's warnings (5, 10): <https://ocaml.org/manual/5.3/comp.html>
- Scala 3.4 specification, Expressions (application order; blocks):
  <https://scala-lang.org/files/archive/spec/3.4/06-expressions.html>
- Lean reference, Syntax of `do` and the functor/applicative operators
  (nested actions):
  <https://lean-lang.org/doc/reference/latest/Functors___-Monads-and--do--Notation/Syntax/>
- GHC User's Guide, `ApplicativeDo`:
  <https://downloads.haskell.org/ghc/latest/docs/users_guide/exts/applicative_do.html>
- Idris 2 tutorial, Interfaces (idiom brackets):
  <https://idris2.readthedocs.io/en/latest/tutorial/interfaces.html>

In this repository: [aoc-2024-day03-community.md](../comparisons/aoc-2024-day03-community.md) §4,
[parser-combinators.md](parser-combinators.md), [negative-arguments.md](negative-arguments.md),
[formatter.md](formatter.md), docs/syntax.md (lines 14, 15, 664, 1117, 1323),
`crates/syntax/src/parser.rs`, `crates/elab/src/effects.rs`,
`crates/fmt/src/spacing.rs`, `crates/elab/src/std/Parse/Parse.sw`.
