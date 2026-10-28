# Negative arguments: should `f -2` mean `f (-2)`? (D1460)

**Status:** research note, 28 October 2026 (SW-840). Nothing is implemented.
The decisions are D1461 to D1467 (§7).

Labels, as in the other notes:

- **[checked]**: read in Stitchwort's source or docs, or run with
  `target/release/stitchwort` built from `82a79b30` (this branch's base);
- **[cited]**: taken from a page or source file fetched on 28 October 2026
  (URL in [Sources](#sources));
- **[inferred]**: my reasoning from checked or cited facts, for example what a
  grammar implies about an example the page does not show;
- **[unverified]**: from memory or a search snippet, not confirmed against a
  primary source.

## Contents

1. [Summary](#1-summary)
2. [Where Stitchwort stands](#2-where-stitchwort-stands)
3. [Survey](#3-survey)
4. [Options for Stitchwort](#4-options-for-stitchwort)
5. [Corpus impact](#5-corpus-impact)
6. [Recommendation](#6-recommendation)
7. [Decisions for Matt](#7-decisions-for-matt)
8. [Implementation plan](#8-implementation-plan)
9. [Sources](#sources)

## 1. Summary

Today `f -2` is `f - 2`, as in Haskell 2010, OCaml, Lean 4, Idris 2 and
PureScript. F#, Elm 0.19, Roc (before its 2025 syntax), MoonScript and GHC's
`LexicalNegation` extension read it as `f (-2)`. They decide by spacing: a
`-` with a space before it and none after it, following an operand, is
negation and starts an argument. Swift uses the same spacing rule for every
operator. Scala reads `f -2` as `f.-(2)`. Agda reads `-2` as a negative
literal and `-x` as a name. Koka and Gleam use bracketed calls, `f(-2)`, so the
question doesn't come up for them.

**Recommendation: option (b), the `LexicalNegation` rule, for `-` in argument
position.** A `-` that follows an operand, has a space (or a line break) before
it and touches the token after it is a prefix minus and starts an argument:
`f -2` is `f (-2)`, `f -x` is `f (-x)`, `f -x.abs` is `f (-(x.abs))`.
Everything else stays as it is: `a - b`, `a-b`, `-x` at the start of an
operand, `a - -b`, `(- 1)`.

The reasons:

1. **It changes nothing in the corpus.** Of 1,786 tracked `.sw` files, no
   `-` is written the way the rule changes (§5). The only cases are two
   parser unit tests that assert today's rule.
2. **No program can change meaning silently.** Binary `-` works only on
   `Nat`, `Int` and `Float` (`numbers.rs:38`, `numbers.rs:1375-1394`
   **[checked]**). So `a -b` checks under the old rule only if `a` is a
   number, and under the new rule only if `a` is a function. A program whose
   meaning would change fails to check under one rule or the other, and the
   new rule's error can say why (§4.2.4) **[inferred]**.
3. **Stitchwort already uses spacing this way.** `p.name` is a field access
   but `f p .name` passes a method section, and `f()` is a call but `f ()`
   passes the unit (docs/syntax.md:19, 1340 **[checked]**). `f -x` against
   `f - x` is the same kind of rule. The formatter already writes binary minus
   as `a - b` and prefix minus as `-x` (`crates/fmt/src/spacing.rs:71-80`
   **[checked]**), so formatted code already follows the rule.
4. **The mistake happens.** In AoC 2024 day 22, `changesOf -2 1 -1 3` gave a
   confusing error about `-`. It was fixed by bracketing every argument
   (aoc/NOTES-2024.md, Day 22 §3 **[checked]**). F# users ask for the reverse
   message (`x -1` read as an application), and F# still doesn't give one
   (dotnet/fsharp#13014 **[cited]**). Both directions confuse people. Of the
   two, only the new rule reads the way people write.

The new mistake it creates is `n -1` meant as subtraction. It becomes
`n (-1)`, which is `E-NOT-A-FUNCTION` today. That error needs a note:
"`-1`, with a space before the `-` and none after it, is a negative argument;
to subtract, write `n - 1`" (§4.2.4).

## 2. Where Stitchwort stands

All **[checked]** at `82a79b30`.

**The rule.** `starts_atom` (`crates/syntax/src/parser.rs:3310`) doesn't
include `Tok::Minus`, so an application never takes a `-` as an argument. The
`-` is then binary in `add_expr` (`parser.rs:3182-3194`). A prefix minus is
parsed by `unary` (`parser.rs:3215-3229`). It applies to `unary` again, then
to `app`, so it binds looser than application and dots and tighter than
`*`: `-x.abs` is `-(x.abs)`, `-f x` is `-(f x)` and `-18 % 100` is
`(-18) % 100`. The tree is `Expr::Neg(Box<Expr>, Span)` (`ast.rs:101`). A
negative literal is `Neg` around `Num`, folded by the elaborator. This was
kept "as today" when prefix minus was added (docs/proposals/integers.md:704-708),
and docs/syntax.md:1114 and docs/guide/04-functions.md:128 say so.

**The lexer** (`crates/syntax/src/lexer.rs:650-654`) makes one `Tok::Minus`
for every `-` that doesn't start `->` or `--`. It keeps no whitespace flag,
but every token has its span and a `line_start` flag (`lexer.rs:193-202`),
which is all the rule needs. The parser already reads spacing from spans for
`f()` (`unit_call`, `parser.rs:3360-3370`), for method sections (`section_at`,
`parser.rs:3300-3309`) and for `rewrite <- h` (`parser.rs:2539-2546`).

**What users see today**:

| Source | Meaning | Result |
|---|---|---|
| `def g: Int := f -2` (with `f: Int -> Int`) | `f - 2` | `E-TYPE-MISMATCH` "expected `Int`, but this has type `Int → Int`" at `f`, note "this arithmetic is on `Int` because `Int` is expected here" |
| `f -x` | `f - x` | the same message |
| `f 1 -2` (two parameters) | `f 1 - 2` | the same, plus "this expression is a function still waiting for `b`" |
| `f -2 * 3` | `f - (2 * 3)` | the same message |
| `n -1` (`n: Nat` or `Int`) | `n - 1` | checks |
| `xs.map (x => x -1)` | `x - 1` | checks |
| `n (-1)` | application | `E-NOT-A-FUNCTION` "it's applied to an argument, but its type is `Nat`" |
| `f (-2)` with `f: Nat -> Nat` | | `E-TYPE-MISMATCH` "a `Nat` can't be negative", note "use an `Int` …" |
| `f !x` | | `E-PARSE` "expected the end of the declaration, but found `!`" |
| `\| -1 => …` (an arm) | the pattern `-1` | checks |
| `\| Some -1 => …` | | `E-PARSE` "expected a pattern or `=`, but found `-`" |
| `f` then an indented line `-x` | `f - x` | the `Int → Int` mismatch |

None of the messages mention spacing or brackets.

**The formatter** works on tokens. It gives each `-` a role
(`crates/fmt/src/layout.rs:178-197`): `Binary` if the token before it ends an
operand (and, for a line starting with `-`, the line continues the one above),
`Unary` otherwise, and `RewriteArrow` for `<-`. Then it spaces the minus
(`spacing.rs:71-80`): one space around a binary minus, none after a unary
one, except `- -x`, which needs the space. So today `f -2` is formatted to
`f - 2`, which is the same program. Before writing, it checks that the tokens
and the syntax tree are unchanged (`crates/fmt/src/check.rs`), and if not it
leaves the file as it was.

**Editors.** The VS Code grammar colours `-` as `keyword.operator` and numbers
as `\b[0-9]+\b` (`editors/vscode/syntaxes/stitchwort.tmLanguage.json:109-124`).
The playground has its own small tokenizer with the same classes
(`web/index.html:2309-2420`). There are no LSP semantic tokens.

**Hashes** are of elaborated kernel terms, not of source. The check cache's
key includes the compiler fingerprint (docs/proposals/check-cache.md §4.2), so
any parser change starts a fresh cache.

## 3. Survey

For each language: what `f -2`, `a -b`, `a-b` and `a - b` mean, where `f` is
a function and `a` and `b` are numbers.

### 3.1 Table

| Language | `f -2` | `a -b` | `a-b` | `a - b` | Rule |
|---|---|---|---|---|---|
| **Haskell 2010** | `f - 2` | `a - b` | `a - b` | `a - b` | Negation is the only prefix operator, at the precedence of binary `-`; "one must write `e1(-e2)`" **[cited: Report §3.4]** |
| **GHC `NegativeLiterals`** | `f (-2)` | `a - b` | `a - b` (since 2020) | `a - b` | `-123` is one token, unless it follows a closing token **[cited]** |
| **GHC `LexicalNegation`** | `f (-2)` | `a (-b)` | `a - b` | `a - b` | Decided while lexing, by the whitespace around `-` **[cited]** |
| **OCaml** | `f - 2` | `a - b` | `a - b` | `a - b` | Unary minus binds looser than application; prefix `-` is the function `~-` **[cited]** |
| **F#** | `f (-2)` | `a (-b)` | `a - b` | `a - b` | `-` touching the next token is `ADJACENT_PREFIX_OP` (merged into a literal for numbers), except in `a-b` **[cited: spec]** |
| **Elm 0.19** | `f (-2)` | `a (-b)` | `a - b` | `a - b` | A `-` after a space and touching the next term is negation, as an argument **[cited: source]** |
| **Swift** | (no juxtaposition) | `a`, then prefix `-b`: an error | `a - b` | `a - b` | Whitespace decides prefix, postfix and infix for every operator **[cited]** |
| **Scala** | `f.-(2)` | `a.-(b)` | `a - b` | `a - b` | Prefix operators start a `PrefixExpr` only; a `-` after an operand is infix **[cited: grammar; inferred for the examples]** |
| **Lean 4** | `f - 2` | `a - b` | `a - b` | `a - b` | `prefix:75 "-"`, below application; whitespace isn't significant **[cited]** |
| **Idris 2** | `f - 2` | `a - b` | `a - b` | `a - b` | A prefix operator starts an expression but is not an argument **[cited: parser; inferred for the examples]** |
| **Agda** | `f (-2)` (a literal) | `a` applied to the name `-b` | the name `a-b` | `a - b` | Most character sequences are names; `-42` is a literal **[cited; inferred for the examples]** |
| **Koka** | `f(-2)` only | | name rules (below) | `a - b` | Bracketed calls; integer literals include `[-]`; prefix operators are only `!` and `~` **[cited]** |
| **Roc** (alpha4, whitespace application) | `f (-2)` | `a (-b)` | `a - b` | `a - b` | "a minus is unary iff it is preceded by whitespace … [and] not followed by whitespace" **[cited: source]** |
| **Roc** (2025 syntax) | `f(-2)` | | | `a - b` | Bracketed calls **[cited]** |
| **Gleam** | `f(-2)` only | `a` then literal `-1` (for `-1`) | `a - b` | `a - b` | `-` before a digit is part of the literal, except right after a name or number **[cited: lexer]** |
| **PureScript** | `f - 2` | `a - b` | `a - b` | `a - b` | `'-' expr3`, above application, as in Haskell **[cited: grammar]** |
| **MoonScript** | `f(-2)` | `a(-b)` | `a - b` | `a - b` | "`c = x -y` compiles to `local c = x(-y)`" **[cited]** |

### 3.2 Notes by language

**Haskell 2010.** "The special form -e denotes prefix negation, the only
prefix operator in Haskell … Prefix negation has the same precedence as the
infix operator - defined in the Prelude … Because e1-e2 parses as an infix
application of the binary operator -, one must write e1(-e2) for the
alternative parsing." `(- e)` "is not a section, but an application of prefix
negation"; `subtract` is the section **[cited: Report §3.4, §3.5]**. So
`f -2` is `f - 2`, and with `f` a function it's a type error, usually a
missing `Num` instance for a function type **[unverified wording]**.

**GHC `NegativeLiterals`.** It makes `-123` one token, desugared as
`fromInteger (-123)` and not `negate (fromInteger 123)`. The motivation is
literals at the edge of a range: "in 8-bit arithmetic -128 is representable,
but +128 is not", so `negate (fromInteger 128)` gave an overflow warning. It
only covers literals, so `f -x` stays `f - x`. Its known problem was
`x-1`, which it read as `x (-1)`: "x-1 will be parsed as x applied to the
argument -1, which is usually not what you want" (GHC issue #18022). GHC
proposal #344 fixed this, merged in July 2020: a negative literal can't follow
a closing token, so `f -123` is `f (-123)` but `x-123` is `(-) x 123`. The
proposal's listed drawback is that changing an existing extension's behaviour
"may not be good practice" **[cited]**.

**GHC `LexicalNegation`** (GHC proposal #229, GHC 9.0). The proposal sorts
each operator occurrence by the tokens around it: *prefix* `a !b`, *suffix*
`a! b`, *tight infix* `a!b`, *loose infix* `a ! b`. A closing token is a name,
keyword, literal or `)`, `]`, `}`, and an opening token is a name, keyword,
literal or `(`, `[`, `{`. Whitespace, comments, `,` and `;` are neither. Loose
infix is always the ordinary operator. Under `LexicalNegation` a prefix `-` is
negation, "for any syntactically atomic expression": `f -x` is `f (-x)`.
Prefix `-` binds tighter than any infix operator, so `-a % b` is `(-a) % b`
whatever `%`'s fixity. `(- x)` becomes a right section of subtraction and
`(-x)` is negation, and the guide notes that the two usually differ in type,
so a mix-up is usually a compile error. Negated literals desugar without
`negate`, which makes the extension "a valid replacement for
NegativeLiterals". The proposal's stated problems are that it breaks some
existing code (`f ~ a ~ b`, `x !y`, `(!3)`), which is fixed by changing
whitespace, and an open corner (`f !C{x=a}` against `f !C {x=a}`) **[cited]**.
I couldn't read GHC's issue tracker: gitlab.haskell.org answered with a
bot-protection page. So known bugs in `LexicalNegation` after release are
**[unverified]**.

**OCaml.** The lexer's integer literal has no sign: `int_literal = decimal_literal
| …`, `decimal_literal = ['0'-'9'] ['0'-'9' '_']*` (`parsing/lexer.mll`).
The manual's lexical page shows an optional `[-]`, which describes
`int_of_string`-style constants and patterns, not tokens. The parser has
`subtractive expr %prec prec_unary_minus`, below application in the
precedence list, and `signed_constant: MINUS INT` for patterns
(`parsing/parser.mly`). "When they appear as prefix operators, they are
interpreted respectively as the functions (~-) and (~-.)" **[cited]**. So
`f -1` is `f - 1`, a type error when `f` is a function. `f ~-1` works,
since `~-` is a prefix symbol, which binds tighter than application
**[inferred from the grammar]**.

**F#.** The spec's "Post-filtering of Adjacent Prefix Tokens": "If the token
stream contains the adjacent tokens `– token`: If `token` is a constant
numeric literal, the pair of tokens is merged … Otherwise … the `-` token is
marked as an `ADJACENT_PREFIX_OP` token. This rule does not apply to the
sequence `token1 - token2`, if all three tokens are adjacent and `token1` is a
terminating token …: `a-b`". Prefix operators are just below `.` in the
precedence table, above application **[cited]**. F# users hit the reverse
mistake: `let minusOne x = x -1` gives FS0001 ("expected to have a function
type"), and `list[1 .. l -2]` gives FS0003 "This value is not a function and
cannot be applied". Issue dotnet/fsharp#13014 (April 2022, still open in the
backlog) asks for a message explaining it. Ionide and the Visual Studio
extension added a code fix in the editor instead **[cited]**.

**Elm 0.19.** In `chompExprEnd`, after a term, an operator `-` with
`end /= opStart` (a space before it) and `opEnd == newStart` (nothing after
it) is parsed as `Negate term` and added to the arguments
(`compiler/src/Parse/Expression.hs`). At the start of an expression,
`possiblyNegativeTerm` reads `-` followed directly by a term, so a prefix
minus has to touch its operand **[cited: source]**. A user reported `1 -2`
giving "TOO MANY ARGS … This value is not a function, but it was given 1
argument", and a reply suggested making an operator without surrounding
whitespace a syntax error instead (Elm Discourse, October 2018) **[cited]**.

**Swift.** "If an operator has whitespace around both sides or around neither
side, it's treated as an infix operator … whitespace on the left side only …
a prefix unary operator … whitespace on the right side only … a postfix
unary operator." `(`, `[`, `{` before and `)`, `]`, `}` after an operator
count as whitespace, as do `,`, `;` and `:`. "Negative integers literals are
expressed by prepending a minus sign" to an integer literal, but the book's
source comment says this "is a parser hack, not a lexer hack" **[cited]**.
Swift has no application by juxtaposition, so `a -b` is two expressions and an
error **[inferred]**. This is the most general form of rule (b), applied to
every operator.

**Scala.** "Literal ::= ['-'] integerLiteral" and "PrefixExpr ::=
[PrefixOperator] SimpleExpr", with `PrefixOperator ::= '-' | '+' | '~' | '!'`.
A prefix operator only starts a `PrefixExpr`, so after an operand `-` is an
infix method: `f -2` is `f.-(2)` **[cited: grammar; inferred for the
example]**. The spec's own example is `negate sin(x)`, which parses `sin` as
an infix operator **[cited]**.

**Lean 4.** `prefix:75 "-" => Neg.neg` (`src/Init/Notation.lean:293`), below
application (`max`), so `-2` can't be an argument **[cited]**. In a 2021 Zulip
thread about `add -3 4`, Eric Wieser wrote "`f -a` is parsed identically to
`f - a`", and the error was "failed to synthesize instance Sub". Mario Carneiro
asked "what if you want a prefix notation which has a space between it and
the symbol?" A user-level macro that used whitespace was shown but not adopted
**[cited]**. Mathlib code writes `f (-x)`.

**Idris 2.** `appExpr` is either a simple expression followed by arguments,
or `iOperator` followed by an expression (`PPrefixOp`) (`src/Idris/Parser.idr`).
So a prefix operator starts an expression but is never an argument
**[cited]**. `-` is `infixl 8` (`Prelude/Ops.idr`), and "`-5` desugars to
`negate (fromInteger 5)`" (`Prelude/Num.idr`) **[cited]**. So `f -2` is
`f - 2` **[inferred]**.

**Agda.** "Since most sequences of characters are valid names, whitespace is
more important than in other languages … the whitespace around `+` is
required, since `1+2` is a valid name." Integer literals include `-42`, and
"Negative integer literals have no default mapping and can only be used
through the `FROMNEG` built-in" **[cited]**. So `f -2` is `f` applied to the
literal `-2`, while `f -x` applies `f` to a name `-x` (out of scope, most
likely), and `a-b` is one name **[inferred]**. Agda's answer is to make every
operator need spaces. Stitchwort won't copy that.

**Koka.** Calls are bracketed (`f(x)`); `prefixexpr ::= { ! | ~ } appexpr`,
and `integer ::= [ - ] (decimal | hexadecimal)` **[cited]**. Identifiers may
contain dashes only between letters: "`n-1` // illegal, a digit cannot follow
a dash … `n-x - 1` // identifier "n-x" minus 1" **[cited]**. So Koka uses
spacing too, for names instead of operators.

**Roc.** The whitespace-application syntax up to alpha4 had, in
`crates/compiler/parse/src/expr.rs`, "a minus is unary iff - it is preceded by
whitespace (spaces, newlines, comments) - it is not followed by whitespace -
it is not followed by >, making ->", and a negated number becomes part of the
literal "for overflow reasons" **[cited]**. The new compiler's syntax uses
`f(x)` calls (docs/mini-tutorial-new-compiler.md) **[cited]**.

**Gleam.** Bracketed calls. The lexer reads `-` followed by a digit as part
of an integer literal, except after a name or number with no space between:
"We want to lex `1-1` and `x-1` as `1 - 1` and `x - 1`"
(`compiler-core/src/parse/lexer.rs`) **[cited]**. What `a -1` then does
depends on the parser (two expressions in a block, most likely)
**[unverified]**.

**PureScript.** `expr3 : expr4 | '-' expr3`, and application is in `expr4`
(`src/Language/PureScript/CST/Parser.y`), as in Haskell 2010. Patterns have
`'-' number` **[cited]**.

**Others.** MoonScript: "The minus sign plays two roles … `c = x -y`
compiles to `local c = x(-y)`; `d = x- z` compiles to `local d = x - z`"
**[cited]**. Unison writes an `Int` literal with a sign (`+4`, `-4`) and a
`Nat` literal without one **[cited]**; how it spaces `f -1` is
**[unverified]**.

### 3.3 Patterns across the field

- Languages with **application by juxtaposition** split two ways. The
  Haskell family (Haskell 2010, OCaml, Lean 4, Idris 2, PureScript) treats
  `-` as only binary after an operand. The F#/Elm/Roc/`LexicalNegation` group
  uses the whitespace rule. Nobody in the second group went back to the first.
  GHC's later proposal (#344) moved `NegativeLiterals` *towards*
  `LexicalNegation` **[cited]**.
- The whitespace group all keep **tight `a-b` as subtraction**. GHC learned
  this the hard way (#18022), and F# and Gleam carve it out explicitly.
- They differ on **how much the minus takes**. F# merges only with a numeric
  literal and otherwise marks the minus adjacent. GHC, Elm and Roc negate one
  atomic term. All of them make `f -x` an argument, not just `f -2`.
- In the old group, the **error message** is the weak point (Lean's Zulip
  thread, Stitchwort's AoC notes). In the new group it's the reverse mistake
  (F# #13014, the Elm Discourse thread). The F# issue shows that leaving the
  message to editor code fixes didn't work well.

## 4. Options for Stitchwort

Terms used below, following GHC proposal #229 and the parser's
`starts_atom`:

- A **closing token** ends an operand: a name, a number, a character or
  text literal (including the end of an interpolated text), `)`, `]`, `}`,
  `_`, `?`, `Type`, `Prop`, `omega`, `ring`.
- An **opening token** starts an atom: a name, a number, a character or text
  literal, `(`, `[`, `{`, `_`, `?`.
- **Spaced before** means that the `-` isn't touching the token before it: a
  space, or the `-` starts a line. (A comment always ends at a line break, so
  it adds nothing.) **Glued after** means that the next token starts where
  the `-` ends.

A `-` that is **spaced before, glued after, follows a closing token and is
followed by an opening token** is called an *argument minus* below. It is the
only kind of `-` whose meaning any option changes. Every other `-` keeps
today's meaning under every option: a `-` after `(`, `[`, `,`, an operator,
`:=`, `=>`, `then`, `else`, `|` or the start of an expression is prefix, and
after a closing token it is binary when it is loose (`a - b`), tight (`a-b`)
or suffix (`a- b`).

The examples used for every option:

| # | Source | Today |
|---|---|---|
| 1 | `f -2` | `f - 2` |
| 2 | `f -x` | `f - x` |
| 3 | `f -x.abs` | `f - x.abs` |
| 4 | `f -2 * 3` | `f - (2 * 3)` |
| 5 | `xs.map (x => g x -1)` | `g x - 1` |
| 6 | `5 -3` (a number before) | `5 - 3` |
| 7 | `[1, -2]` | a list |
| 8 | `-x.y` | `-(x.y)` |
| 9 | `\| -1 => …` | pattern `-1` |
| 10 | `\| Some -1 => …` | `E-PARSE` |
| 11 | `x - -y` | `x - (-y)` |
| 12 | `n-1` | `n - 1` |
| 13 | `n -1` with `n: Nat` | `n - 1` |
| 14 | `f -g x` | `f - (g x)` |
| 15 | `f` / indented line `-x` | `f - x` |

### 4.1 Option (a): keep the rule, improve the message

**Rule.** Unchanged.

**Change.** When the left operand of a binary `-` is a function (its type
reduces to a `Π`) and the `-` was an argument minus, the type mismatch gets a
note:

```
[E-TYPE-MISMATCH] Error: type mismatch
 2 │ def g: Int := f -2
   │               ┬
   │               ╰── expected `Int`, but this has type `Int → Int`
   │ Note: `f -2` is `f - 2`, a subtraction; for a negative argument write `f (-2)`
```

The elaborator doesn't see spacing, so `Expr::Binary(BinOp::Sub, …)` would
need a marker set by the parser (a new field, or a side table of spans).

**Examples.** All 15 as today. 10 is still `E-PARSE`.

**Formatter.** Unchanged: `f -2` becomes `f - 2`, which is the same program
but hides what the author wrote. The formatter could instead keep an argument
minus as written (as `Kept`) so the error stays easy to read.

**New mistakes.** None.

**Hashes, LSP, highlighters.** No change.

**Cost and value.** Small. It fixes the message, which was the AoC complaint,
but `f (-2)` stays the only spelling. Lean, OCaml and Haskell users expect
this. F#, Elm and Roc users, and anyone writing maths, don't.

### 4.2 Option (b): the whitespace rule (`LexicalNegation` for `-`)

**Lexing rule.** No new token is needed. The parser decides from spans, as
`unit_call` and `section_at` already do. At token `i`:

```
argument_minus(i) :=
    tokens[i] is `-`
    && i > 0 && tokens[i-1] is a closing token
    && (tokens[i].line_start || tokens[i-1].span.end != tokens[i].span.start)
    && tokens[i+1] exists && !tokens[i+1].line_start
    && tokens[i].span.end == tokens[i+1].span.start
    && tokens[i+1] is an opening token
```

**Parsing rule.** `starts_atom` is also true at an argument minus. In `app`'s
argument loop, an argument minus is consumed and the argument is
`Expr::Neg(atom)`, where `atom` is what `self.atom(false)` reads: one atom
with its field accesses and `()` calls. This is any other argument's extent,
so the minus covers exactly what the argument would have covered without it.
`add_expr` never sees an argument minus. In `add_expr`, a `-` after an operand
is binary as before. That is the loose, tight and suffix cases, since the
argument minus has already been taken by `app`.

The same check in the pattern parser, where a constructor reads its
arguments (`ctor_args`), turns `Some -1` into `Some (-1)`, with the same
restriction to numerals as `(-k)`. An arm's top-level `| -1 =>` already works.

**Examples.**

| # | Source | Under (b) |
|---|---|---|
| 1 | `f -2` | `f (-2)` |
| 2 | `f -x` | `f (-x)` |
| 3 | `f -x.abs` | `f (-(x.abs))`, the same as `-x.abs` as an operand |
| 4 | `f -2 * 3` | `(f (-2)) * 3`, like GHC |
| 5 | `xs.map (x => g x -1)` | `g x (-1)`: an error if `g` takes one argument (see the errors below) |
| 6 | `5 -3` | `5 (-3)`: `E-NOT-A-FUNCTION`, with the new note |
| 7 | `[1, -2]` | unchanged: after `,` the `-` is prefix |
| 8 | `-x.y` | unchanged: `-(x.y)` |
| 9 | `\| -1 => …` | unchanged |
| 10 | `\| Some -1 => …` | `Some (-1)` (D1464) |
| 11 | `x - -y` | unchanged: loose binary, then prefix |
| 12 | `n-1` | unchanged: tight infix is subtraction |
| 13 | `n -1`, `n: Nat` | `n (-1)`: `E-NOT-A-FUNCTION`, with the new note |
| 14 | `f -g x` | `f (-g) x` (D1462) |
| 15 | `f` / indented `-x` | `f (-x)` (D1463) |

Unchanged as well: `-x` at the start of an operand, `then -n`, `(-x)`,
`(- 1)` (still the number, not a section: syntax.md:1368), `rewrite <- h`
(the `-` follows `<`, not a closing token), `a -> -1`, `x == -1`, and `--`
comments (`f --x` is still `f` and a comment).

**Precedence.** Example 4 shows that an argument minus binds tighter than
`*` (it's part of the argument), just as a prefix minus at the start of an
operand binds tighter than `*` today (`-a * b` is `(-a) * b`). The one place
the reading differs is example 14: `-g x` alone is `-(g x)`, but `f -g x` is
`f (-g) x`. GHC has the same split. In Stitchwort, `-g` with `g` a function
fails to check (today `-g` with `g: Int -> Int` gives "expected `Int`, but
this has type `Int → Int`" at `g` **[checked]**), so mistakes show up. The
error could note "`-g` negates `g` alone; write `f (-(g x))`" (part of
D1467).

**No silent changes.** Binary `-` elaborates only for `Nat`, `Int` and
`Float` (`numbers.rs:38-43`, `1375-1394`). An application needs a function
type. No type is both, so for any `a -b` at most one of the two readings
checks. A program that checks today and contains an argument minus fails
after the change, and the reverse holds too **[inferred]**. The exception is a
left operand whose type is still unknown when it's checked (a hole `_`, or a
lambda parameter with no expected type): the elaborator could solve it either
way. Even then the program fails somewhere, because today's reading needed a
number **[inferred]**.

**Formatter.** `roles` (`layout.rs:178-197`) must give an argument minus the
role `Unary`, using the same predicate as the parser, so `f -2` is never
rewritten to `f - 2` (loose, which is subtraction) or `f-2` (tight, which is
also subtraction). The gap before it should be `Kept`, like `f()`, because
spacing changes meaning there. The gap after it is already `Rule(false)` for
`Unary`. The re-parse check would catch a mistake, but it would then refuse
to format the file, so the role has to be right. The formatter adds and
removes no brackets, so `f (-2)` and `f -2` both stay as written (D1466).
`n-1` becomes `n - 1` as today, which has the same meaning under (b).

**Errors for the new mistakes.**

1. `n -1` with `n: Nat` (or `Int`, `Float`, a constructor's result) is
   `E-NOT-A-FUNCTION` today. It needs a note, in the existing
   `not_a_function_hint` (`crates/elab/src/check.rs:2179-2193`), which already
   adds a note for `f x ()`:

   ```
   [E-NOT-A-FUNCTION] Error: this isn't a function
    1 │ def h (n: Nat): Nat := n -1
      │                        ──┬─
      │                          ╰── it's applied to an argument, but its type is `Nat`
      │ Note: `-1`, with a space before the `-` and none after it, is a negative
      │       argument; to subtract, write `n - 1`
   ```

2. `g x -1` where `g x` is already a number: the same error and note, naming
   `g x`.
3. `f a -1` where `f` takes one argument fewer: whichever of these the
   elaborator reports, too many arguments or a mismatch at the result, gets
   the same note.
4. `f -g x` (example 14) with `g` a function: the type mismatch on `-g` gets
   "`-g` negates `g` alone here; for `-(g x)` write `f (-(g x))`".

For the hint to tell `n -1` from `n (-1)`, the parser has to record that the
negation was an unbracketed argument. The simplest way is a flag on
`Expr::Neg`. There are 28 uses of `Expr::Neg` across 10 files, most of them
patterns that would gain a `_` (`git grep "Expr::Neg"` **[checked]**). A
side table of spans on the module would avoid that churn. The flag never
reaches the kernel.

**Hashes.** `f -2` and `f (-2)` give the same tree apart from spans and the
flag. So they elaborate to the same term and have the same hash. No existing
definition's tree changes (§5), so no existing hash moves and the
hash-stability check needs no update. The check cache starts fresh anyway,
because the compiler fingerprint changes.

**LSP.** It uses the parser, so hover, go-to-definition and completion follow
the new tree with no work. `nav.rs` already handles `Expr::Neg`. Recovery
(`parse_module_recovering`) needs a test that a half-typed `f -` (a minus at
the end of a line, so spaced after) is still binary and gives the same "missing
operand" error as today.

**Highlighters.** No change is needed: `-` stays an operator and digits stay
numbers. Optionally, the TextMate grammar and the playground tokenizer could
colour an argument minus before a digit as part of the number
(`(?<=[\s(\[,])-[0-9]+`). That would make `f -2` and `n -1` look different
from `n - 1` (D1468 recommends against it for now).

### 4.3 Option (c): negative literals only

**Rule.** As (b), but the token after the minus must be a number (`Num` or
`Float`), not any opening token. Either the lexer merges the two into a
negative literal, as F# does, or the parser does the same check and builds
`Neg(Num)`.

**Examples.** 1 `f (-2)`. 2 `f -x` stays `f - x`. 3 stays. 4 `(f (-2)) * 3`.
5 `g x (-1)`. 6 `5 (-3)`. 13 `n (-1)`. 10 `Some (-1)`. 14 stays. 15 only for
a literal. The others are unchanged.

**Assessment.** It fixes the common case (in the corpus, 151 of the 153
bracketed negative arguments are literals, §5). It also has every one of
(b)'s new mistakes, since `n -1` is a literal. But it adds a split of its
own: `f -2` passes a number while `f -x` subtracts, and in a language that
reads `-x` as `Int.neg x` everywhere else this is harder to explain than
either rule. GHC tried this split (`NegativeLiterals`) and then offered
`LexicalNegation` as its replacement **[cited]**. Formatter, errors, hashes
and editors are as for (b), restricted to literals. The error for `f -x` is
option (a)'s.

### 4.4 Option (d): refuse an argument minus

**Rule.** An argument minus is `E-PARSE`:

```
[E-PARSE] Error: `-2` right after `f`, with a space before the `-` and none after it, is ambiguous
 Note: for a negative argument write `f (-2)`; to subtract write `f - 2`
```

This is how `!` works today: `f !x` is `E-PARSE` (§2), and docs/syntax.md says
"not an argument (`f !x` is a syntax error: write `f (!x)`)". Elm users
proposed the same in 2018 **[cited]**.

**Examples.** 1 to 6, 13, 14 and 15 are errors. The rest are unchanged.

**Assessment.** No meaning changes, and the error appears before type checking,
so it's always clear. It keeps (b) open for later, because everything (b)
gives a meaning to is an error under (d). But it also creates (b)'s new
mistakes (`n -1` is now an error), and it still makes users write the
brackets. So it has the cost of (b) without the convenience. The formatter
has nothing to format, since such a file doesn't parse. Hashes, LSP and
highlighters don't change.

### 4.5 Other approaches, not recommended

- **(e) Decide by type.** Parse an argument minus both ways and let the
  elaborator choose: an argument if the head is a function, subtraction if
  it's a number. Thanks to the "no silent change" argument in §4.2, the
  choice would always be unique, but meaning would depend on types. The
  formatter, which sees only tokens, couldn't space the `-` correctly, and
  neither could someone reading the code. Lean and Agda deliberately keep
  parsing type-free, and no language in the survey does this.
- **(f) A separate negation symbol.** OCaml's `~-` lets you write
  `f ~-2` with no spacing rule, since a prefix symbol binds tighter than
  application **[inferred]**. Koka's grammar has only `!` and `~` as prefix
  operators **[cited]**; that `~` is its negation is **[unverified]**.
  But `-2` is how everyone writes a negative number, and Stitchwort already
  has `-` as a prefix operator.
- **(g) Make tight binary minus an error** (`a-b`), and give whitespace a
  stricter meaning in general (the Elm Discourse suggestion; Agda). The
  formatter already fixes `a-b` to `a - b`, so this gains nothing.
- **(h) All prefix operators.** A general version of (b), as in Swift: the
  same rule for `!`. `!` has no binary meaning (`!=` is its own token), so
  `f !x` is unambiguous and could simply become `f (!x)`. This is a
  sub-question of (b) (D1465), not a separate option.

### 4.6 Comparison

| | (a) message | (b) whitespace | (c) literals | (d) refuse |
|---|---|---|---|---|
| `f -2` | `f - 2`, with a note | `f (-2)` | `f (-2)` | error |
| `f -x` | `f - x`, with a note | `f (-x)` | `f - x` | error |
| `n -1`, `n: Nat` | `n - 1` | error + note | error + note | error |
| Existing corpus meaning changes | 0 | 0 | 0 | 0 (0 new errors) |
| Silent meaning changes possible | no | no | no | no |
| Formatter change | optional | roles + `Kept` gap | roles, literals only | none |
| AST change | a flag on `Sub` | a flag on `Neg` (for the note) | a flag on `Neg` | none |
| Like | Haskell 2010, OCaml, Lean 4, Idris 2, PureScript | GHC `LexicalNegation`, F# (in effect), Elm, Roc, MoonScript, Swift | GHC `NegativeLiterals` | `!` today |

## 5. Corpus impact

**Method.** A small Rust program, built against `crates/syntax` at
`82a79b30`, lexed every tracked `.sw` file (`git ls-files '*.sw'`: 1,786
files) with `stitchwort_syntax::lex`. For each `-` token it recorded the
context (after a closing token, after an operator, keyword or opening
bracket, or at the start of a line), the spacing on each side, and the kind
of the next token. It also counted bracketed negations in argument position
(a closing token, a space, then `(-`). Six files don't lex, all intentionally
(`examples/reject/char-surrogate.sw`, `logic-unicode-forall.sw`,
`logic-unicode-subset.sw`, `single-ampersand.sw`,
`text-block-interpolation-lines.sw`, `text-block-same-line.sw`). None of them
contains a `-` of the kind that matters. The program lived in a scratch
directory and isn't committed. Its output is summarised below.

**`-` after a closing token** (the only context any option changes):

| Spacing | Count (files) | Meaning under (b) |
|---|---|---|
| `a - b` (loose), next a name/bracket | 718 (120) | unchanged |
| `a - b` (loose), next a number | 371 (97) | unchanged |
| `a -b` (**argument minus**) | **0** | would change |
| `a- b` (suffix) | 0 | unchanged |
| `a-b` (tight) | 1 (1): `crates/fmt/tests/golden/unary-minus.before.sw:3`, `x-y` | unchanged (subtraction) |

**`-` at the start of a line**: 3 in total, and none of them changes. Two
are `- 1` (loose, the formatter's golden test of a continued subtraction, in
the before and after files). The third is
`crates/elab/src/std/Float/Theory.sw:1791`, `-Float.infinity …`, whose
previous token is `:=`, not a closing token.

**`-` elsewhere** (prefix today, prefix under every option): 220 glued after
an operator or keyword (`* -1`, `== -0.0`, `then -…`), 257 glued after an
opening bracket or comma (`(-1)`, `[-1, …]`), 471 written `- b` after an
operator (almost all `rewrite <- h`, plus
`examples/reject/section-minus-is-negation.sw`'s `(- 1)`), and 6 more in the
formatter's golden tests.

**Bracketed negative arguments** that (b) would let you write without
brackets: 151 `(-k)` with a numeral `k`, in 31 files (mostly
`aoc/src/Aoc/Year2024/Day14`, `crates/elab/src/std/Float/Theory.sw`,
`examples/accept/int-*.sw`), and 2 `(-e)` with a name
(`Float.ieeeRank (-Float.infinity)`, `crates/elab/src/std/Float/Float.sw:362`;
`Float.toSource (-Float.infinity)`, `examples/accept/float-operations.sw:67`).
These are counts of what the change would allow, not of changes: the formatter
leaves them as written (D1466).

**Outside `.sw` files.**

- Rust: `git grep` over `*.rs` for a closing character, a space, then `-`
  touching a name, digit or bracket finds only shell flags, JavaScript, test
  output and two Stitchwort strings: the parser tests
  `("f -x", "(Sub f x)")` and `("f -5", "(Sub f 5)")` in
  `prefix_minus_precedence` (`crates/syntax/src/parser.rs:5253, 5262`). They
  test today's rule and would be updated.
- Documentation that states today's rule: docs/syntax.md:1114 (and 1115 for
  patterns), docs/guide/04-functions.md:128 ("A negative literal as an
  argument needs brackets: `f -4` is `f - 4`"), and the precedence table in
  docs/proposals/integers.md:690 and 704-708. That table is a record of the
  integers decision, so it should get a pointer to this note rather than be
  rewritten.
- The AoC notes record the mistake itself: aoc/NOTES-2024.md, Day 22 §3 and
  its item 8.

**Per option:** (a) changes nothing. (b) changes the meaning of 0 tokens in
the corpus, and the 2 parser test cases. (c) changes 0 tokens and the
`f -5` test case. (d) makes 0 files fail and changes the 2 test cases to
expect errors. The quick grep on 28 October also found nothing, and these
numbers confirm it at token level, including text interpolations, which the
lexer tokenizes.

## 6. Recommendation

**Adopt option (b) for `-`**, with these choices (the D questions below):

- The argument minus negates one atom with its dots and `()` calls, like any
  argument (D1462).
- A line break counts as a space, so a continuation line that starts with a
  glued `-x` after an operand is an argument (D1463).
- `Some -1` works in patterns, numerals only, like `(-k)` (D1464).
- The formatter keeps the spacing of an argument minus and adds or removes
  no brackets (D1466).
- Notes on the new mistakes (D1467).
- `!` follows in a separate small change (D1465).

Why (b) and not the others:

1. **(b) is the rule people already write by.** In the corpus, every binary
   minus after an operand has a space on both sides or neither, and every
   prefix minus touches its operand. That's the formatter's style, so no
   existing code changes. The only programs (b) affects are ones that don't
   check today (`f -2`) or that are written in a style the corpus never uses
   (`n -1`).
2. **The failure is always loud.** Since `-` is only for numbers and
   application only for functions, (b) can't change a working program into a
   different working program (§4.2). Every new mistake is a type error, at a
   place that can name the cause. Languages with overloaded `-` (Haskell's
   `Num` on functions, F#'s operators on any type) can't say this.
3. **It matches Stitchwort's other spacing rules.** `p.name` against
   `f p .name`, `f()` against `f ()`, and now `f - x` against `f -x`. Each
   time, a space before and none after means "a new argument starts here".
   GHC proposal #229 gives the general version of this as prefix, suffix,
   tight and loose occurrences.
4. **(c) stops halfway.** It still costs `n -1`, and it adds the `f -2` /
   `f -x` split that GHC moved away from. **(d)** costs as much as (b) and
   gives nothing back. **(a)** is the safe fallback: if (b) isn't wanted, the
   message part of (a) should be built anyway, since it's the AoC complaint.

The risk is people coming from Haskell, OCaml or Lean who write `n -1` to
mean `n - 1`. In the corpus that style doesn't appear at all, the formatter
would never produce it, and the new note says what to write.

## 7. Decisions for Matt

- **D1461.** Adopt the whitespace rule (§4.2): an argument minus (a space or
  line break before the `-`, none after, after an operand) starts a negative
  argument, so `f -2` is `f (-2)` and `f -x` is `f (-x)`. Everything else
  keeps today's meaning. **[rec: yes, option (b). If not, build option (a)'s
  note instead.]**
- **D1462.** How much an argument minus takes: one atom with its dots and
  `()` calls, as any argument does (`f -x.abs` is `f (-(x.abs))`,
  `f -g x` is `f (-g) x`, `f -2 * 3` is `(f (-2)) * 3`). This is GHC's, Elm's
  and Roc's choice. **[rec: yes]**
- **D1463.** A line break before the `-` counts as a space, so in a
  continued application an indented line starting `-x` is a negative
  argument (`f` / `  -x` is `f (-x)`). The alternative is to refuse it with
  an error, like a method section at the start of a line (docs/syntax.md:1342).
  The corpus has no case either way. **[rec: count it as a space. That's one
  rule, and the formatter writes a continued subtraction as `- 1`.]**
- **D1464.** Patterns: allow `Some -1` (and `Cons -1 rest`) as a
  constructor's argument, numerals only, as `(-k)` is. It's a parse error
  today, so nothing changes meaning. **[rec: yes, in the same change]**
- **D1465.** `!`: make `f !x` mean `f (!x)` under the same rule. It's a
  syntax error today and `!` has no binary meaning, so nothing is ambiguous.
  **[rec: yes, as a separate small ticket after `-`]**
- **D1466.** The formatter keeps an argument minus as written (a space
  before, none after, with the gap before it `Kept`) and adds or removes no
  brackets, so `f (-2)` and `f -2` both stay. It doesn't rewrite the 153
  bracketed arguments in the corpus. **[rec: yes]**
- **D1467.** Notes for the new mistakes: on `E-NOT-A-FUNCTION` (and
  too-many-arguments) when the argument was an unbracketed negative
  ("`-1` … is a negative argument; to subtract, write `n - 1`"), and on the
  type mismatch on `-g` in `f -g x` ("`-g` negates `g` alone"). The parser records the
  form with a flag on `Expr::Neg`. **[rec: yes, in the same change, since
  without the note the new mistake is as confusing as the old one]**
- **D1468.** Colour a glued `-` before a digit as part of the number in the
  VS Code grammar and the playground. **[rec: no, not now. `-` stays an
  operator everywhere, and a highlighter regex can't see whether a closing
  token comes before it]**

## 8. Implementation plan

For option (b) with the recommendations above. Each stage is a lane with its
own tests. Stages 1 and 2 must merge together, or 2 right after 1, because
until stage 2 the formatter would rewrite `f -2` to `f - 2` or refuse the
file.

**Stage 1: parser and messages** (Sonnet; it touches the parser and the
elaborator).

- `crates/syntax/src/parser.rs`: add `fn argument_minus_at(&self, i: usize)
  -> bool` next to `unit_call` and `section_at`, with the predicate from
  §4.2. In `starts_atom`, add `|| self.argument_minus_at(self.pos)`. In
  `atom` (or at the top of `app`'s argument loop), on an argument minus:
  consume it, read `self.atom(false)`, and return
  `Expr::Neg(operand, span, NegForm::Argument)`. In `ctor_args` (patterns),
  accept an argument minus followed by a numeral as `Pattern::NegNum`.
- `crates/syntax/src/ast.rs`: give `Expr::Neg` a third field (`bool` or a
  two-variant enum, `Operand` / `Argument`), or a module-level side table.
  Update the 28 uses, in `syntax`, `elab` (`check.rs`, `effects.rs`,
  `numbers.rs`, `ring.rs`, `autobind.rs`, `module.rs`, `nav.rs`) and
  `driver/tests/named_arguments.rs`.
- `crates/elab/src/check.rs`: in `not_a_function_hint` and the
  too-many-arguments path, when the argument is `Neg(_, _, Argument)`, add
  the D1467 note, naming the head as written. In `numbers.rs`, the mismatch
  on a function operand of an argument minus gets the "negates `g` alone"
  note.
- Tests:
  - `parser.rs` `prefix_minus_precedence`: change `f -x` to
    `(f (- x))` and `f -5` to `(f (- 5))`. Add `f -x.abs`,
    `f -2 * 3` → `(Mul (f (- 2)) 3)`, `f -g x` → `((f (- g)) x)`, `f 1 -2`,
    `f -(a * 2)`, `n-1` → `(Sub n 1)`, `n- 1` → `(Sub n 1)`, `n - 1`,
    `x - -y`, `[1, -2]`, `f --x` (a comment), `f -` at the end of a line
    (binary, parse error), the continuation-line case, and `f "a" -1`,
    `(f x) -1`, `xs.length -1`.
  - The pattern tests: `Some -1`, `Cons -1 rest`, `Some -x` (an error, as
    `(-x)` is today).
  - The recovery parser: a half-typed `f -` gives today's error.
  - `examples/accept/negative-arguments.sw`: `f -2`, `f -x`, `f -x.abs`,
    `g 1 -2`, `xs.map (x => clamp x -1 1)`, `Some -1` in a pattern, with
    `test`s that the values are right and `theorem`s that `f -2 = f (-2)` by
    `rfl`.
  - `examples/reject/negative-argument-not-a-function.sw` (`n -1`,
    `n: Nat`: `E-NOT-A-FUNCTION` and the note),
    `negative-argument-too-many.sw` (`g x -1` with `g` of one parameter),
    `negative-argument-function-operand.sw` (`f -g x`). Each has an
    `expect-error` line and a snapshot of the message.
  - A hash test that `def a: Int := f -2` and `def a: Int := f (-2)` give the
    same hash.
- Docs: docs/syntax.md:1114 (the `-e` row: replace "Not an argument …"),
  1115 and 94 (patterns), the operator sections paragraph (1368 is
  unchanged but should mention `f -1`), docs/guide/04-functions.md:128, and a
  pointer from docs/proposals/integers.md:704-708 to this note.

**Stage 2: formatter** (DeepSeek, from a precise spec; small).

- `crates/fmt/src/layout.rs` `roles`: an argument minus (the same predicate;
  it can be moved into `stitchwort_syntax` as a public function on
  `&[Token]`, so that parser and formatter can't drift apart) is
  `Role::Unary`.
- `crates/fmt/src/spacing.rs` `gap`: the gap before an argument minus is
  `Gap::Kept(spaced)`, which is always a space.
- Tests: a golden pair `crates/fmt/tests/golden/negative-arguments.{before,after}.sw`
  with `f -2`, `f   -x` (spaces collapse to one, the minus stays glued),
  `f (-2)` (kept), `n-1` → `n - 1`, `n -  1` → `n - 1`, and the continuation
  line. Extend the formatter fuzz test (`crates/fmt/tests/fuzz.rs`) to
  generate argument minuses. `fmt_repo.rs` should still pass with no file
  changes.

**Stage 3: `!` arguments** (D1465; DeepSeek).

- `parser.rs`: an argument `!` (the same spacing predicate) starts an atom,
  read as `prefix_op(true, …)` of one atom. Update `bang_precedence` and the
  syntax.md `!a` row ("not an argument …"). Add an accept example and a
  formatter golden case (`f !x` stays).

**Checks for every stage:** `task test:lane AREA=syntax` (and `elab`,
`fmt`), `task test:one` for the new tests, then the merge tier. Stage 1
also runs the daily tier's hash-stability check, which should show no
change: no existing definition's tree changes (§5).

## Sources

All fetched on 28 October 2026.

- Haskell 2010 Report, chapter 3 (§3.4 Operator applications, §3.5
  Sections): <https://www.haskell.org/onlinereport/haskell2010/haskellch3.html>
- GHC User's Guide, `LexicalNegation`:
  <https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/lexical_negation.html>
- GHC User's Guide, `NegativeLiterals`:
  <https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/negative_literals.html>
- GHC proposal #229, whitespace-sensitive operator parsing:
  <https://gh.ali360.cloudns.ch/ghc-proposals/ghc-proposals/blob/master/proposals/0229-whitespace-bang-patterns.rst>
- GHC proposal #344, Negative Literals Improved:
  <https://gh.ali360.cloudns.ch/ghc-proposals/ghc-proposals/blob/master/proposals/0344-negative-literals-improved.rst>
- GHC commit "Improve NegativeLiterals (#18022, GHC Proposal #344)", July 2020:
  <https://mail.haskell.org/pipermail/ghc-commits/2020-July/045069.html>
  (the issue tracker, gitlab.haskell.org, answered with a bot-protection page)
- OCaml manual, expressions: <https://ocaml.org/manual/5.2/expr.html>; lexical
  conventions: <https://ocaml.org/manual/5.2/lex.html>; `parsing/lexer.mll`
  and `parsing/parser.mly`: <https://gh.ali360.cloudns.ch/ocaml/ocaml/tree/trunk/parsing>
- F# language specification, lexical analysis ("Post-filtering of Adjacent
  Prefix Tokens") and basic grammar elements (precedence):
  <https://gh.ali360.cloudns.ch/fsharp/fslang-spec/tree/main/spec>
- dotnet/fsharp issue #13014, "Improve Error Reporting: help with ambiguity
  between subtraction and negation":
  <https://gh.ali360.cloudns.ch/dotnet/fsharp/issues/13014>; FS0003:
  <https://learn.microsoft.com/en-us/dotnet/fsharp/language-reference/compiler-messages/fs0003>
- Elm compiler, `compiler/src/Parse/Expression.hs`:
  <https://gh.ali360.cloudns.ch/elm/compiler/blob/master/compiler/src/Parse/Expression.hs>;
  Elm Discourse, "Weird edge case in the language syntax '1 - 2' /= '1 -2'":
  <https://discourse.elm-lang.org/t/weird-edge-case-in-the-language-syntax-1-2-1-2/2371>
- The Swift Programming Language, Lexical Structure (Operators, Integer
  Literals): <https://gh.ali360.cloudns.ch/swiftlang/swift-book/blob/main/TSPL.docc/ReferenceManual/LexicalStructure.md>
- Scala 2.13 specification, expressions (prefix operations) and syntax
  summary: <https://scala-lang.org/files/archive/spec/2.13/06-expressions.html>,
  <https://scala-lang.org/files/archive/spec/2.13/13-syntax-summary.html>
- Lean 4, `src/Init/Notation.lean`:
  <https://gh.ali360.cloudns.ch/leanprover/lean4/blob/master/src/Init/Notation.lean>;
  Zulip, "Unary/prefix minus precedence bug?":
  <https://leanprover-community.github.io/archive/stream/270676-lean4/topic/Unary.2Fprefix.20minus.20precedence.20bug.3F.html>
- Idris 2, `src/Idris/Parser.idr`, `libs/prelude/Prelude/Ops.idr`,
  `libs/prelude/Prelude/Num.idr`: <https://gh.ali360.cloudns.ch/idris-lang/Idris2>
- Agda, lexical structure and literal overloading:
  <https://agda.readthedocs.io/en/latest/language/lexical-structure.html>,
  <https://agda.readthedocs.io/en/latest/language/literal-overloading.html>
- The Koka book (identifiers, literals, operator expressions):
  <https://koka-lang.github.io/koka/doc/book.html>
- Roc, `crates/compiler/parse/src/expr.rs` at `alpha4-rolling`:
  <https://gh.ali360.cloudns.ch/roc-lang/roc/blob/alpha4-rolling/crates/compiler/parse/src/expr.rs>;
  new-compiler tutorial: <https://gh.ali360.cloudns.ch/roc-lang/roc/blob/main/docs/mini-tutorial-new-compiler.md>
- Gleam, `compiler-core/src/parse/lexer.rs`:
  <https://gh.ali360.cloudns.ch/gleam-lang/gleam/blob/main/compiler-core/src/parse/lexer.rs>
- PureScript, `src/Language/PureScript/CST/Parser.y`:
  <https://gh.ali360.cloudns.ch/purescript/purescript/blob/master/src/Language/PureScript/CST/Parser.y>
- MoonScript, "Considerations":
  <https://lalabuy948.gitbooks.io/moonscript/content/moonscript_-_the_language/considerations.html>
- Unison, literals: <https://www.unison-lang.org/docs/language-reference/literals/>
