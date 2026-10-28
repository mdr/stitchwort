# Review: negative arguments (SW-853)

An independent review of [negative-arguments.md](negative-arguments.md)
before it is implemented, 28 October 2026. It also covers two decisions Matt
made after the note was approved: **D1474** (a `-` glued to a numeral is part
of the number unless an operand comes right before it with no space, so
`-1.abs` is `(-1).abs`) and **D1468** (colour such a `-` as part of the
number in the editors).

Everything was checked at `a53a4cdc`, with `target/release/stitchwort` built
from it. The note says `82a79b30`. The files it cites are the same, and the
corpus counts below came out the same. Test files were in a scratch
directory and are not committed.

The findings are ranked by severity. Each one says whether the note should
change before a lane starts.

## Summary

The choice of option (b) holds up. The corpus claim is right: no tracked
`.sw` file has an argument minus, and the two parser test cases are the only
code that asserts today's rule. Six things need fixing first:

1. The rule as written ignores block statements. A block line that starts
   with `-y` is valid today, and a literal implementation of §8 would make it
   an argument of the line above (finding 1).
2. With D1474, "no program can change meaning silently" is no longer true for
   `Float` literals: `-2.5.floor` checks today and gives `-2.0`, and under
   D1474 it gives `-3.0` (finding 2).
3. Stage 1 can't merge on its own, and two formatter rules that are harmless
   today would make the formatter refuse files after the change (finding 3).
4. §8 has no plan for D1474 (finding 4).
5. The D1467 note can't quote the head "as written", because the elaborator
   has no source text. "Too many arguments" is really two error sites
   (finding 5).
6. The regex suggested for D1468 misses several cases (finding 6).

## Findings

### 1. High: a `-` that starts a block statement is not an argument

**Problem.** The predicate in §4.2 reads raw tokens and counts a line break
as a space. §8 says to add `|| self.argument_minus_at(self.pos)` to
`starts_atom`. But a line at the block's column is a new statement, not a
continuation. The parser knows this only through `peek()`, which returns
`None` at a stop (`is_stop`, `parser.rs:654-672`; `peek`, `parser.rs:715-720`).
`section_at` is safe because its caller first checks
`self.peek() == Some(&Tok::Dot)` (`parser.rs:3300-3309`, `3333`). The new
predicate has no such guard.

**Evidence.** This program checks and passes today:

```
def f (x: Int): Int :=
  let y := x + 1
  -y

test "block line starting with minus" := f 1 == -2
```

`stitchwort test e.sw` gives "✓ block line starting with minus … 1 passed".
Here `-y` comes after a closing token (`1`), has a line break before it and
touches `y`, so the §4.2 predicate calls it an argument minus. Implemented
literally, `-y` becomes `x + 1 (-y)`, and the block is left with no result.

The corpus has the same shape for `!`, which matters for stage 3:
`examples/accept/terminal-ops.sw:58-59` is `let c := Pair.snd (…)` followed
by a line `!c.inputIsTerminal && …` at the block's column. My token scan (see
finding 9) finds this one `!` case and no `-` case.

**Change the note: yes.**

- §4.2: the predicate applies only when `peek()` returns the `-`, that is,
  not at a stop (block column, `calc` step, rewrite-rule end).
- D1469: say "a *continuation* line". A line at the block's column stays a
  statement.
- §8: say this in stage 1 and stage 3, and add tests: a block line `-y`
  stays the block's result, and an indented `-y` under the same line is an
  argument.

The formatter needs no rule for this, because its gaps are only between
tokens on one line. But the shared token-level predicate that stage 2
suggests can't see block columns. So it can't be the parser's whole rule:
the parser adds the stop check on top of it.

### 2. High: D1474 allows silent changes for `Float` literals

**Problem.** §1 (reason 2), §4.2 ("No silent changes") and §6 (reason 2)
say that under one of the two readings the program fails to check. That
argument is about application against subtraction. D1474 changes something
else, `-(N.f)` against `(-N).f`, and both can check.

**Evidence.**

```
import Std (Float)
def today: Float := -2.5.floor
def bracketed: Float := (-2.5).floor
def absToday: Float := -2.5.abs
test "today: -2.5.floor is -(2.5.floor)" := today == -2.0
test "(-2.5).floor" := bracketed == -3.0
test "today: -2.5.abs is -(2.5.abs)" := absToday == -2.5
```

All three tests pass today. Under D1474, `today` becomes `-3.0` and
`absToday` becomes `2.5`, and both still check. `Float.floor`, `ceil`,
`round` and `abs` are at `crates/elab/src/std/Float/Float.sw:190, 237-243`.

Integer numerals are safe as far as I found. A numeral used as a receiver
defaults to `Nat`, and negating the result fails today. `-7.mod 2` and
`-3.sub 5` give "expected `Int`, but this has type `Nat`", and `-5.natAbs`
gives E-UNKNOWN-FIELD.

**Corpus.** No change. `git grep -nE -- "-[0-9][0-9]*(\.[0-9]+)?([eE][+-]?[0-9]+)?\.[A-Za-z_]" -- '*.sw'`,
with comment lines removed, finds nothing. A spaced `- N.f` doesn't occur
either. The only bracketed form is `(-0e-400).bits`
(`examples/accept/float-literals.sw:14`), and its meaning doesn't change.
That confirms Matt's grep.

**Change the note: yes.** Limit the guarantee to argument minus, and add a
sentence saying that D1474 changes the meaning of `-<float>.f` and that the
corpus has no case of it. Add the `Float` case to the tests. See D1491.

### 3. Medium: the stage boundaries and two formatter rules

**(a) Stage 1 can't merge alone.** Stage 1 adds
`examples/accept/negative-arguments.sw`. `crates/cli/tests/fmt_repo.rs`
fails for any tracked file outside `examples/reject/` and the other excluded
paths that the formatter would change *or refuse*
(`Err(e) => unformatted.push(… "refused" …)`). Before stage 2, the formatter
writes `f -2` as `f - 2` (role `Binary`, `layout.rs:178-197`), which under
the new parser is a different tree. So the check refuses the file and
`fmt_repo` fails. "Or 2 right after 1" would leave `main` failing the merge
tier in between.

Stage 2 can safely land *first*. A formatter that keeps `f -2` as written
produces the same tokens and today's tree. Recommendation: one lane for
stages 1 and 2, or stage 2 first. See D1492.

**(b) The formatter glues a spaced binary minus at the start of a line.**
For a `-` at the start of a line, `roles` uses `t.column > prev_line_col`
(`layout.rs:186-189`), not the parser's block column. Today:

```
def w (x: Int) (y: Int): Int :=
  add
      x
    - y
```

`stitchwort fmt` rewrites `    - y` to `    -y`. Today the meaning is the
same. Under (b), `-y` is an argument minus: the tree check fails and the
file is refused. Stage 2 must not glue a line-start `-` that has a space
after it and comes after an operand. Keep that gap (`Kept`), or classify it
as `Binary`.

**(c) The formatter glues `- 1.abs` into `-1.abs`.** With D1474 those two
mean different things. The golden test shows that the formatter glues every
prefix minus: `crates/fmt/tests/golden/unary-minus.before.sw` has `-   x`
and `- 2`, which become `-x` and `-2` (`spacing.rs` `gap`, the `Unary` arm
`Gap::Rule(*right == Minus)`). Stage 2 needs a `Kept` gap after a prefix
minus when the next tokens are a numeral and a glued `.`.

**Change the note: yes** (§8 stage order, and stage 2 items (b) and (c) with
golden cases).

### 4. Medium: §8 has no plan for D1474

These need to be written down:

- **Where.** The numeral is an atom, so in `unary` a `-` glued to
  `Num`/`Float` has to produce `Neg(Num)` as the *base* of `atom`'s
  field/`()` loop (`parser.rs:3380-3420`), and not
  `prefix_op(…, self.unary())`. The argument-minus path needs the same base
  when the next token is a numeral. `add_expr` already takes the tight `x-1`
  before `unary` sees it, so `x-1.abs` stays `x - (1.abs)` with no extra
  check. The lexer can't simply merge `-1` into one token: the formatter's
  `- -x` rule (`spacing.rs`, `Gap::Rule(*right == Minus)`) would then join
  `- -1` into the comment `--1`.
- **What it covers.** If the numeral is an atom, then `-3.sub 5` is
  `(-3).sub 5` (`-8`), and `-1.add 2` is `1`. Both are type errors today.
  D1474's wording only covers `.abs` with no arguments. See D1490.
- **Lexer interactions** (`lexer.rs:428-462`):
  - `-1.5` is one `Float`, so `-1.5.abs` is `(-1.5).abs`.
  - `-1.0` is a `Float`, not `1` and `.0`.
  - `1e-5` has no `Minus` token.
  - A number after a `.` is digits only (`xs.0.1`), so `-1.0.1` is
    `(-1.0).1`.
  - `--1` is still a comment.
  - In `- -1.abs`, the inner `-1` is a number: `-((-1).abs)`.
  - `x - -1.abs` is `x - ((-1).abs)`.
- **Patterns.** No change: `(-k)` and `Some -1` take a numeral only
  (`parser.rs:947-956`).
- **Docs.** syntax.md:1114 (the `-e` row: "`-x.abs` is `-(x.abs)`" stays
  true, but the row needs "`-1.abs` is `(-1).abs`"), the numeric-literals row
  (`-5`), and docs/guide/04-functions.md.
- **Tests.**
  - Parser cases: `-1.abs` → `(- 1).abs`, `f -1.abs`, `x-1.abs`,
    `- 1.abs`, `-x.abs` (unchanged), `-1.5.abs`, `- -1.abs`, `(-0e-400).bits`.
  - An accept example with `-5.natAbs` (today E-UNKNOWN-FIELD) and the
    `Float` case from finding 2.

**Other languages, for D1474.** The ones that have method dots read `-1.f`
as `-(1.f)`, and two of them warn about it:

- **Rust.** rustc's `ambiguous_negative_literals` lint (allow by default)
  says "`-` has lower precedence than method calls, which might be
  unexpected", with "e.g. `-4.abs()` equals `-4`; while `(-4).abs()` equals
  `4`" **[cited: rustc lint listing, allowed-by-default]**.
- **Kotlin.** "`-1.inc()` evaluates to `-2` and not `0` as it might be
  expected", and JetBrains has an inspection whose quick fix adds the
  brackets **[cited: Inspectopedia WrapUnaryOperator; search summary, page
  not opened]**.
- **Swift.** `print(-1.f())` is parsed as `print(-(1.f()))`, the forum
  replied that this is intended, and the book has "`-42.trailingZeroBitCount
  // -1`" **[cited: Swift Forums thread 57984]**.
- **F#.** The spec merges `-` with an adjacent numeric literal, so `(-1)`
  is the receiver **[inferred from the spec text the note quotes; not
  run]**.
- **Haskell and Elm.** They have no method dot on a literal, so the question
  doesn't arise.

So D1474 goes against Rust, Kotlin and Swift. But those languages lint the
reading D1474 rejects, which supports the choice.

The decision also brings back a split based on what kind of token follows,
the kind the note criticised in option (c) (§4.3): `f -1.abs` is
`f ((-1).abs)`, while `f -x.abs` is `f (-(x.abs))`. The docs should say so
in one line.

**Change the note: yes.** Add D1474 to §6, §7 and §8, and a survey row.

### 5. Medium: D1467's notes don't have the information they assume

- **No head text.** The elaborator has no source text. `SourceMap` appears
  only in its tests (`grep -rn SourceMap crates/elab/src`). The existing hint
  can name the head only when it is a definition or a variable
  (`called_name`, `check.rs:2197-2203`). For `xs.length -1`, `g x -1` and
  `(f x) -1`, "to subtract, write `n - 1`" can't quote the head. The
  argument is available as `value: &Expr` (`check.rs:1887`), so the flag can
  be read and a numeral operand can be printed. Suggested wording: "`-1`
  here is a negative argument (a space before the `-`, none after); to
  subtract, put a space after the `-` as well."
- **Two error sites, not a too-many-arguments path.** For a definition, an
  extra argument is the same E-NOT-A-FUNCTION from `function_parts`
  (`check.rs:2533`). `g x (-1)` with `g: Int -> Int` gives "this isn't a
  function … its type is `Int`". A constructor has its own error, "`Some`
  takes 1 argument(s) … it's given 2" (`check.rs:1615`), which
  `not_a_function_hint` never sees. The pipe case `x |> g -1` goes through
  `function_parts` (checked).
- The `-g` mismatch (item 4) is raised while elaborating the `Neg` itself,
  so the flag is available there.

**Change the note: yes.** Fix the wording in §4.2 and §7 (D1467), and in §8
name both sites and add a reject example for `Some 5 -1`.

### 6. Low to medium: the D1468 regex

The note suggests `(?<=[\s(\[,])-[0-9]+`. Under (b) with D1474, a `-`
glued to a numeral is part of the number unless a closing character touches
it on the left. Against that rule, the regex:

- **misses** a `-` after an operator or keyword with no space: `x*-1`,
  `x==-1`, `:=-1`, `=>-1`, `{x = …}` written `{-1`, and `${-1}` in an
  interpolation. The parser reads all of these as negative numbers.
- **misses** `-1` at column 0. TextMate matches one line at a time, so a
  lookbehind for `\s` fails at the start of the line.
- **cuts floats short.** `-1.5` and `-1e3` colour only `-1`. The existing
  number rule `\b[0-9]+\b` (`stitchwort.tmLanguage.json:110`) already splits
  `1.5`.
- **is right** for `x-1` (not coloured), `f -1`, `x - -1`, `[-1` and
  `(-1`. `--1` stays a comment, because the comment rule matches from the
  first `-`.

A negative lookbehind matches the rule more closely:

```
(?<![A-Za-z0-9_')\]}"])-[0-9]+(?:\.[0-9]+)?(?:[eE][+-]?[0-9]+)?
```

Its one known error is a keyword glued to the minus, such as `then-1`: the
`n` before it blocks the match, though the parser reads a negative number.
That is rare, and `stitchwort fmt` adds the space.

The playground's tokenizer (`web/index.html:2300-2420`) scans left to right
and knows the previous token and whether it touches. So it can apply the
rule exactly, with no regex. Also, the note's reason for recommending
against D1468 ("a highlighter regex can't see whether a closing token comes
before it") is weaker than it says: the rule depends only on the character
right before the `-`.

**Change the note: yes** (§4.2 Highlighters and D1468). The task can be
small and go with stage 2 or later.

### 7. Low: the closing and opening token lists disagree

- The note's closing tokens (§4) include `?` and leave out `cases`.
- The formatter's `ends_operand` (`layout.rs:128-149`) includes `KwCases`
  and leaves out `Question`.
- `starts_atom` (`parser.rs:3310-3334`) also starts an atom at `include`, at
  a bare `cases` and at a method section `.name`.

In the parser the closing-token test is redundant, since the predicate is
only reached after an atom. In the formatter it is the whole test. The
shared function that stage 2 proposes should be the single list, with `?`
and `cases` in it. The note also says it follows GHC #229, but #229 counts
keywords as closing tokens ("Closing non-terminals include identifiers,
keywords, literals, and closing brackets" **[cited: proposal 0229]**).
Stitchwort decides by "comes after an atom", which is better, and the note
should say it differs.

**Change the note: a sentence.**

### 8. Low: test cases to add to §8

Each of these has a meaning worth pinning down:

- `(.fst -1)`. Today it is `x => x.fst - 1`: a section that starts an
  expression takes the operators after it (D1192, syntax.md ~1350). Under
  (b) it is `x => x.fst (-1)`. The docs should mention it next to
  `(.fst + 1)`.
- `xs |> .drop -1`, which becomes `xs.drop (-1)`, and `x |> f -1`, which
  becomes `f x (-1)`.
- `(let x := f -1; x)` (SW-788): the `;` is not a closing token, so
  `(let x := 1; -x)` stays prefix.
- `"${n -1}"`: the interpolation is tokenized, so this becomes `n (-1)`.
  It checks today.
- `f() -1`, which becomes `(f()) (-1)`, and `f -()`.
- `Some 5 -1` in an expression (the constructor error site, finding 5).
- Block cases (finding 1). Formatter cases from finding 3 (b) and (c).

### 9. Low: factual checks and small slips

These are correct as stated:

- **Corpus.** I re-ran the scan with my own program built against
  `crates/syntax`. Of 1,786 files, the same 6 don't lex. Loose minus after
  an operand: 1,089 (718 + 371). Argument minus: 0. Tight: 1. Line-start
  loose: 2.
- **Outside `.sw` files.** No Stitchwort argument minus in fenced code
  blocks in `*.md`, `web/`, `editors/`, or Rust strings, apart from
  `parser.rs:5253, 5262`.
- **§2.** Every row of the "What users see today" table I ran matches.
- `Expr::Neg` has 28 uses in 10 files.
- `-` arithmetic is only `Nat`/`Int`/`Float`. `numbers.rs` has three kinds,
  and `Add`/`Mul` are the only arithmetic interfaces
  (`std/core/AddMul.sw`), with no `Sub`.
- **GHC claims.** `LexicalNegation`'s "any syntactically atomic expression",
  "`-a % b` is `(-a) % b`", and `(- x)` as a section **[cited: GHC user's
  guide]**.

These are slips:

- docs/syntax.md:19 should be :20.
- The AoC notes record the mistake twice, not once: Day 14 also has "`f a -1`
  is `f a - 1`, as in Haskell; `(-1)` needed" (aoc/NOTES-2024.md:4222).
- §4.2 says a left operand whose type is unknown "could be solved either
  way". In my tests the new reading failed:
  `useFn (x => x (-1))` gives "expected `?1`, but this has type `?5 (-1)`",
  while `useFn (x => x -1)` checks today, and the reverse holds when
  `a := Int -> Int` is given. So the claim holds, and the hedge can be
  narrower.

**Change the note: optional.**

## Questions for Matt

- **D1490.** Under D1474, a negative numeral is one atom everywhere,
  including as the receiver of a dot call with arguments: `-3.sub 5` is
  `(-3).sub 5` (`-8`), and `-1.add 2` is `1`. Both are type errors today.
  **[rec: yes, the numeral is an atom. Say so in syntax.md.]**
- **D1491.** Accept that D1474 silently changes `-<float>.f`
  (`-2.5.floor`: `-2.0` → `-3.0`; `-2.5.abs`: `-2.5` → `2.5`), given that the
  corpus has no case of it? **[rec: yes. State it in the note and syntax.md
  and add the tests; no warning.]**
- **D1492.** Stage order: build stages 1 and 2 in one lane, or merge the
  formatter (stage 2) first. Stage 1 alone fails `fmt_repo`.
  **[rec: one lane, Sonnet.]**

## Sources

Fetched or searched on 28 October 2026.

- GHC User's Guide, `LexicalNegation`:
  <https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/lexical_negation.html>
- GHC proposal #229:
  <https://gh.ali360.cloudns.ch/ghc-proposals/ghc-proposals/blob/master/proposals/0229-whitespace-bang-patterns.rst>
- rustc lints, allowed by default (`ambiguous_negative_literals`):
  <https://doc.rust-lang.org/rustc/lints/listing/allowed-by-default.html>
- Swift Forums, "abs(_:) returns negative numbers in Int extension":
  <https://forums.swift.org/t/solved-abs-returns-negative-numbers-in-int-extension/57984>
- JetBrains Inspectopedia, WrapUnaryOperator (Kotlin), from a search
  summary: <https://www.jetbrains.com.cn/en-us/help/inspectopedia/WrapUnaryOperator.html>;
  Kotlin forum, "-1.plus(2) == -3": <https://discuss.kotlinlang.org/t/1-plus-2-3/2182>
