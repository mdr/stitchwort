# The formatter's style sheet

**Status:** stage 0 of [formatter-architecture.md](formatter-architecture.md)
§6, 13 November 2026 (SW-3158). Paper lane: nothing is built. It stops for
Matt's sign-off on the samples and for four decisions,
[D3564–D3567](#4-decisions-for-matt).

**What is already decided** (Matt, 13 November 2026). The formatter chooses
every line break from the code's structure, with a Wadler/Prettier document
engine and the 120-column width of D1014 (D3558). Authors keep only their
blank lines; there are no other hints (D3560a). A pipeline that fits on one
line stays there, and otherwise has one stage per line (D3560b). The
formatter works from a lossless tree (D3562). The decisions of
[formatter.md](formatter.md) §8 that are not about line breaks stand:
no options (D1015), no alignment (D1016), D1012/D1017 comma brackets,
closers of comma-less brackets piled up (D1018), blank-line runs collapsed
and none added (D1020), tight effect rows (D1037), `decreasing` lines as
header continuations (D1038). So do the newer token rules: `∀` before a
theorem's explicit parameters (D3472), `:= match` on the header line when
it fits (D3553), and redundant brackets dropped (D2307).

Claims are marked **[measured]** (a script over the 1,724 tracked `.sw`
files outside `examples/reject`, `examples/soundness`,
`examples/projects/reject` and the formatter's test data, at `051b6f58b`;
pattern-based, so counts are approximate),
**[probe]** (through the release binary's `fmt`, see
[Appendix](#appendix-the-probes)) or **[estimated]**. Every "before" below
is real code from the repo, cited by file and line; every "after" is
**hand-written under the rule** (no formatter produces it yet). Each after
parses, and has the same tokens as its before except where a rule says it
changes them [probe].

## In plain words: the house style

**One layout for each piece of code.** Whoever wrote it and however they
broke the lines, the formatter prints it the same way. The author's blank
lines are the only thing it keeps.

**Fit or break.** Every construct is first tried on one line. If it fits in
120 characters, it stays there. If not, it breaks in its standard way, and
the pieces inside it get the same choice in turn, outside in. Width is
counted in characters, so `∀` and `→` count one each.

**How things break:**

- *Declarations*: the header on one line if it fits. Otherwise its
  parameters continue on lines indented 4, and the result type or
  conclusion gets its own line, also at 4. The body goes after `:=` if the
  whole thing fits, otherwise on the next line at 2.
- *Theorem headers* (D3564): the variables share the first line; each
  premise (a parameter whose type is visibly a statement, such as `h: a ≤
  b`) gets a line of its own; then the conclusion. This is Matt's sketch,
  recommended in D3564.
- *Arms*: a `match`, a definition's equations, a data type's constructors
  and a handler's clauses always put each alternative on its own line once
  there are two or more (recommended in D3566). An arm's body follows `=>` if it fits,
  otherwise it goes below at 2.
- *Calls* (recommended in D3567): when a call doesn't fit, its simple arguments (names,
  numbers) stay on the function's line and each bracketed argument gets its
  own line at 2. A last argument that is a lambda, a list or a record stays
  on the line and opens downwards, as `xs.map (x =>` does today.
- *Operators*: a long chain breaks before each operator of its loosest
  level, `&&`, `∧`, `→`, `=` or `|>` starting the continuation lines at 2.
- *Brackets with commas* (lists, records, tuples, imports): all on one line,
  or one item per line with the closer on its own line (D1012 as now).
- *`if`*: one line if it fits; otherwise `if c then a` / `else if d then b`
  / `else e`, one clause a line, as most code here already is.
- *Proofs*: a `calc` step is `_ = e := proof` on one line if it fits,
  otherwise the proof goes below. A `rewrite` that doesn't fit puts each
  rule on its own line, `in` at the end of the last one, and what it proves
  below.

**What never changes:** comments and their text, strings (never split),
text blocks (moved as one piece), the order of everything, and the meaning:
the formatter checks its output parses to the same tree, and leaves a
declaration as written if it can't.

**Spacing and indentation stay as today:** steps of 2 (4 for header lines),
`x: T` with no space before the colon, `{ a = 1 }` but `{IO}`, `f()` for a
unit call, one space around operators, no alignment.

**What changes most** ([§3](#3-what-changes-most)): theorem headers (4,300
of the 8,760 are over 120 today), long lines in general (8,200 lines over
120), and, depending on D3565, merging `(a: Nat) (b: Nat)` into `(a b:
Nat)` (about 4,500 places).

**The four questions** ([§4](#4-decisions-for-matt)): D3564, the shape of a
long theorem header; D3565, whether the formatter merges parameters of the
same type; D3566, whether alternatives (`|`) always go one per line; D3567,
how a call that doesn't fit breaks. The rest I've settled, saying why.

## 1. The engine, in five rules

These hold everywhere; the per-construct rules in §2 only say where a
construct's break points are and how far each piece is indented.

**E1. Groups.** Each construct is a *group*: a list of pieces with places
it may break. A group goes on one line if the whole of it, plus whatever
must follow it on the same line (a closing bracket, a `,`, a `:=`), fits
within 120 characters from where it starts. Otherwise *every* break point
of that group breaks (Wadler's rule), and each inner group decides again
for itself. Outer groups break first.

**E2. Indentation.** A piece that moves to a new line is indented 2 from
the line its construct starts on: bodies, arms, arguments, operator
continuations, pipeline stages, `calc` steps, list items. Two exceptions,
both at 4: a declaration's header lines (parameters, conclusion,
`decreasing`), and a `rewrite`'s rule lines, so they stand apart from the
body at 2 below them. A comma bracket's closer goes at the indentation of
the line its opener is on (D1012).

**E3. Hard breaks.** Some breaks happen whatever the width: a comment (it
ends its line), a blank line the author kept, a block of two or more
statements, a text block, two or more alternatives under D3566, and
`decreasing`. A group containing a hard break is broken.

**E4. Blank lines.** Kept, as one, between items of a vertical list:
declarations, statements, arms, constructors, fields, list items, `calc`
steps. A kept blank line is a hard break, so it keeps its list vertical
(the one hint authors have). Dropped elsewhere: at the start or end of a
body, and inside an expression. Never added (D1020).

**E5. What can't fit stays long.** A string, a name or a comment is never
split. A line that is still over 120 once everything around it has broken
is left long; it is not an error. About 770 of today's over-long lines hold
a string [measured]; 12 hold a string too long to fit even on a line of its
own [measured].

**Width is in characters** (Unicode code points), not bytes as the current
formatter's `:= match` rule counts. The operators `∀ → ≤ ∧` are one
character on screen and three bytes; counting bytes would break proof
headers 5–10 characters early: 8,217 code lines are over 120 characters,
but 8,718 are over 120 bytes [measured]. All of Stitchwort's spellings are
one column wide (D1200), and tabs are not allowed, so characters are
columns.

## 2. The rules, construct by construct

Rules are numbered S1–S40 for review comments. "Settled" means I decided
it; the reason follows. The four marked **D35xx** are Matt's.

### 2.1 Files, namespaces and imports

**S1. File head.** `namespace` is the first line after any leading
comments; imports follow with no blank line between them, then one blank
line (R19, unchanged). Imports keep their order (the formatter never sorts).

**S2. An import list** is a comma bracket: one line if it fits, otherwise
one item per line with the closer at column 0 (D1012). Settled: it is what
D1012 already says for brackets, and only 9 import lines are over 120
[measured].

Before (`aoc/src/Aoc/Year2020/Day19/Proofs/ParseComplete.sw:6`):

```text
namespace Aoc.Year2020.Day19.Proofs
import Aoc.Year2020.Day19 (..)
import Aoc.Year2020.Day19.Spec (LetterWritten, LineBreakWritten, MessageWritten, NumberedWritten, NumberWritten, ReceivedWritten, RuleWritten, SequenceWritten)
import Std (Bool, Char, DecEq, Eq, Exists, Fail, List, NonEmptyList, Parse, Result, Text, Void)
```

After:

```text
namespace Aoc.Year2020.Day19.Proofs
import Aoc.Year2020.Day19 (..)
import Aoc.Year2020.Day19.Spec (
  LetterWritten,
  LineBreakWritten,
  MessageWritten,
  NumberedWritten,
  NumberWritten,
  ReceivedWritten,
  RuleWritten,
  SequenceWritten
)
import Std (Bool, Char, DecEq, Eq, Exists, Fail, List, NonEmptyList, Parse, Result, Text, Void)
```

**S3. Sections.** The language has no `section … end`; a namespace is per
file. Nothing to rule.

### 2.2 Doc comments and attributes

**S4. Doc comments** (`--|` runs and the `--` lines above a declaration)
move with the declaration they sit on, unchanged, never re-wrapped (as
today). A blank line between a comment and the code keeps them apart.

**S5. Attributes** `@[…]` above a declaration stay on their own line
(a hard break); an attribute before a field or a constructor stays in front
of it on the same line. Spacing inside follows the usual rules. Settled: the
current rule (R15); 302 own-line attributes and 5 inline ones [measured].

An inline attribute doesn't stop a record from joining: before
(`examples/extract/attributes.sw:43`):

```text
type Drawing = {
  @[js.name "type"] kind: Text,
  @[js.name "items"] shapes: List Shape
}
```

After:

```text
type Drawing = { @[js.name "type"] kind: Text, @[js.name "items"] shapes: List Shape }
```

### 2.3 Declaration headers

**S6. The header group.** `def`, `theorem`, `instance`, `test` and their
`export`/`opaque` forms: name, parameters, `:`, result type or conclusion.
If the header fits on one line, it is one line. If not, it breaks as S7
(definitions) or S8 (theorems), and the result type or conclusion goes on a
line of its own at 4, ending with `:=`. A broken header never takes its body
on its last line: the body starts below at 2, so it stands out from the
header lines at 4 (also a `match`: D3553's "on the header line" means a
one-line header). Settled: Matt's sketch shows the conclusion on its own
line; and a body joined to the end of a long conclusion is hard to find.

**S7. A definition's parameters** fill the lines at 4: as many as fit on
each line. Settled: only 107 definition headers are over 120 [measured],
almost all with plain parameters; D3564's premise rule applies to them too
when they have premises (`(h: i < n)`), so there is one rule for headers.

**S8. A theorem's parameters: D3564.** See [§4](#d3564-the-shape-of-a-long-theorem-header).
Recommended: the first line has the name, `∀` and the leading variables;
each premise gets a line of its own at 4; variables between premises
share a line; the conclusion follows at 4. The samples are in §4.

**S9. Parameter groups: D3565.** Whether `(a: Nat) (b: Nat)` becomes `(a b:
Nat)`. See [§4](#d3565-merging-parameters-of-the-same-type).

**S10. Function types in a signature** (`def f: A → B → C`): a chain of
`→`, broken before each arrow (S27), lines at 4 since they are header lines.

Before (`crates/elab/src/std/core/Builtins.sw:28`):

```text
def J: [a: Type] → [x y: a] → (motive: (y': a) → x = y' → Type) → (base: motive x rfl) → (p: x = y) → motive y p
```

After, if it didn't fit:

```text
def J: [a: Type]
    → [x y: a]
    → (motive: (y': a) → x = y' → Type)
    → (base: motive x rfl)
    → (p: x = y)
    → motive y p
```

(As written it is 112 characters, so it fits and stays one line; the
after shows the shape it breaks to. Today's formatter puts these lines at
2, as continuations; S6 puts every header line at 4.)

**S11. `decreasing`.** A header with `decreasing` always breaks: the
measure on its own line at 4, then `:=` alone at column 0, then the body
(R21, D1038). Settled: it is how `docs/syntax.md` teaches it and how 77
sites are written; 2 sites put `:=` at the end of the `decreasing` line
[measured] and change.

Before and after (`aoc/src/Aoc/Year2020/Day09/Day09.sw:61`): unchanged.

```text
def runFrom (target: Nat) (front: List Nat) (count: Nat) (sum: Nat) (rest: List Nat): Option (List Nat)
    decreasing front.length + rest.length
:=
  if target < sum then
    match front with
      | [] => None
      | [first, ..later] => runFrom target later (count - 1) (sum - first) rest
  else if sum == target && 2 <= count then Some (front.take count)
  else
    match rest with
      | [] => None
      | [next, ..more] => runFrom target front (count + 1) (sum + next) more
```

### 2.4 Bodies

**S12. `:=` body.** The body goes after `:=` on the header line if the
whole declaration fits there. Otherwise it goes on the next line at 2, and
breaks inside as its own rules say. Exceptions that open on the `:=` line
whatever follows, as long as their first line fits there: a `match … with`
(D3553), a `calc e0` (settled: the same rule as `match`, for the same
reason), a comma bracket (D1012's opener at the end of the line before), a
text block's `"""`, and a last-argument "hug" (S23). A block of two or
more statements always starts below.

Settled, against "a theorem's proof always starts on its own line": one
rule for all declarations, and 2,891 theorems already have their proof on
the header line [measured]. About 450 one-line bodies written below the
header would join it [measured: 202 definitions, 116 theorems, 95 tests,
38 instances].

Joins. Before (`aoc/src/Aoc/Year2020/Day04/Spec/Spec.sw:32`):

```text
def year (low: Nat) (high: Nat) (value: Text): Bool :=
  digits 4 value ∧ low <= number value.toList <= high
```

After:

```text
def year (low: Nat) (high: Nat) (value: Text): Bool := digits 4 value ∧ low <= number value.toList <= high
```

Breaks. Before (`aoc/src/Aoc/Year2020/Day09/Day09.sw:77`, 121 characters):

```text
def XmasData.runSumming (data: XmasData) (target: Nat): Option (List Nat) := runFrom target data.numbers 0 0 data.numbers
```

After:

```text
def XmasData.runSumming (data: XmasData) (target: Nat): Option (List Nat) :=
  runFrom target data.numbers 0 0 data.numbers
```

**S13. `instance` and `test`** follow S12 exactly. A `test`'s name is a
string and never splits, so a long name pushes the body below.

Before (`aoc/src/Aoc/Common/Tests/Grid.sw:42-47`):

```text
test "parse a grid" := parsedGrid """
  123
  456
  """ == Ok small
test "parse a short row" := parsedGrid "123\n45\n" == Err "line 2: expected 3 cells, as on the first line, got 2"
test "parse a letter" := parsedGrid "123\n4x6\n" == Err "line 2, column 2: expected a digit or the end of the line, got 'x'"
```

After (the third test is 124 characters):

```text
test "parse a grid" := parsedGrid """
  123
  456
  """ == Ok small
test "parse a short row" := parsedGrid "123\n45\n" == Err "line 2: expected 3 cells, as on the first line, got 2"
test "parse a letter" :=
  parsedGrid "123\n4x6\n" == Err "line 2, column 2: expected a digit or the end of the line, got 'x'"
```

An instance written over two lines that fits on one joins
(`crates/elab/src/std/core/DecEq.sw:35`, 114 characters joined):

```text
instance List.instDecEq [auto decEq: DecEq a]: DecEq (List a) := { decide = List.decEq (x y => DecEq.decide x y) }
```

### 2.5 Data types, records, interfaces, abilities

**S14. Constructors: D3566 (b), Matt, 13 Nov 2026.** A data type's
constructors fit or break like a record's fields: on one line if the whole
declaration fits (`type Direction = | Up | Right | Down | Left`), otherwise
one per line at 2, each with its `|`. Fields of a constructor stay on its
line, breaking like a header's parameters (at 4) if one is too long. Arms
are different: two or more always go one per line (S16 onwards, D3566).

Before (`aoc/src/Aoc/Common/Grid.sw:22`, four lines today):

```text
type Direction =
  | Up
  | Right
  | Down
  | Left
```

After:

```text
type Direction = | Up | Right | Down | Left
```

**S15. Record types and interfaces** (`{ name: T, … }`) are comma brackets:
one line if they fit, otherwise one field per line (D1012). A doc comment
on a field is a hard break, so a documented record stays open. Settled,
against "records always open": 558 record types are already written on one
line and 42 open [measured], so fit-or-break keeps nearly all of them as
they are; 24 of the 42 would join.

Joins. Before (`crates/elab/src/std/core/IO.sw:12`):

```text
type Console = {
  inputIsTerminal: Bool,
  outputIsTerminal: Bool,
  columns: Nat,
  rows: Nat
}
```

After:

```text
type Console = { inputIsTerminal: Bool, outputIsTerminal: Bool, columns: Nat, rows: Nat }
```

Stays open because of its doc comments (`aoc/src/Aoc/Common/Plane.sw:29`):
unchanged.

```text
interface Frame (f: Type) = {
  --| `1` if `y` grows up the page, `-1` if it grows down.
  up: Int,
  --| The sign squares to 1.
  unit: up * up = 1
}
```

**S16. Abilities** (`ability IO where` and its operations): one operation
per line at 2, always, as a declaration list (a hard break, like
constructors). Trailing comments stay on their operation's line
(`crates/elab/src/std/core/IO.sw:24`, unchanged). Type synonyms (`type
Grid = List (List Nat)`) are a header and a type: S6 and S27.

### 2.6 Blocks, `let` and local definitions

**S17. Blocks.** Each statement on its own line at the block's column (a
hard break: a block of two or more statements never joins). A `let`'s
value follows `:=` if it fits, otherwise goes below at 2, with S12's
exceptions (a `match`, `calc`, comma bracket, text block or hug stays on
the line). Local `def`s and `theorem`s follow the top-level rules,
indented. Settled: unchanged from today.

Before and after (`aoc/src/Aoc/Year2020/Day09/Day09.sw:22`): unchanged;
the last line is 107 characters, and the interpolation inside it is never
broken (S32).

```text
def main(): {IO, Fail} () :=
  let data := parseData IO.readAll()
  let invalid := data.firstInvalid (preamble := 25) |> .orFail "every number is the sum of two before it"
  IO.print "Part 1: ${invalid}"
  IO.print "Part 2: ${data.weakness invalid |> .orFail "no run of two or more numbers sums to ${invalid}"}"
```

**S18. Expression `let` and sequences** (`(let x := e; body)`, `(a; b)`):
printed on one line. If one doesn't fit, it breaks after each `;`, the
parts lined up one column inside the bracket. Settled: 15 expression `let`s
and a handful of sequences in the repo [measured], none long enough to
matter; the `;` can't become a line break (that changes tokens), so this
is the only shape available.

### 2.7 `if`

**S19. `if`.** One line if it fits. Otherwise one clause a line, all at the
`if`'s column: `if c then a`, then `else if d then b` for each further
condition, then `else e`. A clause whose branch doesn't fit after its
keyword ends with `then` or `else` and puts the branch below at 2. Settled:
this is the dominant broken shape today (202 `else e` lines and 159 `else
if` lines, against 69 bare `else`) [measured], and it reads as a table of
cases. The rule is per clause, so one long branch doesn't stretch the
others.

Before and after (`aoc/src/Aoc/Common/Grid.sw:235`): the `if` keeps its
shape; the arm whose body is too long moves its body below (S21).

```text
def checkGrid (rows: List (List a)): {Fail} Grid a :=
  if empty: firstWidth rows = 0 then Fail.fail "expected a grid, got no cells"
  else
    match firstRagged rows with
      | Some (index, row) => Fail.fail "line ${index + 1}: expected ${firstWidth rows} cells, as on the first line, got ${row.length}"
      | None => { rows, nonEmpty = Decidable.toBoolOfNot (DecEq.decide (firstWidth rows) 0) empty }
```

After:

```text
def checkGrid (rows: List (List a)): {Fail} Grid a :=
  if empty: firstWidth rows = 0 then Fail.fail "expected a grid, got no cells"
  else
    match firstRagged rows with
      | Some (index, row) =>
        Fail.fail "line ${index + 1}: expected ${firstWidth rows} cells, as on the first line, got ${row.length}"
      | None => { rows, nonEmpty = Decidable.toBoolOfNot (DecEq.decide (firstWidth rows) 0) empty }
```

The `validValue` chain (`aoc/src/Aoc/Year2020/Day04/Spec/Spec.sw:56`,
eight `else if`s) is already in this shape and doesn't change.

### 2.8 `match`, arms, guards, handlers and clause lambdas

**S20. Alternatives: D3566.** Recommended: two or more alternatives (of a
`match`, `handle`, a definition's equations, or a clause lambda) always go
one per line, each `|` at 2 from the line the construct starts on. One
alternative may share the line (`|> matches | ['#', ..digits] => …`,
`(match some | (j, y) if i != j => (x, y))`). `match x with` and `handle e
with` end their line. Samples in §4.

**S21. An arm** is `| patterns => body`: the body after `=>` if it fits,
otherwise below at 2 from the `|` (R11, as today). A guard stays with its
pattern, `| p if c =>`. A body that is a `match` always starts below (its
arms need a column of their own). About 90 arms written with a one-line
body below `=>` would join [measured].

Joins. Before (`aoc/src/Aoc/Common/Proofs/Range.sw:26`), inside a match:

```text
  | Zero =>
    omega
```

After: `  | Zero => omega`.

**S22. Patterns** are printed flat; a pattern too long for its line breaks
like the expression of the same shape (a list, record or tuple pattern is a
comma bracket). An or-pattern (`| 'k' | 'w' =>`) never breaks: a `|` that
starts a line starts the next arm, so its alternatives must share a line
(docs/syntax.md, "Or-patterns"). Settled: forced by the grammar.

### 2.9 Application, named arguments and the hug

**S23. Calls: D3567.** Recommended: a call that fits is one line. One that
doesn't keeps the function and its leading simple arguments (names,
literals, `_`, `?`, dotted names, `f()`) on its line, and puts each
remaining argument on its own line at 2. *Hug*: if the last argument is a
lambda, a clause lambda, a list, a record or a tuple, and the whole call up
to that argument's opening bracket fits on the line, the call stays on the
line (the other arguments with it) and the last argument opens downwards:
its body or items go below at 2, and it closes on its last line. A
parenthesised call is not huggable: hugging it gives Lisp-style staircases.
Samples in §4.

**S24. Named arguments** `(name := value)` are bracketed arguments: in a
broken call each gets its own line. Settled: they are what the call reads
by, so they deserve the line.

**S25. Closing brackets of comma-less brackets** pile up at the end of the
last line, `…)))`, never on lines of their own (D1018, unchanged).

**S26. Dot chains never break at a dot.** `xs.map f` on one line; `xs` then
`.map f` on the next would be `xs (.map f)`, a call with a method section
(docs/syntax.md, "Method sections"), so breaking there changes meaning. A
long dot chain breaks only inside its arguments, or at the `|>`s if it is a
pipeline. Settled: forced by the grammar. (A line starting with `.` occurs
only inside text blocks today [measured].)

### 2.10 Operators and precedence

**S27. Operator chains.** A chain of operators at one precedence level is a
group. When it breaks, every operator of that level starts a new line at 2
from the chain's first line, with the operator first (`&& b`, `∧ q`, `→ r`,
`= rhs`, `++ ys`). Tighter levels inside an operand are their own groups
and break only if they still don't fit; brackets are kept as written (only
D2307's redundant ones are dropped). Chained comparisons (`a ≤ b ≤ c`) are
one level. Settled: leading operators are what the repo writes (656 lines
start with an operator, 202 end with one, mostly `→` in theorem
statements) [measured], and the layout rules let a line start with any
infix operator (docs/syntax.md, "Layout").

Before (`aoc/src/Aoc/Common/Grid.sw:97`; the chain is 173 characters
joined, so every `&&` of it breaks):

```text
def touching (at: Position) (other: Position): Bool :=
  not (at.row == other.row && at.column == other.column)
    && at.row ≤ other.row + 1 && other.row ≤ at.row + 1 && at.column ≤ other.column + 1 && other.column ≤ at.column + 1
```

After:

```text
def touching (at: Position) (other: Position): Bool :=
  not (at.row == other.row && at.column == other.column)
    && at.row ≤ other.row + 1
    && other.row ≤ at.row + 1
    && at.column ≤ other.column + 1
    && other.column ≤ at.column + 1
```

Two levels: `||` breaks, the `&&` inside each operand fits
(`aoc/src/Aoc/Common/Grid.sw:91`, unchanged):

```text
def adjacent (from: Position) (to: Position): Bool :=
  (from.row == to.row && (from.column + 1 == to.column || to.column + 1 == from.column))
    || (from.column == to.column && (from.row + 1 == to.row || to.row + 1 == from.row))
```

**S28. Propositions.** `→` chains, `∧`/`∨` chains and `=` follow S27.
A `∀ (x: T) =>` or `∃` keeps its binders on its line and its body follows
`=>`; when the body breaks, its continuation lines are at 2 from the
quantifier's line, so a nested `∀` indents again. This shows the
structure: what the inner `∀` covers is visibly inside it.

Before (`aoc/src/Aoc/Common/Proofs/PrefixSums.sw:12`, a header of three
lines up to 164 characters, and a `rewrite`):

```text
theorem PrefixSums.tableAt ∀ (c: Nat): ∀ (above: List Nat) (sums: List (List Nat)) => c < List.length above →
    (∀ (i: Nat) => i < List.length sums → c < List.length (List.getOr sums i [])) → ∀ (r: Nat) => r ≤ List.length sums →
    List.getOr (List.getOr (PrefixSums.table above sums) r []) c 0 = List.getOr above c 0 + List.sumBy (List.range 0 r) (i => List.getOr (List.getOr sums i []) c 0)
  | above, [], ha, hs, Zero, hr => Eq.sym (Nat.addZero (List.getOr above c 0))
  | above, [], ha, hs, Succ r, hr => cases
  | above, [row, ..rest], ha, hs, Zero, hr => Eq.sym (Nat.addZero (List.getOr above c 0))
  | above, [row, ..rest], ha, hs, Succ r, hr =>
    let hrow: c < List.length row := hs 0 rfl
    let next := List.zipWith above row Nat.add
    let hnext: c < List.length next := List.lengthZipWithAtLeast above (Succ c) row ha hrow Nat.add
    rewrite PrefixSums.tableAt c next rest hnext (i hi => hs (Succ i) hi) r hr,
      List.getOrZipWithAdd above c row ha hrow,
      List.sumByRangeSucc (i => List.getOr (List.getOr [row, ..rest] i []) c 0) r
      in omega
```

After:

```text
theorem PrefixSums.tableAt ∀ (c: Nat):
    ∀ (above: List Nat) (sums: List (List Nat)) => c < List.length above
      → (∀ (i: Nat) => i < List.length sums → c < List.length (List.getOr sums i []))
      → ∀ (r: Nat) => r ≤ List.length sums
        → List.getOr (List.getOr (PrefixSums.table above sums) r []) c 0
          = List.getOr above c 0 + List.sumBy (List.range 0 r) (i => List.getOr (List.getOr sums i []) c 0)
  | above, [], ha, hs, Zero, hr => Eq.sym (Nat.addZero (List.getOr above c 0))
  | above, [], ha, hs, Succ r, hr => cases
  | above, [row, ..rest], ha, hs, Zero, hr => Eq.sym (Nat.addZero (List.getOr above c 0))
  | above, [row, ..rest], ha, hs, Succ r, hr =>
    let hrow: c < List.length row := hs 0 rfl
    let next := List.zipWith above row Nat.add
    let hnext: c < List.length next := List.lengthZipWithAtLeast above (Succ c) row ha hrow Nat.add
    rewrite PrefixSums.tableAt c next rest hnext (i hi => hs (Succ i) hi) r hr,
        List.getOrZipWithAdd above c row ha hrow,
        List.sumByRangeSucc (i => List.getOr (List.getOr [row, ..rest] i []) c 0) r in
      omega
```

### 2.11 Pipelines

**S29. Pipes** (D3560b): one line if the whole pipeline fits; otherwise the
head on its line and each `|> stage` on its own line at 2. A stage that is
itself too long breaks inside (its lambda hugs, S23). A pipeline inside a
stage's lambda is its own group. About 30 pipelines written one stage per
line fit on one line and join [measured]; the 243 lines that already hold
two or more stages are unaffected when they fit.

Joins. Before (`aoc/src/Aoc/Year2021/Day01/Spec/Spec.sw:14`):

```text
def slidingWindows (size: Nat) (measurements: List Nat): List (List Nat) :=
  measurements.tails
    |> .map (.take size)
    |> .filter (window => window.length == size)
```

After:

```text
def slidingWindows (size: Nat) (measurements: List Nat): List (List Nat) :=
  measurements.tails |> .map (.take size) |> .filter (window => window.length == size)
```

Stays broken (`aoc/src/Aoc/Year2020/Day03/Day03.sw:42`, 125 characters
joined): unchanged.

```text
def treesOn (map: Grid Square) (slope: Slope): Nat :=
  let find := map.lookupOr Open
  List.rangeFrom (count := map.height) (start := 1)
    |> .takeWhile (step => step * slope.down < map.height)
    |> .count (step => find { row = step * slope.down, column = step * slope.right % map.width } == Tree)
```

### 2.12 Lambdas

**S30. Lambdas.** `params => body` on one line if it fits; otherwise `=>`
ends the line and the body goes below at 2 from the line the lambda starts
on, closing bracket after the body. As a last argument it hugs (S23); as
any other argument it gets its own line. Typed parameters print as a
header's do.

Before (`aoc/src/Aoc/Common/Grid.sw:81`), lambdas that aren't the last
argument, with their extents arranged by hand:

```text
def Position.countAround (at: Position) (keep: Position → Bool): Nat :=
  Nat.sumFrom (at.row - 1) (row =>
    Nat.sumFrom (at.column - 1) (column =>
      if row == at.row && column == at.column then 0 else Bool.toNat (keep { row, column }))
      (at.column + 1 + 1 - (at.column - 1)))
    (at.row + 1 + 1 - (at.row - 1))
```

After (D3567's recommendation: the lambda isn't last, so it doesn't hug):

```text
def Position.countAround (at: Position) (keep: Position → Bool): Nat :=
  Nat.sumFrom
    (at.row - 1)
    (row =>
      Nat.sumFrom
        (at.column - 1)
        (column => if row == at.row && column == at.column then 0 else Bool.toNat (keep { row, column }))
        (at.column + 1 + 1 - (at.column - 1)))
    (at.row + 1 + 1 - (at.row - 1))
```

The after is taller, but each argument of `sumFrom` is now visibly one: in
the before, the reader has to count brackets to see that the third line's
`)` ends the inner lambda and the next line is `sumFrom`'s count.

### 2.13 Brackets: records, lists, tuples

**S31. Comma brackets** (lists, records, tuples, record updates, imports,
`omega [..]` facts): one line if they fit, otherwise one item per line at
2, comma at each line's end, none after the last, the closer on its own
line at the opening line's indentation, and the opener at the end of the
line before (D1012, D1017, unchanged). There are no set or map literals in
the language (sets and maps are built with calls such as `.toSet`), so
nothing more to rule. A record update that breaks keeps `{ r |` on the
opening line: `{ position |`, then the fields. Spreads (`..xs`) are items.

Opens. Before (`aoc/src/Aoc/Year2020/Day03/Day03.sw:50`, a list the author
put below the header, 127 characters):

```text
def slopes: List Slope :=
  [{ right = 1, down = 1 }, { right = 3, down = 1 }, { right = 5, down = 1 }, { right = 7, down = 1 }, { right = 1, down = 2 }]
```

After:

```text
def slopes: List Slope := [
  { right = 1, down = 1 },
  { right = 3, down = 1 },
  { right = 5, down = 1 },
  { right = 7, down = 1 },
  { right = 1, down = 2 }
]
```

The test-table shape, a call ending in a list (`aoc/src/Aoc/Year2020/Day12/Tests/Examples.sw:26`),
is the hug and doesn't change:

```text
test "the example's instructions" := (parsed example).map (.instructions) == Ok [
  { action = Forward, value = 10 },
  { action = Move North, value = 3 },
  { action = Forward, value = 7 },
  { action = Turn Right, value = 90 },
  { action = Forward, value = 11 }
]
```

### 2.14 Text

**S32. Strings and interpolation.** A string is never split or re-spelled.
An interpolation `${…}` is printed on one line whatever its length
(spacing inside follows the usual rules). Settled: a break inside a
string's `${}` would read as part of the text.

**S33. Text blocks** (`"""`): the opening `"""` ends its line, the block's
lines move as one piece with the line it starts on, and what follows the
closing `"""` stays on that line (as today). A text block is a hard break.
Sample: S13's first test, unchanged.

### 2.15 Types and ability rows

**S34. Types** are expressions: application (S23), `→` chains (S27), tuples
(S31). Effect rows stay tight and on one line: `{IO, Fail}` (D1037). A
binder's type that is too long breaks inside the binder's bracket at 2 from
the binder's line; rare (none seen in the samples).

### 2.16 Proofs

The language has no `show … from`, `have` or tactic blocks; a `let h: P :=
proof` is the "have", and follows S17. `cases`, `omega`, `ring` and `rfl`
are terms.

**S35. `calc`.** `calc e0` (on the `:=` line if it fits, S12), then the
steps at 2 from the line `calc` is on, one per line (a hard break). A step
is `_ R e := proof` on one line if it fits; otherwise `:=` ends the step
line and the proof goes below at 2. If `_ R e` alone doesn't fit, `e`
breaks at 4 as a header would. Settled: `:=` at the end, as everywhere else
in the language; today 177 steps put `:=` at the start of the proof's line
and 60 at the end [measured]; the 177 change.

Before (`aoc/src/Aoc/Common/Proofs/Range.sw:32`, an excerpt):

```text
            calc Succ (List.occurrences (List.rangeFrom c (Succ s)) (id => r.contains id))
              _ = Succ (Succ r.to - Nat.max r.from (Succ s))
                := rewrite countFrom r c (Succ s) omega
              _ = Succ r.to - s := omega
```

After (the first step fits on one line at this depth, 100 characters):

```text
            calc Succ (List.occurrences (List.rangeFrom c (Succ s)) (id => r.contains id))
              _ = Succ (Succ r.to - Nat.max r.from (Succ s)) := rewrite countFrom r c (Succ s) omega
              _ = Succ r.to - s := omega
```

**S36. `rewrite`.** `rewrite rules in body` on one line if it fits.
Otherwise the body goes on its own line at 2; and if the rules don't fit
on the `rewrite` line, each rule gets its own line at 4, with `in` at the
end of the last. Settled: `in` at the end is what 993 lines do against 70
that start with it [measured]; rules at 4 keep them apart from the body at
2 (the same idea as header lines). Sample: S28's last arm.

**S37. Induction** (`match induct (f x) with`) is a `match` (S20, D3553).
`docs/guide/examples/proofs.sw:115` is unchanged: its first line is 114
characters.

### 2.17 Comments

Stitchwort has only `--` line comments, so every comment ends a line. Of
28,315 own-line comment lines, 28,119 are at column 0 between declarations
[measured in the architecture note]. Three rules cover the rest.

**S38. An own-line comment** belongs to the item after it (a declaration,
statement, arm, field, constructor, list item, `calc` step or argument) and
is printed on its own line just above it, at its indentation. Its text is
never changed or re-wrapped, even past 120. It forces its enclosing group
to break.

Before (`aoc/src/Aoc/Common/Proofs/Range.sw:30-31`): the comment stays above
its `calc`, between the arm's `=>` and its body, unchanged:

```text
      | True, True =>
        -- (`t` and `i` are True, so the match has already counted the first id, and `max from s` is `s`)
        calc Succ (List.occurrences (List.rangeFrom c (Succ s)) (id => r.contains id))
```

**S39. A trailing comment** stays at the end of the line of the token
before it, after one space (D1016: no alignment), and forces its enclosing
group to break, since nothing can follow it on the line. Example: an
ability's operations, and `crates/elab/src/std/Terminal/Key.sw:20`'s
documented constructor `| Printable (char: Char) -- a printable character,
space included`, both unchanged. In a list, the comment ends the item's
line after its comma (the architecture note's `[1, 2, -- two` sample).

**S40. A comment no rule places** (between a function and its first
argument, say) makes the formatter leave that declaration as written,
re-indented only, and count it; the repo-wide count is tested to be 0, as
today. Stage 2 reports where such comments are.

## 3. What changes most

Counts are lines or sites over the 1,724 files [measured, by pattern].

| Rule | What changes | How much |
|---|---|---|
| S8, D3564: theorem headers | headers over 120 are re-laid-out; multi-line headers that fit are joined | 4,303 of 8,757 theorem headers are over 120 joined; 3,173 are written over several lines today |
| E1 in general | lines over 120 are broken | 8,217 code lines over 120 characters; 3,313 are a declaration's first line; 770 hold a string |
| S9, D3565: merge parameters | `(a: Nat) (b: Nat)` → `(a b: Nat)` | about 4,480 adjacent pairs with the same type |
| S20, D3566: alternatives | if (a): one-line `match`es with 2+ arms break; if (c): multi-line ones that fit join | (a) 118 one-line matches, 51 one-line data types; (c) 1,069 matches and 396 data types join instead |
| S12: bodies | one-line bodies below `:=` that fit join the header | about 450 |
| S35: `calc` | `:=` moves to the end of the step line | 177 steps |
| S21: arms | one-line bodies below `=>` that fit join | about 90 |
| S36: `rewrite` | `in` moves to the end of the rule line | 70 |
| S29: pipes | pipelines written one stage a line that fit join | about 30 |
| S15: records | open record types that fit join | 24 of 42 |
| S11: `decreasing` | `:=` moves to its own line | 2 |

The first three dwarf the rest. Every one of them is layout only (D3565
also changes tokens, see §4), and none changes a hash.

## 4. Decisions for Matt

### D3564: the shape of a long theorem header

**The problem.** 4,303 of the 8,757 theorem headers don't fit in 120
characters [measured]. Today each author breaks them wherever: after the
fourth parameter, mid-way through the variables, or not at all (up to 260
characters). With many parameters they're hard to scan: you can't see
what the theorem is about (the variables), what it assumes (the premises)
or what it says (the conclusion).

**The change.** One fixed shape for a header that doesn't fit, chosen from
three:

- **(a) Fill:** the parameters packed onto lines at 4, as many as fit;
  conclusion on its own line.
- **(b) All or nothing:** one parameter per line, then the conclusion.
- **(c) Variables, then premises (Matt's sketch):** the first line has the
  name, `∀` and the variables; each premise gets a line of its own; a run of
  variables between premises shares a line; then the conclusion. Each line
  that is still too long fills, as (a).

The formatter has no types, so "premise" is judged from the text: a
parameter is a premise when its type has a relation or connective at its
top level or at the end of its `→`/`∀` chain (`=`, `≠`, `<`, `≤`, `∈`,
`∉`, `∧`, `∨`, `¬`, `↔`, `∃`), or applies a capitalised name to one of the
header's earlier variables (`NumberWritten chars a`, `Agrees other slots`).
So `(f: Position → a → b)` is a variable and `(h: x = y)` a premise. The
misjudgements are harmless: an indexed type such as `(v: Vec a n)` gets a
line of its own as if it were a premise; a proposition named by a variable
(`(p: P)`) shares the variables' line.

Samples, before (`aoc/src/Aoc/Year2020/Day09/Proofs/Complete.sw:13`; body
cut to `same => ?` here):

```text
theorem shrinksInside ∀ (numbers: List Nat) (target: Nat) (start: Nat) (length: Nat) (sums: ((numbers.drop start).take length).sum = target)
    (front: List Nat) (count: Nat) (sum: Nat) (from: Nat) (at: front = numbers.drop from) (total: sum = (front.take count).sum)
    (notBeyond: from + count ≤ start + length) (over: target < sum): from ≠ start :=
  same => ?
```

(a) Fill:

```text
theorem shrinksInside ∀ (numbers: List Nat) (target: Nat) (start: Nat) (length: Nat)
    (sums: ((numbers.drop start).take length).sum = target) (front: List Nat) (count: Nat) (sum: Nat) (from: Nat)
    (at: front = numbers.drop from) (total: sum = (front.take count).sum) (notBeyond: from + count ≤ start + length)
    (over: target < sum): from ≠ start :=
  same => ?
```

(b) All or nothing:

```text
theorem shrinksInside ∀
    (numbers: List Nat)
    (target: Nat)
    (start: Nat)
    (length: Nat)
    (sums: ((numbers.drop start).take length).sum = target)
    (front: List Nat)
    (count: Nat)
    (sum: Nat)
    (from: Nat)
    (at: front = numbers.drop from)
    (total: sum = (front.take count).sum)
    (notBeyond: from + count ≤ start + length)
    (over: target < sum):
    from ≠ start :=
  same => ?
```

(c) Variables, then premises:

```text
theorem shrinksInside ∀ (numbers: List Nat) (target: Nat) (start: Nat) (length: Nat)
    (sums: ((numbers.drop start).take length).sum = target)
    (front: List Nat) (count: Nat) (sum: Nat) (from: Nat)
    (at: front = numbers.drop from)
    (total: sum = (front.take count).sum)
    (notBeyond: from + count ≤ start + length)
    (over: target < sum):
    from ≠ start :=
  same => ?
```

(c) with D3565's merging as well:

```text
theorem shrinksInside ∀ (numbers: List Nat) (target start length: Nat)
    (sums: ((numbers.drop start).take length).sum = target)
    (front: List Nat) (count sum from: Nat)
    (at: front = numbers.drop from)
    (total: sum = (front.take count).sum)
    (notBeyond: from + count ≤ start + length)
    (over: target < sum):
    from ≠ start :=
  same => ?
```

Matt's example under (c) (`aoc/src/Aoc/Year2020/Day09/Proofs/ParseComplete.sw:26`,
138 and 168 characters today), with the body under D3567:

```text
theorem writtenUnique ∀ (chars: List Char) (a: Nat) (b: Nat)
    (writtenA: NumberWritten chars a)
    (writtenB: NumberWritten chars b):
    a = b :=
  Result.okInjective
    (Eq.trans
      (Eq.sym (Parse.runsRun Parse.nat chars a (runsNumber chars a writtenA)))
      (Parse.runsRun Parse.nat chars b (runsNumber chars b writtenB)))
```

Premises between variables (`aoc/src/Aoc/Common/GridGraph.sw:28`), before:

```text
theorem stepEdgesListed ∀ (enter: Position → Option Nat) (states: List Position)
    (complete: ∀ (position: Position) (cost: Nat) => enter position = Some cost → position ∈ states) (position: Position) (next: Position)
    (weight: Nat) (edge: (next, weight) ∈ stepEdges enter position): next ∈ states :=
```

(c):

```text
theorem stepEdgesListed ∀ (enter: Position → Option Nat) (states: List Position)
    (complete: ∀ (position: Position) (cost: Nat) => enter position = Some cost → position ∈ states)
    (position: Position) (next: Position) (weight: Nat)
    (edge: (next, weight) ∈ stepEdges enter position):
    next ∈ states :=
```

A short one (`aoc/src/Aoc/Common/GridGraph.sw:56`, 162 characters):

```text
theorem memPositionsOfWithin ∀ (height: Nat) (width: Nat) (position: Position)
    (inside: position.within height width = True):
    position ∈ positions height width :=
```

**What it should do.** Under (c), a reader finds the variables on the
first line, the assumptions one per line, and the claim on the last line,
in every long theorem. The headers above go from 3 lines of up to 140
characters to 4–8 lines of under 100. Of the 4,303 long headers, about
3,350 have at least one premise and 3,070 already list variables before
premises; the other 1,240 interleave them, and (c) shows that as
alternating lines [measured, with the syntactic test above]. (b) is the
most regular but makes a 13-parameter header 15 lines; (a) is the
shortest but hides the premises in the run of parameters, which is
Matt's complaint.

**[rec: (c)]**, with "premise" judged from the syntax as described, and the
same rule for `def` headers (they rarely have premises, so it is fill for
them).

### D3565: merging parameters of the same type

**The problem.** `(a: Nat) (b: Nat)` and `(a b: Nat)` mean the same, and
both are common: about 4,480 adjacent parameter pairs have the same type
written out twice [measured]. Under D3558 each piece of code should have
one layout, and the merged form is what Matt's sketch writes; it saves 5–20
characters a header.

**The change.** The formatter merges adjacent parameters of the same kind
(explicit `( )` or implicit `[ ]`) whose types are the same text, in
definition and theorem headers, `∀` binders and lambdas. Not when the type
mentions one of the names being merged (`(x: P x) (y: P x)` would change
which `x` the second type means), not across a comment, and not in a
constructor's fields (each field is an accessor of its own, and is often
documented on its own). It never splits a group.

**Is that allowed for a formatter whose check compares tokens?** It needs
two changes to the check, the same kind the existing token rules needed:

- *Tokens.* The check already allows some token changes: D1012's commas,
  D2307's brackets, and D3472's `∀` (inserted before the check runs, so the
  check compares against the text with `∀`). Merging is the same kind: do
  it as a pass before layout, and check that pass on its own.
- *Tree.* The compiler's tree keeps the grouping (`Binder { names: [a, b]
  }` against two `Binder`s [source: `crates/syntax/src/ast.rs:954`]), so
  the tree check must compare with groups split into one binder per name.
  That comparison can't see a captured name, which is why the rule refuses
  a type that mentions a merged name; the guard is a token test, simple
  enough to trust. The hash test over the repo (`fmt_hashes`, F3) checks
  the result independently [estimated: the terms are the same, since a
  group is one function type per name].

**What it should do.** Shorter headers (`(target start length: Nat)`
above), one spelling for the same parameters, and a merged header that
more often fits on one line. Cost: the check gains a binder-splitting
comparison and the guard; about 4,480 sites change once.

**[rec: yes, merge]**, with the guard. The alternative, leaving grouping to
the author, is the one author choice left in a header, against D3558.

### D3566: alternatives one per line

**The problem.** Under fit-or-break alone, a short `match` written on four
lines would join into one, and a one-line `match` on a proof would stay:

```text
match position.row with | Zero => None | Succ above => Some { position | row = above }
```

1,069 multi-line `match`es fit on one line, and 396 data types written
one constructor a line [measured]. Joining them makes the arms hard to
scan, and an inner `match` on one line takes the arms after it, so joining
can change meaning (docs/syntax.md, clause lambdas; the check would catch
it, at the cost of that declaration being left as written).

**The change.** Three options:

- **(a)** Two or more alternatives always go one per line: arms of a
  `match`, `handle` or definition, clause lambdas, and a data type's
  constructors. One alternative may share the line.
- **(b)** As (a) for arms; a data type's constructors fit or break like a
  record's fields (`type Heading = | North | East | South | West`).
- **(c)** Fit or break everywhere.

Samples. Before (`aoc/src/Aoc/Common/Proofs/Plane.sw:147`):

```text
theorem coordsStepOpposite ∀ [auto frame: Frame f] (coords: Coords f) (heading: Heading): (coords.step heading).step heading.opposite = coords :=
  coordsExt _ _ (match heading with | North => omega | East => omega | South => omega | West => omega)
    (match heading with | North => omega | East => omega | South => omega | West => omega)
```

(a), with D3567's recommendation (the two `_` are simple arguments and
stay on `coordsExt`'s line):

```text
theorem coordsStepOpposite ∀ [auto frame: Frame f] (coords: Coords f) (heading: Heading):
    (coords.step heading).step heading.opposite = coords :=
  coordsExt _ _
    (match heading with
      | North => omega
      | East => omega
      | South => omega
      | West => omega)
    (match heading with
      | North => omega
      | East => omega
      | South => omega
      | West => omega)
```

Constructors under (a), from `aoc/src/Aoc/Year2021/Day10/Day10.sw:31`:
`type Token = | Opener (bracket: Bracket) | Closer (bracket: Bracket)`
becomes three lines (S14). Under (b) it, and `type Direction = | Up | Right
| Down | Left` (`aoc/src/Aoc/Common/Grid.sw:22`, four lines today), would
be one line.

**What it should do.** (a): every `|` starts a line, so the shape matches
the grammar's rule that a `|` starting a line is the next alternative, and
nothing that is vertical today becomes horizontal. It changes the fewest
sites: 118 one-line `match`es and 51 one-line data types break [measured].
(b) joins 396 data types; (c) also joins 1,069 matches. The cost of (a) is
taller code for tiny matches in proofs, as above.

**[rec: (a)]**

### D3567: how a call that doesn't fit breaks

**The problem.** Most long lines in proofs are calls: a lemma applied to
variables and to other calls. Breaking them is the most frequent choice
the formatter makes, and the result decides whether proofs read well.

**The change.** Three options:

- **(a) One argument per line** (Prettier, the architecture note's
  mock-ups): the function alone, then every argument on its own line at 2.
- **(b) Fill:** the arguments packed onto lines at 2, as many as fit.
- **(c) Simple arguments stay, bracketed ones get lines, and the last can
  hug:** the function and its leading simple arguments (names, literals,
  `_`, `?`, dotted names, `f()`) stay on the first line; each remaining
  argument gets its own line at 2. If the last argument is a lambda, a
  clause lambda, a list, a record or a tuple, and the whole call up to its
  opening bracket fits, the call stays on one line and that argument opens
  downwards instead.

Samples. Before (`aoc/src/Aoc/Common/Proofs/Range.sw:56`):

```text
theorem countEmpty ∀ (r: Range) (e: Nat.leq r.from r.to = False) (ids: List Nat): ids.occurrences (id => r.contains id) = r.size :=
  calc List.occurrences ids (id => r.contains id)
    _ = 0 := List.occurrencesNone ids
      (id => r.contains id)
      (id =>
        match t: Nat.leq r.from id with
          | True => Nat.leqFalseOfLess r.to id omega
          | False => rfl)
    _ = r.size := omega
```

(c):

```text
theorem countEmpty ∀ (r: Range) (e: Nat.leq r.from r.to = False) (ids: List Nat):
    ids.occurrences (id => r.contains id) = r.size :=
  calc List.occurrences ids (id => r.contains id)
    _ = 0 := List.occurrencesNone ids (id => r.contains id) (id =>
      match t: Nat.leq r.from id with
        | True => Nat.leqFalseOfLess r.to id omega
        | False => rfl)
    _ = r.size := omega
```

(a):

```text
theorem countEmpty ∀ (r: Range) (e: Nat.leq r.from r.to = False) (ids: List Nat):
    ids.occurrences (id => r.contains id) = r.size :=
  calc List.occurrences ids (id => r.contains id)
    _ = 0 :=
      List.occurrencesNone
        ids
        (id => r.contains id)
        (id =>
          match t: Nat.leq r.from id with
            | True => Nat.leqFalseOfLess r.to id omega
            | False => rfl)
    _ = r.size := omega
```

(b) would give `List.occurrencesNone ids (id => r.contains id)` on one line
and the lambda below, with its `match` deeper still. S30's
`countAround` and D3564's `writtenUnique` body are (c) too: there no
argument is simple or huggable, so (c) and (a) agree. Under (a), D3566's
sample would put each `_` on a line of its own.

**What it should do.** (c) keeps the common proof shapes compact: `f x y
(g z)` breaks as `f x y` with `(g z)` below, and `xs.map (x =>` with its
body below, which is how 607 lambdas are written today (510 others start a
line of their own) [measured]. (a) is the simplest rule and the most
regular, but turns a lemma applied to six variables into seven lines. (b)
is shortest but makes the argument boundaries hard to see in nested
proofs.

**[rec: (c)]**

### D3568: a lambda after `:=` (Matt, 13 Nov 2026: yes)

A lambda right after `:=` (a `let` or a declaration body) stays on the
`:=` line and its body goes below at +2, as a last-argument lambda hugs
under D3567. Without it the body rule (S12) moved the whole lambda below:

```
  let skipNoise := () =>
    let skipped := Parse.span (char => ¬(starts char))
    ()
```

not `let skipNoise :=` with `() =>` alone on the next line. Matt: "that
looks far better".

### D3569: a call of only plain arguments that doesn't fit (Matt, 13 Nov 2026: yes)

Under D3567 (c) plain arguments stay on the function's line, so a call
whose arguments are all plain could not break. When such a line still
overflows 120, its arguments fill onto continuation lines at +4, as many
per line as fit:

```
                Graph.settleKeeps graph costs sources reach edgesReach queue settled best cost state
                    least taken invariant)
```

Calls that fit, and calls with bracketed arguments, are unchanged. Not one
argument per line, which made the example 13 lines.

## Findings worth tickets

- **Width in bytes.** The current formatter's `:= match` rule (D3553)
  measures 120 in bytes, so a header full of `∀ → ≤` joins its `match`
  later than it should. E5 says characters; the current rule could change
  now, independently of the rewrite.
- **Header continuation at 2 or 4.** Today's formatter puts a signature's
  `→` continuation lines at 2 (D1040's "+2 from the line they continue"),
  while premises and `decreasing` are at 4 (R1, D1038). S6 makes every
  header line 4; the probe of `Builtins.sw:28`'s break shape shows today's
  2.
- **Multi-line record updates** come out as `{` / `position |` / fields
  under today's formatter [probe]; S31 keeps `{ position |` together. None
  exist in the repo today, so it only matters for new code.
- **`decreasing` and `:=`.** Two files put `:=` at the end of the
  `decreasing` line (`crates/elab/src/std/Nat/PartitionPoint.sw:14`,
  `examples/accept/let-proof-pattern-unfold.sw:20`) against 77 that follow
  the documented shape; a one-line fix each, or wait for the reformat.

## Appendix: the probes

All in the lane's scratchpad (`sw3158/`), with `target/release/stitchwort`
at `051b6f58b`:

- **`samples.txt` and `check.py`:** every before/after pair in this note as
  whole declarations (excerpts wrapped in a header). Each side goes through
  `stitchwort fmt -`: every before and every after parses (none refused).
  With all whitespace removed, before and after are the same text, except
  the D3565 sample, which merges binders on purpose. Every after line is at
  most 120 characters. Most afters are also
  fixed points of today's formatter, which keeps line breaks; the
  exceptions are D1040's 2 against S6's 4 for a signature's `→` lines, the
  record update above, and a broken header followed by `:= match`, which
  today's D3553 rule joins onto the conclusion line (S6 says the body of a
  broken header starts below). Same tree was not checked: there is no
  command for it.
- **`stats.py`, `headers.py`, `joins.py`, `g.py`:** the counts. Line-based
  patterns over the 1,724 files, so they are approximate: comments and
  text blocks are skipped crudely, and "would fit" is the joined length of
  the lines with single spaces, measured in characters.
