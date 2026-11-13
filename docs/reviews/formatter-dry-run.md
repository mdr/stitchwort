# Formatter stage 4: dry run

SW-3189 (formatter stage 4 dry run), for Matt. Nothing in the repo's `.sw`
files was changed: the new formatter's tree printer (`stitchwort dev fmt-tree
--print`, built from `main` at 796bdcbe6, the stage 3 merge) was run over
every tracked `.sw` file under std, `aoc/src`, `games` and `examples`, and
its output was compared with the files as they are today. This note is what
that comparison shows, with real before and after samples, grouped by rule.

## In plain words

**What changes.** About a quarter of all lines move (31,000 of 130,000).
Most of that is lines that are too long today: there are 8,090 code lines
over 120 characters now and 19 after (the 19 left are mostly lines holding one string, which is never split). Breaking them, and laying out theorem headers the way you
sketched in D3564, adds lines: the three folders of real code grow by about
a quarter (std +26%, aoc +25%, games +23%), and the examples hardly move
(+1%). Overall 130,315 lines become 153,089 (+17.5%). Going the other way,
3,263 `(a: Nat) (b: Nat)` pairs merge into `(a b: Nat)` (D3565), and 1,370
places that were broken over several lines join up because they now fit.

**What stays.** Every file passes the printer's own checks: same tokens
(apart from the deliberate rewrites), same comments on the same tokens, same
syntax tree, and the same text when formatted again. 0 declarations were
left as written and no construct lacked a rule. Comments, blank lines
(the ones the author wrote stay), imports, strings and the order of everything are
unchanged. Imports changed in no file. 101 files that are deliberately
broken (`examples/reject` and two project examples that don't parse) were
left out of the numbers.

**What to look at.** The decisions D3564 to D3569 do what they said. Five
other things I'd like you to see before the switch, in "Worth a look" below:
one is a real problem (a `:= match` that breaks its scrutinee), one is a
bug (`def main()` becomes `def main ()`), the other three are matters of
taste. Recommendations are there too.

## The numbers

Lines are counted per file, then summed. "Before-lines that change" is how
many of today's lines are removed or replaced (git's own count of the
diff); the total of lines added is larger, 53,797, because broken lines
take more lines. Source: `fmt-tree --print` per file, compared with
`git diff --no-index`.

| Area | Files | Files touched | Lines before | Lines after | Before-lines that change | Share |
|---|---:|---:|---:|---:|---:|---:|
| all | 2,517 | 1,839 | 130,315 | 153,089 | 31,023 | 24% |
| std | 98 | 94 | 35,698 | 44,889 | 10,682 | 30% |
| aoc | 633 | 588 | 50,981 | 63,503 | 13,336 | 26% |
| games | 29 | 28 | 2,857 | 3,513 | 686 | 24% |
| examples | 1,757 | 1,129 | 40,779 | 41,184 | 6,319 | 15% |
| examples/accept | 513 | 400 | 24,050 | 24,289 | 3,546 | 15% |
| examples/reject | 825 | 506 | 8,047 | 7,992 | 1,557 | 19% |
| examples/extract | 57 | 45 | 3,823 | 3,776 | 321 | 8% |
| examples/goals | 43 | 20 | 521 | 539 | 71 | 14% |
| examples/projects | 188 | 62 | 2,813 | 3,163 | 547 | 19% |
| examples/soundness | 131 | 96 | 1,525 | 1,425 | 277 | 18% |

| Std namespace | Files | Lines before | Lines after | Before-lines that change | Share |
|---|---:|---:|---:|---:|---:|
| std/List | 12 | 8,045 | 9,904 | 2,374 | 30% |
| std/Parse | 3 | 5,554 | 8,105 | 1,995 | 36% |
| std/Map | 4 | 4,313 | 5,757 | 1,658 | 38% |
| std/Float | 3 | 2,626 | 3,379 | 910 | 35% |
| std/Nat | 8 | 2,053 | 2,535 | 722 | 35% |
| std/core | 25 | 2,840 | 3,098 | 490 | 17% |
| std/Graph | 1 | 1,475 | 1,958 | 464 | 31% |
| std/Set | 2 | 1,117 | 1,346 | 374 | 33% |
| std/Omega | 2 | 1,134 | 1,471 | 332 | 29% |
| std/Int | 5 | 925 | 1,054 | 299 | 32% |

Other totals from the printer's own summary lines:

| Measure | Before | After |
|---|---:|---:|
| Code lines over 120 characters (all folders) | 8,090 | 19 |
| std alone | 2,776 | 2 |
| aoc alone | 4,682 | 14 |
| games alone | 249 | 2 |
| examples | 383 | 1 |

Parameter groups merged (D3565), by the printer's own count: 3,263 (std
1,027, aoc 1,199, games 57, examples 980).

## The most common kinds of change

Counted over the 12,878 separate changed regions (hunks) of the diff, by
a script that looks for each pattern. A region can count in more than one
row, and the counts are approximate (the script reads the text, it doesn't
parse).

| Kind of change | Regions |
|---|---:|
| An over-long line broken (same tokens, more lines) | 5,101 |
| Parameters merged, `(a: T) (b: T)` to `(a b: T)` | 3,263 (printer's count) |
| A theorem header laid out over several lines (D3564) | 2,583 |
| Lines joined because they now fit | 1,370 |
| A `rewrite` proof re-laid out (many just indented one level) | 1,248 |
| A `match` moved off the `:=` line (header too long to share it) | 768 |
| A last-argument lambda opened downwards, `(x =>` at line end | 706 |
| A data type joined onto its `type` line (D3566) | 581 |
| `def f()` printed as `def f ()` (bug, see below) | 397 |
| A `match` moved up onto the `:=` line (the header now fits) | 278 |
| An operator chain broken before `∧`, `&&`, `∨` | 321 |
| Arms joined onto fewer lines | 223 |
| A list or record opened one item per line | 145 |
| A pipeline broken before `|>` | 80 |
| `calc` proofs re-laid out (56 now start on the `:=` line) | 79 |
| `if`/`else` chain broken one clause per line | 38 |
| A list or record joined onto one line | 61 |

Blank lines are never added or removed, comments never change text, and no
file's imports change.

## Worth a look

### W1. A `:= match` on the header line can break in the middle of its scrutinee (real problem, 63 places)

**The problem.** Today's rule (D3553) puts `match ... with` on the header
line when the header fits. The printer applies it whenever the *header*
fits, even if the `match x y with` line then overflows. The match head is
wrapped as if it were a call (D3569), and the arms sit at 2, level with the
wrapped pieces. Three real cases:

`aoc/src/Aoc/Common/Grid.sw:197`

Before:

```text
def Grid.step (grid: Grid a) (position: Position) (direction: Direction): Option Position :=
  match position.step direction with
    | Some next => if grid.contains next then Some next else None
    | None => None
```

After:

```text
def Grid.step (grid: Grid a) (position: Position) (direction: Direction): Option Position := match position.step
    direction with
  | Some next => if grid.contains next then Some next else None
  | None => None
```

`aoc/src/Aoc/Common/Offset.sw:47`

Before:

```text
def Position.offset (position: Position) (offset: Offset): Option Position :=
  match (position.row.toInt + offset.rows).toNatChecked with
    | None => None
    | Some row =>
      match (position.column.toInt + offset.columns).toNatChecked with
        | None => None
        | Some column => Some { row, column }
```

After:

```text
def Position.offset (position: Position) (offset: Offset): Option Position := match (position.row.toInt
  + offset.rows).toNatChecked with
  | None => None
  | Some row =>
    match (position.column.toInt + offset.columns).toNatChecked with
      | None => None
      | Some column => Some { row, column }
```

`aoc/src/Aoc/Year2020/Day07/Day07.sw:114`

Before:

```text
def Rules.bagsInside (rules: Rules) (colour: Colour): {Fail} Nat :=
  match rules.book.bagsToDepth (rules.all.length + 1) colour with
    | Some total => total
    | None => Fail.fail "the rules for ${colour.name} bags go round in a cycle"
```

After:

```text
def Rules.bagsInside (rules: Rules) (colour: Colour): {Fail} Nat := match rules.book.bagsToDepth
  (rules.all.length + 1)
  colour with
  | Some total => total
  | None => Fail.fail "the rules for ${colour.name} bags go round in a cycle"
```


**Recommendation.** Hug the `match` onto the header line only when the whole
`match ... with` fits on that line (120); otherwise put the `match` below
at 2 like any other body (arms at 4, as in the "Before" samples). This is
what D3553's "when it fits" says. 63 places (std 28, aoc 21, examples 10,
games 4) go back to the usual shape. It should be a small rule change in the printer.

### W2. `def main()` becomes `def main ()` (bug, 397 places)

Every definition with no parameters but `()` gets a space before the
brackets: `def main(): {IO, Fail} () :=` becomes `def main (): {IO, Fail} () :=`.
Calls keep `f()`: `IO.readAll()` is untouched. The style note itself
writes `def main()` in its examples, and today's files do, so this looks
like a slip rather than a decision.

`aoc/src/Aoc/Year2021/Day01/Day01.sw:23`

Before:

```text
def main(): {IO, Fail} () :=
```

After:

```text
def main (): {IO, Fail} () :=
```

**Recommendation.** Fix in the printer so that a definition's `()`
stays attached to its name. Otherwise 397 changed regions (427 definitions in the output)
churn for nothing.

### W3. A record or list body that would fit on its own line is opened on the `:=` line (taste, 64 of 218)

D3568 lets a lambda after `:=` stay on the `:=` line. The printer does the
same for a record or a list: `:= {` or `:= [` ends the line and the items go
below. In 218 places that is what it does, and in 64 the whole record would
have fitted on the next line at 2, which is where today's code puts it:

`aoc/src/Aoc/Year2020/Day03/Spec/Spec.sw:23`

Before:

```text
def moved (position: Position) (slope: Slope): Position :=
  { row = position.row + slope.down, column = position.column + slope.right }
```

After:

```text
def moved (position: Position) (slope: Slope): Position := {
  row = position.row + slope.down,
  column = position.column + slope.right
}
```

This turns a 2-line body into 4. The hug is right when the body doesn't fit
below (the list in section 10); here it is only longer.

**Recommendation.** Hug a record or list after `:=` only when the one-line
form below would not fit. That keeps the body rule (S12) uniform and removes
about 130 lines of height. (A lambda keeps its hug: D3568 was your call.)

### W4. A long test with a text block explodes into eleven lines (taste)

`aoc/src/Aoc/Year2020/Day04/Tests/Examples.sw:68`

Before:

```text
test "a passport parsed" :=
  parsed """
    hcl:#ae17e1 iyr:2013
    eyr:2024""" == Ok [{ fields = [{ key = HairColor, value = "#ae17e1" }, { key = IssueYear, value = "2013" }, { key = ExpirationYear, value = "2024" }] }]
```

After:

```text
test "a passport parsed" := parsed """
  hcl:#ae17e1 iyr:2013
  eyr:2024"""
  == Ok [
    {
      fields = [
        { key = HairColor, value = "#ae17e1" },
        { key = IssueYear, value = "2013" },
        { key = ExpirationYear, value = "2024" }
      ]
    }
  ]
```

A long `==` on a text-block argument opens every level it can: the record,
the list and the field list. Nothing is wrong (the line was 150 characters),
but it is the tallest result in the sample, and the text block's indentation
moves from 4 to 2 as well. I'd leave it, but you may want a `test` body to be
exempt.

### W5. Small layout oddities, each on one line

- **A pattern's continuation lines up with the body** (about 20 places). In
  the arm below the pattern's second line and the `let` that follows are both at 6:

`aoc/src/Aoc/Year2020/Day12/Proofs/Complete.sw:38`

Before:

```text
    | Witness letter (Witness digits (Both split (Both actionWritten (Both nonEmpty (Both allDigits (Both decimal turn)))))) =>
      let sameItem: { action = item.action, value = Parse.digitsValue digits } = item := rewrite <- decimal in instructionEta item
```

After:

```text
    | Witness letter
      (Witness digits (Both split (Both actionWritten (Both nonEmpty (Both allDigits (Both decimal turn)))))) =>
      let sameItem: { action = item.action, value = Parse.digitsValue digits } = item :=
        rewrite <- decimal in instructionEta item
```

  Recommendation: continue a long pattern at +4, like a header's parameters.
- **A parenthesised `if` closes with `else` under its `(`**, not indented:

`aoc/src/Aoc/Year2025/Day02/Proofs/Part2.sw:359`

Before:

```text
theorem termIds ∀ (w: Nat → Int) (r: Range) (k: Nat) (hk: 1 ≤ k) (n: Nat) (hn: 2 ≤ n):
    (if Nat.leq (k * n) r.to.digitCount then w n * (RepetitionTemplate.sumIn { blockLength = k, copies = n } r).toInt else 0)
```

After:

```text
theorem termIds ∀ (w: Nat → Int) (r: Range) (k: Nat)
    (hk: 1 ≤ k)
    (n: Nat)
    (hn: 2 ≤ n):
    (if Nat.leq (k * n) r.to.digitCount then w n * (RepetitionTemplate.sumIn { blockLength = k, copies = n } r).toInt
    else 0)
```

  Seen twice (both in `aoc/src/Aoc/Year2025/Day02/Proofs/Part2.sw`). It reads as if `else` belonged to the line above
  the `(`. Recommendation: `else` at +2 from the `(`.
- **Plain argument after a bracketed one gets its own line** (`rest` in the
  Graph sample, section 5). It is what the rule says (each remaining argument
  on its own line) and it reads fine; mentioned because it turns three-word
  lines into three one-word lines. No change recommended.
- **Earlier lambda arguments stay on the call line when the last one hugs**
  (section 5, `Bool.inspect ... (t => rfl) (f =>`). Following S23, but the
  first line ends up 118 characters. No change recommended.

## The samples

Each is a real hunk from the diff, before first. Paths are in the repo;
`std/` is `crates/elab/src/std/`. Where a hunk shows a change that comes with
the rule, the line under the heading says which rule.

### 1. Long theorem headers with premises (D3564)

**The variables share the first line, the premise (`sub`, a statement) gets a line of its own.** (`std/List/Attach.sw:40`)

Before:

```text
theorem List.sumByAttachFrom ∀ [auto add: Add b] (whole: List a) (rest: List a) (f: a → b) (sub: ∀ (x: a) => List.Mem x rest → List.Mem x whole):
```

After:

```text
theorem List.sumByAttachFrom ∀ [auto add: Add b] (whole rest: List a) (f: a → b)
    (sub: ∀ (x: a) => List.Mem x rest → List.Mem x whole):
```

**Each premise (`h1`, `h2`) on its own line, then the conclusion; the body call breaks too.** (`std/Float/Float.sw:526`)

Before:

```text
theorem Float.ieeeLtTrans ∀ (x: Float) (y: Float) (z: Float) (h1: Float.ieeeLt x y = True) (h2: Float.ieeeLt y z = True): Float.ieeeLt x z = True :=
  Float.rankIeeeLt x z (And.left (Float.ieeeLtNotNaN x y h1)) (And.right (Float.ieeeLtNotNaN y z h2))
```

After:

```text
theorem Float.ieeeLtTrans ∀ (x y z: Float)
    (h1: Float.ieeeLt x y = True)
    (h2: Float.ieeeLt y z = True):
    Float.ieeeLt x z = True :=
  Float.rankIeeeLt x z
    (And.left (Float.ieeeLtNotNaN x y h1))
    (And.right (Float.ieeeLtNotNaN y z h2))
```

**Four plain premises, one per line, then the one that is long.** (`aoc/src/Aoc/Common/Proofs/Grid.sw:129`)

Before:

```text
theorem touchingOfBounds ∀ (r: Nat) (c: Nat) (a: Nat) (b: Nat) (h1: r - 1 ≤ a) (h2: a ≤ r + 1) (h3: c - 1 ≤ b) (h4: b ≤ c + 1)
    (other: not (a == r && b == c) = True): touching { row = r, column = c } { row = a, column = b } = True :=
```

After:

```text
theorem touchingOfBounds ∀ (r c a b: Nat)
    (h1: r - 1 ≤ a)
    (h2: a ≤ r + 1)
    (h3: c - 1 ≤ b)
    (h4: b ≤ c + 1)
    (other: not (a == r && b == c) = True):
    touching { row = r, column = c } { row = a, column = b } = True :=
```

**A header that fits except for its conclusion: the conclusion goes on its own line at 4.** (`std/List/Attach.sw:46`)

Before:

```text
theorem List.sumByAttach ∀ [auto add: Add b] (xs: List a) (f: a → b): List.sumBy (List.attach xs) (e => f e.value) = List.sumBy xs f :=
```

After:

```text
theorem List.sumByAttach ∀ [auto add: Add b] (xs: List a) (f: a → b):
    List.sumBy (List.attach xs) (e => f e.value) = List.sumBy xs f :=
```

### 2. Merged parameters (D3565)

**`(a: Nat) (m: Nat) (n: Nat)` becomes `(a m n: Nat)`; the header still fits on one line.** (`std/Nat/Arith.sw:535`)

Before:

```text
theorem Nat.leMin ∀ (a: Nat) (m: Nat) (n: Nat) (hm: a ≤ m) (hn: a ≤ n): a ≤ Nat.min m n :=
```

After:

```text
theorem Nat.leMin ∀ (a m n: Nat) (hm: a ≤ m) (hn: a ≤ n): a ≤ Nat.min m n :=
```

**Merged parameters, and a call too long for a line breaks one bracketed argument per line.** (`std/Nat/Arith.sw:582`)

Before:

```text
theorem Nat.powMono ∀ (b: Nat) (e: Nat) (f: Nat) (h: e ≤ f): Nat.pow (Succ b) e ≤ Nat.pow (Succ b) f :=
  Nat.leCongRight (Nat.pow (Succ b) e) (Nat.pow (Succ b) e * Nat.pow (Succ b) (f - e)) (Nat.pow (Succ b) f)
```

After:

```text
theorem Nat.powMono ∀ (b e f: Nat) (h: e ≤ f): Nat.pow (Succ b) e ≤ Nat.pow (Succ b) f :=
  Nat.leCongRight
    (Nat.pow (Succ b) e)
    (Nat.pow (Succ b) e * Nat.pow (Succ b) (f - e))
    (Nat.pow (Succ b) f)
```

### 3. Data constructors (D3566)

**Constructors join onto the `type` line if the whole declaration fits.** (`std/Fin/Fin.sw:7`)

Before:

```text
type Fin: Nat → Type =
  | FZero: Fin (Succ n)
  | FSucc (i: Fin n): Fin (Succ n)
```

After:

```text
type Fin: Nat → Type = | FZero: Fin (Succ n) | FSucc (i: Fin n): Fin (Succ n)
```

**A plain enum of four names becomes one line.** (`std/Float/Model.sw:84`)

Before:

```text
type Float.Model.Location: Type =
  | Exact
  | BelowHalf
  | Half
  | AboveHalf
```

After:

```text
type Float.Model.Location: Type = | Exact | BelowHalf | Half | AboveHalf
```

**The same rule at its limit: 119 characters, four constructors with fields.** (`std/Parse/Parse.sw:37`)

Before:

```text
type Parse.Problem =
  | Expected (what: Text)
  | Literal (text: Text)
  | Literals (texts: List Text)
  | Message (text: Text)
```

After:

```text
type Parse.Problem = | Expected (what: Text) | Literal (text: Text) | Literals (texts: List Text) | Message (text: Text)
```

### 4. Match arms and patterns (D3566)

**An arm whose body fits goes on the arm line.** (`aoc/src/Aoc/Year2020/Day02/Proofs/Policies.sw:29`)

Before:

```text
    | [c, ..rest], Zero =>
      rewrite holdsNothingBefore letter rest (Succ start) position omega in cases
    | [c, ..rest], Succ index =>
      rewrite holdsGet letter rest (Succ start) index position omega in cases
```

After:

```text
    | [c, ..rest], Zero => rewrite holdsNothingBefore letter rest (Succ start) position omega in cases
    | [c, ..rest], Succ index => rewrite holdsGet letter rest (Succ start) index position omega in cases
```

**An arm whose body is too long goes below the `=>`, at +2.** (`games/rogue/src/Rogue/Proofs/Apart.sw:136`)

Before:

```text
        | Move direction => monstersTurnApart dice (playerMoves dice state direction) (playerMovesApart dice state direction apart)
```

After:

```text
        | Move direction =>
          monstersTurnApart dice (playerMoves dice state direction) (playerMovesApart dice state direction apart)
```

**`let x := match ... with` keeps the `match` on the `let` line; the arms sit at +2.** (`games/rogue/src/Rogue/Generate.sw:77`)

Before:

```text
  let more :=
    match extra with
      | 0 => [(0, 3)]
      | 1 => [(1, 4)]
      | _ => []
```

After:

```text
  let more := match extra with
    | 0 => [(0, 3)]
    | 1 => [(1, 4)]
    | _ => []
```

**`:= match ... with` stays on the header line when that fits (as today, D3553); arms drop to 2.** (`aoc/src/Aoc/Year2020/Day04/Proofs/Rules.sw:20`)

Before:

```text
theorem yearSpec ∀ (low: Nat) (high: Nat) (value: Text): yearBetween low high value = year low high value :=
  match value with
    | MkText chars => yearChars low high chars
```

After:

```text
theorem yearSpec ∀ (low high: Nat) (value: Text): yearBetween low high value = year low high value := match value with
  | MkText chars => yearChars low high chars
```

**A long pattern wraps, and the body sits below.** (`aoc/src/Aoc/Year2020/Day12/Proofs/Complete.sw:38`)

Before:

```text
    | Witness letter (Witness digits (Both split (Both actionWritten (Both nonEmpty (Both allDigits (Both decimal turn)))))) =>
      let sameItem: { action = item.action, value = Parse.digitsValue digits } = item := rewrite <- decimal in instructionEta item
```

After:

```text
    | Witness letter
      (Witness digits (Both split (Both actionWritten (Both nonEmpty (Both allDigits (Both decimal turn)))))) =>
      let sameItem: { action = item.action, value = Parse.digitsValue digits } = item :=
        rewrite <- decimal in instructionEta item
```

### 5. Broken calls and the hug (D3567)

**Plain arguments stay on the function line; each bracketed argument goes on its own line at +2.** (`std/Graph/Search.sw:585`)

Before:

```text
          Graph.relaxKeeps costs cost rest (queue.insert (cost + weight, next)) (costs.set best next (cost + weight)) entry
```

After:

```text
          Graph.relaxKeeps costs cost rest
            (queue.insert (cost + weight, next))
            (costs.set best next (cost + weight))
            entry
```

**A plain argument (`rest`) after a bracketed one also gets its own line.** (`std/Graph/Search.sw:432`)

Before:

```text
        index.lookupEntriesOff state (start + 1) rest
```

After:

```text
        index.lookupEntriesOff state
          (start + 1)
          rest
```

**The last lambda hugs the line (`(f =>`), the earlier lambda arguments stay on the call line.** (`std/Nat/Arith.sw:524`)

Before:

```text
theorem Nat.leqMaxAbove ∀ (x: Nat) (a: Nat) (b: Nat) (h: Nat.leq x a = False): Nat.leq x (Nat.max a b) = Nat.leq x b :=
  Bool.inspect (Nat.leq a b) (c => Nat.leq x (Bool.ifThenElse c (u => b) (u => a)) = Nat.leq x b)
    (t => rfl)
    (f => Eq.trans h (Eq.sym (Nat.leqFalseOfLess b x (Nat.lessTrans b a x f.read h.read))))
```

After:

```text
theorem Nat.leqMaxAbove ∀ (x a b: Nat) (h: Nat.leq x a = False): Nat.leq x (Nat.max a b) = Nat.leq x b :=
  Bool.inspect (Nat.leq a b) (c => Nat.leq x (Bool.ifThenElse c (u => b) (u => a)) = Nat.leq x b) (t => rfl) (f =>
    Eq.trans h (Eq.sym (Nat.leqFalseOfLess b x (Nat.lessTrans b a x f.read h.read))))
```

### 6. A lambda after `:=` (D3568)

**The lambda stays on the `:=` line, its body goes below at +2.** (`aoc/src/Aoc/Year2021/Day01/Tests/Input.sw:7`)

Before:

```text
def inputDepths: Result (List Nat) Text := Fail.toResult (() => parseDepths (include "../../../../../inputs/2021/day01.txt"))
```

After:

```text
def inputDepths: Result (List Nat) Text := Fail.toResult (() =>
  parseDepths (include "../../../../../inputs/2021/day01.txt"))
```

**A `:=` that sat alone on its own line moves back up onto the header line, with the lambda.** (`aoc/src/Aoc/Year2020/Day19/Proofs/Sound.sw:35`)

Before:

```text
theorem sound ∀ (rules: Rules) (fuel number: Nat): LeavesAfter rules fuel number
    := message left found =>
```

After:

```text
theorem sound ∀ (rules: Rules) (fuel number: Nat): LeavesAfter rules fuel number := message left found =>
```

### 7. A call of only plain arguments (D3569)

**All arguments are names, so they fill the line and wrap at +4, not one per line.** (`aoc/src/Aoc/Year2020/Day14/Proofs/Parts.sw:57`)

Before:

```text
  let agrees := foldAgrees Computer.writeValue Spec.writeMasked writeValueAgrees program.instructions Computer.start Spec.start startAgrees
```

After:

```text
  let agrees :=
    foldAgrees Computer.writeValue Spec.writeMasked writeValueAgrees program.instructions Computer.start Spec.start
        startAgrees
```

### 8. Pipelines

**A pipeline that is too long breaks before `|>`, at +2.** (`aoc/src/Aoc/Year2020/Day04/Spec/Spec.sw:49`)

Before:

```text
  value.toList |> matches | ['#', ..rest] => rest.length == 6 ∧ rest.all (char => Parse.isDigit char ∨ ('a' <= char <= 'f'))
```

After:

```text
  value.toList
    |> matches | ['#', ..rest] => rest.length == 6 ∧ rest.all (char => Parse.isDigit char ∨ ('a' <= char <= 'f'))
```

**A `|>` stage with a hugged lambda: the stage moves to its own line.** (`aoc/src/Aoc/Year2020/Day10/Day10.sw:50`)

Before:

```text
  bag.device |> .flatMap (device =>
    let chain := bag.chain device
    if chain.fits then Some (chain.differences.count (d => d == 1) * chain.differences.count (d => d == 3)) else None)
```

After:

```text
  bag.device
    |> .flatMap (device =>
      let chain := bag.chain device
      if chain.fits then Some (chain.differences.count (d => d == 1) * chain.differences.count (d => d == 3)) else None)
```

### 9. Operators and ∃ chains

**A `&&` chain that overflows: one operand per line.** (`aoc/src/Aoc/Common/Grid.sw:99`)

Before:

```text
    && at.row ≤ other.row + 1 && other.row ≤ at.row + 1 && at.column ≤ other.column + 1 && other.column ≤ at.column + 1
```

After:

```text
    && at.row ≤ other.row + 1
    && other.row ≤ at.row + 1
    && at.column ≤ other.column + 1
    && other.column ≤ at.column + 1
```

**`=` and `∨` break before the operator.** (`aoc/src/Aoc/Year2020/Day04/Proofs/Proofs.sw:24`)

Before:

```text
    required.all has = ((keys.filter (key => not (has key))).map Key.code == [] ∨ (keys.filter (key => not (has key))).map Key.code == ["cid"]) :=
```

After:

```text
    required.all has
      = ((keys.filter (key => not (has key))).map Key.code == []
        ∨ (keys.filter (key => not (has key))).map Key.code == ["cid"]) :=
```

**An `∃` with a long `∧` chain: the first conjunct stays after `=>`, the others start with `∧`.** (`aoc/src/Aoc/Year2020/Day09/Spec/Spec.sw:28`)

Before:

```text
def Part1 (numbers: List Nat) (preamble: Nat) (answer: Nat): Prop :=
  ∃ (position: Nat) =>
    preamble ≤ position ∧ numbers.get position = Some answer ∧ ¬SumOfTwo (previous numbers preamble position) answer
      ∧ (∀ (earlier: Nat) => preamble ≤ earlier < position → ∀ (number: Nat) => numbers.get earlier = Some number →
        SumOfTwo (previous numbers preamble earlier) number)
```

After:

```text
def Part1 (numbers: List Nat) (preamble answer: Nat): Prop :=
  ∃ (position: Nat) => preamble ≤ position
    ∧ numbers.get position = Some answer
    ∧ ¬SumOfTwo (previous numbers preamble position) answer
    ∧ (∀ (earlier: Nat) => preamble ≤ earlier < position
      → ∀ (number: Nat) => numbers.get earlier = Some number → SumOfTwo (previous numbers preamble earlier) number)
```

**The same, nested: the inner `∃` hugs its first conjunct.** (`aoc/src/Aoc/Year2020/Day10/Spec/Spec.sw:36`)

Before:

```text
  ∃ (highest: Nat) => Highest adapters highest ∧ ∃ (chain: List Nat) =>
    List.Perm chain adapters ∧ Connects chain (highest + 3) = True
```

After:

```text
  ∃ (highest: Nat) => Highest adapters highest
    ∧ ∃ (chain: List Nat) => List.Perm chain adapters
      ∧ Connects chain (highest + 3) = True
```

### 10. Records, lists and text blocks

**A record body that does not fit after the header breaks one field per line.** (`aoc/src/Aoc/Year2020/Day03/Spec/Spec.sw:23`)

Before:

```text
def moved (position: Position) (slope: Slope): Position :=
  { row = position.row + slope.down, column = position.column + slope.right }
```

After:

```text
def moved (position: Position) (slope: Slope): Position := {
  row = position.row + slope.down,
  column = position.column + slope.right
}
```

**A list of records too long for one line: one item per line.** (`aoc/src/Aoc/Year2020/Day03/Spec/Spec.sw:54`)

Before:

```text
def puzzleSlopes: List Slope :=
  [{ right = 1, down = 1 }, { right = 3, down = 1 }, { right = 5, down = 1 }, { right = 7, down = 1 }, { right = 1, down = 2 }]
```

After:

```text
def puzzleSlopes: List Slope := [
  { right = 1, down = 1 },
  { right = 3, down = 1 },
  { right = 5, down = 1 },
  { right = 7, down = 1 },
  { right = 1, down = 2 }
]
```

**A text block and a long comparison: each level opens as far as it needs to.** (`aoc/src/Aoc/Year2020/Day04/Tests/Examples.sw:68`)

Before:

```text
test "a passport parsed" :=
  parsed """
    hcl:#ae17e1 iyr:2013
    eyr:2024""" == Ok [{ fields = [{ key = HairColor, value = "#ae17e1" }, { key = IssueYear, value = "2013" }, { key = ExpirationYear, value = "2024" }] }]
```

After:

```text
test "a passport parsed" := parsed """
  hcl:#ae17e1 iyr:2013
  eyr:2024"""
  == Ok [
    {
      fields = [
        { key = HairColor, value = "#ae17e1" },
        { key = IssueYear, value = "2013" },
        { key = ExpirationYear, value = "2024" }
      ]
    }
  ]
```

### 11. `calc` and `rewrite` proofs

**`calc` hugs the `:=` when its first line fits; the steps drop to 2.** (`std/Nat/Divides.sw:79`)

Before:

```text
theorem Nat.modAddOfModZero ∀ (x: Nat) (z: Nat) (m: Nat) (h: z % m = 0): (x + z) % m = x % m :=
  calc (x + z) % m
    _ = (x + z % m) % m := Eq.sym (Nat.addModMod x z m)
    _ = (x + 0) % m := rewrite h in rfl
    _ = x % m := rewrite Nat.addZero x in rfl
```

After:

```text
theorem Nat.modAddOfModZero ∀ (x z m: Nat) (h: z % m = 0): (x + z) % m = x % m := calc (x + z) % m
  _ = (x + z % m) % m := Eq.sym (Nat.addModMod x z m)
  _ = (x + 0) % m := rewrite h in rfl
  _ = x % m := rewrite Nat.addZero x in rfl
```

**A `rewrite` that does not fit: the rule arguments one per line at +6, the result below at +2.** (`std/Map/Spec.sw:1125`)

Before:

```text
          rewrite Map.Spec.lookupConsEntrySkip key kk (Map.Spec.mapMaybe f rest) (z => Ordering.lessNotEqual (Eq.trans (Eq.sym d) z)) (f kk vv) in
          Map.Spec.lookupMapMaybe f key (Some kk) rest arest
```

After:

```text
          rewrite Map.Spec.lookupConsEntrySkip key kk
                (Map.Spec.mapMaybe f rest)
                (z => Ordering.lessNotEqual (Eq.trans (Eq.sym d) z))
                (f kk vv) in
            Map.Spec.lookupMapMaybe f key (Some kk) rest arest
```

### 12. `if` / `else` chains

**`if c then` / `else if d then`: one clause per line; each result below if too long.** (`std/Map/Spec.sw:986`)

Before:

```text
    if Map.Spec.isLess x.fst y.fst then Map.Spec.consEntry x.fst (Map.Spec.merge both onlyLeft onlyRight xs [y, ..ys]) (onlyLeft x.fst x.snd)
    else if Map.Spec.isLess y.fst x.fst then Map.Spec.consEntry y.fst (Map.Spec.merge both onlyLeft onlyRight [x, ..xs] ys) (onlyRight y.fst y.snd)
```

After:

```text
    if Map.Spec.isLess x.fst y.fst then
      Map.Spec.consEntry x.fst (Map.Spec.merge both onlyLeft onlyRight xs [y, ..ys]) (onlyLeft x.fst x.snd)
    else if Map.Spec.isLess y.fst x.fst then
      Map.Spec.consEntry y.fst (Map.Spec.merge both onlyLeft onlyRight [x, ..xs] ys) (onlyRight y.fst y.snd)
```

**A chain inside a hugged lambda.** (`std/Parse/Parse.sw:707`)

Before:

```text
    |> .map (what => if endsLine ∧ what == "a line break" then "the end of the line" else if what == "the end" then endOfInput else what)
```

After:

```text
    |> .map (what =>
      if endsLine ∧ what == "a line break" then "the end of the line"
      else if what == "the end" then endOfInput
      else what)
```

**A two-way `if` too long for a line: `else` starts the next line.** (`aoc/src/Aoc/Year2020/Day14/Proofs/Parse.sw:41`)

Before:

```text
    if startsWithMask instructions then ({ instructions }: Program) else Fail.fail "the program has to start with a mask"
```

After:

```text
    if startsWithMask instructions then ({ instructions }: Program)
    else Fail.fail "the program has to start with a mask"
```

### 13. Interpolated text and `let`

**A string is never split, so the call breaks around it.** (`aoc/src/Aoc/Year2020/Day11/Day11.sw:27`)

Before:

```text
  IO.print "Part 1: ${layout.settledOccupied adjacentRule |> .orFail "the seats didn't settle within ${roundLimit} rounds"}"
  IO.print "Part 2: ${layout.settledOccupied layout.sightRule |> .orFail "the seats didn't settle within ${roundLimit} rounds"}"
```

After:

```text
  IO.print
    "Part 1: ${layout.settledOccupied adjacentRule |> .orFail "the seats didn't settle within ${roundLimit} rounds"}"
  IO.print
    "Part 2: ${layout.settledOccupied layout.sightRule |> .orFail "the seats didn't settle within ${roundLimit} rounds"}"
```

**A string too long even for its own line stays long.** (`aoc/src/Aoc/Year2021/Day12/Day12.sw:83`)

Before:

```text
  | Some (index, passage) => Fail.fail "line ${index + 1}: ${passage.from.name}-${passage.to.name} joins two big caves, so a path could cross it back and forth forever and there would be infinitely many paths"
```

After:

```text
  | Some (index, passage) =>
    Fail.fail
      "line ${index + 1}: ${passage.from.name}-${passage.to.name} joins two big caves, so a path could cross it back and forth forever and there would be infinitely many paths"
```

### 14. Comments

**Comments stay with the code below them and move with it.** (`aoc/src/Aoc/Year2021/Day02/Proofs/Proofs.sw:62`)

Before:

```text
      -- `cases` would leave the forward move's `start.aim + 0` as it is: it
      -- doesn't split a record's field (SW-1913).
      match command with
        | Forward _ => rewrite Int.addZero start.aim in omega
        | Down _ => omega
        | Up _ => omega
```

After:

```text
        -- `cases` would leave the forward move's `start.aim + 0` as it is: it
        -- doesn't split a record's field (SW-1913).
        match command with
          | Forward _ => rewrite Int.addZero start.aim in omega
          | Down _ => omega
          | Up _ => omega
```

### 15. Header form

**`main()` becomes `main ()` (see "Worth a look").** (`aoc/src/Aoc/Year2021/Day01/Day01.sw:23`)

Before:

```text
def main(): {IO, Fail} () :=
```

After:

```text
def main (): {IO, Fail} () :=
```


## Method and caveats

- The printer is the release binary from `main` (stage 3, merge 796bdcbe6);
  later changes to it will change these numbers.
- Per-file output came from `stitchwort dev fmt-tree --print FILE`, with the
  trailing summary stripped, then compared with the original by
  `git diff --no-index`. The scratch copies are not kept in the repo.
- Line counts are text lines. "Regions" are git's `-U0` hunks with patience
  matching, so one reflowed declaration is one region.
- The pattern counts for the kinds table come from regular expressions over
  those regions, not from the printer; treat them as good to about 10%.
- 101 files that don't parse (the rejection examples for syntax errors) are
  excluded from every number and every sample.
