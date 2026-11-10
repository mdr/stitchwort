# `∧` on `Bool`s in a proposition: D3486 decided (SW-2735)

**Status:** decided, 10 November 2026. Matt delegated D3486 to this lane
("Do a short Fable 5.2 paper lane to decide"). **Decision: yes, as
[bool-as-proposition.md](bool-as-proposition.md) §4.3 recommends**, with the
rule stated by position (§4) and the printer's exceptions spelled out (§5).
Paper lane: no build, no tests; one probe file, run with the release CLI at
`d93fe49f4`. Migration cost is not counted (D2303).

Marks: **[measured]** run or counted today; **[checked]** read in the code or
docs at the place given; **[memory]** prior art recalled, not re-read;
**[inferred]** reasoning, not run.

## 1. The question

`∧` and `&&` are one token (D1200, `docs/syntax.md:13`). D3482 lets a `Bool`
stand where a proposition is expected, meaning `b = True`. So `a ∧ b` on two
`Bool`s in a statement could be either of two terms:

- **the proposition** `a = True ∧ b = True`: an `And` of two facts;
- **the test fact** `(a && b) = True`: one equation about one `Bool`.

Each implies the other; they are not the same term.

## 2. What tells them apart today

**[measured, [`today.sw`](bool-operators-in-propositions/today.sw)]**

| | the proposition | the test fact |
|---|---|---|
| prints as | `a = True ∧ b = True` | `(a && b) = True` |
| `match h with \| Both l r` | checks | `E-TYPE-MISMATCH` (until readings, stage 2) |
| `rewrite h` in a goal with `if a && b` | `E-REWRITE-RULE`: not an equation | checks |
| closed, `True` and `True`: `rfl` | `E-TYPE-MISMATCH` | checks, by computing |
| what `if h: a = True && i < xs.length` gives | `h: a = True ∧ i < xs.length` | (never) |

So the proposition is the form with parts, and the test fact is the form
that computes and rewrites. Readings and crossing
(bool-as-proposition.md §5 to §7) will convert between them, but `rewrite`,
`rfl` and `match h:` will always see which one a term is.

How often each is written, by `grep -E` over `.sw` files **[measured;
line counts, approximate]**:

| | `∧` or `∨` with an `= True` operand | `(… && …) = True` or `(… \|\| …) = True` |
|---|---|---|
| `crates/elab/src/std` | 53 | 5 |
| `aoc/src` | 104 | 10 |

Typical of the first: `read ≠ [] ∧ read.all Parse.isDigit = True ∧ n =
Parse.digitsValue read` (`2020/Day02/Proofs/Parse.sw:15`), `gate ∈
device.gates ∧ gate.ready values = True` (`2024/Day24/Proofs/Part1.sw:76`).
Typical of the second: `onMap: (position.row < risks.height &&
position.column < risks.width) = True` (`2021/Day15/Proofs/Search.sw:31`), a
fact that came from a program's `if`. Written statements want the logical
`∧` about ten times as often as the test.

## 3. The options

1. **Operators are logical; `Bool`s coerce at the leaves** (the note's
   recommendation). `a ∧ b` is `a = True ∧ b = True`. The test fact is
   written and printed `(a && b) = True`.
2. **Two `Bool` operands make the test**, printed `a && b`. Then
   `c.isDigit ∧ d.isDigit` is a test fact and `c.isDigit ∧ x < 3` is an
   `And`.
3. **The elaborator picks by context**: the test where something nearby
   wants an equation (a `rewrite` rule, an `rfl`), the proposition
   otherwise.
4. **Rule 1, with a bare printed form for the test fact**: print it `a &&
   b` and the proposition `a ∧ b`, or print it `a.and b` or `(a && b:
   Bool)`.
5. **Make the two terms one**, so the choice stops mattering: define `∧` on
   coerced `Bool`s to be the test, or the test to be the `And`.
6. **Rule 1 or 2, plus a warning** on `a ∧ b` with two `Bool` operands.

## 4. The decision

**Option 1. Which operator `∧`, `∨` and `¬` are is settled by the position
alone, never by the operands' types:**

- where a proposition is expected, they are `And`, `Or` and `Not`, and each
  operand is again a position where a proposition is expected, so a `Bool`
  operand `b` there is `b = True`;
- where a `Bool` is expected, or nothing is known, they are the test, as
  today (`docs/syntax.md`, "`&&`, `||` and `not`");
- the test fact is written with its `= True` or `= False`, whose left side
  is not a proposition position: `(a && b) = True`.

So `a ∧ b` is `a = True ∧ b = True`, `¬a` is `¬(a = True)`, `a → b` is `a =
True → b = True`, and `xs.all (x => p x ∧ q x)` still has the test inside,
because `all` expects a `Bool`.

Reasons, in order of weight:

- **One sentence, and no silent change of kind.** Under option 2, adding
  `∧ x < 3` to `c.isDigit ∧ d.isDigit`, or changing a field from `Bool` to
  a proposition, turns an equation into an `And`: every `rewrite h`, `rfl`
  and `Both l r` on it changes meaning or stops checking, with no edit at
  those places. Under option 1 the statement's shape is what was written.
- **It is what `if` already gives.** `if wanted && i < xs.length` hands its
  branch `wanted = True ∧ i < xs.length` (`docs/syntax.md:1859`), and `if
  h: p && q` gives `h: p ∧ q` (`:1856`) **[checked; the second measured]**.
  Under option 2, `if h: a && b` on two `Bool`s would be the one `if` whose
  `h` is not a conjunction.
- **Both terms keep a spelling.** Under option 1 the proposition is `a ∧ b`
  and the test fact `(a && b) = True`. Under option 2 the proposition, the
  one written ten times as often (§2), has only the long form `a = True ∧ b
  = True`, and prints that way. The readings themselves need it:
  `Bool.andReading: Decidable (a ∧ b)` with `does = a && b`
  (bool-as-proposition.md §5.1) says nothing under option 2.
- **A statement with `∧` has parts at once.** `Both l r`, `h.left`, `auto`
  and `omega` use a conjunction's parts today (`docs/syntax.md:1859`, last
  sentence), with no reader. Under option 2 they wait for stage 2's
  readings, and go through `sound` ever after.
- **The `= True` that stays carries information.** It marks the form that
  `rewrite` can use and that computes. Those facts mostly come from
  programs (a `match e:`, a `filter`, an unfolded definition), where the
  reader of a goal wants to know that is what they hold.

What option 1 costs: D3482's "printed without `= True`" holds for every
fact except a test whose top is `&&` or `||`; and a closed goal `a ∧ b`
needs `Both rfl rfl`, `cases` or `auto` where the test fact needs one
`rfl`.

Why not the others:

- **3, by context.** The same statement would be two different terms in
  two files, depending on proofs far from it; a statement's hash would
  depend on its uses. It also can't be told from the printed form.
- **4, a bare print for the test.** `h: a && b` beside `k: a ∧ b` asks the
  reader to see a difference the language says does not exist (D1200), and
  `a && b` pasted into a statement reads back as the other term, so the
  print-then-read-back property (bool-as-proposition.md §4.4) fails.
  `a.and b` is not the term either: `&&` is `if a then b else False`, no
  call of a function **[checked, `logic.rs:5`]**. `(a && b: Bool)` reads
  back but is longer and odder than `= True`.
- **5, one term.** `And` is an inductive proposition and `(a && b) = True`
  an equation; no definition makes them convertible. Elaborating one as
  the other is option 2, or loses the test fact altogether (and with it
  `rewrite` on a program's condition). Crossing (D3488) is the honest
  version of this option: it makes the choice not matter where a type
  mismatch would otherwise be, and leaves the terms distinct.
- **6, a warning.** Under option 1 the form is not ambiguous, and it is
  the form std and AoC statements should use; warning on it punishes the
  good spelling.

Prior art, all **[memory]**: SSReflect has two notations, `a && b` (coerced
by `is_true`) and `a /\ b`, joined by `andP`; Lean 4 has `&&` (`Bool.and`)
and `∧`, where `a ∧ b` on `Bool`s coerces each side and `simp` normalises
`(a && b) = true` to `a = true ∧ b = true`; Agda has `T (a ∧ b)` against
`T a × T b`. All three keep two terms and give each a spelling; none picks
by operand type. With one token for both, Stitchwort can give only one of
them the bare spelling, and Lean's normal form is the logical one.

## 5. What SW-2734 must do

Nothing in the design changes: SW-2734 was briefed to option 1. These are
the exact rules, including two points §4.3 and §4.4 left open.

**Elaborator.**

1. In `check_type` (`check.rs:7016`), `logic::classify` still runs first:
   `&&`, `||`, `not`/`!` where a proposition is expected are `And`, `Or`,
   `Not`, whatever their operands are. Never look at the operands' types to
   choose. Each operand is elaborated by the same `check_type`, which is
   where a `Bool` operand becomes `b = True`.
2. The coercion itself comes after `infer`, on the whole inferred term:
   when its type is `Bool` and a proposition is expected, the result is
   `term = True`. So forms that `check_type` does not take apart are
   coerced whole: `(h: if c then a else b)` is `(if c then a else b) =
   True`, not an `if` between two equations **[inferred from
   `check.rs:7016-7052`: only the logic operators are classified before
   `infer`]**. Brackets change nothing: `(a && b)` in a proposition is
   still the `And`.
3. `if h: a && b` on two `Bool`s gives `h: a = True ∧ b = True`, and the
   plain `if a && b` whose branch uses the proof gives the same (SW-1305
   does so already for a `Bool` operand). The `else` branch gets
   `¬(a = True ∧ b = True)`. No `if` produces `(a && b) = True` except
   through `match e: a && b with`.
4. The sides of `=`, a `Bool`-expected position, and an unknown expected
   type are unchanged: there `&&` is the test (bool-as-proposition.md
   §4.1).
5. No warning and no new error. `E-NOT-A-TYPE`'s `Bool` notes go, as §4.6
   of the note says.

**Printer.** `e = True` prints as `e` **only when `e`'s printed form does
not start, at its top, with an operator that `logic::classify` takes in a
proposition position**: `&&`, `||`, and prefix `!` or `not`. Those keep
`= True`. Concretely:

| Term | Prints as |
|---|---|
| `a = True ∧ b = True` | `a ∧ b` |
| `(a && b) = True`, `(a \|\| b) = True` | unchanged |
| `(a && b) = True ∧ c = True` | `(a && b) = True ∧ c` |
| `xs.any (x => p x && q x) = True` | `xs.any (x => p x && q x)` (the `&&` is under a `Bool` position) |
| `(if c then a else b) = True` | `if c then a else b` in brackets where needed (rule 2 reads it back whole) |
| `Bool.not a = True` | `a.not`, never `!a` or `not a`, which read back as `¬(a = True)` |
| `(a && b) = False`, `b = False` | unchanged |

The read-back test in SW-2734's brief is the check on this table: for each
printed hypothesis, elaborating the text as a proposition gives the same
term. It should include a test fact as an operand of `∧`, a test under a
lambda, an `if` and a `match` as the test, and `Bool.not`.

**Docs.** `docs/syntax.md:1856` changes from "both operands must be
propositions" to the rule in §4, with `(a && b) = True` named as the way to
write the test fact. The proving guide's "Writing statements" should say:
state facts with `∧`; write `(a && b) = True` only for a fact a program
hands you and you mean to `rewrite` with.

## 6. Findings for tickets

- `rewrite h` with `h: a ∧ b` on `Bool`s fails with "isn't an equation"
  (§2). Once statements are written bare, a note there would help: "`h` is
  a conjunction; rewrite with `h.left` and `h.right`, or state the test as
  `(a && b) = True`".
- bool-as-proposition.md §4.4 names only `&&` and `||` as the printer's
  exceptions; prefix `!`/`not` belongs in the list (it is covered there
  only by the `a.not` row).
- The stage 6 sweeps should leave the 15 `(… && …) = True` statements as
  they are, and not "tidy" them to `∧`: several are rewritten with.
