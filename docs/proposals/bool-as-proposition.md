# Reading a `Bool` fact as a proposition (SW-2704)

**Status:** draft 2, 12 November 2026. Stages 1 (§4, SW-2734), 2 (§5, §6,
§6.8, SW-2977) and 3 (std's readings, the stuck-decision step, the
`W-DECISION-TEST` warning and the `.read` note: SW-2967, SW-3019, SW-3029,
SW-3031) are built; see §11 for what stage 3 settled. Follows D3482 (Matt,
10 November 2026: yes, after a design note) and
[bool-and-prop.md](bool-and-prop.md) §7.3 and §7.5. Decided: D3486 (§4.3),
D3487 (§5), D3488 (§7) and D3531 (§6.8), see [§12](#12-decisions-for-matt).
Draft 2 folds in the review of draft 1,
[SW-2964-bool-reader-review.md](../reviews/SW-2964-bool-reader-review.md),
whose recommendations Matt accepted: a reading is a marked `↔` theorem, one
per test, declared with the test; an explicit word, `.read`, instead of
silent crossing; the revised plan. Draft 1 read the code at `f55b2381b`,
the review at `cd8ac0d08`. Migration cost is not counted (D2303).

It builds on D3480's `Decidable`, the record `{ holds: Bool, sound,
complete }` (D3483; [decidable-record.md](decidable-record.md), built).

How claims are marked:

- **[measured]**: run with the release CLI on the probe files in
  [bool-as-proposition/](bool-as-proposition/), or counted with `grep -w`
  over `std`, `aoc/src` and `games`. Counts include each helper's own
  definition.
- **[checked]**: read in the code or a note, at the place given.
- **[cited]**: read at the link given ([Sources](#sources)).
- **[memory]**: prior art recalled, not re-read.
- **[inferred]**: reasoning; not run and not cited.
- **[review]**: from the SW-2964 review, which marks its own claims.

## 0. Summary

**The problem.** A fact that comes from a program is a test giving `True`:
`(s.contains k && xs.any p) = True`. It has no constructors, so a proof takes
it apart with helper lemmas, and the `= True` was noise in every statement.
Across std and AoC there are about 650 calls of the take-apart helpers
(`Bool.andLeft`, `List.anyTrueElim` and their like) and about 615 calls that
carry a fact between a test and its proposition (`DecEq.sound`,
`(List.memContains xs x).forward`) **[measured, §8.4]**.

**The change**, in four parts:

1. **A `Bool` where a proposition is expected means `b = True`**, and is
   printed as `b`. The logical operators stay logical: `a ∧ b` on two `Bool`s
   is the proposition "`a` and `b`", not the test `a && b` (D3486). Built
   (stage 1).
2. **Readings.** A reading says what proposition a test decides: an ordinary
   proved theorem `test = True ↔ P` (or `test = False ↔ P`), marked
   `@[reading]` (D3487). Each test has at most one reading of each polarity,
   declared beside the test's function. Std declares them for `&&`, `||`,
   `not`, then `any`, `all`, `contains`, `Nat.equal` and so on. Nothing is
   trusted: the elaborator only writes `reading.forward h` or
   `reading.backward p`, which the kernel checks.
3. **Patterns and constructors go through readings.** `match h with | Both
   inSet (Witness x (Both xIn px))` on the fact above works: each
   constructor pattern reads the test under it, one layer at a time.
   Writing `Both l r` where `(a && b) = True` is wanted works too.
4. **`.read`** (D3488, D3531): `found.read`, for `found: xs.contains x`, is
   the whole fact as its proposition, `x ∈ xs`. It works in every position,
   including `rewrite` rules and untyped `let`s. A fact is never converted
   silently (§7).

**What it should do.** 2024 day 8's `part2IncludesPart1` goes from 17 lines
and 12 helper calls to about 7 lines and none **[inferred; its two inner
steps measured in `readings.sw`]**. About 650 helper calls become patterns
and constructors, and most of the 615 crossings become one word, `.read`,
instead of thirty lemma names **[measured counts; that each one goes is
inferred]**. Code that checks today is unaffected: the reader runs only
where there is a type error today and the elaborator isn't trying one
reading before another; the acceptance check is that no example's hash
changes (§13).

Stage 1 is built; the rest is about 20 lane-hours **[estimated]**, in
[§11](#11-staged-plan).

## 1. Words

- **Test**: an expression of type `Bool`.
- **Test fact**: a proof of `e = True` or `e = False` for a test `e`. Its
  **polarity** is which.
- **Reading**: a theorem `e = True ↔ P` or `e = False ↔ P`, marked
  `@[reading]`. `P` is what the test "reads as" at that polarity.
- **Reader**: the elaborator function that, given a test and a polarity,
  finds its reading.
- **Crossing**: turning a test fact into its reading (`r.forward h`), or back
  (`r.backward p`). Written `.read` (§6.8); never silent (§7).

## 2. Today

Stage 1 is built (SW-2734, `288c2d7fe`, D3482): `(h: b)` for `b: Bool`
checks as `b = True`, goals print `b = True` as `b`, and the old
`E-NOT-A-TYPE` notes for `Bool`s are gone (`docs/syntax.md`, "A `Bool` as a
proposition"). What is still as draft 1 found it **[measured, `today.sw`;
checked again by the review]**:

- `match h with | Both l r` on `h: (a && b) = True` is `E-TYPE-MISMATCH`,
  "these patterns match a `And`, but the argument has type …" (`lib.rs`,
  `check_tree`, checked).
- `h: a = True` and `k: a = False` together don't close a goal: `cases`
  finds no contradiction.
- `∧` and `&&` are one token (D1200). Where a proposition is expected it is
  `And`; elsewhere the `Bool` reading is tried first (`logic.rs:1-19`,
  checked).
- `omega` reads `(p && q) = True`, `(p || q) = True`, `not p`, both
  polarities, and a decision's test through the decision (`d.holds = True`
  by `d.sound`, `= False` by `Decidable.refute`), through bridge lemmas it
  names in Rust (`omega.rs:123-163`, `bool_form`, checked). `auto` has its
  own smaller version for conjunctions (`auto.rs:36-38`, checked).
- `Decidable` instances are found from the proposition, one per head
  (`interfaces.rs:14-24`, checked). Nothing goes from a test to a
  proposition.
- `deriving (DecEq)` still answers by `Decidable.yes`/`no` under a match
  (`derive.rs:49-56`), so a derived `==` on unknowns is stuck on the
  decision; and `List.decMem`, `decDistinct`, `decSorted` and `decLeHead`
  recurse on the list, so their `holds` is not the test std's functions
  use (`if x ∈ xs` and `if xs.contains x` are different tests) **[review,
  §1]**.

## 3. Prior art

### 3.1 SSReflect: a coercion and named views

- `Coercion is_true (b : bool) := b = true`; the printer hides it
  **[cited: R1, "Boolean reflection"; G1 §4.1]**.
- `reflect P b` "asserts that `(is_true b)` and `P` are logically equivalent
  propositions" **[cited: R1, "The reflect predicate"]**. View lemmas are
  named with a `P`: `andP`, `orP`, `negP`, `hasP` **[cited: R1; `hasP` from
  memory]**.
- **The user names the view.** `move/andP`, `case/orP`, `apply/andP`: for
  `case/term`, "the generalisation step is replaced by a case analysis step"
  **[cited: R1]**. `move=> /andP [h1 h2]` reads and takes apart in one step
  **[cited: G1 §4.1.1]**.
- **View hints.** "The view mechanism can insert automatically a view hint":
  the engine "automatically detects from the shape of the top assumption"
  which adapter to use (`iffLR`, `introN`; `elimT` and `introT` in `ssrbool`
  **[memory]**). `Hint View` adds adapters **[cited: R1]**.
- **Negation** is handled by more adapters: `introNTF` concludes `~~ b = c`
  from `if c then ~ P else P` **[cited: R1]**.
- The stated cost: newcomers must learn the view names and the `/` syntax
  **[memory]**.

**Taken from it:** the hidden coercion; one lemma per connective that goes
both ways; adapters chosen from the fact's shape. **Not taken:** naming the
view at each use. Here the pattern says which shape is wanted, and the test
says which reading has it.

### 3.2 Lean 4: a coercion, and `simp` with `propext`

- "There is a coercion from every `Bool` `b` to the proposition `b = true`"
  **[cited: L2]**. It is unfolded when elaborated, so goals show `b = true`,
  not `b` **[inferred from L2: the coercion's target is the equation, and
  elaborating it leaves the equation]**. Lean 3 showed `↑b` **[cited: Z3,
  for Lean 3]**. So bool-and-prop.md §7.5's appeal to Lean's example was
  right for SSReflect only; that note is corrected (SW-2714).
- `&&` is `Bool.and` and `∧` is `And`: different notations, never one for
  the other **[cited: L2]**. `a ∧ b` on `Bool`s coerces each side
  **[memory]**.
- The reader is `simp`: `Bool.and_eq_true: ((a && b) = true) = (a = true ∧
  b = true)`, `Bool.or_eq_true`, `Bool.not_eq_true: (¬b = true) = (b =
  false)`, `decide_eq_true_eq: (decide p = true) = p`, all `@[simp]`
  **[cited: L4]**. They are equations between propositions, so they need
  `propext`, which D3481 rules out.
- Mathlib's users report the crossing as the pain point **[cited: Z1, in
  bool-and-prop.md §3.3]**.

**Taken from it:** the coercion's meaning; `∧` staying logical on `Bool`s;
the choice of lemmas (Lean's simp set is the list of readings to declare).
**Not taken:** rewriting with them.

### 3.3 Agda: `T` and `Reflects`

- `T : Bool → Set` turns a test into a type **[memory]**. `Reflects A b` has
  `ofʸ : A → Reflects A true` and `ofⁿ : ¬ A → Reflects A false`
  **[cited: A4]**.
- Readings are built by hand from combinators: `T-reflects`, `¬-reflects`,
  `_×-reflects_ : Reflects A a → Reflects B b → Reflects (A × B) (a ∧ b)`,
  `_⊎-reflects_`, `_→-reflects_` **[cited: A4]**. `invert` gives the proof
  once the `Bool` is known. Nothing finds a reading from a test.

**Taken from it:** the readings compose by the test's structure, so the
reader can work one layer at a time.

### 3.4 Views of data

- Wadler's views (1987) let a type be matched through another type's
  constructors, by a pair of conversion functions **[cited: V2, abstract and
  summary; paper not re-read]**.
- McBride and McKinna (2004) generalise this for dependent types: a view is
  a type family indexed by the thing viewed, with a function that covers
  every value; matching on the view's constructors refines the thing viewed
  **[cited: V3, abstract; the mechanism from memory]**.
- Haskell's view patterns and F#'s active patterns name the conversion in
  the pattern **[memory]**.

A reading is a view of a *fact*, not of data. That makes it much simpler
than the general case: proofs are erased and any two proofs of a test fact
are equal (K), so nothing has to be refined when a fact is viewed, and
nothing happens at run time. `sound` is the covering function.

## 4. The coercion

### 4.1 Where a `Bool` is accepted

Wherever a proposition is expected and the expression has type `Bool`
**[inferred from `check_type`, `check.rs:7016-7052`]**:

- a theorem's statement, a binder's type (`(h: c.isDigit)`), `∀` and `∃`
  bodies, a type ascription, `if h: b`, `let h: b := …`;
- each operand of `∧`, `∨`, `¬`, `→`, `↔` in a proposition;
- an argument whose expected type is exactly `Prop`: the body of `x => f x`
  given for `a → Prop`, or `Decidable b`.

Not accepted:

- where a `Type` is needed (`List b`): still `E-NOT-A-TYPE`;
- a function `f: a → Bool` given for `a → Prop`: an error whose note says to
  write `x => f x` (an implementation call whether to do that silently
  later);
- the two sides of an `=`. `(a != b) = !d` stays the error it is today
  (`reject/not-a-type-not-equal-statement`, checked): coercing `!d` there
  would quietly turn a comparison of `Bool`s into an equation between
  propositions;
- where the expected sort is not known yet.

### 4.2 What it means

`b` becomes `b = True`: the same term as writing it out, so hashes of
existing statements don't depend on which was written.

### 4.3 The logical operators (D3486)

**Decided: yes, the rule below** (D3486, SW-2735, 10 November 2026):
[bool-operators-in-propositions.md](bool-operators-in-propositions.md).

`∧` and `&&` are one token, so `a ∧ b` on two `Bool`s in a proposition could
mean either of two different terms:

- the proposition `a = True ∧ b = True`, or
- the test fact `(a && b) = True`.

They are equivalent but not the same term: `rewrite`, `rfl` and `Both` see
the difference.

**Recommended rule: an operator written in a proposition is always the
logical one; a `Bool` is only coerced at the leaves.** So `a ∧ b` is `a =
True ∧ b = True`, `c.isDigit ∧ x < 3` is `c.isDigit = True ∧ x < 3`, and
`¬b` (also written `!b`) is `¬(b = True)`. This is today's rule with the
operands coerced, and Lean's **[memory]**.

The test fact is written with its `= True`: `(a && b) = True`. The left of
an `=` is not a proposition position, so there `&&` is the test, as today
**[measured, `today.sw` and §2]**. In practice such facts are rarely
written; they come from programs (an `if`, a `filter`, a definition
unfolding).

Why not the other rule ("two `Bool` operands make a test"):

- `c.isDigit ∧ d.isDigit` would be a test and `c.isDigit ∧ x < 3` a
  proposition, so adding a conjunct changes the term's kind;
- it can't be said in one sentence;
- the next step along that road is "any two decidable operands make a
  test", which is option 2 of bool-and-prop.md, already turned down.

### 4.4 Printing

One rule: **`e = True` prints as `e`, unless that text would read back as a
different term.** With §4.3's rule the exceptions are the tests whose top
is `&&` or `||`, which keep `= True`:

| Term | Prints as |
|---|---|
| `s.contains k = True`, `c.isDigit = True`, `xs.any f = True`, `b = True` | `s.contains k`, `c.isDigit`, `xs.any f`, `b` |
| `Nat.leq a b = True` | `a ≤ b` (today) |
| `a = True ∧ b = True` | `a ∧ b` |
| `(a && b) = True` | `(a && b) = True` (today) |
| `¬(b = True)` | `¬b` |
| `b = False` | `b = False` |
| `Nat.leq a b = False` | `(a ≤ b) = False` (today `(a <= b) = False`) |
| `Bool.not a = True` | `a.not` |

The `= True` that stays is useful: it marks a fact as a program's test, the
thing `rewrite` can use and a `match h:` refines.

`b = False` is not printed as `¬b`. They are different terms, and `rewrite`
wants the first.

### 4.5 Folding comparisons in goals and errors

Goals, error labels and `rfl` notes all print through one printer
(`cx.show`, `pretty.rs`, checked). Two changes there:

- `Nat.leq a b` prints as `a ≤ b` in a `Bool` position too, with `≤`, not
  `<=`. With the coercion, the same text is right in both positions.
- The form `(a <= b).decTrue.toBool` that a note could show (bool-and-prop.md
  §7.5) went with `Decidable.toBool` (SW-2746, SW-2761): a decision's test
  is its `holds` field, which computes to the test.

### 4.6 The errors stage 1 changed

- `E-NOT-A-TYPE` stays for things that are neither types nor `Bool`s, and
  for the sides of an `=` (§4.1). Its `Bool` notes go (`logic.rs`,
  `check.rs:5216`), and two reject examples become accept examples
  (`and-bool-in-prop`, `if-proof-on-bool`, checked).
- `if h: b` on a `Bool` gives `h: b = True` in the first branch. The second
  should get `h: b = False`, the form `rewrite` wants; `h.read` turns it
  into `¬b` where that is wanted (§6.8). (SW-2703 owns `if h:`.)
- The note for `if h: a < b = True` ("the guard is already a proposition")
  stays.

## 5. Readings and the reader

### 5.1 What a reading is

An ordinary theorem, proved once, beside the test's function, marked
`@[reading]` (D3487):

```
@[reading]
theorem Bool.andReads (a b: Bool): (a && b) = True ↔ a ∧ b

@[reading]
theorem Bool.andReadsFalse (a b: Bool): (a && b) = False ↔ a = False ∨ b = False

@[reading]
theorem List.anyReads (xs: List a) (p: a → Bool): xs.any p ↔ ∃ (x: a) => x ∈ xs ∧ p x

@[reading]
theorem List.containsReads [auto eq: DecEq a] (xs: List a) (x: a): xs.contains x ↔ x ∈ xs
```

A positive reading may leave out its `= True`, as any statement may since
stage 1: `xs.any f ↔ …` is `xs.any f = True ↔ …`. The negative ones are
written as they read; no `not` encoding is needed. Std already has 27
lemmas of this shape, and AoC 33; they become readings by being marked (and
moved beside their function, §5.3) **[review, §2.2]**.

The starting set **[inferred]**, writing `∃ x ∈ xs, p` for `∃ (x: a) => x ∈
xs ∧ p` and `∀ x ∈ xs, p` for `∀ (x: a) => x ∈ xs → p`:

| Test | `= True` reads as | `= False` reads as | Stage |
|---|---|---|---|
| `a && b` | `a ∧ b` | `a = False ∨ b = False` | 2 |
| `a \|\| b` | `a ∨ b` | `a = False ∧ b = False` | 2 |
| `not a` | `a = False` | `a` | 2 |
| `xs.any f` | `∃ x ∈ xs, f x` | `∀ x ∈ xs, f x = False` | 3 |
| `xs.all f` | `∀ x ∈ xs, f x` | `∃ x ∈ xs, f x = False` | 3 |
| `xs.contains x` | `x ∈ xs` | `x ∉ xs` | 3 |
| `Nat.equal a b` (`a == b` on `Nat`) | `a = b` | `a ≠ b` | 3 |
| `s.isSubset t` | `∀ k ∈ s, k ∈ t` | (none at first) | 3 |
| `o.isSome`, `xs.isEmpty` | `∃ x, o = Some x`, `xs = []` | `o = None`, (none) | 3 |
| `Nat.leq a b`, `s.contains k`, `c.isDigit` | themselves | `Nat.leq a b = False` reads as `b < a` | 3 |

### 5.2 Why a marked `↔` theorem

Draft 1 proposed a `Decidable` definition marked `@[reading]`. The review's
comparison **[review, §2.3]**, in short:

| | `Decidable` definition (draft 1) | `↔` theorem (decided) |
|---|---|---|
| Where the test is | in the body, the `holds` field; found by evaluating it | in the statement: the left side |
| What a reader of std sees | `Decidable (a ∧ b)`; two readings of different tests have the same type | `(a && b) = True ↔ a ∧ b` |
| `= False` readings | encoded as `holds = not (a && b)` | written as they read |
| What the compiler emits | `r.sound h`, `r.complete p` | `r.forward h`, `r.backward p`: what proofs write by hand today |
| Existing lemmas | all rewritten as records | `List.memContains` and its like get the mark |
| Kind | a `def` in `Type`, whose body matters to what depends on it | a theorem: folded, and dependants see only its statement |
| A decision from it | is the reading | one line: `{ holds = test, sound = r.forward, complete = r.backward }` |

Not instance search, because instances are found from the proposition and
the reader starts from the test; and the readings of `&&`, `||` and `not`
and the negative ones are not instances of anything. Not a table in Rust
(today's `omega`), because it can't grow with the library, and a project's
own collection type couldn't have readings. Not named views (SSReflect's
`case/andP`): the pattern already says which shape is wanted.

`@[reading]` is the first attribute allowed on a theorem (`attributes.rs`,
checked). An `instance` can't carry it: an instance is a `Decidable`, not
an `↔`. Where an instance's test should read as its proposition, the
reader's stuck-decision step (§5.4, step 2) does it with no declaration.

### 5.3 How a reading is declared

When a `@[reading]` theorem is checked, the elaborator looks at its
statement, `∀ params, lhs ↔ P`, and files it under **(polarity, head of the
test)**. It is refused, with the error named, if:

- **`E-READING-SHAPE`**: the statement isn't an `↔`; its left side isn't `e
  = True` or `e = False` (or a bare `Bool` `e`, which is `e = True`); `e`
  isn't a call of a function defined by the program or the library (a
  variable, a constructor or a constant has no parts to read); the call's
  arguments aren't the theorem's parameters, each exactly once (as an
  instance's head is a type applied to distinct variables), so that
  matching a test against it only reads off its arguments (one exception,
  SW-3029: a function over a row `{e}`, such as `List.any`, is stated with
  pure arguments, which pass the empty row and its divergence `Total`
  instead of a parameter; a test fact's test is a `Bool`, which `{e} Bool`
  is only at the empty row, so the reading of a function whose result is
  `{e} Bool` still fits every test fact with its head; the reader checks
  the row is empty before using it, so a rare function whose result is
  `Bool` whatever its callback's row fits only at the empty row); or `e` is an
  `if` other than `&&` and `||`; or the call passes the function more
  arguments than its definition takes (`def tiny: Nat → Bool := small`
  takes none, so `tiny n` unfolds to `small n` before it is read, and a
  reading filed under `tiny` could never be found; SW-2992);
- **`E-READING-OVERLAP`**: the same polarity of the same head already has
  a reading. The message names it. One reading per test (D3487): "what does
  `xs.contains x` read as?" then has one answer, which every error and a
  hover can print **[review, §2.4]**;
- **`E-READING-PLACE`**: it isn't declared with its test (D3487): in the
  library, in the same file as the test's function (the core counts as one
  file, since it is always loaded); in a project, in the same namespace.

The head is the function the call is of. `&&` and `||` are two `if`s
(`Bool.ifThenElse a (_ => b) (_ => False)` and `Bool.ifThenElse a (_ =>
True) (_ => b)`, `omega.rs`, `bool_form`, checked), so they count as two
heads of their own, and their readings, like `not`'s, live in the core.

**Why with the test** **[review, §2.5]**. The library loads its files on
demand, by the names a program mentions, and a pattern `Both l r` mentions
no reading. A reading in another file than its test's would work or fail
by whether something else had loaded that file: the bug std had twice,
for instances (SW-1362) and congruence lemmas (SW-1354). A test can only
appear in a term if its file is loaded, so a reading in the same file is
always there. The same rule makes the check cache right without a new
input (§5.7), and means importing a namespace never changes how a test
from elsewhere reads. What it costs: a project can't give a std test a
reading std forgot; it can still use the lemma by hand, or wrap the test in
a function of its own, which may have one.

### 5.4 How a reading is found

`read(test, polarity)`:

1. Look at the test as it is, with calls folded: the form the goal prints.
2. **A stuck decision** (stage 3). If the test is `d.holds` for a `d:
   Decidable P` that doesn't compute (a derived `==`, a hypothesis), it
   reads as `P` (or `¬P`), through `d.sound`, `d.complete` and
   `Decidable.refute`. No declaration needed.
3. Look up (polarity, head of the test). At most one theorem is there; its
   parameters are the test's arguments.
4. If none, and the head is a call that isn't `opaque`, unfold it one step
   and go to 1. So a project's `def isAntinode city p := city.antennas.any
   (…)` reads as `∃` with no declaration. At most 8 steps.
5. Otherwise the test is a **leaf**: it reads only as itself.

The reader works **one layer at a time**. `Bool.andReads`'s parts are `a =
True` and `b = True`, test facts again. A nested pattern asks again for the
part it touches. Nothing is searched: the pattern drives every step.

**Folded or unfolded** **[review, §2.4]**. `xs.contains x` is `List.any xs
(member => member == x)` by definition. Folded it reads as `x ∈ xs`; if a
`rewrite` or an unfolding has left the `any`, it reads as `∃`. The rule
that makes this predictable: the reader goes by the test as the goal prints
it (step 1). Both readings are equivalent to the test, so neither choice
can prove anything false. With gluing off (`STITCHWORT_GLUE=0`) a fact's
type has its calls unfolded already, so the reader starts from the type as
written (a variable's declared type, an annotation, a parameter's type,
the definition's own type) and evaluates with calls folded, and finds the
same reading as glued (SW-2992).

**Checking order (D3537, Matt, 12 Nov 2026).** Dependencies, not source
position, decide which uses see a reading. Each `@[reading]` theorem's
test function is known from its syntax before anything is checked (`f x…`,
`Ns.f x…`, `x.f y…`, with `↔` or `Iff (…) (…)`), and every declaration
that mentions that function gets an ordering edge after the reading, as
instances do, so a use above the reading, or in another file of the
namespace, is checked after it. The reading's own dependencies (a lemma
its proof uses) are left out, so no edge closes a cycle: they read the
test as what it unfolds to, as the reading's proof does, and an error
there says the reading isn't available because it depends on that
declaration. The library is written in an order that works and gets no
edges. A reading whose proof fails is filed as its stand-in (D3527), so
its users rely on it like any use of a failed theorem; one with no
stand-in fails them with `E-FAILED-DEPENDENCY`, which goes without saying
(SW-2992).

**Unfolding leaks implementations** **[review, §2.6]**. Step 4 lets `Both
lo hi` take apart `h: c.isDigit` by unfolding `isDigit` to its two
comparisons, so the proof depends on how `isDigit` is written. That is true
of any proof that unfolds a definition. `opaque` is the existing way to stop
it, and the reader respects it; a test meant to be abstract gets a reading
of its own or is `opaque`.

### 5.5 When none fits

- **Two readings for one key** can't exist (§5.3).
- **None fits.** A pattern, a constructor or `.read` is `E-NO-READING`
  (§6.7), which says what the test reads as, if anything.
- **Ambiguity is never a soundness or provability question.** Every reading
  of a test is equivalent to the test.

### 5.6 Unknowns and stuck terms

- **The test's head is an unknown** (`?f x`): it is a leaf for now, and a
  pattern on it reports that it can't be taken apart, as other patterns do
  on a type not known yet.
- **Unknowns inside the test** (`xs.any ?f`) don't block: the reading's
  parameters are the test's arguments, unknowns included. The reader never
  solves an unknown.
- **A variable or an unknown function's call** (`b`, `p x`): a leaf. Its
  fact can be matched only by a name, `_`, or `()` when it computes to
  `False = True`.
- **A test that computes to `True` or `False`** is not read. `False = True`
  is matched by `()` as today.
- **A folded call** (`small 3`) is looked up by its function first, as
  written, before anything it computes to: `small 3` reads by `small`'s
  reading even though it computes to `True`. A declaration's own test is
  read from its statement as written, a term, never from its value.

### 5.7 Cost and the check cache

- Declaring: one look at the statement per reading.
- Finding: a lookup by head, reading off the arguments, and up to 8
  unfolding steps when the head has no reading. The bound should become one
  on work, not steps, if a large test is ever slow to reject.
- The reader is called from six places: a constructor or record pattern
  whose type is a test fact (the split, and compiling the pattern, which
  needs the record type), a constructor or a record literal checked against
  a test fact, `.read`, and a field of a fact (`h.left`, tried once on the
  reading when the fact has no such field). Each was an error before. So
  code that checks today calls it only where it failed before, and never
  inside one of the elaborator's try-one-reading-then-another paths (§13).
  A pattern or a constructor reads again while the reading is a test fact
  (§6.4), up to 8 readings; `.read` and a field read one.
- **The check cache** keys a unit by its own text and the keys of the units
  it needs (`cache/mod.rs`, header). A reading lives in its test's file or
  namespace, which is always among those, so a changed reading changes the
  key of everything that can use it. The readings themselves are one more
  table in an entry, as the instances are, and are replayed with it.

## 6. Patterns

### 6.1 Taking a fact apart

Where a constructor pattern meets a scrutinee of type `e = True` or `e =
False`, and the constructor's type isn't `=`, the elaborator reads `e` at
that polarity, and matches on `r.forward h` instead of `h`. The hook is the
place that reports the mismatch today (`lib.rs`, `check_tree`, checked).

This is every place patterns are written: `match`, equation arms, `let Both
l r := h`, and a lambda's parameter.

**`Refl` never triggers a reading** **[review, §4]**: `match h with | Refl`
on `h: b = True` substitutes `True` for `b`, as today, whatever `b` is. To
match the reading of `(x == y) = True` as an equation, write `match
same.read with | Refl`.

### 6.2 Nesting

```
theorem example (a b c: Bool) (h: (a && (b || c)) = True): b ∨ c :=
  match h with
    | Both ha (Inl hb) => Inl hb
    | Both ha (Inr hc) => Inr hc
```

`Both` reads `a && (b || c)` as `∧`; its second field has type `(b || c) =
True`; `Inl` and `Inr` read that as `∨`. The term this stands for checks
**[measured, `nested` in `readings.sw`]**, and so does `Witness x (Both xIn
(Both small big))` on `xs.any (x => 3 ≤ x && x ≤ 5)` **[measured,
`anyNested`]**.

A name stops the reading: in `Both ha rest`, `rest: (b || c) = True` stays
a test fact, ready for `rewrite`.

### 6.3 With `match h:`

`match h: a && b with | True => … | False => …` is unchanged: it refines
the test in the goal and gives `h: (a && b) = True` or `= False`. Reading
`h` afterwards (`let Both ha hb := h`) gives facts and refines nothing. The
two don't interfere: one splits the `Bool`, the other takes apart a fact
about it.

### 6.4 Negation

- `h: e = False` is read through the negative reading: `match h with | Inl
  na | Inr nb` on `(a && b) = False` **[measured, `negative` in
  `readings.sw`]**.
- `(not e) = True` reads as `e = False` and `(not e) = False` as `e =
  True`, by `not`'s two readings; the reader reads the result again when the
  pattern asks.
- `.read` on a fact `e = False` with no negative reading gives `¬e` (that
  is, `¬(e = True)`) (§6.8).
- A new closer for `cases` and `auto`: `h: e = True` and `k: e = False` in
  scope close any goal. It needs no reader, and is its own ticket.

### 6.5 Exhaustiveness

After the reading, the scrutinee is an ordinary `P ∧ Q`, `P ∨ Q` or `∃`, so
the ordinary coverage check applies: an `∨` needs both arms. In a program
(a `def` returning data), a fact read as `∨` or `∃` can't be matched
(`E-PROP-ELIM`, as for any `∨`); there a program wants `match e: test with`.

In one column, the constructor patterns must agree on the type they match:
`| Both l r` in one arm and `| Refl` in another is an error. Names and `_`
mix with anything.

### 6.6 Building

- A constructor (`Both x y`, `Inl x`, `Witness x p`) checked against `e =
  True` or `e = False` reads `e` at that polarity, checks the constructor
  against the reading, and wraps it in `r.backward` **[measured, `build`]**.
- A field of a fact, `h.left`, is `h.read.left`.
- **Not built** **[review, §4]**: a lambda checked against a test fact, and
  a test fact applied to arguments (draft 1's `∀` hooks). They served few
  uses (`List.allMember` 18, `Set.isSubsetIntro` and `Elim` 5) and were the
  most surprising part: an equation's proof applied like a function.
  `allSmall.read y yIn` applies the function the reading gives, and a std
  function builds such a fact from a lambda.

### 6.7 Errors

```
[E-NO-READING] Error: `h` can't be taken apart with `Both`
  │ match h with
  │   | Both l r => …
  │     ───┬────
  │        ╰── `h` is the test fact `xs.isSorted`, which reads as `List.Sorted xs`
  │ Note 1: `Both` matches `And`; `List.Sorted xs` isn't one
  │ Note 2: a test fact can always be matched by a name
```

- For a leaf: "`b` has no reading, so the fact `b` has no parts", with a
  note on `@[reading]` when the head is a function of the program's own.
- For `.read` on a leaf at `True`: the same.
- The mismatch error where a test fact is given for its reading gets the
  note "`found` is the test `xs.contains x`, which reads as `x ∈ xs`: write
  `found.read`" (stage 3, once std's readings are in).

### 6.8 Reading a whole fact: `.read` (D3531)

`h.read`, for a test fact `h: e = True`, is the proposition `e` reads as,
proved by `r.forward h`; for `h: e = False`, the negative reading, or if
`e` has none, `¬e` (`¬(e = True)`).

```
rewrite same.read in …                    -- today: rewrite DecEq.sound same in …
let equal := same.read
Eq.sym same.read
| True => omega [(within _ found.read).right]   -- 2024 day 12, Sides.sw:226
let Both _ sameFrequency := same in … sameFrequency.read …
```

- **It works in every position**, including the 201 measured where silent
  crossing can't (rewrite rules, untyped `let`s, `Eq.sym`) **[review,
  §3.3]**. It needs no expected type, because each test has one reading.
- **It is one layer**, as a pattern is. `h.read.read` is two.
- **It fails at the word.** `b.read` on a leaf's fact is `E-NO-READING`.
- **It is the pattern hook's term** with no pattern round it.

The way back, a proposition to its test fact, has two cases **[review,
§3.4]**: where the wanted type is known, a constructor builds it (§6.6) and
otherwise the reading's `backward` is written by hand; where it isn't,
it is instance search: once each decision's `holds` is its test (§13), a
std function `[auto d: Decidable p] (h: p): d.holds = True` gives the test
fact. A word for it waits for stage 3's counts.

## 7. Silent crossing, deferred (D3488)

Draft 1 proposed converting a whole fact silently where its reading is
wanted, at a type mismatch. Decided: not now (D3488); `.read` instead,
and revisit after a measured sweep. The review's reasons **[review,
§3.2]**:

- **A test fact is itself an equation.** Where an equation is wanted,
  `(x == y) = True` fits as it stands, so there is no mismatch to hook in
  the commonest places such facts are used: `rewrite same in` (which
  silently rewrites `x == y` to `True`), `let equal := same`, `Eq.sym same`.
- **Whether there is a mismatch can depend on elaboration order**: for `f
  same` with `f: [x y: a] → x = y → …`, it depends on whether `a` is known
  yet.
- **The elaborator uses type errors to choose** between readings of `if
  c`, `&&` with nothing expected, and comparison sections. A crossing that
  turns such an error into a success sends a program that checks today
  down the other path, to a different term, with no error anywhere.
- **The win is smaller than draft 1 said**: of the 510 named uses, at most
  270 sit where a mismatch could occur; about 300 to 350 calls in all,
  not 615 **[review, §3.3]**.

If silent crossing comes later, it is "insert `.read` where the types
don't fit", only where the wanted type's head is known and is not `=`, and
only outside the try-and-fall-back paths; `e = False` against `¬(e =
True)` first. That is stage 4's measurement (§11).

## 8. The wins, on real code

### 8.1 2024 day 8, `part2IncludesPart1` (`Day08/Proofs/Part2.sw:191`)

Today **[checked]**, 17 lines: `Set.isSubsetIntro`, two rewrites with
`Set.containsFilter`, then `Bool.andIntro` twice, `Bool.andLeft` three
times, `Bool.andRight` twice, `List.anyTrueElim` twice and `List.anyOfMem`
twice. The four `any` calls each need their test's lambda written out in
full, up to 150 characters.

After **[inferred; to be measured once stage 3 is in, review §5.6]**:

```
theorem part2IncludesPart1 (city: City):
    (antinodeLocations city (isAntinode city)).isSubset (antinodeLocations city (isHarmonicAntinode city)) :=
  Set.isSubsetIntro (key has =>
    let Both onMap (Witness first (Both firstIn (Witness second (Both secondIn (Both same (Both inLine twice)))))) :=
      rewrite Set.containsFilter … at has in has
    rewrite Set.containsFilter … in
    Both onMap (Witness first (Both firstIn (Witness second (Both secondIn (Both same inLine))))))
```

About seven lines, no take-apart helpers. The lambdas go because the reader
takes each test from the fact's own type. `isHarmonicAntinode city key` has
no reading, so it is unfolded one step to its `any` (§5.4, step 4). The two
rewrites stay: an equation between tests is the right tool for `filter`
(bool-and-prop.md §6, point 4).

### 8.2 2024 day 12, `Sides.sw:226`

Today **[checked]**:

```
| True => Void.exfalso (omega [And.right (within { row, column = Succ last }
    ((List.memContains region.plots { row, column = Succ last }).forward found))])
```

After **[inferred]**: `| True => omega [(within _ found.read).right]`.

### 8.3 2024 day 8, `part2Correct` and `antennasAreAntinodes` (`:160`, `:177`)

- `Bool.andRight same` and the `DecEq.sound` round it become a pattern and
  a word: `let Both _ sameFrequency := same in … sameFrequency.read`.
- `antennasAreAntinodes` builds two nested `any` facts with `List.anyOfMem`
  and `Bool.andIntro`, lambdas in full; it becomes `Both (positionsOnMap …)
  (Witness first (Both firstIn (Witness second (Both secondIn (Both same
  (inLineSelf …))))))` **[inferred]**.

### 8.4 Counts

Uses across `std`, `aoc/src` and `games` **[measured, `grep -w`, at
`f55b2381b`; the review found them unchanged to within a few at
`cd8ac0d08`, except where marked]**:

| Removed by | Helpers | Uses |
|---|---|---|
| Patterns and building (stages 2, 3) | `Bool.andLeft` 175, `andRight` 194, `andIntro` 82, `orElim` 36, `orLeft` 15, `orRight` 20 | 522 |
| | `List.anyTrueElim` 41, `anyOfMem` 45, `allMember` 18 | 104 |
| | `Bool.orFalseLeft`/`Right`, `andFalseElim`, `notTrue`, `Set.isSubsetIntro`/`Elim` | 24 |
| `.read` (stages 2, 3) | `DecEq.sound` 290, `DecEq.soundFalse` 73 | 363 |
| | `.forward`/`.backward` on a one-function test-to-proposition `↔` lemma (`List.memContains` 34, 28 more names) | about 75 |
| | `Nat.equalSound` 46, `Nat.leqFalse` 42, `Bool.falseOfNotTrue` 35, `List.allToAll` 15, `List.allOfAll` 9 | 147 |
| Not readings | `Set.containsFromListIff` 16 (two functions deep), `Set.memToList` 14 (its test reads as itself) | 30 |
| Done before this design | D3480's `Decidable.toBool…` lemmas | deleted |
| **Not** by this design | `Void.exfalso (Bool.falseNotTrue h)`, `… (Bool.trueNotFalse h)` | 157 and 70 mentions at `cd8ac0d08` (396 at `f55b2381b`: most of that sweep has happened) |

So about 650 for patterns and building, and about 585 for `.read`. `.read`
doesn't remove a crossing; it makes it one word instead of thirty lemma
names. Of those 585, at most about half sit where silent crossing could
ever have applied (§7). Two honest limits:

- A removed helper isn't always a shorter proof. `f (Bool.andLeft r)
  (Bool.andRight r)` becomes a `let Both l r := r` and `f l r`.
- `rewrite DecEq.sound same in` becomes `rewrite same.read in`: shorter
  and needs no lemma name, but not gone.

## 9. Tactics: one reader, later

A module, `reading.rs`, has the reader of §5.4. The end state is that the
tactics use it too:

- **`auto`** replaces `from_conjuncts` (`auto.rs:36-38`) with "a hypothesis
  with everything its `∧` layers give", so an `if a && b` whose fact is a
  test fact is used like an `∧`. **`cases`** does the same for its
  hypothesis closer. Small, visible, after stage 2.
- **The `e = True` against `e = False` closer** for `cases` and `auto`
  needs no reader: its own ticket, now.
- **`omega`** already reads `&&`, `||`, `not`, both polarities and
  decisions, after computing the fact. Moving it onto the reader changes the
  terms it emits and no proof a user writes, so it goes last, and only if
  the reader's interface fits `omega`'s needs (it reads goals as well as
  facts, and splits) **[review, §4]**.

`cases` and `auto` deciding a *goal* go the other way, from a proposition to
its test, by instance search as now: the proof is `d.sound rfl`.

## 10. What depended on the `Decidable` note

Settled: `Decidable` is `{ holds, sound, complete }` (D3483); `==` on `Nat`
computes to `Nat.equal`; a derived `==` is a stuck decision, read by §5.4's
step 2 (stage 3). Still open, for stage 3: std's four recursive decisions
and `deriving (DecEq)` written test first (§13), so that each decision's
`holds` is the test its reading reads.

A `&&` whose right side uses the left's proof (`n != 0 && len % n == 0`) is
a `Decidable.elim`, not the plain `if`; it gets no reading at first, so it
is a leaf.

## 11. Staged plan

Estimates are lane-hours and guesses **[estimated]**; stage 1 took 30 min
against 3 h, so they are probably high. Each stage leaves `main` green.
Stages that write kernel terms get an Opus review (D2364). Each
language-visible stage updates `docs/syntax.md` and the guide in the same
lane.

| # | Lane | Needs | Model | Est. |
|---|---|---|---|---|
| 1 | **The coercion and printing** (§4) | nothing | Opus | done (SW-2734) |
| now | The `e = True` against `e = False` closer for `cases` and `auto` | nothing | any | small |
| now | Std's four recursive decisions written test first (`decMem`, `decDistinct`, `decSorted`, `decLeHead`), and `deriving (DecEq)` as decidable-record.md stage 4 planned | nothing | Sonnet | 2 h |
| 2 | **The reader, with `&&`, `\|\|`, `not`** (§5, §6, §6.8): `@[reading]` theorems, one per test, declared with the test, and their checks (`E-READING-SHAPE`, `E-READING-OVERLAP`, `E-READING-PLACE`); the reader with unfolding; patterns, building, both polarities, `.read`, `h.left`; `E-NO-READING`; the readings in the check cache; `Iff` into the core, where the six connective readings live; **no example's hash changes** | 1 | Opus | 6 h |
| 3 | **Std's readings**: `any`, `all`, `contains`, `Nat.equal`, `isSubset`, `isSome`, `isEmpty` and the negatives, each beside its function; the stuck-decision step (§5.4, step 2); the warning when a decision's `holds` isn't the test its proposition's reading reads (§13); the mismatch note suggesting `.read` | 2 | Sonnet; Opus for step 2 | 4 h |
| 4 | **Measure, then decide**: after one AoC year is swept with `.read`, count the `.read`s that sit where restricted silent crossing (§7) would apply | 3, 6 | Sonnet | 1 h |
| 5 | `auto` and `cases` on the reader (§9) | 2 | Opus | done (SW-3059) |
| 6 | **Sweeps**, by area: helpers replaced by patterns and `.read`; the `= True ↔` lemmas marked or deleted | 3 | Sonnet, three lanes (std, AoC 2020-21, AoC 2024) | 3 × 1.5 h |
| 7 | **Guide and tour**: a guide chapter "Tests and propositions", the proving guide's "Writing statements"; one sentence more: "to use the whole fact as its proposition, write `.read`" | 3 | Sonnet | done (SW-3098: a section "Tests and propositions" in guide chapter 10) |
| last | `omega` on the reader's table | 5 | Opus | optional |

Stages 3 and 5 can run in parallel after 2.

**Stage 3 as built (SW-3031).** The stuck-decision step reads `d.holds`
when `d` is `Decidable.holds d` or a call's field `(f x).holds` whose
decision forces to a neutral (not an unknown); its terms are `d.sound h`,
`d.complete q`, `Decidable.refute d h` and `Decidable.toBoolOfNot d n`
(which moved into the core for it). Since SW-2968 a derived `==` is no
longer a stuck decision: its test is `T.%same x y`. D3541 (a, SW-3044):
`deriving (DecEq)` also generates `T.%sameReads` (`T.%same x y ↔ x = y`)
and `T.%sameReadsFalse` (`T.%same x y = False ↔ x ≠ y`) from
`%sameSound`/`%sameComplete` (and `refute`/`toBoolOfNot`), for `T` and each
container member, filed with the instance. They are found by the test's
head before anything unfolds, so a record's `==` reads as `x = y` too. A derived decision of a record of propositions (SW-3038) is written the same way: `T.%holds` (the fields' decisions' tests joined by `&&`), `T.%holdsSound`, `T.%holdsComplete`, and the readings `T.%holdsReads` and `T.%holdsReadsFalse`. The warning,
`W-DECISION-TEST`, compares the function at the head of an instance's
`holds` (through the decisions it is made from) with the function a
positive reading of the same proposition is stated for, at whichever of
the two is checked second; arguments aren't compared, since they come from
sub-decisions the instance doesn't choose (`if a ∧ b` decides `a = True` by
`Bool`'s `DecEq`). Std's four recursive decisions were already written
test first (SW-2967), and std gives no warning.

**Std's remaining readings (SW-3067).** Declared beside their tests, each
checked by the library's own audit:

| Test | `= True` reads as | `= False` reads as |
|---|---|---|
| `Nat.leq m n` (`<=`, and `<`, `>`, `>=` through it) | `m ≤ n` (`Nat.LessEq m n`, the identity) | `n < m` (`Nat.LessThan n m`) |
| `Int.leq a b` | `a ≤ b` | `b < a` |
| `Int.less a b` | `a < b` | `b ≤ a` |
| `List.inRange x from until` | `from ≤ x < until` | `¬(from ≤ x < until)` |
| `Nat.divides d n` | `∃ t => n = t * d` (`Nat.dividesIff`, marked) | `¬(∃ t => n = t * d)` |
| `List.isDistinct xs` | `List.Distinct xs` (`List.isDistinctIff`, marked) | `¬(List.Distinct xs)` |
| `xs.contains x` on a `List` | `x ∈ xs` (`List.memContains`) | `x ∉ xs` |
| `xs.contains x` on a `NonEmptyList` | `NonEmptyList.Mem x xs` (`NonEmptyList.containsMem`, marked and moved beside `contains`) | `¬(NonEmptyList.Mem x xs)` |

`<` on `Nat` is `Nat.leq (Succ m) n`, so `(x < y) = False` reads as `y < Succ x`,
which is `y ≤ x` by computation. The `Nat` readings are in the core, in
`Equality.sw` and stated with `Nat.LessEq`/`Nat.LessThan` rather than the
operators, which the prelude can't name yet at that point; a reading placed
in a core file after code that mentions the test makes the prelude fail
with only "this needs the prelude's …" errors. `List.inRangeIff` (membership
in `List.range`) can't be the reading: it lives in a different file than
`List.inRange`, so the reading is the bounds. Example:
`examples/accept/readings-comparisons.sw`.

**Stage 5 as built (SW-3059).** `auto`'s last resort before a
contradiction, and `cases`'s hypothesis closer after its exact match, use
the *parts* of the hypotheses in scope (`auto::hypothesis_parts`): each
side of a conjunction, as before, and what a test fact reads as
(`reading::hypothesis_reads`, the term `.read` writes: `Iff.forward (r
args) h`, or for a stuck decision `d.sound h` and `Decidable.refute d h`, or
for `e = False` with no reading `¬e`), each taken apart again, up to 8
layers deep. A hypothesis is read by its type as written, as `.read` reads
it; a part has the type the reading's statement gave it, with its calls
folded. A context reads at most 64 test facts, the latest first, and each
reading may unfold its test up to 8 steps, so a large context costs a
bounded amount. A reading that failed to check gives nothing (no error),
nor does a leaf's `e = True`. For `auto` the parts a reading gave come after
the conjunction parts, so a proof that worked before keeps its term; in
`cases`, a case a part closes is no longer split (`cases-bool`'s `andLeft`
and `cases-argument`'s three theorems got shorter proofs and new hashes).
One addition the List.all example needed: after the contradiction closer,
`auto` applies a `∀` in scope once (`from_rules`): a hypothesis or a part,
its leading binders replaced by unknowns only as far as the rest unifies
with the goal (so a conclusion `x ≠ 0`, itself `x = 0 → Void`, stays
whole), each premise left unknown filled by a hypothesis or a part exactly,
nothing deeper. It applies to a written `∀` hypothesis as well as a read
one (D3544). A rule's conclusion isn't read: `xs.all (x => x != 0) = True`
gives `∀ x ∈ xs, (x != 0) = True`, which doesn't match a goal `y ≠ 0`
(reading it is a follow-up). Opus review: docs/reviews/SW-3059-review.md. With gluing off, `auto`'s obligations now keep the context's written
types (`Obligation::written`), so a hypothesis reads the same way; a `match
e:` equation has no written type, so with gluing off its test is read
unfolded (`xs.contains x` as `∃`), as `.read` reads it there too.

## 12. Decisions for Matt

- **D3486: In a proposition, does `a ∧ b` on two `Bool`s mean the
  proposition "`a` and `b`" (`a = True ∧ b = True`), with the test fact
  written and printed in full as `(a && b) = True`?** **Decided: yes**
  (SW-2735, 10 November 2026):
  [bool-operators-in-propositions.md](bool-operators-in-propositions.md).
- **D3487: Are readings ordinary proved declarations marked `@[reading]`,
  which std and projects can add, and not a fixed list in the compiler?**
  **Decided: yes, amended** (Matt, 12 November 2026, per the SW-2964
  review): a reading is a marked `↔` theorem, one per test (and polarity),
  declared with the test (§5).
- **D3488: Should a whole fact be converted silently where its reading is
  wanted?** **Decided: not for now** (Matt, 12 November 2026): an explicit
  word in stage 2; revisit after a measured sweep (§7, stage 4).
- **D3531: What is the word?** **Decided: `.read`** (Matt, 12 November
  2026): `found.read`, for `found: xs.contains x`, is `x ∈ xs`. The way back
  waits for stage 3 (§6.8).

Implementation calls, made here and open to change in the lanes:

- `∧` operands coerce one by one; `f: a → Bool` is not accepted for `a →
  Prop` (§4.1).
- `b = False` never prints as `¬b` (§4.4).
- A reading's test is its head applied to its parameters, each once; the
  key is (polarity, head), with `&&` and `||` as heads of their own (§5.3).
- A head with no reading is unfolded up to 8 steps, never through `opaque`
  (§5.4).
- The reader works one layer at a time, driven by the pattern (§5.4).
- `Refl` never triggers a reading (§6.1).
- Reading a fact refines nothing in the goal (§6.3).
- `Iff` moves into the core, so the six connective readings can be stated
  there with `↔`.
- The names: `@[reading]`, `Bool.andReads`, `.read`, `E-NO-READING`,
  `E-READING-SHAPE`, `E-READING-OVERLAP`, `E-READING-PLACE`.

## 13. Risks

- **The reader changing programs that check today** **[review, §5.1]**.
  The elaborator tries one reading of `if c`, `&&` and comparison sections
  and falls back to another on a type error. If the reader turned such an
  error into a success, a program that checks today would elaborate to a
  different term with no error. The hooks are narrow (a constructor
  against an equation, which those fallbacks don't rely on), and **the
  check is that no existing example's hash changes**: stage 2's lane and
  the verifier after it.
- **Load order and the cache** **[review, §5.2]**: readings live with
  their tests, checked at the declaration (`E-READING-PLACE`), so a proof
  never passes or fails by what else is in the run.
- **The test's folded form** **[review, §5.3]**: which reading applies goes
  by whether the test is folded. Stage 2 tests a fact read both ways.
- **Readings by unfolding leak implementations** **[review, §5.4]**: not a
  soundness matter; `opaque` stops it.
- **Std's decisions disagree with std's tests** **[review, §2.7, §5.5]**:
  `x ∈ xs` and `xs.contains x` are two tests today. Readings paper over it
  for patterns but not for `rewrite`. The rule that removes it: where a
  test `t` reads as `P` and `P` has a decision, the decision's `holds` is
  `t`. Checked by a warning in stage 3, satisfied by writing the four
  recursive decisions test first.
- **The counts are of calls, not of proofs that get shorter**
  **[review, §5.6]**: measure 2024 day 8 and day 12 by hand once stage 3
  is in.
- **Surprising coercions** (stage 1): `(x: ready)` where `x: Bool` was
  meant now declares a proof of `ready`; a `Bool` beside `=` is not
  coerced (§4.1).
- **Learnability.** One sentence covers it: "a fact about a test can be
  taken apart, and built, like the proposition it decides; `.read` gives
  the whole proposition". What a newcomer can't see is *which*
  proposition; with one reading per test, `E-NO-READING` and a hover can
  always say it. Nothing is hidden for good: the elaborated term is a call
  of a std theorem one can write by hand.
- **What it rules out or constrains later.**
  - `b` in a type position is taken, so `Bool` can't later coerce to a type
    some other way (Agda's `T`, Idris's `So`).
  - One reading per test can be widened later (the key grows, nothing
    written stops checking); silent crossing can be added later. Neither
    can be taken back cheaply, which is the reason for the order.
  - A future `simp` fits: the readings are Lean's `Bool` simp lemmas as
    `↔` theorems, usable as they are.
- **Readings that overreach.** A reading with a deep test
  (`(s.filter p).contains k` as `k ∈ s ∧ p k`) would be `simp` by another
  name. §5.3's shape rule (a head applied to parameters) refuses it;
  `filter` stays a rewrite.

## 14. What this note did not do

- Draft 1 ran probes only, with the release CLI; draft 2 adds the review's
  amendments and no new measurements.
- The "after" proofs in §8 were not checked, apart from their inner steps.
- Cost is argued, not measured.
- How readings interact with effects in a test (`xs.any f` with an
  effectful `f`) was not looked at; tests in propositions are pure.
- The SSReflect adapter names are from memory, as marked; Lean 4's goal
  display is inferred from its coercion (§3.2). Wadler's and McBride and
  McKinna's papers were read in abstract only.

Findings for tickets (draft 1's and the review's):

1. `cases` and `auto` don't close a goal from `h: e = True` and `k: e =
   False` (§6.4, measured).
2. `List.decMem`, `decDistinct`, `decSorted` and `decLeHead` recurse on the
   list, so `if x ∈ xs` and `if xs.contains x` are different tests; and
   `deriving (DecEq)` still answers by `Decidable.yes`/`no` (§2).
3. `(a <= b) = False` printed with ASCII `<=` where the positive form
   prints `≤` (draft 1, §2; stage 1 may have settled it).
4. bool-and-prop.md §7.5 said Lean prints such a fact as `b`; Lean 4 shows
   `b = true` (§3.2). Corrected there (SW-2714).

## Sources

- **[G1]** G. Gonthier, A. Mahboubi, "An introduction to small scale
  reflection in Coq", Journal of Formalized Reasoning 3(2), 2010.
  <https://jfr.unibo.it/article/view/1979> (as quoted in bool-and-prop.md;
  not re-read).
- **[R1]** The Rocq reference manual, "The SSReflect proof language",
  "Views and reflection".
  <https://rocq-prover.org/doc/V9.0.0/refman/proof-engine/ssreflect-proof-language.html>
- **[L2]** The Lean Language Reference, "Booleans".
  <https://lean-lang.org/doc/reference/latest/Basic-Types/Booleans/>
- **[L4]** Lean 4, `Init/SimpLemmas`, as rendered at
  <https://florisvandoorn.com/LeanCourse25/docs/Init/SimpLemmas.html>
- **[Z3]** Lean Zulip, "Lean can convert between Bool and Prop? How?" and
  "Prop -> Bool regression" (search summaries; threads not read in full).
  <https://leanprover-community.github.io/archive/stream/270676-lean4/topic/Lean.20can.20convert.20between.20Bool.20and.20Prop.3F.20How.3F.html>
- **[A4]** agda-stdlib, `Relation.Nullary.Reflects`.
  <https://agda.github.io/agda-stdlib/master/Relation.Nullary.Reflects.html>
- **[V2]** P. Wadler, "Views: a way for pattern matching to cohabit with
  data abstraction", POPL 1987 (summary read; paper not).
- **[V3]** C. McBride, J. McKinna, "The view from the left", Journal of
  Functional Programming 14(1), 2004, pp. 69-111.
  <https://doi.org/10.1017/S0956796803004829> (abstract read).
- The review's own sources (Rocq's `Stdlib.Bool.Bool`, Isabelle's `[iff]`,
  agda-stdlib's `Decidable.Core`) are listed in
  [SW-2964-bool-reader-review.md](../reviews/SW-2964-bool-reader-review.md).

Stitchwort notes this builds on: bool-and-prop.md, decidable-record.md,
interfaces.md §5.5 and §5.12, attributes.md, omega.md, decide.md,
check-cache.md, `docs/syntax.md` ("Logic notation", "A `Bool` as a
proposition", "cases").
