# Reading a `Bool` fact as a proposition (SW-2704)

**Status:** draft 1, 10 November 2026. Design only; nothing built. Follows
D3482 (Matt, 10 November 2026: yes, after a design note) and
[bool-and-prop.md](bool-and-prop.md) §7.3 and §7.5. Open decisions: D3486 to
D3488 ([§12](#12-decisions-for-matt)). Code was read at `f55b2381b`.
Migration cost is not counted (D2303).

It assumes D3480's `Decidable`, `{ does: Bool, sound, complete }`, whose own
note ([decidable-record.md](decidable-record.md), SW-2703) is being written
in parallel. [§10](#10-what-depends-on-the-decidable-note) lists what here
depends on it.

How claims are marked:

- **[measured]**: run today with the release CLI on the probe files in
  [bool-as-proposition/](bool-as-proposition/), or counted with `grep -w`
  over `std`, `aoc/src` and `games` at that commit. Counts include each
  helper's own definition.
- **[checked]**: read in the code or a note, at the place given.
- **[cited]**: read today at the link given ([Sources](#sources)).
- **[memory]**: prior art recalled, not re-read today.
- **[inferred]**: my reasoning; not run and not cited.

## 0. Summary

**The problem.** A fact that comes from a program is a test giving `True`:
`(s.contains k && xs.any p) = True`. It has no constructors, so a proof takes
it apart with helper lemmas, and the `= True` is noise in every statement.
Across std and AoC there are about 650 calls of the take-apart helpers
(`Bool.andLeft`, `List.anyTrueElim` and their like) and about 615 calls that
only carry a fact between a test and its proposition (`DecEq.sound`,
`(List.memContains xs x).forward`) **[measured, §8.4]**.

**The change**, in four parts:

1. **A `Bool` where a proposition is expected means `b = True`**, and is
   printed as `b`. The logical operators stay logical: `a ∧ b` on two `Bool`s
   is the proposition "`a` and `b`", not the test `a && b` (D3486).
2. **Readings.** A reading says what proposition a test decides: an ordinary
   proved definition of type `Decidable P`, whose `does` is the test, marked
   `@[reading]` (D3487). Std declares them for `&&`, `||`, `any`, `all`,
   `contains`, `==`, `isSubset` and so on. Nothing is trusted: the elaborator
   only writes `reading.sound h` or `reading.complete p`, which the kernel
   checks.
3. **Patterns and constructors go through readings.** `match h with | Both
   inSet (Witness x (Both xIn px))` on the fact above works: each
   constructor pattern asks for one reading of the test under it. Writing
   `Both l r` where `(a && b) = True` is wanted works too. A fact whose
   reading is a `∀` can be applied, and built with a lambda.
4. **Crossing** (D3488): a whole fact passed where its reading is wanted, or
   the other way, is converted: `found: xs.contains x = True` is accepted
   for `x ∈ xs`. So are `e = False` and `¬(e = True)`.

`omega`, `auto` and `cases` use the same reader in place of `omega`'s private
table.

**What it should do.** 2024 day 8's `part2IncludesPart1` goes from 17 lines
and 12 helper calls to 7 lines and none **[inferred; its two inner steps
measured in `readings.sw`]**. About 1,265 helper calls in std and AoC become
removable **[measured counts; that each one goes is inferred]**. Code that
checks today is unaffected: the reader runs only where there is a type error
today **[inferred]**.

Seven lanes, about 26 lane-hours **[estimated]**, in [§11](#11-staged-plan).

## 1. Words

- **Test**: an expression of type `Bool`.
- **Test fact**: a proof of `e = True` or `e = False` for a test `e`.
- **Reading**: a definition `r: Decidable P` whose `does` computes to a
  test. `P` is what the test "reads as".
- **Reader**: the elaborator function that, given a test and the shape of
  proposition wanted, finds a reading.
- **Crossing**: turning a test fact into its reading (`r.sound h`), or back
  (`r.complete p`).

## 2. Today

All **[measured, `today.sw`]** unless marked:

- `(h: b)` for `b: Bool` is `E-NOT-A-TYPE`, "this has type `Bool`, so it
  isn't a type". `¬a` and `a ∧ b` on `Bool`s in a proposition add the note
  "`&&` here is on propositions; for a `Bool` `b`, the proposition that it's
  true is `b = True`". `if h: b` adds a note suggesting `if h: c = True`
  (`check.rs:5216`, checked).
- `match h with | Both l r` on `h: (a && b) = True` is `E-TYPE-MISMATCH`,
  "these patterns match a `And`, but the argument has type …"
  (`lib.rs:4797`, checked).
- `h: a = True` and `k: a = False` together don't close a goal: `cases`
  finds no contradiction.
- Goals print `h: (a && b) = True`, `k: (c <= d) = False`, `m: xs.any (x =>
  x <= c) = True`, `p: a.not = True`, but `a ≤ b` for `Nat.leq a b = True`
  (`pretty.rs:1266`, checked). So the printer already hides one `= True`,
  and already tells the test `&&` from the proposition `∧`.
- `∧` and `&&` are one token (D1200). Where a proposition is expected it is
  `And` and its operands must be propositions; elsewhere the `Bool` reading
  is tried first (`logic.rs:1-19`, checked).
- `omega` reads `(p && q) = True`, `(p || q) = True`, `not p`, both
  polarities, and `Decidable.toBool d`, through 25 bridge lemmas it names in
  Rust (`omega.rs:124-148`, `bool_form` at `:860`, `read` at `:1474`,
  checked). `auto` has its own smaller version for conjunctions
  (`auto.rs:36-38`, checked).
- `Decidable` instances are found from the proposition, one per head
  (`interfaces.rs:14-24`, checked). Nothing goes from a test to a
  proposition.

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
- The form `(a <= b).decTrue.toBool` that a note can show today
  (bool-and-prop.md §7.5) is gone once D3480's `does` computes to the test.
  The printer's `comparison` reads a comparison through an `Ord` dictionary
  as `Decidable.toBool (Ord.decLessEq d a b)` (`pretty.rs:1731-1750`,
  checked); it changes to the `does` projection.

### 4.6 Today's errors

- `E-NOT-A-TYPE` stays for things that are neither types nor `Bool`s, and
  for the sides of an `=` (§4.1). Its `Bool` notes go (`logic.rs`,
  `check.rs:5216`), and two reject examples become accept examples
  (`and-bool-in-prop`, `if-proof-on-bool`, checked).
- `if h: b` on a `Bool` gives `h: b = True` in the first branch. The second
  should get `h: b = False`, the form `rewrite` wants; crossing (§7) turns
  it into `¬b` where that is wanted. (SW-2703 owns `if h:`.)
- The note for `if h: a < b = True` ("the guard is already a proposition")
  stays.

## 5. Readings and the reader

### 5.1 What a reading is

An ordinary definition, proved once, in std or in a project:

```
@[reading]
def Bool.andReading (a b: Bool): Decidable (a ∧ b) := {
  does = a && b,
  sound = h => Both (Bool.andLeft h) (Bool.andRight h),
  complete = h => Bool.andIntro h.left h.right
}

@[reading]
def List.anyReading (xs: List a) (f: a → Bool): Decidable (∃ (x: a) => x ∈ xs ∧ f x) := {
  does = xs.any f, sound = …, complete = …
}
```

**[measured, `readings.sw`: five readings written this way against a
stand-in record check, and each one's `does` equals its test by `rfl` with
everything unknown.]**

The starting set **[inferred]**, writing `∃ x ∈ xs, p` for `∃ (x: a) => x ∈
xs ∧ p` and `∀ x ∈ xs, p` for `∀ (x: a) => x ∈ xs → p`:

| Test | Reads as | Negative: `test = False` reads as |
|---|---|---|
| `a && b` | `a ∧ b` | `a = False ∨ b = False` |
| `a \|\| b` | `a ∨ b` | `a = False ∧ b = False` |
| `not a` | `a = False` | `a` |
| `xs.any f` | `∃ x ∈ xs, f x` | `∀ x ∈ xs, f x = False` |
| `xs.all f` | `∀ x ∈ xs, f x` | `∃ x ∈ xs, f x = False` |
| `xs.contains x` | `x ∈ xs` | `x ∉ xs` |
| `a == b` | `a = b` | `a ≠ b` |
| `s.isSubset t` | `∀ k ∈ s, k ∈ t` | (none at first) |
| `o.isSome`, `xs.isEmpty` | `∃ x, o = Some x`, `xs = []` | `o = None`, (none) |
| `Nat.leq a b`, `s.contains k`, `c.isDigit` | themselves | `Nat.leq a b = False` reads as `b < a` |

A negative reading is the same kind of definition, with `does = not (a &&
b)`: it has to be declared, because "not both" gives "one is false" only by
looking at the `Bool`s **[measured: `notAndReading` in `readings.sw`]**.

### 5.2 Why a marked definition, and not instance search or a Rust table

- **Not instance search.** Instances are found from the proposition, one
  per head. The reader goes the other way, from the test, so it needs its
  own index whatever feeds it. Some readings shouldn't be instances (the
  negative ones; `∃ x ∈ xs, f x`, whose head is `∃`). Some instances are
  pointless as readings (`Nat.decLessEq`, whose proposition is its test).
- **Not a table in Rust** (today's `omega`). It can't grow with the library,
  and a project's own collection type couldn't have readings.
- **An attribute on a `Decidable`**, because D3480's record is exactly a
  test with its two proofs, the mechanism for attributes exists (`@[tailrec]`,
  `@[noReceiver]`, checked), and the reading stays an ordinary definition
  that can be called by hand: `(List.anyReading xs f).sound h` is the escape
  hatch, and is all the elaborator ever writes.

An `instance` may also carry `@[reading]` (`List.decMem`, for `xs.contains
x`), and `deriving (DecEq)` puts it on what it generates.

### 5.3 How a reading is declared

When a `@[reading]` definition is checked, the elaborator computes its
`does` with the parameters as unknowns and files it under **(polarity, head
of the test, head of the proposition)**:

- polarity is negative when `does` is `not e`; the head is then `e`'s;
- the head of the test is the function it is stuck on (`List.any`,
  `Set.contains`), or "and"/"or" for the two `Bool.ifThenElse` shapes that
  `&&` and `||` are (`omega.rs:886-898`, checked);
- the head of the proposition is `∧`, `∨`, `∃`, `=`, `∀`/`→`, or a named
  proposition (`List.Mem`).

It is refused if:

- its type isn't `Decidable P` (`E-READING-SHAPE`);
- `does` is a bare parameter, a constant, or leaves a parameter
  undetermined (it would fit everything, or couldn't be filled in);
- another reading has the same key and their tests overlap
  (`E-READING-OVERLAP`, naming the other);
- it is declared outside the module that owns the test's head function or
  the proposition's head: the orphan rule instances have
  (`interfaces.rs:17-19`, checked).

### 5.4 How a reading is found

`read(test, polarity, wanted)`, where `wanted` is the head of proposition
the caller needs (from a pattern's constructor, an expected type, or
"any"):

1. Compute the test to where it is stuck, keeping calls folded.
2. **A stuck decision.** If the test is `d.does` for a `d: Decidable P`
   that doesn't compute (a dictionary's `==`, a hypothesis), it reads as
   `P`, through `d` itself. No table needed.
3. Look up (polarity, head, wanted). Match the reading's `does` against the
   test, which fills in the reading's parameters; `auto` parameters such as
   `DecEq a` are found as usual.
4. If nothing is filed under this head, unfold the head one step and go to
   1. So a project's `def isAntinode city p := city.antennas.any (…)` reads
   as `∃` with no declaration. At most 8 steps (an implementation call).
5. Otherwise the test is a **leaf**: it reads only as itself.

The reader works **one layer at a time**. `andReading`'s parts are `a =
True` and `b = True`, test facts again. A nested pattern or a deeper
expected type asks again for the part it touches. So nothing is searched:
the pattern or type that is wanted drives every step.

### 5.5 When two fit, or none

- **Two with the same key** can't exist (§5.3).
- **Two with different wanted shapes** is the useful case: `xs.any f` could
  read as `∃ x ∈ xs, f x` and as `List.Any (x => f x) xs`. The caller's
  wanted shape picks. When the caller wants "any" (`omega`), the first
  declared wins; it only asks about `∧`, `∨` and `¬`, which have one each.
- **Ambiguity is never a soundness or provability question.** Every reading
  of a test is equivalent to the test, so two readings are equivalent to
  each other. The choice changes which constructors a pattern needs, and
  the pattern is what made the choice.
- **None fits.** In a pattern or a constructor this is `E-NO-READING` (§6.5).
  In crossing it is the type mismatch reported today, with a note.

### 5.6 Unknowns and stuck terms

- **The test's head is an unknown** (`?f x`): the reader answers "blocked".
  A crossing waits, as an instance obligation does (`interfaces.rs:21-24`,
  checked). A pattern can't wait, and reports "the type of this isn't known
  yet", as other patterns do.
- **Unknowns inside the test** (`xs.any ?f`) don't block: matching fills the
  reading's parameters with them. The reader never assigns an unknown of
  the caller's.
- **A variable or an unknown function's call** (`b`, `p x`): a leaf. Its
  fact can be matched only by a name, `_`, or `()` when it computes to
  `False = True`.
- **A test that computes to `True` or `False`** is not read. `False = True`
  is matched by `()` as today.

### 5.7 Cost

- Declaring: one evaluation of `does` per reading; a few dozen readings.
- Finding: a hash lookup by head, one first-order match against a small
  pattern, and up to 8 unfolding steps when the head has no reading.
- The reader is called from three places only: a constructor pattern whose
  type doesn't match the fact (an error today), a constructor or lambda
  checked against a test fact (an error today), and a type mismatch with a
  test fact on one side (an error today). So code that checks today never
  calls it. **[inferred; nothing measured, since nothing is built]**
- `omega` calls it once per fact in scope, in place of `bool_form`, which
  does the same work by hand.
- The table is part of what a cached check depends on, as the instance
  table is (interfaces.md §9.3, checked): the check cache's key must
  include it.

## 6. Patterns

### 6.1 Taking a fact apart

Where a constructor pattern meets a scrutinee of type `e = True` or `e =
False`, and the constructor belongs to a proposition (`Both`, `Inl`, `Inr`,
`Witness`), the elaborator asks the reader for `e` with that proposition as
the wanted shape, and matches on `r.sound h` instead of `h`. The hook is
the place that reports the mismatch today (`lib.rs:4797`, checked).

This is every place patterns are written: `match`, equation arms, `let Both
l r := h`, and a lambda's parameter.

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
about it. A one-step spelling (`if Both ha hb: a && b`) is possible later
and not proposed.

### 6.4 Negation

- `h: e = False` is read through the negative readings (§5.1): `match h
  with | Inl na | Inr nb` on `(a && b) = False` **[measured, `negative` in
  `readings.sw`]**.
- `(not e) = True` is first turned into `e = False`, and `(not e) = False`
  into `e = True`, by fixed lemmas (`Bool.notTrue`, as `omega` does today).
- `e = False` and `¬(e = True)` are different terms that mean the same.
  Each is accepted where the other is wanted (§7). With a reading `P` of
  `e`, `e = False` is accepted for `¬P` too, through `complete`.
- A new closer for `cases` and `auto`: `h: e = True` and `k: e = False` in
  scope close any goal. Today they don't **[measured, `clash` in
  `today.sw`]**.

### 6.5 Exhaustiveness

After the reading, the scrutinee is an ordinary `P ∧ Q`, `P ∨ Q` or `∃`, so
the ordinary coverage check applies: an `∨` needs both arms. A fact read as
`∨` or `∃` can be matched only where the result is a proof, as for any
`∨` (`E-PROP-ELIM`).

In one column, the constructor patterns must agree on the reading: `| Both
l r` in one arm and `| Refl` in another is an error. Names and `_` mix with
anything.

### 6.6 Building

- A constructor (`Both x y`, `Inl x`, `Witness x p`) checked against `e =
  True` asks the reader with that constructor's proposition, checks the
  constructor against the reading, and wraps it in `r.complete` **[measured,
  `build`]**.
- A lambda checked against a test fact asks for a `∀` reading: `key has =>
  …` proves `s.isSubset t`.
- A test fact applied to arguments asks for a `∀` reading: `allSmall y
  yIn` **[measured, `useAll`]**.
- A field of a fact (`h.left`) asks as a pattern would.

### 6.7 Errors

```
[E-NO-READING] Error: `h` can't be taken apart with `Both`
  │ match h with
  │   | Both l r => …
  │     ───┬────
  │        ╰── `h` is the test `xs.isSorted`, which has no reading as `∧`
  │ Note 1: it reads as `List.Sorted xs` (`List.sortedReading`)
  │ Note 2: a test fact can always be matched by a name
```

- For a leaf: "`b` is a variable, so the fact `b` has no parts".
- For crossing that fails: today's `E-TYPE-MISMATCH`, with "`found` is the
  test `xs.contains x`, which reads as `x ∈ xs`".
- Hovering a pattern that went through a reading names it (LSP; an
  implementation call).

## 7. Crossing (D3488)

When a term's type and the expected type don't unify, both are known, and
one of them is a test fact:

- **fact given, proposition wanted:** read the test with the expected
  type's head as the wanted shape; if the reading unifies with the expected
  type, the term becomes `r.sound h`;
- **proposition given, fact wanted:** the same, with `r.complete p`;
- `e = False` against `¬(e = True)`, and against `¬P`, as in §6.4.

One layer only. `found: xs.contains x = True` is accepted for `x ∈ xs`, and
`same: (a == b) = True` for `a = b`. A fact that needs two layers converted
inside a `∧` is not; a pattern does that.

Why this is safe to do silently **[inferred]**:

- it happens only where there is a type error today;
- it applies only between a test and a reading declared for it, which are
  proved equivalent;
- both sides are proofs, erased at run time, so no program's behaviour can
  change;
- the term written is `r.sound h`, checked by the kernel.

It is recommended, but as a later stage, because it is the part with the
most room for confusing errors, and patterns and building are useful
without it.

## 8. The wins, on real code

### 8.1 2024 day 8, `part2IncludesPart1` (`Day08/Proofs/Part2.sw:191`)

Today **[checked]**, 17 lines: `Set.isSubsetIntro`, two rewrites with
`Set.containsFilter`, then `Bool.andIntro` twice, `Bool.andLeft` three
times, `Bool.andRight` twice, `List.anyTrueElim` twice and `List.anyOfMem`
twice. The four `any` calls each need their test's lambda written out in
full, up to 150 characters.

After **[inferred]**:

```
theorem part2IncludesPart1 (city: City):
    (antinodeLocations city (isAntinode city)).isSubset (antinodeLocations city (isHarmonicAntinode city)) :=
  key has =>
    let Both onMap (Witness first (Both firstIn (Witness second (Both secondIn (Both same (Both inLine twice)))))) :=
      rewrite Set.containsFilter … at has in has
    rewrite Set.containsFilter … in
    Both onMap (Witness first (Both firstIn (Witness second (Both secondIn (Both same inLine)))))
```

Seven lines, no helpers. The lambdas go because the reader takes each test
from the fact's own type. `isHarmonicAntinode city key` has no reading, so
it is unfolded one step to its `any` (§5.4, step 4). The two rewrites stay:
an equation between tests is the right tool for `filter` (bool-and-prop.md
§6, point 4).

### 8.2 2024 day 12, `Sides.sw:226`

Today **[checked]**:

```
| True => Void.exfalso (omega [And.right (within { row, column = Succ last }
    ((List.memContains region.plots { row, column = Succ last }).forward found))])
```

After, with crossing **[inferred]**: `| True => omega [(within _ found).right]`.
`found: region.plots.contains … = True` is accepted for `… ∈ region.plots`.
Without crossing this line doesn't change.

### 8.3 2024 day 8, `part2Correct` and `antennasAreAntinodes` (`:160`, `:177`)

- `Decidable.toBoolSound _ (Bool.andRight same)` becomes a pattern on
  `same`: `Both _ sameFrequency`, the second part crossing to the equation.
- `antennasAreAntinodes` builds two nested `any` facts with `List.anyOfMem`
  and `Bool.andIntro`, lambdas in full; it becomes `Both (positionsOnMap …)
  (Witness first (Both firstIn (Witness second (Both secondIn (Both same
  (inLineSelf …))))))` **[inferred]**.

### 8.4 Counts

Uses across `std`, `aoc/src` and `games` **[measured, `grep -w`; each
includes the helper's definition]**:

| Removed by | Helpers | Uses |
|---|---|---|
| Patterns and building (stages 2, 3) | `Bool.andLeft` 175, `andRight` 194, `andIntro` 82, `orElim` 36, `orLeft` 15, `orRight` 20 | 522 |
| | `List.anyTrueElim` 41, `anyOfMem` 45, `allMember` 18 | 104 |
| | `Bool.orFalseLeft`/`Right`, `andFalseElim`, `notTrue`, `Set.isSubsetIntro`/`Elim` | 24 |
| Crossing (stage 4) | `DecEq.sound` 293, `DecEq.soundFalse` 70 | 363 |
| | `.forward`/`.backward` on a test-to-proposition `↔` lemma (`List.memContains` 34, `Set.containsFromListIff` 16, `Set.memToList` 14, 28 more names) | at least 105 |
| | `Nat.equalSound` 46, `Nat.leqFalse` 42, `Bool.falseOfNotTrue` 35, `List.allToAll` 15, `List.allOfAll` 9 | 147 |
| D3480 alone (SW-2703) | `Decidable.toBoolSound`, `toBoolFalse`, `toBoolOf`, `toBoolOfNot` | 71 |
| **Not** by this design | `Void.exfalso (Bool.falseNotTrue h)` 334, `… (Bool.trueNotFalse h)` 62 | 396 |

So 650 for patterns and at least 615 for crossing. Two honest limits:

- A removed helper isn't always a shorter proof. `f (Bool.andLeft r)
  (Bool.andRight r)` becomes a `let Both l r := r` and `f l r`.
- **`Bool.falseNotTrue` is mostly not this design's win**, though
  bool-and-prop.md §1 lists it. 334 of its 421 uses are an impossible arm,
  `Void.exfalso (Bool.falseNotTrue h)` where `h` computes to `False =
  True`, and `Bool.trueNotFalse` has 62 more. `cases` closes such an arm
  today **[measured on one: `Succ n ≤ 0 ⊢ Void`; that it closes all of them
  is inferred]**. That is a sweep with no language change (a finding,
  §14).

## 9. Tactics: one reader

A new module, `reading.rs`, with the reader of §5.4 and one helper over it:

- `read(test, polarity, wanted)`: a reading, a leaf, or blocked;
- `facts_of(h)`: a hypothesis with everything its `∧` layers give, whether
  the `∧` is the proposition or a test's reading.

Then:

- **`omega`** drops `bool_form`'s `And`, `Or`, `Not` and `ToBool` arms and
  the bridge lemmas for them (`omega.rs:126-148`). It reads each fact by
  `facts_of`, asks the reader for `∨` to find its case splits, and keeps
  only what is arithmetic: `Nat.leq`, `Int.leq`, `Int.less`, `Nat.equal`.
  The terms it emits are `r.sound h` in place of `Bool.andLeft h`.
- **`auto`** replaces `from_conjuncts` (`auto.rs:36-38`) with `facts_of`,
  so the proof an `if a && b` gives its branch is found the same way as a
  `∧` hypothesis.
- **`cases`** uses `facts_of` for its "a hypothesis" closer, and gets the
  `e = True` against `e = False` closer (§6.4). Its splitting is unchanged:
  it splits the stuck `Bool`, and facts about it compute.

`cases` and `auto` deciding a *goal* go the other way, from a proposition to
its test, by instance search as now. With D3480 that test is `d.does`, and
the proof is `d.sound rfl`.

## 10. What depends on the `Decidable` note

- **The type of a reading** is D3480's record. If its field names or shape
  change in SW-2703, readings follow; nothing else here cares.
- **§5.4 step 2** needs `does` to be a projection that is stuck on a stuck
  decision.
- **`==`** must compute to the type's own test (`Nat.equal a b`) for the
  `a == b` reading to be found by head, and `deriving (DecEq)` must mark
  what it generates.
- **`if h: b`'s second branch** (§4.6) is SW-2703's to settle.
- **A `&&` whose right side uses the left's proof** (`n != 0 && len % n ==
  0`) has a different shape from the plain `&&`. It gets no reading at
  first, so it is a leaf.
- **Stage 1 (the coercion and printing) depends on none of this** and can
  start now.

## 11. Staged plan

Estimates are lane-hours and are guesses **[estimated]**; no lane like
these has been timed. Each stage leaves `main` green: 1 to 5 only accept
more programs or change printing; 6 is sweeps. Stages 2 to 5 write kernel
terms, so each gets an Opus review (D2364). Each language-visible stage
updates `docs/syntax.md` and the guide in the same lane.

| # | Lane | Needs | Model | Est. |
|---|---|---|---|---|
| 1 | **The coercion and printing** (§4): `Bool` in a proposition position; the printing rule with a print-then-read-back test over the examples; `≤` in `Bool` positions; `E-NOT-A-TYPE` notes | nothing | Opus | 3 h |
| 2 | **The reader, with `&&`, `\|\|`, `not`** (§5, §6): `@[reading]`, the table, `read`; patterns, building, both polarities; `E-NO-READING`, `E-READING-SHAPE`, `E-READING-OVERLAP`; the check cache's key | SW-2703 built | Opus | 6 h |
| 3 | **Std's readings**: `any`, `all`, `contains`, `==`, `isSubset`, `isSome`, `isEmpty`, the negatives; `∀` readings by application and lambda | 2 | Sonnet for the readings, Opus for the `∀` hooks | 4 h |
| 4 | **Crossing** (§7), if D3488 is yes; the `e = True`/`e = False` closer | 2 | Opus | 4 h |
| 5 | **`omega`, `auto`, `cases` on the reader** (§9); `omega`'s table deleted | 2 | Opus | 4 h |
| 6 | **Sweeps**, by area: statements lose `= True`; helpers replaced by patterns; the `= True ↔` twins and the helpers left unused deleted | 3, 4 | Sonnet, three lanes (std, AoC 2020-21, AoC 2024) | 3 × 1.5 h |
| 7 | **Guide and tour**: a guide chapter "Tests and propositions", a feature-tour page, the proving guide's "Writing statements" | 3 | Sonnet | 1.5 h |

Stage 1 can run beside SW-2703's build. Stages 3, 4 and 5 can run in
parallel after 2.

## 12. Decisions for Matt

- **D3486: In a proposition, does `a ∧ b` on two `Bool`s mean the
  proposition "`a` and `b`" (`a = True ∧ b = True`), with the test fact
  written and printed in full as `(a && b) = True`?** **[rec: yes]** (§4.3,
  §4.4). It is a small step back from D3482's "printed without `= True`":
  every fact prints bare except a test whose top is `&&` or `||`. The
  alternative: two `Bool` operands make the test, printed `a && b`, and
  whether a statement is a test or a proposition then depends on its
  operands' types. **Decided: yes** (SW-2735, 10 November 2026):
  [bool-operators-in-propositions.md](bool-operators-in-propositions.md).
- **Decided (D3487, Matt, 12 Nov 2026): yes, amended per docs/reviews/SW-2964-bool-reader-review.md: a reading is a marked `↔` theorem, one per test, declared with the test.**
- **D3487: Are readings ordinary proved definitions marked `@[reading]`,
  which std and projects can add, and not a fixed list in the compiler?**
  **[rec: yes]** (§5.1 to §5.3). It adds one attribute to the language and
  an orphan rule like the one for instances. Nothing is trusted either way.
- **Decided (D3488, Matt, 12 Nov 2026): no silent crossing for now; an explicit word (working name `.read`) in stage 2; revisit after a measured sweep (SW-2964 review).**
- **Decided (D3531, Matt, 12 Nov 2026): the word is `.read` (`found.read` turns `xs.contains x = True` into `x ∈ xs`).**
- **D3488: Should a whole fact be converted silently where its reading is
  wanted, and back (`found: xs.contains x = True` accepted for `x ∈ xs`;
  `e = False` for `¬e`)?** **[rec: yes, as stage 4, one layer only]** (§7).
  It is about half the measured win (615 of 1,265 uses). The alternative is
  patterns and building only, with crossings still written by hand.

Implementation calls, made here and open to change in the lanes:

- `∧` operands coerce one by one; `f: a → Bool` is not accepted for `a →
  Prop` (§4.1).
- `b = False` never prints as `¬b` (§4.4).
- Readings are filed by (polarity, test head, proposition head); the same
  key twice is an error at the declaration (§5.3).
- A head with no reading is unfolded up to 8 steps (§5.4).
- The reader works one layer at a time, driven by the pattern or the
  expected type (§5.4).
- A blocked crossing waits; a blocked pattern is an error (§5.6).
- One column's constructor patterns must agree on the reading (§6.5).
- Reading a fact refines nothing in the goal (§6.3).
- An `instance` can also be a reading; `deriving (DecEq)` marks its own
  (§5.2).
- The names: `@[reading]`, `Bool.andReading`, `E-NO-READING`.

## 13. Risks

- **Surprising coercions.**
  - `(x: ready)` where `x: Bool` was meant now declares a proof of `ready`.
    Lean has the same; the error comes at the first use.
  - A `Bool` beside `=` could have become an equation between
    propositions; §4.1 excludes the sides of an `=` for that reason.
  - Two terms that print alike: avoided by the printing rule (§4.4), which
    lane 1 tests by reading back what it prints.
  - Crossing can hide which form a lemma wants. It is limited to one layer
    and to declared readings, and the hover names it.
- **Ambiguity.** One reading per key, by construction. Between shapes the
  pattern chooses. No choice affects what is provable (§5.5).
- **Performance.** No instance search happens in a pattern: a lookup and a
  match per constructor (§5.7). The unfolding in step 4 is bounded. Not
  measured.
- **Learnability.**
  - One sentence covers it: "a fact about a test can be taken apart, and
    built, like the proposition it decides".
  - What a newcomer can't see is *which* proposition. `E-NO-READING` lists
    the readings; the hover names the one used; a `stitchwort readings`
    listing would be cheap.
  - Nothing is hidden for good: the elaborated term is a call of a std
    definition one can write by hand.
  - SSReflect's cost was naming views at every use; here there is nothing
    to name.
- **What it rules out or constrains later.**
  - `b` in a type position is taken, so `Bool` can't later coerce to a type
    some other way (Agda's `T`, Idris's `So`).
  - D3486 fixes what `∧` on `Bool`s means in a statement; changing it later
    changes those statements' terms.
  - A general view feature for data (Wadler's) is not ruled out, but its
    patterns would have to coexist with these: constructor patterns on a
    test fact already have a meaning.
  - A future `simp` fits: the readings are Lean's `Bool` simp lemmas as
    pairs of implications instead of `propext` equations, and `simp` could
    use the same table.
  - `rewrite` with `↔` under connectives (bool-and-prop.md §7.4) is
    independent.
- **Readings that overreach.** A reading with a deep pattern
  (`(s.filter p).contains k` as `k ∈ s ∧ p k`) would be `simp` by another
  name. The key is the head only, and std should keep to one function per
  reading; `filter` stays a rewrite.

## 14. What this note did not do

- No build and no test run; probes only, with the release CLI.
- The reader, the hooks and crossing are designs, not prototypes. What was
  run is the *output*: the readings and the terms that patterns would
  stand for (`readings.sw`).
- The "after" proofs in §8 were not checked, apart from their inner steps.
- Cost is argued, not measured.
- How readings interact with effects in a test (`xs.any f` with an
  effectful `f`) was not looked at; tests in propositions are pure.
- The SSReflect adapter names are from memory, as marked; Lean 4's goal
  display is inferred from its coercion (§3.2). Wadler's and McBride and
  McKinna's papers were read in abstract only.

Findings for tickets:

1. 396 `Void.exfalso (Bool.falseNotTrue h)` and `… trueNotFalse h` arms
   that `cases` should close today: a sweep with no language change
   (§8.4).
2. `cases` doesn't close a goal from `h: a = True` and `k: a = False`
   (§2, measured).
3. `(a <= b) = False` prints with ASCII `<=` where the positive form prints
   `≤` (§2, measured).
4. bool-and-prop.md §7.5 said Lean prints such a fact as `b`; Lean 4 shows
   `b = true` (§3.2). Corrected there (SW-2714).

## Sources

- **[G1]** G. Gonthier, A. Mahboubi, "An introduction to small scale
  reflection in Coq", Journal of Formalized Reasoning 3(2), 2010.
  <https://jfr.unibo.it/article/view/1979> (as quoted in bool-and-prop.md;
  not re-read today).
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

Stitchwort notes this builds on: bool-and-prop.md, decidable-record.md
(SW-2703, in progress), interfaces.md §5.5 and §5.12, attributes.md,
omega.md, decide.md, `docs/syntax.md` ("Logic notation", "cases").
