# The `Bool` reader before stage 2: a review for D3487 and D3488 (SW-2964)

**Status:** review, 12 November 2026. Paper lane: no build, no tests, no
probes run. Reviews [bool-as-proposition.md](../proposals/bool-as-proposition.md)
(draft 1, 10 November) against the code at `cd8ac0d08`. Migration cost is
not counted (D2303).

How claims are marked:

- **[checked]**: read today in the code or a note, at the place given.
- **[measured]**: counted today with `grep` or a short script over
  `crates/elab/src/std`, `aoc/src` and `games` at `cd8ac0d08`. The script
  sorts uses by the text just before them, so its classes are rough.
- **[cited]**: read today at the link given ([Sources](#sources)), through
  a page-extraction tool; quotes are as it returned them.
- **[recalled]**: prior art from memory, not re-read today.
- **[inferred]**: my reasoning from the code; not run.

## 0. Summary

**The problem.** A fact from a program is a test giving `True`:
`(s.contains k && xs.any p) = True`. Proofs take such facts apart with
helper lemmas (about 650 calls) and carry them to and from propositions
with more (about 615 calls). The note proposes a *reader*: the compiler
looks up what proposition a test stands for, so `Both l r` works on an
`&&` fact, and (D3488) a whole fact is converted silently where its
proposition is wanted. Stage 2, about 6 hours of Opus, builds the reader.
Two decisions gate it.

**D3487: are readings ordinary proved definitions that std and projects
can add, and not a fixed list in the compiler?** **[rec: yes, with three
changes to their shape]**

1. **A reading is a marked `↔` theorem, not a `Decidable` definition.**
   `@[reading] theorem List.containsReads: xs.contains x ↔ x ∈ xs`. The
   test and the proposition are both in the statement, where a person, an
   error message and the cache can see them. The negative ones need no
   trick: `(a && b) = False ↔ a = False ∨ b = False`. Std already has 27
   lemmas of this shape; they become readings by being marked.
2. **One reading per test.** Each test function reads as exactly one
   proposition (and one more for `= False`). "What does this test read
   as?" then has one answer, which every error and a hover can print. The
   note's key (test, wanted shape) allows several, chosen by the pattern.
3. **A reading lives where its test is defined**: the same file in std,
   the same namespace in a project. So nothing a file imports can change
   how its tests read, and the reader never depends on which library files
   happen to be loaded (a bug class std has hit twice: SW-1354, SW-1362).

A fixed list is ruled out by std itself: sets, maps, `isSubset`, `isSome`
and sixty existing `= True ↔` lemmas want readings, and each would be a
name wired into Rust, as `omega`'s 25 are today.

**D3488: silent crossing of a whole fact, as stage 4?** **[rec: no, not as
proposed. Build an explicit one-word crossing first (working name
`found.read`), and decide silent crossing later, from counts, for the cases
where it can't mislead.]**

- It is sound: the term is `reading.forward h`, checked by the kernel.
- It is not predictable, because **a test fact is itself an equation.**
  Silent crossing fires only on a type mismatch, and wherever an equation
  is wanted, `(x == y) = True` fits as it stands. So there is no mismatch
  in the commonest places such facts are used: as a `rewrite` rule (where
  it silently rewrites `x == y` to `True` instead of `x` to `y`), in a
  `let` with no type, and under `Eq.sym`.
- The measured win is about half what the note says. Of the 510 named
  uses, at most 270 (53%) sit where a mismatch could occur; 201 sit where
  it can't (121 rewrite rules, 48 untyped `let`s, 32 under `Eq.sym` or
  `Eq.trans`) **[measured, rough]**. `DecEq.sound` alone: 169 of 290
  can't cross.
- An explicit word works in all of those places, shows the reader of a
  proof that a crossing happened, and fails with a direct error at the
  word. Silent crossing is then just "insert `.read` at a mismatch", which
  can be added later without breaking anything; taking it out later would
  break proofs.

**What changes in the plan** (§6): stage 2 keeps its size but builds the
amended readings and `.read`; the `∀` hooks in stage 3 are dropped (`.read`
gives the function); stage 4 becomes a measurement and a later decision;
`omega` moves last and may not be worth doing; two small tickets can start
now (the `e = True` against `e = False` closer, and std's decisions written
test first). Before stage 2 is merged, one check matters most: **no
existing example's hash may change** (§5.1).

## 1. What has been built since the note

The note read the code at `f55b2381b`. Since then **[checked]**:

- **Stage 1 is in** (SW-2734, `288c2d7fe`): a `Bool` where a proposition
  is expected means `b = True` and prints as `b`; `docs/syntax.md`, "A
  `Bool` as a proposition". It took 30 minutes against 3 hours estimated
  (ticket SW-2734), so the note's other estimates are probably high too.
- **`Decidable` is the record**, with the field named `holds`, not `does`
  (D3483): `{ holds: Bool, sound, complete }`
  (`std/core/Decidable.sw:21`). `Yes`/`No`, `toBool`, `fromYes` and the
  `toBool…` lemmas are gone (SW-2746, SW-2761, SW-2823, SW-2831).
- **`omega` reads a decision's test through the decision**: `d.holds =
  True` by `d.sound`, `= False` by `Decidable.refute` (`omega.rs`, header).
  Its named `Bool` lemmas are still listed in Rust (`omega.rs:123-163`).
- **`deriving (DecEq)` is not test first.** It still matches on the two
  values and answers `Decidable.yes`/`no` (`derive.rs:49-56`), so `r == s`
  on unknown values is stuck on the decision. decidable-record.md stage 4
  planned otherwise.
- **`List.decMem` is not test first either.** It recurses on the list
  (`std/List/Toolkit.sw:486`), so its `holds` is stuck on `xs` and is not
  `xs.contains x`, which is `List.any xs (member => member == x)`
  (`Toolkit.sw:307`). The same goes for `List.decDistinct`, `decSorted`
  and `decLeHead`.

Where the note is now out of date:

| Note | Now |
|---|---|
| §2 "Today" | Stage 1's rows are history: `(h: b)` checks, goals print bare |
| `does` throughout | `holds` |
| §4.5, the `(a <= b).decTrue.toBool` form | gone with `toBool` |
| §5.2: "an `instance` may also carry `@[reading]` (`List.decMem`, for `xs.contains x`)" | wrong as std stands: `decMem`'s test isn't `contains` (above) |
| §8.4: `Bool.falseNotTrue` 334 + `trueNotFalse` 62 | 157 and 70 mentions **[measured]**: most of that sweep has happened |
| §8.4: "D3480 alone: `toBoolSound` …, 71" | done; the lemmas are deleted |
| §10, "what depends on the `Decidable` note" | all settled; `==` on `Nat` computes to `Nat.equal`; derived `==` is a stuck decision |
| §11 stage 1 | done |

The other helper counts in §8.4 still hold to within a few **[measured]**:
`Bool.andLeft` 175, `andRight` 194, `andIntro` 82, `DecEq.sound` 290,
`soundFalse` 73. Stage 1 removed none of them, as expected.

## 2. D3487: what a reading should be

### 2.1 The options

1. **A fixed list in the compiler.** Today's `omega`.
2. **Marked `Decidable` definitions** (the note): `@[reading] def
   Bool.andReading (a b: Bool): Decidable (a ∧ b) := { holds = a && b, … }`.
3. **Marked `↔` theorems**: `@[reading] theorem Bool.andReads (a b: Bool):
   (a && b) = True ↔ a ∧ b`.
4. **No declarations: use the `Decidable` instances** (bool-and-prop.md
   §7.3's first sketch).
5. **Named views** (SSReflect): the user writes which lemma, `case/andP`.
6. **Rewriting to a normal form** (Lean's `simp` set).

### 2.2 Why not the others

- **A fixed list (1)** can't follow the library. Std has 27 one-line `=
  True ↔` lemmas and AoC 33 (bool-and-prop.md §2.4), each a reading
  someone needed. A project's own collection could have none. And every
  entry is a std name the compiler knows by text: `omega.rs` lists about
  25 such names today, and they have to be kept in step by hand
  **[checked]**. Trust is the same either way: the kernel checks the
  emitted term.
- **Instances alone (4)** don't work, for four reasons **[checked]**:
  - instances are found from the proposition; the reader starts from the
    test;
  - an instance's test is the reader's test only if the instance is
    written test first, and four of std's are not (§1);
  - the readings for `&&`, `||` and `not` are about `Bool`s (`a && b`
    reads as `a = True ∧ b = True`); `Decidable.and` is about two other
    decisions;
  - the negative readings, and `xs.any f` as `∃`, are not instances of
    anything.

  What instances do give is the note's step 2 (§5.4): a test that is a
  stuck decision's `holds` reads as that decision's proposition, through
  the decision itself. That covers every derived `==` with no declaration,
  and should stay. Agda's library makes the same point from the other
  side: its `isYes` is "a stricter version of `does`" kept so that the
  proposition can be recovered by unification **[cited: A5]**. Once a test
  has computed away from its decision (`Nat.equal a b`), the proposition
  has to be declared.
- **Named views (5).** SSReflect's views are named at each use, and the
  engine adds an adapter chosen "from the shape of the top assumption"
  **[cited: R1]**. The note is right that Stitchwort's pattern already
  says which shape is wanted, so there is nothing to name. The by-hand
  form stays available in every design: `(List.containsReads xs
  x).forward h`.
- **A normal form (6)** needs `propext` or generalized rewriting, turns a
  whole fact over at once, and D2541 has no `simp`. The note's "one layer,
  driven by the pattern" is better: there is no normal form to define or
  to argue about.

### 2.3 `↔` theorems (3) against `Decidable` definitions (2)

Both are ordinary proved definitions that std and projects add; nothing is
trusted in either. The differences:

| | `Decidable` definition (the note) | `↔` theorem (recommended) |
|---|---|---|
| Where the test is | in the body, as the `holds` field; found by evaluating it | in the statement: the left side |
| What a reader of std sees | a type `Decidable (a ∧ b)`; two readings with different tests have the same type | `(a && b) = True ↔ a ∧ b` |
| `= False` readings | encoded as `holds = not (a && b)`; the compiler infers "negative" from the `not`, and wraps each use to turn `e = False` into `not e = True` | `(a && b) = False ↔ a = False ∨ b = False`, as written |
| What the compiler emits | `r.sound h`, `r.complete p` | `r.forward h`, `r.backward p`: what proofs write by hand today |
| Existing lemmas | all rewritten as records | `List.memContains` and its like are readings already; they get the mark |
| Kind of definition | a `def` in `Type`: it has a value, and its body matters to anything that depends on it | a theorem: folded, never unfolded, and dependants see only its statement (`docs/core.md`, "Theorems stay folded") |
| Shape checks at declaration | `holds` not a bare parameter, not a constant, no parameter left undetermined, polarity inferred | the left side is `e = True` or `e = False` with a function at `e`'s head, and every parameter appears in `e` |
| A later `rewrite` with `↔` (bool-and-prop.md §7.4) or a `simp` | would have to unpack records | the same lemmas, as they are |
| A decision from a reading | is the reading | one line: `{ holds = test, sound = r.forward, complete = r.backward }` |

The note's argument for (2) was that D3480's record "is exactly a test with
its two proofs". That is true, and it is the reason the last row is one
line. But the record hides the one thing the reader, the user and the
error message all need first: which test. Both pieces of prior art that
pair a test with a proposition put the pair in the type: SSReflect's
`andP: reflect (b1 /\ b2) (b1 && b2)`, and Rocq's own library, which
states `andb_true_iff` as `b1 && b2 = true <-> b1 = true /\ b2 = true` and
proves `iff_reflect` to move between the two forms **[cited: R1, R2]**.
Isabelle has an attribute for exactly this job: `[iff]` "declares logical
equivalences to the Simplifier and the Classical reasoner at the same
time", and such a rule becomes "a safe introduction and elimination pair"
**[cited: I2]**. That is a reading: one marked equivalence, used both to
take a fact apart and to build it.

The one place (2) is shorter: a hand-written `DecEq` instance, test first,
needs one mark under (2) and a one-line theorem plus a mark under (3). A
std helper (`Decidable.reads d: d.holds = True ↔ p`) makes that line
mechanical, and step 2 already covers instances that are not test first.

### 2.4 One reading per test

The note files readings under (polarity, test head, proposition head), so
`xs.any f` may read as `∃ x ∈ xs, f x` *and* as `List.Any …`, and the
pattern picks. I recommend (polarity, test head) only: **each test reads as
one proposition.**

- **The user can ask one question.** "What does `xs.contains x` read as?"
  has one answer. `E-NO-READING` can always say it: "`found` is the test
  `xs.contains x`, which reads as `x ∈ xs`; `Both` needs an `∧`". A hover
  on the test, and a `stitchwort readings` listing, print the same line.
  With several readings per test the honest message is a list, and "the
  first declared wins" (§5.5, for `omega`) is a rule nobody can see.
- **An explicit crossing needs it** (§3.4): `found.read` with no expected
  type must mean one thing.
- **It is enough in practice** **[inferred]**. The reader computes the
  test first, so on a list of known shape `xs.all f` is already `f a &&
  rest.all f` and reads as `∧`, which is what `List.All` would have given.
  The second shape is one lemma away (`List.allToAll`, 15 uses).
- **Widening later is additive.** If a second shape proves necessary, the
  key grows and nothing written stops checking. Narrowing later would
  break proofs.

Two readings for one test in the plain sense (same key) are refused at the
declaration in both designs.

There is one overlap the key can't remove, and the note should say so: **a
test can be folded or unfolded.** `xs.contains x` is `List.any xs (member
=> member == x)` by definition. Folded it reads as `x ∈ xs`; if a `rewrite`
or an unfolding has left the `any` in the hypothesis, it reads as `∃`. The
rule that makes this predictable: **the reader goes by the test as the goal
prints it.** The reader and the printer must use the same folded form
(`quote_folded`), and the stage should test that they do. Neither choice
can prove anything false; both readings are equivalent to the test.

### 2.5 Where a reading may be declared

The note copies the instance rule: the module that owns the test's head
function *or* the proposition's head. I recommend **the test's home only**:
the file that declares the test's function in std, the namespace that
declares it in a project.

- **Std is one owner** (`interfaces.rs:172`, `module_owner`), so the
  module-level rule says nothing inside std. And std loads its files on
  demand, by the names a program mentions (`library.rs`, header). A
  pattern `Both l r` mentions no reading. If `List.any`'s reading lived in
  `List/Lemmas.sw` while `List.any` is in `List/Toolkit.sw`, the pattern
  would work or fail by whether something else had loaded `Lemmas.sw`.
  Std has had this bug twice, for instances (SW-1362) and congruence
  lemmas (SW-1354), and `instances_beside` (`library.rs:514`) now checks
  instances at the level of files for that reason **[checked]**. A test
  can only appear in a term if its file is loaded, so a reading in the
  same file is always there.
- **The check cache** keys a unit by its own text and the keys of the
  units it needs (`cache/mod.rs`, header). The test's home is always among
  those. A reading anywhere else is an input the key can miss, in the one
  way an entry's dependency list doesn't catch: a reading that *wasn't*
  there when the unit was checked **[inferred]**. The readings table
  itself is one more side table in an entry, as the instance table is.
- **No action at a distance.** With this rule, importing a namespace can
  never change how a test from elsewhere reads. That is the property
  Isabelle's global rule sets lack; its manual warns that "the union of
  simpsets from theory imports … is not always a good starting point"
  **[cited: I2]**.

What it costs: a project can't give a std test a reading std forgot. It can
still use the lemma by hand, or wrap the test in its own function, which
may have a reading. And std's readings sit beside the functions, not in
the lemma files, so their proofs (about ten lines each for `any`, `all`,
`contains`) move to `Toolkit.sw`.

The three connectives' tests are not functions with a home (`&&` is an
`if`), so their six readings go in the core, which is always loaded. `Iff`
is in `Logic/Logic.sw` today, outside the core **[checked]**; either it
moves in, or the core's six are stated as pairs of implications. An
implementation call.

### 2.6 The amended reading, in full

```
@[reading]
theorem Bool.andReads (a b: Bool): (a && b) = True ↔ a ∧ b
@[reading]
theorem Bool.andReadsFalse (a b: Bool): (a && b) = False ↔ a = False ∨ b = False
@[reading]
theorem List.containsReads [auto eq: DecEq a] (xs: List a) (x: a): xs.contains x ↔ x ∈ xs
@[reading]
theorem List.anyReads (xs: List a) (f: a → Bool): xs.any f ↔ ∃ (x: a) => x ∈ xs ∧ f x
```

Finding a reading for a test `t` with polarity `True` or `False`:

1. Compute `t` to where it is stuck, keeping calls folded.
2. If `t` is `d.holds` for a stuck decision `d: Decidable P`, it reads as
   `P` (or `¬P`), through `d.sound`, `d.complete` and `Decidable.refute`.
3. Look up (polarity, head of `t`). At most one theorem is there; match
   its left side against `t` to fill its parameters.
4. If none, and the head is a definition that isn't `opaque`, unfold one
   step and go to 1 (the note's bound of 8).
5. Otherwise `t` is a leaf, and reads as itself.

A pattern, a constructor or `.read` then works on the one proposition
found. If a pattern's constructor doesn't belong to it, that is
`E-NO-READING`, which names the proposition.

Step 4 has a cost the note doesn't mention: `match h with | Both lo hi` on
`h: c.isDigit` would work, by unfolding `isDigit` to its two comparisons.
A proof written that way depends on how `isDigit` is implemented. That is
true of any proof that unfolds a definition, and `opaque` is the existing
way to stop it; the stage must make the reader respect `opaque`, and the
guide should say that a test meant to be abstract gets a reading of its
own or is `opaque`.

### 2.7 A coherence check worth adding

Std has two tests for list membership today: `if x ∈ xs` runs
`(List.decMem x xs).holds` and `if xs.contains x` runs `List.any …`
(§1). Both read as `x ∈ xs` (by step 2 and by declaration), but they are
different terms, so a fact from one doesn't rewrite a program written
with the other. That is the two-`if` problem D3480 removed, left over in
std's own instances.

The rule that removes it: **where a test `t` reads as `P` and `P` has a
decision, the decision's `holds` is `t`.** It is cheap to check when
either is declared (compare with unknowns, warn if they differ), and
cheap to satisfy: the instance is built from the reading in one line. It
also makes the backward crossing a plain library function (§3.4).

## 3. D3488: silent crossing

### 3.1 Is it sound?

Yes. The elaborator writes `r.forward h` or `r.backward p` and the kernel
checks it. Both sides are proofs, erased at run time. Nothing is trusted.

### 3.2 Is it predictable?

Less than the note says. The note's safety argument is that crossing
"happens only where there is a type error today". Three problems follow
from the fact that `e = True` is an equation.

**(a) Where an equation is wanted, there is no error to hook.** The
largest family of crossings by far is `==` to `=`: `DecEq.sound` (290) and
`Nat.equalSound` (46). Their targets are equations, and so is the fact.

- `rewrite same in …` with `same: (x == y) = True` checks today, and
  means "replace `x == y` by `True`". A user told that "a test fact is
  accepted where its reading is wanted" will expect it to rewrite `x` to
  `y`. It won't, and nothing will say why: the likely result is a warning
  that the rule matched nothing, or a goal that didn't change. 109 of the
  290 `DecEq.sound` calls are rewrite rules **[measured]**.
- `Eq.sym same`, `Eq.trans same …`: the parameter's type is `?a = ?b`
  with both sides unknown, and `(x == y) = True` fits it. The call checks
  and gives `True = (x == y)`; the error comes later and somewhere else
  **[inferred]**.
- `let equal := same`: there is no expected type, so nothing happens.

**(b) Whether there is a mismatch can depend on the order things are
elaborated.** For `f same` where `f: [x y: a] → x = y → …`, the expected
type is `?x = ?y`. If `a` is already known not to be `Bool`, the fact
doesn't fit and crossing fires. If `a` is still unknown, or is `Bool`, the
fact fits as it stands. So moving an argument, or adding an annotation
elsewhere, can change whether the crossing happens. The note's condition
"both are known" doesn't settle this; a type is often half known
**[inferred]**.

**(c) The elaborator uses type errors to choose.** Several places try one
reading and fall back to another when the first fails, "with everything
the first try did undone": `if c` (a `Bool` first, then a proposition),
`&&` with nothing expected, comparison sections (`docs/syntax.md`, "`&&`,
`||` and `not`") **[checked]**. A program that checks today may check
*because* a first try hit a type mismatch. If crossing turns that mismatch
into a success, the program now elaborates down the other path, to a
different term, with no error anywhere. So "only where there is an error
today" is not the same as "only in programs that are rejected today".
This applies to the pattern and constructor hooks too, though far less:
those mismatches (a `Both` against an equation) are not ones the fallback
paths rely on. See §5.1 for the check.

Smaller surprises:

- **Goals.** After stage 1 a list fact prints `found: xs.contains x` and
  the wanted type `x ∈ xs`; for a set, `k ∈ s` *is* `s.contains k = True`,
  one term. Silent crossing makes the list case behave like the set case
  in arguments but not in `rewrite`, so the difference a user must
  eventually learn shows up later and less clearly.
- **"Why didn't it cross?"** One layer only is the right limit, but it is
  a limit users will hit: `h: (x == y) = True ∧ q` is not accepted for `x
  = y ∧ q`. The mismatch error then has to explain a conversion that was
  nearly applied.

### 3.3 Is the win what the note says?

The note: "at least 615" uses removed by crossing, half of the total.

Sorting the 510 named-helper uses by what stands just before them
**[measured, rough: a script on the preceding text]**:

| Position | Uses | Silent crossing |
|---|---|---|
| An argument or a result with a known type | 244 | may apply |
| A `let` with a type | 26 | applies |
| A `rewrite` rule | 121 | can't: no expected type, and the fact is a valid rule already |
| A `let` with no type | 48 | can't: no expected type |
| Under `Eq.sym`, `Eq.trans`, `Eq.cong` | 32 | can't: the fact fits as an equation |
| In an `omega [...]` or `auto [...]` list | 17 | not needed where `omega` reads the fact already |
| The helper's own definition or docs | 22 | not a use |

So at most 270 of 510 (53%), and that is a ceiling: "an argument with a
known type" includes arguments whose type is only half known (3.2 b).

For the other 105 (`.forward`/`.backward` on a test-to-proposition `↔`),
at least 30 are on lemmas that are not readings by the note's own rule of
one function per reading (§13, "Readings that overreach") **[checked]**:

- `Set.containsFromListIff` (16) is about `(Set.fromList xs).contains
  key`, two functions deep (`Set/Spec.sw:319`);
- `Set.memToList` (14) relates `key ∈ s.toList` to `s.contains key`, and
  `s.contains key` already reads as itself (`Set/Spec.sw:408`).

A fair restatement: silent crossing removes perhaps 300 to 350 calls, a
quarter of the 1,265, not a half. Patterns and building (stages 2 and 3)
are unaffected and remain the larger, safer win.

### 3.4 What to build instead: one explicit word

A postfix form on a test fact that means "this fact, as the proposition
its test reads as". The working name here is `.read`; the name is Matt's
to choose (§7).

```
rewrite same.read in …                    -- today: rewrite DecEq.sound same in …
let equal := same.read
Eq.sym same.read
| True => omega [(within _ found.read).right]   -- 2024 day 12, Sides.sw:226
let Both _ sameFrequency := same in … sameFrequency.read …
```

- **It works in every position**, including the 201 where silent crossing
  can't. It needs no expected type, because each test has one reading
  (§2.4).
- **It is one layer**, as a pattern is. `h.read.read` is two.
- **It fails at the word.** `b.read` on a variable's fact is
  `E-NO-READING`: "`b` is a variable, so the fact `b` has no parts". There
  is no "nearly crossed" case to explain.
- **The mismatch error teaches it.** Where `found` is passed for `x ∈
  xs`, today's `E-TYPE-MISMATCH` gets the note "`found` is the test
  `xs.contains x`, which reads as `x ∈ xs`: write `found.read`", and the
  editor can offer that as a fix.
- **It is what the pattern hook already needs.** A pattern on a test fact
  matches on `r.forward h`; `.read` is that term with no pattern round it.
  So it adds almost nothing to stage 2.
- **`e = False`** reads through the negative reading where there is one,
  and otherwise as `¬(e = True)`. So `absent.read` covers
  `Bool.falseOfNotTrue`'s partner, `DecEq.soundFalse` and `Nat.leqFalse`.

Going back, from a proposition to its test fact, has two cases:

- *The wanted type is known* (`isIn` given where `xs.contains x = True`
  is wanted): the reader finds the reading from the wanted test and
  writes `r.backward isIn`. This is the one direction where the explicit
  word needs the expected type, and a second name may read better than
  reusing `.read` (§7).
- *It isn't* (`rewrite … in`): this is instance search, which exists. With
  §2.7's rule the decision for `x ∈ xs` has `xs.contains x` as its
  `holds`, so a std function `[auto d: Decidable p] (h: p): d.holds =
  True` gives the test fact, with no reader involved. The `Decidable`
  record has made that half of crossing a library matter.

Prior art agrees that the crossing is written, though each makes it short.
Lean coerces a `Bool` to `b = true` and a decidable proposition to a
`Bool` **[cited: L2]**, but going from `(a == b) = true` to `a = b` in a
term is a named lemma or a `simp` call **[recalled]**. SSReflect writes
the view: `move/eqP` **[cited: R1]**. Agda writes `toWitness` and
`fromWitness` **[cited: A5]**. None converts a whole hypothesis silently
at a mismatch.

### 3.5 Silent crossing later, if at all

Once `.read` exists, silent crossing is "insert `.read` where the types
don't fit". If Matt wants it after seeing proofs written with `.read`, the
version that avoids §3.2's problems is:

- only where the wanted type's head is known and is **not `=`** (so never
  `==` to `=`, where a mismatch can't be told from a fit);
- only outside the elaborator's own try-and-fall-back paths;
- `e = False` against `¬(e = True)` first: the wanted type is a function
  type, which no equation fits, so the mismatch is always certain.

By the script's counts that would cover about 139 of the 510 named uses
(`soundFalse`, `leqFalse`, `falseOfNotTrue`, `allToAll`, `allOfAll` in
argument positions), plus the eligible `.forward`/`.backward` calls. That
is a modest gain over one written word, which is why it should wait for
real counts.

## 4. The reader's shape (§5, §6, §9 of the note)

**Keep:** one layer at a time, driven by the pattern; no search; nothing
trusted; a name or `_` stops the reading and leaves a test fact for
`rewrite`; the stuck-decision step; unfolding a test with no reading of
its own; reading and `match h:` kept separate.

**Simplify:**

- `read(test, polarity)` gives one proposition. The `wanted` argument
  goes, with the "first declared wins" rule and the "two with different
  wanted shapes" case (§5.5 of the note).
- Negative polarity needs no `not` encoding and no fixed `Bool.notTrue`
  step: `Bool.not a = True ↔ a = False` is itself a reading, and the
  reader reads the result again when the pattern asks.
- The `∀` hooks (§6.6: a test fact applied to arguments, a lambda checked
  against a test fact) can go. `allSmall.read y yIn` applies the function
  the reading gives, and a std function builds the fact from a lambda.
  The hooks serve few uses (`List.allMember` 18, `Set.isSubsetIntro` and
  `Elim` 5 **[measured]**) and are the most surprising part of the
  design: an equation's proof applied like a function.

**Decide explicitly** (the note leaves these open or implicit):

- **`Refl` on a test fact keeps its present meaning.** `match h with |
  Refl` on `h: b = True` substitutes `True` for `b` today. The note's §6.1
  lists only `Both`, `Inl`, `Inr` and `Witness` as triggers, but §6.5 and
  §8.3 talk of `Refl` and of `same` "crossing to the equation" inside a
  pattern. If `Refl` on `(x == y) = True` read the fact as `x = y`, the
  same pattern would mean two different things by whether the test is a
  variable. So: `Refl` never triggers a reading; write `match same.read
  with | Refl`.
- **The reader is off inside try-and-fall-back elaboration**, or each such
  path is checked one by one (§3.2 c).
- **In a program** (a `def` returning data), a fact read as `∨` or `∃`
  can't be matched (`E-PROP-ELIM`, as the note says). The error there
  should point to `match e: test with`, which is what a program wants.

**`omega`, `auto`, `cases` (§9).** "One reader for all" is the right end
state for the *table*: `omega` should not carry a private copy of the
connective lemmas by name. But the order matters:

- `omega` already reads `&&`, `||`, `not`, both polarities and decisions,
  after computing the fact (`omega.rs`, header) **[checked]**. Moving it
  onto the reader changes the terms it emits and no proof a user writes.
  It is a refactor of the most heavily used tactic for no visible gain, so
  it goes last, and only if the reader's interface turns out to fit
  `omega`'s needs (it reads goals as well as facts, and splits).
- `auto`'s `from_conjuncts` and `cases`' hypothesis closer gain something
  visible from `facts_of`: an `if a && b` whose fact is a test fact is
  used like a `∧`. Small, and worth doing after stage 2.
- The `e = True` against `e = False` closer needs no reader at all. It can
  be its own ticket now.

## 5. Risks the note under-rates, and what to measure first

### 5.1 The reader changing programs that check today

§3.2 (c). **The check:** stage 2's lane, and any later crossing lane,
must show that no existing example's hash snapshot changes, and the
verifier should confirm it over std and AoC after the merge. A changed
hash on a program nobody edited means the reader fired inside a fallback
path. This is the measurement to insist on, and it costs nothing to
write: the snapshots exist.

### 5.2 Load order and the cache

§2.5. **The check:** an index-time rule like `instances_beside`: every
`@[reading]` in std is in the file that declares its test's function.
Without it, the first symptom would be a proof that passes or fails by
what else is in the run.

### 5.3 The test's folded form

§2.4. Which reading applies goes by whether the test is folded. **The
check:** a test in stage 2 that reads a fact both ways, and that the
goal's printed test is the one the reader keyed on.

### 5.4 Readings by unfolding leak implementations

§2.6, step 4. Not a soundness matter. The stage must respect `opaque`,
and the guide must say what to do for a test meant to be abstract.

### 5.5 Std's instances disagree with std's tests

§1 and §2.7. `x ∈ xs` and `xs.contains x` are two tests. Readings paper
over it for patterns but not for `rewrite`. **Measure:** how many std
decisions have a `holds` that is a named test with unknowns: by my reading
12 of 16 are, and `List.decMem`, `decDistinct`, `decSorted`, `decLeHead`
are not **[checked, by reading each instance's first lines]**.

### 5.6 The counts are of calls, not of proofs that get shorter

The note says this for patterns (§8.4). It applies more to crossing:
`rewrite DecEq.sound same in` becomes `rewrite same.read in`, which is
shorter and needs no lemma name, but is not gone. The win of `.read` is
that there is one word to know instead of thirty lemma names, not fewer
tokens. **Measure before the sweeps:** rewrite 2024 day 8's
`part2IncludesPart1` and day 12's `Sides.sw:226` by hand once stage 2 is
in, and compare with §8.1 and §8.2's sketches, which were never checked.

### 5.7 Cost

Lookup is a hash by head and one first-order match; it is not a risk. The
cost to watch is the unfolding in step 4 on the error path, where a
pattern that doesn't fit may unfold a large test eight times before
reporting. The bound should be on work, not only on steps.

## 6. Proposed changes to bool-as-proposition.md

I have not edited the note. In order of the note's sections:

1. **Status, §2, §10, §11:** bring up to date as in §1's table here;
   `does` becomes `holds` throughout.
2. **§5.1:** a reading is a `@[reading]` theorem `e = True ↔ P` or `e =
   False ↔ P`; rewrite the two examples and the table's "Negative" column
   as theorems; drop the `holds = not (…)` encoding.
3. **§5.2:** replace "an attribute on a `Decidable`" with §2.3's table;
   drop "an `instance` may also carry `@[reading]`"; add `Decidable.reads`
   and the one-line decision from a reading. `@[reading]` is the first
   attribute allowed on a theorem (`attributes.rs`: "a theorem can't have
   attributes" **[checked]**).
4. **§5.3:** the key is (polarity, test head). The refusal list becomes:
   the left side isn't a test fact; the test's head is a variable or a
   constant; a parameter doesn't appear in the test; the head already has
   a reading (`E-READING-OVERLAP`); it isn't declared in the test's home
   (file in std, namespace in a project). Add the index-time file check.
5. **§5.4:** `read(test, polarity)`; step 4 respects `opaque`.
6. **§5.5:** delete "two with different wanted shapes" and "first declared
   wins"; add the folded-or-unfolded rule (§2.4 here).
7. **§5.7:** add the load-order argument and the cache's missing-reading
   case; bound step 4 by work.
8. **§6.1, §6.5:** say that `Refl` never triggers a reading. **§6.6:**
   drop the lambda and application hooks; keep constructors and `h.left`.
9. **A new §6.8, "Reading a whole fact":** `.read`, both polarities, and
   the two ways back (§3.4 here).
10. **§7:** rewrite as "silent crossing, deferred", with §3.2's three
    problems and §3.5's restricted version.
11. **§8.2, §8.3:** rewrite the "after" lines with `.read`. **§8.4:**
    replace "at least 615" with §3.3's table; move `Set.containsFromListIff`
    and `Set.memToList` out of the crossing row.
12. **§9:** `omega` last and optional; `auto` and `cases` on `facts_of`;
    the closer as its own ticket.
13. **§11**, the plan:

| # | Lane | Change from the note |
|---|---|---|
| now | The `e = True` against `e = False` closer for `cases` and `auto` | new; needs nothing; small |
| now | Std's four recursive decisions written test first (`decMem`, `decDistinct`, `decSorted`, `decLeHead`), and `deriving (DecEq)` as decidable-record.md stage 4 planned | new; a std lane; can run beside stage 2 |
| 2 | The reader with `&&`, `\|\|`, `not`: `@[reading]` theorems, one per test, placed with the test; patterns, building, both polarities, **`.read`**; `E-NO-READING`, `E-READING-OVERLAP`; the readings table in the cache; the reader off in fallback paths; **no example hash changes** | amended shape; `.read` added; hash check added |
| 3 | Std's readings for `any`, `all`, `contains`, `Nat.equal`, `isSubset`, `isSome`, `isEmpty` and the negatives, each beside its function; the decision-agrees-with-reading warning | the `∀` hooks dropped, so all Sonnet |
| 4 | **Measure, then decide**: after one AoC year is swept with `.read`, count the `.read`s that sit where §3.5's restricted silent crossing would apply | replaces "Crossing" |
| 5 | `auto` and `cases` on `facts_of` | `omega` split off |
| 6 | Sweeps | unchanged; they use `.read` |
| 7 | Guide and tour | unchanged; one sentence more: "to use the whole fact as its proposition, write `.read`" |
| last | `omega` on the reader's table | optional |

14. **§12:** D3487 and D3488 restated as in §7 here. Under
    "implementation calls": the key; `Refl`; `opaque`; the six core
    readings and where `Iff` lives.
15. **§13:** add §5.1 to §5.5 here. Under "what it rules out": one reading
    per test can be widened later; silent crossing can be added later;
    neither can be taken back cheaply, which is the reason for the order.

## 7. Decisions for Matt

- **D3487: Are readings ordinary proved definitions marked `@[reading]`,
  which std and projects can add, and not a fixed list in the compiler?**
  **[rec: yes]**, in this form: a reading is a theorem `test ↔
  proposition`; each test has one; it is declared where the test is. The
  alternative shape is the note's (a `Decidable` definition, several per
  test chosen by the pattern, declared in either owner's module).
- **D3488: Should a whole fact be converted silently where its reading is
  wanted, and back?** **[rec: no for now. Add an explicit postfix word in
  stage 2; revisit silent crossing after a measured sweep, and then only
  where the wanted type is not an equation.]**
- **New, needs a number: what is the word?** `found.read` is the working
  name. It should be short, read as "the fact, as its proposition", and
  not look like a field. Candidates: `.read`, `.fact`, `.meaning`. A
  second word for the way back where the wanted type is known (a
  proposition given, a test fact wanted) is worth having if one word
  reads wrongly in that direction. **[rec: `.read`; decide the way back
  when stage 3 shows how often it is needed]**

## 8. What this review did not do

- Nothing was run. What the elaborator does today with `Eq.sym same`,
  with `Refl` on `(x == y) = True`, and with a half-known expected type
  (§3.2, §4) is inferred from the notes and `docs/syntax.md`, not probed.
- The position counts (§3.3) come from a script that looks at the text
  before each helper name. They are good to perhaps ten percent. The 105
  `.forward`/`.backward` uses were not classified, beyond the two lemmas
  named.
- I read the headers of `library.rs`, `cache/mod.rs`, `interfaces.rs`,
  `attributes.rs` and `omega.rs`, and the std files named, not the bodies.
  Whether std can load a file in the middle of checking a declaration
  (which would be another way to solve §2.5) I did not establish; the
  header says loading is decided before a module is checked.
- "12 of 16 instances are test first" (§5.5) is from each instance's
  first line.
- The design of `.read` going backward is a sketch.
- Lean's term-mode crossing lemmas are recalled, not re-read. The
  SSReflect, Rocq, Isabelle, Lean and Agda pages were read through a tool
  that returns extracts, not in full.

Findings for tickets:

1. `List.decMem`, `decDistinct`, `decSorted` and `decLeHead` recurse on
   the list, so `if x ∈ xs` and `if xs.contains x` are different tests
   (§1). Write them test first.
2. `deriving (DecEq)` still answers by `Decidable.yes`/`no` under a match
   (`derive.rs:49-56`); decidable-record.md stage 4 planned a test
   `T.%same`.
3. `cases` and `auto` don't close a goal from `h: e = True` and `k: e =
   False` (the note's finding 2): needs no reader.
4. bool-as-proposition.md §8.4 counts `Set.containsFromListIff` and
   `Set.memToList` as crossings; neither is a one-function reading.

## Sources

- **[R1]** The Rocq reference manual, "The SSReflect proof language",
  "Views and reflection" (read today: "The reflect predicate", "General
  mechanism for interpreting goals and assumptions", "Declaring new Hint
  Views").
  <https://rocq-prover.org/doc/V9.0.0/refman/proof-engine/ssreflect-proof-language.html>
- **[R2]** Rocq standard library, `Stdlib.Bool.Bool` (read today:
  `reflect_iff`, `iff_reflect`, `andb_true_iff`, `eqb_spec`, and that the
  `bool` hint database is used only by `auto with bool`).
  <https://rocq-prover.org/doc/V9.0.0/stdlib/Stdlib.Bool.Bool.html>
- **[L2]** The Lean Language Reference, "Booleans" (read today: the two
  coercions; nothing there on converting `b = true` facts).
  <https://lean-lang.org/doc/reference/latest/Basic-Types/Booleans/>
- **[I2]** The Isabelle/Isar Reference Manual, "Generic tools and
  packages" (read today: the `iff`, `intro`, `elim`, `dest` attributes;
  the Simplifier's note on imported simpsets).
  <https://isabelle.in.tum.de/website-Isabelle2021/dist/library/Doc/Isar_Ref/Generic.html>
- **[A5]** agda-stdlib, `Relation.Nullary.Decidable.Core` (read today:
  `Dec`, `isYes`, `True`, `toWitness`, `fromWitness`).
  <https://agda.github.io/agda-stdlib/master/Relation.Nullary.Decidable.Core.html>

Stitchwort notes and code this builds on: bool-as-proposition.md,
bool-and-prop.md, bool-operators-in-propositions.md, decidable-record.md,
`docs/syntax.md` ("A `Bool` as a proposition", "`&&`, `||` and `not`"),
`crates/elab/src/{interfaces,library,attributes,omega,derive}.rs`,
`crates/elab/src/cache/mod.rs`, `crates/elab/src/std/core/Decidable.sw`,
`std/List/Toolkit.sw`, `std/Set/Spec.sw`, `std/Logic/Logic.sw`.
