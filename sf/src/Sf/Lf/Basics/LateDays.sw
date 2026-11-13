-- Software Foundations, Volume 1: Logical Foundations, Basics.v, section
-- "Course Late Policies, Formalized" (module `LateDays`), ported to
-- Stitchwort. Copyright and licence: sf/LICENSE-SF. Exercises are stated
-- as in Basics.sw: a statement or a function with `?` for the reader to
-- fill in.

namespace Sf.Lf.Basics.LateDays

-- Suppose a course lowers a student's final letter grade if they hand in
-- too many assignments late. This section models that, with the features
-- seen so far, and proves some simple facts about the policy.
--
-- First, a data type for the "letter" part of a grade:

type Letter =
  | A
  | B
  | C
  | D
  | F

-- Then the modifiers: a `Natural` `A` is a plain grade of A.

type Modifier =
  | Plus
  | Natural
  | Minus

-- A full grade is a letter and a modifier. Informally, "A-" is
-- `MkGrade A Minus`, and "C" is `MkGrade C Natural`.
--
-- The book names the constructor `Grade`, like the type. In Stitchwort
-- that makes every later use of `Grade` as a type ambiguous
-- (`E-AMBIGUOUS`), so the constructor is `MkGrade`, as the library's
-- `Pair` has `MkPair`.

type Grade =
  | MkGrade (l: Letter) (m: Modifier)

-- We want to say when one grade is better than another, so we need to
-- compare grades. We could define tests (`gradeEqb`, `gradeLtb`, …), but
-- a slightly more informative type for a comparison says whether two
-- values are equal, less or greater. The book defines one, `comparison`,
-- with constructors `Eq`, `Lt` and `Gt`, and notes that Rocq's library
-- has it too. Stitchwort's library has it as `Ordering`, with
-- constructors `Less`, `Equal` and `Greater`, which this port uses.
--
-- Comparing two letters uses two features of patterns. Matching two
-- values at once, separated by a comma, is shorthand for nested matches:
--
--     match l1, l2 with          match l1 with
--       | A, A => Equal            | A => match l2 with
--       | A, _ => Greater            | A => Equal
--                                    | _ => Greater
--
-- And `|` inside a pattern matches any of several alternatives: the
-- pattern `C, (A | B)` stands for the two cases `C, A` and `C, B`.

def letterComparison (l1 l2: Letter): Ordering := match l1, l2 with
  | A, A => Equal
  | A, _ => Greater
  | B, A => Less
  | B, B => Equal
  | B, _ => Greater
  | C, (A | B) => Less
  | C, C => Equal
  | C, _ => Greater
  | D, (A | B | C) => Less
  | D, D => Equal
  | D, _ => Greater
  | F, (A | B | C | D) => Less
  | F, F => Equal

-- Trying it on a few examples:

test "letterComparison B A" := letterComparison B A == Less

test "letterComparison D D" := letterComparison D D == Equal

test "letterComparison B F" := letterComparison B F == Greater

-- As a further check, `letterComparison` should give `Equal` when a letter
-- is compared with itself.

-- Exercise: 1 star, standard (letter_comparison)

theorem letterComparisonEq ∀ (l: Letter): letterComparison l l = Equal := ?

-- The same strategy compares two modifiers, ordered `Plus > Natural >
-- Minus`.

def modifierComparison (m1 m2: Modifier): Ordering := match m1, m2 with
  | Plus, Plus => Equal
  | Plus, _ => Greater
  | Natural, Plus => Less
  | Natural, Natural => Equal
  | Natural, _ => Greater
  | Minus, (Plus | Natural) => Less
  | Minus, Minus => Equal

-- Exercise: 2 stars, standard (grade_comparison)
--
-- Complete the definition by pattern matching. This ordering is
-- "lexicographic": compare the letters first, and look at the modifiers
-- only if the letters are equal, so every A is above every B. Hint: match
-- `g1` and `g2` together, but don't list all the cases: split on the
-- result of a suitable call to `letterComparison`, to get just three.

--| Exercise (grade_comparison): replace the `?` with the definition.
def gradeComparison (g1 g2: Grade): Ordering := ?

-- These unit tests should hold once it is defined correctly.

theorem testGradeComparison1: gradeComparison (MkGrade A Minus) (MkGrade B Plus) = Greater := ?

theorem testGradeComparison2: gradeComparison (MkGrade A Minus) (MkGrade A Plus) = Less := ?

theorem testGradeComparison3: gradeComparison (MkGrade F Plus) (MkGrade F Plus) = Equal := ?

theorem testGradeComparison4: gradeComparison (MkGrade B Minus) (MkGrade C Plus) = Greater := ?

-- Now a late penalty. First, what it means to lower the letter of a
-- grade. `F` is already the lowest, so it is left alone.

def lowerLetter (l: Letter): Letter := match l with
  | A => B
  | B => C
  | C => D
  | D => F
  -- Can't go lower than F!
  | F => F

-- The formalisation already helps with corner cases of the policy. We
-- might expect `lowerLetter`'s result to be lower, as this claims:
--
--     theorem lowerLetterLowers (l: Letter): letterComparison (lowerLetter l) l = Less := cases
--
-- But it isn't provable. (Do you see why?) In Rocq the proof, by cases
-- on `l`, gets stuck in the last case. Stitchwort's `cases` splits `l`
-- and closes four of the five cases by computing. On the fifth, the
-- error says what is left, and, since a failed proof makes the checker
-- search for inputs that make the statement false, why:
--
--     [E-CASES] Error: `cases` can't close the case l = F
--       Note 1: goal: Equal = Less
--       Note 3: 4 other cases were closed (4 by computation)
--       Note 4: this statement is false; a counterexample:
--                 l = F
--               `letterComparison (lowerLetter l) l = Less` is false:
--                 left:  Equal
--                 right: Less
--
-- The problem is the edge case of lowering `F`:

theorem lowerLetterFIsF: lowerLetter F = F := rfl

-- With that insight, a better statement is provable. Its hypothesis says
-- that `F` is strictly smaller than `l`, which rules out the problem case:
-- as long as `l` is above `F`, it is lowered.

-- Exercise: 2 stars, standard (lower_letter_lowers)

theorem lowerLetterLowers ∀ (l: Letter) (h: letterComparison F l = Less): letterComparison (lowerLetter l) l = Less := ?

-- Exercise: 2 stars, standard (lower_grade)
--
-- Using `lowerLetter`, define what it means to lower a grade by one step:
-- send `g` one step lower, unless it is already `MkGrade F Minus`, which
-- stays as it is. Once it is right, the unit tests below should hold
-- trivially.
--
-- Hint: for a short definition that is easy to prove things about, use a
-- nested match. The outer one should look only at the modifier, not the
-- letter. Don't list all the cases. (The book's solution is under 10
-- lines.)

--| Exercise (lower_grade): replace the `?` with the definition.
def lowerGrade (g: Grade): Grade := ?

theorem lowerGradeAPlus: lowerGrade (MkGrade A Plus) = MkGrade A Natural := ?

theorem lowerGradeANatural: lowerGrade (MkGrade A Natural) = MkGrade A Minus := ?

theorem lowerGradeAMinus: lowerGrade (MkGrade A Minus) = MkGrade B Plus := ?

theorem lowerGradeBPlus: lowerGrade (MkGrade B Plus) = MkGrade B Natural := ?

theorem lowerGradeFNatural: lowerGrade (MkGrade F Natural) = MkGrade F Minus := ?

theorem lowerGradeTwice: lowerGrade (lowerGrade (MkGrade B Minus)) = MkGrade C Natural := ?

theorem lowerGradeThrice: lowerGrade (lowerGrade (lowerGrade (MkGrade B Minus))) = MkGrade C Minus := ?

-- The book states this one as a theorem rather than an example only as a
-- hint that it is used in proofs below.

theorem lowerGradeFMinus: lowerGrade (MkGrade F Minus) = MkGrade F Minus := ?

-- Exercise: 3 stars, standard (lower_grade_lowers)
--
-- As long as the grade starts above F-, `lowerGrade` does lower it.
-- Splitting everything in sight is *not* a good idea: split carefully,
-- and rewrite. Hint: with `gradeComparison` defined as suggested, you
-- only need to split a letter in one case, and the case for `F` will
-- probably use `lowerGradeFMinus`.

theorem lowerGradeLowers ∀ (g: Grade) (h: gradeComparison (MkGrade F Minus) g = Less): gradeComparison (lowerGrade g) g = Less := ?

-- With a function that lowers a grade by one step, we can write a
-- late-days policy. Given a number of late days, `applyLatePolicy`
-- computes the final grade from the initial grade `g`:
--
--     late days   penalty
--       0 - 8     none
--       9 - 16    lower by one step (A+ to A, A to A-, A- to B+, …)
--      17 - 20    lower by two steps
--        >= 21    lower by three steps (a whole letter)
--
-- The book writes the tests with its `ltb` (`late_days <? 9`), from the
-- exercise in Basics. Here they are the library's `<` on numbers.

def applyLatePolicy (lateDays: Nat) (g: Grade): Grade :=
  if lateDays < 9 then g
  else if lateDays < 17 then lowerGrade g
  else if lateDays < 21 then lowerGrade (lowerGrade g)
  else lowerGrade (lowerGrade (lowerGrade g))

-- Sometimes it helps to unfold a definition to make progress in a proof.
-- The book proves that a call of `applyLatePolicy` equals its right side
-- by `reflexivity`, so that `rewrite` can expose the definition's
-- internals:

theorem applyLatePolicyUnfold ∀ (lateDays: Nat) (g: Grade):
    applyLatePolicy lateDays g = (if lateDays < 9 then g
      else if lateDays < 17 then lowerGrade g
      else if lateDays < 21 then lowerGrade (lowerGrade g)
      else lowerGrade (lowerGrade (lowerGrade g))) :=
  rfl

-- In Stitchwort this lemma is rarely needed: a `match` on a test, such as
-- `match early: lateDays < 9 with | True => … | False => …`, finds the
-- test inside the definition and computes the `if` in each case. And
-- every definition comes with equations of its own (`applyLatePolicy.eq1`
-- here; `stitchwort doc applyLatePolicy` lists them).
--
-- Now some properties of the policy. If a student has at most eight late
-- days, their grade is unaffected. Once `applyLatePolicyUnfold` is used,
-- the hypothesis rewrites it.
--
-- The book states the hypothesis as `late_days <? 9 = true`. In
-- Stitchwort the proposition `lateDays < 9` *is* the test giving `True`,
-- so the hypothesis is written as the proposition; its negation, the
-- test giving `False`, is written `(lateDays < 9) = False`.

-- Exercise: 2 stars, standard (no_penalty_for_mostly_on_time)

theorem noPenaltyForMostlyOnTime ∀ (lateDays: Nat) (g: Grade) (h: lateDays < 9): applyLatePolicy lateDays g = g := ?

-- If a student has between 9 and 16 late days, their final grade is
-- lowered by one step.

-- Exercise: 2 stars, standard (graded_lowered_once)

theorem gradeLoweredOnce ∀ (lateDays: Nat) (g: Grade) (h1: (lateDays < 9) = False) (h2: lateDays < 17): applyLatePolicy lateDays g = lowerGrade g := ?
