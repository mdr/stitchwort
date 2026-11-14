-- `lo <= x <= hi` is `lo <= x && x <= hi`: `<` and `<=` chain together, as
-- do `>` and `>=`. A middle operand that is a call is computed once, in
-- order, and the later links are only tested if the earlier ones hold. The
-- goals, facts and hypotheses read as the conjunction written out.
import Std (Bool, Fail, List, Nat, Parse, Result)
import Std.Fail (toResult)

def inRange (lo x hi: Nat): Bool := lo <= x <= hi

test "in range" := inRange 1 2 3
test "below" := !inRange 3 2 3
test "above" := !inRange 1 4 3

-- A name or a literal in the middle gives the very conjunction written out.
theorem inRangeIsConjunction ∀ (lo x hi: Nat): (lo <= x <= hi) = (lo <= x ∧ x <= hi) := rfl

-- Any length, and downwards.
theorem ascending ∀ (a b c d: Nat) (h: a < b <= c < d): a < d := omega

theorem descending ∀ (a b c: Nat) (h: c >= b > a): a < c := omega

-- A chain is one conjunct of a longer `∧`.
theorem oneConjunct ∀ (a b c: Nat) (h: a <= b <= c ∧ b != 0): a <= b := h.left.left

def twice (n: Nat): Nat := n + n

-- The middle is a call: the statement reads as written out.
theorem rangeOfTwice ∀ (n: Nat) (h: 3 <= twice n <= 9): n < 5 := omega

theorem rangeOfTwiceParts ∀ (n: Nat) (h: 3 <= twice n <= 9): 3 <= twice n := h.left

-- An `if` learns the whole chain; `auto` uses its parts.
def pred (n: Nat): Nat := if 3 <= twice n <= 9 then n - 1 else 0

test "pred" := pred 3 == 2

def named (n: Nat): Nat := if h: 3 <= n <= 9 then n - 3 else 0

test "named" := named 5 == 2

def guarded: Nat → Nat
  | k if 3 <= twice k < 9 => k
  | _ => 0

test "guarded" := guarded 3 == 3 && guarded 5 == 0

def inLambda (xs: List Nat): List Nat := xs.filter (x => 2 <= twice x <= 8)

test "in a lambda" := inLambda [0, 1, 2, 3, 4, 5] == [1, 2, 3, 4]

-- The middle reads the input once.
def digit(): {Parse} Bool := 0 < Parse.nat() <= 9

test "once" := toResult (() => Parse.line "5" digit) == Ok True
test "too big" := toResult (() => Parse.line "15" digit) == Ok False

-- The second `Parse.nat()` is not run when the first link fails, so there is
-- no second number to read.
def skipped(): {Parse} Bool := 5 < Parse.nat() <= Parse.nat()

test "short-circuits" := toResult (() => Parse.line "3" skipped) == Ok False

-- A chain inside a larger `if h:` proposition keeps its facts: the goals read
-- as written, and `h` gives the parts.
def nestedNamed (n: Nat): Nat := if h: n != 0 && 3 <= twice n <= 9 then 12 / n + (twice n - 3) * 0 else 0

test "nested" := nestedNamed 3 == 4 ∧ nestedNamed 0 == 0 ∧ nestedNamed 5 == 0

def nestedEither (n: Nat): Bool := if h: n = 0 || 3 <= twice n <= 9 then True else False

test "nested or" := nestedEither 0 ∧ nestedEither 3 ∧ !nestedEither 1

-- The input is read once, whichever side of the `&&` the chain is on.
def guardedDigit (ok: Bool): {Parse} Bool := ok && 0 < Parse.nat() <= 9

test "once, after &&" := toResult (() => Parse.line "5" (() => guardedDigit True)) == Ok True
