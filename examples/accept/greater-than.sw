-- `a > b` is `b < a` and `a >= b` is `b <= a`: the same terms, so goals and
-- messages show `<` and `<=`. `a > b` runs `b` first, which only matters for
-- nothing: the language is pure. `!b` is `Bool.not b`.

import Std (Nat)

type Suit = | Clubs | Diamonds | Hearts | Spades

test "Nat" := 3 > 2 ∧ 3 ≥ 3 ∧ ¬(2 > 3) ∧ ¬(2 ≥ 3)
test "Int" := (-1: Int) > -2 ∧ (0: Int) ≥ 0 ∧ ¬((-3: Int) > -2)
test "Text" := "b" > "a" ∧ "a" ≥ "a" ∧ ¬("a" > "b")
test "a derived Ord" := Spades > Clubs ∧ Hearts ≥ Hearts ∧ ¬(Clubs ≥ Diamonds)
test "not" := ¬False ∧ ¬(¬True)
test "precedence" := ¬False ∧ True
test "a decision" := (if 5 > 0 then 1 else 2) == 1

def sign (x: Int): Nat := if x > 0 then 1 else if x < 0 then 2 else 0

test "if on >" := sign 4 == 1 ∧ sign (-4) == 2 ∧ sign 0 == 0

def nonEmpty (t: Text): Bool := ¬t.isEmpty

test "bang on a method call" := nonEmpty "a" ∧ ¬nonEmpty ""

-- In a statement, `>` is `<` the other way round, so a lemma about `<` proves it.
theorem greaterOfLess (a: Nat) (b: Nat) (h: a < b): b > a := h

theorem greaterEqOfLessEq (a: Nat) (b: Nat) (h: a ≤ b): b ≥ a := h

theorem succGreaterEq (n: Nat): Succ n ≥ n := Nat.leSucc n

-- A chain of `>` and `>=` proves what the steps add up to: `a > b >= c` is
-- `c < a`. The proofs are those of the flipped steps.
theorem descending (a: Nat) (b: Nat) (c: Nat) (h1: b < a) (h2: c ≤ b): a > c :=
  calc a
    _ > b := h1
    _ ≥ c := h2

theorem descendingLe (a: Nat) (b: Nat) (c: Nat) (h1: b ≤ a) (h2: c ≤ b): a ≥ c :=
  calc a
    _ ≥ b := h1
    _ ≥ c := h2

-- `=` goes with either direction; its proof is used flipped.
theorem descendingEq (a: Nat) (b: Nat) (c: Nat) (h1: a = b) (h2: c < b): a > c :=
  calc a
    _ = b := h1
    _ > c := h2

-- `!` is `not`: where a proposition is expected it's `Not`.
theorem notGreater (a: Nat) (b: Nat) (h: ¬(a > b)): Not (b < a) := h
