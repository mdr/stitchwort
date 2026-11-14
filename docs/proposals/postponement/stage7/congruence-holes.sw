-- SW-967 (3), AoC 2021 day 12: a congruence lemma's function arguments,
-- `_`, are solved by its callback, not by the goal. Checked where the goal
-- is known (`sums`, as a theorem's body), it works today; as a `rewrite`
-- rule, which is elaborated with nothing expected, the callback's `rfl`
-- makes both functions the same unknown (day 12's "`?14 … = ?14 …`").
import Std (Eq, List, Nat)

def count (n: Nat): Nat := match n with
  | Zero => 1
  | Succ k => count k + 1

def listing (n: Nat): List Nat := match n with
  | Zero => [0]
  | Succ k => Cons n (listing k)

theorem countIsLength: (n: Nat) → count n = List.length (listing n)
  | Zero => rfl
  | Succ k => rewrite countIsLength k in rfl

-- Checks today.
theorem sums ∀ (xs: List Nat): List.sumBy xs count = List.sumBy xs (n => List.length (listing n)) :=
  List.sumByCong xs _ _ (n =>
    match n with
      | Zero => rfl
      | Succ k => countIsLength (Succ k))

-- "expected `?4 xs (Succ k) = ?4 xs (Succ k)`, but this has type `count k + 1 = …`".
theorem viaRewrite ∀ (xs: List Nat): List.sumBy xs count + 0 = List.sumBy xs (n => List.length (listing n)) :=
  rewrite List.sumByCong xs _ _ (n =>
        match n with
          | Zero => rfl
          | Succ k => countIsLength (Succ k)) in
    rfl

-- `Eq.trans`'s first argument has a goal with an unknown right side:
-- "`1` and `?8 xs 0` aren't equal".
theorem viaTrans ∀ (xs: List Nat): List.sumBy xs count = List.sumBy xs (n => List.length (listing n)) :=
  Eq.trans
    (List.sumByCong xs _ _ (n =>
      match n with
        | Zero => rfl
        | Succ k => countIsLength (Succ k)))
    rfl
