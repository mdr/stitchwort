-- A case with a condition is an `if` to a proof. Its equation takes the
-- condition as a hypothesis, and the cases below it take that it failed.
-- A decided condition is stated as a proposition: `n != 3` gives `n ≠ 3`.
def skipThree: Nat → Nat
  | n if n != 3 => n
  | _ => 0

theorem skipThreeKeeps (n: Nat) (other: n ≠ 3): skipThree n = n := skipThree.eq1 n other

theorem skipThreeDrops: skipThree 3 = 0 := skipThree.eq2 3 rfl

-- `match induct` splits at the condition: `eq2` knows `x > 3`, and `eq3`
-- knows it failed.
def countBig: List Nat → Nat
  | [] => 0
  | [x, ..rest] if x > 3 => 1 + countBig rest
  | [_, ..rest] => countBig rest

theorem countBigAtMost (xs: List Nat): countBig xs ≤ xs.length := match induct (countBig xs) with
  | eq1 => omega
  | eq2 x rest big ih => omega
  | eq3 x rest small ih => omega
