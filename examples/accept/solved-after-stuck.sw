-- A call stuck on an unknown that a part compared earlier solves (SW-1315).
-- `lem`'s statement at the unknown `?b` has `pick ?b 5`, stuck on `?b`;
-- the first conjunct solves `?b` with `True`, and the second compares the
-- stuck call with `5`. The call is evaluated again then, with `?b`'s
-- solution in, and computes to `5`. A stuck call only reads back with the
-- solution in: left stuck, it printed as `pick True 5` and didn't unify
-- with `5`, and the dictionary case below failed on two sides that print
-- alike, `x + x`.
import Std (Bool, Int, Nat)

def pick (b: Bool): Nat → Nat := match b with
  | True => n => n
  | False => n => 0

theorem lem [b: Bool]: b = b ∧ pick b 5 = pick b 5 := Both rfl rfl

theorem picked: True = True ∧ pick True 5 = 5 := lem

-- The same with a dictionary the first conjunct solves: `d.add x x` at
-- the unknown `?d` is `Add.add` stuck on `?d` until evaluated again with
-- `Int.instAdd` for `?d`.
theorem addVia [d: Add a] (x: a): d = d ∧ d.add x x = d.add x x := Both rfl rfl

theorem addInt (x: Int): Int.instAdd = Int.instAdd ∧ Int.add x x = x + x := addVia x
