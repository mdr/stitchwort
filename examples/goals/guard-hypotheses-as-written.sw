-- In an arm under a guard that refines the goal, a hypothesis and the goal
-- show as written with the condition replaced (`0 < pick True`, `0 < 1`),
-- not as what they compute to (`True = True`).
import Std (Bool, Char, Nat)

def pick (b: Bool): Nat := if b then 1 else 0

theorem character ∀ (n: Nat) (c: Char) (h: 0 < pick (c == 'a')): pick (c == 'a') = 1 ∨ 0 < 1 := match n with
  | 0 if g: c == 'a' => ?
  | _ => ?

theorem variable ∀ (n: Nat) (b: Bool) (h: 0 < pick b) (h2: pick b = 1): pick b = 1 := match n with
  | 0 if g: b => ?
  | _ => ?
