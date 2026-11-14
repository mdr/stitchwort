-- P2. A named (dependent) `match` on a `Bool` in a definition, whose arm
-- uses the equation: stepping through it by hand, and the generator's
-- proof by one `J`.
import Std (Bool, Eq, List, Nat, Option, Void)

type Big = { value: Nat, isBig: Nat.leq 10 value = True }

def firstBig: List Nat → Option Big
  | Nil => None
  | Cons x rest =>
    match big: Nat.leq 10 x with
      | True => Some ({ value = x, isBig = big })
      | False => firstBig rest

-- By hand, as an agent would try: rewrite with the condition.
theorem byRewrite ∀ (x: Nat) (rest: List Nat)
    (h: Nat.leq 10 x = True):
    firstBig (Cons x rest) = Some ({ value = x, isBig = h }) :=
  rewrite h in rfl

theorem byMatch ∀ (x: Nat) (rest: List Nat)
    (h: Nat.leq 10 x = True):
    firstBig (Cons x rest) = Some ({ value = x, isBig = h }) :=
  match e: Nat.leq 10 x with
    | True => rfl
    | False => Void.exfalso (Bool.falseNotTrue (Eq.trans (Eq.sym e) h))

theorem byCases ∀ (x: Nat) (rest: List Nat)
    (h: Nat.leq 10 x = True):
    firstBig (Cons x rest) = Some ({ value = x, isBig = h }) :=
  cases
