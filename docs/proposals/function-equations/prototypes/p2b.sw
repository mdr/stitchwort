-- P2b. The same definition with the `match` written as a local definition,
-- so that source can name the helper the compiler would lift it to
-- (`firstBig.step` here, `firstBig.%match1` for a `match`): the generator's
-- proof is one `J` on the hypothesis, with the motive over the scrutinee
-- *and* its equation, which neither `rewrite` nor `match` can choose.
import Std (Bool, Eq, List, Nat, Option, Void)

type Big = { value: Nat, isBig: Nat.leq 10 value = True }

def firstBig: List Nat → Option Big
  | Nil => None
  | Cons x rest =>
    def step: (b: Bool) → Nat.leq 10 x = b → Option Big
      | True, big => Some ({ value = x, isBig = big })
      | False, big => firstBig rest
    step (Nat.leq 10 x) rfl

-- `firstBig.eq2.true`
theorem firstBigEq2True ∀ (x: Nat) (rest: List Nat) (h: Nat.leq 10 x = True):
    firstBig (Cons x rest) = Some ({ value = x, isBig = h }) :=
  J (y e => firstBig (Cons x rest) = firstBig.step x rest y e) rfl h

-- `firstBig.eq2.false`
theorem firstBigEq2False ∀ (x: Nat) (rest: List Nat) (h: Nat.leq 10 x = False):
    firstBig (Cons x rest) = firstBig rest :=
  J (y e => firstBig (Cons x rest) = firstBig.step x rest y e) rfl h
