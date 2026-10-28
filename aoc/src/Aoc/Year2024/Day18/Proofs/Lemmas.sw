-- Facts about lists that std doesn't have.

namespace Aoc.Year2024.Day18.Proofs
import Std (Bool, DecEq, List, Nat, Void)

theorem containsCons [auto eq: DecEq a] (x: a) (rest: List a) (wanted: a): (Cons x rest).contains wanted = (x == wanted ∨ rest.contains wanted) := rfl

-- What the first `fewer` hold, the first `more` hold too.
theorem containsTakeMono [auto eq: DecEq a] (wanted: a): (xs: List a) → (fewer: Nat) → (more: Nat) → fewer ≤ more →
    (xs.take fewer).contains wanted = True → (xs.take more).contains wanted = True
  | xs, Zero, more, le, there => Void.exfalso (Bool.falseNotTrue there)
  | Nil, Succ fewer, more, le, there => Void.exfalso (Bool.falseNotTrue there)
  | Cons x rest, Succ fewer, Zero, le, there => Void.exfalso (Bool.falseNotTrue le)
  | Cons x rest, Succ fewer, Succ more, le, there =>
    rewrite containsCons x (rest.take more) wanted in
      rewrite containsCons x (rest.take fewer) wanted at there in
      match same: x == wanted with
        | True => rfl
        | False => containsTakeMono wanted rest fewer more le there
