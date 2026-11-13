--| Facts about lists that std doesn't have.

namespace Aoc.Year2024.Day18.Proofs
import Std (Bool, DecEq, List, Nat, Void)

theorem containsCons [auto eq: DecEq a] (x: a) (rest: List a) (wanted: a): [x, ..rest].contains wanted = (x == wanted ∨ rest.contains wanted) := rfl

--| What the first `fewer` hold, the first `more` hold too.
theorem containsTakeMono [auto eq: DecEq a] (wanted: a) (xs: List a) (fewer more: Nat) (le: fewer ≤ more)
    (there: (xs.take fewer).contains wanted = True): (xs.take more).contains wanted = True := match xs, fewer, more with
      | xs, Zero, more => cases
      | [x, ..rest], Succ fewer, Succ more =>
        rewrite containsCons x (rest.take more) wanted in
          rewrite containsCons x (rest.take fewer) wanted at there in
          match same: x == wanted with
            | True => rfl
            | False => containsTakeMono wanted rest fewer more le there
