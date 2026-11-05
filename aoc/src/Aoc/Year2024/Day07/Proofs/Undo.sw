--| Undoing a multiplication or a concatenation: the remainder and quotient
--| the program checks.

namespace Aoc.Year2024.Day07.Proofs
import Aoc.Year2024.Day07 (..)
import Aoc.Year2024.Day07.Spec (..)
import Std (Bool, DecEq, Eq, Nat, Void)

--| `v * d + r` is `target`, for a remainder `r < d`, exactly when `target`
--| leaves remainder `r` and quotient `v`.
theorem divModMatch (d: Nat) [auto ok: d ≠ 0] (r: Nat) (small: r < d) (v: Nat) (target: Nat):
    (v * d + r == target) = (target % d == r && v == target / d) :=
  Bool.eqOf (v * d + r == target) (target % d == r && v == target / d)
    (matches =>
      let same := DecEq.sound matches
      rewrite Nat.modUnique target d v r small (Eq.sym same), Nat.divUnique target d v r small (Eq.sym same)
        in Bool.andIntro (DecEq.refl r) (DecEq.refl v))
    (both =>
      let remainder := DecEq.sound (Bool.andLeft both)
      let quotient := DecEq.sound (Bool.andRight both)
      rewrite quotient, <- remainder, <- Nat.divModEq target d ok in DecEq.refl target)
