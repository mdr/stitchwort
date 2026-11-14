-- SW-969 (2), AoC 2021 day 13: `cases` as an argument solves the call's
-- holes before the expected type does.
import Std (Bool, Eq, Nat)

type P = { x: Nat, y: Nat }

def shift (b: Bool) (p: P): P := if b then { p | x = p.x + 1 } else p

theorem holesExt ∀ (b: Bool) (p q: P) (sameX: q.x = (shift b p).x) (sameY: q.y = p.y): q = shift b p :=
  P.ext _ _ cases cases
