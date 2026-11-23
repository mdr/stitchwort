-- Accepted today: `same0`. Refused today (E-REFL), predicted to check once
-- comparison skips proofs everywhere (stage 5, rule I): `sameCall`. Both
-- sides are stuck calls of `pick`, compared argument by argument in the
-- shortcut mode, which compares constructors' proof fields (D2352); the
-- sealed `selfEq 0` is not `byComputing` there. SW-4661 found this behind
-- `PrefixSums.atOf`'s rewrite (not only rewrite's search).
import Std (List, Nat)

type Checked: Type = | MkChecked (n: Nat) (ok: n = n)

theorem selfEq ∀ (n: Nat): n = n := byComputing

def mk (n: Nat): Checked := MkChecked n (selfEq n)

def zero: Checked := MkChecked 0 byComputing

def pick (d: Checked): List Checked → Checked
  | [] => d
  | [x, ..rest] => x

theorem same0: mk 0 = zero := byComputing

theorem sameCall ∀ (xs: List Checked): pick (mk 0) xs = pick zero xs := byComputing
