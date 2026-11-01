-- expect-error: E-DUPLICATE
-- `Kind.eq2` is the name of `Kind`'s second arm's generated equation
-- (D2176), so a declaration can't take it.
import Std (Nat)

def Kind: Nat → Nat
  | 3 => 1
  | _ => 0

theorem Kind.eq2: Kind 4 = 0 := rfl
