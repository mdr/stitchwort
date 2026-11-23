-- expect-error: E-UNFOLDING-THEOREM
-- Every theorem is sealed (D3722): no other declaration sees its proof, so
-- one can't be named in `unfolding`. Only its statement can be used.
import Std (Nat)

theorem addZero ∀ (n: Nat): n + 0 = n := byComputing

def cast (n x: Nat): Nat := J (y p => Nat) x (addZero n)

theorem castComputes: cast 3 5 = 5 unfolding addZero := byComputing
