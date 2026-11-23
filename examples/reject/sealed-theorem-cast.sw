-- expect-error: E-REFL
-- A cast along a theorem's proof doesn't compute, even on numbers: the proof
-- is sealed (D3722), so `addZero 3` stays a call where `J` needs `byComputing`.
-- The note says so, and doesn't suggest `unfolding addZero`, which is refused.
import Std (Nat)

theorem addZero ∀ (n: Nat): n + 0 = n := byComputing

def cast (n x: Nat): Nat := J (y p => Nat) x (addZero n)

theorem castComputes: cast 3 5 = 5 := byComputing
