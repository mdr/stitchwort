-- A cast along a theorem's proof computes on numbers, though the proof is
-- sealed (D3722) and never looked inside: `cast 3 5` takes its base because
-- its ends, `3 + 0` and `3`, are equal (rule K, docs/core.md, "The equality
-- rule"). Refused (E-REFL) before rule K, when `J` needed the proof itself
-- to be `byComputing`.
import Std (Nat)

theorem addZero ∀ (n: Nat): n + 0 = n := byComputing

def cast (n x: Nat): Nat := J (y p => Nat) x (addZero n)

theorem castComputes: cast 3 5 = 5 := byComputing
