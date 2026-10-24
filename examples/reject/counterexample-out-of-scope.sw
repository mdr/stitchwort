-- expect-error: E-REFL
-- Out of scope for the search: a function parameter, and a hypothesis
-- nothing decides. No note, and no other error (acceptance test 8).
import Std (List)

theorem mapKeeps (f: Nat -> Nat) (xs: List Nat): List.map f xs = xs := rfl

theorem bounded (n: Nat) (h: (k: Nat) -> k <= n): n = 1 := rfl
