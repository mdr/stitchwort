-- An unknown function applied to `()` is found from what it's compared
-- with: `f ()` against `double n` gives `f := _ => double n`, since `()`
-- is the only value it can be applied to.
import Std (Nat)

def double (n: Nat): Nat := n + n

theorem atUnit [f: () → Nat] [v: Nat] (h: f () = v): f () = v := h

theorem doubleIsFour (n: Nat) (h: double n = 4): double n = 4 := atUnit h
