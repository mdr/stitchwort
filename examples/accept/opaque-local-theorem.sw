-- A local theorem inside a body with `unfolding` is sealed like any theorem:
-- the body that holds it unfolds `two`, as its clause says, but not the
-- local theorem's proof, which it uses by its statement (D3722).
import Std (Nat, Eq)

opaque def two: Nat := 2

theorem twoPlus ∀ (n: Nat): two + n = n + 2 unfolding two :=
  theorem base: two = 2 := byComputing
  rewrite base then arithmetic
