-- A `Bool` test being `True` is shown as the test alone, as it can be
-- written (docs/proposals/bool-as-proposition.md §4.4): `h1: a`,
-- `h3: xs.any (…)`, `h5: ¬a`, `h6: a ∧ b`. It keeps its `= True` where the
-- bare text would read back as another proposition: under `&&` and `||`
-- (`h2`), and as a side of `=` (`h7`). `= False` is shown as written (`h4`).
import Std (Bool, Nat, List)

theorem shown ∀ (a b: Bool) (n: Nat) (xs: List Nat)
    (h1: a = True)
    (h2: (a && b) = True)
    (h3: xs.any (x => x <= n) = True)
    (h4: a = False)
    (h5: Not (a = True))
    (h6: And (a = True) (b = True))
    (h7: (a = True) = (b = True)):
    b = True :=
  ?
