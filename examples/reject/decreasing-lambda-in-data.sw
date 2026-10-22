-- expect-error: E-DECREASING
-- A recursive call inside a function kept in a list: equal lists would need
-- equal functions, which is function extensionality.
import Std (List, Nat)

def stored (n: Nat): Nat
  decreasing n
:=
  List.sum (List.map ((g: Nat -> Nat) => g (n - 1)) [d => if h: d < n then stored d else 0])
