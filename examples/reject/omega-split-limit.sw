-- expect-error: E-OMEGA
-- Four disjunctions need 15 splits to cover all 16 cases, more than
-- `omega` makes; the message says so.
import Std (Nat)

theorem tooMany (a: Nat) (b: Nat) (c: Nat) (d: Nat)
    (ha: (a == 0 || a == 1) = True) (hb: (b == 0 || b == 1) = True)
    (hc: (c == 0 || c == 1) = True) (hd: (d == 0 || d == 1) = True): a + b + c + d <= 4 := omega
