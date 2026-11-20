-- An implicit thunk fixed only by an explicit argument's type: `Holds (()
-- => half 4)` against `Holds ?f`. Unfolded, `Fail.toOption (() => half 4)`
-- computes to `Some 2` while `Fail.toOption ?f` is stuck on `?f ()`, so
-- comparing the unfoldings can't solve `?f`. Once that comparison has
-- failed, the calls' arguments solve it: a thunk facing `() => …` is
-- solved like an unknown facing data, as `Parse.Follows ?same ?alike ?p
-- ?q` against two parsers written `() => …` needs (SW-4323). An unknown
-- facing any other lambda waits for a data unknown beside it (SW-4316).
import Std (Fail)

def half (n: Nat): {Fail} Nat := if n % 2 == 0 then n / 2 else Fail.fail "odd"

def Holds (f: () → {Fail} Nat): Prop := Fail.toOption f = Fail.toOption f

theorem useHolds ∀ [f: () → {Fail} Nat] (h: Holds f): 1 = 1 := byComputing

theorem halfHolds ∀ (h: Holds (() => half 4)): 1 = 1 := useHolds h
