-- `Quot.ind` has no computation rule, so the proof it makes here is never
-- `byComputing` (docs/proposals/map-equality.md §7.4.4, test A6). The cast
-- along it computes all the same, in the checker as when running
-- (accept/quot-transport-ind.sw): its ends, `0` and `0`, are equal (rule K,
-- docs/core.md, "The equality rule"). Refused (E-REFL) before rule K.
def AllTrue (x y: Bool): Prop := Unit
def Q: Type := Quot Bool AllTrue

def p: 0 = 0 := Quot.ind [p := q => 0 = 0] (b => byComputing) (Quot.mk False: Q)

def n: Nat := J (y proof => Nat) 0 p

theorem nIsZero: n = 0 := byComputing
