-- expect-error: E-REFL
-- `Quot.ind` has no computation rule, so in the kernel `J` on a proof it
-- made is stuck (docs/proposals/map-equality.md §7.4.4, test A6), with no
-- `Quot.sound` anywhere: K proves `p = rfl` but doesn't make them
-- convertible. Running it gives `0` (accept/quot-transport-ind.sw).
def AllTrue (x: Bool) (y: Bool): Prop := Unit
def Q: Type := Quot Bool AllTrue

def p: 0 = 0 := Quot.ind [p := q => 0 = 0] (b => rfl) (Quot.mk False: Q)

def n: Nat := J (y proof => Nat) 0 p

theorem nIsZero: n = 0 := rfl
