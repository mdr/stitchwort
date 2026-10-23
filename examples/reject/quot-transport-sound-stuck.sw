-- expect-error: E-REFL
-- In the kernel, `J` on `Quot.sound` is stuck (docs/proposals/map-equality.md
-- §9.1, test A3): `n` is a closed `Nat` in normal form that isn't a numeral.
-- Running it gives `0` (accept/quot-transport-sound.sw).
def AllTrue (x: Bool) (y: Bool): Prop := Unit
def Q: Type := Quot Bool AllTrue

theorem same: (Quot.mk False: Q) = Quot.mk True := Quot.sound Trivial

def n: Nat := J (y p => Nat) 0 same

theorem nIsZero: n = 0 := rfl
