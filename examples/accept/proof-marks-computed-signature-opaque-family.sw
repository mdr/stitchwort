-- The parameters of `f`, whose type is written through opaque definitions,
-- have their proof marks checked off the type computed under `f`'s own
-- transparency set (SW-4802): the written binder `fam: Fam` is bound as the
-- kernel bound it, with `Fam` unfolded, so the computed domain `fam 0` is
-- read as an application of a function.
import Std (Nat)

opaque def Fam: Type 1 := Nat → Type

opaque def R (fam: Fam): Type unfolding Fam := fam 0 → Nat

opaque def f: (fam: Fam) → R fam unfolding R, Fam := fam x => 0
