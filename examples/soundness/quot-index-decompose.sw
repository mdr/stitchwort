-- expect-error: E-INDEX-STUCK
-- R3 (docs/proposals/map-equality.md §7.6): `Quot.mk` isn't a constructor,
-- so index unification never splits `Quot.mk True = Quot.mk False` into
-- `True = False`, nor calls it impossible: it's stuck. Covering only `AtF`
-- would treat the quotient's representatives as told apart, and they're
-- equal (`Quot.sound Trivial`). Pairs with `which` in accept/quot-forms.sw,
-- where the index is a variable, which matching solves.
def AllTrue (x: Bool) (y: Bool): Prop := Unit
def Q: Type := Quot Bool AllTrue

type At: Q -> Type =
  | AtF: At (Quot.mk False)
  | AtT: At (Quot.mk True)

def only: At (Quot.mk False) -> Nat
  | AtF => 0
