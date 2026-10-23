-- Quotients (docs/proposals/map-equality.md §7): the accepted programs
-- nearest the rejected ones in soundness/quot-*.sw, which say which they
-- pair with. The canonical example is the quotient of `Bool` by the
-- relation that relates everything, which identifies `False` and `True`.
def AllTrue (x: Bool) (y: Bool): Prop := Unit
def Q: Type := Quot Bool AllTrue

-- Related values are equal by `Quot.sound` (soundness/quot-related-not-convertible.sw).
theorem same: (Quot.mk False: Q) = Quot.mk True := Quot.sound Trivial

-- A function that respects the relation lifts (soundness/quot-lift-projection.sw).
def constFalse (q: Q): Bool := Quot.lift (b => False) (x y related => rfl) q

-- `Quot.ind` proves propositions about every quotient (soundness/quot-ind-into-data.sw).
theorem allSame (q: Q): q = Quot.mk False :=
  Quot.ind [p := q => q = Quot.mk False] (x => Quot.sound Trivial) q

-- A stuck `Quot.ind` is equal to itself (soundness/quot-ind-computes.sw).
theorem indItself (q: Q):
    Quot.ind [p := q => Unit] (b => Trivial) q = Quot.ind [p := q => Unit] (b => Trivial) q :=
  rfl

-- The identity respects equality, so it lifts on the quotient by equality
-- (soundness/quot-relation-mismatch.sw).
def BoolEq (x: Bool) (y: Bool): Prop := x = y
def unwrapEq (q: Quot Bool BoolEq): Bool := Quot.lift (b => b) (x y h => h) q

-- Carriers are types: the universe `Prop` (whose elements are
-- propositions) and `Type` are (soundness/quot-of-proposition.sw).
def QProp: Type := Quot Prop (a b => Unit)
def QType: Type 1 := Quot Type (a b => a = b)

-- Matching on a quotient index that's a variable solves it
-- (soundness/quot-index-decompose.sw).
type At: Q -> Type =
  | AtF: At (Quot.mk False)
  | AtT: At (Quot.mk True)

def which (q: Q) (a: At q): Bool :=
  match a with
    | AtF => False
    | AtT => True

-- Likewise inside a pair (soundness/quot-index-in-pair.sw, -in-list.sw,
-- -in-record.sw).
type AtP: (Q, Nat) -> Type =
  | PF: AtP (Quot.mk False, 0)
  | PT: AtP (Quot.mk True, 1)

def whichPair (q: Q) (a: AtP (q, 0)): Bool :=
  match a with
    | PF => False

-- A quotient field that doesn't mention the type being defined
-- (soundness/quot-recursive-relation.sw).
type T: Type =
  | Node (kids: Quot Nat (x y => Unit))
