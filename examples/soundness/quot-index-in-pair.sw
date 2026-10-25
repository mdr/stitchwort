-- expect-error: E-INDEX-STUCK
-- R12 (docs/proposals/map-equality.md §7.6): a quotient index inside a pair
-- is split at the pair, as usual, and the equation between the quotients
-- that leaves is stuck, so the whole problem is, never decided. Pairs with
-- `whichPair` in accept/quot-forms.sw.
def AllTrue (x: Bool) (y: Bool): Prop := Unit
def Q: Type := Quot Bool AllTrue

type AtP: (Q, Nat) → Type =
  | AtF: AtP (Quot.mk False, 0)
  | AtT: AtP (Quot.mk True, 0)

def only: AtP (Quot.mk False, 0) → Nat
  | AtF => 0
