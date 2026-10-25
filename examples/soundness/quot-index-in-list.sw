-- expect-error: E-INDEX-STUCK
-- R12 (docs/proposals/map-equality.md §7.6): likewise inside a list. Pairs
-- with `whichPair` in accept/quot-forms.sw.
def AllTrue (x: Bool) (y: Bool): Prop := Unit
def Q: Type := Quot Bool AllTrue

type AtL: List Q → Type =
  | AtF: AtL [Quot.mk False]
  | AtT: AtL [Quot.mk True]

def only: AtL [Quot.mk False] → Nat
  | AtF => 0
