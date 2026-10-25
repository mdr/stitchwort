-- expect-error: E-INDEX-STUCK
-- R12 (docs/proposals/map-equality.md §7.6): likewise inside a record.
-- Pairs with `whichPair` in accept/quot-forms.sw.
def AllTrue (x: Bool) (y: Bool): Prop := Unit
def Q: Type := Quot Bool AllTrue

type QN = { q: Q, n: Nat }

type AtR: QN → Type =
  | AtF: AtR { q = Quot.mk False, n = 0 }
  | AtT: AtR { q = Quot.mk True, n = 0 }

def only: AtR { q = Quot.mk False, n = 0 } → Nat
  | AtF => 0
