import Std (Eq, Nat)
type G = { turn: Nat, last: Nat }
def G.begin (first: Nat): G := { turn = 1, last = first }
def G.step (g: G): G := { turn = g.turn + 1, last = g.last }
theorem iterTurn: (count: Nat) → (g: G) → (Nat.iterate count G.step g).turn = g.turn + count
  | Zero, g => omega
  | Succ count, g => rewrite iterTurn count (G.step g) in omega
theorem a ∀ (first later: Nat): 0 = 0 :=
  let final := Nat.iterate later G.step (G.begin first)
  let turns: final.turn = Succ later := Eq.trans (iterTurn later _) (Nat.addComm 1 later)
  rfl
