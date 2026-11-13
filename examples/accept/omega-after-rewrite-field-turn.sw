-- `omega` after a `rewrite`, where the goal's `1 + later` comes from a
-- record field whose type was an unknown when the goal was written.

import Std (Eq, Nat)

type G = { turn: Nat, last: Nat }

def G.begin (first: Nat): G := { turn = 1, last = first }

def G.step (g: G): G := { turn = g.turn + 1, last = g.last }

theorem iterTurn ∀ (count: Nat) (g: G): (Nat.iterate count G.step g).turn = g.turn + count := match count with
  | Zero => omega
  | Succ count => rewrite iterTurn count (G.step g) in omega

theorem finalTurn ∀ (first: Nat) (later: Nat): (Nat.iterate later G.step (G.begin first)).turn = Succ later :=
  let final := Nat.iterate later G.step (G.begin first)
  let turns: final.turn = Succ later := rewrite iterTurn later _ in omega
  turns
