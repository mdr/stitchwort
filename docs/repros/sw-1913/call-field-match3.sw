-- With record eta, `match` reads a goal holding a field of a call of a
-- definition by well-founded recursion, `(pick n empty).items`, through the
-- call's unfolding: a `match` on the call no longer finds it (`probeCall`),
-- and one on what its body tests rewrites inside the call (`probeTest`),
-- so the goal shows the recursion's internals instead of `pick n empty`.
import Std (Nat)

type Bag = { items: List Nat }

def empty: Bag := { items = [] }

def pick (n: Nat) (bag: Bag): Bag
  decreasing n
:=
  if n ≤ 1 then bag else pick (n / 2) { items = [n, ..bag.items] } [decreasing := omega]

def Fits (bag: Bag): Prop := bag.items.length ≤ 100

theorem probeCall (n: Nat): Fits (pick n empty) :=
  match same: pick n empty with
    | result => ?

theorem probeTest (n: Nat): Fits (pick n empty) :=
  match small: Nat.leq n 1 with
    | True => ?
    | False => ?
