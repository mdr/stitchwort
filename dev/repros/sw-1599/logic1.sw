import Std (List, Nat, Bool)

type Box = { n: Nat, big: Bool }

def Box.small (b: Box): Bool := b.n < 3

def g1 (bs: List Box): List Box :=
  let p := b => b.small && b.big
  bs.filter p

def g2 (bs: List Box): Nat := bs.foldLeft 0 (acc b => if b.small && !b.big then acc + 1 else acc)

def g3 (bs: List Box): Bool := bs.all (b => b.small || b.big)
