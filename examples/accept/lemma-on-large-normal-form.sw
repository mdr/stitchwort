-- A std lemma applied to a predicate whose normal form is huge. `grow 30`
-- takes 30 steps to compute but written out has 2^30 nodes, so whatever
-- reads the lemma's type back for its `Ord` dictionary keeps `keep x` as
-- a call.
import Std (Bool, Eq, Nat, Set)

type Tree =
  | Leaf (n: Nat)
  | Node (left: Tree) (right: Tree)

def grow: Nat → Tree → Tree
  | Zero, tree => tree
  | Succ n, tree => grow n (Node tree tree)

def startsAt: Nat → Tree → Bool
  | Zero, _ => False
  | Succ _, Leaf _ => True
  | Succ _, Node _ _ => False

def keep (x: Nat) (k: Nat): Bool := startsAt k (grow 30 (Leaf x))

theorem applied (x: Nat) (s: Set Nat) (key: Nat):
    Set.contains (s.filter (keep x)) key = (Set.contains s key && keep x key) :=
  Set.containsFilter s key (keep x)
