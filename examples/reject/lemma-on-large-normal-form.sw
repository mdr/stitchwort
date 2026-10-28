-- expect-error: E-TYPE-MISMATCH
-- A std lemma applied to the wrong predicate, one whose normal form is huge
-- (`grow 30` written out has 2^30 nodes): a type mismatch showing the calls,
-- not running out of resources.
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

theorem misapplied (x: Nat) (s: Set Nat) (key: Nat):
    Set.contains (s.filter (keep x)) key = (Set.contains s key && keep (x + 1) key) :=
  Set.containsFilter s key (keep x)
