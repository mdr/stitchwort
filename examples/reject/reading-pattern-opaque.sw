-- expect-error: E-NO-READING
-- An opaque test has no reading: the checker can't look inside `big`, so a
-- fact about it has no parts and `Inl`/`Inr` can't take it apart
-- (docs/proposals/bool-as-proposition.md §5.4, §6.7).
import Std (Bool, Nat)

opaque def big (n: Nat): Bool := n < 10

def t (n: Nat) (h: big n = True): Nat := match h with
  | Inl x => 0
  | Inr y => 1
