-- expect-error: E-AUTO-NONE
-- Nothing decides `Void` (it's never true), so `auto` can't find a proof.
def impossible : [auto ok : Void] -> Nat := 0

def use : Nat := impossible
