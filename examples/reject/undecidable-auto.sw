-- expect-error: E-AUTO-NONE
-- Nothing decides a statement about every `Nat`, so `auto` can't find a
-- proof. (`Void` is decided: it is false, `E-AUTO-FALSE`.)
def impossible: [auto ok: (n: Nat) -> n = 0] -> Nat := 0

def use: Nat := impossible
