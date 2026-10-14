-- expect-error: E-EXPORT
-- JS can't pass a proof, so an export's preconditions are checked at runtime.
-- Nothing can decide whether two functions are equal, so this can't be.
export
pick : (f : Nat -> Nat) -> [auto same : f = f] -> Nat
pick f = 0
