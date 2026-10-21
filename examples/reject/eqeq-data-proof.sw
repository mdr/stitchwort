-- expect-error: E-INSTANCE-NONE
-- A proof field is left out of the comparison only if it's an equation in a
-- type with `DecEq` (docs/proposals/interfaces.md §5.11, D179): then any
-- two of its proofs are equal. `same` is an equation between functions,
-- which have none, so `DecEq` isn't derived, and the message says why. An
-- equation in `Bool` is fine: `Small`, in examples/accept/eqeq-proof-fields.sw.
type Shifted =
  | MkShifted (n: Nat) (same: ((x: Nat) => x + n) = ((x: Nat) => n + x))

def same (a: Shifted) (b: Shifted): Bool := a == b
