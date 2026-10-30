-- expect-error: E-TERMINATION
-- CVE-2026-72705's result was `T` definitionally equal to `T → False`.
-- The same through a recursive function that receives the recursive one:
-- `outer 0` would be `outer 1 → Void`, and so on. Neighbour: `inner`
-- itself, a type computed by structural recursion, is accepted; only
-- `outer` is refused.
def outer (n: Nat): Prop := inner (x => outer x) n

def inner (k: Nat → Prop): Nat → Prop
  | Zero => k (Succ Zero) → Void
  | Succ m => inner k m
