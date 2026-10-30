-- expect-error: E-TERMINATION
-- Rocq CVE-2026-72705 (docs/research/kernel.md C26): a recursive function
-- passed to another recursive function, which applies it to something that
-- isn't smaller (`k 1`). Rocq refused this when the receiver was a plain
-- definition but not when it was a fixpoint. Here `inner` is recursive, and
-- `x` is lambda-bound, so unknown: `outer 0` would loop. Neighbour:
-- `walk`/`stepBy` in accept/mutual.sw.
def outer (n: Nat): Void := inner (x => outer x) n

def inner (k: Nat → Void): Nat → Void
  | Zero => k (Succ Zero)
  | Succ m => inner k m
