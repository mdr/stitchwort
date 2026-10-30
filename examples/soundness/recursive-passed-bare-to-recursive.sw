-- expect-error: E-TERMINATION
-- CVE-2026-72705 with the function passed bare, as in the advisory: a
-- member must be given all its arguments wherever it's used, so `outer`
-- alone is refused before size change. Neighbour: `walk`/`stepBy` in
-- accept/mutual.sw.
def outer (n: Nat): Void := inner outer n

def inner (k: Nat → Void): Nat → Void
  | Zero => k (Succ Zero)
  | Succ m => inner k m
