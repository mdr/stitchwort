-- expect-error: E-TERMINATION
-- Matching on a computed value hides that `m` is a part of `k`: the patterns
-- take apart `k + 0`, not `k`, so the recursive call isn't seen as smaller.
-- The message says so, and suggests matching `k` itself.
def count (k: Nat): Nat :=
  match k + 0 with
    | Zero => Zero
    | Succ m => count m
