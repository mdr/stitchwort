-- A `let` whose value is a call that computes a long list at once, then
-- matches: each branch refines the context the list's call is in. The call
-- doesn't mention what's matched, so it's kept as the call, not written out
-- as its 160,000 elements and evaluated again at every branch: that takes
-- about 1.2 s here, kept 0.2 s (SW-1106, SW-2481).
-- differential: skip (a 160,000-element list is deeper than the recursive reference evaluator can go, SW-2616)
import Std (List, Bool)

def pick (b: Bool) (n: Nat): Nat :=
  let zeros: List Nat := List.replicate 160000 0
  match b with
    | True =>
      match n with
        | Zero => zeros.length
        | Succ m => m
    | False => 0
