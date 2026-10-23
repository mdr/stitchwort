-- expect-error: E-REFL
-- A `Map` built by hand whose node stores the wrong size: one entry, size 5.
-- The record's `sized` field (`Map.Tree.Sized`) says each stored size is the
-- number of keys under it, so `Map.size` always counts the entries
-- (docs/proposals/map-equality.md, "Stage 0 results"). Before that field,
-- this map was accepted and its `size` was 5.

import Std (Map)
import Std.Map.Tree (Tip, Bin)

def wrong: Map Nat Text :=
  { tree = Bin 5 Tip 1 "a" Tip
  , ordered = Both (Both Trivial Trivial) (Both Trivial Trivial)
  , sized = Both rfl (Both Trivial Trivial)
  }
