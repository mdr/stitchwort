-- expect-error: E-WALK
-- A `handle` inside the code: the walk follows binds, calls, splits and
-- values, not handlers, and says so; a lemma about the handling function
-- is the way through it.

import Std (Parse, Option, Nat, Bool, List)

ability Ping where
  ping: () → {Ping} Nat

def answered(): {Parse Nat} Nat :=
  handle Ping.ping() with
    | return x => x
    | ping u, k => k 0

theorem givesAnswered: Parse.Gives Parse.Invariant.any (() => answered()) (n => n = 0) :=
  byWalking []
