-- expect-error: E-PARTIAL
-- Draft 1's `drain` (docs/proposals/partial.md §2), with a partial loop:
-- a total function that runs a computation to its end, recursing on what's
-- left of it, would turn an endless one into a proof of anything. A total
-- function can't run a partial computation at all, so there's nothing to
-- drain: here the "drain" is refused where it runs `forever ()`, and there
-- is no other way into a `Delay` (it isn't a data type, so there's no
-- `case` on one, and no eliminator).
import Effect (Delay)

type Empty : Type

def forever () : {Partial} Empty := forever ()

def drain (prog : () -> {Partial} Empty) : Empty := prog ()

theorem contradiction : Void := emptyVoid (drain forever)

def emptyVoid : Empty -> Void
  | ()
