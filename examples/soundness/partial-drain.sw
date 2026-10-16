-- expect-error: E-PARTIAL
-- Draft 1's `drain` (docs/proposals/partial.md §2), with a partial loop:
-- a total function that runs a computation to its end, recursing on what's
-- left of it, would turn an endless one into a proof of anything. A total
-- function can't run a partial computation at all, so there's nothing to
-- drain: here the "drain" is refused where it runs `forever ()`, and there
-- is no other way into a `Delay` (it isn't a data type, so there's no
-- `case` on one, and no eliminator).
type Empty : Type

forever : () -> {Partial} Empty
forever u = forever ()

drain : (() -> {Partial} Empty) -> Empty
drain prog = prog ()

theorem contradiction : Void
contradiction = emptyVoid (drain forever)

emptyVoid : Empty -> Void
emptyVoid ()
