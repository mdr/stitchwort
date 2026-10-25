-- expect-error: E-PARTIAL-CALLBACK
-- Stage 1: std's `List.map` can't take a partial callback, even though its
-- row is polymorphic, so the fix is a hand-written `Partial` helper, not a
-- change to std (docs/proposals/partial.md §7.3, partial-stage-2.md G3).
import Std.Effect (Effects)
import Std (List, Nat)

def children (n: Nat): List Nat := if n > 3 then [] else [n + 1, n + 2]

def countNodes (n: Nat): {Partial} Nat := 1 + List.sum (List.map countNodes (children n))
