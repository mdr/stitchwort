-- expect-error: E-REFL
-- A failed proof that mentions a `Map` shows the map as the `Map.fromList`
-- it was built from, in key order, not as the quotient's raw search tree
-- (SW-3432). Past eight entries the list is elided.
import Std (Map, Nat)

def table: Map Nat Nat :=
  Map.fromList [(1, 2), (2, 4), (3, 6), (4, 8), (5, 10), (6, 12), (7, 14), (8, 16), (9, 18), (10, 20)]

theorem wrong: table
      = Map.fromList [(1, 2), (2, 4), (3, 6), (4, 8), (5, 10), (6, 12), (7, 14), (8, 16), (9, 18), (10, 21)] :=
  byComputing
