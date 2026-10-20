-- Uses both instances without importing them: an instance is found by its
-- type, in the module that owns the interface or the type, which this one
-- depends on anyway. A different area for `Nat` is a named alternative,
-- passed by name.
namespace Report

import Shapes (Shape)
import Geometry (Area)

def total (shapes: List Shape): Nat := shapes.foldLeft (n s => n + Area.area s) 0

def linear: Area Nat := { area = n => n }

test "shapes" := total [Square 2, Rect 2 3] == 10
test "nat" := Area.area 5 == 25
test "named" := Area.area [area := linear] 5 == 5
