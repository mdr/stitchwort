namespace Day

import A (Cat)
import B (Cat)
import Cat (f)

def g: Nat := f

test "the project namespace" := g == 1
