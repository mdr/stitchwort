-- expect-error: E-NAMED-BRACKET
-- Round brackets name an explicit parameter and square ones an implicit
-- parameter, as in declarations; the wrong one says which to write (D1093).

def pick [count: Nat] (x: Nat): Nat := x + count

def roundForImplicit: Nat := pick (count := 2) 1
def squareForExplicit: Nat := pick [x := 1]
