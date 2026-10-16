-- expect-error: E-EXPORT
-- Both would be exported to JavaScript as `area`.
export
Squares.area : Nat -> Nat
Squares.area s = s * s

export
Circles.area : Nat -> Nat
Circles.area r = 3 * r * r
