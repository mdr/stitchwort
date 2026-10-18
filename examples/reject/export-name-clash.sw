-- expect-error: E-EXPORT
-- Both would be exported to JavaScript as `area`.
export def Squares.area (s : Nat) : Nat := s * s

export def Circles.area (r : Nat) : Nat := 3 * r * r
