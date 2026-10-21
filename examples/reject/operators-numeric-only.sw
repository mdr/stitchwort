-- expect-error: E-TYPE-MISMATCH
-- `-` is only for `Nat` and `Int`: there's no interface for subtraction, so
-- an expression with one is on numbers whatever else it has.
type Point = { x: Int, y: Int }

def diff (p: Point) (q: Point): Point := p + q - p
