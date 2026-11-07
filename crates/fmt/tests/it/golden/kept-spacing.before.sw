-- Spacing that changes meaning is copied (§2.3).
def main(): {IO} () := IO.print "hi"
def unit: () := id ()
def field (p: Point): Nat := p.x+p.y
def section: List Nat := [1, 2] |> .map (x => x)
def neg (x: Int): Int := -x - - x
theorem back (h: a = b): b = a := rewrite <- h in rfl
@[js.name  "q"]
def q: Nat := 1
def interp (n: Nat): Text := "n is ${ n }, ${n}"
