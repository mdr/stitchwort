-- expect-error: E-MUTUAL-SIGNATURE
-- A lemma about a local function needs that function final, so its type
-- can compute. `f` calls its owner, so it isn't final until `cycleTy` is.
def cycleTy (n: Nat): Nat :=
  def f: Nat → Nat
    | Zero => 0
    | Succ k => f k
  theorem fz: f 0 = 35 := rfl
  f n
