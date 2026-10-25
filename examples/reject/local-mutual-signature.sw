-- expect-error: E-MUTUAL-SIGNATURE
-- A local lemma about a local definition that calls its owner: `a` isn't
-- finished until `f` is, so `b`'s type can't mention it. State it as a
-- top-level theorem about `f.a` instead.

def f (n: Nat): Nat :=
  def a: Nat → Nat
    | Zero => 0
    | Succ k => f k
  theorem b (k: Nat): a k = a k := rfl
  n
