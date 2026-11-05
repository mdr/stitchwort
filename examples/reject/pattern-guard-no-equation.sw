-- expect-error: E-NO-EQUATION
-- Generated equations stop at the first arm with a condition: `f.eq1` is
-- there and unchanged, `f.eq2` says why it isn't (stage 2 will add it).

def f: Nat → Nat
  | 0 => 5
  | n if n > 3 => n
  | _ => 1

theorem eq1Holds: f 0 = 5 := f.eq1

theorem eq2Missing (n: Nat): f (Succ n) = 7 := f.eq2

-- A guarded alternative of a `match` that is an arm's right side: the arm has
-- its equation, the alternatives below it don't.
def g: Nat → List Nat → Nat
  | 0, _ => 0
  | Succ k, xs =>
    match xs with
      | [x, .._] if x > k => x
      | _ => k

theorem g1: g 0 [] = 0 := g.eq1 []
theorem g2NoCons: g 1 [] = 0 := g.eq2.cons
