-- expect-error: E-NO-EQUATION
-- Generated equations stop at the first arm with a condition: `f.eq1` is
-- there and unchanged, `f.eq2` says why it isn't (stage 2 will add it).

def f: Nat → Nat
  | 0 => 5
  | n if n > 3 => n
  | _ => 1

theorem eq1Holds: f 0 = 5 := f.eq1

theorem eq2Missing (n: Nat): f (Succ n) = 7 := f.eq2
