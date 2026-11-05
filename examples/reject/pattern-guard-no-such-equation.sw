-- expect-error: E-UNKNOWN-NAME
-- Equations of guarded arms are numbered by arm, as any others are: a guard
-- doesn't add one, so `clamp` has two.

def clamp (limit: Nat): Nat → Nat
  | n if n <= limit => n
  | _ => limit

theorem noThird: clamp 1 2 = 1 := clamp.eq3
