-- SW-3344 review F2: each substitution copies only the hypotheses the goal
-- or a visible hypothesis needs. Copying the hidden originals of earlier
-- copies too doubled the copies with each field: 14.5 s at 12 fields, and
-- this one, at 16, didn't finish in two minutes. Now about 2 s.
import Std (Nat)
type Big =
  | MkBig
      (f1: Nat)
      (f2: Nat)
      (f3: Nat)
      (f4: Nat)
      (f5: Nat)
      (f6: Nat)
      (f7: Nat)
      (f8: Nat)
      (f9: Nat)
      (f10: Nat)
      (f11: Nat)
      (f12: Nat)
      (f13: Nat)
      (f14: Nat)
      (f15: Nat)
      (f16: Nat)
theorem big ∀ (p: Nat → Prop)
    (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16: Nat)
    (h: MkBig x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16
      = MkBig y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16)
    (q1 q2: p (y1 + y2 + y3 + y4 + y5 + y6 + y7 + y8 + y9 + y10 + y11 + y12 + y13 + y14 + y15 + y16 + 0)):
    x1 + x2 + x3 + x4 + x5 + x6 + x7 + x8 + x9 + x10 + x11 + x12 + x13 + x14 + x15 + x16 + 0
      = y1 + y2 + y3 + y4 + y5 + y6 + y7 + y8 + y9 + y10 + y11 + y12 + y13 + y14 + y15 + y16 + 0 :=
  cases
