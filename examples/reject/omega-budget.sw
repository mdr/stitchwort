-- expect-error: E-OMEGA
-- Ten dense constraints over eight unknowns use up the search budget.
import Std (Nat)

theorem dense (a: Nat) (b: Nat) (c: Nat) (d: Nat) (e: Nat) (f: Nat) (g: Nat) (h: Nat)
    (h1: 3 * a + 5 * b <= 7 * c + 2 * d + 11) (h2: 5 * c + 3 * d <= 7 * e + 2 * f + 13)
    (h3: 7 * e + 2 * f <= 3 * g + 5 * h + 17) (h4: 2 * g + 7 * h <= 5 * a + 3 * b + 19)
    (h5: 11 * a + 2 * c <= 3 * e + 5 * g + 23) (h6: 13 * b + 3 * d <= 2 * f + 7 * h + 29)
    (h7: 2 * a + 3 * c + 5 * e + 7 * g <= 31 + b + d + f + h) (h8: 3 * b + 5 * d + 7 * f + 11 * h <= 37 + a + c + e + g)
    (h9: 17 * a + 19 * h <= 23 * c + 29 * f + 41) (h10: 13 * d + 11 * e <= 7 * b + 5 * g + 43):
    a + b + c + d + e + f + g + h <= 500 := omega
