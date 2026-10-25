-- `Std.Omega` used by hand: the quoted facts and goal, and the certificate, that
-- the future `omega` keyword (docs/proposals/omega.md, milestone 1b) will write
-- for us. `Omega.prove` takes the atoms' values (`MkEnv`), the quoted facts and
-- goal, a certificate, `rfl` (the kernel runs `Omega.check` on them to show it
-- accepts), and the proofs of the facts. The quoted syntax mirrors the
-- statement's shape exactly: `(a + b) + c` is `NAdd (NAdd a b) c`, `x + 1` is
-- `NAdd x (NLit 1)`, `3 * x` is `MulLeft 3 x`, `x * 3` is `MulRight x 3`.
--
-- Every row means `0 <= c + Σ a_i * x_i`. A step adds one row to the
-- certificate's context (which starts empty): `Input i` copies fact row `i`,
-- `NegGoal` the goal's negation, `NatNonneg i` says `x_i >= 0`, `Combine`
-- adds multiples of earlier rows, `Divide r d` divides row `r` by `d` (rounding
-- the constant down), `Split l a b` tries `l >= 0` in `a` and its opposite in
-- `b`, and `Close r` ends a branch at a row `0 <= negative`.

import Std (Omega, Nat, Bool)
import Std.Omega.Env (MkEnv)
import Std.Omega.NTerm (NV, NLit, NAdd, NSucc, MulLeft, MulRight)
import Std.Omega.Fact (FLe, FLt, FEq, FNotLe, FNotLt)
import Std.Omega.Goal (GLe, GLt, GVoid)
import Std.Omega.Row (MkRow)
import Std.Omega.Step (Input, NegGoal, NatNonneg, Combine, Divide)
import Std.Omega.Cert (Close, Then, Split)

-- Day 5 `absorbStacked`, the stacked arm.
theorem stacked (id: Nat) (lastTo: Nat) (rFrom: Nat) (h1: id ≤ lastTo) (h2: lastTo + 1 ≤ rFrom): id < rFrom :=
  Omega.prove (MkEnv [id, lastTo, rFrom] []) [FLe (NV 0) (NV 1), FLe (NAdd (NV 1) (NLit 1)) (NV 2)] (GLt (NV 0) (NV 2))
    (Then (Input 0) (Then (Input 1) (Then NegGoal (Then (Combine [MkPair 1 0, MkPair 1 1, MkPair 1 2]) (Close 3)))))
    rfl (Both h1 (Both h2 Trivial))

-- Day 5 `absorbStacked`, True arm: hypotheses as Bool equations, through the bridge lemmas.
theorem absorbTrue (lastFrom: Nat) (id: Nat) (lastTo: Nat) (rFrom: Nat) (i: (Nat.leq lastFrom id ∧ Nat.leq id lastTo) = True)
    (e: Nat.leq rFrom (lastTo + 1) = False): id < rFrom :=
  Omega.prove (MkEnv [lastFrom, id, lastTo, rFrom] []) [FLe (NV 1) (NV 2), FLt (NAdd (NV 2) (NLit 1)) (NV 3)] (GLt (NV 1) (NV 3))
    (Then (Input 0) (Then (Input 1) (Then NegGoal (Then (Combine [MkPair 1 0, MkPair 1 1, MkPair 1 2]) (Close 3)))))
    rfl (Both (Bool.andRight (Nat.leq lastFrom id) (Nat.leq id lastTo) i) (Both (Nat.leqFalse rFrom (lastTo + 1) e) Trivial))

-- Day 5 `absorbStacked`, False arm.
theorem absorbFalse (id: Nat) (lastFrom: Nat) (rFrom: Nat) (h: id < lastFrom) (ok: lastFrom ≤ rFrom): id < rFrom :=
  Omega.prove (MkEnv [id, lastFrom, rFrom] []) [FLt (NV 0) (NV 1), FLe (NV 1) (NV 2)] (GLt (NV 0) (NV 2))
    (Then (Input 0) (Then (Input 1) (Then NegGoal (Then (Combine [MkPair 1 0, MkPair 1 1, MkPair 1 2]) (Close 3)))))
    rfl (Both h (Both ok Trivial))

-- No hypotheses: needs `x_1 >= 0`.
theorem leAddRight (x: Nat) (y: Nat): x ≤ x + y :=
  Omega.prove (MkEnv [x, y] []) [] (GLe (NV 0) (NAdd (NV 0) (NV 1)))
    (Then NegGoal (Then (NatNonneg 1) (Then (Combine [MkPair 1 0, MkPair 1 1]) (Close 2))))
    rfl Trivial

-- Multiplication shape, `x * 3` (MulRight): both directions are `-1 >= 0` after the negated goal alone.
theorem mulRight3 (x: Nat): x * 3 = x + x + x :=
  Omega.proveEq (MkEnv [x] []) [] (MulRight (NV 0) 3) (NAdd (NAdd (NV 0) (NV 0)) (NV 0))
    (Then NegGoal (Close 0)) (Then NegGoal (Close 0)) rfl rfl Trivial

-- Multiplication shape, `3 * x` (MulLeft).
theorem mulLeft3 (x: Nat): 3 * x = x + x + x :=
  Omega.proveEq (MkEnv [x] []) [] (MulLeft 3 (NV 0)) (NAdd (NAdd (NV 0) (NV 0)) (NV 0))
    (Then NegGoal (Close 0)) (Then NegGoal (Close 0)) rfl rfl Trivial

-- `x * 0 = 0`
theorem mulRight0 (x: Nat): x * 0 = 0 :=
  Omega.proveEq (MkEnv [x] []) [] (MulRight (NV 0) 0) (NLit 0)
    (Then NegGoal (Close 0)) (Then NegGoal (Close 0)) rfl rfl Trivial

-- `0 * x = 0`
theorem mulLeft0 (x: Nat): 0 * x = 0 :=
  Omega.proveEq (MkEnv [x] []) [] (MulLeft 0 (NV 0)) (NLit 0)
    (Then NegGoal (Close 0)) (Then NegGoal (Close 0)) rfl rfl Trivial

-- `x * 1 = x`
theorem mulRight1 (x: Nat): x * 1 = x :=
  Omega.proveEq (MkEnv [x] []) [] (MulRight (NV 0) 1) (NV 0)
    (Then NegGoal (Close 0)) (Then NegGoal (Close 0)) rfl rfl Trivial

-- `1 * x = x`
theorem mulLeft1 (x: Nat): 1 * x = x :=
  Omega.proveEq (MkEnv [x] []) [] (MulLeft 1 (NV 0)) (NV 0)
    (Then NegGoal (Close 0)) (Then NegGoal (Close 0)) rfl rfl Trivial

-- An equation from two inequalities: each direction is refuted separately.
theorem antisym (a: Nat) (b: Nat) (h1: a ≤ b) (h2: b ≤ a): a = b :=
  Omega.proveEq (MkEnv [a, b] []) [FLe (NV 0) (NV 1), FLe (NV 1) (NV 0)] (NV 0) (NV 1)
    (Then (Input 0) (Then NegGoal (Then (Combine [MkPair 1 0, MkPair 1 1]) (Close 2))))
    (Then (Input 1) (Then NegGoal (Then (Combine [MkPair 1 0, MkPair 1 1]) (Close 2))))
    rfl rfl (Both h1 (Both h2 Trivial))

-- A closed contradiction: the row is `-2 >= 0`.
theorem threeLtTwo (h: 3 < 2): Void :=
  Omega.prove (MkEnv [] []) [FLt (NLit 3) (NLit 2)] GVoid (Then (Input 0) (Close 0)) rfl (Both h Trivial)

-- A contradiction unrelated to the goal.
theorem disconnected (x: Nat) (y: Nat) (h: y < y): x < 0 :=
  Omega.prove (MkEnv [x, y] []) [FLt (NV 1) (NV 1)] (GLt (NV 0) (NLit 0)) (Then (Input 0) (Close 0)) rfl (Both h Trivial)

-- A `Void` goal from two facts.
theorem twoFactsVoid (x: Nat) (y: Nat) (h1: x + 1 ≤ y) (h2: y ≤ x): Void :=
  Omega.prove (MkEnv [x, y] []) [FLe (NAdd (NV 0) (NLit 1)) (NV 1), FLe (NV 1) (NV 0)] GVoid
    (Then (Input 0) (Then (Input 1) (Then (Combine [MkPair 1 0, MkPair 1 1]) (Close 2))))
    rfl (Both h1 (Both h2 Trivial))

-- `2 * x = 1` has no solution: dividing its two rows (`1 - 2x` and `2x - 1`) by 2 gives
-- `-x >= 0` and `x - 1 >= 0`.
theorem twoXEqOne (x: Nat) (h: 2 * x = 1): Void :=
  Omega.prove (MkEnv [x] []) [FEq (MulLeft 2 (NV 0)) (NLit 1)] GVoid
    (Then (Input 0) (Then (Input 1) (Then (Divide 0 2) (Then (Divide 1 2) (Then (Combine [MkPair 1 2, MkPair 1 3]) (Close 4))))))
    rfl (Both h Trivial)

-- The integer regression: rationally satisfiable (x = y = 1/2), refuted by a split on `-y >= 0`
-- and rounding down after each division.
theorem splitRegression (x: Nat) (y: Nat) (h1: 1 ≤ 2 * x + 3 * y) (h2: 2 * x + 3 * y ≤ 4) (h3: 2 * y ≤ 3 * x + 1) (h4: 3 * x ≤ 2 * y + 2): Void :=
  Omega.prove (MkEnv [x, y] [])
    [
      FLe (NLit 1) (NAdd (MulLeft 2 (NV 0)) (MulLeft 3 (NV 1))),
      FLe (NAdd (MulLeft 2 (NV 0)) (MulLeft 3 (NV 1))) (NLit 4),
      FLe (MulLeft 2 (NV 1)) (NAdd (MulLeft 3 (NV 0)) (NLit 1)),
      FLe (MulLeft 3 (NV 0)) (NAdd (MulLeft 2 (NV 1)) (NLit 2))
    ]
    GVoid
    (Then (Input 0) (Then (Input 1) (Then (Input 2) (Then (Input 3)
      (Split (MkRow 0 [0, -1] [])
        (Then (Combine [MkPair 1 0, MkPair 3 4]) (Then (Divide 5 2) (Then (Combine [MkPair 1 3, MkPair 2 4]) (Then (Divide 7 3)
          (Then (Combine [MkPair 1 6, MkPair 1 8]) (Close 9))))))
        (Then (Combine [MkPair 1 1, MkPair 3 4]) (Then (Divide 5 2) (Then (Combine [MkPair 1 2, MkPair 3 6]) (Then (Divide 7 2)
          (Then (Combine [MkPair 1 4, MkPair 1 8]) (Close 9)))))))))))
    rfl (Both h1 (Both h2 (Both h3 (Both h4 Trivial))))

-- Ten variables in a chain, for timing: `3 * x0 - 3 * x9 - 8 >= 0` against the nine links times 3.
theorem chain10 (x0: Nat) (x1: Nat) (x2: Nat) (x3: Nat) (x4: Nat) (x5: Nat) (x6: Nat) (x7: Nat) (x8: Nat) (x9: Nat)
    (h0: x0 ≤ x1) (h1: x1 ≤ x2) (h2: x2 ≤ x3) (h3: x3 ≤ x4) (h4: x4 ≤ x5) (h5: x5 ≤ x6) (h6: x6 ≤ x7) (h7: x7 ≤ x8) (h8: x8 ≤ x9):
    3 * x0 ≤ x9 + 2 * x9 + 7 :=
  Omega.prove (MkEnv [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9] [])
    [
      FLe (NV 0) (NV 1),
      FLe (NV 1) (NV 2),
      FLe (NV 2) (NV 3),
      FLe (NV 3) (NV 4),
      FLe (NV 4) (NV 5),
      FLe (NV 5) (NV 6),
      FLe (NV 6) (NV 7),
      FLe (NV 7) (NV 8),
      FLe (NV 8) (NV 9)
    ]
    (GLe (MulLeft 3 (NV 0)) (NAdd (NAdd (NV 9) (MulLeft 2 (NV 9))) (NLit 7)))
    (Then (Input 0) (Then (Input 1) (Then (Input 2) (Then (Input 3) (Then (Input 4) (Then (Input 5) (Then (Input 6) (Then (Input 7) (Then (Input 8)
      (Then NegGoal
        (Then (Combine [MkPair 3 0, MkPair 3 1, MkPair 3 2, MkPair 3 3, MkPair 3 4, MkPair 3 5, MkPair 3 6, MkPair 3 7, MkPair 3 8, MkPair 1 9])
          (Close 10))))))))))))
    rfl (Both h0 (Both h1 (Both h2 (Both h3 (Both h4 (Both h5 (Both h6 (Both h7 (Both h8 Trivial)))))))))
