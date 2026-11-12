--| The soundness of `Omega.check` (std/Omega/Omega.sw): [`Omega.prove`] says
--| that a certificate the checker accepts proves the goal from the facts, for
--| every environment, whatever the lengths of its lists. Every lemma is about
--| values at a given environment: no function or propositional
--| extensionality, no assumptions.
-- (docs/proposals/omega.md §6.6)

import Omega.Env (MkEnv)
import Omega.NTerm (NV, NLit, NAdd, NSucc, MulLeft, MulRight)
import Omega.ITerm (IV, IOfNat, INegSucc, IAdd, INeg, IMulLeft, IMulRight, ISubNat)
import Omega.Fact (FLe, FLt, FEq, FNotLe, FNotLt, FSub, FMax, FMin, FNe, FILe, FINotLe, FILt, FINotLt, FIEq, FINe)
import Omega.Goal (GLe, GLt, GVoid, GILe, GILt, GINotLe, GINotLt)
import Omega.Row (MkRow)
import Omega.Step (Input, NegGoal, NatNonneg, Combine, Divide)
import Omega.Cert (Close, Then, Split, Cases)

--| Carrying `0 <= y` to `0 <= x` along `x = y`.
theorem Omega.nonnegEq [x y: Int] (e: x = y) (h: 0 ≤ y): 0 ≤ x := J (z p => Int.leq (OfNat 0) z = True) h (Eq.sym e)

theorem Omega.dotAdd (as bs vs: List Int):
    Omega.dot (Omega.addC as bs) vs = Omega.dot as vs + Omega.dot bs vs :=
  match as, bs, vs with
    | [], bs, vs => Eq.sym (Int.zeroAdd (Omega.dot bs vs))
    | [a, ..as], [], vs => Eq.sym (Int.addZero (Omega.dot [a, ..as] vs))
    | [a, ..as], [b, ..bs], [] => rfl
    | [a, ..as], [b, ..bs], [v, ..vs] =>
      Eq.trans (Int.addCong (Int.mulDistribRight a b v) (Omega.dotAdd as bs vs))
        (Int.addAddSwap (a * v) (b * v) (Omega.dot as vs) (Omega.dot bs vs))

theorem Omega.dotScale (k: Int) (as vs: List Int): Omega.dot (Omega.scaleC k as) vs = k * Omega.dot as vs :=
  match as, vs with
    | [], vs => Eq.sym (Int.mulZero k)
    | [a, ..as], [] => Eq.sym (Int.mulZero k)
    | [a, ..as], [v, ..vs] =>
      Eq.trans (Int.addCong (Int.mulAssoc k a v) (Omega.dotScale k as vs))
        (Eq.sym (Int.mulDistribLeft k (a * v) (Omega.dot as vs)))

theorem Omega.dotUnit (i: Nat) (ns: List Nat): Omega.dot (Omega.unit i) (Omega.toInts ns) = OfNat (Omega.natAt i ns) :=
  match i, ns with
    | Zero, [] => rfl
    | Zero, [x, ..xs] => Eq.trans (Int.addZero (Int.mul (OfNat 1) (OfNat x))) (Int.oneMul (OfNat x))
    | Succ i, [] => rfl
    | Succ i, [x, ..xs] => Eq.trans (Int.zeroAdd (Omega.dot (Omega.unit i) (Omega.toInts xs))) (Omega.dotUnit i xs)

theorem Omega.dotUnitInt (i: Nat) (vs: List Int): Omega.dot (Omega.unit i) vs = Omega.intAt i vs :=
  match i, vs with
    | Zero, [] => rfl
    | Zero, [x, ..xs] => Eq.trans (Int.addZero (Int.mul (OfNat 1) x)) (Int.oneMul x)
    | Succ i, [] => rfl
    | Succ i, [x, ..xs] =>
      Eq.trans (Eq.cong (t => Int.add t (Omega.dot (Omega.unit i) xs)) (Int.zeroMul x))
        (Eq.trans (Int.zeroAdd (Omega.dot (Omega.unit i) xs)) (Omega.dotUnitInt i xs))

theorem Omega.isZeroEq (x: Int) (h: Omega.isZero x = True): x = OfNat 0 :=
  match x with
    | OfNat Zero => rfl

theorem Omega.dotAllZero (as vs: List Int) (h: Omega.allZero as = True): Omega.dot as vs = OfNat 0 :=
  match as, vs with
    | [], vs => rfl
    | [a, ..as], [] => rfl
    | [a, ..as], [v, ..vs] =>
      Int.addCong
        (Eq.trans (Eq.cong (t => Int.mul t v) (Omega.isZeroEq a (Bool.andLeft h))) (Int.zeroMul v))
        (Omega.dotAllZero as vs (Bool.andRight h))

--| A coefficient that `d` divides is `d` times its quotient.
theorem Omega.divExact (d: Nat) (a: Int) (h: Omega.isZero (a % OfNat (Succ d)) = True): a = OfNat (Succ d) * (a / OfNat (Succ d)) :=
  Eq.sym (Eq.trans (Eq.sym (Int.addZero (OfNat (Succ d) * (a / OfNat (Succ d)))))
    (Eq.trans (Eq.cong (Int.add (OfNat (Succ d) * (a / OfNat (Succ d)))) (Eq.sym (Omega.isZeroEq (a % OfNat (Succ d)) h)))
      (Int.divAddMod a (OfNat (Succ d)))))

theorem Omega.dotDiv (d: Nat) (as vs: List Int) (h: Omega.allDiv d as = True):
    Omega.dot as vs = OfNat (Succ d) * Omega.dot (Omega.divC d as) vs :=
  match as, vs with
    | [], vs => Eq.sym (Int.mulZero (OfNat (Succ d)))
    | [a, ..as], [] => Eq.sym (Int.mulZero (OfNat (Succ d)))
    | [a, ..as], [v, ..vs] =>
      Eq.trans
        (Int.addCong
          (Eq.trans (Eq.cong (t => Int.mul t v) (Omega.divExact d a (Bool.andLeft h)))
            (Int.mulAssoc (OfNat (Succ d)) (a / OfNat (Succ d)) v))
          (Omega.dotDiv d as vs (Bool.andRight h)))
        (Eq.sym (Int.mulDistribLeft (OfNat (Succ d)) ((a / OfNat (Succ d)) * v) (Omega.dot (Omega.divC d as) vs)))

--| `(c + d) + ((x1 + x2) + (y1 + y2)) = (c + (x1 + y1)) + (d + (x2 + y2))`
theorem Omega.add3Swap (c: Int) (d: Int) (x1: Int) (x2: Int) (y1: Int) (y2: Int):
    (c + d) + ((x1 + x2) + (y1 + y2)) = (c + (x1 + y1)) + (d + (x2 + y2)) :=
  Eq.trans (Eq.cong (Int.add (c + d)) (Int.addAddSwap x1 x2 y1 y2))
    (Eq.sym (Int.addAddSwap c (x1 + y1) d (x2 + y2)))

theorem Omega.valueAdd (nv: List Int) (iv: List Int) (r s: Omega.Row):
    Omega.Row.value nv iv (Omega.Row.add r s) = Omega.Row.value nv iv r + Omega.Row.value nv iv s :=
  match r, s with
    | MkRow c ns is, MkRow d ms js =>
      Eq.trans (Eq.cong (Int.add (c + d)) (Int.addCong (Omega.dotAdd ns ms nv) (Omega.dotAdd is js iv)))
        (Omega.add3Swap c d (Omega.dot ns nv) (Omega.dot ms nv) (Omega.dot is iv) (Omega.dot js iv))

theorem Omega.valueScale (nv: List Int) (iv: List Int) (k: Int) (r: Omega.Row):
    Omega.Row.value nv iv (Omega.Row.scale k r) = k * Omega.Row.value nv iv r :=
  match r with
    | MkRow c ns is =>
      Eq.trans (Eq.cong (Int.add (k * c))
          (Eq.trans (Int.addCong (Omega.dotScale k ns nv) (Omega.dotScale k is iv))
            (Eq.sym (Int.mulDistribLeft k (Omega.dot ns nv) (Omega.dot is iv)))))
        (Eq.sym (Int.mulDistribLeft k c (Omega.dot ns nv + Omega.dot is iv)))

theorem Omega.evalAdd (env: Omega.Env) (r: Omega.Row) (s: Omega.Row):
    Omega.Row.eval env (Omega.Row.add r s) = Omega.Row.eval env r + Omega.Row.eval env s :=
  Omega.valueAdd (Omega.toInts (Omega.Env.nats env)) (Omega.Env.ints env) r s

theorem Omega.evalScale (env: Omega.Env) (k: Int) (r: Omega.Row):
    Omega.Row.eval env (Omega.Row.scale k r) = k * Omega.Row.eval env r :=
  Omega.valueScale (Omega.toInts (Omega.Env.nats env)) (Omega.Env.ints env) k r

--| `r - s` means `r` minus `s`.
theorem Omega.evalSub (env: Omega.Env) (r: Omega.Row) (s: Omega.Row):
    Omega.Row.eval env (Omega.Row.sub r s) = Omega.Row.eval env r + Int.neg (Omega.Row.eval env s) :=
  Eq.trans (Omega.evalAdd env r (Omega.Row.scale (NegSucc 0) s))
    (Eq.cong (Int.add (Omega.Row.eval env r))
      (Eq.trans (Omega.evalScale env (NegSucc 0) s) (Int.negOneMul (Omega.Row.eval env s))))

--| The linear form of a term means the term.
theorem Omega.linEval (env: Omega.Env) (t: Omega.NTerm): Omega.Row.eval env (Omega.NTerm.lin t) = OfNat (Omega.NTerm.eval env t) :=
  match t with
    | NV i =>
      Eq.trans (Int.zeroAdd (Int.add (Omega.dot (Omega.unit i) (Omega.toInts (Omega.Env.nats env))) (OfNat 0)))
        (Eq.trans (Int.addZero (Omega.dot (Omega.unit i) (Omega.toInts (Omega.Env.nats env))))
          (Omega.dotUnit i (Omega.Env.nats env)))
    | NLit n => Int.addZero (OfNat n)
    | NAdd a b =>
      Eq.trans (Omega.evalAdd env (Omega.NTerm.lin a) (Omega.NTerm.lin b)) (Int.addCong (Omega.linEval env a) (Omega.linEval env b))
    | NSucc a =>
      Eq.trans (Omega.evalAdd env (Omega.NTerm.lin a) Omega.Row.one)
        (Eq.trans (Eq.cong (t => Int.add t (OfNat 1)) (Omega.linEval env a))
          (Eq.cong OfNat (Nat.addOne (Omega.NTerm.eval env a))))
    | MulLeft k t =>
      Eq.trans (Omega.evalScale env (OfNat k) (Omega.NTerm.lin t)) (Eq.cong (Int.mul (OfNat k)) (Omega.linEval env t))
    | MulRight t k =>
      Eq.trans (Omega.evalScale env (OfNat k) (Omega.NTerm.lin t))
        (Eq.trans (Eq.cong (Int.mul (OfNat k)) (Omega.linEval env t))
          (Eq.cong OfNat (Nat.mulComm k (Omega.NTerm.eval env t))))

--| The convention: `a <= b` gives the row `b - a >= 0`.
theorem Omega.leRowHolds (env: Omega.Env) (a: Omega.NTerm) (b: Omega.NTerm) (h: Omega.NTerm.eval env a ≤ Omega.NTerm.eval env b):
    Omega.Row.Holds env (Omega.leRow a b) :=
  Omega.nonnegEq
    (Eq.trans (Omega.evalSub env (Omega.NTerm.lin b) (Omega.NTerm.lin a))
      (Int.addCong (Omega.linEval env b) (Eq.cong Int.neg (Omega.linEval env a))))
    (Int.subNonnegOfLe (Omega.NTerm.eval env a) (Omega.NTerm.eval env b) h)

--| `-1 - n` is `NegSucc n`.
theorem Omega.negSuccOfNat (n: Nat): Int.add (NegSucc 0) (Int.neg (OfNat n)) = NegSucc n :=
  match n with
    | Zero => rfl
    | Succ n => rfl

--| The linear form of an `Int` term means the term.
theorem Omega.ilinEval (env: Omega.Env) (t: Omega.ITerm): Omega.Row.eval env (Omega.ITerm.lin t) = Omega.ITerm.eval env t :=
  match t with
    | IV i =>
      Eq.trans (Int.zeroAdd (Int.add (OfNat 0) (Omega.dot (Omega.unit i) (Omega.Env.ints env))))
        (Eq.trans (Int.zeroAdd (Omega.dot (Omega.unit i) (Omega.Env.ints env)))
          (Omega.dotUnitInt i (Omega.Env.ints env)))
    | IOfNat t => Omega.linEval env t
    | INegSucc t =>
      Eq.trans (Omega.evalSub env (MkRow (NegSucc 0) [] []) (Omega.NTerm.lin t))
        (Eq.trans (Eq.cong (x => Int.add (NegSucc 0) (Int.neg x)) (Omega.linEval env t))
          (Omega.negSuccOfNat (Omega.NTerm.eval env t)))
    | IAdd a b =>
      Eq.trans (Omega.evalAdd env (Omega.ITerm.lin a) (Omega.ITerm.lin b)) (Int.addCong (Omega.ilinEval env a) (Omega.ilinEval env b))
    | INeg a =>
      Eq.trans (Omega.evalScale env (NegSucc 0) (Omega.ITerm.lin a))
        (Eq.trans (Int.negOneMul (Omega.Row.eval env (Omega.ITerm.lin a))) (Eq.cong Int.neg (Omega.ilinEval env a)))
    | IMulLeft k t =>
      Eq.trans (Omega.evalScale env k (Omega.ITerm.lin t)) (Eq.cong (Int.mul k) (Omega.ilinEval env t))
    | IMulRight t k =>
      Eq.trans (Omega.evalScale env k (Omega.ITerm.lin t))
        (Eq.trans (Eq.cong (Int.mul k) (Omega.ilinEval env t)) (Int.mulComm k (Omega.ITerm.eval env t)))
    | ISubNat a b =>
      Eq.trans (Omega.evalSub env (Omega.NTerm.lin a) (Omega.NTerm.lin b))
        (Eq.trans (Int.addCong (Omega.linEval env a) (Eq.cong Int.neg (Omega.linEval env b)))
          (Int.addNegOfNat (Omega.NTerm.eval env a) (Omega.NTerm.eval env b)))

-- `Int`'s order, by cases on the constructors down to `Nat`'s.

theorem Omega.intLeqRefl (a: Int): Int.leq a a = True :=
  match a with
    | OfNat m => Nat.leRefl m
    | NegSucc m => Nat.leRefl m

theorem Omega.intLeqOfEq [a b: Int] (e: a = b): Int.leq a b = True := J (y p => Int.leq a y = True) (Omega.intLeqRefl a) e

theorem Omega.intLeAntisym (a b: Int) (h1: Int.leq a b = True) (h2: Int.leq b a = True): a = b :=
  match a, b with
    | OfNat m, OfNat n => Eq.cong OfNat (Nat.leAntisym m n h1 h2)
    | NegSucc m, NegSucc n => Eq.cong NegSucc (Nat.leAntisym m n h2 h1)

--| `m < n` as `m + 1 <= n`.
theorem Omega.natLeqAddOne (m: Nat) (n: Nat) (h: m < n): m + 1 ≤ n := J (y p => Nat.leq y n = True) h (Eq.sym (Nat.addOne m))

--| `a < b` is `a + 1 <= b`.
theorem Omega.intLeqOfLess (a b: Int) (h: Int.less a b = True): Int.leq (Int.add a (OfNat 1)) b = True :=
  match a, b with
    | OfNat m, OfNat n => Omega.natLeqAddOne m n h
    | NegSucc Zero, OfNat n => rfl
    | NegSucc (Succ m), OfNat n => rfl
    | NegSucc (Succ m), NegSucc n => h

--| `Not (a <= b)` is `b + 1 <= a`.
theorem Omega.intLeqOfNotLeq (a b: Int) (h: Int.leq a b = False): Int.leq (Int.add b (OfNat 1)) a = True :=
  match a, b with
    | OfNat m, OfNat n => Omega.natLeqAddOne n m (Nat.leqFalse m n h)
    | OfNat m, NegSucc Zero => rfl
    | OfNat m, NegSucc (Succ n) => rfl
    | NegSucc m, NegSucc (Succ n) => Nat.leqFalse (Succ n) m h

--| `Not (a < b)` is `b <= a`.
theorem Omega.intLeqOfNotLess (a b: Int) (h: Int.less a b = False): Int.leq b a = True :=
  match a, b with
    | OfNat m, OfNat n => Nat.leqFalse (Succ m) n h
    | OfNat m, NegSucc n => rfl
    | NegSucc m, NegSucc n => Nat.leqFalse (Succ n) m h

--| `a <= b` gives `0 <= b - a`.
theorem Omega.intSubNonneg (a b: Int) (h: Int.leq a b = True): 0 ≤ Int.add b (Int.neg a) :=
  match a, b with
    | OfNat m, OfNat n => Int.subNonnegOfLe m n h
    | NegSucc m, OfNat n => rfl
    | NegSucc m, NegSucc n =>
      Omega.nonnegEq (Eq.trans (Int.subNatNatSucc m n) (Eq.sym (Int.subOfNats m n))) (Int.subNonnegOfLe n m h)

--| The convention on `Int`: `a <= b` gives the row `b - a >= 0`.
theorem Omega.ileRowHolds (env: Omega.Env) (a: Omega.ITerm) (b: Omega.ITerm) (h: Int.leq (Omega.ITerm.eval env a) (Omega.ITerm.eval env b) = True):
    Omega.Row.Holds env (Omega.ileRow a b) :=
  Omega.nonnegEq
    (Eq.trans (Omega.evalSub env (Omega.ITerm.lin b) (Omega.ITerm.lin a))
      (Int.addCong (Omega.ilinEval env b) (Eq.cong Int.neg (Omega.ilinEval env a))))
    (Omega.intSubNonneg (Omega.ITerm.eval env a) (Omega.ITerm.eval env b) h)

--| Every row holds in `env`.
def Omega.RowsHold (env: Omega.Env): (rows: List Omega.Row) → Prop
  | [] => Unit
  | [r, ..rs] => (Omega.Row.Holds env r) ∧ (Omega.RowsHold env rs)

--| The row, if there is one, holds in `env`.
def Omega.OptHolds (env: Omega.Env): (option: Option Omega.Row) → Prop
  | None => Unit
  | Some r => Omega.Row.Holds env r

theorem Omega.rowsAppend (env: Omega.Env) (xs ys: List Omega.Row)
    (hx: Omega.RowsHold env xs) (hy: Omega.RowsHold env ys): Omega.RowsHold env (List.append xs ys) :=
  match xs, hx with
    | [], hx => hy
    | [x, ..xs], Both h hs => Both h (Omega.rowsAppend env xs ys hs hy)

theorem Omega.getRowHolds (env: Omega.Env) (rs: List Omega.Row) (i: Nat) (h1: Omega.RowsHold env rs): Omega.Row.Holds env (Omega.getRow rs i) :=
  match rs, i, h1 with
    | [], i, h => rfl
    | [r, ..rs], Zero, Both h hs => h
    | [r, ..rs], Succ i, Both h hs => Omega.getRowHolds env rs i hs

theorem Omega.optRowHolds (env: Omega.Env) (o: Option Omega.Row) (h: Omega.OptHolds env o): Omega.Row.Holds env (Omega.optRow o) :=
  match o with
    | None => rfl
    | Some r => h

-- The operation facts (stage 2), about plain numbers: what always holds, then
-- the two cases.

--| `a <= (a - b) + b`, whichever of `a` and `b` is larger.
theorem Omega.leSubAdd (a b: Nat): a ≤ (a - b) + b :=
  match a, b with
    | a, Zero => Nat.leAddRight a 0
    | Zero, Succ b => rfl
    | Succ a, Succ b =>
      Nat.leCongRight (Succ a) (Succ ((a - b) + b)) ((a - b) + Succ b) (Eq.sym (Nat.addSucc (a - b) b)) (Omega.leSubAdd a b)

theorem Omega.subLeLeft (t: Nat) (a: Nat) (b: Nat) (h: t = a - b): t ≤ a :=
  Nat.leCongLeft (a - b) t a (Eq.sym h) (Nat.subLe a b)

theorem Omega.subLeAdd (t: Nat) (a: Nat) (b: Nat) (h: t = a - b): a ≤ t + b :=
  Nat.leCongRight a ((a - b) + b) (t + b) (Eq.cong (x => x + b) (Eq.sym h)) (Omega.leSubAdd a b)

theorem Omega.subCases (t: Nat) (a: Nat) (b: Nat) (h: t = a - b)
    (kl: (b ≤ a) ∧ ((t + b = a) ∧ Unit) → Void) (kr: (a < b) ∧ ((t = 0) ∧ Unit) → Void): Void :=
  Bool.inspect (Nat.leq b a) (x => Void)
    (e => kl (Both e (Both (Eq.trans (Eq.cong (x => x + b) h) (Eq.trans (Nat.addComm (a - b) b) (Nat.addSubCancel b a e))) Trivial)))
    (e => kr (Both (Nat.leqFalse b a e) (Both (Eq.trans h (Nat.subEqZero a b (Nat.lessLe a b (Nat.leqFalse b a e)))) Trivial)))

theorem Omega.maxCases (t: Nat) (a: Nat) (b: Nat) (h: t = Nat.max a b)
    (kl: (a ≤ b) ∧ ((t = b) ∧ Unit) → Void) (kr: (b < a) ∧ ((t = a) ∧ Unit) → Void): Void :=
  Bool.inspect (Nat.leq a b) (x => Void)
    (e => kl (Both e (Both (Eq.trans h (Nat.maxRight a b e)) Trivial)))
    (e => kr (Both (Nat.leqFalse a b e) (Both (Eq.trans h (Nat.maxLeft a b (Nat.lessLe b a (Nat.leqFalse a b e)))) Trivial)))

theorem Omega.minCases (t: Nat) (a: Nat) (b: Nat) (h: t = Nat.min a b)
    (kl: (a ≤ b) ∧ ((t = a) ∧ Unit) → Void) (kr: (b < a) ∧ ((t = b) ∧ Unit) → Void): Void :=
  Bool.inspect (Nat.leq a b) (x => Void)
    (e => kl (Both e (Both (Eq.trans h (Nat.minLeft a b e)) Trivial)))
    (e => kr (Both (Nat.leqFalse a b e) (Both (Eq.trans h (Nat.minRight a b e)) Trivial)))

theorem Omega.neCases (a: Nat) (b: Nat) (h: a ≠ b)
    (kl: (a < b) ∧ Unit → Void) (kr: (b < a) ∧ Unit → Void): Void :=
  Bool.inspect (Nat.leq (Succ a) b) (x => Void)
    (e => kl (Both e Trivial))
    (e => kr (Both (Nat.leNeSucc b a (Nat.leqFalse (Succ a) b e) (p => h (Eq.sym p))) Trivial))

theorem Omega.ineCases (a: Int) (b: Int) (h: a ≠ b)
    (kl: (Int.less a b = True) ∧ Unit → Void) (kr: (Int.less b a = True) ∧ Unit → Void): Void :=
  Bool.inspect (Int.less a b) (x => Void)
    (e => kl (Both e Trivial))
    (e => Bool.inspect (Int.less b a) (x => Void)
      (e2 => kr (Both e2 Trivial))
      (e2 => h (Omega.intLeAntisym a b (Omega.intLeqOfNotLess b a e2) (Omega.intLeqOfNotLess a b e))))

theorem Omega.factRowsHold (env: Omega.Env) (f: Omega.Fact) (h: Omega.Fact.holds env f): Omega.RowsHold env (Omega.Fact.rows f) :=
  match f with
    | FLe a b => Both (Omega.leRowHolds env a b h) Trivial
    | FLt a b => Both (Omega.leRowHolds env (NSucc a) b h) Trivial
    | FEq a b =>
      Both (Omega.leRowHolds env a b (Nat.leOfEq (Omega.NTerm.eval env a) (Omega.NTerm.eval env b) h))
        (Both (Omega.leRowHolds env b a (Nat.leOfEq (Omega.NTerm.eval env b) (Omega.NTerm.eval env a) (Eq.sym h))) Trivial)
    | FNotLe a b => Both (Omega.leRowHolds env (NSucc b) a (Nat.ltOfNotLe (Omega.NTerm.eval env a) (Omega.NTerm.eval env b) h)) Trivial
    | FNotLt a b => Both (Omega.leRowHolds env b a (Nat.leOfNotLt (Omega.NTerm.eval env a) (Omega.NTerm.eval env b) h)) Trivial
    | FSub t a b =>
      Both (Omega.leRowHolds env t a (Omega.subLeLeft (Omega.NTerm.eval env t) (Omega.NTerm.eval env a) (Omega.NTerm.eval env b) h))
        (Both (Omega.leRowHolds env a (NAdd t b) (Omega.subLeAdd (Omega.NTerm.eval env t) (Omega.NTerm.eval env a) (Omega.NTerm.eval env b) h)) Trivial)
    | FMax t a b =>
      Both (Omega.leRowHolds env a t (Nat.leCongRight (Omega.NTerm.eval env a) (Nat.max (Omega.NTerm.eval env a) (Omega.NTerm.eval env b)) (Omega.NTerm.eval env t) (Eq.sym h)
          (Nat.leMaxLeft (Omega.NTerm.eval env a) (Omega.NTerm.eval env b))))
        (Both (Omega.leRowHolds env b t (Nat.leCongRight (Omega.NTerm.eval env b) (Nat.max (Omega.NTerm.eval env a) (Omega.NTerm.eval env b)) (Omega.NTerm.eval env t) (Eq.sym h)
          (Nat.leMaxRight (Omega.NTerm.eval env a) (Omega.NTerm.eval env b)))) Trivial)
    | FMin t a b =>
      Both (Omega.leRowHolds env t a (Nat.leCongLeft (Nat.min (Omega.NTerm.eval env a) (Omega.NTerm.eval env b)) (Omega.NTerm.eval env t) (Omega.NTerm.eval env a) (Eq.sym h)
          (Nat.minLeLeft (Omega.NTerm.eval env a) (Omega.NTerm.eval env b))))
        (Both (Omega.leRowHolds env t b (Nat.leCongLeft (Nat.min (Omega.NTerm.eval env a) (Omega.NTerm.eval env b)) (Omega.NTerm.eval env t) (Omega.NTerm.eval env b) (Eq.sym h)
          (Nat.minLeRight (Omega.NTerm.eval env a) (Omega.NTerm.eval env b)))) Trivial)
    | FNe a b => Trivial
    | FILe a b => Both (Omega.ileRowHolds env a b h) Trivial
    | FINotLe a b =>
      Both (Omega.ileRowHolds env (Omega.ITerm.succ b) a (Omega.intLeqOfNotLeq (Omega.ITerm.eval env a) (Omega.ITerm.eval env b) h)) Trivial
    | FILt a b =>
      Both (Omega.ileRowHolds env (Omega.ITerm.succ a) b (Omega.intLeqOfLess (Omega.ITerm.eval env a) (Omega.ITerm.eval env b) h)) Trivial
    | FINotLt a b =>
      Both (Omega.ileRowHolds env b a (Omega.intLeqOfNotLess (Omega.ITerm.eval env a) (Omega.ITerm.eval env b) h)) Trivial
    | FIEq a b =>
      Both (Omega.ileRowHolds env a b (Omega.intLeqOfEq h)) (Both (Omega.ileRowHolds env b a (Omega.intLeqOfEq (Eq.sym h))) Trivial)
    | FINe a b => Trivial

--| A fact with cases holds in one of them.
theorem Omega.factCases (env: Omega.Env) (f: Omega.Fact) (h: Omega.Fact.holds env f) (ok: Omega.Fact.splits f = True)
    (kl: (Omega.Facts.holds env (Omega.Fact.left f) → Void)) (kr: (Omega.Facts.holds env (Omega.Fact.right f) → Void)): Void :=
  match f with
    | FSub t a b => Omega.subCases (Omega.NTerm.eval env t) (Omega.NTerm.eval env a) (Omega.NTerm.eval env b) h kl kr
    | FMax t a b => Omega.maxCases (Omega.NTerm.eval env t) (Omega.NTerm.eval env a) (Omega.NTerm.eval env b) h kl kr
    | FMin t a b => Omega.minCases (Omega.NTerm.eval env t) (Omega.NTerm.eval env a) (Omega.NTerm.eval env b) h kl kr
    | FNe a b => Omega.neCases (Omega.NTerm.eval env a) (Omega.NTerm.eval env b) h kl kr
    | FINe a b => Omega.ineCases (Omega.ITerm.eval env a) (Omega.ITerm.eval env b) h kl kr

theorem Omega.factsRowsHold (env: Omega.Env) (fs: List Omega.Fact) (h1: Omega.Facts.holds env fs): Omega.RowsHold env (Omega.Facts.rows fs) :=
  match fs, h1 with
    | [], h => Trivial
    | [f, ..fs], Both h hs =>
      Omega.rowsAppend env (Omega.Fact.rows f) (Omega.Facts.rows fs) (Omega.factRowsHold env f h) (Omega.factsRowsHold env fs hs)

theorem Omega.getFactHolds (env: Omega.Env) (fs: List Omega.Fact) (i: Nat) (h1: Omega.Facts.holds env fs): Omega.Fact.holds env (Omega.getFact fs i) :=
  match fs, i, h1 with
    | [], i, h => rfl
    | [f, ..fs], Zero, Both h hs => h
    | [f, ..fs], Succ i, Both h hs => Omega.getFactHolds env fs i hs

theorem Omega.combineHolds (env: Omega.Env) (ctx: List Omega.Row) (hc: Omega.RowsHold env ctx)
    (ts: List (Pair Nat Nat)): Omega.Row.Holds env (Omega.combine ctx ts) :=
  match ts with
    | [] => rfl
    | [MkPair k r, ..ts] =>
      Omega.nonnegEq (Omega.evalAdd env (Omega.Row.scale (OfNat k) (Omega.getRow ctx r)) (Omega.combine ctx ts))
        (Int.addNonneg (Omega.Row.eval env (Omega.Row.scale (OfNat k) (Omega.getRow ctx r))) (Omega.Row.eval env (Omega.combine ctx ts))
          (Omega.nonnegEq (Omega.evalScale env (OfNat k) (Omega.getRow ctx r))
            (Int.mulNonneg (OfNat k) (Omega.Row.eval env (Omega.getRow ctx r)) rfl (Omega.getRowHolds env ctx r hc)))
          (Omega.combineHolds env ctx hc ts))

theorem Omega.divideHolds (env: Omega.Env) (d: Nat) (r: Omega.Row) (ok: Omega.Row.divisible d r = True)
    (h: Omega.Row.Holds env r): Omega.Row.Holds env (Omega.Row.divide d r) :=
  match d, r with
    | Succ d, MkRow c ns is =>
      Int.divFloorNonneg d c
        (Omega.dot (Omega.divC d ns) (Omega.toInts (Omega.Env.nats env)) + Omega.dot (Omega.divC d is) (Omega.Env.ints env))
        (Omega.nonnegEq
          (Eq.cong (Int.add c)
            (Eq.sym (Eq.trans
              (Int.addCong
                (Omega.dotDiv d ns (Omega.toInts (Omega.Env.nats env)) (Bool.andLeft ok))
                (Omega.dotDiv d is (Omega.Env.ints env) (Bool.andRight ok)))
              (Eq.sym (Int.mulDistribLeft (OfNat (Succ d))
                (Omega.dot (Omega.divC d ns) (Omega.toInts (Omega.Env.nats env)))
                (Omega.dot (Omega.divC d is) (Omega.Env.ints env)))))))
          h)

theorem Omega.splitOtherHolds (env: Omega.Env) (l: Omega.Row) (h: Int.leq (OfNat 0) (Omega.Row.eval env l) = False):
    Omega.Row.Holds env (Omega.Row.splitOther l) :=
  Omega.nonnegEq (Omega.evalSub env (MkRow (NegSucc 0) [] []) l) (Int.negOneSubNonneg (Omega.Row.eval env l) h)

theorem Omega.contraVoid (env: Omega.Env) (r: Omega.Row) (ok: Omega.Row.isContra r = True) (h: Omega.Row.Holds env r): Void :=
  match r with
    | MkRow c ns is =>
      Int.notNonnegOfIsNeg c (Bool.andLeft ok)
        (Omega.nonnegEq
          (Eq.sym (Eq.trans
            (Eq.cong (Int.add c)
              (Int.addCong
                (Omega.dotAllZero ns (Omega.toInts (Omega.Env.nats env))
                  (Bool.andLeft (Bool.andRight ok)))
                (Omega.dotAllZero is (Omega.Env.ints env)
                  (Bool.andRight (Bool.andRight ok)))))
            (Int.addZero c)))
          h)

theorem Omega.stepHolds (env: Omega.Env) (facts: List Omega.Row) (neg: Option Omega.Row) (ctx: List Omega.Row)
    (hf: Omega.RowsHold env facts) (hn: Omega.OptHolds env neg) (hc: Omega.RowsHold env ctx)
    (s: Omega.Step) (ok: Omega.Step.valid facts neg ctx s = True): Omega.Row.Holds env (Omega.Step.row facts neg ctx s) :=
  match s with
    | Input i => Omega.getRowHolds env facts i hf
    | NegGoal => Omega.optRowHolds env neg hn
    | NatNonneg i => Omega.nonnegEq (Omega.linEval env (NV i)) rfl
    | Combine ts => Omega.combineHolds env ctx hc ts
    | Divide r d =>
      Omega.divideHolds env d (Omega.getRow ctx r)
        (Bool.andRight ok)
        (Omega.getRowHolds env ctx r hc)

--| A `Cases` step: the branch for the case that holds has its rows.
theorem Omega.casesHold (env: Omega.Env) (g: Omega.Fact) (hg: Omega.Fact.holds env g) (sp: Omega.Fact.splits g = True)
    (ctx: List Omega.Row) (hc: Omega.RowsHold env ctx)
    (kl: Omega.RowsHold env (List.append ctx (Omega.Facts.rows (Omega.Fact.left g))) → Void)
    (kr: Omega.RowsHold env (List.append ctx (Omega.Facts.rows (Omega.Fact.right g))) → Void): Void :=
  Omega.factCases env g hg sp
    (hl => kl (Omega.rowsAppend env ctx (Omega.Facts.rows (Omega.Fact.left g)) hc (Omega.factsRowsHold env (Omega.Fact.left g) hl)))
    (hr => kr (Omega.rowsAppend env ctx (Omega.Facts.rows (Omega.Fact.right g)) hc (Omega.factsRowsHold env (Omega.Fact.right g) hr)))

theorem Omega.checkCertSound (env: Omega.Env) (fs: List Omega.Fact) (facts: List Omega.Row) (neg: Option Omega.Row)
    (hfs: Omega.Facts.holds env fs) (hf: Omega.RowsHold env facts) (hn: Omega.OptHolds env neg)
    (cert: Omega.Cert) (ctx: List Omega.Row) (hc: Omega.RowsHold env ctx) (ok: Omega.checkCert fs facts neg ctx cert = True): Void :=
  match cert with
    | Close r => Omega.contraVoid env (Omega.getRow ctx r) ok (Omega.getRowHolds env ctx r hc)
    | Then s rest =>
      Omega.checkCertSound env fs facts neg hfs hf hn rest (List.append ctx [Omega.Step.row facts neg ctx s])
        (Omega.rowsAppend env ctx [Omega.Step.row facts neg ctx s] hc
          (Both (Omega.stepHolds env facts neg ctx hf hn hc s
            (Bool.andLeft ok)) Trivial))
        (Bool.andRight ok)
    | Split l left right =>
      Bool.inspect (Int.leq (OfNat 0) (Omega.Row.eval env l)) (b => Void)
        (e => Omega.checkCertSound env fs facts neg hfs hf hn left (List.append ctx [l])
          (Omega.rowsAppend env ctx [l] hc (Both e Trivial))
          (Bool.andLeft ok))
        (e => Omega.checkCertSound env fs facts neg hfs hf hn right (List.append ctx [Omega.Row.splitOther l])
          (Omega.rowsAppend env ctx [Omega.Row.splitOther l] hc (Both (Omega.splitOtherHolds env l e) Trivial))
          (Bool.andRight ok))
    | Cases f left right =>
      Omega.casesHold env (Omega.getFact fs f) (Omega.getFactHolds env fs f hfs)
        (Bool.andLeft ok)
        ctx hc
        (h => Omega.checkCertSound env fs facts neg hfs hf hn left (List.append ctx (Omega.Facts.rows (Omega.Fact.left (Omega.getFact fs f)))) h
          (Bool.andLeft (Bool.andRight
            ok)))
        (h => Omega.checkCertSound env fs facts neg hfs hf hn right (List.append ctx (Omega.Facts.rows (Omega.Fact.right (Omega.getFact fs f)))) h
          (Bool.andRight (Bool.andRight
            ok)))

--| Soundness: if `check` accepts, the facts imply the goal, in every environment.
theorem Omega.prove (env: Omega.Env) (facts: List Omega.Fact) (goal: Omega.Goal) (cert: Omega.Cert)
    (ok: Omega.check facts goal cert = True) (hs: Omega.Facts.holds env facts): Omega.Goal.holds env goal :=
  match goal with
    | GLe a b =>
      Bool.inspect (Nat.leq (Omega.NTerm.eval env a) (Omega.NTerm.eval env b)) (x => x = True) (e => rfl)
        (e => Void.exfalso (Omega.checkCertSound env facts (Omega.Facts.rows facts) (Some (Omega.leRow (NSucc b) a))
          hs (Omega.factsRowsHold env facts hs)
          (Omega.leRowHolds env (NSucc b) a (Nat.leqFalse (Omega.NTerm.eval env a) (Omega.NTerm.eval env b) e))
          cert [] Trivial ok))
    | GLt a b =>
      Bool.inspect (Nat.leq (Succ (Omega.NTerm.eval env a)) (Omega.NTerm.eval env b)) (x => x = True) (e => rfl)
        (e => Void.exfalso (Omega.checkCertSound env facts (Omega.Facts.rows facts) (Some (Omega.leRow b a))
          hs (Omega.factsRowsHold env facts hs)
          (Omega.leRowHolds env b a (Nat.leqFalse (Succ (Omega.NTerm.eval env a)) (Omega.NTerm.eval env b) e))
          cert [] Trivial ok))
    | GVoid =>
      Omega.checkCertSound env facts (Omega.Facts.rows facts) None hs (Omega.factsRowsHold env facts hs) Trivial cert [] Trivial ok
    | GILe a b =>
      Bool.inspect (Int.leq (Omega.ITerm.eval env a) (Omega.ITerm.eval env b)) (x => x = True) (e => rfl)
        (e => Void.exfalso (Omega.checkCertSound env facts (Omega.Facts.rows facts) (Some (Omega.ileRow (Omega.ITerm.succ b) a))
          hs (Omega.factsRowsHold env facts hs)
          (Omega.ileRowHolds env (Omega.ITerm.succ b) a (Omega.intLeqOfNotLeq (Omega.ITerm.eval env a) (Omega.ITerm.eval env b) e))
          cert [] Trivial ok))
    | GILt a b =>
      Bool.inspect (Int.less (Omega.ITerm.eval env a) (Omega.ITerm.eval env b)) (x => x = True) (e => rfl)
        (e => Void.exfalso (Omega.checkCertSound env facts (Omega.Facts.rows facts) (Some (Omega.ileRow b a))
          hs (Omega.factsRowsHold env facts hs)
          (Omega.ileRowHolds env b a (Omega.intLeqOfNotLess (Omega.ITerm.eval env a) (Omega.ITerm.eval env b) e))
          cert [] Trivial ok))
    | GINotLe a b =>
      Bool.inspect (Int.leq (Omega.ITerm.eval env a) (Omega.ITerm.eval env b)) (x => x = False)
        (e => Void.exfalso (Omega.checkCertSound env facts (Omega.Facts.rows facts) (Some (Omega.ileRow a b))
          hs (Omega.factsRowsHold env facts hs) (Omega.ileRowHolds env a b e) cert [] Trivial ok))
        (e => rfl)
    | GINotLt a b =>
      Bool.inspect (Int.less (Omega.ITerm.eval env a) (Omega.ITerm.eval env b)) (x => x = False)
        (e => Void.exfalso (Omega.checkCertSound env facts (Omega.Facts.rows facts) (Some (Omega.ileRow (Omega.ITerm.succ a) b))
          hs (Omega.factsRowsHold env facts hs)
          (Omega.ileRowHolds env (Omega.ITerm.succ a) b (Omega.intLeqOfLess (Omega.ITerm.eval env a) (Omega.ITerm.eval env b) e))
          cert [] Trivial ok))
        (e => rfl)

--| An equation, from two refutations.
theorem Omega.proveEq (env: Omega.Env) (facts: List Omega.Fact) (a: Omega.NTerm) (b: Omega.NTerm) (c1: Omega.Cert) (c2: Omega.Cert)
    (ok1: Omega.check facts (GLe a b) c1 = True) (ok2: Omega.check facts (GLe b a) c2 = True) (hs: Omega.Facts.holds env facts):
    Omega.NTerm.eval env a = Omega.NTerm.eval env b :=
  Nat.leAntisym (Omega.NTerm.eval env a) (Omega.NTerm.eval env b)
    (Omega.prove env facts (GLe a b) c1 ok1 hs) (Omega.prove env facts (GLe b a) c2 ok2 hs)

--| An equation on `Int`, from two refutations.
theorem Omega.proveIntEq (env: Omega.Env) (facts: List Omega.Fact) (a: Omega.ITerm) (b: Omega.ITerm) (c1: Omega.Cert) (c2: Omega.Cert)
    (ok1: Omega.check facts (GILe a b) c1 = True) (ok2: Omega.check facts (GILe b a) c2 = True) (hs: Omega.Facts.holds env facts):
    Omega.ITerm.eval env a = Omega.ITerm.eval env b :=
  Omega.intLeAntisym (Omega.ITerm.eval env a) (Omega.ITerm.eval env b)
    (Omega.prove env facts (GILe a b) c1 ok1 hs) (Omega.prove env facts (GILe b a) c2 ok2 hs)
