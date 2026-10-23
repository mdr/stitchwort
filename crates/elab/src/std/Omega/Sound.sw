-- The soundness of `Omega.check` (std/Omega/Omega.sw; docs/proposals/omega.md
-- §6.6): `Omega.prove` says that a certificate the checker accepts proves the
-- goal from the facts, for every environment, whatever the lengths of its
-- lists. Every lemma is about values at a given environment: no function or
-- propositional extensionality, no assumptions.

import Omega.Env (MkEnv)
import Omega.NTerm (NV, NLit, NAdd, NSucc, MulLeft, MulRight)
import Omega.Fact (FLe, FLt, FEq, FNotLe, FNotLt, FSub, FMax, FMin, FNe)
import Omega.Goal (GLe, GLt, GVoid)
import Omega.Row (MkRow)
import Omega.Step (Input, NegGoal, NatNonneg, Combine, Divide)
import Omega.Cert (Close, Then, Split, Cases)

-- Carrying `0 <= y` to `0 <= x` along `x = y`.
theorem Omega.nonnegEq [x y: Int] (e: x = y) (h: 0 <= y): 0 <= x := J (z p => Int.leq (OfNat 0) z = True) h (Eq.sym e)

theorem Omega.dotAdd: (as: List Int) -> (bs: List Int) -> (vs: List Int) ->
    Omega.dot (Omega.addC as bs) vs = Omega.dot as vs + Omega.dot bs vs
  | Nil, bs, vs => Eq.sym (Int.zeroAdd (Omega.dot bs vs))
  | Cons a as, Nil, vs => Eq.sym (Int.addZero (Omega.dot (Cons a as) vs))
  | Cons a as, Cons b bs, Nil => rfl
  | Cons a as, Cons b bs, Cons v vs =>
    Eq.trans (Int.addCong (Int.mulDistribRight a b v) (Omega.dotAdd as bs vs))
      (Int.addAddSwap (a * v) (b * v) (Omega.dot as vs) (Omega.dot bs vs))

theorem Omega.dotScale (k: Int): (as: List Int) -> (vs: List Int) -> Omega.dot (Omega.scaleC k as) vs = k * Omega.dot as vs
  | Nil, vs => Eq.sym (Int.mulZero k)
  | Cons a as, Nil => Eq.sym (Int.mulZero k)
  | Cons a as, Cons v vs =>
    Eq.trans (Int.addCong (Int.mulAssoc k a v) (Omega.dotScale k as vs))
      (Eq.sym (Int.mulDistribLeft k (a * v) (Omega.dot as vs)))

theorem Omega.dotUnit: (i: Nat) -> (ns: List Nat) -> Omega.dot (Omega.unit i) (Omega.toInts ns) = OfNat (Omega.natAt i ns)
  | Zero, Nil => rfl
  | Zero, Cons x xs => Eq.trans (Int.addZero (Int.mul (OfNat 1) (OfNat x))) (Int.oneMul (OfNat x))
  | Succ i, Nil => rfl
  | Succ i, Cons x xs => Eq.trans (Int.zeroAdd (Omega.dot (Omega.unit i) (Omega.toInts xs))) (Omega.dotUnit i xs)

theorem Omega.isZeroEq: (x: Int) -> Omega.isZero x = True -> x = OfNat 0
  | OfNat Zero, h => rfl
  | OfNat (Succ n), h => Void.exfalso (Bool.falseNotTrue h)
  | NegSucc n, h => Void.exfalso (Bool.falseNotTrue h)

theorem Omega.dotAllZero: (as: List Int) -> (vs: List Int) -> Omega.allZero as = True -> Omega.dot as vs = OfNat 0
  | Nil, vs, h => rfl
  | Cons a as, Nil, h => rfl
  | Cons a as, Cons v vs, h =>
    Int.addCong
      (Eq.trans (Eq.cong (t => Int.mul t v) (Omega.isZeroEq a (Bool.andLeft (Omega.isZero a) (Omega.allZero as) h))) (Int.zeroMul v))
      (Omega.dotAllZero as vs (Bool.andRight (Omega.isZero a) (Omega.allZero as) h))

-- A coefficient that `d` divides is `d` times its quotient.
theorem Omega.divExact (d: Nat) (a: Int) (h: Omega.isZero (a % OfNat (Succ d)) = True): a = OfNat (Succ d) * (a / OfNat (Succ d)) :=
  Eq.sym (Eq.trans (Eq.sym (Int.addZero (OfNat (Succ d) * (a / OfNat (Succ d)))))
    (Eq.trans (Eq.cong (Int.add (OfNat (Succ d) * (a / OfNat (Succ d)))) (Eq.sym (Omega.isZeroEq (a % OfNat (Succ d)) h)))
      (Int.divAddMod a (OfNat (Succ d)))))

theorem Omega.dotDiv (d: Nat): (as: List Int) -> (vs: List Int) -> Omega.allDiv d as = True ->
    Omega.dot as vs = OfNat (Succ d) * Omega.dot (Omega.divC d as) vs
  | Nil, vs, h => Eq.sym (Int.mulZero (OfNat (Succ d)))
  | Cons a as, Nil, h => Eq.sym (Int.mulZero (OfNat (Succ d)))
  | Cons a as, Cons v vs, h =>
    Eq.trans
      (Int.addCong
        (Eq.trans (Eq.cong (t => Int.mul t v) (Omega.divExact d a (Bool.andLeft (Omega.isZero (a % OfNat (Succ d))) (Omega.allDiv d as) h)))
          (Int.mulAssoc (OfNat (Succ d)) (a / OfNat (Succ d)) v))
        (Omega.dotDiv d as vs (Bool.andRight (Omega.isZero (a % OfNat (Succ d))) (Omega.allDiv d as) h)))
      (Eq.sym (Int.mulDistribLeft (OfNat (Succ d)) ((a / OfNat (Succ d)) * v) (Omega.dot (Omega.divC d as) vs)))

-- `(c + d) + ((x1 + x2) + (y1 + y2)) = (c + (x1 + y1)) + (d + (x2 + y2))`
theorem Omega.add3Swap (c: Int) (d: Int) (x1: Int) (x2: Int) (y1: Int) (y2: Int):
    (c + d) + ((x1 + x2) + (y1 + y2)) = (c + (x1 + y1)) + (d + (x2 + y2)) :=
  Eq.trans (Eq.cong (Int.add (c + d)) (Int.addAddSwap x1 x2 y1 y2))
    (Eq.sym (Int.addAddSwap c (x1 + y1) d (x2 + y2)))

theorem Omega.valueAdd (nv: List Int) (iv: List Int): (r: Omega.Row) -> (s: Omega.Row) ->
    Omega.Row.value nv iv (Omega.Row.add r s) = Omega.Row.value nv iv r + Omega.Row.value nv iv s
  | MkRow c ns is, MkRow d ms js =>
    Eq.trans (Eq.cong (Int.add (c + d)) (Int.addCong (Omega.dotAdd ns ms nv) (Omega.dotAdd is js iv)))
      (Omega.add3Swap c d (Omega.dot ns nv) (Omega.dot ms nv) (Omega.dot is iv) (Omega.dot js iv))

theorem Omega.valueScale (nv: List Int) (iv: List Int) (k: Int): (r: Omega.Row) ->
    Omega.Row.value nv iv (Omega.Row.scale k r) = k * Omega.Row.value nv iv r
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

-- `r - s` means `r` minus `s`.
theorem Omega.evalSub (env: Omega.Env) (r: Omega.Row) (s: Omega.Row):
    Omega.Row.eval env (Omega.Row.sub r s) = Omega.Row.eval env r + Int.neg (Omega.Row.eval env s) :=
  Eq.trans (Omega.evalAdd env r (Omega.Row.scale (NegSucc 0) s))
    (Eq.cong (Int.add (Omega.Row.eval env r))
      (Eq.trans (Omega.evalScale env (NegSucc 0) s) (Int.negOneMul (Omega.Row.eval env s))))

-- The linear form of a term means the term.
theorem Omega.linEval (env: Omega.Env): (t: Omega.NTerm) -> Omega.Row.eval env (Omega.NTerm.lin t) = OfNat (Omega.NTerm.eval env t)
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

-- The convention: `a <= b` gives the row `b - a >= 0`.
theorem Omega.leRowHolds (env: Omega.Env) (a: Omega.NTerm) (b: Omega.NTerm) (h: Omega.NTerm.eval env a <= Omega.NTerm.eval env b):
    Omega.Row.Holds env (Omega.leRow a b) :=
  Omega.nonnegEq
    (Eq.trans (Omega.evalSub env (Omega.NTerm.lin b) (Omega.NTerm.lin a))
      (Int.addCong (Omega.linEval env b) (Eq.cong Int.neg (Omega.linEval env a))))
    (Int.subNonnegOfLe (Omega.NTerm.eval env a) (Omega.NTerm.eval env b) h)

def Omega.RowsHold (env: Omega.Env): List Omega.Row -> Prop
  | Nil => Unit
  | Cons r rs => And (Omega.Row.Holds env r) (Omega.RowsHold env rs)

def Omega.OptHolds (env: Omega.Env): Option Omega.Row -> Prop
  | None => Unit
  | Some r => Omega.Row.Holds env r

theorem Omega.rowsAppend (env: Omega.Env): (xs: List Omega.Row) -> (ys: List Omega.Row) ->
    Omega.RowsHold env xs -> Omega.RowsHold env ys -> Omega.RowsHold env (List.append xs ys)
  | Nil, ys, hx, hy => hy
  | Cons x xs, ys, Both h hs, hy => Both h (Omega.rowsAppend env xs ys hs hy)

theorem Omega.getRowHolds (env: Omega.Env): (rs: List Omega.Row) -> (i: Nat) -> Omega.RowsHold env rs -> Omega.Row.Holds env (Omega.getRow rs i)
  | Nil, i, h => rfl
  | Cons r rs, Zero, Both h hs => h
  | Cons r rs, Succ i, Both h hs => Omega.getRowHolds env rs i hs

theorem Omega.optRowHolds (env: Omega.Env): (o: Option Omega.Row) -> Omega.OptHolds env o -> Omega.Row.Holds env (Omega.optRow o)
  | None, h => rfl
  | Some r, h => h

-- The operation facts (stage 2), about plain numbers: what always holds, then
-- the two cases.

-- `a <= (a - b) + b`, whichever of `a` and `b` is larger.
theorem Omega.leSubAdd: (a: Nat) -> (b: Nat) -> a <= (a - b) + b
  | a, Zero => Nat.leAddRight a 0
  | Zero, Succ b => rfl
  | Succ a, Succ b =>
    Nat.leCongRight (Succ a) (Succ ((a - b) + b)) ((a - b) + Succ b) (Eq.sym (Nat.addSucc (a - b) b)) (Omega.leSubAdd a b)

theorem Omega.subLeLeft (t: Nat) (a: Nat) (b: Nat) (h: t = a - b): t <= a :=
  Nat.leCongLeft (a - b) t a (Eq.sym h) (Nat.subLe a b)

theorem Omega.subLeAdd (t: Nat) (a: Nat) (b: Nat) (h: t = a - b): a <= t + b :=
  Nat.leCongRight a ((a - b) + b) (t + b) (Eq.cong (x => x + b) (Eq.sym h)) (Omega.leSubAdd a b)

theorem Omega.subCases (t: Nat) (a: Nat) (b: Nat) (h: t = a - b)
    (kl: And (b <= a) (And (t + b = a) Unit) -> Void) (kr: And (a < b) (And (t = 0) Unit) -> Void): Void :=
  Bool.inspect (Nat.leq b a) (x => Void)
    (e => kl (Both e (Both (Eq.trans (Eq.cong (x => x + b) h) (Eq.trans (Nat.addComm (a - b) b) (Nat.addSubCancel b a e))) Trivial)))
    (e => kr (Both (Nat.leqFalse b a e) (Both (Eq.trans h (Nat.subEqZero a b (Nat.lessLe a b (Nat.leqFalse b a e)))) Trivial)))

theorem Omega.maxCases (t: Nat) (a: Nat) (b: Nat) (h: t = Nat.max a b)
    (kl: And (a <= b) (And (t = b) Unit) -> Void) (kr: And (b < a) (And (t = a) Unit) -> Void): Void :=
  Bool.inspect (Nat.leq a b) (x => Void)
    (e => kl (Both e (Both (Eq.trans h (Nat.maxRight a b e)) Trivial)))
    (e => kr (Both (Nat.leqFalse a b e) (Both (Eq.trans h (Nat.maxLeft a b (Nat.lessLe b a (Nat.leqFalse a b e)))) Trivial)))

theorem Omega.minCases (t: Nat) (a: Nat) (b: Nat) (h: t = Nat.min a b)
    (kl: And (a <= b) (And (t = a) Unit) -> Void) (kr: And (b < a) (And (t = b) Unit) -> Void): Void :=
  Bool.inspect (Nat.leq a b) (x => Void)
    (e => kl (Both e (Both (Eq.trans h (Nat.minLeft a b e)) Trivial)))
    (e => kr (Both (Nat.leqFalse a b e) (Both (Eq.trans h (Nat.minRight a b e)) Trivial)))

theorem Omega.neCases (a: Nat) (b: Nat) (h: Not (a = b))
    (kl: And (a < b) Unit -> Void) (kr: And (b < a) Unit -> Void): Void :=
  Bool.inspect (Nat.leq (Succ a) b) (x => Void)
    (e => kl (Both e Trivial))
    (e => kr (Both (Nat.leNeSucc b a (Nat.leqFalse (Succ a) b e) (p => h (Eq.sym p))) Trivial))

theorem Omega.factRowsHold (env: Omega.Env): (f: Omega.Fact) -> Omega.Fact.holds env f -> Omega.RowsHold env (Omega.Fact.rows f)
  | FLe a b, h => Both (Omega.leRowHolds env a b h) Trivial
  | FLt a b, h => Both (Omega.leRowHolds env (NSucc a) b h) Trivial
  | FEq a b, h =>
    Both (Omega.leRowHolds env a b (Nat.leOfEq (Omega.NTerm.eval env a) (Omega.NTerm.eval env b) h))
      (Both (Omega.leRowHolds env b a (Nat.leOfEq (Omega.NTerm.eval env b) (Omega.NTerm.eval env a) (Eq.sym h))) Trivial)
  | FNotLe a b, h => Both (Omega.leRowHolds env (NSucc b) a (Nat.ltOfNotLe (Omega.NTerm.eval env a) (Omega.NTerm.eval env b) h)) Trivial
  | FNotLt a b, h => Both (Omega.leRowHolds env b a (Nat.leOfNotLt (Omega.NTerm.eval env a) (Omega.NTerm.eval env b) h)) Trivial
  | FSub t a b, h =>
    Both (Omega.leRowHolds env t a (Omega.subLeLeft (Omega.NTerm.eval env t) (Omega.NTerm.eval env a) (Omega.NTerm.eval env b) h))
      (Both (Omega.leRowHolds env a (NAdd t b) (Omega.subLeAdd (Omega.NTerm.eval env t) (Omega.NTerm.eval env a) (Omega.NTerm.eval env b) h)) Trivial)
  | FMax t a b, h =>
    Both (Omega.leRowHolds env a t (Nat.leCongRight (Omega.NTerm.eval env a) (Nat.max (Omega.NTerm.eval env a) (Omega.NTerm.eval env b)) (Omega.NTerm.eval env t) (Eq.sym h)
        (Nat.leMaxLeft (Omega.NTerm.eval env a) (Omega.NTerm.eval env b))))
      (Both (Omega.leRowHolds env b t (Nat.leCongRight (Omega.NTerm.eval env b) (Nat.max (Omega.NTerm.eval env a) (Omega.NTerm.eval env b)) (Omega.NTerm.eval env t) (Eq.sym h)
        (Nat.leMaxRight (Omega.NTerm.eval env a) (Omega.NTerm.eval env b)))) Trivial)
  | FMin t a b, h =>
    Both (Omega.leRowHolds env t a (Nat.leCongLeft (Nat.min (Omega.NTerm.eval env a) (Omega.NTerm.eval env b)) (Omega.NTerm.eval env t) (Omega.NTerm.eval env a) (Eq.sym h)
        (Nat.minLeLeft (Omega.NTerm.eval env a) (Omega.NTerm.eval env b))))
      (Both (Omega.leRowHolds env t b (Nat.leCongLeft (Nat.min (Omega.NTerm.eval env a) (Omega.NTerm.eval env b)) (Omega.NTerm.eval env t) (Omega.NTerm.eval env b) (Eq.sym h)
        (Nat.minLeRight (Omega.NTerm.eval env a) (Omega.NTerm.eval env b)))) Trivial)
  | FNe a b, h => Trivial

-- A fact with cases holds in one of them.
theorem Omega.factCases (env: Omega.Env): (f: Omega.Fact) -> Omega.Fact.holds env f -> Omega.Fact.splits f = True ->
    (Omega.Facts.holds env (Omega.Fact.left f) -> Void) -> (Omega.Facts.holds env (Omega.Fact.right f) -> Void) -> Void
  | FLe a b, h, ok, kl, kr => Bool.falseNotTrue ok
  | FLt a b, h, ok, kl, kr => Bool.falseNotTrue ok
  | FEq a b, h, ok, kl, kr => Bool.falseNotTrue ok
  | FNotLe a b, h, ok, kl, kr => Bool.falseNotTrue ok
  | FNotLt a b, h, ok, kl, kr => Bool.falseNotTrue ok
  | FSub t a b, h, ok, kl, kr => Omega.subCases (Omega.NTerm.eval env t) (Omega.NTerm.eval env a) (Omega.NTerm.eval env b) h kl kr
  | FMax t a b, h, ok, kl, kr => Omega.maxCases (Omega.NTerm.eval env t) (Omega.NTerm.eval env a) (Omega.NTerm.eval env b) h kl kr
  | FMin t a b, h, ok, kl, kr => Omega.minCases (Omega.NTerm.eval env t) (Omega.NTerm.eval env a) (Omega.NTerm.eval env b) h kl kr
  | FNe a b, h, ok, kl, kr => Omega.neCases (Omega.NTerm.eval env a) (Omega.NTerm.eval env b) h kl kr

theorem Omega.factsRowsHold (env: Omega.Env): (fs: List Omega.Fact) -> Omega.Facts.holds env fs -> Omega.RowsHold env (Omega.Facts.rows fs)
  | Nil, h => Trivial
  | Cons f fs, Both h hs =>
    Omega.rowsAppend env (Omega.Fact.rows f) (Omega.Facts.rows fs) (Omega.factRowsHold env f h) (Omega.factsRowsHold env fs hs)

theorem Omega.getFactHolds (env: Omega.Env): (fs: List Omega.Fact) -> (i: Nat) -> Omega.Facts.holds env fs -> Omega.Fact.holds env (Omega.getFact fs i)
  | Nil, i, h => rfl
  | Cons f fs, Zero, Both h hs => h
  | Cons f fs, Succ i, Both h hs => Omega.getFactHolds env fs i hs

theorem Omega.combineHolds (env: Omega.Env) (ctx: List Omega.Row) (hc: Omega.RowsHold env ctx):
    (ts: List (Pair Nat Nat)) -> Omega.Row.Holds env (Omega.combine ctx ts)
  | Nil => rfl
  | Cons (MkPair k r) ts =>
    Omega.nonnegEq (Omega.evalAdd env (Omega.Row.scale (OfNat k) (Omega.getRow ctx r)) (Omega.combine ctx ts))
      (Int.addNonneg (Omega.Row.eval env (Omega.Row.scale (OfNat k) (Omega.getRow ctx r))) (Omega.Row.eval env (Omega.combine ctx ts))
        (Omega.nonnegEq (Omega.evalScale env (OfNat k) (Omega.getRow ctx r))
          (Int.mulNonneg (OfNat k) (Omega.Row.eval env (Omega.getRow ctx r)) rfl (Omega.getRowHolds env ctx r hc)))
        (Omega.combineHolds env ctx hc ts))

theorem Omega.divideHolds (env: Omega.Env): (d: Nat) -> (r: Omega.Row) -> Omega.Row.divisible d r = True ->
    Omega.Row.Holds env r -> Omega.Row.Holds env (Omega.Row.divide d r)
  | Zero, r, ok, h => Void.exfalso (Bool.falseNotTrue ok)
  | Succ d, MkRow c ns is, ok, h =>
    Int.divFloorNonneg d c
      (Omega.dot (Omega.divC d ns) (Omega.toInts (Omega.Env.nats env)) + Omega.dot (Omega.divC d is) (Omega.Env.ints env))
      (Omega.nonnegEq
        (Eq.cong (Int.add c)
          (Eq.sym (Eq.trans
            (Int.addCong
              (Omega.dotDiv d ns (Omega.toInts (Omega.Env.nats env)) (Bool.andLeft (Omega.allDiv d ns) (Omega.allDiv d is) ok))
              (Omega.dotDiv d is (Omega.Env.ints env) (Bool.andRight (Omega.allDiv d ns) (Omega.allDiv d is) ok)))
            (Eq.sym (Int.mulDistribLeft (OfNat (Succ d))
              (Omega.dot (Omega.divC d ns) (Omega.toInts (Omega.Env.nats env)))
              (Omega.dot (Omega.divC d is) (Omega.Env.ints env)))))))
        h)

theorem Omega.splitOtherHolds (env: Omega.Env) (l: Omega.Row) (h: Int.leq (OfNat 0) (Omega.Row.eval env l) = False):
    Omega.Row.Holds env (Omega.Row.splitOther l) :=
  Omega.nonnegEq (Omega.evalSub env (MkRow (NegSucc 0) Nil Nil) l) (Int.negOneSubNonneg (Omega.Row.eval env l) h)

theorem Omega.contraVoid (env: Omega.Env): (r: Omega.Row) -> Omega.Row.isContra r = True -> Omega.Row.Holds env r -> Void
  | MkRow c ns is, ok, h =>
    Int.notNonnegOfIsNeg c (Bool.andLeft (Int.isNeg c) (Omega.allZero ns && Omega.allZero is) ok)
      (Omega.nonnegEq
        (Eq.sym (Eq.trans
          (Eq.cong (Int.add c)
            (Int.addCong
              (Omega.dotAllZero ns (Omega.toInts (Omega.Env.nats env))
                (Bool.andLeft (Omega.allZero ns) (Omega.allZero is) (Bool.andRight (Int.isNeg c) (Omega.allZero ns && Omega.allZero is) ok)))
              (Omega.dotAllZero is (Omega.Env.ints env)
                (Bool.andRight (Omega.allZero ns) (Omega.allZero is) (Bool.andRight (Int.isNeg c) (Omega.allZero ns && Omega.allZero is) ok)))))
          (Int.addZero c)))
        h)

theorem Omega.stepHolds (env: Omega.Env) (facts: List Omega.Row) (neg: Option Omega.Row) (ctx: List Omega.Row)
    (hf: Omega.RowsHold env facts) (hn: Omega.OptHolds env neg) (hc: Omega.RowsHold env ctx):
    (s: Omega.Step) -> Omega.Step.valid facts neg ctx s = True -> Omega.Row.Holds env (Omega.Step.row facts neg ctx s)
  | Input i, ok => Omega.getRowHolds env facts i hf
  | NegGoal, ok => Omega.optRowHolds env neg hn
  | NatNonneg i, ok => Omega.nonnegEq (Omega.linEval env (NV i)) rfl
  | Combine ts, ok => Omega.combineHolds env ctx hc ts
  | Divide r d, ok =>
    Omega.divideHolds env d (Omega.getRow ctx r)
      (Bool.andRight (Omega.hasRow ctx r) (Omega.Row.divisible d (Omega.getRow ctx r)) ok)
      (Omega.getRowHolds env ctx r hc)

-- A `Cases` step: the branch for the case that holds has its rows.
theorem Omega.casesHold (env: Omega.Env) (g: Omega.Fact) (hg: Omega.Fact.holds env g) (sp: Omega.Fact.splits g = True)
    (ctx: List Omega.Row) (hc: Omega.RowsHold env ctx)
    (kl: Omega.RowsHold env (List.append ctx (Omega.Facts.rows (Omega.Fact.left g))) -> Void)
    (kr: Omega.RowsHold env (List.append ctx (Omega.Facts.rows (Omega.Fact.right g))) -> Void): Void :=
  Omega.factCases env g hg sp
    (hl => kl (Omega.rowsAppend env ctx (Omega.Facts.rows (Omega.Fact.left g)) hc (Omega.factsRowsHold env (Omega.Fact.left g) hl)))
    (hr => kr (Omega.rowsAppend env ctx (Omega.Facts.rows (Omega.Fact.right g)) hc (Omega.factsRowsHold env (Omega.Fact.right g) hr)))

theorem Omega.checkCertSound (env: Omega.Env) (fs: List Omega.Fact) (facts: List Omega.Row) (neg: Option Omega.Row)
    (hfs: Omega.Facts.holds env fs) (hf: Omega.RowsHold env facts) (hn: Omega.OptHolds env neg):
    (cert: Omega.Cert) -> (ctx: List Omega.Row) -> Omega.RowsHold env ctx -> Omega.checkCert fs facts neg ctx cert = True -> Void
  | Close r, ctx, hc, ok => Omega.contraVoid env (Omega.getRow ctx r) ok (Omega.getRowHolds env ctx r hc)
  | Then s rest, ctx, hc, ok =>
    Omega.checkCertSound env fs facts neg hfs hf hn rest (List.append ctx [Omega.Step.row facts neg ctx s])
      (Omega.rowsAppend env ctx [Omega.Step.row facts neg ctx s] hc
        (Both (Omega.stepHolds env facts neg ctx hf hn hc s
          (Bool.andLeft (Omega.Step.valid facts neg ctx s) (Omega.checkCert fs facts neg (List.append ctx [Omega.Step.row facts neg ctx s]) rest) ok)) Trivial))
      (Bool.andRight (Omega.Step.valid facts neg ctx s) (Omega.checkCert fs facts neg (List.append ctx [Omega.Step.row facts neg ctx s]) rest) ok)
  | Split l left right, ctx, hc, ok =>
    Bool.inspect (Int.leq (OfNat 0) (Omega.Row.eval env l)) (b => Void)
      (e => Omega.checkCertSound env fs facts neg hfs hf hn left (List.append ctx [l])
        (Omega.rowsAppend env ctx [l] hc (Both e Trivial))
        (Bool.andLeft (Omega.checkCert fs facts neg (List.append ctx [l]) left) (Omega.checkCert fs facts neg (List.append ctx [Omega.Row.splitOther l]) right) ok))
      (e => Omega.checkCertSound env fs facts neg hfs hf hn right (List.append ctx [Omega.Row.splitOther l])
        (Omega.rowsAppend env ctx [Omega.Row.splitOther l] hc (Both (Omega.splitOtherHolds env l e) Trivial))
        (Bool.andRight (Omega.checkCert fs facts neg (List.append ctx [l]) left) (Omega.checkCert fs facts neg (List.append ctx [Omega.Row.splitOther l]) right) ok))
  | Cases f left right, ctx, hc, ok =>
    Omega.casesHold env (Omega.getFact fs f) (Omega.getFactHolds env fs f hfs)
      (Bool.andLeft (Omega.Fact.splits (Omega.getFact fs f))
        (Omega.checkCert fs facts neg (List.append ctx (Omega.Facts.rows (Omega.Fact.left (Omega.getFact fs f)))) left
          && Omega.checkCert fs facts neg (List.append ctx (Omega.Facts.rows (Omega.Fact.right (Omega.getFact fs f)))) right) ok)
      ctx hc
      (h => Omega.checkCertSound env fs facts neg hfs hf hn left (List.append ctx (Omega.Facts.rows (Omega.Fact.left (Omega.getFact fs f)))) h
        (Bool.andLeft
          (Omega.checkCert fs facts neg (List.append ctx (Omega.Facts.rows (Omega.Fact.left (Omega.getFact fs f)))) left)
          (Omega.checkCert fs facts neg (List.append ctx (Omega.Facts.rows (Omega.Fact.right (Omega.getFact fs f)))) right)
          (Bool.andRight (Omega.Fact.splits (Omega.getFact fs f))
            (Omega.checkCert fs facts neg (List.append ctx (Omega.Facts.rows (Omega.Fact.left (Omega.getFact fs f)))) left
              && Omega.checkCert fs facts neg (List.append ctx (Omega.Facts.rows (Omega.Fact.right (Omega.getFact fs f)))) right) ok)))
      (h => Omega.checkCertSound env fs facts neg hfs hf hn right (List.append ctx (Omega.Facts.rows (Omega.Fact.right (Omega.getFact fs f)))) h
        (Bool.andRight
          (Omega.checkCert fs facts neg (List.append ctx (Omega.Facts.rows (Omega.Fact.left (Omega.getFact fs f)))) left)
          (Omega.checkCert fs facts neg (List.append ctx (Omega.Facts.rows (Omega.Fact.right (Omega.getFact fs f)))) right)
          (Bool.andRight (Omega.Fact.splits (Omega.getFact fs f))
            (Omega.checkCert fs facts neg (List.append ctx (Omega.Facts.rows (Omega.Fact.left (Omega.getFact fs f)))) left
              && Omega.checkCert fs facts neg (List.append ctx (Omega.Facts.rows (Omega.Fact.right (Omega.getFact fs f)))) right) ok)))

-- Soundness: if `check` accepts, the facts imply the goal, in every environment.
theorem Omega.prove (env: Omega.Env) (facts: List Omega.Fact): (goal: Omega.Goal) -> (cert: Omega.Cert) ->
    Omega.check facts goal cert = True -> Omega.Facts.holds env facts -> Omega.Goal.holds env goal
  | GLe a b, cert, ok, hs =>
    Bool.inspect (Nat.leq (Omega.NTerm.eval env a) (Omega.NTerm.eval env b)) (x => x = True) (e => rfl)
      (e => Void.exfalso (Omega.checkCertSound env facts (Omega.Facts.rows facts) (Some (Omega.leRow (NSucc b) a))
        hs (Omega.factsRowsHold env facts hs)
        (Omega.leRowHolds env (NSucc b) a (Nat.leqFalse (Omega.NTerm.eval env a) (Omega.NTerm.eval env b) e))
        cert Nil Trivial ok))
  | GLt a b, cert, ok, hs =>
    Bool.inspect (Nat.leq (Succ (Omega.NTerm.eval env a)) (Omega.NTerm.eval env b)) (x => x = True) (e => rfl)
      (e => Void.exfalso (Omega.checkCertSound env facts (Omega.Facts.rows facts) (Some (Omega.leRow b a))
        hs (Omega.factsRowsHold env facts hs)
        (Omega.leRowHolds env b a (Nat.leqFalse (Succ (Omega.NTerm.eval env a)) (Omega.NTerm.eval env b) e))
        cert Nil Trivial ok))
  | GVoid, cert, ok, hs =>
    Omega.checkCertSound env facts (Omega.Facts.rows facts) None hs (Omega.factsRowsHold env facts hs) Trivial cert Nil Trivial ok

-- An equation, from two refutations.
theorem Omega.proveEq (env: Omega.Env) (facts: List Omega.Fact) (a: Omega.NTerm) (b: Omega.NTerm) (c1: Omega.Cert) (c2: Omega.Cert)
    (ok1: Omega.check facts (GLe a b) c1 = True) (ok2: Omega.check facts (GLe b a) c2 = True) (hs: Omega.Facts.holds env facts):
    Omega.NTerm.eval env a = Omega.NTerm.eval env b :=
  Nat.leAntisym (Omega.NTerm.eval env a) (Omega.NTerm.eval env b)
    (Omega.prove env facts (GLe a b) c1 ok1 hs) (Omega.prove env facts (GLe b a) c2 ok2 hs)
