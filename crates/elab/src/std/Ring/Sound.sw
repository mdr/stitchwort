-- The soundness of `Std.Ring` (std/Ring/Ring.sw; docs/proposals/proof-automation.md
-- §6.2): a polynomial's normal form means the same as the polynomial, in
-- every environment (`Ring.NExpr.sound`, `Ring.ZExpr.sound`), so two sides
-- with the same normal form are equal (`Ring.proveNat`, `Ring.proveInt`), and
-- with hypotheses added to the other side, equal once they are cancelled
-- (`Ring.proveNatWith`, `Ring.proveIntWith`). It uses `Int`'s ring laws and
-- nothing about lists from the library: soundness doesn't need the normal
-- form to be sorted, only that monomials `Ring.cmp` calls alike are.

import Ring.Env (MkEnv)
import Ring.NExpr (NAtom, NNum, NAdd, NMul, NSucc)
import Ring.ZExpr (ZAtom, ZNum, ZAdd, ZMul, ZNeg, ZSub, ZOfNat, ZNegSucc)
import Ring.Mono (MkMono)

-- Rearranging sums and products

theorem Ring.addLeftComm (a: Int) (b: Int) (c: Int): Int.add a (Int.add b c) = Int.add b (Int.add a c) :=
  Eq.trans (Eq.sym (Int.addAssoc a b c))
    (Eq.trans (Eq.cong (t => Int.add t c) (Int.addComm a b)) (Int.addAssoc b a c))

theorem Ring.mulLeftComm (a: Int) (b: Int) (c: Int): Int.mul a (Int.mul b c) = Int.mul b (Int.mul a c) :=
  Eq.trans (Eq.sym (Int.mulAssoc a b c))
    (Eq.trans (Eq.cong (t => Int.mul t c) (Int.mulComm a b)) (Int.mulAssoc b a c))

theorem Ring.mulMulSwap (a: Int) (b: Int) (c: Int) (d: Int):
    Int.mul (Int.mul a b) (Int.mul c d) = Int.mul (Int.mul a c) (Int.mul b d) :=
  Eq.trans (Int.mulAssoc a b (Int.mul c d))
    (Eq.trans (Eq.cong (Int.mul a) (Ring.mulLeftComm b c d)) (Eq.sym (Int.mulAssoc a c (Int.mul b d))))

theorem Ring.addNegCancel (a: Int) (c: Int): Int.add (Int.add a c) (Int.neg c) = a :=
  Eq.trans (Int.addAssoc a c (Int.neg c)) (Eq.trans (Eq.cong (Int.add a) (Int.addNeg c)) (Int.addZero a))

theorem Ring.addRightCancel (a: Int) (b: Int) (c: Int) (h: Int.add a c = Int.add b c): a = b :=
  Eq.trans (Eq.sym (Ring.addNegCancel a c))
    (Eq.trans (Eq.cong (t => Int.add t (Int.neg c)) h) (Ring.addNegCancel b c))

theorem Ring.natAddRightCancel (a: Nat) (b: Nat) (c: Nat) (h: a + c = b + c): a = b :=
  Int.ofNatInjective a b (Ring.addRightCancel (OfNat a) (OfNat b) (OfNat c) (Eq.cong OfNat h))

theorem Ring.natAddOne (n: Nat): n + 1 = Succ n := Eq.trans (Nat.addSucc n 0) (Eq.cong Succ (Nat.addZero n))

-- Variables

theorem Ring.lookupNat: (i: Nat) -> (ns: List Nat) -> (is: List Int) -> Ring.lookup ns is (Ring.twice i) = OfNat (Ring.natAt ns i)
  | Zero, ns, is => rfl
  | Succ i, Nil, is => Ring.lookupNat i Nil (Ring.intTail is)
  | Succ i, Cons n ns, is => Ring.lookupNat i ns (Ring.intTail is)

theorem Ring.lookupInt: (j: Nat) -> (ns: List Nat) -> (is: List Int) -> Ring.lookup ns is (Succ (Ring.twice j)) = Ring.intAt is j
  | Zero, ns, is => rfl
  | Succ j, ns, Nil => Ring.lookupInt j (Ring.natTail ns) Nil
  | Succ j, ns, Cons x xs => Ring.lookupInt j (Ring.natTail ns) xs

theorem Ring.prodInsertVar (env: Ring.Env) (v: Nat): (ws: List Nat) ->
    Ring.prod env (Ring.insertVar v ws) = Int.mul (Ring.var env v) (Ring.prod env ws)
  | Nil => rfl
  | Cons w ws =>
    match h: Nat.leq v w with
      | True => rfl
      | False =>
        Eq.trans (Eq.cong (Int.mul (Ring.var env w)) (Ring.prodInsertVar env v ws))
          (Ring.mulLeftComm (Ring.var env w) (Ring.var env v) (Ring.prod env ws))

theorem Ring.prodMulVars (env: Ring.Env): (vs: List Nat) -> (ws: List Nat) ->
    Ring.prod env (Ring.mulVars vs ws) = Int.mul (Ring.prod env vs) (Ring.prod env ws)
  | Nil, ws => Eq.sym (Int.oneMul (Ring.prod env ws))
  | Cons v vs, ws =>
    Eq.trans (Ring.prodInsertVar env v (Ring.mulVars vs ws))
      (Eq.trans (Eq.cong (Int.mul (Ring.var env v)) (Ring.prodMulVars env vs ws))
        (Eq.sym (Int.mulAssoc (Ring.var env v) (Ring.prod env vs) (Ring.prod env ws))))

-- Monomials `Ring.cmp` calls alike have the same variables.

def Ring.isEqual: Ordering -> Bool
  | Less => False
  | Equal => True
  | Greater => False

theorem Ring.lessNotEqual (h: Less = Equal): Void := Bool.falseNotTrue (Eq.cong Ring.isEqual h)

theorem Ring.greaterNotEqual (h: Greater = Equal): Void := Bool.falseNotTrue (Eq.cong Ring.isEqual h)

theorem Ring.cmpEq: (vs: List Nat) -> (ws: List Nat) -> Ring.cmp vs ws = Equal -> vs = ws
  | Nil, Nil, h => rfl
  | Nil, Cons w ws, h => Void.exfalso (Ring.lessNotEqual h)
  | Cons v vs, Nil, h => Void.exfalso (Ring.greaterNotEqual h)
  | Cons v vs, Cons w ws, h =>
    match e: Nat.equal v w with
      | True => Eq.trans (Eq.cong (t => Cons t vs) (Nat.equalSound v w e)) (Eq.cong (Cons w) (Ring.cmpEq vs ws h))
      | False =>
        match f: Nat.leq v w with
          | True => Void.exfalso (Ring.lessNotEqual h)
          | False => Void.exfalso (Ring.greaterNotEqual h)

-- Polynomials

theorem Ring.evalCons (env: Ring.Env): (c: Int) -> (vs: List Nat) -> (p: List Ring.Mono) ->
    Ring.Poly.eval env (Ring.cons c vs p) = Int.add (Int.mul c (Ring.prod env vs)) (Ring.Poly.eval env p)
  | OfNat Zero, vs, p =>
    Eq.sym (Eq.trans (Eq.cong (t => Int.add t (Ring.Poly.eval env p)) (Int.zeroMul (Ring.prod env vs))) (Int.zeroAdd (Ring.Poly.eval env p)))
  | OfNat (Succ n), vs, p => rfl
  | NegSucc n, vs, p => rfl

theorem Ring.evalInsert (env: Ring.Env) (c: Int) (vs: List Nat): (p: List Ring.Mono) ->
    Ring.Poly.eval env (Ring.insert c vs p) = Int.add (Int.mul c (Ring.prod env vs)) (Ring.Poly.eval env p)
  | Nil => Ring.evalCons env c vs Nil
  | Cons (MkMono d ws) p =>
    match h: Ring.cmp vs ws with
      | Less => Ring.evalCons env c vs (Cons (MkMono d ws) p)
      | Equal =>
        Eq.trans (Ring.evalCons env (Int.add c d) ws p)
          (Eq.trans (Eq.cong (t => Int.add t (Ring.Poly.eval env p)) (Int.mulDistribRight c d (Ring.prod env ws)))
            (Eq.trans (Int.addAssoc (Int.mul c (Ring.prod env ws)) (Int.mul d (Ring.prod env ws)) (Ring.Poly.eval env p))
              (Eq.cong (t => Int.add (Int.mul c (Ring.prod env t)) (Int.add (Int.mul d (Ring.prod env ws)) (Ring.Poly.eval env p)))
                (Eq.sym (Ring.cmpEq vs ws h)))))
      | Greater =>
        Eq.trans (Eq.cong (Int.add (Int.mul d (Ring.prod env ws))) (Ring.evalInsert env c vs p))
          (Ring.addLeftComm (Int.mul d (Ring.prod env ws)) (Int.mul c (Ring.prod env vs)) (Ring.Poly.eval env p))

theorem Ring.evalAdd (env: Ring.Env): (p: List Ring.Mono) -> (q: List Ring.Mono) ->
    Ring.Poly.eval env (Ring.add p q) = Int.add (Ring.Poly.eval env p) (Ring.Poly.eval env q)
  | Nil, q => Eq.sym (Int.zeroAdd (Ring.Poly.eval env q))
  | Cons (MkMono c vs) p, q =>
    Eq.trans (Ring.evalInsert env c vs (Ring.add p q))
      (Eq.trans (Eq.cong (Int.add (Int.mul c (Ring.prod env vs))) (Ring.evalAdd env p q))
        (Eq.sym (Int.addAssoc (Int.mul c (Ring.prod env vs)) (Ring.Poly.eval env p) (Ring.Poly.eval env q))))

theorem Ring.evalScale (env: Ring.Env) (c: Int) (vs: List Nat): (q: List Ring.Mono) ->
    Ring.Poly.eval env (Ring.scale c vs q) = Int.mul (Int.mul c (Ring.prod env vs)) (Ring.Poly.eval env q)
  | Nil => Eq.sym (Int.mulZero (Int.mul c (Ring.prod env vs)))
  | Cons (MkMono d ws) q =>
    Eq.trans (Ring.evalInsert env (Int.mul c d) (Ring.mulVars vs ws) (Ring.scale c vs q))
      (Eq.trans
        (Eq.cong (t => Int.add t (Ring.Poly.eval env (Ring.scale c vs q)))
          (Eq.trans (Eq.cong (Int.mul (Int.mul c d)) (Ring.prodMulVars env vs ws))
            (Ring.mulMulSwap c d (Ring.prod env vs) (Ring.prod env ws))))
        (Eq.trans (Eq.cong (Int.add (Int.mul (Int.mul c (Ring.prod env vs)) (Int.mul d (Ring.prod env ws)))) (Ring.evalScale env c vs q))
          (Eq.sym (Int.mulDistribLeft (Int.mul c (Ring.prod env vs)) (Int.mul d (Ring.prod env ws)) (Ring.Poly.eval env q)))))

theorem Ring.evalMul (env: Ring.Env): (p: List Ring.Mono) -> (q: List Ring.Mono) ->
    Ring.Poly.eval env (Ring.mul p q) = Int.mul (Ring.Poly.eval env p) (Ring.Poly.eval env q)
  | Nil, q => Eq.sym (Int.zeroMul (Ring.Poly.eval env q))
  | Cons (MkMono c vs) p, q =>
    Eq.trans (Ring.evalAdd env (Ring.scale c vs q) (Ring.mul p q))
      (Eq.trans (Int.addCong (Ring.evalScale env c vs q) (Ring.evalMul env p q))
        (Eq.sym (Int.mulDistribRight (Int.mul c (Ring.prod env vs)) (Ring.Poly.eval env p) (Ring.Poly.eval env q))))

theorem Ring.evalNeg (env: Ring.Env) (p: List Ring.Mono): Ring.Poly.eval env (Ring.neg p) = Int.neg (Ring.Poly.eval env p) :=
  Eq.trans (Ring.evalScale env (NegSucc 0) Nil p) (Int.negOneMul (Ring.Poly.eval env p))

theorem Ring.evalConst (env: Ring.Env) (c: Int): Ring.Poly.eval env (Ring.const c) = c :=
  Eq.trans (Ring.evalCons env c Nil Nil) (Eq.trans (Int.addZero (Int.mul c (OfNat 1))) (Int.mulOne c))

theorem Ring.evalSingle (env: Ring.Env) (v: Nat): Ring.Poly.eval env (Ring.single v) = Ring.var env v :=
  Eq.trans (Int.addZero (Int.mul (OfNat 1) (Int.mul (Ring.var env v) (OfNat 1))))
    (Eq.trans (Int.oneMul (Int.mul (Ring.var env v) (OfNat 1))) (Int.mulOne (Ring.var env v)))

theorem Ring.mulCong [a a2 b b2: Int] (p: a = a2) (q: b = b2): Int.mul a b = Int.mul a2 b2 :=
  Eq.trans (Eq.cong (t => Int.mul t b) p) (Eq.cong (Int.mul a2) q)

-- The normal form of a side means the side.

theorem Ring.NExpr.sound (env: Ring.Env): (e: Ring.NExpr) -> Ring.Poly.eval env (Ring.NExpr.poly e) = OfNat (Ring.NExpr.eval env e)
  | NAtom i => Eq.trans (Ring.evalSingle env (Ring.twice i)) (Ring.lookupNat i (Ring.Env.nats env) (Ring.Env.ints env))
  | NNum n => Ring.evalConst env (OfNat n)
  | NAdd a b =>
    Eq.trans (Ring.evalAdd env (Ring.NExpr.poly a) (Ring.NExpr.poly b)) (Int.addCong (Ring.NExpr.sound env a) (Ring.NExpr.sound env b))
  | NMul a b =>
    Eq.trans (Ring.evalMul env (Ring.NExpr.poly a) (Ring.NExpr.poly b)) (Ring.mulCong (Ring.NExpr.sound env a) (Ring.NExpr.sound env b))
  | NSucc a =>
    Eq.trans (Ring.evalAdd env (Ring.NExpr.poly a) (Ring.const (OfNat 1)))
      (Eq.trans (Int.addCong (Ring.NExpr.sound env a) (Ring.evalConst env (OfNat 1))) (Eq.cong OfNat (Ring.natAddOne (Ring.NExpr.eval env a))))

theorem Ring.ZExpr.sound (env: Ring.Env): (e: Ring.ZExpr) -> Ring.Poly.eval env (Ring.ZExpr.poly e) = Ring.ZExpr.eval env e
  | ZAtom i => Eq.trans (Ring.evalSingle env (Succ (Ring.twice i))) (Ring.lookupInt i (Ring.Env.nats env) (Ring.Env.ints env))
  | ZNum c => Ring.evalConst env c
  | ZAdd a b =>
    Eq.trans (Ring.evalAdd env (Ring.ZExpr.poly a) (Ring.ZExpr.poly b)) (Int.addCong (Ring.ZExpr.sound env a) (Ring.ZExpr.sound env b))
  | ZMul a b =>
    Eq.trans (Ring.evalMul env (Ring.ZExpr.poly a) (Ring.ZExpr.poly b)) (Ring.mulCong (Ring.ZExpr.sound env a) (Ring.ZExpr.sound env b))
  | ZNeg a => Eq.trans (Ring.evalNeg env (Ring.ZExpr.poly a)) (Eq.cong Int.neg (Ring.ZExpr.sound env a))
  | ZSub a b =>
    Eq.trans (Ring.evalAdd env (Ring.ZExpr.poly a) (Ring.neg (Ring.ZExpr.poly b)))
      (Int.addCong (Ring.ZExpr.sound env a) (Eq.trans (Ring.evalNeg env (Ring.ZExpr.poly b)) (Eq.cong Int.neg (Ring.ZExpr.sound env b))))
  | ZOfNat e => Ring.NExpr.sound env e
  | ZNegSucc e =>
    Eq.trans (Ring.evalNeg env (Ring.add (Ring.NExpr.poly e) (Ring.const (OfNat 1))))
      (Eq.cong Int.neg
        (Eq.trans (Ring.evalAdd env (Ring.NExpr.poly e) (Ring.const (OfNat 1)))
          (Eq.trans (Int.addCong (Ring.NExpr.sound env e) (Ring.evalConst env (OfNat 1))) (Eq.cong OfNat (Ring.natAddOne (Ring.NExpr.eval env e))))))

-- Equal normal forms, equal sides: what `ring` applies, with `rfl` for `ok`.

theorem Ring.proveNat (env: Ring.Env) (a: Ring.NExpr) (b: Ring.NExpr) (ok: Ring.NExpr.poly a = Ring.NExpr.poly b):
    Ring.NExpr.eval env a = Ring.NExpr.eval env b :=
  Int.ofNatInjective (Ring.NExpr.eval env a) (Ring.NExpr.eval env b)
    (Eq.trans (Eq.sym (Ring.NExpr.sound env a)) (Eq.trans (Eq.cong (Ring.Poly.eval env) ok) (Ring.NExpr.sound env b)))

theorem Ring.proveInt (env: Ring.Env) (a: Ring.ZExpr) (b: Ring.ZExpr) (ok: Ring.ZExpr.poly a = Ring.ZExpr.poly b):
    Ring.ZExpr.eval env a = Ring.ZExpr.eval env b :=
  Eq.trans (Eq.sym (Ring.ZExpr.sound env a)) (Eq.trans (Eq.cong (Ring.Poly.eval env) ok) (Ring.ZExpr.sound env b))

-- With hypotheses `l1 = r1`, ...: `a + (r1 + ...) = b + (l1 + ...)` as
-- polynomials, and the two sums are equal, so `a = b` (`ring [h1, ...]`).

theorem Ring.NExpr.sidesAgree (env: Ring.Env): (hs: List (Pair Ring.NExpr Ring.NExpr)) -> Ring.NExpr.allHold env hs ->
    Ring.NExpr.eval env (Ring.NExpr.lefts hs) = Ring.NExpr.eval env (Ring.NExpr.rights hs)
  | Nil, h => rfl
  | Cons (MkPair l r) hs, h =>
    Eq.trans (Eq.cong (t => t + Ring.NExpr.eval env (Ring.NExpr.lefts hs)) (And.left h))
      (Eq.cong (Nat.add (Ring.NExpr.eval env r)) (Ring.NExpr.sidesAgree env hs (And.right h)))

theorem Ring.ZExpr.sidesAgree (env: Ring.Env): (hs: List (Pair Ring.ZExpr Ring.ZExpr)) -> Ring.ZExpr.allHold env hs ->
    Ring.ZExpr.eval env (Ring.ZExpr.lefts hs) = Ring.ZExpr.eval env (Ring.ZExpr.rights hs)
  | Nil, h => rfl
  | Cons (MkPair l r) hs, h =>
    Int.addCong (And.left h) (Ring.ZExpr.sidesAgree env hs (And.right h))

theorem Ring.proveNatWith (env: Ring.Env) (a: Ring.NExpr) (b: Ring.NExpr) (hs: List (Pair Ring.NExpr Ring.NExpr))
    (ok: Ring.NExpr.poly (NAdd a (Ring.NExpr.rights hs)) = Ring.NExpr.poly (NAdd b (Ring.NExpr.lefts hs)))
    (h: Ring.NExpr.allHold env hs):
    Ring.NExpr.eval env a = Ring.NExpr.eval env b :=
  Ring.natAddRightCancel (Ring.NExpr.eval env a) (Ring.NExpr.eval env b) (Ring.NExpr.eval env (Ring.NExpr.rights hs))
    (Eq.trans (Ring.proveNat env (NAdd a (Ring.NExpr.rights hs)) (NAdd b (Ring.NExpr.lefts hs)) ok)
      (Eq.cong (Nat.add (Ring.NExpr.eval env b)) (Ring.NExpr.sidesAgree env hs h)))

theorem Ring.proveIntWith (env: Ring.Env) (a: Ring.ZExpr) (b: Ring.ZExpr) (hs: List (Pair Ring.ZExpr Ring.ZExpr))
    (ok: Ring.ZExpr.poly (ZAdd a (Ring.ZExpr.rights hs)) = Ring.ZExpr.poly (ZAdd b (Ring.ZExpr.lefts hs)))
    (h: Ring.ZExpr.allHold env hs):
    Ring.ZExpr.eval env a = Ring.ZExpr.eval env b :=
  Ring.addRightCancel (Ring.ZExpr.eval env a) (Ring.ZExpr.eval env b) (Ring.ZExpr.eval env (Ring.ZExpr.rights hs))
    (Eq.trans (Ring.proveInt env (ZAdd a (Ring.ZExpr.rights hs)) (ZAdd b (Ring.ZExpr.lefts hs)) ok)
      (Eq.cong (Int.add (Ring.ZExpr.eval env b)) (Ring.ZExpr.sidesAgree env hs h)))

-- Hand-written uses, as `ring` writes them: `x * (y + 1) = x + y * x`, and
-- `(a + b) * (a - b) = a * a - b * b` at `Int`.
theorem Ring.proveNatExample (x: Nat) (y: Nat): x * (y + 1) = x + y * x :=
  Ring.proveNat (MkEnv [x, y] []) (NMul (NAtom 0) (NAdd (NAtom 1) (NNum 1))) (NAdd (NAtom 0) (NMul (NAtom 1) (NAtom 0))) rfl

theorem Ring.proveIntExample (a: Int) (b: Int): (a + b) * (a - b) = a * a - b * b :=
  Ring.proveInt (MkEnv [] [a, b]) (ZMul (ZAdd (ZAtom 0) (ZAtom 1)) (ZSub (ZAtom 0) (ZAtom 1)))
    (ZSub (ZMul (ZAtom 0) (ZAtom 0)) (ZMul (ZAtom 1) (ZAtom 1))) rfl

-- `h: p + p + n = n * n` gives `(n + p) + (n + p) + Succ n = Succ n * Succ n`
-- (`List.pairsStep`).
theorem Ring.proveNatWithExample (n: Nat) (p: Nat) (h: p + p + n = n * n): (n + p) + (n + p) + Succ n = Succ n * Succ n :=
  Ring.proveNatWith (MkEnv [n, p] [])
    (NAdd (NAdd (NAdd (NAtom 0) (NAtom 1)) (NAdd (NAtom 0) (NAtom 1))) (NSucc (NAtom 0))) (NMul (NSucc (NAtom 0)) (NSucc (NAtom 0)))
    [MkPair (NAdd (NAdd (NAtom 1) (NAtom 1)) (NAtom 0)) (NMul (NAtom 0) (NAtom 0))] rfl (Both h Trivial)
