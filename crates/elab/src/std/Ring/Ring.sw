-- `Std.Ring`: equations between polynomials, by normalising both sides
-- (docs/proposals/proof-automation.md §6.2, stage 2). A side of a `Nat` or
-- `Int` equation is written as syntax over numbered atoms (`Ring.NExpr`,
-- `Ring.ZExpr`); `poly` turns it into a polynomial in a normal form; and
-- `Ring.proveNat` / `Ring.proveInt` (std/Ring/Sound.sw) say that two sides
-- with the same normal form are equal, in every environment. The compiler's
-- `ring` writes the syntax and applies the theorem to `rfl`, so the kernel
-- checks the equation by running `poly` on both sides. Nothing here is
-- trusted beyond the kernel.
--
-- The normal form is a list of monomials, each a nonzero `Int` coefficient
-- and the sorted list of its variables (with repeats: `x * x` is `[x, x]`),
-- sorted by `Ring.cmp` with no two alike. Every operation builds its result
-- by inserting one monomial at a time (`Ring.insert`), which keeps that form,
-- so two polynomials are equal exactly when their normal forms are the same
-- list. Both `Nat` and `Int` sides are normalised over `Int` coefficients: a
-- `Nat` side means `OfNat` of its value. Variables are numbered so that `Nat`
-- atom `i` is `2 * i` and `Int` atom `j` is `2 * j + 1` (`Ring.lookup`), so
-- an `Int` side may mention a `Nat` atom under `OfNat`.

import Ring.Env (MkEnv)
import Ring.NExpr (NAtom, NNum, NAdd, NMul, NSucc)
import Ring.ZExpr (ZAtom, ZNum, ZAdd, ZMul, ZNeg, ZSub, ZOfNat, ZNegSucc)
import Ring.Mono (MkMono)

-- Syntax and meaning

-- The atoms' values: `Nat` atoms and `Int` atoms, each numbered from 0 in
-- its own list.
type Ring.Env: Type =
  | MkEnv (nats: List Nat) (ints: List Int)

-- The `i`th entry, or 0 past the end.
def Ring.natAt: List Nat -> Nat -> Nat
  | Nil, i => 0
  | Cons x xs, Zero => x
  | Cons x xs, Succ i => Ring.natAt xs i

def Ring.intAt: List Int -> Nat -> Int
  | Nil, i => OfNat 0
  | Cons x xs, Zero => x
  | Cons x xs, Succ i => Ring.intAt xs i

-- `Nat`-valued syntax. Each node means what the surface syntax computes to,
-- so a quoted side converts with the side it quotes: `NSucc` is `Succ`,
-- which `x + 1` and `1 + x` compute to, and `NMul` is `Nat.mul`.
type Ring.NExpr: Type =
  | NAtom (i: Nat)
  | NNum (n: Nat)
  | NAdd (a: Ring.NExpr) (b: Ring.NExpr)
  | NMul (a: Ring.NExpr) (b: Ring.NExpr)
  | NSucc (a: Ring.NExpr)

@[noReceiver]
def Ring.NExpr.eval (env: Ring.Env): Ring.NExpr -> Nat
  | NAtom i => Ring.natAt (Ring.Env.nats env) i
  | NNum n => n
  | NAdd a b => Ring.NExpr.eval env a + Ring.NExpr.eval env b
  | NMul a b => Ring.NExpr.eval env a * Ring.NExpr.eval env b
  | NSucc a => Succ (Ring.NExpr.eval env a)

-- `Int`-valued syntax. `ZOfNat e` is a `Nat` side embedded (`OfNat`), which
-- is what `x.toInt` and `Int` arithmetic on `OfNat`s compute to, and
-- `ZNegSucc e` is `-(e + 1)`.
type Ring.ZExpr: Type =
  | ZAtom (i: Nat)
  | ZNum (c: Int)
  | ZAdd (a: Ring.ZExpr) (b: Ring.ZExpr)
  | ZMul (a: Ring.ZExpr) (b: Ring.ZExpr)
  | ZNeg (a: Ring.ZExpr)
  | ZSub (a: Ring.ZExpr) (b: Ring.ZExpr)
  | ZOfNat (e: Ring.NExpr)
  | ZNegSucc (e: Ring.NExpr)

@[noReceiver]
def Ring.ZExpr.eval (env: Ring.Env): Ring.ZExpr -> Int
  | ZAtom i => Ring.intAt (Ring.Env.ints env) i
  | ZNum c => c
  | ZAdd a b => Int.add (Ring.ZExpr.eval env a) (Ring.ZExpr.eval env b)
  | ZMul a b => Int.mul (Ring.ZExpr.eval env a) (Ring.ZExpr.eval env b)
  | ZNeg a => Int.neg (Ring.ZExpr.eval env a)
  | ZSub a b => Int.sub (Ring.ZExpr.eval env a) (Ring.ZExpr.eval env b)
  | ZOfNat e => OfNat (Ring.NExpr.eval env e)
  | ZNegSucc e => NegSucc (Ring.NExpr.eval env e)

-- Hypotheses for `ring [h1, h2]`: each a pair of sides `MkPair l r` with
-- `l = r`, as `Both h1 (Both h2 Trivial)`.
def Ring.NExpr.allHold (env: Ring.Env): List (Pair Ring.NExpr Ring.NExpr) -> Prop
  | Nil => Unit
  | Cons (MkPair l r) hs => And (Ring.NExpr.eval env l = Ring.NExpr.eval env r) (Ring.NExpr.allHold env hs)

def Ring.ZExpr.allHold (env: Ring.Env): List (Pair Ring.ZExpr Ring.ZExpr) -> Prop
  | Nil => Unit
  | Cons (MkPair l r) hs => And (Ring.ZExpr.eval env l = Ring.ZExpr.eval env r) (Ring.ZExpr.allHold env hs)

-- The hypotheses' left sides added up (`lefts`), and their right sides.
def Ring.NExpr.lefts: List (Pair Ring.NExpr Ring.NExpr) -> Ring.NExpr
  | Nil => NNum 0
  | Cons (MkPair l r) hs => NAdd l (Ring.NExpr.lefts hs)

def Ring.NExpr.rights: List (Pair Ring.NExpr Ring.NExpr) -> Ring.NExpr
  | Nil => NNum 0
  | Cons (MkPair l r) hs => NAdd r (Ring.NExpr.rights hs)

def Ring.ZExpr.lefts: List (Pair Ring.ZExpr Ring.ZExpr) -> Ring.ZExpr
  | Nil => ZNum (OfNat 0)
  | Cons (MkPair l r) hs => ZAdd l (Ring.ZExpr.lefts hs)

def Ring.ZExpr.rights: List (Pair Ring.ZExpr Ring.ZExpr) -> Ring.ZExpr
  | Nil => ZNum (OfNat 0)
  | Cons (MkPair l r) hs => ZAdd r (Ring.ZExpr.rights hs)

-- Variables

-- `Nat` atom `i` is variable `2 * i`, `Int` atom `j` is variable `2 * j + 1`.
def Ring.twice: Nat -> Nat
  | Zero => Zero
  | Succ i => Succ (Succ (Ring.twice i))

def Ring.natTail: List Nat -> List Nat
  | Nil => Nil
  | Cons x xs => xs

def Ring.intTail: List Int -> List Int
  | Nil => Nil
  | Cons x xs => xs

def Ring.lookup: List Nat -> List Int -> Nat -> Int
  | ns, is, Zero => OfNat (Ring.natAt ns 0)
  | ns, is, Succ Zero => Ring.intAt is 0
  | ns, is, Succ (Succ v) => Ring.lookup (Ring.natTail ns) (Ring.intTail is) v

def Ring.var (env: Ring.Env) (v: Nat): Int := Ring.lookup (Ring.Env.nats env) (Ring.Env.ints env) v

-- Polynomials

-- `c` times the product of the variables `vs`.
type Ring.Mono: Type =
  | MkMono (c: Int) (vs: List Nat)

def Ring.prod (env: Ring.Env): List Nat -> Int
  | Nil => OfNat 1
  | Cons v vs => Int.mul (Ring.var env v) (Ring.prod env vs)

@[noReceiver]
def Ring.Mono.eval (env: Ring.Env): Ring.Mono -> Int
  | MkMono c vs => Int.mul c (Ring.prod env vs)

def Ring.Poly.eval (env: Ring.Env): List Ring.Mono -> Int
  | Nil => OfNat 0
  | Cons m p => Int.add (Ring.Mono.eval env m) (Ring.Poly.eval env p)

-- The order of monomials: by their variable lists, lexicographically.
def Ring.cmp: List Nat -> List Nat -> Ordering
  | Nil, Nil => Equal
  | Nil, Cons w ws => Less
  | Cons v vs, Nil => Greater
  | Cons v vs, Cons w ws => if Nat.equal v w then Ring.cmp vs ws else (if Nat.leq v w then Less else Greater)

-- A variable into a sorted list of variables.
def Ring.insertVar (v: Nat): List Nat -> List Nat
  | Nil => Cons v Nil
  | Cons w ws => if Nat.leq v w then Cons v (Cons w ws) else Cons w (Ring.insertVar v ws)

-- The variables of a product of two monomials.
def Ring.mulVars: List Nat -> List Nat -> List Nat
  | Nil, ws => ws
  | Cons v vs, ws => Ring.insertVar v (Ring.mulVars vs ws)

-- `c * vs` in front of `p`, unless `c` is 0.
def Ring.cons: Int -> List Nat -> List Ring.Mono -> List Ring.Mono
  | OfNat Zero, vs, p => p
  | OfNat (Succ n), vs, p => Cons (MkMono (OfNat (Succ n)) vs) p
  | NegSucc n, vs, p => Cons (MkMono (NegSucc n) vs) p

-- `c * vs + p`, in normal form when `p` is: before the first monomial
-- that comes after it, or added to the one alike (dropped if that makes 0).
def Ring.insert (c: Int) (vs: List Nat): List Ring.Mono -> List Ring.Mono
  | Nil => Ring.cons c vs Nil
  | Cons (MkMono d ws) p =>
    match Ring.cmp vs ws with
      | Less => Ring.cons c vs (Cons (MkMono d ws) p)
      | Equal => Ring.cons (Int.add c d) ws p
      | Greater => Cons (MkMono d ws) (Ring.insert c vs p)

def Ring.add: List Ring.Mono -> List Ring.Mono -> List Ring.Mono
  | Nil, q => q
  | Cons (MkMono c vs) p, q => Ring.insert c vs (Ring.add p q)

-- `(c * vs) * q`
def Ring.scale (c: Int) (vs: List Nat): List Ring.Mono -> List Ring.Mono
  | Nil => Nil
  | Cons (MkMono d ws) q => Ring.insert (Int.mul c d) (Ring.mulVars vs ws) (Ring.scale c vs q)

def Ring.mul: List Ring.Mono -> List Ring.Mono -> List Ring.Mono
  | Nil, q => Nil
  | Cons (MkMono c vs) p, q => Ring.add (Ring.scale c vs q) (Ring.mul p q)

def Ring.neg (p: List Ring.Mono): List Ring.Mono := Ring.scale (NegSucc 0) Nil p

def Ring.const (c: Int): List Ring.Mono := Ring.cons c Nil Nil

def Ring.single (v: Nat): List Ring.Mono := Cons (MkMono (OfNat 1) (Cons v Nil)) Nil

-- The normal forms of the two kinds of side.
def Ring.NExpr.poly: Ring.NExpr -> List Ring.Mono
  | NAtom i => Ring.single (Ring.twice i)
  | NNum n => Ring.const (OfNat n)
  | NAdd a b => Ring.add (Ring.NExpr.poly a) (Ring.NExpr.poly b)
  | NMul a b => Ring.mul (Ring.NExpr.poly a) (Ring.NExpr.poly b)
  | NSucc a => Ring.add (Ring.NExpr.poly a) (Ring.const (OfNat 1))

def Ring.ZExpr.poly: Ring.ZExpr -> List Ring.Mono
  | ZAtom i => Ring.single (Succ (Ring.twice i))
  | ZNum c => Ring.const c
  | ZAdd a b => Ring.add (Ring.ZExpr.poly a) (Ring.ZExpr.poly b)
  | ZMul a b => Ring.mul (Ring.ZExpr.poly a) (Ring.ZExpr.poly b)
  | ZNeg a => Ring.neg (Ring.ZExpr.poly a)
  | ZSub a b => Ring.add (Ring.ZExpr.poly a) (Ring.neg (Ring.ZExpr.poly b))
  | ZOfNat e => Ring.NExpr.poly e
  | ZNegSucc e => Ring.neg (Ring.add (Ring.NExpr.poly e) (Ring.const (OfNat 1)))

-- Unit tests. Library types have no derived `==`, so the normal forms are
-- checked as `rfl` examples (the kernel computes both sides), and the parts
-- that return numbers and lists of numbers as tests.

-- `Nat` atoms 0 and 1 are variables 0 and 2.
theorem Ring.polyAddCommExample: Ring.NExpr.poly (NAdd (NAtom 0) (NAtom 1)) = Ring.NExpr.poly (NAdd (NAtom 1) (NAtom 0)) := rfl

theorem Ring.polyMulExample: Ring.NExpr.poly (NMul (NAtom 1) (NAtom 0)) = [MkMono (OfNat 1) [0, 2]] := rfl

theorem Ring.polySquareExample:
    Ring.NExpr.poly (NMul (NSucc (NAtom 0)) (NSucc (NAtom 0))) = [MkMono (OfNat 1) [], MkMono (OfNat 2) [0], MkMono (OfNat 1) [0, 0]] :=
  rfl

theorem Ring.polyLikeTermsExample: Ring.NExpr.poly (NAdd (NAtom 0) (NAdd (NNum 2) (NAtom 0))) = [MkMono (OfNat 2) [], MkMono (OfNat 2) [0]] := rfl

-- Zero is the empty list, however it comes about.
theorem Ring.polyZeroExample: Ring.NExpr.poly (NMul (NNum 0) (NAtom 0)) = Nil := rfl

theorem Ring.polySubSelfExample: Ring.ZExpr.poly (ZSub (ZAtom 0) (ZAtom 0)) = Nil := rfl

theorem Ring.polyNegSuccExample: Ring.ZExpr.poly (ZNeg (ZOfNat (NSucc (NAtom 0)))) = Ring.ZExpr.poly (ZNegSucc (NAtom 0)) := rfl

-- A `Nat` atom under `OfNat` is variable `2 * i`, an `Int` atom `2 * j + 1`.
theorem Ring.polyAtomsExample: Ring.ZExpr.poly (ZAdd (ZOfNat (NAtom 3)) (ZAtom 3)) = [MkMono (OfNat 1) [6], MkMono (OfNat 1) [7]] := rfl

theorem Ring.polySquaresExample:
    Ring.ZExpr.poly (ZMul (ZAdd (ZAtom 0) (ZAtom 1)) (ZSub (ZAtom 0) (ZAtom 1)))
      = Ring.ZExpr.poly (ZSub (ZMul (ZAtom 0) (ZAtom 0)) (ZMul (ZAtom 1) (ZAtom 1))) :=
  rfl

test "poly: different polynomials have different values somewhere" :=
  Ring.Poly.eval (MkEnv [3] []) (Ring.NExpr.poly (NMul (NAtom 0) (NNum 2)))
    != Ring.Poly.eval (MkEnv [3] []) (Ring.NExpr.poly (NAdd (NAtom 0) (NNum 2)))

test "poly: a normal form means the side" :=
  Ring.Poly.eval (MkEnv [3, 4] [-5]) (Ring.ZExpr.poly (ZMul (ZSub (ZOfNat (NAtom 0)) (ZAtom 0)) (ZNegSucc (NAtom 1)))) == -40

test "mulVars keeps the variables sorted" := Ring.mulVars [3, 1, 2] [0, 2] == [0, 1, 2, 2, 3]

test "cmp: lexicographic, shorter first" :=
  Ring.cmp [] [0] == Less && Ring.cmp [0, 1] [0, 2] == Less && Ring.cmp [1] [0, 5] == Greater && Ring.cmp [2, 2] [2, 2] == Equal

test "lookup: Nat atoms at even variables, Int atoms at odd, 0 past the end" :=
  Ring.lookup [5, 6] [-1, -2] 2 == 6 && Ring.lookup [5, 6] [-1, -2] 3 == -2 && Ring.lookup [5] [] 7 == 0 && Ring.lookup [5] [] 4 == 0
