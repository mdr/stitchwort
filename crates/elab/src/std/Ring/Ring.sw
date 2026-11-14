--| `Std.Ring`: equations between polynomials, by normalising both sides. A
--| side of a `Nat` or `Int` equation is written as syntax over numbered atoms
--| (`Ring.NExpr`, `Ring.ZExpr`); `poly` turns it into a polynomial in a normal
--| form; and [`Ring.proveNat`] / [`Ring.proveInt`] (std/Ring/Sound.sw) say that
--| two sides with the same normal form are equal, in every environment. The
--| compiler's `ring` writes the syntax and applies the theorem to `rfl`, so
--| the kernel checks the equation by running `poly` on both sides. Nothing
--| here is trusted beyond the kernel.
--|
--| The normal form is a list of monomials, each a nonzero `Int` coefficient
--| and the sorted list of its variables (with repeats: `x * x` is `[x, x]`),
--| sorted by `Ring.cmp` with no two alike. Every operation builds its result
--| by inserting one monomial at a time (`Ring.insert`), which keeps that form,
--| so two polynomials are equal exactly when their normal forms are the same
--| list. Both `Nat` and `Int` sides are normalised over `Int` coefficients: a
--| `Nat` side means `OfNat` of its value. Variables are numbered so that `Nat`
--| atom `i` is `2 * i` and `Int` atom `j` is `2 * j + 1` (`Ring.lookup`), so
--| an `Int` side may mention a `Nat` atom under `OfNat`.
-- (docs/proposals/proof-automation.md §6.2, stage 2)

import Ring.Env (MkEnv)
import Ring.NExpr (NAtom, NNum, NAdd, NMul, NSucc)
import Ring.ZExpr (ZAtom, ZNum, ZAdd, ZMul, ZNeg, ZSub, ZOfNat, ZNegSucc)
import Ring.Mono (MkMono)

-- Syntax and meaning

--| The atoms' values: `Nat` atoms and `Int` atoms, each numbered from 0 in
--| its own list.
type Ring.Env: Type = | MkEnv (nats: List Nat) (ints: List Int)

--| The `i`th entry, or 0 past the end.
@[tailrec]
def Ring.natAt: (xs: List Nat) → (i: Nat) → Nat
  | [], i => 0
  | [x, ..xs], Zero => x
  | [x, ..xs], Succ i => Ring.natAt xs i

--| The `i`th entry of a list of integers, or 0 past the end.
@[tailrec]
def Ring.intAt: (xs: List Int) → (i: Nat) → Int
  | [], i => OfNat 0
  | [x, ..xs], Zero => x
  | [x, ..xs], Succ i => Ring.intAt xs i

--| A quoted `Nat` side of an equation, as `ring` reads it. Each node means what the surface syntax computes to,
--| so a quoted side converts with the side it quotes: `NSucc` is `Succ`,
--| which `x + 1` and `1 + x` compute to, and `NMul` is `Nat.mul`.
type Ring.NExpr: Type =
  | NAtom (i: Nat)
  | NNum (n: Nat)
  | NAdd (a: Ring.NExpr) (b: Ring.NExpr)
  | NMul (a: Ring.NExpr) (b: Ring.NExpr)
  | NSucc (a: Ring.NExpr)

--| The `Nat` a quoted side stands for, with its atoms' values from `env`.
@[noReceiver]
def Ring.NExpr.eval (env: Ring.Env): (expr: Ring.NExpr) → Nat
  | NAtom i => Ring.natAt (Ring.Env.nats env) i
  | NNum n => n
  | NAdd a b => Ring.NExpr.eval env a + Ring.NExpr.eval env b
  | NMul a b => Ring.NExpr.eval env a * Ring.NExpr.eval env b
  | NSucc a => Succ (Ring.NExpr.eval env a)

--| A quoted `Int` side of an equation, as `ring` reads it. `ZOfNat e` is a `Nat` side embedded (`OfNat`), which
--| is what `x.toInt` and `Int` arithmetic on `OfNat`s compute to, and
--| `ZNegSucc e` is `-(e + 1)`.
type Ring.ZExpr: Type =
  | ZAtom (i: Nat)
  | ZNum (c: Int)
  | ZAdd (a: Ring.ZExpr) (b: Ring.ZExpr)
  | ZMul (a: Ring.ZExpr) (b: Ring.ZExpr)
  | ZNeg (a: Ring.ZExpr)
  | ZSub (a: Ring.ZExpr) (b: Ring.ZExpr)
  | ZOfNat (e: Ring.NExpr)
  | ZNegSucc (e: Ring.NExpr)

--| The `Int` a quoted side stands for, with its atoms' values from `env`.
@[noReceiver]
def Ring.ZExpr.eval (env: Ring.Env): (expr: Ring.ZExpr) → Int
  | ZAtom i => Ring.intAt (Ring.Env.ints env) i
  | ZNum c => c
  | ZAdd a b => Int.add (Ring.ZExpr.eval env a) (Ring.ZExpr.eval env b)
  | ZMul a b => Int.mul (Ring.ZExpr.eval env a) (Ring.ZExpr.eval env b)
  | ZNeg a => Int.neg (Ring.ZExpr.eval env a)
  | ZSub a b => Int.sub (Ring.ZExpr.eval env a) (Ring.ZExpr.eval env b)
  | ZOfNat e => OfNat (Ring.NExpr.eval env e)
  | ZNegSucc e => NegSucc (Ring.NExpr.eval env e)

--| Hypotheses for `ring [h1, h2]`: each a pair of sides `MkPair l r` with
--| `l = r`, as `Both h1 (Both h2 Trivial)`.
def Ring.NExpr.allHold (env: Ring.Env): (pairs: List (Pair Ring.NExpr Ring.NExpr)) → Prop
  | [] => Unit
  | [MkPair l r, ..hs] => (Ring.NExpr.eval env l = Ring.NExpr.eval env r) ∧ (Ring.NExpr.allHold env hs)

--| `Int` hypotheses for `ring [h1, h2]`: each a pair of sides `MkPair l r` with `l = r`.
def Ring.ZExpr.allHold (env: Ring.Env): (pairs: List (Pair Ring.ZExpr Ring.ZExpr)) → Prop
  | [] => Unit
  | [MkPair l r, ..hs] => (Ring.ZExpr.eval env l = Ring.ZExpr.eval env r) ∧ (Ring.ZExpr.allHold env hs)

--| The hypotheses' left sides added up.
def Ring.NExpr.lefts: (pairs: List (Pair Ring.NExpr Ring.NExpr)) → Ring.NExpr
  | [] => NNum 0
  | [MkPair l r, ..hs] => NAdd l (Ring.NExpr.lefts hs)

--| The hypotheses' right sides added up.
def Ring.NExpr.rights: (pairs: List (Pair Ring.NExpr Ring.NExpr)) → Ring.NExpr
  | [] => NNum 0
  | [MkPair l r, ..hs] => NAdd r (Ring.NExpr.rights hs)

--| The `Int` hypotheses' left sides added up.
def Ring.ZExpr.lefts: (pairs: List (Pair Ring.ZExpr Ring.ZExpr)) → Ring.ZExpr
  | [] => ZNum (OfNat 0)
  | [MkPair l r, ..hs] => ZAdd l (Ring.ZExpr.lefts hs)

--| The `Int` hypotheses' right sides added up.
def Ring.ZExpr.rights: (pairs: List (Pair Ring.ZExpr Ring.ZExpr)) → Ring.ZExpr
  | [] => ZNum (OfNat 0)
  | [MkPair l r, ..hs] => ZAdd r (Ring.ZExpr.rights hs)

-- Variables

--| Twice the number. `Nat` atom `i` is variable `2 * i`, `Int` atom `j` is variable `2 * j + 1`.
def Ring.twice: (n: Nat) → Nat
  | Zero => Zero
  | Succ i => Succ (Succ (Ring.twice i))

--| The list without its first entry (empty for an empty list).
def Ring.natTail: (xs: List Nat) → List Nat
  | [] => []
  | [x, ..xs] => xs

--| The list without its first entry (empty for an empty list).
def Ring.intTail: (xs: List Int) → List Int
  | [] => []
  | [x, ..xs] => xs

--| The value of variable `v`: `Nat` atom `v / 2` for an even `v`, `Int` atom `v / 2` for an odd one.
@[tailrec]
def Ring.lookup: (naturals: List Nat) → (integers: List Int) → (v: Nat) → Int
  | ns, is, Zero => OfNat (Ring.natAt ns 0)
  | ns, is, Succ Zero => Ring.intAt is 0
  | ns, is, Succ (Succ v) => Ring.lookup (Ring.natTail ns) (Ring.intTail is) v

--| The value of variable `v` in `env`.
def Ring.var (env: Ring.Env) (v: Nat): Int := Ring.lookup (Ring.Env.nats env) (Ring.Env.ints env) v

-- Polynomials

--| A monomial: `c` times the product of the variables `vs`.
type Ring.Mono: Type = | MkMono (c: Int) (vs: List Nat)

--| The product of the variables' values.
def Ring.prod (env: Ring.Env): (vars: List Nat) → Int
  | [] => OfNat 1
  | [v, ..vs] => Int.mul (Ring.var env v) (Ring.prod env vs)

--| A monomial's value in `env`.
@[noReceiver]
def Ring.Mono.eval (env: Ring.Env): (mono: Ring.Mono) → Int
  | MkMono c vs => Int.mul c (Ring.prod env vs)

--| A polynomial's value in `env`: the sum of its monomials'.
def Ring.Poly.eval (env: Ring.Env): (poly: List Ring.Mono) → Int
  | [] => OfNat 0
  | [m, ..p] => Int.add (Ring.Mono.eval env m) (Ring.Poly.eval env p)

--| The order of monomials: by their variable lists, lexicographically.
@[tailrec]
def Ring.cmp: (xs: List Nat) → (ys: List Nat) → Ordering
  | [], [] => Equal
  | [], [w, ..ws] => Less
  | [v, ..vs], [] => Greater
  | [v, ..vs], [w, ..ws] => if Nat.equal v w then Ring.cmp vs ws else (if Nat.leq v w then Less else Greater)

--| A variable into a sorted list of variables.
def Ring.insertVar (v: Nat): (vars: List Nat) → List Nat
  | [] => [v]
  | [w, ..ws] => if Nat.leq v w then [v, w, ..ws] else [w, ..Ring.insertVar v ws]

--| The variables of a product of two monomials.
def Ring.mulVars: (xs: List Nat) → (ys: List Nat) → List Nat
  | [], ws => ws
  | [v, ..vs], ws => Ring.insertVar v (Ring.mulVars vs ws)

--| `c * vs` in front of `rest`, unless `c` is 0.
def Ring.cons: (c: Int) → (vs: List Nat) → (rest: List Ring.Mono) → List Ring.Mono
  | OfNat Zero, vs, p => p
  | OfNat (Succ n), vs, p => [MkMono (OfNat (Succ n)) vs, ..p]
  | NegSucc n, vs, p => [MkMono (NegSucc n) vs, ..p]

--| `c * vs + poly`, in normal form when `poly` is: before the first monomial that
--| comes after it, or added to the one alike (dropped if that makes 0).
def Ring.insert (c: Int) (vs: List Nat): (poly: List Ring.Mono) → List Ring.Mono
  | [] => Ring.cons c vs []
  | [MkMono d ws, ..p] =>
    match Ring.cmp vs ws with
      | Less => Ring.cons c vs [MkMono d ws, ..p]
      | Equal => Ring.cons (Int.add c d) ws p
      | Greater => [MkMono d ws, ..Ring.insert c vs p]

--| The sum of two polynomials in normal form, in normal form.
def Ring.add: (poly: List Ring.Mono) → (other: List Ring.Mono) → List Ring.Mono
  | [], q => q
  | [MkMono c vs, ..p], q => Ring.insert c vs (Ring.add p q)

--| A polynomial times one monomial: `(c * vs) * q`.
def Ring.scale (c: Int) (vs: List Nat): (poly: List Ring.Mono) → List Ring.Mono
  | [] => []
  | [MkMono d ws, ..q] => Ring.insert (Int.mul c d) (Ring.mulVars vs ws) (Ring.scale c vs q)

--| The product of two polynomials in normal form, in normal form.
def Ring.mul: (poly: List Ring.Mono) → (other: List Ring.Mono) → List Ring.Mono
  | [], q => []
  | [MkMono c vs, ..p], q => Ring.add (Ring.scale c vs q) (Ring.mul p q)

--| A polynomial negated: `-p`.
def Ring.neg (p: List Ring.Mono): List Ring.Mono := Ring.scale (NegSucc 0) [] p

--| The constant polynomial `c`.
def Ring.const (c: Int): List Ring.Mono := Ring.cons c [] []

--| The polynomial of one variable, `v`.
def Ring.single (v: Nat): List Ring.Mono := [MkMono (OfNat 1) [v]]

--| The normal form of a `Nat` side.
def Ring.NExpr.poly: (expr: Ring.NExpr) → List Ring.Mono
  | NAtom i => Ring.single (Ring.twice i)
  | NNum n => Ring.const (OfNat n)
  | NAdd a b => Ring.add (Ring.NExpr.poly a) (Ring.NExpr.poly b)
  | NMul a b => Ring.mul (Ring.NExpr.poly a) (Ring.NExpr.poly b)
  | NSucc a => Ring.add (Ring.NExpr.poly a) (Ring.const (OfNat 1))

--| The normal form of an `Int` side.
def Ring.ZExpr.poly: (expr: Ring.ZExpr) → List Ring.Mono
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

--| `Nat` atoms 0 and 1 are variables 0 and 2.
theorem Ring.polyAddCommExample: Ring.NExpr.poly (NAdd (NAtom 0) (NAtom 1))
      = Ring.NExpr.poly (NAdd (NAtom 1) (NAtom 0)) :=
  rfl

theorem Ring.polyMulExample: Ring.NExpr.poly (NMul (NAtom 1) (NAtom 0)) = [MkMono (OfNat 1) [0, 2]] := rfl

theorem Ring.polySquareExample: Ring.NExpr.poly (NMul (NSucc (NAtom 0)) (NSucc (NAtom 0)))
      = [MkMono (OfNat 1) [], MkMono (OfNat 2) [0], MkMono (OfNat 1) [0, 0]] :=
  rfl

theorem Ring.polyLikeTermsExample: Ring.NExpr.poly (NAdd (NAtom 0) (NAdd (NNum 2) (NAtom 0)))
      = [MkMono (OfNat 2) [], MkMono (OfNat 2) [0]] :=
  rfl

--| Zero is the empty list, however it comes about.
theorem Ring.polyZeroExample: Ring.NExpr.poly (NMul (NNum 0) (NAtom 0)) = [] := rfl

theorem Ring.polySubSelfExample: Ring.ZExpr.poly (ZSub (ZAtom 0) (ZAtom 0)) = [] := rfl

theorem Ring.polyNegSuccExample: Ring.ZExpr.poly (ZNeg (ZOfNat (NSucc (NAtom 0))))
      = Ring.ZExpr.poly (ZNegSucc (NAtom 0)) :=
  rfl

--| A `Nat` atom under `OfNat` is variable `2 * i`, an `Int` atom `2 * j + 1`.
theorem Ring.polyAtomsExample: Ring.ZExpr.poly (ZAdd (ZOfNat (NAtom 3)) (ZAtom 3))
      = [MkMono (OfNat 1) [6], MkMono (OfNat 1) [7]] :=
  rfl

theorem Ring.polySquaresExample: Ring.ZExpr.poly (ZMul (ZAdd (ZAtom 0) (ZAtom 1)) (ZSub (ZAtom 0) (ZAtom 1)))
      = Ring.ZExpr.poly (ZSub (ZMul (ZAtom 0) (ZAtom 0)) (ZMul (ZAtom 1) (ZAtom 1))) :=
  rfl

test "poly: different polynomials have different values somewhere" :=
  Ring.Poly.eval (MkEnv [3] []) (Ring.NExpr.poly (NMul (NAtom 0) (NNum 2)))
    ≠ Ring.Poly.eval (MkEnv [3] []) (Ring.NExpr.poly (NAdd (NAtom 0) (NNum 2)))

test "poly: a normal form means the side" :=
  Ring.Poly.eval (MkEnv [3, 4] [-5]) (Ring.ZExpr.poly (ZMul (ZSub (ZOfNat (NAtom 0)) (ZAtom 0)) (ZNegSucc (NAtom 1))))
    == -40

test "mulVars keeps the variables sorted" := Ring.mulVars [3, 1, 2] [0, 2] == [0, 1, 2, 2, 3]

test "cmp: lexicographic, shorter first" :=
  Ring.cmp [] [0] == Less
    ∧ Ring.cmp [0, 1] [0, 2] == Less
    ∧ Ring.cmp [1] [0, 5] == Greater
    ∧ Ring.cmp [2, 2] [2, 2] == Equal

test "lookup: Nat atoms at even variables, Int atoms at odd, 0 past the end" :=
  Ring.lookup [5, 6] [-1, -2] 2 == 6
    ∧ Ring.lookup [5, 6] [-1, -2] 3 == -2
    ∧ Ring.lookup [5] [] 7 == 0
    ∧ Ring.lookup [5] [] 4 == 0
