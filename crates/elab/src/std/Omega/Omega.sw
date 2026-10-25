-- `Std.Omega`: linear arithmetic by a checked certificate (docs/proposals/omega.md,
-- milestone 1a). Facts and a goal about `Nat` are written as syntax over
-- numbered atoms; `Omega.check` replays a certificate saying how to combine
-- them into something false; `Omega.prove` (std/Omega/Sound.sw) says that when
-- the check passes, the facts imply the goal, in every environment. The
-- compiler's `omega` (milestone 1b) finds the certificate and writes the
-- `Omega.prove` application; nothing here is trusted beyond the kernel.
--
-- Rows are `0 <= c + Σ a_i * nat_i + Σ b_j * int_j` with `Int` coefficients.
-- Coefficient lists grow to cover every index the syntax mentions (adding two
-- lists keeps the longer one, `NV i` has a list of length `i + 1`), so no
-- coefficient is ever dropped and there is no separate dimension: an atom
-- past the end of the environment means 0.

import Omega.Env (MkEnv)
import Omega.NTerm (NV, NLit, NAdd, NSucc, MulLeft, MulRight)
import Omega.Fact (FLe, FLt, FEq, FNotLe, FNotLt, FSub, FMax, FMin, FNe)
import Omega.Goal (GLe, GLt, GVoid)
import Omega.Row (MkRow)
import Omega.Step (Input, NegGoal, NatNonneg, Combine, Divide)
import Omega.Cert (Close, Then, Split, Cases)

-- Syntax and meaning

-- The atoms' values: `Nat` atoms and (from stage 2) `Int` atoms, each
-- numbered from 0 in its own list.
type Omega.Env: Type =
  | MkEnv (nats: List Nat) (ints: List Int)

-- The `i`th entry, or 0 past the end.
def Omega.natAt: Nat -> List Nat -> Nat
  | i, Nil => 0
  | Zero, Cons x xs => x
  | Succ i, Cons x xs => Omega.natAt i xs

-- `Nat`-valued syntax. Each node means what the surface syntax computes to,
-- so a quoted term converts with the term it quotes: `MulLeft 3 (NV 0)` is
-- `3 * x` (left folded for a variable `x`, and otherwise unfolding),
-- `MulRight (NV 0) 3` is `x * 3` (which doesn't unfold), and `NSucc` is
-- `Succ`, which `1 + x` computes to.
type Omega.NTerm: Type =
  | NV (i: Nat)
  | NLit (n: Nat)
  | NAdd (a: Omega.NTerm) (b: Omega.NTerm)
  | NSucc (a: Omega.NTerm)
  | MulLeft (k: Nat) (t: Omega.NTerm)
  | MulRight (t: Omega.NTerm) (k: Nat)

@[noReceiver]
def Omega.NTerm.eval (env: Omega.Env): Omega.NTerm -> Nat
  | NV i => Omega.natAt i (Omega.Env.nats env)
  | NLit n => n
  | NAdd a b => Omega.NTerm.eval env a + Omega.NTerm.eval env b
  | NSucc a => Succ (Omega.NTerm.eval env a)
  | MulLeft k t => k * Omega.NTerm.eval env t
  | MulRight t k => Omega.NTerm.eval env t * k

-- A hypothesis. `FNotLe` and `FNotLt` quote `Not (a <= b)` and `Not (a < b)`
-- directly; other forms (`Nat.leq a b = False`, `(p && q) = True`) reach
-- these through bridge lemmas (`Nat.leqFalse`, `Bool.andLeft`, ...).
--
-- Stage 2's operation facts say what an atom is: `FSub t a b` says `t` is
-- `a - b` (the compiler puts the real `a - b` in the environment as `t` and
-- proves the fact by `rfl`), and `FMax`/`FMin` likewise for `Nat.max` and
-- `Nat.min`. Each gives rows that always hold (`a - b <= a`, ...) and two
-- cases a certificate may split on (`Cases`); `FNe`, `Not (a = b)`, gives
-- only the cases.
type Omega.Fact: Type =
  | FLe (a: Omega.NTerm) (b: Omega.NTerm)
  | FLt (a: Omega.NTerm) (b: Omega.NTerm)
  | FEq (a: Omega.NTerm) (b: Omega.NTerm)
  | FNotLe (a: Omega.NTerm) (b: Omega.NTerm)
  | FNotLt (a: Omega.NTerm) (b: Omega.NTerm)
  | FSub (t: Omega.NTerm) (a: Omega.NTerm) (b: Omega.NTerm)
  | FMax (t: Omega.NTerm) (a: Omega.NTerm) (b: Omega.NTerm)
  | FMin (t: Omega.NTerm) (a: Omega.NTerm) (b: Omega.NTerm)
  | FNe (a: Omega.NTerm) (b: Omega.NTerm)

@[noReceiver]
def Omega.Fact.holds (env: Omega.Env): Omega.Fact -> Prop
  | FLe a b => Omega.NTerm.eval env a <= Omega.NTerm.eval env b
  | FLt a b => Omega.NTerm.eval env a < Omega.NTerm.eval env b
  | FEq a b => Omega.NTerm.eval env a = Omega.NTerm.eval env b
  | FNotLe a b => Not (Omega.NTerm.eval env a <= Omega.NTerm.eval env b)
  | FNotLt a b => Not (Omega.NTerm.eval env a < Omega.NTerm.eval env b)
  | FSub t a b => Omega.NTerm.eval env t = Omega.NTerm.eval env a - Omega.NTerm.eval env b
  | FMax t a b => Omega.NTerm.eval env t = Nat.max (Omega.NTerm.eval env a) (Omega.NTerm.eval env b)
  | FMin t a b => Omega.NTerm.eval env t = Nat.min (Omega.NTerm.eval env a) (Omega.NTerm.eval env b)
  | FNe a b => Not (Omega.NTerm.eval env a = Omega.NTerm.eval env b)

-- The facts' proofs, as `Both h1 (Both h2 Trivial)`.
def Omega.Facts.holds (env: Omega.Env): List Omega.Fact -> Prop
  | Nil => Unit
  | Cons f fs => And (Omega.Fact.holds env f) (Omega.Facts.holds env fs)

-- The goal. An equation is two `GLe` goals (`Omega.proveEq`); `GVoid` says
-- the facts contradict each other.
type Omega.Goal: Type =
  | GLe (a: Omega.NTerm) (b: Omega.NTerm)
  | GLt (a: Omega.NTerm) (b: Omega.NTerm)
  | GVoid

@[noReceiver]
def Omega.Goal.holds (env: Omega.Env): Omega.Goal -> Prop
  | GLe a b => Omega.NTerm.eval env a <= Omega.NTerm.eval env b
  | GLt a b => Omega.NTerm.eval env a < Omega.NTerm.eval env b
  | GVoid => Void

-- Rows

-- `0 <= c + Σ nats_i * x_i + Σ ints_j * y_j`.
type Omega.Row: Type =
  | MkRow (c: Int) (nats: List Int) (ints: List Int)

-- `Σ a_i * v_i`, stopping at the shorter list.
def Omega.dot: List Int -> List Int -> Int
  | Nil, vs => OfNat 0
  | Cons a as, Nil => OfNat 0
  | Cons a as, Cons v vs => a * v + Omega.dot as vs

def Omega.toInts: List Nat -> List Int
  | Nil => Nil
  | Cons x xs => Cons (OfNat x) (Omega.toInts xs)

@[noReceiver]
def Omega.Row.value (nv: List Int) (iv: List Int): Omega.Row -> Int
  | MkRow c ns is => c + (Omega.dot ns nv + Omega.dot is iv)

@[noReceiver]
def Omega.Row.eval (env: Omega.Env) (r: Omega.Row): Int :=
  Omega.Row.value (Omega.toInts (Omega.Env.nats env)) (Omega.Env.ints env) r

@[noReceiver]
def Omega.Row.Holds (env: Omega.Env) (r: Omega.Row): Prop := 0 <= Omega.Row.eval env r

-- Adding keeps the longer list: nothing is dropped.
def Omega.addC: List Int -> List Int -> List Int
  | Nil, bs => bs
  | Cons a as, Nil => Cons a as
  | Cons a as, Cons b bs => Cons (a + b) (Omega.addC as bs)

def Omega.scaleC (k: Int): List Int -> List Int
  | Nil => Nil
  | Cons a as => Cons (k * a) (Omega.scaleC k as)

-- Atom `i`'s coefficients: `i` zeros, then 1.
def Omega.unit: Nat -> List Int
  | Zero => [OfNat 1]
  | Succ i => Cons (OfNat 0) (Omega.unit i)

def Omega.Row.add: Omega.Row -> Omega.Row -> Omega.Row
  | MkRow c ns is, MkRow d ms js => MkRow (c + d) (Omega.addC ns ms) (Omega.addC is js)

@[noReceiver]
def Omega.Row.scale (k: Int): Omega.Row -> Omega.Row
  | MkRow c ns is => MkRow (k * c) (Omega.scaleC k ns) (Omega.scaleC k is)

-- `r - s`
def Omega.Row.sub (r: Omega.Row) (s: Omega.Row): Omega.Row := Omega.Row.add r (Omega.Row.scale (NegSucc 0) s)

def Omega.Row.zero: Omega.Row := MkRow (OfNat 0) Nil Nil

def Omega.Row.one: Omega.Row := MkRow (OfNat 1) Nil Nil

-- A term's linear form.
def Omega.NTerm.lin: Omega.NTerm -> Omega.Row
  | NV i => MkRow (OfNat 0) (Omega.unit i) Nil
  | NLit n => MkRow (OfNat n) Nil Nil
  | NAdd a b => Omega.Row.add (Omega.NTerm.lin a) (Omega.NTerm.lin b)
  | NSucc a => Omega.Row.add (Omega.NTerm.lin a) Omega.Row.one
  | MulLeft k t => Omega.Row.scale (OfNat k) (Omega.NTerm.lin t)
  | MulRight t k => Omega.Row.scale (OfNat k) (Omega.NTerm.lin t)

-- The convention (docs/proposals/omega.md §6.3), all through this one row:
-- `a <= b` is `b - a >= 0`; `a < b` is `Succ a <= b`; `Not (a <= b)` is
-- `Succ b <= a`; `Not (a < b)` is `b <= a`; `a = b` is both `a <= b` and
-- `b <= a`.
def Omega.leRow (a: Omega.NTerm) (b: Omega.NTerm): Omega.Row := Omega.Row.sub (Omega.NTerm.lin b) (Omega.NTerm.lin a)

def Omega.Fact.rows: Omega.Fact -> List Omega.Row
  | FLe a b => [Omega.leRow a b]
  | FLt a b => [Omega.leRow (NSucc a) b]
  | FEq a b => [Omega.leRow a b, Omega.leRow b a]
  | FNotLe a b => [Omega.leRow (NSucc b) a]
  | FNotLt a b => [Omega.leRow b a]
  | FSub t a b => [Omega.leRow t a, Omega.leRow a (NAdd t b)]
  | FMax t a b => [Omega.leRow a t, Omega.leRow b t]
  | FMin t a b => [Omega.leRow t a, Omega.leRow t b]
  | FNe a b => []

-- Whether a fact has cases, and what each case adds, as facts: `a - b` is
-- `t` with `t + b = a` when `b <= a`, and 0 when `a < b`; `max` and `min`
-- are one side or the other; `a != b` is `a < b` or `b < a`.
def Omega.Fact.splits: Omega.Fact -> Bool
  | FSub t a b => True
  | FMax t a b => True
  | FMin t a b => True
  | FNe a b => True
  | f => False

def Omega.Fact.left: Omega.Fact -> List Omega.Fact
  | FSub t a b => [FLe b a, FEq (NAdd t b) a]
  | FMax t a b => [FLe a b, FEq t b]
  | FMin t a b => [FLe a b, FEq t a]
  | FNe a b => [FLt a b]
  | f => []

def Omega.Fact.right: Omega.Fact -> List Omega.Fact
  | FSub t a b => [FLt a b, FEq t (NLit 0)]
  | FMax t a b => [FLt b a, FEq t a]
  | FMin t a b => [FLt b a, FEq t b]
  | FNe a b => [FLt b a]
  | f => []

-- The input rows: each fact's rows, in order (an equation gives two).
def Omega.Facts.rows: List Omega.Fact -> List Omega.Row
  | Nil => Nil
  | Cons f fs => List.append (Omega.Fact.rows f) (Omega.Facts.rows fs)

-- The goal's negation: `Not (a <= b)` for `GLe`, `Not (a < b)` for `GLt`;
-- nothing for `GVoid`.
def Omega.Goal.negRow: Omega.Goal -> Option Omega.Row
  | GLe a b => Some (Omega.leRow (NSucc b) a)
  | GLt a b => Some (Omega.leRow b a)
  | GVoid => None

-- Certificates

-- One step adds one row, numbered after the rows before it (from 0).
type Omega.Step: Type =
  -- input row `i`: `Omega.Facts.rows`'s `i`th
  | Input (i: Nat)
  -- the goal's negation (not for `GVoid`)
  | NegGoal
  -- `0 <= x_i` for `Nat` atom `i`
  | NatNonneg (i: Nat)
  -- `Σ k * row r` for `MkPair k r`, each `r` an earlier row
  | Combine (terms: List (Pair Nat Nat))
  -- row `r` divided by `d > 0`, which must divide every coefficient; the
  -- constant is rounded down
  | Divide (r: Nat) (d: Nat)

type Omega.Cert: Type =
  -- row `r` has every coefficient 0 and a negative constant
  | Close (r: Nat)
  | Then (s: Omega.Step) (rest: Omega.Cert)
  -- `left` has the row `l`, `right` the row `-1 - l`; a row made in one
  -- branch isn't seen by the other
  | Split (l: Omega.Row) (left: Omega.Cert) (right: Omega.Cert)
  -- fact `f`'s cases (`Omega.Fact.left` and `right`): each branch has its
  -- case's rows after the rows before it
  | Cases (f: Nat) (left: Omega.Cert) (right: Omega.Cert)

-- Fact `i`, or `0 <= 0` (which has no cases) if there is none.
def Omega.getFact: List Omega.Fact -> Nat -> Omega.Fact
  | Nil, i => FLe (NLit 0) (NLit 0)
  | Cons f fs, Zero => f
  | Cons f fs, Succ i => Omega.getFact fs i

-- Row `i`, or the zero row (`0 <= 0`) if there is none.
def Omega.getRow: List Omega.Row -> Nat -> Omega.Row
  | Nil, i => Omega.Row.zero
  | Cons r rs, Zero => r
  | Cons r rs, Succ i => Omega.getRow rs i

def Omega.hasRow (rows: List Omega.Row) (i: Nat): Bool := Nat.leq (Succ i) (List.length rows)

def Omega.optRow: Option Omega.Row -> Omega.Row
  | None => Omega.Row.zero
  | Some r => r

def Omega.combine (ctx: List Omega.Row): List (Pair Nat Nat) -> Omega.Row
  | Nil => Omega.Row.zero
  | Cons (MkPair k r) ts => Omega.Row.add (Omega.Row.scale (OfNat k) (Omega.getRow ctx r)) (Omega.combine ctx ts)

def Omega.allRefs (ctx: List Omega.Row): List (Pair Nat Nat) -> Bool
  | Nil => True
  | Cons (MkPair k r) ts => Omega.hasRow ctx r && Omega.allRefs ctx ts

def Omega.isZero: Int -> Bool
  | OfNat Zero => True
  | OfNat (Succ n) => False
  | NegSucc n => False

def Omega.allZero: List Int -> Bool
  | Nil => True
  | Cons a as => Omega.isZero a && Omega.allZero as

-- Every coefficient is a multiple of `d + 1`.
def Omega.allDiv (d: Nat): List Int -> Bool
  | Nil => True
  | Cons a as => Omega.isZero (a % OfNat (Succ d)) && Omega.allDiv d as

def Omega.divC (d: Nat): List Int -> List Int
  | Nil => Nil
  | Cons a as => Cons (a / OfNat (Succ d)) (Omega.divC d as)

@[noReceiver]
def Omega.Row.divisible: Nat -> Omega.Row -> Bool
  | Zero, r => False
  | Succ d, MkRow c ns is => Omega.allDiv d ns && Omega.allDiv d is

-- `/` by a positive number rounds down.
@[noReceiver]
def Omega.Row.divide: Nat -> Omega.Row -> Omega.Row
  | Zero, r => r
  | Succ d, MkRow c ns is => MkRow (c / OfNat (Succ d)) (Omega.divC d ns) (Omega.divC d is)

-- `0 <= c` with `c < 0` and no atoms left.
def Omega.Row.isContra: Omega.Row -> Bool
  | MkRow c ns is => Int.isNeg c && (Omega.allZero ns && Omega.allZero is)

-- `-1 - l`: `l >= 0` or this is.
def Omega.Row.splitOther (l: Omega.Row): Omega.Row := Omega.Row.sub (MkRow (NegSucc 0) Nil Nil) l

-- Whether a step's references are good. Only `Divide`'s check matters for
-- soundness (a missing row reads as the zero row, which is true); the others
-- make a malformed certificate fail instead of meaning something else.
@[noReceiver]
def Omega.Step.valid (facts: List Omega.Row) (neg: Option Omega.Row) (ctx: List Omega.Row): Omega.Step -> Bool
  | Input i => Omega.hasRow facts i
  | NegGoal => Option.isSome neg
  | NatNonneg i => True
  | Combine ts => Omega.allRefs ctx ts
  | Divide r d => Omega.hasRow ctx r && Omega.Row.divisible d (Omega.getRow ctx r)

@[noReceiver]
def Omega.Step.row (facts: List Omega.Row) (neg: Option Omega.Row) (ctx: List Omega.Row): Omega.Step -> Omega.Row
  | Input i => Omega.getRow facts i
  | NegGoal => Omega.optRow neg
  | NatNonneg i => Omega.NTerm.lin (NV i)
  | Combine ts => Omega.combine ctx ts
  | Divide r d => Omega.Row.divide d (Omega.getRow ctx r)

def Omega.checkCert (fs: List Omega.Fact) (facts: List Omega.Row) (neg: Option Omega.Row) (ctx: List Omega.Row): Omega.Cert -> Bool
  | Close r => Omega.Row.isContra (Omega.getRow ctx r)
  | Then s rest =>
    Omega.Step.valid facts neg ctx s && Omega.checkCert fs facts neg (List.append ctx [Omega.Step.row facts neg ctx s]) rest
  | Split l left right =>
    Omega.checkCert fs facts neg (List.append ctx [l]) left && Omega.checkCert fs facts neg (List.append ctx [Omega.Row.splitOther l]) right
  | Cases f left right =>
    Omega.Fact.splits (Omega.getFact fs f)
      && (Omega.checkCert fs facts neg (List.append ctx (Omega.Facts.rows (Omega.Fact.left (Omega.getFact fs f)))) left
        && Omega.checkCert fs facts neg (List.append ctx (Omega.Facts.rows (Omega.Fact.right (Omega.getFact fs f)))) right)

-- The checker. It doesn't look at the environment: the kernel runs it on the
-- quoted facts, goal and certificate alone.
def Omega.check (facts: List Omega.Fact) (goal: Omega.Goal) (cert: Omega.Cert): Bool :=
  Omega.checkCert facts (Omega.Facts.rows facts) (Omega.Goal.negRow goal) Nil cert

-- `id <= last.to` and `last.to + 1 <= r.from` give `id < r.from` (day 5's
-- `absorbStacked`): the three rows add up to `-1 >= 0`.
test "check: absorbStacked" := Omega.check [FLe (NV 0) (NV 1), FLe (NAdd (NV 1) (NLit 1)) (NV 2)] (GLt (NV 0) (NV 2))
  (Then (Input 0) (Then (Input 1) (Then NegGoal (Then (Combine [MkPair 1 0, MkPair 1 1, MkPair 1 2]) (Close 3)))))

-- No `n`: with `x = 1`, `x <= 0` is false, and its negation's row `x - 1 >= 0`
-- keeps `x`'s coefficient, so `Close` refuses it.
test "check: no dropped coefficient" := Bool.not (Omega.check [] (GLe (NV 0) (NLit 0)) (Then NegGoal (Close 0)))

-- Malformed certificates: each must be refused. Each comes with the same
-- certificate corrected, which is accepted, so the refusal is for the reason named.

-- A row that doesn't exist yet: `Combine` naming row 5 when there are 2 (it would read as the zero row).
test "check refuses: Combine of a missing row" := Bool.not (Omega.check [FLt (NV 0) (NV 0)] GVoid
  (Then (Input 0) (Then (Combine [MkPair 1 0, MkPair 1 5]) (Close 1))))

test "check accepts: Combine of an existing row" := Omega.check [FLt (NV 0) (NV 0)] GVoid
  (Then (Input 0) (Then (Combine [MkPair 1 0, MkPair 1 0]) (Close 1)))

-- `Close` on a row that doesn't exist (the zero row isn't a contradiction).
test "check refuses: Close of a missing row" := Bool.not (Omega.check [FLt (NV 0) (NV 0)] GVoid
  (Then (Input 0) (Close 3)))

test "check accepts: Close of an existing row" := Omega.check [FLt (NV 0) (NV 0)] GVoid
  (Then (Input 0) (Close 0))

-- `Input 3` with one fact: it would give the zero row, and row 1 would close.
test "check refuses: Input of a missing fact" := Bool.not (Omega.check [FLt (NV 0) (NV 0)] GVoid
  (Then (Input 3) (Then (Input 0) (Close 1))))

test "check accepts: Input of an existing fact" := Omega.check [FLt (NV 0) (NV 0)] GVoid
  (Then (Input 0) (Then (Input 0) (Close 1)))

-- `NegGoal` when the goal is `GVoid`: there is no negation to use.
test "check refuses: NegGoal for a void goal" := Bool.not (Omega.check [FLt (NV 0) (NV 0)] GVoid
  (Then NegGoal (Then (Input 0) (Close 1))))

test "check accepts: NegGoal for a goal that has one" := Omega.check [FLt (NV 0) (NV 0)] (GLe (NV 0) (NV 0))
  (Then NegGoal (Then (Input 0) (Close 1)))

-- A row made in the left branch of a `Split` isn't there in the right one:
-- the left makes row 2, the right (which has rows 0 and 1) closes it.
test "check refuses: Close of the other branch's row" := Bool.not (Omega.check [FLt (NV 0) (NV 0)] GVoid
  (Then (Input 0) (Split (MkRow 0 [1] []) (Then (Combine [MkPair 1 0]) (Close 2)) (Close 2))))

test "check accepts: Close of the branch's own row" := Omega.check [FLt (NV 0) (NV 0)] GVoid
  (Then (Input 0) (Split (MkRow 0 [1] []) (Then (Combine [MkPair 1 0]) (Close 2)) (Close 0)))

-- The same for `Combine`: the right branch's new row would be 2, which it names.
test "check refuses: Combine of the other branch's row" := Bool.not (Omega.check [FLt (NV 0) (NV 0)] GVoid
  (Then (Input 0) (Split (MkRow 0 [1] []) (Then (Combine [MkPair 1 0]) (Close 2)) (Then (Combine [MkPair 1 0, MkPair 1 2]) (Close 2)))))

test "check accepts: Combine of the branch's own rows" := Omega.check [FLt (NV 0) (NV 0)] GVoid
  (Then (Input 0) (Split (MkRow 0 [1] []) (Then (Combine [MkPair 1 0]) (Close 2)) (Then (Combine [MkPair 1 0]) (Close 2))))

-- `Divide` by 0 would leave the row alone, and row 1 would close.
test "check refuses: Divide by 0" := Bool.not (Omega.check [FLt (NV 0) (NV 0)] GVoid
  (Then (Input 0) (Then (Divide 0 0) (Close 1))))

test "check accepts: Divide by 1" := Omega.check [FLt (NV 0) (NV 0)] GVoid
  (Then (Input 0) (Then (Divide 0 1) (Close 1)))

-- `Divide` where `d` doesn't divide a `Nat` coefficient (3 at atom 7, by 2 ...).
test "check refuses: Divide by a non-divisor, Nat coefficient" := Bool.not (Omega.check
  [FLe (NLit 1) (MulLeft 3 (NV 7)), FLe (MulLeft 3 (NV 7)) (NLit 0)] GVoid
  (Then (Input 0) (Then (Input 1) (Then (Divide 0 2) (Then (Divide 1 2) (Then (Combine [MkPair 1 2, MkPair 1 3]) (Close 4)))))))

-- ... and by 3, which divides it.
test "check accepts: Divide by a divisor, Nat coefficient" := Omega.check
  [FLe (NLit 1) (MulLeft 3 (NV 7)), FLe (MulLeft 3 (NV 7)) (NLit 0)] GVoid
  (Then (Input 0) (Then (Input 1) (Then (Divide 0 3) (Then (Divide 1 3) (Then (Combine [MkPair 1 2, MkPair 1 3]) (Close 4))))))

-- The same for an `Int` coefficient: the split's row `3 * y >= 0`, divided by 2.
test "check refuses: Divide by a non-divisor, Int coefficient" := Bool.not (Omega.check [FLt (NV 0) (NV 0)] GVoid
  (Then (Input 0) (Split (MkRow 0 [] [3]) (Then (Divide 1 2) (Close 0)) (Close 0))))

test "check accepts: Divide by a divisor, Int coefficient" := Omega.check [FLt (NV 0) (NV 0)] GVoid
  (Then (Input 0) (Split (MkRow 0 [] [3]) (Then (Divide 1 3) (Close 0)) (Close 0)))

-- `Close` needs every coefficient 0, including one past the facts' highest atom:
-- `x_5 - 1 >= 0` is satisfiable.
test "check refuses: Close with an atom beyond the facts" := Bool.not (Omega.check [FLt (NV 0) (NV 0)] GVoid
  (Then (Input 0) (Then (NatNonneg 5) (Then (Combine [MkPair 1 0, MkPair 1 1]) (Close 2)))))

test "check accepts: Close without that atom" := Omega.check [FLt (NV 0) (NV 0)] GVoid
  (Then (Input 0) (Then (NatNonneg 5) (Then (Combine [MkPair 1 0]) (Close 2))))

-- `Divide` rounds down: `2x - 1 >= 0` gives `x - 1 >= 0`, so with `-x >= 0` the sum is `-1`
-- (rounding to `x + 0` would not close).
test "check: Divide floors a negative constant" := Omega.check [FLe (NLit 1) (MulLeft 2 (NV 0)), FLe (NV 0) (NLit 0)] GVoid
  (Then (Input 0) (Then (Input 1) (Then (Divide 0 2) (Then (Combine [MkPair 1 2, MkPair 1 1]) (Close 3)))))

-- `1 - 2x >= 0` gives `-x >= 0` (the `1 / 2` is 0), so with `x - 1 >= 0` the sum is `-1`.
test "check: Divide floors a positive constant" := Omega.check [FLe (MulLeft 2 (NV 0)) (NLit 1), FLe (NLit 1) (NV 0)] GVoid
  (Then (Input 0) (Then (Input 1) (Then (Divide 0 2) (Then (Combine [MkPair 1 2, MkPair 1 1]) (Close 3)))))

-- `Cases` (stage 2): `t = a - b` and `b <= a` give `t + b <= a`. The left case
-- (`b <= a`, `t + b = a`) has rows 0 to 2, and its row 1, `a - (t + b) >= 0`,
-- meets the goal's negation; the right case (`a < b`, `t = 0`) has `b - a - 1 >= 0`,
-- which meets the fact `b <= a` (input row 2: `FSub` gives two rows first).
test "check: Cases on a subtraction" := Omega.check [FSub (NV 0) (NV 1) (NV 2), FLe (NV 2) (NV 1)] (GLe (NAdd (NV 0) (NV 2)) (NV 1))
  (Cases 0
    (Then NegGoal (Then (Combine [MkPair 1 1, MkPair 1 3]) (Close 4)))
    (Then (Input 2) (Then (Combine [MkPair 1 0, MkPair 1 3]) (Close 4))))

-- The same certificate naming a fact without cases, or one that isn't there.
test "check refuses: Cases on a fact without cases" := Bool.not (Omega.check [FLe (NV 2) (NV 1), FSub (NV 0) (NV 1) (NV 2)] (GLe (NAdd (NV 0) (NV 2)) (NV 1))
  (Cases 0
    (Then NegGoal (Then (Combine [MkPair 1 1, MkPair 1 3]) (Close 4)))
    (Then (Input 0) (Then (Combine [MkPair 1 0, MkPair 1 3]) (Close 4)))))

test "check refuses: Cases on a missing fact" := Bool.not (Omega.check [FSub (NV 0) (NV 1) (NV 2), FLe (NV 2) (NV 1)] (GLe (NAdd (NV 0) (NV 2)) (NV 1))
  (Cases 5
    (Then NegGoal (Then (Combine [MkPair 1 1, MkPair 1 3]) (Close 4)))
    (Then (Input 2) (Then (Combine [MkPair 1 0, MkPair 1 3]) (Close 4)))))

-- A row of one case isn't there in the other: the right branch closing on the
-- left case's row 1 is refused.
test "check refuses: Cases using the other case's row" := Bool.not (Omega.check [FSub (NV 0) (NV 1) (NV 2), FLe (NV 2) (NV 1)] (GLe (NAdd (NV 0) (NV 2)) (NV 1))
  (Cases 0
    (Then NegGoal (Then (Combine [MkPair 1 1, MkPair 1 3]) (Close 4)))
    (Then NegGoal (Then (Combine [MkPair 1 1, MkPair 1 3]) (Close 4)))))
