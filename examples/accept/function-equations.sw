-- Generated equations, one for each arm (docs/proposals/function-equations.md,
-- stage 1a): `f.eqK` states arm K of `f`, with the earlier arms that
-- overlap it as hypotheses. Each is an ordinary theorem the kernel checks.
import Std (Bool, Char, Eq, Int, List, Nat, Option, Void, byDecision)

type Num =
  | Reg (value: Nat)
  | Pr (left: Num) (right: Num)

-- Plain arms: `addLeftmost.eq1` and `addLeftmost.eq2`.
def addLeftmost (amount: Nat): Num → Num
  | Reg value => Reg (value + amount)
  | Pr left right => Pr (addLeftmost amount left) right

theorem addLeftmostPair ∀ (amount: Nat) (l: Num) (r: Num):
    addLeftmost amount (Pr l r) = Pr (addLeftmost amount l) r :=
  addLeftmost.eq2 amount l r

-- An overlap: arm 3 holds only where arm 2 doesn't, so `ex.eq3` takes
-- `notArm2: (a: Nat) → (b: Nat) → left = Reg a → right = Reg b → Void`.
def ex (depth: Nat): Num → Nat
  | Reg _ => 0
  | Pr (Reg a) (Reg b) => if 4 ≤ depth then a + b else 0
  | Pr left right => ex (depth + 1) left + ex (depth + 1) right

-- Where the left part is known to be a pair, `cases` proves the hypothesis.
theorem exPairLeft ∀ (depth: Nat) (x: Num) (y: Num) (r: Num):
    ex depth (Pr (Pr x y) r) = ex (depth + 1) (Pr x y) + ex (depth + 1) r :=
  ex.eq3 depth (Pr x y) r cases

def isReg: Num → Bool
  | Reg _ => True
  | Pr _ _ => False

-- From a fact about the left part instead.
theorem exNotReg ∀ (depth: Nat) (left: Num) (right: Num) (notReg: isReg left = False):
    ex depth (Pr left right) = ex (depth + 1) left + ex (depth + 1) right :=
  ex.eq3 depth left right (a b el er => Bool.trueNotFalse (rewrite el at notReg in notReg))

-- The call is stuck on `left`, so `rewrite` finds it.
theorem exAtLeast ∀ (depth: Nat) (left: Num) (right: Num)
    (h: ∀ (a b: Nat) => left = Reg a → right = Reg b → Void):
    ex (depth + 1) left ≤ ex depth (Pr left right) :=
  rewrite ex.eq3 depth left right h in omega

-- Number literals: the catch-all takes `x1 ≠ 3` and `x1 ≠ 7`, which `omega`
-- proves.
def kind: Nat → Nat
  | 3 => 1
  | 7 => 2
  | _ => 0

theorem kindBig ∀ (n: Nat) (big: 10 ≤ n): kind n = 0 := kind.eq3 n omega omega

-- Character literals on one variable: merged into one `char ∉ ['k', 'j']`.
type Command = | Up | Down

def commandOf (char: Char): Option Command := match char with
  | 'k' => Some Up
  | 'j' => Some Down
  | _ => None

def keys: List Char := ['k', 'j']

theorem commandOfOther ∀ (char: Char) (other: char ∉ keys): commandOf char = None :=
  commandOf.eq3 char other

theorem commandOfX: commandOf 'x' = None := commandOf.eq3 'x' byDecision

-- An arm that also constrains another column keeps Lean's form:
-- `notArm1: c = 'k' → xs = [] → Void`.
def keyed: Char → List Char → Nat
  | 'k', [] => 1
  | c, xs => 2

theorem keyedNonEmpty ∀ (c: Char) (x: Char) (xs: List Char): keyed c [x, ..xs] = 2 :=
  keyed.eq2 c [x, ..xs] (ck nil => List.consNotNil x xs nil)

-- `Int` literals.
def sign: Int → Nat
  | 0 => 0
  | (-1) => 1
  | _ => 2

theorem signFive: sign 5 = 2 := sign.eq3 5 byDecision byDecision

-- Or-patterns: one equation for each alternative, `orp.eq1.or1` and
-- `orp.eq1.or2`; the catch-all takes both as hypotheses.
def orp: Num → Nat
  | Reg 0 | Reg 1 => 5
  | _ => 6

theorem orpOne: orp (Reg 1) = 5 := orp.eq1.or2

theorem orpPair ∀ (l: Num) (r: Num): orp (Pr l r) = 6 := orp.eq2 (Pr l r) cases cases

-- `decreasing`: the arms don't hold by `rfl` on unknown arguments, so the
-- equation is what states them.
def takeFirst [a: Type] (xs: List a): Nat → List a
    decreasing List.length xs
  | Zero => []
  | Succ k =>
    match xs with
      | [] => []
      | [x, ..rest] => [x, ..takeFirst rest k [decreasing := Nat.leRefl (List.length rest)]]

theorem takeNone ∀ [a: Type] (xs: List a): takeFirst xs 0 = [] := takeFirst.eq1 xs

-- `opaque`: checked with `unfolding secret`, as `secret.unfold` is.
opaque def secret: Nat → Nat
  | 0 => 1
  | n => n + 2

theorem secretPositive ∀ (n: Nat) (h: 0 < n): secret n = n + 2 := secret.eq2 n omega

-- A local definition gets its own: `withLocal.go.eq2`.
def withLocal (n: Nat): Nat :=
  def go: Nat → Nat
    | 0 => 1
    | Succ m => go m
  go n

theorem goStep ∀ (m: Nat): withLocal.go (Succ m) = withLocal.go m := withLocal.go.eq2 m

-- A `:=` body that is a `match` on its parameters counts as arms (D2187).
def isZero (n: Nat): Bool := match n with
  | 0 => True
  | _ => False

theorem isZeroOfPos ∀ (n: Nat) (h: 0 < n): isZero n = False := isZero.eq2 n omega

-- An effect-polymorphic definition's equations are at the empty row: the
-- library's `List.filter.eq2` is `List.filter (Cons x xs) p = List.filterStep
-- x (List.filter xs p) (p x)`.
theorem filterCons ∀ (x: Nat) (xs: List Nat) (p: Nat → Bool) (h: p x = False):
    List.filter [x, ..xs] p = List.filter xs p :=
  rewrite List.filter.eq2 x xs p, h in rfl
