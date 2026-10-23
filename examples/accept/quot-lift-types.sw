-- A quotient of types, lifted into data (docs/proposals/map-equality.md
-- §7.4.2, test A7). The representative is a type, so it's erased (D921): at
-- run time a `QTy` is the placeholder, and a lift is the application `f q`,
-- which takes `q` or not as `f`'s own type says. Every runner
-- (`run --reference`, `test`, `run`, `run --js`) gives `7` with the lifted
-- function a definition, a lambda and a variable (the last needs D922's
-- calling convention for function values).
--
--   $ stitchwort run examples/accept/quot-lift-types.sw
--   7
--   7
--   7
--   8
--   1
import Std (IO, Nat)

def QTy: Type 1 := Quot (Type 0) (a b => a = b)

def seven (a: Type 0): Nat := 7

def answer: Nat := Quot.lift seven (a b h => rfl) (Quot.mk Nat: QTy)

def answerLambda: Nat := Quot.lift (a => 7) (a b h => rfl) (Quot.mk Nat: QTy)

def liftWith (g: Type 0 -> Nat) (q: QTy): Nat := Quot.lift g (a b h => J (b' h' => g a = g b') rfl h) q

def answerVariable: Nat := liftWith seven (Quot.mk Nat)

def eightVariable: Nat := liftWith (a => 8) (Quot.mk (List Nat))

-- For contrast, a carrier whose elements are data: the representative is
-- passed to the lifted function.
def BoolEq (x: Bool) (y: Bool): Prop := x = y
def QE: Type := Quot Bool BoolEq

def toNat (b: Bool): Nat := if b then 1 else 0

def one: Nat := Quot.lift toNat (x y same => rewrite same in rfl) (Quot.mk True: QE)

theorem answerIsSeven: answer = 7 := rfl

test "a definition lifted" := answer == 7
test "a lambda lifted" := answerLambda == 7
test "a variable lifted" := answerVariable == 7
test "a variable lifted, given a lambda" := eightVariable == 8
test "a data representative" := one == 1

def main(): {IO} () :=
  IO.print (Nat.toText answer)
  IO.print (Nat.toText answerLambda)
  IO.print (Nat.toText answerVariable)
  IO.print (Nat.toText eightVariable)
  IO.print (Nat.toText one)
