-- Lean's const_fold benchmark (tests/compile_bench/const_fold.lean, from the
-- reference-counting paper "Counting Immutable Beans"): build an expression
-- tree of 2^N leaves, then evaluate it, and evaluate it again after
-- reassociating its additions and multiplications to the right and folding the
-- constants. Both evaluations must agree. Prints `<eval> <eval after folding>`.
--
-- The first argument is the tree's depth N (default 20; native code's
-- recursion limit allows up to 23, which uses 4 GB; `-- 12` for a small run). The second is a
-- number of rounds (default 1): round r starts the leaf values at r, so every
-- round builds a different tree and prints its own line. Lean's original runs
-- one round at N = 23, which needs a 4 GB stack.
import Std (Fail, IO, List, Nat, Text)

--| A tiny arithmetic expression. `Var` evaluates to 0 and stands in for an
--| unknown that folding must not touch.
type Expr = | Var (name: Nat) | Val (value: Nat) | Add (left: Expr) (right: Expr) | Mul (left: Expr) (right: Expr)

--| A complete tree of `depth` levels of additions whose leaves are numbers
--| near `value` (counting down by one on the right, up on the left); a leaf
--| that reaches 0 is the variable `Var 1`.
def mkExpr: Nat → Nat → Expr
  | Zero, value => if value == 0 then Var 1 else Val value
  | Succ depth, value => Add (mkExpr depth (value + 1)) (mkExpr depth (value - 1))

--| `Add left right` with `Add` chains in `left` moved to the right.
def appendAdd: Expr → Expr → Expr
  | Add first second, third => Add first (appendAdd second third)
  | first, second => Add first second

--| `Mul left right` with `Mul` chains in `left` moved to the right.
def appendMul: Expr → Expr → Expr
  | Mul first second, third => Mul first (appendMul second third)
  | first, second => Mul first second

--| The expression with every `Add` and `Mul` chain right-associated.
def reassoc: Expr → Expr
  | Add first second =>
    let first' := reassoc first
    let second' := reassoc second
    appendAdd first' second'
  | Mul first second =>
    let first' := reassoc first
    let second' := reassoc second
    appendMul first' second'
  | e => e

--| The expression with the constants at the head of right-associated chains
--| combined.
def constFolding: Expr → Expr
  | Add first second =>
    match constFolding first, constFolding second with
      | Val a, Val b => Val (a + b)
      | Val a, Add e (Val b) => Add (Val (a + b)) e
      | Val a, Add (Val b) e => Add (Val (a + b)) e
      | first', second' => Add first' second'
  | Mul first second =>
    match constFolding first, constFolding second with
      | Val a, Val b => Val (a * b)
      | Val a, Mul e (Val b) => Mul (Val (a * b)) e
      | Val a, Mul (Val b) e => Mul (Val (a * b)) e
      | first', second' => Mul first' second'
  | e => e

def eval: Expr → Nat
  | Var name => 0
  | Val value => value
  | Add left right => eval left + eval right
  | Mul left right => eval left * eval right

--| One round: the answers for the tree whose leaves start at `start`.
def round (depth start: Nat): Text :=
  let e := mkExpr depth start
  let before := eval e
  let after := eval (constFolding (reassoc e))
  "${before} ${after}"

def main(): {IO, Fail} () :=
  let (depth, rounds) := match IO.args() with
    | [] => (20, 1)
    | [text] => (Fail.need text.toNat "expected no arguments, a depth, or a depth and rounds", 1)
    | [text, count] => (Fail.need text.toNat "expected a depth", Fail.need count.toNat "expected a number of rounds")
    | _ => Fail.fail "expected no arguments, a depth, or a depth and rounds"
  List.foldLeft (List.range 1 (rounds + 1)) () (u start => IO.print (round depth start))
