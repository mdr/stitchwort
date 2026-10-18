-- Exact arity needing the elaborator: the alias unfolds to two arguments.

def BinOp : Type := Nat -> Nat -> Nat

def add : BinOp
  | Zero, y => y
  | Succ x, y => Succ (add x y)

def sub : BinOp
  | a, b => a - b

def zero : BinOp := \a b => 0

-- converter report:
-- line 7: add: moved lambda parameter(s) y
-- line 8: add: moved lambda parameter(s) y
-- line 11: sub: moved lambda parameter(s) b
