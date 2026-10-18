-- Exact arity needing the elaborator: the alias unfolds to two arguments.

BinOp : Type
BinOp = Nat -> Nat -> Nat

add : BinOp
add Zero = \y -> y
add (Succ x) = \y -> Succ (add x y)

sub : BinOp
sub a = \b -> a - b

zero : BinOp
zero = \a b -> 0
