-- expect-error: E-TYPE-MISMATCH
-- In the `False` branch the payload is a `Bool`, so it can't be used as a
-- number, even though the `True` branch's payload is one.
def PayloadType: Bool -> Type
  | True  => Nat
  | False => Bool

type Tree: Type =
  | Leaf
  | Node (tag: Bool) (payload: PayloadType tag) (rest: PayloadType tag -> Tree)

def depth: Tree -> Nat
  | Leaf              => 0
  | Node True  n rest => Succ (depth (rest (n + 1)))
  | Node False b rest => Succ (depth (rest (b + 1)))
