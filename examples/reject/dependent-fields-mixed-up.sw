-- expect-error: E-TYPE-MISMATCH
-- In the `False` branch the payload is a `Bool`, so it can't be used as a
-- number, even though the `True` branch's payload is one.
PayloadType : Bool -> Type
PayloadType True  = Nat
PayloadType False = Bool

type Tree : Type =
  | Leaf
  | Node (tag : Bool) (payload : PayloadType tag) (rest : PayloadType tag -> Tree)

depth : Tree -> Nat
depth Leaf                = 0
depth (Node True  n rest) = Succ (depth (rest (n + 1)))
depth (Node False b rest) = Succ (depth (rest (b + 1)))
