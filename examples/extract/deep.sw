-- Deeply nested values cross the boundary. Decoding and encoding keep their
-- own stack, so a user's list of a million elements, or a tree a million
-- deep, is fine (`deep_values_cross_the_boundary` in
-- crates/cli/tests/extract.rs). These functions are loops, so they handle
-- them too.
--
-- run: echo (More 1 (More 2 End))
-- run: count (More 1 (More 2 End))
-- run: flip (More 1 (More 2 (More 3 End)))
-- run: build 3
-- run: echoTree (Node (Node Leaf Leaf) Leaf)
-- run: spine 3
-- run: echoSeq (Step "a" (Step "b" Stop))
-- run: steps 2

-- A list of numbers, written out.
type Chain : Type =
  | End
  | More (head : Nat) (tail : Chain)

export
echo : Chain -> Chain
echo c = c

countOnto : Nat -> Chain -> Nat
countOnto n End        = n
countOnto n (More h t) = countOnto (Succ n) t

export
count : Chain -> Nat
count c = countOnto 0 c

flipOnto : Chain -> Chain -> Chain
flipOnto acc End        = acc
flipOnto acc (More h t) = flipOnto (More h acc) t

export
flip : Chain -> Chain
flip c = flipOnto End c

-- `More 0 (More 1 … (More (n - 1) End))`.
buildOnto : Chain -> Nat -> Chain
buildOnto acc Zero     = acc
buildOnto acc (Succ n) = buildOnto (More n acc) n

export
build : Nat -> Chain
build n = buildOnto End n

type Tree : Type =
  | Leaf
  | Node (left : Tree) (right : Tree)

export
echoTree : Tree -> Tree
echoTree t = t

-- A tree `n` deep, down its left side.
spineOnto : Tree -> Nat -> Tree
spineOnto t Zero     = t
spineOnto t (Succ n) = spineOnto (Node t Leaf) n

export
spine : Nat -> Tree
spine n = spineOnto Leaf n

-- A list with a parameter.
type Seq (a : Type) : Type =
  | Stop
  | Step (item : a) (rest : Seq a)

export
echoSeq : Seq Text -> Seq Text
echoSeq s = s

stepsOnto : Seq Text -> Nat -> Seq Text
stepsOnto s Zero     = s
stepsOnto s (Succ n) = stepsOnto (Step "x" s) n

export
steps : Nat -> Seq Text
steps n = stepsOnto Stop n
