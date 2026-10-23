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
type Chain: Type =
  | End
  | More (head: Nat) (tail: Chain)

export def echo (c: Chain): Chain := c

def countOnto (n: Nat): Chain -> Nat
  | End => n
  | More h t => countOnto (Succ n) t

export def count (c: Chain): Nat := countOnto 0 c

def flipOnto (acc: Chain): Chain -> Chain
  | End => acc
  | More h t => flipOnto (More h acc) t

export def flip (c: Chain): Chain := flipOnto End c

-- `More 0 (More 1 … (More (n - 1) End))`.
def buildOnto (acc: Chain): Nat -> Chain
  | Zero => acc
  | Succ n => buildOnto (More n acc) n

export def build (n: Nat): Chain := buildOnto End n

type Tree: Type =
  | Leaf
  | Node (left: Tree) (right: Tree)

export def echoTree (t: Tree): Tree := t

-- A tree `n` deep, down its left side.
def spineOnto (t: Tree): Nat -> Tree
  | Zero => t
  | Succ n => spineOnto (Node t Leaf) n

export def spine (n: Nat): Tree := spineOnto Leaf n

-- A list with a parameter.
type Seq (a: Type): Type =
  | Stop
  | Step (item: a) (rest: Seq a)

export def echoSeq (s: Seq Text): Seq Text := s

def stepsOnto (s: Seq Text): Nat -> Seq Text
  | Zero => s
  | Succ n => stepsOnto (Step "x" s) n

export def steps (n: Nat): Seq Text := stepsOnto Stop n
