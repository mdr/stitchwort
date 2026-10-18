-- Data types defined together, at the JS boundary: each has a codec, and
-- their `.d.ts` types refer to each other. Decoding and encoding keep their
-- own stack, so a tree a million deep crosses both ways
-- (`deep_mutual_values_cross_the_boundary` in crates/cli/tests/extract.rs).
--
-- run: size (Node 1 (FCons (Node 2 FNil) (FCons (Node 3 FNil) FNil)))
-- run: sizeForest (FCons (Node 2 FNil) FNil)
-- run: relabel (Node 1 (FCons (Node 2 FNil) FNil))
-- run: echoTree (Node 1 (FCons (Node 2 FNil) FNil))
-- run: echoForest FNil
-- run: deep 3
-- run: flatten (Bloom "a" (MoreRoses (Bloom "b" NoRoses) NoRoses))

type Tree : Type =
  | Node (label : Nat) (kids : Forest)

type Forest : Type =
  | FNil
  | FCons (first : Tree) (rest : Forest)

export def size : Tree -> Nat
  | Node n kids => Succ (sizeForest kids)

export def sizeForest : Forest -> Nat
  | FNil       => 0
  | FCons t ts => size t + sizeForest ts

-- One more on every label.
export def relabel : Tree -> Tree
  | Node n kids => Node (Succ n) (relabelAll kids)

def relabelAll : Forest -> Forest
  | FNil       => FNil
  | FCons t ts => FCons (relabel t) (relabelAll ts)

export def echoTree (t : Tree) : Tree := t

export def echoForest (f : Forest) : Forest := f

-- `n` deep, each node's only child the one below it. A loop.
def deepOnto (t : Tree) : Nat -> Tree
  | Zero   => t
  | Succ n => deepOnto (Node n (FCons t FNil)) n

export def deep (n : Nat) : Tree := deepOnto (Node 0 FNil) n

-- With a parameter.
type Rose (a : Type) : Type =
  | Bloom (value : a) (kids : Roses a)

type Roses (a : Type) : Type =
  | NoRoses
  | MoreRoses (first : Rose a) (rest : Roses a)

def flattenRose : Rose a -> List a
  | Bloom x kids => Cons x (flattenRoses kids)

def flattenRoses : Roses a -> List a
  | NoRoses        => Nil
  | MoreRoses r rs => List.append (flattenRose r) (flattenRoses rs)

export def flatten (r : Rose Text) : List Text := flattenRose r

export def echoRose (r : Rose Text) : Rose Text := r
