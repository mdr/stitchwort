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

export
size : Tree -> Nat
size (Node n kids) = Succ (sizeForest kids)

export
sizeForest : Forest -> Nat
sizeForest FNil         = 0
sizeForest (FCons t ts) = size t + sizeForest ts

-- One more on every label.
export
relabel : Tree -> Tree
relabel (Node n kids) = Node (Succ n) (relabelAll kids)

relabelAll : Forest -> Forest
relabelAll FNil         = FNil
relabelAll (FCons t ts) = FCons (relabel t) (relabelAll ts)

export
echoTree : Tree -> Tree
echoTree t = t

export
echoForest : Forest -> Forest
echoForest f = f

-- `n` deep, each node's only child the one below it. A loop.
deepOnto : Tree -> Nat -> Tree
deepOnto t Zero     = t
deepOnto t (Succ n) = deepOnto (Node n (FCons t FNil)) n

export
deep : Nat -> Tree
deep n = deepOnto (Node 0 FNil) n

-- With a parameter.
type Rose (a : Type) : Type =
  | Bloom (value : a) (kids : Roses a)

type Roses (a : Type) : Type =
  | NoRoses
  | MoreRoses (first : Rose a) (rest : Roses a)

flattenRose : Rose a -> List a
flattenRose (Bloom x kids) = Cons x (flattenRoses kids)

flattenRoses : Roses a -> List a
flattenRoses NoRoses          = Nil
flattenRoses (MoreRoses r rs) = List.append (flattenRose r) (flattenRoses rs)

export
flatten : Rose Text -> List Text
flatten r = flattenRose r

export
echoRose : Rose Text -> Rose Text
echoRose r = r
