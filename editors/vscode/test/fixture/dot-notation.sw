-- Dot notation by type (docs/proposals/namespaces.md §4.8): `e.f` is `T.f`
-- with `e` in the place of `T.f`'s first parameter of type `T`, where `T` is
-- `e`'s type. A record's field is the case where `T.f` is its projection.

type Bag (a: Type): Type =
  | Empty
  | Put (x: a) (rest: Bag a)

def Bag.length: Bag a -> Nat
  | Empty => 0
  | Put _ b => 1 + b.length

type Person = { name: Text, age: Nat }

def Bag.map (f: a -> b): Bag a -> Bag b
  | Empty => Empty
  | Put x xs => Put (f x) (Bag.map f xs)

def Price: Type := Nat

def Price.show (p: Price): Text := "$" ++ p.toText

type Sized (n: Nat) = { value: Nat }

def Sized.read (n: Nat) (s: Sized n): Nat := s.value

def names (people: Bag Person): Bag Text := people.map (p => p.name)

def lengths (ts: Bag Text): Bag Nat := ts.map (t => t.length)

def splitLine (line: Text): List Text := line.split ','

def splitter (t: Text): Char -> List Text := t.split

def showPrice (p: Price): Text := p.show

def showNat (n: Nat): Text := n.toText

def readIt (s: Sized 3): Nat := s.read 3

def nameLength (p: Person): Nat := p.name.length

def symm (x: Nat) (y: Nat) (p: x = y): y = x := p.sym

def projected (ps: Bag Person): Bag Text := Bag.map Person.name ps

def letp (n: Nat): Text :=
  let q: Price := n
  q.show

def mkPrice (n: Nat): Price := n

def lets (n: Nat): Text :=
  let q := mkPrice n
  q.show

def applied (n: Nat): Text := (mkPrice n).show

test "split" := (splitLine "a,b").length == 2
test "partial split" := (splitter "a,b,c" ',').length == 3
test "price" := showPrice 3 == "$3"
test "read" := readIt { value = 7 } == 7
test "names" := (names (Put { name = "ab", age = 1 } Empty)).length == 1
test "name length" := nameLength { name = "abc", age = 1 } == 3
test "letp" := letp 4 == "$4"
test "lets" := lets 4 == "$4"
test "applied" := applied 4 == "$4"
test "nat" := showNat 4 == "4"

-- The pre-pass can't know which `label` `s.label` means, so it groups
-- `Shape.describe` with every `….label` (§5): here with `Tile.label` too.
type Shape = { name: Text }
type Tile  = { shape: Shape }

def Shape.label (s: Shape): Text := s.name

def Tile.label (t: Tile): Text := t.shape.describe

def Shape.describe (s: Shape): Text := s.label


test "cycle" := Tile.label { shape = { name = "a" } } == "a"

-- The receiver runs first, then the arguments as written, though the call
-- is `Shape.shout suffix s` (§4.8.2).
ability Log where
  log: Text -> {Log} ()

def Shape.shout (suffix: Text) (s: Shape): {Log} Text :=
  log ("shout " ++ s.name)
  s.name ++ suffix

def pick (t: Text): {Log} Shape :=
  log ("pick " ++ t)
  { name = t }

def sfx (t: Text): {Log} Text :=
  log ("sfx " ++ t)
  t

def both(): {Log} Text := (pick "a").shout (sfx "!")

def collect (f: () -> {Log | e} a): {e} Pair (List Text) a :=
  handle f() with
    | return x => MkPair Nil x
    | log t, k =>
      let r := k()
      MkPair (Cons t (Pair.fst r)) (Pair.snd r)

test "order" := Text.join (',') (Pair.fst (collect both)) == "pick a,sfx !,shout a"
