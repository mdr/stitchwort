-- Dot notation by type (docs/proposals/namespaces.md §4.8): `e.f` is `T.f`
-- with `e` in the place of `T.f`'s first parameter of type `T`, where `T` is
-- `e`'s type. A record's field is the case where `T.f` is its projection.

type Bag (a : Type) : Type =
  | Empty
  | Put (x : a) (rest : Bag a)

Bag.length : Bag a -> Nat
Bag.length Empty = 0
Bag.length (Put _ b) = 1 + b.length

type Person = { name : Text, age : Nat }

Bag.map : (a -> b) -> Bag a -> Bag b
Bag.map f Empty = Empty
Bag.map f (Put x xs) = Put (f x) (Bag.map f xs)

Price : Type
Price = Nat

Price.show : Price -> Text
Price.show p = "$" ++ p.toText

type Sized (n : Nat) = { value : Nat }

Sized.read : (n : Nat) -> Sized n -> Nat
Sized.read n s = s.value

names : Bag Person -> Bag Text
names people = people.map (\p -> p.name)

lengths : Bag Text -> Bag Nat
lengths ts = ts.map (\t -> t.length)

splitLine : Text -> List Text
splitLine line = line.split ','

splitter : Text -> Char -> List Text
splitter t = t.split

showPrice : Price -> Text
showPrice p = p.show

showNat : Nat -> Text
showNat n = n.toText

readIt : Sized 3 -> Nat
readIt s = s.read 3

nameLength : Person -> Nat
nameLength p = p.name.length

symm : (x : Nat) -> (y : Nat) -> x = y -> y = x
symm x y p = p.sym

projected : Bag Person -> Bag Text
projected ps = Bag.map Person.name ps

letp : Nat -> Text
letp n =
  let q : Price = n
  q.show

mkPrice : Nat -> Price
mkPrice n = n

lets : Nat -> Text
lets n =
  let q = mkPrice n
  q.show

applied : Nat -> Text
applied n = (mkPrice n).show

test "split" = (splitLine "a,b").length == 2
test "partial split" = (splitter "a,b,c" ',').length == 3
test "price" = showPrice 3 == "$3"
test "read" = readIt { value = 7 } == 7
test "names" = (names (Put { name = "ab", age = 1 } Empty)).length == 1
test "name length" = nameLength { name = "abc", age = 1 } == 3
test "letp" = letp 4 == "$4"
test "lets" = lets 4 == "$4"
test "applied" = applied 4 == "$4"
test "nat" = showNat 4 == "4"

-- The pre-pass can't know which `label` `s.label` means, so it groups
-- `Shape.describe` with every `….label` (§5): here with `Tile.label` too.
type Shape = { name : Text }
type Tile  = { shape : Shape }

Shape.label : Shape -> Text
Shape.label s = s.name

Tile.label : Tile -> Text
Tile.label t = t.shape.describe

Shape.describe : Shape -> Text
Shape.describe s = s.label


test "cycle" = Tile.label { shape = { name = "a" } } == "a"

-- The receiver runs first, then the arguments as written, though the call
-- is `Shape.shout suffix s` (§4.8.2).
ability Log where
  log : Text -> {Log} ()

Shape.shout : Text -> Shape -> {Log} Text
Shape.shout suffix s =
  log ("shout " ++ s.name)
  s.name ++ suffix

pick : Text -> {Log} Shape
pick t =
  log ("pick " ++ t)
  { name = t }

sfx : Text -> {Log} Text
sfx t =
  log ("sfx " ++ t)
  t

both : () -> {Log} Text
both u = (pick "a").shout (sfx "!")

collect : (() -> {Log | e} a) -> {e} Pair (List Text) a
collect f =
  handle f () with
    | return x -> MkPair Nil x
    | log t => k ->
      let r = k ()
      MkPair (Cons t (Pair.fst r)) (Pair.snd r)

test "order" = Text.join (',') (Pair.fst (collect both)) == "pick a,sfx !,shout a"
