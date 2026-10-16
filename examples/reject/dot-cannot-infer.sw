-- expect-error: E-CANNOT-INFER
-- In the plain call the lambda is checked before `people`, when `p`'s type
-- isn't known yet. `people.map (\p -> p.name)` checks `people` first.

type Person = { name : Text }

type Bag (a : Type) : Type =
  | Empty
  | Put (x : a) (rest : Bag a)

Bag.map : (a -> b) -> Bag a -> Bag b
Bag.map f Empty = Empty
Bag.map f (Put x xs) = Put (f x) (Bag.map f xs)

names : Bag Person -> Bag Text
names people = Bag.map (\p -> p.name) people
