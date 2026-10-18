-- expect-error: E-CANNOT-INFER
-- In the plain call the lambda is checked before `people`, when `p`'s type
-- isn't known yet. `people.map (\p => p.name)` checks `people` first.

type Person = { name : Text }

type Bag (a : Type) : Type =
  | Empty
  | Put (x : a) (rest : Bag a)

def Bag.map (f : a -> b) : Bag a -> Bag b
  | Empty => Empty
  | Put x xs => Put (f x) (Bag.map f xs)

def names (people : Bag Person) : Bag Text := Bag.map (\p => p.name) people
