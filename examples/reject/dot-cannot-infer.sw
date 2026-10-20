-- expect-error: E-CANNOT-INFER
-- The lambda is checked after `Empty` (it comes first, but its parameter
-- type isn't known yet), and `Empty` doesn't fix `p`'s type either.
-- `Bag.map (\(p: Person) => p.name) Empty` works.

type Person = { name: Text }

type Bag (a: Type): Type =
  | Empty
  | Put (x: a) (rest: Bag a)

def Bag.map (f: a -> b): Bag a -> Bag b
  | Empty => Empty
  | Put x xs => Put (f x) (Bag.map f xs)

def names: Bag Text := Bag.map (p => p.name) Empty
