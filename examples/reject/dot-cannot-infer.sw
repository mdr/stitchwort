-- expect-error: E-CANNOT-INFER
-- The lambda is checked after `Empty`, and `Empty` doesn't fix `p`'s type.
-- `Bag.map Empty ((p: Person) => p.name)` works.

type Person = { name: Text }

type Bag (a: Type): Type =
  | Empty
  | Put (x: a) (rest: Bag a)

def Bag.map: Bag a → (f: a → b) → Bag b
  | Empty, f => Empty
  | Put x xs, f => Put (f x) (Bag.map xs f)

def names: Bag Text := Bag.map Empty (p => p.name)
