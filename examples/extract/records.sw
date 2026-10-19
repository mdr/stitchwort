-- Records at the JS boundary (docs/proposals/records.md §11): a record is a
-- plain object with its fields as keys, in declared order, and no `tag`.
-- Proof fields are left out; coming in, each is re-established by a
-- decision procedure, and an input that fails it is refused.
--
-- run: greet { name = "Ada", age = 36 }
-- run: birthday { age = 36, name = "Ada" }
-- run: rename "Grace" { name = "Ada", age = 36 }
-- run: oldest [{ name = "Ada", age = 36 }, { name = "Alan", age = 41 }]
-- run: weird { tag = "t", __proto__ = 1, constructor = 2, x' = 3 }
-- run: unbox { value = [1, 2, 3] }
-- run: sorted [1, 2, 2, 5]
-- run: sorted [2, 1]
-- run: smallest { items = [1, 4, 9], ok = rfl }
-- run: total { items = [1, 2, 3], size = 3, ok = rfl }
-- run: team { lead = { name = "Ada", age = 36 }, size = 4 }

type Person = { name: Text, age: Nat }

export def greet (p: Person): Text := "Hello, " ++ p.name

export def birthday (p: Person): Person := { p | age = p.age + 1 }

export def rename (n: Text) (p: Person): Person := { p | name = n }

def older (p: Person) (q: Person): Person := if Nat.leq q.age p.age then p else q

export def oldest: List Person -> Maybe Person
  | Nil       => Nothing
  | Cons p ps => Just (oldestFrom p ps)

def oldestFrom (p: Person): List Person -> Person
  | Nil       => p
  | Cons q qs => oldestFrom (older p q) qs

-- A record has no tag, so a field called `tag` keeps the key `tag`;
-- `__proto__` is still `$__proto__`, and a prime is `$`.
type Weird = { tag: Text, __proto__: Nat, constructor: Nat, x' : Nat }

export def weird (w : Weird) : Weird := { w | tag = w.tag ++ "!", x' = w.x' + w.constructor + w.__proto__ }

-- A parameterised record is a generic TypeScript type.
type Box (a : Type) = { value : a }

export def unbox (b : Box (List Nat)) : Box Nat := { value = List.length b.value }

-- A proof field that depends on an earlier field, with a decision procedure.
def IsSorted (xs : List Nat) : Prop := isSorted xs = True

def isSorted : List Nat -> Bool
  | Nil => True
  | Cons x Nil => True
  | Cons x (Cons y rest) => if Nat.leq x y then isSorted (Cons y rest) else False

def decIsSorted (xs : List Nat) : Decidable (IsSorted xs) := Bool.decTrue (isSorted xs)

type SortedList = { items : List Nat, ok : IsSorted items }

-- Out: the proof is left out.
export def sorted (xs : List Nat) : Maybe SortedList := if h : IsSorted xs then Just { items = xs, ok = h } else Nothing

-- In: `ok` is checked.
export def smallest : SortedList -> Maybe Nat
  | { items = Nil, .. }       => Nothing
  | { items = Cons x xs, .. } => Just x

-- A proof field about two earlier fields, checked with the prelude's
-- `Nat.decEq`.
type Sized = { items: List Nat, size: Nat, ok: List.length items = size }

export def total (s: Sized): Nat := s.size

-- Records inside records.
type Team = { lead: Person, size: Nat }

export def team (t: Team): Team := { t | lead = birthday t.lead }
