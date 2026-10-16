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

type Person = { name : Text, age : Nat }

export
greet : Person -> Text
greet p = "Hello, " ++ p.name

export
birthday : Person -> Person
birthday p = { p | age = p.age + 1 }

export
rename : Text -> Person -> Person
rename n p = { p | name = n }

older : Person -> Person -> Person
older p q = if leq q.age p.age then p else q

export
oldest : List Person -> Maybe Person
oldest Nil         = Nothing
oldest (Cons p ps) = Just (oldestFrom p ps)

oldestFrom : Person -> List Person -> Person
oldestFrom p Nil         = p
oldestFrom p (Cons q qs) = oldestFrom (older p q) qs

-- A record has no tag, so a field called `tag` keeps the key `tag`;
-- `__proto__` is still `$__proto__`, and a prime is `$`.
type Weird = { tag : Text, __proto__ : Nat, constructor : Nat, x' : Nat }

export
weird : Weird -> Weird
weird w = { w | tag = w.tag ++ "!", x' = w.x' + w.constructor + w.__proto__ }

-- A parameterised record is a generic TypeScript type.
type Box (a : Type) = { value : a }

export
unbox : Box (List Nat) -> Box Nat
unbox b = { value = length b.value }

-- A proof field that depends on an earlier field, with a decision procedure.
IsSorted : List Nat -> Prop
IsSorted xs = isSorted xs = True

isSorted : List Nat -> Bool
isSorted Nil                   = True
isSorted (Cons x Nil)          = True
isSorted (Cons x (Cons y rest)) = if leq x y then isSorted (Cons y rest) else False

decIsSorted : (xs : List Nat) -> Decidable (IsSorted xs)
decIsSorted xs = decTrue (isSorted xs)

type SortedList = { items : List Nat, ok : IsSorted items }

-- Out: the proof is left out.
export
sorted : List Nat -> Maybe SortedList
sorted xs = if h : IsSorted xs then Just { items = xs, ok = h } else Nothing

-- In: `ok` is checked.
export
smallest : SortedList -> Maybe Nat
smallest { items = Nil, .. }       = Nothing
smallest { items = Cons x xs, .. } = Just x

-- A proof field about two earlier fields, checked with the prelude's
-- `decEqNat`.
type Sized = { items : List Nat, size : Nat, ok : length items = size }

export
total : Sized -> Nat
total s = s.size

-- Records inside records.
type Team = { lead : Person, size : Nat }

export
team : Team -> Team
team t = { t | lead = birthday t.lead }
