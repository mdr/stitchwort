-- Declared records (docs/proposals/records.md, stage 1): a record type is a
-- new type with named fields, written and read by name.

type Person = { name : Text, age : Nat }

alice : Person
alice = { name = "Alice", age = 30 }

-- Fields may be given in any order.
bob : Person
bob = { age = 25, name = "Bob" }

birthday : Person -> Person
birthday p = { p | age = p.age + 1 }

describe : Person -> Text
describe { name, age } = name ++ " is " ++ Nat.toText age

-- `..` ignores the other fields.
nameOf : Person -> Text
nameOf { name, .. } = name

-- A field is read with `.`, which binds tighter than application.
older : Person -> Person -> Bool
older p q = Nat.leq q.age p.age

-- Records nest, and patterns nest inside other patterns.
type Team = { lead : Person, size : Nat }

leadName : Team -> Text
leadName t = t.lead.name

firstLead : List Team -> Text
firstLead Nil                                     = "nobody"
firstLead (Cons { lead = { name, .. }, .. } rest) = name

-- Parameters and dependent fields, as for data types: `ok` mentions the
-- earlier fields.
type Sized (a : Type) = { items : List a, size : Nat, ok : List.length items = size }

empty : Sized Nat
empty = { items = Nil, size = 0, ok = rfl }

push : a -> Sized a -> Sized a
push x s = { items = Cons x s.items, size = Succ s.size, ok = Eq.cong Succ s.ok }

-- An update must replace every later field whose type mentions a replaced
-- one: here `ok`, which mentions `items` and `size`.
grown : Sized Nat
grown = { push 1 empty | items = [1, 2], size = 2, ok = rfl }

-- A projection's type mentions the earlier fields as projections.
theorem sizeIsLength : (s : Sized a) -> List.length s.items = s.size
sizeIsLength s = s.ok

-- A record of proofs.
type Between (lo : Nat) (hi : Nat) (n : Nat) : Prop = { above : lo <= n, below : n <= hi }

theorem fiveBetween : Between 1 10 5
fiveBetween = { above = rfl, below = rfl }

theorem belowOf : Between 1 10 5 -> 5 <= 10
belowOf b = b.below

-- An update that changes nothing isn't `rfl` until stage 2 (eta), but it's
-- provable by matching. (After `->`, `{` starts a row of abilities, so a
-- record there is in parentheses.)
theorem sameAge : (p : Person) -> ({ p | age = p.age } = p)
sameAge { name, age } = rfl

-- A field called `tag` is an ordinary field.
type Labelled = { tag : Text, value : Nat }

labelled : Labelled
labelled = { tag = "x", value = 1 }

-- `==` is derived for a record whose fields all have decision procedures.
test "equal records" = alice == { name = "Alice", age = 30 }
test "unequal records" = not (alice == bob)
test "update" = (birthday alice).age == 31
test "update keeps the rest" = (birthday alice).name == "Alice"
test "pattern" = describe bob == "Bob is 25"
test "rest pattern" = nameOf alice == "Alice"
test "access binds tightly" = older alice bob
test "nested" = leadName { lead = alice, size = 3 } == "Alice"
test "nested patterns" = firstLead [{ lead = bob, size = 1 }] == "Bob"
test "dependent" = (push 7 grown).size == 3
test "tag field" = labelled.tag == "x"
