# 5. Interfaces

An **interface** names operations a type can support, like a Scala trait used as a type class, or a Rust trait. An **instance** says how one type supports it. A function asks for an instance with an `auto` parameter, and the compiler finds it from the type, so callers don't pass it.

## What every type gets

Before writing interfaces of your own, know what you get for free. Every data type and record you declare gets, when its fields have them too:

- `==` and `!=` (the `DecEq` interface);
- an order, `<`, `<=`, `Ord.compare`, and so `List.sort` and use as a `Map` key (the `Ord` interface): constructors in the order they're declared, then fields left to right;
- text for `${…}` (the `Show` interface), in the form you'd write the value in source.

There's no `deriving` clause to write:

<!-- snippet: interfaces.sw#derived -->
```stitchwort
type Suit =
  | Clubs
  | Diamonds
  | Hearts
  | Spades

type Card = { rank: Nat, suit: Suit }

def aceOfSpades: Card := { rank = 14, suit = Spades }
def twoOfClubs: Card := { rank = 2, suit = Clubs }

test "equality" := aceOfSpades == aceOfSpades ∧ aceOfSpades ≠ twoOfClubs
test "order: fields left to right" := twoOfClubs < aceOfSpades
test "constructors in declared order" := List.sort [Spades, Clubs, Hearts] == [Clubs, Hearts, Spades]
test "text" := "${twoOfClubs}" == "{ rank = 2, suit = Clubs }"
```

A type gets none of these when one of its fields can't have it. A function can't be compared, so a record with a function field has no `==`, and the error says why:

<!-- snippet: errors/no-instance.sw -->
```stitchwort
type Rule = { name: Text, applies: Nat → Bool }

def sameRule (a: Rule) (b: Rule): Bool := a == b
```

<!-- output: check errors/no-instance.sw -->
```text
[E-INSTANCE-NONE] Error: no `DecEq` instance for `Rule`
   ╭─[ errors/no-instance.sw:3:43 ]
   │
 3 │ def sameRule (a: Rule) (b: Rule): Bool := a == b
   │                                           ───┬──
   │                                              ╰──── this needs `DecEq Rule`
   │
   │ Note 1: `==` isn't derived for `Rule`: its field `applies` is a function, and functions can't be compared
   │
   │ Note 2: an instance of `DecEq` for `Rule` can be declared in `Main`
───╯
```

## Declaring an interface

An interface is a record type with one type parameter, whose fields are its operations. An instance is a definition marked `instance`, whose value is a record of the operations:

<!-- snippet: interfaces.sw#interface -->
```stitchwort
interface Describe (a: Type) =
  { describe: a → Text }

instance Suit.instDescribe: Describe Suit :=
  { describe = suit => match suit with
    | Clubs => "♣"
    | Diamonds => "♦"
    | Hearts => "♥"
    | Spades => "♠" }

instance Card.instDescribe: Describe Card :=
  { describe = card => "${card.rank}${Describe.describe card.suit}" }

test "describe a card" := Describe.describe aceOfSpades == "14♠"
```

`Describe.describe` is the operation, found for the type of its argument. Instances are named, by convention `Type.instInterface`. There is at most one instance of an interface for a type, and it lives with the interface or with the type (in the same file, or the same namespace in a project), so it is always the same one wherever the type is used.

## Asking for an instance: `auto`

A function that works for any type with an instance takes an `[auto …]` parameter. Callers don't pass it; the compiler finds the instance for the type at hand:

<!-- snippet: interfaces.sw#auto -->
```stitchwort
def describeAll [auto describer: Describe a] (items: List a): Text := Text.join (items.map Describe.describe) ' '

test "the instance is found from the type" := describeAll [aceOfSpades, twoOfClubs] == "14♠ 2♣"
```

An instance can itself need instances of the types inside it, so one declaration covers lists of anything describable:

<!-- snippet: interfaces.sw#instance-with-context -->
```stitchwort
instance Describe.instList [auto Describe a]: Describe (List a) :=
  { describe = items => "[${describeAll items}]" }

test "instances for containers" := Describe.describe [[twoOfClubs], [aceOfSpades]] == "[[2♣] [14♠]]"
```

`[auto Describe a]`, without a name, also works when you never need to refer to the instance.

## Another instance, by name

Sometimes a type needs to be described, compared or sorted in another way. Write the alternative as a plain `def` of the interface's type. `auto` never finds it; pass it by name where you want it:

<!-- snippet: interfaces.sw#named-alternative -->
```stitchwort
def plain: Describe Suit := { describe = suit => "${suit}" }

test "passing another by name" := describeAll [describer := plain] [Hearts, Spades] == "Hearts Spades"
```

For sorting, the simplest way is often a comparison function or a key:

<!-- snippet: interfaces.sw#custom-order -->
```stitchwort
def highestFirst (cards: List Card): List Card := cards.sortBy (a b => Ord.compare b.rank a.rank)

test "sort another way" := highestFirst [twoOfClubs, aceOfSpades] == [aceOfSpades, twoOfClubs]
test "sort by a key" := [aceOfSpades, twoOfClubs].sortOn (.suit) == [twoOfClubs, aceOfSpades]
```

## Replacing what's derived

A type's own instance replaces the derived one. `Show.fromText` builds a `Show` instance from one function:

<!-- snippet: interfaces.sw#custom-show -->
```stitchwort
type Celsius = { degrees: Int }

instance Celsius.instShow: Show Celsius := Show.fromText (temperature => "${temperature.degrees}°C")

def freezing: Celsius := { degrees = 0 }

test "custom text" := "${freezing}" == "0°C"
test "inside a list" := "${[freezing]}" == "[0°C]"
```

## Interfaces with laws

An interface can include **laws**: fields whose types are statements, which every instance must prove. The library's `Add` (what `+` and `List.sum` use) says that adding is associative and commutative, with `zero` as its unit:

<!-- snippet: ../../../crates/elab/src/std/core/AddMul.sw@Add -->
```stitchwort
interface Add (a: Type) = {
  zero: a,
  add: a → a → a,
  zeroAdd: (x: a) → add zero x = x,
  assoc: (x: a) → (y: a) → (z: a) → add (add x y) z = add x (add y z),
  comm: (x: a) → (y: a) → add x y = add y x
}
```

So an instance for a type of your own needs a proof of each law. For a record of two numbers, each law follows from the same law for `Int`, field by field (`Vector.ext` says two `Vector`s are equal when their fields are; [chapter 10](10-proofs.md) explains proofs):

<!-- snippet: interfaces.sw#add -->
```stitchwort
type Vector = { dx: Int, dy: Int }

instance Vector.instAdd: Add Vector := {
  zero = { dx = 0, dy = 0 },
  add = a b => { dx = a.dx + b.dx, dy = a.dy + b.dy },
  zeroAdd = v => Vector.ext { dx = 0 + v.dx, dy = 0 + v.dy } v (Int.zeroAdd v.dx) (Int.zeroAdd v.dy),
  assoc = u v w => Vector.ext { dx = u.dx + v.dx + w.dx, dy = u.dy + v.dy + w.dy } { dx = u.dx + (v.dx + w.dx), dy = u.dy + (v.dy + w.dy) } (Int.addAssoc u.dx v.dx w.dx) (Int.addAssoc u.dy v.dy w.dy),
  comm = u v => Vector.ext { dx = u.dx + v.dx, dy = u.dy + v.dy } { dx = v.dx + u.dx, dy = v.dy + u.dy } (Int.addComm u.dx v.dx) (Int.addComm u.dy v.dy)
}

def moves: List Vector := [{ dx = 1, dy = 2 }, { dx = -3, dy = 1 }]

test "sum uses Add" := moves.sum == { dx = -2, dy = 3 }
```

Laws are erased: they cost nothing at run time. In exchange, a theorem about `List.sum` holds for every type with an `Add` instance.

The library's interfaces are `DecEq` (`==`), `Ord` (order), `Show` (text), `Add` (`+`) and `Mul` (`*`). More: [syntax.md, Interfaces](../syntax.md#interfaces), and the design note [interfaces.md](../proposals/interfaces.md).
