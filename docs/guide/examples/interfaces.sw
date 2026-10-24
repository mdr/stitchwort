-- Chapter 5: interfaces, instances, and what every type gets for free.
import Std (Int, List, Nat, Ord, Show, Text)

-- begin derived
type Suit =
  | Clubs
  | Diamonds
  | Hearts
  | Spades

type Card = { rank: Nat, suit: Suit }

def aceOfSpades: Card := { rank = 14, suit = Spades }
def twoOfClubs: Card := { rank = 2, suit = Clubs }

test "equality" := aceOfSpades == aceOfSpades && aceOfSpades != twoOfClubs
test "order: fields left to right" := twoOfClubs < aceOfSpades
test "constructors in declared order" := List.sort [Spades, Clubs, Hearts] == [Clubs, Hearts, Spades]
test "text" := "${twoOfClubs}" == "{ rank = 2, suit = Clubs }"
-- end derived

-- begin interface
interface Describe (a: Type) =
  { describe: a -> Text }

instance Suit.instDescribe: Describe Suit :=
  { describe = suit => match suit with
    | Clubs => "♣"
    | Diamonds => "♦"
    | Hearts => "♥"
    | Spades => "♠" }

instance Card.instDescribe: Describe Card :=
  { describe = card => "${card.rank}${Describe.describe card.suit}" }

test "describe a card" := Describe.describe aceOfSpades == "14♠"
-- end interface

-- begin auto
def describeAll [auto describer: Describe a] (items: List a): Text := Text.join ' ' (items.map Describe.describe)

test "the instance is found from the type" := describeAll [aceOfSpades, twoOfClubs] == "14♠ 2♣"
-- end auto

-- begin instance-with-context
instance Describe.instList [auto Describe a]: Describe (List a) :=
  { describe = items => "[${describeAll items}]" }

test "instances for containers" := Describe.describe [[twoOfClubs], [aceOfSpades]] == "[[2♣] [14♠]]"
-- end instance-with-context

-- begin named-alternative
def plain: Describe Suit := { describe = suit => "${suit}" }

test "passing another by name" := describeAll [describer := plain] [Hearts, Spades] == "Hearts Spades"
-- end named-alternative

-- begin custom-show
type Celsius = { degrees: Int }

instance Celsius.instShow: Show Celsius := Show.fromText (temperature => "${temperature.degrees}°C")

def freezing: Celsius := { degrees = 0 }

test "custom text" := "${freezing}" == "0°C"
test "inside a list" := "${[freezing]}" == "[0°C]"
-- end custom-show

-- begin custom-order
def highestFirst (cards: List Card): List Card := cards.sortBy (a b => Ord.compare b.rank a.rank)

test "sort another way" := highestFirst [twoOfClubs, aceOfSpades] == [aceOfSpades, twoOfClubs]
test "sort by a key" := [aceOfSpades, twoOfClubs].sortOn (.suit) == [twoOfClubs, aceOfSpades]
-- end custom-order

-- begin add
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
-- end add
