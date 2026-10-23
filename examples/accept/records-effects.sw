-- The order record fields run in (docs/proposals/records.md §6.1): each
-- field expression once, in the order written, and then the record is built
-- in declaration order. An update runs its base once, first.

import Std (IO, Pair)

type Pair2 = { a: Text, b: Text }

def orNone: Option Text -> Text
  | None => "none"
  | Some t => t

def next(): {IO} Text := orNone IO.readLine()

-- `b` is written first, so it reads the first line.
def backwards(): {IO} Pair2 := { b = next(), a = next() }

-- The base prints once, before the new field is read.
def base(): {IO} Pair2 :=
  IO.print "base"
  { a = "x", b = "y" }

def updated(): {IO} Pair2 := { base() | a = next() }

def eqTexts: List Text -> List Text -> Bool
  | Nil, Nil => True
  | Cons x xs, Cons y ys => if x == y then eqTexts xs ys else False
  | _, _ => False

test "fields run in the order written" :=
  (Pair.snd (IO.simulate ["1", "2"] backwards)).b == "1"

test "and are put where they belong" :=
  (Pair.snd (IO.simulate ["1", "2"] backwards)).a == "2"

test "an update's base runs once" :=
  eqTexts (Pair.fst (IO.simulate ["1"] updated)) ["base"]

test "an update keeps the base's other fields" :=
  (Pair.snd (IO.simulate ["1"] updated)) == { a = "1", b = "y" }
