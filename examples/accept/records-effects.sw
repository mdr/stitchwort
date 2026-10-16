-- The order record fields run in (docs/proposals/records.md §6.1): each
-- field expression once, in the order written, and then the record is built
-- in declaration order. An update runs its base once, first.

type Pair2 = { a : Text, b : Text }

orNone : Maybe Text -> Text
orNone Nothing  = "none"
orNone (Just t) = t

next : () -> {IO} Text
next u = orNone (readLine ())

-- `b` is written first, so it reads the first line.
backwards : () -> {IO} Pair2
backwards u = { b = next (), a = next () }

-- The base prints once, before the new field is read.
base : () -> {IO} Pair2
base u =
  print "base"
  { a = "x", b = "y" }

updated : () -> {IO} Pair2
updated u = { base () | a = next () }

eqTexts : List Text -> List Text -> Bool
eqTexts Nil         Nil         = True
eqTexts (Cons x xs) (Cons y ys) = if x == y then eqTexts xs ys else False
eqTexts _           _           = False

test "fields run in the order written" =
  (Pair.snd (IO.simulate ["1", "2"] backwards)).b == "1"

test "and are put where they belong" =
  (Pair.snd (IO.simulate ["1", "2"] backwards)).a == "2"

test "an update's base runs once" =
  eqTexts (Pair.fst (IO.simulate ["1"] updated)) ["base"]

test "an update keeps the base's other fields" =
  (Pair.snd (IO.simulate ["1"] updated)) == { a = "1", b = "y" }
