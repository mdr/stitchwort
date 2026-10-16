-- adder.sw as it had to be written before `Partial`: every definition is
-- total, so the loop needs a bound. It adds the numbers on at most 1000
-- lines, and silently ignores any after that.
--
--   $ stitchwort run examples/accept/adder-fuel.sw
--
-- Being total, its `main` can be tested in the language: the tests below
-- run it with `simulate`, against scripted input. crates/driver/tests/run.rs
-- checks that adder.sw prints the same, for input within the bound.

-- The text, or a default at end of input.
textOr : Text -> Maybe Text -> Text
textOr d Nothing  = d
textOr d (Just t) = t

-- Reports a line that should be a number, and goes on with the new total.
stepNumber : Nat -> Text -> Maybe Nat -> (Nat -> {IO} Nat) -> {IO} Nat
stepNumber total l Nothing  more =
  print ("\"" ++ l ++ "\" isn't a number; skipped")
  more total
stepNumber total l (Just n) more =
  print ("  total: " ++ natToText (total + n))
  more (total + n)

-- What to do with a line, given the total so far. An empty line, or the end
-- of input, stops.
step : Nat -> Maybe Text -> (Nat -> {IO} Nat) -> {IO} Nat
step total Nothing  more = total
step total (Just l) more =
  if textIsEmpty l then total else stepNumber total l (textToNat (textTrim l)) more

-- Adds the numbers on at most this many more lines. The bound keeps the
-- recursion structural: every run of `main` performs a bounded number of
-- operations.
addLines : Nat -> Nat -> {IO} Nat
addLines 0        total = total
addLines (Succ n) total = step total (readLine ()) (\t -> addLines n t)

main : () -> {IO} ()
main u =
  print "What's your name?"
  let name = textOr "stranger" (readLine ())
  print ("Hello, " ++ name ++ "! Type numbers to add, one per line, and an empty line to stop.")
  let total = addLines 1000 0
  print ("The sum is " ++ natToText total ++ ". Goodbye, " ++ name ++ ".")

-- Testing `main` with scripted input

eqTexts : List Text -> List Text -> Bool
eqTexts Nil         Nil         = True
eqTexts (Cons x xs) (Cons y ys) = if x == y then eqTexts xs ys else False
eqTexts _           _           = False

printed : List Text -> List Text
printed input = fst (simulate input main)

test "a session" =
  eqTexts (printed ["Ada", "1", "2", "x", " 39 ", ""])
    [ "What's your name?"
    , "Hello, Ada! Type numbers to add, one per line, and an empty line to stop."
    , "  total: 1"
    , "  total: 3"
    , "\"x\" isn't a number; skipped"
    , "  total: 42"
    , "The sum is 42. Goodbye, Ada."
    ]

test "end of input stops it too" =
  eqTexts (printed ["Ada", "5"])
    [ "What's your name?"
    , "Hello, Ada! Type numbers to add, one per line, and an empty line to stop."
    , "  total: 5"
    , "The sum is 5. Goodbye, Ada."
    ]

test "no input at all" =
  eqTexts (printed [])
    [ "What's your name?"
    , "Hello, stranger! Type numbers to add, one per line, and an empty line to stop."
    , "The sum is 0. Goodbye, stranger."
    ]
