-- adder.sw as it had to be written before `Partial`: every definition is
-- total, so the loop needs a bound. It adds the numbers on at most 1000
-- lines, and silently ignores any after that.
--
--   $ stitchwort run examples/accept/adder-fuel.sw
--
-- Being total, its `main` can be tested in the language: the tests below
-- run it with `IO.simulate`, against scripted input. crates/driver/tests/run.rs
-- checks that adder.sw prints the same, for input within the bound.

-- The text, or a default at end of input.
def textOr (d: Text): Maybe Text -> Text
  | Nothing => d
  | Just t  => t

-- Reports a line that should be a number, and goes on with the new total.
def stepNumber (total: Nat) (l: Text): Maybe Nat -> (Nat -> {IO} Nat) -> {IO} Nat
  | Nothing, more =>
    IO.print ("\"" ++ l ++ "\" isn't a number; skipped")
    more total
  | Just n,  more =>
    IO.print ("  total: " ++ Nat.toText (total + n))
    more (total + n)

-- What to do with a line, given the total so far. An empty line, or the end
-- of input, stops.
def step (total: Nat): Maybe Text -> (Nat -> {IO} Nat) -> {IO} Nat
  | Nothing, more => total
  | Just l,  more =>
    if l.isEmpty then total else stepNumber total l ((l.trim).toNat) more

-- Adds the numbers on at most this many more lines. The bound keeps the
-- recursion structural: every run of `main` performs a bounded number of
-- operations.
def addLines: Nat -> Nat -> {IO} Nat
  | 0,      total => total
  | Succ n, total => step total (IO.readLine()) (\t => addLines n t)

def main(): {IO} () :=
  IO.print "What's your name?"
  let name := textOr "stranger" (IO.readLine())
  IO.print ("Hello, " ++ name ++ "! Type numbers to add, one per line, and an empty line to stop.")
  let total := addLines 1000 0
  IO.print ("The sum is " ++ Nat.toText total ++ ". Goodbye, " ++ name ++ ".")

-- Testing `main` with scripted input

def eqTexts: List Text -> List Text -> Bool
  | Nil,       Nil       => True
  | Cons x xs, Cons y ys => if x == y then eqTexts xs ys else False
  | _,         _         => False

def printed (input: List Text): List Text := Pair.fst (IO.simulate input main)

test "a session" :=
  eqTexts (printed ["Ada", "1", "2", "x", " 39 ", ""])
    [ "What's your name?"
    , "Hello, Ada! Type numbers to add, one per line, and an empty line to stop."
    , "  total: 1"
    , "  total: 3"
    , "\"x\" isn't a number; skipped"
    , "  total: 42"
    , "The sum is 42. Goodbye, Ada."
    ]

test "end of input stops it too" :=
  eqTexts (printed ["Ada", "5"])
    [ "What's your name?"
    , "Hello, Ada! Type numbers to add, one per line, and an empty line to stop."
    , "  total: 5"
    , "The sum is 5. Goodbye, Ada."
    ]

test "no input at all" :=
  eqTexts (printed [])
    [ "What's your name?"
    , "Hello, stranger! Type numbers to add, one per line, and an empty line to stop."
    , "The sum is 0. Goodbye, stranger."
    ]
