-- A small interactive program: run it with `stitchwort run`.
--
--   $ stitchwort run examples/accept/adder.sw
--   What's your name?
--   Ada
--   Hello, Ada! Type numbers to add, one per line, and an empty line to stop.
--   40
--     total: 40
--   two
--   "two" isn't a number; skipped
--   2
--     total: 42
--
--   The sum is 42. Goodbye, Ada.
--
-- It reads until an empty line or the end of the input, however long that
-- is: its loop is `Partial` (docs/proposals/partial.md), so it needs no
-- bound. Only `stitchwort run` and the playground run partial code, so the
-- tests below are about its total parts; crates/driver/tests/run.rs and
-- crates/cli/tests/run.rs run whole sessions. adder-fuel.sw is the same
-- program with a bound on the number of lines, as it had to be written
-- before `Partial`.

-- The text, or a default at end of input.
def textOr (d: Text): Maybe Text -> Text
  | Nothing => d
  | Just t  => t

-- Reports a line that should be a number, and goes on with the new total.
def stepNumber (total: Nat) (l: Text): Maybe Nat -> (Nat -> {IO, Partial | e} Nat) -> {IO, Partial | e} Nat
  | Nothing, more =>
    print ("\"" ++ l ++ "\" isn't a number; skipped")
    more total
  | Just n,  more =>
    print ("  total: " ++ Nat.toText (total + n))
    more (total + n)

-- What to do with a line, given the total so far. An empty line, or the end
-- of input, stops. `step` and `stepNumber` aren't recursive: they mention
-- `Partial` only because `more` may be partial. They're polymorphic in the
-- rest of the row (`| e`) because `addLines` passes itself as `more`, and a
-- recursive call is a request only `addLines`'s own definition can answer.
def step (total: Nat): Maybe Text -> (Nat -> {IO, Partial | e} Nat) -> {IO, Partial | e} Nat
  | Nothing, more => total
  | Just l,  more =>
    if Text.isEmpty l then total else stepNumber total l (Text.toNat (Text.trim l)) more

-- Adds up the numbers on the lines to come, until an empty line or the end
-- of the input.
def addLines (total: Nat): {IO, Partial} Nat := step total (readLine()) addLines

def main(): {IO, Partial} () :=
  print "What's your name?"
  let name := textOr "stranger" (readLine())
  print ("Hello, " ++ name ++ "! Type numbers to add, one per line, and an empty line to stop.")
  let total := addLines 0
  print ("The sum is " ++ Nat.toText total ++ ". Goodbye, " ++ name ++ ".")

test "a name" := textOr "stranger" (Just "Ada") == "Ada"

test "no name" := textOr "stranger" Nothing == "stranger"
