-- A comparison passed as a `Bool` argument may have an operand that performs
-- an operation: the operation runs first, and the comparison is decided on
-- its result.
import Std (Bool, Fail, Nat, Parse, Result, Text)
import Std.Fail (toResult)

-- `Parse.mark()` runs, then `≤` is decided on its offset.
def shortNumber(): {Parse} Nat :=
  let number := Parse.nat()
  Parse.ensure (Parse.mark().offset ≤ 3) "expected at most three digits"
  number

test "three digits" := toResult (() => Parse.line "123" shortNumber) == Ok 123
test "four digits" := toResult (() => Parse.line "1234" shortNumber) == Err "column 5: expected at most three digits"

def check (ok: Bool): Bool := ok

-- `<`, `>` and `=` too, with the operation on either side.
def before(): {Parse} Bool := check (Parse.mark().offset < 3)
def after(): {Parse} Bool := check (3 < Parse.mark().offset)
def atStart(): {Parse} Bool := check (Parse.mark().offset = 0)

test "at the start" := toResult (() => Parse.line "" (() => (before(), after(), atStart()))) == Ok (True, False, True)
