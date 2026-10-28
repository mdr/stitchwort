-- `natDigits atLeast atMost` reads a number of that many digits; its
-- message says "a 1-digit number" for one count and "a number of 2 to 5
-- digits" for a range.
import Std (Fail, Nat, Parse, Result, Text)
import Std.Fail (toResult)
import Std.Parse (char, natDigits, sepBy1)

def threeBits(): {Parse} (List Nat) := sepBy1 (() => natDigits 1 1) (() => char ',')

def year(): {Parse} Nat := natDigits 4 4

def code(): {Parse} Nat := natDigits 2 5

test "digits" := toResult (() => Parse.all "0,3,5" threeBits) == Ok [0, 3, 5]

test "one digit" := toResult (() => Parse.all "0,10" threeBits) == Err "line 1, column 3: expected a 1-digit number, got '1'"

test "four digits" := toResult (() => Parse.all "202" year) == Err "line 1, column 1: expected a 4-digit number, got '2'"

test "a range" := toResult (() => Parse.all "7" code) == Err "line 1, column 1: expected a number of 2 to 5 digits, got '7'"
