-- Read in two passes: a lexer turns characters into tokens that remember
-- where they were (`Parse.located`), and a parser reads the tokens with the
-- same combinators. `Parse.tokens` runs both, and a failure in the second
-- says where in the source.
import Std (Char, Fail, List, Option, Parse, Result, Text)
import Std.Fail (toResult)
import Std.Parse (nat)

type Token = | Num (value: Nat) | Word (text: Text) | Comma

def lexToken(): {Parse Char} Parse.Located Token :=
  Parse.spaces()
  Parse.located (() =>
    Parse.oneOf [
      () => Num nat(),
      () => Word (Parse.takeWhile1 "a word" Char.isAsciiLetter),
      () =>
        Parse.text ","
        Comma
    ])

-- A token is picked by a function from it to what it carries.
def numberOf (token: Parse.Located Token): Option Nat := match token with
  | { value = Num value, .. } => Some value
  | _ => None

def isComma (token: Parse.Located Token): Option () := match token with
  | { value = Comma, .. } => Some ()
  | _ => None

def numbers(): {Parse (Parse.Located Token)} List Nat :=
  Parse.sepBy (() => Parse.one "a number" numberOf) (() => Parse.one "a comma" isComma)

def parseNumbers (input: Text): {Fail} List Nat := Parse.tokens input (() => Parse.many lexToken) numbers

test "numbers" := toResult (() => parseNumbers "3, 14 ,15") == Ok [3, 14, 15]
test "a word instead of a number" :=
  toResult (() => parseNumbers "3, pi") == Err "line 1, column 4: expected a number, got 'pi'"
test "the end of the input" :=
  toResult (() => parseNumbers "3,") == Err "line 1, column 3: expected a number, got the end of the input"
