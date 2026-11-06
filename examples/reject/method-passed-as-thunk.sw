-- expect-error: E-ABILITY
-- A method that returns a parser, passed where `Parse.eachLine` wants a
-- `() → {Parse} a`, runs on the spot (SW-1565): the note says to write
-- `() => digits.parser`.
import Std (Fail, List, Nat, Parse)

type Digits = { base: Nat }

def Digits.parser (digits: Digits): {Parse} Nat := Parse.nat()

def readAll (input: Text) (digits: Digits): {Fail} List Nat :=
  Parse.eachLine input digits.parser
