-- expect-error: E-TYPE-MISMATCH
-- `Parse.tokens` lexes with a parser of characters, then parses with one of
-- tokens, `{Parse (Parse.Located token)}`. A second parser of characters
-- reads the wrong thing, and the row says so.
import Std (Fail, List, Nat, Parse, Text)
import Std.Parse (nat)

def lexToken(): {Parse Char} Parse.Located Nat := Parse.located (() => nat())

def total(): {Parse Char} Nat := nat()

def parse (input: Text): {Fail} Nat := Parse.tokens [a := Nat] input (() => Parse.many lexToken) total
