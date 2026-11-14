-- expect-error: E-UNKNOWN-NAME
-- Names other languages use for something std spells differently get a
-- "did you mean" by meaning, since spelling distance can't find them:
-- `Char.isLower` is `Char.isAsciiLowercase`. A name with no such meaning gets
-- no suggestion. Each line is one error.
import Std (Char, List, Map, Text)

def a: Bool := Char.isLower 'a'
def b: Nat := List.size [1, 2, 3]
def c: Nat := Text.len "abc"
def d: Bool := 'a'.isLowercase
def e: Bool := Char.isFrobnicated 'a'
