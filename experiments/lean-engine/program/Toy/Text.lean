/-
A stand-in for Stitchwort's `Text`, which is a list of characters
(`MkText (List Char)`), with the six operations the engine uses. Lean's
`String` is a byte array whose `all` doesn't reduce in proofs, so a port
on `String` would measure Lean's string library, not the engine's proof.
-/

structure Text where
  chars : List Char
  deriving DecidableEq

namespace Text

def ofString (s : String) : Text := ⟨s.toList⟩
def toString (text : Text) : String := String.ofList text.chars

def space : Text := ⟨[' ']⟩
def newline : Text := ⟨['\n']⟩

def isEmpty (text : Text) : Bool := text.chars.isEmpty
def length (text : Text) : Nat := text.chars.length
def all (text : Text) (p : Char → Bool) : Bool := text.chars.all p
def replicate (n : Nat) (c : Char) : Text := ⟨List.replicate n c⟩
def join (pieces : List Text) : Text := ⟨pieces.flatMap (·.chars)⟩

end Text
