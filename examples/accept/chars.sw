-- Characters: Unicode scalar values (docs/proposals/text-and-io.md).

def isJust: Maybe a -> Bool
  | Nothing => False
  | Just x  => True

def codeOr: Maybe Char -> Nat
  | Nothing => 999
  | Just c  => Char.toNat c

test "0"        := isJust (Char.fromNat 0)
test "d7ff"     := isJust (Char.fromNat 55295)
test "d800"     := not (isJust (Char.fromNat 55296))
test "dfff"     := not (isJust (Char.fromNat 57343))
test "e000"     := isJust (Char.fromNat 57344)
test "10ffff"   := isJust (Char.fromNat 1114111)
test "110000"   := not (isJust (Char.fromNat 1114112))
test "roundtrip" := codeOr (Char.fromNat 65) == 65

test "code a"    := Char.toNat 'a' == 97
test "eq"        := 'a' == 'a'
test "neq"       := not ('a' == 'b')
test "max"       := Char.toNat '\u{10FFFF}' == 1114111
test "emoji"     := Char.toNat '😀' == 128512
test "escape"    := '\n' == '\u{A}'
test "from lit"  := codeOr (Char.fromNat 233) == Char.toNat 'é'

theorem aIsA: 'a' = 'a' := rfl

def sameChar (x: Char) (y: Char): Bool := if h: x = y then True else False

test "if h" := sameChar 'x' 'x'
