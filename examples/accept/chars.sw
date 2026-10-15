-- Characters: Unicode scalar values (docs/proposals/text-and-io.md).

isJust : Maybe a -> Bool
isJust Nothing  = False
isJust (Just x) = True

codeOr : Maybe Char -> Nat
codeOr Nothing  = 999
codeOr (Just c) = charToNat c

test "0"        = isJust (charFromNat 0)
test "d7ff"     = isJust (charFromNat 55295)
test "d800"     = not (isJust (charFromNat 55296))
test "dfff"     = not (isJust (charFromNat 57343))
test "e000"     = isJust (charFromNat 57344)
test "10ffff"   = isJust (charFromNat 1114111)
test "110000"   = not (isJust (charFromNat 1114112))
test "roundtrip" = codeOr (charFromNat 65) == 65

test "code a"    = charToNat 'a' == 97
test "eq"        = 'a' == 'a'
test "neq"       = not ('a' == 'b')
test "max"       = charToNat '\u{10FFFF}' == 1114111
test "emoji"     = charToNat '😀' == 128512
test "escape"    = '\n' == '\u{A}'
test "from lit"  = codeOr (charFromNat 233) == charToNat 'é'

theorem aIsA : 'a' = 'a'
aIsA = rfl

sameChar : (x : Char) -> (y : Char) -> Bool
sameChar x y = if h : x = y then True else False

test "if h" = sameChar 'x' 'x'
