-- Text: sequences of Unicode scalar values (docs/proposals/text-and-io.md).

-- The contract: exact sequences, compared by scalar value, never normalised.
test "e-acute is one scalar"        = textLength "\u{E9}" == 1
test "e and a combining accent: two" = textLength "e\u{301}" == 2
test "no normalisation"             = not ("\u{E9}" == "e\u{301}")
test "an emoji is one scalar"       = textLength "\u{1F600}" == 1
test "a literal emoji too"          = textLength "😀" == 1
test "scalar order, not UTF-16"     = not (textLess "\u{10000}" "\u{E000}")
test "the other way round"          = textLess "\u{E000}" "\u{10000}"
test "equal"                        = "héllo" == "h\u{E9}llo"
test "not equal"                    = not ("abc" == "abd")
test "prefix is less"               = textLess "ab" "abc"
test "empty is least"               = textLess "" "a"
test "not less than itself"         = not (textLess "abc" "abc")

-- Basic operations.
test "append"            = "foo" ++ "bar" == "foobar"
test "append is right-associative" = "a" ++ "b" ++ "c" == "abc"
test "append binds looser than +"  = "n=" ++ natToText (1 + 2) == "n=3"
test "lists too"         = eqNat (length ([1, 2] ++ [3])) 3
test "length"            = textLength "hello" == 5
test "empty"             = textIsEmpty ""
test "not empty"         = not (textIsEmpty " ")
test "escapes"           = textLength "\n\t\\\"\'" == 5
test "fold"              = textFold (\c n -> charToNat c + n) 0 "ab" == 195

unconsCode : Maybe (Pair Char Text) -> Nat
unconsCode Nothing              = 0
unconsCode (Just (MkPair c cs)) = charToNat c

firstChar : Text -> Nat
firstChar t = unconsCode (textUncons t)

test "uncons"            = firstChar "xyz" == 120
test "uncons empty"      = firstChar "" == 0

-- `trim` removes exactly space, \t, \n, \r, U+000B and U+000C.
test "trim"              = textTrim "  \t hi there \r\n" == "hi there"
test "trim vt and ff"    = textTrim "\u{B}\u{C}x\u{B}\u{C}" == "x"
test "trim all"          = textTrim " \n " == ""
test "trim nothing"      = textTrim "" == ""
test "no-break space stays" = textTrim "\u{A0}x" == "\u{A0}x"
test "ideographic space stays" = textTrim "\u{3000}" == "\u{3000}"

-- Numbers.
justIs : Nat -> Maybe Nat -> Bool
justIs n Nothing  = False
justIs n (Just m) = n == m

isNothing : Maybe a -> Bool
isNothing Nothing  = True
isNothing (Just x) = False

test "natToText 0"       = natToText 0 == "0"
test "natToText 42"      = natToText 42 == "42"
test "natToText 10"      = natToText 10 == "10"
test "natToText big"     = natToText 12345678901234567890 == "12345678901234567890"
test "textToNat"         = justIs 42 (textToNat "42")
test "leading zeros"     = justIs 7 (textToNat "007")
test "zero"              = justIs 0 (textToNat "0")
test "big"               = justIs 98765432109876543210 (textToNat "98765432109876543210")
test "empty isn't a number"  = isNothing (textToNat "")
test "no sign"           = isNothing (textToNat "+1")
test "no minus"          = isNothing (textToNat "-1")
test "no spaces"         = isNothing (textToNat " 1")
test "no trailing space" = isNothing (textToNat "1 ")
test "no separators"     = isNothing (textToNat "1,000")
test "ASCII digits only" = isNothing (textToNat "\u{663}")

-- The law `textToNat (natToText n) = Just n`, for every n up to 100 and
-- some larger ones. (Not much further: the evaluator recurses once per
-- number, and isn't stack-safe yet.)
roundTrips : Nat -> Bool
roundTrips Zero     = justIs 0 (textToNat (natToText 0))
roundTrips (Succ n) = if justIs (Succ n) (textToNat (natToText (Succ n))) then roundTrips n else False

allRoundTrip : List Nat -> Bool
allRoundTrip Nil         = True
allRoundTrip (Cons n ns) = if justIs n (textToNat (natToText n)) then allRoundTrip ns else False

test "natToText round trip" = roundTrips 100
test "natToText round trip, larger" =
  allRoundTrip [999, 1000, 1001, 9999, 10000, 65535, 1114111, 4294967296, 18446744073709551616]

-- Splitting keeps empty fields.
eqTexts : List Text -> List Text -> Bool
eqTexts Nil         Nil         = True
eqTexts (Cons x xs) (Cons y ys) = if x == y then eqTexts xs ys else False
eqTexts _           _           = False

test "split"             = eqTexts (textSplit ',' "a,b") ["a", "b"]
test "split keeps empty fields" = eqTexts (textSplit ',' "a,,b") ["a", "", "b"]
test "split empty"       = eqTexts (textSplit ',' "") [""]
test "split separator only" = eqTexts (textSplit ',' ",") ["", ""]
test "split at the ends" = eqTexts (textSplit ',' ",a,") ["", "a", ""]
test "split without separator" = eqTexts (textSplit ',' "abc") ["abc"]
test "join"              = textJoin '-' ["a", "", "b"] == "a--b"
test "join nothing"      = textJoin '-' [] == ""

-- Proved for every text, in the prelude.
theorem joinSplit : textJoin ',' (textSplit ',' "a,,b") = "a,,b"
joinSplit = textJoinSplit ',' "a,,b"

theorem roundTrip : (t : Text) -> textFromList (textToList t) = t
roundTrip t = textFromToList t

-- By computation.
theorem helloLength : textLength "hello" = 5
helloLength = rfl
