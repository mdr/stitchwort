-- Text: sequences of Unicode scalar values (docs/proposals/text-and-io.md).

-- The contract: exact sequences, compared by scalar value, never normalised.
test "e-acute is one scalar"        := "\u{E9}".length == 1
test "e and a combining accent: two" := "e\u{301}".length == 2
test "no normalisation"             := not ("\u{E9}" == "e\u{301}")
test "an emoji is one scalar"       := "\u{1F600}".length == 1
test "a literal emoji too"          := "😀".length == 1
test "scalar order, not UTF-16"     := not ("\u{10000}".less "\u{E000}")
test "the other way round"          := "\u{E000}".less "\u{10000}"
test "equal"                        := "héllo" == "h\u{E9}llo"
test "not equal"                    := not ("abc" == "abd")
test "prefix is less"               := "ab".less "abc"
test "empty is least"               := "".less "a"
test "not less than itself"         := not ("abc".less "abc")

-- Basic operations.
test "append"            := "foo" ++ "bar" == "foobar"
test "append is right-associative" := "a" ++ "b" ++ "c" == "abc"
test "append binds looser than +"  := "n=" ++ Nat.toText (1 + 2) == "n=3"
test "lists too"         := Nat.equal (([1, 2] ++ [3]).length) 3
test "length"            := "hello".length == 5
test "empty"             := "".isEmpty
test "not empty"         := not (" ".isEmpty)
test "escapes"           := "\n\t\\\"\'".length == 5
test "fold"              := "ab".fold (c n => Char.toNat c + n) 0 == 195

def unconsCode: Maybe (Pair Char Text) -> Nat
  | Nothing            => 0
  | Just (MkPair c cs) => Char.toNat c

def firstChar (t: Text): Nat := unconsCode (t.uncons)

test "uncons"            := firstChar "xyz" == 120
test "uncons empty"      := firstChar "" == 0

-- `trim` removes exactly space, \t, \n, \r, U+000B and U+000C.
test "trim"              := "  \t hi there \r\n".trim == "hi there"
test "trim vt and ff"    := "\u{B}\u{C}x\u{B}\u{C}".trim == "x"
test "trim all"          := " \n ".trim == ""
test "trim nothing"      := "".trim == ""
test "no-break space stays" := "\u{A0}x".trim == "\u{A0}x"
test "ideographic space stays" := "\u{3000}".trim == "\u{3000}"

-- Numbers.
def justIs (n: Nat): Maybe Nat -> Bool
  | Nothing => False
  | Just m  => n == m

def isNothing: Maybe a -> Bool
  | Nothing => True
  | Just x  => False

test "natToText 0"       := Nat.toText 0 == "0"
test "natToText 42"      := Nat.toText 42 == "42"
test "natToText 10"      := Nat.toText 10 == "10"
test "natToText big"     := Nat.toText 12345678901234567890 == "12345678901234567890"
test "textToNat"         := justIs 42 ("42".toNat)
test "leading zeros"     := justIs 7 ("007".toNat)
test "zero"              := justIs 0 ("0".toNat)
test "big"               := justIs 98765432109876543210 ("98765432109876543210".toNat)
test "empty isn't a number"  := isNothing ("".toNat)
test "no sign"           := isNothing ("+1".toNat)
test "no minus"          := isNothing ("-1".toNat)
test "no spaces"         := isNothing (" 1".toNat)
test "no trailing space" := isNothing ("1 ".toNat)
test "no separators"     := isNothing ("1,000".toNat)
test "ASCII digits only" := isNothing ("\u{663}".toNat)

-- The law `Text.toNat (Nat.toText n) = Just n`, for every n up to 100 and
-- some larger ones. (Not much further: the evaluator recurses once per
-- number, and isn't stack-safe yet.)
def roundTrips: Nat -> Bool
  | Zero   => justIs 0 ((Nat.toText 0).toNat)
  | Succ n => if justIs (Succ n) ((Nat.toText (Succ n)).toNat) then roundTrips n else False

def allRoundTrip: List Nat -> Bool
  | Nil       => True
  | Cons n ns => if justIs n ((Nat.toText n).toNat) then allRoundTrip ns else False

test "natToText round trip" := roundTrips 100
test "natToText round trip, larger" :=
  allRoundTrip [999, 1000, 1001, 9999, 10000, 65535, 1114111, 4294967296, 18446744073709551616]

-- Splitting keeps empty fields.
def eqTexts: List Text -> List Text -> Bool
  | Nil,       Nil       => True
  | Cons x xs, Cons y ys => if x == y then eqTexts xs ys else False
  | _,         _         => False

test "split"             := eqTexts ("a,b".split ',') ["a", "b"]
test "split keeps empty fields" := eqTexts ("a,,b".split ',') ["a", "", "b"]
test "split empty"       := eqTexts ("".split ',') [""]
test "split separator only" := eqTexts (",".split ',') ["", ""]
test "split at the ends" := eqTexts (",a,".split ',') ["", "a", ""]
test "split without separator" := eqTexts ("abc".split ',') ["abc"]
test "join"              := Text.join '-' ["a", "", "b"] == "a--b"
test "join nothing"      := Text.join '-' [] == ""

-- Proved for every text, in the prelude.
theorem joinSplit: Text.join ',' ("a,,b".split ',') = "a,,b" := Text.joinSplit ',' "a,,b"

theorem roundTrip (t: Text): Text.fromList (Text.toList t) = t := Text.fromToList t

-- By computation.
theorem helloLength: "hello".length = 5 := rfl
