-- Text: sequences of Unicode scalar values (docs/proposals/text-and-io.md).

-- The contract: exact sequences, compared by scalar value, never normalised.
test "e-acute is one scalar"        := Text.length "\u{E9}" == 1
test "e and a combining accent: two" := Text.length "e\u{301}" == 2
test "no normalisation"             := not ("\u{E9}" == "e\u{301}")
test "an emoji is one scalar"       := Text.length "\u{1F600}" == 1
test "a literal emoji too"          := Text.length "😀" == 1
test "scalar order, not UTF-16"     := not (Text.less "\u{10000}" "\u{E000}")
test "the other way round"          := Text.less "\u{E000}" "\u{10000}"
test "equal"                        := "héllo" == "h\u{E9}llo"
test "not equal"                    := not ("abc" == "abd")
test "prefix is less"               := Text.less "ab" "abc"
test "empty is least"               := Text.less "" "a"
test "not less than itself"         := not (Text.less "abc" "abc")

-- Basic operations.
test "append"            := "foo" ++ "bar" == "foobar"
test "append is right-associative" := "a" ++ "b" ++ "c" == "abc"
test "append binds looser than +"  := "n=" ++ Nat.toText (1 + 2) == "n=3"
test "lists too"         := Nat.equal (List.length ([1, 2] ++ [3])) 3
test "length"            := Text.length "hello" == 5
test "empty"             := Text.isEmpty ""
test "not empty"         := not (Text.isEmpty " ")
test "escapes"           := Text.length "\n\t\\\"\'" == 5
test "fold"              := Text.fold (\c n => Char.toNat c + n) 0 "ab" == 195

def unconsCode : Maybe (Pair Char Text) -> Nat
  | Nothing            => 0
  | Just (MkPair c cs) => Char.toNat c

def firstChar (t : Text) : Nat := unconsCode (Text.uncons t)

test "uncons"            := firstChar "xyz" == 120
test "uncons empty"      := firstChar "" == 0

-- `trim` removes exactly space, \t, \n, \r, U+000B and U+000C.
test "trim"              := Text.trim "  \t hi there \r\n" == "hi there"
test "trim vt and ff"    := Text.trim "\u{B}\u{C}x\u{B}\u{C}" == "x"
test "trim all"          := Text.trim " \n " == ""
test "trim nothing"      := Text.trim "" == ""
test "no-break space stays" := Text.trim "\u{A0}x" == "\u{A0}x"
test "ideographic space stays" := Text.trim "\u{3000}" == "\u{3000}"

-- Numbers.
def justIs (n : Nat) : Maybe Nat -> Bool
  | Nothing => False
  | Just m  => n == m

def isNothing : Maybe a -> Bool
  | Nothing => True
  | Just x  => False

test "natToText 0"       := Nat.toText 0 == "0"
test "natToText 42"      := Nat.toText 42 == "42"
test "natToText 10"      := Nat.toText 10 == "10"
test "natToText big"     := Nat.toText 12345678901234567890 == "12345678901234567890"
test "textToNat"         := justIs 42 (Text.toNat "42")
test "leading zeros"     := justIs 7 (Text.toNat "007")
test "zero"              := justIs 0 (Text.toNat "0")
test "big"               := justIs 98765432109876543210 (Text.toNat "98765432109876543210")
test "empty isn't a number"  := isNothing (Text.toNat "")
test "no sign"           := isNothing (Text.toNat "+1")
test "no minus"          := isNothing (Text.toNat "-1")
test "no spaces"         := isNothing (Text.toNat " 1")
test "no trailing space" := isNothing (Text.toNat "1 ")
test "no separators"     := isNothing (Text.toNat "1,000")
test "ASCII digits only" := isNothing (Text.toNat "\u{663}")

-- The law `Text.toNat (Nat.toText n) = Just n`, for every n up to 100 and
-- some larger ones. (Not much further: the evaluator recurses once per
-- number, and isn't stack-safe yet.)
def roundTrips : Nat -> Bool
  | Zero   => justIs 0 (Text.toNat (Nat.toText 0))
  | Succ n => if justIs (Succ n) (Text.toNat (Nat.toText (Succ n))) then roundTrips n else False

def allRoundTrip : List Nat -> Bool
  | Nil       => True
  | Cons n ns => if justIs n (Text.toNat (Nat.toText n)) then allRoundTrip ns else False

test "natToText round trip" := roundTrips 100
test "natToText round trip, larger" :=
  allRoundTrip [999, 1000, 1001, 9999, 10000, 65535, 1114111, 4294967296, 18446744073709551616]

-- Splitting keeps empty fields.
def eqTexts : List Text -> List Text -> Bool
  | Nil,       Nil       => True
  | Cons x xs, Cons y ys => if x == y then eqTexts xs ys else False
  | _,         _         => False

test "split"             := eqTexts (Text.split ',' "a,b") ["a", "b"]
test "split keeps empty fields" := eqTexts (Text.split ',' "a,,b") ["a", "", "b"]
test "split empty"       := eqTexts (Text.split ',' "") [""]
test "split separator only" := eqTexts (Text.split ',' ",") ["", ""]
test "split at the ends" := eqTexts (Text.split ',' ",a,") ["", "a", ""]
test "split without separator" := eqTexts (Text.split ',' "abc") ["abc"]
test "join"              := Text.join '-' ["a", "", "b"] == "a--b"
test "join nothing"      := Text.join '-' [] == ""

-- Proved for every text, in the prelude.
theorem joinSplit : Text.join ',' (Text.split ',' "a,,b") = "a,,b" := Text.joinSplit ',' "a,,b"

theorem roundTrip (t : Text) : Text.fromList (Text.toList t) = t := Text.fromToList t

-- By computation.
theorem helloLength : Text.length "hello" = 5 := rfl
