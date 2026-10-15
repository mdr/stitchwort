-- `Text` and `Char` cross the boundary as JS strings. Many of the cases are
-- where JavaScript's own string functions would give a different answer:
-- they count, compare and split UTF-16 code units, not characters.
--
-- `.length` is 2 for an emoji, but it's one character:
-- run: len "\u{1F600}"
-- run: len "e\u{301}"
-- run: len ""
-- run: len "a\u{0}b"
-- run: chars "a\u{1F600}b"
-- run: chars "\u{10FFFF}\u{FFFF}\u{FFFE}\u{FDD0}"
-- run: fromChars ['\u{1F600}', 'x', '\u{0}']
-- run: echo "h\u{E9}llo, \u{4E16}\u{754C} \u{1F600}"
-- run: echo "\u{0}\u{FFFF}\u{10FFFF}"
-- run: echoChar '\u{1F600}'
-- run: echoChar '\u{0}'
-- run: codeOf '\u{1F600}'
-- run: codeOf '\u{FFFE}'
-- run: charOf 55296
-- run: charOf 57343
-- run: charOf 57344
-- run: charOf 1114111
-- run: charOf 1114112
-- No normalisation: these are canonically equivalent, but different texts.
-- run: same "\u{E9}" "e\u{301}"
-- run: same "\u{1F600}" "\u{1F600}"
-- JS's `<` says "\u{10000}" < "\u{E000}" (its first code unit is 0xD800):
-- run: order "\u{10000}" "\u{E000}"
-- run: order "\u{E000}" "\u{10000}"
-- run: order "ab" "a"
-- run: order "" ""
-- run: join "a" "\u{1F600}"
-- Splitting on a supplementary character, and never inside one:
-- run: split '\u{1F600}' "a\u{1F600}b\u{1F600}"
-- run: split ',' "a,,b"
-- run: split ',' ""
-- run: joinOn '\u{1F600}' ["a", "", "b"]
-- run: joinOn ',' []
-- JS's `trim` also removes U+00A0, U+2028 and U+FEFF; `textTrim` doesn't.
-- run: trim " \t\n\r\u{B}\u{C}x y \r\n"
-- run: trim "\u{A0}x\u{2028}"
-- run: trim "\u{FEFF}x"
-- `Number` or `parseInt` accepts each of these; `textToNat` accepts only
-- digits.
-- run: toNat "007"
-- run: toNat ""
-- run: toNat " 12"
-- run: toNat "+5"
-- run: toNat "12abc"
-- run: toNat "0x10"
-- run: toNat "1e3"
-- run: toNat "\u{661}\u{662}"
-- run: toNat "18446744073709551616"
-- run: fromNat 18446744073709551616
-- `slice(1)` would cut the emoji in half:
-- run: uncons "\u{1F600}x"
-- run: uncons ""
-- `split("").reverse()` would swap the emoji's two halves:
-- run: reverse "ab\u{1F600}c"
-- run: countChar '\u{1F600}' "\u{1F600}a\u{1F600}"
-- run: countChar '\u{D7FF}' "\u{D7FF}\u{E000}"
-- run: greet (MkPerson "Zo\u{EB}" '\u{1F600}' ["x", ""])
-- run: initials [MkPerson "Ana" 'A' [], MkPerson "\u{10000}" '\u{10000}' ["t"]]
-- run: rename "\u{0}" (MkPerson "a" 'b' ["c"])
-- run: orEmpty (Just "\u{1F600}")
-- run: orEmpty Nothing
-- run: firstOf (MkPair '\u{1F600}' "rest")
-- run: located (At "a\u{1F600}" 'x' ['y'])
-- Native operations used as values, and their results taken apart by user
-- code:
-- run: empty ""
-- run: empty "\u{0}"
-- run: less "\u{10000}" "\u{E000}"
-- run: codes "a\u{1F600}\u{10FFFF}"
-- run: lengths ["", "\u{1F600}", "ab"]
-- run: texts [['a', '\u{1F600}'], []]
-- run: prefixAll ["", "\u{1F600}"]
-- run: firstField ',' "ab,cd"
-- run: firstField '\u{1F600}' "\u{1F600}x"
-- run: trimmedHead "  \u{1F600}x "
-- run: trimmedHead " \t"
-- run: isText "\u{1F600}"

export
len : Text -> Nat
len t = textLength t

export
chars : Text -> List Char
chars t = textToList t

export
fromChars : List Char -> Text
fromChars cs = textFromList cs

export
echo : Text -> Text
echo t = t

export
echoChar : Char -> Char
echoChar c = c

export
codeOf : Char -> Nat
codeOf c = charToNat c

export
charOf : Nat -> Maybe Char
charOf n = charFromNat n

export
same : Text -> Text -> Bool
same a b = a == b

export
order : Text -> Text -> Ordering
order a b = textCompare a b

export
join : Text -> Text -> Text
join a b = a ++ b

export
split : Char -> Text -> List Text
split c t = textSplit c t

export
joinOn : Char -> List Text -> Text
joinOn c ts = textJoin c ts

export
trim : Text -> Text
trim t = textTrim t

export
toNat : Text -> Maybe Nat
toNat t = textToNat t

export
fromNat : Nat -> Text
fromNat n = natToText n

export
uncons : Text -> Maybe (Pair Char Text)
uncons t = textUncons t

-- User code over the characters.
export
reverse : Text -> Text
reverse t = textFromList (reverseOnto (textToList t) Nil)

countIn : Char -> List Char -> Nat
countIn c Nil         = 0
countIn c (Cons d ds) = if c == d then Succ (countIn c ds) else countIn c ds

export
countChar : Char -> Text -> Nat
countChar c t = countIn c (textToList t)

-- Text inside a user's data type, a list and the prelude's `Maybe` and `Pair`.
type Person : Type =
  | MkPerson (name : Text) (initial : Char) (tags : List Text)

export
greet : Person -> Text
greet (MkPerson name initial tags) = "Hello, " ++ name ++ " (" ++ textFromList (Cons initial Nil) ++ ")"

initialsOf : List Person -> List Char
initialsOf Nil                      = Nil
initialsOf (Cons (MkPerson n i t) ps) = Cons i (initialsOf ps)

export
initials : List Person -> List Char
initials ps = initialsOf ps

export
rename : Text -> Person -> Person
rename n (MkPerson m i t) = MkPerson n i (Cons m t)

export
orEmpty : Maybe Text -> Text
orEmpty Nothing  = ""
orEmpty (Just t) = t

export
firstOf : Pair Char Text -> Char
firstOf p = fst p

-- Fields named like the decoder's own variables.
type Located : Type =
  | At (path : Text) (x : Char) (inside : List Char)

export
located : Located -> Located
located (At p c cs) = At (p ++ "/") c (Cons c cs)

-- The prelude's text operations are native JavaScript, and a `Text` is a
-- string. These use them as values, partly applied, and with their results
-- taken apart by ordinary pattern matching.
export
empty : Text -> Bool
empty t = textIsEmpty t

export
less : Text -> Text -> Bool
less a b = textLess a b

export
codes : Text -> List Nat
codes t = textFold (\c ns -> Cons (charToNat c) ns) Nil t

mapList : (a -> b) -> List a -> List b
mapList f Nil         = Nil
mapList f (Cons x xs) = Cons (f x) (mapList f xs)

export
lengths : List Text -> List Nat
lengths ts = mapList textLength ts

export
texts : List (List Char) -> List Text
texts ls = mapList MkText ls

export
prefixAll : List Text -> List Text
prefixAll ts = mapList (textAppend "pre") ts

firstOfList : List Text -> Text
firstOfList Nil         = "none"
firstOfList (Cons f fs) = f

export
firstField : Char -> Text -> Text
firstField c t = firstOfList (textSplit c t)

leadingChar : Text -> Maybe Char
leadingChar (MkText Nil)         = Nothing
leadingChar (MkText (Cons c cs)) = Just c

export
trimmedHead : Text -> Maybe Char
trimmedHead t = leadingChar (textTrim t)

-- The characters aren't used, so they aren't made into a list.
export
isText : Text -> Bool
isText (MkText _) = True
