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
-- JS's `trim` also removes U+00A0, U+2028 and U+FEFF; `Text.trim` doesn't.
-- run: trim " \t\n\r\u{B}\u{C}x y \r\n"
-- run: trim "\u{A0}x\u{2028}"
-- run: trim "\u{FEFF}x"
-- `Number` or `parseInt` accepts each of these; `Text.toNat` accepts only
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
-- run: orEmpty (Some "\u{1F600}")
-- run: orEmpty None
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

import Std (Char, List, Nat, Pair, Text)

export def len (t: Text): Nat := Text.length t

export def chars (t: Text): List Char := Text.toList t

export def fromChars (cs: List Char): Text := Text.fromList cs

export def echo (t: Text): Text := t

export def echoChar (c: Char): Char := c

export def codeOf (c: Char): Nat := Char.toNat c

export def charOf (n: Nat): Option Char := Char.fromNat n

export def same (a: Text) (b: Text): Bool := a == b

export def order (a: Text) (b: Text): Ordering := Text.compare a b

export def join (a: Text) (b: Text): Text := a ++ b

export def split (c: Char) (t: Text): List Text := Text.split c t

export def joinOn (c: Char) (ts: List Text): Text := Text.join c ts

export def trim (t: Text): Text := Text.trim t

export def toNat (t: Text): Option Nat := Text.toNat t

export def fromNat (n: Nat): Text := Nat.toText n

export def uncons (t: Text): Option (Pair Char Text) := Text.uncons t

-- User code over the characters.
export def reverse (t: Text): Text := Text.fromList (List.reverseOnto (Text.toList t) Nil)

def countIn (c: Char): List Char -> Nat
  | Nil       => 0
  | Cons d ds => if c == d then Succ (countIn c ds) else countIn c ds

export def countChar (c: Char) (t: Text): Nat := countIn c (Text.toList t)

-- Text inside a user's data type, a list and the prelude's `Option` and `Pair`.
type Person: Type =
  | MkPerson (name: Text) (initial: Char) (tags: List Text)

export def greet: Person -> Text
  | MkPerson name initial tags => "Hello, " ++ name ++ " (" ++ Text.fromList (Cons initial Nil) ++ ")"

def initialsOf: List Person -> List Char
  | Nil => Nil
  | Cons (MkPerson n i t) ps => Cons i (initialsOf ps)

export def initials (ps: List Person): List Char := initialsOf ps

export def rename (n: Text): Person -> Person
  | MkPerson m i t => MkPerson n i (Cons m t)

export def orEmpty: Option Text -> Text
  | None => ""
  | Some t  => t

export def firstOf (p: Pair Char Text): Char := Pair.fst p

-- Fields named like the decoder's own variables.
type Located: Type =
  | At (path: Text) (x: Char) (inside: List Char)

export def located: Located -> Located
  | At p c cs => At (p ++ "/") c (Cons c cs)

-- The prelude's text operations are native JavaScript, and a `Text` is a
-- string. These use them as values, partly applied, and with their results
-- taken apart by ordinary pattern matching.
export def empty (t: Text): Bool := Text.isEmpty t

export def less (a: Text) (b: Text): Bool := Text.less a b

export def codes (t: Text): List Nat := Text.fold (c ns => Cons (Char.toNat c) ns) Nil t

def mapList (f: a -> b): List a -> List b
  | Nil       => Nil
  | Cons x xs => Cons (f x) (mapList f xs)

export def lengths (ts: List Text): List Nat := mapList Text.length ts

export def texts (ls: List (List Char)): List Text := mapList MkText ls

export def prefixAll (ts: List Text): List Text := mapList (Text.append "pre") ts

def firstOfList: List Text -> Text
  | Nil       => "none"
  | Cons f fs => f

export def firstField (c: Char) (t: Text): Text := firstOfList (Text.split c t)

def leadingChar: Text -> Option Char
  | MkText Nil         => None
  | MkText (Cons c cs) => Some c

export def trimmedHead (t: Text): Option Char := leadingChar (Text.trim t)

-- The characters aren't used, so they aren't made into a list.
export def isText: Text -> Bool
  | MkText _ => True
