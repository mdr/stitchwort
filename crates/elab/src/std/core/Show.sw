--| The `Show` interface, its quoting and bracketing helpers, and
--| the `Show` instances for the core types.
-- Loaded with the core: Interpolation (`"${e}"`) and `deriving (Show)` use
-- `Show`, and the elements of lists and tuples print through it
-- (docs/proposals/prelude-slim.md §2.1).

-- `Show` (docs/proposals/interfaces.md §5.14, §6.4): `"${e}"` inserts
-- `Show.toText e`. `toText` is for people (`"tea"` is `tea`); `toSource` is
-- a source-like representation, used for the elements of lists, tuples,
-- records and constructors (`"tea"` with its quotes). It isn't promised to
-- parse back. A data type or record declared in a program gets both derived
-- (`T.%instShow`); a module's own `instance` replaces that.

--| Itself: so `"${text}"` works when `text` is already text.
def Text.toText (text: Text): Text := text

--| The character on its own: `'a'.toText` is `"a"`.
def Char.toText (char: Char): Text := MkText [char]

--| `"True"` or `"False"`, as the constructors are written.
def Bool.toText: (b: Bool) → Text
  | True => "True"
  | False => "False"

--| `"Less"`, `"Equal"` or `"Greater"`, as the constructors are written.
def Ordering.toText: (ordering: Ordering) → Text
  | Less => "Less"
  | Equal => "Equal"
  | Greater => "Greater"

--| Types whose values can be shown as text: `"${e}"` inserts `Show.toText e`.
--| `toSource` is the form used inside lists, tuples and records (`"tea"` with its quotes).
interface Show (a: Type) = { toText: a → Text, toSource: a → Text }

--| A `Show` instance that shows values with `f`, the same way inside lists and records as on their own.
--| For numbers, and for a user's own type with a
--| `toText`: `instance Point.instShow: Show Point := Show.fromText Point.toText`.
def Show.fromText (f: a → Text): Show a := { toText = f, toSource = f }

--| A character as it's written in a literal quoted with `quote`, then `rest`.
def Show.escapeChar (quote char: Char) (rest: List Char): List Char :=
  if Nat.equal (Char.toNat char) 92 then ['\\', '\\', ..rest]
  else if Nat.equal (Char.toNat char) (Char.toNat quote) then ['\\', char, ..rest]
  else if Nat.equal (Char.toNat char) 10 then ['\\', 'n', ..rest]
  else if Nat.equal (Char.toNat char) 9 then ['\\', 't', ..rest]
  else if Nat.equal (Char.toNat char) 13 then ['\\', 'r', ..rest]
  else [char, ..rest]

--| A character as it's written in a literal quoted with `quote`, when it's
--| followed by `next`: a `$` before a `{` would start an interpolation, so it is escaped.
def Show.escapeBefore (quote char: Char) (rest: List Char): (chars: List Char) → List Char
  | [] => Show.escapeChar quote char rest
  | [next, .._] =>
    if Nat.equal (Char.toNat char) 36 then
      (if Nat.equal (Char.toNat next) 123 then ['\\', char, ..rest] else [char, ..rest])
    else Show.escapeChar quote char rest

--| Characters as they're written in a literal quoted with `quote`.
def Show.escapeChars (quote: Char): (chars: List Char) → List Char
  | [] => []
  | [char, ..chars] => Show.escapeBefore quote char (Show.escapeChars quote chars) chars

--| `"tea"` with its quotes and escapes.
def Show.quoteText (text: Text): Text := MkText ['"', ..List.append (Show.escapeChars '"' (Text.toList text)) ['"']]

--| A character in quotes, escaped as in a literal: `'a'`.
def Show.quoteChar (char: Char): Text := MkText ['\'', ..Show.escapeChar '\'' char ['\'']]

--| Whether the characters include a space.
@[tailrec]
def Show.hasSpace: (chars: List Char) → Bool
  | [] => False
  | [char, ..chars] => if Nat.equal (Char.toNat char) 32 then True else Show.hasSpace chars

--| Whether text starts like a bracketed or quoted thing, which reads as one
--| piece: `[`, `(`, `{`, `"`, `'`. (A record is an argument as it is, `Some {
--| price = 3 }`, as after a function.)
def Show.startsBracketed (char: Char): Bool :=
  if Nat.equal (Char.toNat char) 91 then True
  else if Nat.equal (Char.toNat char) 40 then True
  else if Nat.equal (Char.toNat char) 123 then True
  else if Nat.equal (Char.toNat char) 34 then True
  else Nat.equal (Char.toNat char) 39

--| An argument of a constructor: bracketed when it has spaces and isn't
--| already one piece (`Some (Some 1)`, `Some (-5)`, `Some [1, 2]`,
--| `Some { price = 3 }`).
def Show.argOf (text: Text): (chars: List Char) → Text
  | [] => text
  | [char, ..chars] =>
    if Nat.equal (Char.toNat char) 45 then Text.append "(" (Text.append text ")")
    else if Show.startsBracketed char then text
    else if Show.hasSpace chars then Text.append "(" (Text.append text ")")
    else text

--| A constructor's argument as it is shown after the constructor: bracketed when it has spaces and isn't one piece.
def Show.arg (text: Text): Text := Show.argOf text (Text.toList text)

--| The elements through `f`, each after `, `.
def Show.itemsAfter (f: a → Text): (xs: List a) → Text
  | [] => ""
  | [x, ..xs] => Text.append ", " (Text.append (f x) (Show.itemsAfter f xs))

--| The elements through `f`, separated by `, `.
def Show.items (f: a → Text): (xs: List a) → Text
  | [] => ""
  | [x, ..xs] => Text.append (f x) (Show.itemsAfter f xs)

--| `[1, 2, 3]`, the elements through `f`.
def Show.list (f: a → Text) (xs: List a): Text := Text.append "[" (Text.append (Show.items f xs) "]")

--| An option as source text, the value shown by `f`: `None`, or `Some 3`.
@[noReceiver]
def Option.showWith (f: a → Text): (option: Option a) → Text
  | None => "None"
  | Some x => Text.append "Some " (Show.arg (f x))

instance Nat.instShow: Show Nat := Show.fromText Nat.toText

instance Int.instShow: Show Int := Show.fromText Int.toText

instance Bool.instShow: Show Bool := Show.fromText Bool.toText

instance Char.instShow: Show Char := { toText = Char.toText, toSource = Show.quoteChar }

instance Text.instShow: Show Text := { toText = Text.toText, toSource = Show.quoteText }

instance Ordering.instShow: Show Ordering := Show.fromText Ordering.toText

instance List.instShow [auto show: Show a]: Show (List a) := Show.fromText (xs => Show.list (x => Show.toSource x) xs)

instance Option.instShow [auto show: Show a]: Show (Option a) := Show.fromText (Option.showWith (x => Show.toSource x))

--| A result as source text, the value shown by `f` and the error by `g`: `Ok 3`, or `Err "bad"`.
@[noReceiver]
def Result.showWith (f: a → Text) (g: e → Text): (result: Result a e) → Text
  | Ok x => Text.append "Ok " (Show.arg (f x))
  | Err m => Text.append "Err " (Show.arg (g m))

instance Result.instShow [auto showA: Show a] [auto showE: Show e]: Show (Result a e) :=
  Show.fromText (Result.showWith (x => Show.toSource x) (m => Show.toSource m))

--| A pair as source text, its parts shown by `f` and `g`: `(1, "a")`.
@[noReceiver]
def Pair.showWith (f: a → Text) (g: b → Text): (pair: Pair a b) → Text
  | MkPair x y => Text.append "(" (Text.append (f x) (Text.append ", " (Text.append (g y) ")")))

instance Pair.instShow [auto showA: Show a] [auto showB: Show b]: Show (Pair a b) :=
  Show.fromText (Pair.showWith (x => Show.toSource x) (y => Show.toSource y))
