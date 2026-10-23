-- core/Show.sw. The `Show` interface, its quoting and bracketing helpers, and
-- the `Show` instances for the core types. Loaded with the core:
-- Interpolation (`"${e}"`) and `deriving (Show)` use `Show`, and the elements
-- of lists and tuples print through it (docs/proposals/prelude-slim.md §2.1).

-- `Show` (docs/proposals/interfaces.md §5.14, §6.4): `"${e}"` inserts
-- `Show.toText e`. `toText` is for people (`"tea"` is `tea`); `toSource` is
-- a source-like representation, used for the elements of lists, tuples,
-- records and constructors (`"tea"` with its quotes). It isn't promised to
-- parse back. A data type or record declared in a program gets both
-- derived (`T.%instShow`); a module's own `instance` replaces that.

-- Itself: so `"${text}"` works when `text` is already text.
def Text.toText (text: Text): Text := text

-- The character on its own: `'a'.toText` is `"a"`.
def Char.toText (char: Char): Text := MkText [char]

-- `"True"` or `"False"`, as the constructors are written.
def Bool.toText: Bool -> Text
  | True => "True"
  | False => "False"

def Ordering.toText: Ordering -> Text
  | Less => "Less"
  | Equal => "Equal"
  | Greater => "Greater"

interface Show (a: Type) = {
  toText: a -> Text,
  toSource: a -> Text
}

-- An instance whose two fields are the same: for numbers, and for a user's
-- own type with a `toText`: `instance Point.instShow: Show Point := Show.fromText Point.toText`.
def Show.fromText (f: a -> Text): Show a := { toText = f, toSource = f }

-- A character as it's written in a literal quoted with `quote`, then `rest`.
def Show.escapeChar (quote: Char) (char: Char) (rest: List Char): List Char :=
  if Nat.equal (Char.toNat char) 92 then Cons '\\' (Cons '\\' rest)
  else if Nat.equal (Char.toNat char) (Char.toNat quote) then Cons '\\' (Cons char rest)
  else if Nat.equal (Char.toNat char) 10 then Cons '\\' (Cons 'n' rest)
  else if Nat.equal (Char.toNat char) 9 then Cons '\\' (Cons 't' rest)
  else if Nat.equal (Char.toNat char) 13 then Cons '\\' (Cons 'r' rest)
  else Cons char rest

-- As above, for a character that's followed by `next`: a `$` before a `{`
-- would start an interpolation.
def Show.escapeBefore (quote: Char) (char: Char) (rest: List Char): List Char -> List Char
  | Nil => Show.escapeChar quote char rest
  | Cons next _ =>
    if Nat.equal (Char.toNat char) 36 then
      (if Nat.equal (Char.toNat next) 123 then Cons '\\' (Cons char rest) else Cons char rest)
    else Show.escapeChar quote char rest

def Show.escapeChars (quote: Char): List Char -> List Char
  | Nil => Nil
  | Cons char chars => Show.escapeBefore quote char (Show.escapeChars quote chars) chars

-- `"tea"` with its quotes and escapes.
def Show.quoteText (text: Text): Text :=
  MkText (Cons '"' (List.append (Show.escapeChars '"' (Text.toList text)) (Cons '"' Nil)))

-- `'a'`.
def Show.quoteChar (char: Char): Text := MkText (Cons '\'' (Show.escapeChar '\'' char (Cons '\'' Nil)))

def Show.hasSpace: List Char -> Bool
  | Nil => False
  | Cons char chars => if Nat.equal (Char.toNat char) 32 then True else Show.hasSpace chars

-- Whether text starts like a bracketed or quoted thing, which reads as one
-- piece: `[`, `(`, `"`, `'`. (`{` is not one: braces straight after a
-- constructor name its fields, so a record argument is bracketed.)
def Show.startsBracketed (char: Char): Bool :=
  if Nat.equal (Char.toNat char) 91 then True
  else if Nat.equal (Char.toNat char) 40 then True
  else if Nat.equal (Char.toNat char) 34 then True
  else Nat.equal (Char.toNat char) 39

-- An argument of a constructor: bracketed when it has spaces and isn't
-- already one piece (`Some (Some 1)`, `Some (-5)`, `Some [1, 2]`,
-- `Some ({ price = 3 })`).
def Show.argOf (text: Text): List Char -> Text
  | Nil => text
  | Cons char chars =>
    if Nat.equal (Char.toNat char) 45 then Text.append "(" (Text.append text ")")
    else if Nat.equal (Char.toNat char) 123 then Text.append "(" (Text.append text ")")
    else if Show.startsBracketed char then text
    else if Show.hasSpace chars then Text.append "(" (Text.append text ")")
    else text

def Show.arg (text: Text): Text := Show.argOf text (Text.toList text)

def Show.itemsAfter (f: a -> Text): List a -> Text
  | Nil => ""
  | Cons x xs => Text.append ", " (Text.append (f x) (Show.itemsAfter f xs))

def Show.items (f: a -> Text): List a -> Text
  | Nil => ""
  | Cons x xs => Text.append (f x) (Show.itemsAfter f xs)

-- `[1, 2, 3]`, the elements through `f`.
def Show.list (f: a -> Text) (xs: List a): Text :=
  Text.append "[" (Text.append (Show.items f xs) "]")

def Option.showWith (f: a -> Text): Option a -> Text
  | None => "None"
  | Some x => Text.append "Some " (Show.arg (f x))

instance Nat.instShow: Show Nat := Show.fromText Nat.toText

instance Int.instShow: Show Int := Show.fromText Int.toText

instance Bool.instShow: Show Bool := Show.fromText Bool.toText

instance Char.instShow: Show Char := { toText = Char.toText, toSource = Show.quoteChar }

instance Text.instShow: Show Text := { toText = Text.toText, toSource = Show.quoteText }

instance Ordering.instShow: Show Ordering := Show.fromText Ordering.toText

instance List.instShow [auto show: Show a]: Show (List a) :=
  Show.fromText (xs => Show.list (x => Show.toSource x) xs)

instance Option.instShow [auto show: Show a]: Show (Option a) :=
  Show.fromText (Option.showWith (x => Show.toSource x))

def Result.showWith (f: a -> Text) (g: e -> Text): Result a e -> Text
  | Ok x => Text.append "Ok " (Show.arg (f x))
  | Err m => Text.append "Err " (Show.arg (g m))

instance Result.instShow [auto showA: Show a] [auto showE: Show e]: Show (Result a e) :=
  Show.fromText (Result.showWith (x => Show.toSource x) (m => Show.toSource m))

def Pair.showWith (f: a -> Text) (g: b -> Text): Pair a b -> Text
  | MkPair x y => Text.append "(" (Text.append (f x) (Text.append ", " (Text.append (g y) ")")))

instance Pair.instShow [auto showA: Show a] [auto showB: Show b]: Show (Pair a b) :=
  Show.fromText (Pair.showWith (x => Show.toSource x) (y => Show.toSource y))
