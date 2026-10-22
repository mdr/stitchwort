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

-- Itself: so `"${t}"` works when `t` is already text.
def Text.toText (t: Text): Text := t

-- The character on its own: `'a'.toText` is `"a"`.
def Char.toText (c: Char): Text := MkText [c]

-- `"True"` or `"False"`, as the constructors are written.
def Bool.toText: Bool -> Text
  | True  => "True"
  | False => "False"

def Ordering.toText: Ordering -> Text
  | Less    => "Less"
  | Equal   => "Equal"
  | Greater => "Greater"

interface Show (a: Type) =
  { toText: a -> Text
  , toSource: a -> Text
  }

-- An instance whose two fields are the same: for numbers, and for a user's
-- own type with a `toText`: `instance Point.instShow: Show Point := Show.fromText Point.toText`.
def Show.fromText (f: a -> Text): Show a := { toText = f, toSource = f }

-- A character as it's written in a literal quoted with `q`, then `rest`.
def Show.escapeChar (q: Char) (c: Char) (rest: List Char): List Char :=
  if Nat.equal (Char.toNat c) 92 then Cons '\\' (Cons '\\' rest)
  else if Nat.equal (Char.toNat c) (Char.toNat q) then Cons '\\' (Cons c rest)
  else if Nat.equal (Char.toNat c) 10 then Cons '\\' (Cons 'n' rest)
  else if Nat.equal (Char.toNat c) 9 then Cons '\\' (Cons 't' rest)
  else if Nat.equal (Char.toNat c) 13 then Cons '\\' (Cons 'r' rest)
  else Cons c rest

-- As above, for a character that's followed by `next`: a `$` before a `{`
-- would start an interpolation.
def Show.escapeBefore (q: Char) (c: Char) (rest: List Char): List Char -> List Char
  | Nil      => Show.escapeChar q c rest
  | Cons d _ =>
    if Nat.equal (Char.toNat c) 36 then
      (if Nat.equal (Char.toNat d) 123 then Cons '\\' (Cons c rest) else Cons c rest)
    else Show.escapeChar q c rest

def Show.escapeChars (q: Char): List Char -> List Char
  | Nil       => Nil
  | Cons c cs => Show.escapeBefore q c (Show.escapeChars q cs) cs

-- `"tea"` with its quotes and escapes.
def Show.quoteText (t: Text): Text :=
  MkText (Cons '"' (List.append (Show.escapeChars '"' (Text.toList t)) (Cons '"' Nil)))

-- `'a'`.
def Show.quoteChar (c: Char): Text := MkText (Cons '\'' (Show.escapeChar '\'' c (Cons '\'' Nil)))

def Show.hasSpace: List Char -> Bool
  | Nil       => False
  | Cons c cs => if Nat.equal (Char.toNat c) 32 then True else Show.hasSpace cs

-- Whether text starts like a bracketed or quoted thing, which reads as one
-- piece: `[`, `(`, `{`, `"`, `'`.
def Show.startsBracketed (c: Char): Bool :=
  if Nat.equal (Char.toNat c) 91 then True
  else if Nat.equal (Char.toNat c) 40 then True
  else if Nat.equal (Char.toNat c) 123 then True
  else if Nat.equal (Char.toNat c) 34 then True
  else Nat.equal (Char.toNat c) 39

-- An argument of a constructor: bracketed when it has spaces and isn't
-- already one piece (`Some (Some 1)`, `Some (-5)`, `Some [1, 2]`).
def Show.argOf (t: Text): List Char -> Text
  | Nil       => t
  | Cons c cs =>
    if Nat.equal (Char.toNat c) 45 then Text.append "(" (Text.append t ")")
    else if Show.startsBracketed c then t
    else if Show.hasSpace cs then Text.append "(" (Text.append t ")")
    else t

def Show.arg (t: Text): Text := Show.argOf t (Text.toList t)

def Show.itemsAfter (f: a -> Text): List a -> Text
  | Nil       => ""
  | Cons x xs => Text.append ", " (Text.append (f x) (Show.itemsAfter f xs))

def Show.items (f: a -> Text): List a -> Text
  | Nil       => ""
  | Cons x xs => Text.append (f x) (Show.itemsAfter f xs)

-- `[1, 2, 3]`, the elements through `f`.
def Show.list (f: a -> Text) (xs: List a): Text :=
  Text.append "[" (Text.append (Show.items f xs) "]")

def Option.showWith (f: a -> Text): Option a -> Text
  | None => "None"
  | Some x  => Text.append "Some " (Show.arg (f x))

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

def Pair.showWith (f: a -> Text) (g: b -> Text): Pair a b -> Text
  | MkPair x y => Text.append "(" (Text.append (f x) (Text.append ", " (Text.append (g y) ")")))

instance Pair.instShow [auto showA: Show a] [auto showB: Show b]: Show (Pair a b) :=
  Show.fromText (Pair.showWith (x => Show.toSource x) (y => Show.toSource y))

