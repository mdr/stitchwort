-- Interfaces and instances (docs/proposals/interfaces.md, stage 1): an
-- interface is a record of operations; an instance is a definition of it
-- for one type, which `auto` finds by the type.

import Pretty (pretty)
import Std (Text)

interface Pretty (a: Type) =
  { pretty: a → Text }

instance Pretty.instNat: Pretty Nat :=
  { pretty = n => if n == 0 then "zero" else "some" }

instance Pretty.instBool: Pretty Bool :=
  { pretty = b => if b then "yes" else "no" }

-- An instance may ask for instances of its head's variables.
instance Pretty.instList [auto p: Pretty a]: Pretty (List a) :=
  { pretty = xs => "[" ++ Text.join (xs.map Pretty.pretty) ',' ++ "]" }

type Item =
  | MkItem

instance Item.instPretty: Pretty Item :=
  { pretty = i => "item" }

-- Asking for one: named, or not.
def shout [auto p: Pretty a] (x: a): Text := Pretty.pretty x ++ "!"
def whisper [auto Pretty a] (x: a): Text := "(" ++ Pretty.pretty x ++ ")"
def both: [auto Pretty a] → a → Text := x => shout x ++ whisper x

-- A named alternative: a plain `def` of the interface's type, never found
-- by `auto`, passed by name.
def loud: Pretty Nat := { pretty = n => "NUMBER" }

-- A function that builds a dictionary is a plain `def` too.
def withPrefix (prefix: Text): Pretty Item := { pretty = i => prefix ++ "item" }

-- A dictionary's fields, by dot notation.
def direct (d: Pretty Nat) (n: Nat): Text := d.pretty n

test "nat" := Pretty.pretty 3 == "some"
test "imported method" := pretty 0 == "zero"
test "bool" := Pretty.pretty True == "yes"
test "item" := Pretty.pretty MkItem == "item"
test "list" := Pretty.pretty [True, False] == "[yes,no]"
test "nested" := Pretty.pretty [[1], [0, 2]] == "[[some],[zero,some]]"
test "shout" := shout [MkItem] == "[item]!"
test "whisper" := whisper False == "(no)"
test "both" := both 0 == "zero!(zero)"
test "by name" := shout [p := loud] 3 == "NUMBER!"
test "by name, method" := Pretty.pretty [pretty := loud] 3 == "NUMBER"
test "builder" := Pretty.pretty [pretty := withPrefix "an "] MkItem == "an item"
test "direct" := direct loud 1 == "NUMBER"
test "direct, instance" := direct Pretty.instNat 1 == "some"
