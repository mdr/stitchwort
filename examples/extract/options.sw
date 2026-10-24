-- `Option T` at the JS boundary (D582): `T | undefined`, no tagged object.
-- `undefined` is `None`; any other value is `Some` of it (so `null` is
-- refused). In a record's field it is an optional property `f?: T`: a
-- missing property is `None`, and an encoded `None` leaves the property out.
-- Only an `Option` inside an `Option` keeps the tagged object, so `Some None`
-- and `None` stay apart.
--
-- run: nickname { name = "Ada", nick = None, age = None }
-- run: nickname { name = "Ada", nick = Some "Countess", age = None }
-- run: withNick { name = "Ada", nick = None, age = Some 36 } (Some "A")
-- run: withNick { name = "Ada", nick = Some "A", age = None } None
-- run: halve (Some 8)
-- run: halve None
-- run: wrap (Some 1)
-- run: wrap None
-- run: unwrap (Some (Some 1))
-- run: unwrap (Some None)
-- run: unwrap None
-- run: keepSome [Some 1, None, Some 3]
-- run: markAll [1, 2, 3]
-- run: peek { items = [Some 1, None], extra = Some [None] }
-- run: swapSides (MkBoth (Some 1) "x")
-- run: required { value = Some 3, ok = rfl }
-- run: capOf { cap = Some ({ value = 7, fits = rfl }) }
-- run: capOf { cap = None }

import Std (Bool, List, Nat, Option, SafeNat, Text)

-- Optional properties: `nick?: string`, `age?: bigint`.
type Profile = { name: Text, nick: Option Text, age: Option Nat }

export def nickname (p: Profile): Text := Option.getOrElse p.name p.nick

export def withNick (p: Profile) (n: Option Text): Profile := { p | nick = n }

-- An argument and a result: `bigint | undefined`.
export def halve: Option Nat -> Option Nat
  | None => None
  | Some n => Some (Nat.div n 2)

-- Nested: the outer is `T | undefined`, the inner the tagged `Option<bigint>`.
export def wrap (x: Option Nat): Option (Option Nat) := Some x

export def unwrap: Option (Option Nat) -> Option Nat
  | None => None
  | Some None => Some 0
  | Some (Some n) => Some n

-- In a list: `(bigint | undefined)[]`.
export def keepSome: List (Option Nat) -> List Nat
  | Nil => Nil
  | Cons None r => keepSome r
  | Cons (Some n) r => Cons n (keepSome r)

export def markAll (xs: List Nat): List (Option Nat) := List.map (x => if Nat.leq x 1 then None else Some x) xs

-- Optional properties of a record with a list, and a list of options.
type Peek = { items: List (Option Nat), extra: Option (List (Option Nat)) }

export def peek (p: Peek): Peek := p

-- A constructor's field is not a record's, so it's `T | undefined`, present.
type Both: Type =
  | MkBoth (left: Option Nat) (right: Text)

export def swapSides: Both -> Both
  | MkBoth l r => MkBoth (Some (Text.length r)) (describe l)

def describe: Option Nat -> Text
  | None => "none"
  | Some n => Nat.toText n

-- A proof field about an `Option` field: checked after it's decoded.
def isSomeNat: Option Nat -> Bool
  | None => False
  | Some _ => True

def Present (o: Option Nat): Prop := isSomeNat o = True

instance decPresent (o: Option Nat): Decidable (Present o) := Bool.decTrue (isSomeNat o)

type Required = { value: Option Nat, ok: Present value }

export def required (r: Required): Option Nat := r.value

-- `SafeNat` inside an optional property: `cap?: number`.
type Cap = { cap: Option SafeNat }

export def capOf (c: Cap): Option SafeNat := c.cap
