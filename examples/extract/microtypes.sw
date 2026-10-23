-- Microtypes (docs/syntax.md, "Microtypes"; docs/proposals/microtypes.md):
-- a one-field record is a type of its own, so a `UserId` can't be passed
-- where an `OrderId` is expected, and `@[js.unboxed]` makes it cross the JS
-- boundary as its field's own form, a plain `string`, instead of as
-- `{ value: string }`. In TypeScript it is `type UserId = string`, named at
-- every use. A `Map` from one, in its derived order, is a plain object.
--
-- run: wrap "u1"
-- run: unwrap { value = "u1" }
-- run: same { value = "u1" } { value = "u1" }
-- run: same { value = "u1" } { value = "u2" }
-- run: owners [{ id = { value = "o1" }, owner = { value = "u1" }, helper = None }, { id = { value = "o2" }, owner = { value = "u2" }, helper = Some { value = "u3" } }]
-- run: helperOf { id = { value = "o1" }, owner = { value = "u1" }, helper = Some { value = "u3" } }
-- run: helperOf { id = { value = "o1" }, owner = { value = "u1" }, helper = None }
-- run: creator (Created { value = "u9" })
-- run: creator Deleted
-- run: ownerOf (Map.fromList [({ value = "o1" }, { value = "u1" }), ({ value = "o2" }, { value = "u2" })]) { value = "o2" }
-- run: ownerOf Map.empty { value = "o2" }
-- run: visits (Map.fromList [({ value = "b" }, 1), ({ value = "a" }, 2), ({ value = "__proto__" }, 3)]) { value = "a" }
-- run: visits Map.empty { value = "" }
-- run: domain { value = "ada@example.com", valid = rfl }
-- run: mailbox (Map.fromList [({ value = "a@b", valid = rfl }, 1)])
-- run: bump { value = 41 }
-- run: tagged { value = ["x", "y"] }
-- run: named { value = "Ada" }

import Std (Bool, List, Map, Nat, Option, Show, Text)

@[js.unboxed]
type UserId = { value: Text }

@[js.unboxed]
type OrderId = { value: Text }

-- `${u}` prints the text alone.
instance UserId.instShow: Show UserId := Show.fromText (u => u.value)

-- A proof field is checked on the way in, as for any record.
def Email.isValid (t: Text): Bool := Text.contains "@" t

@[js.unboxed]
type Email = { value: Text, valid: Email.isValid value = True }

-- Any field type that crosses: a `bigint`, a list.
@[js.unboxed]
type Count = { value: Nat }

@[js.unboxed]
type Tags = { value: List Text }

-- Inside a record, an `Option` and a list, and in a constructor's field.
type Order = { id: OrderId, owner: UserId, helper: Option UserId }

type Event =
  | Created (by: UserId)
  | Deleted

export def wrap (t: Text): UserId := { value = t }

export def unwrap (u: UserId): Text := u.value

export def same (a: UserId) (b: UserId): Bool := a == b

export def owners (orders: List Order): List UserId := orders.map (o => o.owner)

export def helperOf (o: Order): Option UserId := o.helper

export def creator: Event -> Option UserId
  | Created u => Some u
  | Deleted => None

-- Keys in the derived order, which is `Text`'s.
export def ownerOf (orders: Map OrderId UserId) (o: OrderId): Option UserId := Map.get o orders

export def visits (m: Map UserId Nat) (u: UserId): Map UserId Nat := Map.insertWith Nat.add u 1 m

export def domain (e: Email): Text := e.value

export def mailbox (m: Map Email Nat): List Email := Map.keys m

export def bump (c: Count): Count := { value = c.value + 1 }

export def tagged (t: Tags): Nat := List.length t.value

export def named (u: UserId): Text := "user ${u}"
