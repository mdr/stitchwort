-- A microtype's derived `==` and order are its field's: an `@[js.unboxed]`
-- id compares as a plain `===` on the string (`Text.decEq`) and orders by
-- `Text.compare`, called directly, as `Text` itself does, rather than
-- through a wrapper around the field's dictionary (SW-590). The same for a
-- `Nat` field, whose order is a record of fields rather than
-- `Ord.fromCompare`, and for a field with a proof beside it. Since these
-- only pass their arguments on, they are the field's functions and
-- instances, the same JS objects: `Map` and `List.distinct` are passed
-- `Text.instOrd` itself (SW-603).
--
-- run: same { value = "c1" } { value = "c1" }
-- run: same { value = "c1" } { value = "c2" }
-- run: order { value = "a" } { value = "b" }
-- run: order { value = "b" } { value = "b" }
-- run: order { value = "é" } { value = "z" }
-- run: unseen [{ id = { value = "c1" }, n = 1 }, { id = { value = "c2" }, n = 2 }, { id = { value = "c3" }, n = 3 }] [{ value = "c2" }]
-- run: unseen [] [{ value = "c2" }]
-- run: byId [{ id = { value = "c2" }, n = 2 }, { id = { value = "c1" }, n = 1 }, { id = { value = "c2" }, n = 5 }]
-- run: distinctIds [{ value = "b" }, { value = "a" }, { value = "b" }, { value = "c" }, { value = "a" }]
-- run: sameCount { value = 3 } { value = 3 }
-- run: orderCount { value = 10 } { value = 9 }
-- run: distinctCounts [{ value = 2 }, { value = 1 }, { value = 2 }]
-- run: sameEmail { value = "a@b", valid = rfl } { value = "a@b", valid = rfl }
-- run: orderEmail { value = "b@c", valid = rfl } { value = "a@b", valid = rfl }

import Std (Bool, List, Map, Nat, Option, Ord, Ordering, Text)

@[js.unboxed]
type CardId = { value: Text }

type Card = { id: CardId, n: Nat }

@[js.unboxed]
type Count = { value: Nat }

def Email.isValid (t: Text): Bool := Text.contains t "@"

@[js.unboxed]
type Email = { value: Text, valid: Email.isValid value = True }

export def same (a: CardId) (b: CardId): Bool := a == b

export def order (a: CardId) (b: CardId): Ordering := Ord.compare a b

export def unseen (cards: List Card) (seen: List CardId): List Card := cards.filter (c => c.id ∉ seen)

export def byId (cards: List Card): Map CardId Card := Map.indexBy cards (c => c.id)

export def distinctIds (ids: List CardId): List CardId := List.distinct ids

export def sameCount (a: Count) (b: Count): Bool := a == b

export def orderCount (a: Count) (b: Count): Ordering := Ord.compare a b

export def distinctCounts (counts: List Count): List Count := List.distinct counts

export def sameEmail (a: Email) (b: Email): Bool := a == b

export def orderEmail (a: Email) (b: Email): Ordering := Ord.compare a b
