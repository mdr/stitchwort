-- The microtype recipe (docs/syntax.md, "Microtypes"): ids that can't be
-- mixed up, a validated `Email` built by a smart constructor, and a
-- `Map OrderId UserId` that crosses to JavaScript as a plain object.
--
-- run: parseEmail "ada@example.com"
-- run: parseEmail "nobody"
-- run: emailText { value = "ada@example.com", valid = rfl }
-- run: ownerOf (Map.fromList [({ value = "o1" }, { value = "u1" }), ({ value = "o2" }, { value = "u2" })]) { value = "o2" }
-- run: ownerOf Map.empty { value = "o1" }
-- run: assign (Map.fromList [({ value = "o1" }, { value = "u1" })]) { value = "o2" } { value = "u2" }
-- run: assign (Map.fromList [({ value = "o1" }, { value = "u1" })]) { value = "o1" } { value = "u2" }
-- run: ordersOf (Map.fromList [({ value = "o1" }, { value = "u1" }), ({ value = "o2" }, { value = "u2" }), ({ value = "o3" }, { value = "u1" })]) { value = "u1" }
-- run: describe { value = "o7" } { value = "u3" }

import Std (Bool, Fail, List, Map, Option, Show, Text)

@[js.unboxed]
type UserId = { value: Text }

@[js.unboxed]
type OrderId = { value: Text }

-- The derived `Show` prints `{ value = "u1" }`; these print the text alone.
instance UserId.instShow: Show UserId := Show.fromText (u => u.value)

instance OrderId.instShow: Show OrderId := Show.fromText (o => o.value)

def Email.isValid (t: Text): Bool := Text.contains t "@"

-- The proof field makes an invalid `Email` impossible to write, and is checked
-- on the way in from JavaScript.
@[js.unboxed]
type Email = { value: Text, valid: Email.isValid value = True }

-- The smart constructor: the only way to get an `Email` from arbitrary text.
def Email.parse (t: Text): Option Email :=
  if h: Email.isValid t = True then Some ({ value = t, valid = h }) else None

-- The same check for code that may fail, with a message.
def Email.parseOrFail (t: Text): {Fail} Email :=
  (Email.parse t).orFail "not an email address: ${t}"

test "a valid address" := (Email.parse "ada@example.com").isSome
test "an invalid address" := (Email.parse "nobody").isNone
test "the failing form" := Fail.toOption (() => Email.parseOrFail "nobody") == None

test "ids of one kind compare" := ({ value = "u1" }: UserId) == { value = "u1" }
test "show prints the text" := "${({ value = "u1" }: UserId)}" == "u1"

export def parseEmail (t: Text): Option Email := Email.parse t

export def emailText (e: Email): Text := e.value

-- The map's keys are `OrderId`s in their derived order, which is `Text`'s: in
-- JavaScript, `{ [orderId: string]: string }`.
export def ownerOf (owners: Map OrderId UserId) (o: OrderId): Option UserId := Map.get owners o

export def assign (owners: Map OrderId UserId) (o: OrderId) (u: UserId): Map OrderId UserId :=
  Map.insert owners o u

export def ordersOf (owners: Map OrderId UserId) (u: UserId): List OrderId :=
  (Map.toList owners).filterMap (entry => if entry.snd == u then Some entry.fst else None)

export def describe (o: OrderId) (u: UserId): Text := "order ${o} belongs to ${u}"
