-- A record update in a goal is shown as written, `{ x | f = s }`: for a
-- field shared by several constructors, and for a record.
type Shape =
  | Dot (ref: Nat) (id: Text)
  | Circle (ref: Nat) (id: Text) (radius: Nat)

type Player = { name: Text, hitPoints: Nat, gold: Nat }

def pick (first: Shape) (second: Shape): Shape := second

theorem renamedKeepsRef (shape: Shape) (newId: Text):
    ({ shape | id = newId ++ "!" }).ref = shape.ref :=
  ?

theorem renamedTwice (shape: Shape) (other: Shape) (newId: Text) (newRef: Nat):
    ({ pick shape other | id = newId, ref = newRef }) = { other | ref = newRef, id = newId } :=
  ?

theorem paid (player: Player) (amount: Nat) (same: {player | gold = amount} = player):
    ({ player | gold = amount, hitPoints = 3 }) = { player | hitPoints = 3 } :=
  ?
