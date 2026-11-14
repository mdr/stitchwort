-- `match h: x == y with | True => DecEq.sound h` on a type with a derived
-- `DecEq`: `DecEq.sound` finds `x` and `y` in `h`'s type with nothing else
-- to go on, since `x == y` is a call of `T.%decide` kept as the call, not
-- what it computes to (on a record, its fields' tests joined by `&&`). The
-- same for a record of one field, whose equality is its field's.
import Std (Bool, DecEq, Eq, List, Nat, Option, Text, Void)

type Position = { row: Nat, column: Nat }

type Monster = { position: Position, glyph: Char }

type Cave = { name: Text }

def monsterAt (position: Position): List Monster → Option Monster
  | [] => None
  | [monster, ..others] => if monster.position == position then Some monster else monsterAt position others

-- No monster is where the player is, so the player isn't on this one's cell.
theorem notOnMonster ∀ (player: Position) (monster: Monster) (monsters: List Monster)
    (clear: monsterAt player monsters = None)
    (located: monsterAt monster.position monsters = Some monster):
    (player == monster.position) = False :=
  match same: player == monster.position with
    | True =>
      let vacant: monsterAt monster.position monsters = None := rewrite <- DecEq.sound same in clear
      Void.exfalso (Option.noneNotSome monster (Eq.trans (Eq.sym vacant) located))
    | False => rfl

-- The monster `monsterAt` finds is on the cell asked about.
theorem foundThere ∀ (position: Position) (found: Monster) (monsters: List Monster)
    (located: monsterAt position monsters = Some found):
    found.position = position :=
  match monsters with
    | [monster, ..others] =>
      match same: monster.position == position with
        | True =>
          let here := DecEq.sound same
          rewrite <- Option.someInjective located in here
        | False => foundThere position found others located

-- A table built from a list of caves has an entry for each of them.
theorem lookupBuilt ∀ (f: Cave → List Cave) (cave: Cave) (caves: List Cave)
    (member: cave ∈ caves):
    List.lookup (caves.map (c => (c, f c))) cave = Some (f cave) :=
  match caves with
    | [c, ..rest] =>
      match e: c == cave with
        | True => rewrite DecEq.sound e in rfl
        | False =>
          match member with
            | Inl same => Void.exfalso (Bool.trueNotFalse (rewrite same, DecEq.refl cave at e))
            | Inr later => lookupBuilt f cave rest later
