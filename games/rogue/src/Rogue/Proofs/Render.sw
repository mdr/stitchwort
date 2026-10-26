-- What `render` draws where: `@` at the player's row and column
-- (`renderPlayer`), and each monster's letter at its cell (`renderMonster`,
-- and `renderEveryMonster` for a valid state). Each cell of the level is
-- `glyphAt` of the marks on its row over the terrain (`renderCell`); the
-- player's mark comes first, so it's the one drawn, and the monsters'
-- come next.
--
-- The cell must be one the terrain covers. That the player and every
-- monster always are, in every state a real game reaches, is Bounds.sw
-- (`drawnPlayer`, `drawnMonster`).

namespace Rogue.Proofs
import Rogue (..)
import Std (Bool, DecEq, Eq, List, Nat, Option, Pair, Text, Void)

-- The player's mark is the first on the player's row, so it's drawn.
theorem glyphAtPlayer (state: State) (terrain: Char): glyphAt (marksIn state state.player.row) state.player.column terrain = '@' :=
  rewrite natEqSelf state.player.row, natEqSelf state.player.column in rfl

theorem lengthWithIndexFrom: (start: Nat) → (xs: List a) → (List.withIndexFrom start xs).length = xs.length
  | start, [] => rfl
  | start, Cons x xs => Eq.cong Succ (lengthWithIndexFrom (Succ start) xs)

-- The `index`th of a list mapped with its indices.
theorem getOrMapIndexed (f: Pair Nat a → b) (fallback: b) (d: a):
    (start: Nat) → (xs: List a) → (index: Nat) → index < xs.length →
    ((List.withIndexFrom start xs).map f).getOr fallback index = f (MkPair (start + index) (xs.getOr d index))
  | start, [], index, inside => Void.exfalso (Bool.falseNotTrue inside)
  | start, Cons x xs, Zero, inside => rewrite Nat.addZero start in rfl
  | start, Cons x xs, Succ index, inside => rewrite Nat.addSucc start index in getOrMapIndexed f fallback d (Succ start) xs index inside
-- Among the monsters' marks on a cell's row, the first in the cell's column
-- is the glyph of the monster `monsterAt` finds there.
theorem findMonsterMark (position: Position) (found: Monster) (rest: List (Nat, Char)):
    (monsters: List Monster) → monsterAt position monsters = Some found →
    (List.append (monsters.filterMap (monster => if monster.position.row == position.row then Some (monster.position.column, monster.kind.glyph) else None)) rest).find (mark => mark.fst == position.column)
      = Some (position.column, found.kind.glyph)
  | [], located => Void.exfalso (Option.noneNotSome found located)
  | Cons monster others, located =>
    match same: monster.position == position with
      | True =>
        let here := DecEq.sound monster.position position same
        let itIs := Option.someInjective monster found located
        rewrite here, natEqSelf position.row, natEqSelf position.column, itIs in rfl
      | False =>
        match sameRow: monster.position.row == position.row with
          | True => rewrite columnDiffers monster.position position same sameRow in findMonsterMark position found rest others located
          | False => findMonsterMark position found rest others located

-- A monster's cell, unless the player stands there, shows that monster.
theorem glyphAtMonster (state: State) (position: Position) (found: Monster) (located: monsterAt position state.monsters = Some found)
    (notPlayer: (state.player == position) = False) (terrain: Char):
    glyphAt (marksIn state position.row) position.column terrain = found.kind.glyph :=
  let items := state.items.filterMap (item => if item.position.row == position.row then Some (item.position.column, item.loot.glyph) else None)
  match sameRow: state.player.row == position.row with
    | True => rewrite columnDiffers state.player position notPlayer sameRow, findMonsterMark position found items state.monsters located in rfl
    | False => rewrite findMonsterMark position found items state.monsters located in rfl

-- The character `render` draws at a cell of the level is `glyphAt` of what
-- stands on the cell's row, over the terrain there (for a cell the terrain
-- covers, as every made level's terrain covers the level).
theorem renderCell (state: State) (position: Position) (tall: position.row < state.level.terrain.length)
    (wide: position.column < (state.level.terrain.getOr [] position.row).length):
    ((render state).getOr "" position.row).toList.getOr ' ' position.column =
      glyphAt (marksIn state position.row) position.column ((state.level.terrain.getOr [] position.row).getOr ' ' position.column) :=
  let terrain := state.level.terrain
  let row := position.row
  let column := position.column
  let chars := terrain.getOr [] row
  let drawCell: List (Nat, Char) → (Nat, Char) → Char := marks => ((column, char)) => glyphAt marks column char
  let drawRow: (Nat, List Char) → Text := ((row, chars)) =>
    let marks := marksIn state row
    chars.withIndex.map (drawCell marks) |> Text.fromList
  let rows := terrain.withIndex.map drawRow
  let long: row < rows.length := rewrite List.lengthMap terrain.withIndex drawRow, lengthWithIndexFrom 0 terrain in tall
  let first: (render state).getOr "" row = rows.getOr "" row :=
    List.getOrAppendLeft rows "" row [statusLine state, keysLine, state.message] long
  let second: rows.getOr "" row = drawRow (0 + row, chars) := getOrMapIndexed drawRow "" [] 0 terrain row tall
  let third: (chars.withIndex.map (drawCell (marksIn state (0 + row)))).getOr ' ' column = glyphAt (marksIn state (0 + row)) (0 + column) (chars.getOr ' ' column) :=
    getOrMapIndexed (drawCell (marksIn state (0 + row))) ' ' ' ' 0 chars column wide
  rewrite first, second in rewrite third, zeroPlus row, zeroPlus column in rfl

-- `render` draws `@` at the player's row and column.
theorem renderPlayer (state: State) (tall: state.player.row < state.level.terrain.length)
    (wide: state.player.column < (state.level.terrain.getOr [] state.player.row).length):
    ((render state).getOr "" state.player.row).toList.getOr ' ' state.player.column = '@' :=
  rewrite renderCell state state.player tall wide in glyphAtPlayer state _

-- And a monster's glyph at each monster's cell: the first monster there, if
-- more than one stood on it (which a valid state never has), and unless the
-- player stands there (which a valid state never has either).
theorem renderMonster (state: State) (position: Position) (found: Monster) (located: monsterAt position state.monsters = Some found)
    (notPlayer: (state.player == position) = False) (tall: position.row < state.level.terrain.length)
    (wide: position.column < (state.level.terrain.getOr [] position.row).length):
    ((render state).getOr "" position.row).toList.getOr ' ' position.column = found.kind.glyph :=
  rewrite renderCell state position tall wide in glyphAtMonster state position found located notPlayer _

-- In a valid state every monster is drawn at its cell: no other monster
-- shares it (`Apart`), and the player is never on it (`Clear`).
theorem renderEveryMonster (state: State) (valid: Valid state) (monster: Monster) (listed: List.Mem monster state.monsters)
    (tall: monster.position.row < state.level.terrain.length) (wide: monster.position.column < (state.level.terrain.getOr [] monster.position.row).length):
    ((render state).getOr "" monster.position.row).toList.getOr ' ' monster.position.column = monster.kind.glyph :=
  let located := monsterAtOwnCell monster state.monsters valid.apart listed
  let notPlayer: (state.player == monster.position) = False :=
    match same: state.player == monster.position with
      | True =>
        let vacant: monsterAt monster.position state.monsters = None := rewrite <- DecEq.sound state.player monster.position same in valid.clear
        Void.exfalso (Option.noneNotSome monster (Eq.trans (Eq.sym vacant) located))
      | False => rfl
  renderMonster state monster.position monster located notPlayer tall wide
