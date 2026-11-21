-- `cases` finds a side of a long `&&` hypothesis, `(a && b && …) = True`,
-- whose sides are calls with tests of their own, where reading every test
-- in it stops at its bound (SW-4485; docs/syntax.md, "cases"). Only the
-- `&&`s are followed, so `g.fine = True` is `Bool.andLeft` and
-- `Bool.andRight` of the hypothesis, not a search of splits that runs out
-- of budget.
type Tile = | Floor | Wall | Door | Water

def Tile.open: Tile → Bool
  | Floor => True
  | Door => True
  | _ => False

def Tile.dry: Tile → Bool
  | Water => False
  | _ => True

def Tile.fine (tile: Tile): Bool := tile.open && tile.dry

theorem seventhFine ∀ (a b c d e f g h: Tile)
    (fine: (a.fine && b.fine && c.fine && d.fine && e.fine && f.fine && g.fine && h.fine) = True):
    g.fine = True :=
  cases
