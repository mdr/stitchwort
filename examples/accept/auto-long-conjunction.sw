-- `auto` finds a side of a long `&&` hypothesis, `(a && b && …) = True`,
-- whose sides are calls with tests of their own, where reading every test
-- in it stops at its bound (SW-4507, as `cases` does since SW-4485): both
-- `Std.byDecision` and an `[auto]` argument close `g.fine = True`, the
-- seventh of eight, from `Bool.andLeft` and `Bool.andRight` of the
-- hypothesis. The name `Std.byDecision` makes the module load them.
type Tile = | Floor | Wall | Door | Water

def Tile.open: Tile → Bool
  | Floor => True
  | Door => True
  | _ => False

def Tile.dry: Tile → Bool
  | Water => False
  | _ => True

def Tile.fine (tile: Tile): Bool := tile.open && tile.dry

def needs (g: Tile) [auto h: g.fine = True]: Nat := 1

theorem usesIt ∀ (a b c d e f g h: Tile)
    (fine: (a.fine && b.fine && c.fine && d.fine && e.fine && f.fine && g.fine && h.fine) = True):
    needs g = 1 :=
  byComputing

theorem seventhFine ∀ (a b c d e f g h: Tile)
    (fine: (a.fine && b.fine && c.fine && d.fine && e.fine && f.fine && g.fine && h.fine) = True):
    g.fine = True :=
  Std.byDecision
