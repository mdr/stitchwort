-- A pair that starts a line after an ability row goes too: the layout joins the lines, so a second pass would drop it.
def readVec [n: Nat] (): {IO}
 (Vec Nat n) :=
  readIt
