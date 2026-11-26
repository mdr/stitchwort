-- A record update whose base is a block: the block's lines must share a
-- column, so its `let` can't follow the opener while the line after it
-- starts at the opener's column (SW-4853).
def t: P := {
  let x := 1
  y|z }
