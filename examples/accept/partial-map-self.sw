-- A partial function that maps itself over its children: std's `List.map`
-- takes partial callbacks, because its row variable `e` is used only bare,
-- `{e}`, so it may stand for a partial row (docs/proposals/partial-stage-3.md
-- §2.2, D1214). The map is then a partial computation in `countNodes`'s own
-- description, and adds no ticks of its own (§4).
import Std (List, Nat)

def children (n: Nat): List Nat := if n > 3 then [] else [n + 1, n + 2]

def countNodes (n: Nat): {Partial} Nat := 1 + List.sum (List.map (children n) countNodes)

test "countNodes" := countNodes 0 == 15
