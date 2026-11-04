-- expect-error: E-PARSE
-- Braces after a constructor with no fields, as an argument: there is
-- nothing to build it by, so the note suggests only a bracketed record.

type Position = { row: Nat, column: Nat }

type Square =
  | Open
  | Tree

def pick (square: Square) (position: Position): Square := square

def d: Square := pick Open { row = 1, column = 2 }
