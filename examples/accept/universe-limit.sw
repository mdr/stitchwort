-- Pairs with the soundness/universe-*.sw examples (SW-902): the largest
-- universe that can be written as a term is `Type 65534`, in `Type 65535`.
def nearTop: Type 65534 := Type 65533

type Big: Type 65534 =
  | MkBig (t: Type 65533)
