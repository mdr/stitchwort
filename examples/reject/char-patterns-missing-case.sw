-- expect-error: E-NONEXHAUSTIVE
-- Characters alone never cover every case: there's always another character.
def isAB : Char -> Bool
  | 'a' => True
  | 'b' => True
