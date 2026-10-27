-- expect-error: E-NONEXHAUSTIVE
-- An or-pattern covers its alternatives and no more: characters other than
-- `'a'` and `'b'` are still missing.
def isAB: Char → Bool
  | 'a' | 'b' => True
