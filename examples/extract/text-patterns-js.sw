-- Text patterns in the generated JS: a `Text` crosses as a string, which the
-- match takes apart into its characters.
--
-- run: keyword "def"
-- run: keyword "do"
-- run: keyword "é→"
-- run: keyword "dog"
-- run: keyword ""
-- run: arrow ['-', '>', 'x']
-- run: arrow ['-', 'x']

export def keyword (word: Text): Nat := match word with
  | "def" => 1
  | "do" | "é→" => 2
  | "" => 3
  | _ => 0

export def arrow (rest: List Char): Bool := match rest with
  | "->" => True
  | ['-', '>', .._] => True
  | _ => False
