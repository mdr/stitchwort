-- An arm's pattern variables are listed before the hypotheses whose types
-- mention them: `x` and `rest` come before `h: xs = [x, ..rest]`, not after
-- it as if they were bound later.
def sumRestOrZero (xs: List Nat): Nat := match h: xs with
  | [] => 0
  | [x, ..rest] => ?
