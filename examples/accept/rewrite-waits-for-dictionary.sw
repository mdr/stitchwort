-- A `rewrite` whose goal holds an operator's dictionary not found yet
-- (docs/proposals/postponement.md, step 4.2). `g` is a let-bound lambda's
-- parameter, whose type only `f h` fixes, so `List.sumBy … g`'s `Add`
-- instance is an obligation still waiting when the `rewrite` is elaborated,
-- and the rule's `List.sumBy` computes to a fold with a different unknown
-- dictionary than the goal's. The `rewrite` fails, the goal holds the
-- obligation's unknown, which the declaration will still settle, so it
-- waits and is tried again once the instance is found (`Add Int`).
import Std (Eq, Int, List, Nat)

def split (xs ys: List Nat) (h: Nat → Int): List.sumBy (xs ++ ys) h = List.sumBy xs h + List.sumBy ys h :=
  let f := g =>
    (rewrite List.sumByAppend xs ys g in rfl: List.sumBy (xs ++ ys) g = Add.add (List.sumBy xs g) (List.sumBy ys g))
  f h

-- With `g`'s type written, the instance is found at once.
def annotated (xs ys: List Nat) (h: Nat → Int): List.sumBy (xs ++ ys) h = List.sumBy xs h + List.sumBy ys h :=
  let f := (g: Nat → Int) =>
    (rewrite List.sumByAppend xs ys g in rfl: List.sumBy (xs ++ ys) g = Add.add (List.sumBy xs g) (List.sumBy ys g))
  f h
