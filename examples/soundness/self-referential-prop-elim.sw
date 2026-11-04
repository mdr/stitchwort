-- expect-error: E-PROP-ELIM
-- A proposition whose constructor holds a proof of the proposition itself
-- can't be matched to produce data (D1980, Lean's rule). In the
-- proof-irrelevant model every `l: Loop` is `MkLoop (Loop.inv l)`, so `steps l`
-- could always be unfolded once more: with proofs compared irrelevantly,
-- conversion would be undecidable (Carneiro 2019;
-- docs/proposals/proof-irrelevance.md §5.1, §7.11). Matched to produce a
-- proof, `Loop` is fine: accept/self-referential-prop.sw.
import Std (Nat)

type Loop: Prop =
  | MkLoop (next: Loop)

def steps (l: Loop): Nat :=
  match l with
    | MkLoop n => Succ (steps n)
