-- A spread in the middle of a list prints as it was written. The source
-- `[0, ..chain, highest + 3]` elaborates to `Cons 0 (chain ++ [highest + 3])`,
-- and the `append` inside the brackets prints as the spread and item it was
-- built from (SW-2151). At the top of a term, `++` stays `++`.
import Std (List, Nat)

theorem middleSpread ∀ (chain: List Nat) (highest: Nat): [0, ..chain, highest + 3] = chain := ?

theorem appendAtTop ∀ (chain: List Nat) (highest: Nat): chain ++ [highest + 3] = chain := ?
