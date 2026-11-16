-- expect-warning: W-REWRITE-REPEATEDLY-UNUSED
-- A listed rule that never rewrote anything, or a set none of whose rules
-- did, warns: an unused rule hides which ones the proof needs. A call
-- checked once per case (`cases then`) warns only about a rule no case used.
import Std (Bool, List, Nat)

rules appends := [List.appendAssoc, List.appendNil]

theorem unused ∀ (xs: List Nat): xs ++ [] = xs := rewrite repeatedly [List.appendNil, List.reverseCons]

theorem unusedSet ∀ (n: Nat) (h: n = 3): n + 1 = 4 := rewrite repeatedly [h, appends]

theorem inSomeCase ∀ (b: Bool) (xs: List Nat): (if b then xs ++ [] else xs) = xs :=
  cases then rewrite repeatedly [List.appendNil]
