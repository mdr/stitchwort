-- expect-error: E-OMEGA
-- A proof search given as an argument is checked after the rest of its
-- call (stage 7, rule 1), so when it fails its message shows the goal the
-- call fixed: `entry.snd`, which waited for the list after the lambda,
-- not a placeholder for it.
import Std (List, Nat)

theorem moreThanOne (f: a → Nat) (xs: List a) (h: 1 < List.sumBy xs f): 1 < List.sumBy xs f := h

def wrong (counts: List (Nat, Nat)) (given: 0 < List.sumBy counts (entry => entry.snd)): Nat :=
  match moreThanOne (entry => entry.snd) counts (omega [given]) with
    | h => 0
