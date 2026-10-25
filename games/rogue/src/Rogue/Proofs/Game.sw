-- The whole game: a valid state stays valid however many turns follow,
-- whatever the seed and command of each (`replayValid`). `replay` folds
-- one turn per seed and command, as the seeded handler runs `step`.

namespace Rogue.Proofs
import Rogue (..)
import Std (List, Nat)

def replay (state: State) (turns: List (Nat, Command)): State :=
  turns.foldLeft state (current turn => seeded turn.fst (() => step current turn.snd))

theorem replayValid: (turns: List (Nat, Command)) → (state: State) → Valid state → Valid (replay state turns)
  | [], state, valid => valid
  | Cons (seed, command) rest, state, valid => replayValid rest (seeded seed (() => step state command)) (stepValid seed state command valid)
