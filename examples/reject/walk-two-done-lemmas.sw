-- expect-error: E-WALK-LEMMA
-- A family has one `@[walk.done]` lemma, so which one a walk uses never
-- depends on the order they were loaded in. `Parse.Gives` already has
-- `Parse.givesDone`.

import Std (Parse)

@[walk.done]
theorem givesDoneAgain ∀ [inv: Parse.Invariant t] [x: a] [holds: a → Prop] (proved: holds x):
    Parse.Gives inv (() => x) holds :=
  Parse.givesDone proved
