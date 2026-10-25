-- The kernel compares two calls of the same definition by their arguments
-- first, and only by what they compute if those differ (D483,
-- docs/proposals/folded-calls.md §7 stage 4). This is the shape of the
-- roguelike's "generate on the stairs" lemma (docs/proposals/
-- opaque-definitions.md §2.3): a level made from an unknown seed, reached
-- two ways. Computing both copies of `mix 16 seed` and comparing them part
-- by part doubles the work with every round (each round mentions the last
-- one twice): 12 s before this, and well over a minute for 18 rounds.
-- `generate seed` against `generate seed` is equal at once (0.15 s).

type Level = { cells: Nat, start: Nat }

type State = { level: Level, turn: Nat }

-- Rounds of arithmetic on a seed nothing is known about.
def mix (rounds: Nat) (seed: Nat): Nat :=
  match rounds with
    | 0 => seed
    | Succ rest => mix rest (seed * seed + seed)

def generate (seed: Nat): Level := { cells = mix 16 seed, start = 0 }

def descend (seed: Nat) (state: State): State := { level = generate seed, turn = state.turn + 1 }

theorem descendMakes (seed: Nat) (state: State): (descend seed state).level = generate seed := rfl

theorem descendCells (seed: Nat) (state: State): (descend seed state).level.cells = (generate seed).cells := rfl
