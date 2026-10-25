-- A record update across lines: a field after `state |` that starts a line
-- lines up with the other fields (games/rogue/NOTES.md §11).
def afterLets (state: State): State :=
  let events := 1
  let hitPoints := 2
  {
    state |
    monsters = events,
    hitPoints,
    turn = state.turn + 1
  }

def alone (state: State): State := {
  state |
  monsters = 1,
  turn = 2
}

def inBranch (state: State) (target: Position): State :=
  if True then {
    state |
    player = target,
    potions = []
  }
  else state

def sameLine (state: State): State := {
  state | monsters = 1,
  turn = 2
}
