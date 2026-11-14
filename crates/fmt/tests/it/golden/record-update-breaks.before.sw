-- A record update too long for one line keeps `{ position |` together and
-- breaks the fields after it (S31).

def update (position: Position) (someLongName: Int) (anotherLongName: Int): Position := { position | x = position.x + someLongName * anotherLongName, y = position.y + someLongName * anotherLongName, facing = turnedLeft position.facing }

-- The shape the old line-based formatter printed normalises to the same.
def alone (position: Position) (someLongName: Int) (anotherLongName: Int): Position := {
  position |
  x = position.x + someLongName * anotherLongName,
  y = position.y + someLongName * anotherLongName,
  facing = turnedLeft position.facing
}

-- A trailing comment on the base stays on the `{ r |` line too.
def noted (position: Position): Position := { position -- the current position
  | x = 1 }
