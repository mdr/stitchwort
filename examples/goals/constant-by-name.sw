-- A constant in a goal is shown by its name, not by its value.
def maxHitPoints: Nat := 12

def startingRooms: List Nat := [3, 1, 4, 1, 5]

def healed (hitPoints: Nat): Nat :=
  if hitPoints + 4 ≤ maxHitPoints then hitPoints + 4 else maxHitPoints

theorem healedAtMost (hitPoints: Nat) (rooms: List Nat) (same: rooms = startingRooms):
    healed hitPoints ≤ maxHitPoints :=
  ?
