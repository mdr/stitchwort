-- Imports the type, and with it its constructors.
namespace Day

import Turns (Move)

def turn: Move := Clockwise

test "a constructor imported with its type" := turn == Clockwise
