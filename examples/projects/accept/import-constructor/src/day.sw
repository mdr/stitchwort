-- Naming a constructor beside its type adds nothing: the type already
-- brings its constructors.
namespace Day

import Turns (Move, Clockwise)

def turn: Move := Clockwise
def forward: Move := Forward

test "a constructor listed with its type" := turn == Clockwise
test "the type brings its other constructors" := forward == Forward
