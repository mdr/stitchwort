-- A playlist's tracks laid end to end: each starts when the one before it
-- ends. With durations that are not negative, the start times never go
-- down, proved for every playlist from `Float.addMonotoneRight`.
import Std (Float, List, Text)

type Track = { title: Text, duration: Float }

-- The start time of each track, the first at `start`.
def startTimes (start: Float): List Track → List Float
  | Nil => Nil
  | Cons track rest => Cons start (startTimes (start + track.duration) rest)

def NoNegativeDurations: List Track → Prop
  | Nil => Unit
  | Cons track rest => And (0.0 <= track.duration) (NoNegativeDurations rest)

theorem nextStartNotEarlier (start: Float) (duration: Float) (nonNegative: 0.0 <= duration):
    (rest: List Track) → List.LeHead Float.leq start (startTimes (start + duration) rest)
  | Nil => Trivial
  | Cons next more => Float.addMonotoneRight start duration nonNegative

theorem startTimesAscend: (start: Float) → (tracks: List Track) → NoNegativeDurations tracks
    → List.Sorted Float.leq (startTimes start tracks)
  | start, Nil, ok => Trivial
  | start, Cons track rest, Both nonNegative restOk =>
    Both (nextStartNotEarlier start track.duration nonNegative rest)
      (startTimesAscend (start + track.duration) rest restOk)

def playlist: List Track := [
  { title = "Intro", duration = 0.0 },
  { title = "Overture", duration = 312.5 },
  { title = "Interlude", duration = 0.1 },
  { title = "Finale", duration = 401.25 }
]

test "start times" := startTimes 0.0 playlist == [0.0, 0.0, 312.5, 312.6]

theorem playlistAscends: List.Sorted Float.leq (startTimes 0.0 playlist) :=
  startTimesAscend 0.0 playlist (Both rfl (Both rfl (Both rfl (Both rfl Trivial))))
