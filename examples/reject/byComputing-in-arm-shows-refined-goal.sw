-- expect-error: E-REFL
-- In the `Rock` arm the message says `beats Rock Rock`, not `beats m m`.
type Move = | Rock | Paper | Scissors

def beats: Move -> Move -> Bool
  | Rock, Scissors => True
  | Paper, Rock => True
  | Scissors, Paper => True
  | _, _ => False

theorem selfBeats ∀ (m: Move): beats m m = True :=
  match m with
    | Rock => byComputing
    | Paper => byComputing
    | Scissors => byComputing
