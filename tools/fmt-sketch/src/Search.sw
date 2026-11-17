--| Spike K1's search (SW-3825), run natively so it can try millions of
--| cases: random short token sequences over `Settled`'s small alphabet,
--| with comments and line breaks, checked against `settledHomed`,
--| `settledAnyLayout` and `settledIdempotent`, the `plain` ones and the
--| others counted apart. `search --count N --seed N` prints the counts and
--| the first failures of each kind; `--candidate` tries `settledBare`.
namespace Fmt.Sketch.Search
import Fmt.Sketch.Settled (..)
import Std (Args, Bool, ExitStatus, IO, List, Nat, Option, Text)
import Syntax (Leaf, Lexed)

def next (state: Nat): Nat := (state * 1103515245 + 12345) % 2147483648

--| `count` cells from the generator's state, and the state after.
def cells (count state: Nat) (made: List Cell): (List Cell, Nat) := match count with
  | Zero => (made, state)
  | Succ fewer =>
    let bits := next state / 64
    let cell: Cell :=
      { kind = bits / 16, leading = bits % 8 == 0, trailing = (bits / 8) % 3 == 0, breaks = (bits / 2) % 2 == 0 }
    cells fewer (next state) [cell, ..made]

def bools (count state: Nat) (made: List Bool): List Bool := match count with
  | Zero => made
  | Succ fewer => bools fewer (next state) [(next state / 1024) % 2 == 0, ..made]

def Leaf.shown (leaf: Leaf): Text :=
  let above := leaf.trivia.leading.map (comment => "${comment.text}⏎") |> Text.concat
  let after := leaf.trivia.trailing.map (comment => " ${comment.text}⏎") |> .getOrElse ""
  "${if leaf.token.lineStart then "⏎" else " "}${above}${leaf.token.text}${after}"

def Lexed.shown (lexed: Lexed): Text := lexed.leaves.map Leaf.shown |> Text.concat

type Tally = {
  plain: Nat,
  other: Nat,
  --| Settled results with a comment on a closer or bar: rule 1's limits used.
  kept: Nat,
  plainNotHomed: Nat,
  plainMoved: Nat,
  plainUnsettled: Nat,
  --| Plain cases whose result changes when a holder need not start its line.
  plainLoose: Nat,
  otherNotHomed: Nat,
  otherMoved: Nat,
  otherUnsettled: Nat,
  shown: List Text
}

def Tally.note (tally: Tally) (label: Text) (lexed: Lexed): Tally :=
  if tally.shown.filter (line => line.startsWith label) |> .length |> (count => count >= 3) then tally
  else { tally | shown = ["${label}: ${lexed.shown}", ..tally.shown] }

def holds (lexed: Lexed): Bool := lexed.leaves.any (leaf =>
  leaf.trivia.trailing.isSome && (leaf.token.kind.isCloser || leaf.token.kind == Syntax.Tok.Pipe))

def step (candidate: Bool) (tally: Tally) (state: Nat): Tally :=
  let length := 2 + (next state / 4096) % 8
  let (made, after) := cells length (next state) []
  let source := sample made
  let settle := (lexed: Lexed) => if candidate then lexed.settledBare else lexed.settled
  let settled := settle source
  let isHomed := homed settled.leaves
  let again := bools length after []
  let same := (choices: List Bool) (keeping: Bool) => (settle (settled.laid keeping choices)).bare == settled.bare
  let stays := same [] True && same again True && same (again.map (_ => True)) True
  let loose := same [] False && same again False
  let idempotent := settle settled == settled
  let tally := if holds settled then { tally | kept = tally.kept + 1 } else tally
  if (if candidate then grammatical source.leaves && !strayComma source.leaves else plain source.leaves) then
    let tally := { tally | plain = tally.plain + 1 }
    let tally :=
      if isHomed then tally else { tally | plainNotHomed = tally.plainNotHomed + 1 } |> .note "plain, not homed" source
    let tally := if stays then tally else { tally | plainMoved = tally.plainMoved + 1 } |> .note "plain, moved" source
    let tally :=
      if loose then tally else { tally | plainLoose = tally.plainLoose + 1 } |> .note "plain, loose layout moves" source
    if idempotent then tally
    else { tally | plainUnsettled = tally.plainUnsettled + 1 } |> .note "plain, not idempotent" source
  else
    let tally := { tally | other = tally.other + 1 }
    let tally :=
      if isHomed then tally else { tally | otherNotHomed = tally.otherNotHomed + 1 } |> .note "other, not homed" source
    let tally := if stays then tally else { tally | otherMoved = tally.otherMoved + 1 } |> .note "other, moved" source
    if idempotent then tally
    else { tally | otherUnsettled = tally.otherUnsettled + 1 } |> .note "other, not idempotent" source

def loop (candidate: Bool) (count state: Nat) (tally: Tally): Tally := match count with
  | Zero => tally
  | Succ fewer => loop candidate fewer (next (next state + count)) (step candidate tally state)

type Options = { count: Nat, seed: Nat, candidate: Bool }

def program: Args.Program := { name = "search", about = "Searches rule N's layout statements (spike K1)." }

def options: Args.Spec Options :=
  Args.Spec.start ((count seed: Nat) (candidate: Bool) => ({ count, seed, candidate }: Options))
    |> .and (Args.option "count" (default := 100000) (metavar := "N") (help := "How many cases."))
    |> .and (Args.option "seed" (default := 1) (metavar := "N") (help := "The generator's seed."))
    |> .and
      (Args.flag "candidate"
        (help := "Take the last commas out before rule N (`settledBare`), counting a parking comma as plain."))

def run (options: Options): {IO} ExitStatus :=
  let start: Tally := {
    plain = 0,
    other = 0,
    kept = 0,
    plainNotHomed = 0,
    plainMoved = 0,
    plainUnsettled = 0,
    plainLoose = 0,
    otherNotHomed = 0,
    otherMoved = 0,
    otherUnsettled = 0,
    shown = []
  }
  let tally := loop options.candidate options.count options.seed start
  IO.write
    "cases ${options.count} seed ${options.seed}: plain ${tally.plain}, other ${tally.other}, with a comment kept on a closer or bar ${tally.kept}\n"
  IO.write
    "plain: not homed ${tally.plainNotHomed}, moved in a keeping layout ${tally.plainMoved}, not idempotent ${tally.plainUnsettled}, moved in a loose layout ${tally.plainLoose}\n"
  IO.write
    "other: not homed ${tally.otherNotHomed}, moved in a keeping layout ${tally.otherMoved}, not idempotent ${tally.otherUnsettled}\n"
  tally.shown.reverse.forEach (line => IO.write "${line}\n")
  ExitStatus.success

def main(): {IO} ExitStatus := Args.runStatus program options run
