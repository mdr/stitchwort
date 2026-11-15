--| A probe of `Toy.Doc.Proofs.Lays` over the goldens and the comment
--| probes: the places a document may leave the printer at (`reach`), as
--| `Lays` lists them but as a set and without the trace, so that it runs.
--| `None` is where `Lays` is `False`: a space or a separator at a line
--| start, a trailing comment at a line start or while another waits. It
--| holds at every width, since neither `Lays` nor `reach` has one.

namespace Toy.Fmt.Tests
import Toy.Doc (..)
import Toy.Doc.Proofs (..)
import Toy.Fmt (..)
import Toy.Syntax (..)
import Std (List, Nat, Option, Result, Text)

def samePlace: Place → Place → Bool
  | AtStart one, AtStart other => one == other
  | Mid one, Mid other => one == other
  | Held one, Held other => one == other
  | _, _ => False

def addPlaces (new old: List Place): List Place :=
  new.foldLeft old (found place => if found.any (samePlace place) then found else [place, ..found])

--| The places `step` leaves from any of `places`, if it refuses none.
def eachPlace (step: Place → Option (List Place)) (places: List Place): Option (List Place) := match places with
  | [] => Some []
  | [place, ..rest] =>
    match step place, eachPlace step rest with
      | Some here, Some there => Some (addPlaces here there)
      | _, _ => None

def chunkStep (indent: Nat) (text: Text) (place: Place): Option (List Place) :=
  if text.isEmpty then Some [place]
  else if text.all (char => char == ' ') then
    match place with
      | AtStart _ => None
      | _ => Some [place]
  else if text == "\n" then None
  else
    match place with
      | AtStart at => Some [Mid at]
      | Mid at => Some [Mid at]
      | Held at => Some [Mid (Nat.max indent (at + 2))]

def sepStep (indent: Nat) (place: Place): Option (List Place) := match place with
  | AtStart _ => None
  | Mid at => Some [Mid at, AtStart indent]
  | Held _ => Some [AtStart indent]

def softStep (indent: Nat) (place: Place): Option (List Place) := match place with
  | Held _ => Some [AtStart indent]
  | other => Some [other, AtStart indent]

def startStep (indent: Nat) (place: Place): Option (List Place) := match place with
  | AtStart at => Some [AtStart at]
  | Mid at => Some [AtStart (Nat.max indent (at + 2))]
  | Held at => Some [AtStart (Nat.max indent (at + 2))]

def suffixStep (comment: Text) (place: Place): Option (List Place) := match place with
  | Mid at => if isLayout comment then None else Some [Held at]
  | _ => None

--| The places `doc` may leave the printer at, from any of `places`, in a
--| construct indented `indent`; `None` if `Lays` refuses a way through it.
def reach: Doc → Nat → List Place → Option (List Place)
  | Doc.Chunk text _, indent, places => eachPlace (chunkStep indent text) places
  | Line, indent, places => eachPlace (sepStep indent) places
  | SoftLine, indent, places => eachPlace (softStep indent) places
  | HardLine, indent, places => eachPlace (place => Some [AtStart indent]) places
  | CommentEnd, _, places => eachPlace (place => Some [AtStart place.indent]) places
  | LineStart, indent, places => eachPlace (startStep indent) places
  | LineStartHere, indent, places => eachPlace (place => Some [AtStart indent]) places
  | Nest more inner, indent, places => reach inner (indent + more) places
  | Group inner _, indent, places => reach inner indent places
  | Flatten inner, indent, places => reach inner indent places
  | OneLineBelow inner, indent, places => reach inner (indent + 2) [AtStart (indent + 2)]
  | Concat docs, indent, places => reachAll docs indent places
  | Fill [], _, places => Some places
  | Fill [first, ..others], indent, places =>
    match reach first indent places with
      | Some after => reachSeps others indent after
      | None => None
  | Choice options, indent, places => reachOptions options indent places
  | LineSuffix comment, _, places => eachPlace (suffixStep comment) places
  | _, _, places => Some places

def reachAll: List Doc → Nat → List Place → Option (List Place)
  | [], _, places => Some places
  | [doc, ..rest], indent, places =>
    match reach doc indent places with
      | Some after => reachAll rest indent after
      | None => None

def reachSeps: List Doc → Nat → List Place → Option (List Place)
  | [], _, places => Some places
  | [item, ..more], indent, places =>
    match eachPlace (sepStep indent) places with
      | Some middle =>
        match reach item indent middle with
          | Some after => reachSeps more indent after
          | None => None
      | None => None

def reachOptions: List Doc → Nat → List Place → Option (List Place)
  | [], _, places => Some places
  | [last], indent, places => reach last indent places
  | [option, ..others], indent, places =>
    match reach option indent places, reachOptions others indent places with
      | Some one, Some rest => Some (addPlaces one rest)
      | _, _ => None

def lays (file: SourceFile): Bool := (reach file.layout 0 [AtStart 0]).isSome

test "reach follows a line break into a nest" :=
  match reach (Concat [Doc.Chunk "f" 1, Nest 2 (Concat [HardLine, Doc.Chunk "x" 1])]) 0 [AtStart 0] with
    | Some [Mid 2] => True
    | _ => False

test "reach refuses a space at a line start" := (reach (Concat [HardLine, Doc.Chunk " " 1]) 0 [AtStart 0]).isNone

test "every golden's layout lays, whichever way its groups, fills and choices go" :=
  goldens.all (golden => lays golden.tree)

test "every comment probe's layout lays" := probes.all (probe =>
  match parse probe.source with
    | Ok file => lays file
    | Err _ => False)
