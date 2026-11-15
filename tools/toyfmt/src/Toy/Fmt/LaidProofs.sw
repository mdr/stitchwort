--| Where the rules put each word: the rules' half of positions. `Lays`
--| (the engine's half, `printLays`) says where a document's words go from
--| a place; here each rule's document is taken through it. A token with
--| its comments puts down exactly `tokenEvents` and leaves the line at
--| `tokenEnd` (`tokenLays`).

namespace Toy.Fmt.Proofs
import Toy.Doc (..)
import Toy.Doc.Proofs (..)
import Toy.Syntax (..)
import Toy.Syntax.Proofs (..)
import Toy.Fmt (..)
import Std (Bool, DecEq, Eq, List, Nat, Option, Parse, Text, Void)

-- Documents one after another.

theorem emptyLays ∀ (doc: Doc) (indent: Nat) (place: Place) (trace: List Event) (next: Place → List Event → Prop)
    (empty: doc.isEmpty = True)
    (lays: Lays doc indent place trace next):
    next place trace :=
  match doc, empty, lays with | Empty, _, lays => lays

theorem filterLays ∀ (docs: List Doc) (indent: Nat) (place: Place) (trace: List Event)
    (next: Place → List Event → Prop)
    (lays: LaysAll docs indent place trace next):
    LaysAll (docs.filter (doc => not doc.isEmpty)) indent place trace next :=
  match docs, lays with
    | [], lays => lays
    | [doc, ..rest], lays =>
      match empty: doc.isEmpty with
        | True =>
          filterLays rest indent place trace next
            (emptyLays doc indent place trace (after later => LaysAll rest indent after later next) empty lays)
        | False =>
          laysWeaker doc indent place trace
            (after later => LaysAll rest indent after later next)
            (after later => LaysAll (rest.filter (doc => not doc.isEmpty)) indent after later next)
            (after later others => filterLays rest indent after later next others)
            lays

--| `Doc.concat` lays as the documents one after another.
theorem concatLays ∀ (docs: List Doc) (indent: Nat) (place: Place) (trace: List Event)
    (next: Place → List Event → Prop)
    (lays: LaysAll docs indent place trace next):
    Lays (Doc.concat docs) indent place trace next :=
  let kept := filterLays docs indent place trace next lays
  match found: docs.filter (doc => not doc.isEmpty) with
    | [] => kept
    | [only] =>
      laysWeaker only indent place trace
        (after later => LaysAll [] indent after later next)
        next
        (after later reached => reached)
        kept
    | [first, second, ..rest] => kept

-- A word.

--| Where a word written at `place` starts its line, if it does: at the
--| line's indentation if nothing is on the line, and on a new line, a
--| comment break, after a waiting comment.
def wordStart (indent: Nat) (place: Place): Option Nat := match place with
  | AtStart at => Some at
  | Mid _ => None
  | Held at => Some (Nat.max indent (at + 2))

--| The indentation of the line a word written at `place` is on.
def wordLine (indent: Nat) (place: Place): Nat := match place with
  | AtStart at => at
  | Mid at => at
  | Held at => Nat.max indent (at + 2)

--| A word is one event, and the line then has words on it.
theorem wordLays ∀ (indent: Nat) (text: Text) (place: Place) (trace: List Event) (next: Place → List Event → Prop)
    (solid: Solid text)
    (reached: next (Mid (wordLine indent place)) (trace ++ [{ word = text, start = wordStart indent place }])):
    WriteLays indent text place trace next :=
  match solid with
    | Both filled (Both noGap layout) =>
      match text.isEmpty, filled with
        | True, never => Void.exfalso (Bool.falseNotTrue (Eq.sym never))
        | False, _ =>
          match gap: text.all (char => char == ' '), noGap, layout with
            | False, _, oneLine =>
              match place, reached with
                | AtStart at, reached => Both oneLine reached
                | Mid at, reached => Both oneLine reached
                | Held at, reached => Both oneLine reached

-- A token's comments.

--| The column of the line a `LineStart` at `place` leaves the printer at
--| the start of: the line it is on if nothing is on it, else a new one, a
--| comment break.
def breakColumn (indent: Nat) (place: Place): Nat := match place with
  | AtStart at => at
  | Mid at => Nat.max indent (at + 2)
  | Held at => Nat.max indent (at + 2)

--| Own-line comments, each starting its line at `column`.
def aboveEvents (column: Nat) (above: List Comment): List Event := match above with
  | [] => []
  | [comment, ..rest] => [{ word = comment.text, start = Some column }, ..aboveEvents column rest]

--| A trailing comment, after the words on its line.
def afterEvents: Option Comment → List Event
  | None => []
  | Some comment => [{ word = comment.text, start = None }]

--| Where the comments above a token leave the printer: where it was if
--| there are none, else at the start of a line at the comments' column.
def aboveEnd (indent: Nat) (place: Place) (above: List Comment): Place := match above with
  | [] => place
  | _ => AtStart (breakColumn indent place)

--| The place after a token on a line indented `line`: its trailing
--| comment waits for the end of the line.
def trailEnd (line: Nat) (after: Option Comment): Place := match after with
  | None => Mid line
  | Some _ => Held line

theorem notesLay ∀ (comments: List Comment) (indent column: Nat) (trace: List Event)
    (next: Place → List Event → Prop)
    (fine: FineAbove comments)
    (reached: next (AtStart column) (trace ++ aboveEvents column comments)):
    LaysAll (comments.map (comment => Doc.concat [Doc.text comment.text, CommentEnd])) indent (AtStart column) trace next :=
  match comments, fine, reached with
    | [], _, reached => rewrite <- List.appendNil trace in reached
    | [comment, ..rest], Both first others, reached =>
      concatLays [Doc.text comment.text, CommentEnd] indent (AtStart column) trace
        (after later =>
          LaysAll
            (rest.map (comment => Doc.concat [Doc.text comment.text, CommentEnd]))
            indent
            after
            later
            next)
        (wordLays indent comment.text (AtStart column) trace
          (after later =>
            LaysAll [CommentEnd] indent after later (reached written =>
              LaysAll
                (rest.map (comment => Doc.concat [Doc.text comment.text, CommentEnd]))
                indent
                reached
                written
                next))
          (commentSolid comment.text first)
          (notesLay rest indent column (trace ++ [{ word = comment.text, start = Some column }]) next others
            (rewrite List.appendAssoc trace [{ word = comment.text, start = Some column }] (aboveEvents column rest) in
              reached)))

--| The comments above a token: each on a line of its own at one column,
--| where the token then starts its line.
theorem aboveLays ∀ (above: List Comment) (indent: Nat) (place: Place) (trace: List Event)
    (next: Place → List Event → Prop)
    (fine: FineAbove above)
    (reached: next (aboveEnd indent place above) (trace ++ aboveEvents (breakColumn indent place) above)):
    Lays (commentsAbove above) indent place trace next :=
  match above, fine, reached with
    | [], _, reached => rewrite <- List.appendNil trace in reached
    | [comment, ..rest], fine, reached =>
      concatLays
        [LineStart, ..[comment, ..rest].map (comment => Doc.concat [Doc.text comment.text, CommentEnd])]
        indent
        place
        trace
        next
        (match place, reached with
          | AtStart at, reached => notesLay [comment, ..rest] indent at trace next fine reached
          | Mid at, reached => notesLay [comment, ..rest] indent (Nat.max indent (at + 2)) trace next fine reached
          | Held at, reached => notesLay [comment, ..rest] indent (Nat.max indent (at + 2)) trace next fine reached)

--| A trailing comment after a token is one event, and waits.
theorem trailingLays ∀ (after: Option Comment) (indent line: Nat) (trace: List Event)
    (next: Place → List Event → Prop)
    (fine: FineAfter after)
    (reached: next (trailEnd line after) (trace ++ afterEvents after)):
    Lays (trailingComment after) indent (Mid line) trace next :=
  match after, fine, reached with
    | None, _, reached => rewrite <- List.appendNil trace in reached
    | Some comment, fine, reached =>
      match commentSolid comment.text fine with | Both _ (Both _ layout) => Both layout reached

-- A token.

--| The events of a token with its comments, written at `place` in a
--| construct indented `indent`: the comments above it, the token (after
--| them it starts their line), its trailing comment.
def tokenEvents (indent: Nat) (place: Place) (comments: Comments) (text: Text): List Event :=
  aboveEvents (breakColumn indent place) comments.above
    ++ [{ word = text, start = wordStart indent (aboveEnd indent place comments.above) }, ..afterEvents comments.after]

--| The place after a token with its comments.
def tokenEnd (indent: Nat) (place: Place) (comments: Comments): Place :=
  trailEnd (wordLine indent (aboveEnd indent place comments.above)) comments.after

--| A token with its comments (P8) puts down `tokenEvents` and leaves the
--| line at `tokenEnd`, from any place.
theorem tokenLays ∀ (comments: Comments) (text: Text) (indent: Nat) (place: Place) (trace: List Event)
    (next: Place → List Event → Prop)
    (fine: Fine comments)
    (solid: Solid text)
    (reached: next (tokenEnd indent place comments) (trace ++ tokenEvents indent place comments text)):
    Lays (token comments text) indent place trace next :=
  match fine with
    | Both fineAbove fineAfter =>
      let above := aboveEvents (breakColumn indent place) comments.above
      let word: Event := { word = text, start = wordStart indent (aboveEnd indent place comments.above) }
      concatLays [commentsAbove comments.above, Doc.text text, trailingComment comments.after] indent place trace next
        (aboveLays comments.above indent place trace
          (after later => LaysAll [Doc.text text, trailingComment comments.after] indent after later next)
          fineAbove
          (wordLays indent text (aboveEnd indent place comments.above) (trace ++ above)
            (after later => LaysAll [trailingComment comments.after] indent after later next)
            solid
            (trailingLays comments.after indent _ ((trace ++ above) ++ [word]) next fineAfter
              (rewrite List.appendAssoc (trace ++ above) [word] (afterEvents comments.after) in
                rewrite List.appendAssoc trace above ([word] ++ afterEvents comments.after) in reached))))
