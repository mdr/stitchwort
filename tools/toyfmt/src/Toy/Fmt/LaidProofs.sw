--| Where the rules put each word: the start of the rules' half of
--| positions. `Lays` (the engine's half, `printLays`) says where a
--| document's words go from a place; here the rules' documents are taken
--| through it. A token with its comments puts down exactly `tokenEvents`
--| and leaves the line at `tokenEnd` (`tokenLays`). In a statement at a
--| column (`Zone`), a token that isn't the statement's first starts a
--| line only deeper than the statement (`tokenRule`), and a closing
--| bracket's own-line comments go at its items' column (`closerRule`).
--| Rules are triples (`Rule`: the places before, the events, the places
--| after) that go one after another (`ruleCons`, `ruleConcat`,
--| `ruleNest`). The tree's rules (an expression, a body, a file) are in
--| `EventProofs.sw`.

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

theorem filterLays ∀ (docs: List Doc) (indent: Nat) (place: Place) (trace: List Event) (next: Place → List Event → Prop)
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
theorem concatLays ∀ (docs: List Doc) (indent: Nat) (place: Place) (trace: List Event) (next: Place → List Event → Prop)
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
  | Broken at => Some at
  | Mid _ => None
  | Held at => Some (Nat.max indent (at + 2))

--| The indentation of the line a word written at `place` is on.
def wordLine (indent: Nat) (place: Place): Nat := match place with
  | AtStart at => at
  | Broken at => at
  | Mid at => at
  | Held at => Nat.max indent (at + 2)

--| A word is one event, and the line then has words on it.
theorem wordLays ∀ (indent: Nat) (text: Text) (place: Place) (trace: List Event) (next: Place → List Event → Prop)
    (solid: Solid text)
    (reached: next (Mid (wordLine indent place)) (trace ++ [{ word = text, start = wordStart indent place }])):
    WriteLays indent text place trace next :=
  match solid with
    | (filled, noGap, layout) =>
      match text.isEmpty, filled with
        | True, never => (Bool.falseNotTrue never.flipped).impossible
        | False, _ =>
          match gap: text.all (char => char == ' '), noGap, layout with
            | False, _, oneLine =>
              match place, reached with
                | AtStart at, reached => (oneLine, reached)
                | Broken at, reached => (oneLine, reached)
                | Mid at, reached => (oneLine, reached)
                | Held at, reached => (oneLine, reached)

-- A token's comments.

--| The column of the line a `LineStart` at `place` leaves the printer at
--| the start of: the line it is on if nothing is on it, else a new one, a
--| comment break.
def breakColumn (indent: Nat) (place: Place): Nat := match place with
  | AtStart at => at
  | Broken at => at
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

--| After a token, with or without a trailing comment, words are on the
--| line.
theorem trailMid ∀ (line: Nat) (after: Option Comment): (trailEnd line after).midLine = True := match after with
  | None => byComputing
  | Some _ => byComputing

theorem notesLay ∀ (comments: List Comment) (indent column: Nat) (trace: List Event) (next: Place → List Event → Prop)
    (fine: FineAbove comments) (reached: next (AtStart column) (trace ++ aboveEvents column comments)):
    LaysAll
      (comments.map (comment => Doc.concat [Doc.text comment.text, CommentEnd]))
      indent
      (AtStart column)
      trace
      next :=
  match comments, fine, reached with
    | [], _, reached => rewrite <- List.appendNil trace then reached
    | [comment, ..rest], Both first others, reached =>
      concatLays
        [Doc.text comment.text, CommentEnd]
        indent
        (AtStart column)
        trace
        (after later =>
          LaysAll (rest.map (comment => Doc.concat [Doc.text comment.text, CommentEnd])) indent after later next)
        (wordLays indent comment.text
          (AtStart column)
          trace
          (after later =>
            LaysAll [CommentEnd] indent after later (reached written =>
              LaysAll
                (rest.map (comment => Doc.concat [Doc.text comment.text, CommentEnd]))
                indent
                reached
                written
                next))
          (commentSolid comment.text first)
          ((
            byComputing,
            (notesLay rest indent column
              (trace ++ [{ word = comment.text, start = Some column }])
              next
              others
              (rewrite List.appendAssoc trace
                    [{ word = comment.text, start = Some column }]
                    (aboveEvents column rest) then
                reached))
          )))

--| The comments above a token: each on a line of its own at one column,
--| where the token then starts its line.
theorem aboveLays ∀ (above: List Comment) (indent: Nat) (place: Place)
    (trace: List Event) (next: Place → List Event → Prop)
    (fine: FineAbove above)
    (reached: next (aboveEnd indent place above) (trace ++ aboveEvents (breakColumn indent place) above)):
    Lays (commentsAbove above) indent place trace next :=
  match above, fine, reached with
    | [], _, reached => rewrite <- List.appendNil trace then reached
    | [comment, ..rest], fine, reached =>
      concatLays
        [LineStart, ..[comment, ..rest].map (comment => Doc.concat [Doc.text comment.text, CommentEnd])]
        indent
        place
        trace
        next
        (match place, reached with
          | AtStart at, reached => notesLay [comment, ..rest] indent at trace next fine reached
          | Broken at, reached => notesLay [comment, ..rest] indent at trace next fine reached
          | Mid at, reached => notesLay [comment, ..rest] indent (Nat.max indent (at + 2)) trace next fine reached
          | Held at, reached => notesLay [comment, ..rest] indent (Nat.max indent (at + 2)) trace next fine reached)

--| A trailing comment after a token is one event, and waits.
theorem trailingLays ∀ (after: Option Comment) (indent line: Nat) (trace: List Event) (next: Place → List Event → Prop)
    (fine: FineAfter after) (reached: next (trailEnd line after) (trace ++ afterEvents after)):
    Lays (trailingComment after) indent (Mid line) trace next :=
  match after, fine, reached with
    | None, _, reached => rewrite <- List.appendNil trace then reached
    | Some comment, fine, reached =>
      match commentSolid comment.text fine with
        | (_, _, layout) => (layout, reached)

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
theorem tokenLays ∀ (comments: Comments) (text: Text) (indent: Nat) (place: Place)
    (trace: List Event) (next: Place → List Event → Prop)
    (fine: Fine comments)
    (solid: Solid text)
    (reached: next (tokenEnd indent place comments) (trace ++ tokenEvents indent place comments text)):
    Lays (token comments text) indent place trace next :=
  match fine with
    | (fineAbove, fineAfter) =>
      let above := aboveEvents (breakColumn indent place) comments.above
      let word: Event := { word = text, start = wordStart indent (aboveEnd indent place comments.above) }
      concatLays
        [commentsAbove comments.above, Doc.text text, trailingComment comments.after]
        indent
        place
        trace
        next
        (aboveLays comments.above indent place trace
          (after later => LaysAll [Doc.text text, trailingComment comments.after] indent after later next)
          fineAbove
          (wordLays indent text
            (aboveEnd indent place comments.above)
            (trace ++ above)
            (after later => LaysAll [trailingComment comments.after] indent after later next)
            solid
            (trailingLays comments.after indent _
              ((trace ++ above) ++ [word])
              next
              fineAfter
              (rewrite List.appendAssoc (trace ++ above) [word] (afterEvents comments.after) then
                rewrite List.appendAssoc trace above ([word] ++ afterEvents comments.after) then reached))))

-- Zones: where the parser's layout rule lets a token start a line.

--| Where the tokens being printed stand for the parser, in a statement
--| at `column`: inside brackets, where a token may start any line, or
--| outside them, where a token that starts a line must be deeper than
--| the statement. Either way no line is shallower than the statement.
type Zone = | Anywhere (column: Nat) | Deeper (column: Nat)

--| Whether a token of the zone may start as `start` says: `Layout.allows`
--| of a token that isn't the statement's first, said of an event.
def Zone.allows (zone: Zone) (start: Option Nat): Prop := match zone with
  | Anywhere _ => True
  | Deeper column =>
    match start with
      | None => True
      | Some at => column < at

--| An indentation no shallower than the zone's statement.
def Zone.holds (zone: Zone) (indent: Nat): Prop := match zone with
  | Anywhere column => column ≤ indent
  | Deeper column => column ≤ indent

--| An indentation a line of the zone's tokens may start at: deeper than
--| the statement, or at its column too inside brackets.
def Zone.under (zone: Zone) (indent: Nat): Prop := match zone with
  | Anywhere column => column ≤ indent
  | Deeper column => column < indent

--| A place where a token of the zone that isn't its statement's first
--| may be written: the line is indented no less than the statement, and
--| deeper if nothing is on it yet.
def Inner (zone: Zone) (place: Place): Prop := match place with
  | AtStart at => zone.under at
  | Broken _ => False
  | Mid at => zone.holds at
  | Held at => zone.holds at

--| A place after a token of the zone: words on the line, which is
--| indented no less than the statement.
def Ended (zone: Zone) (place: Place): Prop := match place with
  | AtStart _ => False
  | Broken _ => False
  | Mid at => zone.holds at
  | Held at => zone.holds at

theorem endedInner ∀ (zone: Zone) (place: Place) (ended: Ended zone place): Inner zone place := match place, ended with
  | Mid at, ended => ended
  | Held at, ended => ended

--| A token's events: its own-line comments at one column, the token
--| starting where `allowed` lets it, its trailing comment.
def TokenAt (allowed: Option Nat → Prop) (comments: Comments) (text: Text) (events: List Event): Prop :=
  ∃ (column: Nat) => ∃ (start: Option Nat) => allowed start
    ∧ events = aboveEvents column comments.above ++ [{ word = text, start }, ..afterEvents comments.after]

--| A token at an inner place starts where the zone allows, whether or
--| not comments above it start its line.
theorem innerStart ∀ (zone: Zone) (indent: Nat) (place: Place) (above: List Comment) (within: zone.holds indent)
    (inner: Inner zone place):
    zone.allows (wordStart indent (aboveEnd indent place above)) :=
  match zone, within, inner with
    | Anywhere column, _, _ => byComputing
    | Deeper column, within, inner =>
      match above, place, inner with
        | [], AtStart at, inner => inner
        | [], Mid at, _ => byComputing
        | [], Held at, inner => arithmetic
        | [comment, ..rest], AtStart at, inner => inner
        | [comment, ..rest], Mid at, inner => arithmetic
        | [comment, ..rest], Held at, inner => arithmetic

--| The line a token at an inner place is on is indented within the zone.
theorem innerLine ∀ (zone: Zone) (indent: Nat) (place: Place) (above: List Comment) (within: zone.holds indent)
    (inner: Inner zone place):
    zone.holds (wordLine indent (aboveEnd indent place above)) :=
  match zone, within, inner with
    | Anywhere column, within, inner =>
      match above, place, inner with
        | [], AtStart at, inner => inner
        | [], Mid at, inner => inner
        | [], Held at, inner => arithmetic
        | [comment, ..rest], AtStart at, inner => inner
        | [comment, ..rest], Mid at, inner => arithmetic
        | [comment, ..rest], Held at, inner => arithmetic
    | Deeper column, within, inner =>
      match above, place, inner with
        | [], AtStart at, inner => arithmetic
        | [], Mid at, inner => inner
        | [], Held at, inner => arithmetic
        | [comment, ..rest], AtStart at, inner => arithmetic
        | [comment, ..rest], Mid at, inner => arithmetic
        | [comment, ..rest], Held at, inner => arithmetic

theorem trailEnded ∀ (zone: Zone) (line: Nat) (after: Option Comment) (within: zone.holds line):
    Ended zone (trailEnd line after) :=
  match after with
    | None => within
    | Some _ => within

-- Rules as triples.

--| Events that are `first`'s and then `second`'s.
def Then (first second: List Event → Prop) (events: List Event): Prop :=
  ∃ (front: List Event) => ∃ (back: List Event) => events = front ++ back ∧ first front ∧ second back

--| No events.
def Done (events: List Event): Prop := events = []

--| In a construct whose indentation `within` holds of, from any place
--| `pre` holds of, every way `doc` may print puts down events `spec`
--| holds of and leaves a place `post` holds of.
def Rule (within: Nat → Prop) (doc: Doc) (pre: Place → Prop) (spec: List Event → Prop) (post: Place → Prop): Prop :=
  ∀ (indent: Nat) (place: Place) (trace: List Event) (next: Place → List Event → Prop) => within indent
    → pre place
    → (∀ (after: Place) (events: List Event) => spec events → post after → next after (trace ++ events))
    → Lays doc indent place trace next

--| `Rule` of documents one after another.
def RuleAll (within: Nat → Prop) (docs: List Doc) (pre: Place → Prop) (spec: List Event → Prop) (post: Place → Prop):
    Prop :=
  ∀ (indent: Nat) (place: Place) (trace: List Event) (next: Place → List Event → Prop) => within indent
    → pre place
    → (∀ (after: Place) (events: List Event) => spec events → post after → next after (trace ++ events))
    → LaysAll docs indent place trace next

theorem ruleCons ∀ (within: Nat → Prop) (doc: Doc) (docs: List Doc)
    (pre middle post: Place → Prop) (first second: List Event → Prop)
    (one: Rule within doc pre first middle)
    (others: RuleAll within docs middle second post):
    RuleAll within [doc, ..docs] pre (Then first second) post :=
  indent place trace next inside holds onward =>
    one indent place trace
      (after later => LaysAll docs indent after later next)
      inside
      holds
      (between front isFirst met =>
        others indent between (trace ++ front) next inside met (after back isSecond reached =>
          rewrite List.appendAssoc trace front back then
            onward after (front ++ back) ((front, back, byComputing, isFirst, isSecond)) reached))

--| `Doc.concat` is its documents one after another.
theorem ruleConcat ∀ (within: Nat → Prop) (docs: List Doc) (pre post: Place → Prop) (spec: List Event → Prop)
    (each: RuleAll within docs pre spec post):
    Rule within (Doc.concat docs) pre spec post :=
  indent place trace next inside holds onward =>
    concatLays docs indent place trace next (each indent place trace next inside holds onward)

theorem holdsDeeper ∀ (zone: Zone) (indent more: Nat) (inside: zone.holds indent): zone.under (indent + Succ more) :=
  match zone, inside with
    | Anywhere column, inside => arithmetic
    | Deeper column, inside => arithmetic

theorem underHolds ∀ (zone: Zone) (indent: Nat) (under: zone.under indent): zone.holds indent := match zone, under with
  | Anywhere column, under => under
  | Deeper column, under => arithmetic

--| What holds at any indentation of the zone holds deeper.
theorem ruleUnder ∀ (zone: Zone) (doc: Doc) (pre post: Place → Prop) (spec: List Event → Prop)
    (rule: Rule zone.holds doc pre spec post):
    Rule zone.under doc pre spec post :=
  indent place trace next inside holds onward =>
    rule indent place trace next (underHolds zone indent inside) holds onward

-- The leaves.

--| A token of the zone that isn't its statement's first: wherever it
--| starts a line, the zone allows it.
theorem tokenRule ∀ (zone: Zone) (comments: Comments) (text: Text)
    (fine: Fine comments)
    (solid: Solid text):
    Rule zone.holds (token comments text) (Inner zone) (TokenAt zone.allows comments text) (Ended zone) :=
  indent place trace next inside inner onward =>
    tokenLays comments text indent place trace next fine solid
      (onward
        (tokenEnd indent place comments)
        (tokenEvents indent place comments text)
        ((
          (breakColumn indent place),
          (wordStart indent (aboveEnd indent place comments.above)),
          (innerStart zone indent place comments.above inside inner),
          byComputing
        ))
        (trailEnded zone _ comments.after (innerLine zone indent place comments.above inside inner)))

--| A place whose line is indented no less than the zone's statement.
def Seated (zone: Zone) (place: Place): Prop := match place with
  | AtStart at => zone.holds at
  | Broken _ => False
  | Mid at => zone.holds at
  | Held at => zone.holds at

theorem endedSeated ∀ (zone: Zone) (place: Place) (ended: Ended zone place): Seated zone place :=
  match place, ended with
    | Mid at, ended => ended
    | Held at, ended => ended

--| After a token there are words on the line.
theorem endedMid ∀ (zone: Zone) (place: Place) (ended: Ended zone place): place.midLine = True :=
  match place, ended with
    | Mid at, _ => byComputing
    | Held at, _ => byComputing

-- A closing bracket.

theorem seatedLine ∀ (zone: Zone) (indent: Nat) (place: Place) (inside: zone.holds indent)
    (seated: Seated zone place):
    zone.holds (wordLine indent place) :=
  match zone, inside, seated with
    | Anywhere column, inside, seated =>
      match place, seated with
        | AtStart at, seated => seated
        | Mid at, seated => seated
        | Held at, seated => arithmetic
    | Deeper column, inside, seated =>
      match place, seated with
        | AtStart at, seated => seated
        | Mid at, seated => seated
        | Held at, seated => arithmetic

--| A start anywhere: what a token in brackets, or a closing bracket, is
--| allowed.
def anyStart (start: Option Nat): Prop := True

--| The own-line comments above a closing bracket, each on its line at
--| the items' column.
theorem closerNotes ∀ (comment: Comment) (rest: List Comment) (indent: Nat)
    (trace: List Event) (next: Place → List Event → Prop)
    (fine: FineAbove [comment, ..rest]) (reached: next (Mid indent) (trace ++ aboveEvents indent [comment, ..rest])):
    LaysAll
      (Doc.joinedWith HardLine ([comment, ..rest].map (comment => Doc.text comment.text)))
      indent
      (AtStart indent)
      trace
      next :=
  match fine with
    | (first, others) =>
      match rest, others, reached with
        | [], _, reached =>
          wordLays indent comment.text
            (AtStart indent)
            trace
            (after later => LaysAll [] indent after later next)
            (commentSolid comment.text first)
            reached
        | [second, ..more], others, reached =>
          wordLays indent comment.text
            (AtStart indent)
            trace
            (after later =>
              LaysAll
                [HardLine, ..Doc.joinedWith HardLine ([second, ..more].map (comment => Doc.text comment.text))]
                indent
                after
                later
                next)
            (commentSolid comment.text first)
            ((
              byComputing,
              (Inr
                (closerNotes second more indent
                  (trace ++ [{ word = comment.text, start = Some indent }])
                  next
                  others
                  (rewrite List.appendAssoc trace
                        [{ word = comment.text, start = Some indent }]
                        (aboveEvents indent [second, ..more]) then
                    reached)))
            ))

--| A closing bracket with its comments (`closer`): own-line comments
--| above it at the items' column, the bracket then on a line of its own;
--| wherever it starts a line, a closing bracket may.
theorem closerRule ∀ (zone: Zone) (comments: Comments) (text: Text)
    (fine: Fine comments)
    (solid: Solid text):
    Rule zone.holds (closer comments text) (Seated zone) (TokenAt anyStart comments text) (Ended zone) :=
  indent place trace next inside seated onward =>
    match comments, fine with
      | { above = [], after }, fine =>
        tokenLays
          { above = [], after }
          text
          indent
          place
          trace
          next
          fine
          solid
          (onward
            (tokenEnd indent place { above = [], after })
            (tokenEvents indent place { above = [], after } text)
            ((0, (wordStart indent place), byComputing, byComputing))
            (trailEnded zone _ after (seatedLine zone indent place inside seated)))
      | { above = [comment, ..rest], after }, (fineAbove, fineAfter) =>
        let notes := aboveEvents (indent + 2) [comment, ..rest]
        let word: Event := { word = text, start = Some indent }
        concatLays
          [
            Nest 2
              (Doc.concat [LineStartHere, joined ([comment, ..rest].map (comment => Doc.text comment.text)) HardLine]),
            HardLine,
            Doc.text text,
            trailingComment after
          ]
          indent
          place
          trace
          next
          (concatLays
            [LineStartHere, joined ([comment, ..rest].map (comment => Doc.text comment.text)) HardLine]
            (indent + 2)
            place
            trace
            (reached written => LaysAll [HardLine, Doc.text text, trailingComment after] indent reached written next)
            (concatLays
              (Doc.joinedWith HardLine ([comment, ..rest].map (comment => Doc.text comment.text)))
              (indent + 2)
              (AtStart (indent + 2))
              trace
              (reached written =>
                LaysAll [] (indent + 2) reached written (left laid =>
                  LaysAll [HardLine, Doc.text text, trailingComment after] indent left laid next))
              (closerNotes comment rest
                (indent + 2)
                trace
                (reached written =>
                  LaysAll [] (indent + 2) reached written (left laid =>
                    LaysAll [] (indent + 2) left laid (out all =>
                      LaysAll [HardLine, Doc.text text, trailingComment after] indent out all next)))
                fineAbove
                ((
                  byComputing,
                  (Inr
                    (wordLays indent text
                      (AtStart indent)
                      (trace ++ notes)
                      (reached written => LaysAll [trailingComment after] indent reached written next)
                      solid
                      (trailingLays after indent indent
                        ((trace ++ notes) ++ [word])
                        next
                        fineAfter
                        (rewrite List.appendAssoc (trace ++ notes) [word] (afterEvents after) then
                          rewrite List.appendAssoc trace notes ([word] ++ afterEvents after) then
                            onward
                              (trailEnd indent after)
                              (notes ++ [word, ..afterEvents after])
                              (((indent + 2), (Some indent), byComputing, byComputing))
                              (trailEnded zone indent after inside)))))
                )))))

-- Rules put together.

--| The last of a list.
theorem ruleLast ∀ (within: Nat → Prop) (doc: Doc) (pre post: Place → Prop) (spec: List Event → Prop)
    (rule: Rule within doc pre spec post):
    RuleAll within [doc] pre spec post :=
  indent place trace next inside holds onward =>
    rule indent place trace (after later => LaysAll [] indent after later next) inside holds onward
