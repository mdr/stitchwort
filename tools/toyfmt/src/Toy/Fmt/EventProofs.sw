--| What the rules lay for each construct of the tree: the rules' half of
--| positions, by induction over expressions, bodies and statements.
--| `Events zone head expr` is the expression's tokens in order, each
--| with its comments, the leftmost starting as `head` says and every
--| other where its place in the tree lets the parser's layout rule take
--| it: anywhere inside brackets, only deeper than the statement outside
--| them, `else` also at the statement's column, a body either on its
--| keyword's line or as lines at one deeper column, each statement's
--| first token starting a line there. `exprLays` says every way an
--| expression's layout may print puts down such events; `statementLays`
--| and `linesLay` say it of a block's lines.

namespace Toy.Fmt.Proofs
import Toy.Doc (..)
import Toy.Doc.Proofs (..)
import Toy.Syntax (..)
import Toy.Syntax.Proofs (..)
import Toy.Fmt (..)
import Std (Bool, DecEq, Eq, List, Nat, Option, Parse, Text, Void)

-- What is laid.

--| The zone inside brackets opened in a statement of `zone`.
def Zone.inside (zone: Zone): Zone := Anywhere zone.column

--| Whether `else` may start as `start` says: on its `if`'s line, or on a
--| line no shallower than the statement.
def Zone.reaches (zone: Zone) (start: Option Nat): Prop := match start with
  | None => True
  | Some at => zone.column ≤ at

--| A start of a line at `column`: a statement's first token in its block.
def atColumn (column: Nat) (start: Option Nat): Prop := start = Some column

--| How the first token of a body's one expression starts when the body
--| is printed on its keyword's line: where the zone allows, and not at a
--| line start unless comments above it put it on a comment break.
def inlineHead (zone: Zone) (value: Expr) (start: Option Nat): Prop :=
  zone.allows start ∧ (value.firstAbove = [] → start = None)

--| The events of an expression of a statement of `zone`: its tokens in
--| order, the leftmost starting as `head` says, the others where the
--| zone allows (anywhere inside brackets).
def Events (zone: Zone) (head: Option Nat → Prop) (expr: Expr): List Event → Prop := match expr with
  | Var name comments => TokenAt head comments name
  | NumberLiteral digits comments => TokenAt head comments digits
  | StringLiteral written comments => TokenAt head comments written
  | Bracketed open inner close =>
    Then (TokenAt head open "(") (Then (Events zone.inside anyStart inner) (TokenAt anyStart close ")"))
  | ListLiteral open items close =>
    Then (TokenAt head open "[") (Then (ItemEvents zone.inside items) (TokenAt anyStart close "]"))
  | Call callee open arguments close =>
    Then
      (Events zone head callee)
      (Then (TokenAt zone.allows open "(") (Then (ItemEvents zone.inside arguments) (TokenAt anyStart close ")")))
  | Field target dot name nameComments =>
    Then (Events zone head target) (Then (TokenAt zone.allows dot ".") (TokenAt zone.allows nameComments name))
  | Negate minus operand => Then (TokenAt head minus "-") (Events zone zone.allows operand)
  | Binary operator sign left right =>
    Then (Events zone head left) (Then (TokenAt zone.allows sign operator.spelling) (Events zone zone.allows right))
  | If ifComments condition thenComments whenTrue elseComments whenFalse =>
    Then
      (TokenAt head ifComments "if")
      (Then
        (Events zone zone.allows condition)
        (Then
          (TokenAt zone.allows thenComments "then")
          (Then
            (BodyEvents zone whenTrue)
            (Then (TokenAt zone.reaches elseComments "else") (BodyEvents zone whenFalse)))))

--| The events of the items between brackets (`zone` is the zone inside
--| them): each value, and the comma after each but the last.
def ItemEvents (zone: Zone) (items: List Expr): List Event → Prop := match items with
  | [] => Done
  | [value] => Events zone anyStart value
  | [value, ..rest] =>
    Then (Events zone anyStart value) (Then (TokenAt anyStart Comments.none ",") (ItemEvents zone rest))

--| The events of a body after its keyword or `=`: its one expression on
--| that line (`InlineEvents`), or its statements as lines at one column
--| that a line of the zone may start at.
def BodyEvents (zone: Zone) (body: Body): List Event → Prop := match body with
  | { statements } => events =>
    InlineEvents zone statements events ∨ (∃ (column: Nat) => zone.under column ∧ LineEvents column statements events)

--| A body of one expression, printed on its keyword's line.
def InlineEvents (zone: Zone) (statements: List (Spaced Statement)): List Event → Prop := match statements with
  | [{ line = Bare value, .. }] => Events zone (inlineHead zone value) value
  | _ => events => False

--| The lines of a block at `column`, one statement after another, with
--| the blank lines kept between them (none before the first).
def LineEvents (column: Nat) (statements: List (Spaced Statement)): List Event → Prop := match statements with
  | [] => Done
  | [{ line, .. }, ..rest] => Then (StatementEvents column line) (LaterLines column rest)

--| The blank line kept before a line that isn't its list's first.
def blankEvents (blankBefore: Bool): List Event := if blankBefore then [Event.blankLine] else []

--| The lines of a block after its first: each after a blank line if it
--| has one before it.
def LaterLines (column: Nat) (statements: List (Spaced Statement)): List Event → Prop := match statements with
  | [] => Done
  | [{ blankBefore, line }, ..rest] => events =>
    ∃ (later: List Event) => events = blankEvents blankBefore ++ later
      ∧ Then (StatementEvents column line) (LaterLines column rest) later

--| A statement of a block at `column`: its first token starts a line at
--| the column, the others stand in the statement; a comment line is one
--| event at the column.
def StatementEvents (column: Nat) (statement: Statement): List Event → Prop := match statement with
  | Let letComments name nameComments equals body =>
    Then
      (TokenAt (atColumn column) letComments "let")
      (Then
        (TokenAt (Deeper column).allows nameComments name)
        (Then (TokenAt (Deeper column).allows equals "=") (BodyEvents (Deeper column) body)))
  | Bare value => Events (Deeper column) (atColumn column) value
  | StatementNote comment => events => events = [{ word = comment.text, start = Some column }]

-- Zones and places.

theorem insideHolds ∀ (zone: Zone) (indent: Nat) (inside: zone.holds indent): zone.inside.holds indent :=
  match zone, inside with
    | Anywhere column, inside => inside
    | Deeper column, inside => inside

theorem insideSeated ∀ (zone: Zone) (place: Place) (seated: Seated zone place): Seated zone.inside place :=
  match zone, place, seated with
    | Anywhere column, AtStart at, seated => seated
    | Anywhere column, Mid at, seated => seated
    | Anywhere column, Held at, seated => seated
    | Deeper column, AtStart at, seated => seated
    | Deeper column, Mid at, seated => seated
    | Deeper column, Held at, seated => seated

theorem insideEnded ∀ (zone: Zone) (place: Place) (ended: Ended zone.inside place): Ended zone place :=
  match zone, place, ended with
    | Anywhere column, Mid at, ended => ended
    | Anywhere column, Held at, ended => ended
    | Deeper column, Mid at, ended => ended
    | Deeper column, Held at, ended => ended

theorem holdsMore ∀ (zone: Zone) (indent more: Nat) (inside: zone.holds indent): zone.holds (indent + more) :=
  match zone, inside with
    | Anywhere column, inside => arithmetic
    | Deeper column, inside => arithmetic

theorem ownHolds ∀ (column: Nat): Zone.holds (Deeper column) column := arithmetic

--| After the lines of a block at a column of the zone, the line is no
--| shallower than the zone's statement.
theorem endedUp ∀ (zone: Zone) (column: Nat) (place: Place) (under: zone.under column)
    (ended: Ended (Deeper column) place):
    Ended zone place :=
  match zone, place, under, ended with
    | Anywhere outer, Mid at, under, ended => arithmetic
    | Anywhere outer, Held at, under, ended => arithmetic
    | Deeper outer, Mid at, under, ended => arithmetic
    | Deeper outer, Held at, under, ended => arithmetic

theorem allowsNone ∀ (zone: Zone): zone.allows None := match zone with
  | Anywhere column => byComputing
  | Deeper column => byComputing

--| The line a construct's leftmost token is on is no shallower than the
--| statement, wherever comments above it put it.
theorem seatedHead ∀ (zone: Zone) (indent: Nat) (place: Place) (above: List Comment) (inside: zone.holds indent)
    (seated: Seated zone place):
    zone.holds (wordLine indent (aboveEnd indent place above)) :=
  match zone, above, place, inside, seated with
    | Anywhere column, [], AtStart at, inside, seated => seated
    | Anywhere column, [], Mid at, inside, seated => seated
    | Anywhere column, [], Held at, inside, seated => arithmetic
    | Anywhere column, [comment, ..rest], AtStart at, inside, seated => seated
    | Anywhere column, [comment, ..rest], Mid at, inside, seated => arithmetic
    | Anywhere column, [comment, ..rest], Held at, inside, seated => arithmetic
    | Deeper column, [], AtStart at, inside, seated => seated
    | Deeper column, [], Mid at, inside, seated => seated
    | Deeper column, [], Held at, inside, seated => arithmetic
    | Deeper column, [comment, ..rest], AtStart at, inside, seated => seated
    | Deeper column, [comment, ..rest], Mid at, inside, seated => arithmetic
    | Deeper column, [comment, ..rest], Held at, inside, seated => arithmetic

--| A token written from a place no shallower than the statement starts
--| a line, if it does, no shallower than the statement: what `else` needs.
theorem seatedReach ∀ (zone: Zone) (indent: Nat) (place: Place) (above: List Comment) (inside: zone.holds indent)
    (seated: Seated zone place):
    zone.reaches (wordStart indent (aboveEnd indent place above)) :=
  match zone, above, place, inside, seated with
    | Anywhere column, [], AtStart at, inside, seated => seated
    | Anywhere column, [], Mid at, inside, seated => byComputing
    | Anywhere column, [], Held at, inside, seated => arithmetic
    | Anywhere column, [comment, ..rest], AtStart at, inside, seated => seated
    | Anywhere column, [comment, ..rest], Mid at, inside, seated => arithmetic
    | Anywhere column, [comment, ..rest], Held at, inside, seated => arithmetic
    | Deeper column, [], AtStart at, inside, seated => seated
    | Deeper column, [], Mid at, inside, seated => byComputing
    | Deeper column, [], Held at, inside, seated => arithmetic
    | Deeper column, [comment, ..rest], AtStart at, inside, seated => seated
    | Deeper column, [comment, ..rest], Mid at, inside, seated => arithmetic
    | Deeper column, [comment, ..rest], Held at, inside, seated => arithmetic

--| At the start of a line, a token starts that line, with or without
--| comments above it.
theorem startAt ∀ (indent at: Nat) (above: List Comment):
    atColumn at (wordStart indent (aboveEnd indent (AtStart at) above)) :=
  match above with
    | [] => byComputing
    | [comment, ..rest] => byComputing

theorem commentsNotNil ∀ (first: Comment) (rest: List Comment) (wrong: [first, ..rest] = []): Void := cases

--| After words on a line, a body's first token is on that line unless
--| comments above it put it on a comment break, deeper than the line.
theorem inlineStart ∀ (zone: Zone) (indent line: Nat) (above: List Comment)
    (inside: zone.holds indent) (onLine: zone.holds line):
    zone.allows (wordStart indent (aboveEnd indent (Mid line) above))
      ∧ (above = [] → wordStart indent (aboveEnd indent (Mid line) above) = None) :=
  match above with
    | [] => ((allowsNone zone), (same => byComputing))
    | [comment, ..rest] => (
      (innerStart zone indent (Mid line) [comment, ..rest] inside onLine),
      (never => Void.impossible (commentsNotNil comment rest never))
    )

-- Events one after another.

theorem thenAssoc ∀ (first second third: List Event → Prop) (front back: List Event)
    (both: Then first second front) (isThird: third back):
    Then first (Then second third) (front ++ back) :=
  match both with
    | (begun, ended, split, isFirst, isSecond) => (
      begun,
      (ended ++ back),
      (rewrite split then List.appendAssoc begun ended back),
      isFirst,
      ended,
      back,
      byComputing,
      isSecond,
      isThird
    )

theorem thenDone ∀ (spec: List Event → Prop) (events: List Event) (holds: spec events): Then spec Done events :=
  (events, [], (List.appendNil events).flipped, holds, byComputing)

theorem doneThen ∀ (spec: List Event → Prop) (events: List Event) (holds: spec events): Then Done spec events :=
  ([], events, byComputing, byComputing, holds)

-- Rules whose leftmost token is the construct's.

--| As `Rule`, for a document whose leftmost token (with the comments
--| `above` it) is printed at the construct's own indentation: from any
--| place no shallower than the statement, whatever holds of where that
--| token starts there is what `spec` is told of it.
def HeadRule (zone: Zone) (doc: Doc) (above: List Comment) (spec: (Option Nat → Prop) → List Event → Prop): Prop :=
  ∀ (head: Option Nat → Prop) (indent: Nat) (place: Place) (trace: List Event) (next: Place
    → List Event
    → Prop) => zone.holds indent
    → Seated zone place
    → head (wordStart indent (aboveEnd indent place above))
    → (∀ (after: Place) (events: List Event) => spec head events → Ended zone after → next after (trace ++ events))
    → Lays doc indent place trace next

theorem tokenHead ∀ (zone: Zone) (comments: Comments) (text: Text)
    (fine: Fine comments)
    (solid: Solid text):
    HeadRule zone (token comments text) comments.above (head => TokenAt head comments text) :=
  head indent place trace next inside seated isHead onward =>
    tokenLays comments text indent place trace next fine solid
      (onward
        (tokenEnd indent place comments)
        (tokenEvents indent place comments text)
        (((breakColumn indent place), (wordStart indent (aboveEnd indent place comments.above)), isHead, byComputing))
        (trailEnded zone _ comments.after (seatedHead zone indent place comments.above inside seated)))

--| A construct's first document, then the rest of it.
theorem headCons ∀ (zone: Zone) (doc: Doc) (docs: List Doc) (above: List Comment)
    (first: (Option Nat → Prop) → List Event → Prop) (second: List Event → Prop)
    (one: HeadRule zone doc above first)
    (others: RuleAll zone.holds docs (Ended zone) second (Ended zone)):
    HeadRule zone (Doc.concat [doc, ..docs]) above (head => Then (first head) second) :=
  head indent place trace next inside seated isHead onward =>
    concatLays
      [doc, ..docs]
      indent
      place
      trace
      next
      (one head indent place trace
        (after later => LaysAll docs indent after later next)
        inside
        seated
        isHead
        (between front isFirst met =>
          others indent between (trace ++ front) next inside met (after back isSecond reached =>
            rewrite List.appendAssoc trace front back then
              onward after (front ++ back) ((front, back, byComputing, isFirst, isSecond)) reached)))

--| A construct that isn't its statement's first: its leftmost token
--| starts where the zone allows.
theorem headInner ∀ (zone: Zone) (doc: Doc) (above: List Comment) (spec: (Option Nat → Prop) → List Event → Prop)
    (rule: HeadRule zone doc above spec):
    Rule zone.holds doc (Ended zone) (spec zone.allows) (Ended zone) :=
  indent place trace next inside ended onward =>
    rule zone.allows indent place trace next inside
      (endedSeated zone place ended)
      (innerStart zone indent place above inside (endedInner zone place ended))
      onward

--| A construct inside brackets: its leftmost token may start any line.
theorem headInside ∀ (zone: Zone) (doc: Doc) (above: List Comment) (spec: (Option Nat → Prop) → List Event → Prop)
    (rule: HeadRule zone.inside doc above spec):
    Rule zone.holds doc (Seated zone) (spec anyStart) (Ended zone) :=
  indent place trace next inside seated onward =>
    rule anyStart indent place trace next
      (insideHolds zone indent inside)
      (insideSeated zone place seated)
      byComputing
      (after events isSpec ended => onward after events isSpec (insideEnded zone after ended))

theorem fromEnded ∀ (zone: Zone) (within: Nat → Prop) (doc: Doc) (spec: List Event → Prop) (post: Place → Prop)
    (rule: Rule within doc (Seated zone) spec post):
    Rule within doc (Ended zone) spec post :=
  indent place trace next inside ended onward =>
    rule indent place trace next inside (endedSeated zone place ended) onward

--| A token after another of its statement.
theorem tokenAfter ∀ (zone: Zone) (comments: Comments) (text: Text)
    (fine: Fine comments)
    (solid: Solid text):
    Rule zone.holds (token comments text) (Ended zone) (TokenAt zone.allows comments text) (Ended zone) :=
  indent place trace next inside ended onward =>
    tokenRule zone comments text fine solid indent place trace next inside (endedInner zone place ended) onward

-- What comes between tokens and puts down no event.

theorem spaceAll ∀ (zone: Zone) (within: Nat → Prop) (docs: List Doc) (spec: List Event → Prop) (post: Place → Prop)
    (rest: RuleAll within docs (Ended zone) spec post):
    RuleAll within [Doc.text " ", ..docs] (Ended zone) spec post :=
  indent place trace next inside ended onward =>
    match place, ended with
      | Mid at, ended => rest indent (Mid at) trace next inside ended onward
      | Held at, ended => rest indent (Held at) trace next inside ended onward

--| The space `Negate` puts before an operand that starts with `-`.
theorem gapAll ∀ (zone: Zone) (within: Nat → Prop) (gap: Bool) (docs: List Doc)
    (spec: List Event → Prop) (post: Place → Prop)
    (rest: RuleAll within docs (Ended zone) spec post):
    RuleAll within [Doc.text (if gap then " " else ""), ..docs] (Ended zone) spec post :=
  match gap with
    | True => spaceAll zone within docs spec post rest
    | False => indent place trace next inside ended onward => rest indent place trace next inside ended onward

--| A `Line` or a fill's separator after a token, at an indentation no
--| shallower than the statement.
theorem sepSeats ∀ (zone: Zone) (indent: Nat) (place: Place) (trace: List Event)
    (next: Place → List Event → Prop) (inside: zone.holds indent)
    (ended: Ended zone place) (reached: ∀ (middle: Place) => Seated zone middle → next middle trace):
    SepLays indent place trace next :=
  match place, ended with
    | Mid at, ended => ((reached (Mid at) ended), (reached (AtStart indent) inside))
    | Held at, ended => reached (AtStart indent) inside

theorem softSeats ∀ (zone: Zone) (indent: Nat) (place: Place) (trace: List Event)
    (next: Place → List Event → Prop) (inside: zone.holds indent)
    (seated: Ended zone place) (reached: ∀ (middle: Place) => Seated zone middle → next middle trace):
    SoftLays indent place trace next :=
  match place, seated with
    | Mid at, seated => ((reached (Mid at) seated), (reached (AtStart indent) inside))
    | Held at, seated => reached (AtStart indent) inside

--| A `Line` before a token that may start a line at the statement's
--| column: `else`.
theorem lineSeatsAll ∀ (zone: Zone) (docs: List Doc) (spec: List Event → Prop) (post: Place → Prop)
    (rest: RuleAll zone.holds docs (Seated zone) spec post):
    RuleAll zone.holds [Line, ..docs] (Ended zone) spec post :=
  indent place trace next inside ended onward =>
    sepSeats zone indent place trace
      (after later => LaysAll docs indent after later next)
      inside
      ended
      (middle seated => rest indent middle trace next inside seated onward)

--| A `Line` in a nest of the statement, before a token of it.
theorem lineAll ∀ (zone: Zone) (docs: List Doc) (spec: List Event → Prop) (post: Place → Prop)
    (rest: RuleAll zone.under docs (Inner zone) spec post):
    RuleAll zone.under [Line, ..docs] (Ended zone) spec post :=
  indent place trace next inside ended onward =>
    match place, ended with
      | Mid at, ended => (
        (rest indent (Mid at) trace next inside ended onward),
        (rest indent (AtStart indent) trace next inside inside onward)
      )
      | Held at, ended => rest indent (AtStart indent) trace next inside inside onward

--| A `,` or closing bracket after an expression: on the line below if
--| the expression ends in a trailing comment.
theorem closeAfterRule ∀ (zone: Zone) (expr: Expr) (doc: Doc) (spec: List Event → Prop)
    (rule: Rule zone.holds doc (Seated zone) spec (Ended zone)):
    Rule zone.holds (closeAfter expr doc) (Ended zone) spec (Ended zone) :=
  indent place trace next inside ended onward =>
    match expr.endsWithComment with
      | True =>
        concatLays
          [HardLine, doc]
          indent
          place
          trace
          next
          ((
            (endedMid zone place ended),
            (Inr
              (rule indent
                (AtStart indent)
                trace
                (after later => LaysAll [] indent after later next)
                inside
                inside
                onward))
          ))
      | False => rule indent place trace next inside (endedSeated zone place ended) onward

-- A fill and a list joined by `Line` lay alike.

theorem joinedStep ∀ (doc: Doc) (rest: List Doc) (indent: Nat) (place: Place)
    (trace: List Event) (next: Place → List Event → Prop)
    (others: ∀ (middle: Place) (between: List Event) => FillLays rest indent middle between next
      → LaysAll (Doc.joinedWith Line rest) indent middle between next)
    (fill: FillLays [doc, ..rest] indent place trace next):
    LaysAll (Doc.joinedWith Line [doc, ..rest]) indent place trace next :=
  match rest, others, fill with
    | [], _, fill => fill
    | [second, ..more], others, fill =>
      laysWeaker doc indent place trace
        (after later => SepsLay [second, ..more] indent after later next)
        (after later => LaysAll [Line, ..Doc.joinedWith Line [second, ..more]] indent after later next)
        (after later seps =>
          sepLaysWeaker indent after later
            (middle between =>
              Lays second indent middle between (reached written => SepsLay more indent reached written next))
            (middle between => LaysAll (Doc.joinedWith Line [second, ..more]) indent middle between next)
            (middle between lays => others middle between lays)
            seps)
        fill

theorem joinedFill ∀ (docs: List Doc) (indent: Nat) (place: Place) (trace: List Event) (next: Place → List Event → Prop)
    (fill: FillLays docs indent place trace next):
    LaysAll (Doc.joinedWith Line docs) indent place trace next :=
  match docs, fill with
    | [], fill => fill
    | [doc, ..rest], fill =>
      joinedStep doc rest indent place trace next
        (middle between lays => joinedFill rest indent middle between next lays)
        fill

-- Token texts.

theorem nameSolid ∀ (text: Text) (name: IsName text): Solid text := match name with
  | (word, _) =>
    match wordToken text word with
      | (solid, _) => solid

theorem digitsSolid ∀ (text: Text) (number: IsDigits text): Solid text := match digitsToken text number with
  | (solid, _) => solid

theorem stringSolid ∀ (text: Text) (string: IsString text): Solid text := match stringToken text string with
  | (solid, _) => solid

theorem operatorSolid ∀ (operator: Operator): Solid operator.spelling := match operatorToken operator with
  | (solid, _) => solid

theorem solidOpenParen: Solid "(" := (byComputing, byComputing, byComputing)

theorem solidCloseParen: Solid ")" := (byComputing, byComputing, byComputing)

theorem solidOpenSquare: Solid "[" := (byComputing, byComputing, byComputing)

theorem solidCloseSquare: Solid "]" := (byComputing, byComputing, byComputing)

theorem solidComma: Solid "," := (byComputing, byComputing, byComputing)

theorem solidDot: Solid "." := (byComputing, byComputing, byComputing)

theorem solidMinus: Solid "-" := (byComputing, byComputing, byComputing)

theorem solidEquals: Solid "=" := (byComputing, byComputing, byComputing)

theorem solidIf: Solid "if" := (byComputing, byComputing, byComputing)

theorem solidThen: Solid "then" := (byComputing, byComputing, byComputing)

theorem solidElse: Solid "else" := (byComputing, byComputing, byComputing)

theorem solidLet: Solid "let" := (byComputing, byComputing, byComputing)

-- Items between brackets.

--| As `RuleAll`, of a fill's items: from any place no shallower than the
--| statement.
def FillRule (zone: Zone) (docs: List Doc) (spec: List Event → Prop): Prop :=
  ∀ (indent: Nat) (place: Place) (trace: List Event) (next: Place → List Event → Prop) => zone.holds indent
    → Seated zone place
    → (∀ (after: Place) (events: List Event) => spec events → Ended zone after → next after (trace ++ events))
    → FillLays docs indent place trace next

--| A list's items (P5): filled, two deeper.
theorem nestFill ∀ (zone: Zone) (docs: List Doc) (spec: List Event → Prop)
    (fill: FillRule zone docs spec):
    Rule zone.holds (Nest 2 (Fill docs)) (Ended zone) spec (Ended zone) :=
  indent place trace next inside ended onward =>
    fill (indent + 2) place trace next (holdsMore zone indent 2 inside) (endedSeated zone place ended) onward

--| A call's arguments (P4) or a declaration's parameters (P2): on the
--| line, or one a line deeper.
theorem nestJoined ∀ (zone: Zone) (more: Nat) (docs: List Doc) (spec: List Event → Prop)
    (fill: FillRule zone docs spec):
    Rule zone.holds (Nest more (Doc.concat [SoftLine, joined docs Line])) (Ended zone) spec (Ended zone) :=
  indent place trace next inside ended onward =>
    concatLays
      [SoftLine, joined docs Line]
      (indent + more)
      place
      trace
      next
      (softSeats zone
        (indent + more)
        place
        trace
        (after later => LaysAll [joined docs Line] (indent + more) after later next)
        (holdsMore zone indent more inside)
        ended
        (middle seated =>
          concatLays
            (Doc.joinedWith Line docs)
            (indent + more)
            middle
            trace
            (after later => LaysAll [] (indent + more) after later next)
            (joinedFill docs
              (indent + more)
              middle
              trace
              (after later => LaysAll [] (indent + more) after later next)
              (fill
                (indent + more)
                middle
                trace
                (after later => LaysAll [] (indent + more) after later next)
                (holdsMore zone indent more inside)
                seated
                onward))))

--| A closing bracket after a `SoftLine`: on the items' line or on its own.
theorem softCloser ∀ (zone: Zone) (comments: Comments) (text: Text)
    (fine: Fine comments)
    (solid: Solid text):
    RuleAll zone.holds [SoftLine, closer comments text] (Ended zone) (TokenAt anyStart comments text) (Ended zone) :=
  indent place trace next inside ended onward =>
    softSeats zone indent place trace
      (after later => LaysAll [closer comments text] indent after later next)
      inside
      ended
      (middle seated =>
        closerRule zone comments text fine solid indent middle trace
          (after later => LaysAll [] indent after later next)
          inside
          seated
          onward)

--| A closing bracket right after its opening one.
theorem emptyCloser ∀ (zone: Zone) (comments: Comments) (text: Text)
    (fine: Fine comments)
    (solid: Solid text):
    RuleAll zone.holds [closer comments text] (Ended zone) (Then Done (TokenAt anyStart comments text)) (Ended zone) :=
  indent place trace next inside ended onward =>
    closerRule zone comments text fine solid indent place trace
      (after later => LaysAll [] indent after later next)
      inside
      (endedSeated zone place ended)
      (after events isToken reached =>
        onward after events (doneThen (TokenAt anyStart comments text) events isToken) reached)

-- Operator chains.

--| A chain's parts: the first at the chain's indentation, the links two
--| deeper.
def ChainLays (parts: List Doc) (indent: Nat) (place: Place) (trace: List Event) (next: Place → List Event → Prop):
    Prop :=
  match parts with
    | [] => False
    | [first, ..links] => Lays first indent place trace (after later => LaysAll links (indent + 2) after later next)

theorem chainCast ∀ (parts other: List Doc) (indent: Nat) (place: Place)
    (trace: List Event) (next: Place → List Event → Prop)
    (same: parts = other)
    (lays: ChainLays parts indent place trace next):
    ChainLays other indent place trace next :=
  rewrite <- same then lays

theorem chainLaid ∀ (parts: List Doc) (first: Doc) (links: List Doc) (indent: Nat) (place: Place)
    (trace: List Event) (next: Place → List Event → Prop)
    (found: parts = [first, ..links])
    (lays: ChainLays parts indent place trace next):
    Lays (Doc.group (Doc.concat [first, Nest 2 (Doc.concat links)])) indent place trace next :=
  let whole := chainCast parts [first, ..links] indent place trace next found lays
  concatLays
    [first, Nest 2 (Doc.concat links)]
    indent
    place
    trace
    next
    (laysWeaker first indent place trace
      (after later => LaysAll links (indent + 2) after later next)
      (after later => LaysAll [Nest 2 (Doc.concat links)] indent after later next)
      (after later all =>
        concatLays links
          (indent + 2)
          after
          later
          (reached written => LaysAll [] indent reached written next)
          (allLaysWeaker links
            (indent + 2)
            after
            later
            next
            (reached written => LaysAll [] indent reached written next)
            (reached written same => same)
            all))
      whole)

--| A link of a chain (P6): its operator after a `Line`, a space, its
--| operand.
theorem linkRule ∀ (zone: Zone) (operator: Operator) (sign: Comments) (right: Expr)
    (fineSign: Fine sign)
    (rightRule: HeadRule zone right.layout right.firstAbove (head => Events zone head right)):
    Rule zone.under
      (link operator sign right.layout)
      (Ended zone)
      (Then (TokenAt zone.allows sign operator.spelling) (Events zone zone.allows right))
      (Ended zone) :=
  ruleConcat zone.under
    [Line, token sign operator.spelling, Doc.text " ", right.layout]
    (Ended zone)
    (Ended zone)
    (Then (TokenAt zone.allows sign operator.spelling) (Events zone zone.allows right))
    (lineAll zone
      [token sign operator.spelling, Doc.text " ", right.layout]
      (Then (TokenAt zone.allows sign operator.spelling) (Events zone zone.allows right))
      (Ended zone)
      (ruleCons zone.under
        (token sign operator.spelling)
        [Doc.text " ", right.layout]
        (Inner zone)
        (Ended zone)
        (Ended zone)
        (TokenAt zone.allows sign operator.spelling)
        (Events zone zone.allows right)
        (ruleUnder zone _
          (Inner zone)
          (Ended zone) _
          (tokenRule zone sign operator.spelling fineSign (operatorSolid operator)))
        (spaceAll zone zone.under
          [right.layout]
          (Events zone zone.allows right)
          (Ended zone)
          (ruleLast zone.under right.layout
            (Ended zone)
            (Ended zone)
            (Events zone zone.allows right)
            (ruleUnder zone right.layout
              (Ended zone)
              (Ended zone)
              (Events zone zone.allows right)
              (headInner zone right.layout right.firstAbove (head => Events zone head right) rightRule))))))

-- A keyword and its body.

--| A keyword's token may be written from any place of `pre`, and starts
--| there as `allowed` says.
def KeyStarts (zone: Zone) (above: List Comment) (pre: Place → Prop) (allowed: Option Nat → Prop): Prop :=
  ∀ (indent: Nat) (place: Place) => zone.holds indent
    → pre place
    → Seated zone place ∧ allowed (wordStart indent (aboveEnd indent place above))

theorem endedStarts ∀ (zone: Zone) (above: List Comment): KeyStarts zone above (Ended zone) zone.allows :=
  indent place inside ended =>
    ((endedSeated zone place ended), (innerStart zone indent place above inside (endedInner zone place ended)))

theorem seatedStarts ∀ (zone: Zone) (above: List Comment): KeyStarts zone above (Seated zone) zone.reaches :=
  indent place inside seated => (seated, (seatedReach zone indent place above inside seated))

--| The document of a body lays the body's events, from right after its
--| keyword (`then`, `else` or `=`) with the keyword's trailing comment
--| `after` waiting if there is one.
def BodyRule (zone: Zone) (bodyDoc: Doc) (after: Option Comment) (body: Body): Prop :=
  ∀ (indent line: Nat) (trace: List Event) (next: Place → List Event → Prop) => zone.holds indent
    → zone.holds line
    → (∀ (reached: Place) (events: List Event) => BodyEvents zone body events
      → Ended zone reached
      → next reached (trace ++ events))
    → Lays bodyDoc indent (trailEnd line after) trace next

--| A keyword, its body, and what follows.
theorem keyCons ∀ (zone: Zone) (keyword: Comments) (text: Text) (bodyDoc: Doc) (body: Body) (allowed: Option Nat → Prop)
    (pre: Place → Prop) (docs: List Doc) (spec: List Event → Prop) (post: Place → Prop)
    (fine: Fine keyword)
    (solid: Solid text)
    (starts: KeyStarts zone keyword.above pre allowed)
    (bodyRule: BodyRule zone bodyDoc keyword.after body)
    (others: RuleAll zone.holds docs (Ended zone) spec post):
    RuleAll zone.holds
      [token keyword text, bodyDoc, ..docs]
      pre
      (Then (TokenAt allowed keyword text) (Then (BodyEvents zone body) spec))
      post :=
  indent place trace next inside holds onward =>
    match starts indent place inside holds with
      | (seated, isAllowed) =>
        let written := tokenEvents indent place keyword text
        tokenLays keyword text indent place trace
          (after later => LaysAll [bodyDoc, ..docs] indent after later next)
          fine
          solid
          (bodyRule indent
            (wordLine indent (aboveEnd indent place keyword.above))
            (trace ++ written)
            (after later => LaysAll docs indent after later next)
            inside
            (seatedHead zone indent place keyword.above inside seated)
            (reached events isBody ended =>
              others indent reached ((trace ++ written) ++ events) next inside ended (last rest isRest met =>
                rewrite List.appendAssoc (trace ++ written) events rest,
                    List.appendAssoc trace written (events ++ rest) then
                  onward last
                    (written ++ (events ++ rest))
                    ((
                      written,
                      (events ++ rest),
                      byComputing,
                      ((
                        (breakColumn indent place),
                        (wordStart indent (aboveEnd indent place keyword.above)),
                        isAllowed,
                        byComputing
                      )),
                      events,
                      rest,
                      byComputing,
                      isBody,
                      isRest
                    ))
                    met)))

--| A keyword and its body, the last of their construct.
theorem keyLast ∀ (zone: Zone) (keyword: Comments) (text: Text) (bodyDoc: Doc) (body: Body)
    (allowed: Option Nat → Prop) (pre: Place → Prop)
    (fine: Fine keyword)
    (solid: Solid text)
    (starts: KeyStarts zone keyword.above pre allowed)
    (bodyRule: BodyRule zone bodyDoc keyword.after body):
    RuleAll zone.holds
      [token keyword text, bodyDoc]
      pre
      (Then (TokenAt allowed keyword text) (BodyEvents zone body))
      (Ended zone) :=
  indent place trace next inside holds onward =>
    match starts indent place inside holds with
      | (seated, isAllowed) =>
        let written := tokenEvents indent place keyword text
        tokenLays keyword text indent place trace
          (after later => LaysAll [bodyDoc] indent after later next)
          fine
          solid
          (bodyRule indent
            (wordLine indent (aboveEnd indent place keyword.above))
            (trace ++ written)
            (after later => LaysAll [] indent after later next)
            inside
            (seatedHead zone indent place keyword.above inside seated)
            (reached events isBody ended =>
              rewrite List.appendAssoc trace written events then
                onward reached
                  (written ++ events)
                  ((
                    written,
                    events,
                    byComputing,
                    ((
                      (breakColumn indent place),
                      (wordStart indent (aboveEnd indent place keyword.above)),
                      isAllowed,
                      byComputing
                    )),
                    isBody
                  ))
                  ended))

--| A body's one expression on its keyword's line, after a space.
theorem inlineLays ∀ (zone: Zone) (value: Expr)
    (rule: HeadRule zone value.layout value.firstAbove (head => Events zone head value))
    (indent line: Nat) (trace: List Event) (next: Place → List Event → Prop) (inside: zone.holds indent)
    (onLine: zone.holds line)
    (onward: ∀ (reached: Place) (events: List Event) => Events zone (inlineHead zone value) value events
      → Ended zone reached
      → next reached (trace ++ events)):
    LaysAll [Doc.text " ", value.layout] indent (Mid line) trace next :=
  rule
    (inlineHead zone value)
    indent
    (Mid line)
    trace
    (after later => LaysAll [] indent after later next)
    inside
    onLine
    (inlineStart zone indent line value.firstAbove inside onLine)
    onward

--| A body's one expression on a line of its own two deeper: a block of
--| one statement at that column.
theorem belowCore ∀ (zone: Zone) (blankBefore: Bool) (value: Expr)
    (rules: ∀ (inner: Zone) => HeadRule inner value.layout value.firstAbove (head => Events inner head value))
    (indent: Nat) (trace: List Event) (next: Place → List Event → Prop) (inside: zone.holds indent)
    (onward: ∀ (reached: Place) (events: List Event) => BodyEvents zone
      { statements = [{ blankBefore, line = Bare value }] }
      events
      → Ended zone reached
      → next reached (trace ++ events)):
    Lays value.layout (indent + 2) (AtStart (indent + 2)) trace next :=
  rules
    (Deeper (indent + 2))
    (atColumn (indent + 2))
    (indent + 2)
    (AtStart (indent + 2))
    trace
    next
    (ownHolds (indent + 2))
    (ownHolds (indent + 2))
    (startAt (indent + 2) (indent + 2) value.firstAbove)
    (reached events isValue ended =>
      onward reached events
        (Inr
          ((
            (indent + 2),
            (holdsDeeper zone indent 1 inside),
            (thenDone (Events (Deeper (indent + 2)) (atColumn (indent + 2)) value) events isValue)
          )))
        (endedUp zone (indent + 2) reached (holdsDeeper zone indent 1 inside) ended))

theorem belowValue ∀ (zone: Zone) (blankBefore: Bool) (value: Expr)
    (rules: ∀ (inner: Zone) => HeadRule inner value.layout value.firstAbove (head => Events inner head value))
    (indent: Nat) (place: Place)
    (mid: place.midLine = True)
    (trace: List Event) (next: Place → List Event → Prop) (inside: zone.holds indent)
    (onward: ∀ (reached: Place) (events: List Event) => BodyEvents zone
      { statements = [{ blankBefore, line = Bare value }] }
      events
      → Ended zone reached
      → next reached (trace ++ events)):
    Lays (below value.layout) indent place trace next :=
  concatLays
    [HardLine, value.layout]
    (indent + 2)
    place
    trace
    next
    ((
      mid,
      (Inr
        (belowCore zone blankBefore value rules indent trace
          (after later => LaysAll [] (indent + 2) after later next)
          inside
          onward))
    ))

--| `let name = body`, a statement or a declaration: the keyword starts
--| as `head` says, the name and `=` stand in the statement.
theorem bindingRule ∀ (zone: Zone) (letComments: Comments) (name: Text) (nameComments equals: Comments) (body: Body)
    (fineLet: Fine letComments)
    (isName: IsName name)
    (fineName: Fine nameComments)
    (fineEquals: Fine equals)
    (bodyRule: BodyRule zone (body.afterEquals equals) equals.after body):
    HeadRule zone (binding letComments name nameComments equals body) letComments.above (head =>
      Then
        (TokenAt head letComments "let")
        (Then
          (TokenAt zone.allows nameComments name)
          (Then (TokenAt zone.allows equals "=") (BodyEvents zone body)))) :=
  head indent place trace next inside seated isHead onward =>
    headCons zone
      (token letComments "let")
      [Doc.text " ", token nameComments name, Doc.text " ", token equals "=", body.afterEquals equals]
      letComments.above
      (first => TokenAt first letComments "let")
      (Then (TokenAt zone.allows nameComments name) (Then (TokenAt zone.allows equals "=") (BodyEvents zone body)))
      (tokenHead zone letComments "let" fineLet solidLet)
      (spaceAll zone zone.holds
        [token nameComments name, Doc.text " ", token equals "=", body.afterEquals equals]
        (Then (TokenAt zone.allows nameComments name) (Then (TokenAt zone.allows equals "=") (BodyEvents zone body)))
        (Ended zone)
        (ruleCons zone.holds
          (token nameComments name)
          [Doc.text " ", token equals "=", body.afterEquals equals]
          (Ended zone)
          (Ended zone)
          (Ended zone)
          (TokenAt zone.allows nameComments name)
          (Then (TokenAt zone.allows equals "=") (BodyEvents zone body))
          (tokenAfter zone nameComments name fineName (nameSolid name isName))
          (spaceAll zone zone.holds
            [token equals "=", body.afterEquals equals]
            (Then (TokenAt zone.allows equals "=") (BodyEvents zone body))
            (Ended zone)
            (keyLast zone equals "="
              (body.afterEquals equals)
              body
              zone.allows
              (Ended zone)
              fineEquals
              solidEquals
              (endedStarts zone equals.above)
              bodyRule))))
      head
      indent
      place
      trace
      next
      inside
      seated
      isHead
      onward

--| The body after `=` with no comment on the `=` (P3): on its line, on
--| one line below, or below and broken; a list also opens on the line.
theorem bareAfterEquals ∀ (blankBefore: Bool) (value: Expr) (above: List Comment) (indent line: Nat)
    (trace: List Event) (next: Place → List Event → Prop)
    (flat: Lays (Doc.concat [Doc.text " ", Flatten value.layout]) indent (Mid line) trace next)
    (opened: Lays (Doc.concat [Doc.text " ", value.layout]) indent (Mid line) trace next)
    (oneLine: Lays (OneLineBelow value.layout) indent (Mid line) trace next)
    (under: Lays (below value.layout) indent (Mid line) trace next):
    Lays
      (Body.afterEquals { statements = [{ blankBefore, line = Bare value }] } { above, after = None })
      indent
      (Mid line)
      trace
      next :=
  match value, flat, opened, oneLine, under with
    | ListLiteral open items close, flat, opened, oneLine, under => (flat, opened)
    | _, flat, opened, oneLine, under => (flat, oneLine, under)

--| An `else` whose branch is one expression: an `if` stays on the
--| `else`'s line when nothing would start a line between them.
theorem elseBare ∀ (zone: Zone) (elseComments: Comments) (blankBefore: Bool) (value: Expr)
    (rule: HeadRule zone value.layout value.firstAbove (head => Events zone head value))
    (viaBranch: BodyRule zone
      (branch elseComments { statements = [{ blankBefore, line = Bare value }] })
      elseComments.after
      { statements = [{ blankBefore, line = Bare value }] }):
    BodyRule zone (elseBranch elseComments { statements = [{ blankBefore, line = Bare value }] }) elseComments.after {
      statements = [{ blankBefore, line = Bare value }]
    } :=
  match value, rule, viaBranch with
    | If ifComments condition thenComments whenTrue innerElse whenFalse, rule, viaBranch =>
      match elseComments, ifComments, rule, viaBranch with
        | { above = elseAbove, after = None }, { above = [], after = ifAfter }, rule, viaBranch =>
          indent line trace next inside onLine onward =>
            concatLays
              [
                Doc.text " ",
                ifLayout { above = [], after = ifAfter } condition thenComments whenTrue innerElse whenFalse
              ]
              indent
              (Mid line)
              trace
              next
              (inlineLays zone
                (If { above = [], after = ifAfter } condition thenComments whenTrue innerElse whenFalse)
                rule
                indent
                line
                trace
                next
                inside
                onLine
                (reached events isValue ended => onward reached events (Inl isValue) ended))
        | { above = elseAbove, after = None }, { above = [comment, ..rest], after = ifAfter }, rule, viaBranch =>
          viaBranch
        | { above = elseAbove, after = Some trailing }, ifComments, rule, viaBranch => viaBranch
    | _, rule, viaBranch => viaBranch

--| What starts a line of a vertical list that isn't its first: a line
--| break after the line before, and the blank line kept.
theorem laterStart ∀ (index: Nat) (blankBefore: Bool) (column: Nat) (place: Place)
    (trace: List Event) (next: Place → List Event → Prop)
    (mid: place.midLine = True) (reached: next (AtStart column) (trace ++ blankEvents blankBefore)):
    Lays (lineStart (index + 1) blankBefore) column place trace next :=
  match blankBefore, reached with
    | True, reached => (mid, (Inl reached))
    | False, reached => (mid, (Inr (rewrite <- List.appendNil trace then reached)))

--| An item and its comma.
theorem itemRule ∀ (zone: Zone) (value: Expr) (comma: Comments)
    (fineComma: Fine comma)
    (rule: HeadRule zone.inside value.layout value.firstAbove (head => Events zone.inside head value)):
    Rule zone.holds
      (Doc.concat [value.layout, closeAfter value (token comma ",")])
      (Seated zone)
      (Then (Events zone.inside anyStart value) (TokenAt anyStart comma ","))
      (Ended zone) :=
  ruleConcat zone.holds
    [value.layout, closeAfter value (token comma ",")]
    (Seated zone)
    (Ended zone)
    (Then (Events zone.inside anyStart value) (TokenAt anyStart comma ","))
    (ruleCons zone.holds value.layout
      [closeAfter value (token comma ",")]
      (Seated zone)
      (Ended zone)
      (Ended zone)
      (Events zone.inside anyStart value)
      (TokenAt anyStart comma ",")
      (headInside zone value.layout value.firstAbove (head => Events zone.inside head value) rule)
      (ruleLast zone.holds
        (closeAfter value (token comma ","))
        (Ended zone)
        (Ended zone)
        (TokenAt anyStart comma ",")
        (closeAfterRule zone value
          (token comma ",")
          (TokenAt anyStart comma ",")
          (headInside zone
            (token comma ",")
            comma.above
            (head => TokenAt head comma ",")
            (tokenHead zone.inside comma "," fineComma solidComma)))))

-- The induction over the tree.

--| A chain's operands and links (P6), from its left-nested tree.
theorem chainLays ∀ (level: Nat) (expr: Expr)
    (lexical: Lexical expr) (zone: Zone)
    (whole: HeadRule zone expr.layout expr.firstAbove (head => Events zone head expr))
    (more: List Doc) (head: Option Nat → Prop) (indent: Nat) (place: Place) (trace: List Event)
    (next: Place → List Event → Prop) (inside: zone.holds indent)
    (seated: Seated zone place) (isHead: head (wordStart indent (aboveEnd indent place expr.firstAbove)))
    (onward: ∀ (after: Place) (events: List Event) => Events zone head expr events
      → Ended zone after
      → LaysAll more (indent + 2) after (trace ++ events) next):
    ChainLays (chainParts level expr ++ more) indent place trace next :=
  match expr, lexical, whole, isHead, onward with
    | Binary operator sign left right, Both fineSign (Both lexLeft lexRight), whole, isHead, onward =>
      match same: operator.level == level with
        | True =>
          rewrite List.appendAssoc (chainParts level left) [link operator sign right.layout] more then
            chainLays level left lexLeft zone
              (exprLays left lexLeft zone)
              ([link operator sign right.layout] ++ more)
              head
              indent
              place
              trace
              next
              inside
              seated
              isHead
              (after events isLeft ended =>
                linkRule zone operator sign right fineSign
                  (exprLays right lexRight zone)
                  (indent + 2)
                  after
                  (trace ++ events)
                  (reached written => LaysAll more (indent + 2) reached written next)
                  (holdsDeeper zone indent 1 inside)
                  ended
                  (last linked isLink met =>
                    rewrite List.appendAssoc trace events linked then
                      onward last (events ++ linked) ((events, linked, byComputing, isLeft, isLink)) met))
        | False =>
          whole head indent place trace
            (after later => LaysAll more (indent + 2) after later next)
            inside
            seated
            isHead
            onward
    | Var name comments, _, whole, isHead, onward =>
      whole head indent place trace
        (after later => LaysAll more (indent + 2) after later next)
        inside
        seated
        isHead
        onward
    | NumberLiteral digits comments, _, whole, isHead, onward =>
      whole head indent place trace
        (after later => LaysAll more (indent + 2) after later next)
        inside
        seated
        isHead
        onward
    | StringLiteral written comments, _, whole, isHead, onward =>
      whole head indent place trace
        (after later => LaysAll more (indent + 2) after later next)
        inside
        seated
        isHead
        onward
    | Bracketed open inner close, _, whole, isHead, onward =>
      whole head indent place trace
        (after later => LaysAll more (indent + 2) after later next)
        inside
        seated
        isHead
        onward
    | ListLiteral open items close, _, whole, isHead, onward =>
      whole head indent place trace
        (after later => LaysAll more (indent + 2) after later next)
        inside
        seated
        isHead
        onward
    | Call callee open arguments close, _, whole, isHead, onward =>
      whole head indent place trace
        (after later => LaysAll more (indent + 2) after later next)
        inside
        seated
        isHead
        onward
    | Field target dot name nameComments, _, whole, isHead, onward =>
      whole head indent place trace
        (after later => LaysAll more (indent + 2) after later next)
        inside
        seated
        isHead
        onward
    | Negate minus operand, _, whole, isHead, onward =>
      whole head indent place trace
        (after later => LaysAll more (indent + 2) after later next)
        inside
        seated
        isHead
        onward
    | If ifComments condition thenComments whenTrue elseComments whenFalse, _, whole, isHead, onward =>
      whole head indent place trace
        (after later => LaysAll more (indent + 2) after later next)
        inside
        seated
        isHead
        onward

--| Every way an expression's layout may print, from any place no
--| shallower than its statement, puts down the expression's `Events`:
--| its leftmost token starting as that place makes it, every other
--| where the parser's layout rule takes it.
theorem exprLays ∀ (expr: Expr)
    (lexical: Lexical expr) (zone: Zone):
    HeadRule zone expr.layout expr.firstAbove (head => Events zone head expr) :=
  match expr, lexical with
    | Var name comments, Both isName fine => head indent place trace next inside seated isHead onward =>
      tokenHead zone comments name fine (nameSolid name isName) head indent place trace next inside seated isHead onward
    | NumberLiteral digits comments, Both isDigits fine => head indent place trace next inside seated isHead onward =>
      tokenHead zone comments digits fine
        (digitsSolid digits isDigits)
        head
        indent
        place
        trace
        next
        inside
        seated
        isHead
        onward
    | StringLiteral written comments, Both isString fine => head indent place trace next inside seated isHead onward =>
      tokenHead zone comments written fine
        (stringSolid written isString)
        head
        indent
        place
        trace
        next
        inside
        seated
        isHead
        onward
    | Bracketed open inner close, Both fineOpen (Both lexInner fineClose) =>
      head indent place trace next inside seated isHead onward =>
        headCons zone
          (token open "(")
          [inner.layout, closeAfter inner (closer close ")")]
          open.above
          (first => TokenAt first open "(")
          (Then (Events zone.inside anyStart inner) (TokenAt anyStart close ")"))
          (tokenHead zone open "(" fineOpen solidOpenParen)
          (ruleCons zone.holds inner.layout
            [closeAfter inner (closer close ")")]
            (Ended zone)
            (Ended zone)
            (Ended zone)
            (Events zone.inside anyStart inner)
            (TokenAt anyStart close ")")
            (fromEnded zone zone.holds inner.layout
              (Events zone.inside anyStart inner)
              (Ended zone)
              (headInside zone inner.layout inner.firstAbove
                (first => Events zone.inside first inner)
                (exprLays inner lexInner zone.inside)))
            (ruleLast zone.holds
              (closeAfter inner (closer close ")"))
              (Ended zone)
              (Ended zone)
              (TokenAt anyStart close ")")
              (closeAfterRule zone inner
                (closer close ")")
                (TokenAt anyStart close ")")
                (closerRule zone close ")" fineClose solidCloseParen))))
          head
          indent
          place
          trace
          next
          inside
          seated
          isHead
          onward
    | ListLiteral open items close, Both fineOpen (Both lexItems fineClose) =>
      match items, lexItems with
        | [], _ => head indent place trace next inside seated isHead onward =>
          headCons zone
            (token open "[")
            [closer close "]"]
            open.above
            (first => TokenAt first open "[")
            (Then Done (TokenAt anyStart close "]"))
            (tokenHead zone open "[" fineOpen solidOpenSquare)
            (emptyCloser zone close "]" fineClose solidCloseSquare)
            head
            indent
            place
            trace
            next
            inside
            seated
            isHead
            onward
        | [first, ..rest], lexItems => head indent place trace next inside seated isHead onward =>
          match lastOfCons first rest with
            | Witness last found =>
              rewrite found then
                headCons zone
                  (token open "[")
                  [Nest 2 (Fill (itemDocs [first, ..rest])), closeAfter last (closer close "]")]
                  open.above
                  (leftmost => TokenAt leftmost open "[")
                  (Then (ItemEvents zone.inside [first, ..rest]) (TokenAt anyStart close "]"))
                  (tokenHead zone open "[" fineOpen solidOpenSquare)
                  (ruleCons zone.holds
                    (Nest 2 (Fill (itemDocs [first, ..rest])))
                    [closeAfter last (closer close "]")]
                    (Ended zone)
                    (Ended zone)
                    (Ended zone)
                    (ItemEvents zone.inside [first, ..rest])
                    (TokenAt anyStart close "]")
                    (nestFill zone
                      (itemDocs [first, ..rest])
                      (ItemEvents zone.inside [first, ..rest])
                      (fillItems first rest lexItems zone))
                    (ruleLast zone.holds
                      (closeAfter last (closer close "]"))
                      (Ended zone)
                      (Ended zone)
                      (TokenAt anyStart close "]")
                      (closeAfterRule zone last
                        (closer close "]")
                        (TokenAt anyStart close "]")
                        (closerRule zone close "]" fineClose solidCloseSquare))))
                  head
                  indent
                  place
                  trace
                  next
                  inside
                  seated
                  isHead
                  onward
    | Call callee open arguments close, Both lexCallee (Both fineOpen (Both lexArguments fineClose)) =>
      match arguments, lexArguments with
        | [], _ => head indent place trace next inside seated isHead onward =>
          headCons zone callee.layout
            [Doc.concat [token open "(", closer close ")"]]
            callee.firstAbove
            (leftmost => Events zone leftmost callee)
            (Then (TokenAt zone.allows open "(") (Then Done (TokenAt anyStart close ")")))
            (exprLays callee lexCallee zone)
            (ruleLast zone.holds
              (Doc.concat [token open "(", closer close ")"])
              (Ended zone)
              (Ended zone)
              (Then (TokenAt zone.allows open "(") (Then Done (TokenAt anyStart close ")")))
              (ruleConcat zone.holds
                [token open "(", closer close ")"]
                (Ended zone)
                (Ended zone)
                (Then (TokenAt zone.allows open "(") (Then Done (TokenAt anyStart close ")")))
                (ruleCons zone.holds
                  (token open "(")
                  [closer close ")"]
                  (Ended zone)
                  (Ended zone)
                  (Ended zone)
                  (TokenAt zone.allows open "(")
                  (Then Done (TokenAt anyStart close ")"))
                  (tokenAfter zone open "(" fineOpen solidOpenParen)
                  (emptyCloser zone close ")" fineClose solidCloseParen))))
            head
            indent
            place
            trace
            next
            inside
            seated
            isHead
            onward
        | [first, ..rest], lexArguments => head indent place trace next inside seated isHead onward =>
          headCons zone callee.layout
            [argumentsLayout open [first, ..rest] close]
            callee.firstAbove
            (leftmost => Events zone leftmost callee)
            (Then
              (TokenAt zone.allows open "(")
              (Then (ItemEvents zone.inside [first, ..rest]) (TokenAt anyStart close ")")))
            (exprLays callee lexCallee zone)
            (ruleLast zone.holds
              (argumentsLayout open [first, ..rest] close)
              (Ended zone)
              (Ended zone)
              (Then
                (TokenAt zone.allows open "(")
                (Then (ItemEvents zone.inside [first, ..rest]) (TokenAt anyStart close ")")))
              (ruleConcat zone.holds
                [
                  token open "(",
                  Nest 2 (Doc.concat [SoftLine, joined (itemDocs [first, ..rest]) Line]),
                  SoftLine,
                  closer close ")"
                ]
                (Ended zone)
                (Ended zone)
                (Then
                  (TokenAt zone.allows open "(")
                  (Then (ItemEvents zone.inside [first, ..rest]) (TokenAt anyStart close ")")))
                (ruleCons zone.holds
                  (token open "(")
                  [Nest 2 (Doc.concat [SoftLine, joined (itemDocs [first, ..rest]) Line]), SoftLine, closer close ")"]
                  (Ended zone)
                  (Ended zone)
                  (Ended zone)
                  (TokenAt zone.allows open "(")
                  (Then (ItemEvents zone.inside [first, ..rest]) (TokenAt anyStart close ")"))
                  (tokenAfter zone open "(" fineOpen solidOpenParen)
                  (ruleCons zone.holds
                    (Nest 2 (Doc.concat [SoftLine, joined (itemDocs [first, ..rest]) Line]))
                    [SoftLine, closer close ")"]
                    (Ended zone)
                    (Ended zone)
                    (Ended zone)
                    (ItemEvents zone.inside [first, ..rest])
                    (TokenAt anyStart close ")")
                    (nestJoined zone 2
                      (itemDocs [first, ..rest])
                      (ItemEvents zone.inside [first, ..rest])
                      (fillItems first rest lexArguments zone))
                    (softCloser zone close ")" fineClose solidCloseParen)))))
            head
            indent
            place
            trace
            next
            inside
            seated
            isHead
            onward
    | Field target dot name nameComments, Both lexTarget (Both fineDot (Both isName fineName)) =>
      head indent place trace next inside seated isHead onward =>
        headCons zone target.layout
          [token dot ".", token nameComments name]
          target.firstAbove
          (leftmost => Events zone leftmost target)
          (Then (TokenAt zone.allows dot ".") (TokenAt zone.allows nameComments name))
          (exprLays target lexTarget zone)
          (ruleCons zone.holds
            (token dot ".")
            [token nameComments name]
            (Ended zone)
            (Ended zone)
            (Ended zone)
            (TokenAt zone.allows dot ".")
            (TokenAt zone.allows nameComments name)
            (tokenAfter zone dot "." fineDot solidDot)
            (ruleLast zone.holds
              (token nameComments name)
              (Ended zone)
              (Ended zone)
              (TokenAt zone.allows nameComments name)
              (tokenAfter zone nameComments name fineName (nameSolid name isName))))
          head
          indent
          place
          trace
          next
          inside
          seated
          isHead
          onward
    | Negate minus operand, Both fineMinus lexOperand => head indent place trace next inside seated isHead onward =>
      headCons zone
        (token minus "-")
        [Doc.text (if operand.startsWithMinus then " " else ""), operand.layout]
        minus.above
        (leftmost => TokenAt leftmost minus "-")
        (Events zone zone.allows operand)
        (tokenHead zone minus "-" fineMinus solidMinus)
        (gapAll zone zone.holds operand.startsWithMinus
          [operand.layout]
          (Events zone zone.allows operand)
          (Ended zone)
          (ruleLast zone.holds operand.layout
            (Ended zone)
            (Ended zone)
            (Events zone zone.allows operand)
            (headInner zone operand.layout operand.firstAbove
              (leftmost => Events zone leftmost operand)
              (exprLays operand lexOperand zone))))
        head
        indent
        place
        trace
        next
        inside
        seated
        isHead
        onward
    | Binary operator sign left right, Both fineSign (Both lexLeft lexRight) =>
      head indent place trace next inside seated isHead onward =>
        let parts :=
          chainLays operator.level left lexLeft zone
            (exprLays left lexLeft zone)
            [link operator sign right.layout]
            head
            indent
            place
            trace
            next
            inside
            seated
            isHead
            (after events isLeft ended =>
              linkRule zone operator sign right fineSign
                (exprLays right lexRight zone)
                (indent + 2)
                after
                (trace ++ events)
                (reached written => LaysAll [] (indent + 2) reached written next)
                (holdsDeeper zone indent 1 inside)
                ended
                (last linked isLink met =>
                  rewrite List.appendAssoc trace events linked then
                    onward last (events ++ linked) ((events, linked, byComputing, isLeft, isLink)) met))
        match found: chainParts operator.level left ++ [link operator sign right.layout] with
          | [first, ..links] =>
            chainLaid
              (chainParts operator.level left ++ [link operator sign right.layout])
              first
              links
              indent
              place
              trace
              next
              found
              parts
    | If ifComments condition thenComments whenTrue elseComments whenFalse, Both fineIf
        (Both lexCondition (Both fineThen (Both lexTrue (Both fineElse lexFalse)))) =>
      head indent place trace next inside seated isHead onward =>
        headCons zone
          (token ifComments "if")
          [
            Doc.text " ",
            condition.layout,
            Doc.text " ",
            token thenComments "then",
            branch thenComments whenTrue,
            Line,
            token elseComments "else",
            elseBranch elseComments whenFalse
          ]
          ifComments.above
          (leftmost => TokenAt leftmost ifComments "if")
          (Then
            (Events zone zone.allows condition)
            (Then
              (TokenAt zone.allows thenComments "then")
              (Then
                (BodyEvents zone whenTrue)
                (Then (TokenAt zone.reaches elseComments "else") (BodyEvents zone whenFalse)))))
          (tokenHead zone ifComments "if" fineIf solidIf)
          (spaceAll zone zone.holds _ _
            (Ended zone)
            (ruleCons zone.holds condition.layout _
              (Ended zone)
              (Ended zone)
              (Ended zone)
              (Events zone zone.allows condition) _
              (headInner zone condition.layout condition.firstAbove
                (leftmost => Events zone leftmost condition)
                (exprLays condition lexCondition zone))
              (spaceAll zone zone.holds _ _
                (Ended zone)
                (keyCons zone thenComments "then"
                  (branch thenComments whenTrue)
                  whenTrue
                  zone.allows
                  (Ended zone)
                  [Line, token elseComments "else", elseBranch elseComments whenFalse]
                  (Then (TokenAt zone.reaches elseComments "else") (BodyEvents zone whenFalse))
                  (Ended zone)
                  fineThen
                  solidThen
                  (endedStarts zone thenComments.above)
                  (branchLays zone thenComments whenTrue lexTrue)
                  (lineSeatsAll zone
                    [token elseComments "else", elseBranch elseComments whenFalse]
                    (Then (TokenAt zone.reaches elseComments "else") (BodyEvents zone whenFalse))
                    (Ended zone)
                    (keyLast zone elseComments "else"
                      (elseBranch elseComments whenFalse)
                      whenFalse
                      zone.reaches
                      (Seated zone)
                      fineElse
                      solidElse
                      (seatedStarts zone elseComments.above)
                      (elseBranchLays zone elseComments whenFalse lexFalse)))))))
          head
          indent
          place
          trace
          next
          inside
          seated
          isHead
          onward

--| The items after the first of a fill, each after a separator.
theorem sepsItems ∀ (items: List Expr)
    (lexical: LexicalItems items)
    (zone: Zone) (indent: Nat) (place: Place) (trace: List Event)
    (next: Place → List Event → Prop) (inside: zone.holds indent)
    (ended: Ended zone place)
    (onward: ∀ (after: Place) (events: List Event) => ItemEvents zone.inside items events
      → Ended zone after
      → next after (trace ++ events)):
    SepsLay (itemDocs items) indent place trace next :=
  match items, lexical, onward with
    | [], _, onward => rewrite <- List.appendNil trace then onward place [] byComputing ended
    | [value], Both lexValue _, onward =>
      sepSeats zone indent place trace
        (middle between => Lays value.layout indent middle between (after later => SepsLay [] indent after later next))
        inside
        ended
        (middle seated =>
          headInside zone value.layout value.firstAbove
            (leftmost => Events zone.inside leftmost value)
            (exprLays value lexValue zone.inside)
            indent
            middle
            trace
            (after later => SepsLay [] indent after later next)
            inside
            seated
            onward)
    | [value, second, ..more], Both lexValue others, onward =>
      sepSeats zone indent place trace
        (middle between =>
          Lays (Doc.concat [value.layout, closeAfter value (token Comments.none ",")]) indent middle between (after later =>
            SepsLay (itemDocs [second, ..more]) indent after later next))
        inside
        ended
        (middle seated =>
          itemRule zone value Comments.none fineNone
            (exprLays value lexValue zone.inside)
            indent
            middle
            trace
            (after later => SepsLay (itemDocs [second, ..more]) indent after later next)
            inside
            seated
            (after events isItem reached =>
              sepsItems
                [second, ..more]
                others
                zone
                indent
                after
                (trace ++ events)
                next
                inside
                reached
                (last rest areItems met =>
                  rewrite List.appendAssoc trace events rest then
                    onward last
                      (events ++ rest)
                      (thenAssoc
                        (Events zone.inside anyStart value)
                        (TokenAt anyStart Comments.none ",")
                        (ItemEvents zone.inside [second, ..more])
                        events
                        rest
                        isItem
                        areItems)
                      met)))

--| The items of a list or a call, as a fill lays them.
theorem fillItems ∀ (first: Expr) (rest: List Expr)
    (lexical: LexicalItems [first, ..rest]) (zone: Zone):
    FillRule zone (itemDocs [first, ..rest]) (ItemEvents zone.inside [first, ..rest]) :=
  match first, rest, lexical with
    | value, [], Both lexValue _ => indent place trace next inside seated onward =>
      headInside zone value.layout value.firstAbove
        (leftmost => Events zone.inside leftmost value)
        (exprLays value lexValue zone.inside)
        indent
        place
        trace
        (after later => SepsLay [] indent after later next)
        inside
        seated
        onward
    | value, [second, ..more], Both lexValue others =>
      indent place trace next inside seated onward =>
        itemRule zone value Comments.none fineNone
          (exprLays value lexValue zone.inside)
          indent
          place
          trace
          (after later => SepsLay (itemDocs [second, ..more]) indent after later next)
          inside
          seated
          (after events isItem reached =>
            sepsItems
              [second, ..more]
              others
              zone
              indent
              after
              (trace ++ events)
              next
              inside
              reached
              (last later areItems met =>
                rewrite List.appendAssoc trace events later then
                  onward last
                    (events ++ later)
                    (thenAssoc
                      (Events zone.inside anyStart value)
                      (TokenAt anyStart Comments.none ",")
                      (ItemEvents zone.inside [second, ..more])
                      events
                      later
                      isItem
                      areItems)
                    met))

--| A branch of an `if` (P7): on its keyword's line, or below.
theorem branchLays ∀ (zone: Zone) (keyword: Comments) (body: Body)
    (lexical: LexicalBody body):
    BodyRule zone (branch keyword body) keyword.after body :=
  match body, lexical with
    | { statements = [] }, Both _ never => (Bool.falseNotTrue never).impossible
    | { statements = [{ blankBefore, line = Bare value }] }, Both (Both lexValue _) _ =>
      match keyword with
        | { above, after = None } => indent line trace next inside onLine onward =>
          (
            (concatLays
              [Doc.text " ", Flatten value.layout]
              indent
              (Mid line)
              trace
              next
              (inlineLays zone value
                (exprLays value lexValue zone)
                indent
                line
                trace
                next
                inside
                onLine
                (reached events isValue ended => onward reached events (Inl isValue) ended))),
            (belowValue zone blankBefore value
              (inner => exprLays value lexValue inner)
              indent
              (Mid line)
              byComputing
              trace
              next
              inside
              onward)
          )
        | { above, after = Some trailing } => indent line trace next inside onLine onward =>
          belowValue zone blankBefore value
            (inner => exprLays value lexValue inner)
            indent
            (Held line)
            byComputing
            trace
            next
            inside
            onward
    | { statements = [{ blankBefore, line = Let letComments name nameComments equals inner }] }, Both lexLines closed =>
      indent line trace next inside onLine onward =>
        blockLays zone
          { blankBefore, line = Let letComments name nameComments equals inner }
          []
          lexLines
          indent
          (trailEnd line keyword.after)
          (trailMid line keyword.after)
          trace
          next
          inside
          onward
    | { statements = [{ blankBefore, line = StatementNote comment }] }, Both lexLines closed =>
      indent line trace next inside onLine onward =>
        blockLays zone
          { blankBefore, line = StatementNote comment }
          []
          lexLines
          indent
          (trailEnd line keyword.after)
          (trailMid line keyword.after)
          trace
          next
          inside
          onward
    | { statements = [first, second, ..rest] }, Both lexLines closed => indent line trace next inside onLine onward =>
      blockLays zone first
        [second, ..rest]
        lexLines
        indent
        (trailEnd line keyword.after)
        (trailMid line keyword.after)
        trace
        next
        inside
        onward

theorem elseBranchLays ∀ (zone: Zone) (elseComments: Comments) (body: Body)
    (lexical: LexicalBody body):
    BodyRule zone (elseBranch elseComments body) elseComments.after body :=
  match body, lexical with
    | { statements = [{ blankBefore, line = Bare value }] }, Both (Both lexValue done) closed =>
      elseBare zone elseComments blankBefore value
        (exprLays value lexValue zone)
        (branchLays zone elseComments
          { statements = [{ blankBefore, line = Bare value }] }
          ((((lexValue, done)), closed)))
    | { statements = [] }, lexical => branchLays zone elseComments { statements = [] } lexical
    | { statements = [{ blankBefore, line = Let letComments name nameComments equals inner }] }, lexical =>
      branchLays zone elseComments
        { statements = [{ blankBefore, line = Let letComments name nameComments equals inner }] }
        lexical
    | { statements = [{ blankBefore, line = StatementNote comment }] }, lexical =>
      branchLays zone elseComments { statements = [{ blankBefore, line = StatementNote comment }] } lexical
    | { statements = [{ blankBefore, line = Bare value }, second, ..rest] }, lexical =>
      match value, lexical with
        | If ifComments condition thenComments whenTrue innerElse whenFalse, lexical =>
          branchLays zone elseComments { statements = [{ blankBefore, line = Bare value }, second, ..rest] } lexical
        | _, lexical =>
          branchLays zone elseComments { statements = [{ blankBefore, line = Bare value }, second, ..rest] } lexical
    | {
        statements = [{ blankBefore, line = Let letComments name nameComments equals inner }, second, ..rest]
      }, lexical =>
      branchLays zone elseComments
        { statements = [{ blankBefore, line = Let letComments name nameComments equals inner }, second, ..rest] }
        lexical
    | { statements = [{ blankBefore, line = StatementNote comment }, second, ..rest] }, lexical =>
      branchLays zone elseComments
        { statements = [{ blankBefore, line = StatementNote comment }, second, ..rest] }
        lexical

--| The body after `=` (P3): on the `=` line, or below.
theorem afterEqualsLays ∀ (zone: Zone) (equals: Comments) (body: Body)
    (lexical: LexicalBody body):
    BodyRule zone (body.afterEquals equals) equals.after body :=
  match body, lexical with
    | { statements = [] }, Both _ never => (Bool.falseNotTrue never).impossible
    | { statements = [{ blankBefore, line = Bare value }] }, Both (Both lexValue _) _ =>
      match equals with
        | { above, after = None } => indent line trace next inside onLine onward =>
          bareAfterEquals blankBefore value above indent line trace next
            (concatLays
              [Doc.text " ", Flatten value.layout]
              indent
              (Mid line)
              trace
              next
              (inlineLays zone value
                (exprLays value lexValue zone)
                indent
                line
                trace
                next
                inside
                onLine
                (reached events isValue ended => onward reached events (Inl isValue) ended)))
            (concatLays
              [Doc.text " ", value.layout]
              indent
              (Mid line)
              trace
              next
              (inlineLays zone value
                (exprLays value lexValue zone)
                indent
                line
                trace
                next
                inside
                onLine
                (reached events isValue ended => onward reached events (Inl isValue) ended)))
            ((
              byComputing,
              (belowCore zone blankBefore value
                (inner => exprLays value lexValue inner)
                indent
                trace
                next
                inside
                onward)
            ))
            (belowValue zone blankBefore value
              (inner => exprLays value lexValue inner)
              indent
              (Mid line)
              byComputing
              trace
              next
              inside
              onward)
        | { above, after = Some trailing } => indent line trace next inside onLine onward =>
          belowValue zone blankBefore value
            (inner => exprLays value lexValue inner)
            indent
            (Held line)
            byComputing
            trace
            next
            inside
            onward
    | { statements = [{ blankBefore, line = Let letComments name nameComments inner innerBody }] }, Both lexLines
          closed => indent line trace next inside onLine onward =>
      blockLays zone
        { blankBefore, line = Let letComments name nameComments inner innerBody }
        []
        lexLines
        indent
        (trailEnd line equals.after)
        (trailMid line equals.after)
        trace
        next
        inside
        onward
    | { statements = [{ blankBefore, line = StatementNote comment }] }, Both lexLines closed =>
      indent line trace next inside onLine onward =>
        blockLays zone
          { blankBefore, line = StatementNote comment }
          []
          lexLines
          indent
          (trailEnd line equals.after)
          (trailMid line equals.after)
          trace
          next
          inside
          onward
    | { statements = [first, second, ..rest] }, Both lexLines closed => indent line trace next inside onLine onward =>
      blockLays zone first
        [second, ..rest]
        lexLines
        indent
        (trailEnd line equals.after)
        (trailMid line equals.after)
        trace
        next
        inside
        onward

--| A block below its keyword: its statements as lines two deeper, a
--| column a line of the zone may start at.
theorem blockLays ∀ (zone: Zone) (first: Spaced Statement) (rest: List (Spaced Statement))
    (lexical: LexicalLines [first, ..rest])
    (indent: Nat) (place: Place)
    (mid: place.midLine = True)
    (trace: List Event) (next: Place → List Event → Prop) (inside: zone.holds indent)
    (onward: ∀ (reached: Place) (events: List Event) => BodyEvents zone { statements = [first, ..rest] } events
      → Ended zone reached
      → next reached (trace ++ events)):
    Lays (below (Body.block { statements = [first, ..rest] })) indent place trace next :=
  concatLays
    [HardLine, Doc.concat (statementLines 0 [first, ..rest])]
    (indent + 2)
    place
    trace
    next
    (Both mid
      (Inr
        (concatLays
          (statementLines 0 [first, ..rest])
          (indent + 2)
          (AtStart (indent + 2))
          trace
          (after later => LaysAll [] (indent + 2) after later next)
          (linesLay first rest lexical
            (indent + 2)
            trace
            (after later => LaysAll [] (indent + 2) after later next)
            (reached events areLines ended =>
              onward reached events
                (Inr (Witness (indent + 2) (Both (holdsDeeper zone indent 1 inside) areLines)))
                (endedUp zone (indent + 2) reached (holdsDeeper zone indent 1 inside) ended))))))

--| The lines of a block at `column`, from the start of its first line:
--| each statement starts its line at the column.
theorem linesLay ∀ (first: Spaced Statement) (rest: List (Spaced Statement))
    (lexical: LexicalLines [first, ..rest])
    (column: Nat) (trace: List Event) (next: Place → List Event → Prop)
    (onward: ∀ (reached: Place) (events: List Event) => LineEvents column [first, ..rest] events
      → Ended (Deeper column) reached
      → next reached (trace ++ events)):
    LaysAll (statementLines 0 [first, ..rest]) column (AtStart column) trace next :=
  match first, lexical, onward with
    | { blankBefore, line }, Both lexLine others, onward =>
      statementLays line lexLine column trace
        (after later => LaysAll (statementLines (0 + 1) rest) column after later next)
        (reached events isLine ended =>
          laterLay 0 rest others column reached (trace ++ events) next ended (last later areLines met =>
            rewrite List.appendAssoc trace events later then
              onward last (events ++ later) ((events, later, byComputing, isLine, areLines)) met))

--| The lines of a block after its first, the first of these the
--| `index + 1`th: each on a new line at the column, after a blank line
--| if it has one before it.
theorem laterLay ∀ (index: Nat) (lines: List (Spaced Statement))
    (lexical: LexicalLines lines)
    (column: Nat) (place: Place) (trace: List Event) (next: Place → List Event → Prop)
    (ended: Ended (Deeper column) place)
    (onward: ∀ (reached: Place) (events: List Event) => LaterLines column lines events
      → Ended (Deeper column) reached
      → next reached (trace ++ events)):
    LaysAll (statementLines (index + 1) lines) column place trace next :=
  match lines, lexical, onward with
    | [], _, onward => rewrite <- List.appendNil trace then onward place [] byComputing ended
    | [{ blankBefore, line }, ..more], Both lexLine others, onward =>
      laterStart index blankBefore column place trace
        (after later => LaysAll [line.layout, ..statementLines (index + 1 + 1) more] column after later next)
        (endedMid (Deeper column) place ended)
        (statementLays line lexLine column
          (trace ++ blankEvents blankBefore)
          (after later => LaysAll (statementLines (index + 1 + 1) more) column after later next)
          (reached events isLine met =>
            laterLay
              (index + 1)
              more
              others
              column
              reached
              ((trace ++ blankEvents blankBefore) ++ events)
              next
              met
              (last later areLines done =>
                rewrite List.appendAssoc (trace ++ blankEvents blankBefore) events later,
                    List.appendAssoc trace (blankEvents blankBefore) (events ++ later) then
                  onward last
                    (blankEvents blankBefore ++ (events ++ later))
                    (((events ++ later), byComputing, events, later, byComputing, isLine, areLines))
                    done)))

--| A statement of a block at `column`, from the start of its line.
theorem statementLays ∀ (statement: Statement)
    (lexical: LexicalStatement statement)
    (column: Nat) (trace: List Event) (next: Place → List Event → Prop)
    (onward: ∀ (reached: Place) (events: List Event) => StatementEvents column statement events
      → Ended (Deeper column) reached
      → next reached (trace ++ events)):
    Lays statement.layout column (AtStart column) trace next :=
  match statement, lexical, onward with
    | Let letComments name nameComments equals body, Both fineLet
        (Both isName (Both fineName (Both fineEquals lexBody))), onward =>
      bindingRule
        (Deeper column)
        letComments
        name
        nameComments
        equals
        body
        fineLet
        isName
        fineName
        fineEquals
        (afterEqualsLays (Deeper column) equals body lexBody)
        (atColumn column)
        column
        (AtStart column)
        trace
        next
        (ownHolds column)
        (ownHolds column)
        (startAt column column letComments.above)
        onward
    | Bare value, lexValue, onward =>
      exprLays value lexValue
        (Deeper column)
        (atColumn column)
        column
        (AtStart column)
        trace
        next
        (ownHolds column)
        (ownHolds column)
        (startAt column column value.firstAbove)
        onward
    | StatementNote comment, fine, onward =>
      wordLays column comment.text
        (AtStart column)
        trace
        next
        (commentSolid comment.text fine)
        (onward (Mid column) [{ word = comment.text, start = Some column }] byComputing (ownHolds column))

-- Declarations and the file.

--| A parameter's type, inside brackets.
def TypeEvents (annotation: TypeExpr): List Event → Prop := match annotation with
  | TypeName name comments => TokenAt anyStart comments name
  | TypeBracketed open inner close =>
    Then (TokenAt anyStart open "(") (Then (TypeEvents inner) (TokenAt anyStart close ")"))

--| The names of a group after its first.
def NamesEvents (names: List Named): List Event → Prop := match names with
  | [] => Done
  | [{ name, comments }, ..rest] => Then (TokenAt anyStart comments name) (NamesEvents rest)

--| A parameter group: its names, then `:` and its type if it has them.
def GroupEvents (group: ParameterGroup): List Event → Prop := match group with
  | Untyped { name, comments } => TokenAt anyStart comments name
  | Typed names colon annotation =>
    Then
      (TokenAt anyStart names.head.comments names.head.name)
      (Then (NamesEvents names.tail) (Then (TokenAt anyStart colon ":") (TypeEvents annotation)))

--| A declaration's parameter groups between their brackets, and the
--| comma after each but the last.
def ParameterEvents (parameters: List ParameterGroup): List Event → Prop := match parameters with
  | [] => Done
  | [group] => GroupEvents group
  | [group, ..rest] =>
    Then (GroupEvents group) (Then (TokenAt anyStart Comments.none ",") (ParameterEvents rest))

--| `takes`, where it was written, standing in its statement.
def TakesEvents (zone: Zone) (takes: Option Comments): List Event → Prop := match takes with
  | None => Done
  | Some comments => TokenAt zone.allows comments "takes"

--| A declaration, from the start of a line at column 0: its first token
--| starts that line, the others stand in it as a statement's do. A
--| function is `fn name (`, with `takes` before `(` if it was written,
--| the parameters, then `) =` and the body.
def DeclarationEvents (declaration: Declaration): List Event → Prop := match declaration with
  | Function fnComments name nameComments takes open parameters close equals body =>
    Then
      (Then
        (TokenAt (atColumn 0) fnComments "fn")
        (Then
          (TokenAt (Deeper 0).allows nameComments name)
          (Then (TakesEvents (Deeper 0) takes) (TokenAt (Deeper 0).allows open "("))))
      (Then
        (ParameterEvents parameters)
        (Then (TokenAt anyStart close ")") (Then (TokenAt (Deeper 0).allows equals "=") (BodyEvents (Deeper 0) body))))
  | Value letComments name nameComments equals body =>
    Then
      (TokenAt (atColumn 0) letComments "let")
      (Then
        (TokenAt (Deeper 0).allows nameComments name)
        (Then (TokenAt (Deeper 0).allows equals "=") (BodyEvents (Deeper 0) body)))
  | DeclarationNote comment => events => events = [{ word = comment.text, start = Some 0 }]

--| A file's declarations, one after another, with the blank lines kept
--| between them (none before the first).
def DeclarationsEvents (declarations: List (Spaced Declaration)): List Event → Prop := match declarations with
  | [] => Done
  | [{ line, .. }, ..rest] => Then (DeclarationEvents line) (LaterDeclarations rest)

--| A file's declarations after its first: each after a blank line if it
--| has one before it.
def LaterDeclarations (declarations: List (Spaced Declaration)): List Event → Prop := match declarations with
  | [] => Done
  | [{ blankBefore, line }, ..rest] => events =>
    ∃ (later: List Event) => events = blankEvents blankBefore ++ later
      ∧ Then (DeclarationEvents line) (LaterDeclarations rest) later

--| The events of a file: what the rules lay for it, whichever way its
--| groups, fills and choices go.
def FileEvents (file: SourceFile): List Event → Prop := DeclarationsEvents file.declarations

theorem solidFn: Solid "fn" := Both byComputing (Both byComputing byComputing)

theorem solidTakes: Solid "takes" := (byComputing, byComputing, byComputing)

theorem solidColon: Solid ":" := (byComputing, byComputing, byComputing)

--| Documents laid one after another may be taken in two parts.
theorem allAppend ∀ (front back: List Doc) (indent: Nat) (place: Place)
    (trace: List Event) (next: Place → List Event → Prop)
    (lays: LaysAll (front ++ back) indent place trace next):
    LaysAll front indent place trace (after later => LaysAll back indent after later next) :=
  match front, lays with
    | [], lays => lays
    | [doc, ..rest], lays =>
      laysWeaker doc indent place trace
        (after later => LaysAll (rest ++ back) indent after later next)
        (after later => LaysAll rest indent after later (reached written => LaysAll back indent reached written next))
        (after later all => allAppend rest back indent after later next all)
        lays

--| A token inside brackets.
theorem tokenInside ∀ (zone: Zone) (comments: Comments) (text: Text)
    (fine: Fine comments)
    (solid: Solid text):
    Rule zone.holds (token comments text) (Seated zone) (TokenAt anyStart comments text) (Ended zone) :=
  headInside zone
    (token comments text)
    comments.above
    (head => TokenAt head comments text)
    (tokenHead zone.inside comments text fine solid)

--| Where a rule puts down nothing.
theorem ruleEmpty ∀ (zone: Zone) (doc: Doc) (empty: doc = Empty): Rule zone.holds doc (Ended zone) Done (Ended zone) :=
  indent place trace next inside ended onward =>
    rewrite empty, <- List.appendNil trace then onward place [] byComputing ended

theorem allNone ∀ (zone: Zone): RuleAll zone.holds [] (Ended zone) Done (Ended zone) :=
  indent place trace next inside ended onward => rewrite <- List.appendNil trace then onward place [] byComputing ended

--| A type inside brackets.
theorem typeLays ∀ (zone: Zone) (annotation: TypeExpr)
    (lexical: LexicalType annotation):
    Rule zone.holds annotation.layout (Seated zone) (TypeEvents annotation) (Ended zone) :=
  match annotation, lexical with
    | TypeName name comments, (isName, fine) => tokenInside zone comments name fine (nameSolid name isName)
    | TypeBracketed open inner close, (fineOpen, lexInner, fineClose) =>
      ruleConcat zone.holds
        [token open "(", inner.layout, closer close ")"]
        (Seated zone)
        (Ended zone)
        (TypeEvents (TypeBracketed open inner close))
        (ruleCons zone.holds
          (token open "(")
          [inner.layout, closer close ")"]
          (Seated zone)
          (Ended zone)
          (Ended zone)
          (TokenAt anyStart open "(")
          (Then (TypeEvents inner) (TokenAt anyStart close ")"))
          (tokenInside zone open "(" fineOpen solidOpenParen)
          (ruleCons zone.holds inner.layout
            [closer close ")"]
            (Ended zone)
            (Ended zone)
            (Ended zone)
            (TypeEvents inner)
            (TokenAt anyStart close ")")
            (fromEnded zone zone.holds inner.layout (TypeEvents inner) (Ended zone) (typeLays zone inner lexInner))
            (ruleLast zone.holds
              (closer close ")")
              (Ended zone)
              (Ended zone)
              (TokenAt anyStart close ")")
              (fromEnded zone zone.holds
                (closer close ")")
                (TokenAt anyStart close ")")
                (Ended zone)
                (closerRule zone close ")" fineClose solidCloseParen)))))

--| A group's names after its first, each after a space.
theorem namesLay ∀ (zone: Zone) (names: List Named)
    (lexical: LexicalNames names):
    Rule zone.holds (namesAfter names) (Ended zone) (NamesEvents names) (Ended zone) :=
  match names, lexical with
    | [], _ => ruleEmpty zone Empty byComputing
    | [{ name, comments }, ..rest], ((isName, fine), others) =>
      ruleConcat zone.holds
        [Doc.text " ", token comments name, namesAfter rest]
        (Ended zone)
        (Ended zone)
        (NamesEvents [{ name, comments }, ..rest])
        (spaceAll zone zone.holds
          [token comments name, namesAfter rest]
          (NamesEvents [{ name, comments }, ..rest])
          (Ended zone)
          (ruleCons zone.holds
            (token comments name)
            [namesAfter rest]
            (Ended zone)
            (Ended zone)
            (Ended zone)
            (TokenAt anyStart comments name)
            (NamesEvents rest)
            (fromEnded zone zone.holds
              (token comments name)
              (TokenAt anyStart comments name)
              (Ended zone)
              (tokenInside zone comments name fine (nameSolid name isName)))
            (ruleLast zone.holds
              (namesAfter rest)
              (Ended zone)
              (Ended zone)
              (NamesEvents rest)
              (namesLay zone rest others))))

--| A parameter group inside its brackets.
theorem groupLays ∀ (zone: Zone) (group: ParameterGroup)
    (lexical: LexicalGroup group):
    Rule zone.holds group.layout (Seated zone) (GroupEvents group) (Ended zone) :=
  match group, lexical with
    | Untyped { name, comments }, (isName, fine) => tokenInside zone comments name fine (nameSolid name isName)
    | Typed names colon annotation, ((isName, fine), lexNames, fineColon, lexType) =>
      let typed := Then (TokenAt anyStart colon ":") (TypeEvents annotation)
      ruleConcat zone.holds
        [
          token names.head.comments names.head.name,
          namesAfter names.tail,
          token colon ":",
          Doc.text " ",
          annotation.layout
        ]
        (Seated zone)
        (Ended zone)
        (GroupEvents (Typed names colon annotation))
        (ruleCons zone.holds
          (token names.head.comments names.head.name)
          [namesAfter names.tail, token colon ":", Doc.text " ", annotation.layout]
          (Seated zone)
          (Ended zone)
          (Ended zone)
          (TokenAt anyStart names.head.comments names.head.name)
          (Then (NamesEvents names.tail) typed)
          (tokenInside zone names.head.comments names.head.name fine (nameSolid names.head.name isName))
          (ruleCons zone.holds
            (namesAfter names.tail)
            [token colon ":", Doc.text " ", annotation.layout]
            (Ended zone)
            (Ended zone)
            (Ended zone)
            (NamesEvents names.tail)
            typed
            (namesLay zone names.tail lexNames)
            (ruleCons zone.holds
              (token colon ":")
              [Doc.text " ", annotation.layout]
              (Ended zone)
              (Ended zone)
              (Ended zone)
              (TokenAt anyStart colon ":")
              (TypeEvents annotation)
              (fromEnded zone zone.holds
                (token colon ":")
                (TokenAt anyStart colon ":")
                (Ended zone)
                (tokenInside zone colon ":" fineColon solidColon))
              (spaceAll zone zone.holds
                [annotation.layout]
                (TypeEvents annotation)
                (Ended zone)
                (ruleLast zone.holds annotation.layout
                  (Ended zone)
                  (Ended zone)
                  (TypeEvents annotation)
                  (fromEnded zone zone.holds annotation.layout
                    (TypeEvents annotation)
                    (Ended zone)
                    (typeLays zone annotation lexType)))))))

--| A parameter group and its comma.
theorem parameterRule ∀ (zone: Zone) (group: ParameterGroup) (comma: Comments)
    (lexical: LexicalGroup group)
    (fineComma: Fine comma):
    Rule zone.holds
      (Doc.concat [group.layout, token comma ","])
      (Seated zone)
      (Then (GroupEvents group) (TokenAt anyStart comma ","))
      (Ended zone) :=
  ruleConcat zone.holds
    [group.layout, token comma ","]
    (Seated zone)
    (Ended zone)
    (Then (GroupEvents group) (TokenAt anyStart comma ","))
    (ruleCons zone.holds group.layout
      [token comma ","]
      (Seated zone)
      (Ended zone)
      (Ended zone)
      (GroupEvents group)
      (TokenAt anyStart comma ",")
      (groupLays zone group lexical)
      (ruleLast zone.holds
        (token comma ",")
        (Ended zone)
        (Ended zone)
        (TokenAt anyStart comma ",")
        (fromEnded zone zone.holds
          (token comma ",")
          (TokenAt anyStart comma ",")
          (Ended zone)
          (tokenInside zone comma "," fineComma solidComma))))

theorem sepsParameters ∀ (parameters: List ParameterGroup)
    (lexical: LexicalParameters parameters)
    (zone: Zone) (indent: Nat) (place: Place) (trace: List Event)
    (next: Place → List Event → Prop) (inside: zone.holds indent)
    (ended: Ended zone place)
    (onward: ∀ (after: Place) (events: List Event) => ParameterEvents parameters events
      → Ended zone after
      → next after (trace ++ events)):
    SepsLay (parameterDocs parameters) indent place trace next :=
  match parameters, lexical, onward with
    | [], _, onward => rewrite <- List.appendNil trace then onward place [] byComputing ended
    | [group], Both lexGroup _, onward =>
      sepSeats zone indent place trace
        (middle between => Lays group.layout indent middle between (after later => SepsLay [] indent after later next))
        inside
        ended
        (middle seated =>
          groupLays zone group lexGroup indent middle trace
            (after later => SepsLay [] indent after later next)
            inside
            seated
            onward)
    | [group, second, ..more], Both lexGroup others, onward =>
      sepSeats zone indent place trace
        (middle between =>
          Lays (Doc.concat [group.layout, token Comments.none ","]) indent middle between (after later =>
            SepsLay (parameterDocs [second, ..more]) indent after later next))
        inside
        ended
        (middle seated =>
          parameterRule zone group Comments.none lexGroup fineNone indent middle trace
            (after later => SepsLay (parameterDocs [second, ..more]) indent after later next)
            inside
            seated
            (after events isParameter reached =>
              sepsParameters
                [second, ..more]
                others
                zone
                indent
                after
                (trace ++ events)
                next
                inside
                reached
                (last rest areParameters met =>
                  rewrite List.appendAssoc trace events rest then
                    onward last
                      (events ++ rest)
                      (thenAssoc
                        (GroupEvents group)
                        (TokenAt anyStart Comments.none ",")
                        (ParameterEvents [second, ..more])
                        events
                        rest
                        isParameter
                        areParameters)
                      met)))

--| A declaration's parameters, as a fill lays them.
theorem fillParameters ∀ (first: ParameterGroup) (rest: List ParameterGroup)
    (lexical: LexicalParameters [first, ..rest]) (zone: Zone):
    FillRule zone (parameterDocs [first, ..rest]) (ParameterEvents [first, ..rest]) :=
  match first, rest, lexical with
    | group, [], Both lexGroup _ => indent place trace next inside seated onward =>
      groupLays zone group lexGroup indent place trace
        (after later => SepsLay [] indent after later next)
        inside
        seated
        onward
    | group, [second, ..more], Both lexGroup others =>
      indent place trace next inside seated onward =>
        parameterRule zone group Comments.none lexGroup fineNone indent place trace
          (after later => SepsLay (parameterDocs [second, ..more]) indent after later next)
          inside
          seated
          (after events isParameter reached =>
            sepsParameters
              [second, ..more]
              others
              zone
              indent
              after
              (trace ++ events)
              next
              inside
              reached
              (last later areParameters met =>
                rewrite List.appendAssoc trace events later then
                  onward last
                    (events ++ later)
                    (thenAssoc
                      (GroupEvents group)
                      (TokenAt anyStart Comments.none ",")
                      (ParameterEvents [second, ..more])
                      events
                      later
                      isParameter
                      areParameters)
                    met))

--| ` takes ` where it was written: nothing where it wasn't.
theorem takesLays ∀ (zone: Zone) (takes: Option Comments)
    (fine: FineTakes takes):
    Rule zone.holds (takesDoc takes) (Ended zone) (TakesEvents zone takes) (Ended zone) :=
  match takes, fine with
    | None, _ => ruleEmpty zone Empty byComputing
    | Some comments, fineTakes => indent place trace next inside ended onward =>
      ruleConcat zone.holds
        [Doc.text " ", token comments "takes", Doc.text " "]
        (Ended zone)
        (Ended zone)
        (Then (TokenAt zone.allows comments "takes") Done)
        (spaceAll zone zone.holds
          [token comments "takes", Doc.text " "]
          (Then (TokenAt zone.allows comments "takes") Done)
          (Ended zone)
          (ruleCons zone.holds
            (token comments "takes")
            [Doc.text " "]
            (Ended zone)
            (Ended zone)
            (Ended zone)
            (TokenAt zone.allows comments "takes")
            Done
            (tokenAfter zone comments "takes" fineTakes solidTakes)
            (spaceAll zone zone.holds [] Done (Ended zone) (allNone zone))))
        indent
        place
        trace
        next
        inside
        ended
        (after events isTakes reached =>
          match isTakes with
            | (front, back, split, holds, none) =>
              let whole: events = front := rewrite split, none then List.appendNil front
              rewrite whole then onward after front holds reached)

--| `fn name (`, with `takes` before `(` if it was written: the keyword
--| starts as `head` says.
theorem openingRule ∀ (zone: Zone) (fnComments: Comments) (name: Text) (nameComments: Comments)
    (takes: Option Comments) (open: Comments)
    (fineFn: Fine fnComments)
    (isName: IsName name)
    (fineName: Fine nameComments)
    (fineTakes: FineTakes takes)
    (fineOpen: Fine open):
    HeadRule zone
      (Doc.concat [token fnComments "fn", Doc.text " ", token nameComments name, takesDoc takes, token open "("])
      fnComments.above
      (head =>
        Then
          (TokenAt head fnComments "fn")
          (Then
            (TokenAt zone.allows nameComments name)
            (Then (TakesEvents zone takes) (TokenAt zone.allows open "(")))) :=
  let afterName := Then (TakesEvents zone takes) (TokenAt zone.allows open "(")
  headCons zone
    (token fnComments "fn")
    [Doc.text " ", token nameComments name, takesDoc takes, token open "("]
    fnComments.above
    (head => TokenAt head fnComments "fn")
    (Then (TokenAt zone.allows nameComments name) afterName)
    (tokenHead zone fnComments "fn" fineFn solidFn)
    (spaceAll zone zone.holds
      [token nameComments name, takesDoc takes, token open "("]
      (Then (TokenAt zone.allows nameComments name) afterName)
      (Ended zone)
      (ruleCons zone.holds
        (token nameComments name)
        [takesDoc takes, token open "("]
        (Ended zone)
        (Ended zone)
        (Ended zone)
        (TokenAt zone.allows nameComments name)
        afterName
        (tokenAfter zone nameComments name fineName (nameSolid name isName))
        (ruleCons zone.holds
          (takesDoc takes)
          [token open "("]
          (Ended zone)
          (Ended zone)
          (Ended zone)
          (TakesEvents zone takes)
          (TokenAt zone.allows open "(")
          (takesLays zone takes fineTakes)
          (ruleLast zone.holds
            (token open "(")
            (Ended zone)
            (Ended zone)
            (TokenAt zone.allows open "(")
            (tokenAfter zone open "(" fineOpen solidOpenParen)))))

--| `) =` and the body after it.
theorem closingLays ∀ (zone: Zone) (close equals: Comments) (bodyDoc: Doc) (body: Body)
    (fineClose: Fine close)
    (fineEquals: Fine equals)
    (bodyRule: BodyRule zone bodyDoc equals.after body)
    (indent: Nat) (place: Place) (trace: List Event) (next: Place → List Event → Prop) (inside: zone.holds indent)
    (seated: Seated zone place)
    (onward: ∀ (reached: Place) (events: List Event) => Then
      (TokenAt anyStart close ")")
      (Then (TokenAt zone.allows equals "=") (BodyEvents zone body))
      events
      → Ended zone reached
      → next reached (trace ++ events)):
    Lays (Doc.concat [closer close ")", Doc.text " ", token equals "="]) indent place trace (after later =>
      LaysAll [bodyDoc] indent after later next) :=
  concatLays
    [closer close ")", Doc.text " ", token equals "="]
    indent
    place
    trace
    (after later => LaysAll [bodyDoc] indent after later next)
    (allAppend
      [closer close ")", Doc.text " ", token equals "="]
      [bodyDoc]
      indent
      place
      trace
      next
      (ruleCons zone.holds
        (closer close ")")
        [Doc.text " ", token equals "=", bodyDoc]
        (Seated zone)
        (Ended zone)
        (Ended zone)
        (TokenAt anyStart close ")")
        (Then (TokenAt zone.allows equals "=") (BodyEvents zone body))
        (closerRule zone close ")" fineClose solidCloseParen)
        (spaceAll zone zone.holds
          [token equals "=", bodyDoc]
          (Then (TokenAt zone.allows equals "=") (BodyEvents zone body))
          (Ended zone)
          (keyLast zone equals "=" bodyDoc body zone.allows
            (Ended zone)
            fineEquals
            solidEquals
            (endedStarts zone equals.above)
            bodyRule))
        indent
        place
        trace
        next
        inside
        seated
        onward))

--| A function declaration (P2), from the start of its line.
--|
--| The opening (`openingRule`), then the parameters as `nestJoined`
--| lays them (none: nothing), then `closingLays`; the events are
--| `DeclarationEvents`' parts in that order.
theorem functionLays ∀ (fnComments: Comments) (name: Text) (nameComments: Comments) (takes: Option Comments)
    (open: Comments) (parameters: List ParameterGroup) (close equals: Comments) (body: Body)
    (lexical: LexicalDeclaration (Function fnComments name nameComments takes open parameters close equals body))
    (trace: List Event) (next: Place → List Event → Prop)
    (onward: ∀ (reached: Place) (events: List Event) => DeclarationEvents
      (Function fnComments name nameComments takes open parameters close equals body)
      events
      → Ended (Deeper 0) reached
      → next reached (trace ++ events)):
    Lays
      (Declaration.layout (Function fnComments name nameComments takes open parameters close equals body))
      0
      (AtStart 0)
      trace
      next :=
  match lexical with
    | (fineFn, isName, fineName, fineTakes, fineOpen, lexParameters, fineClose, fineEquals, lexBody) =>
      let opening :=
        Doc.concat [token fnComments "fn", Doc.text " ", token nameComments name, takesDoc takes, token open "("]
      let closing := Doc.concat [closer close ")", Doc.text " ", token equals "="]
      let bodyRule := afterEqualsLays (Deeper 0) equals body lexBody
      match parameters, lexParameters, onward with
        | [], _, onward =>
          concatLays
            [Doc.concat [opening, closing], body.afterEquals equals]
            0
            (AtStart 0)
            trace
            next
            (concatLays
              [opening, closing]
              0
              (AtStart 0)
              trace
              (after later => LaysAll [body.afterEquals equals] 0 after later next)
              (openingRule
                (Deeper 0)
                fnComments
                name
                nameComments
                takes
                open
                fineFn
                isName
                fineName
                fineTakes
                fineOpen
                (atColumn 0)
                0
                (AtStart 0)
                trace
                (after later =>
                  LaysAll [closing] 0 after later (reached written =>
                    LaysAll [body.afterEquals equals] 0 reached written next))
                (ownHolds 0)
                (ownHolds 0)
                (startAt 0 0 fnComments.above)
                (after events isOpening ended =>
                  closingLays
                    (Deeper 0)
                    close
                    equals
                    (body.afterEquals equals)
                    body
                    fineClose
                    fineEquals
                    bodyRule
                    0
                    after
                    (trace ++ events)
                    next
                    (ownHolds 0)
                    (endedSeated (Deeper 0) after ended)
                    (reached rest isClosing met =>
                      rewrite List.appendAssoc trace events rest then
                        onward reached
                          (events ++ rest)
                          ((
                            events,
                            rest,
                            byComputing,
                            isOpening,
                            (doneThen
                              (Then
                                (TokenAt anyStart close ")")
                                (Then (TokenAt (Deeper 0).allows equals "=") (BodyEvents (Deeper 0) body)))
                              rest
                              isClosing)
                          ))
                          met))))
        | [first, ..others], lexParameters, onward =>
          let listed := Nest 4 (Doc.concat [SoftLine, joined (parameterDocs [first, ..others]) Line])
          concatLays
            [Doc.group (Doc.concat [opening, listed, SoftLine, closing]), body.afterEquals equals]
            0
            (AtStart 0)
            trace
            next
            (concatLays
              [opening, listed, SoftLine, closing]
              0
              (AtStart 0)
              trace
              (after later => LaysAll [body.afterEquals equals] 0 after later next)
              (openingRule
                (Deeper 0)
                fnComments
                name
                nameComments
                takes
                open
                fineFn
                isName
                fineName
                fineTakes
                fineOpen
                (atColumn 0)
                0
                (AtStart 0)
                trace
                (after later =>
                  LaysAll [listed, SoftLine, closing] 0 after later (reached written =>
                    LaysAll [body.afterEquals equals] 0 reached written next))
                (ownHolds 0)
                (ownHolds 0)
                (startAt 0 0 fnComments.above)
                (after events isOpening ended =>
                  nestJoined
                    (Deeper 0)
                    4
                    (parameterDocs [first, ..others])
                    (ParameterEvents [first, ..others])
                    (fillParameters first others lexParameters (Deeper 0))
                    0
                    after
                    (trace ++ events)
                    (middle between =>
                      LaysAll [SoftLine, closing] 0 middle between (reached written =>
                        LaysAll [body.afterEquals equals] 0 reached written next))
                    (ownHolds 0)
                    ended
                    (listEnd listedEvents areParameters listEnded =>
                      softSeats
                        (Deeper 0)
                        0
                        listEnd
                        ((trace ++ events) ++ listedEvents)
                        (middle between =>
                          LaysAll [closing] 0 middle between (reached written =>
                            LaysAll [body.afterEquals equals] 0 reached written next))
                        (ownHolds 0)
                        listEnded
                        (middle seated =>
                          closingLays
                            (Deeper 0)
                            close
                            equals
                            (body.afterEquals equals)
                            body
                            fineClose
                            fineEquals
                            bodyRule
                            0
                            middle
                            ((trace ++ events) ++ listedEvents)
                            next
                            (ownHolds 0)
                            seated
                            (reached rest isClosing met =>
                              rewrite List.appendAssoc (trace ++ events) listedEvents rest,
                                  List.appendAssoc trace events (listedEvents ++ rest) then
                                onward reached
                                  (events ++ (listedEvents ++ rest))
                                  ((
                                    events,
                                    (listedEvents ++ rest),
                                    byComputing,
                                    isOpening,
                                    listedEvents,
                                    rest,
                                    byComputing,
                                    areParameters,
                                    isClosing
                                  ))
                                  met))))))

--| A declaration, from the start of its line at column 0.
theorem declarationLays ∀ (declaration: Declaration)
    (lexical: LexicalDeclaration declaration)
    (trace: List Event) (next: Place → List Event → Prop)
    (onward: ∀ (reached: Place) (events: List Event) => DeclarationEvents declaration events
      → Ended (Deeper 0) reached
      → next reached (trace ++ events)):
    Lays declaration.layout 0 (AtStart 0) trace next :=
  match declaration, lexical, onward with
    | Function fnComments name nameComments takes open parameters close equals body, lexical, onward =>
      functionLays fnComments name nameComments takes open parameters close equals body lexical trace next onward
    | Value letComments name nameComments equals body, Both fineLet
        (Both isName (Both fineName (Both fineEquals lexBody))), onward =>
      bindingRule
        (Deeper 0)
        letComments
        name
        nameComments
        equals
        body
        fineLet
        isName
        fineName
        fineEquals
        (afterEqualsLays (Deeper 0) equals body lexBody)
        (atColumn 0)
        0
        (AtStart 0)
        trace
        next
        (ownHolds 0)
        (ownHolds 0)
        (startAt 0 0 letComments.above)
        onward
    | DeclarationNote comment, fine, onward =>
      wordLays 0 comment.text
        (AtStart 0)
        trace
        next
        (commentSolid comment.text fine)
        (onward (Mid 0) [{ word = comment.text, start = Some 0 }] byComputing (ownHolds 0))

--| A file's declarations (P9), from the start of the first: each starts
--| its line at column 0.
theorem declarationsLay ∀ (first: Spaced Declaration) (rest: List (Spaced Declaration))
    (lexical: LexicalDeclarations [first, ..rest])
    (trace: List Event) (next: Place → List Event → Prop)
    (onward: ∀ (reached: Place) (events: List Event) => DeclarationsEvents [first, ..rest] events
      → Ended (Deeper 0) reached
      → next reached (trace ++ events)):
    LaysAll (declarationLines 0 [first, ..rest]) 0 (AtStart 0) trace next :=
  match first, lexical, onward with
    | { blankBefore, line }, Both lexLine others, onward =>
      concatLays
        [lineStart 0 blankBefore, line.layout]
        0
        (AtStart 0)
        trace
        (after later => LaysAll (declarationLines (0 + 1) rest) 0 after later next)
        (declarationLays line lexLine trace
          (after later =>
            LaysAll [] 0 after later (reached written =>
              LaysAll (declarationLines (0 + 1) rest) 0 reached written next))
          (reached events isLine ended =>
            laterDeclarationsLay 0 rest others reached (trace ++ events) next ended (last later areLines met =>
              rewrite List.appendAssoc trace events later then
                onward last (events ++ later) ((events, later, byComputing, isLine, areLines)) met)))

--| A file's declarations after its first, the first of these the
--| `index + 1`th: each on a new line at column 0, after a blank line if
--| it has one before it.
theorem laterDeclarationsLay ∀ (index: Nat) (lines: List (Spaced Declaration))
    (lexical: LexicalDeclarations lines)
    (place: Place) (trace: List Event) (next: Place → List Event → Prop)
    (ended: Ended (Deeper 0) place)
    (onward: ∀ (reached: Place) (events: List Event) => LaterDeclarations lines events
      → Ended (Deeper 0) reached
      → next reached (trace ++ events)):
    LaysAll (declarationLines (index + 1) lines) 0 place trace next :=
  match lines, lexical, onward with
    | [], _, onward => rewrite <- List.appendNil trace then onward place [] byComputing ended
    | [{ blankBefore, line }, ..more], Both lexLine others, onward =>
      concatLays
        [lineStart (index + 1) blankBefore, line.layout]
        0
        place
        trace
        (after later => LaysAll (declarationLines (index + 1 + 1) more) 0 after later next)
        (laterStart index blankBefore 0 place trace
          (after later =>
            LaysAll [line.layout] 0 after later (reached written =>
              LaysAll (declarationLines (index + 1 + 1) more) 0 reached written next))
          (endedMid (Deeper 0) place ended)
          (declarationLays line lexLine
            (trace ++ blankEvents blankBefore)
            (after later =>
              LaysAll [] 0 after later (reached written =>
                LaysAll (declarationLines (index + 1 + 1) more) 0 reached written next))
            (reached events isLine met =>
              laterDeclarationsLay
                (index + 1)
                more
                others
                reached
                ((trace ++ blankEvents blankBefore) ++ events)
                next
                met
                (last later areLines done =>
                  rewrite List.appendAssoc (trace ++ blankEvents blankBefore) events later,
                      List.appendAssoc trace (blankEvents blankBefore) (events ++ later) then
                    onward last
                      (blankEvents blankBefore ++ (events ++ later))
                      (((events ++ later), byComputing, events, later, byComputing, isLine, areLines))
                      done))))

--| Every way a file's layout may print lays the file's events.
theorem fileLays ∀ (file: SourceFile)
    (lexical: LexicalFile file)
    (next: Place → List Event → Prop)
    (onward: ∀ (reached: Place) (events: List Event) => FileEvents file events → next reached events):
    Lays file.layout 0 (AtStart 0) [] next :=
  match file, lexical, onward with
    | { declarations = [] }, _, onward => onward (AtStart 0) [] byComputing
    | { declarations = [first, ..rest] }, lexical, onward =>
      concatLays
        [Doc.concat (declarationLines 0 [first, ..rest]), HardLine]
        0
        (AtStart 0)
        []
        next
        (concatLays
          (declarationLines 0 [first, ..rest])
          0
          (AtStart 0)
          []
          (after later => LaysAll [HardLine] 0 after later next)
          (declarationsLay first rest lexical []
            (after later => LaysAll [HardLine] 0 after later next)
            (reached events areLines ended =>
              ((endedMid (Deeper 0) reached ended), (Inr (onward (AtStart 0) events areLines))))))

--| Where the rules put every word of a file that satisfies what the
--| parser guarantees: at every width, the file's events are a trace the
--| printed pieces' words, each with where it starts its line if it does,
--| are in order, but that a trailing comment comes after the closers
--| printed on its line (`Tucks`).
theorem printedEvents ∀ (file: SourceFile) (width: Nat)
    (lexical: LexicalFile file):
    ∃ (laid: List Event) => FileEvents file laid ∧ Tucks laid (eventsOf (printedPieces file.layout width).reverse) :=
  match printLays
    (place events => FileEvents file events)
    file.layout
    width
    (fileLays file lexical (place events => FileEvents file events) (reached events holds => holds)) with
    | (place, laid, holds, tucks) => (laid, holds, tucks)
