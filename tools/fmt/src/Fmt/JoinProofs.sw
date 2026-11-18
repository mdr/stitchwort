--| The rules' half of `printLexes1` (docs/proposals/self-hosted-fmt-s1-sketch.md §1.5, ticket 18b): the document
--| the rules build joins (`Joins (Follows kinds)`), so by `printedLexes` its printed text lexes to its pieces.
--|
--| Each rule is a triple (`Passes kinds doc pre post`): from every edge that satisfies `pre`, the document joins
--| and leaves an edge that satisfies `post`. What may follow a token is decided by the first character of the next
--| text, and a space, a bracket, a comma or a `:` may follow any token (`followsStops`). So the edges need say little:
--| the line ends with a token or nothing, never with a comment (`Token`); a trailing comment waits only where the
--| tree says the code before ends with one (`Around.before`, `Expr.trails`); and where the next text is glued to the
--| last, as after an opening bracket or a prefix operator, that it may follow it.

namespace Fmt.JoinProofs
import Std (Bool, Char, DecEq, Doc, Eq, List, Nat, Option, Text, Void, byDecision)
import Std.Doc (..)
import Std.Doc.Proofs (..)
import Syntax (Expr, Tok, Word, isWordChar)
import Syntax.Proofs (MayFollow)
import Fmt (..)
import Fmt.PrintLexProofs (Follows)
import Fmt.SpellProofs (..)
import Syntax (Note)

-- What may follow a token.

--| A text that isn't a comment.
def Token (text: Text): Prop := text.startsWith "--" = False

--| A character no token goes on with: not part of a name or number, nor of a longer operator, nor a `.`.
def Stops (char: Char): Prop :=
  isWordChar char = False
    ∧ char.isAsciiDigit = False
    ∧ char ≠ '='
    ∧ char ≠ '>'
    ∧ char ≠ '+'
    ∧ char ≠ '-'
    ∧ char ≠ '.'
    ∧ char ≠ 'e'
    ∧ char ≠ 'E'

theorem takeWhileStops ∀ (passes: Char → Bool) (rest: List Char) (first: Char)
    (head: rest.head = Some first)
    (fails: passes first = False):
    rest.takeWhile passes = [] :=
  match rest, head with
    | [], head => (Option.someNotNone first head.flipped).impossible
    | [other, ..more], head => rewrite Option.someInjective head, fails

theorem headDiffers ∀ (rest: List Char) (first other: Char)
    (head: rest.head = Some first)
    (differs: first ≠ other):
    rest.head ≠ Some other :=
  same => differs (Option.someInjective (Eq.trans head.flipped same))

--| A token may be followed by a text that starts with a character no token goes on with.
--|
--| Proof idea: One case per kind with a condition; each is a character the head isn't, or a run of name or digit
--| characters that the head stops at once.
theorem mayFollowStops ∀ (kind: Tok) (text: Text) (rest: List Char) (first: Char)
    (head: rest.head = Some first)
    (stops: Stops first):
    MayFollow kind text rest :=
  match stops with
    | (word, digit, notEquals, notGreater, notPlus, notMinus, notDot, notE, notBigE) =>
      let noWord := takeWhileStops isWordChar rest first head word
      let noDigit := takeWhileStops Char.isAsciiDigit rest first head digit
      match kind with
        | Colon => headDiffers rest first '=' head notEquals
        | Equals => (headDiffers rest first '=' head notEquals, headDiffers rest first '>' head notGreater)
        | Plus => headDiffers rest first '+' head notPlus
        | Minus => (headDiffers rest first '-' head notMinus, headDiffers rest first '>' head notGreater)
        | Lt => (headDiffers rest first '=' head notEquals, headDiffers rest first '-' head notMinus)
        | Gt => headDiffers rest first '=' head notEquals
        | Bang => bang => (headDiffers rest first '=' head notEquals, (run => (rewrite noWord at run then cases)))
        | KwDef => (noWord, headDiffers rest first '.' head notDot)
        | Lower => (noWord, headDiffers rest first '.' head notDot)
        | Upper => (noWord, headDiffers rest first '.' head notDot)
        | Num => (
          noDigit,
          headDiffers rest first '.' head notDot,
          headDiffers rest first 'e' head notE,
          headDiffers rest first 'E' head notBigE
        )
        | Float => (noDigit, headDiffers rest first 'e' head notE, headDiffers rest first 'E' head notBigE)
        | other => byComputing

theorem stopsSpace: Stops ' ' :=
  (byComputing, byComputing, byDecision, byDecision, byDecision, byDecision, byDecision, byDecision, byDecision)

theorem stopsParen: Stops ')' :=
  (byComputing, byComputing, byDecision, byDecision, byDecision, byDecision, byDecision, byDecision, byDecision)

theorem stopsSquare: Stops ']' :=
  (byComputing, byComputing, byDecision, byDecision, byDecision, byDecision, byDecision, byDecision, byDecision)

theorem stopsBrace: Stops '}' :=
  (byComputing, byComputing, byDecision, byDecision, byDecision, byDecision, byDecision, byDecision, byDecision)

theorem stopsComma: Stops ',' :=
  (byComputing, byComputing, byDecision, byDecision, byDecision, byDecision, byDecision, byDecision, byDecision)

theorem stopsColon: Stops ':' :=
  (byComputing, byComputing, byDecision, byDecision, byDecision, byDecision, byDecision, byDecision, byDecision)

--| A token may be followed by a text that starts with a character no token goes on with.
theorem followsStops ∀ (kinds: Text → Tok) (word next: Text) (first: Char)
    (token: Token word)
    (head: next.toList.head = Some first)
    (stops: Stops first):
    Follows kinds word next :=
  (token, mayFollowStops (kinds word) word next.toList first head stops)

theorem followsSpace ∀ (kinds: Text → Tok) (word: Text) (token: Token word): Follows kinds word " " :=
  followsStops kinds word " " ' ' token byComputing stopsSpace

--| The texts a `Closing` writes: closers and the comma.
def Closes (text: Text): Prop := text = ")" ∨ text = "]" ∨ text = "}" ∨ text = ","

theorem followsCloser ∀ (kinds: Text → Tok) (word text: Text)
    (token: Token word)
    (closes: Closes text):
    Follows kinds word text :=
  match closes with
    | Inl same => rewrite same then followsStops kinds word ")" ')' token byComputing stopsParen
    | Inr (Inl same) => rewrite same then followsStops kinds word "]" ']' token byComputing stopsSquare
    | Inr (Inr (Inl same)) => rewrite same then followsStops kinds word "}" '}' token byComputing stopsBrace
    | Inr (Inr (Inr same)) => rewrite same then followsStops kinds word "," ',' token byComputing stopsComma

theorem followsToken ∀ (kinds: Text → Tok) (word next: Text) (follows: Follows kinds word next): Token word :=
  follows.left

-- The edges.

--| Where an element whose first text is `first` starts: the line ends with nothing or with a token `first` may
--| follow; a trailing comment waits only if the code before ends with one (`before`).
def Ready (kinds: Text → Tok) (before: Bool) (first: Text) (edge: Edge): Prop := match edge with
  | Plain None => True
  | Plain (Some word) => Follows kinds word first
  | Waiting None => before = True
  | Waiting (Some word) => before = True ∧ Token word

--| Where an element ends: the line ends with nothing or with a token; a trailing comment waits only if the element
--| ends with one (`trails`).
def Ended (trails: Bool) (edge: Edge): Prop := match edge with
  | Plain None => True
  | Plain (Some word) => Token word
  | Waiting None => trails = True
  | Waiting (Some word) => trails = True ∧ Token word

--| After a space or a line break: nothing on the line yet, or a comment waiting only if `trails`.
def Gapped (trails: Bool) (edge: Edge): Prop := match edge with
  | Plain None => True
  | Plain (Some word) => False
  | Waiting None => trails = True
  | Waiting (Some word) => trails = True ∧ Token word

--| Straight after the token `text`, a comment after it waiting only if `trails`.
def Left (text: Text) (trails: Bool) (edge: Edge): Prop := match edge with
  | Plain (Some word) => word = text
  | Waiting (Some word) => word = text ∧ trails = True
  | _ => False

--| After an opening bracket: anything may come next.
def Free (kinds: Text → Tok) (trails: Bool) (edge: Edge): Prop := match edge with
  | Plain None => True
  | Plain (Some word) => ∀ (next: Text) => Follows kinds word next
  | Waiting None => trails = True
  | Waiting (Some word) => trails = True ∧ Token word

theorem gappedReady ∀ (kinds: Text → Tok) (trails: Bool) (first: Text) (edge: Edge)
    (gapped: Gapped trails edge):
    Ready kinds trails first edge :=
  match edge, gapped with
    | Plain None, _ => byComputing
    | Waiting None, waits => waits
    | Waiting (Some word), waits => waits

theorem gappedEnded ∀ (trails: Bool) (edge: Edge) (gapped: Gapped trails edge): Ended trails edge :=
  match edge, gapped with
    | Plain None, _ => byComputing
    | Waiting None, waits => waits
    | Waiting (Some word), waits => waits

theorem freeReady ∀ (kinds: Text → Tok) (trails: Bool) (first: Text) (edge: Edge)
    (free: Free kinds trails edge):
    Ready kinds trails first edge :=
  match edge, free with
    | Plain None, _ => byComputing
    | Plain (Some word), any => any first
    | Waiting None, waits => waits
    | Waiting (Some word), waits => waits

theorem freeEnded ∀ (kinds: Text → Tok) (trails: Bool) (edge: Edge) (free: Free kinds trails edge): Ended trails edge :=
  match edge, free with
    | Plain None, _ => byComputing
    | Plain (Some word), any => (any " ").left
    | Waiting None, waits => waits
    | Waiting (Some word), waits => waits

theorem readyEnded ∀ (kinds: Text → Tok) (before: Bool) (first: Text) (edge: Edge)
    (ready: Ready kinds before first edge):
    Ended before edge :=
  match edge, ready with
    | Plain None, _ => byComputing
    | Plain (Some word), follows => follows.left
    | Waiting None, waits => waits
    | Waiting (Some word), waits => waits

theorem leftEnded ∀ (text: Text) (trails: Bool)
    (token: Token text) (edge: Edge)
    (left: Left text trails edge):
    Ended trails edge :=
  match edge, left with
    | Plain None, never => (Bool.falseNotTrue never).impossible
    | Waiting None, never => (Bool.falseNotTrue never).impossible
    | Plain (Some word), same => rewrite same then token
    | Waiting (Some word), (same, waits) => (waits, (rewrite same then token))

--| An ended element is ready for a closer or comma, and for a space.
theorem endedReadyCloser ∀ (kinds: Text → Tok) (trails: Bool) (text: Text)
    (closes: Closes text) (edge: Edge)
    (ended: Ended trails edge):
    Ready kinds trails text edge :=
  match edge, ended with
    | Plain None, _ => byComputing
    | Plain (Some word), token => followsCloser kinds word text token closes
    | Waiting None, waits => waits
    | Waiting (Some word), waits => waits

theorem endedWeaker ∀ (trails trails': Bool)
    (implies: trails = True → trails' = True) (edge: Edge)
    (ended: Ended trails edge):
    Ended trails' edge :=
  match edge, ended with
    | Plain None, _ => byComputing
    | Plain (Some word), token => token
    | Waiting None, waits => implies waits
    | Waiting (Some word), (waits, token) => (implies waits, token)

theorem readyWeaker ∀ (kinds: Text → Tok) (before before': Bool) (first: Text)
    (implies: before = True → before' = True) (edge: Edge)
    (ready: Ready kinds before first edge):
    Ready kinds before' first edge :=
  match edge, ready with
    | Plain None, _ => byComputing
    | Plain (Some word), follows => follows
    | Waiting None, waits => implies waits
    | Waiting (Some word), (waits, token) => (implies waits, token)

-- The triples.

--| From every edge that satisfies `pre`, `doc` joins, and leaves an edge that satisfies `post`.
def Passes (kinds: Text → Tok) (doc: Doc) (pre post: Edge → Prop): Prop :=
  ∀ (edge: Edge) (next: Edge → Prop) => pre edge
    → (∀ (after: Edge) => post after → next after)
    → Joins (Follows kinds) doc edge next

def PassesAll (kinds: Text → Tok) (docs: List Doc) (pre post: Edge → Prop): Prop :=
  ∀ (edge: Edge) (next: Edge → Prop) => pre edge
    → (∀ (after: Edge) => post after → next after)
    → JoinsAll (Follows kinds) docs edge next

theorem passesFrom ∀ (kinds: Text → Tok) (doc: Doc) (pre weaker post: Edge → Prop)
    (passes: Passes kinds doc pre post) (implies: ∀ (edge: Edge) => weaker edge → pre edge):
    Passes kinds doc weaker post :=
  edge next holds after => passes edge next (implies edge holds) after

theorem passesTo ∀ (kinds: Text → Tok) (doc: Doc) (pre post weaker: Edge → Prop)
    (passes: Passes kinds doc pre post) (implies: ∀ (edge: Edge) => post edge → weaker edge):
    Passes kinds doc pre weaker :=
  edge next holds after => passes edge next holds (left reached => after left (implies left reached))

theorem allFrom ∀ (kinds: Text → Tok) (docs: List Doc) (pre weaker post: Edge → Prop)
    (passes: PassesAll kinds docs pre post) (implies: ∀ (edge: Edge) => weaker edge → pre edge):
    PassesAll kinds docs weaker post :=
  edge next holds after => passes edge next (implies edge holds) after

theorem allTo ∀ (kinds: Text → Tok) (docs: List Doc) (pre post weaker: Edge → Prop)
    (passes: PassesAll kinds docs pre post) (implies: ∀ (edge: Edge) => post edge → weaker edge):
    PassesAll kinds docs pre weaker :=
  edge next holds after => passes edge next holds (left reached => after left (implies left reached))

theorem passesNil ∀ (kinds: Text → Tok) (pre post: Edge → Prop) (implies: ∀ (edge: Edge) => pre edge → post edge):
    PassesAll kinds [] pre post :=
  edge next holds after => after edge (implies edge holds)

theorem passesCons ∀ (kinds: Text → Tok) (doc: Doc) (docs: List Doc) (pre middle post: Edge → Prop)
    (first: Passes kinds doc pre middle)
    (rest: PassesAll kinds docs middle post):
    PassesAll kinds [doc, ..docs] pre post :=
  edge next holds after =>
    first edge (between => JoinsAll (Follows kinds) docs between next) holds (between reached =>
      rest between next reached after)

--| Documents one after another, then more: the first lot, then the second from where the first leaves off.
theorem joinsAllAppend ∀ (follows: Text → Text → Prop) (front back: List Doc) (edge: Edge) (next: Edge → Prop)
    (joins: JoinsAll follows front edge (between => JoinsAll follows back between next)):
    JoinsAll follows (front ++ back) edge next :=
  match front, joins with
    | [], joins => joins
    | [doc, ..rest], joins =>
      joinsWeaker follows doc edge
        (between => JoinsAll follows rest between (later => JoinsAll follows back later next))
        (between => JoinsAll follows (rest ++ back) between next)
        (between later => joinsAllAppend follows rest back between next later)
        joins

theorem passesAppend ∀ (kinds: Text → Tok) (front back: List Doc) (pre middle post: Edge → Prop)
    (first: PassesAll kinds front pre middle)
    (second: PassesAll kinds back middle post):
    PassesAll kinds (front ++ back) pre post :=
  edge next holds after =>
    joinsAllAppend
      (Follows kinds)
      front
      back
      edge
      next
      (first edge (between => JoinsAll (Follows kinds) back between next) holds (between reached =>
        second between next reached after))

theorem passesLast ∀ (kinds: Text → Tok) (doc: Doc) (pre post: Edge → Prop)
    (only: Passes kinds doc pre post):
    PassesAll kinds [doc] pre post :=
  passesCons kinds doc [] pre post post only (passesNil kinds post post (edge holds => holds))

theorem emptyJoins ∀ (kinds: Text → Tok) (doc: Doc) (edge: Edge) (next: Edge → Prop)
    (empty: doc.isEmpty = True)
    (joins: Joins (Follows kinds) doc edge next):
    next edge :=
  match doc, empty, joins with | Doc.Nothing, _, joins => joins

theorem filterJoins ∀ (kinds: Text → Tok) (docs: List Doc) (edge: Edge) (next: Edge → Prop)
    (joins: JoinsAll (Follows kinds) docs edge next):
    JoinsAll (Follows kinds) (docs.filter (doc => not doc.isEmpty)) edge next :=
  match docs, joins with
    | [], joins => joins
    | [doc, ..rest], joins =>
      match empty: doc.isEmpty with
        | True =>
          filterJoins kinds rest edge next
            (emptyJoins kinds doc edge (between => JoinsAll (Follows kinds) rest between next) empty joins)
        | False =>
          joinsWeaker
            (Follows kinds)
            doc
            edge
            (between => JoinsAll (Follows kinds) rest between next)
            (between => JoinsAll (Follows kinds) (rest.filter (doc => not doc.isEmpty)) between next)
            (between later => filterJoins kinds rest between next later)
            joins

--| `Doc.concat` joins as the documents one after another.
theorem concatJoins ∀ (kinds: Text → Tok) (docs: List Doc) (edge: Edge) (next: Edge → Prop)
    (joins: JoinsAll (Follows kinds) docs edge next):
    Joins (Follows kinds) (Doc.concat docs) edge next :=
  let kept := filterJoins kinds docs edge next joins
  match found: docs.filter (doc => not doc.isEmpty) with
    | [] => kept
    | [only] =>
      joinsWeaker
        (Follows kinds)
        only
        edge
        (between => JoinsAll (Follows kinds) [] between next)
        next
        (between reached => reached)
        kept
    | [first, second, ..rest] => kept

theorem passesConcat ∀ (kinds: Text → Tok) (docs: List Doc) (pre post: Edge → Prop)
    (each: PassesAll kinds docs pre post):
    Passes kinds (Doc.concat docs) pre post :=
  edge next holds after => concatJoins kinds docs edge next (each edge next holds after)

theorem passesConcatOf ∀ (kinds: Text → Tok) (docs: List Doc) (pre post: Edge → Prop)
    (each: PassesAll kinds docs pre post):
    Passes kinds (Concat docs) pre post :=
  edge next holds after => each edge next holds after

theorem passesTwo ∀ (kinds: Text → Tok) (first second: Doc) (pre middle post: Edge → Prop)
    (one: Passes kinds first pre middle)
    (other: Passes kinds second middle post):
    PassesAll kinds [first, second] pre post :=
  passesCons kinds first [second] pre middle post one (passesLast kinds second middle post other)

-- The document's constructors.

theorem passesNothing ∀ (kinds: Text → Tok) (pre: Edge → Prop): Passes kinds Doc.Nothing pre pre :=
  edge next holds after => after edge holds

theorem passesBreakParent ∀ (kinds: Text → Tok) (pre: Edge → Prop): Passes kinds BreakParent pre pre :=
  edge next holds after => after edge holds

theorem passesBlank ∀ (kinds: Text → Tok) (pre: Edge → Prop): Passes kinds Blank pre pre := edge next holds after =>
  after edge holds

theorem passesMark ∀ (kinds: Text → Tok) (key: Nat) (pre: Edge → Prop): Passes kinds (Mark key) pre pre :=
  edge next holds after => after edge holds

theorem passesHard ∀ (kinds: Text → Tok) (pre post: Edge → Prop) (fresh: post (Plain None)):
    Passes kinds HardLine pre post :=
  edge next holds after => after (Plain None) fresh

theorem passesCloserLine ∀ (kinds: Text → Tok) (key: Nat) (pre post: Edge → Prop) (fresh: post (Plain None)):
    Passes kinds (CloserLine key) pre post :=
  edge next holds after => after (Plain None) fresh

theorem passesNest ∀ (kinds: Text → Tok) (indent: Nat) (inner: Doc) (pre post: Edge → Prop)
    (passes: Passes kinds inner pre post):
    Passes kinds (Nest indent inner) pre post :=
  passes

theorem passesAlign ∀ (kinds: Text → Tok) (inner: Doc) (pre post: Edge → Prop)
    (passes: Passes kinds inner pre post):
    Passes kinds (Align inner) pre post :=
  passes

theorem passesGroup ∀ (kinds: Text → Tok) (inner: Doc) (hard: Bool) (pre post: Edge → Prop)
    (passes: Passes kinds inner pre post):
    Passes kinds (Group inner hard) pre post :=
  passes

theorem passesIdGroup ∀ (kinds: Text → Tok) (id: Nat) (inner: Doc) (hard: Bool) (pre post: Edge → Prop)
    (passes: Passes kinds inner pre post):
    Passes kinds (IdGroup id inner hard) pre post :=
  passes

theorem passesFlatten ∀ (kinds: Text → Tok) (inner: Doc) (pre post: Edge → Prop)
    (passes: Passes kinds inner pre post):
    Passes kinds (Flatten inner) pre post :=
  passes

theorem passesIfBroken ∀ (kinds: Text → Tok) (id: Nat) (broken flat: Doc) (pre post: Edge → Prop)
    (brokenPasses: Passes kinds broken pre post)
    (flatPasses: Passes kinds flat pre post):
    Passes kinds (IfBroken id broken flat) pre post :=
  edge next holds after => (brokenPasses edge next holds after, flatPasses edge next holds after)

theorem passesOneLineBelow ∀ (kinds: Text → Tok) (inner: Doc) (pre post: Edge → Prop)
    (passes: Passes kinds inner (edge => edge = Plain None) post):
    Passes kinds (OneLineBelow inner) pre post :=
  edge next holds after => passes (Plain None) next byComputing after

--| Each option of a choice, from the same edges to the same edges.
def EachPasses (kinds: Text → Tok) (pre post: Edge → Prop): List Doc → Prop
  | [] => True
  | [option, ..others] => Passes kinds option pre post ∧ EachPasses kinds pre post others

theorem optionsPass ∀ (kinds: Text → Tok) (options: List Doc) (pre post: Edge → Prop)
    (each: EachPasses kinds pre post options)
    (keeps: ∀ (edge: Edge) => pre edge → post edge) (edge: Edge) (next: Edge → Prop)
    (holds: pre edge) (after: ∀ (left: Edge) => post left → next left):
    OptionsJoin (Follows kinds) options edge next :=
  match options, each with
    | [], _ => after edge (keeps edge holds)
    | [last], (passes, _) => passes edge next holds after
    | [option, second, ..others], (passes, rest) =>
      (passes edge next holds after, optionsPass kinds [second, ..others] pre post rest keeps edge next holds after)

--| A choice whose options all pass, from edges where doing nothing would too.
theorem passesChoice ∀ (kinds: Text → Tok) (options: List Doc) (pre post: Edge → Prop)
    (each: EachPasses kinds pre post options) (keeps: ∀ (edge: Edge) => pre edge → post edge):
    Passes kinds (Choice options) pre post :=
  edge next holds after => optionsPass kinds options pre post each keeps edge next holds after

--| A displaced element passes if its contents do from where they start, and from a fresh line where a comment
--| waits.
theorem passesDisplaced ∀ (kinds: Text → Tok) (inner: Doc) (pre post: Edge → Prop)
    (passes: Passes kinds inner pre post) (fresh: pre (Plain None)):
    Passes kinds (Displaced inner) pre post :=
  edge next holds after =>
    match edge with
      | Plain touching => passes (Plain touching) next holds after
      | Waiting touching => (passes (Waiting touching) next holds after, passes (Plain None) next fresh after)

--| `LineStart` and `LineStartHere`: a line break, or where a line starts the edge as it was.
theorem passesStart ∀ (kinds: Text → Tok) (pre post: Edge → Prop)
    (keeps: ∀ (touching: Option Text) => pre (Waiting touching) → post (Waiting touching)) (fresh: post (Plain None)):
    Passes kinds LineStart pre post :=
  edge next holds after =>
    match edge with
      | Plain touching => after (Plain None) fresh
      | Waiting touching => (after (Waiting touching) (keeps touching holds), after (Plain None) fresh)

theorem passesStartHere ∀ (kinds: Text → Tok) (pre post: Edge → Prop)
    (keeps: ∀ (touching: Option Text) => pre (Waiting touching) → post (Waiting touching)) (fresh: post (Plain None)):
    Passes kinds LineStartHere pre post :=
  edge next holds after =>
    match edge with
      | Plain touching => after (Plain None) fresh
      | Waiting touching => (after (Waiting touching) (keeps touching holds), after (Plain None) fresh)

--| A `SoftLine`: nothing, or a line break.
theorem passesSoft ∀ (kinds: Text → Tok) (pre post: Edge → Prop)
    (keeps: ∀ (edge: Edge) => pre edge → post edge) (fresh: post (Plain None)):
    Passes kinds SoftLine pre post :=
  edge next holds after =>
    match edge with
      | Plain touching => (after (Plain touching) (keeps (Plain touching) holds), after (Plain None) fresh)
      | Waiting touching => (after (Waiting touching) (keeps (Waiting touching) holds), after (Plain None) fresh)

--| A `Line` after an element: a space or a line break.
theorem passesLine ∀ (kinds: Text → Tok) (trails: Bool): Passes kinds Line (Ended trails) (Gapped trails) :=
  edge next holds after =>
    match edge, holds with
      | Plain None, _ => (byComputing, after (Plain None) byComputing)
      | Plain (Some word), token => (followsSpace kinds word token, after (Plain None) byComputing)
      | Waiting None, waits => (after (Waiting None) waits, after (Plain None) byComputing)
      | Waiting (Some word), waits => (after (Waiting (Some word)) waits, after (Plain None) byComputing)

--| A space after an element.
theorem passesSpace ∀ (kinds: Text → Tok) (trails: Bool): Passes kinds (Doc.text " ") (Ended trails) (Gapped trails) :=
  edge next holds after =>
    match edge, holds with
      | Plain None, _ => (byComputing, after (Plain None) byComputing)
      | Plain (Some word), token => (followsSpace kinds word token, after (Plain None) byComputing)
      | Waiting None, waits => after (Waiting None) waits
      | Waiting (Some word), waits => after (Waiting (Some word)) waits

-- Texts, closers and comments.

theorem solidSpaces ∀ (text: Text) (solid: isLayout text = False): text.all (char => char == ' ') = False :=
  match spaces: text.all (char => char == ' ') with | False => byComputing

theorem solidTouch ∀ (text: Text) (solid: isLayout text = False): textTouch text = Some text := rewrite solid

theorem solidGap ∀ (text: Text) (solid: isLayout text = False): gapOr text = text := rewrite solidSpaces text solid

--| A token's text, from where it may stand: the line then ends with it.
theorem textPasses ∀ (kinds: Text → Tok) (before: Bool) (text: Text)
    (solid: isLayout text = False):
    Passes kinds (Doc.text text) (Ready kinds before text) (edge => edge = Plain (Some text)) :=
  edge next ready after =>
    let filled := wordFilled text solid
    let spaces := solidSpaces text solid
    let touched: next (Plain (textTouch text)) :=
      rewrite solidTouch text solid then after (Plain (Some text)) byComputing
    match edge, ready with
      | Plain None, _ => rewrite filled then (byComputing, touched)
      | Plain (Some word), follows => rewrite filled then ((rewrite solidGap text solid then follows), touched)
      | Waiting touching, _ => rewrite filled, solidTouch text solid, spaces then after (Plain (Some text)) byComputing

theorem closesToken ∀ (text: Text) (closes: Closes text): Token text := match closes with
  | Inl same => rewrite same
  | Inr (Inl same) => rewrite same
  | Inr (Inr (Inl same)) => rewrite same
  | Inr (Inr (Inr same)) => rewrite same

theorem closesSolid ∀ (text: Text) (closes: Closes text): isLayout text = False := match closes with
  | Inl same => rewrite same
  | Inr (Inl same) => rewrite same
  | Inr (Inr (Inl same)) => rewrite same
  | Inr (Inr (Inr same)) => rewrite same

theorem closerCloses ∀ (text: Text) (closer: isCloserText text = True): Closes text := match paren: text == ")" with
  | True => Inl (DecEq.sound paren)
  | False =>
    match square: text == "]" with
      | True => Inr (Inl (DecEq.sound square))
      | False =>
        match brace: text == "}" with
          | True => Inr (Inr (Inl (DecEq.sound brace)))

theorem closerNotComma ∀ (text: Text) (closer: isCloserText text = True): (text == ",") = False :=
  match closerCloses text closer with
    | Inl same => rewrite same
    | Inr (Inl same) => rewrite same
    | Inr (Inr (Inl same)) => rewrite same
    | Inr (Inr (Inr same)) => rewrite same at closer then cases

--| A closer or comma: from where it may stand, the line ends with it, and a comment waiting before it still waits.
theorem closingPasses ∀ (kinds: Text → Tok) (before: Bool) (text: Text)
    (closes: Closes text):
    Passes kinds (Closing text) (Ready kinds before text) (Left text before) :=
  edge next ready after =>
    let solid := closesSolid text closes
    let filled := wordFilled text solid
    let spaces := solidSpaces text solid
    let token := closesToken text closes
    match edge, ready with
      | Plain None, _ =>
        rewrite filled then (byComputing, (rewrite solidTouch text solid then after (Plain (Some text)) byComputing))
      | Plain (Some word), follows =>
        rewrite filled then
          (
            (rewrite solidGap text solid then follows),
            (rewrite solidTouch text solid then after (Plain (Some text)) byComputing)
          )
      | Waiting None, waits => (
        spaces,
        filled,
        byComputing,
        followsSpace kinds text token,
        (rewrite solidTouch text solid then after (Waiting (Some text)) (byComputing, waits))
      )
      | Waiting (Some word), (waits, wordToken) => (
        spaces,
        filled,
        (rewrite solidGap text solid then followsCloser kinds word text wordToken closes),
        followsSpace kinds text token,
        (rewrite solidTouch text solid then after (Waiting (Some text)) (byComputing, waits))
      )

--| A token's text as the rules write it (`piece`): a closer joins a waiting comment's line, other text starts a
--| new one.
theorem piecePasses ∀ (kinds: Text → Tok) (before: Bool) (text: Text)
    (solid: isLayout text = False)
    (comma: (text == ",") = False):
    Passes kinds (piece text) (Ready kinds before text) (Left text (isCloserText text && before)) :=
  match closer: isCloserText text with
    | True => closingPasses kinds before text (closerCloses text closer)
    | False =>
      rewrite comma then
        passesTo kinds
          (Doc.text text)
          (Ready kinds before text)
          (edge => edge = Plain (Some text))
          (Left text False)
          (textPasses kinds before text solid)
          (edge same => rewrite same)

--| A comment on a line of its own, written where a line starts or a comment waits.
theorem commentPasses ∀ (kinds: Text → Tok) (before: Bool) (text: Text)
    (comment: commentText text = True):
    Passes kinds (Doc.text text) (Gapped before) (edge => True) :=
  edge next gapped after =>
    let solid := commentNotLayout text comment
    let filled := wordFilled text solid
    let spaces := solidSpaces text solid
    match edge, gapped with
      | Plain None, _ => rewrite filled then (byComputing, after _ byComputing)
      | Waiting touching, _ => rewrite filled, spaces then after _ byComputing

-- Own-line comments and kept blank lines.

theorem blankListPasses ∀ (kinds: Text → Tok) (blank: Bool) (pre: Edge → Prop):
    PassesAll kinds (if blank then [Blank] else []) pre pre :=
  match blank with
    | True => passesLast kinds Blank pre pre (passesBlank kinds pre)
    | False => passesNil kinds pre pre (edge holds => holds)

theorem blankLeadPasses ∀ (kinds: Text → Tok) (blank: Bool) (pre: Edge → Prop):
    PassesAll kinds (if blank then [BreakParent, Blank] else []) pre pre :=
  match blank with
    | True => passesTwo kinds BreakParent Blank pre pre pre (passesBreakParent kinds pre) (passesBlank kinds pre)
    | False => passesNil kinds pre pre (edge holds => holds)

theorem notesAbovePasses ∀ (kinds: Text → Tok) (before keep: Bool) (notes: List Note)
    (sound: notesSound notes = True):
    PassesAll kinds (notesAbove keep notes) (Gapped before) (Gapped before) :=
  match notes with
    | [] => passesNil kinds (Gapped before) (Gapped before) (edge holds => holds)
    | [note, ..rest] =>
      passesAppend kinds
        (if note.blankBefore && keep then [Blank] else [])
        ([Doc.text note.text, HardLine] ++ notesAbove True rest)
        (Gapped before)
        (Gapped before)
        (Gapped before)
        (blankListPasses kinds (note.blankBefore && keep) (Gapped before))
        (passesCons kinds
          (Doc.text note.text)
          ([HardLine] ++ notesAbove True rest)
          (Gapped before)
          (edge => True)
          (Gapped before)
          (commentPasses kinds before note.text (Bool.andLeft sound))
          (passesCons kinds HardLine
            (notesAbove True rest)
            (edge => True)
            (Gapped before)
            (Gapped before)
            (passesHard kinds (edge => True) (Gapped before) byComputing)
            (notesAbovePasses kinds before True rest (Bool.andRight sound))))

theorem laterCloserNotesPasses ∀ (kinds: Text → Tok) (notes: List Note)
    (sound: notesSound notes = True):
    PassesAll kinds (laterCloserNotes notes) (edge => True) (edge => True) :=
  match notes with
    | [] => passesNil kinds (edge => True) (edge => True) (edge holds => holds)
    | [note, ..rest] =>
      passesCons kinds HardLine
        ((if note.blankBefore then [Blank] else []) ++ [Doc.text note.text] ++ laterCloserNotes rest)
        (edge => True)
        (Gapped False)
        (edge => True)
        (passesHard kinds (edge => True) (Gapped False) byComputing)
        (passesAppend kinds
          (if note.blankBefore then [Blank] else [])
          ([Doc.text note.text] ++ laterCloserNotes rest)
          (Gapped False)
          (Gapped False)
          (edge => True)
          (blankListPasses kinds note.blankBefore (Gapped False))
          (passesCons kinds
            (Doc.text note.text)
            (laterCloserNotes rest)
            (Gapped False)
            (edge => True)
            (edge => True)
            (commentPasses kinds False note.text (Bool.andLeft sound))
            (laterCloserNotesPasses kinds rest (Bool.andRight sound))))

theorem closerNotesPasses ∀ (kinds: Text → Tok) (before: Bool) (notes: List Note)
    (sound: notesSound notes = True):
    PassesAll kinds (closerNotes notes) (Gapped before) (edge => True) :=
  match notes with
    | [] => passesNil kinds (Gapped before) (edge => True) (edge holds => byComputing)
    | [note, ..rest] =>
      passesCons kinds
        (Doc.text note.text)
        (laterCloserNotes rest)
        (Gapped before)
        (edge => True)
        (edge => True)
        (commentPasses kinds before note.text (Bool.andLeft sound))
        (laterCloserNotesPasses kinds rest (Bool.andRight sound))

--| Where a line starts, from where a token may stand: a comment may still wait.
theorem startPasses ∀ (kinds: Text → Tok) (before: Bool) (first: Text):
    Passes kinds LineStart (Ready kinds before first) (Gapped before) :=
  passesStart kinds
    (Ready kinds before first)
    (Gapped before)
    (touching ready =>
      match touching, ready with
        | None, waits => waits
        | Some word, waits => waits)
    byComputing

theorem startHerePasses ∀ (kinds: Text → Tok) (before: Bool) (first: Text):
    Passes kinds LineStartHere (Ready kinds before first) (Gapped before) :=
  passesStartHere kinds
    (Ready kinds before first)
    (Gapped before)
    (touching ready =>
      match touching, ready with
        | None, waits => waits
        | Some word, waits => waits)
    byComputing

-- A token's leaf.

theorem andTrueSame ∀ (flag: Bool): (flag && True) = flag := match flag with
  | True => byComputing
  | False => byComputing

--| What comes before a token's text in its leaf: its own-line comments and kept blank line, and the line a closer
--| takes after a comment. From where the token may stand to where it still may, and where no comment waits if it is
--| a closer with a trailing comment of its own.
--|
--| Proof idea: Cases on the leaf's comments. Own-line comments end with a line break, which a closer's do too
--| (`CloserLine`); a closer with no own-line comments but a trailing comment takes a line of its own where a comment
--| waits; anything else leaves the edge as it was.
theorem frontPasses ∀ (kinds: Text → Tok) (word: Word) (around: Around) (key: Nat)
    (sound: word.sound = True)
    (closerFree: isCloserText word.text = True → around.hoisted = False):
    PassesAll kinds
      (word.leading around key
        ++ (if isCloserText word.text && !word.noted && around.before && word.trails then [CloserLine key] else []))
      (Ready kinds around.before word.text)
      (Ready kinds (around.before && !(isCloserText word.text && word.trails)) word.text) :=
  let notes: notesSound word.comments.above = True := Bool.andLeft (Bool.andRight sound)
  match word, notes with
    | { text, comments = { above, after, blankBefore } }, notes =>
      match closer: isCloserText text with
        | True =>
          let notHoisted := closerFree closer
          match above with
            | [] =>
              match before: around.before, after with
                | True, Some comment =>
                  rewrite notHoisted then
                    passesAppend kinds
                      (if around.item && blankBefore then [BreakParent, Blank] else [])
                      [CloserLine key]
                      (Ready kinds True text)
                      (Ready kinds True text)
                      (Ready kinds False text)
                      (blankLeadPasses kinds (around.item && blankBefore) (Ready kinds True text))
                      (passesLast kinds
                        (CloserLine key)
                        (Ready kinds True text)
                        (Ready kinds False text)
                        (passesCloserLine kinds key (Ready kinds True text) (Ready kinds False text) byComputing))
                | True, None =>
                  rewrite notHoisted,
                      List.appendNil (if around.item && blankBefore then [BreakParent, Blank] else []) then
                    blankLeadPasses kinds (around.item && blankBefore) (Ready kinds True text)
                | False, after =>
                  rewrite notHoisted,
                      List.appendNil (if around.item && blankBefore then [BreakParent, Blank] else []) then
                    blankLeadPasses kinds (around.item && blankBefore) (Ready kinds False text)
            | [first, ..rest] =>
              rewrite notHoisted then
                passesCons kinds BreakParent
                  [Nest 2 (Doc.concat [LineStartHere, ..closerNotes [first, ..rest]]), CloserLine key]
                  (Ready kinds around.before text)
                  (Ready kinds around.before text)
                  (Ready kinds (around.before && !after.isSome) text)
                  (passesBreakParent kinds (Ready kinds around.before text))
                  (passesTwo kinds
                    (Nest 2 (Doc.concat [LineStartHere, ..closerNotes [first, ..rest]]))
                    (CloserLine key)
                    (Ready kinds around.before text)
                    (edge => True)
                    (Ready kinds (around.before && !after.isSome) text)
                    (passesNest kinds 2 _
                      (Ready kinds around.before text)
                      (edge => True)
                      (passesConcat kinds
                        [LineStartHere, ..closerNotes [first, ..rest]]
                        (Ready kinds around.before text)
                        (edge => True)
                        (passesCons kinds LineStartHere
                          (closerNotes [first, ..rest])
                          (Ready kinds around.before text)
                          (Gapped around.before)
                          (edge => True)
                          (startHerePasses kinds around.before text)
                          (closerNotesPasses kinds around.before [first, ..rest] notes))))
                    (passesCloserLine kinds key
                      (edge => True)
                      (Ready kinds (around.before && !after.isSome) text)
                      byComputing))
        | False =>
          rewrite andTrueSame around.before then
            match hoisted: around.hoisted with
              | True =>
                passesNil kinds (Ready kinds around.before text) (Ready kinds around.before text) (edge holds => holds)
              | False =>
                match above with
                  | [] =>
                    rewrite List.appendNil (if around.item && blankBefore then [BreakParent, Blank] else []) then
                      blankLeadPasses kinds (around.item && blankBefore) (Ready kinds around.before text)
                  | [first, ..rest] =>
                    rewrite List.appendNil
                          ([BreakParent, LineStart, ..notesAbove around.item [first, ..rest]]
                            ++ (if blankBefore then [Blank] else [])) then
                      passesAppend kinds
                        [BreakParent, LineStart, ..notesAbove around.item [first, ..rest]]
                        (if blankBefore then [Blank] else [])
                        (Ready kinds around.before text)
                        (Gapped around.before)
                        (Ready kinds around.before text)
                        (passesCons kinds BreakParent
                          [LineStart, ..notesAbove around.item [first, ..rest]]
                          (Ready kinds around.before text)
                          (Ready kinds around.before text)
                          (Gapped around.before)
                          (passesBreakParent kinds (Ready kinds around.before text))
                          (passesCons kinds LineStart
                            (notesAbove around.item [first, ..rest])
                            (Ready kinds around.before text)
                            (Gapped around.before)
                            (Gapped around.before)
                            (startPasses kinds around.before text)
                            (notesAbovePasses kinds around.before around.item [first, ..rest] notes)))
                        (allTo kinds
                          (if blankBefore then [Blank] else [])
                          (Gapped around.before)
                          (Gapped around.before)
                          (Ready kinds around.before text)
                          (blankListPasses kinds blankBefore (Gapped around.before))
                          (edge gapped => gappedReady kinds around.before text edge gapped))

theorem leftWeaker ∀ (text: Text) (flag flag': Bool)
    (implies: flag = True → flag' = True) (edge: Edge)
    (left: Left text flag edge):
    Left text flag' edge :=
  match edge, left with
    | Plain (Some word), same => same
    | Waiting (Some word), (same, waits) => (same, implies waits)
    | Plain None, never => (Bool.falseNotTrue never).impossible
    | Waiting None, never => (Bool.falseNotTrue never).impossible

--| A token's trailing comment, written after it on its line, where no comment waits yet.
theorem trailingPasses ∀ (kinds: Text → Tok) (word: Word) (flag: Bool)
    (sound: afterSound word.comments.after = True)
    (token: Token word.text)
    (bare: word.trails = True → flag = False):
    PassesAll kinds word.trailing (Left word.text flag) (Left word.text (word.trails || flag)) :=
  match word with
    | { text, comments = { above, after = None, blankBefore } } =>
      passesNil kinds (Left text flag) (Left text flag) (edge holds => holds)
    | { text, comments = { above, after = Some comment, blankBefore } } =>
      let solid := commentNotLayout comment sound
      let fresh := bare byComputing
      passesLast kinds (LineSuffix comment) (Left text flag) (Left text True) (edge next left after =>
        match edge, left with
          | Plain (Some last), same => (
            wordFilled comment solid,
            ((rewrite same then followsSpace kinds text token), after (Waiting (Some last)) (same, byComputing))
          )
          | Waiting (Some last), (same, waits) => (Bool.falseNotTrue (Eq.trans fresh.flipped waits)).impossible
          | Plain None, never => (Bool.falseNotTrue never).impossible
          | Waiting None, never => (Bool.falseNotTrue never).impossible)

theorem bareFlag ∀ (closer before trails: Bool)
    (trailing: trails = True):
    (closer && (before && !(closer && trails))) = False :=
  rewrite trailing then
    match closer, before with
      | True, True => byComputing
      | True, False => byComputing
      | False, before => byComputing

theorem leafFlag ∀ (closer before trails: Bool)
    (flag: (trails || (closer && (before && !(closer && trails)))) = True):
    (trails || (closer && before)) = True :=
  match closer, before, trails, flag with
    | True, True, True, _ => byComputing
    | True, True, False, _ => byComputing
    | True, False, True, _ => byComputing
    | False, before, True, _ => byComputing

--| A token's leaf, from where its text may stand: the line then ends with the text, with a comment waiting only if
--| the token has a trailing comment, or is a closer after code that ends with one.
--|
--| Proof idea: The leading documents (`frontPasses`) leave the token where it may stand, with no comment waiting if
--| it is a closer with a trailing comment of its own; then its piece (`piecePasses`) and its trailing comment
--| (`trailingPasses`).
theorem leafPasses ∀ (kinds: Text → Tok) (word: Word) (around: Around) (key: Nat)
    (sound: word.sound = True)
    (token: Token word.text)
    (comma: (word.text == ",") = False)
    (closerFree: isCloserText word.text = True → around.hoisted = False):
    Passes kinds
      (word.leaf around key)
      (Ready kinds around.before word.text)
      (Left word.text (word.trails || (isCloserText word.text && around.before))) :=
  let flag := around.before && !(isCloserText word.text && word.trails)
  let own := if isCloserText word.text && !word.noted && around.before && word.trails then [CloserLine key] else []
  let solid: isLayout word.text = False := Bool.notTrue (isLayout word.text) (Bool.andLeft sound)
  let after: afterSound word.comments.after = True := Bool.andRight (Bool.andRight sound)
  passesConcat kinds _ _ _
    (rewrite <- List.appendAssoc (word.leading around key) own ([piece word.text] ++ word.trailing) then
      passesAppend kinds
        (word.leading around key ++ own)
        ([piece word.text] ++ word.trailing)
        (Ready kinds around.before word.text)
        (Ready kinds flag word.text)
        (Left word.text (word.trails || (isCloserText word.text && around.before)))
        (frontPasses kinds word around key sound closerFree)
        (passesCons kinds
          (piece word.text)
          word.trailing
          (Ready kinds flag word.text)
          (Left word.text (isCloserText word.text && flag))
          (Left word.text (word.trails || (isCloserText word.text && around.before)))
          (piecePasses kinds flag word.text solid comma)
          (allTo kinds word.trailing
            (Left word.text (isCloserText word.text && flag))
            (Left word.text (word.trails || (isCloserText word.text && flag)))
            (Left word.text (word.trails || (isCloserText word.text && around.before)))
            (trailingPasses kinds word (isCloserText word.text && flag) after token (trailing =>
              bareFlag (isCloserText word.text) around.before word.trails trailing))
            (edge left =>
              leftWeaker word.text
                (word.trails || (isCloserText word.text && flag))
                (word.trails || (isCloserText word.text && around.before))
                (leafFlag (isCloserText word.text) around.before word.trails)
                edge
                left))))

-- What the tree's words must be.

--| A token that is no closer or comma, printed as the rules print it.
def WordJoins (word: Word): Prop :=
  word.sound = True ∧ Token word.text ∧ (word.text == ",") = False ∧ isCloserText word.text = False

--| A closing bracket.
def CloserJoins (word: Word): Prop := word.sound = True ∧ isCloserText word.text = True

--| An opening bracket: anything may follow it.
def OpenerJoins (kinds: Text → Tok) (word: Word): Prop :=
  WordJoins word ∧ ∀ (next: Text) => Follows kinds word.text next

--| The facts that carry the glue, for each token of an expression: what kind of token it is, and that a prefix
--| operator's operand may follow it where nothing is written between them.
def Joinable (kinds: Text → Tok): Expr → Prop
  | Atom _ word => WordJoins word
  | Paren open inner close => OpenerJoins kinds open ∧ CloserJoins close ∧ Joinable kinds inner
  | Tuple open items _ close => OpenerJoins kinds open ∧ CloserJoins close ∧ AllJoinable kinds items
  | ListOf open items _ close => OpenerJoins kinds open ∧ CloserJoins close ∧ AllJoinable kinds items
  | App head arguments => Joinable kinds head ∧ AllJoinable kinds arguments
  | Infix _ left operator right => Joinable kinds left ∧ WordJoins operator ∧ Joinable kinds right
  | Prefix operator operand =>
    WordJoins operator
      ∧ Joinable kinds operand
      ∧ ((prefixGap operator operand).isEmpty = True → Follows kinds operator.text operand.lead.text)
  | _ => False

def AllJoinable (kinds: Text → Tok): List Expr → Prop
  | [] => True
  | [expr, ..rest] => Joinable kinds expr ∧ AllJoinable kinds rest

--| What the rules' lemmas say of an expression: its element joins from where its first token may stand, and leaves
--| the line ending with a token, a comment waiting only if it ends with one.
def ElPasses (kinds: Text → Tok) (expr: Expr): Prop :=
  expr.within1 = True
    → Joinable kinds expr
    → ∀ (around: Around) => Passes kinds (expr.el around) (Ready kinds around.before expr.lead.text) (Ended expr.trails)

-- Comments ending an element.

theorem trailsBackAppend ∀ (front back: List Word)
    (trails: trailsBack front = True):
    trailsBack (front ++ back) = True :=
  match front with
    | [word, ..rest] =>
      match own: word.trails with
        | True => byComputing
        | False =>
          match closer: isCloserText word.text with
            | True => trailsBackAppend rest back trails

--| A bracket ends with a comment when its closer does, or the code before the closer does.
theorem bracketTrails ∀ (open close: Word) (middle: List Word)
    (closer: isCloserText close.text = True):
    trailsBack ([open, ..middle] ++ [close]).reverse = (close.trails || trailsBack (middle.reverse ++ [open])) :=
  rewrite List.reverseSnoc [open, ..middle] close, List.reverseCons open middle, closer

-- Openers, and the comments before an element.

theorem ownEmpty ∀ (text: Text) (rest: Bool) (key: Nat)
    (closer: isCloserText text = False):
    (if isCloserText text && rest then [CloserLine key] else []) = [] :=
  rewrite closer

theorem flagSame ∀ (before: Bool) (text: Text) (trails: Bool)
    (closer: isCloserText text = False):
    (before && !(isCloserText text && trails)) = before :=
  rewrite closer, andTrueSame before

--| A token's own-line comments and kept blank line, before a token that is no closer.
theorem leadingPasses ∀ (kinds: Text → Tok) (word: Word) (around: Around) (key: Nat)
    (sound: word.sound = True)
    (closer: isCloserText word.text = False):
    PassesAll kinds
      (word.leading around key)
      (Ready kinds around.before word.text)
      (Ready kinds around.before word.text) :=
  let front :=
    frontPasses kinds word around key sound (same => (Bool.falseNotTrue (Eq.trans closer.flipped same)).impossible)
  rewrite ownEmpty word.text (!word.noted && around.before && word.trails) key closer,
      flagSame around.before word.text word.trails closer at front then
    rewrite List.appendNil (word.leading around key) at front then front

theorem markListPasses ∀ (kinds: Text → Tok) (marked: Bool) (key: Nat) (pre: Edge → Prop):
    PassesAll kinds (if marked then [Mark key] else []) pre pre :=
  match marked with
    | True => passesLast kinds (Mark key) pre pre (passesMark kinds key pre)
    | False => passesNil kinds pre pre (edge holds => holds)

--| An opening bracket, from where it may stand: then anything may come next.
theorem openingPasses ∀ (kinds: Text → Tok) (word: Word) (around: Around) (closer: Word)
    (opener: OpenerJoins kinds word):
    Passes kinds (word.opening around closer) (Ready kinds around.before word.text) (Free kinds word.trails) :=
  match opener with
    | ((sound, token, comma, notCloser), free) =>
      let marked := closer.noted || closer.trails
      let solid: isLayout word.text = False := Bool.notTrue (isLayout word.text) (Bool.andLeft sound)
      let after: afterSound word.comments.after = True := Bool.andRight (Bool.andRight sound)
      let piecePass := piecePasses kinds around.before word.text solid comma
      passesConcat kinds _ _ _
        (passesAppend kinds
          (word.leading around around.at)
          ((if marked then [Mark around.at] else []) ++ [piece word.text] ++ word.trailing)
          (Ready kinds around.before word.text)
          (Ready kinds around.before word.text)
          (Free kinds word.trails)
          (leadingPasses kinds word around around.at sound notCloser)
          (passesAppend kinds
            (if marked then [Mark around.at] else [])
            ([piece word.text] ++ word.trailing)
            (Ready kinds around.before word.text)
            (Ready kinds around.before word.text)
            (Free kinds word.trails)
            (markListPasses kinds marked around.at (Ready kinds around.before word.text))
            (passesCons kinds
              (piece word.text)
              word.trailing
              (Ready kinds around.before word.text)
              (Left word.text False)
              (Free kinds word.trails)
              (passesTo kinds
                (piece word.text)
                (Ready kinds around.before word.text)
                (Left word.text (isCloserText word.text && around.before))
                (Left word.text False)
                piecePass
                (edge left =>
                  leftWeaker word.text
                    (isCloserText word.text && around.before)
                    False
                    (flag => rewrite notCloser at flag then flag)
                    edge
                    left))
              (allTo kinds word.trailing
                (Left word.text False)
                (Left word.text (word.trails || False))
                (Free kinds word.trails)
                (trailingPasses kinds word False after token (trailing => byComputing))
                (edge left =>
                  match edge, left with
                    | Plain (Some last), same => rewrite same then free
                    | Waiting (Some last), (same, waits) =>
                      (rewrite Bool.orFalse word.trails at waits then waits, rewrite same then token)
                    | Plain None, never => (Bool.falseNotTrue never).impossible
                    | Waiting None, never => (Bool.falseNotTrue never).impossible)))))

-- Framing, and the elements of the slice.

--| A node's document after its first token's own-line comments, displaced or not.
theorem framedPasses ∀ (kinds: Text → Tok) (first: Word) (around: Around) (doc: Doc) (post: Edge → Prop)
    (sound: first.sound = True)
    (closer: isCloserText first.text = False)
    (inner: Passes kinds doc (Ready kinds around.before first.text) post):
    Passes kinds (framedBy first around doc) (Ready kinds around.before first.text) post :=
  let pre := Ready kinds around.before first.text
  let placed := if first.noted || around.before then Displaced doc else doc
  let placedPasses: Passes kinds placed pre post := match first.noted || around.before with
    | True => passesDisplaced kinds doc pre post inner byComputing
    | False => inner
  passesConcat kinds _ pre post
    (passesTwo kinds
      (Doc.concat (first.leading around around.at))
      placed
      pre
      pre
      post
      (passesConcat kinds
        (first.leading around around.at)
        pre
        pre
        (leadingPasses kinds first around around.at sound closer))
      placedPasses)

--| The leftmost token of an element is one that joins as a token.
theorem leadJoins ∀ (kinds: Text → Tok) (expr: Expr) (joinable: Joinable kinds expr): WordJoins expr.lead :=
  match expr, joinable with
    | Atom kind word, joins => joins
    | Paren open inner close, (opener, _) => opener.left
    | Tuple open items comma close, (opener, _) => opener.left
    | ListOf open items comma close, (opener, _) => opener.left
    | App head arguments, (headJoins, _) => leadJoins kinds head headJoins
    | Infix kind left operator right, (leftJoins, _) => leadJoins kinds left leftJoins
    | Prefix operator operand, (operator, _) => operator

theorem framedExprPasses ∀ (kinds: Text → Tok) (expr: Expr) (around: Around) (doc: Doc) (post: Edge → Prop)
    (within: expr.within1 = True)
    (joinable: Joinable kinds expr)
    (inner: Passes kinds doc (Ready kinds around.before expr.lead.text) post):
    Passes kinds (expr.framed around doc) (Ready kinds around.before expr.lead.text) post :=
  let lead := leadJoins kinds expr joinable
  rewrite <- firstWordLead expr within then
    framedPasses kinds expr.firstWord around doc post
      (rewrite firstWordLead expr within then lead.left)
      (rewrite firstWordLead expr within then lead.right.right.right)
      (rewrite firstWordLead expr within then inner)

theorem atomTrails ∀ (word: Word) (before: Bool)
    (closer: isCloserText word.text = False)
    (flag: (word.trails || (isCloserText word.text && before)) = True):
    trailsBack [word] = True :=
  rewrite closer at flag then match own: word.trails with | True => byComputing

--| A name or numeral.
theorem atomPasses ∀ (kinds: Text → Tok) (kind: Tok) (word: Word) (around: Around)
    (joins: WordJoins word):
    Passes kinds ((Atom kind word).el around) (Ready kinds around.before word.text) (Ended (Atom kind word).trails) :=
  match joins with
    | (sound, token, comma, closer) =>
      passesTo kinds
        (word.leaf around around.at)
        (Ready kinds around.before word.text)
        (Left word.text (word.trails || (isCloserText word.text && around.before)))
        (Ended (Atom kind word).trails)
        (leafPasses kinds word around around.at sound token comma (same =>
          (Bool.falseNotTrue (Eq.trans closer.flipped same)).impossible))
        (edge left =>
          endedWeaker
            (word.trails || (isCloserText word.text && around.before))
            (trailsBack [word])
            (atomTrails word around.before closer)
            edge
            (leftEnded word.text (word.trails || (isCloserText word.text && around.before)) token edge left))

--| A bracket ends with a comment where its closer, or the code before it, does.
theorem closeTrails ∀ (open close: Word) (middle: List Word)
    (closer: isCloserText close.text = True)
    (flag: (close.trails || (isCloserText close.text && trailsBack middle.reverse)) = True):
    trailsBack ([open, ..middle] ++ [close]).reverse = True :=
  rewrite bracketTrails open close middle closer then
    match own: close.trails with
      | True => byComputing
      | False => rewrite closer at flag then trailsBackAppend middle.reverse [open] flag

--| A closer after an element, ending its bracket.
theorem closePasses ∀ (kinds: Text → Tok) (open close: Word) (middle: List Word) (around: Around) (key: Nat)
    (closer: CloserJoins close)
    (fresh: around.hoisted = False)
    (before: around.before = trailsBack middle.reverse):
    Passes kinds
      (close.leaf around key)
      (Ended around.before)
      (Ended (trailsBack ([open, ..middle] ++ [close]).reverse)) :=
  match closer with
    | (sound, isCloser) =>
      let closes := closerCloses close.text isCloser
      let token := closesToken close.text closes
      passesFrom kinds
        (close.leaf around key)
        (Ready kinds around.before close.text)
        (Ended around.before)
        (Ended (trailsBack ([open, ..middle] ++ [close]).reverse))
        (passesTo kinds
          (close.leaf around key)
          (Ready kinds around.before close.text)
          (Left close.text (close.trails || (isCloserText close.text && around.before)))
          (Ended (trailsBack ([open, ..middle] ++ [close]).reverse))
          (leafPasses kinds close around key sound token (closerNotComma close.text isCloser) (same => fresh))
          (edge left =>
            endedWeaker
              (close.trails || (isCloserText close.text && around.before))
              (trailsBack ([open, ..middle] ++ [close]).reverse)
              (flag => closeTrails open close middle isCloser (rewrite <- before then flag))
              edge
              (leftEnded close.text (close.trails || (isCloserText close.text && around.before)) token edge left)))
        (edge ended => endedReadyCloser kinds around.before close.text closes edge ended)

theorem parenInnerPasses ∀ (kinds: Text → Tok) (inner: Expr) (around: Around) (pre post: Edge → Prop)
    (within: inner.within1 = True)
    (passes: Passes kinds (inner.el around) pre post):
    Passes kinds (parenInner inner around) pre post :=
  match inner with
    | Block _ _ _ => cases
    | If _ _ _ _ _ _ _ => cases
    | _ => passes

--| `( … )`: the opener, the element inside, which may follow it, and the closer.
theorem parenPasses ∀ (kinds: Text → Tok) (open: Word) (inner: Expr) (close: Word) (around: Around)
    (within: inner.within1 = True)
    (opener: OpenerJoins kinds open)
    (closer: CloserJoins close)
    (innerPasses: ∀ (place: Around) => Passes kinds
      (inner.el place)
      (Ready kinds place.before inner.lead.text)
      (Ended inner.trails)):
    Passes kinds
      (parenDoc open inner close around)
      (Ready kinds around.before open.text)
      (Ended (Paren open inner close).trails) :=
  let innerAround := around.next open.trails 1
  let closeAround := around.next inner.trails (1 + inner.size)
  passesConcat kinds _ _ _
    (passesCons kinds
      (open.opening around close)
      [parenInner inner innerAround, close.leaf closeAround around.at]
      (Ready kinds around.before open.text)
      (Free kinds open.trails)
      (Ended (Paren open inner close).trails)
      (openingPasses kinds open around close opener)
      (passesTwo kinds
        (parenInner inner innerAround)
        (close.leaf closeAround around.at)
        (Free kinds open.trails)
        (Ended inner.trails)
        (Ended (Paren open inner close).trails)
        (passesFrom kinds
          (parenInner inner innerAround)
          (Ready kinds open.trails inner.lead.text)
          (Free kinds open.trails)
          (Ended inner.trails)
          (parenInnerPasses kinds inner innerAround _ _ within (innerPasses innerAround))
          (edge free => freeReady kinds open.trails inner.lead.text edge free))
        (closePasses kinds open close inner.words closeAround around.at closer byComputing byComputing)))

--| What a prefix operator writes before its operand: a space before a `-` or a numeral's application, else nothing,
--| where the operand may follow the operator.
theorem gapPasses ∀ (kinds: Text → Tok) (operator: Word) (operand: Expr)
    (token: Token operator.text)
    (glue: (prefixGap operator operand).isEmpty = True → Follows kinds operator.text operand.lead.text):
    Passes kinds
      (prefixGap operator operand)
      (Left operator.text operator.trails)
      (Ready kinds operator.trails operand.lead.text) :=
  match spaced: operator.text == "-" && (operand.firstWord.text == "-" || operand.numeralApplication) with
    | True =>
      passesTo kinds
        (Doc.text " ")
        (Left operator.text operator.trails)
        (Gapped operator.trails)
        (Ready kinds operator.trails operand.lead.text)
        (passesFrom kinds
          (Doc.text " ")
          (Ended operator.trails)
          (Left operator.text operator.trails)
          (Gapped operator.trails)
          (passesSpace kinds operator.trails)
          (edge left => leftEnded operator.text operator.trails token edge left))
        (edge gapped => gappedReady kinds operator.trails operand.lead.text edge gapped)
    | False =>
      let follows := glue byComputing
      edge next left after =>
        after edge
          (match edge, left with
            | Plain (Some last), same => rewrite same then follows
            | Waiting (Some last), (same, waits) => (waits, (rewrite same then token))
            | Plain None, never => (Bool.falseNotTrue never).impossible
            | Waiting None, never => (Bool.falseNotTrue never).impossible)

--| A prefix operator and its operand.
theorem prefixPasses ∀ (kinds: Text → Tok) (operator: Word) (operand: Expr) (around: Around)
    (joins: WordJoins operator)
    (glue: (prefixGap operator operand).isEmpty = True → Follows kinds operator.text operand.lead.text)
    (operandPasses: ∀ (place: Around) => Passes kinds
      (operand.el place)
      (Ready kinds place.before operand.lead.text)
      (Ended operand.trails)):
    Passes kinds
      (Doc.concat [
        operator.leaf { around | hoisted = True } around.at,
        prefixGap operator operand,
        operand.el (around.next operator.trails 1)
      ])
      (Ready kinds around.before operator.text)
      (Ended (Prefix operator operand).trails) :=
  match joins with
    | (sound, token, comma, closer) =>
      passesConcat kinds _ _ _
        (passesCons kinds
          (operator.leaf { around | hoisted = True } around.at)
          [prefixGap operator operand, operand.el (around.next operator.trails 1)]
          (Ready kinds around.before operator.text)
          (Left operator.text operator.trails)
          (Ended (Prefix operator operand).trails)
          (passesTo kinds
            (operator.leaf { around | hoisted = True } around.at)
            (Ready kinds around.before operator.text)
            (Left operator.text (operator.trails || (isCloserText operator.text && around.before)))
            (Left operator.text operator.trails)
            (leafPasses kinds operator { around | hoisted = True } around.at sound token comma (same =>
              (Bool.falseNotTrue (Eq.trans closer.flipped same)).impossible))
            (edge left =>
              leftWeaker operator.text
                (operator.trails || (isCloserText operator.text && around.before))
                operator.trails
                (flag => rewrite closer, Bool.orFalse operator.trails at flag then flag)
                edge
                left))
          (passesTwo kinds
            (prefixGap operator operand)
            (operand.el (around.next operator.trails 1))
            (Left operator.text operator.trails)
            (Ready kinds operator.trails operand.lead.text)
            (Ended (Prefix operator operand).trails)
            (gapPasses kinds operator operand token glue)
            (passesTo kinds
              (operand.el (around.next operator.trails 1))
              (Ready kinds operator.trails operand.lead.text)
              (Ended operand.trails)
              (Ended (Prefix operator operand).trails)
              (operandPasses (around.next operator.trails 1))
              (edge ended =>
                endedWeaker operand.trails
                  (Prefix operator operand).trails
                  (trails =>
                    rewrite List.reverseCons operator operand.words then
                      trailsBackAppend operand.words.reverse [operator] trails)
                  edge
                  ended))))
