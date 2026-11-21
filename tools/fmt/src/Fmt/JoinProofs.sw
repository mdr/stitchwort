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
import Syntax.LexProofs (Laid, MayFollow)
import Fmt (..)
import Fmt.PrintLexProofs (Follows)
import Fmt.SpellProofs (..)
import Fmt.CalmProofs (bracketFrom, bracketIs, lambdaHugNone, matchedNone, plainDef, plainDefIs, valueElPlain)
import Fmt.PrintLexProofs (Printable, pieceFold, printedLexes)
import Syntax (Comments, Decl, DefBody, DefKind, Header, lex)
import Syntax (InfixKind, Note)
import Syntax.SharedFacts (solidSpaces)

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
      let noWord := List.takeWhileHeadFails isWordChar rest first head word
      let noDigit := List.takeWhileHeadFails Char.isAsciiDigit rest first head digit
      match kind with
        | Colon => List.headNeOfHead rest first '=' head notEquals
        | Equals => (List.headNeOfHead rest first '=' head notEquals, List.headNeOfHead rest first '>' head notGreater)
        | Plus => List.headNeOfHead rest first '+' head notPlus
        | Minus => (List.headNeOfHead rest first '-' head notMinus, List.headNeOfHead rest first '>' head notGreater)
        | Lt => (List.headNeOfHead rest first '=' head notEquals, List.headNeOfHead rest first '-' head notMinus)
        | Gt => List.headNeOfHead rest first '=' head notEquals
        | Bang => bang => (List.headNeOfHead rest first '=' head notEquals, (run => (rewrite noWord at run then cases)))
        | KwDef | Lower | Upper => (noWord, List.headNeOfHead rest first '.' head notDot)
        | Num => (
          noDigit,
          List.headNeOfHead rest first '.' head notDot,
          List.headNeOfHead rest first 'e' head notE,
          List.headNeOfHead rest first 'E' head notBigE
        )
        | Float => (noDigit, List.headNeOfHead rest first 'e' head notE, List.headNeOfHead rest first 'E' head notBigE)
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
  cases

theorem freeReady ∀ (kinds: Text → Tok) (trails: Bool) (first: Text) (edge: Edge)
    (free: Free kinds trails edge):
    Ready kinds trails first edge :=
  cases edge then free first

theorem freeEnded ∀ (kinds: Text → Tok) (trails: Bool) (edge: Edge) (free: Free kinds trails edge): Ended trails edge :=
  match edge, free with
    | Plain None, _ => byComputing
    | Plain (Some word), any => (any " ").left
    | Waiting None | Waiting (Some _), waits => waits

theorem leftEnded ∀ (text: Text) (trails: Bool)
    (token: Token text) (edge: Edge)
    (left: Left text trails edge):
    Ended trails edge :=
  match edge, left with
    | Plain None | Waiting None, never => (Bool.falseNotTrue never).impossible
    | Plain (Some word), same => rewrite same then token
    | Waiting (Some word), (same, waits) => (waits, (rewrite same then token))

--| An ended element is ready for a closer or comma, and for a space.
theorem endedReadyCloser ∀ (kinds: Text → Tok) (trails: Bool) (text: Text)
    (closes: Closes text) (edge: Edge)
    (ended: Ended trails edge):
    Ready kinds trails text edge :=
  cases edge then followsCloser kinds _ text ended closes

theorem endedWeaker ∀ (trails trails': Bool)
    (implies: trails = True → trails' = True) (edge: Edge)
    (ended: Ended trails edge):
    Ended trails' edge :=
  cases

theorem readyWeaker ∀ (kinds: Text → Tok) (before before': Bool) (first: Text)
    (implies: before = True → before' = True) (edge: Edge)
    (ready: Ready kinds before first edge):
    Ready kinds before' first edge :=
  cases

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

theorem passesFrom ∀ [kinds: Text → Tok] [doc: Doc] [pre weaker post: Edge → Prop]
    (passes: Passes kinds doc pre post) (implies: ∀ (edge: Edge) => weaker edge → pre edge):
    Passes kinds doc weaker post :=
  edge next holds after => passes edge next (implies edge holds) after

theorem passesTo ∀ [kinds: Text → Tok] [doc: Doc] [pre post weaker: Edge → Prop]
    (passes: Passes kinds doc pre post) (implies: ∀ (edge: Edge) => post edge → weaker edge):
    Passes kinds doc pre weaker :=
  edge next holds after => passes edge next holds (left reached => after left (implies left reached))

theorem allFrom ∀ [kinds: Text → Tok] [docs: List Doc] [pre weaker post: Edge → Prop]
    (passes: PassesAll kinds docs pre post) (implies: ∀ (edge: Edge) => weaker edge → pre edge):
    PassesAll kinds docs weaker post :=
  edge next holds after => passes edge next (implies edge holds) after

theorem allTo ∀ [kinds: Text → Tok] [docs: List Doc] [pre post weaker: Edge → Prop]
    (passes: PassesAll kinds docs pre post) (implies: ∀ (edge: Edge) => post edge → weaker edge):
    PassesAll kinds docs pre weaker :=
  edge next holds after => passes edge next holds (left reached => after left (implies left reached))

theorem passesNil ∀ (kinds: Text → Tok) (pre post: Edge → Prop) (implies: ∀ (edge: Edge) => pre edge → post edge):
    PassesAll kinds [] pre post :=
  edge next holds after => after edge (implies edge holds)

theorem passesCons ∀ [kinds: Text → Tok] [doc: Doc] [docs: List Doc] [pre middle post: Edge → Prop]
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

theorem passesAppend ∀ [kinds: Text → Tok] [front back: List Doc] [pre middle post: Edge → Prop]
    (first: PassesAll kinds front pre middle)
    (second: PassesAll kinds back middle post):
    PassesAll kinds (front ++ back) pre post :=
  edge next holds after =>
    joinsAllAppend _ front back edge next (first edge _ holds (between reached => second between next reached after))

theorem passesLast ∀ [kinds: Text → Tok] [doc: Doc] [pre post: Edge → Prop]
    (only: Passes kinds doc pre post):
    PassesAll kinds [doc] pre post :=
  passesCons only (passesNil kinds post post (edge holds => holds))

theorem emptyJoins ∀ (kinds: Text → Tok) (doc: Doc) (edge: Edge) (next: Edge → Prop)
    (empty: doc.isEmpty = True)
    (joins: Joins (Follows kinds) doc edge next):
    next edge :=
  cases

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

theorem passesConcat ∀ [kinds: Text → Tok] [docs: List Doc] [pre post: Edge → Prop]
    (each: PassesAll kinds docs pre post):
    Passes kinds (Doc.concat docs) pre post :=
  edge next holds after => concatJoins kinds docs edge next (each edge next holds after)

theorem passesTwo ∀ [kinds: Text → Tok] [first second: Doc] [pre middle post: Edge → Prop]
    (one: Passes kinds first pre middle)
    (other: Passes kinds second middle post):
    PassesAll kinds [first, second] pre post :=
  passesCons one (passesLast other)

-- The document's constructors.

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

theorem passesNest ∀ [kinds: Text → Tok] (indent: Nat) [inner: Doc] [pre post: Edge → Prop]
    (passes: Passes kinds inner pre post):
    Passes kinds (Nest indent inner) pre post :=
  passes

theorem passesGroup ∀ [kinds: Text → Tok] [inner: Doc] (hard: Bool) [pre post: Edge → Prop]
    (passes: Passes kinds inner pre post):
    Passes kinds (Group inner hard) pre post :=
  passes

theorem passesIdGroup ∀ [kinds: Text → Tok] (id: Nat) [inner: Doc] (hard: Bool) [pre post: Edge → Prop]
    (passes: Passes kinds inner pre post):
    Passes kinds (IdGroup id inner hard) pre post :=
  passes

theorem passesFlatten ∀ [kinds: Text → Tok] [inner: Doc] [pre post: Edge → Prop]
    (passes: Passes kinds inner pre post):
    Passes kinds (Flatten inner) pre post :=
  passes

theorem passesIfBroken ∀ [kinds: Text → Tok] (id: Nat) [broken flat: Doc] [pre post: Edge → Prop]
    (brokenPasses: Passes kinds broken pre post)
    (flatPasses: Passes kinds flat pre post):
    Passes kinds (IfBroken id broken flat) pre post :=
  edge next holds after => (brokenPasses edge next holds after, flatPasses edge next holds after)

theorem passesOneLineBelow ∀ [kinds: Text → Tok] [inner: Doc] (pre: Edge → Prop) [post: Edge → Prop]
    (passes: Passes kinds inner (edge => edge = Plain None) post):
    Passes kinds (OneLineBelow inner) pre post :=
  edge next holds after => passes (Plain None) next byComputing after

--| Each option of a choice, from the same edges to the same edges.
def EachPasses (kinds: Text → Tok) (pre post: Edge → Prop): List Doc → Prop
  | [] => True
  | [option, ..others] => Passes kinds option pre post ∧ EachPasses kinds pre post others

--| A displaced element passes if its contents do from where they start, and from a fresh line where a comment
--| waits.
theorem passesDisplaced ∀ [kinds: Text → Tok] [inner: Doc] [pre post: Edge → Prop]
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

theorem closesToken ∀ (text: Text) (closes: Closes text): Token text := cases

theorem closesSolid ∀ (text: Text) (closes: Closes text): isLayout text = False := cases

theorem closerCloses ∀ (text: Text) (closer: isCloserText text = True): Closes text := match paren: text == ")" with
  | True => Inl (DecEq.sound paren)
  | False =>
    match square: text == "]" with
      | True => Inr (Inl (DecEq.sound square))
      | False =>
        match brace: text == "}" with
          | True => Inr (Inr (Inl (DecEq.sound brace)))

theorem closerNotComma ∀ (text: Text) (closer: isCloserText text = True): (text == ",") = False := cases

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
    | False => rewrite comma then passesTo (textPasses kinds before text solid) (edge same => rewrite same)

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
    | True => passesLast (passesBlank kinds pre)
    | False => passesNil kinds pre pre (edge holds => holds)

--| An item's kept blank line with no comments above: the line it starts may still have a comment waiting.
theorem blankLeadPasses ∀ (kinds: Text → Tok) (blank before: Bool) (first: Text):
    PassesAll kinds
      (if blank then [BreakParent, LineStart, Blank] else [])
      (Ready kinds before first)
      (Ready kinds before first) :=
  match blank with
    | True =>
      passesCons
        (passesBreakParent kinds (Ready kinds before first))
        (allTo (passesTwo (startPasses kinds before first) (passesBlank kinds (Gapped before))) (edge gapped =>
          gappedReady kinds before first edge gapped))
    | False => passesNil kinds (Ready kinds before first) (Ready kinds before first) (edge holds => holds)

theorem notesAbovePasses ∀ (kinds: Text → Tok) (before: Bool) (notes: List Note)
    (sound: notesSound notes = True):
    PassesAll kinds (notesAbove notes) (Gapped before) (Gapped before) :=
  match notes with
    | [] => passesNil kinds (Gapped before) (Gapped before) (edge holds => holds)
    | [note, ..rest] =>
      passesAppend
        (blankListPasses kinds note.blankBefore (Gapped before))
        (passesCons
          (commentPasses kinds before note.text (Bool.andLeft sound))
          (passesCons
            (passesHard kinds (edge => True) (Gapped before) byComputing)
            (notesAbovePasses kinds before rest (Bool.andRight sound))))

theorem laterCloserNotesPasses ∀ (kinds: Text → Tok) (notes: List Note)
    (sound: notesSound notes = True):
    PassesAll kinds (laterCloserNotes notes) (edge => True) (edge => True) :=
  match notes with
    | [] => passesNil kinds (edge => True) (edge => True) (edge holds => holds)
    | [note, ..rest] =>
      passesCons
        (passesHard kinds (edge => True) (Gapped False) byComputing)
        (passesAppend
          (blankListPasses kinds note.blankBefore (Gapped False))
          (passesCons
            (commentPasses kinds False note.text (Bool.andLeft sound))
            (laterCloserNotesPasses kinds rest (Bool.andRight sound))))

theorem closerNotesPasses ∀ (kinds: Text → Tok) (before: Bool) (notes: List Note)
    (sound: notesSound notes = True):
    PassesAll kinds (closerNotes notes) (Gapped before) (edge => True) :=
  match notes with
    | [] => passesNil kinds (Gapped before) (edge => True) (edge holds => byComputing)
    | [note, ..rest] =>
      passesAppend
        (blankListPasses kinds note.blankBefore (Gapped before))
        (passesCons
          (commentPasses kinds before note.text (Bool.andLeft sound))
          (laterCloserNotesPasses kinds rest (Bool.andRight sound)))

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
                    passesAppend
                      (blankLeadPasses kinds (around.item && blankBefore) True text)
                      (passesLast
                        (passesCloserLine kinds key (Ready kinds True text) (Ready kinds False text) byComputing))
                | True, None =>
                  rewrite notHoisted,
                      List.appendNil (if around.item && blankBefore then [BreakParent, LineStart, Blank] else []) then
                    blankLeadPasses kinds (around.item && blankBefore) True text
                | False, after =>
                  rewrite notHoisted,
                      List.appendNil (if around.item && blankBefore then [BreakParent, LineStart, Blank] else []) then
                    blankLeadPasses kinds (around.item && blankBefore) False text
            | [first, ..rest] =>
              rewrite notHoisted then
                passesCons
                  (passesBreakParent kinds (Ready kinds around.before text))
                  (passesTwo
                    (passesNest 2
                      (passesConcat
                        [docs := [LineStartHere, ..closerNotes [first, ..rest]]]
                        (passesCons
                          [doc := LineStartHere]
                          (startHerePasses kinds around.before text)
                          (closerNotesPasses kinds around.before [first, ..rest] notes))))
                    (passesCloserLine kinds key
                      (edge => True)
                      (Ready kinds (around.before && !after.isSome) text)
                      byComputing))
        | False =>
          rewrite Bool.andTrue around.before then
            match hoisted: around.hoisted with
              | True =>
                passesNil kinds (Ready kinds around.before text) (Ready kinds around.before text) (edge holds => holds)
              | False =>
                match above with
                  | [] =>
                    rewrite List.appendNil
                          (if around.item && blankBefore then [BreakParent, LineStart, Blank] else []) then
                      blankLeadPasses kinds (around.item && blankBefore) around.before text
                  | [first, ..rest] =>
                    rewrite List.appendNil
                          ([BreakParent, LineStart, ..notesAbove [first, ..rest]]
                            ++ (if blankBefore then [Blank] else [])) then
                      passesAppend
                        (passesCons
                          (passesBreakParent kinds (Ready kinds around.before text))
                          (passesCons
                            (startPasses kinds around.before text)
                            (notesAbovePasses kinds around.before [first, ..rest] notes)))
                        (allTo (blankListPasses kinds blankBefore (Gapped around.before)) (edge gapped =>
                          gappedReady kinds around.before text edge gapped))

theorem leftWeaker ∀ (text: Text) (flag flag': Bool)
    (implies: flag = True → flag' = True) (edge: Edge)
    (left: Left text flag edge):
    Left text flag' edge :=
  cases

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
      passesLast (edge next left after =>
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
  rewrite trailing then cases

theorem leafFlag ∀ (closer before trails: Bool)
    (flag: (trails || (closer && (before && !(closer && trails)))) = True):
    (trails || (closer && before)) = True :=
  cases

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
  passesConcat
    (rewrite <- List.appendAssoc (word.leading around key) own ([piece word.text] ++ word.trailing) then
      passesAppend
        (frontPasses kinds word around key sound closerFree)
        (passesCons
          (piecePasses kinds flag word.text solid comma)
          (allTo
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
  | Tuple open items _ close | ListOf open items _ close =>
    OpenerJoins kinds open ∧ CloserJoins close ∧ AllJoinable kinds items
  | App head arguments => Joinable kinds head ∧ AllJoinable kinds arguments ∧ arguments ≠ []
  | Infix _ left operator right => Joinable kinds left ∧ WordJoins operator ∧ Joinable kinds right
  | Prefix operator operand =>
    WordJoins operator
      ∧ Joinable kinds operand
      ∧ ((prefixGap operator operand).isEmpty = True → Follows kinds operator.text operand.lead.text)
  | _ => False

def AllJoinable (kinds: Text → Tok): List Expr → Prop
  | [] => True
  | [expr, ..rest] => Joinable kinds expr ∧ AllJoinable kinds rest

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
  rewrite closer, Bool.andTrue before

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
    | True => passesLast (passesMark kinds key pre)
    | False => passesNil kinds pre pre (edge holds => holds)

--| A token's own-line comments, whatever the code before ends with: `leading` doesn't read it.
theorem leadingTrue ∀ (kinds: Text → Tok) (word: Word) (around: Around) (key: Nat)
    (sound: word.sound = True)
    (closer: isCloserText word.text = False):
    PassesAll kinds (word.leading around key) (Ready kinds True word.text) (Ready kinds True word.text) :=
  leadingPasses kinds word { around | before = True } key sound closer

--| A token that is no closer: from where it may stand, even with a comment waiting, the line then ends with it.
theorem wordLeafPasses ∀ (kinds: Text → Tok) (word: Word) (around: Around) (key: Nat)
    (joins: WordJoins word):
    Passes kinds (word.leaf around key) (Ready kinds True word.text) (Left word.text word.trails) :=
  match joins with
    | (sound, token, comma, notCloser) =>
      let solid: isLayout word.text = False := Bool.notTrue (isLayout word.text) (Bool.andLeft sound)
      let after: afterSound word.comments.after = True := Bool.andRight (Bool.andRight sound)
      let piecePass := piecePasses kinds True word.text solid comma
      passesConcat
        (rewrite ownEmpty word.text (!word.noted && around.before && word.trails) key notCloser then
          passesAppend
            (leadingTrue kinds word around key sound notCloser)
            (passesCons
              (passesTo piecePass (edge left =>
                leftWeaker word.text
                  (isCloserText word.text && True)
                  False
                  (flag => rewrite notCloser at flag then flag)
                  edge
                  left))
              (allTo (trailingPasses kinds word False after token (trailing => byComputing)) (edge left =>
                leftWeaker word.text
                  (word.trails || False)
                  word.trails
                  (flag => rewrite Bool.orFalse word.trails at flag then flag)
                  edge
                  left))))

--| An opening bracket, from where it may stand: then anything may come next.
theorem openingPasses ∀ (kinds: Text → Tok) (word: Word) (around: Around) (closer: Word)
    (opener: OpenerJoins kinds word):
    Passes kinds (word.opening around closer) (Ready kinds True word.text) (Free kinds word.trails) :=
  match opener with
    | ((sound, token, comma, notCloser), free) =>
      let marked := closer.noted || closer.trails
      let solid: isLayout word.text = False := Bool.notTrue (isLayout word.text) (Bool.andLeft sound)
      let after: afterSound word.comments.after = True := Bool.andRight (Bool.andRight sound)
      let piecePass := piecePasses kinds True word.text solid comma
      passesConcat
        (passesAppend
          (leadingTrue kinds word around around.at sound notCloser)
          (passesAppend
            (markListPasses kinds marked around.at (Ready kinds True word.text))
            (passesCons
              (passesTo piecePass (edge left =>
                leftWeaker word.text
                  (isCloserText word.text && True)
                  False
                  (flag => rewrite notCloser at flag then flag)
                  edge
                  left))
              (allTo (trailingPasses kinds word False after token (trailing => byComputing)) (edge left =>
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
    (inner: Passes kinds doc (Ready kinds True first.text) post):
    Passes kinds (framedBy first around doc) (Ready kinds True first.text) post :=
  let pre := Ready kinds True first.text
  let placed := if first.displaces around then Displaced doc else doc
  let placedPasses: Passes kinds placed pre post := match first.displaces around with
    | True => passesDisplaced inner byComputing
    | False => inner
  passesConcat (passesTwo (passesConcat (leadingTrue kinds first around around.at sound closer)) placedPasses)

--| The leftmost token of an element is one that joins as a token.
theorem leadJoins ∀ (kinds: Text → Tok) (expr: Expr) (joinable: Joinable kinds expr): WordJoins expr.lead :=
  match expr, joinable with
    | Atom kind word, joins => joins
    | Paren _ _ _ | Tuple _ _ _ _ | ListOf _ _ _ _, (opener, _) => opener.left
    | App head _ | Infix _ head _ _, (headJoins, _) => leadJoins kinds head headJoins
    | Prefix operator operand, (operator, _) => operator

theorem framedExprPasses ∀ (kinds: Text → Tok) (expr: Expr) (around: Around) (doc: Doc) (post: Edge → Prop)
    (within: expr.within1 = True)
    (joinable: Joinable kinds expr)
    (inner: Passes kinds doc (Ready kinds True expr.lead.text) post):
    Passes kinds (expr.framed around doc) (Ready kinds True expr.lead.text) post :=
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
  cases

--| A name or numeral.
theorem atomPasses ∀ (kinds: Text → Tok) (kind: Tok) (word: Word) (around: Around)
    (joins: WordJoins word):
    Passes kinds ((Atom kind word).el around) (Ready kinds True word.text) (Ended (Atom kind word).trails) :=
  match joins with
    | (sound, token, comma, closer) => passesTo (wordLeafPasses kinds word around around.at joins) (edge left =>
      endedWeaker word.trails _
        (trails => atomTrails word False closer (rewrite trails))
        edge
        (leftEnded word.text word.trails token edge left))

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
      passesFrom
        (passesTo
          (leafPasses kinds close around key sound token (closerNotComma close.text isCloser) (same => fresh))
          (edge left =>
            endedWeaker _ _
              (flag => closeTrails open close middle isCloser (rewrite <- before then flag))
              edge
              (leftEnded close.text _ token edge left)))
        (edge ended => endedReadyCloser kinds around.before close.text closes edge ended)

theorem parenInnerPasses ∀ (kinds: Text → Tok) (inner: Expr) (around: Around) (pre post: Edge → Prop)
    (within: inner.within1 = True)
    (passes: Passes kinds (inner.el around) pre post):
    Passes kinds (parenInner inner around) pre post :=
  cases

--| `( … )`: the opener, the element inside, which may follow it, and the closer.
theorem parenPasses ∀ (kinds: Text → Tok) (open: Word) (inner: Expr) (close: Word) (around: Around)
    (within: inner.within1 = True)
    (opener: OpenerJoins kinds open)
    (closer: CloserJoins close)
    (innerPasses: ∀ (place: Around) => Passes kinds
      (inner.el place)
      (Ready kinds True inner.lead.text)
      (Ended inner.trails)):
    Passes kinds
      (parenDoc open inner close around)
      (Ready kinds True open.text)
      (Ended (Paren open inner close).trails) :=
  let innerAround := around.next open.trails 1
  let closeAround := around.next inner.trails (1 + inner.size)
  passesConcat
    (passesCons
      (openingPasses kinds open around close opener)
      (passesTwo
        (passesFrom (parenInnerPasses kinds inner innerAround _ _ within (innerPasses innerAround)) (edge free =>
          readyWeaker kinds open.trails True inner.lead.text
            (trails => byComputing)
            edge
            (freeReady kinds open.trails inner.lead.text edge free)))
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
      passesTo
        (passesFrom (passesSpace kinds operator.trails) (edge left =>
          leftEnded operator.text operator.trails token edge left))
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
      (Ready kinds True operand.lead.text)
      (Ended operand.trails)):
    Passes kinds
      (Doc.concat [
        operator.leaf { around | hoisted = True } around.at,
        prefixGap operator operand,
        operand.el (around.next operator.trails 1)
      ])
      (Ready kinds True operator.text)
      (Ended (Prefix operator operand).trails) :=
  passesConcat
    (passesCons
      (wordLeafPasses kinds operator { around | hoisted = True } around.at joins)
      (passesTwo
        (gapPasses kinds operator operand joins.right.left glue)
        (passesFrom
          (passesTo (operandPasses (around.next operator.trails 1)) (edge ended =>
            endedWeaker operand.trails _
              (trails =>
                rewrite List.reverseCons operator operand.words then
                  trailsBackAppend operand.words.reverse [operator] trails)
              edge
              ended))
          (edge ready => readyWeaker kinds operator.trails True operand.lead.text (trails => byComputing) edge ready))))

-- Comma brackets.

--| Each item's element passes wherever it stands.
def EachEl (kinds: Text → Tok): List Expr → Prop
  | [] => True
  | [expr, ..rest] =>
    (∀ (place: Around) => Passes kinds (expr.el place) (Ready kinds True expr.lead.text) (Ended expr.trails))
      ∧ EachEl kinds rest

theorem gappedReadyTrue ∀ (kinds: Text → Tok) (trails: Bool) (first: Text) (edge: Edge)
    (gapped: Gapped trails edge):
    Ready kinds True first edge :=
  readyWeaker kinds trails True first (holds => byComputing) edge (gappedReady kinds trails first edge gapped)

theorem freeReadyTrue ∀ (kinds: Text → Tok) (trails: Bool) (first: Text) (edge: Edge)
    (free: Free kinds trails edge):
    Ready kinds True first edge :=
  readyWeaker kinds trails True first (holds => byComputing) edge (freeReady kinds trails first edge free)

--| A comma after an item: it joins the item's line, a comment after the item still waiting.
theorem commaPasses ∀ (kinds: Text → Tok) (trails: Bool): Passes kinds (Closing ",") (Ended trails) (Ended trails) :=
  edge next ended after =>
    match edge, ended with
      | Plain None, _ => (byComputing, after (Plain (Some ",")) byComputing)
      | Plain (Some word), token =>
        (followsCloser kinds word "," token (Inr (Inr (Inr byComputing))), after (Plain (Some ",")) byComputing)
      | Waiting None, waits => (
        byComputing,
        byComputing,
        byComputing,
        followsSpace kinds "," byComputing,
        after (Waiting (Some ",")) (waits, byComputing)
      )
      | Waiting (Some word), (waits, token) => (
        byComputing,
        byComputing,
        followsCloser kinds word "," token (Inr (Inr (Inr byComputing))),
        followsSpace kinds "," byComputing,
        after (Waiting (Some ",")) (waits, byComputing)
      )

--| The words so far end with a comment if the last lot does.
theorem seenAppend ∀ (seen words: List Word)
    (trails: trailsBack words.reverse = True):
    trailsBack (seen ++ words).reverse = True :=
  rewrite List.reverseAppend seen words then trailsBackAppend words.reverse seen.reverse trails

theorem itemTrails ∀ (seen: List Word) (item: Expr) (edge: Edge)
    (ended: Ended item.trails edge):
    Ended (trailsBack (seen ++ itemsWords [item]).reverse) edge :=
  endedWeaker item.trails _
    (trails => rewrite List.appendNil item.words then seenAppend seen item.words trails)
    edge
    ended

--| A broken bracket's items after the first: each on a line, after a comma.
--|
--| Proof idea: Induction on the items; each line break leaves no token on the line, so the item may start there, and
--| the words seen so far end with a comment exactly when the last item does (`seenAppend`).
theorem brokenRestPasses ∀ (kinds: Text → Tok) (seen: List Word) (items: List Expr) (bare arm before: Bool) (at: Nat)
    (each: EachEl kinds items):
    PassesAll kinds
      (brokenItems bare arm False before at items)
      (Ended (trailsBack seen.reverse))
      (Ended (trailsBack (seen ++ itemsWords items).reverse)) :=
  match items, each with
    | [], _ =>
      passesNil kinds (Ended (trailsBack seen.reverse)) (Ended (trailsBack (seen ++ []).reverse)) (edge ended =>
        rewrite List.appendNil seen then ended)
    | [item], (passes, _) =>
      passesTwo
        (passesLine kinds (trailsBack seen.reverse))
        (passesFrom
          (passesTo (passes (firstAround bare arm before at)) (edge ended => itemTrails seen item edge ended))
          (edge gapped => gappedReadyTrue kinds (trailsBack seen.reverse) item.lead.text edge gapped))
    | [item, second, ..more], (passes, rest) =>
      passesCons
        (passesLine kinds (trailsBack seen.reverse))
        (passesCons
          (passesFrom
            (passesTo (passes (firstAround bare arm before at)) (edge ended =>
              endedWeaker item.trails _ (seenAppend seen item.words) edge ended))
            (edge gapped => gappedReadyTrue kinds (trailsBack seen.reverse) item.lead.text edge gapped))
          (passesCons
            (commaPasses kinds (trailsBack (seen ++ item.words).reverse))
            (rewrite <- List.appendAssoc seen item.words (itemsWords [second, ..more]) then
              brokenRestPasses kinds
                (seen ++ item.words)
                [second, ..more]
                False
                arm
                item.trails
                (at + item.size)
                rest)))

theorem openTrails ∀ (open: Word) (closer: isCloserText open.text = False): trailsBack [open] = open.trails :=
  rewrite closer, Bool.orFalse open.trails

--| A broken bracket's items: the first on a line of its own after the opener, the rest after commas.
theorem brokenPasses ∀ (kinds: Text → Tok) (open: Word) (items: List Expr) (bare arm before: Bool) (at: Nat)
    (notCloser: isCloserText open.text = False)
    (each: EachEl kinds items):
    PassesAll kinds
      (brokenItems bare arm True before at items)
      (Free kinds open.trails)
      (Ended (trailsBack ([open] ++ itemsWords items).reverse)) :=
  match items, each with
    | [], _ => passesNil kinds (Free kinds open.trails) (Ended (trailsBack ([open] ++ []).reverse)) (edge free =>
      rewrite openTrails open notCloser then freeEnded kinds open.trails edge free)
    | [item], (passes, _) =>
      passesTwo
        (passesSoft kinds (Free kinds open.trails) (Free kinds open.trails) (edge free => free) byComputing)
        (passesFrom
          (passesTo (passes (firstAround bare arm before at)) (edge ended => itemTrails [open] item edge ended))
          (edge free => freeReadyTrue kinds open.trails item.lead.text edge free))
    | [item, second, ..more], (passes, rest) =>
      passesCons
        (passesSoft kinds (Free kinds open.trails) (Free kinds open.trails) (edge free => free) byComputing)
        (passesCons
          (passesFrom
            (passesTo (passes (firstAround bare arm before at)) (edge ended =>
              endedWeaker item.trails _ (seenAppend [open] item.words) edge ended))
            (edge free => freeReadyTrue kinds open.trails item.lead.text edge free))
          (passesCons
            (commaPasses kinds (trailsBack ([open] ++ item.words).reverse))
            (rewrite <- List.appendAssoc [open] item.words (itemsWords [second, ..more]) then
              brokenRestPasses kinds
                ([open] ++ item.words)
                [second, ..more]
                False
                arm
                item.trails
                (at + item.size)
                rest)))

--| A filled list's cells after the first, each after a space or a line break.
--|
--| Proof idea: Induction on the items, as `brokenRestPasses`, with `SepsJoin`'s separator before each cell.
theorem sepsCellsJoin ∀ (kinds: Text → Tok) (seen: List Word) (items: List Expr) (arm before: Bool) (at: Nat)
    (each: EachEl kinds items)
    (edge: Edge) (next: Edge → Prop)
    (ended: Ended (trailsBack seen.reverse) edge)
    (after: ∀ (left: Edge) => Ended (trailsBack (seen ++ itemsWords items).reverse) left → next left):
    SepsJoin (Follows kinds) (cells False arm before at items) edge next :=
  match items, each with
    | [], _ => after edge (rewrite List.appendNil seen then ended)
    | [item], (passes, _) => passesLine kinds (trailsBack seen.reverse) edge _ ended (middle gapped =>
      passes
        (firstAround False arm before at)
        middle _
        (gappedReadyTrue kinds (trailsBack seen.reverse) item.lead.text middle gapped)
        (left itemEnded => after left (itemTrails seen item left itemEnded)))
    | [item, second, ..more], (passes, rest) =>
      passesLine kinds (trailsBack seen.reverse) edge _ ended (middle gapped =>
        passesConcat
          (passesTwo
            (passesFrom
              (passesTo (passes (firstAround False arm before at)) (edge ended =>
                endedWeaker item.trails _ (seenAppend seen item.words) edge ended))
              (edge gapped => gappedReadyTrue kinds (trailsBack seen.reverse) item.lead.text edge gapped))
            (commaPasses kinds (trailsBack (seen ++ item.words).reverse)))
          middle _
          gapped
          (left cellEnded =>
            sepsCellsJoin kinds
              (seen ++ item.words)
              [second, ..more]
              arm
              item.trails
              (at + item.size)
              rest
              left
              next
              cellEnded
              (last lastEnded =>
                after last
                  (rewrite List.appendAssoc seen item.words (itemsWords [second, ..more]) at lastEnded then
                    lastEnded))))

--| A filled list's cells: the first after the opener, each later one after a space or a line break.
theorem cellsPasses ∀ (kinds: Text → Tok) (open: Word) (items: List Expr) (bare arm before: Bool) (at: Nat)
    (notCloser: isCloserText open.text = False)
    (each: EachEl kinds items):
    Passes kinds
      (Fill (cells bare arm before at items))
      (Free kinds open.trails)
      (Ended (trailsBack ([open] ++ itemsWords items).reverse)) :=
  edge next free after =>
    match items, each with
      | [], _ =>
        after edge (rewrite List.appendNil [open], openTrails open notCloser then freeEnded kinds open.trails edge free)
      | [item], (passes, _) =>
        passes
          (firstAround bare arm before at)
          edge _
          (freeReadyTrue kinds open.trails item.lead.text edge free)
          (left ended => after left (itemTrails [open] item left ended))
      | [item, second, ..more], (passes, rest) =>
        passesConcat
          (passesTwo
            (passesFrom
              (passesTo (passes (firstAround bare arm before at)) (edge ended =>
                endedWeaker item.trails _ (seenAppend [open] item.words) edge ended))
              (edge free => freeReadyTrue kinds open.trails item.lead.text edge free))
            (commaPasses kinds (trailsBack ([open] ++ item.words).reverse)))
          edge _
          free
          (left cellEnded =>
            sepsCellsJoin kinds
              ([open] ++ item.words)
              [second, ..more]
              arm
              item.trails
              (at + item.size)
              rest
              left
              next
              cellEnded
              (last lastEnded =>
                after last
                  (rewrite List.appendAssoc [open] item.words (itemsWords [second, ..more]) at lastEnded then
                    lastEnded)))

--| A closer that ends a bracket: from where the code before it leaves the line, the line ends with the closer, a
--| comment waiting only if the bracket ends with one.
theorem closerEnds ∀ (kinds: Text → Tok) (front: List Word) (close: Word) (around: Around) (key: Nat)
    (closer: CloserJoins close)
    (fresh: around.hoisted = False)
    (before: around.before = True → trailsBack front.reverse = True):
    Passes kinds (close.leaf around key) (Ended around.before) (Ended (trailsBack (front ++ [close]).reverse)) :=
  match closer with
    | (sound, isCloser) =>
      let closes := closerCloses close.text isCloser
      let token := closesToken close.text closes
      passesFrom
        (passesTo
          (leafPasses kinds close around key sound token (closerNotComma close.text isCloser) (same => fresh))
          (edge left =>
            endedWeaker _ _
              (flag =>
                rewrite List.reverseSnoc front close then
                  match own: close.trails with
                    | True => byComputing
                    | False => rewrite isCloser at flag then rewrite isCloser then before flag)
              edge
              (leftEnded close.text _ token edge left)))
        (edge ended => endedReadyCloser kinds around.before close.text closes edge ended)

theorem beforeCloseIs ∀ (open: Word) (items: List Expr) (close: Word):
    (ListOf open items False close).trailsBeforeClose = trailsBack ([open] ++ itemsWords items).reverse :=
  rewrite List.reverseSnoc [open, ..itemsWords items] close

--| A tuple's or list's parts (`bracketContent`): the opener, the items filled or broken, and the closer.
--|
--| Proof idea: `bracketIs` names the three layouts. In each the items leave the line as their words say
--| (`cellsPasses`, `brokenPasses`), which is what the closer reads (`beforeCloseIs`, `closerEnds`).
theorem bracketContentPasses ∀ (kinds: Text → Tok) (list: Bool) (open: Word) (items: List Expr)
    (close: Word) (around: Around)
    (opener: OpenerJoins kinds open)
    (closer: CloserJoins close)
    (each: EachEl kinds items):
    Passes kinds
      (bracketContent list open items close around)
      (Ready kinds True open.text)
      (Ended (ListOf open items False close).trails) :=
  let whole := ListOf open items False close
  let closeAround := around.next whole.trailsBeforeClose (whole.size - 1)
  let notCloser := opener.left.right.right.right
  let seen := trailsBack ([open] ++ itemsWords items).reverse
  let prefixPass := openingPasses kinds open around close opener
  let closerPass: Passes kinds (close.leaf closeAround around.at) (Ended seen) (Ended whole.trails) :=
    passesFrom
      (closerEnds kinds [open, ..itemsWords items] close closeAround around.at closer byComputing (before =>
        rewrite beforeCloseIs open items close at before then before))
      (edge ended => rewrite beforeCloseIs open items close then ended)
  let broken := brokenItems (list && items.all Expr.plainItem) around.inArm True open.trails (around.at + 1) items
  let brokenPass: PassesAll kinds
    [open.opening around close, Nest 2 (Doc.concat broken), SoftLine, close.leaf closeAround around.at]
    (Ready kinds True open.text)
    (Ended whole.trails) :=
    passesCons prefixPass
      (passesCons
        (passesConcat
          (brokenPasses kinds open items
            (list && items.all Expr.plainItem)
            around.inArm
            open.trails
            (around.at + 1)
            notCloser
            each))
        (passesTwo (passesSoft kinds (Ended seen) (Ended seen) (edge ended => ended) byComputing) closerPass))
  rewrite bracketIs list open items close around then
    match empty: items.isEmpty with
      | True =>
        passesConcat
          (passesTwo prefixPass
            (passesFrom closerPass (edge free =>
              rewrite emptyItems items empty, List.appendNil [open], openTrails open notCloser then
                freeEnded kinds open.trails edge free)))
      | False =>
        match filled: list && !whole.holdsTrailingComment && items.all Expr.plainItem with
          | True =>
            let fill :=
              Nest 2 (Fill (cells (list && items.all Expr.plainItem) around.inArm open.trails (around.at + 1) items))
            passesConcat
              [docs := [open.opening around close, fill, close.leaf closeAround around.at]]
              (passesCons prefixPass
                (passesTwo
                  (passesNest 2
                    (cellsPasses kinds open items
                      (list && items.all Expr.plainItem)
                      around.inArm
                      open.trails
                      (around.at + 1)
                      notCloser
                      each))
                  closerPass))
          | False =>
            match holds: whole.holdsTrailingComment with
              | True =>
                let withBreak :=
                  passesAppend
                    [front := [
                      open.opening around close,
                      Nest 2 (Doc.concat broken),
                      SoftLine,
                      close.leaf closeAround around.at
                    ]]
                    [back := [BreakParent]]
                    brokenPass
                    (passesLast (passesBreakParent kinds (Ended whole.trails)))
                passesConcat withBreak
              | False => passesConcat brokenPass

theorem emptyItems ∀ (items: List Expr) (empty: items.isEmpty = True): items = [] := match items with
  | [] => byComputing

-- Elements one after another, with a space or line break between each two.

--| Documents printed in order with a separator between each two: the first from `pre`, the others after a
--| separator; each but the last leaves the line ending with a token, the last leaves `post`.
def PassesSeq (kinds: Text → Tok) (pre post: Edge → Prop): List Doc → Prop
  | [] => ∀ (edge: Edge) => pre edge → post edge
  | [doc, ..rest] => SeqFrom kinds pre post doc rest

def SeqFrom (kinds: Text → Tok) (pre post: Edge → Prop) (doc: Doc): List Doc → Prop
  | [] => Passes kinds doc pre post
  | [next, ..more] => Passes kinds doc pre (Ended True) ∧ SeqFrom kinds (Gapped True) post next more

--| The documents with a space between each two (`spaced`).
theorem joinedSeq ∀ (kinds: Text → Tok) (docs: List Doc) (pre post: Edge → Prop)
    (seq: PassesSeq kinds pre post docs):
    PassesAll kinds (Doc.joinedWith (Doc.text " ") docs) pre post :=
  match docs, seq with
    | [], keeps => passesNil kinds pre post keeps
    | [only], passes => passesLast passes
    | [doc, next, ..more], (first, rest) =>
      passesCons first (passesCons (passesSpace kinds True) (joinedSeq kinds [next, ..more] (Gapped True) post rest))

theorem spacedSeq ∀ (kinds: Text → Tok) (docs: List Doc) (pre post: Edge → Prop)
    (seq: PassesSeq kinds pre post docs):
    Passes kinds (spaced docs) pre post :=
  passesConcat (joinedSeq kinds docs pre post seq)

theorem sepsSeq ∀ (kinds: Text → Tok) (doc: Doc) (more: List Doc) (post: Edge → Prop)
    (seq: SeqFrom kinds (Gapped True) post doc more)
    (edge: Edge) (next: Edge → Prop)
    (ended: Ended True edge) (after: ∀ (left: Edge) => post left → next left):
    SepsJoin (Follows kinds) [doc, ..more] edge next :=
  passesLine kinds True edge _ ended (middle gapped =>
    match more, seq with
      | [], passes => passesFrom passes (edge g => g) middle _ gapped after
      | [second, ..rest], (first, others) =>
        first middle _ gapped (left firstEnded => sepsSeq kinds second rest post others left next firstEnded after))

--| A fill of documents: the first from `pre`, each later one after a space or a line break.
theorem fillSeq ∀ (kinds: Text → Tok) (docs: List Doc) (pre post: Edge → Prop)
    (seq: PassesSeq kinds pre post docs):
    Passes kinds (Fill docs) pre post :=
  edge next holds after =>
    match docs, seq with
      | [], keeps => after edge (keeps edge holds)
      | [only], passes => passes edge _ holds after
      | [doc, second, ..more], (first, rest) =>
        first edge _ holds (left ended => sepsSeq kinds second more post rest left next ended after)

--| A sequence split in two: the first part leaves a token, the second starts after a separator.
theorem splitSeq ∀ (kinds: Text → Tok) (front back: List Doc) (pre post: Edge → Prop)
    (filledFront: front ≠ [])
    (filledBack: back ≠ [])
    (seq: PassesSeq kinds pre post (front ++ back)):
    PassesSeq kinds pre (Ended True) front ∧ PassesSeq kinds (Gapped True) post back :=
  match front, seq with
    | [], _ => (filledFront byComputing).impossible
    | [only], seq =>
      match back, seq with
        | [], _ => (filledBack byComputing).impossible
        | [next, ..more], (first, rest) => (first, rest)
    | [doc, second, ..more], (first, rest) =>
      let (frontRest, backRest) :=
        splitSeq kinds [second, ..more] back (Gapped True) post (List.consNotNil second more) filledBack rest
      ((first, frontRest), backRest)

--| Documents each on a line of their own.
theorem hardSeq ∀ (kinds: Text → Tok) (docs: List Doc) (pre post: Edge → Prop)
    (filled: docs ≠ [])
    (seq: PassesSeq kinds (Gapped True) post docs):
    PassesAll kinds (docs.concatMap (doc => [HardLine, doc])) pre post :=
  match docs, seq with
    | [], _ => (filled byComputing).impossible
    | [only], passes => passesTwo (passesHard kinds pre (Gapped True) byComputing) passes
    | [doc, second, ..more], (first, rest) =>
      passesCons
        (passesHard kinds pre (Gapped True) byComputing)
        (passesCons first (hardSeq kinds [second, ..more] (Ended True) post (List.consNotNil second more) rest))

--| A choice of one or more options, each passing.
theorem passesChoiceOf ∀ [kinds: Text → Tok] [first: Doc] (others: List Doc) [pre post: Edge → Prop]
    (passes: Passes kinds first pre post)
    (each: EachPasses kinds pre post others):
    Passes kinds (Choice [first, ..others]) pre post :=
  edge next holds after =>
    match others, each with
      | [], _ => passes edge next holds after
      | [second, ..more], (secondPasses, rest) =>
        (passes edge next holds after, passesChoiceOf more secondPasses rest edge next holds after)

--| A call's last argument opened passes, if it opens.
def HugPasses (kinds: Text → Tok) (hug: Option Doc) (pre post: Edge → Prop): Prop := match hug with
  | None => True
  | Some open => Passes kinds open pre post

--| A call's layouts (`appFrom`): on one line; hugging its last argument; or the function and the arguments it keeps
--| on its line, then each other argument on a line of its own. In each the elements come in order with a space or
--| a line break between each two.
--|
--| Proof idea: The sequence of the call's elements passes (`seq`); each layout is the sequence spaced (`spacedSeq`),
--| filled (`fillSeq`), or split where the kept elements end (`splitSeq`), the rest each after a line break
--| (`hardSeq`); the hug passes as the last argument does.
theorem appFromPasses ∀ (kinds: Text → Tok) (id keep: Nat) (between betweenFront: Bool) (headDoc lastDoc: Doc)
    (front: List Doc) (hug: Option Doc) (pre post: Edge → Prop)
    (seq: PassesSeq kinds pre post ([headDoc, ..front] ++ [lastDoc]))
    (hugPasses: HugPasses kinds hug (Gapped True) post)
    (positive: keep ≠ 0)
    (short: keep ≤ ([headDoc, ..front] ++ [lastDoc]).length):
    Passes kinds (appFrom id keep between betweenFront headDoc front lastDoc hug).doc pre post :=
  let docs := [headDoc, ..front] ++ [lastDoc]
  match full: keep == docs.length with
    | True =>
      match between with
        | True => spacedSeq kinds docs pre post seq
        | False => passesNest 4 (fillSeq kinds docs pre post seq)
    | False =>
      let (keptSeq, droppedSeq) :=
        splitSeq kinds
          (docs.take keep)
          (docs.drop keep)
          pre
          post
          (List.takeConsNotNil headDoc (front ++ [lastDoc]) keep positive)
          (List.dropNotNil docs keep short full)
          (rewrite List.appendTakeDrop docs keep then seq)
      let (headSeq, lastSeq) :=
        splitSeq kinds
          [headDoc, ..front]
          [lastDoc]
          pre
          post
          (List.consNotNil headDoc front)
          (List.consNotNil lastDoc [])
          seq
      let flat: Passes kinds (Flatten (spaced docs)) pre post := passesFlatten (spacedSeq kinds docs pre post seq)
      let rest := Doc.concat (docs.drop keep |> .concatMap (doc => [HardLine, doc]))
      let restPasses: Passes kinds rest (Ended True) post :=
        passesConcat
          (hardSeq kinds (docs.drop keep) (Ended True) post (List.dropNotNil docs keep short full) droppedSeq)
      let fillFront := keep > 2 && !betweenFront
      let frontDoc := if fillFront then IdGroup id (Nest 4 (Fill (docs.take keep))) False else spaced (docs.take keep)
      let restDoc := if fillFront then IfBroken id (Nest 4 rest) (Nest 2 rest) else Nest 2 rest
      let frontPass: Passes kinds frontDoc pre (Ended True) := match fillFront with
        | True => passesIdGroup id False (passesNest 4 (fillSeq kinds (docs.take keep) pre (Ended True) keptSeq))
        | False => spacedSeq kinds (docs.take keep) pre (Ended True) keptSeq
      let restPass: Passes kinds restDoc (Ended True) post := match fillFront with
        | True => passesIfBroken id (passesNest 4 restPasses) (passesNest 2 restPasses)
        | False => passesNest 2 restPasses
      let broken: Passes kinds (Doc.concat [frontDoc, restDoc]) pre post := passesConcat (passesTwo frontPass restPass)
      match hug, hugPasses with
        | None, _ => passesChoiceOf [Doc.concat [frontDoc, restDoc]] flat (broken, byComputing)
        | Some open, opens =>
          let hugged: Passes kinds (Doc.concat [Flatten (spaced [headDoc, ..front]), Doc.text " ", open]) pre post :=
            passesConcat
              (passesCons
                (passesFlatten (spacedSeq kinds [headDoc, ..front] pre (Ended True) headSeq))
                (passesTwo (passesSpace kinds True) opens))
          passesChoiceOf
            [Doc.concat [Flatten (spaced [headDoc, ..front]), Doc.text " ", open], Doc.concat [frontDoc, restDoc]]
            flat
            (hugged, broken, byComputing)

-- Calls.

theorem seqPrepend ∀ (kinds: Text → Tok) (pre post: Edge → Prop) (doc: Doc) (docs: List Doc)
    (first: Passes kinds doc pre (Ended True))
    (rest: PassesSeq kinds (Gapped True) post docs)
    (filled: docs ≠ []):
    PassesSeq kinds pre post [doc, ..docs] :=
  match docs, rest with
    | [], _ => (filled byComputing).impossible
    | [next, ..more], seq => (first, seq)

theorem endedTrue ∀ (trails: Bool) (edge: Edge) (ended: Ended trails edge): Ended True edge :=
  endedWeaker trails True (holds => byComputing) edge ended

theorem keptShort ∀ (previous: Expr) (arguments: List Expr): keptFront previous arguments ≤ arguments.length :=
  match arguments with
    | [] => byComputing
    | [argument, ..rest] =>
      match kept: argument.simple && !previous.trails with
        | True => arithmetic [keptShort argument rest]
        | False => byComputing

--| A run of documents passes inside a nest after the first.
theorem passesHeadTail ∀ [kinds: Text → Tok] [head: Doc] [tail: List Doc] (indent: Nat) [pre post: Edge → Prop]
    (all: PassesAll kinds [head, ..tail] pre post):
    Passes kinds (Doc.concat [head, Nest indent (Doc.concat tail)]) pre post :=
  let middle := (edge: Edge) => JoinsAll (Follows kinds) tail edge post
  let tailPasses: Passes kinds (Doc.concat tail) middle post :=
    passesConcat (edge next holds after => allWeaker (Follows kinds) tail edge post next after holds)
  let headPasses: Passes kinds head pre middle := edge next holds after =>
    joinsWeaker (Follows kinds) head edge middle next after (all edge post holds (left done => done))
  passesConcat (passesTwo headPasses (passesNest indent tailPasses))

--| A tuple's or list's element.
theorem commaBracketPasses ∀ (kinds: Text → Tok) (list: Bool) (open: Word) (items: List Expr)
    (close: Word) (around: Around)
    (opener: OpenerJoins kinds open)
    (closer: CloserJoins close)
    (each: EachEl kinds items):
    Passes kinds
      (commaBracket list open items close around)
      (Ready kinds True open.text)
      (Ended (ListOf open items False close).trails) :=
  passesGroup
    (bracketContent list open items close around).forcesBreak
    (bracketContentPasses kinds list open items close around opener closer each)

--| A bracket as a call's last argument, as it stands and opened.
theorem huggedBracketPasses ∀ (kinds: Text → Tok) (list: Bool) (open: Word) (items: List Expr) (close: Word)
    (around: Around) (hard: Bool)
    (opener: OpenerJoins kinds open)
    (closer: CloserJoins close)
    (each: EachEl kinds items):
    Passes kinds
      (framedBy open around (Group (bracketContent list open items close { around | hoisted = True }) hard))
      (Ready kinds True open.text)
      (Ended (ListOf open items False close).trails) :=
  framedPasses kinds open around
    (Group (bracketContent list open items close { around | hoisted = True }) hard) _
    opener.left.left
    opener.left.right.right.right
    (passesGroup hard (bracketContentPasses kinds list open items close { around | hoisted = True } opener closer each))

theorem hugFrom ∀ (kinds: Text → Tok) (hug: Option Doc) (pre weaker post later: Edge → Prop)
    (passes: HugPasses kinds hug pre post)
    (from: ∀ (edge: Edge) => weaker edge → pre edge) (to: ∀ (edge: Edge) => post edge → later edge):
    HugPasses kinds hug weaker later :=
  match hug, passes with
    | None, _ => byComputing
    | Some open, opens => passesFrom (passesTo opens to) from

--| Each item's element passes, given the induction's facts.
theorem allElPasses ∀ (kinds: Text → Tok) (items: List Expr)
    (within: allWithin1 items = True)
    (joinable: AllJoinable kinds items):
    EachEl kinds items :=
  match items, joinable with
    | [], _ => byComputing
    | [item, ..rest], (joins, others) => (
      place => elPasses kinds item (Bool.andLeft within) joins place,
      allElPasses kinds rest (Bool.andRight within) others
    )

--| A call's last argument, as it stands and opened.
theorem lastArgumentPasses ∀ (kinds: Text → Tok) (argument: Expr) (around: Around)
    (within: argument.within1 = True)
    (joinable: Joinable kinds argument):
    Passes kinds (lastArgument argument around).fst (Ready kinds True argument.lead.text) (Ended argument.trails)
      ∧ HugPasses kinds
        (lastArgument argument around).snd
        (Ready kinds True argument.lead.text)
        (Ended argument.trails) :=
  match argument, joinable with
    | Tuple open items comma close, (opener, closer, each) =>
      let content := bracketContent False open items close { around | hoisted = True }
      let elements := allElPasses kinds items within each
      (
        huggedBracketPasses kinds False open items close around content.forcesBreak opener closer elements,
        huggedBracketPasses kinds False open items close around True opener closer elements
      )
    | ListOf open items comma close, (opener, closer, each) =>
      let content := bracketContent True open items close { around | hoisted = True }
      let elements := allElPasses kinds items within each
      (
        huggedBracketPasses kinds True open items close around content.forcesBreak opener closer elements,
        huggedBracketPasses kinds True open items close around True opener closer elements
      )
    | Atom _ _ |
        App _ _ |
        Infix _ _ _ _ |
        Prefix _ _ |
        Paren _ (Atom _ _) _ |
        Paren _ (Paren _ _ _) _ |
        Paren _ (Tuple _ _ _ _) _ |
        Paren _ (ListOf _ _ _ _) _ |
        Paren _ (App _ _) _ |
        Paren _ (Infix _ _ _ _) _ |
        Paren _ (Prefix _ _) _, joins => (elPasses kinds argument within joins around, byComputing)

--| A call's arguments: the documents before the last and the last, in order, each after a separator; the last's
--| hug passes as it does; and one document before the last for each argument but one.
--|
--| Proof idea: Induction on the arguments (`argumentDocsConsTest`), the words seen so far growing by each argument's.
theorem argumentsSeq ∀ (kinds: Text → Tok) (arm: Bool) (previous: Expr) (at: Nat)
    (arguments: List Expr) (seen: List Word)
    (filled: arguments ≠ [])
    (within: allWithin1 arguments = True)
    (joinable: AllJoinable kinds arguments):
    PassesSeq kinds
      (Gapped True)
      (Ended (trailsBack (seen ++ itemsWords arguments).reverse))
      ((argumentDocs arm previous at arguments).fst
        ++ [((argumentDocs arm previous at arguments).snd.getOrElse (Nothing, None)).fst])
      ∧ HugPasses kinds
        ((argumentDocs arm previous at arguments).snd.getOrElse (Nothing, None)).snd
        (Gapped True)
        (Ended (trailsBack (seen ++ itemsWords arguments).reverse))
      ∧ (argumentDocs arm previous at arguments).fst.length + 1 = arguments.length :=
  match arguments, joinable with
    | [], _ => (filled byComputing).impossible
    | [argument], (joins, _) =>
      let place := { before = previous.trails, hoisted = False, item = False, at, inArm = arm }
      let (lastPass, hugPass) := lastArgumentPasses kinds argument place (Bool.andLeft within) joins
      (
        passesFrom (passesTo lastPass (edge ended => itemTrails seen argument edge ended)) (edge gapped =>
          gappedReadyTrue kinds True argument.lead.text edge gapped),
        hugFrom kinds
          (lastArgument argument place).snd
          (Ready kinds True argument.lead.text)
          (Gapped True)
          (Ended argument.trails)
          (Ended (trailsBack (seen ++ itemsWords [argument]).reverse))
          hugPass
          (edge gapped => gappedReadyTrue kinds True argument.lead.text edge gapped)
          (edge ended => itemTrails seen argument edge ended),
        byComputing
      )
    | [argument, next, ..more], (joins, rest) =>
      let place := { before = previous.trails, hoisted = False, item = False, at, inArm = arm }
      let later := argumentDocs arm argument (at + argument.size) [next, ..more]
      let (seq, hugs, length) :=
        argumentsSeq kinds arm argument
          (at + argument.size)
          [next, ..more]
          (seen ++ argument.words)
          (List.consNotNil next more)
          (Bool.andRight within)
          rest
      (
        seqPrepend kinds
          (Gapped True)
          (Ended (trailsBack (seen ++ itemsWords [argument, next, ..more]).reverse))
          (argument.el place)
          (later.fst ++ [(later.snd.getOrElse (Nothing, None)).fst])
          (passesFrom
            (passesTo (elPasses kinds argument (Bool.andLeft within) joins place) (edge ended =>
              endedTrue argument.trails edge ended))
            (edge gapped => gappedReadyTrue kinds True argument.lead.text edge gapped))
          (rewrite List.appendAssoc seen argument.words (itemsWords [next, ..more]) at seq then seq)
          (List.snocNotNil later.fst (later.snd.getOrElse (Nothing, None)).fst),
        rewrite List.appendAssoc seen argument.words (itemsWords [next, ..more]) at hugs then hugs,
        arithmetic [length]
      )

--| A call: its function and arguments in one of `appFrom`'s layouts.
theorem appPasses ∀ (kinds: Text → Tok) (head: Expr) (arguments: List Expr) (around: Around)
    (headWithin: head.within1 = True)
    (within: allWithin1 arguments = True)
    (headJoins: Joinable kinds head)
    (joinable: AllJoinable kinds arguments)
    (filled: arguments ≠ []):
    Passes kinds
      (appDocs head arguments around).doc
      (Ready kinds True head.lead.text)
      (Ended (trailsBack (head.words ++ itemsWords arguments).reverse)) :=
  let pre := Ready kinds True head.lead.text
  let post := Ended (trailsBack (head.words ++ itemsWords arguments).reverse)
  let results := argumentDocs around.inArm head (around.at + head.size) arguments
  let front := results.fst
  let lastDoc := (results.snd.getOrElse (Nothing, None)).fst
  let (seq, hugs, length) :=
    argumentsSeq kinds around.inArm head (around.at + head.size) arguments head.words filled within joinable
  let short: 1 + keptFront head arguments ≤ ([head.el around, ..front] ++ [lastDoc]).length :=
    rewrite List.lengthAppend front [lastDoc] then arithmetic [keptShort head arguments, length]
  rewrite appDocsIsOneFirst head arguments around then
    appFromPasses kinds
      (around.at + 1)
      (1 + keptFront head arguments)
      (commentBetween head arguments)
      (commentBetween head (arguments.take (1 + keptFront head arguments - 1)))
      (head.el around)
      lastDoc
      front
      (results.snd.getOrElse (Nothing, None)).snd
      pre
      post
      (seqPrepend kinds pre post
        (head.el around)
        (front ++ [lastDoc])
        (passesTo (elPasses kinds head headWithin headJoins around) (edge ended => endedTrue head.trails edge ended))
        seq
        (List.snocNotNil front lastDoc))
      hugs
      (arithmetic)
      short

-- Operator chains.

theorem chainOfPasses ∀ (kinds: Text → Tok) (arms: Bool) (links: List Doc) (pre post: Edge → Prop)
    (all: PassesAll kinds links pre post)
    (filled: links ≠ []):
    Passes kinds (chainOf arms links) pre post :=
  match links, all with
    | [], _ => (filled byComputing).impossible
    | [head, ..tail], all =>
      let joined := Doc.concat [head, Nest (if arms then 0 else 2) (Doc.concat tail)]
      passesGroup joined.forcesBreak (passesHeadTail (if arms then 0 else 2) all)

theorem opTrails ∀ (left: List Word) (operator: Word) (right: List Word)
    (trails: trailsBack right.reverse = True):
    trailsBack (left ++ [operator, ..right]).reverse = True :=
  seenAppend left
    [operator, ..right]
    (rewrite List.reverseCons operator right then trailsBackAppend right.reverse [operator] trails)

--| What follows a chain's operator: a space and the operand.
theorem chainRightPasses ∀ (kinds: Text → Tok) (level: Option Nat) (right: Expr) (place: Around)
    (within: right.within1 = True)
    (joinable: Joinable kinds right):
    PassesAll kinds (chainRight level right place) (Ended True) (Ended right.trails) :=
  let rest: PassesAll kinds (linkDocs level False right place) (Gapped True) (Ended right.trails) :=
    allFrom (linkDocsPasses kinds level False right place within joinable) (edge gapped =>
      gappedReadyTrue kinds True right.lead.text edge gapped)
  let spaced: PassesAll kinds [Doc.text " ", ..linkDocs level False right place] (Ended True) (Ended right.trails) :=
    passesCons (passesSpace kinds True) rest
  match right with
    | Atom _ _ | Paren _ _ _ | Tuple _ _ _ _ | ListOf _ _ _ _ | App _ _ | Infix _ _ _ _ | Prefix _ _ => spaced

--| A chain's links: the first operand's, then each operator after a separator and its operand after a space.
theorem chainLinksPasses ∀ (kinds: Text → Tok) (level: Option Nat) (first: Bool) (left: Expr) (operator: Word)
    (right: Expr) (around: Around)
    (leftWithin: left.within1 = True)
    (rightWithin: right.within1 = True)
    (leftJoins: Joinable kinds left)
    (operatorJoins: WordJoins operator)
    (rightJoins: Joinable kinds right):
    PassesAll kinds
      (chainLinks level first left operator right around)
      (Ready kinds True left.lead.text)
      (Ended (trailsBack (left.words ++ [operator, ..right.words]).reverse)) :=
  let operatorAround := around.next left.trails left.size
  let rightAround := around.next operator.trails (left.size + 1)
  let leaf := operator.leaf operatorAround operatorAround.at
  let post := Ended (trailsBack (left.words ++ [operator, ..right.words]).reverse)
  passesAppend
    (linkDocsPasses kinds level first left around leftWithin leftJoins)
    (passesCons
      (passesLine kinds left.trails)
      (passesCons
        (passesFrom
          (passesTo (wordLeafPasses kinds operator operatorAround operatorAround.at operatorJoins) (edge left =>
            endedTrue operator.trails edge
              (leftEnded operator.text operator.trails operatorJoins.right.left edge left)))
          (edge gapped => gappedReadyTrue kinds left.trails operator.text edge gapped))
        (allTo (chainRightPasses kinds level right rightAround rightWithin rightJoins) (edge ended =>
          endedWeaker right.trails _ (opTrails left.words operator right.words) edge ended))))

--| A chain operand's documents: the links of a chain of the same level, else the element.
theorem linkDocsPasses ∀ (kinds: Text → Tok) (level: Option Nat) (first: Bool) (expr: Expr) (around: Around)
    (within: expr.within1 = True)
    (joinable: Joinable kinds expr):
    PassesAll kinds (linkDocs level first expr around) (Ready kinds True expr.lead.text) (Ended expr.trails) :=
  let element: PassesAll kinds [expr.el around] (Ready kinds True expr.lead.text) (Ended expr.trails) :=
    passesLast (elPasses kinds expr within joinable around)
  match expr, joinable with
    | Atom _ _ | Paren _ _ _ | Tuple _ _ _ _ | ListOf _ _ _ _ | App _ _ | Prefix _ _, _ => element
    | Infix kind left operator right, (leftJoins, operatorJoins, rightJoins) =>
      match kind with
        | InfixBinary | InfixArrow =>
          match inChain: (Infix kind left operator right).inChain level with
            | True =>
              chainLinksPasses kinds level first left operator right around
                (Bool.andLeft within)
                (Bool.andLeft (Bool.andRight within))
                leftJoins
                operatorJoins
                rightJoins
            | False => element
        | _ => cases

--| An operator chain's element.
theorem chainPasses ∀ (kinds: Text → Tok) (level: Option Nat) (left: Expr) (operator: Word)
    (right: Expr) (around: Around)
    (leftWithin: left.within1 = True)
    (rightWithin: right.within1 = True)
    (leftJoins: Joinable kinds left)
    (operatorJoins: WordJoins operator)
    (rightJoins: Joinable kinds right):
    Passes kinds
      (chain level left operator right around)
      (Ready kinds True left.lead.text)
      (Ended (trailsBack (left.words ++ [operator, ..right.words]).reverse)) :=
  chainOfPasses kinds
    (left.opensArms level)
    (chainLinks level True left operator right around)
    (Ready kinds True left.lead.text)
    (Ended (trailsBack (left.words ++ [operator, ..right.words]).reverse))
    (chainLinksPasses kinds level True left operator right around leftWithin rightWithin leftJoins operatorJoins
        rightJoins)
    (List.appendNotNilRight (linkDocs level True left around) _ (List.consNotNil Line _))

-- The induction.

--| Wherever an expression stands, its element joins from where its first token may stand and leaves the line ending
--| with a token, a comment waiting only if the expression ends with one.
--|
--| Proof idea: Induction on the expression, as `elSpells`: each node by its rule's lemma inside `framedExprPasses`,
--| the parts by the induction.
theorem elPasses ∀ (kinds: Text → Tok) (expr: Expr)
    (within: expr.within1 = True)
    (joinable: Joinable kinds expr) (around: Around):
    Passes kinds (expr.el around) (Ready kinds True expr.lead.text) (Ended expr.trails) :=
  let inside := { around | hoisted = True }
  match expr, joinable with
    | Atom kind word, joins => atomPasses kinds kind word around joins
    | Paren open inner close, (opener, closer, innerJoins) =>
      framedExprPasses kinds
        (Paren open inner close)
        around _ _
        within
        (opener, closer, innerJoins)
        (parenPasses kinds open inner close inside within opener closer (place =>
          elPasses kinds inner within innerJoins place))
    | Tuple open items comma close, (opener, closer, each) =>
      framedExprPasses kinds
        (Tuple open items comma close)
        around
        (commaBracket False open items close inside) _
        within
        (opener, closer, each)
        (commaBracketPasses kinds False open items close inside opener closer (allElPasses kinds items within each))
    | ListOf open items comma close, (opener, closer, each) =>
      framedExprPasses kinds
        (ListOf open items comma close)
        around
        (commaBracket True open items close inside) _
        within
        (opener, closer, each)
        (commaBracketPasses kinds True open items close inside opener closer (allElPasses kinds items within each))
    | App head arguments, (headJoins, each, filled) =>
      framedExprPasses kinds
        (App head arguments)
        around _ _
        within
        (headJoins, each, filled)
        (appPasses kinds head arguments inside (Bool.andLeft within) (Bool.andRight within) headJoins each filled)
    | Infix kind left operator right, (leftJoins, operatorJoins, rightJoins) =>
      match kind with
        | InfixBinary | InfixArrow =>
          framedExprPasses kinds
            (Infix kind left operator right)
            around _ _
            within
            (leftJoins, operatorJoins, rightJoins)
            (chainPasses kinds _ left operator right inside
              (Bool.andLeft within)
              (Bool.andLeft (Bool.andRight within))
              leftJoins
              operatorJoins
              rightJoins)
        | _ => cases
    | Prefix operator operand, (joins, operandJoins, glue) =>
      framedExprPasses kinds
        (Prefix operator operand)
        around _ _
        within
        (joins, operandJoins, glue)
        (prefixPasses kinds operator operand around joins glue (place =>
          elPasses kinds operand (Bool.andLeft within) operandJoins place))

-- Hugs.

--| A call's hug: the function and the arguments before the last flattened, a space, and the last opened.
theorem appFromHugPasses ∀ (kinds: Text → Tok) (id keep: Nat) (between betweenFront: Bool) (headDoc lastDoc: Doc)
    (front: List Doc) (hug: Option Doc) (pre post: Edge → Prop)
    (seq: PassesSeq kinds pre post ([headDoc, ..front] ++ [lastDoc]))
    (hugPasses: HugPasses kinds hug (Gapped True) post):
    HugPasses kinds (appFrom id keep between betweenFront headDoc front lastDoc hug).hug pre post :=
  let docs := [headDoc, ..front] ++ [lastDoc]
  match full: keep == docs.length with
    | True => byComputing
    | False =>
      match hug, hugPasses with
        | None, _ => byComputing
        | Some open, opens =>
          let (headSeq, _) :=
            splitSeq kinds
              [headDoc, ..front]
              [lastDoc]
              pre
              post
              (List.consNotNil headDoc front)
              (List.consNotNil lastDoc [])
              seq
          passesConcat
            [docs := [Flatten (spaced [headDoc, ..front]), Doc.text " ", open]]
            (passesCons
              (passesFlatten (spacedSeq kinds [headDoc, ..front] pre (Ended True) headSeq))
              (passesTwo (passesSpace kinds True) opens))

theorem callHugPasses ∀ (kinds: Text → Tok) (value: Expr) (inside: Around)
    (within: value.within1 = True)
    (joinable: Joinable kinds value):
    HugPasses kinds (value.callHug inside) (Ready kinds True value.lead.text) (Ended value.trails) :=
  match value, joinable with
    | App head arguments, (headJoins, each, filled) =>
      let pre := Ready kinds True head.lead.text
      let post := Ended (trailsBack (head.words ++ itemsWords arguments).reverse)
      let results := argumentDocs inside.inArm head (inside.at + head.size) arguments
      let front := results.fst
      let lastDoc := (results.snd.getOrElse (Nothing, None)).fst
      let (seq, hugs, _) :=
        argumentsSeq kinds inside.inArm head
          (inside.at + head.size)
          arguments
          head.words
          filled
          (Bool.andRight within)
          each
      rewrite appDocsIsOneFirst head arguments inside then
        appFromHugPasses kinds
          (inside.at + 1)
          (1 + keptFront head arguments)
          (commentBetween head arguments)
          (commentBetween head (arguments.take (1 + keptFront head arguments - 1)))
          (head.el inside)
          lastDoc
          front
          (results.snd.getOrElse (Nothing, None)).snd
          pre
          post
          (seqPrepend kinds pre post
            (head.el inside)
            (front ++ [lastDoc])
            (passesTo (elPasses kinds head (Bool.andLeft within) headJoins inside) (edge ended =>
              endedTrue head.trails edge ended))
            seq
            (List.snocNotNil front lastDoc))
          hugs
    | Atom _ _ | Paren _ _ _ | Tuple _ _ _ _ | ListOf _ _ _ _ | Infix _ _ _ _ | Prefix _ _, _ => byComputing

-- The body after `:=`.

theorem eachAppend ∀ (kinds: Text → Tok) (pre post: Edge → Prop) (front back: List Doc)
    (first: EachPasses kinds pre post front)
    (second: EachPasses kinds pre post back):
    EachPasses kinds pre post (front ++ back) :=
  match front, first with
    | [], _ => second
    | [doc, ..rest], (passes, others) => (passes, eachAppend kinds pre post rest back others second)

theorem spacedHugsPass ∀ (kinds: Text → Tok) (hug: Option Doc) (post: Edge → Prop)
    (passes: HugPasses kinds hug (Gapped True) post):
    EachPasses kinds (Ended True) post (optionList (hug.map (open => Doc.concat [Doc.text " ", open]))) :=
  match hug, passes with
    | None, _ => byComputing
    | Some open, opens => (passesConcat (passesTwo (passesSpace kinds True) opens), byComputing)

--| What follows a `:=`: the value below, or one of the layouts that keep its start on the line.
--|
--| Proof idea: `matchedNone`, `valueElPlain` and `lambdaHugNone` leave the value's element; each option is it after
--| a space or a line break, or the call's hug after a space (`callHugPasses`).
theorem bodyAfterPasses ∀ (kinds: Text → Tok) (value: Expr) (assign: Word) (around: Around)
    (semi: Bool) (post: Edge → Prop)
    (within: value.within1 = True)
    (joinable: Joinable kinds value) (ends: ∀ (edge: Edge) => Ended value.trails edge → post edge):
    Passes kinds (bodyAfter value assign around semi).fst (Ended True) post
      ∧ Passes kinds (bodyAfter value assign around semi).snd (Ended True) post :=
  let inside: Around := { around | hoisted = True }
  let ready := Ready kinds True value.lead.text
  let element: Passes kinds (value.el around) ready post := passesTo (elPasses kinds value within joinable around) ends
  let afterGap: Passes kinds (value.el around) (Gapped True) post :=
    passesFrom element (edge gapped => gappedReadyTrue kinds True value.lead.text edge gapped)
  let spacedPass: Passes kinds (Doc.concat [Doc.text " ", value.el around]) (Ended True) post :=
    passesConcat (passesTwo (passesSpace kinds True) afterGap)
  let below: Passes kinds (Nest 2 (Doc.concat [HardLine, value.el around])) (Ended True) post :=
    passesNest 2 (passesConcat (passesTwo (passesHard kinds (Ended True) ready byComputing) element))
  let lowered: Passes kinds (OneLineBelow (value.el around)) (Ended True) post :=
    passesOneLineBelow (Ended True) (passesFrom element (edge fresh => rewrite fresh))
  let hugs := callHugPasses kinds value inside within joinable
  rewrite matchedNone value inside within,
      valueElPlain value around semi within,
      lambdaHugNone value semi inside (value.el around) within then
    match plain: assign.trails || value.noted || value.isBlock with
      | True => (below, below)
      | False => (
        below,
        passesChoiceOf _
          (passesFlatten spacedPass)
          (eachAppend kinds
            (Ended True)
            post
            (if value.opensBracket || (value.callHug inside).isSome then [OneLineBelow (value.el around)] else [])
            ((if value.opensBracket then [Doc.concat [Doc.text " ", value.el around]]
              else optionList ((value.callHug inside).map (open => Doc.concat [Doc.text " ", open])))
              ++ [Nest 2 (Doc.concat [HardLine, value.el around])])
            (match value.opensBracket || (value.callHug inside).isSome with
              | True => (lowered, byComputing)
              | False => byComputing)
            (eachAppend kinds
              (Ended True)
              post
              (if value.opensBracket then [Doc.concat [Doc.text " ", value.el around]]
               else optionList ((value.callHug inside).map (open => Doc.concat [Doc.text " ", open])))
              [Nest 2 (Doc.concat [HardLine, value.el around])]
              (match value.opensBracket with
                | True => (spacedPass, byComputing)
                | False =>
                  spacedHugsPass kinds
                    (value.callHug inside)
                    post
                    (hugFrom kinds
                      (value.callHug inside)
                      ready
                      (Gapped True)
                      (Ended value.trails)
                      post
                      hugs
                      (edge gapped => gappedReadyTrue kinds True value.lead.text edge gapped)
                      ends))
              (below, byComputing)))
      )

-- Declarations.

theorem endedReadyColon ∀ (kinds: Text → Tok) (trails: Bool) (edge: Edge)
    (ended: Ended trails edge):
    Ready kinds trails ":" edge :=
  cases edge then followsStops kinds _ ":" ':' ended byComputing stopsColon

--| A token that is no closer, then the line ends with it.
theorem wordEnds ∀ (kinds: Text → Tok) (word: Word) (around: Around) (key: Nat)
    (joins: WordJoins word):
    Passes kinds (word.leaf around key) (Ready kinds True word.text) (Ended True) :=
  passesTo (wordLeafPasses kinds word around key joins) (edge left =>
    endedTrue word.trails edge (leftEnded word.text word.trails joins.right.left edge left))

theorem wordAfterGap ∀ (kinds: Text → Tok) (word: Word) (around: Around) (key: Nat)
    (joins: WordJoins word):
    Passes kinds (word.leaf around key) (Gapped True) (Ended True) :=
  passesFrom (wordEnds kinds word around key joins) (edge gapped => gappedReadyTrue kinds True word.text edge gapped)

--| A definition's type: below the `:` if a comment follows it, else after a space.
theorem typedPasses ∀ (kinds: Text → Tok) (trails: Bool) (typeDoc: Doc) (first: Text)
    (typePass: Passes kinds typeDoc (Ready kinds True first) (Ended True)):
    PassesAll kinds
      (if trails then [Nest 4 (Doc.concat [HardLine, typeDoc])] else [Doc.text " ", Nest 4 typeDoc])
      (Ended True)
      (Ended True) :=
  match trails with
    | True =>
      passesLast
        (passesNest 4
          (passesConcat (passesTwo (passesHard kinds (Ended True) (Ready kinds True first) byComputing) typePass)))
    | False =>
      passesTwo
        (passesSpace kinds True)
        (passesNest 4 (passesFrom typePass (edge gapped => gappedReadyTrue kinds True first edge gapped)))

--| A plain definition: its keyword, name, `:`, type, `:=` and body, from the start of a line.
--|
--| Proof idea: The header's tokens one after another with spaces (`spacedSeq`), the `:` after any token
--| (`endedReadyColon`), the type after a space or a line break, then the `:=` after a space and the body
--| (`bodyAfterPasses`) in either of `IfBroken`'s forms.
theorem plainDefPasses ∀ (kinds: Text → Tok) (keyword: Comments) (name: Word) (colon: Comments) (result: Expr)
    (colonEq: Comments) (value: Expr) (post: Edge → Prop)
    (resultWithin: result.within1 = True)
    (valueWithin: value.within1 = True)
    (keywordJoins: WordJoins (fixedWord "def" keyword))
    (nameJoins: WordJoins name)
    (colonJoins: WordJoins (fixedWord ":" colon))
    (resultJoins: Joinable kinds result)
    (assignJoins: WordJoins (fixedWord ":=" colonEq))
    (valueJoins: Joinable kinds value) (ends: ∀ (edge: Edge) => Ended value.trails edge → post edge):
    Passes kinds (plainDef keyword name colon result colonEq value) (Ready kinds True "def") post :=
  let start: Around := { before = False, hoisted = True, item = False, at = 0, inArm = False }
  let keywordWord := fixedWord "def" keyword
  let colonWord := fixedWord ":" colon
  let assign := fixedWord ":=" colonEq
  let colonAround := start.next (trailsBack [name, keywordWord]) 2
  let typeDoc := result.el (start.next colonWord.trails 3)
  let headDoc := spaced (headDocs start [keywordWord, name])
  let typed := if colonWord.trails then [Nest 4 (Doc.concat [HardLine, typeDoc])] else [Doc.text " ", Nest 4 typeDoc]
  let headerDoc := Doc.concat ([headDoc, colonWord.leaf colonAround 2] ++ typed)
  let typeReady := Ready kinds True result.lead.text
  let typePass: Passes kinds typeDoc typeReady (Ended True) :=
    passesTo (elPasses kinds result resultWithin resultJoins (start.next colonWord.trails 3)) (edge ended =>
      endedTrue result.trails edge ended)
  let headPass: Passes kinds headDoc (Ready kinds True "def") (Ended True) :=
    spacedSeq kinds
      [keywordWord.leaf start 0, name.leaf (start.next keywordWord.trails 1) 1]
      (Ready kinds True "def")
      (Ended True)
      (
        wordEnds kinds keywordWord start 0 keywordJoins,
        wordAfterGap kinds name (start.next keywordWord.trails 1) 1 nameJoins
      )
  let colonPass: Passes kinds (colonWord.leaf colonAround 2) (Ended True) (Ended True) :=
    passesFrom (wordEnds kinds colonWord colonAround 2 colonJoins) (edge ended => endedReadyColon kinds True edge ended)
  let typedPass: PassesAll kinds typed (Ended True) (Ended True) :=
    typedPasses kinds colonWord.trails typeDoc result.lead.text typePass
  let headerPass: Passes kinds headerDoc (Ready kinds True "def") (Ended True) :=
    passesConcat (passesCons headPass (passesCons colonPass typedPass))
  let body := bodyAfter value assign (start.next assign.trails (4 + result.size)) False
  let (belowPass, choicePass) :=
    bodyAfterPasses kinds value assign
      (start.next assign.trails (4 + result.size))
      False
      post
      valueWithin
      valueJoins
      ends
  let assignLeaf := assign.leaf (start.next result.trails (3 + result.size)) (3 + result.size)
  let breaks :=
    headerDoc.forcesBreak
      || (([keywordWord, name].reverse.drop 1 |> .any Word.trails)
        || colonWord.trails
        || (result.words.reverse.drop 1 |> .any Word.trails)
        || (value.layoutBody && (lastCode [keywordWord, name]).trails))
  passesConcat
    (passesCons
      (passesIdGroup 0 breaks headerPass)
      (passesCons
        (passesSpace kinds True)
        (passesTwo
          (wordAfterGap kinds assign (start.next result.trails (3 + result.size)) (3 + result.size) assignJoins)
          (passesIfBroken 0 belowPass choicePass))))

--| What `printLexes1` needs of a declaration's tokens, beyond its words being `Printable`: each may be followed
--| as the rules print it (`WordJoins`, `Joinable`). It is the tree-side leaf statement that read-back reads.
def DeclJoins (kinds: Text → Tok): Decl → Prop
  | Definition [] header (Assigned colonEq value) =>
    WordJoins (fixedWord header.kind.keywordText header.keyword)
      ∧ WordJoins header.name
      ∧ WordJoins (fixedWord ":" header.colon)
      ∧ Joinable kinds header.result
      ∧ WordJoins (fixedWord ":=" colonEq)
      ∧ Joinable kinds value
  | _ => False

--| A slice 1 declaration's document joins from the start of a line.
theorem doc1Passes ∀ (kinds: Text → Tok) (decl: Decl) (doc: Doc)
    (within: decl.within1 = True)
    (joins: DeclJoins kinds decl)
    (shows: decl.doc1 = Some doc):
    Joins (Follows kinds) doc (Plain None) (after => True) :=
  match decl, joins with
    | Definition [] header (Assigned colonEq value), (keywordJoins, nameJoins, colonJoins, resultJoins, assignJoins,
        valueJoins) =>
      match header with
        | {
            exportKeyword = None,
            opaqueKeyword = None,
            kind = DefPlain,
            keyword,
            name,
            forallKeyword = None,
            params = [],
            colon,
            result,
            decreasingClause = None,
            unfoldingClause = None
          } =>
          rewrite <- Option.someInjective shows, plainDefIs keyword name colon result colonEq value then
            plainDefPasses kinds keyword name colon result colonEq value
              (after => True)
              (Bool.andRight (Bool.andLeft within))
              (Bool.andRight within)
              keywordJoins
              nameJoins
              colonJoins
              resultJoins
              assignJoins
              valueJoins
              (edge ended => byComputing)
              (Plain None)
              (after => True)
              byComputing
              (after holds => holds)

--| `printLexes1`: the text the rules print for a slice 1 declaration, at any width, lexes to the leaves of the
--| printed pieces' layout, given that its words are `Printable` (each piece lexes as its kind says) and its tokens
--| join as the rules print them (`DeclJoins`).
--|
--| Proof idea: `doc1Spells` gives `Uniform` and the document's words; `doc1Passes` gives `Joins`; `printedLexes`
--| does the rest.
theorem printLexes1 ∀ (kinds: Text → Tok) (decl: Decl) (doc: Doc) (width: Nat)
    (within: decl.within1 = True)
    (sound: decl.sound = True)
    (joins: DeclJoins kinds decl)
    (printable: Every (Printable kinds) decl.spelt)
    (shows: decl.doc1 = Some doc):
    lex (Doc.print doc width)
      = Ok {
        leaves = ((pieceFold kinds (printedPieces doc width)).foldLeft Laid.start Laid.lay).leaves.reverse,
        end = {
          leading = ((pieceFold kinds (printedPieces doc width)).foldLeft Laid.start Laid.lay).pending.reverse,
          blankLines = ((pieceFold kinds (printedPieces doc width)).foldLeft Laid.start Laid.lay).blankRun,
          trailing = None
        }
      } :=
  let (uniform, _, words) := doc1Spells decl doc within sound shows
  printedLexes doc width kinds uniform (doc1Passes kinds decl doc within joins shows) (rewrite words then printable)
