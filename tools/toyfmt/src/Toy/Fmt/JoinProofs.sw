--| The rules' half of "what the printer puts next to what": the document
--| the rules build for a tree whose texts are the lexer's (`LexicalFile`)
--| joins (`Joins standsBefore`, `fileJoins`), and its words are all
--| `Proper`. So by the engine's half (`joinedPlaced`) a file printed at any
--| width lexes to its pieces (`printedTokens`).
--|
--| Each rule is a triple (`Passes doc pre post`): from every edge that
--| satisfies `pre`, the document joins and leaves an edge that satisfies
--| `post`. The edges are few: after layout (`Loose`), after a bracket or
--| dot, before which anything may come next (`Free`), after a token that
--| a space or a closing sign may follow (`Meets`), and after one token
--| in particular (`Left`).

namespace Toy.Fmt.Proofs
import Toy.Doc (..)
import Toy.Doc.Proofs (..)
import Toy.Syntax (..)
import Toy.Syntax.Proofs (..)
import Toy.Fmt (..)
import Std (Bool, DecEq, Eq, List, Option, Parse, Text, Void)

-- The edges.

--| Any edge.
def Open (edge: Edge): Prop := True

--| After layout, or with a comment waiting: what comes next starts
--| fresh.
def Loose (edge: Edge): Prop := match edge with
  | Plain (Some word) => False
  | _ => True

--| Anything may come next.
def Free (edge: Edge): Prop := match edge with
  | Plain (Some word) => ∀ (next: Text) => standsBefore word next
  | _ => True

--| A space, a closing bracket, a comma, a dot or `(` may come next.
def Meets (edge: Edge): Prop := match edge with
  | Plain (Some word) => ∀ (next: Text) => Closing next → standsBefore word next
  | _ => True

--| `text` may come next.
def Admits (text: Text) (edge: Edge): Prop := match edge with
  | Plain (Some word) => standsBefore word text
  | _ => True

--| Straight after `text`, or after its trailing comment.
def Left (text: Text) (edge: Edge): Prop := match edge with
  | Plain (Some word) => word = text
  | Plain None => False
  | Edge.Waiting => True

--| `expr` may come next: its first token is `-` or starts with no
--| operator character.
def Enters (expr: Expr) (edge: Edge): Prop := match edge with
  | Plain (Some word) =>
    (∀ (text: Text) => Opens text → standsBefore word text) ∧ (expr.startsWithMinus = True → standsBefore word "-")
  | _ => True

theorem looseFree ∀ (edge: Edge) (loose: Loose edge): Free edge := match edge, loose with
  | Plain None, _ => rfl
  | Edge.Waiting, _ => rfl
  | Plain (Some word), never => Void.exfalso (Bool.falseNotTrue never)

theorem freeMeets ∀ (edge: Edge) (free: Free edge): Meets edge := match edge, free with
  | Plain None, _ => rfl
  | Edge.Waiting, _ => rfl
  | Plain (Some word), any => (following closing => any following)

theorem looseMeets ∀ (edge: Edge) (loose: Loose edge): Meets edge := freeMeets edge (looseFree edge loose)

theorem freeAdmits ∀ (text: Text) (edge: Edge) (free: Free edge): Admits text edge := match edge, free with
  | Plain None, _ => rfl
  | Edge.Waiting, _ => rfl
  | Plain (Some word), any => any text

theorem looseAdmits ∀ (text: Text) (edge: Edge) (loose: Loose edge): Admits text edge :=
  freeAdmits text edge (looseFree edge loose)

theorem meetsAdmits ∀ (text: Text) (closing: Closing text) (edge: Edge) (meets: Meets edge): Admits text edge :=
  match edge, meets with
    | Plain None, _ => rfl
    | Edge.Waiting, _ => rfl
    | Plain (Some word), any => any text closing

theorem freeEnters ∀ (expr: Expr) (edge: Edge) (free: Free edge): Enters expr edge := match edge, free with
  | Plain None, _ => rfl
  | Edge.Waiting, _ => rfl
  | Plain (Some word), any => Both (text opens => any text) (minus => any "-")

theorem looseEnters ∀ (expr: Expr) (edge: Edge) (loose: Loose edge): Enters expr edge :=
  freeEnters expr edge (looseFree edge loose)

theorem entersAdmits ∀ (expr: Expr) (text: Text)
    (opens: Opens text) (edge: Edge)
    (enters: Enters expr edge):
    Admits text edge :=
  match edge, enters with
    | Plain None, _ => rfl
    | Edge.Waiting, _ => rfl
    | Plain (Some word), Both any _ => any text opens

theorem leftMeets ∀ (text: Text) (ends: Ends text) (edge: Edge) (left: Left text edge): Meets edge :=
  match edge, left with
    | Plain None, never => Void.exfalso (Bool.falseNotTrue never)
    | Edge.Waiting, _ => rfl
    | Plain (Some word), same => rewrite same in (following closing => endsBefore text following ends closing)

theorem leftFree ∀ (text: Text) (free: ∀ (next: Text) => standsBefore text next) (edge: Edge)
    (left: Left text edge):
    Free edge :=
  match edge, left with
    | Plain None, never => Void.exfalso (Bool.falseNotTrue never)
    | Edge.Waiting, _ => rfl
    | Plain (Some word), same => rewrite same in free

--| After a `-`, an expression that doesn't start with one.
theorem minusEnters ∀ (operand: Expr) (edge: Edge)
    (plain: operand.startsWithMinus = False)
    (left: Left "-" edge):
    Enters operand edge :=
  match edge, left with
    | Plain None, never => Void.exfalso (Bool.falseNotTrue never)
    | Edge.Waiting, _ => rfl
    | Plain (Some word), same =>
      rewrite same in
        Both (text opens => minusBefore text opens) (minus =>
          Void.exfalso (Bool.falseNotTrue (Eq.trans (Eq.sym plain) minus)))

theorem closingSpace: Closing " " := later => Both rfl (Both rfl rfl)

theorem closingOpen: Closing "(" := later => Both rfl (Both rfl rfl)

theorem closingClose: Closing ")" := later => Both rfl (Both rfl rfl)

theorem closingSquare: Closing "]" := later => Both rfl (Both rfl rfl)

theorem closingComma: Closing "," := later => Both rfl (Both rfl rfl)

theorem closingDot: Closing "." := later => Both rfl (Both rfl rfl)

-- The triples.

--| From every edge that satisfies `pre`, `doc` joins and leaves an edge
--| that satisfies `post`; and its words are proper.
def Passes (doc: Doc) (pre post: Edge → Prop): Prop :=
  AllProper doc.words
    ∧ (∀ (edge: Edge) => ∀ (next: Edge → Prop) => pre edge
      → (∀ (after: Edge) => post after → next after)
      → Joins standsBefore doc edge next)

def PassesAll (docs: List Doc) (pre post: Edge → Prop): Prop :=
  AllProper (wordsAll docs)
    ∧ (∀ (edge: Edge) => ∀ (next: Edge → Prop) => pre edge
      → (∀ (after: Edge) => post after → next after)
      → JoinsAll standsBefore docs edge next)

theorem properAppend ∀ (front back: List Text)
    (first: AllProper front)
    (second: AllProper back):
    AllProper (front ++ back) :=
  match front, first with
    | [], _ => second
    | [piece, ..rest], Both head others => Both head (properAppend rest back others second)

theorem properWord ∀ (text: Text) (proper: Proper text): AllProper (wordsOf [text]) := match layout: isLayout text with
  | True => rfl
  | False => Both proper rfl

theorem passesFrom ∀ (doc: Doc) (pre weaker post: Edge → Prop)
    (passes: Passes doc pre post) (implies: ∀ (edge: Edge) => weaker edge → pre edge):
    Passes doc weaker post :=
  match passes with
    | Both proper joins => Both proper (edge next holds after => joins edge next (implies edge holds) after)

theorem passesTo ∀ (doc: Doc) (pre post weaker: Edge → Prop)
    (passes: Passes doc pre post) (implies: ∀ (edge: Edge) => post edge → weaker edge):
    Passes doc pre weaker :=
  match passes with
    | Both proper joins =>
      Both proper (edge next holds after => joins edge next holds (left reached => after left (implies left reached)))

theorem allFrom ∀ (docs: List Doc) (pre weaker post: Edge → Prop)
    (passes: PassesAll docs pre post) (implies: ∀ (edge: Edge) => weaker edge → pre edge):
    PassesAll docs weaker post :=
  match passes with
    | Both proper joins => Both proper (edge next holds after => joins edge next (implies edge holds) after)

theorem allTo ∀ (docs: List Doc) (pre post weaker: Edge → Prop)
    (passes: PassesAll docs pre post) (implies: ∀ (edge: Edge) => post edge → weaker edge):
    PassesAll docs pre weaker :=
  match passes with
    | Both proper joins =>
      Both proper (edge next holds after => joins edge next holds (left reached => after left (implies left reached)))

theorem passesNil ∀ (pre post: Edge → Prop) (implies: ∀ (edge: Edge) => pre edge → post edge): PassesAll [] pre post :=
  Both rfl (edge next holds after => after edge (implies edge holds))

theorem passesCons ∀ (doc: Doc) (docs: List Doc) (pre middle post: Edge → Prop)
    (first: Passes doc pre middle)
    (rest: PassesAll docs middle post):
    PassesAll [doc, ..docs] pre post :=
  match first, rest with
    | Both proper joins, Both restProper restJoins =>
      Both (properAppend doc.words (wordsAll docs) proper restProper) (edge next holds after =>
        joins edge (between => JoinsAll standsBefore docs between next) holds (between reached =>
          restJoins between next reached after))

--| The last of a list.
theorem passesLast ∀ (doc: Doc) (pre post: Edge → Prop) (only: Passes doc pre post): PassesAll [doc] pre post :=
  passesCons doc [] pre post post only (passesNil post post (edge holds => holds))

theorem emptyJoins ∀ (doc: Doc) (edge: Edge) (next: Edge → Prop)
    (empty: doc.isEmpty = True)
    (joins: Joins standsBefore doc edge next):
    next edge :=
  match doc, empty, joins with | Empty, _, joins => joins

theorem filterJoins ∀ (docs: List Doc) (edge: Edge) (next: Edge → Prop)
    (joins: JoinsAll standsBefore docs edge next):
    JoinsAll standsBefore (docs.filter (doc => not doc.isEmpty)) edge next :=
  match docs, joins with
    | [], joins => joins
    | [doc, ..rest], joins =>
      match empty: doc.isEmpty with
        | True =>
          filterJoins rest edge next
            (emptyJoins doc edge (between => JoinsAll standsBefore rest between next) empty joins)
        | False =>
          joinsWeaker standsBefore doc edge
            (between => JoinsAll standsBefore rest between next)
            (between => JoinsAll standsBefore (rest.filter (doc => not doc.isEmpty)) between next)
            (between later => filterJoins rest between next later)
            joins

--| `Doc.concat` joins as the documents one after another.
theorem concatJoins ∀ (docs: List Doc) (edge: Edge) (next: Edge → Prop)
    (joins: JoinsAll standsBefore docs edge next):
    Joins standsBefore (Doc.concat docs) edge next :=
  let kept := filterJoins docs edge next joins
  match found: docs.filter (doc => not doc.isEmpty) with
    | [] => kept
    | [only] =>
      joinsWeaker standsBefore only edge
        (between => JoinsAll standsBefore [] between next)
        next
        (between reached => reached)
        kept
    | [first, second, ..rest] => kept

theorem passesConcat ∀ (docs: List Doc) (pre post: Edge → Prop)
    (each: PassesAll docs pre post):
    Passes (Doc.concat docs) pre post :=
  match each with
    | Both proper joins => Both (rewrite concatWords docs in proper) (edge next holds after =>
      concatJoins docs edge next (joins edge next holds after))

theorem passesTwo ∀ (first second: Doc) (pre middle post: Edge → Prop)
    (one: Passes first pre middle)
    (other: Passes second middle post):
    Passes (Doc.concat [first, second]) pre post :=
  passesConcat
    [first, second]
    pre
    post
    (passesCons first [second] pre middle post one (passesLast second middle post other))

-- The leaves.

theorem gapSolid ∀ (text: Text) (noGap: text.all (char => char == ' ') = False): gapOr text = text :=
  rewrite noGap in rfl

theorem touchSolid ∀ (text: Text) (layout: isLayout text = False): textTouch text = Some text := rewrite layout in rfl

theorem textJoins ∀ (text: Text) (edge: Edge) (next: Edge → Prop)
    (solid: Solid text)
    (admits: Admits text edge) (reached: next (Plain (Some text))):
    WriteJoins standsBefore edge text next :=
  match solid with
    | Both filled (Both noGap layout) =>
      let touched: next (Plain (textTouch text)) := rewrite touchSolid text layout in reached
      match text.isEmpty, filled with
        | True, never => Void.exfalso (Bool.falseNotTrue (Eq.sym never))
        | False, _ =>
          match edge, admits with
            | Plain None, _ => Both rfl touched
            | Plain (Some word), ok => Both (rewrite gapSolid text noGap in ok) touched
            | Edge.Waiting, _ =>
              match text.all (char => char == ' '), noGap with
                | False, _ => touched

--| A word: after anything it may follow, and then the line ends with it.
theorem passesText ∀ (text: Text)
    (solid: Solid text)
    (proper: Proper text):
    Passes (Doc.text text) (Admits text) (edge => edge = Plain (Some text)) :=
  Both (properWord text proper) (edge next admits after => textJoins text edge next solid admits (after _ rfl))

--| A space, after anything a space may follow.
theorem passesSpace: Passes (Doc.text " ") Meets Loose := Both rfl (edge next meets after =>
  match edge, meets with
    | Plain None, _ => Both rfl (after (Plain None) rfl)
    | Plain (Some word), any => Both (any " " closingSpace) (after (Plain None) rfl)
    | Edge.Waiting, _ => after Edge.Waiting rfl)

--| The empty text `Negate` writes before an operand that doesn't start
--| with `-`.
theorem passesNothing ∀ (pre: Edge → Prop): Passes (Doc.text "") pre pre :=
  Both rfl (edge next holds after => after edge holds)

theorem passesLine: Passes Line Meets Loose := Both rfl (edge next meets after =>
  match edge, meets with
    | Plain None, _ => Both rfl (after (Plain None) rfl)
    | Plain (Some word), any => Both (any " " closingSpace) (after (Plain None) rfl)
    | Edge.Waiting, _ => after (Plain None) rfl)

theorem passesHard ∀ (pre: Edge → Prop): Passes HardLine pre Loose :=
  Both rfl (edge next holds after => after (Plain None) rfl)

theorem passesCommentEnd ∀ (pre: Edge → Prop): Passes CommentEnd pre Loose :=
  Both rfl (edge next holds after => after (Plain None) rfl)

theorem passesSoft ∀ (pre post: Edge → Prop) (keeps: ∀ (edge: Edge) => pre edge → post edge) (fresh: post (Plain None)):
    Passes SoftLine pre post :=
  Both rfl (edge next holds after =>
    match edge, holds with
      | Plain touching, holds => Both (after (Plain touching) (keeps (Plain touching) holds)) (after (Plain None) fresh)
      | Edge.Waiting, _ => after (Plain None) fresh)

theorem passesStart ∀ (pre: Edge → Prop): Passes LineStart pre Loose := Both rfl (edge next holds after =>
  match edge with
    | Plain touching => after (Plain None) rfl
    | Edge.Waiting => Both (after Edge.Waiting rfl) (after (Plain None) rfl))

theorem passesStartHere ∀ (pre: Edge → Prop): Passes LineStartHere pre Loose := Both rfl (edge next holds after =>
  match edge with
    | Plain touching => after (Plain None) rfl
    | Edge.Waiting => Both (after Edge.Waiting rfl) (after (Plain None) rfl))

theorem passesBelow ∀ (doc: Doc) (pre post: Edge → Prop) (passes: Passes doc Loose post): Passes (below doc) pre post :=
  passesTwo HardLine doc pre Loose post (passesHard pre) passes

theorem passesOneLineBelow ∀ (doc: Doc) (pre post: Edge → Prop)
    (passes: Passes doc Loose post):
    Passes (OneLineBelow doc) pre post :=
  match passes with | Both proper joins => Both proper (edge next holds after => joins (Plain None) next rfl after)

theorem passesChoiceTwo ∀ (first second: Doc) (pre post: Edge → Prop)
    (one: Passes first pre post)
    (other: Passes second pre post):
    Passes (Choice [first, second]) pre post :=
  match one, other with
    | Both proper joins, Both _ otherJoins =>
      Both proper (edge next holds after => Both (joins edge next holds after) (otherJoins edge next holds after))

theorem passesChoiceThree ∀ (first second third: Doc) (pre post: Edge → Prop)
    (one: Passes first pre post)
    (other: Passes second pre post)
    (last: Passes third pre post):
    Passes (Choice [first, second, third]) pre post :=
  match one, other, last with
    | Both proper joins, Both _ otherJoins, Both _ lastJoins => Both proper (edge next holds after =>
      Both (joins edge next holds after) (Both (otherJoins edge next holds after) (lastJoins edge next holds after)))

-- Tokens and their comments.

def FineAbove: List Comment → Prop
  | [] => True
  | [comment, ..rest] => IsComment comment.text ∧ FineAbove rest

def FineAfter: Option Comment → Prop
  | None => True
  | Some comment => IsComment comment.text

--| A token's comments are comments.
def Fine (comments: Comments): Prop := FineAbove comments.above ∧ FineAfter comments.after

theorem passesComment ∀ (comment: Comment) (fine: IsComment comment.text): Passes (Doc.text comment.text) Loose Open :=
  passesTo _ _ _ Open
    (passesFrom _ _ Loose _
      (passesText comment.text (commentSolid comment.text fine) (commentProper comment.text fine))
      (looseAdmits comment.text))
    (edge reached => rfl)

theorem noteLines ∀ (comments: List Comment)
    (fine: FineAbove comments):
    PassesAll (comments.map (comment => Doc.concat [Doc.text comment.text, CommentEnd])) Loose Loose :=
  match comments, fine with
    | [], _ => passesNil Loose Loose (edge holds => holds)
    | [comment, ..rest], Both first others =>
      passesCons
        (Doc.concat [Doc.text comment.text, CommentEnd])
        (rest.map (comment => Doc.concat [Doc.text comment.text, CommentEnd]))
        Loose
        Loose
        Loose
        (passesTwo
          (Doc.text comment.text)
          CommentEnd
          Loose
          Open
          Loose
          (passesComment comment first)
          (passesCommentEnd Open))
        (noteLines rest others)

theorem abovePasses ∀ (above: List Comment) (text: Text)
    (fine: FineAbove above):
    Passes (commentsAbove above) (Admits text) (Admits text) :=
  match above, fine with
    | [], _ => Both rfl (edge next holds after => after edge holds)
    | [comment, ..rest], fine =>
      passesConcat _
        (Admits text)
        (Admits text)
        (passesCons LineStart _
          (Admits text)
          Loose
          (Admits text)
          (passesStart (Admits text))
          (allTo _ Loose Loose (Admits text) (noteLines [comment, ..rest] fine) (looseAdmits text)))

theorem trailingPasses ∀ (after: Option Comment) (text: Text)
    (fine: FineAfter after)
    (ends: Ends text):
    Passes (trailingComment after) (edge => edge = Plain (Some text)) (Left text) :=
  match after, fine with
    | None, _ => Both rfl (edge next same reached => reached edge (rewrite same in rfl))
    | Some comment, fine =>
      match commentSolid comment.text fine with
        | Both filled _ => Both (properWord comment.text (commentProper comment.text fine)) (edge next same reached =>
          rewrite same in Both filled (Both (endsBefore text " " ends closingSpace) (reached Edge.Waiting rfl)))

--| A token with its comments: after anything its text may follow, and
--| it leaves the line at its text or at its trailing comment.
theorem tokenPasses ∀ (comments: Comments) (text: Text)
    (fine: Fine comments)
    (spelled: TokenText text):
    Passes (token comments text) (Admits text) (Left text) :=
  match fine, spelled with
    | Both fineAbove fineAfter, Both solid ends =>
      passesConcat _
        (Admits text)
        (Left text)
        (passesCons _ _
          (Admits text)
          (Admits text)
          (Left text)
          (abovePasses comments.above text fineAbove)
          (passesCons _ _
            (Admits text)
            (edge => edge = Plain (Some text))
            (Left text)
            (passesText text solid (endsProper text ends))
            (passesLast _ _ _ (trailingPasses comments.after text fineAfter ends))))

theorem closerLines ∀ (comments: List Comment)
    (fine: FineAbove comments):
    PassesAll (Doc.joinedWith HardLine (comments.map (comment => Doc.text comment.text))) Loose Open :=
  match comments, fine with
    | [], _ => passesNil Loose Open (edge holds => rfl)
    | [only], Both first _ => passesLast _ Loose Open (passesComment only first)
    | [comment, next, ..rest], Both first others =>
      passesCons _ _ Loose Open Open
        (passesComment comment first)
        (passesCons HardLine _ Open Loose Open (passesHard Open) (closerLines [next, ..rest] others))

--| A closing bracket with its comments, as any token.
theorem closerPasses ∀ (comments: Comments) (text: Text)
    (fine: Fine comments)
    (spelled: TokenText text):
    Passes (closer comments text) (Admits text) (Left text) :=
  match comments, fine, spelled with
    | { above = [], after }, fine, spelled => tokenPasses { above = [], after } text fine spelled
    | { above = [comment, ..rest], after }, Both fineAbove fineAfter, Both solid ends =>
      let lines := [comment, ..rest].map (comment => Doc.text comment.text) |> joined HardLine
      passesConcat
        [Nest 2 (Doc.concat [LineStartHere, lines]), HardLine, Doc.text text, trailingComment after]
        (Admits text)
        (Left text)
        (passesCons _ _
          (Admits text)
          Open
          (Left text)
          (passesTwo LineStartHere lines
            (Admits text)
            Loose
            Open
            (passesStartHere (Admits text))
            (passesConcat _ Loose Open (closerLines [comment, ..rest] fineAbove)))
          (passesCons HardLine _ Open Loose
            (Left text)
            (passesHard Open)
            (passesCons _ _ Loose
              (edge => edge = Plain (Some text))
              (Left text)
              (passesFrom _ _ Loose _ (passesText text solid (endsProper text ends)) (looseAdmits text))
              (passesLast _ _ _ (trailingPasses after text fineAfter ends)))))

--| A token after anything a closing sign may follow, leaving the same.
theorem meetingToken ∀ (comments: Comments) (text: Text)
    (fine: Fine comments)
    (spelled: TokenText text)
    (closing: Closing text):
    Passes (token comments text) Meets Meets :=
  match spelled with
    | Both solid ends =>
      passesTo _ _ _ Meets
        (passesFrom _ _ Meets _ (tokenPasses comments text fine (Both solid ends)) (meetsAdmits text closing))
        (leftMeets text ends)

theorem meetingCloser ∀ (comments: Comments) (text: Text)
    (fine: Fine comments)
    (spelled: TokenText text)
    (closing: Closing text):
    Passes (closer comments text) Meets Meets :=
  match spelled with
    | Both solid ends =>
      passesTo _ _ _ Meets
        (passesFrom _ _ Meets _ (closerPasses comments text fine (Both solid ends)) (meetsAdmits text closing))
        (leftMeets text ends)

--| A token after layout.
theorem looseToken ∀ (comments: Comments) (text: Text)
    (fine: Fine comments)
    (spelled: TokenText text):
    Passes (token comments text) Loose Meets :=
  match spelled with
    | Both solid ends =>
      passesTo _ _ _ Meets
        (passesFrom _ _ Loose _ (tokenPasses comments text fine (Both solid ends)) (looseAdmits text))
        (leftMeets text ends)

--| An opening bracket or a dot: anything may come next.
theorem openingToken ∀ (comments: Comments) (mark: Punctuation) (pre: Edge → Prop)
    (fine: Fine comments)
    (notDefines: mark ≠ Defines)
    (admitted: ∀ (edge: Edge) => pre edge → Admits (MkText [signChar mark]) edge):
    Passes (token comments (MkText [signChar mark])) pre Free :=
  passesTo _ _ _ Free
    (passesFrom _ _ pre _ (tokenPasses comments (MkText [signChar mark]) fine (signToken mark notDefines)) admitted)
    (leftFree (MkText [signChar mark]) (signFree mark notDefines))

--| `closer` after `expr`, on the next line if `expr` ends in a comment.
theorem closeAfterPasses ∀ (expr: Expr) (doc: Doc) (post: Edge → Prop)
    (passes: Passes doc Meets post):
    Passes (closeAfter expr doc) Meets post :=
  match expr.endsWithComment with
    | True =>
      passesTwo HardLine doc Meets Loose post (passesHard Meets) (passesFrom doc Meets Loose post passes looseMeets)
    | False => passes
