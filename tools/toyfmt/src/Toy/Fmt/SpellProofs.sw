--| Spelling, for expressions (SW-3418, layer E): tokens whose views are
--| those of a trace of an expression's events spell the expression
--| (`Spelled`), which is what the parser's read-back asks for.
--|
--| Three steps. A word's event is a token of the kind the tree has there
--| (`nameEvent` and the others). A token's events, its comments
--| included, are one view (`tokenSeen`), and events one after another
--| are their views one after another (`Seen`, `seenThen`). Then the
--| induction over the tree (`exprSpells`), which takes the tokens apart
--| as the views are put together.
--|
--| Outside brackets the induction stops at an `if` (`Plain`): there a
--| branch may be a block, which `Spelled` doesn't describe yet.

namespace Toy.Fmt.Proofs
import Toy.Doc (..)
import Toy.Doc.Proofs (..)
import Toy.Syntax (..)
import Toy.Syntax.Proofs (..)
import Toy.Fmt (..)
import Std (Bool, DecEq, Eq, List, Nat, Option, Parse, Text, Void)

-- A token's kind from its word.

--| A lexeme that makes a token.
def makesToken: Lexeme → Bool
  | CommentLexeme => False
  | LineBreak => False
  | _ => True

--| What is seen after a token of `kind`: it takes the trivia waiting.
def codeView (seen: Views) (kind: Kind) (start: Option Nat): Views :=
  { views = [{ kind, start, above = seen.pending.reverse, trailing = None }, ..seen.views], pending = [] }

--| The event of a word that is neither a comment nor a line break is a
--| token of the kind the word spells.
theorem codeEvent ∀ (seen: Views) (text: Text) (start: Option Nat)
    (code: makesToken (lexemeOf text) = True):
    viewEvent seen { word = text, start } = codeView seen (lexemeKind (lexemeOf text) text) start :=
  match isBreak: text == "\n" with
    | True =>
      let same: text = "\n" := DecEq.sound isBreak
      Void.impossible
        (Bool.falseNotTrue (Eq.trans (Eq.flipped (Eq.cong ((word: Text) => makesToken (lexemeOf word)) same)) code))
    | False =>
      match lexeme: lexemeOf text, code with
        | CommentLexeme, never => (Bool.falseNotTrue never).impossible
        | LineBreak, never => (Bool.falseNotTrue never).impossible
        | _, _ => cases

--| A name's event is a `Name` token of its text.
theorem nameEvent ∀ (seen: Views) (text: Text) (start: Option Nat)
    (name: IsName text):
    viewEvent seen { word = text, start } = codeView seen (Name text) start :=
  match name with
    | (((first, others, same, starts, all)), noKeyword) =>
      let found: lexemeOf (MkText [first, ..others]) = WordLexeme :=
        Eq.cong ((lexeme: Option Lexeme) => lexeme.getOrElse StrayLexeme) (wordLexemeStart first others starts)
      let lexeme: lexemeOf text = WordLexeme := rewrite textOf text [first, ..others] same then found
      let kind: wordKind text = Name text := rewrite noKeyword
      Eq.trans
        (codeEvent seen text start (Eq.cong makesToken lexeme))
        (Eq.cong
          ((spelt: Kind) => codeView seen spelt start)
          (Eq.trans (Eq.cong ((read: Lexeme) => lexemeKind read text) lexeme) kind))

--| Digits' event is a `Number` token of their text.
theorem digitsEvent ∀ (seen: Views) (text: Text) (start: Option Nat)
    (number: IsDigits text):
    viewEvent seen { word = text, start } = codeView seen (Number text) start :=
  match number with
    | (first, others, same, digit, all) =>
      let found: lexemeOf (MkText [first, ..others]) = DigitsLexeme :=
        Eq.cong
          ((lexeme: Option Lexeme) => lexeme.getOrElse StrayLexeme)
          (digitsLexemeStart first others digit (digitIsNoWordStart first digit))
      let lexeme: lexemeOf text = DigitsLexeme := rewrite textOf text [first, ..others] same then found
      Eq.trans
        (codeEvent seen text start (Eq.cong makesToken lexeme))
        (Eq.cong ((spelt: Kind) => codeView seen spelt start) (Eq.cong ((read: Lexeme) => lexemeKind read text) lexeme))

--| A string's event is a `Str` token of its text.
theorem stringEvent ∀ (seen: Views) (text: Text) (start: Option Nat)
    (string: IsString text):
    viewEvent seen { word = text, start } = codeView seen (Str text) start :=
  match string with
    | (segments, same, _) =>
      let lexeme: lexemeOf text = StringLexeme := rewrite textOf text ['"', ..Parse.joinReads segments ++ ['"']] same
      Eq.trans
        (codeEvent seen text start (Eq.cong makesToken lexeme))
        (Eq.cong ((spelt: Kind) => codeView seen spelt start) (Eq.cong ((read: Lexeme) => lexemeKind read text) lexeme))

--| A keyword's event is its `Reserved` token.
theorem keywordEvent ∀ (seen: Views) (keyword: Keyword) (start: Option Nat):
    viewEvent seen { word = keyword.spelling, start } = codeView seen (Reserved keyword) start :=
  cases

--| The event of a bracket, the comma, the dot or `=` is its `Sign` token.
theorem signEvent ∀ (seen: Views) (mark: Punctuation) (start: Option Nat):
    viewEvent seen { word = mark.spelling, start } = codeView seen (Sign mark) start :=
  cases

--| An operator's event is its `Op` token.
theorem operatorEvent ∀ (seen: Views) (operator: Operator) (start: Option Nat):
    viewEvent seen { word = operator.spelling, start } = codeView seen (Op operator) start :=
  cases

theorem commentNoBreak ∀ (text: Text) (comment: IsComment text) (isBreak: (text == "\n") = True): Void :=
  let same: text = "\n" := DecEq.sound isBreak
  Bool.falseNotTrue
    (Eq.trans
      (Eq.flipped (Eq.cong ((word: Text) => isCommentLexeme (lexemeOf word)) same))
      (Eq.cong isCommentLexeme (commentLexeme text comment)))

--| A comment that starts its line waits for the next token.
theorem ownLineEvent ∀ (seen: Views) (text: Text) (column: Nat)
    (comment: IsComment text):
    viewEvent seen { word = text, start = Some column }
      = { views = seen.views, pending = [OwnLine { text }, ..seen.pending] } :=
  match isBreak: text == "\n" with
    | True => Void.impossible (commentNoBreak text comment isBreak)
    | False => rewrite commentLexeme text comment

--| A comment after words on its line goes on the newest token.
theorem trailingEvent ∀ (seen: Views) (text: Text)
    (comment: IsComment text):
    viewEvent seen { word = text, start = None }
      = { views = viewTrailing seen.views { text }, pending = seen.pending } :=
  match isBreak: text == "\n" with
    | True => Void.impossible (commentNoBreak text comment isBreak)
    | False => rewrite commentLexeme text comment

-- The views of a token's events, and of events one after another.

theorem viewsAppend ∀ (seen: Views) (front back: List Event):
    viewsFrom seen (front ++ back) = viewsFrom (viewsFrom seen front) back :=
  match front with
    | [] => byComputing
    | [event, ..rest] => viewsAppend (viewEvent seen event) rest back

--| The trivia waiting (the newest first) once the comments `above` have
--| been seen after `pending`.
def waiting (pending: List Trivia) (above: List Comment): List Trivia := match above with
  | [] => pending
  | [comment, ..rest] => waiting [OwnLine comment, ..pending] rest

theorem waitingReverse ∀ (pending: List Trivia) (above: List Comment):
    (waiting pending above).reverse = pending.reverse ++ above.map OwnLine :=
  match above with
    | [] => (List.appendNil pending.reverse).flipped
    | [comment, ..rest] =>
      calc (waiting pending [comment, ..rest]).reverse
        _ = [OwnLine comment, ..pending].reverse ++ rest.map OwnLine := waitingReverse [OwnLine comment, ..pending] rest
        _ = (pending.reverse ++ [OwnLine comment]) ++ rest.map OwnLine :=
          Eq.cong ((front: List Trivia) => front ++ rest.map OwnLine) (List.reverseCons (OwnLine comment) pending)
        _ = pending.reverse ++ [comment, ..rest].map OwnLine :=
          List.appendAssoc pending.reverse [OwnLine comment] (rest.map OwnLine)

--| The comments above a token, each starting its line, all wait.
theorem aboveViews ∀ (above: List Comment) (column: Nat) (seen: Views)
    (fine: FineAbove above):
    viewsFrom seen (aboveEvents column above) = { views = seen.views, pending = waiting seen.pending above } :=
  match above, fine with
    | [], _ =>
      match seen with
        | { views, pending } => byComputing
    | [{ text }, ..rest], Both fineFirst fineRest =>
      Eq.trans
        (Eq.cong ((next: Views) => viewsFrom next (aboveEvents column rest)) (ownLineEvent seen text column fineFirst))
        (aboveViews rest column { views = seen.views, pending = [OwnLine { text }, ..seen.pending] } fineRest)

--| The view of a token of the tree: the comments above it after what
--| was waiting, and its trailing comment.
def tokenView (pending: List Trivia) (kind: Kind) (start: Option Nat) (comments: Comments): TokenView :=
  { kind, start, above = (waiting pending comments.above).reverse, trailing = comments.after }

--| `events`, seen with `pending` waiting, are the views `found` (in
--| source order) and leave nothing waiting.
def Seen (pending: List Trivia) (events: List Event) (found: List TokenView): Prop :=
  ∀ (earlier: List TokenView) => viewsFrom { views = earlier, pending } events
    = { views = found.reverse ++ earlier, pending = [] }

theorem seenThen ∀ (pending: List Trivia) (front back: List Event) (first second: List TokenView)
    (one: Seen pending front first)
    (other: Seen [] back second):
    Seen pending (front ++ back) (first ++ second) :=
  earlier =>
    calc viewsFrom { views = earlier, pending } (front ++ back)
      _ = viewsFrom (viewsFrom { views = earlier, pending } front) back :=
        viewsAppend { views = earlier, pending } front back
      _ = viewsFrom { views = first.reverse ++ earlier, pending = [] } back :=
        Eq.cong ((seen: Views) => viewsFrom seen back) (one earlier)
      _ = { views = second.reverse ++ (first.reverse ++ earlier), pending = [] } := other (first.reverse ++ earlier)
      _ = { views = (second.reverse ++ first.reverse) ++ earlier, pending = [] } :=
        Eq.cong
          ((views: List TokenView) => ({ views, pending = [] }: Views))
          (Eq.flipped (List.appendAssoc second.reverse first.reverse earlier))
      _ = { views = (first ++ second).reverse ++ earlier, pending = [] } :=
        Eq.cong
          ((views: List TokenView) => ({ views, pending = [] }: Views))
          (Eq.cong ((front: List TokenView) => front ++ earlier) (List.reverseAppend first second).flipped)

--| A token's events are one view, starting where the events allow.
theorem tokenSeen ∀ (allowed: Option Nat → Prop) (comments: Comments) (text: Text) (kind: Kind)
    (events: List Event) (pending: List Trivia)
    (fine: Fine comments)
    (reads: ∀ (seen: Views) (start: Option Nat) => viewEvent seen { word = text, start } = codeView seen kind start)
    (laid: TokenAt allowed comments text events):
    ∃ (start: Option Nat) => allowed start ∧ Seen pending events [tokenView pending kind start comments] :=
  match comments, fine, laid with
    | { above, after = None }, (fineAbove, _), (column, start, ok, split) => (
      start,
      ok,
      (earlier =>
        rewrite split then
          calc viewsFrom { views = earlier, pending } (aboveEvents column above ++ [{ word = text, start }])
            _ = viewsFrom (viewsFrom { views = earlier, pending } (aboveEvents column above)) [
                { word = text, start }
              ] := viewsAppend { views = earlier, pending } (aboveEvents column above) [{ word = text, start }]
            _ = viewsFrom { views = earlier, pending = waiting pending above } [{ word = text, start }] :=
              Eq.cong
                ((seen: Views) => viewsFrom seen [{ word = text, start }])
                (aboveViews above column { views = earlier, pending } fineAbove)
            _ = codeView { views = earlier, pending = waiting pending above } kind start :=
              reads { views = earlier, pending = waiting pending above } start)
    )
    | { above, after = Some { text = written } }, (fineAbove, fineAfter), (column, start, ok, split) => (
      start,
      ok,
      (earlier =>
        rewrite split then
          let waited: Views := { views = earlier, pending = waiting pending above }
          calc viewsFrom
            { views = earlier, pending }
            (aboveEvents column above ++ [{ word = text, start }, { word = written, start = None }])
            _ = viewsFrom (viewsFrom { views = earlier, pending } (aboveEvents column above)) [
                { word = text, start },
                { word = written, start = None }
              ] := viewsAppend { views = earlier, pending } (aboveEvents column above) [
              { word = text, start },
              { word = written, start = None }
            ]
            _ = viewsFrom waited [{ word = text, start }, { word = written, start = None }] :=
              Eq.cong
                ((seen: Views) => viewsFrom seen [{ word = text, start }, { word = written, start = None }])
                (aboveViews above column { views = earlier, pending } fineAbove)
            _ = viewEvent (codeView waited kind start) { word = written, start = None } :=
              Eq.cong ((seen: Views) => viewEvent seen { word = written, start = None }) (reads waited start)
            _ = {
                views = viewTrailing (codeView waited kind start).views { text = written },
                pending = (codeView waited kind start).pending
              } := trailingEvent (codeView waited kind start) written fineAfter)
    )

-- A token of the tree from its view.

theorem ownComments ∀ (above: List Comment): ownLineComments (above.map OwnLine) = above := match above with
  | [] => byComputing
  | [comment, ..rest] => Eq.cong (Cons comment) (ownComments rest)

theorem trailingOf ∀ (trailing: Option (Parse.Located Comment)):
    trailing.map (comment => comment.value) = commentOf trailing :=
  cases

theorem commentsSame ∀ (comments: Comments) (above: List Comment) (after: Option Comment)
    (sameAbove: above = comments.above)
    (sameAfter: after = comments.after):
    comments = { above, after } :=
  match comments, sameAbove, sameAfter with
    | { above = held, after = kept }, sameAbove, sameAfter =>
      Eq.trans
        (Eq.cong ((part: List Comment) => ({ above = part, after = kept }: Comments)) sameAbove.flipped)
        (Eq.cong ((part: Option Comment) => ({ above, after = part }: Comments)) sameAfter.flipped)

--| A token that isn't its statement's first holds the comments its view
--| shows, as the tree keeps them.
theorem viewComments ∀ (token: Parse.Located Token) (kind: Kind) (start: Option Nat) (comments: Comments)
    (same: viewOf token = tokenView [] kind start comments):
    comments
      = { above = ownLineComments token.value.above, after = token.value.trailing.map (comment => comment.value) } :=
  commentsSame comments _ _
    (Eq.trans
      (Eq.cong ownLineComments
        (Eq.trans (Eq.cong ((view: TokenView) => view.above) same) (waitingReverse [] comments.above)))
      (ownComments comments.above))
    (Eq.trans (trailingOf token.value.trailing) (Eq.cong ((view: TokenView) => view.trailing) same))

--| The zone of the events and the layout of the parser are of one
--| statement: any zone inside brackets, and outside them the zone
--| deeper than the statement's column.
def Suits (zone: Zone) (layout: Layout): Prop := match layout with
  | InBrackets => True
  | InStatement column _ =>
    match zone with
      | Deeper at => at = column
      | Anywhere _ => False

--| `token` isn't the first token of the layout's statement.
def Apart (layout: Layout) (token: Parse.Located Token): Prop := match layout with
  | InBrackets => True
  | InStatement _ from => (token.offset == from) = False

def AllApart (layout: Layout) (tokens: List (Parse.Located Token)): Prop := match tokens with
  | [] => True
  | [token, ..rest] => Apart layout token ∧ AllApart layout rest

theorem apartFront ∀ (layout: Layout) (front back: List (Parse.Located Token))
    (apart: AllApart layout (front ++ back)):
    AllApart layout front :=
  match front, apart with
    | [], _ => byComputing
    | [token, ..rest], Both one others => (one, (apartFront layout rest back others))

theorem apartBack ∀ (layout: Layout) (front back: List (Parse.Located Token))
    (apart: AllApart layout (front ++ back)):
    AllApart layout back :=
  match front, apart with
    | [], apart => apart
    | [token, ..rest], Both one others => apartBack layout rest back others

theorem bracketApart ∀ (tokens: List (Parse.Located Token)): AllApart InBrackets tokens := match tokens with
  | [] => byComputing
  | [token, ..rest] => (byComputing, (bracketApart rest))

--| `token` is the tree's token of `kind` with `comments`, as `Spelled`
--| asks at `layout`.
def Fits (layout: Layout) (token: Parse.Located Token) (kind: Kind) (comments: Comments): Prop :=
  token.value.kind = kind ∧ layout.allows token = True ∧ comments = layout.comments token

theorem allowsCast ∀ (zone: Zone) (given wanted: Option Nat)
    (same: wanted = given) (allowed: zone.allows given):
    zone.allows wanted :=
  rewrite same then allowed

--| A token that starts where the zone deeper than a statement allows is
--| one the statement's layout allows.
theorem deeperAllows ∀ (at column from: Nat) (token: Parse.Located Token) (start: Option Nat)
    (suits: at = column) (allowed: (Deeper at).allows start)
    (same: (viewOf token).start = start):
    (InStatement column from).allows token = True :=
  match token, same with
    | { value = { kind, startsLine = False, column = indent, above, trailing }, offset, length }, _ => byComputing
    | { value = { kind, startsLine = True, column = indent, above, trailing }, offset, length }, same =>
      let lower: at < indent := allowsCast (Deeper at) start (Some indent) same allowed
      let deeper: (indent > column) = True := arithmetic [lower, suits]
      rewrite deeper

--| A token of the tree that isn't its statement's first, from its view.
theorem innerFits ∀ (zone: Zone) (layout: Layout) (token: Parse.Located Token) (kind: Kind)
    (start: Option Nat) (comments: Comments)
    (suits: Suits zone layout)
    (apart: Apart layout token) (allowed: zone.allows start)
    (same: viewOf token = tokenView [] kind start comments):
    Fits layout token kind comments :=
  match layout, zone, suits, apart, allowed with
    | InBrackets, _, _, _, _ =>
      ((Eq.cong ((view: TokenView) => view.kind) same), byComputing, (viewComments token kind start comments same))
    | InStatement column from, Deeper at, suits, apart, allowed => (
      (Eq.cong ((view: TokenView) => view.kind) same),
      (deeperAllows at column from token start suits allowed (Eq.cong ((view: TokenView) => view.start) same)),
      (match isFirst: token.offset == from, apart with
        | False, _ => viewComments token kind start comments same)
    )
    | InStatement column from, Anywhere at, never, _, _ =>
      match never with
        | ()

theorem bracketFits ∀ (token: Parse.Located Token) (kind: Kind) (start: Option Nat) (comments: Comments)
    (same: viewOf token = tokenView [] kind start comments):
    Fits InBrackets token kind comments :=
  innerFits (Anywhere 0) InBrackets token kind start comments byComputing byComputing byComputing same

--| What the induction knows of the tokens of an expression whose
--| leftmost token starts as `head` says after `pending`: every other
--| token isn't the statement's first, and the leftmost fits the tree
--| (it may be the statement's first, whose comments above are the
--| block's note lines).
def Leads (layout: Layout) (pending: List Trivia) (head: Option Nat → Prop)
    (above: List Comment) (tokens: List (Parse.Located Token)):
    Prop :=
  match tokens with
    | [] => True
    | [first, ..others] =>
      AllApart layout others
        ∧ (∀ (kind: Kind) (start: Option Nat) (after: Option Comment) => head start
          → viewOf first = tokenView pending kind start { above, after }
          → layout.allows first = True ∧ ({ above, after }: Comments) = layout.comments first)

theorem headFits ∀ (layout: Layout) (pending: List Trivia) (head: Option Nat → Prop) (above: List Comment)
    (first: Parse.Located Token) (others: List (Parse.Located Token)) (kind: Kind)
    (start: Option Nat) (after: Option Comment)
    (leads: Leads layout pending head above [first, ..others]) (allowed: head start)
    (same: viewOf first = tokenView pending kind start { above, after }):
    Fits layout first kind { above, after } :=
  match leads with | (_, fit) => ((Eq.cong ((view: TokenView) => view.kind) same), (fit kind start after allowed same))

--| The tokens of an expression that isn't its statement's first lead.
theorem innerLeads ∀ (zone: Zone) (layout: Layout) (above: List Comment) (tokens: List (Parse.Located Token))
    (suits: Suits zone layout)
    (apart: AllApart layout tokens):
    Leads layout [] zone.allows above tokens :=
  match tokens, apart with
    | [], _ => byComputing
    | [first, ..others], Both one rest => (
      rest,
      (kind start after allowed same =>
        match innerFits zone layout first kind start { above, after } suits one allowed same with
          | (_, both) => both)
    )

theorem bracketLeads ∀ (head: Option Nat → Prop) (above: List Comment) (tokens: List (Parse.Located Token)):
    Leads InBrackets [] head above tokens :=
  match tokens with
    | [] => byComputing
    | [first, ..others] => (
      (bracketApart others),
      (kind start after allowed same =>
        match bracketFits first kind start { above, after } same with
          | (_, both) => both)
    )

-- Tokens taken apart as their views are.

def noViews (views: List TokenView): Bool := match views with
  | [] => True
  | _ => False

theorem viewsNil ∀ (goal: List (Parse.Located Token) → Prop) (tokens: List (Parse.Located Token))
    (same: tokens.map viewOf = []) (step: goal []):
    goal tokens :=
  match tokens, same with
    | [], _ => step
    | [token, ..rest], same => Void.impossible (Bool.falseNotTrue (Eq.cong noViews same))

theorem viewsCons ∀ (goal: List (Parse.Located Token) → Prop) (tokens: List (Parse.Located Token))
    (view: TokenView) (views: List TokenView)
    (same: tokens.map viewOf = [view, ..views])
    (step: ∀ (token: Parse.Located Token) (rest: List (Parse.Located Token)) => viewOf token = view
      → rest.map viewOf = views
      → goal [token, ..rest]):
    goal tokens :=
  match tokens, same with
    | [token, ..rest], same => byFacts
    | [], same => byFacts

theorem viewsOne ∀ (goal: List (Parse.Located Token) → Prop) (tokens: List (Parse.Located Token)) (view: TokenView)
    (same: tokens.map viewOf = [view]) (step: ∀ (token: Parse.Located Token) => viewOf token = view → goal [token]):
    goal tokens :=
  viewsCons goal tokens view [] same (found rest tokenSame restSame =>
    viewsNil ((later: List (Parse.Located Token)) => goal [found, ..later]) rest restSame (step found tokenSame))

theorem consViews ∀ (token: Parse.Located Token) (rest: List (Parse.Located Token))
    (view: TokenView) (views: List TokenView)
    (tokenSame: viewOf token = view)
    (restSame: rest.map viewOf = views):
    [token, ..rest].map viewOf = [view, ..views] :=
  Eq.trans (Eq.cong ((first: TokenView) => [first, ..rest.map viewOf]) tokenSame) (Eq.cong (Cons view) restSame)

theorem viewsSplit ∀ (goal: List (Parse.Located Token) → Prop)
    (tokens: List (Parse.Located Token)) (front back: List TokenView)
    (same: tokens.map viewOf = front ++ back)
    (step: ∀ (first second: List (Parse.Located Token)) => first.map viewOf = front
      → second.map viewOf = back
      → goal (first ++ second)):
    goal tokens :=
  match front, same, step with
    | [], same, step => step [] tokens byComputing same
    | [view, ..views], same, step => viewsCons goal tokens view (views ++ back) same (found rest tokenSame restSame =>
      viewsSplit
        ((later: List (Parse.Located Token)) => goal [found, ..later])
        rest
        views
        back
        restSame
        (first second firstSame secondSame =>
          step [found, ..first] second (consViews found first view views tokenSame firstSame) secondSame))

-- What the parser guarantees of where comments and blocks are.

--| A list of lines as `withoutFirstBlank` leaves it: no blank line is
--| kept above the first.
def Unspaced (lines: List (Spaced a)): Prop := withoutFirstBlank lines = lines

--| A body that is one expression.
def OneExpression: List (Spaced Statement) → Prop
  | [{ line = Bare _, .. }] => True
  | _ => False

--| What the parser guarantees of where comments and blocks are, in an
--| expression read inside brackets (`bracketed`) or in a statement:
--| outside brackets a statement's first token holds no comments above it
--| (they are the block's comment lines), nor does the first token of a
--| body on its keyword's line (it doesn't start a line); inside
--| brackets every body is one expression; and no body keeps a blank line
--| above its first line.
def HeadedExpr (bracketed: Bool): Expr → Prop
  | Var _ _ => True
  | NumberLiteral _ _ => True
  | StringLiteral _ _ => True
  | Bracketed _ inner _ => HeadedExpr True inner
  | ListLiteral _ items trailingComma _ => HeadedItems items
  | Call callee _ arguments trailingComma _ => HeadedExpr bracketed callee ∧ HeadedItems arguments
  | Field target _ _ _ => HeadedExpr bracketed target
  | Negate _ operand => HeadedExpr bracketed operand
  | Binary _ _ left right => HeadedExpr bracketed left ∧ HeadedExpr bracketed right
  | If _ condition _ whenTrue _ whenFalse =>
    HeadedExpr bracketed condition ∧ HeadedBody bracketed whenTrue ∧ HeadedBody bracketed whenFalse

def HeadedItems: List Expr → Prop
  | [] => True
  | [value, ..rest] => HeadedExpr True value ∧ HeadedItems rest

def HeadedBody (bracketed: Bool): Body → Prop
  | { statements } =>
    HeadedLines bracketed statements ∧ Unspaced statements ∧ (bracketed = True → OneExpression statements)

def HeadedLines (bracketed: Bool): List (Spaced Statement) → Prop
  | [] => True
  | [{ line, .. }, ..rest] => HeadedStatement bracketed line ∧ HeadedLines bracketed rest

def HeadedStatement (bracketed: Bool): Statement → Prop
  | Let letComments _ _ _ body => letComments.above = [] ∧ HeadedBody False body
  | Bare value => (bracketed = False → value.firstAbove = []) ∧ HeadedExpr bracketed value
  | StatementNote _ => True

def HeadedDeclaration: Declaration → Prop
  | Function fnComments _ _ _ _ _ trailingComma _ _ body => fnComments.above = [] ∧ HeadedBody False body
  | Value letComments _ _ _ body => letComments.above = [] ∧ HeadedBody False body
  | DeclarationNote _ => True

def HeadedDeclarations: List (Spaced Declaration) → Prop
  | [] => True
  | [{ line, .. }, ..rest] => HeadedDeclaration line ∧ HeadedDeclarations rest

def HeadedFile: SourceFile → Prop
  | { declarations } => HeadedDeclarations declarations ∧ Unspaced declarations

def bracketedOf: Layout → Bool
  | InBrackets => True
  | InStatement _ _ => False

--| Whether the first line keeps a blank line above it.
def firstBlankBefore (lines: List (Spaced Statement)): Bool := match lines with
  | [first, .._] => first.blankBefore
  | [] => False

-- The induction over the tree.

--| No `if` outside brackets.
def NoIf: Expr → Prop
  | Var _ _ => True
  | NumberLiteral _ _ => True
  | StringLiteral _ _ => True
  | Bracketed _ _ _ => True
  | ListLiteral _ _ _ _ => True
  | Call callee _ _ trailingComma _ => NoIf callee
  | Field target _ _ _ => NoIf target
  | Negate _ operand => NoIf operand
  | Binary _ _ left right => NoIf left ∧ NoIf right
  | If _ _ _ _ _ _ => False

--| The expressions `exprSpells` covers at `layout`: all of them inside
--| brackets, where an `if`'s branches are one expression each; outside
--| brackets those with no `if`, whose branch may be a block.
def Covered (layout: Layout) (expr: Expr): Prop := match layout with
  | InBrackets => True
  | InStatement _ _ => NoIf expr

theorem coveredPart ∀ (layout: Layout) (whole part: Expr)
    (narrow: NoIf whole → NoIf part)
    (plain: Covered layout whole):
    Covered layout part :=
  match layout, plain with
    | InBrackets, _ => byComputing
    | InStatement _ _, noIf => narrow noIf

--| The layout of a statement like `layout`'s whose first token is at
--| the offset `from`. The views of an expression's events don't depend
--| on the offset, so the tokens that spell it may be at any.
def restart (layout: Layout) (from: Nat): Layout := match layout with
  | InBrackets => InBrackets
  | InStatement column _ => InStatement column from

theorem suitsRestart ∀ (zone: Zone) (layout: Layout) (from: Nat)
    (suits: Suits zone layout):
    Suits zone (restart layout from) :=
  match layout, suits with
    | InBrackets, _ => byComputing
    | InStatement column _, suits =>
      match zone, suits with
        | Deeper at, suits => suits
        | Anywhere _, never => never

--| The events of `expr`, seen with `pending` waiting, are views (one at
--| least) that leave nothing waiting, and tokens with those views that
--| lead (`Leads`) spell the expression at `layout`, wherever the
--| statement starts; the first view starts as `head` says, with the
--| comments above the expression's first token after what was waiting.
def Spells (layout: Layout) (pending: List Trivia) (head: Option Nat → Prop) (expr: Expr) (events: List Event): Prop :=
  ∃ (first: TokenView) => ∃ (others: List TokenView) => Seen pending events [first, ..others]
    ∧ (∀ (from: Nat) (tokens: List (Parse.Located Token)) => tokens.map viewOf = [first, ..others]
      → Leads (restart layout from) pending head expr.firstAbove tokens
      → Spelled (restart layout from) expr tokens)
    ∧ head first.start
    ∧ first.above = (waiting pending expr.firstAbove).reverse

--| One token with a leaf's view is the leaf's token.
theorem leafSpells ∀ (layout: Layout) (pending: List Trivia) (head: Option Nat → Prop) (above: List Comment)
    (after: Option Comment) (kind: Kind) (start: Option Nat) (tokens: List (Parse.Located Token))
    (same: tokens.map viewOf = [tokenView pending kind start { above, after }]) (allowed: head start)
    (leads: Leads layout pending head above tokens):
    ∃ (found: Parse.Located Token) => tokens = [found]
      ∧ found.value.kind = kind
      ∧ layout.allows found = True
      ∧ ({ above, after }: Comments) = layout.comments found :=
  viewsOne
    (later =>
      Leads layout pending head above later
        → ∃ (found: Parse.Located Token) => later = [found]
          ∧ found.value.kind = kind
          ∧ layout.allows found = True
          ∧ ({ above, after }: Comments) = layout.comments found)
    tokens
    (tokenView pending kind start { above, after })
    same
    (found foundSame held =>
      match headFits layout pending head above found [] kind start after held allowed foundSame with
        | (kindSame, allows, notes) => (found, byComputing, kindSame, allows, notes))
    leads

theorem blockAheadBrackets ∀ (tokens: List (Parse.Located Token)): blockAhead InBrackets tokens = False := cases

--| Tokens with the views of an expression's events spell it.
theorem exprSpells ∀ (zone: Zone) (layout: Layout) (head: Option Nat → Prop) (expr: Expr)
    (events: List Event) (pending: List Trivia)
    (suits: Suits zone layout)
    (shaped: Shaped expr)
    (lexical: Lexical expr)
    (headed: HeadedExpr (bracketedOf layout) expr)
    (commaless: NoTrailingCommas expr)
    (plain: Covered layout expr)
    (laid: Events zone head expr events):
    Spells layout pending head expr events :=
  match expr, shaped, lexical, headed, plain, laid with
    | Var text { above, after }, _, Both isName fine, _, _, laid =>
      match tokenSeen head
        { above, after }
        text
        (Name text)
        events
        pending
        fine
        (seen start => nameEvent seen text start isName)
        laid with
        | Witness start (Both allowed seen) => (
          (tokenView pending (Name text) start { above, after }),
          [],
          seen,
          (from tokens same leads =>
            leafSpells (restart layout from) pending head above after (Name text) start tokens same allowed leads),
          allowed,
          byComputing
        )
    | NumberLiteral text { above, after }, _, Both isDigits fine, _, _, laid =>
      match tokenSeen head
        { above, after }
        text
        (Number text)
        events
        pending
        fine
        (seen start => digitsEvent seen text start isDigits)
        laid with
        | Witness start (Both allowed seen) => (
          (tokenView pending (Number text) start { above, after }),
          [],
          seen,
          (from tokens same leads =>
            leafSpells (restart layout from) pending head above after (Number text) start tokens same allowed leads),
          allowed,
          byComputing
        )
    | StringLiteral text { above, after }, _, Both isString fine, _, _, laid =>
      match tokenSeen head
        { above, after }
        text
        (Str text)
        events
        pending
        fine
        (seen start => stringEvent seen text start isString)
        laid with
        | Witness start (Both allowed seen) => (
          (tokenView pending (Str text) start { above, after }),
          [],
          seen,
          (from tokens same leads =>
            leafSpells (restart layout from) pending head above after (Str text) start tokens same allowed leads),
          allowed,
          byComputing
        )
    | Bracketed ({ above, after }) inner close, Both shapedInner _, Both fineOpen
        (Both innerLexical fineClose), headedInner, _, Witness front
        (Witness back
          (Both split (Both openLaid (Witness mid (Witness tail (Both backSplit (Both innerLaid closeLaid))))))) =>
      match tokenSeen head
        { above, after }
        "("
        (Sign OpenParen)
        front
        pending
        fineOpen
        (seen start => signEvent seen OpenParen start)
        openLaid, exprSpells zone.inside InBrackets anyStart inner mid [] byComputing shapedInner innerLexical
          headedInner commaless byComputing innerLaid, tokenSeen anyStart close ")"
        (Sign CloseParen)
        tail
        []
        fineClose
        (seen start => signEvent seen CloseParen start)
        closeLaid with
        | Witness openStart (Both openAllowed openSeen), Witness first
            (Witness others (Both innerSeen (Both innerSpells _))), Witness closeStart (Both _ closeSeen) => (
          (tokenView pending (Sign OpenParen) openStart { above, after }),
          ([first, ..others] ++ [(tokenView [] (Sign CloseParen) closeStart close)]),
          (rewrite split, backSplit then
            seenThen pending front
              (mid ++ tail)
              [(tokenView pending (Sign OpenParen) openStart { above, after })]
              ([first, ..others] ++ [(tokenView [] (Sign CloseParen) closeStart close)])
              openSeen
              (seenThen [] mid tail
                [first, ..others]
                [(tokenView [] (Sign CloseParen) closeStart close)]
                innerSeen
                closeSeen)),
          (from tokens same =>
            viewsCons
              (later =>
                Leads (restart layout from) pending head above later
                  → Spelled (restart layout from) (Bracketed ({ above, after }) inner close) later)
              tokens
              (tokenView pending (Sign OpenParen) openStart { above, after })
              ([first, ..others] ++ [(tokenView [] (Sign CloseParen) closeStart close)])
              same
              (opener rest openSame restSame =>
                viewsSplit
                  (later =>
                    Leads (restart layout from) pending head above [opener, ..later]
                      → Spelled (restart layout from) (Bracketed ({ above, after }) inner close) [opener, ..later])
                  rest
                  [first, ..others]
                  [(tokenView [] (Sign CloseParen) closeStart close)]
                  restSame
                  (innerTokens closing innerSame closingSame =>
                    viewsOne
                      (later =>
                        Leads (restart layout from) pending head above [opener, ..innerTokens ++ later]
                          → Spelled (restart layout from) (Bracketed ({ above, after }) inner close) [
                            opener,
                            ..innerTokens ++ later
                          ])
                      closing
                      (tokenView [] (Sign CloseParen) closeStart close)
                      closingSame
                      (shut closeSame leads =>
                        match headFits
                          (restart layout from)
                          pending
                          head
                          above
                          opener
                          (innerTokens ++ [shut])
                          (Sign OpenParen)
                          openStart
                          after
                          leads
                          openAllowed
                          openSame, bracketFits shut (Sign CloseParen) closeStart close closeSame with
                          | (openKind, openAllows, openNotes), (closeKind, _, closeNotes) => (
                            opener,
                            innerTokens,
                            shut,
                            byComputing,
                            openKind,
                            openAllows,
                            closeKind,
                            (innerSpells 0 innerTokens innerSame (bracketLeads anyStart inner.firstAbove innerTokens)),
                            openNotes,
                            closeNotes
                          ))))),
          openAllowed,
          byComputing
        )
    | ListLiteral ({ above, after }) items trailingComma close, Both shapedItems bare, Both fineOpen
        (Both itemsLexical fineClose), headedItems, _, Witness front
        (Witness back
          (Both split (Both openLaid (Witness mid (Witness tail (Both backSplit (Both itemsLaid closeLaid))))))) =>
      match tokenSeen head
        { above, after }
        "["
        (Sign OpenSquare)
        front
        pending
        fineOpen
        (seen start => signEvent seen OpenSquare start)
        openLaid, itemsSpell zone.inside items mid shapedItems itemsLexical headedItems commaless.right
          itemsLaid, tokenSeen anyStart close "]"
        (Sign CloseSquare)
        tail
        []
        fineClose
        (seen start => signEvent seen CloseSquare start)
        closeLaid with
        | Witness openStart (Both openAllowed openSeen), Witness found (Both itemsSeen itemsSpelled), Witness closeStart
            (Both _ closeSeen) => (
          (tokenView pending (Sign OpenSquare) openStart { above, after }),
          (found ++ [(tokenView [] (Sign CloseSquare) closeStart close)]),
          (rewrite split, backSplit then
            seenThen pending front
              (mid ++ tail)
              [(tokenView pending (Sign OpenSquare) openStart { above, after })]
              (found ++ [(tokenView [] (Sign CloseSquare) closeStart close)])
              openSeen
              (seenThen [] mid tail found [(tokenView [] (Sign CloseSquare) closeStart close)] itemsSeen closeSeen)),
          (from tokens same =>
            viewsCons
              (later =>
                Leads (restart layout from) pending head above later
                  → Spelled (restart layout from) (ListLiteral ({ above, after }) items trailingComma close) later)
              tokens
              (tokenView pending (Sign OpenSquare) openStart { above, after })
              (found ++ [(tokenView [] (Sign CloseSquare) closeStart close)])
              same
              (opener rest openSame restSame =>
                viewsSplit
                  (later =>
                    Leads (restart layout from) pending head above [opener, ..later]
                      → Spelled (restart layout from) (ListLiteral ({ above, after }) items trailingComma close) [
                        opener,
                        ..later
                      ])
                  rest
                  found
                  [(tokenView [] (Sign CloseSquare) closeStart close)]
                  restSame
                  (itemTokens closing itemsSame closingSame =>
                    viewsOne
                      (later =>
                        Leads (restart layout from) pending head above [opener, ..itemTokens ++ later]
                          → Spelled (restart layout from) (ListLiteral ({ above, after }) items trailingComma close) [
                            opener,
                            ..itemTokens ++ later
                          ])
                      closing
                      (tokenView [] (Sign CloseSquare) closeStart close)
                      closingSame
                      (shut closeSame leads =>
                        match headFits
                          (restart layout from)
                          pending
                          head
                          above
                          opener
                          (itemTokens ++ [shut])
                          (Sign OpenSquare)
                          openStart
                          after
                          leads
                          openAllowed
                          openSame, bracketFits shut (Sign CloseSquare) closeStart close closeSame with
                          | (openKind, openAllows, openNotes), (closeKind, _, closeNotes) => (
                            opener,
                            itemTokens,
                            shut,
                            byComputing,
                            openKind,
                            openAllows,
                            closeKind,
                            (itemsSpelled itemTokens itemsSame),
                            openNotes,
                            closeNotes,
                            commaless.left
                          ))))),
          openAllowed,
          byComputing
        )
    | Call callee open arguments trailingComma close, Both _
        (Both shapedCallee (Both shapedArguments bare)), Both calleeLexical
        (Both fineOpen (Both argumentsLexical fineClose)), Both headedCallee headedArguments, plain, Witness front
        (Witness back
          (Both split
            (Both calleeLaid
              (Witness mid
                (Witness afterOpen
                  (Both backSplit
                    (Both openLaid
                      (Witness inner (Witness tail (Both innerSplit (Both argumentsLaid closeLaid))))))))))) =>
      match exprSpells zone layout head callee front pending suits shapedCallee calleeLexical headedCallee
          commaless.right.left
          (coveredPart layout (Call callee open arguments trailingComma close) callee (noIf => noIf) plain)
          calleeLaid, tokenSeen zone.allows open "("
        (Sign OpenParen)
        mid
        []
        fineOpen
        (seen start => signEvent seen OpenParen start)
        openLaid, itemsSpell zone.inside arguments inner shapedArguments argumentsLexical headedArguments
          commaless.right.right argumentsLaid, tokenSeen anyStart close ")"
        (Sign CloseParen)
        tail
        []
        fineClose
        (seen start => signEvent seen CloseParen start)
        closeLaid with
        | Witness calleeFirst
            (Witness calleeOthers (Both calleeSeen (Both calleeSpells calleeStarts))), Witness openStart
            (Both openAllowed openSeen), Witness found (Both argumentsSeen argumentsSpelled), Witness closeStart
            (Both _ closeSeen) => (
          calleeFirst,
          (calleeOthers
            ++ ([(tokenView [] (Sign OpenParen) openStart open)]
              ++ (found ++ [(tokenView [] (Sign CloseParen) closeStart close)]))),
          (rewrite split, backSplit, innerSplit then
            seenThen pending front
              (mid ++ (inner ++ tail))
              [calleeFirst, ..calleeOthers]
              ([(tokenView [] (Sign OpenParen) openStart open)]
                ++ (found ++ [(tokenView [] (Sign CloseParen) closeStart close)]))
              calleeSeen
              (seenThen [] mid
                (inner ++ tail)
                [(tokenView [] (Sign OpenParen) openStart open)]
                (found ++ [(tokenView [] (Sign CloseParen) closeStart close)])
                openSeen
                (seenThen [] inner tail found
                  [(tokenView [] (Sign CloseParen) closeStart close)]
                  argumentsSeen
                  closeSeen))),
          (from tokens same =>
            viewsCons
              (later =>
                Leads (restart layout from) pending head callee.firstAbove later
                  → Spelled (restart layout from) (Call callee open arguments trailingComma close) later)
              tokens
              calleeFirst
              (calleeOthers
                ++ ([(tokenView [] (Sign OpenParen) openStart open)]
                  ++ (found ++ [(tokenView [] (Sign CloseParen) closeStart close)])))
              same
              (lead rest leadSame restSame =>
                viewsSplit
                  (later =>
                    Leads (restart layout from) pending head callee.firstAbove [lead, ..later]
                      → Spelled (restart layout from) (Call callee open arguments trailingComma close) [lead, ..later])
                  rest
                  calleeOthers
                  ([(tokenView [] (Sign OpenParen) openStart open)]
                    ++ (found ++ [(tokenView [] (Sign CloseParen) closeStart close)]))
                  restSame
                  (calleeRest afterCallee calleeRestSame afterCalleeSame =>
                    viewsCons
                      (later =>
                        Leads (restart layout from) pending head callee.firstAbove [lead, ..calleeRest ++ later]
                          → Spelled (restart layout from) (Call callee open arguments trailingComma close) [
                            lead,
                            ..calleeRest ++ later
                          ])
                      afterCallee
                      (tokenView [] (Sign OpenParen) openStart open)
                      (found ++ [(tokenView [] (Sign CloseParen) closeStart close)])
                      afterCalleeSame
                      (opener afterOpener openSame afterOpenerSame =>
                        viewsSplit
                          (later =>
                            Leads (restart layout from) pending head callee.firstAbove [
                              lead,
                              ..calleeRest ++ [opener, ..later]
                            ]
                              → Spelled (restart layout from) (Call callee open arguments trailingComma close) [
                                lead,
                                ..calleeRest ++ [opener, ..later]
                              ])
                          afterOpener
                          found
                          [(tokenView [] (Sign CloseParen) closeStart close)]
                          afterOpenerSame
                          (argumentTokens closing argumentsSame closingSame =>
                            viewsOne
                              (later =>
                                Leads (restart layout from) pending head callee.firstAbove [
                                  lead,
                                  ..calleeRest ++ [opener, ..argumentTokens ++ later]
                                ]
                                  → Spelled (restart layout from) (Call callee open arguments trailingComma close) [
                                    lead,
                                    ..calleeRest ++ [opener, ..argumentTokens ++ later]
                                  ])
                              closing
                              (tokenView [] (Sign CloseParen) closeStart close)
                              closingSame
                              (shut closeSame leads =>
                                match leads with
                                  | (apart, fit) =>
                                    match apartBack
                                      (restart layout from)
                                      calleeRest
                                      [opener, ..argumentTokens ++ [shut]]
                                      apart with
                                      | (openApart, _) =>
                                        match innerFits zone
                                          (restart layout from)
                                          opener
                                          (Sign OpenParen)
                                          openStart
                                          open
                                          (suitsRestart zone layout from suits)
                                          openApart
                                          openAllowed
                                          openSame, bracketFits shut (Sign CloseParen) closeStart close closeSame with
                                          | (openKind, openAllows, openNotes), (closeKind, _, closeNotes) => (
                                            [lead, ..calleeRest],
                                            opener,
                                            argumentTokens,
                                            shut,
                                            byComputing,
                                            openKind,
                                            openAllows,
                                            closeKind,
                                            (calleeSpells from
                                              [lead, ..calleeRest]
                                              (consViews lead calleeRest calleeFirst calleeOthers leadSame
                                                  calleeRestSame)
                                              ((
                                                (apartFront
                                                  (restart layout from)
                                                  calleeRest
                                                  [opener, ..argumentTokens ++ [shut]]
                                                  apart),
                                                fit
                                              ))),
                                            (argumentsSpelled argumentTokens argumentsSame),
                                            openNotes,
                                            closeNotes,
                                            commaless.left
                                          ))))))),
          calleeStarts
        )
    | Field target dot name nameComments, Both _ shapedTarget, Both targetLexical
        (Both fineDot (Both isName fineName)), headedTarget, plain, Witness front
        (Witness back
          (Both split (Both targetLaid (Witness mid (Witness tail (Both backSplit (Both dotLaid nameLaid))))))) =>
      match exprSpells zone layout head target front pending suits shapedTarget targetLexical headedTarget commaless
        (coveredPart layout (Field target dot name nameComments) target (noIf => noIf) plain)
        targetLaid, tokenSeen zone.allows dot "."
        (Sign Dot)
        mid
        []
        fineDot
        (seen start => signEvent seen Dot start)
        dotLaid, tokenSeen zone.allows nameComments name
        (Name name)
        tail
        []
        fineName
        (seen start => nameEvent seen name start isName)
        nameLaid with
        | Witness targetFirst
            (Witness targetOthers (Both targetSeen (Both targetSpells targetStarts))), Witness dotStart
            (Both dotAllowed dotSeen), Witness nameStart (Both nameAllowed nameSeen) => (
          targetFirst,
          (targetOthers
            ++ ([(tokenView [] (Sign Dot) dotStart dot)] ++ [(tokenView [] (Name name) nameStart nameComments)])),
          (rewrite split, backSplit then
            seenThen pending front
              (mid ++ tail)
              [targetFirst, ..targetOthers]
              ([(tokenView [] (Sign Dot) dotStart dot)] ++ [(tokenView [] (Name name) nameStart nameComments)])
              targetSeen
              (seenThen [] mid tail
                [(tokenView [] (Sign Dot) dotStart dot)]
                [(tokenView [] (Name name) nameStart nameComments)]
                dotSeen
                nameSeen)),
          (from tokens same =>
            viewsCons
              (later =>
                Leads (restart layout from) pending head target.firstAbove later
                  → Spelled (restart layout from) (Field target dot name nameComments) later)
              tokens
              targetFirst
              (targetOthers
                ++ ([(tokenView [] (Sign Dot) dotStart dot)] ++ [(tokenView [] (Name name) nameStart nameComments)]))
              same
              (lead rest leadSame restSame =>
                viewsSplit
                  (later =>
                    Leads (restart layout from) pending head target.firstAbove [lead, ..later]
                      → Spelled (restart layout from) (Field target dot name nameComments) [lead, ..later])
                  rest
                  targetOthers
                  ([(tokenView [] (Sign Dot) dotStart dot)] ++ [(tokenView [] (Name name) nameStart nameComments)])
                  restSame
                  (targetRest afterTarget targetRestSame afterTargetSame =>
                    viewsCons
                      (later =>
                        Leads (restart layout from) pending head target.firstAbove [lead, ..targetRest ++ later]
                          → Spelled (restart layout from) (Field target dot name nameComments) [
                            lead,
                            ..targetRest ++ later
                          ])
                      afterTarget
                      (tokenView [] (Sign Dot) dotStart dot)
                      [(tokenView [] (Name name) nameStart nameComments)]
                      afterTargetSame
                      (dotToken afterDot dotSame afterDotSame =>
                        viewsOne
                          (later =>
                            Leads (restart layout from) pending head target.firstAbove [
                              lead,
                              ..targetRest ++ [dotToken, ..later]
                            ]
                              → Spelled (restart layout from) (Field target dot name nameComments) [
                                lead,
                                ..targetRest ++ [dotToken, ..later]
                              ])
                          afterDot
                          (tokenView [] (Name name) nameStart nameComments)
                          afterDotSame
                          (named nameSame leads =>
                            match leads with
                              | (apart, fit) =>
                                match apartBack (restart layout from) targetRest [dotToken, named] apart with
                                  | (dotApart, nameApart, _) =>
                                    match innerFits zone
                                      (restart layout from)
                                      dotToken
                                      (Sign Dot)
                                      dotStart
                                      dot
                                      (suitsRestart zone layout from suits)
                                      dotApart
                                      dotAllowed
                                      dotSame, innerFits zone
                                      (restart layout from)
                                      named
                                      (Name name)
                                      nameStart
                                      nameComments
                                      (suitsRestart zone layout from suits)
                                      nameApart
                                      nameAllowed
                                      nameSame with
                                      | (dotKind, dotAllows, dotNotes), (nameKind, nameAllows, nameNotes) => (
                                        [lead, ..targetRest],
                                        dotToken,
                                        named,
                                        byComputing,
                                        dotKind,
                                        dotAllows,
                                        nameKind,
                                        nameAllows,
                                        (targetSpells from
                                          [lead, ..targetRest]
                                          (consViews lead targetRest targetFirst targetOthers leadSame targetRestSame)
                                          ((
                                            (apartFront (restart layout from) targetRest [dotToken, named] apart),
                                            fit
                                          ))),
                                        dotNotes,
                                        nameNotes
                                      )))))),
          targetStarts
        )
    | Negate ({ above, after }) operand, Both _ shapedOperand, Both fineMinus
          operandLexical, headedOperand, plain, Witness front
        (Witness back (Both split (Both minusLaid operandLaid))) =>
      match tokenSeen head
        { above, after }
        "-"
        (Op Minus)
        front
        pending
        fineMinus
        (seen start => operatorEvent seen Minus start)
        minusLaid, exprSpells zone layout zone.allows operand back [] suits shapedOperand operandLexical headedOperand
          commaless
          (coveredPart layout (Negate ({ above, after }) operand) operand (noIf => noIf) plain)
          operandLaid with
        | Witness minusStart (Both minusAllowed minusSeen), Witness first
            (Witness others (Both operandSeen (Both operandSpells _))) => (
          (tokenView pending (Op Minus) minusStart { above, after }),
          [first, ..others],
          (rewrite split then
            seenThen pending front back
              [(tokenView pending (Op Minus) minusStart { above, after })]
              [first, ..others]
              minusSeen
              operandSeen),
          (from tokens same =>
            viewsCons
              (later =>
                Leads (restart layout from) pending head above later
                  → Spelled (restart layout from) (Negate ({ above, after }) operand) later)
              tokens
              (tokenView pending (Op Minus) minusStart { above, after })
              [first, ..others]
              same
              (minus operandTokens minusSame operandSame leads =>
                match leads, headFits
                  (restart layout from)
                  pending
                  head
                  above
                  minus
                  operandTokens
                  (Op Minus)
                  minusStart
                  after
                  leads
                  minusAllowed
                  minusSame with
                  | (apart, _), (minusKind, minusAllows, minusNotes) => (
                    minus,
                    operandTokens,
                    byComputing,
                    minusKind,
                    minusAllows,
                    (operandSpells from operandTokens operandSame
                      (innerLeads zone
                        (restart layout from)
                        operand.firstAbove
                        operandTokens
                        (suitsRestart zone layout from suits)
                        apart)),
                    minusNotes
                  ))),
          minusAllowed,
          byComputing
        )
    | Binary operator sign left right, Both _ (Both _ (Both _ (Both _ (Both shapedLeft shapedRight)))), Both fineSign
        (Both leftLexical rightLexical), Both headedLeft headedRight, plain, Witness front
        (Witness back
          (Both split (Both leftLaid (Witness mid (Witness tail (Both backSplit (Both signLaid rightLaid))))))) =>
      match exprSpells zone layout head left front pending suits shapedLeft leftLexical headedLeft commaless.left
        (coveredPart layout (Binary operator sign left right) left (noIf => noIf.left) plain)
        leftLaid, tokenSeen zone.allows sign operator.spelling
        (Op operator)
        mid
        []
        fineSign
        (seen start => operatorEvent seen operator start)
        signLaid, exprSpells zone layout zone.allows right tail [] suits shapedRight rightLexical headedRight
          commaless.right
          (coveredPart layout (Binary operator sign left right) right (noIf => noIf.right) plain)
          rightLaid with
        | Witness leftFirst (Witness leftOthers (Both leftSeen (Both leftSpells leftStarts))), Witness signStart
            (Both signAllowed signSeen), Witness rightFirst
            (Witness rightOthers (Both rightSeen (Both rightSpells _))) => (
          leftFirst,
          (leftOthers ++ ([(tokenView [] (Op operator) signStart sign)] ++ [rightFirst, ..rightOthers])),
          (rewrite split, backSplit then
            seenThen pending front
              (mid ++ tail)
              [leftFirst, ..leftOthers]
              ([(tokenView [] (Op operator) signStart sign)] ++ [rightFirst, ..rightOthers])
              leftSeen
              (seenThen [] mid tail
                [(tokenView [] (Op operator) signStart sign)]
                [rightFirst, ..rightOthers]
                signSeen
                rightSeen)),
          (from tokens same =>
            viewsCons
              (later =>
                Leads (restart layout from) pending head left.firstAbove later
                  → Spelled (restart layout from) (Binary operator sign left right) later)
              tokens
              leftFirst
              (leftOthers ++ ([(tokenView [] (Op operator) signStart sign)] ++ [rightFirst, ..rightOthers]))
              same
              (lead rest leadSame restSame =>
                viewsSplit
                  (later =>
                    Leads (restart layout from) pending head left.firstAbove [lead, ..later]
                      → Spelled (restart layout from) (Binary operator sign left right) [lead, ..later])
                  rest
                  leftOthers
                  ([(tokenView [] (Op operator) signStart sign)] ++ [rightFirst, ..rightOthers])
                  restSame
                  (leftRest afterLeft leftRestSame afterLeftSame =>
                    viewsCons
                      (later =>
                        Leads (restart layout from) pending head left.firstAbove [lead, ..leftRest ++ later]
                          → Spelled (restart layout from) (Binary operator sign left right) [lead, ..leftRest ++ later])
                      afterLeft
                      (tokenView [] (Op operator) signStart sign)
                      [rightFirst, ..rightOthers]
                      afterLeftSame
                      (signed rightTokens signSame rightSame leads =>
                        match leads with
                          | (apart, fit) =>
                            match apartBack (restart layout from) leftRest [signed, ..rightTokens] apart with
                              | (signApart, rightApart) =>
                                match innerFits zone
                                  (restart layout from)
                                  signed
                                  (Op operator)
                                  signStart
                                  sign
                                  (suitsRestart zone layout from suits)
                                  signApart
                                  signAllowed
                                  signSame with
                                  | (signKind, signAllows, signNotes) => (
                                    [lead, ..leftRest],
                                    signed,
                                    rightTokens,
                                    byComputing,
                                    signKind,
                                    signAllows,
                                    (leftSpells from
                                      [lead, ..leftRest]
                                      (consViews lead leftRest leftFirst leftOthers leadSame leftRestSame)
                                      ((
                                        (apartFront (restart layout from) leftRest [signed, ..rightTokens] apart),
                                        fit
                                      ))),
                                    (rightSpells from rightTokens rightSame
                                      (innerLeads zone
                                        (restart layout from)
                                        right.firstAbove
                                        rightTokens
                                        (suitsRestart zone layout from suits)
                                        rightApart)),
                                    signNotes
                                  ))))),
          leftStarts
        )
    | If ({ above, after }) condition thenComments whenTrue elseComments whenFalse, Both shapedCondition
        (Both shapedTrue shapedFalse), Both fineIf
        (Both conditionLexical
          (Both fineThen (Both trueLexical (Both fineElse falseLexical)))), headed, plain, Witness ifEvents
        (Witness afterIf
          (Both ifSplit
            (Both ifLaid
              (Witness conditionEvents
                (Witness afterCondition
                  (Both conditionSplit
                    (Both conditionLaid
                      (Witness thenEvents
                        (Witness afterThen
                          (Both thenSplit
                            (Both thenLaid
                              (Witness trueEvents
                                (Witness afterTrue
                                  (Both trueSplit
                                    (Both trueLaid
                                      (Witness elseEvents
                                        (Witness falseEvents
                                          (Both elseSplit (Both elseLaid falseLaid))))))))))))))))))) =>
      match layout, suits, headed, plain with
        | InStatement _ _, _, _, never => (Bool.falseNotTrue never).impossible
        | InBrackets, _, Both headedCondition (Both headedTrue headedFalse), _ =>
          match tokenSeen head
            { above, after }
            "if"
            (Reserved IfKeyword)
            ifEvents
            pending
            fineIf
            (seen start => keywordEvent seen IfKeyword start)
            ifLaid, exprSpells zone InBrackets zone.allows condition conditionEvents [] byComputing shapedCondition
              conditionLexical headedCondition commaless.left byComputing conditionLaid, tokenSeen zone.allows
              thenComments "then"
              (Reserved ThenKeyword)
              thenEvents
              []
              fineThen
              (seen start => keywordEvent seen ThenKeyword start)
              thenLaid, bodySpells zone whenTrue trueEvents shapedTrue trueLexical headedTrue commaless.right.left
              trueLaid, tokenSeen zone.reaches elseComments "else"
            (Reserved ElseKeyword)
            elseEvents
            []
            fineElse
            (seen start => keywordEvent seen ElseKeyword start)
            elseLaid, bodySpells zone whenFalse falseEvents shapedFalse falseLexical headedFalse commaless.right.right
              falseLaid with
            | Witness ifStart (Both ifAllowed ifSeen), Witness conditionFirst
                (Witness conditionOthers (Both conditionSeen (Both conditionSpells _))), Witness thenStart
                (Both _ thenSeen), Witness trueFirst (Witness trueOthers (Both trueSeen trueSpells)), Witness elseStart
                (Both _ elseSeen), Witness falseFirst (Witness falseOthers (Both falseSeen falseSpells)) => (
              (tokenView pending (Reserved IfKeyword) ifStart { above, after }),
              ([conditionFirst, ..conditionOthers]
                ++ ([(tokenView [] (Reserved ThenKeyword) thenStart thenComments)]
                  ++ ([trueFirst, ..trueOthers]
                    ++ ([(tokenView [] (Reserved ElseKeyword) elseStart elseComments)]
                      ++ [falseFirst, ..falseOthers])))),
              (rewrite ifSplit, conditionSplit, thenSplit, trueSplit, elseSplit then
                seenThen pending ifEvents
                  (conditionEvents ++ (thenEvents ++ (trueEvents ++ (elseEvents ++ falseEvents))))
                  [(tokenView pending (Reserved IfKeyword) ifStart { above, after })]
                  ([conditionFirst, ..conditionOthers]
                    ++ ([(tokenView [] (Reserved ThenKeyword) thenStart thenComments)]
                      ++ ([trueFirst, ..trueOthers]
                        ++ ([(tokenView [] (Reserved ElseKeyword) elseStart elseComments)]
                          ++ [falseFirst, ..falseOthers]))))
                  ifSeen
                  (seenThen [] conditionEvents
                    (thenEvents ++ (trueEvents ++ (elseEvents ++ falseEvents)))
                    [conditionFirst, ..conditionOthers]
                    ([(tokenView [] (Reserved ThenKeyword) thenStart thenComments)]
                      ++ ([trueFirst, ..trueOthers]
                        ++ ([(tokenView [] (Reserved ElseKeyword) elseStart elseComments)]
                          ++ [falseFirst, ..falseOthers])))
                    conditionSeen
                    (seenThen [] thenEvents
                      (trueEvents ++ (elseEvents ++ falseEvents))
                      [(tokenView [] (Reserved ThenKeyword) thenStart thenComments)]
                      ([trueFirst, ..trueOthers]
                        ++ ([(tokenView [] (Reserved ElseKeyword) elseStart elseComments)]
                          ++ [falseFirst, ..falseOthers]))
                      thenSeen
                      (seenThen [] trueEvents
                        (elseEvents ++ falseEvents)
                        [trueFirst, ..trueOthers]
                        ([(tokenView [] (Reserved ElseKeyword) elseStart elseComments)] ++ [falseFirst, ..falseOthers])
                        trueSeen
                        (seenThen [] elseEvents falseEvents
                          [(tokenView [] (Reserved ElseKeyword) elseStart elseComments)]
                          [falseFirst, ..falseOthers]
                          elseSeen
                          falseSeen))))),
              (from tokens same =>
                viewsCons
                  (later =>
                    Leads InBrackets pending head above later
                      → Spelled InBrackets
                        (If ({ above, after }) condition thenComments whenTrue elseComments whenFalse)
                        later)
                  tokens
                  (tokenView pending (Reserved IfKeyword) ifStart { above, after })
                  ([conditionFirst, ..conditionOthers]
                    ++ ([(tokenView [] (Reserved ThenKeyword) thenStart thenComments)]
                      ++ ([trueFirst, ..trueOthers]
                        ++ ([(tokenView [] (Reserved ElseKeyword) elseStart elseComments)]
                          ++ [falseFirst, ..falseOthers]))))
                  same
                  (ifToken afterIfTokens ifSame afterIfSame =>
                    viewsSplit
                      (later =>
                        Leads InBrackets pending head above [ifToken, ..later]
                          → Spelled InBrackets
                            (If ({ above, after }) condition thenComments whenTrue elseComments whenFalse)
                            [ifToken, ..later])
                      afterIfTokens
                      [conditionFirst, ..conditionOthers]
                      ([(tokenView [] (Reserved ThenKeyword) thenStart thenComments)]
                        ++ ([trueFirst, ..trueOthers]
                          ++ ([(tokenView [] (Reserved ElseKeyword) elseStart elseComments)]
                            ++ [falseFirst, ..falseOthers])))
                      afterIfSame
                      (conditionTokens afterConditionTokens conditionSame afterConditionSame =>
                        viewsCons
                          (later =>
                            Leads InBrackets pending head above [ifToken, ..conditionTokens ++ later]
                              → Spelled InBrackets
                                (If ({ above, after }) condition thenComments whenTrue elseComments whenFalse)
                                [ifToken, ..conditionTokens ++ later])
                          afterConditionTokens
                          (tokenView [] (Reserved ThenKeyword) thenStart thenComments)
                          ([trueFirst, ..trueOthers]
                            ++ ([(tokenView [] (Reserved ElseKeyword) elseStart elseComments)]
                              ++ [falseFirst, ..falseOthers]))
                          afterConditionSame
                          (thenToken afterThenTokens thenSame afterThenSame =>
                            viewsSplit
                              (later =>
                                Leads InBrackets pending head above [ifToken, ..conditionTokens ++ [thenToken, ..later]]
                                  → Spelled InBrackets
                                    (If ({ above, after }) condition thenComments whenTrue elseComments whenFalse)
                                    [ifToken, ..conditionTokens ++ [thenToken, ..later]])
                              afterThenTokens
                              [trueFirst, ..trueOthers]
                              ([(tokenView [] (Reserved ElseKeyword) elseStart elseComments)]
                                ++ [falseFirst, ..falseOthers])
                              afterThenSame
                              (trueTokens afterTrueTokens trueSame afterTrueSame =>
                                viewsCons
                                  (later =>
                                    Leads InBrackets pending head above [
                                      ifToken,
                                      ..conditionTokens ++ [thenToken, ..trueTokens ++ later]
                                    ]
                                      → Spelled InBrackets
                                        (If ({ above, after }) condition thenComments whenTrue elseComments whenFalse)
                                        [ifToken, ..conditionTokens ++ [thenToken, ..trueTokens ++ later]])
                                  afterTrueTokens
                                  (tokenView [] (Reserved ElseKeyword) elseStart elseComments)
                                  [falseFirst, ..falseOthers]
                                  afterTrueSame
                                  (elseToken falseTokens elseSame falseSame leads =>
                                    match headFits InBrackets pending head above ifToken
                                      (conditionTokens ++ [thenToken, ..trueTokens ++ [elseToken, ..falseTokens]])
                                      (Reserved IfKeyword)
                                      ifStart
                                      after
                                      leads
                                      ifAllowed
                                      ifSame, bracketFits thenToken
                                      (Reserved ThenKeyword)
                                      thenStart
                                      thenComments
                                      thenSame, bracketFits elseToken
                                      (Reserved ElseKeyword)
                                      elseStart
                                      elseComments
                                      elseSame with
                                      | (ifKind, ifAllows, ifNotes), (thenKind, thenAllows, thenNotes), (elseKind, _,
                                          elseNotes) => (
                                        ifToken,
                                        conditionTokens,
                                        thenToken,
                                        trueTokens,
                                        elseToken,
                                        falseTokens,
                                        byComputing,
                                        ifKind,
                                        ifAllows,
                                        thenKind,
                                        thenAllows,
                                        elseKind,
                                        byComputing,
                                        (conditionSpells 0 conditionTokens conditionSame
                                          (bracketLeads zone.allows condition.firstAbove conditionTokens)),
                                        (rest after =>
                                          inlineSpelledBody InBrackets whenTrue trueTokens rest shapedTrue
                                            (trueSpells trueTokens trueSame)
                                            after),
                                        (rest after =>
                                          inlineSpelledBody InBrackets whenFalse falseTokens rest shapedFalse
                                            (falseSpells falseTokens falseSame)
                                            after),
                                        ifNotes,
                                        thenNotes,
                                        elseNotes
                                      ))))))),
              ifAllowed,
              byComputing
            )

--| Tokens with the views of the events of items between brackets spell
--| the items.
theorem itemsSpell ∀ (zone: Zone) (items: List Expr) (events: List Event)
    (shaped: ShapedItems items)
    (lexical: LexicalItems items)
    (headed: HeadedItems items)
    (commaless: NoTrailingCommasItems items)
    (laid: ItemEvents zone items events):
    ∃ (found: List TokenView) => Seen [] events found
      ∧ (∀ (tokens: List (Parse.Located Token)) => tokens.map viewOf = found → SpelledItems items tokens) :=
  match items, shaped, lexical, headed, laid with
    | [], _, _, _, laid => (
      [],
      (rewrite laid then (earlier => byComputing)),
      (tokens same => viewsNil (later => SpelledItems [] later) tokens same byComputing)
    )
    | [value], Both shapedValue _, Both valueLexical _, Both headedValue _, laid =>
      match exprSpells zone InBrackets anyStart value events [] byComputing shapedValue valueLexical headedValue
          commaless.left byComputing laid with
        | Witness first (Witness others (Both seen (Both spells _))) => (
          [first, ..others],
          seen,
          (tokens same => spells 0 tokens same (bracketLeads anyStart value.firstAbove tokens))
        )
    | [value, second, ..rest], Both shapedValue shapedRest, Both valueLexical restLexical, Both headedValue
          headedRest, Witness front
        (Witness back
          (Both split (Both valueLaid (Witness mid (Witness tail (Both backSplit (Both commaLaid restLaid))))))) =>
      match exprSpells zone InBrackets anyStart value front [] byComputing shapedValue valueLexical headedValue
          commaless.left byComputing valueLaid, tokenSeen anyStart Comments.none ","
        (Sign Comma)
        mid
        []
        fineNone
        (seen start => signEvent seen Comma start)
        commaLaid, itemsSpell zone [second, ..rest] tail shapedRest restLexical headedRest commaless.right restLaid with
        | Witness first (Witness others (Both valueSeen (Both valueSpells _))), Witness commaStart
            (Both _ commaSeen), Witness found (Both restSeen restSpelled) => (
          ([first, ..others] ++ ([tokenView [] (Sign Comma) commaStart Comments.none] ++ found)),
          (rewrite split, backSplit then
            seenThen [] front
              (mid ++ tail)
              [first, ..others]
              ([tokenView [] (Sign Comma) commaStart Comments.none] ++ found)
              valueSeen
              (seenThen [] mid tail [tokenView [] (Sign Comma) commaStart Comments.none] found commaSeen restSeen)),
          (tokens same =>
            viewsSplit
              (later => SpelledItems [value, second, ..rest] later)
              tokens
              [first, ..others]
              ([tokenView [] (Sign Comma) commaStart Comments.none] ++ found)
              same
              (valueTokens afterValue valueSame afterValueSame =>
                viewsCons
                  (later => SpelledItems [value, second, ..rest] (valueTokens ++ later))
                  afterValue
                  (tokenView [] (Sign Comma) commaStart Comments.none)
                  found
                  afterValueSame
                  (commaToken laterTokens commaSame laterSame =>
                    match bracketFits commaToken (Sign Comma) commaStart Comments.none commaSame with
                      | (commaKind, _, _) => (
                        valueTokens,
                        commaToken,
                        laterTokens,
                        byComputing,
                        commaKind,
                        (valueSpells 0 valueTokens valueSame (bracketLeads anyStart value.firstAbove valueTokens)),
                        (restSpelled laterTokens laterSame)
                      ))))
        )

--| Inside brackets, tokens with the views of a body's events spell the
--| body as one expression, laid on its keyword's line or below it.
theorem bodySpells ∀ (zone: Zone) (body: Body) (events: List Event)
    (shaped: ShapedBody body)
    (lexical: LexicalBody body)
    (headed: HeadedBody True body)
    (commaless: NoTrailingCommasBody body)
    (laid: BodyEvents zone body events):
    ∃ (first: TokenView) => ∃ (others: List TokenView) => Seen [] events [first, ..others]
      ∧ (∀ (tokens: List (Parse.Located Token)) => tokens.map viewOf = [first, ..others]
        → SpelledInline InBrackets body tokens) :=
  match body, shaped, lexical, headed, laid with
    | { statements = [{ blankBefore, line = Bare value }] }, Both (Both shapedValue _) _, Both
        (Both valueLexical _) _, Both (Both (Both _ headedValue) _) (Both unspaced _), laid =>
      match exprSpells
        (Anywhere 0)
        InBrackets
        anyStart
        value
        events
        []
        byComputing
        shapedValue
        valueLexical
        headedValue
        commaless.left
        byComputing
        (bodyFree zone blankBefore value events laid) with
        | Witness first (Witness others (Both seen (Both spells _))) => (
          first,
          others,
          seen,
          (tokens same =>
            (
              (Eq.flipped (Eq.cong firstBlankBefore unspaced)),
              (blockAheadBrackets tokens),
              (spells 0 tokens same (bracketLeads anyStart value.firstAbove tokens)),
              byComputing
            ))
        )
    | { statements = [] }, _, _, Both _ (Both _ one), _ => Void.impossible (Bool.falseNotTrue (one byComputing))
    | { statements = [{ blankBefore, line = Let _ _ _ _ _ }] }, _, _, Both _ (Both _ one), _ =>
      Void.impossible (Bool.falseNotTrue (one byComputing))
    | { statements = [{ blankBefore, line = StatementNote _ }] }, _, _, Both _ (Both _ one), _ =>
      Void.impossible (Bool.falseNotTrue (one byComputing))
    | { statements = [_, _, .._] }, _, _, Both _ (Both _ one), _ =>
      Void.impossible (Bool.falseNotTrue (one byComputing))

-- A statement's first token, `else`, and a body on its keyword's line.

theorem reachesCast ∀ (zone: Zone) (given wanted: Option Nat)
    (same: wanted = given) (reaches: zone.reaches given):
    zone.reaches wanted :=
  rewrite same then reaches

--| An `else` that starts where the zone of a statement reaches is one
--| the statement's layout allows.
theorem reachesElse ∀ (at column from: Nat) (found: Parse.Located Token) (start: Option Nat)
    (suits: at = column) (reaches: (Deeper at).reaches start)
    (same: (viewOf found).start = start):
    (InStatement column from).allowsElse found = True :=
  match found, same with
    | { value = { kind, startsLine = False, column = indent, above, trailing }, offset, length }, _ => byComputing
    | { value = { kind, startsLine = True, column = indent, above, trailing }, offset, length }, same =>
      let lower: at ≤ indent := reachesCast (Deeper at) start (Some indent) same reaches
      let level: (indent >= column) = True := arithmetic [lower, suits]
      rewrite level

theorem firstAllowed ∀ (column: Nat) (first: Parse.Located Token):
    (InStatement column first.offset).allows first = True :=
  match first with
    | { value = { kind, startsLine = False, column = indent, above, trailing }, offset, length } => byComputing
    | { value = { kind, startsLine = True, column = indent, above, trailing }, offset, length } =>
      match deeper: indent > column with
        | True => byComputing
        | False => rewrite ownOffset offset

--| The comments of a statement's first token, as the tree keeps them:
--| none above, whatever its view shows there.
theorem firstComments ∀ (column from: Nat) (first: Parse.Located Token) (pending: List Trivia) (kind: Kind)
    (start: Option Nat) (after: Option Comment)
    (is: (first.offset == from) = True)
    (same: viewOf first = tokenView pending kind start { above = [], after }):
    ({ above = [], after }: Comments) = (InStatement column from).comments first :=
  match isFirst: first.offset == from, is with
    | True, _ =>
      Eq.cong
        ((part: Option Comment) => ({ above = [], after = part }: Comments))
        (Eq.flipped (Eq.trans (trailingOf first.value.trailing) (Eq.cong ((view: TokenView) => view.trailing) same)))

--| A statement's first token leads the statement's expression when the
--| tree holds no comments above it: whatever waits above the token is
--| the block's note lines.
theorem firstLeads ∀ (column: Nat) (pending: List Trivia) (head: Option Nat → Prop)
    (first: Parse.Located Token) (others: List (Parse.Located Token))
    (apart: AllApart (InStatement column first.offset) others):
    Leads (InStatement column first.offset) pending head [] [first, ..others] :=
  Both apart (kind start after allowed same =>
    Both
      (firstAllowed column first)
      (firstComments column first.offset first pending kind start after (ownOffset first.offset) same))

--| Each number above the one before it: the offsets of tokens in source
--| order.
def Rising: List Nat → Prop
  | [] => True
  | [only] => True
  | [lower, higher, ..rest] => lower < higher ∧ Rising [higher, ..rest]

--| Tokens whose offsets rise from one no lower than a statement's start
--| aren't the statement's first.
theorem risingApart ∀ (column from bound: Nat) (tokens: List (Parse.Located Token))
    (low: from ≤ bound)
    (rising: Rising [bound, ..tokens.map (found => found.offset)]):
    AllApart (InStatement column from) tokens :=
  match tokens, rising with
    | [], _ => byComputing
    | [next, ..rest], Both above more =>
      ((arithmetic [low, above]), (risingApart column from next.offset rest (arithmetic [low, above]) more))

theorem leadsWider ∀ (layout: Layout) (pending: List Trivia) (head wide: Option Nat → Prop) (above: List Comment)
    (tokens: List (Parse.Located Token)) (wider: ∀ (start: Option Nat) => wide start → head start)
    (leads: Leads layout pending head above tokens):
    Leads layout pending wide above tokens :=
  match tokens, leads with
    | [], _ => byComputing
    | [first, ..others], Both apart fit =>
      (apart, (kind start after allowed same => fit kind start after (wider start allowed) same))

theorem notStarting ∀ (column from: Nat) (found: Parse.Located Token) (rest: List (Parse.Located Token))
    (unstarted: (viewOf found).start = None):
    blockAhead (InStatement column from) [found, ..rest] = False :=
  match found, unstarted with
    | { value = { kind, startsLine = False, column = indent, above, trailing }, offset, length }, _ => byComputing

--| No block is ahead of tokens whose first doesn't start a line.
theorem inlineAhead ∀ (layout: Layout) (tokens: List (Parse.Located Token)) (first: TokenView) (others: List TokenView)
    (same: tokens.map viewOf = [first, ..others])
    (unstarted: bracketedOf layout = False → first.start = None):
    blockAhead layout tokens = False :=
  match layout, unstarted with
    | InBrackets, _ => blockAheadBrackets tokens
    | InStatement column from, unstarted =>
      viewsCons
        (later => blockAhead (InStatement column from) later = False)
        tokens
        first
        others
        same
        (found rest foundSame _ =>
          notStarting column from found rest
            (Eq.trans (Eq.cong ((view: TokenView) => view.start) foundSame) (unstarted byComputing)))

--| Clearing the comments above an expression's first token
--| (`Layout.headed`) changes nothing in a tree that holds none there
--| outside brackets.
theorem headedOfNoAbove ∀ (layout: Layout) (value: Expr)
    (none: bracketedOf layout = False → value.firstAbove = []):
    layout.headed value = value :=
  match layout, none with
    | InBrackets, none => byComputing
    | InStatement column start, none => noAboveCleared value (none byComputing)

theorem leadsCast ∀ (layout: Layout) (pending: List Trivia) (head: Option Nat → Prop)
    (above: List Comment) (tokens: List (Parse.Located Token))
    (none: above = [])
    (leads: Leads layout pending head [] tokens):
    Leads layout pending head above tokens :=
  rewrite none then leads
