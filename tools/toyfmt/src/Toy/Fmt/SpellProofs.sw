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
def codeView (seen: Views) (kind: Kind) (start: Option Nat): Views := {
  views = [{ kind, start, above = seen.pending.reverse, trailing = None }, ..seen.views],
  pending = []
}

--| The event of a word that is neither a comment nor a line break is a
--| token of the kind the word spells.
theorem codeEvent ∀ (seen: Views) (text: Text) (start: Option Nat)
    (code: makesToken (lexemeOf text) = True):
    viewEvent seen { word = text, start } = codeView seen (lexemeKind (lexemeOf text) text) start :=
  match isBreak: text == "\n" with
    | True =>
      let same: text = "\n" := DecEq.sound isBreak
      Void.exfalso
        (Bool.falseNotTrue (Eq.trans (Eq.sym (Eq.cong ((word: Text) => makesToken (lexemeOf word)) same)) code))
    | False =>
      match lexeme: lexemeOf text, code with
        | CommentLexeme, never => Void.exfalso (Bool.falseNotTrue never)
        | LineBreak, never => Void.exfalso (Bool.falseNotTrue never)
        | Spaces, _ => rfl
        | WordLexeme, _ => rfl
        | DigitsLexeme, _ => rfl
        | StringLexeme, _ => rfl
        | SignLexeme, _ => rfl
        | SymbolsLexeme, _ => rfl
        | StrayLexeme, _ => rfl

--| A name's event is a `Name` token of its text.
theorem nameEvent ∀ (seen: Views) (text: Text) (start: Option Nat)
    (name: IsName text):
    viewEvent seen { word = text, start } = codeView seen (Name text) start :=
  match name with
    | Both (Witness first (Witness others (Both same (Both starts all)))) noKeyword =>
      let found: lexemeOf (MkText [first, ..others]) = WordLexeme :=
        Eq.cong ((lexeme: Option Lexeme) => lexeme.getOrElse StrayLexeme) (wordLexemeStart first others starts)
      let lexeme: lexemeOf text = WordLexeme := rewrite textOf text [first, ..others] same in found
      let kind: wordKind text = Name text := rewrite noKeyword in rfl
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
    | Witness first (Witness others (Both same (Both digit all))) =>
      let found: lexemeOf (MkText [first, ..others]) = DigitsLexeme :=
        Eq.cong
          ((lexeme: Option Lexeme) => lexeme.getOrElse StrayLexeme)
          (digitsLexemeStart first others digit (digitIsNoWordStart first digit))
      let lexeme: lexemeOf text = DigitsLexeme := rewrite textOf text [first, ..others] same in found
      Eq.trans
        (codeEvent seen text start (Eq.cong makesToken lexeme))
        (Eq.cong
          ((spelt: Kind) => codeView seen spelt start)
          (Eq.cong ((read: Lexeme) => lexemeKind read text) lexeme))

--| A string's event is a `Str` token of its text.
theorem stringEvent ∀ (seen: Views) (text: Text) (start: Option Nat)
    (string: IsString text):
    viewEvent seen { word = text, start } = codeView seen (Str text) start :=
  match string with
    | Witness segments (Both same _) =>
      let lexeme: lexemeOf text = StringLexeme :=
        rewrite textOf text ['"', ..Parse.joinReads segments ++ ['"']] same in rfl
      Eq.trans
        (codeEvent seen text start (Eq.cong makesToken lexeme))
        (Eq.cong
          ((spelt: Kind) => codeView seen spelt start)
          (Eq.cong ((read: Lexeme) => lexemeKind read text) lexeme))

--| A keyword's event is its `Reserved` token.
theorem keywordEvent ∀ (seen: Views) (keyword: Keyword) (start: Option Nat):
    viewEvent seen { word = keyword.spelling, start } = codeView seen (Reserved keyword) start :=
  match keyword with
    | FnKeyword => rfl
    | LetKeyword => rfl
    | IfKeyword => rfl
    | ThenKeyword => rfl
    | ElseKeyword => rfl

--| The event of a bracket, the comma, the dot or `=` is its `Sign` token.
theorem signEvent ∀ (seen: Views) (mark: Punctuation) (start: Option Nat):
    viewEvent seen { word = mark.spelling, start } = codeView seen (Sign mark) start :=
  match mark with
    | OpenParen => rfl
    | CloseParen => rfl
    | OpenSquare => rfl
    | CloseSquare => rfl
    | Comma => rfl
    | Dot => rfl
    | Defines => rfl

--| An operator's event is its `Op` token.
theorem operatorEvent ∀ (seen: Views) (operator: Operator) (start: Option Nat):
    viewEvent seen { word = operator.spelling, start } = codeView seen (Op operator) start :=
  match operator with
    | Or => rfl
    | And => rfl
    | EqualTo => rfl
    | NotEqual => rfl
    | LessThan => rfl
    | LessEqual => rfl
    | Append => rfl
    | Plus => rfl
    | Minus => rfl
    | Times => rfl
    | Divide => rfl
    | Remainder => rfl

theorem commentNoBreak ∀ (text: Text) (comment: IsComment text) (isBreak: (text == "\n") = True): Void :=
  let same: text = "\n" := DecEq.sound isBreak
  Bool.falseNotTrue
    (Eq.trans
      (Eq.sym (Eq.cong ((word: Text) => isCommentLexeme (lexemeOf word)) same))
      (Eq.cong isCommentLexeme (commentLexeme text comment)))

--| A comment that starts its line waits for the next token.
theorem ownLineEvent ∀ (seen: Views) (text: Text) (column: Nat)
    (comment: IsComment text):
    viewEvent seen { word = text, start = Some column }
      = { views = seen.views, pending = [OwnLine { text }, ..seen.pending] } :=
  match isBreak: text == "\n" with
    | True => Void.exfalso (commentNoBreak text comment isBreak)
    | False => rewrite commentLexeme text comment in rfl

--| A comment after words on its line goes on the newest token.
theorem trailingEvent ∀ (seen: Views) (text: Text)
    (comment: IsComment text):
    viewEvent seen { word = text, start = None }
      = { views = viewTrailing seen.views { text }, pending = seen.pending } :=
  match isBreak: text == "\n" with
    | True => Void.exfalso (commentNoBreak text comment isBreak)
    | False => rewrite commentLexeme text comment in rfl

-- The views of a token's events, and of events one after another.

theorem viewsAppend ∀ (seen: Views) (front back: List Event):
    viewsFrom seen (front ++ back) = viewsFrom (viewsFrom seen front) back :=
  match front with
    | [] => rfl
    | [event, ..rest] => viewsAppend (viewEvent seen event) rest back

--| The trivia waiting (the newest first) once the comments `above` have
--| been seen after `pending`.
def waiting (pending: List Trivia) (above: List Comment): List Trivia := match above with
  | [] => pending
  | [comment, ..rest] => waiting [OwnLine comment, ..pending] rest

theorem waitingReverse ∀ (pending: List Trivia) (above: List Comment):
    (waiting pending above).reverse = pending.reverse ++ above.map OwnLine :=
  match above with
    | [] => Eq.sym (List.appendNil pending.reverse)
    | [comment, ..rest] =>
      Eq.trans
        (waitingReverse [OwnLine comment, ..pending] rest)
        (Eq.trans
          (Eq.cong ((front: List Trivia) => front ++ rest.map OwnLine) (List.reverseCons (OwnLine comment) pending))
          (List.appendAssoc pending.reverse [OwnLine comment] (rest.map OwnLine)))

--| The comments above a token, each starting its line, all wait.
theorem aboveViews ∀ (above: List Comment) (column: Nat) (seen: Views)
    (fine: FineAbove above):
    viewsFrom seen (aboveEvents column above) = { views = seen.views, pending = waiting seen.pending above } :=
  match above, fine with
    | [], _ =>
      match seen with
        | { views, pending } => rfl
    | [{ text }, ..rest], Both fineFirst fineRest =>
      Eq.trans
        (Eq.cong ((next: Views) => viewsFrom next (aboveEvents column rest)) (ownLineEvent seen text column fineFirst))
        (aboveViews rest column { views = seen.views, pending = [OwnLine { text }, ..seen.pending] } fineRest)

--| The view of a token of the tree: the comments above it after what
--| was waiting, and its trailing comment.
def tokenView (pending: List Trivia) (kind: Kind) (start: Option Nat) (comments: Comments): TokenView := {
  kind,
  start,
  above = (waiting pending comments.above).reverse,
  trailing = comments.after
}

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
    Eq.trans
      (viewsAppend { views = earlier, pending } front back)
      (Eq.trans
        (Eq.cong ((seen: Views) => viewsFrom seen back) (one earlier))
        (Eq.trans
          (other (first.reverse ++ earlier))
          (Eq.cong
            ((views: List TokenView) => ({ views, pending = [] }: Views))
            (Eq.trans
              (Eq.sym (List.appendAssoc second.reverse first.reverse earlier))
              (Eq.cong
                ((front: List TokenView) => front ++ earlier)
                (Eq.sym (List.reverseAppend first second)))))))

--| A token's events are one view, starting where the events allow.
theorem tokenSeen ∀ (allowed: Option Nat → Prop) (comments: Comments) (text: Text) (kind: Kind)
    (events: List Event) (pending: List Trivia)
    (fine: Fine comments)
    (reads: ∀ (seen: Views) (start: Option Nat) => viewEvent seen { word = text, start } = codeView seen kind start)
    (laid: TokenAt allowed comments text events):
    ∃ (start: Option Nat) => allowed start ∧ Seen pending events [tokenView pending kind start comments] :=
  match comments, fine, laid with
    | { above, after = None }, Both fineAbove _, Witness column (Witness start (Both ok split)) =>
      Witness start
        (Both ok
          (earlier =>
            rewrite split in
              Eq.trans
                (viewsAppend { views = earlier, pending } (aboveEvents column above) [{ word = text, start }])
                (Eq.trans
                  (Eq.cong
                    ((seen: Views) => viewsFrom seen [{ word = text, start }])
                    (aboveViews above column { views = earlier, pending } fineAbove))
                  (reads { views = earlier, pending = waiting pending above } start))))
    | { above, after = Some { text = written } }, Both fineAbove fineAfter,
      Witness column (Witness start (Both ok split)) =>
      Witness start
        (Both ok
          (earlier =>
            rewrite split in
              Eq.trans
                (viewsAppend
                  { views = earlier, pending }
                  (aboveEvents column above)
                  [{ word = text, start }, { word = written, start = None }])
                (Eq.trans
                  (Eq.cong
                    ((seen: Views) => viewsFrom seen [{ word = text, start }, { word = written, start = None }])
                    (aboveViews above column { views = earlier, pending } fineAbove))
                  (Eq.trans
                    (Eq.cong
                      ((seen: Views) => viewEvent seen { word = written, start = None })
                      (reads { views = earlier, pending = waiting pending above } start))
                    (trailingEvent
                      (codeView { views = earlier, pending = waiting pending above } kind start)
                      written
                      fineAfter)))))

-- A token of the tree from its view.

theorem ownComments ∀ (above: List Comment): ownLineComments (above.map OwnLine) = above := match above with
  | [] => rfl
  | [comment, ..rest] => Eq.cong (Cons comment) (ownComments rest)

theorem trailingOf ∀ (trailing: Option (Parse.Located Comment)):
    trailing.map (comment => comment.value) = commentOf trailing :=
  match trailing with
    | None => rfl
    | Some _ => rfl

theorem commentsSame ∀ (comments: Comments) (above: List Comment) (after: Option Comment)
    (sameAbove: above = comments.above)
    (sameAfter: after = comments.after):
    comments = { above, after } :=
  match comments, sameAbove, sameAfter with
    | { above = held, after = kept }, sameAbove, sameAfter =>
      Eq.trans
        (Eq.cong ((part: List Comment) => ({ above = part, after = kept }: Comments)) (Eq.sym sameAbove))
        (Eq.cong ((part: Option Comment) => ({ above, after = part }: Comments)) (Eq.sym sameAfter))

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
    | [], _ => rfl
    | [token, ..rest], Both one others => Both one (apartFront layout rest back others)

theorem apartBack ∀ (layout: Layout) (front back: List (Parse.Located Token))
    (apart: AllApart layout (front ++ back)):
    AllApart layout back :=
  match front, apart with
    | [], apart => apart
    | [token, ..rest], Both one others => apartBack layout rest back others

theorem bracketApart ∀ (tokens: List (Parse.Located Token)): AllApart InBrackets tokens := match tokens with
  | [] => rfl
  | [token, ..rest] => Both rfl (bracketApart rest)

--| `token` is the tree's token of `kind` with `comments`, as `Spelled`
--| asks at `layout`.
def Fits (layout: Layout) (token: Parse.Located Token) (kind: Kind) (comments: Comments): Prop :=
  token.value.kind = kind ∧ layout.allows token = True ∧ comments = layout.comments token

theorem allowsCast ∀ (zone: Zone) (given wanted: Option Nat)
    (same: wanted = given)
    (allowed: zone.allows given):
    zone.allows wanted :=
  rewrite same in allowed

--| A token that starts where the zone deeper than a statement allows is
--| one the statement's layout allows.
theorem deeperAllows ∀ (at column from: Nat) (token: Parse.Located Token) (start: Option Nat)
    (suits: at = column)
    (allowed: (Deeper at).allows start)
    (same: (viewOf token).start = start):
    (InStatement column from).allows token = True :=
  match token, same with
    | { value = { kind, startsLine = False, column = indent, above, trailing }, offset, length }, _ => rfl
    | { value = { kind, startsLine = True, column = indent, above, trailing }, offset, length }, same =>
      let lower: at < indent := allowsCast (Deeper at) start (Some indent) same allowed
      let deeper: (indent > column) = True := omega [lower, suits]
      rewrite deeper in rfl

--| A token of the tree that isn't its statement's first, from its view.
theorem innerFits ∀ (zone: Zone) (layout: Layout) (token: Parse.Located Token)
    (kind: Kind) (start: Option Nat) (comments: Comments)
    (suits: Suits zone layout)
    (apart: Apart layout token)
    (allowed: zone.allows start)
    (same: viewOf token = tokenView [] kind start comments):
    Fits layout token kind comments :=
  match layout, zone, suits, apart, allowed with
    | InBrackets, _, _, _, _ =>
      Both (Eq.cong ((view: TokenView) => view.kind) same) (Both rfl (viewComments token kind start comments same))
    | InStatement column from, Deeper at, suits, apart, allowed =>
      Both
        (Eq.cong ((view: TokenView) => view.kind) same)
        (Both
          (deeperAllows at column from token start suits allowed (Eq.cong ((view: TokenView) => view.start) same))
          (match isFirst: token.offset == from, apart with
            | False, _ => viewComments token kind start comments same))
    | InStatement column from, Anywhere at, never, _, _ => Void.exfalso (Bool.falseNotTrue never)

theorem bracketFits ∀ (token: Parse.Located Token) (kind: Kind) (start: Option Nat) (comments: Comments)
    (same: viewOf token = tokenView [] kind start comments):
    Fits InBrackets token kind comments :=
  innerFits (Anywhere 0) InBrackets token kind start comments rfl rfl rfl same

--| What the induction knows of the tokens of an expression whose
--| leftmost token starts as `head` says after `pending`: every other
--| token isn't the statement's first, and the leftmost fits the tree
--| (it may be the statement's first, whose comments above are the
--| block's note lines).
def Leads (layout: Layout) (pending: List Trivia) (head: Option Nat → Prop) (above: List Comment)
    (tokens: List (Parse.Located Token)):
    Prop :=
  match tokens with
    | [] => True
    | [first, ..others] =>
      AllApart layout others
        ∧ (∀ (kind: Kind) (start: Option Nat) (after: Option Comment) => head start
          → viewOf first = tokenView pending kind start { above, after }
          → layout.allows first = True ∧ ({ above, after }: Comments) = layout.comments first)

theorem headFits ∀ (layout: Layout) (pending: List Trivia) (head: Option Nat → Prop) (above: List Comment)
    (first: Parse.Located Token) (others: List (Parse.Located Token))
    (kind: Kind) (start: Option Nat) (after: Option Comment)
    (leads: Leads layout pending head above [first, ..others])
    (allowed: head start)
    (same: viewOf first = tokenView pending kind start { above, after }):
    Fits layout first kind { above, after } :=
  match leads with
    | Both _ fit => Both (Eq.cong ((view: TokenView) => view.kind) same) (fit kind start after allowed same)

--| The tokens of an expression that isn't its statement's first lead.
theorem innerLeads ∀ (zone: Zone) (layout: Layout) (above: List Comment) (tokens: List (Parse.Located Token))
    (suits: Suits zone layout)
    (apart: AllApart layout tokens):
    Leads layout [] zone.allows above tokens :=
  match tokens, apart with
    | [], _ => rfl
    | [first, ..others], Both one rest =>
      Both rest
        (kind start after allowed same =>
          match innerFits zone layout first kind start { above, after } suits one allowed same with
            | Both _ both => both)

theorem bracketLeads ∀ (head: Option Nat → Prop) (above: List Comment) (tokens: List (Parse.Located Token)):
    Leads InBrackets [] head above tokens :=
  match tokens with
    | [] => rfl
    | [first, ..others] =>
      Both
        (bracketApart others)
        (kind start after allowed same =>
          match bracketFits first kind start { above, after } same with
            | Both _ both => both)

-- Tokens taken apart as their views are.

def noViews (views: List TokenView): Bool := match views with
  | [] => True
  | _ => False

theorem viewsNil ∀ (goal: List (Parse.Located Token) → Prop) (tokens: List (Parse.Located Token))
    (same: tokens.map viewOf = [])
    (step: goal []):
    goal tokens :=
  match tokens, same with
    | [], _ => step
    | [token, ..rest], same => Void.exfalso (Bool.falseNotTrue (Eq.cong noViews same))

theorem viewsCons ∀ (goal: List (Parse.Located Token) → Prop) (tokens: List (Parse.Located Token))
    (view: TokenView) (views: List TokenView)
    (same: tokens.map viewOf = [view, ..views])
    (step: ∀ (token: Parse.Located Token) (rest: List (Parse.Located Token)) => viewOf token = view
      → rest.map viewOf = views
      → goal [token, ..rest]):
    goal tokens :=
  match tokens, same with
    | [token, ..rest], same =>
      step token rest
        (List.consInjectiveHead (viewOf token) view (rest.map viewOf) views same)
        (Eq.cong (.drop 1) same)
    | [], same => Void.exfalso (Bool.falseNotTrue (Eq.sym (Eq.cong noViews same)))

theorem viewsOne ∀ (goal: List (Parse.Located Token) → Prop) (tokens: List (Parse.Located Token))
    (view: TokenView)
    (same: tokens.map viewOf = [view])
    (step: ∀ (token: Parse.Located Token) => viewOf token = view → goal [token]):
    goal tokens :=
  viewsCons goal tokens view [] same
    (found rest tokenSame restSame =>
      viewsNil ((later: List (Parse.Located Token)) => goal [found, ..later]) rest restSame (step found tokenSame))

theorem consViews ∀ (token: Parse.Located Token) (rest: List (Parse.Located Token))
    (view: TokenView) (views: List TokenView)
    (tokenSame: viewOf token = view)
    (restSame: rest.map viewOf = views):
    [token, ..rest].map viewOf = [view, ..views] :=
  Eq.trans
    (Eq.cong ((first: TokenView) => [first, ..rest.map viewOf]) tokenSame)
    (Eq.cong (Cons view) restSame)

theorem viewsSplit ∀ (goal: List (Parse.Located Token) → Prop) (tokens: List (Parse.Located Token))
    (front back: List TokenView)
    (same: tokens.map viewOf = front ++ back)
    (step: ∀ (first second: List (Parse.Located Token)) => first.map viewOf = front
      → second.map viewOf = back
      → goal (first ++ second)):
    goal tokens :=
  match front, same, step with
    | [], same, step => step [] tokens rfl same
    | [view, ..views], same, step =>
      viewsCons goal tokens view (views ++ back) same
        (found rest tokenSame restSame =>
          viewsSplit ((later: List (Parse.Located Token)) => goal [found, ..later]) rest views back restSame
            (first second firstSame secondSame =>
              step [found, ..first] second (consViews found first view views tokenSame firstSame) secondSame))
