--| Rule N undoes what the printer does with a closer: `settledViews`'
--| middle (toy-plus-plus.md §3.1).
--|
--| The rules lay a file's events in the tree's order (`FileEvents`). The
--| printer writes a closer (`Closing`) before a trailing comment that
--| waits on its line, so the printed trace is the laid one with those
--| comments after their closers (`Toy.Doc.Proofs.Tucks`), and the lexer
--| puts each on the last closer of its line. Rule N's first half, said of
--| token views (`homeViews`, which `tokensHomeViews` ties to
--| `homeStep`), moves each back: over the tucked closers, which hold
--| nothing, to the token the tree has it on, where it stays because the
--| laid trace is calm (`CalmProofs.sw`). So the views of the printed
--| trace, homed, are the views of the laid one (`tucksHome`).

namespace Toy.Fmt.Proofs
import Toy.Doc (..)
import Toy.Doc.Proofs (..)
import Toy.Syntax (..)
import Toy.Syntax.Proofs (..)
import Toy.Fmt (..)
import Std (Bool, DecEq, Eq, List, Nat, Option, Parse, Text, Void)

-- Rule N's first half, on views.

def movesPastView (current previous: TokenView): Bool :=
  (current.kind.isCloser || current.kind.isComma) && not (hasOwnLine current.above) && previous.trailing.isNone

def homedView (comment: Comment) (current: TokenView) (earlier: List TokenView): List TokenView := match earlier with
  | [previous, ..rest] if movesPastView current previous =>
    [{ current | trailing = None }, ..homedView comment previous rest]
  | _ => [{ current | trailing = Some comment }, ..earlier]

def homeStepView (earlier: List TokenView) (view: TokenView): List TokenView := match view.trailing with
  | Some comment if view.kind.isCloser || view.kind.isComma => homedView comment view earlier
  | _ => [view, ..earlier]

--| `homeStep` over views that are newest first, the oldest read first.
def homeViews: List TokenView → List TokenView
  | [] => []
  | [newest, ..earlier] => homeStepView (homeViews earlier) newest

theorem homedViews ∀ (comment: Parse.Located Comment)
    (current: Parse.Located Token) (earlier: List (Parse.Located Token)):
    (homed comment current earlier).map viewOf = homedView comment.value (viewOf current) (earlier.map viewOf) :=
  match earlier with
    | [] => byComputing
    | [{ value = { kind, startsLine, column, above, trailing }, offset, length }, ..rest] =>
      match closes: current.value.kind.isCloser || current.value.kind.isComma with
        | False => byComputing
        | True =>
          match own: hasOwnLine current.value.above with
            | True => byComputing
            | False =>
              match trailing with
                | Some held => byComputing
                | None =>
                  Eq.cong
                    ((later: List TokenView) => [viewOf (trailingSet current None), ..later])
                    (homedViews comment
                      { value = { kind, startsLine, column, above, trailing = None }, offset, length }
                      rest)

theorem homeStepViews ∀ (earlier: List (Parse.Located Token)) (token: Parse.Located Token):
    (homeStep earlier token).map viewOf = homeStepView (earlier.map viewOf) (viewOf token) :=
  match token with
    | { value = { kind, startsLine, column, above, trailing }, offset, length } =>
      match trailing with
        | None => byComputing
        | Some comment =>
          match closes: kind.isCloser || kind.isComma with
            | False => byComputing
            | True =>
              homedViews comment
                { value = { kind, startsLine, column, above, trailing = Some comment }, offset, length }
                earlier

theorem homeFoldViews ∀ (tokens earlier: List (Parse.Located Token)):
    (tokens.foldLeft earlier homeStep).map viewOf = (tokens.map viewOf).foldLeft (earlier.map viewOf) homeStepView :=
  match tokens with
    | [] => byComputing
    | [token, ..rest] =>
      Eq.trans
        (homeFoldViews rest (homeStep earlier token))
        (Eq.cong
          ((found: List TokenView) => (rest.map viewOf).foldLeft found homeStepView)
          (homeStepViews earlier token))

theorem homeViewsFold ∀ (views: List TokenView): views.reverse.foldLeft [] homeStepView = homeViews views :=
  match views with
    | [] => byComputing
    | [newest, ..earlier] =>
      calc [newest, ..earlier].reverse.foldLeft [] homeStepView
        _ = (earlier.reverse ++ [newest]).foldLeft [] homeStepView :=
          Eq.cong ((found: List TokenView) => found.foldLeft [] homeStepView) (List.reverseCons newest earlier)
        _ = homeStepView (earlier.reverse.foldLeft [] homeStepView) newest :=
          List.foldLeftAppend earlier.reverse [] [newest] homeStepView
        _ = homeStepView (homeViews earlier) newest :=
          Eq.cong ((found: List TokenView) => homeStepView found newest) (homeViewsFold earlier)

--| The views of the tokens rule N's first half gives are the tokens'
--| views, homed.
theorem tokensHomeViews ∀ (tokens: List (Parse.Located Token)):
    (tokens.reverse.foldLeft [] homeStep).map viewOf = homeViews (tokens.map viewOf) :=
  calc (tokens.reverse.foldLeft [] homeStep).map viewOf
    _ = (tokens.reverse.map viewOf).foldLeft [] homeStepView := homeFoldViews tokens.reverse []
    _ = (tokens.map viewOf).reverse.foldLeft [] homeStepView :=
      Eq.cong ((found: List TokenView) => found.foldLeft [] homeStepView) (List.mapReverse tokens viewOf)
    _ = homeViews (tokens.map viewOf) := homeViewsFold (tokens.map viewOf)

-- Views that stay.

theorem freshHome ∀ (view: TokenView) (earlier: List TokenView)
    (none: view.trailing = None):
    homeStepView earlier view = [view, ..earlier] :=
  match view, none with | { kind, start, above, trailing = None }, _ => byComputing

--| A trailing comment on a steady view doesn't move back from it.
theorem steadyHomed ∀ (comment: Comment) (top: TokenView)
    (earlier: List TokenView) (steady: SteadyView { top | trailing = Some comment } earlier):
    homedView comment top earlier = [{ top | trailing = Some comment }, ..earlier] :=
  match top, steady with
    | { kind, start, above, trailing }, (_, blocked) =>
      match earlier, blocked with
        | [], _ => byComputing
        | [previous, ..rest], blocked =>
          match closes: kind.isCloser || kind.isComma with
            | False => byComputing
            | True =>
              let stays := blocked byComputing byComputing
              match own: hasOwnLine above with
                | True => byComputing
                | False =>
                  match prior: previous.trailing with
                    | Some held => byComputing

theorem steadyHome ∀ (view: TokenView) (earlier: List TokenView)
    (steady: SteadyView view earlier):
    homeStepView earlier view = [view, ..earlier] :=
  match view, steady with
    | { kind, start, above, trailing = None }, _ => byComputing
    | { kind, start, above, trailing = Some comment }, steady =>
      let homed := steadyHomed comment { kind, start, above, trailing = Some comment } earlier steady
      match closes: kind.isCloser || kind.isComma with
        | False => byComputing
        | True => homed

-- The closers tucked before a comment.

--| A tucked closer as a view: a closing bracket or comma that holds
--| nothing.
def CloserView (view: TokenView): Prop :=
  (view.kind.isCloser || view.kind.isComma) = True ∧ view.above = [] ∧ view.trailing = None

def closerView (event: Event): TokenView :=
  { kind = lexemeKind (lexemeOf event.word) event.word, start = event.start, above = [], trailing = None }

--| A closer after words on its line is a token that holds nothing.
theorem closerSeen ∀ (views: List TokenView) (event: Event)
    (closer: Closer event):
    viewEvent { views, pending = [] } event = { views = [closerView event, ..views], pending = [] }
      ∧ CloserView (closerView event) :=
  match event, closer with
    | { word, start }, (unstarted, closes) =>
      match round: word == ")" with
        | True =>
          let same: word = ")" := DecEq.sound round
          rewrite same then (byComputing, byComputing, byComputing, byComputing)
        | False =>
          match square: word == "]" with
            | True =>
              let same: word = "]" := DecEq.sound square
              rewrite same then (byComputing, byComputing, byComputing, byComputing)
            | False =>
              match comma: word == "," with
                | True =>
                  let same: word = "," := DecEq.sound comma
                  rewrite same then (byComputing, byComputing, byComputing, byComputing)

--| The views after closers, each a token on top of those before.
def tuckViews (closers: List Event) (onto: List TokenView): List TokenView := match closers with
  | [] => onto
  | [closer, ..rest] => tuckViews rest [closerView closer, ..onto]

theorem closersSeen ∀ (closers: List Event) (views: List TokenView)
    (all: List.All Closer closers):
    viewsFrom { views, pending = [] } closers = { views = tuckViews closers views, pending = [] } :=
  match closers, all with
    | [], _ => byComputing
    | [closer, ..rest], (first, others) =>
      Eq.trans
        (Eq.cong ((seen: Views) => viewsFrom seen rest) (closerSeen views closer first).left)
        (closersSeen rest [closerView closer, ..views] others)

theorem closerViewsSnoc ∀ (front: List TokenView) (last: TokenView)
    (all: List.All CloserView front)
    (closer: CloserView last):
    List.All CloserView (front ++ [last]) :=
  match front, all with
    | [], _ => (closer, ())
    | [first, ..rest], (firstCloser, others) => (firstCloser, (closerViewsSnoc rest last others closer))

--| The closers' views are in front of the views they were read onto.
theorem tuckViewsFront ∀ (closers: List Event)
    (all: List.All Closer closers):
    ∃ (front: List TokenView) => List.All CloserView front
      ∧ (∀ (onto: List TokenView) => tuckViews closers onto = front ++ onto) :=
  match closers, all with
    | [], _ => ([], (), (onto => byComputing))
    | [closer, ..rest], (first, others) =>
      match tuckViewsFront rest others with
        | (front, allFront, same) => (
          (front ++ [closerView closer]),
          (closerViewsSnoc front (closerView closer) allFront (closerSeen [] closer first).right),
          (onto =>
            Eq.trans (same [closerView closer, ..onto]) (List.appendAssoc front [closerView closer] onto).flipped)
        )

--| Closers hold no trailing comment, so rule N leaves them where they
--| are.
theorem prefixHome ∀ (front: List TokenView) (top: TokenView) (rest home: List TokenView)
    (all: List.All CloserView front)
    (topFree: top.trailing = None)
    (sameHome: homeViews rest = home):
    homeViews (front ++ [top, ..rest]) = front ++ [top, ..home] :=
  match front, all with
    | [], _ =>
      Eq.trans (Eq.cong ((found: List TokenView) => homeStepView found top) sameHome) (freshHome top home topFree)
    | [first, ..others], (closer, more) =>
      Eq.trans
        (Eq.cong
          ((found: List TokenView) => homeStepView found first)
          (prefixHome others top rest home more topFree sameHome))
        (freshHome first (others ++ [top, ..home]) closer.right.right)

theorem noneNotSome ∀ (comment: Comment) (wrong: Some comment = (None: Option Comment)): Void := cases

--| A comment on the newest of the closers written before it goes back
--| over all of them, each holding nothing, to the token before them,
--| where it stays: by induction on the closers.
theorem pastClosers ∀ (comment: Comment) (newest: TokenView) (others: List TokenView)
    (top: TokenView) (home: List TokenView)
    (closer: CloserView newest)
    (all: List.All CloserView others)
    (topFree: top.trailing = None) (steady: SteadyView { top | trailing = Some comment } home):
    homedView comment newest (others ++ [top, ..home])
      = [newest, ..others ++ [{ top | trailing = Some comment }, ..home]] :=
  match newest, closer with
    | { kind, start, above, trailing }, (closes, noAbove, noTrailing) =>
      match others, all with
        | [], _ =>
          match top, topFree, steady with
            | { kind = topKind, start = topStart, above = topAbove, trailing = Some held }, wrong, _ =>
              (noneNotSome held wrong).impossible
            | { kind = topKind, start = topStart, above = topAbove, trailing = None }, _, steady =>
              let stays :=
                steadyHomed comment { kind = topKind, start = topStart, above = topAbove, trailing = None } home steady
              rewrite closes, noAbove, noTrailing, stays
        | [{ kind = nextKind, start = nextStart, above = nextAbove, trailing = Some held }, ..more], (
            (_, _, wrong),
            _
          ) => (noneNotSome held wrong).impossible
        | [{ kind = nextKind, start = nextStart, above = nextAbove, trailing = None }, ..more], (nextCloser,
            moreClosers) =>
          let later :=
            pastClosers comment
              { kind = nextKind, start = nextStart, above = nextAbove, trailing = None }
              more
              top
              home
              nextCloser
              moreClosers
              topFree
              steady
          rewrite closes, noAbove, noTrailing, later

--| Where a comment on a view goes doesn't depend on what the view held.
theorem homedTrailing ∀ (comment: Comment) (current: TokenView) (held: Option Comment) (earlier: List TokenView):
    homedView comment { current | trailing = held } earlier = homedView comment current earlier :=
  match current with
    | { kind, start, above, trailing } =>
      match earlier with
        | [] => byComputing
        | [previous, ..rest] => byComputing

theorem closerHomes ∀ (comment: Comment) (view: TokenView) (earlier: List TokenView)
    (closes: (view.kind.isCloser || view.kind.isComma) = True):
    homeStepView earlier { view | trailing = Some comment }
      = homedView comment { view | trailing = Some comment } earlier :=
  match view, closes with | { kind, start, above, trailing }, closes => rewrite closes

--| The printed views of a comment after the closers tucked before it,
--| homed, are the laid ones: the comment on the token before the closers.
theorem tuckHome ∀ (front: List TokenView) (comment: Comment) (top: TokenView) (rest home: List TokenView)
    (all: List.All CloserView front)
    (topFree: top.trailing = None)
    (sameHome: homeViews rest = home) (steady: SteadyView { top | trailing = Some comment } home):
    homeViews (viewTrailing (front ++ [top, ..rest]) comment) = front ++ [{ top | trailing = Some comment }, ..home] :=
  match front, all with
    | [], _ =>
      Eq.trans
        (Eq.cong ((found: List TokenView) => homeStepView found { top | trailing = Some comment }) sameHome)
        (steadyHome { top | trailing = Some comment } home steady)
    | [newest, ..others], (closer, more) =>
      calc homeStepView (homeViews (others ++ [top, ..rest])) { newest | trailing = Some comment }
        _ = homeStepView (others ++ [top, ..home]) { newest | trailing = Some comment } :=
          Eq.cong
            ((found: List TokenView) => homeStepView found { newest | trailing = Some comment })
            (prefixHome others top rest home more topFree sameHome)
        _ = homedView comment { newest | trailing = Some comment } (others ++ [top, ..home]) :=
          closerHomes comment newest (others ++ [top, ..home]) closer.left
        _ = homedView comment newest (others ++ [top, ..home]) :=
          homedTrailing comment newest (Some comment) (others ++ [top, ..home])
        _ = [newest, ..others ++ [{ top | trailing = Some comment }, ..home]] :=
          pastClosers comment newest others top home closer more topFree steady

-- Stretch by stretch.

--| The laid views `laid` and the printed views `printed` after the same
--| stretches, where the laid trace is calm so far (`found`): the printed
--| ones, homed, are the laid ones, which are stable.
def JoinedAt (found: Option Prior) (laid printed: Views): Prop := match found with
  | None => True
  | Some prior =>
    homeViews printed.views = laid.views ∧ printed.pending = laid.pending ∧ Suited prior laid ∧ StableViews laid.views

--| After a token, the newest printed view is that token's, with no
--| trailing comment yet.
def FreshTop (prior: Prior) (printed: Views): Prop := match prior with
  | Worded _ => ∃ (top: TokenView) => ∃ (rest: List TokenView) => printed.views = [top, ..rest] ∧ top.trailing = None
  | _ => True

def FreshAt (found: Option Prior) (printed: Views): Prop := match found with
  | None => True
  | Some prior => FreshTop prior printed

theorem joinedOf ∀ (found: Option Prior) (laid printed: Views)
    (kept: StaysCalm found laid)
    (home: homeViews printed.views = laid.views)
    (pending: printed.pending = laid.pending):
    JoinedAt found laid printed :=
  match found, kept with
    | None, _ => byComputing
    | Some prior, (suited, stable) => (home, pending, suited, stable)

theorem calmFromNone ∀ (events: List Event): calmFrom None events = None := match events with
  | [] => byComputing
  | [event, ..rest] => calmFromNone rest

theorem freshOf ∀ (found: Option Prior) (printed: Views) (top: TokenView) (rest: List TokenView)
    (same: printed.views = [top, ..rest])
    (free: top.trailing = None):
    FreshAt found printed :=
  match found with
    | None => byComputing
    | Some Blanked => byComputing
    | Some Noted => byComputing
    | Some Trailed => byComputing
    | Some (Worded able) => (top, rest, same, free)

--| A token read onto both: the same view on top of each.
theorem wordHome ∀ (prior: Prior) (kind: Kind) (start: Option Nat) (laid printed: Views)
    (home: homeViews printed.views = laid.views)
    (pending: printed.pending = laid.pending)
    (kept: StaysCalm (afterWord prior kind) (codeView laid kind start)):
    JoinedAt (afterWord prior kind) (codeView laid kind start) (codeView printed kind start)
      ∧ FreshAt (afterWord prior kind) (codeView printed kind start) :=
  (
    (joinedOf
      (afterWord prior kind)
      (codeView laid kind start)
      (codeView printed kind start)
      kept
      (rewrite home, pending)
      byComputing),
    (freshOf
      (afterWord prior kind)
      (codeView printed kind start)
      { kind, start, above = printed.pending.reverse, trailing = None }
      printed.views
      byComputing
      byComputing)
  )

theorem breakNotStart ∀ (word: Text) (at: Nat) (wrong: (None: Option Nat) = Some at): Void := cases

--| One event read onto both keeps them joined, where a trailing comment
--| finds the token it follows without one: after a token (`FreshTop`), not
--| at a line's start.
theorem keptHome ∀ (event: Event) (found: Option Prior) (laid printed: Views)
    (joined: JoinedAt found laid printed)
    (fresh: FreshAt found printed ∨ Stretch.Starts (Kept event)):
    JoinedAt (stepOn found event) (viewEvent laid event) (viewEvent printed event)
      ∧ FreshAt (stepOn found event) (viewEvent printed event) :=
  match found, joined, fresh with
    | None, _, _ => (byComputing, byComputing)
    | Some prior, (home, pending, suited, stable), fresh =>
      let kept := calmStepViews prior event laid suited stable
      match event, kept, fresh with
        | { word, start }, kept, fresh =>
          match isBreak: word == "\n" with
            | True => (((home, (Eq.cong addBlank pending), kept.left, kept.right)), byComputing)
            | False =>
              match lexeme: lexemeOf word with
                | CommentLexeme =>
                  match start, kept, fresh with
                    | Some column, kept, _ => (
                      (
                        home,
                        (Eq.cong ((waiting: List Trivia) => [OwnLine { text = word }, ..waiting]) pending),
                        kept.left,
                        kept.right
                      ),
                      byComputing
                    )
                    | None, kept, fresh =>
                      match prior, kept, fresh with
                        | Blanked, _, _ => (byComputing, byComputing)
                        | Noted, _, _ => (byComputing, byComputing)
                        | Trailed, _, _ => (byComputing, byComputing)
                        | Worded False, _, _ => (byComputing, byComputing)
                        | Worded True, kept, Inr (Inl (at, wrong)) => (breakNotStart word at wrong).impossible
                        | Worded True, kept, Inr (Inr same) =>
                          (Bool.trueNotFalse (rewrite same at isBreak then isBreak)).impossible
                        | Worded True, kept, Inl (top, rest, same, topFree) =>
                          match laid, printed, home, pending, same, kept with
                            | { views = laidViews, pending = laidPending }, {
                                views = printedViews,
                                pending = printedPending
                              }, home, pending, same, kept =>
                              let homed: homeViews [top, ..rest] = laidViews := rewrite same at home then home
                              let sameLaid: laidViews = [top, ..homeViews rest] :=
                                Eq.trans homed.flipped (freshHome top (homeViews rest) topFree)
                              let after: StaysCalm (Some Trailed) {
                                views = [{ top | trailing = Some { text = word } }, ..homeViews rest],
                                pending = laidPending
                              } :=
                                rewrite sameLaid at kept then kept
                              rewrite same, sameLaid then
                                (
                                  (
                                    (steadyHome
                                      { top | trailing = Some { text = word } }
                                      (homeViews rest)
                                      after.right.left),
                                    pending,
                                    after.left,
                                    after.right
                                  ),
                                  byComputing
                                )
                | Spaces => wordHome prior (lexemeKind Spaces word) start laid printed home pending kept
                | LineBreak => wordHome prior (lexemeKind LineBreak word) start laid printed home pending kept
                | WordLexeme => wordHome prior (lexemeKind WordLexeme word) start laid printed home pending kept
                | DigitsLexeme => wordHome prior (lexemeKind DigitsLexeme word) start laid printed home pending kept
                | StringLexeme => wordHome prior (lexemeKind StringLexeme word) start laid printed home pending kept
                | SignLexeme => wordHome prior (lexemeKind SignLexeme word) start laid printed home pending kept
                | SymbolsLexeme => wordHome prior (lexemeKind SymbolsLexeme word) start laid printed home pending kept
                | StrayLexeme => wordHome prior (lexemeKind StrayLexeme word) start laid printed home pending kept

theorem staysCast ∀ (found other: Option Prior) (seen later: Views)
    (sameFound: found = other)
    (sameSeen: seen = later)
    (kept: StaysCalm found seen):
    StaysCalm other later :=
  rewrite <- sameFound, <- sameSeen then kept

theorem joinedCast ∀ (found other: Option Prior) (laid laidTo printed printedTo: Views)
    (sameFound: found = other)
    (sameLaid: laid = laidTo)
    (samePrinted: printed = printedTo)
    (joined: JoinedAt found laid printed):
    JoinedAt other laidTo printedTo :=
  rewrite <- sameFound, <- sameLaid, <- samePrinted then joined

theorem commentStarted ∀ (at: Nat) (wrong: Some at = (None: Option Nat)): Void := cases

--| A trailing comment and the closers tucked before it, read in the laid
--| order onto one and in the printed order onto the other, after a token
--| a comment may follow: homed, the comment goes back over the closers
--| (`tuckHome`) to that token, where the calm laid trace keeps it.
theorem tuckedFree ∀ (word: Text) (closers: List Event) (laidViews printedViews: List TokenView)
    (laidPending printedPending: List Trivia) (top: TokenView) (rest: List TokenView)
    (isComment: IsComment word)
    (closing: List.All Closer closers)
    (home: homeViews printedViews = laidViews)
    (pending: printedPending = laidPending)
    (suited: Suited (Worded True) { views = laidViews, pending = laidPending })
    (stable: StableViews laidViews)
    (same: printedViews = [top, ..rest])
    (topFree: top.trailing = None):
    JoinedAt
      (calmFrom (Some (Worded True)) [{ word, start = None }, ..closers])
      (viewsFrom { views = laidViews, pending = laidPending } [{ word, start = None }, ..closers])
      (viewsFrom { views = printedViews, pending = printedPending } (closers ++ [{ word, start = None }])) :=
  let held: Comment := { text = word }
  let comment: Event := { word, start = None }
  let laid: Views := { views = laidViews, pending = laidPending }
  let printed: Views := { views = printedViews, pending = printedPending }
  let moved: TokenView := { top | trailing = Some held }
  let homed: homeViews [top, ..rest] = laidViews := rewrite same at home then home
  let sameLaid: laidViews = [top, ..homeViews rest] := Eq.trans homed.flipped (freshHome top (homeViews rest) topFree)
  let noneLaid: laidPending = [] := suited.left
  let nonePrinted: printedPending = [] := Eq.trans pending noneLaid
  match tuckViewsFront closers closing with
    | (front, allFront, frontSame) =>
      let trailed: viewEvent laid comment = { views = [moved, ..homeViews rest], pending = [] } :=
        Eq.trans (trailingEvent laid word isComment) (rewrite sameLaid, noneLaid)
      let once: StaysCalm (Some Trailed) { views = [moved, ..homeViews rest], pending = [] } :=
        staysCast _
          (Some Trailed) _ _
          (trailingCalm (Worded True) word isComment)
          trailed
          (calmStepViews (Worded True) comment laid suited stable)
      let laidAfter: viewsFrom laid [comment, ..closers]
        = { views = front ++ [moved, ..homeViews rest], pending = [] } :=
        calc viewsFrom (viewEvent laid comment) closers
          _ = viewsFrom { views = [moved, ..homeViews rest], pending = [] } closers :=
            Eq.cong ((seen: Views) => viewsFrom seen closers) trailed
          _ = { views = tuckViews closers [moved, ..homeViews rest], pending = [] } :=
            closersSeen closers [moved, ..homeViews rest] closing
          _ = { views = front ++ [moved, ..homeViews rest], pending = [] } :=
            Eq.cong ((views: List TokenView) => ({ views, pending = [] }: Views)) (frontSame [moved, ..homeViews rest])
      let before: viewsFrom printed closers = { views = tuckViews closers [top, ..rest], pending = [] } :=
        rewrite same, nonePrinted then closersSeen closers [top, ..rest] closing
      let printedAfter: viewsFrom printed (closers ++ [comment])
        = { views = viewTrailing (front ++ [top, ..rest]) held, pending = [] } :=
        calc viewsFrom printed (closers ++ [comment])
          _ = viewEvent (viewsFrom printed closers) comment := viewsSnoc printed closers comment
          _ = viewEvent { views = tuckViews closers [top, ..rest], pending = [] } comment :=
            Eq.cong ((seen: Views) => viewEvent seen comment) before
          _ = { views = viewTrailing (tuckViews closers [top, ..rest]) held, pending = [] } :=
            trailingEvent { views = tuckViews closers [top, ..rest], pending = [] } word isComment
          _ = { views = viewTrailing (front ++ [top, ..rest]) held, pending = [] } :=
            Eq.cong
              ((views: List TokenView) => ({ views = viewTrailing views held, pending = [] }: Views))
              (frontSame [top, ..rest])
      let back: homeViews (viewTrailing (front ++ [top, ..rest]) held) = front ++ [moved, ..homeViews rest] :=
        tuckHome front held top rest (homeViews rest) allFront topFree byComputing once.right.left
      joinedOf
        (calmFrom (Some (Worded True)) [comment, ..closers])
        (viewsFrom laid [comment, ..closers])
        (viewsFrom printed (closers ++ [comment]))
        (calmViews [comment, ..closers] (Some (Worded True)) laid ((suited, stable)))
        (calc homeViews (viewsFrom printed (closers ++ [comment])).views
          _ = homeViews (viewTrailing (front ++ [top, ..rest]) held) :=
            Eq.cong ((seen: Views) => homeViews seen.views) printedAfter
          _ = front ++ [moved, ..homeViews rest] := back
          _ = (viewsFrom laid [comment, ..closers]).views := (Eq.cong ((seen: Views) => seen.views) laidAfter).flipped)
        (Eq.trans
          (Eq.cong ((seen: Views) => seen.pending) printedAfter)
          (Eq.cong ((seen: Views) => seen.pending) laidAfter).flipped)

--| A trailing comment's stretch keeps the views joined. Where no comment
--| may follow, the laid trace isn't calm, and nothing is claimed.
theorem tuckedHome ∀ (comment: Event) (closers: List Event) (found: Option Prior) (laid printed: Views)
    (fits: Stretch.Fits (Tucked comment closers))
    (joined: JoinedAt found laid printed)
    (fresh: FreshAt found printed):
    JoinedAt
      (calmFrom found [comment, ..closers])
      (viewsFrom laid [comment, ..closers])
      (viewsFrom printed (closers ++ [comment])) :=
  match comment, fits with
    | { word, start = Some at }, (unstarted, _, _) => (commentStarted at unstarted).impossible
    | { word, start = None }, (_, isComment, closing) =>
      let stops: ∀ (prior: Prior) => afterTrailing prior = None
        → calmFrom (Some prior) [{ word, start = None }, ..closers] = None :=
        prior none =>
          calc calmFrom (stepOn (Some prior) { word, start = None }) closers
            _ = calmFrom (afterTrailing prior) closers :=
              Eq.cong ((next: Option Prior) => calmFrom next closers) (trailingCalm prior word isComment)
            _ = calmFrom None closers := Eq.cong ((next: Option Prior) => calmFrom next closers) none
            _ = None := calmFromNone closers
      match found, joined, fresh with
        | None, _, _ => rewrite calmFromNone closers
        | Some Blanked, _, _ => rewrite stops Blanked byComputing
        | Some Noted, _, _ => rewrite stops Noted byComputing
        | Some Trailed, _, _ => rewrite stops Trailed byComputing
        | Some (Worded False), _, _ => rewrite stops (Worded False) byComputing
        | Some (Worded True), (home, pending, suited, stable), (top, rest, same, topFree) =>
          match laid, printed, home, pending, suited, stable, same with
            | { views = laidViews, pending = laidPending }, {
                views = printedViews,
                pending = printedPending
              }, home, pending, suited, stable, same =>
              tuckedFree word closers laidViews printedViews laidPending printedPending top rest isComment closing home
                  pending suited stable same topFree

--| Whether the first stretch finds the printed views fresh, or starts a
--| line.
def FirstFresh (found: Option Prior) (printed: Views) (stretches: List Stretch): Prop := match stretches with
  | [] => True
  | [first, .._] => FreshAt found printed ∨ first.Starts

--| The stretches of a calm laid trace, read in the laid order onto one
--| and in the printed order onto the other, keep the views joined: by
--| induction on the stretches, an event by `keptHome`, a comment's
--| stretch by `tuckedHome`; after a comment's stretch the next starts a
--| line (`LineEnded`).
theorem stretchesHome ∀ (stretches: List Stretch) (found: Option Prior) (laid printed: Views)
    (fits: List.All Stretch.Fits stretches)
    (spaced: LineEnded stretches)
    (joined: JoinedAt found laid printed)
    (fresh: FirstFresh found printed stretches):
    JoinedAt
      (calmFrom found (laidOf stretches))
      (viewsFrom laid (laidOf stretches))
      (viewsFrom printed (printedOf stretches)) :=
  match stretches, fits, spaced, fresh with
    | [], _, _, _ => joined
    | [Kept event, ..rest], (_, others), spaced, fresh =>
      let next := keptHome event found laid printed joined fresh
      stretchesHome rest
        (stepOn found event)
        (viewEvent laid event)
        (viewEvent printed event)
        others
        (match rest, spaced with
          | [], _ => byComputing
          | [second, ..more], spaced => spaced)
        next.left
        (match rest with
          | [] => byComputing
          | [second, ..more] => Inl next.right)
    | [Tucked comment closers, ..rest], (first, others), spaced, fresh =>
      let free: FreshAt found printed := match fresh with
        | Inl found => found
        | Inr never => (Bool.falseNotTrue never).impossible
      let next := tuckedHome comment closers found laid printed first joined free
      joinedCast _ _ _ _ _ _
        (calmFromAppend [comment, ..closers] (laidOf rest) found).flipped
        (viewsAppend laid [comment, ..closers] (laidOf rest)).flipped
        (viewsAppend printed (closers ++ [comment]) (printedOf rest)).flipped
        (stretchesHome rest
          (calmFrom found [comment, ..closers])
          (viewsFrom laid [comment, ..closers])
          (viewsFrom printed (closers ++ [comment]))
          others
          (match rest, spaced with
            | [], _ => byComputing
            | [second, ..more], (_, later) => later)
          next
          (match rest, spaced with
            | [], _ => byComputing
            | [second, ..more], (starts, _) => Inr starts))

--| Rule N's first half takes the views of what was printed to the views
--| of what the rules laid, which it then leaves as they are: the laid
--| trace is calm, and the printed one is it with each trailing comment
--| after the closers on its line.
theorem tucksHome ∀ (laid printed: List Event) (after: Prior)
    (tucks: Tucks laid printed)
    (calms: calm Blanked laid = Some after):
    homeViews (viewsOf printed).views = (viewsOf laid).views
      ∧ (viewsOf printed).pending = (viewsOf laid).pending
      ∧ StableViews (viewsOf laid).views :=
  match tucks with
    | (stretches, fits, spaced, sameLaid, samePrinted) =>
      let start: Views := { views = [], pending = [] }
      let joined :=
        stretchesHome stretches
          (Some Blanked)
          start
          start
          fits
          spaced
          ((byComputing, byComputing, byComputing, byComputing))
          (match stretches with
            | [] => byComputing
            | [first, ..rest] => Inl byComputing)
      let calmed: calmFrom (Some Blanked) (laidOf stretches) = Some after := rewrite <- sameLaid then calms
      let known: JoinedAt (Some after) (viewsOf (laidOf stretches)) (viewsOf (printedOf stretches)) :=
        joinedCast _ _ _ _ _ _ calmed byComputing byComputing joined
      rewrite sameLaid, samePrinted then (known.left, known.right.left, known.right.right.right)
