--| Rule N has nothing to move in a tree the parser gave (toy-plus-plus.md
--| §3.1): the tokens the printed text lexes to are tokens rule N leaves
--| as they are, so the parser reads the printed text through rule N as
--| it would without it.
--|
--| Three steps. `StableViews` says of token views what rule N asks
--| (`Toy.Syntax.Proofs.Stable`, `BareComma`): a comma holds nothing, and
--| a closing bracket's trailing comment has own-line comments above the
--| bracket or a trailing comment before it (`stableTokens`). `calm` reads
--| a trace event by event, remembering only what the last event was, and
--| a calm trace's views are stable (`calmStable`). And the events of a
--| file of the parser's shape are calm (`fileCalm`): the tree has no
--| comments for a comma, and every closing bracket's are
--| `settledCloser`.

namespace Toy.Fmt.Proofs
import Toy.Doc (..)
import Toy.Doc.Proofs (..)
import Toy.Syntax (..)
import Toy.Syntax.Proofs (..)
import Toy.Fmt (..)
import Std (Bool, DecEq, Eq, List, Nat, Option, Parse, Text, Void)

-- Views rule N leaves as they are.

--| Whether a trailing comment on `current` stays there: it has own-line
--| comments above it, or the token before it has a trailing comment; so
--| does the first token's.
def blockedBy (current: TokenView) (earlier: List TokenView): Bool := match earlier with
  | [] => True
  | [previous, .._] => hasOwnLine current.above || previous.trailing.isSome

--| Rule N moves nothing of `current`, after `earlier` (newest first).
def SteadyView (current: TokenView) (earlier: List TokenView): Prop :=
  (current.kind.isComma = True → current.above = [] ∧ current.trailing = None)
    ∧ (current.trailing.isSome = True
      → (current.kind.isCloser || current.kind.isComma) = True
      → blockedBy current earlier = True)

def StableViews: List TokenView → Prop
  | [] => True
  | [newest, ..earlier] => SteadyView newest earlier ∧ StableViews earlier

theorem boolNotBoth ∀ (value: Bool) (yes: value = True) (no: value = False): Void :=
  Bool.trueNotFalse (Eq.trans yes.flipped no)

theorem steadyToken ∀ (token: Parse.Located Token) (earlier: List (Parse.Located Token))
    (steady: SteadyView (viewOf token) (earlier.map viewOf)):
    Steady token earlier ∧ BareComma token :=
  match token, steady with
    | { value = { kind, startsLine, column, above, trailing }, offset, length }, (bare, blocked) =>
      match trailing, bare, blocked with
        | None, bare, _ => (byComputing, (isComma => (((bare isComma).left), byComputing)))
        | Some comment, bare, blocked => (
          (match closes: kind.isCloser || kind.isComma with
            | False => byComputing
            | True =>
              match earlier, blocked with
                | [], _ => byComputing
                | [previous, ..rest], blocked =>
                  let stays := blocked byComputing byComputing
                  match own: hasOwnLine above with
                    | True => rewrite closes
                    | False =>
                      match prior: previous.value.trailing with
                        | Some _ => rewrite closes),
          (isComma =>
            match (bare isComma).right with
              | ())
        )

--| Tokens whose views rule N would leave are tokens it leaves.
theorem stableTokens ∀ (tokens: List (Parse.Located Token))
    (stable: StableViews (tokens.map viewOf)):
    Stable tokens ∧ List.All BareComma tokens :=
  match tokens, stable with
    | [], _ => (byComputing, ())
    | [token, ..earlier], (steady, others) =>
      let (stays, bare) := steadyToken token earlier steady
      let (rest, bares) := stableTokens earlier others
      (((stays, rest)), ((bare, bares)))

-- A trace read event by event.

--| What a trace's last event was, as far as rule N cares.
type Prior =
  --| Nothing yet, or a blank line.
  | Blanked
  --| An own-line comment.
  | Noted
  --| A token; `free` if a trailing comment may follow it and stay: it is
  --| no comma, and no closing bracket unless a comment came before it.
  | Worded (free: Bool)
  --| A trailing comment.
  | Trailed

def afterWord (prior: Prior) (kind: Kind): Option Prior :=
  if kind.isComma then
    match prior with
      | Worded _ => Some (Worded False)
      | Trailed => Some (Worded False)
      | _ => None
  else if kind.isCloser then
    match prior with
      | Noted => Some (Worded True)
      | Trailed => Some (Worded True)
      | _ => Some (Worded False)
  else Some (Worded True)

def afterTrailing: Prior → Option Prior
  | Worded True => Some Trailed
  | _ => None

--| The event after `prior`, read as `viewEvent` reads it; `None` where
--| rule N would have something to move: a comma after trivia, or a
--| trailing comment after a comma or a closing bracket that isn't
--| blocked.
def calmStep (prior: Prior) (event: Event): Option Prior :=
  if event.word == "\n" then Some Blanked
  else
    match lexemeOf event.word with
      | CommentLexeme =>
        match event.start with
          | Some _ => Some Noted
          | None => afterTrailing prior
      | lexeme => afterWord prior (lexemeKind lexeme event.word)

--| `calmStep` after what was read so far, if that was calm.
def stepOn (found: Option Prior) (event: Event): Option Prior := match found with
  | Some prior => calmStep prior event
  | None => None

def calmFrom (found: Option Prior) (events: List Event): Option Prior := match events with
  | [] => found
  | [event, ..rest] => calmFrom (stepOn found event) rest

--| What the trace's last event was, read after `prior`, if rule N has
--| nothing to move in it.
def calm (prior: Prior) (events: List Event): Option Prior := calmFrom (Some prior) events

--| What `prior` says of the views seen so far.
def Suited (prior: Prior) (seen: Views): Prop := match prior with
  | Blanked => True
  | Noted => ∃ (comment: Comment) => ∃ (rest: List Trivia) => seen.pending = [OwnLine comment, ..rest]
  | Worded free =>
    seen.pending = []
      ∧ (∃ (top: TokenView) => ∃ (rest: List TokenView) => seen.views = [top, ..rest]
        ∧ top.trailing = None
        ∧ (free = True
          → top.kind.isComma = False ∧ ((top.kind.isCloser || top.kind.isComma) = True → blockedBy top rest = True)))
  | Trailed =>
    seen.pending = []
      ∧ (∃ (top: TokenView) => ∃ (rest: List TokenView) => seen.views = [top, ..rest] ∧ top.trailing.isSome = True)

--| After an event that `calmStep` read as `found`, the views `seen`
--| suit it and are stable; nothing is said where `calmStep` stopped.
def StaysCalm (found: Option Prior) (seen: Views): Prop := match found with
  | Some next => Suited next seen ∧ StableViews seen.views
  | None => True

theorem ownLineLast ∀ (front: List Trivia) (comment: Comment): hasOwnLine (front ++ [OwnLine comment]) = True :=
  match front with
    | [] => byComputing
    | [OwnLine first, ..rest] => byComputing
    | [BlankLine, ..rest] => ownLineLast rest comment

theorem ownLineReversed ∀ (comment: Comment) (rest: List Trivia): hasOwnLine [OwnLine comment, ..rest].reverse = True :=
  rewrite List.reverseCons (OwnLine comment) rest then ownLineLast rest.reverse comment

--| Whether a trailing comment stays on a token doesn't depend on which
--| comment it is.
theorem blockedTrailing ∀ (top: TokenView) (rest: List TokenView) (trailing: Option Comment):
    blockedBy { top | trailing } rest = blockedBy top rest :=
  match rest with
    | [] => byComputing
    | [previous, ..others] => byComputing

--| A token just read, which is no comma, is steady: it has no trailing
--| comment yet.
theorem freshSteady ∀ (kind: Kind) (start: Option Nat) (above: List Trivia) (earlier: List TokenView)
    (notComma: kind.isComma = False):
    SteadyView { kind, start, above, trailing = None } earlier :=
  ((isComma => (boolNotBoth kind.isComma isComma notComma).impossible), (wrong => (Bool.falseNotTrue wrong).impossible))

--| A token read after `prior` keeps the views stable, and the views suit
--| what `afterWord` says: by cases on the token's kind and on `prior`.
theorem afterWordViews ∀ (prior: Prior) (kind: Kind) (start: Option Nat) (seen: Views)
    (suited: Suited prior seen)
    (stable: StableViews seen.views):
    StaysCalm (afterWord prior kind) (codeView seen kind start) :=
  match seen, suited, stable with
    | { views, pending }, suited, stable =>
      let view: TokenView := { kind, start, above = pending.reverse, trailing = None }
      match comma: kind.isComma with
        | True =>
          let bare: pending = [] → SteadyView view views := none =>
            ((isComma => ((rewrite none), byComputing)), (wrong => (Bool.falseNotTrue wrong).impossible))
          match prior, suited with
            | Blanked, _ => byComputing
            | Noted, _ => byComputing
            | Worded free, (none, _) => (
              (byComputing, view, views, byComputing, byComputing, (wrong => (Bool.falseNotTrue wrong).impossible)),
              (bare none),
              stable
            )
            | Trailed, (none, _) => (
              (byComputing, view, views, byComputing, byComputing, (wrong => (Bool.falseNotTrue wrong).impossible)),
              (bare none),
              stable
            )
        | False =>
          let steady: SteadyView view views := freshSteady kind start pending.reverse views comma
          match closer: kind.isCloser with
            | False => (
              (
                byComputing,
                view,
                views,
                byComputing,
                byComputing,
                (free =>
                  (comma, (closes => (Bool.falseNotTrue (rewrite closer, comma at closes then closes)).impossible)))
              ),
              steady,
              stable
            )
            | True =>
              match prior, suited with
                | Blanked, _ => (
                  (byComputing, view, views, byComputing, byComputing, (wrong => (Bool.falseNotTrue wrong).impossible)),
                  steady,
                  stable
                )
                | Worded free, _ => (
                  (byComputing, view, views, byComputing, byComputing, (wrong => (Bool.falseNotTrue wrong).impossible)),
                  steady,
                  stable
                )
                | Noted, (comment, rest, waiting) => (
                  (
                    byComputing,
                    view,
                    views,
                    byComputing,
                    byComputing,
                    (free =>
                      (
                        comma,
                        (closes =>
                          match views with
                            | [] => byComputing
                            | [previous, ..others] => rewrite waiting, ownLineReversed comment rest)
                      ))
                  ),
                  steady,
                  stable
                )
                | Trailed, (none, top, rest, same, has) => (
                  (
                    byComputing,
                    view,
                    views,
                    byComputing,
                    byComputing,
                    (free =>
                      (
                        comma,
                        (closes =>
                          rewrite same, has then
                            match own: hasOwnLine pending.reverse with
                              | True => byComputing
                              | False => byComputing)
                      ))
                  ),
                  steady,
                  stable
                )

--| An event read after `prior` keeps the views stable, and the views
--| suit what `calmStep` says: `calmStep` follows `viewEvent` case by
--| case.
theorem calmStepViews ∀ (prior: Prior) (event: Event) (seen: Views)
    (suited: Suited prior seen)
    (stable: StableViews seen.views):
    StaysCalm (calmStep prior event) (viewEvent seen event) :=
  match event with
    | { word, start } =>
      match isBreak: word == "\n" with
        | True => (byComputing, stable)
        | False =>
          match lexeme: lexemeOf word with
            | CommentLexeme =>
              match start with
                | Some column => ((({ text = word }), seen.pending, byComputing), stable)
                | None =>
                  match seen, prior, suited, stable with
                    | { views, pending }, Blanked, _, _ => byComputing
                    | { views, pending }, Noted, _, _ => byComputing
                    | { views, pending }, Trailed, _, _ => byComputing
                    | { views, pending }, Worded False, _, _ => byComputing
                    | { views, pending }, Worded True, (none, top, rest, same, bare, free), stable =>
                      let facts := free byComputing
                      let held: SteadyView top rest ∧ StableViews rest := rewrite same at stable then stable
                      rewrite same then
                        (
                          (none, ({ top | trailing = Some { text = word } }), rest, byComputing, byComputing),
                          (
                            (isComma => (boolNotBoth top.kind.isComma isComma facts.left).impossible),
                            (has closes =>
                              rewrite blockedTrailing top rest (Some { text = word }) then facts.right closes)
                          ),
                          held.right
                        )
            | Spaces => afterWordViews prior (lexemeKind Spaces word) start seen suited stable
            | LineBreak => afterWordViews prior (lexemeKind LineBreak word) start seen suited stable
            | WordLexeme => afterWordViews prior (lexemeKind WordLexeme word) start seen suited stable
            | DigitsLexeme => afterWordViews prior (lexemeKind DigitsLexeme word) start seen suited stable
            | StringLexeme => afterWordViews prior (lexemeKind StringLexeme word) start seen suited stable
            | SignLexeme => afterWordViews prior (lexemeKind SignLexeme word) start seen suited stable
            | SymbolsLexeme => afterWordViews prior (lexemeKind SymbolsLexeme word) start seen suited stable
            | StrayLexeme => afterWordViews prior (lexemeKind StrayLexeme word) start seen suited stable

theorem stepKept ∀ (found: Option Prior) (event: Event) (seen: Views)
    (kept: StaysCalm found seen):
    StaysCalm (stepOn found event) (viewEvent seen event) :=
  match found, kept with
    | None, _ => byComputing
    | Some prior, (suited, stable) => calmStepViews prior event seen suited stable

theorem calmViews ∀ (events: List Event) (found: Option Prior) (seen: Views)
    (kept: StaysCalm found seen):
    StaysCalm (calmFrom found events) (viewsFrom seen events) :=
  match events with
    | [] => kept
    | [event, ..rest] => calmViews rest (stepOn found event) (viewEvent seen event) (stepKept found event seen kept)

--| The views of a calm trace are views rule N leaves as they are.
theorem calmStable ∀ (events: List Event) (after: Prior)
    (calms: calm Blanked events = Some after):
    StableViews (viewsOf events).views :=
  let all: StaysCalm (calm Blanked events) (viewsOf events) :=
    calmViews events (Some Blanked) { views = [], pending = [] } ((byComputing, byComputing))
  (rewrite calms at all then all).right

-- A token's events are calm.

theorem calmFromAppend ∀ (front back: List Event) (found: Option Prior):
    calmFrom found (front ++ back) = calmFrom (calmFrom found front) back :=
  match front with
    | [] => byComputing
    | [event, ..rest] => calmFromAppend rest back (stepOn found event)

theorem ownLineCalm ∀ (prior: Prior) (text: Text) (column: Nat)
    (comment: IsComment text):
    calmStep prior { word = text, start = Some column } = Some Noted :=
  match isBreak: text == "\n" with
    | True => Void.impossible (commentNoBreak text comment isBreak)
    | False => rewrite commentLexeme text comment

theorem trailingCalm ∀ (prior: Prior) (text: Text)
    (comment: IsComment text):
    calmStep prior { word = text, start = None } = afterTrailing prior :=
  match isBreak: text == "\n" with
    | True => Void.impossible (commentNoBreak text comment isBreak)
    | False => rewrite commentLexeme text comment

--| The kind of the newest token seen.
def kindSeen (seen: Views): Option Kind := match seen.views with
  | [view, .._] => Some view.kind
  | [] => None

theorem someKind ∀ (first second: Kind) (same: Some first = Some second): first = second := cases

theorem noKind ∀ (kind: Kind) (wrong: None = Some kind): Void := cases

--| A word that `viewEvent` reads as a token of `kind` is one `calmStep`
--| reads so: the two take a word's kind the same way.
theorem wordCalm ∀ (prior: Prior) (text: Text) (kind: Kind) (start: Option Nat)
    (reads: ∀ (seen: Views) (start: Option Nat) => viewEvent seen { word = text, start } = codeView seen kind start):
    calmStep prior { word = text, start } = afterWord prior kind :=
  let read: kindSeen (viewEvent { views = [], pending = [] } { word = text, start }) = Some kind :=
    Eq.cong kindSeen (reads { views = [], pending = [] } start)
  match isBreak: text == "\n" with
    | False =>
      match lexeme: lexemeOf text with
        | CommentLexeme =>
          match start, read with
            | Some column, read => (noKind kind read).impossible
            | None, read => (noKind kind read).impossible
        | Spaces => Eq.cong ((found: Kind) => afterWord prior found) (someKind _ _ read)
        | LineBreak => Eq.cong ((found: Kind) => afterWord prior found) (someKind _ _ read)
        | WordLexeme => Eq.cong ((found: Kind) => afterWord prior found) (someKind _ _ read)
        | DigitsLexeme => Eq.cong ((found: Kind) => afterWord prior found) (someKind _ _ read)
        | StringLexeme => Eq.cong ((found: Kind) => afterWord prior found) (someKind _ _ read)
        | SignLexeme => Eq.cong ((found: Kind) => afterWord prior found) (someKind _ _ read)
        | SymbolsLexeme => Eq.cong ((found: Kind) => afterWord prior found) (someKind _ _ read)
        | StrayLexeme => Eq.cong ((found: Kind) => afterWord prior found) (someKind _ _ read)

--| What the last event was once the comments `above` a token are read.
def afterAbove (prior: Prior) (above: List Comment): Prior := match above with
  | [] => prior
  | _ => Noted

theorem aboveCalm ∀ (above: List Comment) (column: Nat) (prior: Prior)
    (fine: FineAbove above):
    calm prior (aboveEvents column above) = Some (afterAbove prior above) :=
  match above, fine with
    | [], _ => byComputing
    | [comment, ..rest], (first, others) =>
      calc calm prior (aboveEvents column [comment, ..rest])
        _ = calm Noted (aboveEvents column rest) :=
          Eq.cong
            ((found: Option Prior) => calmFrom found (aboveEvents column rest))
            (ownLineCalm prior comment.text column first)
        _ = Some (afterAbove Noted rest) := aboveCalm rest column Noted others
        _ = Some Noted := match rest with
          | [] => byComputing
          | [_, .._] => byComputing

def afterComment (worded: Prior) (after: Option Comment): Option Prior := match after with
  | None => Some worded
  | Some _ => afterTrailing worded

def afterToken (found: Option Prior) (after: Option Comment): Option Prior := match found with
  | Some worded => afterComment worded after
  | None => None

--| What the last event is after a token of `kind` with `comments`.
def wholeToken (prior: Prior) (kind: Kind) (comments: Comments): Option Prior :=
  afterToken (afterWord (afterAbove prior comments.above) kind) comments.after

theorem trailCalm ∀ (found: Option Prior) (after: Option Comment)
    (fine: FineAfter after):
    calmFrom found (afterEvents after) = afterToken found after :=
  match after, fine, found with
    | None, _, None => byComputing
    | None, _, Some worded => byComputing
    | Some comment, fine, None => byComputing
    | Some comment, fine, Some worded => trailingCalm worded comment.text fine

--| A token's events, read: its comments above, the token, its trailing
--| comment.
theorem tokenCalm ∀ (comments: Comments) (text: Text) (kind: Kind) (column: Nat) (start: Option Nat) (prior: Prior)
    (fine: Fine comments)
    (reads: ∀ (seen: Views) (start: Option Nat) => viewEvent seen { word = text, start } = codeView seen kind start):
    calm prior (aboveEvents column comments.above ++ [{ word = text, start }, ..afterEvents comments.after])
      = wholeToken prior kind comments :=
  match comments, fine with
    | { above, after }, (fineAbove, fineAfter) =>
      let word: Event := { word = text, start }
      let from := afterAbove prior above
      calc calm prior (aboveEvents column above ++ [word, ..afterEvents after])
        _ = calmFrom (calm prior (aboveEvents column above)) [word, ..afterEvents after] :=
          calmFromAppend (aboveEvents column above) [word, ..afterEvents after] (Some prior)
        _ = calmFrom (Some from) [word, ..afterEvents after] :=
          Eq.cong
            ((found: Option Prior) => calmFrom found [word, ..afterEvents after])
            (aboveCalm above column prior fineAbove)
        _ = calmFrom (afterWord from kind) (afterEvents after) :=
          Eq.cong ((found: Option Prior) => calmFrom found (afterEvents after)) (wordCalm from text kind start reads)
        _ = afterToken (afterWord from kind) after := trailCalm (afterWord from kind) after fineAfter

-- Constructs whose events are calm.

def anyPrior (prior: Prior): Prop := True

--| What the last event of a construct is: a trailing comment if its last
--| token has one, else that token.
def EndsWith (ends: Bool) (after: Prior): Prop := match ends with
  | True => after = Trailed
  | False => ∃ (free: Bool) => after = Worded free

--| Events `spec` holds of are calm after any event `pre` holds of, and
--| end in one `post` holds of.
def Calms (spec: List Event → Prop) (pre post: Prior → Prop): Prop :=
  ∀ (events: List Event) (prior: Prior) => spec events
    → pre prior
    → ∃ (after: Prior) => calm prior events = Some after ∧ post after

theorem calmsThen ∀ [first second: List Event → Prop] [pre mid post: Prior → Prop]
    (one: Calms first pre mid)
    (other: Calms second mid post):
    Calms (Then first second) pre post :=
  events prior laid holds =>
    match laid with
      | (front, back, split, isFirst, isSecond) =>
        match one front prior isFirst holds with
          | (middle, calmed, reached) =>
            match other back middle isSecond reached with
              | (after, calmedBack, done) => (
                after,
                (rewrite split then
                  calc calm prior (front ++ back)
                    _ = calmFrom (calm prior front) back := calmFromAppend front back (Some prior)
                    _ = calm middle back := Eq.cong ((found: Option Prior) => calmFrom found back) calmed
                    _ = Some after := calmedBack),
                done
              )

theorem calmsLoose ∀ [spec: List Event → Prop] [pre post: Prior → Prop]
    (calms: Calms spec pre post):
    Calms spec pre anyPrior :=
  events prior laid holds =>
    match calms events prior laid holds with | (after, calmed, _) => (after, calmed, byComputing)

theorem calmsAny ∀ [spec: List Event → Prop] [post: Prior → Prop] (pre: Prior → Prop)
    (calms: Calms spec anyPrior post):
    Calms spec pre post :=
  events prior laid holds => calms events prior laid byComputing

theorem calmsDone ∀ (pre: Prior → Prop): Calms Done pre pre := events prior none holds => (prior, (rewrite none), holds)

theorem plainAfter ∀ (prior: Prior) (kind: Kind) (comments: Comments)
    (notComma: kind.isComma = False)
    (notCloser: kind.isCloser = False):
    ∃ (after: Prior) => wholeToken prior kind comments = Some after ∧ EndsWith comments.after.isSome after :=
  match comments with
    | { above, after = None } => ((Worded True), (rewrite notComma, notCloser), ((True, byComputing)))
    | { above, after = Some comment } => (Trailed, (rewrite notComma, notCloser), byComputing)

--| A token that is neither a comma nor a closing bracket: after any
--| event, and its trailing comment stays.
theorem tokenCalms ∀ (allowed: Option Nat → Prop) (comments: Comments) (text: Text) (kind: Kind)
    (fine: Fine comments)
    (reads: ∀ (seen: Views) (start: Option Nat) => viewEvent seen { word = text, start } = codeView seen kind start)
    (notComma: kind.isComma = False)
    (notCloser: kind.isCloser = False):
    Calms (TokenAt allowed comments text) anyPrior (EndsWith comments.after.isSome) :=
  events prior laid holds =>
    match laid, plainAfter prior kind comments notComma notCloser with
      | (column, start, _, split), (after, same, ends) =>
        (after, (rewrite split then Eq.trans (tokenCalm comments text kind column start prior fine reads) same), ends)

theorem signCalms ∀ (allowed: Option Nat → Prop) (comments: Comments) (mark: Punctuation)
    (fine: Fine comments)
    (notComma: (Sign mark).isComma = False)
    (notCloser: (Sign mark).isCloser = False):
    Calms (TokenAt allowed comments mark.spelling) anyPrior (EndsWith comments.after.isSome) :=
  tokenCalms allowed comments mark.spelling
    (Sign mark)
    fine
    (seen start => signEvent seen mark start)
    notComma
    notCloser

theorem keywordCalms ∀ (allowed: Option Nat → Prop) (comments: Comments) (keyword: Keyword)
    (fine: Fine comments):
    Calms (TokenAt allowed comments keyword.spelling) anyPrior (EndsWith comments.after.isSome) :=
  tokenCalms allowed comments keyword.spelling
    (Reserved keyword)
    fine
    (seen start => keywordEvent seen keyword start)
    byComputing
    byComputing

theorem nameCalms ∀ (allowed: Option Nat → Prop) (comments: Comments) (name: Text)
    (isName: IsName name)
    (fine: Fine comments):
    Calms (TokenAt allowed comments name) anyPrior (EndsWith comments.after.isSome) :=
  tokenCalms allowed comments name
    (Name name)
    fine
    (seen start => nameEvent seen name start isName)
    byComputing
    byComputing

theorem closerWord ∀ (from: Prior) (kind: Kind)
    (closer: kind.isCloser = True)
    (notComma: kind.isComma = False):
    ∃ (free: Bool) => afterWord from kind = Some (Worded free) :=
  match from with
    | Blanked => (False, (rewrite notComma, closer))
    | Noted => (True, (rewrite notComma, closer))
    | Worded free => (False, (rewrite notComma, closer))
    | Trailed => (True, (rewrite notComma, closer))

--| A closing bracket whose comments are `settledCloser`: its trailing
--| comment, if it has one, comes after own-line comments above the
--| bracket or after the trailing comment before it, so it stays.
theorem closerAfter ∀ (prior: Prior) (kind: Kind) (comments: Comments) (before: Bool)
    (closer: kind.isCloser = True)
    (notComma: kind.isComma = False)
    (settled: settledCloser before comments = True)
    (holds: EndsWith before prior):
    ∃ (after: Prior) => wholeToken prior kind comments = Some after ∧ EndsWith comments.after.isSome after :=
  match comments, settled with
    | { above, after = None }, _ =>
      match closerWord (afterAbove prior above) kind closer notComma with
        | (free, same) => ((Worded free), (rewrite same), ((free, byComputing)))
    | { above = [], after = Some comment }, settled =>
      match before, settled, holds with
        | True, _, trailed => (Trailed, (rewrite trailed, notComma, closer), byComputing)
        | False, never, _ => (Bool.falseNotTrue never).impossible
    | { above = [first, ..rest], after = Some comment }, _ => (Trailed, (rewrite notComma, closer), byComputing)

theorem closerCalms ∀ (allowed: Option Nat → Prop) (comments: Comments) (mark: Punctuation) (before: Bool)
    (fine: Fine comments)
    (closer: (Sign mark).isCloser = True)
    (notComma: (Sign mark).isComma = False)
    (settled: settledCloser before comments = True):
    Calms (TokenAt allowed comments mark.spelling) (EndsWith before) (EndsWith comments.after.isSome) :=
  events prior laid holds =>
    match laid, closerAfter prior (Sign mark) comments before closer notComma settled holds with
      | (column, start, _, split), (after, same, ends) => (
        after,
        (rewrite split then
          Eq.trans
            (tokenCalm comments mark.spelling (Sign mark) column start prior fine (seen start =>
              signEvent seen mark start))
            same),
        ends
      )

--| A comma, which holds nothing, after a token or its trailing comment.
theorem commaCalms ∀ (before: Bool): Calms (TokenAt anyStart Comments.none ",") (EndsWith before) anyPrior :=
  events prior laid holds =>
    match laid with
      | (column, start, _, split) =>
        let read := tokenCalm Comments.none "," (Sign Comma) column start prior fineNone (seen start =>
          signEvent seen Comma start)
        let worded: wholeToken prior (Sign Comma) Comments.none = Some (Worded False) := match before, holds with
          | True, trailed => rewrite trailed
          | False, (free, isWorded) => rewrite isWorded
        ((Worded False), (rewrite split then Eq.trans read worded), byComputing)

-- The tree.

def afterBlank (prior: Prior) (blankBefore: Bool): Prior := if blankBefore then Blanked else prior

theorem blankCalm ∀ (blankBefore: Bool) (later: List Event) (prior: Prior):
    calm prior (blankEvents blankBefore ++ later) = calm (afterBlank prior blankBefore) later :=
  match blankBefore with
    | True => byComputing
    | False => byComputing

--| An expression's events are calm after any event, and end as its last
--| token does: by induction on the expression, one `calmsThen` per part,
--| each closing bracket by `closerCalms` from its `settledCloser`.
theorem exprCalms ∀ (zone: Zone) (head: Option Nat → Prop) (expr: Expr)
    (shaped: Shaped expr)
    (lexical: Lexical expr):
    Calms (Events zone head expr) anyPrior (EndsWith expr.endsWithComment) :=
  match expr, shaped, lexical with
    | Var name comments, _, (isName, fine) => nameCalms head comments name isName fine
    | NumberLiteral digits comments, _, (isDigits, fine) =>
      tokenCalms head comments digits
        (Number digits)
        fine
        (seen start => digitsEvent seen digits start isDigits)
        byComputing
        byComputing
    | StringLiteral written comments, _, (isString, fine) =>
      tokenCalms head comments written
        (Str written)
        fine
        (seen start => stringEvent seen written start isString)
        byComputing
        byComputing
    | Bracketed open inner close, (shapedInner, settled), (fineOpen, lexInner, fineClose) =>
      calmsThen
        (calmsLoose (signCalms head open OpenParen fineOpen byComputing byComputing))
        (calmsThen
          (exprCalms zone.inside anyStart inner shapedInner lexInner)
          (closerCalms anyStart close CloseParen inner.endsWithComment fineClose byComputing byComputing settled))
    | ListLiteral open items close, (shapedItems, settled), (fineOpen, lexItems, fineClose) =>
      calmsThen
        (signCalms head open OpenSquare fineOpen byComputing byComputing)
        (calmsThen
          (itemsCalms zone.inside open items shapedItems lexItems)
          (closerCalms anyStart close CloseSquare
            (itemsEndWithComment open items)
            fineClose
            byComputing
            byComputing
            settled))
    | Call callee open arguments close, (postfix, shapedCallee, shapedArguments, settled), (lexCallee, fineOpen,
        lexArguments, fineClose) =>
      calmsThen
        (calmsLoose (exprCalms zone head callee shapedCallee lexCallee))
        (calmsThen
          (signCalms zone.allows open OpenParen fineOpen byComputing byComputing)
          (calmsThen
            (itemsCalms zone.inside open arguments shapedArguments lexArguments)
            (closerCalms anyStart close CloseParen
              (itemsEndWithComment open arguments)
              fineClose
              byComputing
              byComputing
              settled)))
    | Field target dot name nameComments, (postfix, shapedTarget), (lexTarget, fineDot, isName, fineName) =>
      calmsThen
        (calmsLoose (exprCalms zone head target shapedTarget lexTarget))
        (calmsThen
          (calmsLoose (signCalms zone.allows dot Dot fineDot byComputing byComputing))
          (nameCalms zone.allows nameComments name isName fineName))
    | Negate minus operand, (isOperand, shapedOperand), (fineMinus, lexOperand) =>
      calmsThen
        (calmsLoose
          (tokenCalms head minus "-"
            (Op Minus)
            fineMinus
            (seen start => operatorEvent seen Minus start)
            byComputing
            byComputing))
        (exprCalms zone zone.allows operand shapedOperand lexOperand)
    | Binary operator sign left right, (_, _, _, _, shapedLeft, shapedRight), (fineSign, lexLeft, lexRight) =>
      calmsThen
        (calmsLoose (exprCalms zone head left shapedLeft lexLeft))
        (calmsThen
          (calmsLoose
            (tokenCalms zone.allows sign operator.spelling
              (Op operator)
              fineSign
              (seen start => operatorEvent seen operator start)
              byComputing
              byComputing))
          (exprCalms zone zone.allows right shapedRight lexRight))
    | If ifComments condition thenComments whenTrue elseComments whenFalse, (shapedCondition, shapedTrue,
        shapedFalse), (fineIf, lexCondition, fineThen, lexTrue, fineElse, lexFalse) =>
      calmsThen
        (calmsLoose (keywordCalms head ifComments IfKeyword fineIf))
        (calmsThen
          (calmsLoose (exprCalms zone zone.allows condition shapedCondition lexCondition))
          (calmsThen
            (calmsLoose (keywordCalms zone.allows thenComments ThenKeyword fineThen))
            (calmsThen
              (calmsLoose (bodyCalms zone whenTrue shapedTrue lexTrue))
              (calmsThen
                (calmsLoose (keywordCalms zone.reaches elseComments ElseKeyword fineElse))
                (bodyCalms zone whenFalse shapedFalse lexFalse)))))

--| The items between brackets, after the opening one: they end as the
--| token before the closing bracket does.
theorem itemsCalms ∀ (zone: Zone) (open: Comments) (items: List Expr)
    (shaped: ShapedItems items)
    (lexical: LexicalItems items):
    Calms (ItemEvents zone items) (EndsWith open.after.isSome) (EndsWith (itemsEndWithComment open items)) :=
  match items, shaped, lexical with
    | [], _, _ => calmsDone (EndsWith open.after.isSome)
    | [first, ..rest], shaped, lexical =>
      calmsAny (EndsWith open.after.isSome) (itemsSome zone open first rest shaped lexical)

theorem itemsSome ∀ (zone: Zone) (open: Comments) (first: Expr) (rest: List Expr)
    (shaped: ShapedItems [first, ..rest])
    (lexical: LexicalItems [first, ..rest]):
    Calms (ItemEvents zone [first, ..rest]) anyPrior (EndsWith (itemsEndWithComment open [first, ..rest])) :=
  match rest, shaped, lexical with
    | [], (shapedFirst, _), (lexFirst, _) => exprCalms zone anyStart first shapedFirst lexFirst
    | [next, ..more], (shapedFirst, shapedRest), (lexFirst, lexRest) =>
      calmsThen
        (exprCalms zone anyStart first shapedFirst lexFirst)
        (calmsThen (commaCalms first.endsWithComment) (itemsSome zone open next more shapedRest lexRest))

theorem bodyCalms ∀ (zone: Zone) (body: Body)
    (shaped: ShapedBody body)
    (lexical: LexicalBody body):
    Calms (BodyEvents zone body) anyPrior (EndsWith body.endsWithComment) :=
  match body, shaped, lexical with
    | { statements }, (shapedLines, closed), (lexLines, _) => events prior laid holds =>
      match laid with
        | Inl inline => inlineCalms zone statements shapedLines lexLines events prior inline holds
        | Inr (column, under, lines) =>
          linesCalms column statements shapedLines lexLines closed events prior lines holds

theorem inlineCalms ∀ (zone: Zone) (statements: List (Spaced Statement))
    (shaped: ShapedLines statements)
    (lexical: LexicalLines statements):
    Calms (InlineEvents zone statements) anyPrior (EndsWith (statementsEndWithComment statements)) :=
  match statements, shaped, lexical with
    | [{ blankBefore, line = Bare value }], (shapedValue, _), (lexValue, _) =>
      exprCalms zone (inlineHead zone value) value shapedValue lexValue
    | [], _, _ => events prior never holds => (Bool.falseNotTrue never).impossible
    | [{ blankBefore, line = Let letComments name nameComments equals body }], _, _ => events prior never holds =>
      (Bool.falseNotTrue never).impossible
    | [{ blankBefore, line = StatementNote comment }], _, _ => events prior never holds =>
      (Bool.falseNotTrue never).impossible
    | [first, second, ..rest], _, _ => events prior never holds => (Bool.falseNotTrue never).impossible

theorem linesCalms ∀ (column: Nat) (statements: List (Spaced Statement))
    (shaped: ShapedLines statements)
    (lexical: LexicalLines statements)
    (closed: ClosedLines statements):
    Calms (LineEvents column statements) anyPrior (EndsWith (statementsEndWithComment statements)) :=
  match statements, shaped, lexical, closed with
    | [], _, _, never => (Bool.falseNotTrue never).impossible
    | [{ blankBefore, line }, ..rest], (shapedLine, shapedRest), (lexLine, lexRest), closed =>
      runCalms column blankBefore line rest shapedLine shapedRest lexLine lexRest closed

--| A block's lines from one of them on: every line is calm after any
--| event, and the last, which is a statement and no comment line
--| (`ClosedLines`), ends as the block does. By induction on the lines
--| after the first.
theorem runCalms ∀ (column: Nat) (blankBefore: Bool) (line: Statement) (rest: List (Spaced Statement))
    (shapedLine: ShapedStatement line)
    (shapedRest: ShapedLines rest)
    (lexLine: LexicalStatement line)
    (lexRest: LexicalLines rest)
    (closed: ClosedLines [{ blankBefore, line }, ..rest]):
    Calms
      (Then (StatementEvents column line) (LaterLines column rest))
      anyPrior
      (EndsWith (statementsEndWithComment [{ blankBefore, line }, ..rest])) :=
  match rest, shapedRest, lexRest, closed with
    | [], _, _, coded =>
      calmsThen (statementCalms column line shapedLine lexLine coded) (calmsDone (EndsWith line.endsWithComment))
    | [{ blankBefore = nextBlank, line = next }, ..more], (shapedNext, shapedMore), (lexNext, lexMore), closed =>
      calmsThen (statementAny column line shapedLine lexLine) (events prior laid holds =>
        match laid with
          | (later, split, run) =>
            match runCalms column nextBlank next more shapedNext shapedMore lexNext lexMore closed later
              (afterBlank prior nextBlank)
              run
              byComputing with
              | (after, calmed, ends) =>
                (after, (rewrite split then Eq.trans (blankCalm nextBlank later prior) calmed), ends))

theorem statementCalms ∀ (column: Nat) (line: Statement)
    (shaped: ShapedStatement line)
    (lexical: LexicalStatement line)
    (coded: Coded line):
    Calms (StatementEvents column line) anyPrior (EndsWith line.endsWithComment) :=
  match line, shaped, lexical, coded with
    | Let letComments name nameComments equals body, shapedBody, (fineLet, isName, fineName, fineEquals, lexBody), _ =>
      calmsThen
        (calmsLoose (keywordCalms (atColumn column) letComments LetKeyword fineLet))
        (calmsThen
          (calmsLoose (nameCalms (Deeper column).allows nameComments name isName fineName))
          (calmsThen
            (calmsLoose (signCalms (Deeper column).allows equals Defines fineEquals byComputing byComputing))
            (bodyCalms (Deeper column) body shapedBody lexBody)))
    | Bare value, shapedValue, lexValue, _ => exprCalms (Deeper column) (atColumn column) value shapedValue lexValue
    | StatementNote comment, _, _, never => (Bool.falseNotTrue never).impossible

--| Any line of a block, a comment line too.
theorem statementAny ∀ (column: Nat) (line: Statement)
    (shaped: ShapedStatement line)
    (lexical: LexicalStatement line):
    Calms (StatementEvents column line) anyPrior anyPrior :=
  match line, shaped, lexical with
    | StatementNote comment, _, isComment => events prior only holds =>
      (Noted, (rewrite only then ownLineCalm prior comment.text column isComment), byComputing)
    | Let letComments name nameComments equals body, shaped, lexical =>
      calmsLoose (statementCalms column (Let letComments name nameComments equals body) shaped lexical byComputing)
    | Bare value, shaped, lexical => calmsLoose (statementCalms column (Bare value) shaped lexical byComputing)

theorem typeCalms ∀ (annotation: TypeExpr)
    (shaped: ShapedType annotation)
    (lexical: LexicalType annotation):
    Calms (TypeEvents annotation) anyPrior (EndsWith annotation.endsWithComment) :=
  match annotation, shaped, lexical with
    | TypeName name comments, _, (isName, fine) => nameCalms anyStart comments name isName fine
    | TypeBracketed open inner close, (shapedInner, settled), (fineOpen, lexInner, fineClose) =>
      calmsThen
        (calmsLoose (signCalms anyStart open OpenParen fineOpen byComputing byComputing))
        (calmsThen
          (typeCalms inner shapedInner lexInner)
          (closerCalms anyStart close CloseParen inner.endsWithComment fineClose byComputing byComputing settled))

theorem namesCalms ∀ (names: List Named) (lexical: LexicalNames names): Calms (NamesEvents names) anyPrior anyPrior :=
  match names, lexical with
    | [], _ => calmsDone anyPrior
    | [{ name, comments }, ..rest], ((isName, fine), others) =>
      calmsThen (calmsLoose (nameCalms anyStart comments name isName fine)) (namesCalms rest others)

theorem groupCalms ∀ (group: ParameterGroup)
    (shaped: ShapedGroup group)
    (lexical: LexicalGroup group):
    Calms (GroupEvents group) anyPrior (EndsWith group.endsWithComment) :=
  match group, shaped, lexical with
    | Untyped { name, comments }, _, (isName, fine) => nameCalms anyStart comments name isName fine
    | Typed ({ head = { name, comments }, tail }) colon annotation, shapedType, (
        (isName, fine),
        lexNames,
        fineColon,
        lexType
      ) =>
      calmsThen
        (calmsLoose (nameCalms anyStart comments name isName fine))
        (calmsThen
          (namesCalms tail lexNames)
          (calmsThen
            (calmsLoose (signCalms anyStart colon Colon fineColon byComputing byComputing))
            (typeCalms annotation shapedType lexType)))

theorem parametersCalms ∀ (open: Comments) (parameters: List ParameterGroup)
    (shaped: ShapedGroups parameters)
    (lexical: LexicalParameters parameters):
    Calms (ParameterEvents parameters) (EndsWith open.after.isSome) (EndsWith (groupsEndWithComment open parameters)) :=
  match parameters, shaped, lexical with
    | [], _, _ => calmsDone (EndsWith open.after.isSome)
    | [first, ..rest], shaped, lexical =>
      calmsAny (EndsWith open.after.isSome) (parametersSome open first rest shaped lexical)

theorem parametersSome ∀ (open: Comments) (first: ParameterGroup) (rest: List ParameterGroup)
    (shaped: ShapedGroups [first, ..rest])
    (lexical: LexicalParameters [first, ..rest]):
    Calms (ParameterEvents [first, ..rest]) anyPrior (EndsWith (groupsEndWithComment open [first, ..rest])) :=
  match rest, shaped, lexical with
    | [], (shapedFirst, _), (lexFirst, _) => groupCalms first shapedFirst lexFirst
    | [next, ..more], (shapedFirst, shapedRest), (lexFirst, lexRest) =>
      calmsThen
        (groupCalms first shapedFirst lexFirst)
        (calmsThen (commaCalms first.endsWithComment) (parametersSome open next more shapedRest lexRest))

theorem takesCalms ∀ (zone: Zone) (takes: Option Comments)
    (fine: FineTakes takes):
    Calms (TakesEvents zone takes) anyPrior anyPrior :=
  match takes, fine with
    | None, _ => calmsDone anyPrior
    | Some comments, fine => calmsLoose (keywordCalms zone.allows comments TakesKeyword fine)

theorem declarationCalms ∀ (declaration: Declaration)
    (shaped: ShapedDeclaration declaration)
    (lexical: LexicalDeclaration declaration):
    Calms (DeclarationEvents declaration) anyPrior anyPrior :=
  match declaration, shaped, lexical with
    | Function fnComments name nameComments takes open parameters close equals body, (
        (shapedGroups, settled),
        shapedBody
      ), (fineFn, isName, fineName, fineTakes, fineOpen, lexParameters, fineClose, fineEquals, lexBody) =>
      calmsThen
        (calmsThen
          (calmsLoose (keywordCalms (atColumn 0) fnComments FnKeyword fineFn))
          (calmsThen
            (calmsLoose (nameCalms (Deeper 0).allows nameComments name isName fineName))
            (calmsThen
              (takesCalms (Deeper 0) takes fineTakes)
              (signCalms (Deeper 0).allows open OpenParen fineOpen byComputing byComputing))))
        (calmsThen
          (parametersCalms open parameters shapedGroups lexParameters)
          (calmsThen
            (calmsLoose
              (closerCalms anyStart close CloseParen
                (groupsEndWithComment open parameters)
                fineClose
                byComputing
                byComputing
                settled))
            (calmsThen
              (calmsLoose (signCalms (Deeper 0).allows equals Defines fineEquals byComputing byComputing))
              (calmsLoose (bodyCalms (Deeper 0) body shapedBody lexBody)))))
    | Value letComments name nameComments equals body, shapedBody, (fineLet, isName, fineName, fineEquals, lexBody) =>
      calmsThen
        (calmsLoose (keywordCalms (atColumn 0) letComments LetKeyword fineLet))
        (calmsThen
          (calmsLoose (nameCalms (Deeper 0).allows nameComments name isName fineName))
          (calmsThen
            (calmsLoose (signCalms (Deeper 0).allows equals Defines fineEquals byComputing byComputing))
            (calmsLoose (bodyCalms (Deeper 0) body shapedBody lexBody))))
    | DeclarationNote comment, _, isComment => events prior only holds =>
      (Noted, (rewrite only then ownLineCalm prior comment.text 0 isComment), byComputing)

theorem laterDeclarationsCalms ∀ (rest: List (Spaced Declaration))
    (shaped: ShapedDeclarations rest)
    (lexical: LexicalDeclarations rest):
    Calms (LaterDeclarations rest) anyPrior anyPrior :=
  match rest, shaped, lexical with
    | [], _, _ => calmsDone anyPrior
    | [{ blankBefore, line }, ..more], (shapedLine, shapedMore), (lexLine, lexMore) => events prior laid holds =>
      match laid with
        | (later, split, run) =>
          match calmsThen
            (declarationCalms line shapedLine lexLine)
            (laterDeclarationsCalms more shapedMore lexMore)
            later
            (afterBlank prior blankBefore)
            run
            byComputing with
            | (after, calmed, ends) =>
              (after, (rewrite split then Eq.trans (blankCalm blankBefore later prior) calmed), ends)

--| The events of a file of the parser's shape are calm: rule N has
--| nothing to move in them.
theorem fileCalm ∀ (file: SourceFile) (events: List Event)
    (shaped: ShapedFile file)
    (lexical: LexicalFile file)
    (laid: FileEvents file events):
    ∃ (after: Prior) => calm Blanked events = Some after :=
  match file, shaped, lexical, laid with
    | { declarations = [] }, _, _, none => (Blanked, (rewrite none))
    | { declarations = [{ blankBefore, line }, ..rest] }, (shapedLine, shapedRest), (lexLine, lexRest), laid =>
      match calmsThen
        (declarationCalms line shapedLine lexLine)
        (laterDeclarationsCalms rest shapedRest lexRest)
        events
        Blanked
        laid
        byComputing with
        | (after, calmed, _) => (after, calmed)

--| The views of a parsed file's events are views rule N leaves as they
--| are.
theorem fileStable ∀ (file: SourceFile) (events: List Event)
    (shaped: ShapedFile file)
    (lexical: LexicalFile file)
    (laid: FileEvents file events):
    StableViews (viewsOf events).views :=
  match fileCalm file events shaped lexical laid with | (after, calmed) => calmStable events after calmed
