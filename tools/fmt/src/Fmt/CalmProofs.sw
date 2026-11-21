--| `calmPrints` (docs/proposals/self-hosted-fmt-s1-sketch.md §1.3, ticket 18a): the rules print a slice 1 tree
--| and its `calm` the same, because `calm` clears only the blank-line flags the rules never read.
--|
--| Every function of `Rules.sw` that slice 1 meets is shown to read a token's comments only through what `calm`
--| keeps: its text, whether it has own-line comments, its trailing comment, and the blank-line flags `kept` leaves
--| where `Word.leading` reads them. The tree's closers are taken to be closers (`Expr.closed`: a `Lexical1` fact),
--| since a bracket word of other text would read its flag as a token's, and `calm` clears it as a closer's.

namespace Fmt.CalmProofs
import Std (Bool, Doc, Eq, List, Nat, Option, Text)
import Std.Doc (..)
import Syntax (Comments, Decl, DefBody, DefKind, Expr, Header, InfixKind, Note, SourceFile, Tok, Word)
import Fmt (..)
import Syntax.SharedFacts (headerResultWithin)

-- A word and its calm word.

--| The pieces of a word the rules read besides the flags `kept` may clear.
def Word.alike (before after: Word): Prop :=
  before.text = after.text
    ∧ before.comments.after = after.comments.after
    ∧ before.comments.above.isEmpty = after.comments.above.isEmpty
    ∧ before.comments.above.map (note => note.text) = after.comments.above.map (note => note.text)

def AllAlike: List Word → List Word → Prop
  | [], [] => True
  | [before, ..more], [after, ..later] => before.alike after ∧ AllAlike more later
  | _, _ => False

theorem keptAlike ∀ (word: Word) (item closer: Bool): word.alike (word.kept item closer) := match word with
  | { text, comments = { above = ([] | [_, .._]), after, blankBefore } } =>
    (byComputing, byComputing, byComputing, byComputing)

theorem alikeTrails ∀ (before after: Word) (alike: before.alike after): before.trails = after.trails := match alike with
  | (_, same, _, _) => Eq.cong (comment => comment.isSome) same

theorem alikeNoted ∀ (before after: Word) (alike: before.alike after): before.noted = after.noted := match alike with
  | (_, _, same, _) => Eq.cong (empty => !empty) same

theorem alikeCloser ∀ (before after: Word) (alike: before.alike after):
    isCloserText before.text = isCloserText after.text :=
  match alike with | (same, _, _, _) => Eq.cong (text => isCloserText text) same

theorem alikeRefl ∀ (word: Word): word.alike word := (byComputing, byComputing, byComputing, byComputing)

theorem alikeTexts ∀ (before after: Word) (alike: before.alike after): before.comments.texts = after.comments.texts :=
  match alike with | (_, same, _, texts) => rewrite same, texts

theorem allAlikeAppend ∀ (front later back after: List Word)
    (fronts: AllAlike front later)
    (backs: AllAlike back after):
    AllAlike (front ++ back) (later ++ after) :=
  match front, later, fronts with
    | [], [], _ => backs
    | [first, ..more], [second, ..others], (same, rest) => (same, (allAlikeAppend more others back after rest backs))

theorem allAlikeLength ∀ (before after: List Word) (alike: AllAlike before after): before.length = after.length :=
  match before, after, alike with
    | [], [], _ => byComputing
    | [first, ..more], [second, ..others], (_, rest) => Eq.cong (n => n + 1) (allAlikeLength more others rest)

theorem allAlikeReverseOnto ∀ (before after front back: List Word)
    (alike: AllAlike before after)
    (fronts: AllAlike front back):
    AllAlike (before.reverseOnto front) (after.reverseOnto back) :=
  match before, after, alike with
    | [], [], _ => fronts
    | [first, ..more], [second, ..others], (same, rest) =>
      allAlikeReverseOnto more others [first, ..front] [second, ..back] rest ((same, fronts))

theorem allAlikeReverse ∀ (before after: List Word)
    (alike: AllAlike before after):
    AllAlike before.reverse after.reverse :=
  allAlikeReverseOnto before after [] [] alike byComputing

theorem trailsBackAlike ∀ (before after: List Word)
    (alike: AllAlike before after):
    trailsBack before = trailsBack after :=
  match before, after, alike with
    | [], [], _ => byComputing
    | [first, ..more], [second, ..others], (same, rest) =>
      rewrite alikeTrails first second same, alikeCloser first second same, trailsBackAlike more others rest

theorem countTrailsAlike ∀ (before after: List Word)
    (alike: AllAlike before after):
    (before.filter Word.trails).length = (after.filter Word.trails).length :=
  match before, after, alike with
    | [], [], _ => byComputing
    | [first, ..more], [second, ..others], (same, rest) =>
      rewrite alikeTrails first second same then
        match second.trails with
          | True => Eq.cong (n => n + 1) (countTrailsAlike more others rest)
          | False => countTrailsAlike more others rest

-- The tree's words, calmed.

--| The brackets' closing words are closers: what `Lexical1` says of a bracket, and what `calm`'s clearing of a
--| closer's flags needs.
def Expr.closed: Expr → Bool
  | Atom _ _ => True
  | Paren _ inner close => isCloserText close.text && inner.closed
  | Tuple _ items _ close | ListOf _ items _ close => isCloserText close.text && allClosed items
  | App head arguments => head.closed && allClosed arguments
  | Infix _ left _ right => left.closed && right.closed
  | Prefix _ operand => operand.closed
  | _ => False

def allClosed: List Expr → Bool
  | [] => True
  | [expr, ..rest] => expr.closed && allClosed rest

--| Calming an item of a list of plain values, or any other.
theorem itemsWordsAll ∀ (items: List Expr) (item: Bool)
    (within: allWithin1 items = True):
    AllAlike (itemsWords items) (itemsWords (calmAll item items)) :=
  match items with
    | [] => byComputing
    | [first, ..rest] =>
      allAlikeAppend first.words
        (first.calm item).words
        (itemsWords rest)
        (itemsWords (calmAll item rest))
        (wordsCalm first item (Bool.andLeft within))
        (itemsWordsAll rest item (Bool.andRight within))

theorem itemsWordsLead ∀ (items: List Expr)
    (within: allWithin1 items = True):
    AllAlike (itemsWords items) (itemsWords (calmLead items)) :=
  match items with
    | [] => byComputing
    | [first, ..rest] =>
      allAlikeAppend first.words
        (first.calm False).words
        (itemsWords rest)
        (itemsWords (calmAll True rest))
        (wordsCalm first False (Bool.andLeft within))
        (itemsWordsAll rest True (Bool.andRight within))

theorem itemsWordsPick ∀ (plain: Bool) (items: List Expr)
    (within: allWithin1 items = True):
    AllAlike (itemsWords items) (itemsWords (pickItems plain items)) :=
  match plain with
    | True => itemsWordsLead items within
    | False => itemsWordsAll items True within

--| `calm` keeps every token's text, own-line comments (as present or not) and trailing comment.
--|
--| Proof idea: Induction on the expression; each constructor's words are its tokens and its parts' words, which `allAlikeAppend` joins from the parts' (`keptAlike` for a token `calm` touches).
theorem wordsCalm ∀ (expr: Expr) (item: Bool)
    (within: expr.within1 = True):
    AllAlike expr.words (expr.calm item).words :=
  match expr with
    | Atom kind word => ((keptAlike word item False), byComputing)
    | Paren open inner close =>
      allAlikeAppend
        [open, ..inner.words]
        [open.kept item False, ..(inner.calm False).words]
        [close]
        [close.kept False True]
        ((keptAlike open item False, wordsCalm inner False within))
        ((keptAlike close False True, byComputing))
    | Tuple open items comma close =>
      allAlikeAppend
        [open, ..itemsWords items]
        [open.kept item False, ..itemsWords (calmAll True items)]
        [close]
        [close.kept False True]
        ((keptAlike open item False, itemsWordsAll items True within))
        ((keptAlike close False True, byComputing))
    | ListOf open items comma close =>
      allAlikeAppend
        [open, ..itemsWords items]
        [open.kept item False, ..itemsWords (calmItems items)]
        [close]
        [close.kept False True]
        ((keptAlike open item False, itemsWordsPick (items.all Expr.plainItem) items within))
        ((keptAlike close False True, byComputing))
    | App head arguments =>
      allAlikeAppend head.words
        (head.calm item).words
        (itemsWords arguments)
        (itemsWords (calmAll False arguments))
        (wordsCalm head item (Bool.andLeft within))
        (itemsWordsAll arguments False (Bool.andRight within))
    | Infix kind left operator right =>
      match kind with
        | InfixBinary =>
          allAlikeAppend left.words
            (left.calm item).words
            [operator, ..right.words]
            [operator.kept False False, ..(right.calm False).words]
            (wordsCalm left item (Bool.andLeft within))
            ((keptAlike operator False False, wordsCalm right False (Bool.andLeft (Bool.andRight within))))
        | InfixArrow =>
          allAlikeAppend left.words
            (left.calm item).words
            [operator, ..right.words]
            [operator.kept False False, ..(right.calm False).words]
            (wordsCalm left item (Bool.andLeft within))
            ((keptAlike operator False False, wordsCalm right False (Bool.andLeft (Bool.andRight within))))
        | _ => cases
    | Prefix operator operand => ((keptAlike operator item False, wordsCalm operand False (Bool.andLeft within)))

-- What the rules read of a token's flags.

--| `calm` keeps what `Word.leading` reads of a token: for a token that starts an item or isn't a closer, the flags
--| it reads, and for a closer, none.
--|
--| Proof idea: Cases on whether the token is hoisted, has own-line comments, and is a closer; in each the document
--| `leading` builds is the same function of the flags, which `kept` changes only where `leading` ignores them (a
--| closer's, a flag above no item), so the Boolean cases each compute.
theorem leadingKept ∀ (word: Word) (around: Around) (key: Nat) (item closer: Bool)
    (same: around.item = item)
    (closes: (!closer || isCloserText word.text) = True):
    (word.kept item closer).leading around key = word.leading around key :=
  match word, around.hoisted with
    | { text, comments = { above, after, blankBefore } }, True => byComputing
    | { text, comments = { above = [], after, blankBefore } }, False =>
      rewrite same then cases item, blankBefore then byComputing
    | { text, comments = { above = [first, ..rest], after, blankBefore } }, False =>
      match isCloserText text with
        | True => byComputing
        | False =>
          match closer with
            | False => cases blankBefore then byComputing

--| A token's leaf is the same for its calm word.
--|
--| Proof idea: Cases on whether the token has own-line comments; `leadingKept` is the only part `calm` changes.
theorem leafKept ∀ (word: Word) (around: Around) (key: Nat) (item closer: Bool)
    (same: around.item = item)
    (closes: (!closer || isCloserText word.text) = True):
    (word.kept item closer).leaf around key = word.leaf around key :=
  match word with
    | { text, comments = { above = [], after, blankBefore } } =>
      rewrite leadingKept { text, comments = { above = [], after, blankBefore } } around key item closer same closes
    | { text, comments = { above = [first, ..rest], after, blankBefore } } =>
      rewrite leadingKept
        { text, comments = { above = [first, ..rest], after, blankBefore } }
        around
        key
        item
        closer
        same
        closes

--| A bracket's opener against its closer's comments: the closer is the same for it.
--|
--| Proof idea: Cases on whether the opener and the closer have own-line comments (the closer's only decides its `Mark`); `leadingKept` for the opener.
theorem openingKept ∀ (open close: Word) (around: Around) (item: Bool)
    (same: around.item = item):
    (open.kept item False).opening around (close.kept False True) = open.opening around close :=
  match open, close with
    | { text, comments = { above = [], after, blankBefore } }, {
        text = other,
        comments = { above = ([] | [_, .._]), after = later, blankBefore = blank }
      } =>
      rewrite leadingKept
        { text, comments = { above = [], after, blankBefore } }
        around
        around.at
        item
        False
        same
        byComputing
    | { text, comments = { above = [first, ..more], after, blankBefore } }, {
        text = other,
        comments = { above = ([] | [_, .._]), after = later, blankBefore = blank }
      } =>
      rewrite leadingKept
        { text, comments = { above = [first, ..more], after, blankBefore } }
        around
        around.at
        item
        False
        same
        byComputing

--| An expression's words begin with its first token, which its calm expression's begin with, calmed.
--|
--| Proof idea: Induction on the expression; a node's first word is its first child's, so each arm takes it from the child's and appends the rest.
theorem wordsFirst ∀ (expr: Expr) (item: Bool)
    (within: expr.within1 = True):
    ∃ (first: Word) (rest later: List Word) => expr.words = [first, ..rest]
      ∧ (expr.calm item).words = [first.kept item False, ..later] :=
  match expr with
    | Atom kind word => (word, [], [], byComputing, byComputing)
    | Paren open inner close =>
      (open, inner.words ++ [close], (inner.calm False).words ++ [close.kept False True], byComputing, byComputing)
    | Tuple open items comma close => (
      open,
      itemsWords items ++ [close],
      itemsWords (calmAll True items) ++ [close.kept False True],
      byComputing,
      byComputing
    )
    | ListOf open items comma close => (
      open,
      itemsWords items ++ [close],
      itemsWords (calmItems items) ++ [close.kept False True],
      byComputing,
      byComputing
    )
    | App head arguments =>
      let (first, rest, later, headWords, calmWords) := wordsFirst head item (Bool.andLeft within)
      (
        first,
        rest ++ itemsWords arguments,
        later ++ itemsWords (calmAll False arguments),
        (rewrite headWords),
        (rewrite calmWords)
      )
    | Infix kind left operator right =>
      match kind with
        | InfixBinary =>
          let (first, rest, later, leftWords, calmWords) := wordsFirst left item (Bool.andLeft within)
          (
            first,
            rest ++ [operator, ..right.words],
            later ++ [operator.kept False False, ..(right.calm False).words],
            (rewrite leftWords),
            (rewrite calmWords)
          )
        | InfixArrow =>
          let (first, rest, later, leftWords, calmWords) := wordsFirst left item (Bool.andLeft within)
          (
            first,
            rest ++ [operator, ..right.words],
            later ++ [operator.kept False False, ..(right.calm False).words],
            (rewrite leftWords),
            (rewrite calmWords)
          )
        | _ => cases
    | Prefix operator operand => (operator, operand.words, (operand.calm False).words, byComputing, byComputing)

theorem firstCalm ∀ (expr: Expr) (item: Bool)
    (within: expr.within1 = True):
    (expr.calm item).firstWord = expr.firstWord.kept item False :=
  let (first, rest, later, plain, calmed) := wordsFirst expr item within
  rewrite plain, calmed

-- What the rules ask of an expression, which `calm` keeps.

theorem sizeCalm ∀ [expr: Expr] (item: Bool) (within: expr.within1 = True): (expr.calm item).size = expr.size :=
  (allAlikeLength expr.words (expr.calm item).words (wordsCalm expr item within)).flipped

theorem trailsCalm ∀ [expr: Expr] (item: Bool) (within: expr.within1 = True): (expr.calm item).trails = expr.trails :=
  (trailsBackAlike expr.words.reverse
    (expr.calm item).words.reverse
    (allAlikeReverse expr.words (expr.calm item).words (wordsCalm expr item within))).flipped

theorem notedCalm ∀ (expr: Expr) (item: Bool) (within: expr.within1 = True): (expr.calm item).noted = expr.noted :=
  rewrite firstCalm expr item within then
    (alikeNoted expr.firstWord (expr.firstWord.kept item False) (keptAlike expr.firstWord item False)).flipped

theorem keptNoted ∀ (word: Word) (item closer: Bool): (word.kept item closer).noted = word.noted :=
  (alikeNoted word (word.kept item closer) (keptAlike word item closer)).flipped

theorem plainItemCalm ∀ (expr: Expr) (item: Bool)
    (within: expr.within1 = True):
    (expr.calm item).plainItem = expr.plainItem :=
  match expr with
    | Atom kind word => rewrite keptNoted word item False
    | Paren _ _ _ | Tuple _ _ _ _ | ListOf _ _ _ _ | App _ _ => byComputing
    | Infix kind left operator right =>
      match kind with
        | InfixBinary => byComputing
        | InfixArrow => byComputing
        | _ => cases
    | Prefix operator operand => byComputing

theorem calmAllEmpty ∀ (items: List Expr) (item: Bool): (calmAll item items).isEmpty = items.isEmpty := match items with
  | [] | [_, .._] => byComputing

theorem calmItemsEmpty ∀ (items: List Expr): (calmItems items).isEmpty = items.isEmpty := match items with
  | [] => byComputing
  | [first, ..rest] =>
    match items.all Expr.plainItem with
      | True => byComputing
      | False => byComputing

theorem calmAllPlain ∀ (items: List Expr) (item: Bool)
    (within: allWithin1 items = True):
    (calmAll item items).all Expr.plainItem = items.all Expr.plainItem :=
  match items with
    | [] => byComputing
    | [first, ..rest] =>
      rewrite plainItemCalm first item (Bool.andLeft within), calmAllPlain rest item (Bool.andRight within)

theorem calmLeadPlain ∀ (items: List Expr)
    (within: allWithin1 items = True):
    (calmLead items).all Expr.plainItem = items.all Expr.plainItem :=
  match items with
    | [] => byComputing
    | [first, ..rest] =>
      rewrite plainItemCalm first False (Bool.andLeft within), calmAllPlain rest True (Bool.andRight within)

--| `calm` keeps whether an argument may stay on its call's line.
--|
--| Proof idea: Cases on the expression; a tuple or list stays empty or not (`calmAllEmpty`, `calmItemsEmpty`), a prefix's operand keeps its constructor.
theorem simpleCalm ∀ (expr: Expr) (item: Bool) (within: expr.within1 = True): (expr.calm item).simple = expr.simple :=
  match expr with
    | Tuple open items comma close => calmAllEmpty items True
    | ListOf open items comma close => calmItemsEmpty items
    | _ => cases

--| In the slice, with its closers closers.
def Expr.good (expr: Expr): Bool := expr.within1 && expr.closed

def allGood: List Expr → Bool
  | [] => True
  | [expr, ..rest] => expr.good && allGood rest

theorem goodWithin ∀ (expr: Expr) (good: expr.good = True): expr.within1 = True := Bool.andLeft good

theorem allGoodWithin ∀ (items: List Expr) (good: allGood items = True): allWithin1 items = True := match items with
  | [] => byComputing
  | [first, ..rest] => Bool.andIntro (goodWithin first (Bool.andLeft good)) (allGoodWithin rest (Bool.andRight good))

-- Chains.

theorem inChainCalm ∀ (expr: Expr) (item: Bool) (level: Option Nat)
    (within: expr.within1 = True):
    (expr.calm item).inChain level = expr.inChain level :=
  match expr with
    | Atom _ _ | Paren _ _ _ | Tuple _ _ _ _ | ListOf _ _ _ _ | App _ _ => byComputing
    | Infix kind left operator right =>
      match kind with
        | InfixBinary => byComputing
        | InfixArrow => byComputing
        | _ => cases
    | Prefix operator operand => byComputing

--| `calm` keeps whether a chain's first operand is a `match`.
--|
--| Proof idea: Induction down the left operands, with `inChainCalm` for each link.
theorem opensArmsCalm ∀ (expr: Expr) (item: Bool) (level: Option Nat)
    (within: expr.within1 = True):
    (expr.calm item).opensArms level = expr.opensArms level :=
  match expr with
    | Atom _ _ | Paren _ _ _ | Tuple _ _ _ _ | ListOf _ _ _ _ | App _ _ => byComputing
    | Infix kind left operator right =>
      match kind with
        | InfixBinary =>
          rewrite inChainCalm (Infix InfixBinary left operator right) item level within,
              opensArmsCalm left item level (Bool.andLeft within)
        | InfixArrow =>
          rewrite inChainCalm (Infix InfixArrow left operator right) item level within,
              opensArmsCalm left item level (Bool.andLeft within)
        | _ => cases
    | Prefix operator operand => byComputing

--| A node's first token's own-line comments print the same for the calm token.
--|
--| Proof idea: Cases on whether it has own-line comments, then `leadingKept`.
theorem framedByKept ∀ (first: Word) (around: Around) (doc: Doc) (item: Bool)
    (same: around.item = item):
    framedBy (first.kept item False) around doc = framedBy first around doc :=
  match first with
    | { text, comments = { above = [], after, blankBefore } } =>
      rewrite leadingKept
            { text, comments = { above = [], after, blankBefore } }
            around
            around.at
            item
            False
            same
            byComputing,
          same then
        cases item, blankBefore then byComputing
    | { text, comments = { above = [head, ..rest], after, blankBefore } } =>
      rewrite leadingKept
        { text, comments = { above = [head, ..rest], after, blankBefore } }
        around
        around.at
        item
        False
        same
        byComputing

theorem framedCalm ∀ (expr: Expr) (around: Around) (doc doc': Doc) (item: Bool)
    (same: around.item = item)
    (within: expr.within1 = True)
    (docs: doc' = doc):
    (expr.calm item).framed around doc' = expr.framed around doc :=
  rewrite firstCalm expr item within, docs, framedByKept expr.firstWord around doc item same

--| The rules print an expression and its calm expression the same, wherever it stands: the induction hypothesis
--| the rules' lemmas take for each part.
def ElKept (expr: Expr): Prop := ∀ (below: Around) => (expr.calm below.item).el below = expr.el below

theorem closerOk ∀ (word: Word) (closes: isCloserText word.text = True): (!True || isCloserText word.text) = True :=
  rewrite closes

theorem parenInnerKept ∀ (inner: Expr) (around: Around)
    (good: inner.good = True)
    (each: (inner.calm False).el around = inner.el around):
    parenInner (inner.calm False) around = parenInner inner around :=
  match inner with
    | Block _ _ _ | If _ _ _ _ _ _ _ => cases
    | _ => each

-- Documents equal part by part.

theorem concatCong ∀ (docs docs': List Doc) (same: docs = docs'): Doc.concat docs = Doc.concat docs' :=
  Eq.cong (list => Doc.concat list) same

theorem list2 ∀ [a b a' b': Doc] (first: a = a') (second: b = b'): [a, b] = [a', b'] := rewrite first, second

theorem list3 ∀ (a b c a' b' c': Doc) (first: a = a') (second: b = b') (third: c = c'): [a, b, c] = [a', b', c'] :=
  rewrite first, second, third

theorem appendCong ∀ (front back front' back': List Doc)
    (first: front = front')
    (second: back = back'):
    front ++ back = front' ++ back' :=
  rewrite first, second

theorem nextEq ∀ (around: Around) (before before': Bool) (skipped skipped': Nat)
    (sameBefore: before = before')
    (sameSkipped: skipped = skipped'):
    around.next before skipped = around.next before' skipped' :=
  rewrite sameBefore, sameSkipped

--| A bracket's document is the same for the calm inner expression and brackets.
--|
--| Proof idea: `Doc.concat` of its three parts: the opener (`openingKept`), the inner (`parenInnerKept`, from the induction hypothesis) and the closer (`leafKept`, at the place the inner's size and trailing comment give, equal by `sizeCalm` and `trailsCalm`); `concatCong` joins them.
theorem parenKept ∀ (open: Word) (inner: Expr) (close: Word) (around: Around) (item: Bool)
    (same: around.item = item)
    (inside: inner.good = True)
    (closes: isCloserText close.text = True)
    (each: ElKept inner):
    parenDoc (open.kept item False) (inner.calm False) (close.kept False True) around
      = parenDoc open inner close around :=
  concatCong
    [
      (open.kept item False).opening around (close.kept False True),
      parenInner (inner.calm False) ((open.kept item False).trails |> (trails => around.next trails 1)),
      (close.kept False True).leaf (around.next (inner.calm False).trails (1 + (inner.calm False).size)) around.at
    ]
    [
      open.opening around close,
      parenInner inner (around.next open.trails 1),
      close.leaf (around.next inner.trails (1 + inner.size)) around.at
    ]
    (list3 _ _ _ _ _ _
      (openingKept open close around item same)
      (parenInnerKept inner (around.next open.trails 1) inside (each (around.next open.trails 1)))
      (rewrite nextEq around
            (inner.calm False).trails
            inner.trails
            (1 + (inner.calm False).size)
            (1 + inner.size)
            (trailsCalm False (goodWithin inner inside))
            (Eq.cong (size => 1 + size) (sizeCalm False (goodWithin inner inside))),
          leafKept close
            (around.next inner.trails (1 + inner.size))
            around.at
            False
            True
            byComputing
            (closerOk close closes)))

-- Prefix operators.

--| `calm` keeps whether an expression is an application of a numeral.
--|
--| Proof idea: Cases on the expression and on a head's kind.
theorem numeralCalm ∀ (expr: Expr) (item: Bool)
    (within: expr.within1 = True):
    (expr.calm item).numeralApplication = expr.numeralApplication :=
  match expr with
    | App head arguments => cases head then byComputing
    | Infix kind left operator right => cases kind then byComputing
    | _ => byComputing

theorem prefixGapCalm ∀ (operator: Word) (operand: Expr) (item: Bool)
    (within: operand.within1 = True):
    prefixGap (operator.kept item False) (operand.calm False) = prefixGap operator operand :=
  rewrite firstCalm operand False within, numeralCalm operand False within

--| A prefix operator's document is the same for the calm operator and operand.
--|
--| Proof idea: Its three parts, the operator's leaf (`leafKept`), the gap (`prefixGapCalm`: the first word's text and the numeral test are kept) and the operand's element.
theorem prefixKept ∀ (operator: Word) (operand: Expr) (around: Around) (item: Bool)
    (same: around.item = item)
    (within: operand.within1 = True)
    (each: ElKept operand):
    Doc.concat [
      (operator.kept item False).leaf { around | hoisted = True } around.at,
      prefixGap (operator.kept item False) (operand.calm False),
      (operand.calm False).el (around.next operator.trails 1)
    ]
      = Doc.concat [
        operator.leaf { around | hoisted = True } around.at,
        prefixGap operator operand,
        operand.el (around.next operator.trails 1)
      ] :=
  concatCong
    [
      (operator.kept item False).leaf { around | hoisted = True } around.at,
      prefixGap (operator.kept item False) (operand.calm False),
      (operand.calm False).el (around.next operator.trails 1)
    ]
    [
      operator.leaf { around | hoisted = True } around.at,
      prefixGap operator operand,
      operand.el (around.next operator.trails 1)
    ]
    (list3 _ _ _ _ _ _
      (leafKept operator { around | hoisted = True } around.at item False same byComputing)
      (prefixGapCalm operator operand item within)
      (each (around.next operator.trails 1)))

-- Brackets.

def AllElKept: List Expr → Prop
  | [] => True
  | [expr, ..rest] => ElKept expr ∧ AllElKept rest

--| `calm`'s items with the first for an item or not, the rest items.
def calmList (first: Bool): List Expr → List Expr
  | [] => []
  | [expr, ..rest] => [expr.calm first, ..calmAll True rest]

theorem calmAllList ∀ (items: List Expr): calmAll True items = calmList True items := match items with
  | [] | [_, .._] => byComputing

theorem pickList ∀ (bare: Bool) (items: List Expr): pickItems bare items = calmList (!bare) items :=
  match bare, items with | True | False, [] | [_, .._] => byComputing

theorem pickEmpty ∀ (bare: Bool) (items: List Expr): (pickItems bare items).isEmpty = items.isEmpty :=
  rewrite pickList bare items then match items with | [] | [_, .._] => byComputing

theorem pickPlain ∀ (bare: Bool) (items: List Expr)
    (within: allWithin1 items = True):
    (pickItems bare items).all Expr.plainItem = items.all Expr.plainItem :=
  match bare with
    | True => calmLeadPlain items within
    | False => calmAllPlain items True within

theorem sizeAlike ∀ (before after: Expr) (alike: AllAlike before.words after.words): before.size = after.size :=
  allAlikeLength before.words after.words alike

theorem trailsAlike ∀ (before after: Expr) (alike: AllAlike before.words after.words): before.trails = after.trails :=
  trailsBackAlike before.words.reverse after.words.reverse (allAlikeReverse before.words after.words alike)

theorem holdsAlike ∀ (before after: Expr)
    (alike: AllAlike before.words after.words):
    before.holdsTrailingComment = after.holdsTrailingComment :=
  rewrite trailsAlike before after alike, countTrailsAlike before.words after.words alike

theorem allAlikeDrop ∀ (before after: List Word) (count: Nat)
    (alike: AllAlike before after):
    AllAlike (before.drop count) (after.drop count) :=
  match count, before, after, alike with
    | Zero, before, after, alike => alike
    | Succ less, [], [], _ => byComputing
    | Succ less, [first, ..more], [second, ..others], (same, rest) => allAlikeDrop more others less rest

theorem beforeCloseAlike ∀ (before after: Expr)
    (alike: AllAlike before.words after.words):
    before.trailsBeforeClose = after.trailsBeforeClose :=
  trailsBackAlike
    (before.words.reverse.drop 1)
    (after.words.reverse.drop 1)
    (allAlikeDrop before.words.reverse after.words.reverse 1 (allAlikeReverse before.words after.words alike))

--| The words of a bracket, its items replaced by items with alike words.
theorem bracketAlike ∀ (open open' close close': Word) (items items': List Expr)
    (opens: open.alike open') (closes: close.alike close')
    (inside: AllAlike (itemsWords items) (itemsWords items')):
    AllAlike (ListOf open items False close).words (ListOf open' items' False close').words :=
  allAlikeAppend
    [open, ..itemsWords items]
    [open', ..itemsWords items']
    [close]
    [close']
    ((opens, inside))
    ((closes, byComputing))

--| The filled cells and the broken lines of a bracket, as the items' elements make them.
--|
--| Proof idea: Induction on the items; each cell is its item's element (the hypothesis) and a comma, and the later cells stand after the item's size (`sizeCalm`).
theorem cellsKept ∀ (bare arm before: Bool) (at: Nat) (items: List Expr)
    (each: AllElKept items)
    (good: allGood items = True):
    cells bare arm before at (calmList (!bare) items) = cells bare arm before at items :=
  match items, each with
    | [], _ => byComputing
    | [item], (first, _) => Eq.cong (doc => [doc]) (first (firstAround bare arm before at))
    | [item, ..rest], (first, others) =>
      List.consEqOfEq
        (Doc.concat [(item.calm (!bare)).el (firstAround bare arm before at), Closing ","])
        (Doc.concat [item.el (firstAround bare arm before at), Closing ","])
        (cells False arm (item.calm (!bare)).trails (at + (item.calm (!bare)).size) (calmAll True rest))
        (cells False arm item.trails (at + item.size) rest)
        (concatCong
          [(item.calm (!bare)).el (firstAround bare arm before at), Closing ","]
          [item.el (firstAround bare arm before at), Closing ","]
          (list2 (first (firstAround bare arm before at)) byComputing))
        (rewrite calmAllList rest,
            sizeCalm (!bare) (goodWithin item (allGoodHead rest good)),
            trailsCalm (!bare) (goodWithin item (allGoodHead rest good)) then
          cellsKept False arm item.trails (at + item.size) (rest) others (allGoodTail rest good))

--| A broken bracket's lines are the same for the calm items.
--|
--| Proof idea: As `cellsKept`, with a separator before each item.
theorem brokenItemsKept ∀ (bare arm first before: Bool) (at: Nat) (items: List Expr)
    (each: AllElKept items)
    (good: allGood items = True):
    brokenItems bare arm first before at (calmList (!bare) items) = brokenItems bare arm first before at items :=
  match items, each with
    | [], _ => byComputing
    | [item], (kept, _) => list2 byComputing (kept (firstAround bare arm before at))
    | [item, ..rest], (kept, others) =>
      List.consEqOfEq
        (if first then SoftLine else Line)
        (if first then SoftLine else Line)
        [
          (item.calm (!bare)).el (firstAround bare arm before at),
          Closing ",",
          ..brokenItems False arm False (item.calm (!bare)).trails (at + (item.calm (!bare)).size) (calmAll True rest)
        ]
        [
          item.el (firstAround bare arm before at),
          Closing ",",
          ..brokenItems False arm False item.trails (at + item.size) rest
        ]
        byComputing
        (List.consEqOfEq _ _ _ _
          (kept (firstAround bare arm before at))
          (List.consEqOfEq
            (Closing ",")
            (Closing ",")
            (brokenItems False arm False (item.calm (!bare)).trails (at + (item.calm (!bare)).size) (calmAll True rest))
            (brokenItems False arm False item.trails (at + item.size) rest)
            byComputing
            (rewrite calmAllList rest,
                sizeCalm (!bare) (goodWithin item (allGoodHead rest good)),
                trailsCalm (!bare) (goodWithin item (allGoodHead rest good)) then
              brokenItemsKept False arm False item.trails (at + item.size) rest others (allGoodTail rest good))))

--| `bracketContent` with what it reads of the items worked out beforehand: whether there are none, whether all are
--| plain values, whether a comment is held inside, the opener and closer, and the lines the items make filled or
--| broken.
def bracketFrom (list empty plain holds: Bool) (prefix closer: Doc) (filled broken: List Doc): Doc :=
  if empty then Doc.concat [prefix, closer]
  else if list && !holds && plain then Doc.concat [prefix, Nest 2 (Fill filled), closer]
  else
    let parts := [prefix, Nest 2 (Doc.concat broken), SoftLine, closer]
    Doc.concat (if holds then parts ++ [BreakParent] else parts)

theorem bracketIs ∀ (list: Bool) (open: Word) (items: List Expr) (close: Word) (around: Around):
    bracketContent list open items close around
      = bracketFrom list items.isEmpty
        (items.all Expr.plainItem)
        (ListOf open items False close).holdsTrailingComment
        (open.opening around close)
        (close.leaf
          (around.next (ListOf open items False close).trailsBeforeClose ((ListOf open items False close).size - 1))
          around.at)
        (cells (list && items.all Expr.plainItem) around.inArm open.trails (around.at + 1) items)
        (brokenItems (list && items.all Expr.plainItem) around.inArm True open.trails (around.at + 1) items) :=
  byComputing

theorem bracketFromCong ∀ (list empty empty' plain plain' holds holds': Bool)
    (prefix prefix' closer closer': Doc) (filled filled' broken broken': List Doc)
    (sameEmpty: empty = empty')
    (samePlain: plain = plain')
    (sameHolds: holds = holds')
    (samePrefix: prefix = prefix')
    (sameCloser: closer = closer')
    (sameFilled: filled = filled')
    (sameBroken: broken = broken'):
    bracketFrom list empty plain holds prefix closer filled broken
      = bracketFrom list empty' plain' holds' prefix' closer' filled' broken' :=
  rewrite sameEmpty, samePlain, sameHolds, samePrefix, sameCloser, sameFilled, sameBroken

--| The rules' comma bracket is the same for the calm items and calm brackets.
--|
--| Proof idea: `bracketFrom` is `bracketContent` from what it reads of the items (empty, plain, a held comment, the
--| opener and closer, the filled and broken lines); each is the same before and after (`pickEmpty`, `pickPlain`,
--| `holdsAlike`, `openingKept`, the closer's `leafKept`, `cellsKept` and `brokenItemsKept`), so the two calls are
--| equal by `bracketFromCong`.
theorem bracketKept ∀ (list: Bool) (open: Word) (items: List Expr) (close: Word) (around: Around) (item: Bool)
    (same: around.item = item)
    (good: allGood items = True)
    (closes: isCloserText close.text = True)
    (each: AllElKept items):
    bracketContent list
      (open.kept item False)
      (pickItems (list && items.all Expr.plainItem) items)
      (close.kept False True)
      around
      = bracketContent list open items close around :=
  let bare := list && items.all Expr.plainItem
  let calmed := pickItems bare items
  let before := ListOf open items False close
  let after := ListOf (open.kept item False) calmed False (close.kept False True)
  let alike: AllAlike before.words after.words :=
    bracketAlike open
      (open.kept item False)
      close
      (close.kept False True)
      items
      calmed
      (keptAlike open item False)
      (keptAlike close False True)
      (itemsWordsPick bare items (allGoodWithin items good))
  let closeSame: (close.kept False True).leaf (around.next after.trailsBeforeClose (after.size - 1)) around.at
    = close.leaf (around.next before.trailsBeforeClose (before.size - 1)) around.at :=
    rewrite nextEq around after.trailsBeforeClose before.trailsBeforeClose
          (after.size - 1)
          (before.size - 1)
          (beforeCloseAlike before after alike).flipped
          (Eq.cong (size => size - 1) (sizeAlike before after alike).flipped),
        leafKept close
          (around.next before.trailsBeforeClose (before.size - 1))
          around.at
          False
          True
          byComputing
          (closerOk close closes)
  let opening' := (open.kept item False).opening around (close.kept False True)
  let opening := open.opening around close
  let closer' := (close.kept False True).leaf (around.next after.trailsBeforeClose (after.size - 1)) around.at
  let closer := close.leaf (around.next before.trailsBeforeClose (before.size - 1)) around.at
  let filled' :=
    cells (list && calmed.all Expr.plainItem) around.inArm (open.kept item False).trails (around.at + 1) calmed
  let filled := cells bare around.inArm open.trails (around.at + 1) items
  let broken' :=
    brokenItems
      (list && calmed.all Expr.plainItem)
      around.inArm
      True
      (open.kept item False).trails
      (around.at + 1)
      calmed
  let broken := brokenItems bare around.inArm True open.trails (around.at + 1) items
  calc bracketContent list (open.kept item False) calmed (close.kept False True) around
    _ = bracketFrom list calmed.isEmpty
        (calmed.all Expr.plainItem)
        after.holdsTrailingComment
        opening'
        closer'
        filled'
        broken' := bracketIs list (open.kept item False) calmed (close.kept False True) around
    _ = bracketFrom list items.isEmpty
        (items.all Expr.plainItem)
        before.holdsTrailingComment
        opening
        closer
        filled
        broken :=
      bracketFromCong list calmed.isEmpty items.isEmpty
        (calmed.all Expr.plainItem)
        (items.all Expr.plainItem)
        after.holdsTrailingComment
        before.holdsTrailingComment
        opening'
        opening
        closer'
        closer
        filled'
        filled
        broken'
        broken
        (pickEmpty bare items)
        (pickPlain bare items (allGoodWithin items good))
        (holdsAlike before after alike).flipped
        (openingKept open close around item same)
        closeSame
        (rewrite pickPlain bare items (allGoodWithin items good), pickList bare items then
          cellsKept bare around.inArm open.trails (around.at + 1) items each good)
        (rewrite pickPlain bare items (allGoodWithin items good), pickList bare items then
          brokenItemsKept bare around.inArm True open.trails (around.at + 1) items each good)
    _ = bracketContent list open items close around := (bracketIs list open items close around).flipped

-- Calls.

theorem huggedFromCong ∀ (first first': Word) (around: Around) (content content': Doc)
    (sameFrame: ∀ (doc: Doc) => framedBy first around doc = framedBy first' around doc)
    (sameContent: content = content'):
    (framedBy first around (Group content content.forcesBreak), Some (framedBy first around (Group content True)))
      = (
        framedBy first' around (Group content' content'.forcesBreak),
        Some (framedBy first' around (Group content' True))
      ) :=
  rewrite sameContent, sameFrame (Group content' content'.forcesBreak), sameFrame (Group content' True)

--| A hugged bracket's two documents are the same for the calm items and bracket.
--|
--| Proof idea: Both are the bracket's content in a group, framed by the opener; `framedByKept` and `bracketKept`.
theorem huggedKept ∀ (list: Bool) (open: Word) (items: List Expr) (close: Word) (around: Around) (item: Bool)
    (same: around.item = item)
    (good: allGood items = True)
    (closes: isCloserText close.text = True)
    (each: AllElKept items):
    huggedBracket list
      (open.kept item False)
      (pickItems (list && items.all Expr.plainItem) items)
      (close.kept False True)
      around
      = huggedBracket list open items close around :=
  huggedFromCong
    (open.kept item False)
    open
    around
    (bracketContent list
      (open.kept item False)
      (pickItems (list && items.all Expr.plainItem) items)
      (close.kept False True)
      { around | hoisted = True })
    (bracketContent list open items close { around | hoisted = True })
    (doc => framedByKept open around doc item same)
    (bracketKept list open items close { around | hoisted = True } item same good closes each)

theorem takeCalm ∀ (items: List Expr) (item: Bool) (count: Nat):
    (calmAll item items).take count = calmAll item (items.take count) :=
  match items, count with
    | [], Zero | Succ _ => byComputing
    | [first, ..rest], Zero => byComputing
    | [first, ..rest], Succ less => Eq.cong (later => [first.calm item, ..later]) (takeCalm rest item less)

--| `calm` keeps how many of a call's elements stay on its line.
--|
--| Proof idea: Induction on the arguments; each is simple or not (`simpleCalm`) and follows a comment or not (`trailsCalm`).
theorem keptFrontKept ∀ (previous previous': Expr) (arguments: List Expr)
    (sameTrails: previous'.trails = previous.trails)
    (within: allWithin1 arguments = True):
    keptFront previous' (calmAll False arguments) = keptFront previous arguments :=
  match arguments with
    | [] => byComputing
    | [argument, ..rest] =>
      rewrite simpleCalm argument False (Bool.andLeft within), sameTrails then
        match argument.simple && !previous.trails with
          | True =>
            Eq.cong
              (count => 1 + count)
              (keptFrontKept argument
                (argument.calm False)
                rest
                (trailsCalm False (Bool.andLeft within))
                (Bool.andRight within))
          | False => byComputing

theorem commentBetweenKept ∀ (previous previous': Expr) (arguments: List Expr)
    (sameTrails: previous'.trails = previous.trails)
    (within: allWithin1 arguments = True):
    commentBetween previous' (calmAll False arguments) = commentBetween previous arguments :=
  match arguments with
    | [] => byComputing
    | [next, ..rest] =>
      rewrite notedCalm next False (Bool.andLeft within),
          sameTrails,
          commentBetweenKept next (next.calm False) rest (trailsCalm False (Bool.andLeft within)) (Bool.andRight within)

-- Elements, in one induction with chains.

-- A good expression's parts are good.

theorem allGoodOf ∀ (items: List Expr)
    (within: allWithin1 items = True)
    (closed: allClosed items = True):
    allGood items = True :=
  match items with
    | [] => byComputing
    | [first, ..rest] =>
      Bool.andIntro
        (Bool.andIntro (Bool.andLeft within) (Bool.andLeft closed))
        (allGoodOf rest (Bool.andRight within) (Bool.andRight closed))

theorem allGoodHead ∀ [first: Expr] (rest: List Expr) (good: allGood [first, ..rest] = True): first.good = True :=
  Bool.andLeft good

theorem allGoodTail ∀ [first: Expr] (rest: List Expr) (good: allGood [first, ..rest] = True): allGood rest = True :=
  Bool.andRight good

theorem parenGood ∀ (open: Word) (inner: Expr) (close: Word)
    (good: (Paren open inner close).good = True):
    inner.good = True :=
  Bool.andIntro (Bool.andLeft good) (Bool.andRight (Bool.andRight good))

theorem parenCloses ∀ (open: Word) (inner: Expr) (close: Word)
    (good: (Paren open inner close).good = True):
    isCloserText close.text = True :=
  Bool.andLeft (Bool.andRight good)

theorem tupleGood ∀ (open: Word) (items: List Expr) (comma: Bool) (close: Word)
    (good: (Tuple open items comma close).good = True):
    allGood items = True :=
  allGoodOf items (Bool.andLeft good) (Bool.andRight (Bool.andRight good))

theorem tupleCloses ∀ (open: Word) (items: List Expr) (comma: Bool) (close: Word)
    (good: (Tuple open items comma close).good = True):
    isCloserText close.text = True :=
  Bool.andLeft (Bool.andRight good)

theorem listGood ∀ (open: Word) (items: List Expr) (comma: Bool) (close: Word)
    (good: (ListOf open items comma close).good = True):
    allGood items = True :=
  allGoodOf items (Bool.andLeft good) (Bool.andRight (Bool.andRight good))

theorem listCloses ∀ (open: Word) (items: List Expr) (comma: Bool) (close: Word)
    (good: (ListOf open items comma close).good = True):
    isCloserText close.text = True :=
  Bool.andLeft (Bool.andRight good)

theorem appGoodHead ∀ (head: Expr) (arguments: List Expr) (good: (App head arguments).good = True): head.good = True :=
  Bool.andIntro (Bool.andLeft (Bool.andLeft good)) (Bool.andLeft (Bool.andRight good))

theorem appGoodArguments ∀ (head: Expr) (arguments: List Expr)
    (good: (App head arguments).good = True):
    allGood arguments = True :=
  allGoodOf arguments (Bool.andRight (Bool.andLeft good)) (Bool.andRight (Bool.andRight good))

theorem binaryGoodLeft ∀ (left: Expr) (operator: Word) (right: Expr)
    (good: (Infix InfixBinary left operator right).good = True):
    left.good = True :=
  Bool.andIntro (Bool.andLeft (Bool.andLeft good)) (Bool.andLeft (Bool.andRight good))

theorem binaryGoodRight ∀ (left: Expr) (operator: Word) (right: Expr)
    (good: (Infix InfixBinary left operator right).good = True):
    right.good = True :=
  Bool.andIntro (Bool.andLeft (Bool.andRight (Bool.andLeft good))) (Bool.andRight (Bool.andRight good))

theorem arrowGoodLeft ∀ (left: Expr) (operator: Word) (right: Expr)
    (good: (Infix InfixArrow left operator right).good = True):
    left.good = True :=
  Bool.andIntro (Bool.andLeft (Bool.andLeft good)) (Bool.andLeft (Bool.andRight good))

theorem arrowGoodRight ∀ (left: Expr) (operator: Word) (right: Expr)
    (good: (Infix InfixArrow left operator right).good = True):
    right.good = True :=
  Bool.andIntro (Bool.andLeft (Bool.andRight (Bool.andLeft good))) (Bool.andRight (Bool.andRight good))

theorem prefixGood ∀ (operator: Word) (operand: Expr)
    (good: (Prefix operator operand).good = True):
    operand.good = True :=
  Bool.andIntro (Bool.andLeft (Bool.andLeft good)) (Bool.andRight good)

theorem chainRightKept ∀ (level: Option Nat) (right: Expr) (around: Around)
    (good: right.good = True)
    (link: linkDocs level False (right.calm False) around = linkDocs level False right around):
    chainRight level (right.calm False) around = chainRight level right around :=
  match right with
    | Block _ _ _ => cases
    | _ => rewrite link

--| A chain's lines are the same for the calm operands and operator.
--|
--| Proof idea: The first operand's lines are `linkDocsKept`'s; the operator's leaf is `leafKept` at the place the
--| left operand's size and trailing comment give (`sizeCalm`, `trailsCalm`); the right operand by `chainRightKept`.
theorem chainLinksKept ∀ (level: Option Nat) (first: Bool) (left: Expr) (operator: Word) (right: Expr) (around: Around)
    (leftGood: left.good = True)
    (rightGood: right.good = True):
    chainLinks level first (left.calm around.item) (operator.kept False False) (right.calm False) around
      = chainLinks level first left operator right around :=
  let calmed := left.calm around.item
  let leftAround := around.next left.trails left.size
  let calmedAround := around.next calmed.trails calmed.size
  let rightAround := around.next operator.trails (left.size + 1)
  let calmedRight := around.next (operator.kept False False).trails (calmed.size + 1)
  let leafSame: (operator.kept False False).leaf calmedAround calmedAround.at
    = operator.leaf leftAround leftAround.at :=
    rewrite nextEq around calmed.trails left.trails calmed.size left.size
          (trailsCalm around.item (goodWithin left leftGood))
          (sizeCalm around.item (goodWithin left leftGood)),
        leafKept operator leftAround leftAround.at False False byComputing byComputing
  let rightSame: calmedRight = rightAround :=
    rewrite nextEq around
      (operator.kept False False).trails
      operator.trails
      (calmed.size + 1)
      (left.size + 1)
      byComputing
      (Eq.cong (size => size + 1) (sizeCalm around.item (goodWithin left leftGood)))
  appendCong
    (linkDocs level first calmed around)
    [
      Line,
      (operator.kept False False).leaf calmedAround calmedAround.at,
      ..chainRight level (right.calm False) calmedRight
    ]
    (linkDocs level first left around)
    [Line, operator.leaf leftAround leftAround.at, ..chainRight level right rightAround]
    (linkDocsKept level first left around leftGood)
    (List.consEqOfEq Line Line
      [(operator.kept False False).leaf calmedAround calmedAround.at, ..chainRight level (right.calm False) calmedRight]
      [operator.leaf leftAround leftAround.at, ..chainRight level right rightAround]
      byComputing
      (List.consEqOfEq
        ((operator.kept False False).leaf calmedAround calmedAround.at)
        (operator.leaf leftAround leftAround.at)
        (chainRight level (right.calm False) calmedRight)
        (chainRight level right rightAround)
        leafSame
        (rewrite rightSame then
          chainRightKept level right rightAround rightGood (linkDocsKept level False right rightAround rightGood))))

theorem chainKept ∀ (level: Option Nat) (left: Expr) (operator: Word) (right: Expr) (around: Around)
    (leftGood: left.good = True)
    (rightGood: right.good = True):
    chain level (left.calm around.item) (operator.kept False False) (right.calm False) around
      = chain level left operator right around :=
  rewrite chainLinksKept level True left operator right around leftGood rightGood,
      opensArmsCalm left around.item level (goodWithin left leftGood)

--| A chain operand's documents are the same for the calm operand.
--|
--| Proof idea: A chain of the level is its links (`chainLinksKept`), any other operand its element (`elCalm`); `inChainCalm` says which.
theorem linkDocsKept ∀ (level: Option Nat) (first: Bool) (expr: Expr) (around: Around)
    (good: expr.good = True):
    linkDocs level first (expr.calm around.item) around = linkDocs level first expr around :=
  match expr with
    | Infix kind left operator right =>
      match kind with
        | InfixBinary =>
          match (Infix InfixBinary left operator right).inChain level with
            | True =>
              chainLinksKept level first left operator right around
                (binaryGoodLeft left operator right good)
                (binaryGoodRight left operator right good)
            | False => Eq.cong (doc => [doc]) (elCalm (Infix InfixBinary left operator right) around good)
        | InfixArrow =>
          match (Infix InfixArrow left operator right).inChain level with
            | True =>
              chainLinksKept level first left operator right around
                (arrowGoodLeft left operator right good)
                (arrowGoodRight left operator right good)
            | False => Eq.cong (doc => [doc]) (elCalm (Infix InfixArrow left operator right) around good)
        | _ => cases
    | Match _ _ _ _ => cases
    | _ => Eq.cong (doc => [doc]) (elCalm expr around good)

--| The rules print an expression and its calm expression the same wherever it stands.
--|
--| Proof idea: Induction on the expression, with each rule's lemma taking the hypothesis for its parts (`ElKept`):
--| a token by `leafKept`; a bracket by `parenKept` or `bracketKept`; a call by `appKept`; a chain by `chainKept`
--| and `linkDocsKept`; a prefix by `prefixKept`. Each node's first token's comments are framed the same
--| (`framedCalm`).
theorem elCalm ∀ (expr: Expr) (around: Around)
    (good: expr.good = True):
    (expr.calm around.item).el around = expr.el around :=
  match expr with
    | Atom kind word => leafKept word around around.at around.item False byComputing byComputing
    | Paren open inner close =>
      framedCalm
        (Paren open inner close)
        around
        (parenDoc open inner close { around | hoisted = True })
        (parenDoc (open.kept around.item False) (inner.calm False) (close.kept False True) { around | hoisted = True })
        around.item
        byComputing
        (goodWithin (Paren open inner close) good)
        (parenKept open inner close
          { around | hoisted = True }
          around.item
          byComputing
          (parenGood open inner close good)
          (parenCloses open inner close good)
          (below => elCalm inner below (parenGood open inner close good)))
    | Prefix operator operand =>
      framedCalm
        (Prefix operator operand)
        around
        (Doc.concat [
          operator.leaf { around | hoisted = True } around.at,
          prefixGap operator operand,
          operand.el (around.next operator.trails 1)
        ])
        (Doc.concat [
          (operator.kept around.item False).leaf { around | hoisted = True } around.at,
          prefixGap (operator.kept around.item False) (operand.calm False),
          (operand.calm False).el (around.next operator.trails 1)
        ])
        around.item
        byComputing
        (goodWithin (Prefix operator operand) good)
        (prefixKept operator operand around around.item byComputing
          (goodWithin operand (prefixGood operator operand good))
          (below => elCalm operand below (prefixGood operator operand good)))
    | Infix kind left operator right =>
      match kind with
        | InfixBinary =>
          framedCalm
            (Infix InfixBinary left operator right)
            around
            (chain (Infix InfixBinary left operator right).chainLevel left operator right { around | hoisted = True })
            (chain
              (Infix InfixBinary left operator right).chainLevel
              (left.calm around.item)
              (operator.kept False False)
              (right.calm False)
              { around | hoisted = True })
            around.item
            byComputing
            (goodWithin (Infix InfixBinary left operator right) good)
            (chainKept
              (Infix InfixBinary left operator right).chainLevel
              left
              operator
              right
              { around | hoisted = True }
              (binaryGoodLeft left operator right good)
              (binaryGoodRight left operator right good))
        | InfixArrow =>
          framedCalm
            (Infix InfixArrow left operator right)
            around
            (chain (Infix InfixArrow left operator right).chainLevel left operator right { around | hoisted = True })
            (chain
              (Infix InfixArrow left operator right).chainLevel
              (left.calm around.item)
              (operator.kept False False)
              (right.calm False)
              { around | hoisted = True })
            around.item
            byComputing
            (goodWithin (Infix InfixArrow left operator right) good)
            (chainKept
              (Infix InfixArrow left operator right).chainLevel
              left
              operator
              right
              { around | hoisted = True }
              (arrowGoodLeft left operator right good)
              (arrowGoodRight left operator right good))
        | _ => cases
    | Tuple open items comma close =>
      framedCalm
        (Tuple open items comma close)
        around
        (commaBracket (list := False) open items close { around | hoisted = True })
        (commaBracket
          (list := False)
          (open.kept around.item False)
          (calmAll True items)
          (close.kept False True)
          { around | hoisted = True })
        around.item
        byComputing
        (goodWithin (Tuple open items comma close) good)
        (Eq.cong
          (doc => Doc.group doc)
          (bracketKept False open items close
            { around | hoisted = True }
            around.item
            byComputing
            (tupleGood open items comma close good)
            (tupleCloses open items comma close good)
            (allElKept items (tupleGood open items comma close good))))
    | ListOf open items comma close =>
      framedCalm
        (ListOf open items comma close)
        around
        (commaBracket (list := True) open items close { around | hoisted = True })
        (commaBracket (list := True) (open.kept around.item False) (calmItems items) (close.kept False True) { around |
          hoisted = True
        })
        around.item
        byComputing
        (goodWithin (ListOf open items comma close) good)
        (Eq.cong
          (doc => Doc.group doc)
          (bracketKept True open items close
            { around | hoisted = True }
            around.item
            byComputing
            (listGood open items comma close good)
            (listCloses open items comma close good)
            (allElKept items (listGood open items comma close good))))
    | App head arguments =>
      framedCalm
        (App head arguments)
        around
        (appDocs head arguments { around | hoisted = True }).doc
        (appDocs (head.calm around.item) (calmAll False arguments) { around | hoisted = True }).doc
        around.item
        byComputing
        (goodWithin (App head arguments) good)
        (Eq.cong
          (applied => applied.doc)
          (appKept head arguments
            { around | hoisted = True }
            (appGoodHead head arguments good)
            (appGoodArguments head arguments good)))

theorem allElKept ∀ (items: List Expr) (good: allGood items = True): AllElKept items := match items with
  | [] => byComputing
  | [first, ..rest] => ((below => elCalm first below (allGoodHead rest good)), (allElKept rest (allGoodTail rest good)))

--| A call's last argument and its hug are the same for the calm argument.
--|
--| Proof idea: Cases on the argument as `lastArgument` has them: a tuple or list hugs (`huggedKept`); a bracketed
--| lambda or block can't be in the slice; any other is its element (`elCalm`).
theorem lastArgumentKept ∀ (argument: Expr) (around: Around)
    (good: argument.good = True):
    lastArgument (argument.calm around.item) around = lastArgument argument around :=
  match argument with
    | Tuple open items comma close =>
      huggedKept False open items close around around.item byComputing
        (tupleGood open items comma close good)
        (tupleCloses open items comma close good)
        (allElKept items (tupleGood open items comma close good))
    | ListOf open items comma close =>
      huggedKept True open items close around around.item byComputing
        (listGood open items comma close good)
        (listCloses open items comma close good)
        (allElKept items (listGood open items comma close good))
    | Paren open inner close =>
      match inner with
        | Binding _ _ _ _ _ => cases
        | Block _ _ _ => cases
        | _ => Eq.cong (doc => (doc, None)) (elCalm (Paren open inner close) around good)
    | Record _ _ _ _ _ => cases
    | _ => Eq.cong (doc => (doc, None)) (elCalm argument around good)

--| The documents of a call's arguments are the same for the calm arguments.
--|
--| Proof idea: Induction on the arguments; each is its element (`elCalm`) after the one before (same trailing
--| comment, `trailsCalm`), and the last is `lastArgumentKept`.
theorem argumentDocsKept ∀ (arm: Bool) (previous previous': Expr) (at: Nat) (arguments: List Expr)
    (sameTrails: previous'.trails = previous.trails)
    (good: allGood arguments = True):
    argumentDocs arm previous' at (calmAll False arguments) = argumentDocs arm previous at arguments :=
  match arguments with
    | [] => byComputing
    | [argument] =>
      rewrite sameTrails then
        Eq.cong
          (last => ([], Some last))
          (lastArgumentKept argument
            { before = previous.trails, hoisted = False, item = False, at, inArm = arm }
            (allGoodHead [] good))
    | [argument, ..rest] =>
      rewrite sameTrails,
          sizeCalm False (goodWithin argument (allGoodHead rest good)),
          argumentDocsKept arm argument
            (argument.calm False)
            (at + argument.size)
            rest
            (trailsCalm False (goodWithin argument (allGoodHead rest good)))
            (allGoodTail rest good),
          elCalm argument
            { before = previous.trails, hoisted = False, item = False, at, inArm = arm }
            (allGoodHead rest good)

theorem takeWithin ∀ (items: List Expr) (count: Nat)
    (within: allWithin1 items = True):
    allWithin1 (items.take count) = True :=
  match items, count with
    | [], Zero | Succ _ => byComputing
    | [first, ..rest], Zero => byComputing
    | [first, ..rest], Succ less => Bool.andIntro (Bool.andLeft within) (takeWithin rest less (Bool.andRight within))

--| A call's document is the same for the calm head and arguments.
--|
--| Proof idea: Each fact `appDocs` reads is the same: the head's element, the arguments' documents (`argumentDocsKept`), how many stay on the line and where comments sit (`keptFrontKept`, `commentBetweenKept`, `takeCalm`).
theorem appKept ∀ (head: Expr) (arguments: List Expr) (around: Around)
    (headGood: head.good = True)
    (argumentsGood: allGood arguments = True):
    appDocs (head.calm around.item) (calmAll False arguments) around = appDocs head arguments around :=
  let within := allGoodWithin arguments argumentsGood
  let sameTrails := trailsCalm around.item (goodWithin head headGood)
  rewrite elCalm head around headGood,
      sizeCalm around.item (goodWithin head headGood),
      argumentDocsKept around.inArm head
        (head.calm around.item)
        (around.at + head.size)
        arguments
        sameTrails
        argumentsGood,
      keptFrontKept head (head.calm around.item) arguments sameTrails within,
      commentBetweenKept head (head.calm around.item) arguments sameTrails within,
      takeCalm arguments False (keptFront head arguments),
      commentBetweenKept head
        (head.calm around.item)
        (arguments.take (keptFront head arguments))
        sameTrails
        (takeWithin arguments (keptFront head arguments) within)

-- The body after `:=`.

theorem matchedNone ∀ (value: Expr) (inside: Around) (within: value.within1 = True): value.matchedParts inside = None :=
  match value with
    | Match _ _ _ _ => cases
    | _ => byComputing

theorem lambdaHugNone ∀ (value: Expr) (semi: Bool) (inside: Around) (doc: Doc)
    (within: value.within1 = True):
    value.lambdaHug semi inside doc = None :=
  match value with
    | Binding _ _ _ _ _ | Calc _ _ _ => cases
    | _ => byComputing

theorem valueElPlain ∀ (value: Expr) (around: Around) (semi: Bool)
    (within: value.within1 = True):
    valueEl value around semi = value.el around :=
  match value with
    | Binding _ _ _ _ _ => cases
    | _ => byComputing

theorem opensCalm ∀ (value: Expr) (item: Bool)
    (within: value.within1 = True):
    (value.calm item).opensBracket = value.opensBracket :=
  match value with
    | Atom _ _ | Paren _ _ _ | Tuple _ _ _ _ | ListOf _ _ _ _ | App _ _ => byComputing
    | Infix kind left operator right =>
      match kind with
        | InfixBinary => byComputing
        | InfixArrow => byComputing
        | _ => cases
    | Prefix operator operand => byComputing

theorem isBlockCalm ∀ (value: Expr) (item: Bool)
    (within: value.within1 = True):
    (value.calm item).isBlock = value.isBlock :=
  match value with
    | Atom _ _ | Paren _ _ _ | Tuple _ _ _ _ | ListOf _ _ _ _ | App _ _ => byComputing
    | Infix kind left operator right =>
      match kind with
        | InfixBinary => byComputing
        | InfixArrow => byComputing
        | _ => cases
    | Prefix operator operand => byComputing

theorem callHugKept ∀ (value: Expr) (inside: Around)
    (good: value.good = True):
    (value.calm inside.item).callHug inside = value.callHug inside :=
  match value with
    | App head arguments =>
      Eq.cong
        (applied => applied.hug)
        (appKept head arguments inside (appGoodHead head arguments good) (appGoodArguments head arguments good))
    | _ => byComputing

theorem matchedCalm ∀ (value: Expr) (item: Bool) (inside: Around)
    (within: value.within1 = True):
    (value.calm item).matchedParts inside = None :=
  match value with
    | Match _ _ _ _ => cases
    | _ => byComputing

theorem lambdaHugCalm ∀ (value: Expr) (item semi: Bool) (inside: Around) (doc: Doc)
    (within: value.within1 = True):
    (value.calm item).lambdaHug semi inside doc = None :=
  match value with
    | Binding _ _ _ _ _ | Calc _ _ _ => cases
    | _ => byComputing

theorem valueElKept ∀ (value: Expr) (around: Around) (semi: Bool)
    (good: value.good = True):
    valueEl (value.calm around.item) around semi = valueEl value around semi :=
  match value with
    | Binding _ _ _ _ _ => cases
    | _ => elCalm value around good

theorem bodyAfterKept ∀ (value: Expr) (assign assign': Word) (around: Around) (semi: Bool)
    (good: value.good = True)
    (sameTrails: assign'.trails = assign.trails):
    bodyAfter (value.calm around.item) assign' around semi = bodyAfter value assign around semi :=
  let within := goodWithin value good
  rewrite matchedCalm value around.item { around | hoisted = True } within,
      matchedNone value { around | hoisted = True } within,
      valueElKept value around semi good,
      sameTrails,
      notedCalm value around.item within,
      isBlockCalm value around.item within,
      callHugKept value { around | hoisted = True } good,
      opensCalm value around.item within,
      lambdaHugCalm value around.item semi { around | hoisted = True } (valueEl value around semi) within,
      lambdaHugNone value semi { around | hoisted = True } (valueEl value around semi) within

-- Declarations.

theorem anyTrailsAlike ∀ (before after: List Word)
    (alike: AllAlike before after):
    before.any Word.trails = after.any Word.trails :=
  match before, after, alike with
    | [], [], _ => byComputing
    | [first, ..more], [second, ..others], (same, rest) =>
      rewrite alikeTrails first second same, anyTrailsAlike more others rest

theorem layoutBodyFalse ∀ (value: Expr) (within: value.within1 = True): value.layoutBody = False := match value with
  | Atom _ _ | Paren _ _ _ | Tuple _ _ _ _ | ListOf _ _ _ _ | App _ _ => byComputing
  | Infix kind left operator right =>
    match kind with
      | InfixBinary => byComputing
      | InfixArrow => byComputing
      | _ => cases
  | Prefix operator operand => byComputing

theorem layoutBodyCalm ∀ (value: Expr) (item: Bool)
    (within: value.within1 = True):
    (value.calm item).layoutBody = False :=
  match value with
    | Atom _ _ | Paren _ _ _ | Tuple _ _ _ _ | ListOf _ _ _ _ | App _ _ => byComputing
    | Infix kind left operator right =>
      match kind with
        | InfixBinary => byComputing
        | InfixArrow => byComputing
        | _ => cases
    | Prefix operator operand => byComputing

--| `defDoc` of a header with no parameters, written out.
def plainDef (keyword: Comments) (name: Word) (colon: Comments) (result: Expr) (colonEq: Comments) (value: Expr): Doc :=
  let start: Around := { before = False, hoisted = True, item = False, at = 0, inArm = False }
  let keywordWord := fixedWord "def" keyword
  let colonWord := fixedWord ":" colon
  let assign := fixedWord ":=" colonEq
  let headWords := [keywordWord, name]
  let colonAround := start.next (trailsBack headWords.reverse) 2
  let typeDoc := result.el (start.next colonWord.trails 3)
  let headDoc := spaced (headDocs start headWords)
  let typed := if colonWord.trails then [Nest 4 (Doc.concat [HardLine, typeDoc])] else [Doc.text " ", Nest 4 typeDoc]
  let headerDoc := Doc.concat ([headDoc, colonWord.leaf colonAround 2] ++ typed)
  let inside :=
    (headWords.reverse.drop 1 |> .any Word.trails)
      || colonWord.trails
      || (result.words.reverse.drop 1 |> .any Word.trails)
      || (value.layoutBody && (lastCode headWords).trails)
  let body := bodyAfter value assign (start.next assign.trails (4 + result.size)) False
  defFrom headerDoc
    (headerDoc.forcesBreak || inside)
    (assign.leaf (start.next result.trails (3 + result.size)) (3 + result.size))
    body.fst
    body.snd

--| `defDoc` of a header with no parameters is `plainDef`.
--|
--| Proof idea: By computing.
theorem plainDefIs ∀ (keyword: Comments) (name: Word) (colon: Comments) (result: Expr)
    (colonEq: Comments) (value: Expr):
    defDoc
      {
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
      }
      colonEq
      value
      = plainDef keyword name colon result colonEq value :=
  byComputing

theorem defFromCong ∀
    (headerDoc headerDoc' assignDoc assignDoc' below below' choice choice': Doc) (breaks breaks': Bool)
    (sameHeader: headerDoc = headerDoc')
    (sameBreaks: breaks = breaks')
    (sameAssign: assignDoc = assignDoc')
    (sameBelow: below = below')
    (sameChoice: choice = choice'):
    defFrom headerDoc breaks assignDoc below choice = defFrom headerDoc' breaks' assignDoc' below' choice' :=
  rewrite sameHeader, sameBreaks, sameAssign, sameBelow, sameChoice

theorem leafCong ∀ (word: Word) (around around': Around) (key key': Nat)
    (sameAround: around = around')
    (sameKey: key = key'):
    word.leaf around key = word.leaf around' key' :=
  rewrite sameAround, sameKey

theorem breaksCong ∀ (headerDoc headerDoc': Doc) (inside inside': Bool)
    (sameHeader: headerDoc = headerDoc')
    (sameInside: inside = inside'):
    (headerDoc.forcesBreak || inside) = (headerDoc'.forcesBreak || inside') :=
  rewrite sameHeader, sameInside

--| Whether a header holds a comment, as `defDoc` asks, is the same for the calm header and body.
--|
--| Proof idea: The words of the type are alike (`anyTrailsAlike` on their reverse, dropped by one), and no value in
--| the slice lays out its body (`layoutBodyFalse`, `layoutBodyCalm`).
theorem plainInsideKept ∀ (keyword: Comments) (name: Word) (colon: Comments) (result value: Expr)
    (resultGood: result.good = True)
    (valueGood: value.good = True):
    (([fixedWord "def" keyword, name.kept False False].reverse.drop 1 |> .any Word.trails)
      || (fixedWord ":" (colon.kept False False)).trails
      || ((result.calm False).words.reverse.drop 1 |> .any Word.trails)
      || ((value.calm False).layoutBody && (lastCode [fixedWord "def" keyword, name.kept False False]).trails))
      = (([fixedWord "def" keyword, name].reverse.drop 1 |> .any Word.trails)
        || (fixedWord ":" colon).trails
        || (result.words.reverse.drop 1 |> .any Word.trails)
        || (value.layoutBody && (lastCode [fixedWord "def" keyword, name]).trails)) :=
  rewrite (anyTrailsAlike
        (result.words.reverse.drop 1)
        ((result.calm False).words.reverse.drop 1)
        (allAlikeDrop result.words.reverse
          (result.calm False).words.reverse
          1
          (allAlikeReverse result.words
            (result.calm False).words
            (wordsCalm result False (goodWithin result resultGood))))).flipped,
      layoutBodyCalm value False (goodWithin value valueGood),
      layoutBodyFalse value (goodWithin value valueGood)

--| The rules' definition is the same for the calm header and body.
--|
--| Proof idea: `defFrom` takes the header, whether it breaks, the `:=` and the body's two forms; each is the same
--| (the name's and `:=`'s `leafKept`, the type's `elCalm`, the held-comment test by `plainInsideKept`, the body by
--| `bodyAfterKept`) and `defFromCong` joins them.
theorem plainDefKept ∀ (keyword: Comments) (name: Word) (colon: Comments) (result: Expr)
    (colonEq: Comments) (value: Expr)
    (resultGood: result.good = True)
    (valueGood: value.good = True):
    plainDef keyword
      (name.kept False False)
      (colon.kept False False)
      (result.calm False)
      (colonEq.kept False False)
      (value.calm False)
      = plainDef keyword name colon result colonEq value :=
  let start: Around := { before = False, hoisted = True, item = False, at = 0, inArm = False }
  let within := goodWithin result resultGood
  let colonWord := fixedWord ":" colon
  let assign := fixedWord ":=" colonEq
  let typeEq := elCalm result (start.next colonWord.trails 3) resultGood
  let headEq: spaced (headDocs start [fixedWord "def" keyword, name.kept False False])
    = spaced (headDocs start [fixedWord "def" keyword, name]) :=
    Eq.cong
      (docs => spaced docs)
      (list2 byComputing
        (leafKept name (start.next (fixedWord "def" keyword).trails 1) 1 False False byComputing byComputing))
  let leafEq :=
    leafKept colonWord (start.next (trailsBack [name, fixedWord "def" keyword]) 2) 2 False False byComputing byComputing
  let typedEq :=
    Eq.cong
      (typed => if colonWord.trails then [Nest 4 (Doc.concat [HardLine, typed])] else [Doc.text " ", Nest 4 typed])
      typeEq
  let headerEq := concatCong _ _ (appendCong _ _ _ _ (list2 headEq leafEq) typedEq)
  let aroundEq :=
    nextEq start
      (fixedWord ":=" (colonEq.kept False False)).trails
      assign.trails
      (4 + (result.calm False).size)
      (4 + result.size)
      byComputing
      (Eq.cong (size => 4 + size) (sizeCalm False within))
  let bodyEq :=
    Eq.trans
      (Eq.cong
        (around => bodyAfter (value.calm False) (fixedWord ":=" (colonEq.kept False False)) around False)
        aroundEq)
      (bodyAfterKept value assign
        (fixedWord ":=" (colonEq.kept False False))
        (start.next assign.trails (4 + result.size))
        False
        valueGood
        byComputing)
  let assignEq: (fixedWord ":=" (colonEq.kept False False)).leaf
    (start.next (result.calm False).trails (3 + (result.calm False).size))
    (3 + (result.calm False).size)
    = assign.leaf (start.next result.trails (3 + result.size)) (3 + result.size) :=
    Eq.trans
      (leafCong
        (fixedWord ":=" (colonEq.kept False False))
        (start.next (result.calm False).trails (3 + (result.calm False).size))
        (start.next result.trails (3 + result.size))
        (3 + (result.calm False).size)
        (3 + result.size)
        (nextEq start
          (result.calm False).trails
          result.trails
          (3 + (result.calm False).size)
          (3 + result.size)
          (trailsCalm False within)
          (Eq.cong (size => 3 + size) (sizeCalm False within)))
        (Eq.cong (size => 3 + size) (sizeCalm False within)))
      (leafKept assign
        (start.next result.trails (3 + result.size))
        (3 + result.size)
        False
        False
        byComputing
        byComputing)
  defFromCong _ _ _ _ _ _ _ _ _ _ headerEq
    (breaksCong _ _ _ _ headerEq (plainInsideKept keyword name colon result value resultGood valueGood))
    assignEq
    (Eq.cong (pair => pair.fst) bodyEq)
    (Eq.cong (pair => pair.snd) bodyEq)

--| A definition's document is the same for the calm header and body.
--|
--| Proof idea: `plainDefIs` on both sides and `plainDefKept` between.
theorem defDocKept ∀ (header: Header) (colonEq: Comments) (value: Expr)
    (within: header.within1 = True)
    (resultGood: header.result.good = True)
    (valueGood: value.good = True):
    defDoc header.calm (colonEq.kept False False) (value.calm False) = defDoc header colonEq value :=
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
      calc defDoc header.calm (colonEq.kept False False) (value.calm False)
        _ = plainDef keyword
            (name.kept False False)
            (colon.kept False False)
            (result.calm False)
            (colonEq.kept False False)
            (value.calm False) :=
          plainDefIs keyword
            (name.kept False False)
            (colon.kept False False)
            (result.calm False)
            (colonEq.kept False False)
            (value.calm False)
        _ = plainDef keyword name colon result colonEq value :=
          plainDefKept keyword name colon result colonEq value resultGood valueGood
        _ = defDoc header colonEq value := (plainDefIs keyword name colon result colonEq value).flipped

-- Declarations and files.

theorem withinAllCalm ∀ (items: List Expr) (item: Bool)
    (within: allWithin1 items = True):
    allWithin1 (calmAll item items) = True :=
  match items with
    | [] => byComputing
    | [first, ..rest] =>
      Bool.andIntro (withinCalm first item (Bool.andLeft within)) (withinAllCalm rest item (Bool.andRight within))

theorem withinLeadCalm ∀ (items: List Expr) (within: allWithin1 items = True): allWithin1 (calmLead items) = True :=
  match items with
    | [] => byComputing
    | [first, ..rest] =>
      Bool.andIntro (withinCalm first False (Bool.andLeft within)) (withinAllCalm rest True (Bool.andRight within))

--| `calm` keeps a tree in the slice.
--|
--| Proof idea: Induction on the expression, with the list lemmas for tuples and lists.
theorem withinCalm ∀ (expr: Expr) (item: Bool) (within: expr.within1 = True): (expr.calm item).within1 = True :=
  match expr with
    | Atom kind word => within
    | Paren open inner close => withinCalm inner False within
    | Tuple open items comma close => withinAllCalm items True within
    | ListOf open items comma close =>
      match items.all Expr.plainItem with
        | True => withinLeadCalm items within
        | False => withinAllCalm items True within
    | App head arguments =>
      Bool.andIntro (withinCalm head item (Bool.andLeft within)) (withinAllCalm arguments False (Bool.andRight within))
    | Infix kind left operator right =>
      match kind with
        | InfixBinary =>
          Bool.andIntro
            (withinCalm left item (Bool.andLeft within))
            (Bool.andIntro
              (withinCalm right False (Bool.andLeft (Bool.andRight within)))
              (Bool.andRight (Bool.andRight within)))
        | InfixArrow =>
          Bool.andIntro
            (withinCalm left item (Bool.andLeft within))
            (Bool.andIntro
              (withinCalm right False (Bool.andLeft (Bool.andRight within)))
              (Bool.andRight (Bool.andRight within)))
        | _ => cases
    | Prefix operator operand => Bool.andIntro (withinCalm operand False (Bool.andLeft within)) (Bool.andRight within)

theorem parenCloser ∀ (text: Text) (is: (text == ")") = True): isCloserText text = True := rewrite is

theorem closerOkExample: (!True || isCloserText ")") = True := closerOk (fixedWord ")" Comments.none) byComputing

theorem bracketCloser ∀ (text: Text) (is: (text == "]") = True): isCloserText text = True := match text == ")" with
  | True => byComputing
  | False => rewrite is

theorem allLexicalClosed ∀ (items: List Expr) (lexical: allLexical items = True): allClosed items = True :=
  match items with
    | [] => byComputing
    | [first, ..rest] =>
      Bool.andIntro (lexicalClosed first (Bool.andLeft lexical)) (allLexicalClosed rest (Bool.andRight lexical))

--| A tree whose words lex has closers for its brackets' last words.
--|
--| Proof idea: Induction on the expression; a bracket's `lexical` says its closer's text is `)` or `]`.
theorem lexicalClosed ∀ (expr: Expr) (lexical: expr.lexical = True): expr.closed = True := match expr with
  | Atom kind word => byComputing
  | Paren open inner close =>
    Bool.andIntro
      (parenCloser close.text (Bool.andLeft (Bool.andRight lexical)))
      (lexicalClosed inner (Bool.andRight (Bool.andRight lexical)))
  | Tuple open items comma close =>
    Bool.andIntro
      (parenCloser close.text (Bool.andLeft (Bool.andRight lexical)))
      (allLexicalClosed items (Bool.andRight (Bool.andRight lexical)))
  | ListOf open items comma close =>
    Bool.andIntro
      (bracketCloser close.text (Bool.andLeft (Bool.andRight lexical)))
      (allLexicalClosed items (Bool.andRight (Bool.andRight lexical)))
  | App head arguments =>
    Bool.andIntro (lexicalClosed head (Bool.andLeft lexical)) (allLexicalClosed arguments (Bool.andRight lexical))
  | Infix kind left operator right =>
    Bool.andIntro
      (lexicalClosed left (Bool.andLeft lexical))
      (lexicalClosed right (Bool.andRight (Bool.andRight lexical)))
  | Prefix operator operand => lexicalClosed operand (Bool.andRight lexical)

theorem headerCalmWithin ∀ (header: Header) (within: header.within1 = True): header.calm.within1 = True :=
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
      Bool.andIntro
        (rewrite Word.keptNameWithin1 name False False then Bool.andLeft within)
        (withinCalm result False (Bool.andRight within))

theorem declCalmWithin ∀ (decl: Decl) (within: decl.within1 = True): decl.calm.within1 = True := match decl with
  | Definition [] header (Assigned colonEq value) =>
    Bool.andIntro (headerCalmWithin header (Bool.andLeft within)) (withinCalm value False (Bool.andRight within))

theorem declDocCalm ∀ (decl: Decl)
    (within: decl.within1 = True)
    (lexical: decl.lexical = True):
    decl.calm.doc1 = decl.doc1 :=
  match decl with
    | Definition [] header (Assigned colonEq value) =>
      Eq.cong
        (doc => Some doc)
        (defDocKept header colonEq value
          (Bool.andLeft within)
          (Bool.andIntro
            (headerResultWithin header (Bool.andLeft within))
            (lexicalClosed header.result (Bool.andLeft (Bool.andRight lexical))))
          (Bool.andIntro (Bool.andRight within) (lexicalClosed value (Bool.andRight (Bool.andRight lexical)))))

theorem declPrintedCalm ∀ (decl: Decl)
    (within: decl.within1 = True)
    (lexical: decl.lexical = True):
    decl.calm.printed1 = decl.printed1 :=
  rewrite declCalmWithin decl within, within, declDocCalm decl within lexical

theorem firstCommentsCalm ∀ (decl: Decl) (within: decl.within1 = True): decl.calm.firstComments = decl.firstComments :=
  match decl with | Definition [] header (Assigned colonEq value) => byComputing

theorem printDeclsCalm ∀ (output: Output) (decls: List Decl)
    (within: decls.all Decl.within1 = True)
    (lexical: decls.all Decl.lexical = True):
    printDecls Decl.printed1 output (decls.map Decl.calm) = printDecls Decl.printed1 output decls :=
  match decls with
    | [] => byComputing
    | [decl, ..rest] =>
      rewrite firstCommentsCalm decl (Bool.andLeft within),
          declPrintedCalm decl (Bool.andLeft within) (Bool.andLeft lexical) then
        printDeclsCalm _ rest (Bool.andRight within) (Bool.andRight lexical)

--| `calmPrints`: the rules print a slice 1 file and its `calm` file the same text.
--|
--| Proof idea: `calm` clears only flags the rules never read, so every rule's document is the same before and after
--| (`elCalm`: by induction on the expression, with each rule's lemma taking the induction hypothesis for its
--| parts; `defDocKept` for the declaration), and the file loop reads the first token's comments and the end's
--| notes, which `calm` keeps.
theorem calmPrints ∀ (file: SourceFile)
    (within: file.within1 = True)
    (lexical: file.lexical = True):
    file.calm.printed1 = file.printed1 :=
  rewrite printDeclsCalm { pieces = [], empty = True } file.decls within lexical

theorem bracketCloserExample: isCloserText "]" = True := bracketCloser "]" byComputing
