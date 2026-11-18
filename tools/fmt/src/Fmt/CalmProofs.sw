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
import Syntax (Comments, Decl, DefBody, Expr, Header, InfixKind, Note, SourceFile, Tok, Word)
import Fmt (..)

-- A word and its calm word.

--| The pieces of a word the rules read besides the flags `kept` may clear.
def Word.alike (before after: Word): Prop :=
  before.text = after.text
    ∧ before.comments.after = after.comments.after
    ∧ before.comments.above.isEmpty = after.comments.above.isEmpty

def AllAlike: List Word → List Word → Prop
  | [], [] => True
  | [before, ..more], [after, ..later] => before.alike after ∧ AllAlike more later
  | _, _ => False

theorem keptAlike ∀ (word: Word) (item closer: Bool): word.alike (word.kept item closer) := match word with
  | { text, comments = { above = [], after, blankBefore } } => (byComputing, byComputing, byComputing)
  | { text, comments = { above = [first, ..rest], after, blankBefore } } => (byComputing, byComputing, byComputing)

theorem alikeTrails ∀ (before after: Word) (alike: before.alike after): before.trails = after.trails := match alike with
  | (_, same, _) => Eq.cong (comment => comment.isSome) same

theorem alikeNoted ∀ (before after: Word) (alike: before.alike after): before.noted = after.noted := match alike with
  | (_, _, same) => Eq.cong (empty => !empty) same

theorem alikeCloser ∀ (before after: Word) (alike: before.alike after):
    isCloserText before.text = isCloserText after.text :=
  match alike with | (same, _, _) => Eq.cong (text => isCloserText text) same

theorem alikeRefl ∀ (word: Word): word.alike word := (byComputing, byComputing, byComputing)

theorem allAlikeRefl ∀ (words: List Word): AllAlike words words := match words with
  | [] => byComputing
  | [word, ..more] => (alikeRefl word, (allAlikeRefl more))

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
  | Tuple _ items _ close => isCloserText close.text && allClosed items
  | ListOf _ items _ close => isCloserText close.text && allClosed items
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
            ((keptAlike operator False False, wordsCalm right False (Bool.andRight within)))
        | InfixArrow =>
          allAlikeAppend left.words
            (left.calm item).words
            [operator, ..right.words]
            [operator.kept False False, ..(right.calm False).words]
            (wordsCalm left item (Bool.andLeft within))
            ((keptAlike operator False False, wordsCalm right False (Bool.andRight within)))
        | _ => cases
    | Prefix operator operand => ((keptAlike operator item False, wordsCalm operand False within))

-- What the rules read of a token's flags.

--| `calm` keeps what `Word.leading` reads: for a token that starts an item (`item`) or isn't a closer, the flags it
--| reads, and for a closer none.
theorem leadingKept ∀ (word: Word) (around: Around) (key: Nat) (item closer: Bool)
    (same: around.item = item)
    (closes: (!closer || isCloserText word.text) = True):
    (word.kept item closer).leading around key = word.leading around key :=
  match word, around.hoisted with
    | { text, comments = { above, after, blankBefore } }, True => byComputing
    | { text, comments = { above = [], after, blankBefore } }, False =>
      rewrite same then
        match item, blankBefore with
          | True, True => byComputing
          | True, False => byComputing
          | False, True => byComputing
          | False, False => byComputing
    | { text, comments = { above = [first, ..rest], after, blankBefore } }, False =>
      match isCloserText text with
        | True => byComputing
        | False =>
          match closer with
            | False =>
              rewrite same then
                match item, blankBefore, first.blankBefore with
                  | True, True, True => byComputing
                  | True, True, False => byComputing
                  | True, False, True => byComputing
                  | True, False, False => byComputing
                  | False, True, True => byComputing
                  | False, True, False => byComputing
                  | False, False, True => byComputing
                  | False, False, False => byComputing

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
theorem openingKept ∀ (open close: Word) (around: Around) (item: Bool)
    (same: around.item = item):
    (open.kept item False).opening around (close.kept False True) = open.opening around close :=
  match open, close with
    | { text, comments = { above = [], after, blankBefore } }, {
        text = other,
        comments = { above = [], after = later, blankBefore = blank }
      } =>
      rewrite leadingKept
        { text, comments = { above = [], after, blankBefore } }
        around
        around.at
        item
        False
        same
        byComputing
    | { text, comments = { above = [], after, blankBefore } }, {
        text = other,
        comments = { above = [first, ..rest], after = later, blankBefore = blank }
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
        comments = { above = [], after = later, blankBefore = blank }
      } =>
      rewrite leadingKept
        { text, comments = { above = [first, ..more], after, blankBefore } }
        around
        around.at
        item
        False
        same
        byComputing
    | { text, comments = { above = [first, ..more], after, blankBefore } }, {
        text = other,
        comments = { above = [second, ..rest], after = later, blankBefore = blank }
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

theorem sizeCalm ∀ (expr: Expr) (item: Bool) (within: expr.within1 = True): (expr.calm item).size = expr.size :=
  (allAlikeLength expr.words (expr.calm item).words (wordsCalm expr item within)).flipped

theorem trailsCalm ∀ (expr: Expr) (item: Bool) (within: expr.within1 = True): (expr.calm item).trails = expr.trails :=
  (trailsBackAlike expr.words.reverse
    (expr.calm item).words.reverse
    (allAlikeReverse expr.words (expr.calm item).words (wordsCalm expr item within))).flipped

theorem holdsCalm ∀ (expr: Expr) (item: Bool)
    (within: expr.within1 = True):
    (expr.calm item).holdsTrailingComment = expr.holdsTrailingComment :=
  rewrite trailsCalm expr item within, countTrailsAlike expr.words (expr.calm item).words (wordsCalm expr item within)

theorem notedCalm ∀ (expr: Expr) (item: Bool) (within: expr.within1 = True): (expr.calm item).noted = expr.noted :=
  rewrite firstCalm expr item within then
    (alikeNoted expr.firstWord (expr.firstWord.kept item False) (keptAlike expr.firstWord item False)).flipped

theorem keptNoted ∀ (word: Word) (item closer: Bool): (word.kept item closer).noted = word.noted :=
  (alikeNoted word (word.kept item closer) (keptAlike word item closer)).flipped

theorem keptTrails ∀ (word: Word) (item closer: Bool): (word.kept item closer).trails = word.trails := byComputing

theorem plainItemCalm ∀ (expr: Expr) (item: Bool)
    (within: expr.within1 = True):
    (expr.calm item).plainItem = expr.plainItem :=
  match expr with
    | Atom kind word => rewrite keptNoted word item False
    | Paren open inner close => byComputing
    | Tuple open items comma close => byComputing
    | ListOf open items comma close => byComputing
    | App head arguments => byComputing
    | Infix kind left operator right =>
      match kind with
        | InfixBinary => byComputing
        | InfixArrow => byComputing
        | _ => cases
    | Prefix operator operand => byComputing

theorem calmAllEmpty ∀ (items: List Expr) (item: Bool): (calmAll item items).isEmpty = items.isEmpty := match items with
  | [] => byComputing
  | [first, ..rest] => byComputing

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

theorem simpleCalm ∀ (expr: Expr) (item: Bool) (within: expr.within1 = True): (expr.calm item).simple = expr.simple :=
  match expr with
    | Atom kind word => byComputing
    | Paren open inner close => byComputing
    | Tuple open items comma close => calmAllEmpty items True
    | ListOf open items comma close => calmItemsEmpty items
    | App head arguments => byComputing
    | Infix kind left operator right =>
      match kind with
        | InfixBinary => byComputing
        | InfixArrow => byComputing
        | _ => cases
    | Prefix operator operand =>
      match operand with
        | Atom kind word => byComputing
        | Paren open inner close => byComputing
        | Tuple open items comma close => byComputing
        | ListOf open items comma close => byComputing
        | App head arguments => byComputing
        | Infix kind left operator right =>
          match kind with
            | InfixBinary => byComputing
            | InfixArrow => byComputing
            | _ => cases
        | Prefix operator operand => byComputing
        | _ => cases

--| In the slice, with its closers closers.
def Expr.good (expr: Expr): Bool := expr.within1 && expr.closed

def allGood: List Expr → Bool
  | [] => True
  | [expr, ..rest] => expr.good && allGood rest

theorem goodWithin ∀ (expr: Expr) (good: expr.good = True): expr.within1 = True := Bool.andLeft good

theorem goodClosed ∀ (expr: Expr) (good: expr.good = True): expr.closed = True := Bool.andRight good

theorem allGoodWithin ∀ (items: List Expr) (good: allGood items = True): allWithin1 items = True := match items with
  | [] => byComputing
  | [first, ..rest] => Bool.andIntro (goodWithin first (Bool.andLeft good)) (allGoodWithin rest (Bool.andRight good))

-- Chains.

theorem chainLevelCalm ∀ (expr: Expr) (item: Bool)
    (within: expr.within1 = True):
    (expr.calm item).chainLevel = expr.chainLevel :=
  match expr with
    | Atom kind word => byComputing
    | Paren open inner close => byComputing
    | Tuple open items comma close => byComputing
    | ListOf open items comma close => byComputing
    | App head arguments => byComputing
    | Infix kind left operator right =>
      match kind with
        | InfixBinary => byComputing
        | InfixArrow => byComputing
        | _ => cases
    | Prefix operator operand => byComputing

theorem inChainCalm ∀ (expr: Expr) (item: Bool) (level: Option Nat)
    (within: expr.within1 = True):
    (expr.calm item).inChain level = expr.inChain level :=
  match expr with
    | Atom kind word => byComputing
    | Paren open inner close => byComputing
    | Tuple open items comma close => byComputing
    | ListOf open items comma close => byComputing
    | App head arguments => byComputing
    | Infix kind left operator right =>
      match kind with
        | InfixBinary => byComputing
        | InfixArrow => byComputing
        | _ => cases
    | Prefix operator operand => byComputing

theorem opensArmsCalm ∀ (expr: Expr) (item: Bool) (level: Option Nat)
    (within: expr.within1 = True):
    (expr.calm item).opensArms level = expr.opensArms level :=
  match expr with
    | Atom kind word => byComputing
    | Paren open inner close => byComputing
    | Tuple open items comma close => byComputing
    | ListOf open items comma close => byComputing
    | App head arguments => byComputing
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

--| Calm leaves a chain's operator at a place where no item starts, and a prefix operand's too.
theorem nextNoItem ∀ (around: Around) (before: Bool) (skipped: Nat): (around.next before skipped).item = False :=
  byComputing

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
        byComputing
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
    | Block _ _ _ => cases
    | If _ _ _ _ _ _ _ => cases
    | _ => each

-- Documents equal part by part.

theorem concatCong ∀ (docs docs': List Doc) (same: docs = docs'): Doc.concat docs = Doc.concat docs' :=
  Eq.cong (list => Doc.concat list) same

theorem list2 ∀ (a b a' b': Doc) (first: a = a') (second: b = b'): [a, b] = [a', b'] := rewrite first, second

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
            (trailsCalm inner False (goodWithin inner inside))
            (Eq.cong (size => 1 + size) (sizeCalm inner False (goodWithin inner inside))),
          leafKept close
            (around.next inner.trails (1 + inner.size))
            around.at
            False
            True
            byComputing
            (closerOk close closes)))
