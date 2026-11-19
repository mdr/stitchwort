--| Where comments fall among a declaration's tokens, as lists of marks (SW-4107, for `wordsEdgeOneLine1`).
--|
--| `marked` pairs each token of a list of texts with whether a comment came since the token before it. The printed
--| words and the tree's tokens (`Decl.spelt`) agree only once the closers, or once the comments, are left out
--| (`printedSpellsSettled`), so a comment's place is compared over the tokens that are no closers: `spread` carries
--| the marks of the printed tokens over to those, and `spreadMarked` says it gives the marks of the words with the
--| closers left out.

namespace Fmt.NoteMarks
import Std (Bool, DecEq, Eq, List, Nat, Text)
import Syntax (Token)
import Fmt (isCloserText)
import Fmt.SpellProofs (notCloser, notComment)

-- Marks.

--| Each token (a text that is no comment) with whether a comment came since the token before it, or since the
--| start with `pending`.
def marked (pending: Bool): List Text → List (Text, Bool)
  | [] => []
  | [text, ..rest] => if notComment text then [(text, pending), ..marked False rest] else marked True rest

--| `marked`'s marks.
def marks (pending: Bool): List Text → List Bool
  | [] => []
  | [text, ..rest] => if notComment text then [pending, ..marks False rest] else marks True rest

--| Whether a comment came after the last token, or since the start with `pending` if there is none.
def pendingAfter (pending: Bool): List Text → Bool
  | [] => pending
  | [text, ..rest] => if notComment text then pendingAfter False rest else pendingAfter True rest

--| For each marked token that is no closer or comma, whether it or a closer or comma since the last such token had a
--| comment before it.
def spread (pending: Bool): List (Text, Bool) → List Bool
  | [] => []
  | [(text, mark), ..rest] =>
    if notCloser text then [pending || mark, ..spread False rest] else spread (pending || mark) rest

--| Whether some token has a mark.
def anyMarked: List (Text, Bool) → Bool
  | [] => False
  | [(_, mark), ..rest] => mark || anyMarked rest

--| No mark after the first.
def tailQuiet: List Bool → Bool
  | [] => True
  | [_, ..rest] => rest.all (mark => !mark)

--| The first mark, if any, is clear.
def firstQuiet: List Bool → Bool
  | [] => True
  | [mark, .._] => !mark

-- Comments are no closers.

theorem noteNotCloser ∀ (text: Text) (note: notComment text = False): notCloser text = True := match a: text == ")" with
  | True => (Bool.trueNotFalse (rewrite DecEq.sound a at note then note)).impossible
  | False =>
    match b: text == "]" with
      | True => (Bool.trueNotFalse (rewrite DecEq.sound b at note then note)).impossible
      | False =>
        match c: text == "}" with
          | True => (Bool.trueNotFalse (rewrite DecEq.sound c at note then note)).impossible
          | False =>
            match d: text == "," with
              | True => (Bool.trueNotFalse (rewrite DecEq.sound d at note then note)).impossible
              | False => byComputing

-- `spread` of the printed tokens is `marks` of the tokens that are no closers.

theorem orTrue ∀ (a: Bool): (a || True) = True := match a with
  | True => byComputing
  | False => byComputing

theorem orFalse ∀ (a: Bool): (a || False) = a := match a with
  | True => byComputing
  | False => byComputing

--| Marking the tokens, then spreading the marks over those that are no closers, marks the texts with the closers left
--| out.
--|
--| Proof idea: induction on the texts; a comment sets the mark both ways, a token that is no closer gives its mark and
--| clears it, and a closer passes its mark on to the next token that is none.
theorem spreadMarked ∀ (texts: List Text) (acc pending: Bool):
    spread acc (marked pending texts) = marks (acc || pending) (texts.filter notCloser) :=
  match texts with
    | [] => byComputing
    | [text, ..rest] =>
      match note: notComment text with
        | False =>
          let kept: notCloser text = True := noteNotCloser text note
          rewrite kept, spreadMarked rest acc True, orTrue acc
        | True =>
          match closer: notCloser text with
            | True => rewrite spreadMarked rest False False
            | False => rewrite spreadMarked rest (acc || pending) False, orFalse (acc || pending)

-- Splitting marks.

theorem marksAppend ∀ (pending: Bool) (front back: List Text):
    marks pending (front ++ back) = marks pending front ++ marks (pendingAfter pending front) back :=
  match front with
    | [] => byComputing
    | [text, ..rest] =>
      match notComment text with
        | True => rewrite marksAppend False rest back
        | False => marksAppend True rest back

theorem pendingAppend ∀ (pending: Bool) (front back: List Text):
    pendingAfter pending (front ++ back) = pendingAfter (pendingAfter pending front) back :=
  match front with
    | [] => byComputing
    | [text, ..rest] =>
      match notComment text with
        | True => pendingAppend False rest back
        | False => pendingAppend True rest back

theorem lengthMarks ∀ (pending: Bool) (texts: List Text):
    (marks pending texts).length = (texts.filter notComment).length :=
  match texts with
    | [] => byComputing
    | [text, ..rest] =>
      match notComment text with
        | True => rewrite lengthMarks False rest
        | False => lengthMarks True rest

theorem fstMarked ∀ (pending: Bool) (texts: List Text): (marked pending texts).map Pair.fst = texts.filter notComment :=
  match texts with
    | [] => byComputing
    | [text, ..rest] =>
      match notComment text with
        | True => rewrite fstMarked False rest
        | False => fstMarked True rest

theorem lengthSpread ∀ (pending: Bool) (pairs: List (Text, Bool)):
    (spread pending pairs).length = ((pairs.map Pair.fst).filter notCloser).length :=
  match pairs with
    | [] => byComputing
    | [(text, mark), ..rest] =>
      match notCloser text with
        | True => rewrite lengthSpread False rest
        | False => lengthSpread (pending || mark) rest

theorem spreadAppend ∀ (front back: List (Text, Bool))
    (quiet: anyMarked front = False):
    spread False (front ++ back) = spread False front ++ spread False back :=
  match front with
    | [] => byComputing
    | [(text, mark), ..rest] =>
      match mark, quiet with
        | True, never => (Bool.trueNotFalse never).impossible
        | False, quiet =>
          match notCloser text with
            | True => rewrite spreadAppend rest back quiet
            | False => spreadAppend rest back quiet

-- No marks.

--| With no marks, `spread` gives none but perhaps the first, which is `pending`.
theorem spreadQuiet ∀ (pairs: List (Text, Bool))
    (quiet: anyMarked pairs = False):
    (spread False pairs).all (mark => !mark) = True :=
  match pairs with
    | [] => byComputing
    | [(text, mark), ..rest] =>
      match mark, quiet with
        | True, never => (Bool.trueNotFalse never).impossible
        | False, quiet =>
          match notCloser text with
            | True => spreadQuiet rest quiet
            | False => spreadQuiet rest quiet

--| After a token with any mark, no marks give none after the first.
theorem spreadTailQuiet ∀ (pending: Bool) (pairs: List (Text, Bool))
    (quiet: anyMarked pairs = False):
    tailQuiet (spread pending pairs) = True :=
  match pairs with
    | [] => byComputing
    | [(text, mark), ..rest] =>
      match mark, quiet with
        | True, never => (Bool.trueNotFalse never).impossible
        | False, quiet =>
          match notCloser text with
            | True => spreadQuiet rest quiet
            | False => spreadTailQuiet (pending || False) rest quiet

-- Lists.

theorem filterSwap ∀ (p q: Text → Bool) (texts: List Text): (texts.filter p).filter q = (texts.filter q).filter p :=
  match texts with
    | [] => byComputing
    | [text, ..rest] =>
      match p text, q text with
        | True, True => rewrite filterSwap p q rest
        | True, False => filterSwap p q rest
        | False, True => filterSwap p q rest
        | False, False => filterSwap p q rest

theorem appendCancel ∀ (front back front' back': List Bool)
    (length: front.length = front'.length)
    (same: front ++ back = front' ++ back'):
    back = back' :=
  match front, front', length, same with
    | [], [], _, same => same
    | [], [_, .._], never, _ => cases
    | [_, .._], [], never, _ => cases
    | [x, ..xs], [y, ..ys], length, same =>
      appendCancel xs back ys back' (Nat.succInjective length) (Eq.cong ((list: List Bool) => list.drop 1) same)

theorem allSplit ∀ (front back: List Bool)
    (all: (front ++ back).all (mark => !mark) = True):
    front.all (mark => !mark) = True ∧ back.all (mark => !mark) = True :=
  match front with
    | [] => (byComputing, all)
    | [mark, ..rest] =>
      match mark, all with
        | True, never => (Bool.falseNotTrue never).impossible
        | False, all => allSplit rest back all

-- Tokens among comments.

--| Some text is no comment.
def hasToken: List Text → Bool
  | [] => False
  | [text, ..rest] => notComment text || hasToken rest

--| Texts that are all comments.
def allNotes (texts: List Text): Bool := texts.all (text => !notComment text)

theorem marksOfToken ∀ (pending: Bool) (texts: List Text)
    (has: hasToken texts = True):
    ∃ (mark: Bool) (later: List Bool) => marks pending texts = [mark, ..later] :=
  match texts with
    | [text, ..rest] =>
      match notComment text with
        | True => (pending, marks False rest, byComputing)
        | False => marksOfToken True rest has

theorem firstAppend ∀ (pending: Bool) (texts: List Text) (more: List Bool)
    (has: hasToken texts = True):
    firstQuiet (marks pending texts ++ more) = firstQuiet (marks pending texts) :=
  let (mark, later, same) := marksOfToken pending texts has
  rewrite same

theorem tailAppend ∀ (pending: Bool) (texts: List Text) (more: List Bool)
    (has: hasToken texts = True)
    (quiet: tailQuiet (marks pending texts ++ more) = True):
    tailQuiet (marks pending texts) = True ∧ more.all (mark => !mark) = True :=
  let (mark, later, same) := marksOfToken pending texts has
  let split: ((later ++ more).all (mark => !mark)) = True := rewrite same at quiet then quiet
  let (front, back) := allSplit later more split
  (rewrite same then front, back)

theorem quietAll ∀ (marks: List Bool)
    (all: marks.all (mark => !mark) = True):
    firstQuiet marks = True ∧ tailQuiet marks = True :=
  match marks with
    | [] => (byComputing, byComputing)
    | [mark, ..rest] => (Bool.andLeft all, Bool.andRight all)

--| A first token with no mark had no comment waiting.
theorem firstClears ∀ (pending: Bool) (texts: List Text)
    (has: hasToken texts = True)
    (first: firstQuiet (marks pending texts) = True):
    pending = False :=
  match texts with
    | [text, ..rest] =>
      match notComment text with
        | True =>
          match pending, first with
            | False, _ => byComputing
            | True, never => (Bool.falseNotTrue never).impossible
        | False => (Bool.trueNotFalse (firstClears True rest has first)).impossible

theorem marksNotes ∀ (pending: Bool) (texts: List Text) (notes: allNotes texts = True): marks pending texts = [] :=
  match texts with
    | [] => byComputing
    | [text, ..rest] =>
      match note: notComment text with
        | False => marksNotes True rest notes

theorem pendingNotes ∀ (pending: Bool) (texts: List Text)
    (notes: allNotes texts = True):
    pendingAfter pending texts = (pending || !texts.isEmpty) :=
  match texts with
    | [] => rewrite orFalse pending
    | [text, ..rest] =>
      match note: notComment text with
        | False => rewrite pendingNotes True rest notes, orTrue pending

theorem hasNotes ∀ (texts: List Text) (notes: allNotes texts = True): hasToken texts = False := match texts with
  | [] => byComputing
  | [text, ..rest] =>
    match note: notComment text with
      | False => hasNotes rest notes

theorem hasAppendLeft ∀ (front back: List Text) (has: hasToken front = True): hasToken (front ++ back) = True :=
  match front with
    | [text, ..rest] =>
      match notComment text with
        | True => byComputing
        | False => hasAppendLeft rest back has

theorem hasAppendRight ∀ (front back: List Text) (has: hasToken back = True): hasToken (front ++ back) = True :=
  match front with
    | [] => has
    | [text, ..rest] =>
      match notComment text with
        | True => byComputing
        | False => hasAppendRight rest back has

theorem filterNotes ∀ (texts: List Text) (notes: allNotes texts = True): texts.filter notCloser = texts :=
  match texts with
    | [] => byComputing
    | [text, ..rest] =>
      match note: notComment text with
        | False => rewrite noteNotCloser text note, filterNotes rest notes

theorem notesAppend ∀ (front back: List Text)
    (frontNotes: allNotes front = True)
    (backNotes: allNotes back = True):
    allNotes (front ++ back) = True :=
  match front with
    | [] => backNotes
    | [text, ..rest] =>
      match note: notComment text with
        | False => notesAppend rest back frontNotes backNotes

theorem appendCancelFront ∀ (front back front' back': List Bool)
    (length: front.length = front'.length)
    (same: front ++ back = front' ++ back'):
    front = front' :=
  match front, front', length, same with
    | [], [], _, same => byComputing
    | [], [_, .._], never, _ => cases
    | [_, .._], [], never, _ => cases
    | [x, ..xs], [y, ..ys], length, same =>
      let head: x = y := List.consInjectiveHead _ _ _ _ same
      rewrite head,
          appendCancelFront xs back ys back'
            (Nat.succInjective length)
            (Eq.cong ((list: List Bool) => list.drop 1) same)

theorem notesNoTokens ∀ (texts: List Text) (notes: allNotes texts = True): texts.filter notComment = [] :=
  match texts with
    | [] => byComputing
    | [text, ..rest] =>
      match note: notComment text with
        | False => notesNoTokens rest notes

theorem allTexts ∀ (front back: List Text) (p: Text → Bool)
    (frontAll: front.all p = True)
    (backAll: back.all p = True):
    (front ++ back).all p = True :=
  match front with
    | [] => backAll
    | [text, ..rest] => Bool.andIntro (Bool.andLeft frontAll) (allTexts rest back p (Bool.andRight frontAll) backAll)

theorem spreadValue ∀ (pairs: List (Text, Bool))
    (quiet: anyMarked (pairs.drop 1) = False):
    tailQuiet (spread False pairs) = True :=
  match pairs with
    | [] => byComputing
    | [(text, mark), ..rest] =>
      match notCloser text with
        | True => spreadQuiet rest quiet
        | False => spreadTailQuiet (False || mark) rest quiet

theorem noteNotCloserExample: notCloser "-- c" = True := noteNotCloser "-- c" byComputing
