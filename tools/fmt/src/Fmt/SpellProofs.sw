--| `printedSpells` (docs/proposals/self-hosted-fmt-s1-sketch.md §1.5, ticket 18a): the text the rules print spells
--| each token of the tree and its comments, in the tree's order, at any width.
--|
--| A document `Spells` a list of texts when every option of each of its choices has those words (`Uniform`), its
--| closers and trailing comments are of the kinds the rules write (`Marked`), and its words are the texts. The
--| rules' lemmas are one for each function of `Rules.sw` that slice 1 meets; `Std.Doc`'s `printedWords` turns the
--| document's words into the printer's.

namespace Fmt.SpellProofs
import Std (Bool, DecEq, Doc, Eq, List, Nat, Option, Text)
import Std.Doc (..)
import Std.Doc.Proofs (..)
import Syntax (Comments, Decl, DefBody, Expr, Header, InfixKind, Note, SourceFile, Tok, Word)
import Fmt (..)

--| A closer the rules write: a closing bracket or a comma.
def closesText (text: Text): Prop := isCloserText text = True ∨ text = ","

--| A trailing comment the rules write: one rule N left.
def commentsText (text: Text): Prop := commentText text = True

--| `doc` writes `texts`: its words are those texts, whichever option its choices take, and its closers and trailing
--| comments are the rules' kinds.
def Spells (doc: Doc) (texts: List Text): Prop := Uniform doc ∧ Marked closesText commentsText doc ∧ doc.words = texts

def SpellsAll (docs: List Doc) (texts: List Text): Prop :=
  AllUniform docs ∧ AllMarked closesText commentsText docs ∧ wordsAll docs = texts

theorem spellsNil: SpellsAll [] [] := (byComputing, byComputing, byComputing)

theorem spellsCons ∀ (doc: Doc) (docs: List Doc) (texts later: List Text)
    (first: Spells doc texts)
    (rest: SpellsAll docs later):
    SpellsAll [doc, ..docs] (texts ++ later) :=
  match first, rest with
    | (uniform, marked, words), (restUniform, restMarked, restWords) =>
      (((uniform, restUniform)), ((marked, restMarked)), (rewrite words, restWords))

theorem spellsLast ∀ (doc: Doc) (texts: List Text) (only: Spells doc texts): SpellsAll [doc] texts :=
  rewrite <- List.appendNil texts then spellsCons doc [] texts [] only spellsNil

-- Documents that spell.

theorem spellsNothing: Spells Nothing [] := (byComputing, byComputing, byComputing)

theorem spellsLine: Spells Line [] := (byComputing, byComputing, byComputing)

theorem spellsSoftLine: Spells SoftLine [] := (byComputing, byComputing, byComputing)

theorem spellsHardLine: Spells HardLine [] := (byComputing, byComputing, byComputing)

theorem spellsBlank: Spells Blank [] := (byComputing, byComputing, byComputing)

theorem spellsLineStart: Spells LineStart [] := (byComputing, byComputing, byComputing)

theorem spellsLineStartHere: Spells LineStartHere [] := (byComputing, byComputing, byComputing)

theorem spellsBreakParent: Spells BreakParent [] := (byComputing, byComputing, byComputing)

theorem spellsMark ∀ (key: Nat): Spells (Mark key) [] := (byComputing, byComputing, byComputing)

theorem spellsCloserLine ∀ (key: Nat): Spells (CloserLine key) [] := (byComputing, byComputing, byComputing)

--| A text that isn't layout is one word.
theorem spellsText ∀ (text: Text) (real: isLayout text = False): Spells (Doc.text text) [text] :=
  (byComputing, byComputing, rewrite real)

--| A space between tokens is layout.
theorem spellsSpace: Spells (Doc.text " ") [] := (byComputing, byComputing, byComputing)

theorem spellsClosing ∀ (text: Text)
    (real: isLayout text = False) (closes: closesText text):
    Spells (Closing text) [text] :=
  (byComputing, closes, rewrite real)

theorem spellsSuffix ∀ (text: Text)
    (real: isLayout text = False) (comment: commentsText text):
    Spells (LineSuffix text) [text] :=
  (byComputing, comment, rewrite real)

theorem spellsNest ∀ (indent: Nat) (inner: Doc) (texts: List Text)
    (spells: Spells inner texts):
    Spells (Nest indent inner) texts :=
  spells

theorem spellsAlign ∀ (inner: Doc) (texts: List Text) (spells: Spells inner texts): Spells (Align inner) texts := spells

theorem spellsDisplaced ∀ (inner: Doc) (texts: List Text)
    (spells: Spells inner texts):
    Spells (Displaced inner) texts :=
  spells

theorem spellsGroup ∀ (inner: Doc) (texts: List Text) (spells: Spells inner texts): Spells (Doc.group inner) texts :=
  spells

theorem spellsIdGroup ∀ (id: Nat) (inner: Doc) (hard: Bool) (texts: List Text)
    (spells: Spells inner texts):
    Spells (IdGroup id inner hard) texts :=
  spells

theorem spellsFlatten ∀ (inner: Doc) (texts: List Text) (spells: Spells inner texts): Spells (Flatten inner) texts :=
  spells

theorem spellsOneLineBelow ∀ (inner: Doc) (texts: List Text)
    (spells: Spells inner texts):
    Spells (OneLineBelow inner) texts :=
  spells

theorem spellsFill ∀ (items: List Doc) (texts: List Text) (each: SpellsAll items texts): Spells (Fill items) texts :=
  each

--| A document in which an option or branch is as the other: both spell the same.
theorem spellsIfBroken ∀ (id: Nat) (broken flat: Doc) (texts: List Text)
    (whenBroken: Spells broken texts)
    (whenFlat: Spells flat texts):
    Spells (IfBroken id broken flat) texts :=
  match whenBroken, whenFlat with
    | (brokenUniform, brokenMarked, brokenWords), (flatUniform, flatMarked, flatWords) =>
      (((brokenUniform, flatUniform, rewrite flatWords, brokenWords)), ((brokenMarked, flatMarked)), brokenWords)

-- Documents in order.

theorem emptyNoWords ∀ (doc: Doc) (empty: doc.isEmpty = True): doc.words = [] := match doc, empty with
  | Nothing, _ => byComputing

theorem filterWords ∀ (docs: List Doc): wordsAll (docs.filter (doc => not doc.isEmpty)) = wordsAll docs :=
  match docs with
    | [] => byComputing
    | [doc, ..rest] =>
      match empty: doc.isEmpty with
        | True => rewrite emptyNoWords doc empty then filterWords rest
        | False => Eq.cong (later => doc.words ++ later) (filterWords rest)

theorem filterSpells ∀ (docs: List Doc) (texts: List Text)
    (each: SpellsAll docs texts):
    SpellsAll (docs.filter (doc => not doc.isEmpty)) texts :=
  match docs, each with
    | [], each => each
    | [doc, ..rest], ((uniform, restUniform), (marked, restMarked), words) =>
      let (keptUniform, keptMarked, keptWords) :=
        filterSpells rest (wordsAll rest) (restUniform, restMarked, byComputing)
      match empty: doc.isEmpty with
        | True => (keptUniform, keptMarked, Eq.trans keptWords (rewrite emptyNoWords doc empty at words then words))
        | False => (
          (uniform, keptUniform),
          (marked, keptMarked),
          Eq.trans (Eq.cong (later => doc.words ++ later) keptWords) words
        )

theorem spellsConcat ∀ (docs: List Doc) (texts: List Text)
    (each: SpellsAll docs texts):
    Spells (Doc.concat docs) texts :=
  let (keptUniform, keptMarked, keptWords) := filterSpells docs texts each
  match kept: docs.filter (doc => not doc.isEmpty) with
    | [] => (byComputing, byComputing, keptWords)
    | [only] => (keptUniform.left, keptMarked.left, Eq.trans (List.appendNil only.words).flipped keptWords)
    | [first, second, ..rest] => (keptUniform, keptMarked, keptWords)

--| Documents that spell the same texts, each.
def SpellsEach (texts: List Text): List Doc → Prop
  | [] => True
  | [doc, ..docs] => Spells doc texts ∧ SpellsEach texts docs

--| The words of the options of a choice are those of its first, if each spells the same.
theorem sameWordsOf ∀ (texts: List Text) (options: List Doc)
    (each: SpellsEach texts options):
    SameWords texts options :=
  match options, each with
    | [], _ => byComputing
    | [option, ..rest], ((_, _, words), others) => (words, (sameWordsOf texts rest others))

theorem eachUniform ∀ (texts: List Text) (options: List Doc) (each: SpellsEach texts options): AllUniform options :=
  match options, each with
    | [], _ => byComputing
    | [option, ..rest], ((uniform, _, _), others) => (uniform, (eachUniform texts rest others))

theorem eachMarked ∀ (texts: List Text) (options: List Doc)
    (each: SpellsEach texts options):
    AllMarked closesText commentsText options :=
  match options, each with
    | [], _ => byComputing
    | [option, ..rest], ((_, marked, _), others) => (marked, (eachMarked texts rest others))

--| A choice whose options each spell the same texts spells them.
theorem spellsChoice ∀ (texts: List Text) (first: Doc) (options: List Doc)
    (each: SpellsEach texts [first, ..options]):
    Spells (Choice [first, ..options]) texts :=
  match each with
    | (spells, others) =>
      match spells with
        | (uniform, marked, words) => (
          ((
            eachUniform texts [first, ..options] each,
            (rewrite words then (byComputing, sameWordsOf texts options others))
          )),
          eachMarked texts [first, ..options] each,
          words
        )

-- A token's own words.

--| A comment rule N left isn't layout (it starts `--`).
theorem commentNotLayout ∀ (text: Text) (comment: commentText text = True): isLayout text = False :=
  let starts := Bool.andLeft comment
  match text with
    | MkText [first, ..rest] =>
      match same: Text.sameChar '-' first with
        | True => rewrite (DecEq.sound (rewrite Text.sameCharEq '-' first at same then same)).flipped

--| A token's own-line comments, its text and its trailing comment, as the rules write them; the own-line comments
--| left out where an enclosing element wrote them (`hoisted`).
def Word.spelledAt (word: Word) (hoisted: Bool): List Text :=
  (if hoisted then [] else word.comments.above.map (note => note.text)) ++ [word.text] ++ word.comments.after.toList

--| The own-line comments are comments as rule N leaves them.
def notesSound: List Note → Bool
  | [] => True
  | [note, ..rest] => commentText note.text && notesSound rest

def afterSound: Option Text → Bool
  | Some comment => commentText comment
  | None => True

--| A token the rules can print: its text isn't layout, and its comments are as rule N leaves them.
def Word.sound (word: Word): Bool :=
  !isLayout word.text && notesSound word.comments.above && afterSound word.comments.after

--| The own-line comments' texts.
def Word.notes (word: Word): List Text := word.comments.above.map (note => note.text)

theorem spellsAppend ∀ (front back: List Doc) (texts later: List Text)
    (first: SpellsAll front texts)
    (second: SpellsAll back later):
    SpellsAll (front ++ back) (texts ++ later) :=
  match front, first with
    | [], (_, _, words) => rewrite <- words then second
    | [doc, ..rest], ((uniform, restUniform), (marked, restMarked), words) =>
      let (backUniform, backMarked, backWords) := second
      let (nextUniform, nextMarked, nextWords) :=
        spellsAppend rest back (wordsAll rest) later (restUniform, restMarked, byComputing) second
      (
        (uniform, nextUniform),
        (marked, nextMarked),
        (rewrite nextWords, <- words, List.appendAssoc doc.words (wordsAll rest) later)
      )

-- Own-line comments.

theorem spellsBlankList ∀ (blank: Bool): SpellsAll (if blank then [Blank] else []) [] := match blank with
  | True => spellsLast Blank [] spellsBlank
  | False => spellsNil

theorem laterCloserNotesSpells ∀ (notes: List Note)
    (sound: notesSound notes = True):
    SpellsAll (laterCloserNotes notes) (notes.map (note => note.text)) :=
  match notes with
    | [] => spellsNil
    | [note, ..rest] =>
      spellsAppend
        [HardLine]
        ((if note.blankBefore then [Blank] else []) ++ [Doc.text note.text] ++ laterCloserNotes rest)
        []
        [note.text, ..rest.map (note => note.text)]
        (spellsLast HardLine [] spellsHardLine)
        (spellsAppend
          (if note.blankBefore then [Blank] else [])
          ([Doc.text note.text] ++ laterCloserNotes rest)
          []
          [note.text, ..rest.map (note => note.text)]
          (spellsBlankList note.blankBefore)
          (spellsCons
            (Doc.text note.text)
            (laterCloserNotes rest)
            [note.text]
            (rest.map (note => note.text))
            (spellsText note.text (commentNotLayout note.text (Bool.andLeft sound)))
            (laterCloserNotesSpells rest (Bool.andRight sound))))

theorem closerNotesSpells ∀ (notes: List Note)
    (sound: notesSound notes = True):
    SpellsAll (closerNotes notes) (notes.map (note => note.text)) :=
  match notes with
    | [] => spellsNil
    | [note, ..rest] =>
      spellsCons
        (Doc.text note.text)
        (laterCloserNotes rest)
        [note.text]
        (rest.map (note => note.text))
        (spellsText note.text (commentNotLayout note.text (Bool.andLeft sound)))
        (laterCloserNotesSpells rest (Bool.andRight sound))

theorem notesAboveSpells ∀ (keep: Bool) (notes: List Note)
    (sound: notesSound notes = True):
    SpellsAll (notesAbove keep notes) (notes.map (note => note.text)) :=
  match notes with
    | [] => spellsNil
    | [note, ..rest] =>
      spellsAppend
        (if note.blankBefore && keep then [Blank] else [])
        ([Doc.text note.text, HardLine] ++ notesAbove True rest)
        []
        [note.text, ..rest.map (note => note.text)]
        (spellsBlankList (note.blankBefore && keep))
        (spellsCons
          (Doc.text note.text)
          [HardLine, ..notesAbove True rest]
          [note.text]
          (rest.map (note => note.text))
          (spellsText note.text (commentNotLayout note.text (Bool.andLeft sound)))
          (spellsCons HardLine
            (notesAbove True rest)
            []
            (rest.map (note => note.text))
            spellsHardLine
            (notesAboveSpells True rest (Bool.andRight sound))))

-- A token and its comments.

theorem spellsAllSame ∀ (docs: List Doc) (texts texts': List Text)
    (spells: SpellsAll docs texts)
    (same: texts = texts'):
    SpellsAll docs texts' :=
  rewrite <- same then spells

--| The own-line comments' texts, unless an enclosing element wrote them.
def Word.notesAt (word: Word) (hoisted: Bool): List Text := if hoisted then [] else word.notes

theorem leadingSpells ∀ (word: Word) (around: Around) (key: Nat)
    (sound: word.sound = True):
    SpellsAll (word.leading around key) (word.notesAt around.hoisted) :=
  match word, around.hoisted with
    | { text, comments = { above, after, blankBefore } }, True => spellsNil
    | { text, comments = { above = [], after, blankBefore } }, False =>
      match around.item && blankBefore with
        | True => spellsCons BreakParent [Blank] [] [] spellsBreakParent (spellsLast Blank [] spellsBlank)
        | False => spellsNil
    | { text, comments = { above = [first, ..rest], after, blankBefore } }, False =>
      match isCloserText text with
        | True =>
          spellsCons BreakParent
            [Nest 2 (Doc.concat [LineStartHere, ..closerNotes [first, ..rest]]), CloserLine key]
            []
            [first.text, ..rest.map (note => note.text)]
            spellsBreakParent
            (spellsAllSame _ _ _
              (spellsCons
                (Nest 2 (Doc.concat [LineStartHere, ..closerNotes [first, ..rest]]))
                [CloserLine key]
                [first.text, ..rest.map (note => note.text)]
                []
                (spellsNest 2
                  (Doc.concat [LineStartHere, ..closerNotes [first, ..rest]])
                  [first.text, ..rest.map (note => note.text)]
                  (spellsConcat
                    [LineStartHere, ..closerNotes [first, ..rest]]
                    [first.text, ..rest.map (note => note.text)]
                    (spellsCons LineStartHere
                      (closerNotes [first, ..rest])
                      []
                      [first.text, ..rest.map (note => note.text)]
                      spellsLineStartHere
                      (closerNotesSpells [first, ..rest] (Bool.andLeft (Bool.andRight sound))))))
                (spellsLast (CloserLine key) [] (spellsCloserLine key)))
              (List.appendNil _))
        | False =>
          spellsAllSame _ _ _
            (spellsAppend
              [BreakParent, LineStart, ..notesAbove around.item [first, ..rest]]
              (if blankBefore then [Blank] else [])
              [first.text, ..rest.map (note => note.text)]
              []
              (spellsCons BreakParent
                [LineStart, ..notesAbove around.item [first, ..rest]]
                []
                [first.text, ..rest.map (note => note.text)]
                spellsBreakParent
                (spellsCons LineStart
                  (notesAbove around.item [first, ..rest])
                  []
                  [first.text, ..rest.map (note => note.text)]
                  spellsLineStart
                  (notesAboveSpells around.item [first, ..rest] (Bool.andLeft (Bool.andRight sound)))))
              (spellsBlankList blankBefore))
            (List.appendNil _)

theorem pieceSpells ∀ (text: Text) (real: isLayout text = False): Spells (piece text) [text] :=
  match same: isCloserText text with
    | True => spellsClosing text real (Inl same)
    | False =>
      match comma: text == "," with
        | True => spellsClosing text real (Inr (DecEq.sound comma))
        | False => spellsText text real

theorem trailingSpells ∀ (word: Word) (sound: word.sound = True): SpellsAll word.trailing word.comments.after.toList :=
  match word with
    | { text, comments = { above, after = None, blankBefore } } => spellsNil
    | { text, comments = { above, after = Some comment, blankBefore } } =>
      spellsLast
        (LineSuffix comment)
        [comment]
        (spellsSuffix comment
          (commentNotLayout comment (Bool.andRight (Bool.andRight sound)))
          (Bool.andRight (Bool.andRight sound)))

theorem spellsCloserLineList ∀ (key: Nat) (own: Bool): SpellsAll (if own then [CloserLine key] else []) [] :=
  match own with
    | True => spellsLast (CloserLine key) [] (spellsCloserLine key)
    | False => spellsNil

theorem leafSpells ∀ (word: Word) (around: Around) (key: Nat)
    (sound: word.sound = True):
    Spells (word.leaf around key) (word.spelledAt around.hoisted) :=
  spellsConcat _ _
    (spellsAppend
      (word.leading around key)
      ((if isCloserText word.text && !word.noted && around.before && word.trails then [CloserLine key] else [])
        ++ [piece word.text]
        ++ word.trailing)
      (word.notesAt around.hoisted)
      ([word.text] ++ word.comments.after.toList)
      (leadingSpells word around key sound)
      (spellsAppend
        (if isCloserText word.text && !word.noted && around.before && word.trails then [CloserLine key] else [])
        ([piece word.text] ++ word.trailing)
        []
        ([word.text] ++ word.comments.after.toList)
        (spellsCloserLineList key (isCloserText word.text && !word.noted && around.before && word.trails))
        (spellsCons
          (piece word.text)
          word.trailing
          [word.text]
          word.comments.after.toList
          (pieceSpells word.text (Bool.notTrue (isLayout word.text) (Bool.andLeft sound)))
          (trailingSpells word sound))))

-- The tree's spelling.

--| The leftmost token of an expression of the slice.
def Expr.lead: Expr → Word
  | Atom _ word => word
  | Paren open _ _ => open
  | Tuple open _ _ _ => open
  | ListOf open _ _ _ => open
  | App head _ => head.lead
  | Infix _ left _ _ => left.lead
  | Prefix operator _ => operator
  | _ => Word.none

--| The items of a bracket, a comma after each but the last.
def commaSpelt: List Expr → List Text
  | [] => []
  | [item] => item.spelt False
  | [item, ..rest] => item.spelt False ++ [","] ++ commaSpelt rest

--| What the rules write for an expression of the slice: each token's own-line comments, text and trailing comment
--| in order, and a comma between a bracket's items; `hoisted` leaves out the first token's own-line comments, which
--| an enclosing element wrote.
def Expr.spelt: Expr → Bool → List Text
  | Atom _ word, hoisted => word.spelledAt hoisted
  | Paren open inner close, hoisted => open.spelledAt hoisted ++ inner.spelt False ++ close.spelledAt False
  | Tuple open items _ close, hoisted => open.spelledAt hoisted ++ commaSpelt items ++ close.spelledAt False
  | ListOf open items _ close, hoisted => open.spelledAt hoisted ++ commaSpelt items ++ close.spelledAt False
  | App head arguments, hoisted => head.spelt hoisted ++ argumentsSpelt arguments
  | Infix _ left operator right, hoisted => left.spelt hoisted ++ operator.spelledAt False ++ right.spelt False
  | Prefix operator operand, hoisted => operator.spelledAt hoisted ++ operand.spelt False
  | _, _ => []

def argumentsSpelt: List Expr → List Text
  | [] => []
  | [argument, ..rest] => argument.spelt False ++ argumentsSpelt rest

theorem wordsLead ∀ (expr: Expr)
    (within: expr.within1 = True):
    ∃ (rest: List Word) => expr.words = [expr.lead, ..rest] :=
  match expr with
    | Atom kind word => ([], byComputing)
    | Paren open inner close => (inner.words ++ [close], byComputing)
    | Tuple open items comma close => (itemsWords items ++ [close], byComputing)
    | ListOf open items comma close => (itemsWords items ++ [close], byComputing)
    | App head arguments =>
      let (rest, headWords) := wordsLead head (Bool.andLeft within)
      (rest ++ itemsWords arguments, rewrite headWords)
    | Infix kind left operator right =>
      match kind with
        | InfixBinary =>
          let (rest, leftWords) := wordsLead left (Bool.andLeft within)
          (rest ++ [operator, ..right.words], rewrite leftWords)
        | InfixArrow =>
          let (rest, leftWords) := wordsLead left (Bool.andLeft within)
          (rest ++ [operator, ..right.words], rewrite leftWords)
        | _ => cases
    | Prefix operator operand => (operand.words, byComputing)

theorem firstWordLead ∀ (expr: Expr) (within: expr.within1 = True): expr.firstWord = expr.lead :=
  let (rest, words) := wordsLead expr within
  rewrite words

theorem spelledAtLead ∀ (word: Word) (hoisted: Bool):
    word.spelledAt hoisted = word.notesAt hoisted ++ word.spelledAt True :=
  match hoisted with
    | True => byComputing
    | False => byComputing

--| Leaving the first token's own-line comments out takes them from the front.
theorem speltLead ∀ (expr: Expr) (hoisted: Bool)
    (within: expr.within1 = True):
    expr.spelt hoisted = expr.lead.notesAt hoisted ++ expr.spelt True :=
  match expr with
    | Atom kind word => spelledAtLead word hoisted
    | Paren open inner close =>
      rewrite spelledAtLead open hoisted,
          List.appendAssoc (open.notesAt hoisted) (open.spelledAt True) (inner.spelt False ++ close.spelledAt False)
    | Tuple open items comma close =>
      rewrite spelledAtLead open hoisted,
          List.appendAssoc (open.notesAt hoisted) (open.spelledAt True) (commaSpelt items ++ close.spelledAt False)
    | ListOf open items comma close =>
      rewrite spelledAtLead open hoisted,
          List.appendAssoc (open.notesAt hoisted) (open.spelledAt True) (commaSpelt items ++ close.spelledAt False)
    | App head arguments =>
      rewrite speltLead head hoisted (Bool.andLeft within),
          List.appendAssoc (head.lead.notesAt hoisted) (head.spelt True) (argumentsSpelt arguments)
    | Infix kind left operator right =>
      match kind with
        | InfixBinary =>
          rewrite speltLead left hoisted (Bool.andLeft within),
              List.appendAssoc
                (left.lead.notesAt hoisted)
                (left.spelt True)
                (operator.spelledAt False ++ right.spelt False)
        | InfixArrow =>
          rewrite speltLead left hoisted (Bool.andLeft within),
              List.appendAssoc
                (left.lead.notesAt hoisted)
                (left.spelt True)
                (operator.spelledAt False ++ right.spelt False)
        | _ => cases
    | Prefix operator operand =>
      rewrite spelledAtLead operator hoisted,
          List.appendAssoc (operator.notesAt hoisted) (operator.spelledAt True) (operand.spelt False)

theorem spellsMarkList ∀ (key: Nat) (own: Bool): SpellsAll (if own then [Mark key] else []) [] := match own with
  | True => spellsLast (Mark key) [] (spellsMark key)
  | False => spellsNil

theorem openingSpells ∀ (word: Word) (around: Around) (closer: Word)
    (sound: word.sound = True):
    Spells (word.opening around closer) (word.spelledAt around.hoisted) :=
  spellsConcat _ _
    (spellsAppend
      (word.leading around around.at)
      ((if closer.noted || closer.trails then [Mark around.at] else []) ++ [piece word.text] ++ word.trailing)
      (word.notesAt around.hoisted)
      ([word.text] ++ word.comments.after.toList)
      (leadingSpells word around around.at sound)
      (spellsAppend
        (if closer.noted || closer.trails then [Mark around.at] else [])
        ([piece word.text] ++ word.trailing)
        []
        ([word.text] ++ word.comments.after.toList)
        (spellsMarkList around.at (closer.noted || closer.trails))
        (spellsCons
          (piece word.text)
          word.trailing
          [word.text]
          word.comments.after.toList
          (pieceSpells word.text (Bool.notTrue (isLayout word.text) (Bool.andLeft sound)))
          (trailingSpells word sound))))

--| A node with its first token's own-line comments before it.
theorem framedSpells ∀ (first: Word) (around: Around) (doc: Doc) (texts: List Text)
    (sound: first.sound = True)
    (inner: Spells doc texts):
    Spells (framedBy first around doc) (first.notesAt around.hoisted ++ texts) :=
  spellsConcat _ _
    (spellsCons
      (Doc.concat (first.leading around around.at))
      [if first.noted || around.before then Displaced doc else doc]
      (first.notesAt around.hoisted)
      texts
      (spellsConcat _ _ (leadingSpells first around around.at sound))
      (spellsLast
        (if first.noted || around.before then Displaced doc else doc)
        texts
        (match first.noted || around.before with
          | True => spellsDisplaced doc texts inner
          | False => inner)))

-- Expressions the rules can print.

--| Every token's text isn't layout and its comments are as rule N leaves them.
def Expr.sound: Expr → Bool
  | Atom _ word => word.sound
  | Paren open inner close => open.sound && inner.sound && close.sound
  | Tuple open items _ close => open.sound && allSound items && close.sound
  | ListOf open items _ close => open.sound && allSound items && close.sound
  | App head arguments => head.sound && allSound arguments
  | Infix _ left operator right => left.sound && operator.sound && right.sound
  | Prefix operator operand => operator.sound && operand.sound
  | _ => False

def allSound: List Expr → Bool
  | [] => True
  | [expr, ..rest] => expr.sound && allSound rest

--| Every expression of a list is `ElSpells`.
def ElSpells (expr: Expr): Prop := ∀ (below: Around) => Spells (expr.el below) (expr.spelt below.hoisted)

def AllElSpells: List Expr → Prop
  | [] => True
  | [expr, ..rest] => ElSpells expr ∧ AllElSpells rest

-- Layout between documents.

theorem spellsJoinedWith ∀ (separator: Doc) (docs: List Doc) (texts: List Text)
    (layout: Spells separator [])
    (each: SpellsAll docs texts):
    SpellsAll (Doc.joinedWith separator docs) texts :=
  match docs, each with
    | [], each => each
    | [only], each => each
    | [doc, next, ..rest], ((uniform, restUniform), (marked, restMarked), words) =>
      let (nextUniform, nextMarked, nextWords) :=
        spellsJoinedWith separator [next, ..rest] (wordsAll [next, ..rest]) layout (
          restUniform,
          restMarked,
          byComputing
        )
      let (separatorUniform, separatorMarked, separatorWords) := layout
      (
        (uniform, separatorUniform, nextUniform),
        (marked, separatorMarked, nextMarked),
        (rewrite separatorWords, nextWords then words)
      )

theorem spellsSpaced ∀ (docs: List Doc) (texts: List Text) (each: SpellsAll docs texts): Spells (spaced docs) texts :=
  spellsConcat _ _ (spellsJoinedWith (Doc.text " ") docs texts spellsSpace each)

-- Brackets without commas.

theorem parenInnerSpells ∀ (inner: Expr) (around: Around)
    (within: inner.within1 = True)
    (each: Spells (inner.el around) (inner.spelt around.hoisted)):
    Spells (parenInner inner around) (inner.spelt around.hoisted) :=
  match inner with
    | Block _ _ _ => cases
    | If _ _ _ _ _ _ _ => cases
    | _ => each

theorem parenSpells ∀ (open: Word) (inner: Expr) (close: Word) (around: Around)
    (within: inner.within1 = True)
    (openSound: open.sound = True)
    (closeSound: close.sound = True)
    (each: ElSpells inner):
    Spells
      (parenDoc open inner close around)
      (open.spelledAt around.hoisted ++ inner.spelt False ++ close.spelledAt False) :=
  spellsConcat _ _
    (spellsCons
      (open.opening around close)
      [parenInner inner (around.next open.trails 1), close.leaf (around.next inner.trails (1 + inner.size)) around.at]
      (open.spelledAt around.hoisted)
      (inner.spelt False ++ close.spelledAt False)
      (openingSpells open around close openSound)
      (spellsCons
        (parenInner inner (around.next open.trails 1))
        [close.leaf (around.next inner.trails (1 + inner.size)) around.at]
        (inner.spelt False)
        (close.spelledAt False)
        (parenInnerSpells inner (around.next open.trails 1) within (each (around.next open.trails 1)))
        (spellsLast
          (close.leaf (around.next inner.trails (1 + inner.size)) around.at)
          (close.spelledAt False)
          (leafSpells close (around.next inner.trails (1 + inner.size)) around.at closeSound))))

theorem leadSound ∀ (expr: Expr) (sound: expr.sound = True): expr.lead.sound = True := match expr with
  | Atom kind word => sound
  | Paren open inner close => Bool.andLeft sound
  | Tuple open items comma close => Bool.andLeft sound
  | ListOf open items comma close => Bool.andLeft sound
  | App head arguments => leadSound head (Bool.andLeft sound)
  | Infix kind left operator right => leadSound left (Bool.andLeft sound)
  | Prefix operator operand => Bool.andLeft sound

--| A node's document, framed by its first token's own-line comments, spells what the node does.
theorem framedExprSpells ∀ (expr: Expr) (around: Around) (doc: Doc)
    (within: expr.within1 = True)
    (sound: expr.sound = True)
    (inner: Spells doc (expr.spelt True)):
    Spells (expr.framed around doc) (expr.spelt around.hoisted) :=
  rewrite speltLead expr around.hoisted within, <- firstWordLead expr within then
    framedSpells expr.firstWord around doc
      (expr.spelt True)
      (rewrite firstWordLead expr within then leadSound expr sound)
      inner

theorem spellsPrefixGap ∀ (operator: Word) (operand: Expr): Spells (prefixGap operator operand) [] :=
  match operator.text == "-" && (operand.firstWord.text == "-" || operand.numeralApplication) with
    | True => spellsSpace
    | False => spellsNothing

theorem prefixSpells ∀ (operator: Word) (operand: Expr) (around: Around)
    (operatorSound: operator.sound = True)
    (each: Spells (operand.el (around.next operator.trails 1)) (operand.spelt False)):
    Spells
      (Doc.concat [
        operator.leaf { around | hoisted = True } around.at,
        prefixGap operator operand,
        operand.el (around.next operator.trails 1)
      ])
      (operator.spelledAt True ++ operand.spelt False) :=
  spellsConcat _ _
    (spellsCons
      (operator.leaf { around | hoisted = True } around.at)
      [prefixGap operator operand, operand.el (around.next operator.trails 1)]
      (operator.spelledAt True)
      (operand.spelt False)
      (leafSpells operator { around | hoisted = True } around.at operatorSound)
      (spellsCons
        (prefixGap operator operand)
        [operand.el (around.next operator.trails 1)]
        []
        (operand.spelt False)
        (spellsPrefixGap operator operand)
        (spellsLast (operand.el (around.next operator.trails 1)) (operand.spelt False) each)))

-- Chains and elements.

theorem chainOfSpells ∀ (arms: Bool) (links: List Doc) (texts: List Text)
    (each: SpellsAll links texts):
    Spells (chainOf arms links) texts :=
  match links, each with
    | [], (_, _, words) => (byComputing, byComputing, words)
    | [head, ..tail], ((headUniform, tailUniform), (headMarked, tailMarked), words) =>
      spellsGroup
        (Doc.concat [head, Nest (if arms then 0 else 2) (Doc.concat tail)])
        texts
        (spellsConcat _ _
          (spellsAllSame _ _ _
            (spellsCons head
              [Nest (if arms then 0 else 2) (Doc.concat tail)]
              head.words
              (wordsAll tail)
              (headUniform, headMarked, byComputing)
              (spellsLast
                (Nest (if arms then 0 else 2) (Doc.concat tail))
                (wordsAll tail)
                (spellsNest
                  (if arms then 0 else 2)
                  (Doc.concat tail)
                  (wordsAll tail)
                  (spellsConcat tail (wordsAll tail) (tailUniform, tailMarked, byComputing)))))
            words))

theorem chainRightSpells ∀ (level: Option Nat) (right: Expr) (around: Around)
    (within: right.within1 = True)
    (link: SpellsAll (linkDocs level False right around) (right.spelt around.hoisted)):
    SpellsAll (chainRight level right around) (right.spelt around.hoisted) :=
  match right with
    | Block _ _ _ => cases
    | _ =>
      spellsCons (Doc.text " ") (linkDocs level False right around) [] (right.spelt around.hoisted) spellsSpace link

theorem chainLinksSpells ∀ (level: Option Nat) (first: Bool) (left: Expr) (operator: Word)
    (right: Expr) (around: Around)
    (leftWithin: left.within1 = True)
    (rightWithin: right.within1 = True)
    (leftSound: left.sound = True)
    (operatorSound: operator.sound = True)
    (rightSound: right.sound = True):
    SpellsAll
      (chainLinks level first left operator right around)
      (left.spelt around.hoisted ++ operator.spelledAt False ++ right.spelt False) :=
  spellsAppend
    (linkDocs level first left around)
    [
      Line,
      operator.leaf (around.next left.trails left.size) (around.next left.trails left.size).at,
      ..chainRight level right (around.next operator.trails (left.size + 1))
    ]
    (left.spelt around.hoisted)
    (operator.spelledAt False ++ right.spelt False)
    (linkDocsSpells level first left around leftWithin leftSound)
    (spellsCons Line
      [
        operator.leaf (around.next left.trails left.size) (around.next left.trails left.size).at,
        ..chainRight level right (around.next operator.trails (left.size + 1))
      ]
      []
      (operator.spelledAt False ++ right.spelt False)
      spellsLine
      (spellsCons
        (operator.leaf (around.next left.trails left.size) (around.next left.trails left.size).at)
        (chainRight level right (around.next operator.trails (left.size + 1)))
        (operator.spelledAt False)
        (right.spelt False)
        (leafSpells operator (around.next left.trails left.size) (around.next left.trails left.size).at operatorSound)
        (chainRightSpells level right
          (around.next operator.trails (left.size + 1))
          rightWithin
          (linkDocsSpells level False right (around.next operator.trails (left.size + 1)) rightWithin rightSound))))

theorem linkDocsSpells ∀ (level: Option Nat) (first: Bool) (expr: Expr) (around: Around)
    (within: expr.within1 = True)
    (sound: expr.sound = True):
    SpellsAll (linkDocs level first expr around) (expr.spelt around.hoisted) :=
  match expr with
    | Infix kind left operator right =>
      match kind with
        | InfixBinary =>
          match (Infix InfixBinary left operator right).inChain level with
            | True =>
              chainLinksSpells level first left operator right around
                (Bool.andLeft within)
                (Bool.andRight within)
                (Bool.andLeft sound)
                (Bool.andLeft (Bool.andRight sound))
                (Bool.andRight (Bool.andRight sound))
            | False =>
              spellsLast
                ((Infix InfixBinary left operator right).el around)
                ((Infix InfixBinary left operator right).spelt around.hoisted)
                (elSpells (Infix InfixBinary left operator right) around within sound)
        | InfixArrow =>
          match (Infix InfixArrow left operator right).inChain level with
            | True =>
              chainLinksSpells level first left operator right around
                (Bool.andLeft within)
                (Bool.andRight within)
                (Bool.andLeft sound)
                (Bool.andLeft (Bool.andRight sound))
                (Bool.andRight (Bool.andRight sound))
            | False =>
              spellsLast
                ((Infix InfixArrow left operator right).el around)
                ((Infix InfixArrow left operator right).spelt around.hoisted)
                (elSpells (Infix InfixArrow left operator right) around within sound)
        | _ => cases
    | Match _ _ _ _ => cases
    | _ => spellsLast (expr.el around) (expr.spelt around.hoisted) (elSpells expr around within sound)

theorem elSpells ∀ (expr: Expr) (around: Around)
    (within: expr.within1 = True)
    (sound: expr.sound = True):
    Spells (expr.el around) (expr.spelt around.hoisted) :=
  match expr with
    | Atom kind word => leafSpells word around around.at sound
    | Paren open inner close =>
      framedExprSpells
        (Paren open inner close)
        around
        (parenDoc open inner close { around | hoisted = True })
        within
        sound
        (parenSpells open inner close
          { around | hoisted = True }
          within
          (Bool.andLeft sound)
          (Bool.andRight (Bool.andRight sound))
          (below => elSpells inner below within (Bool.andLeft (Bool.andRight sound))))
    | Prefix operator operand =>
      framedExprSpells
        (Prefix operator operand)
        around
        (Doc.concat [
          operator.leaf { around | hoisted = True } around.at,
          prefixGap operator operand,
          operand.el (around.next operator.trails 1)
        ])
        within
        sound
        (prefixSpells operator operand around
          (Bool.andLeft sound)
          (elSpells operand (around.next operator.trails 1) within (Bool.andRight sound)))
    | Infix kind left operator right =>
      match kind with
        | InfixBinary =>
          framedExprSpells
            (Infix InfixBinary left operator right)
            around
            (chain (Infix InfixBinary left operator right).chainLevel left operator right { around | hoisted = True })
            within
            sound
            (chainOfSpells
              (left.opensArms (Infix InfixBinary left operator right).chainLevel)
              (chainLinks (Infix InfixBinary left operator right).chainLevel True left operator right { around |
                hoisted = True
              })
              (left.spelt True ++ operator.spelledAt False ++ right.spelt False)
              (chainLinksSpells
                (Infix InfixBinary left operator right).chainLevel
                True
                left
                operator
                right
                { around | hoisted = True }
                (Bool.andLeft within)
                (Bool.andRight within)
                (Bool.andLeft sound)
                (Bool.andLeft (Bool.andRight sound))
                (Bool.andRight (Bool.andRight sound))))
        | InfixArrow =>
          framedExprSpells
            (Infix InfixArrow left operator right)
            around
            (chain (Infix InfixArrow left operator right).chainLevel left operator right { around | hoisted = True })
            within
            sound
            (chainOfSpells
              (left.opensArms (Infix InfixArrow left operator right).chainLevel)
              (chainLinks (Infix InfixArrow left operator right).chainLevel True left operator right { around |
                hoisted = True
              })
              (left.spelt True ++ operator.spelledAt False ++ right.spelt False)
              (chainLinksSpells
                (Infix InfixArrow left operator right).chainLevel
                True
                left
                operator
                right
                { around | hoisted = True }
                (Bool.andLeft within)
                (Bool.andRight within)
                (Bool.andLeft sound)
                (Bool.andLeft (Bool.andRight sound))
                (Bool.andRight (Bool.andRight sound))))
        | _ => cases
    | _ => ?
