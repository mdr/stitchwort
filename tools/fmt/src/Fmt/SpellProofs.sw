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
import Syntax (Comments, Decl, DefBody, DefKind, Expr, Header, InfixKind, Note, SourceFile, Tok, Word)
import Fmt (..)
import Fmt.CalmProofs (
  bracketFrom,
  bracketIs,
  headerResultWithin,
  lambdaHugNone,
  matchedNone,
  plainDef,
  plainDefIs,
  valueElPlain
)

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

--| The own-line comments after a closer's first spell their texts.
--|
--| Proof idea: Induction on the notes; each is a line break, a kept blank line and its text.
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

--| Own-line comments above a token spell their texts.
--|
--| Proof idea: Induction on the notes; each is an optional blank line, its text and a line break.
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

--| What a token writes before it spells its own-line comments, unless an enclosing element wrote them.
--|
--| Proof idea: Cases on whether the token is hoisted, has own-line comments and is a closer; each branch is a list of layout documents around `closerNotes` or `notesAbove`.
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

--| A token's leaf spells its own-line comments (unless hoisted), its text and its trailing comment.
--|
--| Proof idea: The concat of its leading documents, an optional `CloserLine`, its piece (`pieceSpells`) and its trailing comment (`trailingSpells`).
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

--| An expression of the slice has a first token.
--|
--| Proof idea: Induction on the expression.
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
--|
--| Proof idea: Induction down the first operands, with `spelledAtLead` at the token.
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

--| A bracket's opener spells as a token does; its `Mark` has no words.
--|
--| Proof idea: As `leafSpells`, with the mark where the closer may take a line of its own.
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
--|
--| Proof idea: The concat of the comments (`leadingSpells`) and the node, displaced or not.
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
def ElSpells (expr: Expr): Prop :=
  expr.within1 = True → expr.sound = True → ∀ (below: Around) => Spells (expr.el below) (expr.spelt below.hoisted)

def AllElSpells: List Expr → Prop
  | [] => True
  | [expr, ..rest] => ElSpells expr ∧ AllElSpells rest

-- Layout between documents.

--| Documents with layout between them spell what the documents do.
--|
--| Proof idea: Induction on the documents.
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

--| A bracket spells its opener, its inner expression and its closer.
--|
--| Proof idea: The concat of `openingSpells`, the inner (the hypothesis) and `leafSpells`.
theorem parenSpells ∀ (open: Word) (inner: Expr) (close: Word) (around: Around)
    (within: inner.within1 = True)
    (openSound: open.sound = True)
    (closeSound: close.sound = True)
    (innerSound: inner.sound = True)
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
        (parenInnerSpells inner (around.next open.trails 1) within (each within innerSound (around.next open.trails 1)))
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

--| A prefix operator spells the operator and its operand.
--|
--| Proof idea: The concat of the operator's leaf, the gap (layout) and the operand's element.
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

--| A chain's lines, grouped, spell what the lines do.
--|
--| Proof idea: Cases on the lines; the first, then the rest in a nest.
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

--| A chain's lines spell the first operand, the operator and the last operand.
--|
--| Proof idea: The first operand's lines (`linkDocsSpells`), a `Line`, the operator's leaf and what follows it (`chainRightSpells`).
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

--| A chain operand's documents spell what the operand spells.
--|
--| Proof idea: A chain of the level is its links, any other operand its element, as in `linkDocsKept`.
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

-- Commas.

theorem spellsComma: Spells (Closing ",") [","] := spellsClosing "," byComputing (Inr byComputing)

theorem spellsSeparator ∀ (first: Bool): Spells (if first then SoftLine else Line) [] := match first with
  | True => spellsSoftLine
  | False => spellsLine

--| A filled list's cells spell its items, a comma after each but the last.
--|
--| Proof idea: Induction on the items.
theorem cellsSpells ∀ (bare arm before: Bool) (at: Nat) (items: List Expr)
    (within: allWithin1 items = True)
    (sound: allSound items = True)
    (each: AllElSpells items):
    SpellsAll (cells bare arm before at items) (commaSpelt items) :=
  match items, each with
    | [], _ => spellsNil
    | [item], (first, _) =>
      spellsLast
        (item.el (firstAround bare arm before at))
        (item.spelt False)
        (first (Bool.andLeft within) (Bool.andLeft sound) (firstAround bare arm before at))
    | [item, ..rest], (first, others) =>
      spellsAllSame _ _ _
        (spellsCons
          (Doc.concat [item.el (firstAround bare arm before at), Closing ","])
          (cells False arm False (at + item.size) rest)
          (item.spelt False ++ [","])
          (commaSpelt rest)
          (spellsConcat _ _
            (spellsCons
              (item.el (firstAround bare arm before at))
              [Closing ","]
              (item.spelt False)
              [","]
              (first (Bool.andLeft within) (Bool.andLeft sound) (firstAround bare arm before at))
              (spellsLast (Closing ",") [","] spellsComma)))
          (cellsSpells False arm False (at + item.size) rest (Bool.andRight within) (Bool.andRight sound) others))
        (List.appendAssoc (item.spelt False) [","] (commaSpelt rest))

--| A broken bracket's lines spell its items, a comma after each but the last.
--|
--| Proof idea: Induction on the items, a separator before each.
theorem brokenItemsSpells ∀ (bare arm first before: Bool) (at: Nat) (items: List Expr)
    (within: allWithin1 items = True)
    (sound: allSound items = True)
    (each: AllElSpells items):
    SpellsAll (brokenItems bare arm first before at items) (commaSpelt items) :=
  match items, each with
    | [], _ => spellsNil
    | [item], (kept, _) =>
      spellsCons
        (if first then SoftLine else Line)
        [item.el (firstAround bare arm before at)]
        []
        (item.spelt False)
        (spellsSeparator first)
        (spellsLast
          (item.el (firstAround bare arm before at))
          (item.spelt False)
          (kept (Bool.andLeft within) (Bool.andLeft sound) (firstAround bare arm before at)))
    | [item, ..rest], (kept, others) =>
      spellsCons
        (if first then SoftLine else Line)
        [
          item.el (firstAround bare arm before at),
          Closing ",",
          ..brokenItems False arm False False (at + item.size) rest
        ]
        []
        (commaSpelt [item, ..rest])
        (spellsSeparator first)
        (spellsAllSame _ _ _
          (spellsCons
            (item.el (firstAround bare arm before at))
            [Closing ",", ..brokenItems False arm False False (at + item.size) rest]
            (item.spelt False)
            ([","] ++ commaSpelt rest)
            (kept (Bool.andLeft within) (Bool.andLeft sound) (firstAround bare arm before at))
            (spellsCons
              (Closing ",")
              (brokenItems False arm False False (at + item.size) rest)
              [","]
              (commaSpelt rest)
              spellsComma
              (brokenItemsSpells False arm False False
                (at + item.size)
                rest
                (Bool.andRight within)
                (Bool.andRight sound)
                others)))
          byComputing)

theorem spellsEq ∀ (doc doc': Doc) (texts: List Text)
    (same: doc = doc')
    (spells: Spells doc' texts):
    Spells doc texts :=
  rewrite same then spells

--| A comma bracket's document spells its opener, its items and its closer.
--|
--| Proof idea: Cases on whether the items are empty, fill their lines, and hold a comment; each document is a concat of the opener, the items' lines and the closer.
theorem bracketFromSpells ∀ (list empty plain holds: Bool) (prefix closer: Doc)
    (filled broken: List Doc) (opens items closes: List Text)
    (prefixSpells: Spells prefix opens)
    (closerSpells: Spells closer closes)
    (filledSpells: SpellsAll filled items)
    (brokenSpells: SpellsAll broken items)
    (emptyItems: empty = True → items = []):
    Spells (bracketFrom list empty plain holds prefix closer filled broken) (opens ++ items ++ closes) :=
  match empty with
    | True =>
      rewrite emptyItems byComputing then
        spellsConcat _ _ (spellsCons prefix [closer] opens closes prefixSpells (spellsLast closer closes closerSpells))
    | False =>
      match list && !holds && plain with
        | True =>
          spellsConcat _ _
            (spellsCons prefix
              [Nest 2 (Fill filled), closer]
              opens
              (items ++ closes)
              prefixSpells
              (spellsCons
                (Nest 2 (Fill filled))
                [closer]
                items
                closes
                (spellsNest 2 (Fill filled) items (spellsFill filled items filledSpells))
                (spellsLast closer closes closerSpells)))
        | False =>
          match holds with
            | True =>
              spellsConcat _ _
                (spellsAllSame _ _ _
                  (spellsAppend
                    [prefix, Nest 2 (Doc.concat broken), SoftLine, closer]
                    [BreakParent]
                    (opens ++ items ++ closes)
                    []
                    (spellsCons prefix
                      [Nest 2 (Doc.concat broken), SoftLine, closer]
                      opens
                      (items ++ closes)
                      prefixSpells
                      (spellsCons
                        (Nest 2 (Doc.concat broken))
                        [SoftLine, closer]
                        items
                        closes
                        (spellsNest 2 (Doc.concat broken) items (spellsConcat broken items brokenSpells))
                        (spellsCons SoftLine
                          [closer]
                          []
                          closes
                          spellsSoftLine
                          (spellsLast closer closes closerSpells))))
                    (spellsLast BreakParent [] spellsBreakParent))
                  (List.appendNil _))
            | False =>
              spellsConcat _ _
                (spellsCons prefix
                  [Nest 2 (Doc.concat broken), SoftLine, closer]
                  opens
                  (items ++ closes)
                  prefixSpells
                  (spellsCons
                    (Nest 2 (Doc.concat broken))
                    [SoftLine, closer]
                    items
                    closes
                    (spellsNest 2 (Doc.concat broken) items (spellsConcat broken items brokenSpells))
                    (spellsCons SoftLine [closer] [] closes spellsSoftLine (spellsLast closer closes closerSpells))))

theorem commaSpeltEmpty ∀ (items: List Expr) (empty: items.isEmpty = True): commaSpelt items = [] :=
  match items, empty with | [], _ => byComputing

--| A tuple or list spells its opener, its items with commas and its closer.
--|
--| Proof idea: `bracketIs` (`bracketContent` is `bracketFrom`), then `bracketFromSpells` with the opener, closer, cells and lines each spelling.
theorem bracketContentSpells ∀ (list: Bool) (open: Word) (items: List Expr) (close: Word) (around: Around)
    (within: allWithin1 items = True)
    (sound: allSound items = True)
    (openSound: open.sound = True)
    (closeSound: close.sound = True)
    (each: AllElSpells items):
    Spells
      (bracketContent list open items close around)
      (open.spelledAt around.hoisted ++ commaSpelt items ++ close.spelledAt False) :=
  spellsEq _ _ _
    (bracketIs list open items close around)
    (bracketFromSpells list items.isEmpty
      (items.all Expr.plainItem)
      (ListOf open items False close).holdsTrailingComment
      (open.opening around close)
      (close.leaf
        (around.next (ListOf open items False close).trailsBeforeClose ((ListOf open items False close).size - 1))
        around.at)
      (cells (list && items.all Expr.plainItem) around.inArm open.trails (around.at + 1) items)
      (brokenItems (list && items.all Expr.plainItem) around.inArm True open.trails (around.at + 1) items)
      (open.spelledAt around.hoisted)
      (commaSpelt items)
      (close.spelledAt False)
      (openingSpells open around close openSound)
      (leafSpells close
        (around.next (ListOf open items False close).trailsBeforeClose ((ListOf open items False close).size - 1))
        around.at
        closeSound)
      (cellsSpells (list && items.all Expr.plainItem) around.inArm open.trails (around.at + 1) items within sound each)
      (brokenItemsSpells
        (list && items.all Expr.plainItem)
        around.inArm
        True
        open.trails
        (around.at + 1)
        items
        within
        sound
        each)
      (commaSpeltEmpty items))

theorem allElSpells ∀ (items: List Expr)
    (within: allWithin1 items = True)
    (sound: allSound items = True):
    AllElSpells items :=
  match items with
    | [] => byComputing
    | [first, ..rest] =>
      ((w s below => elSpells first below w s), (allElSpells rest (Bool.andRight within) (Bool.andRight sound)))

-- Calls.

--| The documents are each `Uniform` and `Marked`, whatever their words are.
def Own (docs: List Doc): Prop := AllUniform docs ∧ AllMarked closesText commentsText docs

theorem ownOfSpells ∀ (docs: List Doc) (texts: List Text) (spells: SpellsAll docs texts): Own docs := match spells with
  | (uniform, marked, _) => (uniform, marked)

theorem spellsOfOwn ∀ (docs: List Doc) (own: Own docs): SpellsAll docs (wordsAll docs) := match own with
  | (uniform, marked) => (uniform, marked, byComputing)

theorem ownTake ∀ (docs: List Doc) (count: Nat) (own: Own docs): Own (docs.take count) := match docs, count, own with
  | [], Zero, _ => (byComputing, byComputing)
  | [], Succ less, _ => (byComputing, byComputing)
  | [first, ..rest], Zero, _ => (byComputing, byComputing)
  | [first, ..rest], Succ less, ((firstUniform, restUniform), (firstMarked, restMarked)) =>
    let (uniform, marked) := ownTake rest less (restUniform, restMarked)
    ((firstUniform, uniform), (firstMarked, marked))

theorem ownDrop ∀ (docs: List Doc) (count: Nat) (own: Own docs): Own (docs.drop count) := match docs, count, own with
  | [], Zero, _ => (byComputing, byComputing)
  | [], Succ less, _ => (byComputing, byComputing)
  | [first, ..rest], Zero, own => own
  | [first, ..rest], Succ less, ((firstUniform, restUniform), (firstMarked, restMarked)) =>
    ownDrop rest less (restUniform, restMarked)

theorem wordsTakeDrop ∀ (docs: List Doc) (count: Nat):
    wordsAll (docs.take count) ++ wordsAll (docs.drop count) = wordsAll docs :=
  match docs, count with
    | [], Zero => byComputing
    | [], Succ less => byComputing
    | [first, ..rest], Zero => byComputing
    | [first, ..rest], Succ less =>
      rewrite List.appendAssoc first.words (wordsAll (rest.take less)) (wordsAll (rest.drop less)),
          wordsTakeDrop rest less

--| The elements of a call that go below, each after a line break, spell what they do.
--|
--| Proof idea: Induction on the documents.
theorem ownConcatMap ∀ (docs: List Doc)
    (own: Own docs):
    SpellsAll (docs.concatMap (doc => [HardLine, doc])) (wordsAll docs) :=
  match docs, own with
    | [], _ => spellsNil
    | [doc, ..rest], ((uniform, restUniform), (marked, restMarked)) =>
      spellsCons HardLine
        [doc, ..rest.concatMap (doc => [HardLine, doc])]
        []
        (wordsAll [doc, ..rest])
        spellsHardLine
        (spellsCons doc
          (rest.concatMap (doc => [HardLine, doc]))
          doc.words
          (wordsAll rest)
          (uniform, marked, byComputing)
          (ownConcatMap rest (restUniform, restMarked)))

--| A call that breaks keeps some elements on its line and the rest each on a line of its own: the words are the
--| elements'.
--|
--| Proof idea: The words of the first `keep` and the rest are the words of all (`wordsTakeDrop`); the front in a group or spaced, the rest in a nest, under `IfBroken` or not.
theorem frontRestSpells ∀ (id keep: Nat) (fillFront: Bool) (docs: List Doc) (texts: List Text)
    (spells: SpellsAll docs texts):
    Spells
      (Doc.concat [
        if fillFront then IdGroup id (Nest 4 (Fill (docs.take keep))) False else spaced (docs.take keep),
        if fillFront then
          IfBroken id
            (Nest 4 (Doc.concat (docs.drop keep |> .concatMap (doc => [HardLine, doc]))))
            (Nest 2 (Doc.concat (docs.drop keep |> .concatMap (doc => [HardLine, doc]))))
        else Nest 2 (Doc.concat (docs.drop keep |> .concatMap (doc => [HardLine, doc])))
      ])
      texts :=
  let own := ownOfSpells docs texts spells
  let kept := spellsOfOwn (docs.take keep) (ownTake docs keep own)
  let rest := spellsConcat _ _ (ownConcatMap (docs.drop keep) (ownDrop docs keep own))
  let words: wordsAll (docs.take keep) ++ wordsAll (docs.drop keep) = texts :=
    Eq.trans (wordsTakeDrop docs keep) (spells.right.right)
  rewrite <- words then
    spellsConcat _ _
      (spellsCons
        (if fillFront then IdGroup id (Nest 4 (Fill (docs.take keep))) False else spaced (docs.take keep))
        [
          if fillFront then
            IfBroken id
              (Nest 4 (Doc.concat (docs.drop keep |> .concatMap (doc => [HardLine, doc]))))
              (Nest 2 (Doc.concat (docs.drop keep |> .concatMap (doc => [HardLine, doc]))))
          else Nest 2 (Doc.concat (docs.drop keep |> .concatMap (doc => [HardLine, doc])))
        ]
        (wordsAll (docs.take keep))
        (wordsAll (docs.drop keep))
        (match fillFront with
          | True =>
            spellsIdGroup id
              (Nest 4 (Fill (docs.take keep)))
              False
              (wordsAll (docs.take keep))
              (spellsNest 4
                (Fill (docs.take keep))
                (wordsAll (docs.take keep))
                (spellsFill (docs.take keep) (wordsAll (docs.take keep)) kept))
          | False => spellsSpaced (docs.take keep) (wordsAll (docs.take keep)) kept)
        (spellsLast
          (if fillFront then
             IfBroken id
               (Nest 4 (Doc.concat (docs.drop keep |> .concatMap (doc => [HardLine, doc]))))
               (Nest 2 (Doc.concat (docs.drop keep |> .concatMap (doc => [HardLine, doc]))))
           else Nest 2 (Doc.concat (docs.drop keep |> .concatMap (doc => [HardLine, doc]))))
          (wordsAll (docs.drop keep))
          (match fillFront with
            | True =>
              spellsIfBroken id
                (Nest 4 (Doc.concat (docs.drop keep |> .concatMap (doc => [HardLine, doc]))))
                (Nest 2 (Doc.concat (docs.drop keep |> .concatMap (doc => [HardLine, doc]))))
                (wordsAll (docs.drop keep))
                (spellsNest 4 _ _ rest)
                (spellsNest 2 _ _ rest)
            | False => spellsNest 2 _ _ rest)))

--| What a call's pieces spell, and what its hug spells.
def AppSpells (applied: Applied) (texts: List Text): Prop :=
  Spells applied.doc texts ∧ (∀ (open: Doc) => applied.hug = Some open → Spells open texts)

--| A call's document and its hug spell the function and its arguments.
--|
--| Proof idea: Cases on whether every element stays on its line; else each option of the choice (flat, hugged if the last argument hugs, the front and the rest) spells the same words (`spellsChoice`).
theorem appFromSpells ∀ (id keep: Nat) (between betweenFront: Bool) (headDoc lastDoc: Doc) (front: List Doc)
    (hug: Option Doc) (headTexts frontTexts lastTexts: List Text)
    (headSpells: Spells headDoc headTexts)
    (frontSpells: SpellsAll front frontTexts)
    (lastSpells: Spells lastDoc lastTexts)
    (hugSpells: ∀ (open: Doc) => hug = Some open → Spells open lastTexts):
    AppSpells (appFrom id keep between betweenFront headDoc front lastDoc hug) (headTexts ++ frontTexts ++ lastTexts) :=
  let docsSpells: SpellsAll ([headDoc, ..front] ++ [lastDoc]) (headTexts ++ frontTexts ++ lastTexts) :=
    spellsCons headDoc
      (front ++ [lastDoc])
      headTexts
      (frontTexts ++ lastTexts)
      headSpells
      (spellsAppend front [lastDoc] frontTexts lastTexts frontSpells (spellsLast lastDoc lastTexts lastSpells))
  match keep == ([headDoc, ..front] ++ [lastDoc]).length with
    | True => (
      (match between with
        | True => spellsSpaced _ _ docsSpells
        | False => spellsNest 4 _ _ (spellsFill _ _ docsSpells)),
      (open none => cases)
    )
    | False =>
      let thirdSpells :=
        frontRestSpells id keep
          (keep > 2 && !betweenFront)
          ([headDoc, ..front] ++ [lastDoc])
          (headTexts ++ frontTexts ++ lastTexts)
          docsSpells
      let allSpells := spellsFlatten _ _ (spellsSpaced _ _ docsSpells)
      match hug with
        | None => (
          spellsChoice
            (headTexts ++ frontTexts ++ lastTexts)
            (Flatten (spaced ([headDoc, ..front] ++ [lastDoc])))
            [
              Doc.concat [
                if keep > 2 && !betweenFront then
                  IdGroup id (Nest 4 (Fill (([headDoc, ..front] ++ [lastDoc]).take keep))) False
                else spaced (([headDoc, ..front] ++ [lastDoc]).take keep),
                if keep > 2 && !betweenFront then
                  IfBroken id
                    (Nest 4
                      (Doc.concat (([headDoc, ..front] ++ [lastDoc]).drop keep |> .concatMap (doc => [HardLine, doc]))))
                    (Nest 2
                      (Doc.concat (([headDoc, ..front] ++ [lastDoc]).drop keep |> .concatMap (doc => [HardLine, doc]))))
                else
                  Nest 2
                    (Doc.concat (([headDoc, ..front] ++ [lastDoc]).drop keep |> .concatMap (doc => [HardLine, doc])))
              ]
            ]
            (allSpells, (thirdSpells, byComputing)),
          (open same => cases)
        )
        | Some opened =>
          let huggedSpells: Spells
            (Doc.concat [Flatten (spaced [headDoc, ..front]), Doc.text " ", opened])
            (headTexts ++ frontTexts ++ lastTexts) :=
            spellsConcat _ _
              (spellsAllSame _ _ _
                (spellsCons
                  (Flatten (spaced [headDoc, ..front]))
                  [Doc.text " ", opened]
                  (headTexts ++ frontTexts)
                  ([] ++ lastTexts)
                  (spellsFlatten _ _
                    (spellsSpaced _ _ (spellsCons headDoc front headTexts frontTexts headSpells frontSpells)))
                  (spellsCons
                    (Doc.text " ")
                    [opened]
                    []
                    lastTexts
                    spellsSpace
                    (spellsLast opened lastTexts (hugSpells opened byComputing))))
                (List.appendAssoc headTexts frontTexts lastTexts))
          (
            spellsChoice
              (headTexts ++ frontTexts ++ lastTexts)
              (Flatten (spaced ([headDoc, ..front] ++ [lastDoc])))
              [
                Doc.concat [Flatten (spaced [headDoc, ..front]), Doc.text " ", opened],
                Doc.concat [
                  if keep > 2 && !betweenFront then
                    IdGroup id (Nest 4 (Fill (([headDoc, ..front] ++ [lastDoc]).take keep))) False
                  else spaced (([headDoc, ..front] ++ [lastDoc]).take keep),
                  if keep > 2 && !betweenFront then
                    IfBroken id
                      (Nest 4
                        (Doc.concat
                          (([headDoc, ..front] ++ [lastDoc]).drop keep |> .concatMap (doc => [HardLine, doc]))))
                      (Nest 2
                        (Doc.concat
                          (([headDoc, ..front] ++ [lastDoc]).drop keep |> .concatMap (doc => [HardLine, doc]))))
                  else
                    Nest 2
                      (Doc.concat (([headDoc, ..front] ++ [lastDoc]).drop keep |> .concatMap (doc => [HardLine, doc])))
                ]
              ]
              (allSpells, (huggedSpells, (thirdSpells, byComputing))),
            (open same => rewrite <- Option.someInjective same then huggedSpells)
          )

theorem spellsGroupWith ∀ (inner: Doc) (hard: Bool) (texts: List Text)
    (spells: Spells inner texts):
    Spells (Group inner hard) texts :=
  spells

--| What a call's last argument and its hug spell.
def LastSpells (last: (Doc, Option Doc)) (texts: List Text): Prop :=
  Spells last.fst texts ∧ (∀ (open: Doc) => last.snd = Some open → Spells open texts)

theorem hugTexts ∀ (open: Word) (hoisted: Bool) (items close: List Text):
    open.spelledAt hoisted ++ items ++ close = open.notesAt hoisted ++ (open.spelledAt True ++ items ++ close) :=
  rewrite spelledAtLead open hoisted, List.appendAssoc (open.notesAt hoisted) (open.spelledAt True) (items ++ close)

--| A hugged bracket and its hug spell the opener, its items and its closer.
--|
--| Proof idea: The opener's own-line comments, then the bracket's content in a group (`bracketContentSpells`); `hugTexts` moves the comments back to the front.
theorem huggedSpells ∀ (list: Bool) (open: Word) (items: List Expr) (close: Word) (around: Around)
    (within: allWithin1 items = True)
    (sound: allSound items = True)
    (openSound: open.sound = True)
    (closeSound: close.sound = True):
    LastSpells
      (huggedBracket list open items close around)
      (open.spelledAt around.hoisted ++ commaSpelt items ++ close.spelledAt False) :=
  let content :=
    bracketContentSpells list open items close
      { around | hoisted = True }
      within
      sound
      openSound
      closeSound
      (allElSpells items within sound)
  let leading := spellsConcat _ _ (leadingSpells open around around.at openSound)
  (
    rewrite hugTexts open around.hoisted (commaSpelt items) (close.spelledAt False) then
      spellsConcat _ _
        (spellsCons _ _ _ _ leading
          (spellsLast
            (Group
              (bracketContent list open items close { around | hoisted = True })
              (bracketContent list open items close { around | hoisted = True }).forcesBreak) _
            (spellsGroupWith _
              (bracketContent list open items close { around | hoisted = True }).forcesBreak _
              content))),
    (hugged same =>
      rewrite <- Option.someInjective same, hugTexts open around.hoisted (commaSpelt items) (close.spelledAt False) then
        spellsConcat _ _
          (spellsCons _ _ _ _ leading
            (spellsLast
              (Group (bracketContent list open items close { around | hoisted = True }) True) _
              (spellsGroupWith _ True _ content))))
  )

--| What an option of a call's arguments spells: nothing if there is none, else its document and its hug.
def LastOption: Option (Doc, Option Doc) → List Text → Prop
  | None, texts => texts = []
  | Some last, texts => LastSpells last texts

--| What `argumentDocs` makes of arguments spells them: the documents before the last, and the last.
def ArgsSpells (made: (List Doc, Option (Doc, Option Doc))) (front last: List Text): Prop :=
  SpellsAll made.fst front ∧ LastOption made.snd last

--| A call's last argument and its hug spell the argument.
--|
--| Proof idea: Cases on the argument as `lastArgument` has them: a tuple or list hugs, any other is its element.
theorem lastArgumentSpells ∀ (argument: Expr) (around: Around)
    (within: argument.within1 = True)
    (sound: argument.sound = True):
    LastSpells (lastArgument argument around) (argument.spelt around.hoisted) :=
  match argument with
    | Tuple open items comma close =>
      huggedSpells False open items close around within
        (Bool.andLeft (Bool.andRight sound))
        (Bool.andLeft sound)
        (Bool.andRight (Bool.andRight sound))
    | ListOf open items comma close =>
      huggedSpells True open items close around within
        (Bool.andLeft (Bool.andRight sound))
        (Bool.andLeft sound)
        (Bool.andRight (Bool.andRight sound))
    | Paren open inner close =>
      match inner with
        | Binding _ _ _ _ _ => cases
        | Block _ _ _ => cases
        | _ => (elSpells (Paren open inner close) around within sound, (open same => cases))
    | Record _ _ _ _ _ => cases
    | _ => (elSpells argument around within sound, (open same => cases))

theorem argsSpellsEq ∀ (made made': (List Doc, Option (Doc, Option Doc))) (front last: List Text)
    (same: made = made')
    (spells: ArgsSpells made' front last):
    ArgsSpells made front last :=
  rewrite same then spells

theorem argumentDocsConsTest ∀ (arm: Bool) (previous argument next: Expr) (at: Nat) (more: List Expr):
    argumentDocs arm previous at [argument, next, ..more]
      = (
        [
          argument.el { before = previous.trails, hoisted = False, item = False, at, inArm = arm },
          ..(argumentDocs arm argument (at + argument.size) [next, ..more]).fst
        ],
        (argumentDocs arm argument (at + argument.size) [next, ..more]).snd
      ) :=
  byComputing

--| A call's arguments spell their texts, split into the documents before the last and the last.
--|
--| Proof idea: Induction on the arguments; each stands after the one before.
theorem argumentDocsSpells ∀ (arm: Bool) (previous: Expr) (at: Nat) (arguments: List Expr)
    (within: allWithin1 arguments = True)
    (sound: allSound arguments = True):
    ∃ (front last: List Text) => ArgsSpells (argumentDocs arm previous at arguments) front last
      ∧ front ++ last = argumentsSpelt arguments :=
  match arguments with
    | [] => ([], [], ((spellsNil, byComputing), byComputing))
    | [argument] => (
      [],
      argument.spelt False,
      (
        (
          spellsNil,
          lastArgumentSpells argument
            { before = previous.trails, hoisted = False, item = False, at, inArm = arm }
            (Bool.andLeft within)
            (Bool.andLeft sound)
        ),
        (List.appendNil (argument.spelt False)).flipped
      )
    )
    | [argument, next, ..more] =>
      let (frontTexts, lastTexts, (docsSpells, lastSpells), texts) :=
        argumentDocsSpells arm argument (at + argument.size) [next, ..more] (Bool.andRight within) (Bool.andRight sound)
      (
        argument.spelt False ++ frontTexts,
        lastTexts,
        (
          (argsSpellsEq _ _ _ _ (argumentDocsConsTest arm previous argument next at more) (
            (spellsCons
              (argument.el { before = previous.trails, hoisted = False, item = False, at, inArm = arm })
              (argumentDocs arm argument (at + argument.size) [next, ..more]).fst
              (argument.spelt False)
              frontTexts
              (elSpells argument
                { before = previous.trails, hoisted = False, item = False, at, inArm = arm }
                (Bool.andLeft within)
                (Bool.andLeft sound))
              docsSpells),
            lastSpells
          )),
          (rewrite List.appendAssoc (argument.spelt False) frontTexts lastTexts, texts)
        )
      )

theorem pickSpells ∀ (option: Option (Doc, Option Doc)) (texts: List Text)
    (last: LastOption option texts):
    LastSpells (option.getOrElse (Nothing, None)) texts :=
  match option, last with
    | None, same => (rewrite same then spellsNothing, (open none => cases))
    | Some pair, spells => spells

theorem appDocsIs ∀ (head: Expr) (arguments: List Expr) (around: Around):
    appDocs head arguments around
      = appFrom
        (around.at + 1)
        (1 + keptFront head arguments)
        (commentBetween head arguments)
        (commentBetween head (arguments.take (1 + keptFront head arguments - 1)))
        (head.el around)
        (argumentDocs around.inArm head (around.at + head.size) arguments).fst
        ((argumentDocs around.inArm head (around.at + head.size) arguments).snd.getOrElse (Nothing, None)).fst
        ((argumentDocs around.inArm head (around.at + head.size) arguments).snd.getOrElse (Nothing, None)).snd :=
  byComputing

--| A call spells its function and its arguments.
--|
--| Proof idea: `appDocsIs` (the facts `appDocs` reads, as projections) and `appFromSpells`.
theorem appDocsSpells ∀ (head: Expr) (arguments: List Expr) (around: Around)
    (headWithin: head.within1 = True)
    (headSound: head.sound = True)
    (within: allWithin1 arguments = True)
    (sound: allSound arguments = True):
    AppSpells (appDocs head arguments around) (head.spelt around.hoisted ++ argumentsSpelt arguments) :=
  let (frontTexts, lastTexts, (frontSpells, lastSpells), texts) :=
    argumentDocsSpells around.inArm head (around.at + head.size) arguments within sound
  let picked := pickSpells (argumentDocs around.inArm head (around.at + head.size) arguments).snd lastTexts lastSpells
  rewrite <- texts, appDocsIs head arguments around then
    appFromSpells
      (around.at + 1)
      (1 + keptFront head arguments)
      (commentBetween head arguments)
      (commentBetween head (arguments.take (1 + keptFront head arguments - 1)))
      (head.el around)
      ((argumentDocs around.inArm head (around.at + head.size) arguments).snd.getOrElse (Nothing, None)).fst
      (argumentDocs around.inArm head (around.at + head.size) arguments).fst
      ((argumentDocs around.inArm head (around.at + head.size) arguments).snd.getOrElse (Nothing, None)).snd
      (head.spelt around.hoisted)
      frontTexts
      lastTexts
      (elSpells head around headWithin headSound)
      frontSpells
      picked.left
      picked.right

--| The rules print an expression spelling its tokens, wherever it stands.
--|
--| Proof idea: Induction on the expression, as `elCalm`: a token by `leafSpells`, a node by its rule's lemma inside `framedExprSpells`.
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
          (Bool.andLeft (Bool.andRight sound))
          (w s below => elSpells inner below w s))
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
    | Tuple open items comma close =>
      framedExprSpells
        (Tuple open items comma close)
        around
        (commaBracket (list := False) open items close { around | hoisted = True })
        within
        sound
        (spellsGroup _ _
          (bracketContentSpells False open items close
            { around | hoisted = True }
            within
            (Bool.andLeft (Bool.andRight sound))
            (Bool.andLeft sound)
            (Bool.andRight (Bool.andRight sound))
            (allElSpells items within (Bool.andLeft (Bool.andRight sound)))))
    | ListOf open items comma close =>
      framedExprSpells
        (ListOf open items comma close)
        around
        (commaBracket (list := True) open items close { around | hoisted = True })
        within
        sound
        (spellsGroup _ _
          (bracketContentSpells True open items close
            { around | hoisted = True }
            within
            (Bool.andLeft (Bool.andRight sound))
            (Bool.andLeft sound)
            (Bool.andRight (Bool.andRight sound))
            (allElSpells items within (Bool.andLeft (Bool.andRight sound)))))
    | App head arguments =>
      framedExprSpells
        (App head arguments)
        around
        (appDocs head arguments { around | hoisted = True }).doc
        within
        sound
        (appDocsSpells head arguments
          { around | hoisted = True }
          (Bool.andLeft within)
          (Bool.andLeft sound)
          (Bool.andRight within)
          (Bool.andRight sound)).left

theorem spellsSuffixExample: Spells (LineSuffix "-- a") ["-- a"] := spellsSuffix "-- a" byComputing byComputing

theorem commentNotLayoutExample: isLayout "-- a" = False := commentNotLayout "-- a" byComputing

-- The body after `:=`.

theorem spellsEachAppend ∀ (texts: List Text) (front back: List Doc)
    (first: SpellsEach texts front)
    (second: SpellsEach texts back):
    SpellsEach texts (front ++ back) :=
  match front, first with
    | [], _ => second
    | [doc, ..rest], (spells, others) => (spells, (spellsEachAppend texts rest back others second))

theorem optionListSpells ∀ (option: Option Doc) (texts: List Text)
    (spells: ∀ (doc: Doc) => option = Some doc → Spells doc texts):
    SpellsEach texts (optionList option) :=
  match option, spells with
    | None, _ => byComputing
    | Some doc, spells => (spells doc byComputing, byComputing)

theorem unnotedNotes ∀ (word: Word) (unnoted: word.noted = False): word.notesAt False = [] := match word with
  | { text, comments = { above = [], after, blankBefore } } => byComputing

--| Own-line comments above the first token that has none: the same either way.
theorem speltUnnoted ∀ (expr: Expr)
    (within: expr.within1 = True)
    (unnoted: expr.noted = False):
    expr.spelt False = expr.spelt True :=
  rewrite speltLead expr False within, unnotedNotes expr.lead (rewrite <- firstWordLead expr within then unnoted)

theorem callHugSpells ∀ (value: Expr) (inside: Around)
    (within: value.within1 = True)
    (sound: value.sound = True):
    ∀ (open: Doc) => value.callHug inside = Some open → Spells open (value.spelt inside.hoisted) :=
  match value with
    | App head arguments =>
      (open same =>
        (appDocsSpells head arguments inside
              (Bool.andLeft within)
              (Bool.andLeft sound)
              (Bool.andRight within)
              (Bool.andRight sound)).right open same)
    | _ => (open same => cases)

theorem spellsTexts ∀ (doc: Doc) (texts texts': List Text)
    (spells: Spells doc texts)
    (same: texts = texts'):
    Spells doc texts' :=
  rewrite <- same then spells

--| A hug after a space spells what the hug does.
--|
--| Proof idea: Cases on the hug.
theorem spacedHugSpells ∀ (hug: Option Doc) (texts: List Text)
    (each: ∀ (open: Doc) => hug = Some open → Spells open texts):
    ∀ (doc: Doc) => hug.map (open => Doc.concat [Doc.text " ", open]) = Some doc → Spells doc texts :=
  match hug, each with
    | None, _ => (doc same => cases)
    | Some opened, each =>
      (doc same =>
        rewrite <- Option.someInjective same then
          spellsConcat _ _
            (spellsCons
              (Doc.text " ")
              [opened]
              []
              texts
              spellsSpace
              (spellsLast opened texts (each opened byComputing))))

--| A body after `:=` spells the value in both its forms.
--|
--| Proof idea: The value's element (`elSpells`); below it is a nest, the choice's options (flat, one line below, the hug on the line, below) each spell the same.
theorem bodyAfterSpells ∀ (value: Expr) (assign: Word) (around: Around) (semi: Bool)
    (within: value.within1 = True)
    (sound: value.sound = True)
    (low: around.hoisted = False):
    Spells (bodyAfter value assign around semi).fst (value.spelt False)
      ∧ Spells (bodyAfter value assign around semi).snd (value.spelt False) :=
  let docSpells: Spells (value.el around) (value.spelt False) :=
    spellsTexts _ _ _ (elSpells value around within sound) (rewrite low)
  let belowSpells: Spells (Nest 2 (Doc.concat [HardLine, value.el around])) (value.spelt False) :=
    spellsNest 2 _ _
      (spellsConcat _ _
        (spellsCons HardLine [value.el around] [] (value.spelt False) spellsHardLine (spellsLast _ _ docSpells)))
  let inside: Around := { around | hoisted = True }
  rewrite matchedNone value inside within,
      valueElPlain value around semi within,
      lambdaHugNone value semi inside (value.el around) within then
    match plain: assign.trails || value.noted || value.isBlock with
      | True => (belowSpells, belowSpells)
      | False =>
        let unnoted: value.noted = False :=
          Bool.orFalseLeft value.noted value.isBlock
            (Bool.orFalseRight assign.trails (value.noted || value.isBlock) plain)
        let hugSpells: ∀ (open: Doc) => value.callHug inside = Some open → Spells open (value.spelt False) :=
          (open same =>
            spellsTexts _ _ _
              (callHugSpells value inside within sound open same)
              (speltUnnoted value within unnoted).flipped)
        let flat: Spells (Flatten (Doc.concat [Doc.text " ", value.el around])) (value.spelt False) :=
          spellsFlatten _ _
            (spellsConcat _ _
              (spellsCons
                (Doc.text " ")
                [value.el around]
                []
                (value.spelt False)
                spellsSpace
                (spellsLast _ _ docSpells)))
        (
          belowSpells,
          spellsChoice (value.spelt False) _ _ (
            flat,
            spellsEachAppend
              (value.spelt False)
              (if value.opensBracket || (value.callHug inside).isSome then [OneLineBelow (value.el around)] else [])
              ((if value.opensBracket then [Doc.concat [Doc.text " ", value.el around]]
                else optionList ((value.callHug inside).map (open => Doc.concat [Doc.text " ", open])))
                ++ [Nest 2 (Doc.concat [HardLine, value.el around])])
              (match value.opensBracket || (value.callHug inside).isSome with
                | True => ((spellsOneLineBelow _ _ docSpells), byComputing)
                | False => byComputing)
              (spellsEachAppend
                (value.spelt False)
                (if value.opensBracket then [Doc.concat [Doc.text " ", value.el around]]
                 else optionList ((value.callHug inside).map (open => Doc.concat [Doc.text " ", open])))
                [Nest 2 (Doc.concat [HardLine, value.el around])]
                (match value.opensBracket with
                  | True => (
                    (spellsConcat _ _
                      (spellsCons
                        (Doc.text " ")
                        [value.el around]
                        []
                        (value.spelt False)
                        spellsSpace
                        (spellsLast _ _ docSpells))),
                    byComputing
                  )
                  | False => optionListSpells _ _ (spacedHugSpells _ _ hugSpells))
                (belowSpells, byComputing))
          )
        )

-- Declarations.

--| A definition's document spells its header, its `:=` and its body.
--|
--| Proof idea: A concat of the header in an `IdGroup`, a space, the `:=` and the body's `IfBroken`.
theorem defFromSpells ∀ (headerDoc assignDoc below choice: Doc)
    (breaks: Bool) (headerTexts assignTexts bodyTexts: List Text)
    (header: Spells headerDoc headerTexts)
    (assigns: Spells assignDoc assignTexts)
    (belowSpells: Spells below bodyTexts)
    (choiceSpells: Spells choice bodyTexts):
    Spells (defFrom headerDoc breaks assignDoc below choice) (headerTexts ++ assignTexts ++ bodyTexts) :=
  spellsConcat _ _
    (spellsCons
      (IdGroup 0 headerDoc breaks)
      [Doc.text " ", assignDoc, IfBroken 0 below choice]
      headerTexts
      (assignTexts ++ bodyTexts)
      (spellsIdGroup 0 headerDoc breaks headerTexts header)
      (spellsCons
        (Doc.text " ")
        [assignDoc, IfBroken 0 below choice]
        []
        (assignTexts ++ bodyTexts)
        spellsSpace
        (spellsCons assignDoc
          [IfBroken 0 below choice]
          assignTexts
          bodyTexts
          assigns
          (spellsLast
            (IfBroken 0 below choice)
            bodyTexts
            (spellsIfBroken 0 below choice bodyTexts belowSpells choiceSpells)))))

--| A definition's tokens in order, as the rules write them: the keyword's own-line comments are the file's.
def Decl.spelt: Decl → List Text
  | Definition _ header (Assigned colonEq value) =>
    (((fixedWord "def" header.keyword).spelledAt True ++ header.name.spelledAt False)
      ++ (fixedWord ":" header.colon).spelledAt False
      ++ header.result.spelt False)
      ++ (fixedWord ":=" colonEq).spelledAt False
      ++ value.spelt False
  | _ => []

def Decl.sound: Decl → Bool
  | Definition _ header (Assigned colonEq value) =>
    (fixedWord "def" header.keyword).sound
      && header.name.sound
      && (fixedWord ":" header.colon).sound
      && header.result.sound
      && (fixedWord ":=" colonEq).sound
      && value.sound
  | _ => False

theorem typedSpells ∀ (trails: Bool) (typeDoc: Doc) (texts: List Text)
    (spells: Spells typeDoc texts):
    SpellsAll (if trails then [Nest 4 (Doc.concat [HardLine, typeDoc])] else [Doc.text " ", Nest 4 typeDoc]) texts :=
  match trails with
    | True =>
      spellsLast _ _
        (spellsNest 4 _ _
          (spellsConcat _ _ (spellsCons HardLine [typeDoc] [] texts spellsHardLine (spellsLast _ _ spells))))
    | False =>
      spellsCons (Doc.text " ") [Nest 4 typeDoc] [] texts spellsSpace (spellsLast _ _ (spellsNest 4 _ _ spells))

--| A definition with no parameters spells its tokens in order.
--|
--| Proof idea: `defFromSpells` with the header (the head words spaced, the colon, the type: `typedSpells`), the `:=`'s leaf and `bodyAfterSpells`.
theorem plainDefSpells ∀ (keyword: Comments) (name: Word) (colon: Comments) (result: Expr)
    (colonEq: Comments) (value: Expr)
    (resultWithin: result.within1 = True)
    (valueWithin: value.within1 = True)
    (keywordSound: (fixedWord "def" keyword).sound = True)
    (nameSound: name.sound = True)
    (colonSound: (fixedWord ":" colon).sound = True)
    (resultSound: result.sound = True)
    (assignSound: (fixedWord ":=" colonEq).sound = True)
    (valueSound: value.sound = True):
    Spells
      (plainDef keyword name colon result colonEq value)
      ((((fixedWord "def" keyword).spelledAt True ++ name.spelledAt False)
        ++ (fixedWord ":" colon).spelledAt False
        ++ result.spelt False)
        ++ (fixedWord ":=" colonEq).spelledAt False
        ++ value.spelt False) :=
  let start: Around := { before = False, hoisted = True, item = False, at = 0, inArm = False }
  let colonWord := fixedWord ":" colon
  let assign := fixedWord ":=" colonEq
  let typeSpells := elSpells result (start.next colonWord.trails 3) resultWithin resultSound
  let bodySpells :=
    bodyAfterSpells value assign (start.next assign.trails (4 + result.size)) False valueWithin valueSound byComputing
  let headSpells: Spells
    (spaced (headDocs start [fixedWord "def" keyword, name]))
    ((fixedWord "def" keyword).spelledAt True ++ name.spelledAt False) :=
    spellsSpaced _ _
      (spellsCons _ _ _ _
        (leafSpells (fixedWord "def" keyword) start 0 keywordSound)
        (spellsLast _ _ (leafSpells name (start.next (fixedWord "def" keyword).trails 1) 1 nameSound)))
  defFromSpells _ _ _ _ _ _ _ _
    (spellsConcat _ _
      (spellsAllSame _ _ _
        (spellsAppend _ _ _ _
          (spellsCons _ _ _ _ headSpells
            (spellsLast _ _
              (leafSpells colonWord (start.next (trailsBack [name, fixedWord "def" keyword]) 2) 2 colonSound)))
          (typedSpells colonWord.trails _ _ typeSpells))
        (List.appendAssoc _ _ _)))
    (leafSpells assign (start.next result.trails (3 + result.size)) (3 + result.size) assignSound)
    bodySpells.left
    bodySpells.right

--| The document a slice 1 declaration has spells the declaration's tokens.
--|
--| Proof idea: `plainDefIs` and `plainDefSpells`, with the tokens' soundness taken from the declaration's.
theorem doc1Spells ∀ (decl: Decl) (doc: Doc)
    (within: decl.within1 = True)
    (sound: decl.sound = True)
    (shows: decl.doc1 = Some doc):
    Spells doc decl.spelt :=
  match decl with
    | Definition [] header (Assigned colonEq value) =>
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
          rewrite <- Option.someInjective shows then
            spellsEq _ _ _
              (plainDefIs keyword name colon result colonEq value)
              (plainDefSpells keyword name colon result colonEq value
                (Bool.andRight (Bool.andLeft within))
                (Bool.andRight within)
                (Bool.andLeft sound)
                (Bool.andLeft (Bool.andRight sound))
                (Bool.andLeft (Bool.andRight (Bool.andRight sound)))
                (Bool.andLeft (Bool.andRight (Bool.andRight (Bool.andRight sound))))
                (Bool.andLeft (Bool.andRight (Bool.andRight (Bool.andRight (Bool.andRight sound)))))
                (Bool.andRight (Bool.andRight (Bool.andRight (Bool.andRight (Bool.andRight sound))))))
        | _ => cases

-- What the printer writes.

--| A word that isn't a closer or comma.
def notCloser (text: Text): Bool := !(isCloserText text || text == ",")

--| A word that isn't a comment.
def notComment (text: Text): Bool := !text.startsWith "--"

theorem closersApart ∀ (text: Text) (closes: closesText text): notCloser text = False := match closes with
  | Inl same => rewrite same
  | Inr same => rewrite same

theorem commentsApart ∀ (text: Text) (comment: commentsText text): notComment text = False :=
  rewrite Bool.andLeft comment

theorem closersApartExample: notCloser ")" = False := closersApart ")" (Inl byComputing)

theorem commentsApartExample: notComment "-- a" = False := commentsApart "-- a" byComputing

--| `printedSpells`: at any width, the text the rules print for a declaration spells the declaration: its words,
--| less the closers and commas, are the tokens and comments of the tree in order; and its words, less the
--| comments, are the tokens, closers and commas in order. The two together say what `Std.Doc`'s `printedWords`
--| allows of a document with closers and trailing comments, which may change places on a line (`Closing` is
--| written before the comment waiting there).
--|
--| Proof idea: `doc1Spells` gives the document's words (each option of each choice the same, closers and comments
--| of the rules' kinds), and `printedWords` says the printer writes them in order but for a closer and a comment
--| changing places.
theorem printedSpells ∀ (decl: Decl) (doc: Doc) (width: Nat)
    (within: decl.within1 = True)
    (sound: decl.sound = True)
    (shows: decl.doc1 = Some doc):
    (wordsOf (printedPieces doc width)).filter notCloser = decl.spelt.filter notCloser
      ∧ (wordsOf (printedPieces doc width)).filter notComment = decl.spelt.filter notComment :=
  let (uniform, marked, words) := doc1Spells decl doc within sound shows
  (
    rewrite <- words then printedWords notCloser closesText commentsText doc width uniform marked (Inl closersApart),
    rewrite <- words then printedWords notComment closesText commentsText doc width uniform marked (Inr commentsApart)
  )

-- From what the glue has to what the rules need.

theorem allAppendBool ∀ (xs ys: List Word) (p: Word → Bool): (xs ++ ys).all p = (xs.all p && ys.all p) := match xs with
  | [] => byComputing
  | [first, ..rest] =>
    match p first with
      | True => allAppendBool rest ys p
      | False => byComputing

theorem allAndBool ∀ (xs: List Word) (p q: Word → Bool)
    (first: xs.all p = True)
    (second: xs.all q = True):
    xs.all (word => p word && q word) = True :=
  match xs with
    | [] => byComputing
    | [word, ..rest] =>
      Bool.andIntro
        (Bool.andIntro (Bool.andLeft first) (Bool.andLeft second))
        (allAndBool rest p q (Bool.andRight first) (Bool.andRight second))

--| A token's own-line comments and trailing comment are as rule N leaves them, as `settled1` says.
def Word.commented (word: Word): Bool := word.comments.texts.all commentText

theorem textsAll ∀ (above: List Note) (after: Option Text):
    ((above.map (note => note.text) ++ after.toList).all commentText) = (notesSound above && afterSound after) :=
  match above, after with
    | [], None => byComputing
    | [], Some comment =>
      match commentText comment with
        | True => byComputing
        | False => byComputing
    | [note, ..rest], after =>
      match commentText note.text with
        | True => textsAll rest after
        | False => byComputing

theorem commentedSound ∀ (word: Word)
    (commented: word.commented = True)
    (real: (!isLayout word.text) = True):
    word.sound = True :=
  Bool.andIntro real (rewrite <- textsAll word.comments.above word.comments.after then commented)

theorem allConsBool ∀ (word: Word) (rest: List Word) (p: Word → Bool)
    (all: [word, ..rest].all p = True):
    p word = True ∧ rest.all p = True :=
  match p word with | True => (byComputing, all)

theorem allSplitBool ∀ (xs ys: List Word) (p: Word → Bool)
    (all: (xs ++ ys).all p = True):
    xs.all p = True ∧ ys.all p = True :=
  match xs with
    | [] => (byComputing, all)
    | [first, ..rest] =>
      let (headOk, tailOk) := allConsBool first (rest ++ ys) p all
      let (restOk, backOk) := allSplitBool rest ys p tailOk
      (Bool.andIntro headOk restOk, backOk)

theorem soundOfAllItems ∀ (items: List Expr)
    (within: allWithin1 items = True)
    (all: (itemsWords items).all Word.sound = True):
    allSound items = True :=
  match items with
    | [] => byComputing
    | [first, ..rest] =>
      let (firstOk, restOk) := allSplitBool first.words (itemsWords rest) Word.sound all
      Bool.andIntro
        (soundOfAll first (Bool.andLeft within) firstOk)
        (soundOfAllItems rest (Bool.andRight within) restOk)

--| The tokens of a slice 1 expression are all sound if its sound structurally.
--|
--| Proof idea: Induction on the expression, splitting the list at each node.
theorem soundOfAll ∀ (expr: Expr)
    (within: expr.within1 = True)
    (all: expr.words.all Word.sound = True):
    expr.sound = True :=
  match expr with
    | Atom kind word => (allConsBool word [] Word.sound all).left
    | Paren open inner close =>
      let (frontOk, closeOk) := allSplitBool [open, ..inner.words] [close] Word.sound all
      let (openOk, innerOk) := allConsBool open inner.words Word.sound frontOk
      Bool.andIntro openOk
        (Bool.andIntro (soundOfAll inner within innerOk) (allConsBool close [] Word.sound closeOk).left)
    | Tuple open items comma close =>
      let (frontOk, closeOk) := allSplitBool [open, ..itemsWords items] [close] Word.sound all
      let (openOk, itemsOk) := allConsBool open (itemsWords items) Word.sound frontOk
      Bool.andIntro openOk
        (Bool.andIntro (soundOfAllItems items within itemsOk) (allConsBool close [] Word.sound closeOk).left)
    | ListOf open items comma close =>
      let (frontOk, closeOk) := allSplitBool [open, ..itemsWords items] [close] Word.sound all
      let (openOk, itemsOk) := allConsBool open (itemsWords items) Word.sound frontOk
      Bool.andIntro openOk
        (Bool.andIntro (soundOfAllItems items within itemsOk) (allConsBool close [] Word.sound closeOk).left)
    | App head arguments =>
      let (headOk, argumentsOk) := allSplitBool head.words (itemsWords arguments) Word.sound all
      Bool.andIntro
        (soundOfAll head (Bool.andLeft within) headOk)
        (soundOfAllItems arguments (Bool.andRight within) argumentsOk)
    | Infix kind left operator right =>
      match kind with
        | InfixBinary =>
          let (leftOk, restOk) := allSplitBool left.words [operator, ..right.words] Word.sound all
          let (operatorOk, rightOk) := allConsBool operator right.words Word.sound restOk
          Bool.andIntro
            (soundOfAll left (Bool.andLeft within) leftOk)
            (Bool.andIntro operatorOk (soundOfAll right (Bool.andRight within) rightOk))
        | InfixArrow =>
          let (leftOk, restOk) := allSplitBool left.words [operator, ..right.words] Word.sound all
          let (operatorOk, rightOk) := allConsBool operator right.words Word.sound restOk
          Bool.andIntro
            (soundOfAll left (Bool.andLeft within) leftOk)
            (Bool.andIntro operatorOk (soundOfAll right (Bool.andRight within) rightOk))
        | _ => cases
    | Prefix operator operand =>
      let (operatorOk, operandOk) := allConsBool operator operand.words Word.sound all
      Bool.andIntro operatorOk (soundOfAll operand within operandOk)

theorem allMapBool ∀ (xs: List Word) (p q: Word → Bool)
    (all: xs.all p = True)
    (implies: ∀ (word: Word) => p word = True → q word = True):
    xs.all q = True :=
  match xs with
    | [] => byComputing
    | [first, ..rest] =>
      let (firstOk, restOk) := allConsBool first rest p all
      Bool.andIntro (implies first firstOk) (allMapBool rest p q restOk implies)

--| Every token of a declaration has text that isn't layout.
def Decl.real (decl: Decl): Bool := decl.words.all (word => !isLayout word.text)

--| A declaration is sound if it is settled and no token's text is layout.
--|
--| Proof idea: Every token is commented-and-real (`allAndBool`), hence sound (`commentedSound`); split the list into the keyword, the name, the colon, the type, the `:=` and the value.
theorem declSoundOfSettled ∀ (decl: Decl)
    (within: decl.within1 = True)
    (settled: decl.settled1 = True)
    (real: decl.real = True):
    decl.sound = True :=
  match decl with
    | Definition [] header (Assigned colonEq value) =>
      let commented := Bool.andRight (Bool.andRight settled)
      let sound :=
        allMapBool
          (Decl.words (Definition [] header (Assigned colonEq value)))
          (word => word.commented && !isLayout word.text)
          Word.sound
          (allAndBool _ Word.commented (word => !isLayout word.text) commented real)
          (word both => commentedSound word (Bool.andLeft both) (Bool.andRight both))
      let tail := header.result.words ++ [fixedWord ":=" colonEq, ..value.words]
      let (keywordOk, afterKeyword) :=
        allConsBool (fixedWord "def" header.keyword) [header.name, fixedWord ":" header.colon, ..tail] Word.sound sound
      let (nameOk, afterName) := allConsBool header.name [fixedWord ":" header.colon, ..tail] Word.sound afterKeyword
      let (colonOk, afterColon) := allConsBool (fixedWord ":" header.colon) tail Word.sound afterName
      let (resultOk, afterResult) :=
        allSplitBool header.result.words [fixedWord ":=" colonEq, ..value.words] Word.sound afterColon
      let (assignOk, valueOk) := allConsBool (fixedWord ":=" colonEq) value.words Word.sound afterResult
      Bool.andIntro keywordOk
        (Bool.andIntro nameOk
          (Bool.andIntro colonOk
            (Bool.andIntro
              (soundOfAll header.result (headerResultWithin header (Bool.andLeft within)) resultOk)
              (Bool.andIntro assignOk (soundOfAll value (Bool.andRight within) valueOk)))))

--| `printedSpells`, from what the passes establish: rule N's `settled1` and tokens that aren't layout.
theorem printedSpellsSettled ∀ (decl: Decl) (doc: Doc) (width: Nat)
    (within: decl.within1 = True)
    (settled: decl.settled1 = True)
    (real: decl.real = True)
    (shows: decl.doc1 = Some doc):
    (wordsOf (printedPieces doc width)).filter notCloser = decl.spelt.filter notCloser
      ∧ (wordsOf (printedPieces doc width)).filter notComment = decl.spelt.filter notComment :=
  printedSpells decl doc width within (declSoundOfSettled decl within settled real) shows

-- A declaration the theorems apply to, so their hypotheses can be met.

--| `def d: A := g [a, b]`.
def exampleDecl: Decl :=
  Definition []
    {
      exportKeyword = None,
      opaqueKeyword = None,
      kind = DefPlain,
      keyword = Comments.none,
      name = fixedWord "d" Comments.none,
      forallKeyword = None,
      params = [],
      colon = Comments.none,
      result = Atom Upper (fixedWord "A" Comments.none),
      decreasingClause = None,
      unfoldingClause = None
    }
    (Assigned Comments.none
      (App (Atom Lower (fixedWord "g" Comments.none)) [
        ListOf
          (fixedWord "[" Comments.none)
          [Atom Lower (fixedWord "a" Comments.none), Atom Lower (fixedWord "b" Comments.none)]
          False
          (fixedWord "]" Comments.none)
      ]))

theorem printedSpellsExample ∀ (width: Nat):
    (wordsOf (printedPieces (exampleDecl.doc1.getOrElse Nothing) width)).filter notCloser
      = exampleDecl.spelt.filter notCloser
      ∧ (wordsOf (printedPieces (exampleDecl.doc1.getOrElse Nothing) width)).filter notComment
        = exampleDecl.spelt.filter notComment :=
  printedSpells exampleDecl (exampleDecl.doc1.getOrElse Nothing) width byComputing byComputing byComputing

theorem calmPrintsExample: ({ decls = [exampleDecl], end = Comments.none }: SourceFile).calm.printed1
      = ({ decls = [exampleDecl], end = Comments.none }: SourceFile).printed1 :=
  Fmt.CalmProofs.calmPrints { decls = [exampleDecl], end = Comments.none } byComputing byComputing

--| The text a declaration prints is the printer's pieces joined, and they spell the declaration (`printedSpells`).
theorem printedSpellsText ∀ (decl: Decl) (text: Text)
    (within: decl.within1 = True)
    (settled: decl.settled1 = True)
    (real: decl.real = True)
    (printed: decl.printed1 = Some text):
    ∃ (doc: Doc) => decl.doc1 = Some doc
      ∧ text = (printedPieces doc width).joinWith ""
      ∧ (wordsOf (printedPieces doc width)).filter notCloser = decl.spelt.filter notCloser
      ∧ (wordsOf (printedPieces doc width)).filter notComment = decl.spelt.filter notComment :=
  match shows: decl.doc1 with
    | None => cases
    | Some doc =>
      let mapped: Doc.print doc width = text := Option.someInjective (rewrite within at printed then printed)
      let spelled := printedSpellsSettled decl doc width within settled real shows
      (doc, byComputing, Eq.trans mapped.flipped (printIsPieces doc width), spelled.left, spelled.right)
