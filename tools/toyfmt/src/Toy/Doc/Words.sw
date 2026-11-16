--| Every reading writes the document's words, in order. A word is a piece
--| of output that isn't layout (spaces, indentation, a line break): the
--| text of a chunk or a trailing comment. Which way groups, fills and
--| choices go changes only the layout between the words, as long as every
--| option of a choice has the same words (`Uniform`); a trailing comment
--| is written before any text that follows it in the document. Through
--| every reading the words are the document's (`readingWords`): nothing
--| lost, repeated or moved.

namespace Toy.Doc.Proofs
import Toy.Doc (..)
import Std (Bool, Eq, List, Nat, Option, Text, Void)

--| Whether a piece of output is only layout: spaces (a gap, indentation,
--| or nothing at all) or a line break.
def isLayout (piece: Text): Bool := piece.all (char => char == ' ') || piece == "\n"

--| The pieces that aren't layout.
def wordsOf (pieces: List Text): List Text := pieces.filter (piece => not (isLayout piece))

--| What the printer has written so far, as words.
def Printer.written (printer: Printer): List Text := wordsOf printer.out.reverse

--| The words printed so far, the trailing comments still waiting last.
def Printer.words (printer: Printer): List Text := printer.written ++ wordsOf printer.suffixes

theorem emptyIsLayout ∀ (text: Text) (empty: text.isEmpty = True): isLayout text = True := match text, empty with
  | MkText [], _ => byComputing

theorem spacesIsLayout ∀ (text: Text) (spaces: text.all (char => char == ' ') = True): isLayout text = True :=
  rewrite repeatedly [spaces]

theorem indentSpaces ∀ (indent: Nat): (" ".repeat indent).all (char => char == ' ') = True := match indent with
  | Zero => byComputing
  | Succ less => indentSpaces less

theorem wordsSnoc ∀ (piece: Text) (out: List Text):
    wordsOf [piece, ..out].reverse = wordsOf out.reverse ++ wordsOf [piece] :=
  rewrite repeatedly [List.reverseCons, List.filterAppend]

theorem layoutNoWord ∀ (piece: Text) (layout: isLayout piece = True): wordsOf [piece] = [] :=
  rewrite repeatedly [layout]

--| A piece of layout adds no word.
theorem layoutSnoc ∀ (piece: Text) (out: List Text)
    (layout: isLayout piece = True):
    wordsOf [piece, ..out].reverse = wordsOf out.reverse :=
  rewrite repeatedly [wordsSnoc, layoutNoWord piece layout, List.appendNil]

theorem trimWords ∀ (out: List Text): wordsOf (trimSpaces out).reverse = wordsOf out.reverse := match out with
  | [] => byComputing
  | [last, ..earlier] =>
    match spaces: last.all (char => char == ' ') with
      | True => rewrite layoutSnoc last earlier (spacesIsLayout last spaces) then trimWords earlier
      | False => byComputing

theorem payIndentWritten ∀ (printer: Printer):
    printer.payIndent.written = printer.written ∧ printer.payIndent.suffixes = printer.suffixes :=
  match owed: printer.owed with
    | None => (byComputing, byComputing)
    | Some Zero => (byComputing, byComputing)
    | Some (Succ less) =>
      ((layoutSnoc (" ".repeat (Succ less)) printer.out (spacesIsLayout _ (indentSpaces (Succ less)))), byComputing)

--| Text put on the line is the next word written, if it is one.
theorem putWritten ∀ (printer: Printer) (text: Text) (width: Nat):
    (printer.put text width).written = printer.written ++ wordsOf [text]
      ∧ (printer.put text width).suffixes = printer.suffixes :=
  match payIndentWritten printer with
    | (written, suffixes) => ((rewrite <- written then wordsSnoc text printer.payIndent.out), suffixes)

theorem flushOneWritten ∀ (printer: Printer) (comment: Text):
    (printer.flushOne comment).written = printer.written ++ wordsOf [comment]
      ∧ (printer.flushOne comment).suffixes = printer.suffixes :=
  match start: printer.atLineStart with
    | True =>
      match payIndentWritten printer with
        | (written, suffixes) => ((rewrite <- written then wordsSnoc comment printer.payIndent.out), suffixes)
    | False =>
      (rewrite repeatedly [wordsSnoc comment [" ", ..printer.out], layoutSnoc " " printer.out byComputing], byComputing)

--| Comments flushed one after another are the next words written.
theorem flushEachWritten ∀ (comments: List Text) (printer: Printer):
    (comments.foldLeft printer Printer.flushOne).written = printer.written ++ wordsOf comments
      ∧ (comments.foldLeft printer Printer.flushOne).suffixes = printer.suffixes :=
  match comments with
    | [] => (rewrite repeatedly [List.appendNil], byComputing)
    | [comment, ..later] =>
      match flushOneWritten printer comment, flushEachWritten later (printer.flushOne comment) with
        | (written, suffixes), (laterWritten, laterSuffixes) => (
          rewrite repeatedly [laterWritten, written, List.appendAssoc, <- List.filterAppend [comment]],
          (Eq.trans laterSuffixes suffixes)
        )

--| Flushing writes the waiting comments: the words stay as they were,
--| and none waits.
theorem flushWritten ∀ (printer: Printer):
    printer.flushSuffixes.written = printer.words ∧ printer.flushSuffixes.suffixes = [] :=
  flushEachWritten printer.suffixes { printer | suffixes = [] }

--| A line break writes the waiting comments and no other word.
theorem newlineWritten ∀ (printer: Printer) (indent: Nat):
    (printer.newline indent).written = printer.words ∧ (printer.newline indent).suffixes = [] :=
  match flushWritten { printer | out = trimSpaces printer.out } with
    | (written, suffixes) => (
      rewrite repeatedly [
        layoutSnoc "\n" ({ printer | out = trimSpaces printer.out }).flushSuffixes.out byComputing,
        <- trimWords printer.out
      ],
      suffixes
    )

theorem newlineWords ∀ (printer: Printer) (indent: Nat): (printer.newline indent).words = printer.words :=
  match newlineWritten printer indent with
    | (written, suffixes) => rewrite repeatedly [written, suffixes, List.appendNil]

theorem emptyNil ∀ (items: List a) (empty: items.isEmpty = True): items = [] := match items, empty with
  | [], _ => byComputing

--| With no comment waiting, text put on the line is the next word.
theorem putClearWords ∀ (printer: Printer) (text: Text) (width: Nat)
    (clear: printer.suffixes = []):
    (printer.put text width).words = printer.written ++ wordsOf [text] :=
  match putWritten printer text width with
    | (written, suffixes) => rewrite repeatedly [written, suffixes, clear, List.appendNil]

--| Text written is the next word, after any comment that was waiting.
theorem writeWords ∀ (printer: Printer) (indent: Nat) (text: Text) (width: Nat):
    (printer.write indent text width).words = printer.words ++ wordsOf [text] :=
  match empty: text.isEmpty with
    | True => rewrite repeatedly [layoutNoWord text (emptyIsLayout text empty), List.appendNil]
    | False =>
      match waiting: printer.suffixes.isEmpty with
        | True =>
          let clear := emptyNil printer.suffixes waiting
          rewrite repeatedly [putClearWords printer text width clear, clear, List.appendNil]
        | False =>
          match spaces: text.all (char => char == ' ') with
            | True => rewrite repeatedly [List.appendNil]
            | False =>
              match newlineWritten printer (printer.continuation indent) with
                | (brokenWritten, brokenSuffixes) =>
                  rewrite repeatedly [<- brokenWritten, putClearWords _ text width brokenSuffixes, spaces]

theorem lineStartWords ∀ (printer: Printer) (indent: Nat): (printer.lineStart indent).words = printer.words :=
  match start: printer.atLineStart with
    | True => byComputing
    | False => newlineWords printer (printer.continuation indent)

theorem blankWords ∀ (printer: Printer): printer.blank.words = printer.words :=
  match blank: printer.atLineStart && printer.started && printer.newlinesAtEnd < 2 with
    | True => rewrite repeatedly [layoutSnoc "\n" printer.out byComputing]
    | False => byComputing

-- The document's words, and the readings.

--| The words of a document, in order: its chunks' texts and its trailing
--| comments, apart from layout. A choice's are its first option's; in a
--| `Uniform` document every option has the same.
def Doc.words: Doc → List Text
  | Chunk text _ => wordsOf [text]
  | LineSuffix comment => wordsOf [comment]
  | Nest _ inner => inner.words
  | Group inner _ => inner.words
  | Flatten inner => inner.words
  | OneLineBelow inner => inner.words
  | Concat docs => wordsAll docs
  | Fill items => wordsAll items
  | Choice options => wordsFirst options
  | _ => []

def wordsAll: List Doc → List Text
  | [] => []
  | [doc, ..docs] => doc.words ++ wordsAll docs

def wordsFirst: List Doc → List Text
  | [] => []
  | [doc, .._] => doc.words

--| Every option of every choice in the document has the same words.
def Uniform: Doc → Prop
  | Nest _ inner => Uniform inner
  | Group inner _ => Uniform inner
  | Flatten inner => Uniform inner
  | OneLineBelow inner => Uniform inner
  | Concat docs => AllUniform docs
  | Fill items => AllUniform items
  | Choice options => AllUniform options ∧ SameWords (wordsFirst options) options
  | _ => True

def AllUniform: List Doc → Prop
  | [] => True
  | [doc, ..docs] => Uniform doc ∧ AllUniform docs

--| Each of the documents has these words.
def SameWords (words: List Text): List Doc → Prop
  | [] => True
  | [doc, ..docs] => doc.words = words ∧ SameWords words docs

def Cmd.words: Cmd → List Text
  | Print _ _ doc => doc.words
  | FillSep _ item => item.words

--| The words the work list has still to write.
def stackWords: List Cmd → List Text
  | [] => []
  | [cmd, ..rest] => cmd.words ++ stackWords rest

def CmdUniform: Cmd → Prop
  | Print _ _ doc => Uniform doc
  | FillSep _ item => Uniform item

def StackUniform: List Cmd → Prop
  | [] => True
  | [cmd, ..rest] => CmdUniform cmd ∧ StackUniform rest

theorem stackWordsAppend ∀ (front back: List Cmd): stackWords (front ++ back) = stackWords front ++ stackWords back :=
  match front with
    | [] => byComputing
    | [cmd, ..rest] => rewrite repeatedly [stackWordsAppend rest back, List.appendAssoc]

theorem stackUniformAppend ∀ (front back: List Cmd)
    (frontUniform: StackUniform front)
    (backUniform: StackUniform back):
    StackUniform (front ++ back) :=
  match front, frontUniform with
    | [], _ => backUniform
    | [cmd, ..rest], Both first others => (first, (stackUniformAppend rest back others backUniform))

theorem printsWords ∀ (indent: Nat) (mode: Mode) (docs: List Doc):
    stackWords (docs.map (Print indent mode)) = wordsAll docs :=
  match docs with
    | [] => byComputing
    | [doc, ..rest] => rewrite repeatedly [printsWords indent mode rest]

theorem printsUniform ∀ (indent: Nat) (mode: Mode) (docs: List Doc)
    (uniform: AllUniform docs):
    StackUniform (docs.map (Print indent mode)) :=
  match docs, uniform with
    | [], _ => byComputing
    | [doc, ..rest], Both first others => (first, (printsUniform indent mode rest others))

theorem fillSepsWords ∀ (indent: Nat) (items: List Doc): stackWords (items.map (FillSep indent)) = wordsAll items :=
  match items with
    | [] => byComputing
    | [item, ..rest] => rewrite repeatedly [fillSepsWords indent rest]

theorem fillSepsUniform ∀ (indent: Nat) (items: List Doc)
    (uniform: AllUniform items):
    StackUniform (items.map (FillSep indent)) :=
  match items, uniform with
    | [], _ => byComputing
    | [item, ..rest], Both first others => (first, (fillSepsUniform indent rest others))

--| The lines a flat fill puts between its items are no words.
theorem joinLinesWords ∀ (items: List Doc): wordsAll (Doc.joinLines items) = wordsAll items := match items with
  | [] => byComputing
  | [only] => byComputing
  | [item, next, ..rest] => rewrite repeatedly [joinLinesWords [next, ..rest]]

theorem joinLinesUniform ∀ (items: List Doc) (uniform: AllUniform items): AllUniform (Doc.joinLines items) :=
  match items, uniform with
    | [], _ => byComputing
    | [only], given => given
    | [item, next, ..rest], Both first others => (first, byComputing, (joinLinesUniform [next, ..rest] others))

--| What a choice may print has the words all its options have.
theorem optionWords ∀ (chosen: Doc) (words: List Text) (option: Doc) (others: List Doc)
    (isOption: IsOption chosen [option, ..others])
    (same: SameWords words [option, ..others]):
    chosen.words = words :=
  match others, isOption, same with
    | [], picked, (first, _) => rewrite picked then first
    | [next, ..rest], Inl picked, (first, _) => rewrite picked then first
    | [next, ..rest], Inr later, (_, laterSame) => optionWords chosen words next rest later laterSame

theorem optionUniform ∀ (chosen: Doc) (options: List Doc)
    (isOption: IsOption chosen options)
    (uniform: AllUniform options):
    Uniform chosen :=
  match options, isOption, uniform with
    | [], picked, _ => rewrite repeatedly [picked]
    | [last], picked, Both first _ => rewrite picked then first
    | [option, next, ..rest], Inl picked, Both first _ => rewrite picked then first
    | [option, next, ..rest], Inr later, Both _ others => optionUniform chosen [next, ..rest] later others

theorem writeLayoutWords ∀ (printer: Printer) (indent: Nat) (text: Text) (width: Nat)
    (layout: isLayout text = True):
    (printer.write indent text width).words = printer.words :=
  rewrite repeatedly [writeWords, layoutNoWord text layout, List.appendNil]

--| A trailing comment set to wait is the next word.
theorem suffixWords ∀ (printer: Printer) (comment: Text):
    ({ printer | suffixes = printer.suffixes ++ [comment] }).words = printer.words ++ wordsOf [comment] :=
  rewrite repeatedly [List.filterAppend, List.appendAssoc]

theorem eitherWords ∀ (condition: Bool) (yes no: (Printer, List Cmd)) (target: List Text)
    (whenYes: yes.fst.words ++ stackWords yes.snd = target)
    (whenNo: no.fst.words ++ stackWords no.snd = target):
    (if condition then yes else no).fst.words ++ stackWords (if condition then yes else no).snd = target :=
  match condition with
    | True => whenYes
    | False => whenNo

theorem eitherUniform ∀ (condition: Bool) (yes no: (Printer, List Cmd))
    (whenYes: StackUniform yes.snd)
    (whenNo: StackUniform no.snd):
    StackUniform (if condition then yes else no).snd :=
  match condition with
    | True => whenYes
    | False => whenNo

theorem headOrWords ∀ (options: List Doc): (options.headOr Empty).words = wordsFirst options := match options with
  | [] => byComputing
  | [option, ..others] => byComputing

theorem headOrUniform ∀ (options: List Doc) (uniform: AllUniform options): Uniform (options.headOr Empty) :=
  match options, uniform with
    | [], _ => byComputing
    | [option, ..others], Both first _ => first

theorem chosenWords ∀ (chosen: Doc) (options: List Doc)
    (isOption: IsOption chosen options)
    (same: SameWords (wordsFirst options) options):
    chosen.words = wordsFirst options :=
  match options, isOption, same with
    | [], picked, _ => rewrite repeatedly [picked]
    | [option, ..others], picked, given => optionWords chosen option.words option others picked given

--| A step of a reading moves words from the work list to the printer, in
--| order: the words printed and those still to print, together, stay the
--| same.
theorem stepWords ∀ (printer: Printer) (cmd: Cmd) (rest: List Cmd) (result: (Printer, List Cmd))
    (steps: StepsTo printer cmd rest result)
    (uniform: CmdUniform cmd):
    result.fst.words ++ stackWords result.snd = printer.words ++ (cmd.words ++ stackWords rest) :=
  match cmd, steps, uniform with
    | FillSep indent item, Inl (Both _ flat), _ => rewrite repeatedly [flat, writeWords, List.appendAssoc]
    | FillSep indent item, Inr broken, _ => rewrite repeatedly [broken, newlineWords]
    | Print indent mode doc, steps, uniform =>
      match doc, steps, uniform with
        | Empty, steps, _ => rewrite repeatedly [steps]
        | BreakParent, steps, _ => rewrite repeatedly [steps]
        | Chunk text width, steps, _ => rewrite repeatedly [steps, writeWords, List.appendAssoc]
        | Line, steps, _ => rewrite steps then cases then rewrite repeatedly [writeLayoutWords, newlineWords]
        | SoftLine, steps, _ => rewrite steps then cases then rewrite repeatedly [newlineWords]
        | HardLine, steps, _ => rewrite repeatedly [steps, newlineWords]
        | LineStart, steps, _ => rewrite repeatedly [steps, lineStartWords]
        | CommentEnd, steps, _ => rewrite repeatedly [steps, newlineWords]
        | LineStartHere, steps, _ =>
          rewrite steps then
            eitherWords _
              ({ printer | owed = Some indent, lineIndent = indent }, rest)
              (printer.newline indent, rest) _
              byComputing
              (rewrite repeatedly [newlineWords])
        | Blank, steps, _ => rewrite repeatedly [steps, blankWords]
        | Nest more inner, steps, _ => rewrite repeatedly [steps]
        | OneLineBelow inner, steps, _ => rewrite repeatedly [steps]
        | Flatten inner, steps, _ => rewrite repeatedly [steps]
        | LineSuffix comment, steps, _ => rewrite repeatedly [steps, suffixWords, List.appendAssoc]
        | Group inner hard, Inl (Both _ flat), _ => rewrite repeatedly [flat]
        | Group inner hard, Inr (Both _ broken), _ => rewrite repeatedly [broken]
        | Concat docs, steps, _ => rewrite repeatedly [steps, stackWordsAppend, printsWords]
        | Fill [], steps, _ => rewrite repeatedly [steps]
        | Fill [first, ..others], Inl (Both _ flat), _ =>
          rewrite repeatedly [flat, stackWordsAppend, printsWords, joinLinesWords]
        | Fill [first, ..others], Inr (Both _ (Witness firstMode broken)), _ =>
          rewrite repeatedly [broken, stackWordsAppend, fillSepsWords, List.appendAssoc]
        | Choice options, Inl (Both _ flat), _ => rewrite repeatedly [flat, headOrWords]
        | Choice options, Inr (Both _ (Witness chosen (Both isOption broken))), Both _ same =>
          rewrite repeatedly [broken, chosenWords chosen options isOption same]

--| A step of a reading leaves the work list uniform.
theorem stepUniform ∀ (printer: Printer) (cmd: Cmd) (rest: List Cmd) (result: (Printer, List Cmd))
    (steps: StepsTo printer cmd rest result)
    (uniform: CmdUniform cmd)
    (restUniform: StackUniform rest):
    StackUniform result.snd :=
  match cmd, steps, uniform with
    | FillSep indent item, Inl (Both _ flat), uniform => rewrite flat then (uniform, restUniform)
    | FillSep indent item, Inr broken, uniform => rewrite broken then (uniform, restUniform)
    | Print indent mode doc, steps, uniform =>
      match doc, steps, uniform with
        | Empty, steps, _ => rewrite repeatedly [steps]
        | BreakParent, steps, _ => rewrite repeatedly [steps]
        | Chunk text width, steps, _ => rewrite repeatedly [steps]
        | Line, steps, _ =>
          rewrite steps then
            eitherUniform _ (printer.write indent " " 1, rest) (printer.newline indent, rest) restUniform restUniform
        | SoftLine, steps, _ =>
          rewrite steps then eitherUniform _ (printer, rest) (printer.newline indent, rest) restUniform restUniform
        | HardLine, steps, _ => rewrite repeatedly [steps]
        | LineStart, steps, _ => rewrite repeatedly [steps]
        | CommentEnd, steps, _ => rewrite repeatedly [steps]
        | LineStartHere, steps, _ =>
          rewrite steps then
            eitherUniform _
              ({ printer | owed = Some indent, lineIndent = indent }, rest)
              (printer.newline indent, rest)
              restUniform
              restUniform
        | Blank, steps, _ => rewrite repeatedly [steps]
        | Nest more inner, steps, uniform => rewrite steps then (uniform, restUniform)
        | OneLineBelow inner, steps, uniform => rewrite steps then (byComputing, uniform, restUniform)
        | Flatten inner, steps, uniform => rewrite steps then (uniform, restUniform)
        | LineSuffix comment, steps, _ => rewrite repeatedly [steps]
        | Group inner hard, Inl (Both _ flat), uniform => rewrite flat then (uniform, restUniform)
        | Group inner hard, Inr (Both _ broken), uniform => rewrite broken then (uniform, restUniform)
        | Concat docs, steps, uniform =>
          rewrite steps then
            stackUniformAppend (docs.map (Print indent mode)) rest (printsUniform indent mode docs uniform) restUniform
        | Fill [], steps, _ => rewrite repeatedly [steps]
        | Fill [first, ..others], Inl (Both _ flat), uniform =>
          rewrite flat then
            stackUniformAppend
              ((Doc.joinLines [first, ..others]).map (Print indent Flat))
              rest
              (printsUniform indent Flat (Doc.joinLines [first, ..others]) (joinLinesUniform [first, ..others] uniform))
              restUniform
        | Fill [first, ..others], Inr (Both _ (Witness firstMode broken)), Both firstUniform othersUniform =>
          rewrite broken then
            (
              firstUniform,
              (stackUniformAppend
                (others.map (FillSep indent))
                rest
                (fillSepsUniform indent others othersUniform)
                restUniform)
            )
        | Choice options, Inl (Both _ flat), Both each _ =>
          rewrite flat then ((headOrUniform options each), restUniform)
        | Choice options, Inr (Both _ (Witness chosen (Both isOption broken))), Both each _ =>
          rewrite broken then ((optionUniform chosen options isOption each), restUniform)

theorem optionSteps ∀ (chosen: Doc) (options: List Doc)
    (isOption: IsOption chosen options):
    chosen.steps ≤ stepsOf options + 1 :=
  match options, isOption with
    | [], picked => rewrite picked then arithmetic
    | [last], picked => rewrite picked then arithmetic
    | [option, next, ..others], Inl picked => rewrite picked then arithmetic
    | [option, next, ..others], Inr later =>
      let bound := optionSteps chosen [next, ..others] later
      arithmetic

--| Every step of a reading weighs the work list down, as the printer's
--| own steps do (`stepLighter`): a reading ends within the same budget.
theorem readingLighter ∀ (printer: Printer) (cmd: Cmd) (rest: List Cmd) (result: (Printer, List Cmd))
    (steps: StepsTo printer cmd rest result):
    stackCost result.snd < cmd.cost + stackCost rest :=
  match cmd, steps with
    | FillSep indent item, Inl (Both _ flat) => rewrite flat then arithmetic
    | FillSep indent item, Inr broken => rewrite broken then arithmetic
    | Print indent mode doc, steps =>
      match doc, steps with
        | Empty, steps => rewrite steps then stepLighter printer 0 (Print indent mode Empty) rest
        | BreakParent, steps => rewrite steps then stepLighter printer 0 (Print indent mode BreakParent) rest
        | Chunk text width, steps =>
          rewrite steps then stepLighter printer 0 (Print indent mode (Chunk text width)) rest
        | Line, steps => rewrite steps then stepLighter printer 0 (Print indent mode Line) rest
        | SoftLine, steps => rewrite steps then stepLighter printer 0 (Print indent mode SoftLine) rest
        | HardLine, steps => rewrite steps then stepLighter printer 0 (Print indent mode HardLine) rest
        | LineStart, steps => rewrite steps then stepLighter printer 0 (Print indent mode LineStart) rest
        | CommentEnd, steps => rewrite steps then stepLighter printer 0 (Print indent mode CommentEnd) rest
        | LineStartHere, steps => rewrite steps then stepLighter printer 0 (Print indent mode LineStartHere) rest
        | Blank, steps => rewrite steps then stepLighter printer 0 (Print indent mode Blank) rest
        | Nest more inner, steps => rewrite steps then stepLighter printer 0 (Print indent mode (Nest more inner)) rest
        | OneLineBelow inner, steps =>
          rewrite steps then stepLighter printer 0 (Print indent mode (OneLineBelow inner)) rest
        | Flatten inner, steps => rewrite steps then stepLighter printer 0 (Print indent mode (Flatten inner)) rest
        | LineSuffix comment, steps =>
          rewrite steps then stepLighter printer 0 (Print indent mode (LineSuffix comment)) rest
        | Concat docs, steps => rewrite steps then stepLighter printer 0 (Print indent mode (Concat docs)) rest
        | Group inner hard, Inl (Both _ flat) => rewrite flat then arithmetic
        | Group inner hard, Inr (Both _ broken) => rewrite broken then arithmetic
        | Fill [], steps => rewrite steps then arithmetic
        | Fill [first, ..others], Inl (Both _ flat) =>
          let bound := joinLinesSteps [first, ..others]
          rewrite repeatedly [flat, stackCostAppend, costPrints] then arithmetic
        | Fill [first, ..others], Inr (Both _ (Witness firstMode broken)) =>
          rewrite repeatedly [broken, stackCostAppend, costFillSeps] then arithmetic
        | Choice options, Inl (Both _ flat) =>
          let bound := headOrSteps options
          rewrite flat then arithmetic
        | Choice options, Inr (Both _ (Witness chosen (Both isOption broken))) =>
          let bound := optionSteps chosen options isOption
          rewrite broken then arithmetic

--| A reading that has the steps to finish its work list writes the work
--| list's words after the printer's, in order, whichever way its groups,
--| fills and choices go.
theorem readingWords ∀ (printer: Printer) (fuel: Nat) (stack: List Cmd) (final: Printer)
    (reads: Reads printer fuel stack final)
    (uniform: StackUniform stack)
    (enough: stackCost stack ≤ fuel):
    final.words = printer.words ++ stackWords stack :=
  match fuel, stack, reads, uniform with
    | Zero, [], reads, _ => rewrite repeatedly [reads, List.appendNil]
    | Succ more, [], reads, _ => rewrite repeatedly [reads, List.appendNil]
    | Zero, [cmd, ..rest], _, _ =>
      let positive := costPositive cmd
      Void.impossible (arithmetic)
    | Succ more, [cmd, ..rest], Witness next (Witness later (Both steps laterReads)), Both first others =>
      let moved := stepWords printer cmd rest (next, later) steps first
      let lighter := readingLighter printer cmd rest (next, later) steps
      let kept := stepUniform printer cmd rest (next, later) steps first others
      Eq.trans (readingWords next more later final laterReads kept (arithmetic)) moved
