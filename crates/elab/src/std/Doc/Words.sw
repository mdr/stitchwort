--| Every reading writes the document's words. A word is a piece of
--| output that isn't layout (spaces, indentation, a line break): the text
--| of a chunk, a closer or a trailing comment. Which way groups, fills
--| and choices go changes only the layout between the words, as long as
--| every option of a choice has the same words (`Uniform`). A trailing
--| comment is written before any chunk that follows it in the document,
--| and after the closers (`Closing`) that join its line: which closers
--| those are is the reading's choice, so the order of the words is the
--| document's only up to that.
--|
--| Three statements, each through every reading. A step moves words from
--| the work list to the printer in order, a closer alone going before
--| the comments that wait (`stepWords`). What holds of every word of the
--| document holds of every word written (`readingEvery`). And the order
--| is the document's to any filter that keeps no closer, or keeps no
--| trailing comment (`readingWords`): the words other than closers are in
--| the document's order, comments among them, and so are the words other
--| than trailing comments, closers among them; in a document with no
--| closer, all the words are. Exactly where each closer lands is `Lays`'
--| to say (`Places.sw`).

import Doc (..)
import Bool (not)
import Doc.Proofs (..)

--| Whether a piece of output is only layout: spaces (a gap, indentation,
--| or nothing at all) or a line break.
def Doc.Proofs.isLayout (piece: Text): Bool := piece.all (char => char == ' ') || piece == "\n"

--| The pieces that aren't layout.
def Doc.Proofs.wordsOf (pieces: List Text): List Text := pieces.filter (piece => not (isLayout piece))

--| What the printer has written so far, as words.
def Doc.Printer.written (printer: Printer): List Text := wordsOf printer.out.reverse

--| The words printed so far, the trailing comments still waiting last.
def Doc.Printer.words (printer: Printer): List Text := printer.written ++ wordsOf printer.suffixes

--| Empty text is layout.
theorem Doc.Proofs.emptyIsLayout ∀ (text: Text) (empty: text.isEmpty = True): isLayout text = True :=
  match text, empty with | MkText [], _ => byComputing

--| Spaces are layout.
theorem Doc.Proofs.spacesIsLayout ∀ (text: Text)
    (spaces: text.all (char => char == ' ') = True):
    isLayout text = True :=
  rewrite repeatedly [spaces]

--| Indentation is spaces.
theorem Doc.Proofs.indentSpaces ∀ (indent: Nat): (" ".repeat indent).all (char => char == ' ') = True :=
  match indent with
    | Zero => byComputing
    | Succ less => indentSpaces less

--| A piece written last adds its words at the end.
theorem Doc.Proofs.wordsSnoc ∀ (piece: Text) (out: List Text):
    wordsOf [piece, ..out].reverse = wordsOf out.reverse ++ wordsOf [piece] :=
  rewrite repeatedly [List.reverseCons, List.filterAppend]

--| A layout piece holds no words.
theorem Doc.Proofs.layoutNoWord ∀ (piece: Text) (layout: isLayout piece = True): wordsOf [piece] = [] :=
  rewrite repeatedly [layout]

--| A piece of layout adds no word.
theorem Doc.Proofs.layoutSnoc ∀ (piece: Text) (out: List Text)
    (layout: isLayout piece = True):
    wordsOf [piece, ..out].reverse = wordsOf out.reverse :=
  rewrite repeatedly [wordsSnoc, layoutNoWord piece layout, List.appendNil]

--| Dropping the spaces at the end of the output leaves its words.
theorem Doc.Proofs.trimWords ∀ (out: List Text): wordsOf (trimSpaces out).reverse = wordsOf out.reverse :=
  match out with
    | [] => byComputing
    | [last, ..earlier] =>
      match spaces: last.all (char => char == ' ') with
        | True => rewrite layoutSnoc last earlier (spacesIsLayout last spaces) then trimWords earlier
        | False => byComputing

--| Paying the indentation owed leaves the words written and the waiting
--| comments as they were.
theorem Doc.Proofs.payIndentWritten ∀ (printer: Printer):
    printer.payIndent.written = printer.written ∧ printer.payIndent.suffixes = printer.suffixes :=
  match owed: printer.owed with
    | None | Some Zero => (byComputing, byComputing)
    | Some (Succ less) =>
      ((layoutSnoc (" ".repeat (Succ less)) printer.out (spacesIsLayout _ (indentSpaces (Succ less)))), byComputing)

--| Text put on the line is the next word written, if it is one.
theorem Doc.Proofs.putWritten ∀ (printer: Printer) (text: Text) (width: Nat):
    (printer.put text width).written = printer.written ++ wordsOf [text]
      ∧ (printer.put text width).suffixes = printer.suffixes :=
  match payIndentWritten printer with
    | (written, suffixes) => ((rewrite <- written then wordsSnoc text printer.payIndent.out), suffixes)

--| Writing a waiting comment adds its words to those written.
theorem Doc.Proofs.flushOneWritten ∀ (printer: Printer) (comment: Text):
    (printer.flushOne comment).written = printer.written ++ wordsOf [comment]
      ∧ (printer.flushOne comment).suffixes = printer.suffixes :=
  match start: printer.atLineStart with
    | True =>
      match payIndentWritten printer with
        | (written, suffixes) => ((rewrite <- written then wordsSnoc comment printer.payIndent.out), suffixes)
    | False =>
      (rewrite repeatedly [wordsSnoc comment [" ", ..printer.out], layoutSnoc " " printer.out byComputing], byComputing)

--| Comments flushed one after another are the next words written.
theorem Doc.Proofs.flushEachWritten ∀ (comments: List Text) (printer: Printer):
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
theorem Doc.Proofs.flushWritten ∀ (printer: Printer):
    printer.flushSuffixes.written = printer.words ∧ printer.flushSuffixes.suffixes = [] :=
  flushEachWritten printer.suffixes { printer | suffixes = [] }

--| A line break writes the waiting comments and no other word.
theorem Doc.Proofs.newlineWritten ∀ (printer: Printer) (indent: Nat):
    (printer.newline indent).written = printer.words ∧ (printer.newline indent).suffixes = [] :=
  match flushWritten { printer | out = trimSpaces printer.out } with
    | (written, suffixes) => (
      rewrite repeatedly [
        layoutSnoc "\n" ({ printer | out = trimSpaces printer.out }).flushSuffixes.out byComputing,
        <- trimWords printer.out
      ],
      suffixes
    )

--| A line break leaves the words the printer has, written and waiting, as they
--| were.
theorem Doc.Proofs.newlineWords ∀ (printer: Printer) (indent: Nat): (printer.newline indent).words = printer.words :=
  match newlineWritten printer indent with
    | (written, suffixes) => rewrite repeatedly [written, suffixes, List.appendNil]

--| A list that is empty is `[]`.
theorem Doc.Proofs.emptyNil ∀ (items: List a) (empty: items.isEmpty = True): items = [] := match items, empty with
  | [], _ => byComputing

--| With no comment waiting, text put on the line is the next word.
theorem Doc.Proofs.putClearWords ∀ (printer: Printer) (text: Text) (width: Nat)
    (clear: printer.suffixes = []):
    (printer.put text width).words = printer.written ++ wordsOf [text] :=
  match putWritten printer text width with
    | (written, suffixes) => rewrite repeatedly [written, suffixes, clear, List.appendNil]

--| Text written is the next word, after any comment that was waiting.
theorem Doc.Proofs.writeWords ∀ (printer: Printer) (indent: Nat) (text: Text) (width: Nat):
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
                  rewrite repeatedly [<- brokenWritten, putClearWords _ text width brokenSuffixes]

--| A comment break leaves the printer's words as they were.
theorem Doc.Proofs.commentBreakWords ∀ (printer: Printer) (indent: Nat):
    (printer.commentBreak indent).words = printer.words :=
  match start: printer.atLineStart with
    | True => byComputing
    | False => newlineWords printer (printer.continuation indent)

--| Setting the carry leaves the printer's words as they were.
theorem Doc.Proofs.floorWords ∀ (printer: Printer) (carry: Carry): { printer | carry = carry }.words = printer.words :=
  byComputing

--| A line start leaves the printer's words as they were.
theorem Doc.Proofs.lineStartWords ∀ (printer: Printer) (indent: Nat):
    (printer.lineStart indent).words = printer.words :=
  match start: printer.atLineStart with
    | True => byComputing
    | False =>
      let broken := printer.newline (printer.continuation indent)
      Eq.trans
        (floorWords broken (printer.carry.startFloor (printer.continuation indent)))
        (newlineWords printer (printer.continuation indent))

--| A closer's line leaves the printer's words as they were.
theorem Doc.Proofs.closerLineWords ∀ (printer: Printer) (key indent: Nat):
    (printer.closerLine key indent).words = printer.words :=
  let closed := { printer | carry = printer.carry.close key }
  let broken :=
    Eq.trans (newlineWords closed (printer.carry.closerAt key indent)) (floorWords printer (printer.carry.close key))
  match start: printer.atLineStart with
    | True =>
      match waiting: printer.suffixes.isEmpty with
        | True => byComputing
        | False => broken
    | False => broken

--| A `Displaced` element leaves the printer's words as they were.
theorem Doc.Proofs.displaceWords ∀ (printer: Printer) (indent: Nat): (printer.displace indent).words = printer.words :=
  match empty: printer.suffixes.isEmpty with
    | True => byComputing
    | False => commentBreakWords printer indent

--| A blank line leaves the printer's words as they were.
theorem Doc.Proofs.blankWords ∀ (printer: Printer): printer.blank.words = printer.words :=
  match blank: printer.atLineStart && printer.started && printer.newlinesAtEnd < 2 with
    | True => rewrite repeatedly [layoutSnoc "\n" printer.out byComputing]
    | False => byComputing

--| Writing the spaces held writes no word and leaves the comments
--| waiting.
theorem Doc.Proofs.writeHeldWritten ∀ (printer: Printer):
    printer.writeHeld.written = printer.written ∧ printer.writeHeld.suffixes = printer.suffixes :=
  match start: printer.atLineStart with
    | True => (byComputing, byComputing)
    | False =>
      match held: printer.heldSpaces with
        | Zero => (byComputing, byComputing)
        | Succ less =>
          ((layoutSnoc (" ".repeat (Succ less)) printer.out (spacesIsLayout _ (indentSpaces (Succ less)))), byComputing)

--| A closer is the next word written, before the comments that wait.
theorem Doc.Proofs.closeWords ∀ (printer: Printer) (text: Text):
    (printer.close text).words = printer.written ++ (wordsOf [text] ++ wordsOf printer.suffixes) :=
  match empty: text.isEmpty with
    | True => rewrite repeatedly [layoutNoWord text (emptyIsLayout text empty)]
    | False =>
      match waiting: printer.suffixes.isEmpty with
        | True =>
          match putWritten printer text text.length with
            | (written, suffixes) => rewrite repeatedly [written, suffixes, List.appendAssoc]
        | False =>
          match putWritten printer.writeHeld text text.length, writeHeldWritten printer with
            | (written, suffixes), (heldWritten, heldSuffixes) =>
              rewrite repeatedly [written, suffixes, heldWritten, heldSuffixes, List.appendAssoc]

--| Where no comment waits, a closer is written as a chunk is.
theorem Doc.Proofs.closeClear ∀ (printer: Printer) (indent: Nat) (text: Text)
    (clear: printer.suffixes.isEmpty = True):
    printer.close text = printer.write indent text text.length :=
  match empty: text.isEmpty with
    | True => byComputing
    | False =>
      match waiting: printer.suffixes.isEmpty, clear with
        | True, _ => byComputing
        | False, never =>
          match never with
            | ()

--| A closer that isn't empty, while a comment waits, is written as text
--| as wide as it is long, after the spaces held.
theorem Doc.Proofs.closePut ∀ (printer: Printer) (text: Text)
    (filled: text.isEmpty = False)
    (waiting: printer.suffixes.isEmpty = False):
    printer.close text = printer.writeHeld.put text text.length :=
  rewrite filled, waiting

--| A word has at least one character.
theorem Doc.Proofs.wordFilled ∀ (text: Text) (word: isLayout text = False): text.isEmpty = False :=
  match empty: text.isEmpty with
    | False => byComputing
    | True => (Bool.falseNotTrue (Eq.trans word.flipped (emptyIsLayout text empty))).impossible

-- The document's words, and the readings.

--| The words of a document, in order: its chunks' texts and its trailing
--| comments, apart from layout. A choice's are its first option's and an
--| `IfBroken`'s its broken branch's; in a `Uniform` document every option,
--| and both branches, have the same.
def Doc.words: Doc → List Text
  | Chunk text _ | Closing text | LineSuffix text => wordsOf [text]
  | Nest _ inner |
      Align inner |
      AlignInset inner |
      Displaced inner |
      Group inner _ |
      NarrowGroup _ inner _ |
      IdGroup _ inner _ |
      IfBroken _ inner _ |
      Flatten inner |
      OneLineBelow inner => inner.words
  | Concat docs | Fill docs => wordsAll docs
  | Choice options => wordsFirst options
  | _ => []

--| The words of the docs, in order.
def Doc.Proofs.wordsAll: List Doc → List Text
  | [] => []
  | [doc, ..docs] => doc.words ++ wordsAll docs

--| The words of the first doc, or none.
def Doc.Proofs.wordsFirst: List Doc → List Text
  | [] => []
  | [doc, .._] => doc.words

--| Every option of every choice in the document has the same words.
def Doc.Proofs.Uniform: Doc → Prop
  | Nest _ inner |
      Align inner |
      AlignInset inner |
      Displaced inner |
      Group inner _ |
      NarrowGroup _ inner _ |
      IdGroup _ inner _ => Uniform inner
  | IfBroken _ broken flat => Uniform broken ∧ Uniform flat ∧ flat.words = broken.words
  | Flatten inner | OneLineBelow inner => Uniform inner
  | Concat docs | Fill docs => AllUniform docs
  | Choice options => AllUniform options ∧ SameWords (wordsFirst options) options
  | _ => True

--| Every doc is `Uniform`.
def Doc.Proofs.AllUniform: List Doc → Prop
  | [] => True
  | [doc, ..docs] => Uniform doc ∧ AllUniform docs

--| Each of the documents has these words.
def Doc.Proofs.SameWords (words: List Text): List Doc → Prop
  | [] => True
  | [doc, ..docs] => doc.words = words ∧ SameWords words docs

--| The words a command writes.
def Doc.Cmd.words: Cmd → List Text
  | Print _ _ doc | FillSep _ doc => doc.words

--| The words the work list has still to write.
def Doc.Proofs.stackWords: List Cmd → List Text
  | [] => []
  | [cmd, ..rest] => cmd.words ++ stackWords rest

--| A command's doc is `Uniform`.
def Doc.Proofs.CmdUniform: Cmd → Prop
  | Print _ _ doc | FillSep _ doc => Uniform doc

--| Every command on the work list is `CmdUniform`.
def Doc.Proofs.StackUniform: List Cmd → Prop
  | [] => True
  | [cmd, ..rest] => CmdUniform cmd ∧ StackUniform rest

--| The words of two work lists put together are those of each, in order.
theorem Doc.Proofs.stackWordsAppend ∀ (front back: List Cmd):
    stackWords (front ++ back) = stackWords front ++ stackWords back :=
  match front with
    | [] => byComputing
    | [cmd, ..rest] => rewrite repeatedly [stackWordsAppend rest back, List.appendAssoc]

--| Two uniform work lists put together are uniform.
theorem Doc.Proofs.stackUniformAppend ∀ (front back: List Cmd)
    (frontUniform: StackUniform front)
    (backUniform: StackUniform back):
    StackUniform (front ++ back) :=
  match front, frontUniform with
    | [], _ => backUniform
    | [cmd, ..rest], _ => byFacts [stackUniformAppend]

--| Printing each of the docs writes the docs' words.
theorem Doc.Proofs.printsWords ∀ (indent: Nat) (mode: Mode) (docs: List Doc):
    stackWords (docs.map (Print indent mode)) = wordsAll docs :=
  match docs with
    | [] => byComputing
    | [doc, ..rest] => rewrite repeatedly [printsWords indent mode rest]

--| Printing uniform docs is a uniform work list.
theorem Doc.Proofs.printsUniform ∀ (indent: Nat) (mode: Mode) (docs: List Doc)
    (uniform: AllUniform docs):
    StackUniform (docs.map (Print indent mode)) :=
  match docs, uniform with
    | [], _ => byComputing
    | [doc, ..rest], _ => byFacts [printsUniform]

--| The separators before a fill's items write the items' words.
theorem Doc.Proofs.fillSepsWords ∀ (indent: Nat) (items: List Doc):
    stackWords (items.map (FillSep indent)) = wordsAll items :=
  match items with
    | [] => byComputing
    | [item, ..rest] => rewrite repeatedly [fillSepsWords indent rest]

--| The separators before uniform items are a uniform work list.
theorem Doc.Proofs.fillSepsUniform ∀ (indent: Nat) (items: List Doc)
    (uniform: AllUniform items):
    StackUniform (items.map (FillSep indent)) :=
  match items, uniform with
    | [], _ => byComputing
    | [item, ..rest], _ => byFacts [fillSepsUniform]

--| The lines a flat fill puts between its items are no words.
theorem Doc.Proofs.joinLinesWords ∀ (items: List Doc): wordsAll (Doc.joinLines items) = wordsAll items :=
  match items with
    | [item, next, ..rest] => rewrite repeatedly [joinLinesWords [next, ..rest]]
    | _ => cases

--| Putting a `Line` between uniform items leaves them uniform.
theorem Doc.Proofs.joinLinesUniform ∀ (items: List Doc) (uniform: AllUniform items): AllUniform (Doc.joinLines items) :=
  match items, uniform with
    | [], _ => byComputing
    | [only], given => given
    | [item, next, ..rest], _ => byFacts [joinLinesUniform]

--| What a choice may print has the words all its options have.
theorem Doc.Proofs.optionWords ∀ (chosen: Doc) (words: List Text) (option: Doc) (others: List Doc)
    (isOption: IsOption chosen [option, ..others])
    (same: SameWords words [option, ..others]):
    chosen.words = words :=
  match others, isOption, same with
    | [], picked, (first, _) => rewrite picked then first
    | [next, ..rest], Inl picked, (first, _) => rewrite picked then first
    | [next, ..rest], Inr later, (_, laterSame) => optionWords chosen words next rest later laterSame

--| A doc that is one of the options of a uniform choice is uniform.
theorem Doc.Proofs.optionUniform ∀ (chosen: Doc) (options: List Doc)
    (isOption: IsOption chosen options)
    (uniform: AllUniform options):
    Uniform chosen :=
  match options, isOption, uniform with
    | [], picked, _ => rewrite repeatedly [picked]
    | [last], picked, Both first _ => rewrite picked then first
    | [option, next, ..rest], Inl picked, Both first _ => rewrite picked then first
    | [option, next, ..rest], Inr later, Both _ others => optionUniform chosen [next, ..rest] later others

--| Writing layout leaves the printer's words as they were.
theorem Doc.Proofs.writeLayoutWords ∀ (printer: Printer) (indent: Nat) (text: Text) (width: Nat)
    (layout: isLayout text = True):
    (printer.write indent text width).words = printer.words :=
  rewrite repeatedly [writeWords, layoutNoWord text layout, List.appendNil]

--| A trailing comment set to wait is the next word.
theorem Doc.Proofs.suffixWords ∀ (printer: Printer) (comment: Text):
    ({ printer | suffixes = printer.suffixes ++ [comment] }).words = printer.words ++ wordsOf [comment] :=
  rewrite repeatedly [List.filterAppend, List.appendAssoc]

--| A step that goes one way or the other leaves the words to come as `target`
--| if each way does.
theorem Doc.Proofs.eitherWords ∀ (condition: Bool) (yes no: (Printer, List Cmd)) (target: List Text)
    (whenYes: yes.fst.words ++ stackWords yes.snd = target)
    (whenNo: no.fst.words ++ stackWords no.snd = target):
    (if condition then yes else no).fst.words ++ stackWords (if condition then yes else no).snd = target :=
  match condition with
    | True => whenYes
    | False => whenNo

--| A step that goes one way or the other leaves a uniform work list if each way
--| does.
theorem Doc.Proofs.eitherUniform ∀ (condition: Bool) (yes no: (Printer, List Cmd))
    (whenYes: StackUniform yes.snd)
    (whenNo: StackUniform no.snd):
    StackUniform (if condition then yes else no).snd :=
  match condition with
    | True => whenYes
    | False => whenNo

--| The first option of a choice has the first option's words.
theorem Doc.Proofs.headOrWords ∀ (options: List Doc): (options.headOr Doc.Nothing).words = wordsFirst options := cases

--| The first option of uniform options is uniform.
theorem Doc.Proofs.headOrUniform ∀ (options: List Doc)
    (uniform: AllUniform options):
    Uniform (options.headOr Doc.Nothing) :=
  match options, uniform with
    | [], _ => byComputing
    | [option, ..others], _ => byFacts

--| An option a choice takes has the words of the first option, if all options
--| have the same words.
theorem Doc.Proofs.chosenWords ∀ (chosen: Doc) (options: List Doc)
    (isOption: IsOption chosen options)
    (same: SameWords (wordsFirst options) options):
    chosen.words = wordsFirst options :=
  match options, isOption, same with
    | [], picked, _ => rewrite repeatedly [picked]
    | [option, ..others], picked, given => optionWords chosen option.words option others picked given

--| The branch an `IfBroken` takes is one of its two.
theorem Doc.Proofs.pickEither ∀ (modes: List (Nat, Mode)) (id: Nat) (broken flat: Doc):
    pickBranch modes id broken flat = broken ∨ pickBranch modes id broken flat = flat :=
  match picked: brokenIn modes id with
    | True => Inl byComputing
    | False => Inr byComputing

--| The branch an `IfBroken` takes has the broken branch's words, if both
--| branches have the same.
theorem Doc.Proofs.pickWords ∀ (modes: List (Nat, Mode)) (id: Nat) (broken flat: Doc)
    (same: flat.words = broken.words):
    (pickBranch modes id broken flat).words = broken.words :=
  match pickEither modes id broken flat with
    | Inl isBroken => rewrite isBroken
    | Inr isFlat => rewrite isFlat then same

--| The branch an `IfBroken` takes is uniform if both are.
theorem Doc.Proofs.pickUniform ∀ (modes: List (Nat, Mode)) (id: Nat) (broken flat: Doc)
    (brokenUniform: Uniform broken)
    (flatUniform: Uniform flat):
    Uniform (pickBranch modes id broken flat) :=
  match pickEither modes id broken flat with
    | Inl isBroken => rewrite isBroken then brokenUniform
    | Inr isFlat => rewrite isFlat then flatUniform

--| Recording a group's mode writes nothing.
theorem Doc.Proofs.recordWords ∀ (printer: Printer) (id: Nat) (mode: Mode):
    (printer.record id mode).words = printer.words :=
  byComputing

--| The rules `stepWords` rewrites a step's words with: what each printer
--| operation writes, and how a stack's words split.
rules Doc.Proofs.wordSteps :=
  [
    writeLayoutWords,
    writeWords,
    newlineWords,
    lineStartWords,
    blankWords,
    suffixWords,
    stackWordsAppend,
    printsWords,
    fillSepsWords,
    joinLinesWords,
    headOrWords
  ]

--| The printer's words, then `cmd`'s, then `later`, as the step that
--| prints `cmd` leaves them: in that order, except that a closer goes
--| before the comments that wait.
def Doc.Cmd.wordsFrom (cmd: Cmd) (printer: Printer) (later: List Text): List Text := match cmd with
  | Print _ _ doc => doc.wordsFrom printer later
  | FillSep _ item => printer.words ++ (item.words ++ later)

--| The printer's words, then the doc's, then `later`, as the step that prints
--| the doc leaves them; a closer goes before the waiting comments.
def Doc.wordsFrom (doc: Doc) (printer: Printer) (later: List Text): List Text := match doc with
  | Closing text => printer.written ++ (wordsOf [text] ++ (wordsOf printer.suffixes ++ later))
  | _ => printer.words ++ (doc.words ++ later)

--| A step of a reading moves words from the work list to the printer, in
--| order, a closer alone going before the comments that wait: the words
--| printed and those still to print, together, stay the same but for
--| that.
theorem Doc.Proofs.stepWords ∀ (printer: Printer) (cmd: Cmd) (rest: List Cmd) (result: (Printer, List Cmd))
    (steps: StepsTo printer cmd rest result)
    (uniform: CmdUniform cmd):
    result.fst.words ++ stackWords result.snd = cmd.wordsFrom printer (stackWords rest) :=
  match cmd, steps, uniform with
    | FillSep indent item, Inl (Both _ flat), _ =>
      rewrite repeatedly [flat, writeLayoutWords] then rewrite repeatedly [List.appendAssoc]
    | FillSep indent item, Inr broken, _ => rewrite repeatedly [broken, wordSteps]
    | Print indent mode doc, steps, uniform =>
      match doc, steps, uniform with
        | Doc.Nothing | BreakParent, steps, _ => rewrite repeatedly [steps]
        | Chunk text width, steps, _ => rewrite repeatedly [steps, wordSteps, List.appendAssoc]
        | Closing text, steps, _ => rewrite repeatedly [steps, closeWords, List.appendAssoc]
        | Line, steps, _ => rewrite steps then cases then rewrite repeatedly [newlineWords, writeLayoutWords]
        | SoftLine, steps, _ => rewrite steps then cases then rewrite repeatedly [newlineWords]
        | HardLine, steps, _ => rewrite repeatedly [steps, wordSteps]
        | Mark key, steps, _ => rewrite repeatedly [steps]
        | CloserLine key, steps, _ => rewrite repeatedly [steps, closerLineWords]
        | LineStart, steps, _ => rewrite repeatedly [steps, wordSteps]
        | LineStartHere, steps, _ =>
          rewrite steps then
            eitherWords _
              ({ printer | owed = Some indent, lineIndent = indent }, rest)
              (printer.newline indent, rest) _
              byComputing
              (rewrite repeatedly [newlineWords])
        | Blank, steps, _ => rewrite repeatedly [steps, wordSteps]
        | Nest _ _ | Align _ | AlignInset _, steps, _ => rewrite repeatedly [steps]
        | Displaced inner, steps, _ => rewrite repeatedly [steps, displaceWords]
        | OneLineBelow _ | Flatten _, steps, _ => rewrite repeatedly [steps]
        | LineSuffix comment, steps, _ => rewrite repeatedly [steps, wordSteps, List.appendAssoc]
        | Group _ _ | NarrowGroup _ _ _, Inl (Both _ flat) | Inr (Both _ flat), _ => rewrite repeatedly [flat]
        | IdGroup _ _ _, Inl (Both _ flat) | Inr (Both _ flat), _ => rewrite repeatedly [flat, recordWords]
        | IfBroken id broken flat, steps, Both _ (Both _ same) =>
          rewrite repeatedly [steps, pickWords printer.modes id broken flat same]
        | Concat docs, steps, _ => rewrite repeatedly [steps, wordSteps]
        | Fill [], steps, _ => rewrite repeatedly [steps]
        | Fill [first, ..others], Inl (Both _ flat), _ => rewrite repeatedly [flat, wordSteps]
        | Fill [first, ..others], Inr (Both _ (Witness firstMode broken)), _ =>
          rewrite repeatedly [broken, wordSteps, List.appendAssoc]
        | Choice options, Inl (Both _ flat), _ => rewrite repeatedly [flat, wordSteps]
        | Choice options, Inr (Both _ (Witness chosen (Both isOption broken))), Both _ same =>
          rewrite repeatedly [broken, chosenWords chosen options isOption same]

--| A step of a reading leaves the work list uniform.
theorem Doc.Proofs.stepUniform ∀ (printer: Printer) (cmd: Cmd) (rest: List Cmd) (result: (Printer, List Cmd))
    (steps: StepsTo printer cmd rest result)
    (uniform: CmdUniform cmd)
    (restUniform: StackUniform rest):
    StackUniform result.snd :=
  match cmd, steps, uniform with
    | FillSep _ _, Inl (Both _ flat) | Inr flat, uniform => rewrite flat then byFacts
    | Print indent mode doc, steps, uniform =>
      match doc, steps, uniform with
        | Doc.Nothing | BreakParent | Chunk _ _ | Closing _, steps, _ => rewrite repeatedly [steps]
        | Line, steps, _ => rewrite steps then byFacts [eitherUniform]
        | SoftLine, steps, _ => rewrite steps then byFacts [eitherUniform]
        | HardLine | Mark _ | CloserLine _ | LineStart, steps, _ => rewrite repeatedly [steps]
        | LineStartHere, steps, _ => rewrite steps then byFacts [eitherUniform]
        | Blank, steps, _ => rewrite repeatedly [steps]
        | Nest _ _ | Align _ | AlignInset _ | Displaced _, steps, uniform => rewrite steps then byFacts
        | OneLineBelow inner, steps, uniform => rewrite steps then byFacts
        | Flatten inner, steps, uniform => rewrite steps then byFacts
        | LineSuffix comment, steps, _ => rewrite repeatedly [steps]
        | Group _ _ | NarrowGroup _ _ _ | IdGroup _ _ _, Inl (Both _ flat) | Inr (Both _ flat), uniform =>
          rewrite flat then byFacts
        | IfBroken id broken flat, steps, Both brokenUniform (Both flatUniform _) =>
          rewrite steps then byFacts [pickUniform]
        | Concat docs, steps, uniform => rewrite steps then byFacts [stackUniformAppend, printsUniform]
        | Fill [], steps, _ => rewrite repeatedly [steps]
        | Fill [first, ..others], Inl (Both _ flat), uniform =>
          rewrite flat then byFacts [stackUniformAppend, printsUniform, joinLinesUniform]
        | Fill [first, ..others], Inr (Both _ (Witness firstMode broken)), Both firstUniform othersUniform =>
          rewrite broken then byFacts [stackUniformAppend, fillSepsUniform]
        | Choice options, Inl (Both _ flat), Both each _ => rewrite flat then byFacts [headOrUniform]
        | Choice options, Inr (Both _ (Witness chosen (Both isOption broken))), Both each _ =>
          rewrite broken then byFacts [optionUniform]

--| An option a choice takes has at most the steps of all the options and one.
theorem Doc.Proofs.optionSteps ∀ (chosen: Doc) (options: List Doc)
    (isOption: IsOption chosen options):
    chosen.steps ≤ stepsOf options + 1 :=
  match options, isOption with
    | [] | [_], picked => rewrite picked then arithmetic
    | [option, next, ..others], Inl picked => rewrite picked then arithmetic
    | [option, next, ..others], Inr later =>
      let bound := optionSteps chosen [next, ..others] later
      arithmetic

--| Every step of a reading weighs the work list down, as the printer's
--| own steps do (`stepLighter`): a reading ends within the same budget.
theorem Doc.Proofs.readingLighter ∀ (printer: Printer) (cmd: Cmd) (rest: List Cmd) (result: (Printer, List Cmd))
    (steps: StepsTo printer cmd rest result):
    stackCost result.snd < cmd.cost + stackCost rest :=
  match cmd, steps with
    | FillSep _ _, Inl (Both _ flat) | Inr flat => rewrite flat then arithmetic
    | Print indent mode doc, steps =>
      match doc, steps with
        | Doc.Nothing, steps => rewrite steps then stepLighter printer 0 (Print indent mode Doc.Nothing) rest
        | BreakParent, steps => rewrite steps then stepLighter printer 0 (Print indent mode BreakParent) rest
        | Chunk text width, steps =>
          rewrite steps then stepLighter printer 0 (Print indent mode (Chunk text width)) rest
        | Closing text, steps => rewrite steps then stepLighter printer 0 (Print indent mode (Closing text)) rest
        | Line, steps => rewrite steps then stepLighter printer 0 (Print indent mode Line) rest
        | SoftLine, steps => rewrite steps then stepLighter printer 0 (Print indent mode SoftLine) rest
        | HardLine, steps => rewrite steps then stepLighter printer 0 (Print indent mode HardLine) rest
        | Mark key, steps => rewrite steps then stepLighter printer 0 (Print indent mode (Mark key)) rest
        | CloserLine key, steps => rewrite steps then stepLighter printer 0 (Print indent mode (CloserLine key)) rest
        | LineStart, steps => rewrite steps then stepLighter printer 0 (Print indent mode LineStart) rest
        | LineStartHere, steps => rewrite steps then stepLighter printer 0 (Print indent mode LineStartHere) rest
        | Blank, steps => rewrite steps then stepLighter printer 0 (Print indent mode Blank) rest
        | Nest more inner, steps => rewrite steps then stepLighter printer 0 (Print indent mode (Nest more inner)) rest
        | Align inner, steps => rewrite steps then stepLighter printer 0 (Print indent mode (Align inner)) rest
        | AlignInset inner, steps =>
          rewrite steps then stepLighter printer 0 (Print indent mode (AlignInset inner)) rest
        | Displaced inner, steps => rewrite steps then stepLighter printer 0 (Print indent mode (Displaced inner)) rest
        | OneLineBelow inner, steps =>
          rewrite steps then stepLighter printer 0 (Print indent mode (OneLineBelow inner)) rest
        | Flatten inner, steps => rewrite steps then stepLighter printer 0 (Print indent mode (Flatten inner)) rest
        | LineSuffix comment, steps =>
          rewrite steps then stepLighter printer 0 (Print indent mode (LineSuffix comment)) rest
        | Concat docs, steps => rewrite steps then stepLighter printer 0 (Print indent mode (Concat docs)) rest
        | Group _ _ | NarrowGroup _ _ _ | IdGroup _ _ _, Inl (Both _ flat) | Inr (Both _ flat) =>
          rewrite flat then arithmetic
        | IfBroken id broken flat, steps =>
          rewrite steps then stepLighter printer 0 (Print indent mode (IfBroken id broken flat)) rest
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

--| `holds` of each of the words.
def Doc.Proofs.Every (holds: Text → Prop): List Text → Prop
  | [] => True
  | [word, ..rest] => holds word ∧ Every holds rest

--| Two lists of words that each satisfy a property do so together.
theorem Doc.Proofs.everyAppend ∀ (holds: Text → Prop) (front back: List Text)
    (first: Every holds front)
    (second: Every holds back):
    Every holds (front ++ back) :=
  match front, first with
    | [], _ => second
    | [word, ..rest], (head, others) => (head, (everyAppend holds rest back others second))

--| Both halves of a list of words that satisfies a property satisfy it.
theorem Doc.Proofs.everySplit ∀ (holds: Text → Prop) (front back: List Text)
    (all: Every holds (front ++ back)):
    Every holds front ∧ Every holds back :=
  match front, all with
    | [], all => (byComputing, all)
    | [word, ..rest], (head, others) =>
      match everySplit holds rest back others with
        | (first, second) => ((head, first), second)

--| What holds of the printer's words, a command's and the words after
--| holds of them as the command's step leaves them.
theorem Doc.Proofs.everyFrom ∀ (holds: Text → Prop) (cmd: Cmd) (printer: Printer) (later: List Text)
    (all: Every holds (printer.words ++ (cmd.words ++ later))):
    Every holds (cmd.wordsFrom printer later) :=
  match cmd, all with
    | FillSep indent item, all => all
    | Print indent mode doc, all =>
      match doc, all with
        | Closing text, all =>
          match everySplit holds printer.words (wordsOf [text] ++ later) all with
            | (printed, after) =>
              match everySplit holds printer.written (wordsOf printer.suffixes) printed, everySplit holds
                (wordsOf [text])
                later
                after with
                | (written, waiting), (closer, rest) =>
                  everyAppend holds printer.written
                    (wordsOf [text] ++ (wordsOf printer.suffixes ++ later))
                    written
                    (everyAppend holds
                      (wordsOf [text])
                      (wordsOf printer.suffixes ++ later)
                      closer
                      (everyAppend holds (wordsOf printer.suffixes) later waiting rest))
        | _, all => all

--| What holds of every word the printer has and of every word on the
--| work list holds of every word a reading ends with, whichever way its
--| groups, fills and choices go and whichever closers join a comment's
--| line: a reading writes no word of its own.
theorem Doc.Proofs.readingEvery ∀ (holds: Text → Prop) (printer: Printer) (fuel: Nat) (stack: List Cmd) (final: Printer)
    (reads: Doc.Proofs.Reads printer fuel stack final)
    (uniform: StackUniform stack)
    (all: Every holds (printer.words ++ stackWords stack)):
    Every holds final.words :=
  match fuel, stack, reads, uniform, all with
    | Zero, stack, reads, _, all => rewrite reads then (everySplit holds printer.words (stackWords stack) all).left
    | Succ more, [], reads, _, all => rewrite reads then (everySplit holds printer.words [] all).left
    | Succ more, [cmd, ..rest], Witness next (Witness later (Both steps laterReads)), Both first others, all =>
      let moved := stepWords printer cmd rest (next, later) steps first
      let kept := stepUniform printer cmd rest (next, later) steps first others
      readingEvery holds next more later final laterReads kept
        (rewrite moved then everyFrom holds cmd printer (stackWords rest) all)

-- Which words are closers and which are trailing comments.

--| Every closer in the document satisfies `closer`, and every trailing
--| comment `suffix`: what a statement about the order of the words needs
--| to know of the two kinds that may change places.
def Doc.Proofs.Marked (closer suffix: Text → Prop): Doc → Prop
  | Closing text => closer text
  | LineSuffix comment => suffix comment
  | Nest _ inner |
      Align inner |
      AlignInset inner |
      Displaced inner |
      Group inner _ |
      NarrowGroup _ inner _ |
      IdGroup _ inner _ => Marked closer suffix inner
  | IfBroken _ broken flat => Marked closer suffix broken ∧ Marked closer suffix flat
  | Flatten inner | OneLineBelow inner => Marked closer suffix inner
  | Concat docs | Fill docs | Choice docs => AllMarked closer suffix docs
  | _ => True

--| Every doc is `Marked` with the closer and suffix tests.
def Doc.Proofs.AllMarked (closer suffix: Text → Prop): List Doc → Prop
  | [] => True
  | [doc, ..docs] => Marked closer suffix doc ∧ AllMarked closer suffix docs

--| A command's doc is `Marked` with the closer and suffix tests.
def Doc.Proofs.CmdMarked (closer suffix: Text → Prop): Cmd → Prop
  | Print _ _ doc | FillSep _ doc => Marked closer suffix doc

--| Every command on the work list is `CmdMarked`.
def Doc.Proofs.StackMarked (closer suffix: Text → Prop): List Cmd → Prop
  | [] => True
  | [cmd, ..rest] => CmdMarked closer suffix cmd ∧ StackMarked closer suffix rest

--| Two marked work lists put together are marked.
theorem Doc.Proofs.stackMarkedAppend ∀ (closer suffix: Text → Prop) (front back: List Cmd)
    (frontUniform: StackMarked closer suffix front)
    (backUniform: StackMarked closer suffix back):
    StackMarked closer suffix (front ++ back) :=
  match front, frontUniform with
    | [], _ => backUniform
    | [cmd, ..rest], _ => byFacts [stackMarkedAppend]

--| Printing marked docs is a marked work list.
theorem Doc.Proofs.printsMarked ∀ (closer suffix: Text → Prop) (indent: Nat) (mode: Mode) (docs: List Doc)
    (uniform: AllMarked closer suffix docs):
    StackMarked closer suffix (docs.map (Print indent mode)) :=
  match docs, uniform with
    | [], _ => byComputing
    | [doc, ..rest], _ => byFacts [printsMarked]

--| The separators before marked items are a marked work list.
theorem Doc.Proofs.fillSepsMarked ∀ (closer suffix: Text → Prop) (indent: Nat) (items: List Doc)
    (uniform: AllMarked closer suffix items):
    StackMarked closer suffix (items.map (FillSep indent)) :=
  match items, uniform with
    | [], _ => byComputing
    | [item, ..rest], _ => byFacts [fillSepsMarked]

--| Putting a `Line` between marked items leaves them marked.
theorem Doc.Proofs.joinLinesMarked ∀ (closer suffix: Text → Prop) (items: List Doc)
    (uniform: AllMarked closer suffix items):
    AllMarked closer suffix (Doc.joinLines items) :=
  match items, uniform with
    | [], _ => byComputing
    | [only], given => given
    | [item, next, ..rest], _ => byFacts [joinLinesMarked]

--| A doc that is one of the options of marked options is marked.
theorem Doc.Proofs.optionMarked ∀ (closer suffix: Text → Prop) (chosen: Doc) (options: List Doc)
    (isOption: IsOption chosen options)
    (uniform: AllMarked closer suffix options):
    Marked closer suffix chosen :=
  match options, isOption, uniform with
    | [], picked, _ => rewrite repeatedly [picked]
    | [last], picked, Both first _ => rewrite picked then first
    | [option, next, ..rest], Inl picked, Both first _ => rewrite picked then first
    | [option, next, ..rest], Inr later, Both _ others => optionMarked closer suffix chosen [next, ..rest] later others

--| A step that goes one way or the other leaves a marked work list if each way
--| does.
theorem Doc.Proofs.eitherMarked ∀ (closer suffix: Text → Prop) (condition: Bool) (yes no: (Printer, List Cmd))
    (whenYes: StackMarked closer suffix yes.snd)
    (whenNo: StackMarked closer suffix no.snd):
    StackMarked closer suffix (if condition then yes else no).snd :=
  match condition with
    | True => whenYes
    | False => whenNo

--| The first option of marked options is marked.
theorem Doc.Proofs.headOrMarked ∀ (closer suffix: Text → Prop) (options: List Doc)
    (uniform: AllMarked closer suffix options):
    Marked closer suffix (options.headOr Doc.Nothing) :=
  match options, uniform with
    | [], _ => byComputing
    | [option, ..others], _ => byFacts

--| The branch an `IfBroken` takes is marked if both are.
theorem Doc.Proofs.pickMarked ∀ (closer suffix: Text → Prop) (modes: List (Nat, Mode)) (id: Nat) (broken flat: Doc)
    (brokenMarked: Marked closer suffix broken)
    (flatMarked: Marked closer suffix flat):
    Marked closer suffix (pickBranch modes id broken flat) :=
  match pickEither modes id broken flat with
    | Inl isBroken => rewrite isBroken then brokenMarked
    | Inr isFlat => rewrite isFlat then flatMarked

--| A step of a reading leaves the work list marked.
theorem Doc.Proofs.stepMarked ∀ (closer suffix: Text → Prop) (printer: Printer) (cmd: Cmd)
    (rest: List Cmd) (result: (Printer, List Cmd))
    (steps: StepsTo printer cmd rest result)
    (uniform: CmdMarked closer suffix cmd)
    (restUniform: StackMarked closer suffix rest):
    StackMarked closer suffix result.snd :=
  match cmd, steps, uniform with
    | FillSep _ _, Inl (Both _ flat) | Inr flat, uniform => rewrite flat then byFacts
    | Print indent mode doc, steps, uniform =>
      match doc, steps, uniform with
        | Doc.Nothing | BreakParent | Chunk _ _ | Closing _, steps, _ => rewrite repeatedly [steps]
        | Line, steps, _ => rewrite steps then byFacts [eitherMarked]
        | SoftLine, steps, _ => rewrite steps then byFacts [eitherMarked]
        | HardLine | Mark _ | CloserLine _ | LineStart, steps, _ => rewrite repeatedly [steps]
        | LineStartHere, steps, _ => rewrite steps then byFacts [eitherMarked]
        | Blank, steps, _ => rewrite repeatedly [steps]
        | Nest _ _ | Align _ | AlignInset _ | Displaced _, steps, uniform => rewrite steps then byFacts
        | OneLineBelow inner, steps, uniform => rewrite steps then byFacts
        | Flatten inner, steps, uniform => rewrite steps then byFacts
        | LineSuffix comment, steps, _ => rewrite repeatedly [steps]
        | Group _ _ | NarrowGroup _ _ _ | IdGroup _ _ _, Inl (Both _ flat) | Inr (Both _ flat), uniform =>
          rewrite flat then byFacts
        | IfBroken id broken flat, steps, Both brokenMarked flatMarked => rewrite steps then byFacts [pickMarked]
        | Concat docs, steps, uniform => rewrite steps then byFacts [stackMarkedAppend, printsMarked]
        | Fill [], steps, _ => rewrite repeatedly [steps]
        | Fill [first, ..others], Inl (Both _ flat), uniform =>
          rewrite flat then byFacts [stackMarkedAppend, printsMarked, joinLinesMarked]
        | Fill [first, ..others], Inr (Both _ (Witness firstMode broken)), Both firstUniform othersUniform =>
          rewrite broken then byFacts [stackMarkedAppend, fillSepsMarked]
        | Choice options, Inl (Both _ flat), each => rewrite flat then byFacts [headOrMarked]
        | Choice options, Inr (Both _ (Witness chosen (Both isOption broken))), each =>
          rewrite broken then byFacts [optionMarked]

-- The comments that wait are trailing comments of the document.

--| A line break leaves no comment waiting, so every waiting comment satisfies
--| any test.
theorem Doc.Proofs.newlineQuiet ∀ (suffix: Text → Prop) (printer: Printer) (indent: Nat):
    Every suffix (printer.newline indent).suffixes :=
  rewrite (newlineWritten printer indent).right

--| Writing leaves every waiting comment satisfying the test, if they did.
theorem Doc.Proofs.writeQuiet ∀ (suffix: Text → Prop) (printer: Printer) (indent: Nat) (text: Text) (width: Nat)
    (waits: Every suffix printer.suffixes):
    Every suffix (printer.write indent text width).suffixes :=
  match empty: text.isEmpty with
    | True => waits
    | False =>
      match waiting: printer.suffixes.isEmpty with
        | True => rewrite (putWritten printer text width).right then waits
        | False =>
          match spaces: text.all (char => char == ' ') with
            | True => waits
            | False =>
              rewrite (putWritten (printer.newline (printer.continuation indent)) text width).right,
                  (newlineWritten printer (printer.continuation indent)).right

--| Writing a closer leaves every waiting comment satisfying the test, if they
--| did.
theorem Doc.Proofs.closeQuiet ∀ (suffix: Text → Prop) (printer: Printer) (text: Text)
    (waits: Every suffix printer.suffixes):
    Every suffix (printer.close text).suffixes :=
  match empty: text.isEmpty with
    | True => waits
    | False =>
      match waiting: printer.suffixes.isEmpty with
        | True => rewrite (putWritten printer text text.length).right then waits
        | False =>
          rewrite (putWritten printer.writeHeld text text.length).right, (writeHeldWritten printer).right then waits

--| A comment break leaves every waiting comment satisfying the test, if
--| they did.
theorem Doc.Proofs.commentBreakQuiet ∀ (suffix: Text → Prop) (printer: Printer) (indent: Nat)
    (waits: Every suffix printer.suffixes):
    Every suffix (printer.commentBreak indent).suffixes :=
  match start: printer.atLineStart with
    | True => waits
    | False => newlineQuiet suffix printer (printer.continuation indent)

--| A line start leaves every waiting comment satisfying the test, if they did.
theorem Doc.Proofs.lineStartQuiet ∀ (suffix: Text → Prop) (printer: Printer) (indent: Nat)
    (waits: Every suffix printer.suffixes):
    Every suffix (printer.lineStart indent).suffixes :=
  match start: printer.atLineStart with
    | True => waits
    | False => newlineQuiet suffix printer (printer.continuation indent)

--| A closer's line leaves every waiting comment satisfying the test, if
--| they did.
theorem Doc.Proofs.closerLineQuiet ∀ (suffix: Text → Prop) (printer: Printer) (key indent: Nat)
    (waits: Every suffix printer.suffixes):
    Every suffix (printer.closerLine key indent).suffixes :=
  let broken := newlineQuiet suffix { printer | carry = printer.carry.close key } (printer.carry.closerAt key indent)
  match start: printer.atLineStart with
    | True =>
      match waiting: printer.suffixes.isEmpty with
        | True => waits
        | False => broken
    | False => broken

--| A `Displaced` element leaves every waiting comment satisfying the test,
--| if they did.
theorem Doc.Proofs.displaceQuiet ∀ (suffix: Text → Prop) (printer: Printer) (indent: Nat)
    (waits: Every suffix printer.suffixes):
    Every suffix (printer.displace indent).suffixes :=
  match empty: printer.suffixes.isEmpty with
    | True => waits
    | False => commentBreakQuiet suffix printer indent waits

--| A blank line leaves every waiting comment satisfying the test, if they did.
theorem Doc.Proofs.blankQuiet ∀ (suffix: Text → Prop) (printer: Printer)
    (waits: Every suffix printer.suffixes):
    Every suffix printer.blank.suffixes :=
  match blank: printer.atLineStart && printer.started && printer.newlinesAtEnd < 2 with | True | False => waits

--| A step that goes one way or the other leaves every waiting comment
--| satisfying the test if each way does.
theorem Doc.Proofs.eitherQuiet ∀ (suffix: Text → Prop) (condition: Bool) (yes no: (Printer, List Cmd))
    (whenYes: Every suffix yes.fst.suffixes)
    (whenNo: Every suffix no.fst.suffixes):
    Every suffix (if condition then yes else no).fst.suffixes :=
  match condition with
    | True => whenYes
    | False => whenNo

--| Through a step of a reading, the comments that wait are trailing
--| comments of the document: what `suffix` holds of.
theorem Doc.Proofs.stepQuiet ∀ (closer suffix: Text → Prop) (printer: Printer) (cmd: Cmd)
    (rest: List Cmd) (result: (Printer, List Cmd))
    (steps: StepsTo printer cmd rest result)
    (marked: CmdMarked closer suffix cmd)
    (waits: Every suffix printer.suffixes):
    Every suffix result.fst.suffixes :=
  match cmd, steps, marked with
    | FillSep indent item, Inl (Both _ flat), _ => rewrite flat then writeQuiet suffix printer indent " " 1 waits
    | FillSep indent item, Inr broken, _ => rewrite broken then newlineQuiet suffix printer indent
    | Print indent mode doc, steps, marked =>
      match doc, steps, marked with
        | Doc.Nothing | BreakParent, steps, _ => rewrite steps then waits
        | Chunk text width, steps, _ => rewrite steps then writeQuiet suffix printer indent text width waits
        | Closing text, steps, _ => rewrite steps then closeQuiet suffix printer text waits
        | Line, steps, _ =>
          rewrite steps then
            eitherQuiet suffix _
              (printer.write indent " " 1, rest)
              (printer.newline indent, rest)
              (writeQuiet suffix printer indent " " 1 waits)
              (newlineQuiet suffix printer indent)
        | SoftLine, steps, _ =>
          rewrite steps then
            eitherQuiet suffix _
              (printer, rest)
              (printer.newline indent, rest)
              waits
              (newlineQuiet suffix printer indent)
        | HardLine, steps, _ => rewrite steps then newlineQuiet suffix printer indent
        | Mark key, steps, _ => rewrite steps then waits
        | CloserLine key, steps, _ => rewrite steps then closerLineQuiet suffix printer key indent waits
        | LineStart, steps, _ => rewrite steps then lineStartQuiet suffix printer indent waits
        | LineStartHere, steps, _ =>
          rewrite steps then
            eitherQuiet suffix _
              ({ printer | owed = Some indent, lineIndent = indent }, rest)
              (printer.newline indent, rest)
              waits
              (newlineQuiet suffix printer indent)
        | Blank, steps, _ => rewrite steps then blankQuiet suffix printer waits
        | Nest _ _ | Align _ | AlignInset _, steps, _ => rewrite steps then waits
        | Displaced inner, steps, _ => rewrite steps then displaceQuiet suffix printer indent waits
        | OneLineBelow _ | Flatten _, steps, _ => rewrite steps then waits
        | LineSuffix comment, steps, isSuffix =>
          rewrite steps then everyAppend suffix printer.suffixes [comment] waits ((isSuffix, byComputing))
        | Group _ _ | NarrowGroup _ _ _ | IdGroup _ _ _, Inl (Both _ flat) | Inr (Both _ flat), _ =>
          rewrite flat then waits
        | IfBroken _ _ _ | Concat _ | Fill [], steps, _ => rewrite steps then waits
        | Fill [_, .._], Inl (Both _ flat) | Inr (Both _ (Witness _ flat)), _ => rewrite flat then waits
        | Choice _, Inl (Both _ flat) | Inr (Both _ (Witness _ (Both _ flat))), _ => rewrite flat then waits

-- The order of the words.

--| Words that all satisfy a property all satisfy a weaker one.
theorem Doc.Proofs.everyWeaker ∀ (strong weak: Text → Prop)
    (words: List Text) (implies: ∀ (word: Text) => strong word → weak word)
    (all: Every strong words):
    Every weak words :=
  match words, all with
    | [], _ => byComputing
    | [word, ..rest], (head, others) => ((implies word head), (everyWeaker strong weak rest implies others))

--| A text the filter drops leaves no word.
theorem Doc.Proofs.siftedWord ∀ (keep: Text → Bool) (text: Text)
    (dropped: keep text = False):
    (wordsOf [text]).filter keep = [] :=
  match layout: isLayout text with
    | True => byComputing
    | False => rewrite repeatedly [dropped]

--| Filtering words that all fail a test leaves none.
theorem Doc.Proofs.siftedAll ∀ (keep: Text → Bool) (texts: List Text)
    (dropped: Every (text => keep text = False) texts):
    (wordsOf texts).filter keep = [] :=
  match texts, dropped with
    | [], _ => byComputing
    | [text, ..rest], (head, others) =>
      match layout: isLayout text with
        | True => siftedAll keep rest others
        | False => rewrite repeatedly [head, siftedAll keep rest others]

--| A filter that keeps no closer, or no trailing comment, can't tell
--| whether a closer went before the comments that wait.
theorem Doc.Proofs.siftedFrom ∀ (keep: Text → Bool) (closer suffix: Text → Prop) (cmd: Cmd)
    (printer: Printer) (later: List Text)
    (marked: CmdMarked closer suffix cmd)
    (waits: Every suffix printer.suffixes)
    (apart: (∀ (text: Text) => closer text → keep text = False)
      ∨ (∀ (comment: Text) => suffix comment → keep comment = False)):
    (cmd.wordsFrom printer later).filter keep = (printer.words ++ (cmd.words ++ later)).filter keep :=
  match cmd, marked with
    | FillSep indent item, _ => byComputing
    | Print indent mode doc, marked =>
      match doc, marked with
        | Closing text, isCloser =>
          match apart with
            | Inl closers =>
              let dropped := siftedWord keep text (closers text isCloser)
              let same: (printer.written ++ (wordsOf [text] ++ (wordsOf printer.suffixes ++ later))).filter keep
                = ((printer.written ++ wordsOf printer.suffixes) ++ (wordsOf [text] ++ later)).filter keep :=
                rewrite repeatedly [List.filterAppend, dropped, List.appendAssoc]
              same
            | Inr comments =>
              let quiet :=
                siftedAll keep printer.suffixes
                  (everyWeaker suffix (comment => keep comment = False) printer.suffixes comments waits)
              let same: (printer.written ++ (wordsOf [text] ++ (wordsOf printer.suffixes ++ later))).filter keep
                = ((printer.written ++ wordsOf printer.suffixes) ++ (wordsOf [text] ++ later)).filter keep :=
                rewrite repeatedly [List.filterAppend, quiet, List.appendAssoc]
              same
        | _, _ => byComputing

--| A reading that has the steps to finish its work list writes the work
--| list's words after the printer's, whichever way its groups, fills and
--| choices go, in an order no filter can tell from the document's if it
--| keeps no closer, or keeps no trailing comment. So the words other
--| than closers are in the document's order, comments among them; and so
--| are the words other than trailing comments, closers among them. In a
--| document with no closer, take `closer` false of every text: every
--| filter qualifies, and the words are the document's in order.
--|
--| By induction on the reading: a step moves words in order (`stepWords`)
--| but for a closer going before the comments that wait, which such a
--| filter doesn't see (`siftedFrom`); the comments that wait are the
--| document's trailing comments throughout (`stepQuiet`).
theorem Doc.Proofs.readingWords ∀ (keep: Text → Bool) (closer suffix: Text → Prop) (printer: Printer) (fuel: Nat)
    (stack: List Cmd) (final: Printer)
    (reads: Doc.Proofs.Reads printer fuel stack final)
    (uniform: StackUniform stack)
    (marked: StackMarked closer suffix stack)
    (waits: Every suffix printer.suffixes)
    (apart: (∀ (text: Text) => closer text → keep text = False)
      ∨ (∀ (comment: Text) => suffix comment → keep comment = False))
    (enough: stackCost stack ≤ fuel):
    final.words.filter keep = (printer.words ++ stackWords stack).filter keep :=
  match fuel, stack, reads, uniform, marked with
    | Zero | Succ _, [], reads, _, _ => rewrite repeatedly [reads, List.appendNil]
    | Zero, [cmd, ..rest], _, _, _ =>
      let positive := costPositive cmd
      Void.impossible (arithmetic)
    | Succ more, [cmd, ..rest], Witness next (Witness later (Both steps laterReads)), Both first others, Both
          firstMarked othersMarked =>
      let moved := stepWords printer cmd rest (next, later) steps first
      let lighter := readingLighter printer cmd rest (next, later) steps
      let kept := stepUniform printer cmd rest (next, later) steps first others
      let keptMarked := stepMarked closer suffix printer cmd rest (next, later) steps firstMarked othersMarked
      let quiet := stepQuiet closer suffix printer cmd rest (next, later) steps firstMarked waits
      calc final.words.filter keep
        _ = (next.words ++ stackWords later).filter keep :=
          readingWords keep closer suffix next more later final laterReads kept keptMarked quiet apart (arithmetic)
        _ = (cmd.wordsFrom printer (stackWords rest)).filter keep :=
          Eq.cong ((words: List Text) => words.filter keep) moved
        _ = (printer.words ++ (cmd.words ++ stackWords rest)).filter keep :=
          siftedFrom keep closer suffix cmd printer (stackWords rest) firstMarked waits apart
