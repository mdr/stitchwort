--| What the printed text starts with. The printer only ever writes in
--| front of what it has written (the output is kept the last piece first),
--| and the only pieces it takes back are spaces at the end of a line
--| (`trimSpaces`). So once a word that isn't spaces is the first piece of
--| the output, it stays first through every reading (`readingAtop`); and
--| a document that starts with a chunk (`Leads`) writes that chunk first,
--| before any space or line break, whatever the width
--| (`printedLeads`).
--|
--| At the other end, a document that ends with a word (`Finishes`: its last
--| chunk or closer, then only marks and trailing comments) prints that
--| word last, followed only by its trailing comments, each after a space
--| (`printedFinishes`): every step leaves the end of the work list in place,
--| and nothing silent writes.

import Doc (..)
import Bool (not)
import Doc.Proofs (..)

-- The first piece stays first.

--| `out` (the pieces the last first) has `word` as its first piece: what
--| was written after it comes in front of it.
def Doc.Proofs.Atop (word: Text) (out: List Text): Prop := ∃ (front: List Text) => out = front ++ [word]

--| A piece written next keeps the first piece first.
theorem Doc.Proofs.atopCons ∀ (word piece: Text) (out: List Text) (atop: Atop word out): Atop word [piece, ..out] :=
  match atop with | (front, same) => ([piece, ..front], (rewrite same))

--| Dropping the spaces at the end of output written over `word` keeps
--| `word`, if it isn't spaces.
theorem Doc.Proofs.trimFrontAtop ∀ (word: Text) (front: List Text)
    (solid: word.all (char => char == ' ') = False):
    Atop word (trimSpaces (front ++ [word])) :=
  match front with
    | [] => ([], (trimKeep word [] solid))
    | [last, ..earlier] =>
      match spaces: last.all (char => char == ' ') with
        | True =>
          match trimFrontAtop word earlier solid with
            | (kept, same) => (kept, (Eq.trans (trimDrop last (earlier ++ [word]) spaces) same))
        | False => ([last, ..earlier], (trimKeep last (earlier ++ [word]) spaces))

--| Dropping the spaces at the end of the output keeps a first piece that
--| isn't spaces.
theorem Doc.Proofs.trimAtop ∀ (word: Text) (out: List Text)
    (solid: word.all (char => char == ' ') = False)
    (atop: Atop word out):
    Atop word (trimSpaces out) :=
  match atop with | (front, same) => rewrite same then trimFrontAtop word front solid

--| Paying the indentation owed keeps the first piece first.
theorem Doc.Proofs.payAtop ∀ (word: Text) (printer: Printer)
    (atop: Atop word printer.out):
    Atop word printer.payIndent.out :=
  match owed: printer.owed with
    | None => atop
    | Some Zero => atop
    | Some (Succ less) => atopCons word (" ".repeat (Succ less)) printer.out atop

--| Text put on the line keeps the first piece first.
theorem Doc.Proofs.putAtop ∀ (word: Text) (printer: Printer) (text: Text) (width: Nat)
    (atop: Atop word printer.out):
    Atop word (printer.put text width).out :=
  atopCons word text printer.payIndent.out (payAtop word printer atop)

--| Writing the spaces held keeps the first piece first.
theorem Doc.Proofs.writeHeldAtop ∀ (word: Text) (printer: Printer)
    (atop: Atop word printer.out):
    Atop word printer.writeHeld.out :=
  match start: printer.atLineStart with
    | True => atop
    | False =>
      match held: printer.heldSpaces with
        | Zero => atop
        | Succ less => atopCons word (" ".repeat (Succ less)) printer.out atop

--| Writing a waiting comment keeps the first piece first.
theorem Doc.Proofs.flushOneAtop ∀ (word: Text) (printer: Printer) (comment: Text)
    (atop: Atop word printer.out):
    Atop word (printer.flushOne comment).out :=
  match start: printer.atLineStart with
    | True => atopCons word comment printer.payIndent.out (payAtop word printer atop)
    | False => atopCons word comment [" ", ..printer.out] (atopCons word " " printer.out atop)

--| Writing comments one after another keeps the first piece first.
theorem Doc.Proofs.flushEachAtop ∀ (word: Text) (comments: List Text) (printer: Printer)
    (atop: Atop word printer.out):
    Atop word (comments.foldLeft printer Printer.flushOne).out :=
  match comments with
    | [] => atop
    | [comment, ..later] => flushEachAtop word later (printer.flushOne comment) (flushOneAtop word printer comment atop)

--| Writing the waiting comments keeps the first piece first.
theorem Doc.Proofs.flushAtop ∀ (word: Text) (printer: Printer)
    (atop: Atop word printer.out):
    Atop word printer.flushSuffixes.out :=
  flushEachAtop word printer.suffixes { printer | suffixes = [] } atop

--| A line break keeps a first piece that isn't spaces first.
theorem Doc.Proofs.newlineAtop ∀ (word: Text) (printer: Printer) (indent: Nat)
    (solid: word.all (char => char == ' ') = False)
    (atop: Atop word printer.out):
    Atop word (printer.newline indent).out :=
  atopCons word "\n"
    ({ printer | out = trimSpaces printer.out }).flushSuffixes.out
    (flushAtop word { printer | out = trimSpaces printer.out } (trimAtop word printer.out solid atop))

--| Writing a chunk keeps a first piece that isn't spaces first.
theorem Doc.Proofs.writeAtop ∀ (word: Text) (printer: Printer) (indent: Nat) (text: Text) (width: Nat)
    (solid: word.all (char => char == ' ') = False)
    (atop: Atop word printer.out):
    Atop word (printer.write indent text width).out :=
  match empty: text.isEmpty with
    | True => atop
    | False =>
      match waiting: printer.suffixes.isEmpty with
        | True => putAtop word printer text width atop
        | False =>
          match spaces: text.all (char => char == ' ') with
            | True => atop
            | False =>
              putAtop word
                (printer.newline (printer.continuation indent))
                text
                width
                (newlineAtop word printer (printer.continuation indent) solid atop)

--| Writing a closer keeps the first piece first.
theorem Doc.Proofs.closeAtop ∀ (word: Text) (printer: Printer) (text: Text)
    (atop: Atop word printer.out):
    Atop word (printer.close text).out :=
  match empty: text.isEmpty with
    | True => atop
    | False =>
      match waiting: printer.suffixes.isEmpty with
        | True => putAtop word printer text text.length atop
        | False => putAtop word printer.writeHeld text text.length (writeHeldAtop word printer atop)

--| A comment break keeps a first piece that isn't spaces first.
theorem Doc.Proofs.commentBreakAtop ∀ (word: Text) (printer: Printer) (indent: Nat)
    (solid: word.all (char => char == ' ') = False)
    (atop: Atop word printer.out):
    Atop word (printer.commentBreak indent).out :=
  match start: printer.atLineStart with
    | True => atop
    | False => newlineAtop word printer (printer.continuation indent) solid atop

--| A line start keeps a first piece that isn't spaces first.
theorem Doc.Proofs.lineStartAtop ∀ (word: Text) (printer: Printer) (indent: Nat)
    (solid: word.all (char => char == ' ') = False)
    (atop: Atop word printer.out):
    Atop word (printer.lineStart indent).out :=
  match start: printer.atLineStart with
    | True => atop
    | False => newlineAtop word printer (printer.continuation indent) solid atop

--| A closer's line keeps a first piece that isn't spaces first.
theorem Doc.Proofs.closerLineAtop ∀ (word: Text) (printer: Printer) (key indent: Nat)
    (solid: word.all (char => char == ' ') = False)
    (atop: Atop word printer.out):
    Atop word (printer.closerLine key indent).out :=
  let broken :=
    newlineAtop word { printer | carry = printer.carry.close key } (printer.carry.closerAt key indent) solid atop
  match start: printer.atLineStart with
    | True =>
      match waiting: printer.suffixes.isEmpty with
        | True => atop
        | False => broken
    | False => broken

--| A `Displaced` element keeps a first piece that isn't spaces first.
theorem Doc.Proofs.displaceAtop ∀ (word: Text) (printer: Printer) (indent: Nat)
    (solid: word.all (char => char == ' ') = False)
    (atop: Atop word printer.out):
    Atop word (printer.displace indent).out :=
  match empty: printer.suffixes.isEmpty with
    | True => atop
    | False => commentBreakAtop word printer indent solid atop

--| A blank line keeps the first piece first.
theorem Doc.Proofs.blankAtop ∀ (word: Text) (printer: Printer)
    (atop: Atop word printer.out):
    Atop word printer.blank.out :=
  match blank: printer.atLineStart && printer.started && printer.newlinesAtEnd < 2 with
    | True => atopCons word "\n" printer.out atop
    | False => atop

--| A step that goes one way or the other keeps the first piece first if
--| each way does.
theorem Doc.Proofs.eitherAtop ∀ (word: Text) (condition: Bool) (yes no: (Printer, List Cmd))
    (whenYes: Atop word yes.fst.out)
    (whenNo: Atop word no.fst.out):
    Atop word (if condition then yes else no).fst.out :=
  match condition with
    | True => whenYes
    | False => whenNo

--| Every step of a reading keeps a first piece that isn't spaces first.
theorem Doc.Proofs.stepAtop ∀ (word: Text) (printer: Printer) (cmd: Cmd) (rest: List Cmd) (result: (Printer, List Cmd))
    (steps: StepsTo printer cmd rest result)
    (solid: word.all (char => char == ' ') = False)
    (atop: Atop word printer.out):
    Atop word result.fst.out :=
  match cmd, steps with
    | FillSep indent item, Inl (Both _ flat) => rewrite flat then writeAtop word printer indent " " 1 solid atop
    | FillSep indent item, Inr broken => rewrite broken then newlineAtop word printer indent solid atop
    | Print indent mode doc, steps =>
      match doc, steps with
        | Doc.Nothing, steps => rewrite steps then atop
        | BreakParent, steps => rewrite steps then atop
        | Chunk text width, steps => rewrite steps then writeAtop word printer indent text width solid atop
        | Closing text, steps => rewrite steps then closeAtop word printer text atop
        | Line, steps =>
          rewrite steps then
            eitherAtop word mode.isFlat
              (printer.write indent " " 1, rest)
              (printer.newline indent, rest)
              (writeAtop word printer indent " " 1 solid atop)
              (newlineAtop word printer indent solid atop)
        | SoftLine, steps =>
          rewrite steps then
            eitherAtop word mode.isFlat
              (printer, rest)
              (printer.newline indent, rest)
              atop
              (newlineAtop word printer indent solid atop)
        | HardLine, steps => rewrite steps then newlineAtop word printer indent solid atop
        | Mark key, steps => rewrite steps then atop
        | CloserLine key, steps => rewrite steps then closerLineAtop word printer key indent solid atop
        | LineStart, steps => rewrite steps then lineStartAtop word printer indent solid atop
        | LineStartHere, steps =>
          rewrite steps then
            eitherAtop word printer.atLineStart
              ({ printer | owed = Some indent, lineIndent = indent }, rest)
              (printer.newline indent, rest)
              atop
              (newlineAtop word printer indent solid atop)
        | Blank, steps => rewrite steps then blankAtop word printer atop
        | Nest more inner, steps => rewrite steps then atop
        | Align inner, steps => rewrite steps then atop
        | AlignInset inner, steps => rewrite steps then atop
        | Displaced inner, steps => rewrite steps then displaceAtop word printer indent solid atop
        | OneLineBelow inner, steps => rewrite steps then atop
        | Flatten inner, steps => rewrite steps then atop
        | LineSuffix comment, steps => rewrite steps then atop
        | Group inner hard, Inl (Both _ flat) => rewrite flat then atop
        | NarrowGroup max inner hard, Inl (Both _ flat) => rewrite flat then atop
        | Group inner hard, Inr (Both _ broken) => rewrite broken then atop
        | NarrowGroup max inner hard, Inr (Both _ broken) => rewrite broken then atop
        | IdGroup id inner hard, Inl (Both _ flat) => rewrite flat then atop
        | IdGroup id inner hard, Inr (Both _ broken) => rewrite broken then atop
        | IfBroken id broken flat, steps => rewrite steps then atop
        | Concat docs, steps => rewrite steps then atop
        | Fill [], steps => rewrite steps then atop
        | Fill [first, ..others], Inl (Both _ flat) => rewrite flat then atop
        | Fill [first, ..others], Inr (Both _ (Witness firstMode broken)) => rewrite broken then atop
        | Choice options, Inl (Both _ flat) => rewrite flat then atop
        | Choice options, Inr (Both _ (Witness chosen (Both isOption broken))) => rewrite broken then atop

--| Through every reading, a first piece that isn't spaces stays first.
theorem Doc.Proofs.readingAtop ∀ (word: Text) (printer: Printer) (fuel: Nat) (stack: List Cmd) (final: Printer)
    (reads: Doc.Proofs.Reads printer fuel stack final)
    (solid: word.all (char => char == ' ') = False)
    (atop: Atop word printer.out):
    Atop word final.out :=
  match fuel, stack, reads with
    | Zero, [], reads => rewrite reads then atop
    | Succ more, [], reads => rewrite reads then atop
    | Zero, [cmd, ..rest], reads => rewrite reads then atop
    | Succ more, [cmd, ..rest], Witness next (Witness later (Both steps laterReads)) =>
      readingAtop word next more later final laterReads solid
        (stepAtop word printer cmd rest (next, later) steps solid atop)

-- A document's first chunk.

--| `doc` starts with the chunk `word`: before anything else, whatever the
--| layout, the printer writes it.
def Doc.Proofs.Leads (word: Text): Doc → Prop
  | Chunk text _ => text = word
  | Concat [first, .._] => Leads word first
  | Nest _ inner => Leads word inner
  | Group inner _ => Leads word inner
  | NarrowGroup _ inner _ => Leads word inner
  | IdGroup _ inner _ => Leads word inner
  | Flatten inner => Leads word inner
  | _ => False

--| From an empty output with no comment waiting and no indentation owed,
--| a word written is the first piece.
theorem Doc.Proofs.writeFirst ∀ (printer: Printer) (indent: Nat) (word: Text) (width: Nat)
    (blank: printer.out = [])
    (clear: printer.suffixes = [])
    (owed: printer.owed = None)
    (filled: word.isEmpty = False):
    Atop word (printer.write indent word width).out :=
  ([], (rewrite filled, clear, owed, blank))

--| The printer of a step that is one pair is that pair's.
theorem Doc.Proofs.pairPrinter ∀ (next printer: Printer) (later stack: List Cmd)
    (same: (next, later) = (printer, stack)):
    next = printer :=
  Eq.cong ((pair: (Printer, List Cmd)) => pair.fst) same

--| The work list of a step that is one pair is that pair's.
theorem Doc.Proofs.pairStack ∀ (next printer: Printer) (later stack: List Cmd)
    (same: (next, later) = (printer, stack)):
    later = stack :=
  Eq.cong ((pair: (Printer, List Cmd)) => pair.snd) same

--| A reading of a work list whose first document leads with `word`,
--| from an empty output with no comment waiting and no indentation owed,
--| leaves `word` the first piece, if it has the steps to write it.
--|
--| Proof idea: each step on the way to the chunk takes a group, a nest or
--| the first of a `Concat` apart without writing (an id group records its
--| mode only), one step less of the budget each; the chunk is written
--| first (`writeFirst`), and every step after keeps it first
--| (`readingAtop`).
theorem Doc.Proofs.leadsReads ∀ (word: Text) (doc: Doc) (printer: Printer) (indent fuel: Nat) (mode: Mode)
    (rest: List Cmd) (final: Printer)
    (leads: Leads word doc)
    (reads: Doc.Proofs.Reads printer fuel [Print indent mode doc, ..rest] final)
    (blank: printer.out = [])
    (clear: printer.suffixes = [])
    (owed: printer.owed = None)
    (filled: word.isEmpty = False)
    (solid: word.all (char => char == ' ') = False)
    (enough: doc.steps ≤ fuel):
    Atop word final.out :=
  match fuel, reads with
    | Zero, _ =>
      let positive := stepsPositive doc
      Void.impossible (arithmetic)
    | Succ more, Witness next (Witness later (Both steps laterReads)) =>
      match doc, leads, steps with
        | Chunk text width, same, steps =>
          let wrote := pairPrinter next (printer.write indent text width) later rest steps
          readingAtop word next more later final laterReads solid
            (rewrite wrote, same then writeFirst printer indent word width blank clear owed filled)
        | Concat [inner, ..others], leads, steps =>
          let moved :=
            pairPrinter next printer later ([Print indent mode inner, ..others.map (Print indent mode)] ++ rest) steps
          let stack :=
            pairStack next printer later ([Print indent mode inner, ..others.map (Print indent mode)] ++ rest) steps
          let bound: 1 + (inner.steps + stepsOf others) ≤ Succ more := enough
          leadsReads word inner printer indent more mode
            (others.map (Print indent mode) ++ rest)
            final
            leads
            (rewrite moved, stack at laterReads then laterReads)
            blank
            clear
            owed
            filled
            solid
            (arithmetic)
        | Nest deeper inner, leads, steps =>
          let moved := pairPrinter next printer later [Print (indent + deeper) mode inner, ..rest] steps
          let stack := pairStack next printer later [Print (indent + deeper) mode inner, ..rest] steps
          let bound: 1 + inner.steps ≤ Succ more := enough
          leadsReads word inner printer
            (indent + deeper)
            more
            mode
            rest
            final
            leads
            (rewrite moved, stack at laterReads then laterReads)
            blank
            clear
            owed
            filled
            solid
            (arithmetic)
        | Flatten inner, leads, steps =>
          let moved := pairPrinter next printer later [Print indent Flat inner, ..rest] steps
          let stack := pairStack next printer later [Print indent Flat inner, ..rest] steps
          let bound: 1 + inner.steps ≤ Succ more := enough
          leadsReads word inner printer indent more Flat rest final leads
            (rewrite moved, stack at laterReads then laterReads)
            blank
            clear
            owed
            filled
            solid
            (arithmetic)
        | Group inner hard, leads, steps =>
          let bound: 1 + inner.steps ≤ Succ more := enough
          match steps with
            | Inl (Both _ flat) =>
              let moved := pairPrinter next printer later [Print indent Flat inner, ..rest] flat
              let stack := pairStack next printer later [Print indent Flat inner, ..rest] flat
              leadsReads word inner printer indent more Flat rest final leads
                (rewrite moved, stack at laterReads then laterReads)
                blank
                clear
                owed
                filled
                solid
                (arithmetic)
            | Inr (Both _ broken) =>
              let moved := pairPrinter next printer later [Print indent Break inner, ..rest] broken
              let stack := pairStack next printer later [Print indent Break inner, ..rest] broken
              leadsReads word inner printer indent more Break rest final leads
                (rewrite moved, stack at laterReads then laterReads)
                blank
                clear
                owed
                filled
                solid
                (arithmetic)
        | NarrowGroup max inner hard, leads, steps =>
          let bound: 1 + inner.steps ≤ Succ more := enough
          match steps with
            | Inl (Both _ flat) =>
              let moved := pairPrinter next printer later [Print indent Flat inner, ..rest] flat
              let stack := pairStack next printer later [Print indent Flat inner, ..rest] flat
              leadsReads word inner printer indent more Flat rest final leads
                (rewrite moved, stack at laterReads then laterReads)
                blank
                clear
                owed
                filled
                solid
                (arithmetic)
            | Inr (Both _ broken) =>
              let moved := pairPrinter next printer later [Print indent Break inner, ..rest] broken
              let stack := pairStack next printer later [Print indent Break inner, ..rest] broken
              leadsReads word inner printer indent more Break rest final leads
                (rewrite moved, stack at laterReads then laterReads)
                blank
                clear
                owed
                filled
                solid
                (arithmetic)
        | IdGroup id inner hard, leads, steps =>
          let bound: 1 + inner.steps ≤ Succ more := enough
          match steps with
            | Inl (Both _ flat) =>
              let moved := pairPrinter next (printer.record id Flat) later [Print indent Flat inner, ..rest] flat
              let stack := pairStack next (printer.record id Flat) later [Print indent Flat inner, ..rest] flat
              leadsReads word inner
                (printer.record id Flat)
                indent
                more
                Flat
                rest
                final
                leads
                (rewrite moved, stack at laterReads then laterReads)
                blank
                clear
                owed
                filled
                solid
                (arithmetic)
            | Inr (Both _ broken) =>
              let moved := pairPrinter next (printer.record id Break) later [Print indent Break inner, ..rest] broken
              let stack := pairStack next (printer.record id Break) later [Print indent Break inner, ..rest] broken
              leadsReads word inner
                (printer.record id Break)
                indent
                more
                Break
                rest
                final
                leads
                (rewrite moved, stack at laterReads then laterReads)
                blank
                clear
                owed
                filled
                solid
                (arithmetic)

--| A document that leads with a word that isn't spaces prints it first,
--| at every width: no space, line break or comment comes before it.
theorem Doc.Proofs.printedLeads ∀ (word: Text) (doc: Doc) (width: Nat)
    (leads: Leads word doc)
    (filled: word.isEmpty = False)
    (solid: word.all (char => char == ' ') = False):
    ∃ (more: List Text) => printedPieces doc width = [word, ..more] :=
  let fuel := 3 * doc.size + 3
  let ran := (Printer.start width).run fuel fuel [Print 0 Break doc]
  let bound := stepsUnderSize doc
  let first: Atop word ran.out :=
    leadsReads word doc
      (Printer.start width)
      0
      fuel
      Break
      []
      ran
      leads
      (runIsReading (Printer.start width) fuel fuel [Print 0 Break doc])
      byComputing
      byComputing
      byComputing
      filled
      solid
      (arithmetic)
  match flushAtop word ran first with | (front, same) => (front.reverse, (rewrite same, List.reverseSnoc front word))

--| A document that leads with a word isn't empty.
theorem Doc.Proofs.leadsFilled ∀ (word: Text) (doc: Doc) (leads: Leads word doc): doc.isEmpty = False :=
  match doc, leads with
    | Chunk text width, _ => byComputing
    | Concat docs, _ => byComputing
    | Nest deeper inner, _ => byComputing
    | Group inner hard, _ => byComputing
    | NarrowGroup max inner hard, _ => byComputing
    | IdGroup id inner hard, _ => byComputing
    | Flatten inner, _ => byComputing

--| The docs put together, the empty ones left out, lead with what the
--| first leads with.
theorem Doc.Proofs.leadsConcat ∀ (word: Text) (first: Doc) (docs: List Doc)
    (leads: Leads word first):
    Leads word (Doc.concat [first, ..docs]) :=
  rewrite leadsFilled word first leads then
    match kept: docs.filter (doc => not doc.isEmpty) with
      | [] => leads
      | [next, ..others] => leads

-- A document's last word.

--| `doc` writes nothing and breaks no line, whatever its layout: a mark,
--| a forced break, nothing, or a trailing comment, which only waits for
--| the end of the line.
def Doc.Proofs.Silent: Doc → Prop
  | Doc.Nothing => True
  | BreakParent => True
  | Mark _ => True
  | LineSuffix _ => True
  | Concat docs => AllSilent docs
  | _ => False

--| Every doc is `Silent`.
def Doc.Proofs.AllSilent: List Doc → Prop
  | [] => True
  | [doc, ..docs] => Silent doc ∧ AllSilent docs

--| `doc` ends with a word `last` holds of: whatever the layout, the last
--| thing it writes is a chunk or closer, and after it only `Silent` docs.
def Doc.Proofs.Finishes (last: Text → Prop): Doc → Prop
  | Chunk text _ => last text
  | Closing text => last text
  | Nest _ inner => Finishes last inner
  | Align inner => Finishes last inner
  | AlignInset inner => Finishes last inner
  | Displaced inner => Finishes last inner
  | Group inner _ => Finishes last inner
  | NarrowGroup _ inner _ => Finishes last inner
  | IdGroup _ inner _ => Finishes last inner
  | IfBroken _ broken flat => Finishes last broken ∧ Finishes last flat
  | Flatten inner => Finishes last inner
  | OneLineBelow inner => Finishes last inner
  | Concat docs => FinishesAll last docs
  | Fill items => FinishesLast last items
  | Choice options => FinishesEach last options
  | _ => False

--| Some doc ends with a word, and every doc after it is `Silent`.
def Doc.Proofs.FinishesAll (last: Text → Prop): List Doc → Prop
  | [] => False
  | [doc, ..docs] => FinishesAll last docs ∨ (Finishes last doc ∧ AllSilent docs)

--| The last doc ends with a word.
def Doc.Proofs.FinishesLast (last: Text → Prop): List Doc → Prop
  | [] => False
  | [item] => Finishes last item
  | [_, ..items] => FinishesLast last items

--| There is a doc, and each ends with a word.
def Doc.Proofs.FinishesEach (last: Text → Prop): List Doc → Prop
  | [] => False
  | [option] => Finishes last option
  | [option, ..others] => Finishes last option ∧ FinishesEach last others

--| A command's doc ends with a word.
def Doc.Proofs.CmdFinishes (last: Text → Prop): Cmd → Prop
  | Print _ _ doc => Finishes last doc
  | FillSep _ item => Finishes last item

--| A command's doc is `Silent` (a fill separator never is: it writes a
--| space or breaks the line).
def Doc.Proofs.CmdSilent: Cmd → Prop
  | Print _ _ doc => Silent doc
  | FillSep _ _ => False

--| Every command on the work list is `CmdSilent`.
def Doc.Proofs.StackSilent: List Cmd → Prop
  | [] => True
  | [cmd, ..rest] => CmdSilent cmd ∧ StackSilent rest

--| Some command on the work list ends with a word, and every command
--| after it is silent.
def Doc.Proofs.StackFinishes (last: Text → Prop): List Cmd → Prop
  | [] => False
  | [cmd, ..rest] => StackFinishes last rest ∨ (CmdFinishes last cmd ∧ StackSilent rest)

--| The printer's last piece is a word `last` holds of, on the line it
--| started.
def Doc.Proofs.Topped (last: Text → Prop) (printer: Printer): Prop :=
  ∃ (word: Text) => ∃ (more: List Text) => last word ∧ printer.out = [word, ..more] ∧ printer.atLineStart = False

--| A reading is on its way to end with a word: the work list still ends
--| with one, or the printer has written it and only silent commands are
--| left.
def Doc.Proofs.Finishing (last: Text → Prop) (printer: Printer) (stack: List Cmd): Prop :=
  StackFinishes last stack ∨ (Topped last printer ∧ StackSilent stack)

--| A work list that ends with a word still does with commands in front.
theorem Doc.Proofs.stackFinishesAppend ∀ (last: Text → Prop) (front back: List Cmd)
    (ends: StackFinishes last back):
    StackFinishes last (front ++ back) :=
  match front with
    | [] => ends
    | [cmd, ..rest] => Inl (stackFinishesAppend last rest back ends)

--| Printing silent docs before a silent work list is a silent work list.
theorem Doc.Proofs.printsSilent ∀ (indent: Nat) (mode: Mode) (docs: List Doc) (rest: List Cmd)
    (quiet: AllSilent docs)
    (silent: StackSilent rest):
    StackSilent (docs.map (Print indent mode) ++ rest) :=
  match docs, quiet with
    | [], _ => silent
    | [doc, ..others], Both first more => (first, (printsSilent indent mode others rest more silent))

--| Printing docs that end with a word, before a silent work list, is a
--| work list that ends with one.
theorem Doc.Proofs.printsFinish ∀ (last: Text → Prop) (indent: Nat) (mode: Mode) (docs: List Doc) (rest: List Cmd)
    (ends: FinishesAll last docs)
    (silent: StackSilent rest):
    StackFinishes last (docs.map (Print indent mode) ++ rest) :=
  match docs, ends with
    | [], never => cases
    | [doc, ..others], Inl later => Inl (printsFinish last indent mode others rest later silent)
    | [doc, ..others], Inr (Both first quiet) => Inr (first, (printsSilent indent mode others rest quiet silent))

--| The separators before items whose last ends with a word, before a
--| silent work list, are a work list that ends with one.
theorem Doc.Proofs.fillSepsFinish ∀ (last: Text → Prop) (indent: Nat) (items: List Doc) (rest: List Cmd)
    (ends: FinishesLast last items)
    (silent: StackSilent rest):
    StackFinishes last (items.map (FillSep indent) ++ rest) :=
  match items, ends with
    | [], never => cases
    | [only], ends => Inr (ends, silent)
    | [item, next, ..more], ends => Inl (fillSepsFinish last indent [next, ..more] rest ends silent)

--| Putting a `Line` between items whose last ends with a word leaves docs
--| that end with one.
theorem Doc.Proofs.joinLinesFinish ∀ (last: Text → Prop) (items: List Doc)
    (ends: FinishesLast last items):
    FinishesAll last (Doc.joinLines items) :=
  match items, ends with
    | [], never => cases
    | [only], ends => Inr (ends, byComputing)
    | [item, next, ..more], ends => Inl (Inl (joinLinesFinish last [next, ..more] ends))

--| The option a broken `Choice` takes ends with a word if each does.
theorem Doc.Proofs.optionFinishes ∀ (last: Text → Prop) (chosen: Doc) (options: List Doc)
    (isOption: IsOption chosen options)
    (ends: FinishesEach last options):
    Finishes last chosen :=
  match options, isOption, ends with
    | [], _, never => cases
    | [only], picked, ends => rewrite picked then ends
    | [option, next, ..more], Inl picked, Both first _ => rewrite picked then first
    | [option, next, ..more], Inr later, Both _ others => optionFinishes last chosen [next, ..more] later others

--| The option a flat `Choice` takes, its first, ends with a word if each
--| does.
theorem Doc.Proofs.headOrFinishes ∀ (last: Text → Prop) (options: List Doc)
    (ends: FinishesEach last options):
    Finishes last (options.headOr Doc.Nothing) :=
  match options, ends with
    | [], never => cases
    | [only], ends => ends
    | [option, next, ..more], Both first _ => first

--| The branch an `IfBroken` takes ends with a word if both do.
theorem Doc.Proofs.pickFinishes ∀ (last: Text → Prop) (modes: List (Nat, Mode)) (id: Nat) (broken flat: Doc)
    (brokenEnds: Finishes last broken)
    (flatEnds: Finishes last flat):
    Finishes last (pickBranch modes id broken flat) :=
  match pickEither modes id broken flat with
    | Inl isBroken => rewrite isBroken then brokenEnds
    | Inr isFlat => rewrite isFlat then flatEnds

--| A step only changes the front of the work list: what was after the
--| command is still at the end.
theorem Doc.Proofs.eitherFront ∀ (condition: Bool) (yes no: (Printer, List Cmd)) (rest: List Cmd)
    (whenYes: ∃ (front: List Cmd) => yes.snd = front ++ rest)
    (whenNo: ∃ (front: List Cmd) => no.snd = front ++ rest):
    ∃ (front: List Cmd) => (if condition then yes else no).snd = front ++ rest :=
  match condition with
    | True => whenYes
    | False => whenNo

--| A step of a reading only changes the front of the work list.
theorem Doc.Proofs.stepFront ∀ (printer: Printer) (cmd: Cmd) (rest: List Cmd) (result: (Printer, List Cmd))
    (steps: StepsTo printer cmd rest result):
    ∃ (front: List Cmd) => result.snd = front ++ rest :=
  match cmd, steps with
    | FillSep indent item, Inl (Both _ flat) => rewrite flat then ([Print indent Flat item], byComputing)
    | FillSep indent item, Inr broken => rewrite broken then ([Print indent Break item], byComputing)
    | Print indent mode doc, steps =>
      match doc, steps with
        | Doc.Nothing, steps => rewrite steps then ([], byComputing)
        | BreakParent, steps => rewrite steps then ([], byComputing)
        | Chunk text width, steps => rewrite steps then ([], byComputing)
        | Closing text, steps => rewrite steps then ([], byComputing)
        | Line, steps =>
          rewrite steps then
            eitherFront mode.isFlat
              (printer.write indent " " 1, rest)
              (printer.newline indent, rest)
              rest
              ([], byComputing)
              ([], byComputing)
        | SoftLine, steps =>
          rewrite steps then
            eitherFront mode.isFlat (printer, rest) (printer.newline indent, rest) rest ([], byComputing) (
              [],
              byComputing
            )
        | HardLine, steps => rewrite steps then ([], byComputing)
        | Mark key, steps => rewrite steps then ([], byComputing)
        | CloserLine key, steps => rewrite steps then ([], byComputing)
        | LineStart, steps => rewrite steps then ([], byComputing)
        | LineStartHere, steps =>
          rewrite steps then
            eitherFront printer.atLineStart
              ({ printer | owed = Some indent, lineIndent = indent }, rest)
              (printer.newline indent, rest)
              rest
              ([], byComputing)
              ([], byComputing)
        | Blank, steps => rewrite steps then ([], byComputing)
        | Nest more inner, steps => rewrite steps then ([Print (indent + more) mode inner], byComputing)
        | Align inner, steps => rewrite steps then ([Print (printer.alignAt indent) mode inner], byComputing)
        | AlignInset inner, steps => rewrite steps then ([Print (printer.alignAt (indent + 2)) mode inner], byComputing)
        | Displaced inner, steps => rewrite steps then ([Print (printer.displacedAt indent) mode inner], byComputing)
        | OneLineBelow inner, steps =>
          rewrite steps then ([Print (indent + 2) mode HardLine, Print (indent + 2) mode inner], byComputing)
        | Flatten inner, steps => rewrite steps then ([Print indent Flat inner], byComputing)
        | LineSuffix comment, steps => rewrite steps then ([], byComputing)
        | Group inner hard, Inl (Both _ flat) => rewrite flat then ([Print indent Flat inner], byComputing)
        | Group inner hard, Inr (Both _ broken) => rewrite broken then ([Print indent Break inner], byComputing)
        | NarrowGroup max inner hard, Inl (Both _ flat) => rewrite flat then ([Print indent Flat inner], byComputing)
        | NarrowGroup max inner hard, Inr (Both _ broken) =>
          rewrite broken then ([Print indent Break inner], byComputing)
        | IdGroup id inner hard, Inl (Both _ flat) => rewrite flat then ([Print indent Flat inner], byComputing)
        | IdGroup id inner hard, Inr (Both _ broken) => rewrite broken then ([Print indent Break inner], byComputing)
        | IfBroken id broken flat, steps =>
          rewrite steps then ([Print indent mode (pickBranch printer.modes id broken flat)], byComputing)
        | Concat docs, steps => rewrite steps then (docs.map (Print indent mode), byComputing)
        | Fill [], steps => rewrite steps then ([], byComputing)
        | Fill [first, ..others], Inl (Both _ flat) =>
          rewrite flat then (Doc.joinLines [first, ..others] |> .map (Print indent Flat), byComputing)
        | Fill [first, ..others], Inr (Both _ (Witness firstMode broken)) =>
          rewrite broken then ([Print indent firstMode first, ..others.map (FillSep indent)], byComputing)
        | Choice options, Inl (Both _ flat) =>
          rewrite flat then ([Print indent mode (options.headOr Doc.Nothing)], byComputing)
        | Choice options, Inr (Both _ (Witness chosen (Both _ broken))) =>
          rewrite broken then ([Print indent mode chosen], byComputing)

--| Text put on the line leaves it the last piece, on a started line.
theorem Doc.Proofs.putTopped ∀ (last: Text → Prop) (printer: Printer) (text: Text) (width: Nat) (isLast: last text):
    Topped last (printer.put text width) :=
  (text, (printer.payIndent.out, (isLast, (byComputing, byComputing))))

--| A word that isn't spaces, written, is the last piece.
theorem Doc.Proofs.writeTopped ∀ (last: Text → Prop) (printer: Printer) (indent: Nat) (text: Text) (width: Nat)
    (solid: isLayout text = False) (isLast: last text):
    Topped last (printer.write indent text width) :=
  rewrite wordFilled text solid then
    match waiting: printer.suffixes.isEmpty with
      | True => putTopped last printer text width isLast
      | False =>
        match spaces: text.all (char => char == ' ') with
          | False => putTopped last (printer.newline (printer.continuation indent)) text width isLast

--| A closer written is the last piece.
theorem Doc.Proofs.closeTopped ∀ (last: Text → Prop) (printer: Printer) (text: Text)
    (solid: isLayout text = False) (isLast: last text):
    Topped last (printer.close text) :=
  rewrite wordFilled text solid then
    match waiting: printer.suffixes.isEmpty with
      | True => putTopped last printer text text.length isLast
      | False => putTopped last printer.writeHeld text text.length isLast

--| A step on a command that ends with a word keeps the reading on its way
--| to end with one.
theorem Doc.Proofs.cmdFinishes ∀ (last: Text → Prop) (printer: Printer) (cmd: Cmd)
    (rest: List Cmd) (result: (Printer, List Cmd))
    (steps: StepsTo printer cmd rest result)
    (solid: ∀ (text: Text) => last text → isLayout text = False)
    (ends: CmdFinishes last cmd)
    (silent: StackSilent rest):
    Finishing last result.fst result.snd :=
  match cmd, steps, ends with
    | FillSep indent item, Inl (Both _ flat), ends => rewrite flat then Inl (Inr (ends, silent))
    | FillSep indent item, Inr broken, ends => rewrite broken then Inl (Inr (ends, silent))
    | Print indent mode doc, steps, ends =>
      match doc, steps, ends with
        | Chunk text width, steps, isLast =>
          rewrite steps then Inr ((writeTopped last printer indent text width (solid text isLast) isLast), silent)
        | Closing text, steps, isLast =>
          rewrite steps then Inr ((closeTopped last printer text (solid text isLast) isLast), silent)
        | Nest more inner, steps, ends => rewrite steps then Inl (Inr (ends, silent))
        | Align inner, steps, ends => rewrite steps then Inl (Inr (ends, silent))
        | AlignInset inner, steps, ends => rewrite steps then Inl (Inr (ends, silent))
        | Displaced inner, steps, ends => rewrite steps then Inl (Inr (ends, silent))
        | Flatten inner, steps, ends => rewrite steps then Inl (Inr (ends, silent))
        | OneLineBelow inner, steps, ends => rewrite steps then Inl (Inl (Inr (ends, silent)))
        | Group inner hard, Inl (Both _ flat), ends => rewrite flat then Inl (Inr (ends, silent))
        | Group inner hard, Inr (Both _ broken), ends => rewrite broken then Inl (Inr (ends, silent))
        | NarrowGroup max inner hard, Inl (Both _ flat), ends => rewrite flat then Inl (Inr (ends, silent))
        | NarrowGroup max inner hard, Inr (Both _ broken), ends => rewrite broken then Inl (Inr (ends, silent))
        | IdGroup id inner hard, Inl (Both _ flat), ends => rewrite flat then Inl (Inr (ends, silent))
        | IdGroup id inner hard, Inr (Both _ broken), ends => rewrite broken then Inl (Inr (ends, silent))
        | IfBroken id broken flat, steps, Both brokenEnds flatEnds =>
          rewrite steps then Inl (Inr ((pickFinishes last printer.modes id broken flat brokenEnds flatEnds), silent))
        | Concat docs, steps, ends => rewrite steps then Inl (printsFinish last indent mode docs rest ends silent)
        | Fill [first, ..others], Inl (Both _ flat), ends =>
          rewrite flat then
            Inl
              (printsFinish last indent Flat
                (Doc.joinLines [first, ..others])
                rest
                (joinLinesFinish last [first, ..others] ends)
                silent)
        | Fill [only], Inr (Both _ (Witness firstMode broken)), ends => rewrite broken then Inl (Inr (ends, silent))
        | Fill [first, next, ..more], Inr (Both _ (Witness firstMode broken)), ends =>
          rewrite broken then Inl (Inl (fillSepsFinish last indent [next, ..more] rest ends silent))
        | Choice options, Inl (Both _ flat), ends =>
          rewrite flat then Inl (Inr ((headOrFinishes last options ends), silent))
        | Choice options, Inr (Both _ (Witness chosen (Both isOption broken))), ends =>
          rewrite broken then Inl (Inr ((optionFinishes last chosen options isOption ends), silent))
        | _, _, never => cases

--| A step on a silent command, once the word is written, keeps it the
--| last piece.
theorem Doc.Proofs.silentStep ∀ (last: Text → Prop) (printer: Printer) (cmd: Cmd)
    (rest: List Cmd) (result: (Printer, List Cmd))
    (steps: StepsTo printer cmd rest result)
    (topped: Topped last printer)
    (quiet: CmdSilent cmd)
    (silent: StackSilent rest):
    Finishing last result.fst result.snd :=
  match cmd, steps, quiet with
    | Print indent mode doc, steps, quiet =>
      match doc, steps, quiet with
        | Doc.Nothing, steps, _ => rewrite steps then Inr (topped, silent)
        | BreakParent, steps, _ => rewrite steps then Inr (topped, silent)
        | Mark key, steps, _ => rewrite steps then Inr (topped, silent)
        | LineSuffix comment, steps, _ => rewrite steps then Inr (topped, silent)
        | Concat docs, steps, quiet =>
          rewrite steps then Inr (topped, (printsSilent indent mode docs rest quiet silent))
        | _, _, never => cases
    | FillSep indent item, _, never => cases

--| Every step keeps a reading on its way to end with a word.
theorem Doc.Proofs.stepFinishes ∀ (last: Text → Prop) (printer: Printer) (cmd: Cmd)
    (rest: List Cmd) (result: (Printer, List Cmd))
    (steps: StepsTo printer cmd rest result)
    (solid: ∀ (text: Text) => last text → isLayout text = False)
    (ahead: Finishing last printer [cmd, ..rest]):
    Finishing last result.fst result.snd :=
  match ahead with
    | Inl (Inl later) =>
      match stepFront printer cmd rest result steps with
        | (front, same) => Inl (rewrite same then stackFinishesAppend last front rest later)
    | Inl (Inr (Both ends silent)) => cmdFinishes last printer cmd rest result steps solid ends silent
    | Inr (Both topped (Both quiet silent)) => silentStep last printer cmd rest result steps topped quiet silent

--| A reading on its way to end with a word, with the steps to finish,
--| leaves that word the last piece, on the line it started.
theorem Doc.Proofs.readingFinishes ∀ (last: Text → Prop) (printer: Printer) (fuel: Nat)
    (stack: List Cmd) (final: Printer)
    (reads: Doc.Proofs.Reads printer fuel stack final)
    (solid: ∀ (text: Text) => last text → isLayout text = False)
    (ahead: Finishing last printer stack)
    (enough: stackCost stack ≤ fuel):
    Topped last final :=
  match fuel, stack, reads, ahead with
    | Zero, [], reads, Inr (Both topped _) => rewrite reads then topped
    | Succ more, [], reads, Inr (Both topped _) => rewrite reads then topped
    | _, [], _, Inl never => cases
    | Zero, [cmd, ..rest], _, _ =>
      let positive := costPositive cmd
      Void.impossible (arithmetic)
    | Succ more, [cmd, ..rest], Witness next (Witness later (Both steps laterReads)), ahead =>
      let lighter := readingLighter printer cmd rest (next, later) steps
      readingFinishes last next more later final laterReads solid
        (stepFinishes last printer cmd rest (next, later) steps solid ahead)
        (arithmetic)

--| Through a reading of a marked work list, the comments that wait are
--| the document's trailing comments.
theorem Doc.Proofs.readingQuiet ∀ (closer suffix: Text → Prop) (printer: Printer) (fuel: Nat)
    (stack: List Cmd) (final: Printer)
    (reads: Doc.Proofs.Reads printer fuel stack final)
    (marked: StackMarked closer suffix stack)
    (waits: Every suffix printer.suffixes):
    Every suffix final.suffixes :=
  match fuel, stack, reads, marked with
    | Zero, [], reads, _ => rewrite reads then waits
    | Succ more, [], reads, _ => rewrite reads then waits
    | Zero, [cmd, ..rest], reads, _ => rewrite reads then waits
    | Succ more, [cmd, ..rest], Witness next (Witness later (Both steps laterReads)), Both first others =>
      readingQuiet closer suffix next more later final laterReads
        (stepMarked closer suffix printer cmd rest (next, later) steps first others)
        (stepQuiet closer suffix printer cmd rest (next, later) steps first waits)

--| Trailing comments as the printer writes them at the end of a line
--| with code on it: each after a space.
def Doc.Proofs.spacedComments: List Text → List Text
  | [] => []
  | [comment, ..comments] => [" ", comment, ..spacedComments comments]

--| Writing comments on a started line puts each after a space.
theorem Doc.Proofs.flushEachTopped ∀ (comments: List Text) (printer: Printer)
    (started: printer.atLineStart = False):
    (comments.foldLeft printer Printer.flushOne).out.reverse = printer.out.reverse ++ spacedComments comments :=
  match comments with
    | [] => (List.appendNil printer.out.reverse).flipped
    | [comment, ..later] =>
      let flushed: (printer.flushOne comment).out = [comment, " ", ..printer.out] := rewrite started
      rewrite flushEachTopped later (printer.flushOne comment) byComputing,
          flushed,
          List.reverseCons comment [" ", ..printer.out],
          List.reverseCons " " printer.out,
          List.appendAssoc (printer.out.reverse ++ [" "]) [comment] (spacedComments later),
          List.appendAssoc printer.out.reverse [" "] ([comment] ++ spacedComments later)

--| Writing the waiting comments on a started line puts each after a
--| space.
theorem Doc.Proofs.flushTopped ∀ (printer: Printer)
    (started: printer.atLineStart = False):
    printer.flushSuffixes.out.reverse = printer.out.reverse ++ spacedComments printer.suffixes :=
  flushEachTopped printer.suffixes { printer | suffixes = [] } started

--| A document that ends with a word prints it last at every width, and
--| after it only trailing comments of the document, each after a space:
--| no line break, and no space but before a comment.
--|
--| Proof idea: the reading takes the work list apart until the command
--| that ends is first, every step leaving what follows it in place
--| (`stepFront`); that command writes the word or hands the ending to
--| its parts (`cmdFinishes`), and the silent commands after it write nothing
--| (`silentStep`). The comments waiting at the end are the document's
--| (`readingQuiet`), and flushing writes each after a space
--| (`flushTopped`).
theorem Doc.Proofs.printedFinishes ∀ (last closer suffix: Text → Prop) (doc: Doc) (width: Nat)
    (ends: Finishes last doc)
    (solid: ∀ (text: Text) => last text → isLayout text = False)
    (marked: Marked closer suffix doc):
    ∃ (front: List Text) => ∃ (word: Text) => ∃ (comments: List Text) => last word
      ∧ Every suffix comments
      ∧ printedPieces doc width = front ++ [word, ..spacedComments comments] :=
  let fuel := 3 * doc.size + 3
  let ran := (Printer.start width).run fuel fuel [Print 0 Break doc]
  let reads := runIsReading (Printer.start width) fuel fuel [Print 0 Break doc]
  let bound := stepsUnderSize doc
  let topped: Topped last ran :=
    readingFinishes last
      (Printer.start width)
      fuel
      [Print 0 Break doc]
      ran
      reads
      solid
      (Inl (Inr (ends, byComputing)))
      (arithmetic)
  let quiet: Every suffix ran.suffixes :=
    readingQuiet closer suffix
      (Printer.start width)
      fuel
      [Print 0 Break doc]
      ran
      reads
      (marked, byComputing)
      byComputing
  match topped with
    | (word, (more, (isLast, (out, started)))) => (
      more.reverse,
      (
        word,
        (
          ran.suffixes,
          (
            isLast,
            (
              quiet,
              (Eq.trans
                (flushTopped ran started)
                (rewrite out,
                    List.reverseCons word more,
                    List.appendAssoc more.reverse [word] (spacedComments ran.suffixes)))
            )
          )
        )
      )
    )

-- Building documents that finish with a word.

--| A document that finishes with a word isn't empty.
theorem Doc.Proofs.finishesFilled ∀ (last: Text → Prop) (doc: Doc) (ends: Finishes last doc): doc.isEmpty = False :=
  match doc, ends with
    | Doc.Nothing, never => cases
    | Chunk _ _, _ => byComputing
    | Closing _, _ => byComputing
    | Nest _ _, _ => byComputing
    | Align _, _ => byComputing
    | AlignInset _, _ => byComputing
    | Displaced _, _ => byComputing
    | Group _ _, _ => byComputing
    | NarrowGroup _ _ _, _ => byComputing
    | IdGroup _ _ _, _ => byComputing
    | IfBroken _ _ _, _ => byComputing
    | Flatten _, _ => byComputing
    | OneLineBelow _, _ => byComputing
    | Concat _, _ => byComputing
    | Fill _, _ => byComputing
    | Choice _, _ => byComputing

--| Leaving out the empty docs keeps silent docs silent.
theorem Doc.Proofs.silentKept ∀ (docs: List Doc)
    (quiet: AllSilent docs):
    AllSilent (docs.filter (doc => not doc.isEmpty)) :=
  match docs, quiet with
    | [], _ => byComputing
    | [doc, ..others], Both first more =>
      match empty: doc.isEmpty with
        | True => silentKept others more
        | False => (first, (silentKept others more))

--| Leaving out the empty docs keeps docs that finish with a word
--| finishing with it.
theorem Doc.Proofs.finishesKept ∀ (last: Text → Prop) (docs: List Doc)
    (ends: FinishesAll last docs):
    FinishesAll last (docs.filter (doc => not doc.isEmpty)) :=
  match docs, ends with
    | [], never => cases
    | [doc, ..others], Inl later =>
      match empty: doc.isEmpty with
        | True => finishesKept last others later
        | False => Inl (finishesKept last others later)
    | [doc, ..others], Inr (Both first quiet) =>
      rewrite finishesFilled last doc first then Inr (first, (silentKept others quiet))

--| The docs put together, the empty ones left out, finish with the word
--| they finish with.
theorem Doc.Proofs.finishesConcat ∀ (last: Text → Prop) (docs: List Doc)
    (ends: FinishesAll last docs):
    Finishes last (Doc.concat docs) :=
  let kept := finishesKept last docs ends
  match found: docs.filter (doc => not doc.isEmpty) with
    | [only] =>
      match kept with
        | Inl never => cases
        | Inr (Both first _) => first
    | [first, second, ..rest] => kept

--| Docs that finish with a word still do with docs in front.
theorem Doc.Proofs.finishesAppend ∀ (last: Text → Prop) (front back: List Doc)
    (ends: FinishesAll last back):
    FinishesAll last (front ++ back) :=
  match front with
    | [] => ends
    | [doc, ..rest] => Inl (finishesAppend last rest back ends)

--| Docs whose last finishes with a word finish with it.
theorem Doc.Proofs.finishesOfLast ∀ (last: Text → Prop) (docs: List Doc)
    (ends: FinishesLast last docs):
    FinishesAll last docs :=
  match docs, ends with
    | [], never => cases
    | [only], ends => Inr (ends, byComputing)
    | [doc, next, ..more], ends => Inl (finishesOfLast last [next, ..more] ends)

--| Docs whose last finishes with a word, a separator between each two,
--| finish with it.
theorem Doc.Proofs.joinedFinishes ∀ (last: Text → Prop) (separator: Doc) (docs: List Doc)
    (ends: FinishesLast last docs):
    FinishesLast last (Doc.joinedWith separator docs) :=
  match docs, ends with
    | [], never => cases
    | [only], ends => ends
    | [doc, next], ends => ends
    | [doc, next, after, ..more], ends => joinedFinishes last separator [next, after, ..more] ends

--| Docs whose last finishes with a word still do with docs in front.
theorem Doc.Proofs.finishesLastAppend ∀ (last: Text → Prop) (front back: List Doc)
    (ends: FinishesLast last back):
    FinishesLast last (front ++ back) :=
  match front, back, ends with
    | _, [], never => cases
    | [], back, ends => ends
    | [doc], [next, ..more], ends => ends
    | [doc, second, ..rest], back, ends => finishesLastAppend last [second, ..rest] back ends
