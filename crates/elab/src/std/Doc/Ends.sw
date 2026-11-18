--| What the printed text starts with. The printer only ever writes in
--| front of what it has written (the output is kept the last piece first),
--| and the only pieces it takes back are spaces at the end of a line
--| (`trimSpaces`). So once a word that isn't spaces is the first piece of
--| the output, it stays first through every reading (`readingAtop`); and
--| a document that starts with a chunk (`Leads`) writes that chunk first,
--| before any space or line break, whatever the width
--| (`printedLeads`).

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
