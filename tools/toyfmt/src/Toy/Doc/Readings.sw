--| The width only chooses among readings. A reading of a document is a
--| run of the printer in which every question the printer asks of the
--| width (does this group fit flat, does the next fill item fit, which
--| option of a choice fits) may be answered either way; everything else,
--| what a chunk, a line break or a comment writes, is the printer's own
--| step. `print` at any width is one reading (`printIsReading`), so what
--| is proved of every reading (that its text lexes and parses back to the
--| tree) holds of `print` at every width, with nothing about `fits`.

namespace Toy.Doc.Proofs
import Toy.Doc (..)
import Std (Bool, List, Nat, Option, Text)

--| `chosen` is what a `Choice` of `options` may print: one of them, or
--| nothing for no options.
def IsOption (chosen: Doc): List Doc → Prop
  | [] => chosen = Empty
  | [last] => chosen = last
  | [option, ..others] => chosen = option ∨ IsOption chosen others

--| One step of a reading: from `printer`, with `cmd` first on the work
--| list and `rest` after it, to the printer and work list `next`. A fill
--| separator is a space (only with no comment waiting) or a line break; a
--| group goes flat (only if it holds no hard break, or is in a flat one
--| already) or breaks; a broken fill's first item goes either way; a
--| broken choice takes any option. Every other step is the printer's,
--| which doesn't look at the width.
def StepsTo (printer: Printer) (cmd: Cmd) (rest: List Cmd) (next: (Printer, List Cmd)): Prop := match cmd with
  | FillSep indent item =>
    (printer.suffixes.isEmpty = True ∧ next = (printer.write indent " " 1, [Print indent Flat item, ..rest]))
      ∨ next = (printer.newline indent, [Print indent Break item, ..rest])
  | Print indent mode doc =>
    match doc with
      | Group inner hard =>
        ((mode.isFlat = True ∨ hard = False) ∧ next = (printer, [Print indent Flat inner, ..rest]))
          ∨ (mode.isFlat = False ∧ next = (printer, [Print indent Break inner, ..rest]))
      | Fill [] => next = (printer, rest)
      | Fill [first, ..others] =>
        (mode.isFlat = True ∧ next = (printer, (Doc.joinLines [first, ..others] |> .map (Print indent Flat)) ++ rest))
          ∨ (mode.isFlat = False
            ∧ (∃ (firstMode: Mode) => next
              = (printer, [Print indent firstMode first, ..others.map (FillSep indent) ++ rest])))
      | Choice options =>
        (mode.isFlat = True ∧ next = (printer, [Print indent mode (options.headOr Empty), ..rest]))
          ∨ (mode.isFlat = False
            ∧ (∃ (chosen: Doc) => IsOption chosen options ∧ next = (printer, [Print indent mode chosen, ..rest])))
      | _ => next = printer.printDoc 0 indent mode doc rest

--| `final` is where a reading of the work list `stack` from `printer`
--| stops, in at most `fuel` steps.
def Reads (printer: Printer) (fuel: Nat) (stack: List Cmd) (final: Printer): Prop := match fuel, stack with
  | 0, _ => final = printer
  | _, [] => final = printer
  | Succ more, [cmd, ..rest] =>
    ∃ (next: Printer) => ∃ (later: List Cmd) => StepsTo printer cmd rest (next, later) ∧ Reads next more later final

theorem ifIsOption ∀ (condition: Bool) (option later: Doc) (others: List Doc)
    (laterIs: IsOption later others):
    (if condition then option else later) = option ∨ IsOption (if condition then option else later) others :=
  match condition with
    | True => Inl rfl
    | False => Inr laterIs

--| What a broken `Choice` takes is one of its options.
theorem chooseIsOption ∀ (printer: Printer) (total indent: Nat) (rest: List Cmd) (options: List Doc):
    IsOption (printer.choose total indent rest options) options :=
  match options with
    | [] => rfl
    | [last] => rfl
    | [option, next, ..others] =>
      ifIsOption _ option
        (printer.choose total indent rest [next, ..others])
        [next, ..others]
        (chooseIsOption printer total indent rest [next, ..others])

--| Every step of the printer, at any width and budget, is a step of a
--| reading.
theorem stepIsReading ∀ (printer: Printer) (total: Nat) (cmd: Cmd) (rest: List Cmd):
    StepsTo printer cmd rest (printer.step total cmd rest) :=
  match cmd with
    | FillSep indent item =>
      match empty: printer.suffixes.isEmpty with
        | False => Inr rfl
        | True =>
          match fit: fits total [(Flat, item)] rest (printer.left - 1) with
            | True => Inl ((rfl, rfl))
            | False => Inr rfl
    | Print indent mode doc =>
      match doc with
        | Group inner hard =>
          match mode with
            | Flat => Inl (((Inl rfl), rfl))
            | Break =>
              match hard with
                | True => Inr ((rfl, rfl))
                | False =>
                  match fit: printer.fitsHere total [(Flat, inner)] rest with
                    | True => Inl (((Inr rfl), rfl))
                    | False => Inr ((rfl, rfl))
        | Fill [] => rfl
        | Fill [first, ..others] =>
          match mode with
            | Flat => Inl ((rfl, rfl))
            | Break =>
              Inr
                ((
                  rfl,
                  (if printer.fitsHere total [(Flat, first)] (others.map (FillSep indent) ++ rest) then Flat
                   else Break),
                  rfl
                ))
        | Choice options =>
          match mode with
            | Flat => Inl ((rfl, rfl))
            | Break =>
              Inr
                ((
                  rfl,
                  (printer.choose total indent rest options),
                  (chooseIsOption printer total indent rest options),
                  rfl
                ))
        | Empty => rfl
        | Chunk text width => rfl
        | Line => rfl
        | SoftLine => rfl
        | HardLine => rfl
        | Blank => rfl
        | Nest more inner => rfl
        | Concat docs => rfl
        | Flatten inner => rfl
        | OneLineBelow inner => rfl
        | LineSuffix comment => rfl
        | LineStart => rfl
        | CommentEnd => rfl
        | LineStartHere => rfl
        | BreakParent => rfl

--| A run of the printer, at any width and budget, is a reading.
theorem runIsReading ∀ (printer: Printer) (total fuel: Nat) (stack: List Cmd):
    Reads printer fuel stack (printer.run total fuel stack) :=
  match fuel, stack with
    | 0, stack => rfl
    | Succ more, [] => rfl
    | Succ more, [cmd, ..rest] =>
      let isStep := stepIsReading printer total cmd rest
      match stepped: printer.step total cmd rest with
        | (next, later) => (next, later, isStep, (runIsReading next total more later))

--| `print` is one of the readings: at every width, the text it gives is
--| what some reading of the document, from the empty printer, leaves
--| (its pieces joined, after the last line's trailing comment). So the
--| width never matters to what holds of every reading.
theorem printIsReading ∀ (doc: Doc) (width: Nat):
    ∃ (final: Printer) => Reads (Printer.start width) (3 * doc.size + 3) [Print 0 Break doc] final
      ∧ print doc width = final.flushSuffixes.out.reverse.joinWith "" :=
  (
    ((Printer.start width).run (3 * doc.size + 3) (3 * doc.size + 3) [Print 0 Break doc]),
    (runIsReading (Printer.start width) (3 * doc.size + 3) (3 * doc.size + 3) [Print 0 Break doc]),
    rfl
  )
