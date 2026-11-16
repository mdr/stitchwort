/-
The width only chooses among readings. A reading of a document is a run
of the printer in which every question the printer asks of the width may
be answered either way; `print` at any width is one reading
(`printIsReading`). A port of `tools/toyfmt/src/Toy/Doc/Readings.sw`.

Idiomatic version: anything in core Lean (`simp`, `grind`,
`fun_induction`).
-/
import Toy.Print

namespace Toy
open Doc Cmd Mode

/-- `chosen` is what a `Choice` of `options` may print: one of them, or
nothing for no options. -/
def IsOption (chosen : Doc) : List Doc → Prop
  | [] => chosen = Doc.Empty
  | [last] => chosen = last
  | option :: others => chosen = option ∨ IsOption chosen others

/-- One step of a reading: from `printer`, with `cmd` first on the work
list and `rest` after it, to the printer and work list `next`. A fill
separator is a space (only with no comment waiting) or a line break; a
group goes flat (only if it holds no hard break, or is in a flat one
already) or breaks; a broken fill's first item goes either way; a broken
choice takes any option. Every other step is the printer's, which
doesn't look at the width. -/
def StepsTo (printer : Printer) (cmd : Cmd) (rest : List Cmd) (next : Printer × List Cmd) : Prop :=
  match cmd with
  | FillSep indent item =>
    (printer.suffixes.isEmpty = true ∧ next = (printer.write indent Text.space 1, Print indent Flat item :: rest))
      ∨ next = (printer.newline indent, Print indent Break item :: rest)
  | Print indent mode doc =>
    match doc with
    | Group inner hard =>
      ((mode.isFlat = true ∨ hard = false) ∧ next = (printer, Print indent Flat inner :: rest))
        ∨ (mode.isFlat = false ∧ next = (printer, Print indent Break inner :: rest))
    | Fill [] => next = (printer, rest)
    | Fill (first :: others) =>
      (mode.isFlat = true ∧ next = (printer, (Doc.joinLines (first :: others)).map (Print indent Flat) ++ rest))
        ∨ (mode.isFlat = false
          ∧ ∃ firstMode : Mode, next = (printer, Print indent firstMode first :: (others.map (FillSep indent) ++ rest)))
    | Choice options =>
      (mode.isFlat = true ∧ next = (printer, Print indent mode (options.headD Doc.Empty) :: rest))
        ∨ (mode.isFlat = false
          ∧ ∃ chosen : Doc, IsOption chosen options ∧ next = (printer, Print indent mode chosen :: rest))
    | _ => next = printer.printDoc 0 indent mode doc rest

/-- `final` is where a reading of the work list `stack` from `printer`
stops, in at most `fuel` steps. -/
def Reads (printer : Printer) (fuel : Nat) (stack : List Cmd) (final : Printer) : Prop :=
  match fuel, stack with
  | 0, _ => final = printer
  | _, [] => final = printer
  | more + 1, cmd :: rest =>
    ∃ next : Printer, ∃ later : List Cmd, StepsTo printer cmd rest (next, later) ∧ Reads next more later final

/-- What a broken `Choice` takes is one of its options. -/
theorem chooseIsOption (printer : Printer) (total indent : Nat) (rest : List Cmd) (options : List Doc) :
    IsOption (printer.choose total indent rest options) options := by
  fun_induction Printer.choose printer total indent rest options <;> grind [IsOption]

/-- Every step of the printer, at any width and budget, is a step of a
reading. -/
theorem stepIsReading (printer : Printer) (total : Nat) (cmd : Cmd) (rest : List Cmd) :
    StepsTo printer cmd rest (printer.step total cmd rest) := by
  have := chooseIsOption printer total
  cases cmd with
  | FillSep indent item => grind [StepsTo, Printer.step]
  | Print indent mode doc =>
    cases doc <;> try rfl
    case Fill items => cases items <;> cases mode <;> simp [StepsTo, Printer.step, Printer.printDoc, Mode.isFlat]
    all_goals cases mode <;> grind [StepsTo, Printer.step, Printer.printDoc, Mode.isFlat]

/-- A run of the printer, at any width and budget, is a reading. -/
theorem runIsReading (printer : Printer) (total fuel : Nat) (stack : List Cmd) :
    Reads printer fuel stack (printer.run total fuel stack) := by
  fun_induction Printer.run printer total fuel stack <;> simp_all [Reads]
  case case3 printer _ cmd rest next later stepped ih => exact ⟨next, later, stepped ▸ stepIsReading .., ih⟩

/-- `print` is one of the readings: at every width, the text it gives is
what some reading of the document, from the empty printer, leaves (its
pieces joined, after the last line's trailing comment). -/
theorem printIsReading (doc : Doc) (width : Nat) :
    ∃ final : Printer, Reads (Printer.start width) (3 * doc.size + 3) [Print 0 Break doc] final
      ∧ print doc width = Text.join final.flushSuffixes.out.reverse :=
  ⟨_, runIsReading .., rfl⟩

end Toy
