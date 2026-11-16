/-
The width only chooses among readings. A reading of a document is a run
of the printer in which every question the printer asks of the width may
be answered either way; `print` at any width is one reading
(`printIsReading`). A port of `tools/toyfmt/src/Toy/Doc/Readings.sw`.

Plain version: terms, `rw`, `cases`, `induction`, `omega`, `obtain` and
anonymous constructors; no `simp`, `grind` or `aesop`.
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

theorem ifIsOption (condition : Bool) (option later : Doc) (others : List Doc)
    (laterIs : IsOption later others) :
    (if condition then option else later) = option ∨ IsOption (if condition then option else later) others := by
  cases condition
  · exact Or.inr laterIs
  · exact Or.inl rfl

/-- What a broken `Choice` takes is one of its options. -/
theorem chooseIsOption (printer : Printer) (total indent : Nat) (rest : List Cmd) :
    (options : List Doc) → IsOption (printer.choose total indent rest options) options
  | [] => rfl
  | [_] => rfl
  | option :: next :: others =>
    ifIsOption _ option _ (next :: others) (chooseIsOption printer total indent rest (next :: others))

/-- Every step of the printer, at any width and budget, is a step of a
reading. -/
theorem stepIsReading (printer : Printer) (total : Nat) (cmd : Cmd) (rest : List Cmd) :
    StepsTo printer cmd rest (printer.step total cmd rest) := by
  cases cmd with
  | FillSep indent item =>
    rw [Printer.step]
    cases empty : printer.suffixes.isEmpty
    · exact Or.inr rfl
    · cases fits total [(Flat, item)] rest (printer.left - 1)
      · exact Or.inr rfl
      · exact Or.inl ⟨empty, rfl⟩
  | Print indent mode doc =>
    cases doc with
    | Group inner hard =>
      cases mode
      · exact Or.inl ⟨Or.inl rfl, rfl⟩
      · cases hard
        · rw [Printer.step, Printer.printDoc]
          cases printer.fitsHere total [(Flat, inner)] rest
          · exact Or.inr ⟨rfl, rfl⟩
          · exact Or.inl ⟨Or.inr rfl, rfl⟩
        · exact Or.inr ⟨rfl, rfl⟩
    | Fill items =>
      cases items with
      | nil => rfl
      | cons first others =>
        cases mode
        · exact Or.inl ⟨rfl, rfl⟩
        · exact Or.inr ⟨rfl, _, rfl⟩
    | Choice options =>
      cases mode
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, _, chooseIsOption printer total indent rest options, rfl⟩
    | _ => rfl

/-- A run of the printer, at any width and budget, is a reading. -/
theorem runIsReading (total : Nat) :
    (fuel : Nat) → (printer : Printer) → (stack : List Cmd) → Reads printer fuel stack (printer.run total fuel stack)
  | 0, _, _ => rfl
  | _ + 1, _, [] => rfl
  | more + 1, printer, cmd :: rest =>
    ⟨_, _, stepIsReading printer total cmd rest, runIsReading total more _ _⟩

/-- `print` is one of the readings: at every width, the text it gives is
what some reading of the document, from the empty printer, leaves (its
pieces joined, after the last line's trailing comment). -/
theorem printIsReading (doc : Doc) (width : Nat) :
    ∃ final : Printer, Reads (Printer.start width) (3 * doc.size + 3) [Print 0 Break doc] final
      ∧ print doc width = Text.join final.flushSuffixes.out.reverse :=
  ⟨_, runIsReading _ _ _ _, rfl⟩

end Toy
