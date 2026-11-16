/-
Every reading writes the document's words, in order (`readingWords`). A
word is a piece of output that isn't layout: the text of a chunk or a
trailing comment. A port of `tools/toyfmt/src/Toy/Doc/Words.sw` and of
the part of `Proofs.sw` it rests on (the step budget).

Idiomatic version: anything in core Lean. What each printer operation
does to the words is a `@[simp]` lemma, so a step of a reading is a case
split closed by `simp` and `grind`.
-/
import Toy.Proofs.Readings

namespace Toy
open Doc Cmd Mode

/-- Whether a piece of output is only layout: spaces (a gap, indentation,
or nothing at all) or a line break. -/
def isLayout (piece : Text) : Bool := piece.all (· == ' ') || piece == Text.newline

/-- The pieces that aren't layout. -/
def wordsOf (pieces : List Text) : List Text := pieces.filter (fun piece => !isLayout piece)

/-- What the printer has written so far, as words. -/
def Printer.written (printer : Printer) : List Text := wordsOf printer.out.reverse

/-- The words printed so far, the trailing comments still waiting last. -/
def Printer.words (printer : Printer) : List Text := printer.written ++ wordsOf printer.suffixes

@[simp] theorem isLayout_space : isLayout Text.space = true := rfl

@[simp] theorem isLayout_newline : isLayout Text.newline = true := rfl

@[simp] theorem isLayout_indent (indent : Nat) : isLayout (Text.replicate indent ' ') = true := by
  simp [isLayout, Text.all, Text.replicate]

theorem isLayout_of_isEmpty {text : Text} (empty : text.isEmpty = true) : isLayout text = true := by
  simp_all [isLayout, Text.all, Text.isEmpty]

theorem isLayout_of_spaces {text : Text} (spaces : text.all (· == ' ') = true) : isLayout text = true := by
  simp [isLayout, spaces]

@[simp] theorem wordsOf_trimSpaces (out : List Text) : wordsOf (trimSpaces out) = wordsOf out := by
  fun_induction trimSpaces out <;> simp_all [wordsOf, isLayout_of_spaces]

@[simp] theorem payIndent_written (printer : Printer) : printer.payIndent.written = printer.written := by
  unfold Printer.payIndent
  split <;> simp [Printer.written, wordsOf]

@[simp] theorem payIndent_suffixes (printer : Printer) : printer.payIndent.suffixes = printer.suffixes := by
  unfold Printer.payIndent
  split <;> rfl

/-- Text put on the line is the next word written, if it is one. -/
@[simp] theorem put_written (printer : Printer) (text : Text) (width : Nat) :
    (printer.put text width).written = printer.written ++ wordsOf [text] := by
  have := payIndent_written printer
  simp_all [Printer.put, Printer.written, wordsOf]

@[simp] theorem put_suffixes (printer : Printer) (text : Text) (width : Nat) :
    (printer.put text width).suffixes = printer.suffixes := by
  simp [Printer.put]

@[simp] theorem flushOne_written (printer : Printer) (comment : Text) :
    (printer.flushOne comment).written = printer.written ++ wordsOf [comment] := by
  have := payIndent_written printer
  unfold Printer.flushOne
  split <;> simp_all [Printer.written, wordsOf]

@[simp] theorem flushOne_suffixes (printer : Printer) (comment : Text) :
    (printer.flushOne comment).suffixes = printer.suffixes := by
  unfold Printer.flushOne
  split <;> simp

/-- Comments flushed one after another are the next words written. -/
theorem flushEach (comments : List Text) (printer : Printer) :
    (comments.foldl Printer.flushOne printer).written = printer.written ++ wordsOf comments
      ∧ (comments.foldl Printer.flushOne printer).suffixes = printer.suffixes := by
  induction comments generalizing printer with
  | nil => simp [wordsOf]
  | cons comment later ih =>
    simp [ih, wordsOf, List.filter_cons]
    split <;> simp

/-- Flushing writes the waiting comments: the words stay as they were,
and none waits. -/
@[simp] theorem flushSuffixes_written (printer : Printer) : printer.flushSuffixes.written = printer.words :=
  (flushEach printer.suffixes { printer with suffixes := [] }).1

@[simp] theorem flushSuffixes_suffixes (printer : Printer) : printer.flushSuffixes.suffixes = [] :=
  (flushEach printer.suffixes { printer with suffixes := [] }).2

/-- A line break writes the waiting comments and no other word. -/
@[simp] theorem newline_written (printer : Printer) (indent : Nat) :
    (printer.newline indent).written = printer.words := by
  have := flushSuffixes_written { printer with out := trimSpaces printer.out }
  have := wordsOf_trimSpaces printer.out
  simp_all [Printer.newline, Printer.written, Printer.words, wordsOf]

@[simp] theorem newline_suffixes (printer : Printer) (indent : Nat) : (printer.newline indent).suffixes = [] := by
  simp [Printer.newline]

@[simp] theorem newline_words (printer : Printer) (indent : Nat) : (printer.newline indent).words = printer.words := by
  simp [Printer.words, wordsOf]

/-- Text written is the next word, after any comment that was waiting. -/
@[simp] theorem write_words (printer : Printer) (indent : Nat) (text : Text) (width : Nat) :
    (printer.write indent text width).words = printer.words ++ wordsOf [text] := by
  unfold Printer.write
  split
  · simp [wordsOf, isLayout_of_isEmpty, *]
  split
  · simp_all [Printer.words, wordsOf]
  split
  · simp [wordsOf, isLayout_of_spaces, *]
  · simp [Printer.words, wordsOf]

@[simp] theorem lineStart_words (printer : Printer) (indent : Nat) :
    (printer.lineStart indent).words = printer.words := by
  unfold Printer.lineStart
  split <;> simp

/-- A trailing comment set to wait is the next word. -/
@[simp] theorem suffix_words (printer : Printer) (comment : Text) :
    ({ printer with suffixes := printer.suffixes ++ [comment] }).words = printer.words ++ wordsOf [comment] := by
  simp [Printer.words, Printer.written, wordsOf]

@[simp] theorem blank_words (printer : Printer) : printer.blank.words = printer.words := by
  unfold Printer.blank
  split <;> simp [Printer.words, Printer.written, wordsOf]

-- The document's words, and the readings.

mutual
  /-- The words of a document, in order: its chunks' texts and its
  trailing comments, apart from layout. A choice's are its first
  option's; in a `Uniform` document every option has the same. -/
  def Doc.words : Doc → List Text
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

  def wordsAll : List Doc → List Text
    | [] => []
    | doc :: docs => doc.words ++ wordsAll docs

  def wordsFirst : List Doc → List Text
    | [] => []
    | doc :: _ => doc.words
end

/-- Each of the documents has these words. -/
def SameWords (words : List Text) : List Doc → Prop
  | [] => True
  | doc :: docs => doc.words = words ∧ SameWords words docs

mutual
  /-- Every option of every choice in the document has the same words. -/
  def Uniform : Doc → Prop
    | Nest _ inner => Uniform inner
    | Group inner _ => Uniform inner
    | Flatten inner => Uniform inner
    | OneLineBelow inner => Uniform inner
    | Concat docs => AllUniform docs
    | Fill items => AllUniform items
    | Choice options => AllUniform options ∧ SameWords (wordsFirst options) options
    | _ => True

  def AllUniform : List Doc → Prop
    | [] => True
    | doc :: docs => Uniform doc ∧ AllUniform docs
end

def Cmd.words : Cmd → List Text
  | Print _ _ doc => doc.words
  | FillSep _ item => item.words

/-- The words the work list has still to write. -/
def stackWords : List Cmd → List Text
  | [] => []
  | cmd :: rest => cmd.words ++ stackWords rest

def CmdUniform : Cmd → Prop
  | Print _ _ doc => Uniform doc
  | FillSep _ item => Uniform item

def StackUniform : List Cmd → Prop
  | [] => True
  | cmd :: rest => CmdUniform cmd ∧ StackUniform rest

@[simp] theorem stackWords_append (front back : List Cmd) :
    stackWords (front ++ back) = stackWords front ++ stackWords back := by
  induction front <;> simp_all [stackWords]

@[simp] theorem stackUniform_append (front back : List Cmd) :
    StackUniform (front ++ back) ↔ StackUniform front ∧ StackUniform back := by
  induction front <;> simp_all [StackUniform, and_assoc]

@[simp] theorem stackWords_prints (indent : Nat) (mode : Mode) (docs : List Doc) :
    stackWords (docs.map (Print indent mode)) = wordsAll docs := by
  induction docs <;> simp_all [stackWords, wordsAll, Cmd.words]

@[simp] theorem stackUniform_prints (indent : Nat) (mode : Mode) (docs : List Doc) :
    StackUniform (docs.map (Print indent mode)) ↔ AllUniform docs := by
  induction docs <;> simp_all [StackUniform, AllUniform, CmdUniform]

@[simp] theorem stackWords_fillSeps (indent : Nat) (items : List Doc) :
    stackWords (items.map (FillSep indent)) = wordsAll items := by
  induction items <;> simp_all [stackWords, wordsAll, Cmd.words]

@[simp] theorem stackUniform_fillSeps (indent : Nat) (items : List Doc) :
    StackUniform (items.map (FillSep indent)) ↔ AllUniform items := by
  induction items <;> simp_all [StackUniform, AllUniform, CmdUniform]

/-- The lines a flat fill puts between its items are no words. -/
@[simp] theorem wordsAll_joinLines (items : List Doc) : wordsAll (Doc.joinLines items) = wordsAll items := by
  fun_induction Doc.joinLines items <;> simp_all [wordsAll, Doc.words]

theorem allUniform_joinLines (items : List Doc) (uniform : AllUniform items) : AllUniform (Doc.joinLines items) := by
  fun_induction Doc.joinLines items <;> simp_all [AllUniform, Uniform]

/-- What a choice may print has the words all its options have. -/
theorem optionWords (chosen : Doc) (words : List Text) (options : List Doc)
    (isOption : IsOption chosen options) (same : SameWords words options) (some : options ≠ []) :
    chosen.words = words := by
  fun_induction IsOption chosen options <;> grind [SameWords]

theorem chosenWords (chosen : Doc) (options : List Doc)
    (isOption : IsOption chosen options) (same : SameWords (wordsFirst options) options) :
    chosen.words = wordsFirst options := by
  cases options with
  | nil => simp_all [IsOption, Doc.words, wordsFirst]
  | cons option others => exact optionWords _ _ _ isOption same (by simp)

theorem optionUniform (chosen : Doc) (options : List Doc)
    (isOption : IsOption chosen options) (uniform : AllUniform options) :
    Uniform chosen := by
  fun_induction IsOption chosen options <;> grind [AllUniform, Uniform]

/-- A step of a reading moves words from the work list to the printer,
in order: the words printed and those still to print, together, stay
the same. -/
theorem stepWords (printer : Printer) (cmd : Cmd) (rest : List Cmd) (result : Printer × List Cmd)
    (steps : StepsTo printer cmd rest result) (uniform : CmdUniform cmd) :
    result.1.words ++ stackWords result.2 = printer.words ++ (cmd.words ++ stackWords rest) := by
  have := chosenWords
  cases cmd with
  | FillSep indent item => rcases steps with ⟨_, rfl⟩ | rfl <;> simp [Cmd.words, stackWords, wordsOf]
  | Print indent mode doc =>
    cases doc
    case Fill items => cases items <;> grind [StepsTo, Cmd.words, stackWords, Doc.words, wordsAll,
      stackWords_append, stackWords_prints, stackWords_fillSeps, wordsAll_joinLines]
    case Choice options =>
      cases options <;> grind [StepsTo, Cmd.words, stackWords, Doc.words, wordsFirst, CmdUniform, Uniform]
    case LineStartHere =>
      obtain rfl : result = _ := steps
      rw [Printer.printDoc]
      split <;> first | rfl | simp [Cmd.words, Doc.words]
    all_goals
      simp_all [StepsTo, Printer.printDoc, Cmd.words, stackWords, Doc.words]
      first | done | (split <;> simp [wordsOf]) | grind [stackWords, Cmd.words]

/-- A step of a reading leaves the work list uniform. -/
theorem stepUniform (printer : Printer) (cmd : Cmd) (rest : List Cmd) (result : Printer × List Cmd)
    (steps : StepsTo printer cmd rest result) (uniform : CmdUniform cmd) (restUniform : StackUniform rest) :
    StackUniform result.2 := by
  have := optionUniform
  have := allUniform_joinLines
  cases cmd with
  | FillSep indent item => rcases steps with ⟨_, rfl⟩ | rfl <;> simp_all [StackUniform, CmdUniform]
  | Print indent mode doc =>
    cases doc
    case Fill items => cases items <;> grind [StepsTo, StackUniform, CmdUniform, Uniform, AllUniform,
      stackUniform_append, stackUniform_prints, stackUniform_fillSeps]
    case Choice options => cases options <;> grind [StepsTo, StackUniform, CmdUniform, Uniform, AllUniform]
    all_goals
      simp_all [StepsTo, Printer.printDoc, StackUniform, CmdUniform, Uniform]
      first | done | (split <;> simp_all) | grind [StackUniform, CmdUniform]

-- The step budget: every step of a reading weighs the work list down.

mutual
  /-- The steps the printer can still take on `doc`, at most: a step on
  a node replaces it by its parts, which weigh less. -/
  def Doc.steps : Doc → Nat
    | Nest _ inner => 1 + inner.steps
    | Group inner _ => 1 + inner.steps
    | Flatten inner => 1 + inner.steps
    | OneLineBelow inner => 2 + inner.steps
    | Concat docs => 1 + stepsOf docs
    | Fill items => 1 + stepsOf items + items.length
    | Choice options => 2 + stepsOf options
    | _ => 1

  def stepsOf : List Doc → Nat
    | [] => 0
    | doc :: docs => doc.steps + stepsOf docs
end

def Cmd.cost : Cmd → Nat
  | Print _ _ doc => doc.steps
  | FillSep _ item => item.steps + 1

def stackCost : List Cmd → Nat
  | [] => 0
  | cmd :: rest => cmd.cost + stackCost rest

theorem stepsPositive (doc : Doc) : 1 ≤ doc.steps := by
  cases doc <;> simp [Doc.steps] <;> omega

theorem costPositive (cmd : Cmd) : 1 ≤ cmd.cost := by
  cases cmd <;> simp [Cmd.cost, stepsPositive]

@[simp] theorem stackCost_append (front back : List Cmd) :
    stackCost (front ++ back) = stackCost front + stackCost back := by
  induction front <;> simp_all [stackCost, Nat.add_assoc]

@[simp] theorem stackCost_prints (indent : Nat) (mode : Mode) (docs : List Doc) :
    stackCost (docs.map (Print indent mode)) = stepsOf docs := by
  induction docs <;> simp_all [stackCost, stepsOf, Cmd.cost]

@[simp] theorem stackCost_fillSeps (indent : Nat) (items : List Doc) :
    stackCost (items.map (FillSep indent)) = stepsOf items + items.length := by
  induction items <;> simp_all [stackCost, stepsOf, Cmd.cost] <;> omega

theorem joinLinesSteps (items : List Doc) : stepsOf (Doc.joinLines items) ≤ stepsOf items + items.length := by
  fun_induction Doc.joinLines items <;> simp_all [stepsOf, Doc.steps] <;> omega

theorem optionSteps (chosen : Doc) (options : List Doc) (isOption : IsOption chosen options) :
    chosen.steps ≤ stepsOf options + 1 := by
  fun_induction IsOption chosen options <;> grind [stepsOf, Doc.steps]

/-- Every step of a reading weighs the work list down: a reading ends
within the printer's budget. -/
theorem readingLighter (printer : Printer) (cmd : Cmd) (rest : List Cmd) (result : Printer × List Cmd)
    (steps : StepsTo printer cmd rest result) :
    stackCost result.2 < cmd.cost + stackCost rest := by
  cases cmd with
  | FillSep indent item => rcases steps with ⟨_, rfl⟩ | rfl <;> simp [stackCost, Cmd.cost] <;> omega
  | Print indent mode doc =>
    cases doc
    case Fill items =>
      have := joinLinesSteps items
      cases items <;> grind [StepsTo, stackCost, Cmd.cost, Doc.steps, stepsOf,
        stackCost_append, stackCost_prints, stackCost_fillSeps]
    case Choice options =>
      have := optionSteps (options := options)
      cases options <;> grind [StepsTo, stackCost, Cmd.cost, Doc.steps, stepsOf]
    all_goals
      simp_all [StepsTo, Printer.printDoc, stackCost, Cmd.cost, Doc.steps]
      first | done | (split <;> simp_all) | grind [stackCost, Cmd.cost]

/-- A reading that has the steps to finish its work list writes the work
list's words after the printer's, in order, whichever way its groups,
fills and choices go. -/
theorem readingWords (printer : Printer) (fuel : Nat) (stack : List Cmd) (final : Printer)
    (reads : Reads printer fuel stack final)
    (uniform : StackUniform stack)
    (enough : stackCost stack ≤ fuel) :
    final.words = printer.words ++ stackWords stack := by
  fun_induction Reads printer fuel stack final
  case case1 stack =>
    have := costPositive
    cases stack <;> grind [stackCost, stackWords]
  case case2 => simp_all [stackWords]
  case case3 printer more cmd rest ih =>
    obtain ⟨next, later, steps, laterReads⟩ := reads
    have := stepWords printer cmd rest _ steps uniform.1
    have := readingLighter printer cmd rest _ steps
    have := stepUniform printer cmd rest _ steps uniform.1 uniform.2
    grind [stackCost, stackWords]

end Toy
