/-
Every reading writes the document's words, in order (`readingWords`). A
word is a piece of output that isn't layout: the text of a chunk or a
trailing comment. A port of `tools/toyfmt/src/Toy/Doc/Words.sw` and of
the part of `Proofs.sw` it rests on (the step budget).

Plain version: terms, `rw`, `cases`, `induction`, `omega`, `obtain` and
anonymous constructors, with `show`, `unfold` and `split` to steer; no
`simp`, `grind` or `aesop`.
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

theorem emptyIsLayout (text : Text) (empty : text.isEmpty = true) : isLayout text = true := by
  obtain ⟨chars⟩ := text
  cases chars with
  | nil => rfl
  | cons first others => exact absurd empty Bool.false_ne_true

theorem spacesIsLayout (text : Text) (spaces : text.all (· == ' ') = true) : isLayout text = true := by
  rw [isLayout, spaces]
  rfl

theorem indentSpaces : (indent : Nat) → (Text.replicate indent ' ').all (· == ' ') = true
  | 0 => rfl
  | less + 1 => indentSpaces less

theorem wordsAppend (front back : List Text) : wordsOf (front ++ back) = wordsOf front ++ wordsOf back :=
  List.filter_append ..

theorem wordsSnoc (piece : Text) (out : List Text) :
    wordsOf (piece :: out).reverse = wordsOf out.reverse ++ wordsOf [piece] := by
  rw [List.reverse_cons, wordsAppend]

theorem layoutNoWord (piece : Text) (layout : isLayout piece = true) : wordsOf [piece] = [] := by
  rw [wordsOf, List.filter_cons, layout]
  rfl

/-- A piece of layout adds no word. -/
theorem layoutSnoc (piece : Text) (out : List Text) (layout : isLayout piece = true) :
    wordsOf (piece :: out).reverse = wordsOf out.reverse := by
  rw [wordsSnoc, layoutNoWord piece layout, List.append_nil]

theorem trimWords (out : List Text) : wordsOf (trimSpaces out).reverse = wordsOf out.reverse := by
  induction out with
  | nil => rfl
  | cons last earlier ih =>
    rw [trimSpaces]
    cases spaces : last.all (· == ' ')
    · rfl
    · rw [layoutSnoc last earlier (spacesIsLayout last spaces)]
      exact ih

theorem payIndentWritten (printer : Printer) :
    printer.payIndent.written = printer.written ∧ printer.payIndent.suffixes = printer.suffixes := by
  obtain ⟨_, out, _, owed, _, _, _, _, _⟩ := printer
  cases owed with
  | none => exact ⟨rfl, rfl⟩
  | some indent =>
    cases indent with
    | zero => exact ⟨rfl, rfl⟩
    | succ less => exact ⟨layoutSnoc _ out (spacesIsLayout _ (indentSpaces (less + 1))), rfl⟩

/-- Text put on the line is the next word written, if it is one. -/
theorem putWritten (printer : Printer) (text : Text) (width : Nat) :
    (printer.put text width).written = printer.written ++ wordsOf [text]
      ∧ (printer.put text width).suffixes = printer.suffixes := by
  obtain ⟨written, suffixes⟩ := payIndentWritten printer
  rw [← written]
  exact ⟨wordsSnoc text printer.payIndent.out, suffixes⟩

theorem flushOneWritten (printer : Printer) (comment : Text) :
    (printer.flushOne comment).written = printer.written ++ wordsOf [comment]
      ∧ (printer.flushOne comment).suffixes = printer.suffixes := by
  obtain ⟨written, suffixes⟩ := payIndentWritten printer
  unfold Printer.flushOne
  cases printer.atLineStart
  · exact ⟨(wordsSnoc comment (Text.space :: printer.out)).trans
      (congrArg (· ++ wordsOf [comment]) (layoutSnoc Text.space printer.out rfl)), rfl⟩
  · rw [← written]
    exact ⟨wordsSnoc comment printer.payIndent.out, suffixes⟩

/-- Comments flushed one after another are the next words written. -/
theorem flushEachWritten : (comments : List Text) → (printer : Printer) →
    (comments.foldl Printer.flushOne printer).written = printer.written ++ wordsOf comments
      ∧ (comments.foldl Printer.flushOne printer).suffixes = printer.suffixes
  | [], printer => ⟨(List.append_nil _).symm, rfl⟩
  | comment :: later, printer => by
    obtain ⟨written, suffixes⟩ := flushOneWritten printer comment
    obtain ⟨laterWritten, laterSuffixes⟩ := flushEachWritten later (printer.flushOne comment)
    rw [List.foldl_cons, laterWritten, written, List.append_assoc, ← wordsAppend]
    exact ⟨rfl, laterSuffixes.trans suffixes⟩

/-- Flushing writes the waiting comments: the words stay as they were,
and none waits. -/
theorem flushWritten (printer : Printer) :
    printer.flushSuffixes.written = printer.words ∧ printer.flushSuffixes.suffixes = [] :=
  flushEachWritten printer.suffixes { printer with suffixes := [] }

/-- A line break writes the waiting comments and no other word. -/
theorem newlineWritten (printer : Printer) (indent : Nat) :
    (printer.newline indent).written = printer.words ∧ (printer.newline indent).suffixes = [] := by
  obtain ⟨written, suffixes⟩ := flushWritten { printer with out := trimSpaces printer.out }
  exact ⟨(layoutSnoc Text.newline _ rfl).trans
    (written.trans (congrArg (· ++ wordsOf printer.suffixes) (trimWords printer.out))), suffixes⟩

theorem newlineWords (printer : Printer) (indent : Nat) : (printer.newline indent).words = printer.words := by
  obtain ⟨written, suffixes⟩ := newlineWritten printer indent
  rw [Printer.words, written, suffixes]
  exact List.append_nil _

/-- With no comment waiting, text put on the line is the next word. -/
theorem putClearWords (printer : Printer) (text : Text) (width : Nat) (clear : printer.suffixes = []) :
    (printer.put text width).words = printer.written ++ wordsOf [text] := by
  obtain ⟨written, suffixes⟩ := putWritten printer text width
  rw [Printer.words, written, suffixes, clear]
  exact List.append_nil _

/-- Text written is the next word, after any comment that was waiting. -/
theorem writeWords (printer : Printer) (indent : Nat) (text : Text) (width : Nat) :
    (printer.write indent text width).words = printer.words ++ wordsOf [text] := by
  unfold Printer.write
  cases empty : text.isEmpty
  · cases waiting : printer.suffixes.isEmpty
    · cases spaces : text.all (· == ' ')
      · obtain ⟨brokenWritten, brokenSuffixes⟩ := newlineWritten printer (printer.continuation indent)
        rw [← brokenWritten]
        exact putClearWords _ text width brokenSuffixes
      · rw [layoutNoWord text (spacesIsLayout text spaces)]
        exact (List.append_nil _).symm
    · have clear := List.isEmpty_iff.mp waiting
      refine (putClearWords printer text width clear).trans ?_
      rw [Printer.words, clear]
      exact congrArg (· ++ wordsOf [text]) (List.append_nil _).symm
  · rw [layoutNoWord text (emptyIsLayout text empty)]
    exact (List.append_nil _).symm

theorem lineStartWords (printer : Printer) (indent : Nat) : (printer.lineStart indent).words = printer.words := by
  unfold Printer.lineStart
  cases printer.atLineStart
  · exact newlineWords printer _
  · rfl

theorem blankWords (printer : Printer) : printer.blank.words = printer.words := by
  unfold Printer.blank
  split
  · exact congrArg (· ++ wordsOf printer.suffixes) (layoutSnoc Text.newline printer.out rfl)
  · rfl

theorem writeLayoutWords (printer : Printer) (indent : Nat) (text : Text) (width : Nat)
    (layout : isLayout text = true) :
    (printer.write indent text width).words = printer.words := by
  rw [writeWords, layoutNoWord text layout, List.append_nil]

/-- A trailing comment set to wait is the next word. -/
theorem suffixWords (printer : Printer) (comment : Text) :
    ({ printer with suffixes := printer.suffixes ++ [comment] }).words = printer.words ++ wordsOf [comment] :=
  (congrArg (printer.written ++ ·) (wordsAppend printer.suffixes [comment])).trans (List.append_assoc ..).symm

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

theorem stackWordsAppend : (front back : List Cmd) →
    stackWords (front ++ back) = stackWords front ++ stackWords back
  | [], _ => rfl
  | cmd :: rest, back =>
    (congrArg (cmd.words ++ ·) (stackWordsAppend rest back)).trans (List.append_assoc ..).symm

theorem stackUniformAppend (front back : List Cmd)
    (frontUniform : StackUniform front) (backUniform : StackUniform back) :
    StackUniform (front ++ back) := by
  induction front with
  | nil => exact backUniform
  | cons cmd rest ih =>
    obtain ⟨first, others⟩ := frontUniform
    exact ⟨first, ih others⟩

theorem printsWords (indent : Nat) (mode : Mode) : (docs : List Doc) →
    stackWords (docs.map (Print indent mode)) = wordsAll docs
  | [] => rfl
  | doc :: rest => congrArg (doc.words ++ ·) (printsWords indent mode rest)

theorem printsUniform (indent : Nat) (mode : Mode) (docs : List Doc) (uniform : AllUniform docs) :
    StackUniform (docs.map (Print indent mode)) := by
  induction docs with
  | nil => exact True.intro
  | cons doc rest ih =>
    obtain ⟨first, others⟩ := uniform
    exact ⟨first, ih others⟩

theorem fillSepsWords (indent : Nat) : (items : List Doc) →
    stackWords (items.map (FillSep indent)) = wordsAll items
  | [] => rfl
  | item :: rest => congrArg (item.words ++ ·) (fillSepsWords indent rest)

theorem fillSepsUniform (indent : Nat) (items : List Doc) (uniform : AllUniform items) :
    StackUniform (items.map (FillSep indent)) := by
  induction items with
  | nil => exact True.intro
  | cons item rest ih =>
    obtain ⟨first, others⟩ := uniform
    exact ⟨first, ih others⟩

/-- The lines a flat fill puts between its items are no words. -/
theorem joinLinesWords : (items : List Doc) → wordsAll (Doc.joinLines items) = wordsAll items
  | [] => rfl
  | [_] => rfl
  | item :: next :: rest => congrArg (item.words ++ ·) (joinLinesWords (next :: rest))

theorem joinLinesUniform : (items : List Doc) → AllUniform items → AllUniform (Doc.joinLines items)
  | [], _ => True.intro
  | [_], given => given
  | _ :: next :: rest, ⟨first, others⟩ => ⟨first, True.intro, joinLinesUniform (next :: rest) others⟩

/-- What a choice may print has the words all its options have. -/
theorem optionWords (chosen : Doc) (words : List Text) (option : Doc) (others : List Doc)
    (isOption : IsOption chosen (option :: others)) (same : SameWords words (option :: others)) :
    chosen.words = words := by
  induction others generalizing option with
  | nil =>
    cases isOption
    exact same.1
  | cons next rest ih =>
    obtain ⟨first, laterSame⟩ := same
    obtain picked | later := isOption
    · rw [picked]
      exact first
    · exact ih next later laterSame

theorem optionUniform (chosen : Doc) (options : List Doc)
    (isOption : IsOption chosen options) (uniform : AllUniform options) :
    Uniform chosen := by
  induction options with
  | nil =>
    cases isOption
    exact True.intro
  | cons option others ih =>
    obtain ⟨first, rest⟩ := uniform
    cases others with
    | nil =>
      cases isOption
      exact first
    | cons next more =>
      obtain picked | later := isOption
      · rw [picked]
        exact first
      · exact ih later rest

theorem headOrWords (options : List Doc) : (options.headD Doc.Empty).words = wordsFirst options := by
  cases options <;> rfl

theorem headOrUniform (options : List Doc) (uniform : AllUniform options) : Uniform (options.headD Doc.Empty) := by
  cases options with
  | nil => exact True.intro
  | cons option others => exact uniform.1

theorem chosenWords (chosen : Doc) (options : List Doc)
    (isOption : IsOption chosen options) (same : SameWords (wordsFirst options) options) :
    chosen.words = wordsFirst options := by
  cases options with
  | nil =>
    cases isOption
    rfl
  | cons option others => exact optionWords chosen _ option others isOption same

theorem keepsWords {next printer : Printer} (tail : List Text) (same : next.words = printer.words) :
    next.words ++ tail = printer.words ++ tail :=
  congrArg (· ++ tail) same

theorem addsWords {next printer : Printer} {added : List Text} (tail : List Text)
    (more : next.words = printer.words ++ added) :
    next.words ++ tail = printer.words ++ (added ++ tail) := by
  rw [more, List.append_assoc]

/-- A step of a reading moves words from the work list to the printer,
in order: the words printed and those still to print, together, stay
the same. -/
theorem stepWords (printer : Printer) (cmd : Cmd) (rest : List Cmd) (result : Printer × List Cmd)
    (steps : StepsTo printer cmd rest result) (uniform : CmdUniform cmd) :
    result.1.words ++ stackWords result.2 = printer.words ++ (cmd.words ++ stackWords rest) := by
  cases cmd with
  | FillSep indent item =>
    obtain ⟨_, flat⟩ | broken := steps
    · rw [flat]
      exact keepsWords _ (writeLayoutWords printer indent Text.space 1 rfl)
    · rw [broken]
      exact keepsWords _ (newlineWords printer indent)
  | Print indent mode doc =>
    cases doc with
    | Chunk text width =>
      cases steps
      exact addsWords _ (writeWords printer indent text width)
    | LineSuffix comment =>
      cases steps
      exact addsWords _ (suffixWords printer comment)
    | Line =>
      cases steps
      rw [Printer.printDoc]
      split
      · exact keepsWords _ (writeLayoutWords printer indent Text.space 1 rfl)
      · exact keepsWords _ (newlineWords printer indent)
    | SoftLine =>
      cases steps
      rw [Printer.printDoc]
      split
      · rfl
      · exact keepsWords _ (newlineWords printer indent)
    | LineStartHere =>
      cases steps
      rw [Printer.printDoc]
      split
      · rfl
      · exact keepsWords _ (newlineWords printer indent)
    | HardLine =>
      cases steps
      exact keepsWords _ (newlineWords printer indent)
    | CommentEnd =>
      cases steps
      exact keepsWords _ (newlineWords printer printer.lineIndent)
    | LineStart =>
      cases steps
      exact keepsWords _ (lineStartWords printer indent)
    | Blank =>
      cases steps
      exact keepsWords _ (blankWords printer)
    | Group inner hard =>
      obtain ⟨_, flat⟩ | ⟨_, broken⟩ := steps
      · rw [flat]
        rfl
      · rw [broken]
        rfl
    | Concat docs =>
      cases steps
      exact congrArg (printer.words ++ ·)
        ((stackWordsAppend _ rest).trans (congrArg (· ++ stackWords rest) (printsWords indent mode docs)))
    | Fill items =>
      cases items with
      | nil =>
        cases steps
        rfl
      | cons first others =>
        obtain ⟨_, flat⟩ | ⟨_, firstMode, broken⟩ := steps
        · rw [flat]
          refine congrArg (printer.words ++ ·) ((stackWordsAppend _ rest).trans ?_)
          rw [printsWords, joinLinesWords]
          rfl
        · rw [broken]
          refine congrArg (printer.words ++ ·) ?_
          refine (congrArg (first.words ++ ·) (stackWordsAppend _ rest)).trans ?_
          rw [fillSepsWords, ← List.append_assoc]
          rfl
    | Choice options =>
      obtain ⟨_, same⟩ := uniform
      obtain ⟨_, flat⟩ | ⟨_, chosen, isOption, broken⟩ := steps
      · rw [flat]
        exact congrArg (fun words => printer.words ++ (words ++ stackWords rest)) (headOrWords options)
      · rw [broken]
        exact congrArg (fun words => printer.words ++ (words ++ stackWords rest))
          (chosenWords chosen options isOption same)
    | _ =>
      cases steps
      rfl

/-- A step of a reading leaves the work list uniform. -/
theorem stepUniform (printer : Printer) (cmd : Cmd) (rest : List Cmd) (result : Printer × List Cmd)
    (steps : StepsTo printer cmd rest result) (uniform : CmdUniform cmd) (restUniform : StackUniform rest) :
    StackUniform result.2 := by
  cases cmd with
  | FillSep indent item =>
    obtain ⟨_, flat⟩ | broken := steps
    · rw [flat]
      exact ⟨uniform, restUniform⟩
    · rw [broken]
      exact ⟨uniform, restUniform⟩
  | Print indent mode doc =>
    cases doc with
    | Nest more inner =>
      cases steps
      exact ⟨uniform, restUniform⟩
    | Flatten inner =>
      cases steps
      exact ⟨uniform, restUniform⟩
    | OneLineBelow inner =>
      cases steps
      exact ⟨True.intro, uniform, restUniform⟩
    | Group inner hard =>
      obtain ⟨_, flat⟩ | ⟨_, broken⟩ := steps
      · rw [flat]
        exact ⟨uniform, restUniform⟩
      · rw [broken]
        exact ⟨uniform, restUniform⟩
    | Concat docs =>
      cases steps
      exact stackUniformAppend _ rest (printsUniform indent mode docs uniform) restUniform
    | Fill items =>
      cases items with
      | nil =>
        cases steps
        exact restUniform
      | cons first others =>
        obtain ⟨_, flat⟩ | ⟨_, firstMode, broken⟩ := steps
        · rw [flat]
          exact stackUniformAppend _ rest
            (printsUniform indent Flat _ (joinLinesUniform (first :: others) uniform)) restUniform
        · rw [broken]
          obtain ⟨firstUniform, othersUniform⟩ := uniform
          exact ⟨firstUniform, stackUniformAppend _ rest (fillSepsUniform indent others othersUniform) restUniform⟩
    | Choice options =>
      obtain ⟨each, _⟩ := uniform
      obtain ⟨_, flat⟩ | ⟨_, chosen, isOption, broken⟩ := steps
      · rw [flat]
        exact ⟨headOrUniform options each, restUniform⟩
      · rw [broken]
        exact ⟨optionUniform chosen options isOption each, restUniform⟩
    | Line =>
      cases steps
      rw [Printer.printDoc]
      split <;> exact restUniform
    | SoftLine =>
      cases steps
      rw [Printer.printDoc]
      split <;> exact restUniform
    | LineStartHere =>
      cases steps
      rw [Printer.printDoc]
      split <;> exact restUniform
    | _ =>
      cases steps
      exact restUniform

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
  cases doc
  case OneLineBelow inner => exact Nat.le_trans (Nat.le_add_right 1 1) (Nat.le_add_right 2 inner.steps)
  case Choice options => exact Nat.le_trans (Nat.le_add_right 1 1) (Nat.le_add_right 2 (stepsOf options))
  case Fill items => exact Nat.le_trans (Nat.le_add_right 1 (stepsOf items)) (Nat.le_add_right _ items.length)
  all_goals first | exact Nat.le_refl 1 | exact Nat.le_add_right 1 _

theorem costPositive (cmd : Cmd) : 1 ≤ cmd.cost := by
  cases cmd with
  | Print indent mode doc => exact stepsPositive doc
  | FillSep indent item => exact Nat.le_add_left 1 item.steps

theorem stackCostAppend : (front back : List Cmd) → stackCost (front ++ back) = stackCost front + stackCost back
  | [], _ => (Nat.zero_add _).symm
  | cmd :: rest, back =>
    (congrArg (cmd.cost + ·) (stackCostAppend rest back)).trans (Nat.add_assoc ..).symm

theorem costPrints (indent : Nat) (mode : Mode) : (docs : List Doc) →
    stackCost (docs.map (Print indent mode)) = stepsOf docs
  | [] => rfl
  | doc :: rest => congrArg (doc.steps + ·) (costPrints indent mode rest)

theorem costFillSeps (indent : Nat) : (items : List Doc) →
    stackCost (items.map (FillSep indent)) = stepsOf items + items.length
  | [] => rfl
  | item :: rest => by
    have tail := costFillSeps indent rest
    show item.steps + 1 + stackCost (rest.map (FillSep indent)) = item.steps + stepsOf rest + (rest.length + 1)
    omega

theorem joinLinesSteps : (items : List Doc) → stepsOf (Doc.joinLines items) ≤ stepsOf items + items.length
  | [] => Nat.le_refl 0
  | [only] => Nat.le_add_right (only.steps + 0) 1
  | item :: next :: rest => by
    have tail := joinLinesSteps (next :: rest)
    show item.steps + (1 + stepsOf (Doc.joinLines (next :: rest)))
      ≤ item.steps + stepsOf (next :: rest) + ((next :: rest).length + 1)
    omega

theorem headOrSteps (options : List Doc) : (options.headD Doc.Empty).steps ≤ stepsOf options + 1 := by
  cases options with
  | nil => exact Nat.le_refl 1
  | cons option rest =>
    show option.steps ≤ option.steps + stepsOf rest + 1
    omega

theorem optionSteps (chosen : Doc) (options : List Doc) (isOption : IsOption chosen options) :
    chosen.steps ≤ stepsOf options + 1 := by
  induction options with
  | nil =>
    cases isOption
    exact Nat.le_refl 1
  | cons option others ih =>
    cases others with
    | nil =>
      cases isOption
      exact Nat.le_add_right _ 1
    | cons next more =>
      obtain picked | later := isOption
      · rw [picked]
        exact Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ 1)
      · have bound := ih later
        show chosen.steps ≤ option.steps + stepsOf (next :: more) + 1
        omega

/-- Every step of a reading weighs the work list down: a reading ends
within the printer's budget. -/
theorem readingLighter (printer : Printer) (cmd : Cmd) (rest : List Cmd) (result : Printer × List Cmd)
    (steps : StepsTo printer cmd rest result) :
    stackCost result.2 < cmd.cost + stackCost rest := by
  cases cmd with
  | FillSep indent item =>
    obtain ⟨_, flat⟩ | broken := steps
    · rw [flat]
      show item.steps + stackCost rest < item.steps + 1 + stackCost rest
      omega
    · rw [broken]
      show item.steps + stackCost rest < item.steps + 1 + stackCost rest
      omega
  | Print indent mode doc =>
    cases doc with
    | Nest more inner =>
      cases steps
      exact Nat.add_lt_add_right (Nat.lt_add_of_pos_left Nat.one_pos) _
    | Flatten inner =>
      cases steps
      exact Nat.add_lt_add_right (Nat.lt_add_of_pos_left Nat.one_pos) _
    | OneLineBelow inner =>
      cases steps
      show 1 + (inner.steps + stackCost rest) < 2 + inner.steps + stackCost rest
      omega
    | Group inner hard =>
      obtain ⟨_, flat⟩ | ⟨_, broken⟩ := steps
      · rw [flat]
        exact Nat.add_lt_add_right (Nat.lt_add_of_pos_left Nat.one_pos) _
      · rw [broken]
        exact Nat.add_lt_add_right (Nat.lt_add_of_pos_left Nat.one_pos) _
    | Concat docs =>
      cases steps
      show stackCost (docs.map (Print indent mode) ++ rest) < 1 + stepsOf docs + stackCost rest
      rw [stackCostAppend, costPrints]
      omega
    | Fill items =>
      cases items with
      | nil =>
        cases steps
        exact Nat.lt_add_of_pos_left Nat.one_pos
      | cons first others =>
        have bound := joinLinesSteps (first :: others)
        obtain ⟨_, flat⟩ | ⟨_, firstMode, broken⟩ := steps
        · rw [flat]
          show stackCost ((Doc.joinLines (first :: others)).map (Print indent Flat) ++ rest)
            < 1 + stepsOf (first :: others) + (first :: others).length + stackCost rest
          rw [stackCostAppend, costPrints]
          omega
        · rw [broken]
          show first.steps + stackCost (others.map (FillSep indent) ++ rest)
            < 1 + (first.steps + stepsOf others) + (others.length + 1) + stackCost rest
          rw [stackCostAppend, costFillSeps]
          omega
    | Choice options =>
      obtain ⟨_, flat⟩ | ⟨_, chosen, isOption, broken⟩ := steps
      · have bound := headOrSteps options
        rw [flat]
        show (options.headD Doc.Empty).steps + stackCost rest < 2 + stepsOf options + stackCost rest
        omega
      · have bound := optionSteps chosen options isOption
        rw [broken]
        show chosen.steps + stackCost rest < 2 + stepsOf options + stackCost rest
        omega
    | Line =>
      cases steps
      rw [Printer.printDoc]
      split <;> exact Nat.lt_add_of_pos_left Nat.one_pos
    | SoftLine =>
      cases steps
      rw [Printer.printDoc]
      split <;> exact Nat.lt_add_of_pos_left Nat.one_pos
    | LineStartHere =>
      cases steps
      rw [Printer.printDoc]
      split <;> exact Nat.lt_add_of_pos_left Nat.one_pos
    | _ =>
      cases steps
      exact Nat.lt_add_of_pos_left Nat.one_pos

/-- A reading that has the steps to finish its work list writes the work
list's words after the printer's, in order, whichever way its groups,
fills and choices go. -/
theorem readingWords (printer : Printer) (fuel : Nat) (stack : List Cmd) (final : Printer)
    (reads : Reads printer fuel stack final)
    (uniform : StackUniform stack)
    (enough : stackCost stack ≤ fuel) :
    final.words = printer.words ++ stackWords stack := by
  induction fuel generalizing printer stack with
  | zero =>
    cases stack with
    | nil =>
      cases reads
      exact (List.append_nil _).symm
    | cons cmd rest =>
      have positive := costPositive cmd
      have short : cmd.cost + stackCost rest ≤ 0 := enough
      omega
  | succ more ih =>
    cases stack with
    | nil =>
      cases reads
      exact (List.append_nil _).symm
    | cons cmd rest =>
      obtain ⟨next, later, steps, laterReads⟩ := reads
      obtain ⟨first, others⟩ := uniform
      have moved := stepWords printer cmd rest (next, later) steps first
      have lighter : stackCost later < cmd.cost + stackCost rest := readingLighter printer cmd rest (next, later) steps
      have kept := stepUniform printer cmd rest (next, later) steps first others
      have short : cmd.cost + stackCost rest ≤ more + 1 := enough
      exact (ih next later laterReads kept (by omega)).trans moved

end Toy
