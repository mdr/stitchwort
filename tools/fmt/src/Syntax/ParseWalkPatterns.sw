--| The pattern parser read for nothing but that it is read: the parsers outside slice 1 that read patterns only need
--| the items they read to stay good, and that they return. Records, constructors, lists and tuples, brackets and
--| the plain pattern.

namespace Syntax.ParseWalkPatterns
import Std (Bool, DecEq, Eq, List, Nat, Option, Pair, Parse, Result, Text)
import Syntax (..)
import Fmt (..)
import Syntax.LexProofs (..)
import Syntax.ParseProofs (..)
import Syntax.ParseWalk (..)
import Syntax.ParseWalkOutside (..)
import Fmt.Grammar1 (..)
import Fmt.Kinds (..)

-- The pattern parser, read for nothing but that it is read: the parsers outside slice 1 that read patterns only need
-- the items they read to stay good, and that they return.

--| `pself` gives a pattern, at every goal.
def PatternNested (pself: PatternGoal → {Parse Item} Pattern): Prop :=
  ∀ (goal: PatternGoal) => Parse.Gives GoodItems (() => pself goal) (pat => True)

theorem reads0WordAhead ∀ (modes: Modes) (word: Text): Reads0 (() => wordAhead modes word) :=
  Parse.reads0Then reads0Left (items => Parse.reads0Done (wordOn modes word items))

theorem reads0CtorAhead ∀ (modes: Modes): Reads0 (() => ctorAhead modes) :=
  Parse.reads0Then (reads0At modes Upper) (upper =>
    Parse.reads0Then (reads0WordAhead modes "Quot.mk") (quot => Parse.reads0Done _))

theorem givesEat ∀ (modes: Modes) (wanted: Tok): Parse.Gives GoodItems (() => modes.eat wanted) (found => True) :=
  Parse.givesAfter0 (reads0At modes wanted) (at =>
    match at with
      | True => Parse.givesThen givesBump (taken _ => Parse.givesDone byComputing)
      | False => Parse.givesDone byComputing)

theorem givesNegativeDigits ∀ (modes: Modes) (minus: Word) (number: Bool):
    Parse.Gives GoodItems (() => negativeDigits modes minus number) (pat => True) :=
  match number with
    | True => Parse.givesThen givesBump (digits _ => Parse.givesDone byComputing)
    | False => givesFail modes "a number"

theorem givesNegativePattern ∀ (modes: Modes): Parse.Gives GoodItems (() => negativePattern modes) (pat => True) :=
  Parse.givesThen givesBump (minus _ =>
    Parse.givesAfter0 (reads0At modes Num) (number => givesNegativeDigits modes minus number))

theorem givesPatternAppendOf ∀ (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes)
    (start: Pattern) (next: PatternLevel)
    (nested: PatternNested pself) (plus: Bool):
    Parse.Gives GoodItems (() => patternAppendOf pself modes start next plus) (pat => True) :=
  match plus with
    | False => Parse.givesDone byComputing
    | True =>
      match isTextPattern start with
        | True => Parse.givesThen givesBump (operator _ =>
          Parse.givesThen (nested { modes, level = next }) (tail _ => Parse.givesDone byComputing))
        | False => Parse.readsFatal

theorem givesPatternAppend ∀ (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes)
    (start: Pattern) (next: PatternLevel)
    (nested: PatternNested pself):
    Parse.Gives GoodItems (() => patternAppend pself modes start next) (pat => True) :=
  Parse.givesAfter0 (reads0At modes PlusPlus) (plus => givesPatternAppendOf pself modes start next nested plus)

theorem givesAlternativeLinksOn ∀ (fuel: Nat) (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes)
    (next: PatternLevel) (found: List (Word, Pattern))
    (nested: PatternNested pself) (items: List Item):
    Parse.Gives GoodItems (() => alternativeLinksOn fuel pself modes next found items) (links => True) :=
  match fuel, items with
    | Succ more, [bar, ..rest] =>
      match linkHere modes bar with
        | True => Parse.givesThen givesBump (barLeaf _ =>
          Parse.givesThen (nested { modes, level = next }) (alternative _ =>
            givesAlternativeLinks more pself modes next [(barLeaf, alternative), ..found] nested))
        | False => Parse.givesDone byComputing
    | Succ more, [] => Parse.givesDone byComputing
    | Zero, items => Parse.givesDone byComputing

theorem givesAlternativeLinks ∀ (fuel: Nat) (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes)
    (next: PatternLevel) (found: List (Word, Pattern))
    (nested: PatternNested pself):
    Parse.Gives GoodItems (() => alternativeLinks fuel pself modes next found) (links => True) :=
  Parse.givesAfter0 reads0Left (items => givesAlternativeLinksOn fuel pself modes next found nested items)

theorem givesAlternatives ∀ (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes)
    (first: Pattern) (next: PatternLevel)
    (nested: PatternNested pself):
    Parse.Gives GoodItems (() => alternatives pself modes first next) (pat => True) :=
  Parse.givesThen Parse.givesMark (here _ =>
    Parse.givesThen (givesAlternativeLinks (here.left + 1) pself modes next [] nested) (links _ =>
      Parse.givesDone byComputing))

-- Records.

theorem givesFieldPatternValue ∀ (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes)
    (nested: PatternNested pself) (equals: Option Word):
    Parse.Gives GoodItems (() => fieldPatternValue pself modes equals) (found => True) :=
  match equals with
    | Some word =>
      Parse.givesThen (nested { modes, level = PatternFieldValue }) (value _ => Parse.givesDone byComputing)
    | None => Parse.givesDone byComputing

theorem givesFieldPatterns ∀ (fuel: Nat) (pself: PatternGoal → {Parse Item} Pattern)
    (modes: Modes) (found: List FieldPattern)
    (nested: PatternNested pself):
    Parse.Gives GoodItems (() => fieldPatterns fuel pself modes found) (read => True) :=
  match fuel with
    | Zero => Parse.givesDone byComputing
    | Succ more =>
      Parse.givesAfter0 (reads0At modes DotDot) (dots => givesFieldPatternStep more pself modes found nested dots)

theorem givesFieldPatternStep ∀ (more: Nat) (pself: PatternGoal → {Parse Item} Pattern)
    (modes: Modes) (found: List FieldPattern)
    (nested: PatternNested pself) (dots: Bool):
    Parse.Gives GoodItems (() => fieldPatternStep more pself modes found dots) (read => True) :=
  match dots with
    | True => Parse.givesThen givesBump (rest _ => Parse.givesDone byComputing)
    | False =>
      Parse.givesAfter0 (reads0At modes RBrace) (closed => givesFieldPatternClose more pself modes found nested closed)

theorem givesFieldPatternClose ∀ (more: Nat) (pself: PatternGoal → {Parse Item} Pattern)
    (modes: Modes) (found: List FieldPattern)
    (nested: PatternNested pself) (closed: Bool):
    Parse.Gives GoodItems (() => fieldPatternClose more pself modes found closed) (read => True) :=
  match closed with
    | True => Parse.givesDone byComputing
    | False => Parse.givesThen (givesLower modes "a field name, or `..`") (name _ =>
      Parse.givesThen
        (Parse.givesThen (givesEat modes Equals) (equals _ => givesFieldPatternValue pself modes nested equals))
        (value _ =>
          Parse.givesThen (givesEat modes Comma) (comma _ =>
            givesFieldPatternNext more pself modes found nested { name, value } comma)))

theorem givesFieldPatternNext ∀ (more: Nat) (pself: PatternGoal → {Parse Item} Pattern)
    (modes: Modes) (found: List FieldPattern)
    (nested: PatternNested pself)
    (field: FieldPattern) (comma: Option Word):
    Parse.Gives GoodItems (() => fieldPatternNext more pself modes found field comma) (read => True) :=
  match comma with
    | Some word => givesFieldPatterns more pself modes [field, ..found] nested
    | None => Parse.givesDone byComputing

theorem givesFieldsPatternEnd ∀ (inner: Modes) (open: Word) (read: (List FieldPattern, Bool, Option Word)):
    Parse.Gives GoodItems (() => fieldsPatternEnd inner open read) (found => True) :=
  match read with
    | (fields, trailingComma, rest) =>
      Parse.givesThen (givesExpectAny inner RBrace "`,` or `}`") (close _ => Parse.givesDone byComputing)

theorem givesFieldsPattern ∀ (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes)
    (nested: PatternNested pself):
    Parse.Gives GoodItems (() => fieldsPattern pself modes) (found => True) :=
  Parse.givesThen (givesExpectAny modes LBrace "`{`") (open _ =>
    Parse.givesThen Parse.givesMark (here _ =>
      Parse.givesThen (givesFieldPatterns (here.left + 1) pself modes.inBrackets [] nested) (read _ =>
        givesFieldsPatternEnd modes.inBrackets open read)))

-- Constructors and their arguments.

theorem givesCtorRecordArgument ∀ (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes)
    (name: Word) (found: List Pattern)
    (nested: PatternNested pself):
    Parse.Gives GoodItems (() => ctorRecordArgument pself modes name found) (pat => True) :=
  match lastIsUpper name found with
    | True => Parse.readsFatal
    | False => Parse.givesThen (givesFieldsPattern pself modes nested) (fields _ => Parse.givesDone byComputing)

theorem givesCtorArgList ∀ (fuel: Nat) (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes) (name: Word)
    (stops: Tok → Bool) (found: List Pattern)
    (nested: PatternNested pself):
    Parse.Gives GoodItems (() => ctorArgList fuel pself modes name stops found) (list => True) :=
  Parse.givesAfter0 (reads0Peek modes) (seen => givesCtorArgListOn fuel pself modes name stops found nested seen)

theorem givesCtorArgListOn ∀ (fuel: Nat) (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes) (name: Word)
    (stops: Tok → Bool) (found: List Pattern)
    (nested: PatternNested pself) (seen: Option Tok):
    Parse.Gives GoodItems (() => ctorArgListOn fuel pself modes name stops found seen) (list => True) :=
  match fuel, seen with
    | Succ more, Some kind =>
      match stops kind with
        | True => Parse.givesDone byComputing
        | False => givesCtorArgBrace more pself modes name stops found nested (kind == LBrace)
    | Succ more, None => Parse.givesDone byComputing
    | Zero, seen => Parse.givesDone byComputing

theorem givesCtorArgBrace ∀ (more: Nat) (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes) (name: Word)
    (stops: Tok → Bool) (found: List Pattern)
    (nested: PatternNested pself) (brace: Bool):
    Parse.Gives GoodItems (() => ctorArgBrace more pself modes name stops found brace) (list => True) :=
  match brace with
    | True => Parse.givesThen (givesCtorRecordArgument pself modes name found nested) (entry _ =>
      givesCtorArgList more pself modes name stops [entry, ..found] nested)
    | False => Parse.givesAfter0 [p := () => left()] reads0Left (items =>
      givesCtorArgMinus more pself modes name stops found nested (argumentMinus items))

theorem givesCtorArgMinus ∀ (more: Nat) (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes) (name: Word)
    (stops: Tok → Bool) (found: List Pattern)
    (nested: PatternNested pself) (minus: Bool):
    Parse.Gives GoodItems (() => ctorArgMinus more pself modes name stops found minus) (list => True) :=
  match minus with
    | True => Parse.givesThen (givesNegativePattern modes) (entry _ =>
      givesCtorArgList more pself modes name stops [entry, ..found] nested)
    | False => Parse.givesThen (nested { modes, level = PatternPlain }) (entry _ =>
      givesCtorArgList more pself modes name stops [entry, ..found] nested)

theorem givesCtorFieldsEnd ∀ (name: Word) (fields: FieldsPattern) (stops: Tok → Bool) (seen: Option Tok):
    Parse.Gives GoodItems (() => ctorFieldsEnd name fields stops seen) (pat => True) :=
  match seen with
    | Some kind =>
      match stops kind with
        | True => Parse.givesDone byComputing
        | False => Parse.readsFatal
    | None => Parse.givesDone byComputing

theorem givesCtorListEnd ∀ (name: Word) (arguments: List Pattern):
    Parse.Gives GoodItems (() => ctorListEnd name arguments) (pat => True) :=
  match arguments with | [] | [_, .._] => Parse.givesDone byComputing

theorem givesCtorArgsOf ∀ (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes) (name: Word) (stops: Tok → Bool)
    (nested: PatternNested pself) (braced: Bool):
    Parse.Gives GoodItems (() => ctorArgsOf pself modes name stops braced) (pat => True) :=
  match braced with
    | True => Parse.givesThen (givesFieldsPattern pself modes nested) (fields _ =>
      Parse.givesAfter0 (reads0Peek modes) (seen => givesCtorFieldsEnd name fields stops seen))
    | False => Parse.givesThen Parse.givesMark (here _ =>
      Parse.givesThen (givesCtorArgList (here.left + 1) pself modes name stops [] nested) (list _ =>
        givesCtorListEnd name list))

theorem givesCtorArgs ∀ (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes) (name: Word) (stops: Tok → Bool)
    (nested: PatternNested pself):
    Parse.Gives GoodItems (() => ctorArgs pself modes name stops) (pat => True) :=
  Parse.givesAfter0 (reads0At modes LBrace) (braced => givesCtorArgsOf pself modes name stops nested braced)

-- The levels.

theorem givesTupleItem ∀ (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes)
    (nested: PatternNested pself):
    Parse.Gives GoodItems (() => tupleItem pself modes) (pat => True) :=
  Parse.givesThen (nested { modes, level = PatternTupleComponent }) (first _ =>
    givesAlternatives pself modes first PatternTupleComponent nested)

theorem givesListItemPattern ∀ (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes)
    (nested: PatternNested pself):
    Parse.Gives GoodItems (() => listItemPattern pself modes) (pat => True) :=
  Parse.givesThen (nested { modes, level = PatternListComponent }) (first _ =>
    givesAlternatives pself modes first PatternListComponent nested)

theorem givesTupleSigned ∀ (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes)
    (nested: PatternNested pself) (minus: Bool):
    Parse.Gives GoodItems (() => tupleSigned pself modes minus) (pat => True) :=
  match minus with
    | True => givesNegativePattern modes
    | False => Parse.givesThen (givesPlainPattern pself modes nested) (plain _ =>
      givesPatternAppend pself modes plain PatternTupleComponent nested)

theorem givesTupleComponentOf ∀ (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes)
    (nested: PatternNested pself) (isCtor: Bool):
    Parse.Gives GoodItems (() => tupleComponentOf pself modes isCtor) (pat => True) :=
  match isCtor with
    | True => Parse.givesThen givesBump (name _ =>
      Parse.givesThen
        (givesCtorArgs pself modes name
          (kind => kind == Comma || kind == RParen || kind == Pipe || kind == PlusPlus)
          nested)
        (ctor _ => givesPatternAppend pself modes ctor PatternTupleComponent nested))
    | False => Parse.givesAfter0 (reads0At modes Minus) (minus => givesTupleSigned pself modes nested minus)

theorem givesTupleComponent ∀ (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes)
    (nested: PatternNested pself):
    Parse.Gives GoodItems (() => tupleComponent pself modes) (pat => True) :=
  Parse.givesAfter0 (reads0CtorAhead modes) (isCtor => givesTupleComponentOf pself modes nested isCtor)

theorem givesListComponentOf ∀ (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes)
    (nested: PatternNested pself) (isCtor: Bool):
    Parse.Gives GoodItems (() => listComponentOf pself modes isCtor) (pat => True) :=
  match isCtor with
    | True => Parse.givesThen givesBump (name _ =>
      Parse.givesThen
        (givesCtorArgs pself modes name
          (kind => kind == Comma || kind == RBracket || kind == Pipe || kind == PlusPlus)
          nested)
        (ctor _ => givesPatternAppend pself modes ctor PatternListComponent nested))
    | False => givesTupleComponent pself modes nested

theorem givesListComponent ∀ (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes)
    (nested: PatternNested pself):
    Parse.Gives GoodItems (() => listComponent pself modes) (pat => True) :=
  Parse.givesAfter0 (reads0CtorAhead modes) (isCtor => givesListComponentOf pself modes nested isCtor)

theorem givesAltPatternOneOf ∀ (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes)
    (nested: PatternNested pself) (isCtor: Bool):
    Parse.Gives GoodItems (() => altPatternOneOf pself modes isCtor) (pat => True) :=
  match isCtor with
    | True => Parse.givesThen givesBump (name _ =>
      Parse.givesThen (givesCtorArgs pself modes name endsAltArguments nested) (ctor _ =>
        givesPatternAppend pself modes ctor PatternAltOne nested))
    | False => givesTupleComponent pself modes nested

theorem givesAltPatternOne ∀ (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes)
    (nested: PatternNested pself):
    Parse.Gives GoodItems (() => altPatternOne pself modes) (pat => True) :=
  Parse.givesAfter0 (reads0CtorAhead modes) (isCtor => givesAltPatternOneOf pself modes nested isCtor)

-- Lists and tuples.

theorem givesListPatternNext ∀ (more: Nat) (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes)
    (found: List Pattern) (item: Pattern)
    (nested: PatternNested pself) (comma: Option Word):
    Parse.Gives GoodItems (() => listPatternNext more pself modes found item comma) (read => True) :=
  match comma with
    | Some word => givesListPatternItems more pself modes [item, ..found] nested
    | None => Parse.givesDone byComputing

theorem givesListPatternDots ∀ (more: Nat) (pself: PatternGoal → {Parse Item} Pattern)
    (modes: Modes) (found: List Pattern)
    (nested: PatternNested pself) (dots: Bool):
    Parse.Gives GoodItems (() => listPatternDots more pself modes found dots) (read => True) :=
  match dots with
    | True => Parse.givesThen givesBump (dotsWord _ =>
      Parse.givesThen (nested { modes, level = PatternPlain }) (tail _ => Parse.givesDone byComputing))
    | False => Parse.givesThen (givesListItemPattern pself modes nested) (entry _ =>
      Parse.givesThen (givesEat modes Comma) (comma _ =>
        givesListPatternNext more pself modes found entry nested comma))

theorem givesListPatternStep ∀ (more: Nat) (pself: PatternGoal → {Parse Item} Pattern)
    (modes: Modes) (found: List Pattern)
    (nested: PatternNested pself) (closed: Bool):
    Parse.Gives GoodItems (() => listPatternStep more pself modes found closed) (read => True) :=
  match closed with
    | True => Parse.givesDone byComputing
    | False =>
      Parse.givesAfter0 (reads0At modes DotDot) (dots => givesListPatternDots more pself modes found nested dots)

theorem givesListPatternItems ∀ (fuel: Nat) (pself: PatternGoal → {Parse Item} Pattern)
    (modes: Modes) (found: List Pattern)
    (nested: PatternNested pself):
    Parse.Gives GoodItems (() => listPatternItems fuel pself modes found) (read => True) :=
  match fuel with
    | Zero => Parse.givesDone byComputing
    | Succ more =>
      Parse.givesAfter0 (reads0At modes RBracket) (closed => givesListPatternStep more pself modes found nested closed)

theorem givesListPatternClose ∀ (inner: Modes) (open: Word) (items: List Pattern) (trailingComma: Bool)
    (tail: Option (Word, Pattern)) (comma: Bool):
    Parse.Gives GoodItems (() => listPatternClose inner open items trailingComma tail comma) (pat => True) :=
  match tail, comma with
    | Some pair, True => Parse.readsFatal
    | Some pair, False =>
      Parse.givesThen (givesExpectAny inner RBracket "`]`: a `..` tail must be the last item") (close _ =>
        Parse.givesDone byComputing)
    | None, comma =>
      Parse.givesThen (givesExpectAny inner RBracket "`,` or `]`") (close _ => Parse.givesDone byComputing)

theorem givesListPatternEnd ∀ (inner: Modes) (open: Word) (read: (List Pattern, Bool, Option (Word, Pattern))):
    Parse.Gives GoodItems (() => listPatternEnd inner open read) (pat => True) :=
  match read with
    | (items, trailingComma, tail) => Parse.givesAfter0 (reads0At inner Comma) (comma =>
      givesListPatternClose inner open items trailingComma tail comma)

theorem givesListPattern ∀ (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes)
    (nested: PatternNested pself):
    Parse.Gives GoodItems (() => listPattern pself modes) (pat => True) :=
  Parse.givesThen givesBump (open _ =>
    Parse.givesThen Parse.givesMark (here _ =>
      Parse.givesThen (givesListPatternItems (here.left + 1) pself modes.inBrackets [] nested) (read _ =>
        givesListPatternEnd modes.inBrackets open read)))

theorem givesTuplePatternEnd ∀ (modes: Modes) (open: Word) (pair: (List Pattern, Bool)):
    Parse.Gives GoodItems (() => tuplePatternEnd modes open pair) (pat => True) :=
  match pair with
    | (items, trailingComma) =>
      Parse.givesThen (givesExpectAny modes RParen "`)`") (close _ => Parse.givesDone byComputing)

theorem givesParenPatternOf ∀ (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes) (open: Word) (first: Pattern)
    (nested: PatternNested pself) (comma: Bool):
    Parse.Gives GoodItems (() => parenPatternOf pself modes open first comma) (pat => True) :=
  match comma with
    | True => Parse.givesThen Parse.givesMark (here _ =>
      Parse.givesThen
        (givesCommaListFrom modes
          (count => modes.at RParen && count >= 2)
          (() => tupleItem pself modes)
          (found => True)
          (count => Parse.givesThen (givesAt modes RParen) (stop _ => Parse.givesDone byComputing))
          (givesTupleItem pself modes nested)
          (here.left + 1)
          1
          first
          []
          byComputing
          ())
        (pair _ => givesTuplePatternEnd modes open pair))
    | False => Parse.givesThen (givesExpectAny modes RParen "`)`") (close _ => Parse.givesDone byComputing)

theorem givesParenPatternEnd ∀ (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes) (open: Word) (first: Pattern)
    (nested: PatternNested pself):
    Parse.Gives GoodItems (() => parenPatternEnd pself modes open first) (pat => True) :=
  Parse.givesAfter0 (reads0At modes Comma) (comma => givesParenPatternOf pself modes open first nested comma)

-- Brackets, parentheses and the plain pattern.

theorem givesNamedPattern ∀ (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes)
    (nested: PatternNested pself):
    Parse.Gives GoodItems (() => namedPattern pself modes) (pat => True) :=
  Parse.givesThen givesBump (open _ =>
    Parse.givesThen (givesLower modes.inBrackets "a field name") (name _ =>
      Parse.givesThen givesBump (colonEq _ =>
        Parse.givesThen (nested { modes = modes.inBrackets, level = PatternPlain }) (value _ =>
          Parse.givesThen (givesExpectAny modes.inBrackets RBracket "`]`") (close _ => Parse.givesDone byComputing)))))

theorem givesBracketPatternOn ∀ (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes)
    (nested: PatternNested pself) (second third: Option Tok):
    Parse.Gives GoodItems (() => bracketPatternOn pself modes second third) (pat => True) :=
  match second, third with
    | Some Lower, Some ColonEq => givesNamedPattern pself modes nested
    | other, others => givesListPattern pself modes nested

theorem givesBracketPattern ∀ (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes)
    (nested: PatternNested pself) (second: Option Tok):
    Parse.Gives GoodItems (() => bracketPattern pself modes second) (pat => True) :=
  Parse.givesAfter0 (reads0PeekAt modes 2) (third => givesBracketPatternOn pself modes nested second third)

theorem givesParenComponent ∀ (pself: PatternGoal → {Parse Item} Pattern) (inner: Modes)
    (nested: PatternNested pself) (isCtor: Bool):
    Parse.Gives GoodItems (() => parenComponent pself inner isCtor) (pat => True) :=
  match isCtor with
    | True => Parse.givesThen givesBump (name _ =>
      givesCtorArgs pself inner name
        (kind => kind == RParen || kind == Comma || kind == Pipe || kind == PlusPlus)
        nested)
    | False => nested { modes = inner, level = PatternPlain }

theorem givesParenMinusPattern ∀ (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes)
    (nested: PatternNested pself):
    Parse.Gives GoodItems (() => parenMinusPattern pself modes) (pat => True) :=
  Parse.givesThen givesBump (open _ =>
    Parse.givesThen (givesTupleItem pself modes.inBrackets nested) (first _ =>
      givesParenPatternEnd pself modes.inBrackets open first nested))

theorem givesParenOpenPattern ∀ (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes)
    (nested: PatternNested pself):
    Parse.Gives GoodItems (() => parenOpenPattern pself modes) (pat => True) :=
  Parse.givesThen givesBump (open _ =>
    Parse.givesThen
      (Parse.givesAfter0 (reads0CtorAhead modes.inBrackets) (isCtor =>
        givesParenComponent pself modes.inBrackets nested isCtor))
      (component _ =>
        Parse.givesThen
          (givesPatternAppend pself modes.inBrackets component PatternTupleComponent nested)
          (appended _ =>
            Parse.givesThen (givesAlternatives pself modes.inBrackets appended PatternTupleComponent nested) (first _ =>
              givesParenPatternEnd pself modes.inBrackets open first nested))))

theorem givesParenPattern ∀ (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes)
    (nested: PatternNested pself) (second: Option Tok):
    Parse.Gives GoodItems (() => parenPattern pself modes second) (pat => True) :=
  match second with
    | Some RParen =>
      Parse.givesThen givesBump (open _ => Parse.givesThen givesBump (close _ => Parse.givesDone byComputing))
    | Some Minus => givesParenMinusPattern pself modes nested
    | other => givesParenOpenPattern pself modes nested

theorem givesQuotOrLower ∀ (modes: Modes) (quot: Bool):
    Parse.Gives GoodItems (() => quotOrLower modes quot) (word => True) :=
  match quot with
    | True => givesBump
    | False => givesLower modes "a pattern"

theorem givesBumpedWord ∀ (kind: Tok): Parse.Gives GoodItems (() => PatternWord kind bump()) (pat => True) :=
  Parse.givesThen givesBump (bumped _ => Parse.givesDone byComputing)

theorem givesPlainPatternOn ∀ (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes)
    (nested: PatternNested pself) (seen: Option Tok):
    Parse.Gives GoodItems (() => plainPatternOn pself modes seen) (pat => True) :=
  match seen with
    | Some Upper => givesBumpedWord Upper
    | Some Lower =>
      Parse.givesThen
        (Parse.givesAfter0 (reads0WordAhead modes "Quot.mk") (quot => givesQuotOrLower modes quot))
        (bumped _ => Parse.givesDone byComputing)
    | Some Underscore => givesBumpedWord Underscore
    | Some Num => givesBumpedWord Num
    | Some CharLit => givesBumpedWord CharLit
    | Some Str => givesBumpedWord Str
    | Some StrStart => Parse.readsFatal
    | Some LBrace => Parse.givesThen (givesFieldsPattern pself modes nested) (fields _ => Parse.givesDone byComputing)
    | Some LBracket =>
      Parse.givesAfter0 (reads0PeekAt modes 1) (second => givesBracketPattern pself modes nested second)
    | Some LParen => Parse.givesAfter0 (reads0PeekAt modes 1) (second => givesParenPattern pself modes nested second)
    | other => givesFailName modes "a pattern or `=`"

theorem givesPlainPattern ∀ (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes)
    (nested: PatternNested pself):
    Parse.Gives GoodItems (() => Syntax.plainPattern pself modes) (pat => True) :=
  Parse.givesAfter0 (reads0Peek modes) (seen => givesPlainPatternOn pself modes nested seen)

theorem givesFieldValuePattern ∀ (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes)
    (nested: PatternNested pself) (isCtor: Bool):
    Parse.Gives GoodItems (() => fieldValuePattern pself modes isCtor) (pat => True) :=
  match isCtor with
    | True => Parse.givesThen givesBump (ctor _ =>
      givesCtorArgs pself modes ctor (kind => kind == Comma || kind == RBrace) nested)
    | False => givesPlainPattern pself modes nested

--| One level of the pattern parser gives a pattern, given that `pself` does at every goal.
theorem givesPatternRule ∀ (pself: PatternGoal → {Parse Item} Pattern)
    (nested: PatternNested pself) (goal: PatternGoal):
    Parse.Gives GoodItems (() => patternRule pself goal) (pat => True) :=
  match goal with
    | { modes, level } =>
      match level with
        | PatternPlain => givesPlainPattern pself modes nested
        | PatternTupleComponent => givesTupleComponent pself modes nested
        | PatternListComponent => givesListComponent pself modes nested
        | PatternAltOne => givesAltPatternOne pself modes nested
        | PatternFieldValue =>
          Parse.givesAfter0 (reads0CtorAhead modes) (isCtor => givesFieldValuePattern pself modes nested isCtor)

--| The pattern parser reads patterns, from good items.
theorem givesPattern ∀ (goal: PatternGoal): Parse.Gives GoodItems (() => pattern goal) (pat => True) :=
  Parse.givesRecursiveWith patternRule
    (inner pat => True)
    (pself nested goal => givesPatternRule pself nested goal)
    goal

theorem givesAltPattern ∀ (modes: Modes): Parse.Gives GoodItems (() => altPattern modes) (pat => True) :=
  Parse.givesThen (givesPattern { modes, level = PatternAltOne }) (first _ =>
    givesAlternatives pattern modes first PatternAltOne givesPattern)

theorem givesArmPatterns ∀ (modes: Modes): Parse.Gives GoodItems (() => armPatterns modes) (patterns => True) :=
  Parse.givesThen (givesAltPattern modes) (first _ =>
    Parse.givesThen Parse.givesMark (here _ =>
      Parse.givesThen
        (givesCommaListFrom modes
          (count => False)
          (() => altPattern modes)
          (found => True)
          (count => Parse.givesDone byComputing)
          (givesAltPattern modes)
          (here.left + 1)
          1
          first
          []
          byComputing
          ())
        (pair _ => Parse.givesDone byComputing)))
