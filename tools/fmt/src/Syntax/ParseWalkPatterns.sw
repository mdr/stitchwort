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
  byWalking [givesBump]

theorem givesNegativeDigits ∀ (modes: Modes) (minus: Word) (number: Bool):
    Parse.Gives GoodItems (() => negativeDigits modes minus number) (pat => True) :=
  byWalking [givesBump, givesFail]

theorem givesNegativePattern ∀ (modes: Modes): Parse.Gives GoodItems (() => negativePattern modes) (pat => True) :=
  byWalking [givesBump, givesNegativeDigits]

theorem givesPatternAppendOf ∀ (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes)
    (start: Pattern) (next: PatternLevel)
    (nested: PatternNested pself) (plus: Bool):
    Parse.Gives GoodItems (() => patternAppendOf pself modes start next plus) (pat => True) :=
  byWalking [givesBump]

theorem givesPatternAppend ∀ (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes)
    (start: Pattern) (next: PatternLevel)
    (nested: PatternNested pself):
    Parse.Gives GoodItems (() => patternAppend pself modes start next) (pat => True) :=
  byWalking [givesPatternAppendOf]

theorem givesAlternativeLinksOn ∀ (fuel: Nat) (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes)
    (next: PatternLevel) (found: List (Word, Pattern))
    (nested: PatternNested pself) (items: List Item):
    Parse.Gives GoodItems (() => alternativeLinksOn fuel pself modes next found items) (links => True) :=
  byWalking [givesBump, givesAlternativeLinks]

theorem givesAlternativeLinks ∀ (fuel: Nat) (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes)
    (next: PatternLevel) (found: List (Word, Pattern))
    (nested: PatternNested pself):
    Parse.Gives GoodItems (() => alternativeLinks fuel pself modes next found) (links => True) :=
  byWalking [givesAlternativeLinksOn]

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
  byWalking []

theorem givesFieldPatterns ∀ (fuel: Nat) (pself: PatternGoal → {Parse Item} Pattern)
    (modes: Modes) (found: List FieldPattern)
    (nested: PatternNested pself):
    Parse.Gives GoodItems (() => fieldPatterns fuel pself modes found) (read => True) :=
  byWalking [givesFieldPatternStep]

theorem givesFieldPatternStep ∀ (more: Nat) (pself: PatternGoal → {Parse Item} Pattern)
    (modes: Modes) (found: List FieldPattern)
    (nested: PatternNested pself) (dots: Bool):
    Parse.Gives GoodItems (() => fieldPatternStep more pself modes found dots) (read => True) :=
  byWalking [givesBump, givesFieldPatternClose]

theorem givesFieldPatternClose ∀ (more: Nat) (pself: PatternGoal → {Parse Item} Pattern)
    (modes: Modes) (found: List FieldPattern)
    (nested: PatternNested pself) (closed: Bool):
    Parse.Gives GoodItems (() => fieldPatternClose more pself modes found closed) (read => True) :=
  byWalking [givesLower, givesEat, givesFieldPatternValue, givesFieldPatternNext]

theorem givesFieldPatternNext ∀ (more: Nat) (pself: PatternGoal → {Parse Item} Pattern)
    (modes: Modes) (found: List FieldPattern)
    (nested: PatternNested pself)
    (field: FieldPattern) (comma: Option Word):
    Parse.Gives GoodItems (() => fieldPatternNext more pself modes found field comma) (read => True) :=
  byWalking [givesFieldPatterns]

theorem givesFieldsPatternEnd ∀ (inner: Modes) (open: Word) (read: (List FieldPattern, Bool, Option Word)):
    Parse.Gives GoodItems (() => fieldsPatternEnd inner open read) (found => True) :=
  byWalking [givesExpectAny]

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
  byWalking [givesFieldsPattern]

theorem givesCtorArgList ∀ (fuel: Nat) (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes) (name: Word)
    (stops: Tok → Bool) (found: List Pattern)
    (nested: PatternNested pself):
    Parse.Gives GoodItems (() => ctorArgList fuel pself modes name stops found) (list => True) :=
  byWalking [givesCtorArgListOn]

theorem givesCtorArgListOn ∀ (fuel: Nat) (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes) (name: Word)
    (stops: Tok → Bool) (found: List Pattern)
    (nested: PatternNested pself) (seen: Option Tok):
    Parse.Gives GoodItems (() => ctorArgListOn fuel pself modes name stops found seen) (list => True) :=
  byWalking [givesCtorArgBrace]

theorem givesCtorArgBrace ∀ (more: Nat) (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes) (name: Word)
    (stops: Tok → Bool) (found: List Pattern)
    (nested: PatternNested pself) (brace: Bool):
    Parse.Gives GoodItems (() => ctorArgBrace more pself modes name stops found brace) (list => True) :=
  byWalking [givesCtorRecordArgument, givesCtorArgList, givesCtorArgMinus]

theorem givesCtorArgMinus ∀ (more: Nat) (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes) (name: Word)
    (stops: Tok → Bool) (found: List Pattern)
    (nested: PatternNested pself) (minus: Bool):
    Parse.Gives GoodItems (() => ctorArgMinus more pself modes name stops found minus) (list => True) :=
  byWalking [givesNegativePattern, givesCtorArgList]

theorem givesCtorFieldsEnd ∀ (name: Word) (fields: FieldsPattern) (stops: Tok → Bool) (seen: Option Tok):
    Parse.Gives GoodItems (() => ctorFieldsEnd name fields stops seen) (pat => True) :=
  byWalking []

theorem givesCtorListEnd ∀ (name: Word) (arguments: List Pattern):
    Parse.Gives GoodItems (() => ctorListEnd name arguments) (pat => True) :=
  byWalking []

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
  byWalking [givesCtorArgsOf]

-- The levels.

theorem givesTupleItem ∀ (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes)
    (nested: PatternNested pself):
    Parse.Gives GoodItems (() => tupleItem pself modes) (pat => True) :=
  byWalking [givesAlternatives]

theorem givesListItemPattern ∀ (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes)
    (nested: PatternNested pself):
    Parse.Gives GoodItems (() => listItemPattern pself modes) (pat => True) :=
  byWalking [givesAlternatives]

theorem givesTupleSigned ∀ (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes)
    (nested: PatternNested pself) (minus: Bool):
    Parse.Gives GoodItems (() => tupleSigned pself modes minus) (pat => True) :=
  byWalking [givesNegativePattern, givesPlainPattern, givesPatternAppend]

theorem givesTupleComponentOf ∀ (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes)
    (nested: PatternNested pself) (isCtor: Bool):
    Parse.Gives GoodItems (() => tupleComponentOf pself modes isCtor) (pat => True) :=
  byWalking [givesCtorArgs, givesPatternAppend, givesTupleSigned]

theorem givesTupleComponent ∀ (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes)
    (nested: PatternNested pself):
    Parse.Gives GoodItems (() => tupleComponent pself modes) (pat => True) :=
  Parse.givesAfter0 (reads0CtorAhead modes) (isCtor => givesTupleComponentOf pself modes nested isCtor)

theorem givesListComponentOf ∀ (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes)
    (nested: PatternNested pself) (isCtor: Bool):
    Parse.Gives GoodItems (() => listComponentOf pself modes isCtor) (pat => True) :=
  byWalking [givesCtorArgs, givesPatternAppend, givesTupleComponent]

theorem givesListComponent ∀ (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes)
    (nested: PatternNested pself):
    Parse.Gives GoodItems (() => listComponent pself modes) (pat => True) :=
  Parse.givesAfter0 (reads0CtorAhead modes) (isCtor => givesListComponentOf pself modes nested isCtor)

theorem givesAltPatternOneOf ∀ (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes)
    (nested: PatternNested pself) (isCtor: Bool):
    Parse.Gives GoodItems (() => altPatternOneOf pself modes isCtor) (pat => True) :=
  byWalking [givesCtorArgs, givesPatternAppend, givesTupleComponent]

theorem givesAltPatternOne ∀ (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes)
    (nested: PatternNested pself):
    Parse.Gives GoodItems (() => altPatternOne pself modes) (pat => True) :=
  Parse.givesAfter0 (reads0CtorAhead modes) (isCtor => givesAltPatternOneOf pself modes nested isCtor)

-- Lists and tuples.

theorem givesListPatternNext ∀ (more: Nat) (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes)
    (found: List Pattern) (item: Pattern)
    (nested: PatternNested pself) (comma: Option Word):
    Parse.Gives GoodItems (() => listPatternNext more pself modes found item comma) (read => True) :=
  byWalking [givesListPatternItems]

theorem givesListPatternDots ∀ (more: Nat) (pself: PatternGoal → {Parse Item} Pattern)
    (modes: Modes) (found: List Pattern)
    (nested: PatternNested pself) (dots: Bool):
    Parse.Gives GoodItems (() => listPatternDots more pself modes found dots) (read => True) :=
  byWalking [givesListItemPattern, givesEat, givesListPatternNext]

theorem givesListPatternStep ∀ (more: Nat) (pself: PatternGoal → {Parse Item} Pattern)
    (modes: Modes) (found: List Pattern)
    (nested: PatternNested pself) (closed: Bool):
    Parse.Gives GoodItems (() => listPatternStep more pself modes found closed) (read => True) :=
  byWalking [givesListPatternDots]

theorem givesListPatternItems ∀ (fuel: Nat) (pself: PatternGoal → {Parse Item} Pattern)
    (modes: Modes) (found: List Pattern)
    (nested: PatternNested pself):
    Parse.Gives GoodItems (() => listPatternItems fuel pself modes found) (read => True) :=
  byWalking [givesListPatternStep]

theorem givesListPatternClose ∀ (inner: Modes) (open: Word) (items: List Pattern) (trailingComma: Bool)
    (tail: Option (Word, Pattern)) (comma: Bool):
    Parse.Gives GoodItems (() => listPatternClose inner open items trailingComma tail comma) (pat => True) :=
  byWalking [givesExpectAny]

theorem givesListPatternEnd ∀ (inner: Modes) (open: Word) (read: (List Pattern, Bool, Option (Word, Pattern))):
    Parse.Gives GoodItems (() => listPatternEnd inner open read) (pat => True) :=
  byWalking [givesListPatternClose]

theorem givesListPattern ∀ (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes)
    (nested: PatternNested pself):
    Parse.Gives GoodItems (() => listPattern pself modes) (pat => True) :=
  Parse.givesThen givesBump (open _ =>
    Parse.givesThen Parse.givesMark (here _ =>
      Parse.givesThen (givesListPatternItems (here.left + 1) pself modes.inBrackets [] nested) (read _ =>
        givesListPatternEnd modes.inBrackets open read)))

theorem givesTuplePatternEnd ∀ (modes: Modes) (open: Word) (pair: (List Pattern, Bool)):
    Parse.Gives GoodItems (() => tuplePatternEnd modes open pair) (pat => True) :=
  byWalking [givesExpectAny]

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
  byWalking [givesParenPatternOf]

-- Brackets, parentheses and the plain pattern.

theorem givesNamedPattern ∀ (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes)
    (nested: PatternNested pself):
    Parse.Gives GoodItems (() => namedPattern pself modes) (pat => True) :=
  byWalking [givesBump, givesLower, givesExpectAny]

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
  byWalking [givesCtorArgs]

theorem givesParenMinusPattern ∀ (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes)
    (nested: PatternNested pself):
    Parse.Gives GoodItems (() => parenMinusPattern pself modes) (pat => True) :=
  byWalking [givesTupleItem, givesParenPatternEnd]

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
  byWalking [givesLower]

theorem givesBumpedWord ∀ (kind: Tok): Parse.Gives GoodItems (() => PatternWord kind bump()) (pat => True) :=
  byWalking [givesBump]

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
  byWalking [givesPlainPatternOn]

theorem givesFieldValuePattern ∀ (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes)
    (nested: PatternNested pself) (isCtor: Bool):
    Parse.Gives GoodItems (() => fieldValuePattern pself modes isCtor) (pat => True) :=
  byWalking [givesCtorArgs, givesPlainPattern]

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
