--| `calc` and `rewrite`, from the compared tier's walks, read as parsers outside slice 1.

namespace Syntax.ParseWalkCalc
import Std (Bool, DecEq, Eq, List, Nat, Option, Pair, Parse, Result, Text)
import Syntax (..)
import Fmt (..)
import Syntax.LexProofs (..)
import Syntax.ParseProofs (..)
import Syntax.ParseWalk (..)
import Syntax.ParseWalkLadder (..)
import Syntax.ParseWalkOutside (..)
import Syntax.ParseWalkPatterns (..)
import Syntax.ParseWalkBinders (..)
import Fmt.Grammar1 (..)
import Fmt.Kinds (..)

theorem givesHereOn ∀ (items: List Item): Parse.Gives GoodItems (() => hereOn items) (found => True) := match items with
  | [item, ..rest] => Parse.givesDone byComputing
  | [] => Parse.givesThen (givesOfReads0 reads0Offset) (here _ => Parse.givesDone byComputing)

theorem givesHere: Parse.Gives GoodItems (() => here()) (found => True) :=
  Parse.givesAfter0 reads0Left (items => givesHereOn items)

theorem givesColumnHere: Parse.Gives GoodItems (() => columnHere()) (found => True) :=
  Parse.givesAfter0 reads0Left (items => Parse.givesDone byComputing)

-- `calc` and `rewrite`, from the compared tier's walks.

theorem givesCalcOperand ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (outside: OutsideCompared self)
    (bases: AtomBases self):
    Parse.Gives GoodItems (() => calcOperand self modes) (found => True) :=
  Parse.givesThen (givesPipedOf self modes nested outside.below bases) (piped parsed =>
    Parse.givesWeaken
      (givesLogicAfter self modes piped nested outside bases (parsedWeaken parsed byComputing))
      (value _ => byComputing))

theorem givesStepSign ∀ (modes: Modes): Parse.Gives GoodItems (() => stepSign modes modes.peek) (signs => True) :=
  readsInPeeked modes
    (seen => stepSign modes seen) _
    (start fine stops => givesFail modes _ start fine)
    (start item later shape fine stopped =>
      match item.kind with
        | Equals | Le | Lt | Ge | Gt => Parse.givesDone byComputing start fine
        | NotEq | EqEq => Parse.readsFatal start fine
        | other => givesFail modes _ start fine)

theorem givesCalcProof ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (colonEq: Bool)
    (nested: Nested self):
    Parse.Gives GoodItems (() => calcProof self modes colonEq) (found => True) :=
  match colonEq with
    | True => Parse.givesThen givesFixedFrom (colonEqKeyword _ =>
      Parse.givesThen (givesFullAny self modes nested) (proof _ => Parse.givesDone byComputing))
    | False => Parse.givesDone byComputing

theorem givesCalcLine ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (indent more at: Nat)
    (found: List CalcStep) (ascending descending: Bool)
    (nested: Nested self)
    (outside: OutsideCompared self)
    (bases: AtomBases self)
    (steps: ∀ (column: Option Nat) (found: List CalcStep) (ascending descending: Bool) => Parse.Gives GoodItems
      (() => calcSteps more self modes indent column found ascending descending)
      (result => True)):
    Parse.Gives GoodItems (() => calcLine more self modes indent at found ascending descending) (result => True) :=
  Parse.givesThen givesFixedFrom (underscore _ =>
    Parse.givesThen (givesStepSign modes) (signs _ =>
      match signs with
        | (up, down) => Parse.givesThen givesBump (relation _ =>
          Parse.givesThen (givesCalcOperand self modes nested outside bases) (operand _ =>
            Parse.givesAfter0 (reads0At modes ColonEq) (colonEq =>
              Parse.givesThen (givesCalcProof self modes colonEq nested) (proof _ =>
                steps
                  (Some at)
                  [{ underscore, relation, operand, proof }, ..found]
                  (ascending || up)
                  (descending || down)))))))

theorem givesCalcSteps ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (indent: Nat) (column: Option Nat)
    (nested: Nested self)
    (outside: OutsideCompared self)
    (bases: AtomBases self)
    (fuel: Nat) (found: List CalcStep) (ascending descending: Bool):
    Parse.Gives GoodItems (() => calcSteps fuel self modes indent column found ascending descending) (result => True) :=
  match fuel with
    | Zero =>
      Parse.givesAfter0
        [p := () => left()]
        [j := items =>
          calcStep Zero self modes indent column found ascending descending (calcNextOn modes indent items)]
        reads0Left
        (items => Parse.givesDone byComputing)
    | Succ more => Parse.givesAfter0 [p := () => left()] reads0Left (items =>
      match calcNextOn modes indent items with
        | None => Parse.givesDone byComputing
        | Some at =>
          match column with
            | Some first =>
              match first != at with
                | True => Parse.readsFatal
                | False =>
                  givesCalcLine self modes indent more at found ascending descending nested outside bases
                    (column found ascending descending =>
                      givesCalcSteps self modes indent column nested outside bases more found ascending descending)
            | None =>
              givesCalcLine self modes indent more at found ascending descending nested outside bases
                (column found ascending descending =>
                  givesCalcSteps self modes indent column nested outside bases more found ascending descending))

theorem givesCalcBody ∀ (self: Goal → {Parse Item} Expr) (inner: Modes) (indent: Nat) (keyword: Comments) (first: Expr)
    (nested: Nested self)
    (outside: OutsideCompared self)
    (bases: AtomBases self):
    Parse.Gives GoodItems (() => calcBody self inner indent keyword first) Out :=
  Parse.givesThen Parse.givesMark (here _ =>
    Parse.givesThen
      (givesCalcSteps self inner indent None nested outside bases (here.left + 1) [] False False)
      (result _ =>
        match result with
          | (steps, ascending, descending) =>
            match steps.isEmpty with
              | True => givesFail inner _
              | False =>
                match ascending && descending with
                  | True => Parse.readsFatal
                  | False => Parse.givesDone byComputing))

theorem givesCalcAfter ∀ (self: Goal → {Parse Item} Expr) (inner: Modes) (indent: Nat) (keyword: Comments) (first: Expr)
    (nested: Nested self)
    (outside: OutsideCompared self)
    (bases: AtomBases self):
    Parse.Gives GoodItems (() => calcAfter self inner indent keyword first inner.peek) Out :=
  readsInPeeked inner
    (seen => calcAfter self inner indent keyword first seen) _
    (start fine stops => givesCalcBody self inner indent keyword first nested outside bases start fine)
    (start item later shape fine stopped =>
      match item.kind.isComparison with
        | True => Parse.readsFatal start fine
        | False => givesCalcBody self inner indent keyword first nested outside bases start fine)

theorem givesCalcExpr ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (outside: OutsideCompared self)
    (bases: AtomBases self):
    Parse.Gives GoodItems (() => calcExpr self modes) Out :=
  Parse.givesAfter0 reads0HeadIndent (indent =>
    Parse.givesThen givesFixedFrom (keyword _ =>
      Parse.givesThen (givesCalcOperand self ({ modes | inCalc = True }).sealed nested outside bases) (first _ =>
        givesCalcAfter self { modes | inCalc = True } indent keyword first nested outside bases)))

theorem reads0OwnLineAt ∀ (wanted: Tok) (column: Nat): Reads0 (() => ownLineAt wanted column) :=
  Parse.reads0Then reads0Left (items => Parse.reads0Done (ownLineOn wanted column items))

theorem reads0StartsAt ∀ (modes: Modes) (wanted: Tok) (column: Nat): Reads0 (() => startsAt modes wanted column) :=
  Parse.reads0Then (reads0At modes wanted) (here =>
    match here with
      | True => Parse.reads0Done True
      | False => reads0OwnLineAt wanted column)

theorem reads0RepeatedlyAhead ∀ (outer: Modes): Reads0 (() => repeatedlyAhead outer) :=
  Parse.reads0Then (reads0WordAhead outer "repeatedly") (word =>
    match word with
      | True => Parse.reads0Then (reads0PeekAt outer 1) (seen => Parse.reads0Done (isSome LBracket seen))
      | False => Parse.reads0Done False)

theorem reads0ReverseAhead ∀ (modes: Modes): Reads0 (() => reverseAhead modes) :=
  Parse.reads0Then (reads0At modes Lt) (less =>
    Parse.reads0Then reads0Left (items =>
      match items with
        | [first, minus, ..rest] =>
          match less with
            | True =>
              Parse.reads0Then (reads0PeekAt modes 1) (second => Parse.reads0Done (reverseMinus minus.glued second))
            | False => Parse.reads0Done False
        | other => Parse.reads0Done False))

theorem givesReverseOf ∀ (modes: Modes): Parse.Gives GoodItems (() => reverseOf modes) (found => True) :=
  Parse.givesAfter0 (reads0ReverseAhead modes) (reverse =>
    match reverse with
      | True => Parse.givesThen givesFixedFrom (less _ =>
        Parse.givesThen givesFixedFrom (second _ => Parse.givesDone byComputing))
      | False => Parse.givesDone byComputing)

theorem givesRewriteRule ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (found: List RewriteRule)
    (nested: Nested self)
    (outside: OutsideBraced self)
    (bases: AtomBases self):
    Parse.Gives GoodItems (() => rewriteRule self modes found) (done => True) :=
  Parse.givesThen (givesReverseOf modes) (reverse _ =>
    Parse.givesThen givesHere (start _ =>
      Parse.givesThen
        (givesAppendOf self { modes | rewriteRule = Some start, rewriteAt = True } nested outside bases)
        (rule _ => Parse.givesDone byComputing)))

theorem givesRewriteRules ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (outside: OutsideBraced self)
    (bases: AtomBases self)
    (fuel: Nat) (found: List RewriteRule):
    Parse.Gives GoodItems (() => rewriteRules fuel self modes found) (rules => True) :=
  Parse.givesThen (givesRewriteRule self modes found nested outside bases) (done _ =>
    Parse.givesAfter0 (reads0At modes Comma) (comma =>
      match fuel with
        | Zero => Parse.givesDone byComputing
        | Succ more =>
          match comma with
            | True => Parse.givesThen givesBump (gone _ => givesRewriteRules self modes nested outside bases more done)
            | False => Parse.givesDone byComputing))

theorem givesSetRule ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (found: List RewriteRule)
    (nested: Nested self):
    Parse.Gives GoodItems (() => setRule self modes found) (done => True) :=
  Parse.givesThen (givesReverseOf modes) (reverse _ =>
    Parse.givesThen (givesFullAny self modes nested) (rule _ => Parse.givesDone byComputing))

theorem givesSetRules ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (fuel: Nat) (found: List RewriteRule):
    Parse.Gives GoodItems (() => setRules fuel self modes found) (result => True) :=
  Parse.givesThen (givesSetRule self modes found nested) (done _ =>
    Parse.givesAfter0 (reads0At modes Comma) (comma =>
      match fuel with
        | Zero => Parse.givesDone byComputing
        | Succ more =>
          match comma with
            | True => Parse.givesThen givesBump (gone _ =>
              Parse.givesAfter0 (reads0At modes RBracket) (closed =>
                match closed with
                  | True => Parse.givesDone byComputing
                  | False => givesSetRules self modes nested more done))
            | False => Parse.givesDone byComputing))

theorem givesRuleSet ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self):
    Parse.Gives GoodItems (() => ruleSet self modes) (set => True) :=
  Parse.givesThen givesFixedFrom (open _ =>
    Parse.givesAfter0 (reads0At modes RBracket) (empty =>
      match empty with
        | True => Parse.readsFatal
        | False => Parse.givesThen Parse.givesMark (here _ =>
          Parse.givesThen (givesSetRules self modes.inBrackets nested (here.left + 1) []) (result _ =>
            match result with
              | (rules, trailingComma) =>
                Parse.givesThen (givesExpectFixed modes.inBrackets RBracket "`,` or `]`") (close _ =>
                  Parse.givesDone byComputing)))))

theorem givesTargetOf ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (at: Comments)
    (nested: Nested self)
    (outside: OutsideBraced self)
    (bases: AtomBases self):
    Parse.Gives GoodItems (() => targetOf self modes at) (target => True) :=
  Parse.givesThen givesHere (start _ =>
    Parse.givesThen
      (givesAppendOf self { modes | rewriteRule = Some start, rewriteAt = False } nested outside bases)
      (target _ => Parse.givesDone byComputing))

theorem givesTargetAfter ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (at: Comments)
    (nested: Nested self)
    (outside: OutsideBraced self)
    (bases: AtomBases self):
    Parse.Gives GoodItems (() => targetAfter self modes at modes.peek) (target => True) :=
  readsInPeeked modes
    (seen => targetAfter self modes at seen) _
    (start fine stops => Parse.readsFatal start fine)
    (start item later shape fine stopped =>
      match item.kind == KwThen || item.kind == KwIn with
        | True => Parse.readsFatal start fine
        | False => givesTargetOf self modes at nested outside bases start fine)

theorem givesRewriteTarget ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (outside: OutsideBraced self)
    (bases: AtomBases self):
    Parse.Gives GoodItems (() => rewriteTarget self modes) (target => True) :=
  Parse.givesAfter0 (reads0WordAhead modes "at") (atAhead =>
    match atAhead with
      | True => Parse.givesThen givesFixedFrom (at _ => givesTargetAfter self modes at nested outside bases)
      | False => Parse.givesDone byComputing)

theorem givesRewriteBody ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (column: Nat) (keyword: Comments)
    (rules: Rules) (target: Option (Comments, Expr))
    (nested: Nested self) (hasThen: Bool):
    Parse.Gives GoodItems (() => rewriteBody self modes column keyword rules target hasThen) Out :=
  match hasThen with
    | True => Parse.givesThen givesFixedFrom (thenKeyword _ =>
      Parse.givesThen (givesSelfAny self nested { modes, level = LevelThenBody }) (body _ =>
        Parse.givesDone byComputing))
    | False => Parse.givesDone byComputing

theorem givesRewriteThen ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (column: Nat) (keyword: Comments)
    (rules: Rules) (target: Option (Comments, Expr))
    (nested: Nested self):
    Parse.Gives GoodItems (() => rewriteThen self modes column keyword rules target) Out :=
  Parse.givesAfter0 (reads0StartsAt modes KwIn column) (old =>
    match old with
      | True => Parse.readsFatal
      | False => Parse.givesAfter0 (reads0StartsAt modes KwThen column) (hasThen =>
        givesRewriteBody self modes column keyword rules target nested hasThen))

theorem givesRewriteRulesOf ∀ (self: Goal → {Parse Item} Expr) (outer: Modes) (repeatedly: Bool)
    (nested: Nested self)
    (outside: OutsideBraced self)
    (bases: AtomBases self):
    Parse.Gives GoodItems (() => rewriteRulesOf self outer repeatedly) (rules => True) :=
  match repeatedly with
    | True => Parse.givesThen givesFixedFrom (opening _ =>
      Parse.givesThen (givesRuleSet self outer nested) (set _ => Parse.givesDone byComputing))
    | False => Parse.givesThen Parse.givesMark (here _ =>
      Parse.givesThen (givesRewriteRules self outer nested outside bases (here.left + 1) []) (rules _ =>
        Parse.givesDone byComputing))

theorem givesRewriteAfter ∀ (self: Goal → {Parse Item} Expr) (outer: Modes) (column: Nat) (keyword: Comments)
    (nested: Nested self)
    (outside: OutsideBraced self)
    (bases: AtomBases self):
    Parse.Gives GoodItems (() => rewriteAfter self outer column keyword) Out :=
  Parse.givesAfter0 (reads0RepeatedlyAhead outer) (repeatedly =>
    Parse.givesThen (givesRewriteRulesOf self outer repeatedly nested outside bases) (rules _ =>
      Parse.givesThen (givesRewriteTarget self outer nested outside bases) (target _ =>
        givesRewriteThen self outer column keyword rules target nested)))

theorem givesRewriteExpr ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (outside: OutsideBraced self)
    (bases: AtomBases self):
    Parse.Gives GoodItems (() => rewriteExpr self modes) Out :=
  Parse.givesThen givesColumnHere (column _ =>
    Parse.givesThen givesFixedFrom (keyword _ =>
      givesRewriteAfter self { modes | rewriteRule = None, rewriteAt = False } column keyword nested outside bases))

-- Walks: `byWalking [items] then t`, outside slice 1.

theorem givesWalkBody ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (keyword: Comments) (items: Expr)
    (nested: Nested self) (hasThen: Bool):
    Parse.Gives GoodItems (() => walkBody self modes keyword items hasThen) Out :=
  match hasThen with
    | True => Parse.givesThen givesFixedFrom (thenKeyword _ =>
      Parse.givesThen (givesSelfAny self nested { modes, level = LevelThenBody }) (body _ =>
        Parse.givesDone byComputing))
    | False => Parse.givesDone byComputing

theorem givesWalkFacts ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (column: Nat) (keyword: Comments) (items: Expr)
    (nested: Nested self):
    Parse.Gives GoodItems (() => walkFacts self modes column keyword items) Out :=
  match hasSpread items with
    | True => Parse.readsFatal
    | False => Parse.givesAfter0 (reads0StartsAt modes KwThen column) (hasThen =>
      givesWalkBody self modes keyword items nested hasThen)

theorem givesWalkExpr ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self):
    Parse.Gives GoodItems (() => walkExpr self modes) Out :=
  Parse.givesThen givesColumnHere (column _ =>
    Parse.givesThen givesFixedFrom (keyword _ =>
      Parse.givesThen (givesListExprAny self modes nested) (list _ =>
        givesWalkFacts self modes column keyword list nested)))
