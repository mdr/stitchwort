--| The walk of slice 1's expression parser, continued from `Syntax.ParseWalk`: heads of calls, unary, the operator
--| ladder from `unary` down, comparisons, `&&` and `||`, `->` and the rest of `expr_inline`, statements and blocks, and
--| the recursion that ties the levels together (`givesExpressionRule`).

namespace Syntax.ParseWalkLadder
import Std (Bool, DecEq, Eq, List, Nat, Option, Pair, Parse, Result, Text)
import Syntax (..)
import Fmt (..)
import Syntax.LexProofs (..)
import Syntax.ParseProofs (..)
import Syntax.ParseWalk (..)
import Fmt.Grammar1 (..)
import Fmt.Kinds (..)

-- Heads of calls.

theorem givesOutHead ∀ [p: () → {Parse Item} Expr]
    (gives: Parse.Gives GoodItems p Out):
    Parse.Gives GoodItems p HeadParsed :=
  Parse.givesWeaken gives (value out => inSliceOut (expr => expr.callHead = True) out)

--| A call's head that starts at no sign is an atom or a bracket: `atom_base` read no sign first.
theorem readsAtomHeadPlain ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (outside: OutsideAtoms self)
    (bases: AtomBases self)
    (start: Parse.Mark Item) (item: Item) (later: List Item)
    (shape: start.rest = [item, ..later])
    (plain: (item.kind == Minus || item.kind == Bang) = False)
    (fine: Parse.Fits Item GoodItems start.rest):
    Parse.ReadsAt start (() => atom self modes True) (read value => HeadParsed value) :=
  readsAtomFrom self modes True outside
    (read value => HeadParsed value)
    (read taken value parsed => parsed)
    (read value out => inSliceOut (expr => expr.callHead = True) out)
    start
    fine
    (here same fits =>
      Parse.readsAtWeaken (readsAtPrefix (bases modes here fits)) (read value (Both found (Witness rest whole)) =>
        let items: [item, ..later] = read ++ rest := calc [item, ..later]
          _ = start.rest := shape.flipped
          _ = here.rest := same.flipped
          _ = read ++ rest := whole
        atomHead (argReadPlain found items plain)))

--| A call's head at `-` on a numeral is that negative numeral.
theorem readsAtomHeadNegative ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (outside: OutsideAtoms self)
    (start: Parse.Mark Item) (item: Item) (later: List Item)
    (shape: start.rest = [item, ..later])
    (isMinus: item.kind = Minus)
    (negative: negativeNumeral start.rest = True)
    (stopped: modes.stops item = False)
    (fine: Parse.Fits Item GoodItems start.rest):
    Parse.ReadsAt start (() => atom self modes True) (read value => HeadParsed value) :=
  readsAtomFrom self modes True outside
    (read value => HeadParsed value)
    (read taken value parsed => parsed)
    (read value out => inSliceOut (expr => expr.callHead = True) out)
    start
    fine
    (here same fits =>
      readsAtPeeked modes
        (seen => atomBaseOn self modes seen) _
        here
        (Some Minus)
        (rewrite <- isMinus then peekSome modes here.rest item later (Eq.trans same shape) stopped)
        (readsNegativeAtomHead self modes here (rewrite same then negative) fits))

--| Where `modes.peek` sees nothing, `atom` reads no tree of the slice.
theorem readsAtomHeadNone ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (outside: OutsideAtoms self) (start: Parse.Mark Item)
    (none: peekIn modes 0 start.rest = None)
    (fine: Parse.Fits Item GoodItems start.rest):
    Parse.ReadsAt start (() => atom self modes True) (read value => HeadParsed value) :=
  readsAtomFrom self modes True outside
    (read value => HeadParsed value)
    (read taken value parsed => parsed)
    (read value out => inSliceOut (expr => expr.callHead = True) out)
    start
    fine
    (here same fits =>
      readsAtPeeked modes
        (seen => atomBaseOn self modes seen) _
        here
        None
        (rewrite same then none)
        (givesOutHead (outside.missings modes) here fits))

theorem peekNone ∀ (modes: Modes) (items: List Item)
    (stops: items = [] ∨ ∃ (item: Item) => ∃ (later: List Item) => items = [item, ..later] ∧ modes.stops item = True):
    peekIn modes 0 items = None :=
  match stops with
    | Inl empty => rewrite empty
    | Inr (Witness item (Witness later (Both shape stopped))) => rewrite shape, stopped

-- Unary.

theorem readsUnaryNext ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (outside: OutsideBraced self)
    (bases: AtomBases self)
    (start: Parse.Mark Item) (item: Item) (later items: List Item)
    (shape: start.rest = [item, ..later])
    (found: items = start.rest)
    (stopped: modes.stops item = False)
    (fine: Parse.Fits Item GoodItems start.rest):
    Parse.ReadsAt start (() => unaryNext self modes item.kind items) (read value => Parsed 18 value) :=
  match negative: item.kind == Minus && negativeNumeral items with
    | True => readsAppAt self modes nested outside start fine (here same fits =>
      readsAtomHeadNegative self modes outside.below here item later
        (Eq.trans same shape)
        (DecEq.sound (Bool.andLeft negative))
        (rewrite same, <- found then Bool.andRight negative)
        stopped
        fits)
    | False =>
      match signed: item.kind == Minus || item.kind == Bang with
        | True => readsAtBumpThen shape fine (after fits =>
          Parse.readsAtThen (nested { modes, level = LevelUnary } after fits) (read operand after2 starts parsed =>
            Parse.readsAtDone after2 _
              (prefixParsed item.leaf.word operand
                (operatorOfItem item (goodHead fine shape) (minusBangSymbolic item.kind signed))
                parsed)))
        | False => readsAppAt self modes nested outside start fine (here same fits =>
          readsAtomHeadPlain self modes outside.below bases here item later (Eq.trans same shape) signed fits)

theorem readsUnaryBar ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (outside: OutsideBraced self)
    (bases: AtomBases self)
    (start: Parse.Mark Item) (item: Item) (later: List Item) (bar: Bool)
    (shape: start.rest = [item, ..later])
    (stopped: modes.stops item = False)
    (fine: Parse.Fits Item GoodItems start.rest):
    Parse.ReadsAt start (() => unaryBar self modes item.kind bar) (read value => Parsed 18 value) :=
  match bar with
    | True => readsAtBumpThen shape fine (after fits =>
      givesOutIn (expr => 18 <= expr.level) (outside.below.clauseLambdas modes item.leaf.word) after fits)
    | False => readsAtAfterLeft fine (after same fits =>
      readsUnaryNext self modes nested outside bases after item later start.rest
        (rewrite same then shape)
        same.flipped
        stopped
        fits)

theorem givesUnarySome ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (outside: OutsideBraced self)
    (bases: AtomBases self)
    (start: Parse.Mark Item) (item: Item) (later: List Item)
    (shape: start.rest = [item, ..later])
    (stopped: modes.stops item = False)
    (fine: Parse.Fits Item GoodItems start.rest):
    Parse.ReadsAt start (() => unarySome self modes item.kind) (read value => Parsed 18 value) :=
  match isMatch: item.kind == KwMatch with
    | True => readsAtBumpThen shape fine (after fits =>
      givesOutIn (expr => 18 <= expr.level) (outside.below.matches modes item.leaf.word) after fits)
    | False =>
      Parse.readsAtAfter0 [p := () => matchesBarAhead modes] (reads0MatchesBarAhead modes) fine (bar after same fits =>
        readsUnaryBar self modes nested outside bases after item later bar (rewrite same then shape) stopped fits)

theorem givesUnary ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (outside: OutsideBraced self)
    (bases: AtomBases self):
    Parse.Gives GoodItems (() => unary self modes) (Parsed 18) :=
  readsInPeeked modes
    (seen => unaryOn self modes seen) _
    (start fine stops =>
      readsAppAt self modes nested outside start fine (here same fits =>
        readsAtomHeadNone self modes outside.below here (rewrite same then peekNone modes start.rest stops) fits))
    (start item later shape fine stopped =>
      givesUnarySome self modes nested outside bases start item later shape stopped fine)

-- The operator ladder, from `unary` down.

theorem givesMulOf ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (outside: OutsideBraced self)
    (bases: AtomBases self):
    Parse.Gives GoodItems (() => mulExpr self modes) (Parsed 16) :=
  givesMulExpr self modes (givesUnary self modes nested outside bases)

theorem givesAddOf ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (outside: OutsideBraced self)
    (bases: AtomBases self):
    Parse.Gives GoodItems (() => addExpr self modes) (Parsed 14) :=
  givesAddExpr self modes (givesMulOf self modes nested outside bases)

theorem givesAppendOf ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (outside: OutsideBraced self)
    (bases: AtomBases self):
    Parse.Gives GoodItems (() => appendExpr self modes) (Parsed 12) :=
  givesAppendExpr self modes
    (Parse.givesWeaken (givesAddOf self modes nested outside bases) (value parsed => parsedWeaken parsed byComputing))

theorem reads0HeadIndent: Reads0 (() => headIndent()) :=
  Parse.reads0Then reads0Left (items => Parse.reads0Done (headIndentOn items))

theorem reads0AtPipe ∀ (modes: Modes): Reads0 (() => atPipe modes) :=
  Parse.reads0Then reads0Left (items => Parse.reads0Done (atPipeOn modes items))

theorem givesRangeEnd ∀ (modes: Modes) (low: Expr) (operator: Word) (high: Expr):
    Parse.Gives GoodItems (() => rangeEnd modes low operator high) (Parsed 12) :=
  Parse.givesAfter0
    (Parse.reads0Then (reads0At modes DotDotLt) (lt =>
      match lt with
        | True => Parse.reads0Done True
        | False => reads0At modes DotDotEq))
    (chained =>
      match chained with
        | True => Parse.readsFatal
        | False => Parse.givesDone (parsedOutside 12 _ byComputing))

theorem givesRangeHigh ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (low: Expr)
    (nested: Nested self)
    (outside: OutsideBraced self)
    (bases: AtomBases self):
    Parse.Gives GoodItems (() => rangeHigh self modes low) (Parsed 12) :=
  byWalking [givesBump, givesAppendOf, givesRangeEnd]

theorem givesRangeOn ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (low: Expr)
    (nested: Nested self)
    (outside: OutsideBraced self)
    (bases: AtomBases self)
    (lowParsed: Parsed 12 low) (seen: Option Tok):
    Parse.Gives GoodItems (() => rangeOn self modes low seen) (Parsed 12) :=
  byWalking [givesRangeHigh]

theorem givesRangeOf ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (outside: OutsideBraced self)
    (bases: AtomBases self):
    Parse.Gives GoodItems (() => rangeExpr self modes) (Parsed 12) :=
  Parse.givesThen (givesAppendOf self modes nested outside bases) (low lowParsed =>
    Parse.givesAfter0 (reads0Peek modes) (seen => givesRangeOn self modes low nested outside bases lowParsed seen))

theorem givesPipedOf ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (outside: OutsidePiped self)
    (bases: AtomBases self):
    Parse.Gives GoodItems (() => pipedRange self modes) (Parsed 12) :=
  Parse.givesAfter0 reads0HeadIndent (indent =>
    Parse.givesThen (givesRangeOf self modes nested outside.below bases) (range rangeParsed =>
      Parse.givesAfter0 (reads0AtPipe modes) (pipe =>
        match pipe with
          | True => Parse.givesWeaken (outside.pipeChains modes indent range) (result chained =>
            match chained with
              | Inl same => rewrite same then rangeParsed
              | Inr out => inSliceOut (expr => 12 <= expr.level) out)
          | False => Parse.givesDone rangeParsed)))

-- Comparisons.

theorem cmpTakesGood ∀ (kind: Tok) (text: Text)
    (took: kind.isComparison = True):
    kind.symbolic1 = True ∧ (Spells kind text → leftNeeds InfixBinary text = 8 ∧ infixLevel InfixBinary text = 6) :=
  match kind, took with
    | Equals | EqEq | Lt | Gt, _ => (byComputing, same => Both (rewrite same) (rewrite same))
    | NotEq, took => (
      byComputing,
      spelled =>
        match spelled with
          | Inl same => Both (rewrite same) (rewrite same)
          | Inr same => Both (rewrite same) (rewrite same)
    )
    | Le, took => (
      byComputing,
      spelled =>
        match spelled with
          | Inl same => Both (rewrite same) (rewrite same)
          | Inr same => Both (rewrite same) (rewrite same)
    )
    | Ge, took => (
      byComputing,
      spelled =>
        match spelled with
          | Inl same => Both (rewrite same) (rewrite same)
          | Inr same => Both (rewrite same) (rewrite same)
    )
    | other, took => (Bool.falseNotTrue took).impossible

--| A comparison's operator word: spelled, and at the level of the table.
def CmpOperator (operator: Word): Prop :=
  (operatorTok operator.text).isSome = True
    ∧ leftNeeds InfixBinary operator.text = 8
    ∧ infixLevel InfixBinary operator.text = 6

theorem cmpOperatorOfItem ∀ (item: Item)
    (good: GoodItem item)
    (took: item.kind.isComparison = True):
    CmpOperator item.leaf.word :=
  let (symbolic, texts) := cmpTakesGood item.kind item.text took
  let (needs, own) := texts (good (symbolicWithin item.kind symbolic))
  (operatorOfItem item good symbolic, needs, own)

theorem compareParsed ∀ (lhs second: Expr) (operator: Word)
    (op: CmpOperator operator)
    (lhsParsed: Parsed 12 lhs)
    (secondParsed: Parsed 12 second):
    Parsed 6 (Infix InfixBinary lhs operator second) :=
  let (spelled, needs, own) := op
  infixParsedAt lhs second operator 6 12 12 lhsParsed secondParsed spelled
    (arithmetic [needs])
    (arithmetic [own])
    (same => arithmetic)
    (same => arithmetic [needs, own, same])
    own

theorem givesCmpChain ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (lhs: Expr) (kind: Tok)
    (operator: Word) (second: Expr)
    (outside: OutsideCompared self)
    (op: CmpOperator operator)
    (lhsParsed: Parsed 12 lhs)
    (secondParsed: Parsed 12 second) (seen: Option Tok):
    Parse.Gives GoodItems (() => cmpChain self modes lhs kind operator second seen) (Parsed 6) :=
  match seen with
    | Some next =>
      match chained: next.isComparison || next == KwIn || next == NotIn with
        | True => givesOutIn (expr => 6 <= expr.level) (outside.comparisonChains modes lhs kind operator second)
        | False => Parse.givesDone (compareParsed lhs second operator op lhsParsed secondParsed)
    | None => Parse.givesDone (compareParsed lhs second operator op lhsParsed secondParsed)

theorem givesCmpAfter ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (lhs: Expr) (kind: Tok)
    (operator: Word) (conditional: Bool)
    (nested: Nested self)
    (outside: OutsideCompared self)
    (bases: AtomBases self)
    (op: CmpOperator operator)
    (lhsParsed: Parsed 12 lhs):
    Parse.Gives GoodItems (() => cmpAfter self modes lhs kind operator conditional) (Parsed 6) :=
  match conditional with
    | True => givesOutIn (expr => 6 <= expr.level) (outside.cmpIfs modes lhs operator)
    | False => Parse.givesThen (givesPipedOf self modes nested outside.below bases) (second secondParsed =>
      Parse.givesAfter0 (reads0Peek modes) (seen =>
        givesCmpChain self modes lhs kind operator second outside op lhsParsed secondParsed seen))

theorem readsCmpCompare ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (lhs: Expr)
    (nested: Nested self)
    (outside: OutsideCompared self)
    (bases: AtomBases self)
    (lhsParsed: Parsed 12 lhs)
    (start: Parse.Mark Item) (item: Item) (later: List Item)
    (shape: start.rest = [item, ..later])
    (took: item.kind.isComparison = True)
    (fine: Parse.Fits Item GoodItems start.rest):
    Parse.ReadsAt start (() => cmpCompare self modes lhs item.kind) (read value => Parsed 6 value) :=
  readsAtBumpThen shape fine (after fits =>
    Parse.givesAfter0
      (reads0At modes KwIf)
      (conditional =>
        givesCmpAfter self modes lhs item.kind item.leaf.word conditional nested outside bases
          (cmpOperatorOfItem item (goodHead fine shape) took)
          lhsParsed)
      after
      fits)

theorem givesCmpPiped ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (first: Option Tok) (lhs: Expr)
    (nested: Nested self)
    (outside: OutsideCompared self)
    (bases: AtomBases self)
    (lhsParsed: Parsed 12 lhs):
    Parse.Gives GoodItems (() => cmpPiped self modes first lhs) (Parsed 6) :=
  readsInPeeked modes
    (seen => cmpOn self modes first lhs seen) _
    (start fine stops => Parse.givesDone (parsedWeaken lhsParsed byComputing) start fine)
    (start item later shape fine stopped =>
      match isMember: item.kind == KwIn || item.kind == NotIn with
        | True => givesOutIn (expr => 6 <= expr.level) (outside.memberships modes first lhs) start fine
        | False =>
          match isCmp: item.kind.isComparison with
            | True => readsCmpCompare self modes lhs nested outside bases lhsParsed start item later shape isCmp fine
            | False => Parse.givesDone (parsedWeaken lhsParsed byComputing) start fine)

theorem givesCmpOf ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (outside: OutsideCompared self)
    (bases: AtomBases self):
    Parse.Gives GoodItems (() => cmpExpr self modes) (Parsed 6) :=
  Parse.givesAfter0 [p := () => left()] reads0Left (items =>
    Parse.givesThen (givesPipedOf self modes nested outside.below bases) (lhs lhsParsed =>
      givesCmpPiped self modes (items.head.map Item.kind) lhs nested outside bases lhsParsed))

-- `&&` and `||`.

--| The text of a logic operator: `&&`, `∧`, `||` or `∨`.
def LogicText (text: Text): Prop := (text = "&&" ∨ text = "∧") ∨ (text = "||" ∨ text = "∨")

--| An operator and its operand, as `logicLinks` reads them: a spelled logic operator, and an operand at the level of
--| `cmp_expr`.
def LogicLink (link: (Word, Expr)): Prop :=
  (operatorTok link.fst.text).isSome = True ∧ LogicText link.fst.text ∧ Parsed 6 link.snd

theorem logicKind ∀ (kind: Tok) (text: Text)
    (spells: kind.within1 = True → Spells kind text)
    (is: (kind == AndAnd || kind == OrOr) = True):
    (operatorTok text).isSome = True ∧ LogicText text :=
  match kind, spells, is with
    | AndAnd, spells, is =>
      let spelled := spells byComputing
      (
        (rewrite operatorTokOfSpells AndAnd text spelled byComputing),
        match spelled with
          | Inl same => Inl (Inl same)
          | Inr same => Inl (Inr same)
      )
    | OrOr, spells, is =>
      let spelled := spells byComputing
      (
        (rewrite operatorTokOfSpells OrOr text spelled byComputing),
        match spelled with
          | Inl same => Inr (Inl same)
          | Inr same => Inr (Inr same)
      )
    | other, spells, is => (Bool.falseNotTrue is).impossible

theorem andLevels ∀ (text: Text)
    (logic: LogicText text)
    (tested: (text == "&&" || text == "∧") = True):
    leftNeeds InfixBinary text = 6 ∧ infixLevel InfixBinary text = 5 :=
  match logic with
    | Inl (Inl same | Inr same) => Both (rewrite same) (rewrite same)
    | Inr (Inl same | Inr same) => (Bool.falseNotTrue (rewrite same at tested)).impossible

theorem orLevels ∀ (text: Text)
    (logic: LogicText text)
    (tested: (text == "&&" || text == "∧") = False):
    leftNeeds InfixBinary text = 5 ∧ infixLevel InfixBinary text = 4 :=
  match logic with
    | Inl (Inl same | Inr same) => (Bool.falseNotTrue (rewrite <- tested, same)).impossible
    | Inr (Inl same | Inr same) => Both (rewrite same) (rewrite same)

--| The next link after a conjunction is an `||`.
def OrFirst: List (Word, Expr) → Prop
  | [(or, next), ..rest] => (or.text == "&&" || or.text == "∧") = False
  | other => True

--| What `conjunctionOf` gives: the conjunction is at the level of `&&`, the links left are all links, and the next
--| one (if any) is an `||`.
def ConjunctionOk (pair: (Expr, List (Word, Expr))): Prop :=
  Parsed 5 pair.fst ∧ List.All LogicLink pair.snd ∧ OrFirst pair.snd

theorem conjunctionCons ∀ (first: Expr) (and: Word) (pair: (Expr, List (Word, Expr)))
    (firstParsed: Parsed 6 first)
    (spelled: (operatorTok and.text).isSome = True)
    (needs: leftNeeds InfixBinary and.text = 6)
    (own: infixLevel InfixBinary and.text = 5)
    (ok: ConjunctionOk pair):
    ConjunctionOk (conjunctionJoin first and pair) :=
  match pair, ok with
    | (right, after), (rightParsed, afterOk, orFirst) => (
      infixParsedAt first right and 5 6 5 firstParsed
        (parsedWeaken rightParsed byComputing)
        spelled
        (arithmetic [needs])
        (arithmetic [own])
        (same => arithmetic [needs, same])
        (same => arithmetic [needs, own, same])
        own,
      afterOk,
      orFirst
    )

theorem conjunctionParsed ∀ (first: Expr) (links: List (Word, Expr))
    (firstParsed: Parsed 6 first)
    (ok: List.All LogicLink links):
    ConjunctionOk (conjunctionOf first links) :=
  match links, ok with
    | [], ok => (parsedWeaken firstParsed byComputing, ok, byComputing)
    | [(and, next), ..rest], (linkOk, restOk) =>
      match isAnd: (and.text == "&&" || and.text == "∧") with
        | True =>
          let (spelled, logic, nextParsed) := linkOk
          let (needs, own) := andLevels and.text logic isAnd
          conjunctionCons first and
            (conjunctionOf next rest)
            firstParsed
            spelled
            needs
            own
            (conjunctionParsed next rest nextParsed restOk)
        | False => (parsedWeaken firstParsed byComputing, (linkOk, restOk), isAnd)

theorem groupAfterZero ∀ (pair: (Expr, List (Word, Expr))) (ok: ConjunctionOk pair): Parsed 4 (groupAfter Zero pair) :=
  match pair, ok with
    | (conjunction, after), (conjunctionParsed, afterOk, orFirst) => parsedWeaken conjunctionParsed byComputing

theorem groupAfterSucc ∀ (more: Nat) (pair: (Expr, List (Word, Expr)))
    (ok: ConjunctionOk pair)
    (rest: ∀ (next: Expr) (links: List (Word, Expr)) => Parsed 6 next
      → List.All LogicLink links
      → Parsed 4 (groupLogic more next links)):
    Parsed 4 (groupAfter (Succ more) pair) :=
  match pair, ok with
    | (conjunction, after), (conjunctionParsed, afterOk, orFirst) =>
      match after, afterOk, orFirst with
        | [(or, next), ..links], (linkOk, linksOk), orFirst =>
          let (spelled, logic, nextParsed) := linkOk
          let (needs, own) := orLevels or.text logic orFirst
          infixParsedAt conjunction
            (groupLogic more next links)
            or
            4
            5
            4
            conjunctionParsed
            (rest next links nextParsed linksOk)
            spelled
            (arithmetic [needs])
            (arithmetic [own])
            (same => arithmetic [needs, same])
            (same => arithmetic [needs, own, same])
            own
        | [], afterOk, orFirst => parsedWeaken conjunctionParsed byComputing

theorem groupLogicParsed ∀ (fuel: Nat) (first: Expr) (links: List (Word, Expr))
    (firstParsed: Parsed 6 first)
    (ok: List.All LogicLink links):
    Parsed 4 (groupLogic fuel first links) :=
  match fuel with
    | Zero => groupAfterZero (conjunctionOf first links) (conjunctionParsed first links firstParsed ok)
    | Succ more =>
      groupAfterSucc more
        (conjunctionOf first links)
        (conjunctionParsed first links firstParsed ok)
        (following rest followingParsed restOk => groupLogicParsed more following rest followingParsed restOk)

theorem reads0QuantifierAhead ∀ (modes: Modes): Reads0 (() => quantifierAhead modes) :=
  Parse.reads0Then (reads0At modes KwExists) (found =>
    match found with
      | True => Parse.reads0Done True
      | False => reads0At modes KwForall)

theorem givesLogicOperand ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (operator: Word) (quantified: Bool)
    (nested: Nested self)
    (outside: OutsideCompared self)
    (bases: AtomBases self)
    (spelled: (operatorTok operator.text).isSome = True)
    (logic: LogicText operator.text):
    Parse.Gives GoodItems (() => logicOperand self modes operator quantified) (Parse.Perhaps LogicLink) :=
  match quantified with
    | True => Parse.givesThen (outside.quantifiers modes) (operand out =>
      Parse.givesDone (spelled, logic, inSliceOut (expr => 6 <= expr.level) out))
    | False => Parse.givesThen (givesCmpOf self modes nested outside bases) (operand parsed =>
      Parse.givesDone (spelled, logic, parsed))

theorem givesLogicOn ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (outside: OutsideCompared self)
    (bases: AtomBases self):
    Parse.Gives GoodItems (() => logicOn self modes modes.peek) (Parse.Perhaps LogicLink) :=
  readsInPeeked modes
    (seen => logicOn self modes seen) _
    (start fine stops => Parse.givesDone byComputing start fine)
    (start item later shape fine stopped =>
      match isLogic: item.kind == AndAnd || item.kind == OrOr with
        | True => readsAtBumpThen shape fine (after fits =>
          let (spelled, logic) := logicKind item.kind item.text (goodHead fine shape) isLogic
          Parse.givesAfter0
            (reads0QuantifierAhead modes)
            (quantified => givesLogicOperand self modes item.leaf.word quantified nested outside bases spelled logic)
            after
            fits)
        | False => Parse.givesDone byComputing start fine)

theorem givesLogicChain ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (first: Expr)
    (nested: Nested self)
    (outside: OutsideCompared self)
    (bases: AtomBases self)
    (firstParsed: Parsed 6 first):
    Parse.Gives GoodItems (() => logicChain self modes first) (Parsed 4) :=
  Parse.givesThen (Parse.givesLoop (givesLogicOn self modes nested outside bases)) (links ok =>
    Parse.givesDone (groupLogicParsed (links.length + 1) first links firstParsed ok))

-- `->`, sections and the rest of `expr_inline`.

theorem sectionedParsedAt ∀ (floor: Nat) (section: Bool) (value: Expr)
    (parsed: Parsed floor value):
    Parsed floor (sectioned section value) :=
  match section with
    | True => parsedOutside floor _ byComputing
    | False => parsed

theorem reads0AllowBrace ∀ (modes: Modes): Reads0 (() => allowBrace modes) :=
  Parse.reads0Then reads0Left (items => Parse.reads0Done (allowBraceOn modes items))

theorem reads0RowAhead ∀ (allowed: Modes): Reads0 (() => rowAhead allowed) :=
  Parse.reads0Then (reads0At allowed LBrace) (found =>
    Parse.reads0Then reads0Left (items => Parse.reads0Done (rowOn found items)))

theorem givesResultType ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (outside: OutsideIffed self):
    Parse.Gives GoodItems (() => resultType self modes) (Parsed 1) :=
  Parse.givesAfter0 (reads0AllowBrace modes) (allowed =>
    Parse.givesAfter0 (reads0RowAhead allowed) (row =>
      match row with
        | True => givesOutIn (expr => 1 <= expr.level) (outside.effectResults allowed)
        | False => nested { modes = allowed, level = LevelFull }))

theorem arrowParsed ∀ (left right: Expr) (arrow: Word)
    (spelled: (operatorTok arrow.text).isSome = True)
    (leftParsed: Parsed 4 left)
    (rightParsed: Parsed 1 right):
    Parsed 1 (Infix InfixArrow left arrow right) :=
  within =>
    let (leftWithin, rightWithin, operatorWithin) := within
    let (leftShaped, leftLexical, leftHigh) := leftParsed leftWithin
    let (rightShaped, rightLexical, rightHigh) := rightParsed rightWithin
    (
      Both leftShaped (Both rightShaped (Both (arithmetic [leftHigh]) (arithmetic [rightHigh]))),
      Both leftLexical (Both spelled rightLexical),
      arithmetic
    )

theorem givesArrowEnd ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (value: Expr) (arrow: Word)
    (nested: Nested self)
    (outside: OutsideIffed self)
    (spelled: (operatorTok arrow.text).isSome = True)
    (parsed: Parsed 4 value):
    Parse.Gives GoodItems (() => arrowEnd self modes value arrow) (Parsed 1) :=
  Parse.givesThen (givesResultType self modes nested outside) (right rightParsed =>
    Parse.givesDone (arrowParsed value right arrow spelled parsed rightParsed))

theorem arrowSymbolic ∀ (kind: Tok) (is: kind = Arrow): kind.symbolic1 = True := rewrite is

theorem givesOpSequence ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (value: Expr) (sequence: Bool)
    (nested: Nested self)
    (outside: OutsideIffed self)
    (parsed: Parsed 4 value):
    Parse.Gives GoodItems (() => opSequence self modes value sequence) (Parsed 1) :=
  readsInPeeked modes
    (seen => opEnd self modes value sequence seen) _
    (start fine stops => Parse.givesDone (parsedWeaken parsed byComputing) start fine)
    (start item later shape fine stopped =>
      match isArrow: item.kind == Arrow with
        | True => readsAtBumpThen shape fine (after fits =>
          givesArrowEnd self modes value item.leaf.word nested outside
            (operatorOfItem item (goodHead fine shape) (arrowSymbolic item.kind (DecEq.sound isArrow)))
            parsed
            after
            fits)
        | False =>
          match isSemi: item.kind == Semi && sequence with
            | True => givesOutIn (expr => 1 <= expr.level) (outside.semis modes value) start fine
            | False => Parse.givesDone (parsedWeaken parsed byComputing) start fine)

theorem reads0SequenceAhead ∀ (modes: Modes): Reads0 (() => sequenceAhead modes) :=
  Parse.reads0Then reads0Left (items => Parse.reads0Done (sequenceOn modes items))

theorem givesOpIffed ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (section: Bool) (iffed: Expr)
    (nested: Nested self)
    (outside: OutsideIffed self)
    (parsed: Parsed 4 iffed):
    Parse.Gives GoodItems (() => opIffed self modes section iffed) (Parsed 1) :=
  Parse.givesAfter0 (reads0SequenceAhead modes) (sequence =>
    givesOpSequence self modes
      (sectioned section iffed)
      sequence
      nested
      outside
      (sectionedParsedAt 4 section iffed parsed))

theorem givesOpLogic ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (section: Bool) (logic: Expr)
    (nested: Nested self)
    (outside: OutsideIffed self)
    (parsed: Parsed 4 logic):
    Parse.Gives GoodItems (() => opLogic self modes section logic) (Parsed 1) :=
  Parse.givesAfter0 [p := () => modes.at IffArrow] (reads0At modes IffArrow) (ahead =>
    Parse.givesThen
      [p := () => iffOf self modes logic ahead]
      [j := iffed => opIffed self modes section iffed]
      (match ahead with
        | True => givesOutIn (expr => 4 <= expr.level) (outside.iffs modes logic)
        | False => Parse.givesDone parsed)
      (iffed iffedParsed => givesOpIffed self modes section iffed nested outside iffedParsed))

theorem givesLogicAfter ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (compared: Expr)
    (nested: Nested self)
    (outside: OutsideCompared self)
    (bases: AtomBases self)
    (parsed: Parsed 6 compared):
    Parse.Gives GoodItems (() => logicAfter self modes compared) (Parsed 4) :=
  Parse.givesAfter0 [p := () => left()] reads0Left (items =>
    match andOrOn modes items with
      | True => givesLogicChain self modes compared nested outside bases parsed
      | False => Parse.givesDone (parsedWeaken parsed byComputing))

theorem givesOpCompared ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (section: Bool) (compared: Expr)
    (nested: Nested self)
    (outside: OutsideIffed self)
    (bases: AtomBases self)
    (parsed: Parsed 6 compared):
    Parse.Gives GoodItems (() => opCompared self modes section compared) (Parsed 1) :=
  Parse.givesThen (givesLogicAfter self modes compared nested outside.below bases parsed) (logic logicParsed =>
    givesOpLogic self modes section logic nested outside logicParsed)

theorem givesOpSection ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (start: Nat) (section: Bool)
    (nested: Nested self)
    (outside: OutsideIffed self)
    (bases: AtomBases self):
    Parse.Gives GoodItems (() => opSection self modes start section) (Parsed 1) :=
  Parse.givesThen
    (givesCmpOf self (if section then { modes | sectionHead = Some start } else modes) nested outside.below bases)
    (compared parsed => givesOpCompared self modes section compared nested outside bases parsed)

theorem givesOperatorExpr ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (outside: OutsideIffed self)
    (bases: AtomBases self):
    Parse.Gives GoodItems (() => operatorExpr self modes) (Parsed 1) :=
  Parse.givesAfter0 reads0Offset (start =>
    Parse.givesAfter0 (reads0At modes Dot) (section => givesOpSection self modes start section nested outside bases))

-- `expr_inline`.

theorem reads0LambdaHere ∀ (modes: Modes): Reads0 (() => lambdaHere modes) := Parse.reads0Then Parse.reads0Here (here =>
  Parse.reads0Then [p := () => left()] reads0Left (items => Parse.reads0Done (lambdaAhead modes (here.left + 1) items)))

theorem reads0LambdaResultHere ∀ (modes: Modes): Reads0 (() => lambdaResultHere modes) :=
  Parse.reads0Then Parse.reads0Here (here =>
    Parse.reads0Then [p := () => left()] reads0Left (items =>
      Parse.reads0Done (lambdaResultType modes (here.left + 1) False items)))

theorem reads0ImplicitHere ∀ (modes: Modes): Reads0 (() => implicitHere modes) :=
  Parse.reads0Then Parse.reads0Here (here =>
    Parse.reads0Then [p := () => left()] reads0Left (items =>
      Parse.reads0Then (reads0Peek modes) (seen => Parse.reads0Done (implicitOn (here.left + 1) items seen))))

theorem reads0PiHere ∀ (modes: Modes): Reads0 (() => piHere modes) := Parse.reads0Then reads0Left (items =>
  Parse.reads0Then (reads0Peek modes) (seen => Parse.reads0Done (piOn items seen)))

theorem givesExprPi ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (pi: Bool)
    (nested: Nested self)
    (outside: Outside self)
    (bases: AtomBases self):
    Parse.Gives GoodItems (() => exprPi self modes pi) (Parsed 1) :=
  match pi with
    | True => givesOutIn (expr => 1 <= expr.level) (outside.piExprs modes False)
    | False => givesOperatorExpr self modes nested outside.below bases

theorem givesExprImplicit ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (implicit: Bool)
    (nested: Nested self)
    (outside: Outside self)
    (bases: AtomBases self):
    Parse.Gives GoodItems (() => exprImplicit self modes implicit) (Parsed 1) :=
  match implicit with
    | True => givesOutIn (expr => 1 <= expr.level) (outside.piExprs modes True)
    | False => Parse.givesAfter0 (reads0PiHere modes) (pi => givesExprPi self modes pi nested outside bases)

theorem givesExprPlain ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (outside: Outside self)
    (bases: AtomBases self):
    Parse.Gives GoodItems (() => exprPlain self modes) (Parsed 1) :=
  Parse.givesAfter0 (reads0ImplicitHere modes) (implicit => givesExprImplicit self modes implicit nested outside bases)

theorem givesExprBinder ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (outside: Outside self)
    (bases: AtomBases self):
    Parse.Gives GoodItems (() => exprBinder self modes modes.peek) (Parsed 1) :=
  readsInPeeked modes
    (seen => exprBinder self modes seen) _
    (start fine stops => givesExprPlain self modes nested outside bases start fine)
    (start item later shape fine stopped =>
      match isQuantifier: item.kind == KwExists || item.kind == KwForall with
        | True =>
          givesOutIn
            [p := () => Syntax.quantifier self modes]
            (expr => 1 <= expr.level)
            (outside.below.below.quantifiers modes)
            start
            fine
        | False =>
          match isIf: item.kind == KwIf with
            | True =>
              givesOutIn
                [p := () => ifKeyword self modes]
                (expr => 1 <= expr.level)
                (outside.ifKeywords modes)
                start
                fine
            | False => givesExprPlain self modes nested outside bases start fine)

theorem givesExprResult ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (refused: Bool)
    (nested: Nested self)
    (outside: Outside self)
    (bases: AtomBases self):
    Parse.Gives GoodItems (() => exprResult self modes refused) (Parsed 1) :=
  match refused with
    | True => Parse.readsFatal
    | False => givesExprBinder self modes nested outside bases

theorem givesExprLambda ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (lambdas: Bool)
    (nested: Nested self)
    (outside: Outside self)
    (bases: AtomBases self):
    Parse.Gives GoodItems (() => exprLambda self modes lambdas) (Parsed 1) :=
  match lambdas with
    | True => givesOutIn (expr => 1 <= expr.level) (outside.lambdas modes)
    | False => Parse.givesAfter0 (reads0LambdaResultHere modes) (refused =>
      givesExprResult self modes refused nested outside bases)

theorem reads0WalkHere ∀ (modes: Modes): Reads0 (() => walkHere modes) :=
  Parse.reads0Mark (here => walkOn modes here.rest)

theorem givesExprWalk ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (walk: Bool)
    (nested: Nested self)
    (outside: Outside self)
    (bases: AtomBases self):
    Parse.Gives GoodItems (() => exprWalk self modes walk) (Parsed 1) :=
  match walk with
    | True => givesOutIn (expr => 1 <= expr.level) (outside.walks modes)
    | False =>
      Parse.givesAfter0 (reads0LambdaHere modes) (lambdas => givesExprLambda self modes lambdas nested outside bases)

theorem givesExprOther ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (outside: Outside self)
    (bases: AtomBases self):
    Parse.Gives GoodItems (() => exprOther self modes) (Parsed 1) :=
  Parse.givesAfter0 (reads0WalkHere modes) (walk => givesExprWalk self modes walk nested outside bases)

theorem givesExprInline ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (outside: Outside self)
    (bases: AtomBases self):
    Parse.Gives GoodItems (() => exprInline self modes) (Parsed 1) :=
  readsInPeeked modes
    (seen => exprInlineOn self modes seen) _
    (start fine stops => givesExprOther self modes nested outside bases start fine)
    (start item later shape fine stopped =>
      match keyword: startsKeywordExpr item.kind with
        | True => givesOutIn (expr => 1 <= expr.level) (outside.keywords modes item.kind keyword) start fine
        | False => givesExprOther self modes nested outside bases start fine)

-- Statements and blocks.

theorem givesStatementValue ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (outside: Outside self)
    (bases: AtomBases self):
    Parse.Gives GoodItems (() => statementValue self modes) StatementOk :=
  byWalking [givesExprInline]

theorem givesStatement ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (outside: Outside self)
    (bases: AtomBases self):
    Parse.Gives GoodItems (() => statement self modes) StatementOk :=
  readsInPeeked modes
    (seen => statementOn self modes seen) _
    (start fine stops => givesStatementValue self modes nested outside bases start fine)
    (start item later shape fine stopped =>
      match other: startsOtherStatement item.kind with
        | True => outside.statementOthers modes item.kind other start fine
        | False => givesStatementValue self modes nested outside bases start fine)

theorem givesBlockOffset ∀ (more: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes) (column: Nat) (many: Bool)
    (done: List Statement) (before: Nat) (next: Item) (now: Nat)
    (doneOk: List.All StatementOk done)
    (again: ∀ (found: List Statement) => List.All StatementOk found
      → Parse.Gives GoodItems (() => blockLines more self modes column many found) (List.All StatementOk)):
    Parse.Gives GoodItems (() => blockOffset more self modes column many done before next now) (List.All StatementOk) :=
  byWalking []

theorem givesBlockItems ∀ (more: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes) (column: Nat) (many: Bool)
    (done: List Statement) (before: Nat) (items: List Item)
    (doneOk: List.All StatementOk done)
    (again: ∀ (found: List Statement) => List.All StatementOk found
      → Parse.Gives GoodItems (() => blockLines more self modes column many found) (List.All StatementOk)):
    Parse.Gives GoodItems (() => blockItems more self modes column many done before items) (List.All StatementOk) :=
  match items with
    | [next, ..rest] => Parse.givesAfter0 reads0Offset (now =>
      givesBlockOffset more self modes column many done before next now doneOk again)
    | [] => Parse.givesDone doneOk

theorem givesBlockDone ∀ (more: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes) (column: Nat) (many: Bool)
    (found: List Statement) (before: Nat) (line: Statement)
    (foundOk: List.All StatementOk found)
    (lineOk: StatementOk line)
    (again: ∀ (found: List Statement) => List.All StatementOk found
      → Parse.Gives GoodItems (() => blockLines more self modes column many found) (List.All StatementOk)):
    Parse.Gives GoodItems (() => blockDone more self modes column many found before line) (List.All StatementOk) :=
  byWalking [givesBlockItems]

theorem givesBlockKind ∀ (more: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes) (column: Nat) (many: Bool)
    (found: List Statement) (before: Nat) (statementModes: Modes) (seen: Option Tok)
    (nested: Nested self)
    (outside: Outside self)
    (bases: AtomBases self)
    (foundOk: List.All StatementOk found)
    (again: ∀ (found: List Statement) => List.All StatementOk found
      → Parse.Gives GoodItems (() => blockLines more self modes column many found) (List.All StatementOk)):
    Parse.Gives GoodItems
      (() => blockKind more self modes column many found before statementModes seen)
      (List.All StatementOk) :=
  byWalking [givesStatement, givesBlockDone]

theorem givesBlockPeek ∀ (more: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes) (column: Nat) (many: Bool)
    (found: List Statement) (before: Nat) (statementModes: Modes)
    (nested: Nested self)
    (outside: Outside self)
    (bases: AtomBases self)
    (foundOk: List.All StatementOk found)
    (again: ∀ (found: List Statement) => List.All StatementOk found
      → Parse.Gives GoodItems (() => blockLines more self modes column many found) (List.All StatementOk)):
    Parse.Gives GoodItems
      (() => blockPeek more self modes column many found before statementModes)
      (List.All StatementOk) :=
  byWalking [givesBlockKind]

theorem givesBlockLine ∀ (more: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes) (column: Nat) (many: Bool)
    (found: List Statement) (before: Nat) (items: List Item)
    (nested: Nested self)
    (outside: Outside self)
    (bases: AtomBases self)
    (foundOk: List.All StatementOk found)
    (again: ∀ (found: List Statement) => List.All StatementOk found
      → Parse.Gives GoodItems (() => blockLines more self modes column many found) (List.All StatementOk)):
    Parse.Gives GoodItems (() => blockLine more self modes column many found before items) (List.All StatementOk) :=
  byWalking [givesBlockPeek]

theorem givesBlockLines ∀ (fuel: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes) (column: Nat)
    (many: Bool) (found: List Statement)
    (nested: Nested self)
    (outside: Outside self)
    (bases: AtomBases self)
    (foundOk: List.All StatementOk found):
    Parse.Gives GoodItems (() => blockLines fuel self modes column many found) (List.All StatementOk) :=
  match fuel with
    | Zero => Parse.givesDone foundOk
    | Succ more => Parse.givesAfter0 reads0Offset (before =>
      Parse.givesAfter0 reads0Left (items =>
        givesBlockLine more self modes column many found before items nested outside bases foundOk (again okAgain =>
          givesBlockLines more self modes column many again nested outside bases okAgain)))

theorem givesBlockResult ∀ (statements: List Statement)
    (ok: List.All StatementOk statements):
    Parse.Gives GoodItems (() => blockResult statements) (Parsed 1) :=
  match statements, ok with
    | [ExprStatement value], (valueOk, rest) => Parse.givesDone valueOk
    | [ExprStatement value, last, ..earlier], (valueOk, rest) =>
      match [last, ..earlier].reverse with
        | [first, ..others] => Parse.givesDone (parsedOutside 1 _ byComputing)
        | [] => Parse.givesDone valueOk
    | [LetStatement _, .._] | [LocalDef _ _ _, .._] | [], _ => Parse.readsFatal

theorem givesBlock ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (column: Nat) (many: Bool)
    (nested: Nested self)
    (outside: Outside self)
    (bases: AtomBases self):
    Parse.Gives GoodItems (() => block self modes column many) (Parsed 1) :=
  Parse.givesThen Parse.givesMark (here _ =>
    Parse.givesThen
      (givesBlockLines
        (here.left + 1)
        self
        (if many then { modes | limit = Some column, letValue = None } else { modes | limit = Some column })
        column
        many
        []
        nested
        outside
        bases
        ())
      (statements ok => givesBlockResult statements ok))

theorem givesExprRuns ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (item: Item) (limit: Nat) (runs: Bool)
    (nested: Nested self)
    (outside: Outside self)
    (bases: AtomBases self):
    Parse.Gives GoodItems (() => exprRuns self modes item limit runs) (Parsed 1) :=
  match runs with
    | True => Parse.givesAfter0 reads0Left (items =>
      match blockEnd modes.lines items.head with
        | Some ending => Parse.readsFatal
        | None => Parse.readsFatal)
    | False =>
      match same: item.leaf.token.column == limit with
        | True => givesBlock self modes item.leaf.token.column False nested outside bases
        | False => givesExprInline self modes nested outside bases

theorem givesExprBlock ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (item: Item)
    (nested: Nested self)
    (outside: Outside self)
    (bases: AtomBases self):
    Parse.Gives GoodItems (() => exprBlock self modes item) (Parsed 1) :=
  byWalking [givesBlock, givesExprRuns]

theorem givesExprOn ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (items: List Item)
    (nested: Nested self)
    (outside: Outside self)
    (bases: AtomBases self):
    Parse.Gives GoodItems (() => exprOn self modes items) (Parsed 1) :=
  match items with
    | [item, ..rest] =>
      match here: startsBlock modes item with
        | True => givesExprBlock self modes item nested outside bases
        | False => givesExprInline self modes nested outside bases
    | [] => givesExprInline self modes nested outside bases

theorem givesExprOf ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (outside: Outside self)
    (bases: AtomBases self):
    Parse.Gives GoodItems (() => expr self modes) (Parsed 1) :=
  byWalking [givesExprOn]

theorem givesThenBody ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (outside: Outside self)
    (bases: AtomBases self):
    Parse.Gives GoodItems (() => thenBody self modes) (Parsed 1) :=
  Parse.givesAfter0 reads0Left (items =>
    match items with
      | [next, ..rest] =>
        match here: next.leaf.token.lineStart
          && modes.allow != Some next.index
          && !modes.endsConstruct next
          && modes.limit == Some next.leaf.token.column with
          | True => givesBlock self modes next.leaf.token.column True nested outside bases
          | False => givesExprOf self modes nested outside bases
      | [] => givesExprOf self modes nested outside bases)

-- The recursion.

theorem givesLogicLevel ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (outside: OutsideCompared self)
    (bases: AtomBases self):
    Parse.Gives GoodItems (() => logicLevel self modes) (Parsed 4) :=
  Parse.givesThen (givesCmpOf self modes nested outside bases) (compared parsed =>
    givesLogicAfter self modes compared nested outside bases parsed)

--| One level of the expression parser reads what `GoalRead` says, given that `self` does at every goal and what the
--| parsers outside slice 1 give.
theorem givesExpressionRule ∀ (self: Goal → {Parse Item} Expr) (goal: Goal)
    (nested: Nested self)
    (outside: Outside self):
    Parse.ReadsIn GoodItems (() => expressionRule self goal) (GoalRead goal) :=
  let bases := givesAtomBases self nested outside.below.below.below.below.below
  match goal with
    | { modes, level } =>
      match level with
        | LevelFull => givesExprOf self modes nested outside bases
        | LevelInline => givesExprInline self modes nested outside bases
        | LevelLogic => givesLogicLevel self modes nested outside.below.below bases
        | LevelComparison => givesCmpOf self modes nested outside.below.below bases
        | LevelAppend => givesAppendOf self modes nested outside.below.below.below.below bases
        | LevelAdditive => givesAddOf self modes nested outside.below.below.below.below bases
        | LevelMultiplicative => givesMulOf self modes nested outside.below.below.below.below bases
        | LevelUnary => givesUnary self modes nested outside.below.below.below.below bases
        | LevelArgument => readsArgumentAtom self modes outside.below.below.below.below.below bases
        | LevelApp => givesAppAny self modes nested outside.below.below.below.below bases
        | LevelThenBody => givesThenBody self modes nested outside bases
