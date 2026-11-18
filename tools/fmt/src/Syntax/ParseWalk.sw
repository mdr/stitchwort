--| The walk of slice 1's expression parser (docs/proposals/self-hosted-fmt-s1-sketch.md, ticket 16b): every parser
--| function from `expr` down to the atoms gives trees that are `Parsed1` (or `ArgParsed`, for an argument), given what
--| the parsers outside slice 1 give. `ParseProofs` has the operator ladder's folds and the look-aheads; this file has
--| the functions that read items by what they peek at, and ties the recursion together.

namespace Syntax.ParseWalk
import Std (Bool, DecEq, Eq, List, Nat, Option, Pair, Parse, Result, Text)
import Syntax (..)
import Fmt (..)
import Syntax.Proofs (..)
import Syntax.ParseProofs (..)

-- What each level of the recursion gives.

--| What `self` gives at a goal: an argument is an `argument1` (so a call's head and arguments are what `shaped1`
--| asks); every other level is `Parsed1` at the lowest level its trees can have in the slice.
def Level.floor: Level → Nat
  | LevelFull => 1
  | LevelInline => 1
  | LevelLogic => 4
  | LevelComparison => 6
  | LevelAppend => 12
  | LevelAdditive => 14
  | LevelMultiplicative => 16
  | LevelUnary => 18
  | LevelArgument => 18
  | LevelApp => 18
  | LevelThenBody => 1

--| A tree in the slice that is shaped, lexical and an argument: an atom, a bracket, or a prefix on one.
def ArgParsed (expr: Expr): Prop :=
  expr.within1 = True → expr.shaped1 = True ∧ expr.lexical1 = True ∧ expr.argument1 = True

def GoalParsed (goal: Goal) (expr: Expr): Prop := match goal.level with
  | LevelArgument => ArgParsed expr
  | LevelFull => Parsed1 1 expr
  | LevelInline => Parsed1 1 expr
  | LevelLogic => Parsed1 4 expr
  | LevelComparison => Parsed1 6 expr
  | LevelAppend => Parsed1 12 expr
  | LevelAdditive => Parsed1 14 expr
  | LevelMultiplicative => Parsed1 16 expr
  | LevelUnary => Parsed1 18 expr
  | LevelApp => Parsed1 18 expr
  | LevelThenBody => Parsed1 1 expr

--| `self` gives, at every goal, what `GoalParsed` says.
def Nested (self: Goal → {Parse Item} Expr): Prop :=
  ∀ (goal: Goal) => Parse.Gives GoodItems (() => self goal) (GoalParsed goal)

--| A tree outside the slice is parsed at every floor, and as an argument.
def Out (expr: Expr): Prop := expr.within1 = False

theorem outParsed ∀ (floor: Nat) [expr: Expr] (out: Out expr): Parsed1 floor expr := parsedOutside floor expr out

theorem outArg ∀ [expr: Expr] (out: Out expr): ArgParsed expr := within =>
  (Bool.falseNotTrue (rewrite out at within)).impossible

theorem argLevel ∀ (expr: Expr) (argument: expr.argument1 = True): 18 <= expr.level := match expr, argument with
  | Atom kind word, argument => arithmetic
  | Paren open inner close, argument => arithmetic
  | Tuple open items trailing close, argument => arithmetic
  | ListOf open items trailing close, argument => arithmetic
  | Prefix operator operand, argument => arithmetic
  | other, argument => (Bool.falseNotTrue argument).impossible

-- What the parsers outside slice 1 give: SW-4000 discharges these. Each is `Out` (the tree is outside the slice) or
-- `True` (the tree is wrapped in a node that is).

type Outside (self: Goal → {Parse Item} Expr) = {
  matches: ∀ (modes: Modes) (keyword: Word) => Parse.Gives GoodItems (() => matchExpr self modes keyword) Out,
  clauseLambdas: ∀ (modes: Modes) (keyword: Word) => Parse.Gives GoodItems
    (() => clauseLambda self modes keyword None ClauseMatches)
    Out,
  braceArguments: ∀ (modes: Modes) => Parse.Gives GoodItems (() => braceArgument self modes) Out,
  records: ∀ (modes: Modes) => Parse.Gives GoodItems (() => recordExpr self modes) Out,
  rests: ∀ (modes: Modes) (kind: Tok) => Parse.Gives GoodItems (() => atomRest self modes kind) Out,
  missings: ∀ (modes: Modes) => Parse.Gives GoodItems (() => atomMissing self modes) Out,
  parenOthers: ∀ (modes: Modes) (second third: Option Tok) => Parse.Gives GoodItems
    (() => parenOther self modes second third)
    Out,
  rightSections: ∀ (modes: Modes) (inside: Nat) => Parse.Gives GoodItems (() => rightSection self modes inside) Out,
  annotations: ∀ (inner: Modes) (open: Word) (first: Expr) => Parse.Gives GoodItems
    (() => annotated self inner open first)
    Out,
  namedArguments: ∀ (modes: Modes) (closer: Tok) (closeText: Text) => Parse.Gives GoodItems
    (() => namedArgument self modes closer closeText)
    Out
}

-- Combinators.

theorem givesOut ∀ [p: () → {Parse Item} Expr] (floor: Nat)
    (gives: Parse.Gives GoodItems p Out):
    Parse.Gives GoodItems p (Parsed1 floor) :=
  Parse.givesWeaken gives (value out => outParsed floor out)

theorem givesOutArg ∀ [p: () → {Parse Item} Expr]
    (gives: Parse.Gives GoodItems p Out):
    Parse.Gives GoodItems p ArgParsed :=
  Parse.givesWeaken gives (value out => outArg out)

--| A look-ahead that reads nothing, then `j` of what it found, from a mark: `j` is read from the mark after it,
--| which has the same items left.
theorem readsAtAfter0 ∀ [start: Parse.Mark Item] [p: () → {Parse Item} a]
    [j: a → {Parse Item} b] [spec: List Item → b → Prop]
    (first: Reads0 p)
    (fine: Parse.Fits Item GoodItems start.rest)
    (rest: ∀ (value: a) (after: Parse.Mark Item) => after.rest = start.rest
      → Parse.Fits Item GoodItems after.rest
      → Parse.ReadsAt after (() => j value) spec):
    Parse.ReadsAt start (() => j (p())) spec :=
  Parse.readsAtThen (first start fine) (read value after starts empty =>
    let same: after.rest = start.rest := rewrite empty at starts then starts.flipped
    Parse.readsAtWeaken (rest value after same (Parse.Fits.after fine starts)) (taken result done =>
      rewrite empty then done))

theorem givesAfter0 ∀ [p: () → {Parse Item} a] [j: a → {Parse Item} b] [holds: b → Prop]
    (first: Reads0 p)
    (rest: ∀ (value: a) => Parse.Gives GoodItems (() => j value) holds):
    Parse.Gives GoodItems (() => j (p())) holds :=
  start fine => readsAtAfter0 first fine (value after same fine2 => rest value after fine2)

theorem reads0MatchesBarAhead ∀ (modes: Modes): Reads0 (() => matchesBarAhead modes) :=
  reads0Then reads0Left (items => reads0Done (matchesBarOn modes items))

theorem minusBangSymbolic ∀ (kind: Tok) (is: (kind == Minus || kind == Bang) = True): kind.symbolic1 = True :=
  match kind, is with
    | Minus, is => byComputing
    | Bang, is => byComputing
    | other, is => (Bool.falseNotTrue is).impossible

--| A word read from a good item that is an operator of the alphabet is one `operatorTok` knows.
theorem operatorOfItem ∀ (item: Item)
    (good: GoodItem item)
    (symbolic: item.kind.symbolic1 = True):
    (operatorTok item.text).isSome = True :=
  rewrite operatorTokOfSpells item.kind item.text (good (symbolicWithin item.kind symbolic)) symbolic

theorem prefixParsed ∀ (operator: Word) (operand: Expr)
    (spelled: (operatorTok operator.text).isSome = True)
    (parsed: Parsed1 18 operand):
    Parsed1 18 (Prefix operator operand) :=
  within =>
    let (shaped, lexical, high) := parsed within
    (Both shaped high, Both spelled lexical, arithmetic)

-- Unary.

theorem readsUnaryNext ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (app: Parse.Gives GoodItems (() => app self modes) (Parsed1 18))
    (start: Parse.Mark Item) (item: Item) (later items: List Item)
    (shape: start.rest = [item, ..later])
    (fine: Parse.Fits Item GoodItems start.rest):
    Parse.ReadsAt start (() => unaryNext self modes item.kind items) (read value => Parsed1 18 value) :=
  match negative: item.kind == Minus && negativeNumeral items with
    | True => app start fine
    | False =>
      match signed: item.kind == Minus || item.kind == Bang with
        | True => readsAtBumpThen shape fine (after fits =>
          Parse.readsAtThen (nested { modes, level = LevelUnary } after fits) (read operand after2 starts parsed =>
            Parse.readsAtDone after2 _ _
              (prefixParsed item.leaf.word operand
                (operatorOfItem item (goodHead fine shape) (minusBangSymbolic item.kind signed))
                parsed)))
        | False => app start fine

theorem readsUnaryBar ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (outside: Outside self)
    (app: Parse.Gives GoodItems (() => app self modes) (Parsed1 18))
    (start: Parse.Mark Item) (item: Item) (later: List Item) (bar: Bool)
    (shape: start.rest = [item, ..later])
    (fine: Parse.Fits Item GoodItems start.rest):
    Parse.ReadsAt start (() => unaryBar self modes item.kind bar) (read value => Parsed1 18 value) :=
  match bar with
    | True => readsAtBumpThen [k := word => clauseLambda self modes word None ClauseMatches] shape fine (after fits =>
      givesOut 18 (outside.clauseLambdas modes item.leaf.word) after fits)
    | False =>
      readsAtAfter0
        [p := () => left()]
        [j := found => unaryNext self modes item.kind found]
        reads0Left
        fine
        (found after same fits =>
          readsUnaryNext self modes nested app after item later found (rewrite same then shape) fits)

theorem givesUnarySome ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (outside: Outside self)
    (app: Parse.Gives GoodItems (() => app self modes) (Parsed1 18))
    (start: Parse.Mark Item) (item: Item) (later: List Item)
    (shape: start.rest = [item, ..later])
    (fine: Parse.Fits Item GoodItems start.rest):
    Parse.ReadsAt start (() => unarySome self modes item.kind) (read value => Parsed1 18 value) :=
  match isMatch: item.kind == KwMatch with
    | True => readsAtBumpThen shape fine (after fits => givesOut 18 (outside.matches modes item.leaf.word) after fits)
    | False =>
      readsAtAfter0
        [p := () => matchesBarAhead modes]
        [j := bar => unaryBar self modes item.kind bar]
        (reads0MatchesBarAhead modes)
        fine
        (bar after same fits =>
          readsUnaryBar self modes nested outside app after item later bar (rewrite same then shape) fits)

theorem givesUnary ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (outside: Outside self)
    (app: Parse.Gives GoodItems (() => app self modes) (Parsed1 18)):
    Parse.Gives GoodItems (() => unary self modes) (Parsed1 18) :=
  readsInPeeked modes
    (seen => unaryOn self modes seen) _
    (start fine stops => app start fine)
    (start item later shape fine stopped => givesUnarySome self modes nested outside app start item later shape fine)

-- Application.

theorem reads0Offset: Reads0 (() => offset()) := reads0Mark (here => here.offset)

theorem argsParsed ∀ (args: List Expr)
    (parsed: List.All ArgParsed args)
    (within: allWithin1 args = True):
    allShaped1 args = True ∧ allLexical1 args = True ∧ args.all Expr.argument1 = True :=
  match args, parsed, within with
    | [], parsed, within => (byComputing, byComputing, byComputing)
    | [first, ..rest], (firstParsed, restParsed), (Both firstWithin restWithin) =>
      let (firstShaped, firstLexical, firstArgument) := firstParsed firstWithin
      let (restShaped, restLexical, restArgument) := argsParsed rest restParsed restWithin
      (Both firstShaped restShaped, Both firstLexical restLexical, Both firstArgument restArgument)

--| A call is parsed: an argument head and arguments after it, at least one.
theorem appParsed ∀ (head first: Expr) (more: List Expr)
    (headParsed: ArgParsed head)
    (firstParsed: ArgParsed first)
    (moreParsed: List.All ArgParsed more):
    Parsed1 18 (App head [first, ..more]) :=
  within =>
    let (headWithin, argsWithin) := within
    let (headShaped, headLexical, headArgument) := headParsed headWithin
    let (argsShaped, argsLexical, argsArgument) := argsParsed [first, ..more] (firstParsed, moreParsed) argsWithin
    (Both headArgument (Both headShaped (Both argsArgument argsShaped)), Both headLexical argsLexical, arithmetic)

theorem argParsedParsed ∀ [expr: Expr] (parsed: ArgParsed expr): Parsed1 18 expr := within =>
  let (shaped, lexical, argument) := parsed within
  (shaped, lexical, argLevel expr argument)

theorem givesOfReads0 ∀ [p: () → {Parse Item} a] (reads: Reads0 p): Parse.Gives GoodItems p (value => True) :=
  start fine => Parse.readsAtWeaken (reads start fine) (read value empty => byComputing)

theorem givesArgumentBrace ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (outside: Outside self) (brace: Bool):
    Parse.Gives GoodItems (() => argumentBrace self modes brace) ArgParsed :=
  match brace with
    | True => givesOutArg (outside.braceArguments modes)
    | False => nested { modes, level = LevelArgument }

theorem givesArgumentAt ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (outside: Outside self) (items: List Item):
    Parse.Gives GoodItems (() => argumentAt self modes items) ArgParsed :=
  match sectionLineAt modes items with
    | True => Parse.readsFatal _ _
    | False =>
      givesAfter0
        [p := () => modes.at Upper && isSome LBrace (modes.peekAt 1)]
        [j := brace => argumentBrace self modes brace]
        (reads0Then [p := () => modes.at Upper] (reads0At modes Upper) (upper =>
          match upper with
            | True => reads0Then [p := () => modes.peekAt 1] (reads0PeekAt modes 1) (found => reads0Done _)
            | False => reads0Done False))
        (brace => givesArgumentBrace self modes nested outside brace)

theorem givesArgument ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (outside: Outside self):
    Parse.Gives GoodItems (() => argument self modes) ArgParsed :=
  givesAfter0 [p := () => left()] [j := items => argumentAt self modes items] reads0Left (items =>
    givesArgumentAt self modes nested outside items)

theorem givesArguments ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (outside: Outside self):
    Parse.Gives GoodItems (() => arguments self modes) (List.All ArgParsed) :=
  Parse.givesLoop
    (givesAfter0
      [p := () => startsAtom modes]
      [j := starts => argumentStep self modes starts]
      (reads0StartsAtom modes)
      (starts =>
        match starts with
          | True => Parse.givesThen (givesArgument self modes nested outside) (value parsed => Parse.givesDone parsed)
          | False => Parse.givesDone byComputing))

theorem givesAppliedTo ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (outside: Outside self) (head: Expr)
    (headParsed: ArgParsed head):
    Parse.Gives GoodItems (() => appliedTo self modes head) (Parsed1 18) :=
  Parse.givesThen (givesArgument self modes nested outside) (first firstParsed =>
    Parse.givesThen (givesArguments self modes nested outside) (more moreParsed =>
      Parse.givesDone (appParsed head first more headParsed firstParsed moreParsed)))

theorem sectionedParsed ∀ (section: Bool) (applied: Expr)
    (parsed: Parsed1 18 applied):
    Parsed1 18 (sectioned section applied) :=
  match section with
    | True => parsedOutside 18 _ byComputing
    | False => parsed

--| `atom_base` gives an argument: what the base is for each of `atomBase`'s modes.
def AtomBases (self: Goal → {Parse Item} Expr): Prop :=
  ∀ (modes: Modes) => Parse.Gives GoodItems (() => atomBase self modes) ArgParsed

theorem givesAtomArgument ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (head: Bool)
    (outside: Outside self)
    (bases: AtomBases self):
    Parse.Gives GoodItems (() => atom self modes head) ArgParsed :=
  givesAtom ArgParsed
    (value out => outArg out)
    self
    modes
    head
    (bases modes)
    (Parse.givesWeaken (outside.records modes) (value out => byComputing))

theorem givesAppEnd ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (outside: Outside self)
    (section: Bool) (head: Expr) (applies: Bool)
    (headParsed: ArgParsed head):
    Parse.Gives GoodItems (() => appEnd self modes section head applies) (Parsed1 18) :=
  match applies with
    | True =>
      Parse.givesThen
        [p := () => appliedTo self modes head]
        [j := applied => sectioned section applied]
        (givesAppliedTo self modes nested outside head headParsed)
        (applied appliedParsed => Parse.givesDone (sectionedParsed section applied appliedParsed))
    | False => Parse.givesDone (sectionedParsed section head (argParsedParsed headParsed))

theorem givesAppCalls ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (outside: Outside self)
    (section: Bool) (head: Expr)
    (headParsed: ArgParsed head):
    Parse.Gives GoodItems (() => appCalls self modes section head) (Parsed1 18) :=
  givesAfter0
    [p := () => startsAtom modes]
    [j := applies => appEnd self modes section head applies]
    (reads0StartsAtom modes)
    (applies => givesAppEnd self modes nested outside section head applies headParsed)

theorem givesAppHead ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (outside: Outside self)
    (bases: AtomBases self) (section: Bool):
    Parse.Gives GoodItems (() => appHead self modes section) (Parsed1 18) :=
  Parse.givesThen
    [p := () => atom self modes True]
    [j := head => appCalls self modes section head]
    (givesAtomArgument self modes True outside bases)
    (head headParsed => givesAppCalls self modes nested outside section head headParsed)

theorem givesAppAt ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (outside: Outside self)
    (bases: AtomBases self) (start: Nat):
    Parse.Gives GoodItems (() => appAt self modes start) (Parsed1 18) :=
  givesAfter0
    [p := () => modes.at Dot && modes.sectionHead != Some start]
    [j := section => appHead self modes section]
    (reads0Then [p := () => modes.at Dot] (reads0At modes Dot) (dot => reads0Done _))
    (section => givesAppHead self modes nested outside bases section)

theorem givesApp ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (outside: Outside self)
    (bases: AtomBases self):
    Parse.Gives GoodItems (() => app self modes) (Parsed1 18) :=
  givesAfter0 [p := () => offset()] [j := start => appAt self modes start] reads0Offset (start =>
    givesAppAt self modes nested outside bases start)

-- The atoms.

theorem givesFailName ∀ (modes: Modes) (what: Text) [holds: a → Prop]:
    Parse.Gives GoodItems (() => modes.failName what) holds :=
  givesAfter0 [p := () => left()] [j := items => modes.failNameOn what items] reads0Left (items =>
    match items with
      | [item, ..rest] =>
        match keywordHere modes item with
          | True => Parse.readsFatal _ _
          | False => givesFail modes what
      | [] => givesFail modes what)

theorem wordWithinWithin ∀ (kind: Tok) (word: kind.wordWithin1 = True): kind.within1 = True := match kind, word with
  | Lower, word => byComputing
  | Upper, word => byComputing
  | Num, word => byComputing
  | Float, word => byComputing
  | other, word => (Bool.falseNotTrue word).impossible

theorem wordLexesAs ∀ (word: Word) (kind: Tok) (lexes: LexesAs word.text kind): word.lexesAs kind = True :=
  rewrite lexes then Both (DecEq.refl word.text) (DecEq.refl kind)

--| The word of a good item of the alphabet, as the atom of its kind.
theorem atomParsed ∀ (item: Item) (good: GoodItem item): ArgParsed (Atom item.kind item.leaf.word) := within =>
  (
    within,
    wordLexesAs item.leaf.word item.kind
      (lexesAsSpells item.kind item.text (good (wordWithinWithin item.kind within)) (mayFollowEnd item.kind item.text)),
    byComputing
  )

theorem readsWordAtom ∀ (start: Parse.Mark Item) (item: Item) (later: List Item)
    (shape: start.rest = [item, ..later])
    (fine: Parse.Fits Item GoodItems start.rest):
    Parse.ReadsAt start (() => wordAtom item.kind) (read value => ArgParsed value) :=
  readsAtBumpThen [k := word => Atom item.kind word] shape fine (after fits =>
    Parse.readsAtDone after _ _ (atomParsed item (goodHead fine shape)))

theorem prefixArgParsed ∀ (operator: Word) (operand: Expr)
    (spelled: (operatorTok operator.text).isSome = True)
    (parsed: ArgParsed operand):
    ArgParsed (Prefix operator operand) :=
  within =>
    let (shaped, lexical, argument) := parsed within
    (Both shaped (argLevel operand argument), Both spelled lexical, argument)

theorem readsPrefixAtom ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (negates: Bool) (start: Parse.Mark Item) (item: Item) (later: List Item)
    (shape: start.rest = [item, ..later])
    (symbolic: item.kind.symbolic1 = True)
    (fine: Parse.Fits Item GoodItems start.rest):
    Parse.ReadsAt start (() => prefixAtom self modes negates) (read value => ArgParsed value) :=
  match negates with
    | True => readsAtBumpThen shape fine (after fits =>
      Parse.readsAtThen (nested { modes, level = LevelArgument } after fits) (read operand after2 starts parsed =>
        Parse.readsAtDone after2 _ _
          (prefixArgParsed item.leaf.word operand (operatorOfItem item (goodHead fine shape) symbolic) parsed)))
    | False => givesFailName modes _ start fine

--| `readsAtBumpThen`, with the items left after the `bump` known: the ones after the item.
theorem readsAtBumpAfter ∀ [start: Parse.Mark Item] [item: Item] [later: List Item]
    [k: Word → {Parse Item} b] [holds: b → Prop]
    (shape: start.rest = [item, ..later])
    (fine: Parse.Fits Item GoodItems start.rest)
    (rest: ∀ (after: Parse.Mark Item) => after.rest = later
      → Parse.Fits Item GoodItems after.rest
      → Parse.ReadsAt after (() => k item.leaf.word) (read value => holds value)):
    Parse.ReadsAt start (() => k (bump())) (read value => holds value) :=
  Parse.readsAtThen (readsAtBump shape) (read word after starts (Both single same) =>
    let joined: [item, ..later] = [item, ..after.rest] := Eq.trans shape.flipped (rewrite single at starts then starts)
    rewrite same then
      rest after (List.consInjective item later after.rest joined).flipped (Parse.Fits.after fine starts))

theorem readsAtLeft ∀ (start: Parse.Mark Item):
    Parse.ReadsAt start (() => left()) (read value => read = [] ∧ value = start.rest) :=
  total state value after here honest h =>
    let same: (state.at.rest, state.at) = (value, after) := Result.okInjective h
    let valueSame: state.at.rest = value := Pair.mkInjectiveFst same
    let atSame: state.at = after := Pair.mkInjectiveSnd same
    let afterStart: after = start := Eq.trans atSame.flipped here
    Witness []
      (Both
        (rewrite afterStart)
        (Both (rewrite afterStart then honest) (Both byComputing (rewrite <- valueSame, here))))

--| `left()` then `j` of the items left, from a mark; `j` is read from the mark after it, which has the same items.
theorem readsAtAfterLeft ∀ [start: Parse.Mark Item] [j: List Item → {Parse Item} b] [spec: List Item → b → Prop]
    (fine: Parse.Fits Item GoodItems start.rest)
    (rest: ∀ (after: Parse.Mark Item) => after.rest = start.rest
      → Parse.Fits Item GoodItems after.rest
      → Parse.ReadsAt after (() => j start.rest) spec):
    Parse.ReadsAt start (() => j (left())) spec :=
  Parse.readsAtThen (readsAtLeft start) (read value after starts (Both empty same) =>
    let tail: after.rest = start.rest := rewrite empty at starts then starts.flipped
    Parse.readsAtWeaken (rewrite same then rest after tail (Parse.Fits.after fine starts)) (taken result done =>
      rewrite empty then done))

theorem readsNegativeNumber ∀ (start: Parse.Mark Item) (minus number: Item) (later: List Item)
    (shape: start.rest = [minus, number, ..later])
    (isMinus: minus.kind = Minus)
    (fine: Parse.Fits Item GoodItems start.rest):
    Parse.ReadsAt start (() => negativeNumber()) (read value => ArgParsed value) :=
  readsAtBumpAfter [k := word => numberAfter word left()] shape fine (after tail fits =>
    readsAtAfterLeft [j := items => numberAfter minus.leaf.word items] fits (after2 same fits2 =>
      rewrite tail then
        readsAtBumpThen
          [k := word => Prefix minus.leaf.word (Atom number.kind word)]
          (rewrite same, tail)
          fits2
          (after3 fits3 =>
            Parse.readsAtDone after3
              (Prefix minus.leaf.word (Atom number.kind number.leaf.word)) _
              (prefixArgParsed minus.leaf.word
                (Atom number.kind number.leaf.word)
                (operatorOfItem minus (goodHead fine shape) (rewrite isMinus))
                (atomParsed number (goodHead fits2 (rewrite same, tail)))))))

theorem minusSymbolic ∀ (kind: Tok) (is: kind = Minus): kind.symbolic1 = True := rewrite is

theorem bangSymbolic ∀ (kind: Tok) (is: kind = Bang): kind.symbolic1 = True := rewrite is

theorem readsNegativeAtomOn ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (items: List Item) (start: Parse.Mark Item) (item: Item) (later: List Item)
    (shape: start.rest = [item, ..later])
    (found: items = start.rest)
    (isMinus: item.kind = Minus)
    (fine: Parse.Fits Item GoodItems start.rest):
    Parse.ReadsAt start (() => negativeAtomOn self modes items) (read value => ArgParsed value) :=
  match negative: negativeNumeral items with
    | True =>
      let (minus, number, rest, split, minusKind, numberKind) := negativeNumeralKinds items negative
      readsNegativeNumber start minus number rest (rewrite <- found then split) minusKind fine
    | False =>
      readsPrefixAtom self modes nested
        (argumentMinus items)
        start
        item
        later
        shape
        (minusSymbolic item.kind isMinus)
        fine

theorem readsNegativeAtom ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (start: Parse.Mark Item) (item: Item) (later: List Item)
    (shape: start.rest = [item, ..later])
    (isMinus: item.kind = Minus)
    (fine: Parse.Fits Item GoodItems start.rest):
    Parse.ReadsAt start (() => negativeAtom self modes) (read value => ArgParsed value) :=
  readsAtAfterLeft [j := items => negativeAtomOn self modes items] fine (after same fits =>
    readsNegativeAtomOn self modes nested start.rest after item later
      (rewrite same then shape)
      same.flipped
      isMinus
      fits)

-- Comma lists.

theorem commaEnd ∀ (holds: a → Prop) (current: a) (found: List a) (currentHolds: holds current)
    (foundHolds: List.All holds found):
    List.All holds [current, ..found].reverse ∧ found.length + 1 <= [current, ..found].reverse.length :=
  (
    List.allReverse holds [current, ..found] (currentHolds, foundHolds),
    arithmetic [List.lengthReverse [current, ..found]]
  )

--| The items of a comma list all hold, and there are at least as many as read so far.
theorem givesCommaListFrom ∀ (modes: Modes) (ends: Nat → {Parse Item} Bool)
    (next: () → {Parse Item} a) (holds: a → Prop)
    (endsGives: ∀ (count: Nat) => Parse.Gives GoodItems (() => ends count) (stop => True))
    (nextGives: Parse.Gives GoodItems next holds)
    (fuel count: Nat) (current: a) (found: List a) (currentHolds: holds current)
    (foundHolds: List.All holds found):
    Parse.Gives GoodItems (() => commaListFrom fuel modes ends next count current found) (pair =>
      List.All holds pair.fst ∧ found.length + 1 <= pair.fst.length) :=
  givesAfter0
    [p := () => modes.peek]
    [j := seen => commaListOn fuel modes ends next count current found seen]
    (reads0Peek modes)
    (seen =>
      match fuel, seen with
        | Succ more, Some kind =>
          match isComma: kind == Comma with
            | True =>
              Parse.givesThen
                [p := () => bump()]
                [j := comma => commaListAfter more modes ends next count [current, ..found] (ends count)]
                givesBump
                (comma _ =>
                  Parse.givesThen
                    [p := () => ends count]
                    [j := stop => commaListAfter more modes ends next count [current, ..found] stop]
                    (endsGives count)
                    (stop _ =>
                      match stop with
                        | True => Parse.givesDone (commaEnd holds current found currentHolds foundHolds)
                        | False =>
                          Parse.givesThen
                            [p := () => next()]
                            [j := value => commaListFrom more modes ends next (count + 1) value [current, ..found]]
                            nextGives
                            (value valueHolds =>
                              Parse.givesWeaken
                                (givesCommaListFrom modes ends next holds endsGives nextGives more
                                  (count + 1)
                                  value
                                  [current, ..found]
                                  valueHolds
                                  (currentHolds, foundHolds))
                                (pair facts => (facts.left, arithmetic [facts.right])))))
            | False => Parse.givesDone (commaEnd holds current found currentHolds foundHolds)
        | Succ more, None => Parse.givesDone (commaEnd holds current found currentHolds foundHolds)
        | Zero, seen => Parse.givesDone (commaEnd holds current found currentHolds foundHolds))

-- Brackets.

theorem textIs ∀ (text expected: Text) (same: text = expected): (text == expected) = True :=
  rewrite same then DecEq.refl expected

theorem openSpelled ∀ (item: Item) (good: GoodItem item) (is: item.kind = LParen): item.leaf.word.text = "(" :=
  (rewrite is at good) byComputing

theorem bracketSpelled ∀ (item: Item) (good: GoodItem item) (is: item.kind = LBracket): item.leaf.word.text = "[" :=
  (rewrite is at good) byComputing

theorem closeSpelled ∀ (item: Item) (good: GoodItem item) (is: item.kind = RBracket): item.leaf.word.text = "]" :=
  (rewrite is at good) byComputing

theorem itemsParsed ∀ (floor: Nat) (items: List Expr)
    (parsed: List.All (Parsed1 floor) items)
    (within: allWithin1 items = True):
    allShaped1 items = True ∧ allLexical1 items = True :=
  match items, parsed, within with
    | [], parsed, within => (byComputing, byComputing)
    | [first, ..rest], (firstParsed, restParsed), (Both firstWithin restWithin) =>
      let (firstShaped, firstLexical, firstHigh) := firstParsed firstWithin
      let (restShaped, restLexical) := itemsParsed floor rest restParsed restWithin
      (Both firstShaped restShaped, Both firstLexical restLexical)

theorem parenParsed ∀ (open close: Word) (inner: Expr)
    (openText: open.text = "(")
    (closeText: close.text = ")")
    (parsed: Parsed1 1 inner):
    ArgParsed (Paren open inner close) :=
  within =>
    let (shaped, lexical, high) := parsed within
    (shaped, Both (textIs open.text "(" openText) (Both (textIs close.text ")" closeText) lexical), byComputing)

theorem tupleParsed ∀ (open close: Word) (items: List Expr) (trailing: Bool)
    (openText: open.text = "(")
    (closeText: close.text = ")")
    (long: 2 <= items.length)
    (parsed: List.All (Parsed1 1) items):
    ArgParsed (Tuple open items trailing close) :=
  within =>
    let (shaped, lexical) := itemsParsed 1 items parsed within
    (
      Both long shaped,
      Both (textIs open.text "(" openText) (Both (textIs close.text ")" closeText) lexical),
      byComputing
    )

theorem listParsed ∀ (open close: Word) (items: List Expr) (trailing: Bool)
    (openText: open.text = "[")
    (closeText: close.text = "]")
    (parsed: List.All (Parsed1 1) items):
    ArgParsed (ListOf open items trailing close) :=
  within =>
    let (shaped, lexical) := itemsParsed 1 items parsed within
    (shaped, Both (textIs open.text "[" openText) (Both (textIs close.text "]" closeText) lexical), byComputing)

theorem givesTupleClose ∀ (modes: Modes): Parse.Gives GoodItems (() => tupleClose modes) (word => word.text = ")") :=
  givesAfter0
    [p := () => modes.at Colon]
    [j := annotated => tupleCloseAfter modes annotated]
    (reads0At modes Colon)
    (annotated =>
      match annotated with
        | True => Parse.readsFatal _ _
        | False => givesExpect modes RParen _ byComputing)

theorem givesParenClose ∀ (inner: Modes) (open: Word) (first: Expr)
    (openText: open.text = "(")
    (parsed: Parsed1 1 first):
    Parse.Gives GoodItems (() => parenClose inner open first) ArgParsed :=
  Parse.givesThen
    [p := () => inner.expect RParen "`)`"]
    [j := close => Paren open first close]
    (givesExpect inner RParen _ byComputing)
    (close closeText => Parse.givesDone (parenParsed open close first openText closeText parsed))

theorem givesTupleEnd ∀ (self: Goal → {Parse Item} Expr) (inner: Modes) (open: Word) (items: List Expr) (trailing: Bool)
    (openText: open.text = "(")
    (long: 2 <= items.length)
    (parsed: List.All (Parsed1 1) items):
    Parse.Gives GoodItems (() => tupleEnd inner open (items, trailing)) ArgParsed :=
  Parse.givesThen
    [p := () => tupleClose inner]
    [j := close => Tuple open items trailing close]
    (givesTupleClose inner)
    (close closeText => Parse.givesDone (tupleParsed open close items trailing openText closeText long parsed))

theorem givesTupleEnds ∀ (inner: Modes) (count: Nat):
    Parse.Gives GoodItems (() => tupleEnds inner count) (stop => True) :=
  givesOfReads0 (reads0Then [p := () => inner.at RParen] (reads0At inner RParen) (found => reads0Done _))

theorem givesTupleSecond ∀ (self: Goal → {Parse Item} Expr) (inner: Modes) (open: Word) (first: Expr)
    (fuel: Nat) (second: Expr)
    (nested: Nested self)
    (openText: open.text = "(")
    (parsed: Parsed1 1 first)
    (secondParsed: Parsed1 1 second):
    Parse.Gives GoodItems (() => tupleSecond self inner open first fuel second) ArgParsed :=
  Parse.givesThen
    [p := () => commaListFrom fuel inner (tupleEnds inner) (() => full self inner) 2 second [first]]
    [j := pair => tupleEnd inner open pair]
    (givesCommaListFrom inner
      (tupleEnds inner)
      (() => full self inner)
      (Parsed1 1)
      (givesTupleEnds inner)
      (nested { modes = inner, level = LevelFull })
      fuel
      2
      second
      [first]
      secondParsed
      (parsed, ()))
    (pair facts =>
      match pair with
        | (items, trailing) => givesTupleEnd self inner open items trailing openText facts.right facts.left)

theorem givesTupleRest ∀ (self: Goal → {Parse Item} Expr) (inner: Modes) (open: Word) (first: Expr)
    (nested: Nested self)
    (openText: open.text = "(")
    (parsed: Parsed1 1 first):
    Parse.Gives GoodItems (() => tupleRest self inner open first) ArgParsed :=
  Parse.givesThen
    [p := () => Parse.mark()]
    [j := here => tupleFuel self inner open first here.left]
    Parse.givesMark
    (here _ =>
      Parse.givesThen
        [p := () => bump()]
        [j := comma => tupleSecond self inner open first here.left (full self inner)]
        givesBump
        (comma _ =>
          Parse.givesThen
            [p := () => full self inner]
            [j := second => tupleSecond self inner open first here.left second]
            (nested { modes = inner, level = LevelFull })
            (second secondParsed =>
              givesTupleSecond self inner open first here.left second nested openText parsed secondParsed)))

theorem givesBracketedFirst ∀ (self: Goal → {Parse Item} Expr) (inner: Modes) (open: Word) (first: Expr)
    (nested: Nested self)
    (outside: Outside self)
    (openText: open.text = "(")
    (parsed: Parsed1 1 first):
    Parse.Gives GoodItems (() => bracketedFirst self inner open first) ArgParsed :=
  readsInPeeked inner
    (seen => bracketedAfter self inner open first seen) _
    (start fine stops => givesParenClose inner open first openText parsed start fine)
    (start item later shape fine stopped =>
      match isComma: item.kind == Comma with
        | True => givesTupleRest self inner open first nested openText parsed start fine
        | False =>
          match isColon: item.kind == Colon with
            | True =>
              givesOutArg [p := () => annotated self inner open first] (outside.annotations inner open first) start fine
            | False => givesParenClose inner open first openText parsed start fine)

theorem givesBracketedTail ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (open: Word)
    (nested: Nested self)
    (outside: Outside self)
    (openText: open.text = "("):
    Parse.Gives GoodItems (() => bracketedTail self modes open) ArgParsed :=
  Parse.givesThen
    [p := () => full self modes.inBrackets]
    [j := first => bracketedFirst self modes.inBrackets open first]
    (nested { modes = modes.inBrackets, level = LevelFull })
    (first parsed => givesBracketedFirst self modes.inBrackets open first nested outside openText parsed)

theorem readsBracketed ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (outside: Outside self)
    (start: Parse.Mark Item) (item: Item) (later: List Item)
    (shape: start.rest = [item, ..later])
    (isParen: item.kind = LParen)
    (fine: Parse.Fits Item GoodItems start.rest):
    Parse.ReadsAt start (() => bracketed self modes) (read value => ArgParsed value) :=
  readsAtBumpThen [k := open => bracketedTail self modes open] shape fine (after fits =>
    givesBracketedTail self modes item.leaf.word nested outside
      (openSpelled item (goodHead fine shape) isParen)
      after
      fits)

theorem readsParenRest ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (outside: Outside self)
    (items: List Item) (start: Parse.Mark Item) (item: Item) (later: List Item)
    (shape: start.rest = [item, ..later])
    (isParen: item.kind = LParen)
    (fine: Parse.Fits Item GoodItems start.rest):
    Parse.ReadsAt start (() => parenRest self modes items) (read value => ArgParsed value) :=
  match rightOperator items with
    | Some inside =>
      givesOutArg [p := () => rightSection self modes inside] (outside.rightSections modes inside) start fine
    | None => readsBracketed self modes nested outside start item later shape isParen fine

theorem readsParenOn ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (outside: Outside self)
    (second third: Option Tok) (start: Parse.Mark Item) (item: Item) (later: List Item)
    (shape: start.rest = [item, ..later])
    (isParen: item.kind = LParen)
    (fine: Parse.Fits Item GoodItems start.rest):
    Parse.ReadsAt start (() => parenOn self modes second third) (read value => ArgParsed value) :=
  match parenOutside second third with
    | True =>
      givesOutArg [p := () => parenOther self modes second third] (outside.parenOthers modes second third) start fine
    | False => readsAtAfterLeft [j := items => parenRest self modes items] fine (after same fits =>
      readsParenRest self modes nested outside start.rest after item later (rewrite same then shape) isParen fits)

theorem readsParenAtom ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (outside: Outside self)
    (start: Parse.Mark Item) (item: Item) (later: List Item)
    (shape: start.rest = [item, ..later])
    (isParen: item.kind = LParen)
    (fine: Parse.Fits Item GoodItems start.rest):
    Parse.ReadsAt start (() => parenAtom self modes) (read value => ArgParsed value) :=
  readsAtAfter0
    [p := () => modes.peekAt 1]
    [j := second => parenSecond self modes second]
    (reads0PeekAt modes 1)
    fine
    (second after same fits =>
      readsAtAfter0
        [p := () => modes.peekAt 2]
        [j := third => parenOn self modes second third]
        (reads0PeekAt modes 2)
        fits
        (third after2 same2 fits2 =>
          readsParenOn self modes nested outside second third after2 item later
            (rewrite same2, same then shape)
            isParen
            fits2))

-- Lists.

theorem givesListSpread ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (dots: Word) (empty: Bool)
    (nested: Nested self):
    Parse.Gives GoodItems (() => listSpread self modes dots empty) (Parsed1 1) :=
  match empty with
    | True => Parse.readsFatal _ _
    | False =>
      Parse.givesThen
        [p := () => full self modes]
        [j := value => Spread dots value]
        (nested { modes, level = LevelFull })
        (value valueParsed => Parse.givesDone (parsedOutside 1 _ byComputing))

theorem givesListItemAfter ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (spread: Bool)
    (nested: Nested self):
    Parse.Gives GoodItems (() => listItemAfter self modes spread) (Parsed1 1) :=
  match spread with
    | True =>
      Parse.givesThen
        [p := () => bump()]
        [j := dots => listSpread self modes dots (modes.at Comma || modes.at RBracket)]
        givesBump
        (dots _ =>
          givesAfter0
            [p := () => modes.at Comma || modes.at RBracket]
            [j := empty => listSpread self modes dots empty]
            (reads0Then [p := () => modes.at Comma] (reads0At modes Comma) (comma =>
              match comma with
                | True => reads0Done True
                | False => reads0At modes RBracket))
            (empty => givesListSpread self modes dots empty nested))
    | False => nested { modes, level = LevelFull }

theorem givesListItem ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self):
    Parse.Gives GoodItems (() => listItem self modes) (Parsed1 1) :=
  givesAfter0
    [p := () => modes.at DotDot]
    [j := spread => listItemAfter self modes spread]
    (reads0At modes DotDot)
    (spread => givesListItemAfter self modes spread nested)

theorem givesListItemsEnd ∀ (self: Goal → {Parse Item} Expr) (inner: Modes) (open: Word)
    (items: List Expr) (trailing: Bool)
    (openText: open.text = "[")
    (parsed: List.All (Parsed1 1) items):
    Parse.Gives GoodItems (() => listItemsEnd self inner open (items, trailing)) ArgParsed :=
  Parse.givesThen
    [p := () => inner.expect RBracket "`,` or `]`"]
    [j := close => ListOf open items trailing close]
    (givesExpect inner RBracket _ byComputing)
    (close closeText => Parse.givesDone (listParsed open close items trailing openText closeText parsed))

theorem givesListItemsFrom ∀ (self: Goal → {Parse Item} Expr) (inner: Modes) (open: Word) (first: Expr)
    (nested: Nested self)
    (openText: open.text = "[")
    (firstParsed: Parsed1 1 first):
    Parse.Gives GoodItems (() => listItemsFrom self inner open first) ArgParsed :=
  Parse.givesThen
    [p := () => Parse.mark()]
    [j := here =>
      listItemsEnd self inner open
        (commaList (here.left + 1) inner (count => inner.at RBracket) (() => listItem self inner) first [])]
    Parse.givesMark
    (here _ =>
      Parse.givesThen
        [p := () => commaList (here.left + 1) inner (count => inner.at RBracket) (() => listItem self inner) first []]
        [j := pair => listItemsEnd self inner open pair]
        (givesCommaListFrom inner
          (count => inner.at RBracket)
          (() => listItem self inner)
          (Parsed1 1)
          (count => givesAt inner RBracket)
          (givesListItem self inner nested)
          (here.left + 1)
          1
          first
          []
          firstParsed
          ())
        (pair facts =>
          match pair with | (items, trailing) => givesListItemsEnd self inner open items trailing openText facts.left))

theorem givesListItems ∀ (self: Goal → {Parse Item} Expr) (inner: Modes) (open: Word)
    (nested: Nested self)
    (openText: open.text = "["):
    Parse.Gives GoodItems (() => listItems self inner open) ArgParsed :=
  Parse.givesThen
    [p := () => listItem self inner]
    [j := first => listItemsFrom self inner open first]
    (givesListItem self inner nested)
    (first firstParsed => givesListItemsFrom self inner open first nested openText firstParsed)

theorem givesListAfter ∀ (self: Goal → {Parse Item} Expr) (inner: Modes) (open: Word)
    (nested: Nested self)
    (openText: open.text = "["):
    Parse.Gives GoodItems (() => listPeek self inner open) ArgParsed :=
  readsInPeeked inner
    (seen => listAfter self inner open seen) _
    (start fine stops => givesListItems self inner open nested openText start fine)
    (start item later shaped fine stopped =>
      match isClose: item.kind == RBracket with
        | True => readsAtBumpThen [k := close => ListOf open [] False close] shaped fine (after fits =>
          Parse.readsAtDone after
            (ListOf open [] False item.leaf.word) _
            (listParsed open item.leaf.word [] False openText
              (closeSpelled item (goodHead fine shaped) (DecEq.sound isClose))
              ()))
        | False => givesListItems self inner open nested openText start fine)

theorem readsListExpr ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (start: Parse.Mark Item) (item: Item) (later: List Item)
    (shape: start.rest = [item, ..later])
    (isBracket: item.kind = LBracket)
    (fine: Parse.Fits Item GoodItems start.rest):
    Parse.ReadsAt start (() => listExpr self modes) (read value => ArgParsed value) :=
  readsAtBumpThen [k := open => listTail self modes open] shape fine (after fits =>
    givesListAfter self modes.inBrackets item.leaf.word nested
      (bracketSpelled item (goodHead fine shape) isBracket)
      after
      fits)

theorem readsBracketAt ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (outside: Outside self)
    (second third: Option Tok) (start: Parse.Mark Item) (item: Item) (later: List Item)
    (shape: start.rest = [item, ..later])
    (isBracket: item.kind = LBracket)
    (fine: Parse.Fits Item GoodItems start.rest):
    Parse.ReadsAt start (() => bracketAt self modes second third) (read value => ArgParsed value) :=
  match named: (isSome Lower second || isSome KwDecreasing second) && isSome ColonEq third with
    | True =>
      givesOutArg
        [p := () => namedArgument self modes RBracket "`]`"]
        (outside.namedArguments modes RBracket "`]`")
        start
        fine
    | False => readsListExpr self modes nested start item later shape isBracket fine

theorem readsBracketAtom ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (outside: Outside self)
    (start: Parse.Mark Item) (item: Item) (later: List Item)
    (shape: start.rest = [item, ..later])
    (isBracket: item.kind = LBracket)
    (fine: Parse.Fits Item GoodItems start.rest):
    Parse.ReadsAt start (() => bracketAtom self modes) (read value => ArgParsed value) :=
  readsAtAfter0
    [p := () => modes.peekAt 1]
    [j := second => bracketSecond self modes second]
    (reads0PeekAt modes 1)
    fine
    (second after same fits =>
      readsAtAfter0
        [p := () => modes.peekAt 2]
        [j := third => bracketAt self modes second third]
        (reads0PeekAt modes 2)
        fits
        (third after2 same2 fits2 =>
          readsBracketAt self modes nested outside second third after2 item later
            (rewrite same2, same then shape)
            isBracket
            fits2))

theorem readsAtomOf ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (outside: Outside self)
    (start: Parse.Mark Item) (item: Item) (later: List Item)
    (shape: start.rest = [item, ..later])
    (fine: Parse.Fits Item GoodItems start.rest):
    Parse.ReadsAt start (() => atomOf self modes item.kind) (read value => ArgParsed value) :=
  match isMinus: item.kind == Minus with
    | True => readsNegativeAtom self modes nested start item later shape (DecEq.sound isMinus) fine
    | False =>
      match isBang: item.kind == Bang with
        | True => readsAtAfterLeft [j := items => prefixBangOn self modes items] fine (after same fits =>
          readsPrefixAtom self modes nested
            (argumentBang start.rest)
            after
            item
            later
            (rewrite same then shape)
            (bangSymbolic item.kind (DecEq.sound isBang))
            fits)
        | False =>
          match isParen: item.kind == LParen with
            | True => readsParenAtom self modes nested outside start item later shape (DecEq.sound isParen) fine
            | False =>
              match isBracket: item.kind == LBracket with
                | True => readsBracketAtom self modes nested outside start item later shape (DecEq.sound isBracket) fine
                | False =>
                  match word: isWord item.kind with
                    | True => readsWordAtom start item later shape fine
                    | False =>
                      givesOutArg [p := () => atomRest self modes item.kind] (outside.rests modes item.kind) start fine

theorem givesAtomBases ∀ (self: Goal → {Parse Item} Expr)
    (nested: Nested self)
    (outside: Outside self):
    AtomBases self :=
  modes =>
    readsInPeeked modes
      (seen => atomBaseOn self modes seen) _
      (start fine stops => givesOutArg [p := () => atomMissing self modes] (outside.missings modes) start fine)
      (start item later shape fine stopped => readsAtomOf self modes nested outside start item later shape fine)
