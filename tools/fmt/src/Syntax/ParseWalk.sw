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

--| A line of a block is good when it is an expression that is: `let`s and local definitions are outside the slice.
def StatementOk (statement: Statement): Prop := match statement with
  | ExprStatement value => Parsed1 1 value
  | other => True

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
    Out,
  memberships: ∀ (modes: Modes) (first: Option Tok) (element: Expr) => Parse.Gives GoodItems
    (() => membership self modes first element)
    Out,
  comparisonChains: ∀ (modes: Modes) (lhs: Expr) (kind: Tok) (operator: Word) (second: Expr) => Parse.Gives GoodItems
    (() => comparisonChain self modes lhs kind operator second)
    Out,
  cmpIfs: ∀ (modes: Modes) (lhs: Expr) (operator: Word) => Parse.Gives GoodItems
    (() => cmpIf self modes lhs operator)
    Out,
  pipeChains: ∀ (modes: Modes) (indent: Nat) (value: Expr) => Parse.Gives GoodItems
    (() => pipeChain self modes indent value)
    (result => result = value ∨ Out result),
  iffs: ∀ (modes: Modes) (logic: Expr) => Parse.Gives GoodItems (() => iff self modes logic) Out,
  quantifiers: ∀ (modes: Modes) => Parse.Gives GoodItems (() => Syntax.quantifier self modes) Out,
  semis: ∀ (modes: Modes) (value: Expr) => Parse.Gives GoodItems (() => semiExpr self modes value) Out,
  keywords: ∀ (modes: Modes) (kind: Tok) => startsKeywordExpr kind = True
    → Parse.Gives GoodItems (() => exprKeyword self modes kind) Out,
  lambdas: ∀ (modes: Modes) => Parse.Gives GoodItems (() => lambda self modes None) Out,
  ifKeywords: ∀ (modes: Modes) => Parse.Gives GoodItems (() => ifKeyword self modes) Out,
  piExprs: ∀ (modes: Modes) (implicit: Bool) => Parse.Gives GoodItems (() => piExpr self modes implicit) Out,
  effectResults: ∀ (allowed: Modes) => Parse.Gives GoodItems (() => effectResult self allowed) Out,
  statementOthers: ∀ (modes: Modes) (kind: Tok) => startsOtherStatement kind = True
    → Parse.Gives GoodItems (() => statementOther self modes kind) StatementOk
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

-- The operator ladder, from `unary` down.

theorem givesUnaryOf ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (outside: Outside self)
    (bases: AtomBases self):
    Parse.Gives GoodItems (() => unary self modes) (Parsed1 18) :=
  givesUnary self modes nested outside (givesApp self modes nested outside bases)

theorem givesMulOf ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (outside: Outside self)
    (bases: AtomBases self):
    Parse.Gives GoodItems (() => mulExpr self modes) (Parsed1 16) :=
  givesMulExpr self modes
    (Parse.givesWeaken (givesUnaryOf self modes nested outside bases) (value parsed => parsedWeaken parsed byComputing))

theorem givesAddOf ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (outside: Outside self)
    (bases: AtomBases self):
    Parse.Gives GoodItems (() => addExpr self modes) (Parsed1 14) :=
  givesAddExpr self modes
    (Parse.givesWeaken (givesMulOf self modes nested outside bases) (value parsed => parsedWeaken parsed byComputing))

theorem givesAppendOf ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (outside: Outside self)
    (bases: AtomBases self):
    Parse.Gives GoodItems (() => appendExpr self modes) (Parsed1 12) :=
  givesAppendExpr self modes
    (Parse.givesWeaken (givesAddOf self modes nested outside bases) (value parsed => parsedWeaken parsed byComputing))

theorem reads0HeadIndent: Reads0 (() => headIndent()) :=
  reads0Then reads0Left (items => reads0Done (headIndentOn items))

theorem reads0AtPipe ∀ (modes: Modes): Reads0 (() => atPipe modes) :=
  reads0Then reads0Left (items => reads0Done (atPipeOn modes items))

theorem givesRangeEnd ∀ (modes: Modes) (low: Expr) (operator: Word) (high: Expr):
    Parse.Gives GoodItems (() => rangeEnd modes low operator high) (Parsed1 12) :=
  givesAfter0
    [p := () => modes.at DotDotLt || modes.at DotDotEq]
    [j := chained => rangeChained low operator high chained]
    (reads0Then [p := () => modes.at DotDotLt] (reads0At modes DotDotLt) (lt =>
      match lt with
        | True => reads0Done True
        | False => reads0At modes DotDotEq))
    (chained =>
      match chained with
        | True => Parse.readsFatal _ _
        | False => Parse.givesDone (parsedOutside 12 _ byComputing))

theorem givesRangeHigh ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (low: Expr)
    (nested: Nested self)
    (outside: Outside self)
    (bases: AtomBases self):
    Parse.Gives GoodItems (() => rangeHigh self modes low) (Parsed1 12) :=
  Parse.givesThen
    [p := () => bump()]
    [j := operator => rangeEnd modes low operator (appendExpr self modes)]
    givesBump
    (operator _ =>
      Parse.givesThen
        [p := () => appendExpr self modes]
        [j := high => rangeEnd modes low operator high]
        (givesAppendOf self modes nested outside bases)
        (high _ => givesRangeEnd modes low operator high))

theorem givesRangeOn ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (low: Expr)
    (nested: Nested self)
    (outside: Outside self)
    (bases: AtomBases self)
    (lowParsed: Parsed1 12 low) (seen: Option Tok):
    Parse.Gives GoodItems (() => rangeOn self modes low seen) (Parsed1 12) :=
  match seen with
    | Some kind =>
      match isDots: kind == DotDot with
        | True => Parse.readsFatal _ _
        | False =>
          match isRange: kind == DotDotLt || kind == DotDotEq with
            | True => givesRangeHigh self modes low nested outside bases
            | False => Parse.givesDone lowParsed
    | None => Parse.givesDone lowParsed

theorem givesRangeOf ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (outside: Outside self)
    (bases: AtomBases self):
    Parse.Gives GoodItems (() => rangeExpr self modes) (Parsed1 12) :=
  Parse.givesThen
    [p := () => appendExpr self modes]
    [j := low => rangeFrom self modes low]
    (givesAppendOf self modes nested outside bases)
    (low lowParsed =>
      givesAfter0 [p := () => modes.peek] [j := seen => rangeOn self modes low seen] (reads0Peek modes) (seen =>
        givesRangeOn self modes low nested outside bases lowParsed seen))

theorem givesPipedOf ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (outside: Outside self)
    (bases: AtomBases self):
    Parse.Gives GoodItems (() => pipedRange self modes) (Parsed1 12) :=
  givesAfter0 [p := () => headIndent()] [j := indent => pipedAt self modes indent] reads0HeadIndent (indent =>
    Parse.givesThen
      [p := () => rangeExpr self modes]
      [j := range => pipedAfter self modes indent range]
      (givesRangeOf self modes nested outside bases)
      (range rangeParsed =>
        givesAfter0
          [p := () => atPipe modes]
          [j := pipe => pipedEnd self modes indent range pipe]
          (reads0AtPipe modes)
          (pipe =>
            match pipe with
              | True => Parse.givesWeaken (outside.pipeChains modes indent range) (result chained =>
                match chained with
                  | Inl same => rewrite same then rangeParsed
                  | Inr out => outParsed 12 out)
              | False => Parse.givesDone rangeParsed)))

-- Comparisons.

theorem cmpTakesGood ∀ (kind: Tok) (text: Text)
    (took: kind.isComparison = True):
    kind.symbolic1 = True ∧ (Spells kind text → leftNeeds InfixBinary text = 8 ∧ infixLevel InfixBinary text = 6) :=
  match kind, took with
    | Equals, took => (byComputing, same => Both (rewrite same) (rewrite same))
    | EqEq, took => (byComputing, same => Both (rewrite same) (rewrite same))
    | Lt, took => (byComputing, same => Both (rewrite same) (rewrite same))
    | Gt, took => (byComputing, same => Both (rewrite same) (rewrite same))
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
    (lhsParsed: Parsed1 12 lhs)
    (secondParsed: Parsed1 12 second):
    Parsed1 6 (Infix InfixBinary lhs operator second) :=
  let (spelled, needs, own) := op
  infixParsedAt lhs second operator 6 12 12 lhsParsed secondParsed spelled (arithmetic [needs]) (arithmetic [own]) own

theorem givesCmpChain ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (lhs: Expr) (kind: Tok)
    (operator: Word) (second: Expr)
    (outside: Outside self)
    (op: CmpOperator operator)
    (lhsParsed: Parsed1 12 lhs)
    (secondParsed: Parsed1 12 second) (seen: Option Tok):
    Parse.Gives GoodItems (() => cmpChain self modes lhs kind operator second seen) (Parsed1 6) :=
  match seen with
    | Some next =>
      match chained: next.isComparison || next == KwIn || next == NotIn with
        | True => givesOut 6 (outside.comparisonChains modes lhs kind operator second)
        | False => Parse.givesDone (compareParsed lhs second operator op lhsParsed secondParsed)
    | None => Parse.givesDone (compareParsed lhs second operator op lhsParsed secondParsed)

theorem givesCmpAfter ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (lhs: Expr) (kind: Tok)
    (operator: Word) (conditional: Bool)
    (nested: Nested self)
    (outside: Outside self)
    (bases: AtomBases self)
    (op: CmpOperator operator)
    (lhsParsed: Parsed1 12 lhs):
    Parse.Gives GoodItems (() => cmpAfter self modes lhs kind operator conditional) (Parsed1 6) :=
  match conditional with
    | True => givesOut 6 (outside.cmpIfs modes lhs operator)
    | False =>
      Parse.givesThen
        [p := () => pipedRange self modes]
        [j := second => cmpSecond self modes lhs kind operator second]
        (givesPipedOf self modes nested outside bases)
        (second secondParsed =>
          givesAfter0
            [p := () => modes.peek]
            [j := seen => cmpChain self modes lhs kind operator second seen]
            (reads0Peek modes)
            (seen => givesCmpChain self modes lhs kind operator second outside op lhsParsed secondParsed seen))

theorem readsCmpCompare ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (lhs: Expr)
    (nested: Nested self)
    (outside: Outside self)
    (bases: AtomBases self)
    (lhsParsed: Parsed1 12 lhs)
    (start: Parse.Mark Item) (item: Item) (later: List Item)
    (shape: start.rest = [item, ..later])
    (took: item.kind.isComparison = True)
    (fine: Parse.Fits Item GoodItems start.rest):
    Parse.ReadsAt start (() => cmpCompare self modes lhs item.kind) (read value => Parsed1 6 value) :=
  readsAtBumpThen
    [k := operator => cmpAfter self modes lhs item.kind operator (modes.at KwIf)]
    shape
    fine
    (after fits =>
      givesAfter0
        [p := () => modes.at KwIf]
        [j := conditional => cmpAfter self modes lhs item.kind item.leaf.word conditional]
        (reads0At modes KwIf)
        (conditional =>
          givesCmpAfter self modes lhs item.kind item.leaf.word conditional nested outside bases
            (cmpOperatorOfItem item (goodHead fine shape) took)
            lhsParsed)
        after
        fits)

theorem givesCmpPiped ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (first: Option Tok) (lhs: Expr)
    (nested: Nested self)
    (outside: Outside self)
    (bases: AtomBases self)
    (lhsParsed: Parsed1 12 lhs):
    Parse.Gives GoodItems (() => cmpPiped self modes first lhs) (Parsed1 6) :=
  readsInPeeked modes
    (seen => cmpOn self modes first lhs seen) _
    (start fine stops => Parse.givesDone (parsedWeaken lhsParsed byComputing) start fine)
    (start item later shape fine stopped =>
      match isMember: item.kind == KwIn || item.kind == NotIn with
        | True =>
          givesOut [p := () => membership self modes first lhs] 6 (outside.memberships modes first lhs) start fine
        | False =>
          match isCmp: item.kind.isComparison with
            | True => readsCmpCompare self modes lhs nested outside bases lhsParsed start item later shape isCmp fine
            | False => Parse.givesDone (parsedWeaken lhsParsed byComputing) start fine)

theorem givesCmpOf ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (outside: Outside self)
    (bases: AtomBases self):
    Parse.Gives GoodItems (() => cmpExpr self modes) (Parsed1 6) :=
  givesAfter0 [p := () => left()] [j := items => cmpFirst self modes (items.head.map Item.kind)] reads0Left (items =>
    Parse.givesThen
      [p := () => pipedRange self modes]
      [j := lhs => cmpPiped self modes (items.head.map Item.kind) lhs]
      (givesPipedOf self modes nested outside bases)
      (lhs lhsParsed => givesCmpPiped self modes (items.head.map Item.kind) lhs nested outside bases lhsParsed))

-- `&&` and `||`.

--| The text of a logic operator: `&&`, `∧`, `||` or `∨`.
def LogicText (text: Text): Prop := (text = "&&" ∨ text = "∧") ∨ (text = "||" ∨ text = "∨")

--| An operator and its operand, as `logicLinks` reads them: a spelled logic operator, and an operand at the level of
--| `cmp_expr`.
def LogicLink (link: (Word, Expr)): Prop :=
  (operatorTok link.fst.text).isSome = True ∧ LogicText link.fst.text ∧ Parsed1 6 link.snd

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
    | Inl (Inl same) => Both (rewrite same) (rewrite same)
    | Inl (Inr same) => Both (rewrite same) (rewrite same)
    | Inr (Inl same) => (Bool.falseNotTrue (rewrite same at tested)).impossible
    | Inr (Inr same) => (Bool.falseNotTrue (rewrite same at tested)).impossible

theorem orLevels ∀ (text: Text)
    (logic: LogicText text)
    (tested: (text == "&&" || text == "∧") = False):
    leftNeeds InfixBinary text = 5 ∧ infixLevel InfixBinary text = 4 :=
  match logic with
    | Inl (Inl same) => (Bool.falseNotTrue (rewrite <- tested, same)).impossible
    | Inl (Inr same) => (Bool.falseNotTrue (rewrite <- tested, same)).impossible
    | Inr (Inl same) => Both (rewrite same) (rewrite same)
    | Inr (Inr same) => Both (rewrite same) (rewrite same)

--| The next link after a conjunction is an `||`.
def OrFirst: List (Word, Expr) → Prop
  | [(or, next), ..rest] => (or.text == "&&" || or.text == "∧") = False
  | other => True

--| What `conjunctionOf` gives: the conjunction is at the level of `&&`, the links left are all links, and the next
--| one (if any) is an `||`.
def ConjunctionOk (pair: (Expr, List (Word, Expr))): Prop :=
  Parsed1 5 pair.fst ∧ List.All LogicLink pair.snd ∧ OrFirst pair.snd

theorem conjunctionCons ∀ (first: Expr) (and: Word) (pair: (Expr, List (Word, Expr)))
    (firstParsed: Parsed1 6 first)
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
        own,
      afterOk,
      orFirst
    )

theorem conjunctionParsed ∀ (first: Expr) (links: List (Word, Expr))
    (firstParsed: Parsed1 6 first)
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

theorem groupAfterZero ∀ (pair: (Expr, List (Word, Expr))) (ok: ConjunctionOk pair): Parsed1 4 (groupAfter Zero pair) :=
  match pair, ok with
    | (conjunction, after), (conjunctionParsed, afterOk, orFirst) => parsedWeaken conjunctionParsed byComputing

theorem groupAfterSucc ∀ (more: Nat) (pair: (Expr, List (Word, Expr)))
    (ok: ConjunctionOk pair)
    (rest: ∀ (next: Expr) (links: List (Word, Expr)) => Parsed1 6 next
      → List.All LogicLink links
      → Parsed1 4 (groupLogic more next links)):
    Parsed1 4 (groupAfter (Succ more) pair) :=
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
            own
        | [], afterOk, orFirst => parsedWeaken conjunctionParsed byComputing

theorem groupLogicParsed ∀ (fuel: Nat) (first: Expr) (links: List (Word, Expr))
    (firstParsed: Parsed1 6 first)
    (ok: List.All LogicLink links):
    Parsed1 4 (groupLogic fuel first links) :=
  match fuel with
    | Zero => groupAfterZero (conjunctionOf first links) (conjunctionParsed first links firstParsed ok)
    | Succ more =>
      groupAfterSucc more
        (conjunctionOf first links)
        (conjunctionParsed first links firstParsed ok)
        (following rest followingParsed restOk => groupLogicParsed more following rest followingParsed restOk)

theorem reads0QuantifierAhead ∀ (modes: Modes): Reads0 (() => quantifierAhead modes) :=
  reads0Then [p := () => modes.at KwExists] (reads0At modes KwExists) (found =>
    match found with
      | True => reads0Done True
      | False => reads0At modes KwForall)

theorem givesLogicOperand ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (operator: Word) (quantified: Bool)
    (nested: Nested self)
    (outside: Outside self)
    (bases: AtomBases self)
    (spelled: (operatorTok operator.text).isSome = True)
    (logic: LogicText operator.text):
    Parse.Gives GoodItems (() => logicOperand self modes operator quantified) (Parse.Perhaps LogicLink) :=
  match quantified with
    | True =>
      Parse.givesThen
        [p := () => Syntax.quantifier self modes]
        [j := operand => Some (operator, operand)]
        (outside.quantifiers modes)
        (operand out =>
          Parse.givesDone [holds := Parse.Perhaps LogicLink] [x := Some (operator, operand)] (
            spelled,
            logic,
            outParsed 6 out
          ))
    | False =>
      Parse.givesThen
        [p := () => cmpExpr self modes]
        [j := operand => Some (operator, operand)]
        (givesCmpOf self modes nested outside bases)
        (operand parsed =>
          Parse.givesDone [holds := Parse.Perhaps LogicLink] [x := Some (operator, operand)] (spelled, logic, parsed))

theorem givesLogicOn ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (outside: Outside self)
    (bases: AtomBases self):
    Parse.Gives GoodItems (() => logicOn self modes modes.peek) (Parse.Perhaps LogicLink) :=
  readsInPeeked modes
    (seen => logicOn self modes seen) _
    (start fine stops => Parse.givesDone byComputing start fine)
    (start item later shape fine stopped =>
      match isLogic: item.kind == AndAnd || item.kind == OrOr with
        | True =>
          readsAtBumpThen
            [k := operator => logicOperand self modes operator (quantifierAhead modes)]
            shape
            fine
            (after fits =>
              let (spelled, logic) := logicKind item.kind item.text (goodHead fine shape) isLogic
              givesAfter0
                [p := () => quantifierAhead modes]
                [j := quantified => logicOperand self modes item.leaf.word quantified]
                (reads0QuantifierAhead modes)
                (quantified =>
                  givesLogicOperand self modes item.leaf.word quantified nested outside bases spelled logic)
                after
                fits)
        | False => Parse.givesDone byComputing start fine)

theorem givesLogicChain ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (first: Expr)
    (nested: Nested self)
    (outside: Outside self)
    (bases: AtomBases self)
    (firstParsed: Parsed1 6 first):
    Parse.Gives GoodItems (() => logicChain self modes first) (Parsed1 4) :=
  Parse.givesThen
    [p := () => logicLinks self modes]
    [j := links => groupLogic (links.length + 1) first links]
    (Parse.givesLoop (givesLogicOn self modes nested outside bases))
    (links ok => Parse.givesDone (groupLogicParsed (links.length + 1) first links firstParsed ok))

-- `->`, sections and the rest of `expr_inline`.

theorem sectionedParsedAt ∀ (floor: Nat) (section: Bool) (value: Expr)
    (parsed: Parsed1 floor value):
    Parsed1 floor (sectioned section value) :=
  match section with
    | True => parsedOutside floor _ byComputing
    | False => parsed

theorem reads0AllowBrace ∀ (modes: Modes): Reads0 (() => allowBrace modes) :=
  reads0Then reads0Left (items => reads0Done (allowBraceOn modes items))

theorem reads0RowAhead ∀ (allowed: Modes): Reads0 (() => rowAhead allowed) :=
  reads0Then [p := () => allowed.at LBrace] (reads0At allowed LBrace) (found =>
    reads0Then [p := () => left()] reads0Left (items => reads0Done (rowOn found items)))

theorem givesResultType ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (outside: Outside self):
    Parse.Gives GoodItems (() => resultType self modes) (Parsed1 1) :=
  givesAfter0
    [p := () => allowBrace modes]
    [j := allowed => resultAllowed self allowed]
    (reads0AllowBrace modes)
    (allowed =>
      givesAfter0
        [p := () => rowAhead allowed]
        [j := row => resultRow self allowed row]
        (reads0RowAhead allowed)
        (row =>
          match row with
            | True => givesOut 1 (outside.effectResults allowed)
            | False => nested { modes = allowed, level = LevelFull }))

theorem arrowParsed ∀ (left right: Expr) (arrow: Word)
    (spelled: (operatorTok arrow.text).isSome = True)
    (leftParsed: Parsed1 4 left)
    (rightParsed: Parsed1 1 right):
    Parsed1 1 (Infix InfixArrow left arrow right) :=
  within =>
    let (leftWithin, rightWithin) := within
    let (leftShaped, leftLexical, leftHigh) := leftParsed leftWithin
    let (rightShaped, rightLexical, rightHigh) := rightParsed rightWithin
    (
      Both leftShaped (Both rightShaped (Both (arithmetic [leftHigh]) (arithmetic [rightHigh]))),
      Both leftLexical (Both spelled rightLexical),
      arithmetic
    )

theorem givesArrowEnd ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (value: Expr) (arrow: Word)
    (nested: Nested self)
    (outside: Outside self)
    (spelled: (operatorTok arrow.text).isSome = True)
    (parsed: Parsed1 4 value):
    Parse.Gives GoodItems (() => arrowEnd self modes value arrow) (Parsed1 1) :=
  Parse.givesThen
    [p := () => resultType self modes]
    [j := right => Infix InfixArrow value arrow right]
    (givesResultType self modes nested outside)
    (right rightParsed => Parse.givesDone (arrowParsed value right arrow spelled parsed rightParsed))

theorem arrowSymbolic ∀ (kind: Tok) (is: kind = Arrow): kind.symbolic1 = True := rewrite is

theorem givesOpSequence ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (value: Expr) (sequence: Bool)
    (nested: Nested self)
    (outside: Outside self)
    (parsed: Parsed1 4 value):
    Parse.Gives GoodItems (() => opSequence self modes value sequence) (Parsed1 1) :=
  readsInPeeked modes
    (seen => opEnd self modes value sequence seen) _
    (start fine stops => Parse.givesDone (parsedWeaken parsed byComputing) start fine)
    (start item later shape fine stopped =>
      match isArrow: item.kind == Arrow with
        | True => readsAtBumpThen [k := arrow => arrowEnd self modes value arrow] shape fine (after fits =>
          givesArrowEnd self modes value item.leaf.word nested outside
            (operatorOfItem item (goodHead fine shape) (arrowSymbolic item.kind (DecEq.sound isArrow)))
            parsed
            after
            fits)
        | False =>
          match isSemi: item.kind == Semi && sequence with
            | True => givesOut [p := () => semiExpr self modes value] 1 (outside.semis modes value) start fine
            | False => Parse.givesDone (parsedWeaken parsed byComputing) start fine)

theorem reads0SequenceAhead ∀ (modes: Modes): Reads0 (() => sequenceAhead modes) :=
  reads0Then [p := () => left()] reads0Left (items => reads0Done (sequenceOn modes items))

theorem givesOpIffed ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (section: Bool) (iffed: Expr)
    (nested: Nested self)
    (outside: Outside self)
    (parsed: Parsed1 4 iffed):
    Parse.Gives GoodItems (() => opIffed self modes section iffed) (Parsed1 1) :=
  givesAfter0
    [p := () => sequenceAhead modes]
    [j := sequence => opSequence self modes (sectioned section iffed) sequence]
    (reads0SequenceAhead modes)
    (sequence =>
      givesOpSequence self modes
        (sectioned section iffed)
        sequence
        nested
        outside
        (sectionedParsedAt 4 section iffed parsed))

theorem givesOpLogic ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (section: Bool) (logic: Expr)
    (nested: Nested self)
    (outside: Outside self)
    (parsed: Parsed1 4 logic):
    Parse.Gives GoodItems (() => opLogic self modes section logic) (Parsed1 1) :=
  givesAfter0
    [p := () => modes.at IffArrow]
    [j := ahead => opIffed self modes section (iffOf self modes logic ahead)]
    (reads0At modes IffArrow)
    (ahead =>
      Parse.givesThen
        [p := () => iffOf self modes logic ahead]
        [j := iffed => opIffed self modes section iffed]
        (match ahead with
          | True => givesOut 4 (outside.iffs modes logic)
          | False => Parse.givesDone parsed)
        (iffed iffedParsed => givesOpIffed self modes section iffed nested outside iffedParsed))

theorem givesLogicAfter ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (compared: Expr)
    (nested: Nested self)
    (outside: Outside self)
    (bases: AtomBases self)
    (parsed: Parsed1 6 compared):
    Parse.Gives GoodItems (() => logicAfter self modes compared) (Parsed1 4) :=
  givesAfter0 [p := () => left()] [j := items => logicOf self modes compared (andOrOn modes items)] reads0Left (items =>
    match andOrOn modes items with
      | True => givesLogicChain self modes compared nested outside bases parsed
      | False => Parse.givesDone (parsedWeaken parsed byComputing))

theorem givesOpCompared ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (section: Bool) (compared: Expr)
    (nested: Nested self)
    (outside: Outside self)
    (bases: AtomBases self)
    (parsed: Parsed1 6 compared):
    Parse.Gives GoodItems (() => opCompared self modes section compared) (Parsed1 1) :=
  Parse.givesThen
    [p := () => logicAfter self modes compared]
    [j := logic => opLogic self modes section logic]
    (givesLogicAfter self modes compared nested outside bases parsed)
    (logic logicParsed => givesOpLogic self modes section logic nested outside logicParsed)

theorem givesOpSection ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (start: Nat) (section: Bool)
    (nested: Nested self)
    (outside: Outside self)
    (bases: AtomBases self):
    Parse.Gives GoodItems (() => opSection self modes start section) (Parsed1 1) :=
  Parse.givesThen
    [p := () => cmpExpr self (if section then { modes | sectionHead = Some start } else modes)]
    [j := compared => opCompared self modes section compared]
    (givesCmpOf self (if section then { modes | sectionHead = Some start } else modes) nested outside bases)
    (compared parsed => givesOpCompared self modes section compared nested outside bases parsed)

theorem givesOperatorExpr ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (outside: Outside self)
    (bases: AtomBases self):
    Parse.Gives GoodItems (() => operatorExpr self modes) (Parsed1 1) :=
  givesAfter0 [p := () => offset()] [j := start => opStart self modes start] reads0Offset (start =>
    givesAfter0
      [p := () => modes.at Dot]
      [j := section => opSection self modes start section]
      (reads0At modes Dot)
      (section => givesOpSection self modes start section nested outside bases))

-- `expr_inline`.

theorem reads0Mark1: Reads0 (() => Parse.mark()) := reads0Mark (here => here)

theorem reads0LambdaHere ∀ (modes: Modes): Reads0 (() => lambdaHere modes) :=
  reads0Then [p := () => Parse.mark()] [j := here => lambdaAhead modes (here.left + 1) left()] reads0Mark1 (here =>
    reads0Then [p := () => left()] [j := items => lambdaAhead modes (here.left + 1) items] reads0Left (items =>
      reads0Done (lambdaAhead modes (here.left + 1) items)))

theorem reads0LambdaResultHere ∀ (modes: Modes): Reads0 (() => lambdaResultHere modes) :=
  reads0Then
    [p := () => Parse.mark()]
    [j := here => lambdaResultType modes (here.left + 1) False left()]
    reads0Mark1
    (here =>
      reads0Then
        [p := () => left()]
        [j := items => lambdaResultType modes (here.left + 1) False items]
        reads0Left
        (items => reads0Done (lambdaResultType modes (here.left + 1) False items)))

theorem reads0ImplicitHere ∀ (modes: Modes): Reads0 (() => implicitHere modes) :=
  reads0Then [p := () => Parse.mark()] [j := here => implicitOn (here.left + 1) left() modes.peek] reads0Mark1 (here =>
    reads0Then [p := () => left()] [j := items => implicitOn (here.left + 1) items modes.peek] reads0Left (items =>
      reads0Then
        [p := () => modes.peek]
        [j := seen => implicitOn (here.left + 1) items seen]
        (reads0Peek modes)
        (seen => reads0Done (implicitOn (here.left + 1) items seen))))

theorem reads0PiHere ∀ (modes: Modes): Reads0 (() => piHere modes) :=
  reads0Then [p := () => left()] [j := items => piOn items modes.peek] reads0Left (items =>
    reads0Then [p := () => modes.peek] [j := seen => piOn items seen] (reads0Peek modes) (seen =>
      reads0Done (piOn items seen)))

theorem givesExprPi ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (pi: Bool)
    (nested: Nested self)
    (outside: Outside self)
    (bases: AtomBases self):
    Parse.Gives GoodItems (() => exprPi self modes pi) (Parsed1 1) :=
  match pi with
    | True => givesOut 1 (outside.piExprs modes False)
    | False => givesOperatorExpr self modes nested outside bases

theorem givesExprImplicit ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (implicit: Bool)
    (nested: Nested self)
    (outside: Outside self)
    (bases: AtomBases self):
    Parse.Gives GoodItems (() => exprImplicit self modes implicit) (Parsed1 1) :=
  match implicit with
    | True => givesOut 1 (outside.piExprs modes True)
    | False => givesAfter0 [p := () => piHere modes] [j := pi => exprPi self modes pi] (reads0PiHere modes) (pi =>
      givesExprPi self modes pi nested outside bases)

theorem givesExprPlain ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (outside: Outside self)
    (bases: AtomBases self):
    Parse.Gives GoodItems (() => exprPlain self modes) (Parsed1 1) :=
  givesAfter0
    [p := () => implicitHere modes]
    [j := implicit => exprImplicit self modes implicit]
    (reads0ImplicitHere modes)
    (implicit => givesExprImplicit self modes implicit nested outside bases)

theorem givesExprBinder ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (outside: Outside self)
    (bases: AtomBases self):
    Parse.Gives GoodItems (() => exprBinder self modes modes.peek) (Parsed1 1) :=
  readsInPeeked modes
    (seen => exprBinder self modes seen) _
    (start fine stops => givesExprPlain self modes nested outside bases start fine)
    (start item later shape fine stopped =>
      match isQuantifier: item.kind == KwExists || item.kind == KwForall with
        | True => givesOut [p := () => Syntax.quantifier self modes] 1 (outside.quantifiers modes) start fine
        | False =>
          match isIf: item.kind == KwIf with
            | True => givesOut [p := () => ifKeyword self modes] 1 (outside.ifKeywords modes) start fine
            | False => givesExprPlain self modes nested outside bases start fine)

theorem givesExprResult ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (refused: Bool)
    (nested: Nested self)
    (outside: Outside self)
    (bases: AtomBases self):
    Parse.Gives GoodItems (() => exprResult self modes refused) (Parsed1 1) :=
  match refused with
    | True => Parse.readsFatal _ _
    | False => givesExprBinder self modes nested outside bases

theorem givesExprLambda ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (lambdas: Bool)
    (nested: Nested self)
    (outside: Outside self)
    (bases: AtomBases self):
    Parse.Gives GoodItems (() => exprLambda self modes lambdas) (Parsed1 1) :=
  match lambdas with
    | True => givesOut 1 (outside.lambdas modes)
    | False =>
      givesAfter0
        [p := () => lambdaResultHere modes]
        [j := refused => exprResult self modes refused]
        (reads0LambdaResultHere modes)
        (refused => givesExprResult self modes refused nested outside bases)

theorem givesExprOther ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (outside: Outside self)
    (bases: AtomBases self):
    Parse.Gives GoodItems (() => exprOther self modes) (Parsed1 1) :=
  givesAfter0
    [p := () => lambdaHere modes]
    [j := lambdas => exprLambda self modes lambdas]
    (reads0LambdaHere modes)
    (lambdas => givesExprLambda self modes lambdas nested outside bases)

theorem givesExprInline ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (outside: Outside self)
    (bases: AtomBases self):
    Parse.Gives GoodItems (() => exprInline self modes) (Parsed1 1) :=
  readsInPeeked modes
    (seen => exprInlineOn self modes seen) _
    (start fine stops => givesExprOther self modes nested outside bases start fine)
    (start item later shape fine stopped =>
      match keyword: startsKeywordExpr item.kind with
        | True =>
          givesOut [p := () => exprKeyword self modes item.kind] 1 (outside.keywords modes item.kind keyword) start fine
        | False => givesExprOther self modes nested outside bases start fine)

-- Statements and blocks.

theorem givesStatementValue ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (outside: Outside self)
    (bases: AtomBases self):
    Parse.Gives GoodItems (() => statementValue self modes) StatementOk :=
  Parse.givesThen
    [p := () => exprInline self modes]
    [j := value => ExprStatement value]
    (givesExprInline self modes nested outside bases)
    (value parsed => Parse.givesDone [holds := StatementOk] [x := ExprStatement value] parsed)

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
  match more_: now != before
    && many
    && next.leaf.token.lineStart
    && next.leaf.token.column == column
    && !endsBlocks next.kind with
    | True => again done doneOk
    | False => Parse.givesDone doneOk

theorem givesBlockItems ∀ (more: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes) (column: Nat) (many: Bool)
    (done: List Statement) (before: Nat) (items: List Item)
    (doneOk: List.All StatementOk done)
    (again: ∀ (found: List Statement) => List.All StatementOk found
      → Parse.Gives GoodItems (() => blockLines more self modes column many found) (List.All StatementOk)):
    Parse.Gives GoodItems (() => blockItems more self modes column many done before items) (List.All StatementOk) :=
  match items with
    | [next, ..rest] =>
      givesAfter0
        [p := () => offset()]
        [j := now => blockOffset more self modes column many done before next now]
        reads0Offset
        (now => givesBlockOffset more self modes column many done before next now doneOk again)
    | [] => Parse.givesDone doneOk

theorem givesBlockDone ∀ (more: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes) (column: Nat) (many: Bool)
    (found: List Statement) (before: Nat) (line: Statement)
    (foundOk: List.All StatementOk found)
    (lineOk: StatementOk line)
    (again: ∀ (found: List Statement) => List.All StatementOk found
      → Parse.Gives GoodItems (() => blockLines more self modes column many found) (List.All StatementOk)):
    Parse.Gives GoodItems (() => blockDone more self modes column many found before line) (List.All StatementOk) :=
  givesAfter0
    [p := () => left()]
    [j := items => blockItems more self modes column many [line, ..found] before items]
    reads0Left
    (items => givesBlockItems more self modes column many [line, ..found] before items (lineOk, foundOk) again)

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
  Parse.givesThen
    [p := () => statement self { statementModes | lines = [{ column, many, kind = lineKindOf seen }, ..modes.lines] }]
    [j := line => blockDone more self modes column many found before line]
    (givesStatement self
      { statementModes | lines = [{ column, many, kind = lineKindOf seen }, ..modes.lines] }
      nested
      outside
      bases)
    (line lineOk => givesBlockDone more self modes column many found before line foundOk lineOk again)

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
  givesAfter0
    [p := () => statementModes.peek]
    [j := seen => blockKind more self modes column many found before statementModes seen]
    (reads0Peek statementModes)
    (seen =>
      givesBlockKind more self modes column many found before statementModes seen nested outside bases foundOk again)

theorem givesBlockLine ∀ (more: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes) (column: Nat) (many: Bool)
    (found: List Statement) (before: Nat)
    (nested: Nested self)
    (outside: Outside self)
    (bases: AtomBases self)
    (foundOk: List.All StatementOk found)
    (again: ∀ (found: List Statement) => List.All StatementOk found
      → Parse.Gives GoodItems (() => blockLines more self modes column many found) (List.All StatementOk)):
    Parse.Gives GoodItems (() => blockLine more self modes column many found before) (List.All StatementOk) :=
  givesBlockPeek more self modes column many found before
    { modes | allow = Some before }
    nested
    outside
    bases
    foundOk
    again

theorem givesBlockLines ∀ (fuel: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes) (column: Nat)
    (many: Bool) (found: List Statement)
    (nested: Nested self)
    (outside: Outside self)
    (bases: AtomBases self)
    (foundOk: List.All StatementOk found):
    Parse.Gives GoodItems (() => blockLines fuel self modes column many found) (List.All StatementOk) :=
  match fuel with
    | Zero => Parse.givesDone foundOk
    | Succ more =>
      givesAfter0
        [p := () => offset()]
        [j := before => blockLine more self modes column many found before]
        reads0Offset
        (before =>
          givesBlockLine more self modes column many found before nested outside bases foundOk (again okAgain =>
            givesBlockLines more self modes column many again nested outside bases okAgain))

theorem givesBlockResult ∀ (statements: List Statement)
    (ok: List.All StatementOk statements):
    Parse.Gives GoodItems (() => blockResult statements) (Parsed1 1) :=
  match statements, ok with
    | [ExprStatement value], (valueOk, rest) => Parse.givesDone valueOk
    | [ExprStatement value, last, ..earlier], (valueOk, rest) =>
      match [last, ..earlier].reverse with
        | [first, ..others] => Parse.givesDone (parsedOutside 1 _ byComputing)
        | [] => Parse.givesDone valueOk
    | [LetStatement binding, ..others], ok => Parse.readsFatal _ _
    | [LocalDef attributes header body, ..others], ok => Parse.readsFatal _ _
    | [], ok => Parse.readsFatal _ _

theorem givesBlock ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (column: Nat) (many: Bool)
    (nested: Nested self)
    (outside: Outside self)
    (bases: AtomBases self):
    Parse.Gives GoodItems (() => block self modes column many) (Parsed1 1) :=
  Parse.givesThen
    [p := () => Parse.mark()]
    [j := here =>
      blockResult
        (blockLines
          (here.left + 1)
          self
          (if many then { modes | limit = Some column, letValue = None } else { modes | limit = Some column })
          column
          many
          [])]
    Parse.givesMark
    (here _ =>
      Parse.givesThen
        [p := () =>
          blockLines
            (here.left + 1)
            self
            (if many then { modes | limit = Some column, letValue = None } else { modes | limit = Some column })
            column
            many
            []]
        [j := statements => blockResult statements]
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
    Parse.Gives GoodItems (() => exprRuns self modes item limit runs) (Parsed1 1) :=
  match runs with
    | True => givesAfter0 [p := () => left()] [j := items => modes.gapOn ranOutLine items] reads0Left (items =>
      match blockEnd modes.lines items.head with
        | Some ending => Parse.readsFatal _ _
        | None => Parse.readsFatal _ _)
    | False =>
      match same: item.leaf.token.column == limit with
        | True => givesBlock self modes item.leaf.token.column False nested outside bases
        | False => givesExprInline self modes nested outside bases

theorem givesExprBlock ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (item: Item)
    (nested: Nested self)
    (outside: Outside self)
    (bases: AtomBases self):
    Parse.Gives GoodItems (() => exprBlock self modes item) (Parsed1 1) :=
  match modes.limit with
    | None => givesBlock self modes item.leaf.token.column True nested outside bases
    | Some limit =>
      match wider: item.leaf.token.column > limit with
        | True => givesBlock self modes item.leaf.token.column True nested outside bases
        | False =>
          givesAfter0
            [p := () => left()]
            [j := items => exprRuns self modes item limit (runsOutAt modes item limit items)]
            reads0Left
            (items => givesExprRuns self modes item limit (runsOutAt modes item limit items) nested outside bases)

theorem givesExprOn ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (later: Bool) (items: List Item)
    (nested: Nested self)
    (outside: Outside self)
    (bases: AtomBases self):
    Parse.Gives GoodItems (() => exprOn self modes later items) (Parsed1 1) :=
  match items with
    | [item, ..rest] =>
      match here: item.leaf.token.lineStart && later && modes.allow != Some item.index && !modes.endsConstruct item with
        | True => givesExprBlock self modes item nested outside bases
        | False => givesExprInline self modes nested outside bases
    | [] => givesExprInline self modes nested outside bases

theorem givesExprOf ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (outside: Outside self)
    (bases: AtomBases self):
    Parse.Gives GoodItems (() => expr self modes) (Parsed1 1) :=
  givesAfter0 [p := () => offset()] [j := now => exprLater self modes (now > 0)] reads0Offset (now =>
    givesAfter0 [p := () => left()] [j := items => exprOn self modes (now > 0) items] reads0Left (items =>
      givesExprOn self modes (now > 0) items nested outside bases))

theorem givesThenBody ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (outside: Outside self)
    (bases: AtomBases self):
    Parse.Gives GoodItems (() => thenBody self modes) (Parsed1 1) :=
  givesAfter0 [p := () => left()] [j := items => thenBodyOn self modes items] reads0Left (items =>
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
    (outside: Outside self)
    (bases: AtomBases self):
    Parse.Gives GoodItems (() => logicLevel self modes) (Parsed1 4) :=
  Parse.givesThen
    [p := () => cmpExpr self modes]
    [j := compared => logicAfter self modes compared]
    (givesCmpOf self modes nested outside bases)
    (compared parsed => givesLogicAfter self modes compared nested outside bases parsed)

--| One level of the expression parser gives what `GoalParsed` says, given that `self` does at every goal and what the
--| parsers outside slice 1 give.
theorem givesExpressionRule ∀ (self: Goal → {Parse Item} Expr) (goal: Goal)
    (nested: Nested self)
    (outside: Outside self):
    Parse.Gives GoodItems (() => expressionRule self goal) (GoalParsed goal) :=
  let bases := givesAtomBases self nested outside
  match goal with
    | { modes, level } =>
      match level with
        | LevelFull => givesExprOf self modes nested outside bases
        | LevelInline => givesExprInline self modes nested outside bases
        | LevelLogic => givesLogicLevel self modes nested outside bases
        | LevelComparison => givesCmpOf self modes nested outside bases
        | LevelAppend => givesAppendOf self modes nested outside bases
        | LevelAdditive => givesAddOf self modes nested outside bases
        | LevelMultiplicative => givesMulOf self modes nested outside bases
        | LevelUnary => givesUnaryOf self modes nested outside bases
        | LevelArgument => givesAtomArgument self modes False outside bases
        | LevelApp => givesApp self modes nested outside bases
        | LevelThenBody => givesThenBody self modes nested outside bases

--| What the parsers outside slice 1 give, for every `self` that gives what `GoalParsed` says: SW-4000 proves it.
def OutsideGives: Type := ∀ (self: Goal → {Parse Item} Expr) => Nested self → Outside self

--| `expressionAt`, which starts the recursion from a declaration's level, gives what `GoalParsed` says at every goal.
theorem givesExpressionAt ∀ (outside: OutsideGives): Nested expressionAt := goal =>
  Parse.givesRecursiveWith expressionRule
    (inner expr => GoalParsed inner expr)
    (self nested argument => givesExpressionRule self argument nested (outside self nested))
    goal

--| A whole expression read by `expression`, from good items: at the level of `expr`.
theorem givesExpression ∀ (modes: Modes) (outside: OutsideGives):
    Parse.Gives GoodItems (() => expression modes) (Parsed1 1) :=
  Parse.givesRecursiveWith expressionRule
    (inner expr => GoalParsed inner expr)
    (self nested argument => givesExpressionRule self argument nested (outside self nested))
    { modes, level = LevelFull }

-- The `def` frame.

--| A definition's name is a name, of the lower-case kind or the upper-case one (`def Foo: Nat := 1` is in slice 1).
def NameOk (name: Word): Prop := name.lexesAs Lower = True ∨ name.lexesAs Upper = True

def BodyOk: DefBody → Prop
  | Assigned colonEq value => Parsed1 1 value
  | other => True

--| What a definition's header and body give: its result and value are parsed, and its name is a name.
def PartsOk (parts: (Header, DefBody)): Prop := Parsed1 1 parts.fst.result ∧ NameOk parts.fst.name ∧ BodyOk parts.snd

def DeclOut (decl: Decl): Prop := decl.within1 = False

theorem givesFixedFrom: Parse.Gives GoodItems (() => fixedFrom()) (comments => True) :=
  Parse.givesThen [p := () => bump()] [j := word => word.comments] givesBump (found _ => Parse.givesDone byComputing)

theorem givesUpperQualified ∀ (modes: Modes) (what: Text):
    Parse.Gives GoodItems (() => modes.upperQualified what) NameOk :=
  readsInPeeked modes
    (seen => modes.upperQualifiedOn what seen) _
    (start fine stops => givesFail modes what start fine)
    (start item later shape fine stopped =>
      match took: isSome Upper (Some item.kind) with
        | False => givesFail modes what start fine
        | True => Parse.readsAtWeaken (readsAtBump shape) (read word (single, same) =>
          rewrite same then
            Inr
              (wordLexesAs item.leaf.word Upper
                (rewrite <- DecEq.sound took then
                  lexesAsSpells item.kind item.text
                    (goodHead fine shape (rewrite DecEq.sound took))
                    (mayFollowEnd item.kind item.text)))))

theorem givesLowerQualified ∀ (modes: Modes) (what: Text):
    Parse.Gives GoodItems (() => modes.lowerQualified what) NameOk :=
  readsInPeeked modes
    (seen => modes.lowerQualifiedOn what seen) _
    (start fine stops => givesFailName modes what start fine)
    (start item later shape fine stopped =>
      match took: isSome Lower (Some item.kind) with
        | False => givesFailName modes what start fine
        | True => Parse.readsAtWeaken (readsAtBump shape) (read word (single, same) =>
          rewrite same then
            Inl
              (wordLexesAs item.leaf.word Lower
                (rewrite <- DecEq.sound took then
                  lexesAsSpells item.kind item.text
                    (goodHead fine shape (rewrite DecEq.sound took))
                    (mayFollowEnd item.kind item.text)))))

theorem givesDefinitionName ∀ (modes: Modes): Parse.Gives GoodItems (() => definitionName modes) NameOk :=
  givesAfter0
    [p := () => modes.at Upper]
    [j := upper => definitionNameAfter modes upper]
    (reads0At modes Upper)
    (upper =>
      match upper with
        | True => givesUpperQualified modes "a name"
        | False => givesLowerQualified modes "a name")

--| What the frame of a declaration reads that is outside slice 1: attributes, the declarations that aren't plain
--- definitions, the parts of a header that a plain definition has none of (`∀`, parameters, `decreasing`,
--| `unfolding`), and a definition's arms. SW-4000 proves these.
type Frame (self: Goal → {Parse Item} Expr) = {
  attributes: ∀ (modes: Modes) => Parse.Gives GoodItems (() => attributesOf modes) (found => True),
  namespaces: ∀ (seen: Seen) (modes: Modes) => Parse.Gives GoodItems (() => namespaceStep seen modes) DeclOut,
  imports: ∀ (seen: Seen) (modes: Modes) => Parse.Gives GoodItems (() => importStep seen modes) DeclOut,
  others: ∀ (modes: Modes) (attributes: List Attributes) (seen: Option Tok) => Parse.Gives GoodItems
    (() => declarationOther modes attributes seen)
    DeclOut,
  foralls: ∀ (modes: Modes) (kind: DefKind) => Parse.Gives GoodItems (() => forallPart modes kind) (found => True),
  params: ∀ (modes: Modes) => Parse.Gives GoodItems (() => headerParams self modes) (found => True),
  decreasings: ∀ (modes headerModes: Modes) (isInstance: Bool) => Parse.Gives GoodItems
    (() => decreasingPart self modes headerModes isInstance)
    (found => True),
  unfoldings: ∀ (modes afterDecreasing: Modes) (isInstance: Bool) => Parse.Gives GoodItems
    (() => unfoldingPart modes afterDecreasing isInstance)
    (found => True),
  arms: ∀ (modes: Modes) (d: Nat) => Parse.Gives GoodItems (() => armsBody self modes d) BodyOk
}

theorem givesAssignedBody ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self):
    Parse.Gives GoodItems (() => assignedBody self modes) BodyOk :=
  Parse.givesThen
    [p := () => fixedFrom()]
    [j := colonEq => assignedValue modes colonEq (self { modes, level = LevelFull })]
    givesFixedFrom
    (colonEq _ =>
      Parse.givesThen
        [p := () => self { modes, level = LevelFull }]
        [j := value => assignedValue modes colonEq value]
        (nested { modes, level = LevelFull })
        (value parsed =>
          givesAfter0
            [p := () => modes.at Pipe]
            [j := arms => assignedEnd colonEq value arms]
            (reads0At modes Pipe)
            (arms =>
              match arms with
                | True => Parse.readsFatal _ _
                | False => Parse.givesDone [holds := BodyOk] [x := Assigned colonEq value] parsed)))

theorem givesDefinitionBodyOn ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (result: Expr) (d: Nat)
    (nested: Nested self)
    (frame: Frame self):
    Parse.Gives GoodItems (() => definitionBodyOn self modes result d modes.peek) BodyOk :=
  givesAfter0
    [p := () => modes.peek]
    [j := seen => definitionBodyOn self modes result d seen]
    (reads0Peek modes)
    (seen =>
      match seen with
        | Some kind =>
          match isAssigned: kind == ColonEq with
            | True => givesAssignedBody self modes nested
            | False =>
              match isArms: kind == Pipe with
                | True => frame.arms modes d
                | False =>
                  match isEquals: kind == Equals with
                    | True => Parse.readsFatal _ _
                    | False => givesFail modes _
        | None =>
          match isEquation result with
            | True => Parse.readsFatal _ _
            | False => Parse.givesDone byComputing)

theorem givesDefinitionBody ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (result: Expr) (isInstance: Bool) (d: Nat)
    (nested: Nested self)
    (frame: Frame self):
    Parse.Gives GoodItems (() => definitionBody self modes result isInstance d) BodyOk :=
  Parse.givesThen
    [p := () => definitionBodyOn self modes result d modes.peek]
    [j := body => definitionChecked isInstance body]
    (givesDefinitionBodyOn self modes result d nested frame)
    (body bodyOk =>
      givesAfter0 [p := () => left()] [j := items => definitionWhere isInstance body items] reads0Left (items =>
        match definitionRefusal isInstance body items with
          | Some message => Parse.readsFatal _ _
          | None => Parse.givesDone bodyOk))

theorem givesAllowColonEq ∀ (modes: Modes): Parse.Gives GoodItems (() => allowColonEq modes) (found => True) :=
  givesAfter0 [p := () => left()] [j := items => allowColonEqOn modes items] reads0Left (items =>
    Parse.givesDone byComputing)

theorem givesAfterDecreasingOf ∀ (modes: Modes) (clause: Option (Comments, Expr)):
    Parse.Gives GoodItems (() => afterDecreasingOf modes clause) (found => True) :=
  match clause.isSome with
    | True => givesAllowColonEq modes
    | False => Parse.givesDone byComputing

theorem givesAfterUnfoldingOf ∀ (afterDecreasing: Modes) (clause: Option (Comments, List Word)):
    Parse.Gives GoodItems (() => afterUnfoldingOf afterDecreasing clause) (found => True) :=
  match clause.isSome with
    | True => givesAllowColonEq afterDecreasing
    | False => Parse.givesDone byComputing

theorem reads0Recovers ∀ (afterUnfolding: Modes): Reads0 (() => recovers afterUnfolding) :=
  reads0Then [p := () => afterUnfolding.at ColonEq] (reads0At afterUnfolding ColonEq) (found =>
    match found with
      | True => reads0Done True
      | False => reads0At afterUnfolding Pipe)

theorem givesBodyModes ∀ (afterUnfolding: Modes) (isInstance: Bool) (local: Option Nat):
    Parse.Gives GoodItems (() => bodyModesOf afterUnfolding isInstance local) (found => True) :=
  match local with
    | Some column => Parse.givesDone byComputing
    | None =>
      givesAfter0
        [p := () => recovers afterUnfolding]
        [j := recovering => recoverMode afterUnfolding isInstance recovering]
        (reads0Recovers afterUnfolding)
        (recovering => Parse.givesDone byComputing)

theorem reads0ClauseConflict ∀ (afterUnfolding: Modes) (clause: Option (Comments, List Word)):
    Reads0 (() => clauseConflict afterUnfolding clause) :=
  reads0Then [p := () => afterUnfolding.at KwDecreasing] (reads0At afterUnfolding KwDecreasing) (found =>
    reads0Done (conflictOn found clause))

theorem givesDefKindOf ∀ (modes: Modes): Parse.Gives GoodItems (() => defKindOf modes) (kind => True) :=
  givesOfReads0 (reads0Then [p := () => modes.peek] (reads0Peek modes) (seen => reads0Done (defKindOn seen)))

theorem givesDefinitionParts ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (exportKeyword opaqueKeyword: Option Comments) (local: Option Nat)
    (nested: Nested self)
    (outside: Outside self)
    (frame: Frame self):
    Parse.Gives GoodItems (() => definitionParts self modes exportKeyword opaqueKeyword local) PartsOk :=
  Parse.givesThen (givesDefKindOf modes) (kind _ =>
    Parse.givesThen givesFixedFrom (keyword _ =>
      Parse.givesThen (givesDefinitionName modes) (name nameOk =>
        Parse.givesThen (frame.foralls modes _) (forallKeyword _ =>
          Parse.givesThen (frame.params modes.sealed) (params _ =>
            Parse.givesThen givesFixedFrom (colon _ =>
              Parse.givesThen (givesResultType self _ nested outside) (result resultParsed =>
                Parse.givesThen (frame.decreasings modes _ _) (decreasingClause _ =>
                  Parse.givesThen (givesAfterDecreasingOf modes decreasingClause) (afterDecreasing _ =>
                    Parse.givesThen (frame.unfoldings modes afterDecreasing _) (unfoldingClause _ =>
                      Parse.givesThen (givesAfterUnfoldingOf afterDecreasing unfoldingClause) (afterUnfolding _ =>
                        givesAfter0 (reads0ClauseConflict afterUnfolding unfoldingClause) (conflict =>
                          match conflict with
                            | True => Parse.readsFatal _ _
                            | False => Parse.givesThen (givesBodyModes afterUnfolding _ local) (bodyModes _ =>
                              Parse.givesThen
                                (givesDefinitionBody self bodyModes result _ _ nested frame)
                                (body bodyOk => Parse.givesDone (resultParsed, nameOk, bodyOk)))))))))))))))

-- Declarations.

--| `Decl.lexical1`, but a definition's name may be an upper-case name too (`def Foo: Nat := 1` is in slice 1,
--| `Header.within1` not asking for a lower-case name).
def Decl.lexicalLoose1: Decl → Bool
  | Definition _ header (Assigned _ value) =>
    (header.name.lexesAs Lower || header.name.lexesAs Upper) && header.result.lexical1 && value.lexical1
  | _ => False

def SourceFile.lexicalLoose1 (file: SourceFile): Bool := file.decls.all Decl.lexicalLoose1

--| What a declaration the parser gives is, when it is within slice 1.
def DeclOk (decl: Decl): Prop := decl.within1 = True → decl.shaped1 = True ∧ decl.lexicalLoose1 = True

theorem declOut ∀ [decl: Decl] (out: DeclOut decl): DeclOk decl := within =>
  (Bool.falseNotTrue (rewrite out at within)).impossible

theorem headerResultWithin ∀ (header: Header) (within: header.within1 = True): header.result.within1 = True :=
  match header with
    | {
        exportKeyword,
        opaqueKeyword,
        kind,
        keyword,
        name,
        forallKeyword,
        params,
        colon,
        result,
        decreasingClause,
        unfoldingClause
      } =>
      match exportKeyword, opaqueKeyword, kind, forallKeyword, params, decreasingClause, unfoldingClause, within with
        | None, None, DefPlain, None, [], None, None, within => within
        | other, others, kinds, foralls, parameters, decreasings, unfoldings, within =>
          (Bool.falseNotTrue within).impossible

theorem definitionOk ∀ (attributes: List Attributes) (header: Header) (body: DefBody)
    (parts: PartsOk (header, body)):
    DeclOk (Definition attributes header body) :=
  within =>
    match attributes, body, parts with
      | [], Assigned colonEq value, (resultParsed, nameOk, valueParsed) =>
        let (headerWithin, valueWithin) := within
        let (resultShaped, resultLexical, resultHigh) := resultParsed (headerResultWithin header headerWithin)
        let (valueShaped, valueLexical, valueHigh) := valueParsed valueWithin
        (Both resultShaped valueShaped, Both nameOk (Both resultLexical valueLexical))

theorem givesDefinition ∀ (modes: Modes) (attributes: List Attributes) (exportKeyword opaqueKeyword: Option Comments)
    (nested: Nested expressionAt) (outside: Outside expressionAt) (frame: Frame expressionAt):
    Parse.Gives GoodItems (() => definition modes attributes exportKeyword opaqueKeyword) DeclOk :=
  Parse.givesThen
    [p := () => definitionParts expressionAt modes exportKeyword opaqueKeyword None]
    [j := parts => definitionOf attributes parts]
    (givesDefinitionParts expressionAt modes exportKeyword opaqueKeyword None nested outside frame)
    (parts ok => match parts, ok with | (header, body), ok => Parse.givesDone (definitionOk attributes header body ok))

theorem givesDeclarationBody ∀ (modes: Modes) (attributes: List Attributes) (nested: Nested expressionAt)
    (outside: Outside expressionAt) (frame: Frame expressionAt):
    Parse.Gives GoodItems (() => declarationBody modes attributes) DeclOk :=
  givesAfter0 [p := () => modes.peek] [j := seen => declarationBodyOn modes attributes seen] (reads0Peek modes) (seen =>
    match seen with
      | Some kind =>
        match isDef: kind == KwDef || kind == KwTheorem with
          | True => givesDefinition modes attributes None None nested outside frame
          | False => Parse.givesWeaken (frame.others modes attributes (Some kind)) (decl out => declOut out)
      | None => Parse.givesWeaken (frame.others modes attributes None) (decl out => declOut out))

theorem givesDeclarationKind ∀ (seen: Seen) (modes: Modes) (attributes: List Attributes) (nested: Nested expressionAt)
    (outside: Outside expressionAt) (frame: Frame expressionAt):
    Parse.Gives GoodItems (() => declarationKind seen modes attributes modes.peek) DeclOk :=
  givesAfter0
    [p := () => modes.peek]
    [j := next => declarationKind seen modes attributes next]
    (reads0Peek modes)
    (next =>
      match next with
        | Some kind =>
          match isNamespace: kind == KwNamespace with
            | True => Parse.givesWeaken (frame.namespaces seen modes) (decl out => declOut out)
            | False =>
              match isImport: kind == KwImport with
                | True => Parse.givesWeaken (frame.imports seen modes) (decl out => declOut out)
                | False => givesDeclarationBody modes attributes nested outside frame
        | None => givesDeclarationBody modes attributes nested outside frame)

theorem givesDeclarationFinish ∀ (modes: Modes) (decl: Decl)
    (ok: DeclOk decl):
    Parse.Gives GoodItems (() => declarationFinish modes decl) DeclOk :=
  givesAfter0 [p := () => left()] [j := items => declarationEnd modes decl items] reads0Left (items =>
    match items.isEmpty with
      | True => Parse.givesDone ok
      | False => givesFail modes _)

theorem givesDeclaration ∀ (seen: Seen) (nested: Nested expressionAt)
    (outside: Outside expressionAt) (frame: Frame expressionAt):
    Parse.Gives GoodItems (() => declaration seen) DeclOk :=
  Parse.givesThen
    [p := () => attributesOf Modes.start]
    [j := attributes => declarationAttributes seen Modes.start attributes]
    (frame.attributes Modes.start)
    (attributes _ =>
      givesAfter0
        [p := () => Modes.start.peek]
        [j := next => declarationRefusal seen Modes.start attributes next]
        (reads0Peek Modes.start)
        (next =>
          match attributesRefused attributes next with
            | Some message => Parse.readsFatal _ _
            | None =>
              Parse.givesThen
                [p := () => declarationKind seen Modes.start attributes Modes.start.peek]
                [j := decl => declarationFinish Modes.start decl]
                (givesDeclarationKind seen Modes.start attributes nested outside frame)
                (decl ok => givesDeclarationFinish Modes.start decl ok)))

-- A file.

--| What a parser gives, `Parse.run` from good items gives.
theorem runGives ∀ (input: List Item) (p: () → {Parse Item} a) (holds: a → Prop)
    (gives: Parse.Gives GoodItems p holds)
    (fits: Parse.Fits Item GoodItems input) (value: a)
    (h: Parse.run input (() =>
      let found := p()
      found)
      = Ok value):
    holds value :=
  match Parse.runFromThenOk p (Parse.State.start input) (found => found) value h with
    | Witness found (Witness middle (Both ran rest)) =>
      match gives
        (Parse.State.start input).at
        fits
        input.length
        (Parse.State.start input)
        found
        middle.at
        byComputing
        (Both byComputing (arithmetic []))
        ran with
        | Witness read (Both starts (Both honest proved)) =>
          let same: found = value := Result.okInjective rest
          rewrite <- same then proved

theorem groupLoweredOk ∀ (seen: Seen) (rest: List (List Leaf)) (found decls: List Decl)
    (decl: Decl) (lowering: Option Text)
    (declOk: DeclOk decl)
    (foundOk: List.All DeclOk found)
    (again: ∀ (next: Seen) (more: List Decl) => List.All DeclOk more
      → parseGroups next rest more = Ok decls
      → List.All DeclOk decls)
    (parses: groupLowered seen rest found decl lowering = Ok decls):
    List.All DeclOk decls :=
  match lowering, parses with
    | Some message, parses => (Result.errNotOk parses).impossible
    | None, parses => again (seen.after decl) [decl, ..found] (declOk, foundOk) parses

theorem groupRanOk ∀ (seen: Seen) (rest: List (List Leaf)) (found decls: List Decl)
    (ran: Result Decl Parse.Failure) (ranOk: ∀ (decl: Decl) => ran = Ok decl → DeclOk decl)
    (foundOk: List.All DeclOk found)
    (again: ∀ (next: Seen) (more: List Decl) => List.All DeclOk more
      → parseGroups next rest more = Ok decls
      → List.All DeclOk decls)
    (parses: groupRan seen rest found ran = Ok decls):
    List.All DeclOk decls :=
  match ran, ranOk, parses with
    | Err failure, ranOk, parses => (Result.errNotOk parses).impossible
    | Ok decl, ranOk, parses =>
      groupLoweredOk seen rest found decls decl decl.loweringError (ranOk decl byComputing) foundOk again parses

theorem parseGroupsOk ∀ (outside: OutsideGives) (frame: Frame expressionAt) (seen: Seen)
    (groups: List (List Leaf)) (found decls: List Decl)
    (good: List.All (group => List.All GoodItem (items group)) groups)
    (foundOk: List.All DeclOk found)
    (parses: parseGroups seen groups found = Ok decls):
    List.All DeclOk decls :=
  match groups, good, parses with
    | [], good, parses =>
      let same: found.reverse = decls := Result.okInjective parses
      rewrite <- same then List.allReverse DeclOk found foundOk
    | [group, ..rest], (groupGood, restGood), parses =>
      let nested: Nested expressionAt := givesExpressionAt outside
      groupRanOk seen rest found decls
        (Parse.run (items group) (() =>
          let decl := declaration seen
          decl))
        (decl ran =>
          runGives
            (items group)
            (() => declaration seen)
            DeclOk
            (givesDeclaration seen nested (outside expressionAt nested) frame)
            { holds = groupGood }
            decl
            ran)
        foundOk
        (following more moreOk again => parseGroupsOk outside frame following rest more decls restGood moreOk again)
        parses

theorem fileEndOk ∀ (lexed: Lexed) (parsed: Result (List Decl) Text)
    (file: SourceFile) (good: ∀ (decls: List Decl) => parsed = Ok decls → List.All DeclOk decls)
    (parses: fileEnd lexed parsed = Ok file):
    List.All DeclOk file.decls :=
  match parsed, good, parses with
    | Ok decls, good, parses =>
      let same: { decls, end = lexed.end.comments } = file := Result.okInjective parses
      rewrite <- same then good decls byComputing
    | Err message, good, parses => (Result.errNotOk parses).impossible

--| The declarations of a file that parses from good items are each as `DeclOk` says.
theorem parseFileOk ∀ (outside: OutsideGives) (frame: Frame expressionAt) (lexed: Lexed) (file: SourceFile)
    (good: List.All (group => List.All GoodItem (items group)) (groupsOf lexed.leaves))
    (parses: parseFile lexed = Ok file):
    List.All DeclOk file.decls :=
  match fileRefusal lexed.leaves, parses with
    | Some message, parses => (Result.errNotOk parses).impossible
    | None, parses =>
      fileEndOk lexed
        (parseGroups Seen.start (groupsOf lexed.leaves) [])
        file
        (decls ran => parseGroupsOk outside frame Seen.start (groupsOf lexed.leaves) [] decls good () ran)
        parses

theorem declsShapedLoose ∀ (decls: List Decl)
    (ok: List.All DeclOk decls)
    (within: decls.all Decl.within1 = True):
    decls.all Decl.shaped1 = True ∧ decls.all Decl.lexicalLoose1 = True :=
  match decls, ok, within with
    | [], ok, within => (byComputing, byComputing)
    | [decl, ..rest], (declOk, restOk), (Both declWithin restWithin) =>
      let (declShaped, declLexical) := declOk declWithin
      let (restShaped, restLexical) := declsShapedLoose rest restOk restWithin
      (Both declShaped restShaped, Both declLexical restLexical)

--| Every declaration of a file of slice 1 that the parser gives is shaped (`Shaped1`, `Decl.shaped1`).
--|
--| It assumes what the parsers outside slice 1 give (`OutsideGives`, `Frame`), which SW-4000 proves, and that every
--| item of every declaration's group is good (the lexer's spelling, `GoodItem`).
theorem parseShaped1 ∀ (outside: OutsideGives) (frame: Frame expressionAt) (lexed: Lexed) (file: SourceFile)
    (good: List.All (group => List.All GoodItem (items group)) (groupsOf lexed.leaves))
    (parses: parseFile lexed = Ok file)
    (within: file.within1 = True):
    file.shaped1 = True :=
  (declsShapedLoose file.decls (parseFileOk outside frame lexed file good parses) within).left

--| Every declaration's words lex as their kinds, but for a name: `def Foo: Nat := 1` is in slice 1 with an
--| upper-case name, which `Decl.lexical1` doesn't allow.
theorem parseLexicalLoose1 ∀ (outside: OutsideGives) (frame: Frame expressionAt) (lexed: Lexed) (file: SourceFile)
    (good: List.All (group => List.All GoodItem (items group)) (groupsOf lexed.leaves))
    (parses: parseFile lexed = Ok file)
    (within: file.within1 = True):
    file.lexicalLoose1 = True :=
  (declsShapedLoose file.decls (parseFileOk outside frame lexed file good parses) within).right

--| A definition's name lexes as a lower-case name.
def Decl.lowerNamed1: Decl → Bool
  | Definition _ header _ => header.name.lexesAs Lower
  | _ => True

def SourceFile.lowerNamed1 (file: SourceFile): Bool := file.decls.all Decl.lowerNamed1

theorem lexicalOfLoose ∀ (decl: Decl)
    (loose: decl.lexicalLoose1 = True)
    (lower: decl.lowerNamed1 = True):
    decl.lexical1 = True :=
  match decl, loose, lower with
    | Definition attributes header (Assigned colonEq value), (Both named (Both result value1)), lower =>
      Both lower (Both result value1)
    | Definition attributes header Primitive, loose, lower => (Bool.falseNotTrue loose).impossible
    | Definition attributes header (Arms arms), loose, lower => (Bool.falseNotTrue loose).impossible
    | Namespace keyword name, loose, lower => (Bool.falseNotTrue loose).impossible
    | Import keyword path open imported close, loose, lower => (Bool.falseNotTrue loose).impossible
    | Data attributes isInterface keyword name params indices body, loose, lower => (Bool.falseNotTrue loose).impossible
    | Ability keyword name params whereKeyword operations, loose, lower => (Bool.falseNotTrue loose).impossible
    | Test keyword name colonEq body, loose, lower => (Bool.falseNotTrue loose).impossible
    | RuleSetDecl keyword name colonEq set, loose, lower => (Bool.falseNotTrue loose).impossible

theorem declsLexical ∀ (decls: List Decl)
    (loose: decls.all Decl.lexicalLoose1 = True)
    (lower: decls.all Decl.lowerNamed1 = True):
    decls.all Decl.lexical1 = True :=
  match decls, loose, lower with
    | [], loose, lower => byComputing
    | [decl, ..rest], (Both declLoose restLoose), (Both declLower restLower) =>
      Both (lexicalOfLoose decl declLoose declLower) (declsLexical rest restLoose restLower)

--| Every word of the file lexes as one token of its kind, for a file whose definitions are named in lower case.
theorem parseLexical1 ∀ (outside: OutsideGives) (frame: Frame expressionAt) (lexed: Lexed) (file: SourceFile)
    (good: List.All (group => List.All GoodItem (items group)) (groupsOf lexed.leaves))
    (parses: parseFile lexed = Ok file)
    (within: file.within1 = True)
    (lower: file.lowerNamed1 = True):
    file.lexical1 = True :=
  declsLexical file.decls (parseLexicalLoose1 outside frame lexed file good parses within) lower
