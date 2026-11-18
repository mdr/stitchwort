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

-- What the parsers outside slice 1 give. Each is `Out` (the tree is outside the slice) or `True` (the tree is wrapped in
-- a node that is). `outsideOf` and `frameOf` prove most of them; `OutsideRest` and `FrameRest` are what is still
-- assumed (SW-4000's follow-up).

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

--| The parsers outside slice 1 that SW-4000 has not yet proved give what `Outside` says of them; the rest of
--| `Outside` is proved below (`outsideOf`).
type OutsideRest (self: Goal → {Parse Item} Expr) = {
  matches: ∀ (modes: Modes) (keyword: Word) => Parse.Gives GoodItems (() => matchExpr self modes keyword) Out,
  clauseLambdas: ∀ (modes: Modes) (keyword: Word) => Parse.Gives GoodItems
    (() => clauseLambda self modes keyword None ClauseMatches)
    Out,
  braceArguments: ∀ (modes: Modes) => Parse.Gives GoodItems (() => braceArgument self modes) Out,
  memberships: ∀ (modes: Modes) (first: Option Tok) (element: Expr) => Parse.Gives GoodItems
    (() => membership self modes first element)
    Out,
  comparisonChains: ∀ (modes: Modes) (lhs: Expr) (kind: Tok) (operator: Word) (second: Expr) => Parse.Gives GoodItems
    (() => comparisonChain self modes lhs kind operator second)
    Out,
  pipeChains: ∀ (modes: Modes) (indent: Nat) (value: Expr) => Parse.Gives GoodItems
    (() => pipeChain self modes indent value)
    (result => result = value ∨ Out result),
  iffs: ∀ (modes: Modes) (logic: Expr) => Parse.Gives GoodItems (() => iff self modes logic) Out,
  calcs: ∀ (modes: Modes) => Parse.Gives GoodItems (() => calcExpr self modes) Out,
  rewrites: ∀ (modes: Modes) => Parse.Gives GoodItems (() => rewriteExpr self modes) Out
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

-- The parsers outside slice 1, proved.

theorem givesSemiAfter ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (value: Expr) (semicolon: Word)
    (nested: Nested self) (seen: Option Tok):
    Parse.Gives GoodItems (() => semiAfter self modes value semicolon seen) Out :=
  match seen with
    | None => Parse.readsFatal _ _
    | Some RParen => Parse.readsFatal _ _
    | Some RBracket => Parse.readsFatal _ _
    | Some RBrace => Parse.readsFatal _ _
    | Some Comma => Parse.readsFatal _ _
    | Some other =>
      Parse.givesThen
        [p := () => self { modes, level = LevelFull }]
        [j := tail => Infix InfixSeq value semicolon tail]
        (nested { modes, level = LevelFull })
        (tail parsed => Parse.givesDone byComputing)

theorem givesSemi ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (value: Expr)
    (nested: Nested self):
    Parse.Gives GoodItems (() => semiExpr self modes value) Out :=
  Parse.givesThen
    [p := () => bump()]
    [j := semicolon => semiAfter self modes value semicolon modes.peek]
    givesBump
    (semicolon _ =>
      givesAfter0
        [p := () => modes.peek]
        [j := seen => semiAfter self modes value semicolon seen]
        (reads0Peek modes)
        (seen => givesSemiAfter self modes value semicolon nested seen))

--| `expect` gives the word of a token of any kind it was asked for.
theorem givesExpectAny ∀ (modes: Modes) (wanted: Tok) (what: Text):
    Parse.Gives GoodItems (() => modes.expect wanted what) (word => True) :=
  readsInPeeked modes
    (seen => modes.expectOn wanted what seen) _
    (start fine stops => givesFail modes what start fine)
    (start item later shape fine stopped =>
      match took: isSome wanted (Some item.kind) with
        | False => givesFail modes what start fine
        | True => Parse.readsAtWeaken (readsAtBump shape) (read word (single, same) => byComputing))

theorem givesAnnotatedEnd ∀ (inner: Modes) (open: Word) (first: Expr) (colon: Word) (annotation: Expr) (comma: Bool):
    Parse.Gives GoodItems (() => annotatedEnd inner open first colon annotation comma) Out :=
  match comma with
    | True => Parse.readsFatal _ _
    | False =>
      Parse.givesThen
        [p := () => inner.expect RParen "`)`"]
        [j := close => Annotation open first colon annotation close]
        (givesExpectAny inner RParen "`)`")
        (close _ => Parse.givesDone byComputing)

theorem givesAnnotated ∀ (self: Goal → {Parse Item} Expr) (inner: Modes) (open: Word) (first: Expr)
    (nested: Nested self):
    Parse.Gives GoodItems (() => annotated self inner open first) Out :=
  Parse.givesThen
    [p := () => bump()]
    [j := colon => annotatedEnd inner open first colon (full self inner) (inner.at Comma)]
    givesBump
    (colon _ =>
      Parse.givesThen
        [p := () => self { modes = inner, level = LevelFull }]
        [j := annotation => annotatedEnd inner open first colon annotation (inner.at Comma)]
        (nested { modes = inner, level = LevelFull })
        (annotation _ =>
          givesAfter0
            [p := () => inner.at Comma]
            [j := comma => annotatedEnd inner open first colon annotation comma]
            (reads0At inner Comma)
            (comma => givesAnnotatedEnd inner open first colon annotation comma)))

theorem givesLower ∀ (modes: Modes) (what: Text): Parse.Gives GoodItems (() => modes.lower what) (word => True) :=
  givesAfter0 [p := () => left()] [j := items => modes.lowerOn what items] reads0Left (items =>
    match items with
      | [item, ..rest] =>
        match named: item.kind == Lower && !modes.stops item with
          | True =>
            match qualified: isQualified item with
              | True => Parse.readsFatal _ _
              | False => givesBump
          | False => givesFailName modes what
      | [] => givesFailName modes what)

theorem givesNamedClose ∀ (inner: Modes) (open name colonEq: Word) (value: Expr) (closer: Tok) (closeText: Text):
    Parse.Gives GoodItems (() => namedClose inner open name colonEq value closer closeText) Out :=
  Parse.givesThen
    [p := () => inner.expect closer closeText]
    [j := close => NamedArg open name colonEq value close]
    (givesExpectAny inner closer closeText)
    (close _ => Parse.givesDone byComputing)

theorem givesNamedColon ∀ (self: Goal → {Parse Item} Expr) (inner: Modes) (open name: Word)
    (closer: Tok) (closeText: Text)
    (nested: Nested self):
    Parse.Gives GoodItems (() => namedColon self inner open name closer closeText) Out :=
  Parse.givesThen
    [p := () => bump()]
    [j := colonEq => namedClose inner open name colonEq (full self inner) closer closeText]
    givesBump
    (colonEq _ =>
      Parse.givesThen
        [p := () => self { modes = inner, level = LevelFull }]
        [j := value => namedClose inner open name colonEq value closer closeText]
        (nested { modes = inner, level = LevelFull })
        (value _ => givesNamedClose inner open name colonEq value closer closeText))

theorem givesNamedHead ∀ (self: Goal → {Parse Item} Expr) (inner: Modes) (open: Word) (closer: Tok) (closeText: Text)
    (nested: Nested self) (clause: Bool):
    Parse.Gives GoodItems (() => namedHead self inner open closer closeText clause) Out :=
  match clause with
    | True =>
      Parse.givesThen
        [p := () => bump()]
        [j := name => namedColon self inner open name closer closeText]
        givesBump
        (name _ => givesNamedColon self inner open name closer closeText nested)
    | False =>
      Parse.givesThen
        [p := () => inner.lower "a name"]
        [j := name => namedColon self inner open name closer closeText]
        (givesLower inner "a name")
        (name _ => givesNamedColon self inner open name closer closeText nested)

theorem givesNamedArgument ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (closer: Tok) (closeText: Text)
    (nested: Nested self):
    Parse.Gives GoodItems (() => namedArgument self modes closer closeText) Out :=
  Parse.givesThen
    [p := () => bump()]
    [j := open => namedHead self modes.inBrackets open closer closeText (modes.inBrackets.at KwDecreasing)]
    givesBump
    (open _ =>
      givesAfter0
        [p := () => modes.inBrackets.at KwDecreasing]
        [j := clause => namedHead self modes.inBrackets open closer closeText clause]
        (reads0At modes.inBrackets KwDecreasing)
        (clause => givesNamedHead self modes.inBrackets open closer closeText nested clause))

--| A gap is an error, which gives anything.
theorem givesGap ∀ (modes: Modes) (message: Text) [holds: a → Prop]:
    Parse.Gives GoodItems (() => modes.gap message) holds :=
  givesAfter0 [p := () => left()] [j := items => modes.gapOn message items] reads0Left (items =>
    match blockEnd modes.lines items.head with
      | Some ending => Parse.readsFatal _ _
      | None => Parse.readsFatal _ _)

theorem reads0RanOutAtLine ∀ (modes: Modes): Reads0 (() => ranOutAtLine modes) :=
  reads0Then [p := () => modes.peek] (reads0Peek modes) (seen =>
    reads0Then [p := () => left()] reads0Left (items => reads0Done (ranOutOn modes seen items)))

theorem givesAtomGap ∀ (modes: Modes) (ran: Bool): Parse.Gives GoodItems (() => atomGap modes ran) Out := match ran with
  | True => givesGap modes ranOutLine
  | False =>
    Parse.givesThen
      [p := () => modes.unexpected "an expression"]
      [j := message => modes.gap message]
      (givesUnexpected modes "an expression")
      (message _ => givesGap modes message)

theorem givesAtomNamed ∀ (modes: Modes) (second: Option Tok):
    Parse.Gives GoodItems (() => atomNamed modes second) Out :=
  match isSome FatArrow second with
    | True => givesFailName modes "an expression"
    | False => givesFail modes "an expression"

theorem givesAtomMissing ∀ (self: Goal → {Parse Item} Expr) (modes: Modes):
    Parse.Gives GoodItems (() => atomMissing self modes) Out :=
  givesAfter0 [p := () => modes.peek] [j := seen => atomMissingAt modes seen] (reads0Peek modes) (seen =>
    match modes.recover && seen.isNone with
      | True =>
        givesAfter0 [p := () => ranOutAtLine modes] [j := ran => atomGap modes ran] (reads0RanOutAtLine modes) (ran =>
          givesAtomGap modes ran)
      | False =>
        givesAfter0
          [p := () => modes.peekAt 1]
          [j := second => atomNamed modes second]
          (reads0PeekAt modes 1)
          (second => givesAtomNamed modes second))

theorem givesNamedBinder ∀ (modes: Modes): Parse.Gives GoodItems (() => namedBinder modes) (found => True) :=
  givesAfter0
    [p := () => modes.at Lower]
    [j := lower => namedBinderOn modes lower (modes.peekAt 1)]
    (reads0At modes Lower)
    (lower =>
      givesAfter0
        [p := () => modes.peekAt 1]
        [j := second => namedBinderOn modes lower second]
        (reads0PeekAt modes 1)
        (second =>
          match lower && isSome Colon second with
            | True => Parse.givesThen (givesLower modes "a name") (name _ =>
              Parse.givesThen givesBump (colon _ => Parse.givesDone byComputing))
            | False => Parse.givesDone byComputing))

theorem givesExpectKeyword ∀ (modes: Modes) (wanted: Tok) (what: Text) (indent: Nat):
    Parse.Gives GoodItems (() => modes.expectKeyword wanted what indent) (word => True) :=
  givesAfter0
    [p := () => modes.peek]
    [j := seen => modes.expectKeywordOn wanted what indent seen left()]
    (reads0Peek modes)
    (seen =>
      givesAfter0
        [p := () => left()]
        [j := items => modes.expectKeywordOn wanted what indent seen items]
        reads0Left
        (items =>
          match seen, items with
            | None, [item, ..rest] =>
              match line: item.kind == wanted && item.leaf.token.lineStart && item.leaf.token.column >= indent with
                | True => givesBump
                | False => givesExpectAny modes wanted what
            | None, [] => givesExpectAny modes wanted what
            | Some kind, others => givesExpectAny modes wanted what))

theorem givesIf ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (indent: Nat) (keyword: Word)
    (nested: Nested self):
    Parse.Gives GoodItems (() => ifExpr self modes indent keyword) Out :=
  Parse.givesThen (givesNamedBinder modes) (binder _ =>
    Parse.givesThen (nested { modes = modes.sealed, level = LevelFull }) (condition _ =>
      Parse.givesThen (givesExpectKeyword modes KwThen "`then`" indent) (thenKeyword _ =>
        Parse.givesThen (nested { modes = modes.sealed, level = LevelFull }) (whenTrue _ =>
          Parse.givesThen (givesExpectKeyword modes KwElse "`else`" indent) (elseKeyword _ =>
            Parse.givesThen (nested { modes, level = LevelFull }) (tail _ => Parse.givesDone byComputing))))))

theorem givesIfKeyword ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self):
    Parse.Gives GoodItems (() => ifKeyword self modes) Out :=
  givesAfter0 reads0HeadIndent (indent =>
    Parse.givesThen givesBump (keyword _ => givesIf self modes indent keyword nested))

--| What `self` gives at some goal, nothing is known of.
theorem givesSelfAny ∀ (self: Goal → {Parse Item} Expr)
    (nested: Nested self) (goal: Goal):
    Parse.Gives GoodItems (() => self goal) (expr => True) :=
  Parse.givesWeaken (nested goal) (found parsed => byComputing)

theorem givesSectionOperand ∀ (self: Goal → {Parse Item} Expr) (inner: Modes) (operatorKind: Tok)
    (nested: Nested self):
    Parse.Gives GoodItems (() => sectionOperand self inner operatorKind) (expr => True) :=
  match operatorKind with
    | Plus => givesSelfAny self nested { modes = inner, level = LevelMultiplicative }
    | Star => givesSelfAny self nested { modes = inner, level = LevelUnary }
    | Slash => givesSelfAny self nested { modes = inner, level = LevelUnary }
    | Percent => givesSelfAny self nested { modes = inner, level = LevelUnary }
    | AndAnd => givesSelfAny self nested { modes = inner, level = LevelComparison }
    | OrOr => Parse.givesThen (givesSelfAny self nested { modes = inner, level = LevelComparison }) (first _ =>
      Parse.givesThen
        [p := () =>
          operatorLinks inner (kind => kind == AndAnd) (() => self { modes = inner, level = LevelComparison })]
        [j := links => rightNested first links]
        (Parse.givesWeaken
          [weaker := links => True]
          (Parse.givesLoop
            (givesOperatorStep inner
              (kind => kind == AndAnd)
              (() => self { modes = inner, level = LevelComparison })
              6
              (link => True)
              (chosen value good took parsed => byComputing)
              (nested { modes = inner, level = LevelComparison })))
          (links ok => byComputing))
        (links _ => Parse.givesDone byComputing))
    | IffArrow => givesSelfAny self nested { modes = inner, level = LevelLogic }
    | other => givesSelfAny self nested { modes = inner, level = LevelAppend }

theorem givesOperatorClose ∀ (open operator: Word) (operand: Option Expr):
    Parse.Gives GoodItems (() => operatorClose open operator operand) Out :=
  Parse.givesThen
    [p := () => bump()]
    [j := close => OperatorSection open None operator operand close]
    givesBump
    (close _ => Parse.givesDone byComputing)

theorem givesOperatorEnd ∀ (inner: Modes) (open operator: Word) (operand: Expr) (closed: Bool):
    Parse.Gives GoodItems (() => operatorEnd inner open operator operand closed) Out :=
  match closed with
    | True => givesOperatorClose open operator (Some operand)
    | False => givesFail inner "`)` after the operand of a section"

theorem givesOperatorHead ∀ (self: Goal → {Parse Item} Expr) (inner: Modes) (open: Word)
    (operatorKind: Tok) (operator: Word)
    (nested: Nested self) (closed: Bool):
    Parse.Gives GoodItems (() => operatorHead self inner open operatorKind operator closed) Out :=
  match closed with
    | True => givesOperatorClose open operator None
    | False => Parse.givesThen (givesSectionOperand self inner operatorKind nested) (operand _ =>
      givesAfter0
        [p := () => inner.at RParen]
        [j := closed => operatorEnd inner open operator operand closed]
        (reads0At inner RParen)
        (closed => givesOperatorEnd inner open operator operand closed))

theorem givesOperatorFirst ∀ (self: Goal → {Parse Item} Expr) (inner: Modes) (open: Word) (items: List Item)
    (nested: Nested self):
    Parse.Gives GoodItems (() => operatorFirst self inner open items) Out :=
  Parse.givesThen givesBump (operator _ =>
    givesAfter0
      [p := () => inner.at RParen]
      [j := closed => operatorHead self inner open _ operator closed]
      (reads0At inner RParen)
      (closed => givesOperatorHead self inner open _ operator nested closed))

theorem givesOperatorSection ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self):
    Parse.Gives GoodItems (() => operatorSection self modes) Out :=
  Parse.givesThen givesBump (open _ =>
    givesAfter0 [p := () => left()] [j := items => operatorFirst self modes.inBrackets open items] reads0Left (items =>
      givesOperatorFirst self modes.inBrackets open items nested))

theorem givesRightOperand ∀ (self: Goal → {Parse Item} Expr) (inner: Modes) (operatorKind: Tok)
    (nested: Nested self):
    Parse.Gives GoodItems (() => rightOperand self inner operatorKind) (found => True) :=
  match operatorKind with
    | Plus => givesSelfAny self nested { modes = inner, level = LevelMultiplicative }
    | Star => givesSelfAny self nested { modes = inner, level = LevelUnary }
    | Slash => givesSelfAny self nested { modes = inner, level = LevelUnary }
    | Percent => givesSelfAny self nested { modes = inner, level = LevelUnary }
    | PlusPlus => givesSelfAny self nested { modes = inner, level = LevelAdditive }
    | AndAnd => givesSelfAny self nested { modes = inner, level = LevelComparison }
    | OrOr => givesSelfAny self nested { modes = inner, level = LevelComparison }
    | IffArrow => givesSelfAny self nested { modes = inner, level = LevelComparison }
    | other => givesSelfAny self nested { modes = inner, level = LevelAppend }

theorem givesRightClose ∀ (inner: Modes) (open: Word) (operand: Expr) (operator: Word):
    Parse.Gives GoodItems (() => rightClose inner open operand operator) Out :=
  Parse.givesThen
    [p := () => inner.expect RParen "`)`"]
    [j := close => OperatorSection open (Some operand) operator None close]
    (givesExpectAny inner RParen "`)`")
    (close _ => Parse.givesDone byComputing)

theorem givesRightEnd ∀ (inner: Modes) (open: Word) (inside start: Nat) (operand: Expr) (here: Nat):
    Parse.Gives GoodItems (() => rightEnd inner open inside start operand here) Out :=
  match here != start + inside - 1 with
    | True => givesFail inner "`)` after the operator of a section"
    | False => Parse.givesThen givesBump (operator _ => givesRightClose inner open operand operator)

theorem givesRightKind ∀ (self: Goal → {Parse Item} Expr) (inner: Modes) (open: Word)
    (inside start: Nat) (items: List Item)
    (nested: Nested self):
    Parse.Gives GoodItems (() => rightKind self inner open inside start items) Out :=
  Parse.givesThen
    [p := () =>
      rightOperand self inner
        (match items.drop (inside - 1) with
          | [item, .._] => item.kind
          | [] => Plus)]
    [j := operand => rightEnd inner open inside start operand offset()]
    (givesRightOperand self inner _ nested)
    (operand _ =>
      givesAfter0
        [p := () => offset()]
        [j := here => rightEnd inner open inside start operand here]
        reads0Offset
        (here => givesRightEnd inner open inside start operand here))

theorem givesRightSection ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (inside: Nat)
    (nested: Nested self):
    Parse.Gives GoodItems (() => rightSection self modes inside) Out :=
  Parse.givesThen givesBump (open _ =>
    givesAfter0
      [p := () => offset()]
      [j := start => rightKind self modes.inBrackets open inside start left()]
      reads0Offset
      (start =>
        givesAfter0
          [p := () => left()]
          [j := items => rightKind self modes.inBrackets open inside start items]
          reads0Left
          (items => givesRightKind self modes.inBrackets open inside start items nested)))

theorem givesCmpIf ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (lhs: Expr) (operator: Word)
    (nested: Nested self):
    Parse.Gives GoodItems (() => cmpIf self modes lhs operator) Out :=
  givesAfter0 reads0HeadIndent (indent =>
    Parse.givesThen
      [p := () => bump()]
      [j := keyword => Infix InfixBinary lhs operator (ifExpr self modes indent keyword)]
      givesBump
      (keyword _ =>
        Parse.givesThen
          [p := () => ifExpr self modes indent keyword]
          [j := tail => Infix InfixBinary lhs operator tail]
          (givesIf self modes indent keyword nested)
          (tail out => Parse.givesDone (Bool.andFalseRight lhs.within1 tail.within1 out))))

theorem givesParenOther ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (second third: Option Tok)
    (nested: Nested self):
    Parse.Gives GoodItems (() => parenOther self modes second third) Out :=
  match isSome RParen second with
    | True => Parse.givesThen [p := () => bump()] [j := open => Unit open bump()] givesBump (open _ =>
      Parse.givesThen [p := () => bump()] [j := close => Unit open close] givesBump (close _ =>
        Parse.givesDone byComputing))
    | False =>
      match isSome Lower second && isSome ColonEq third with
        | True => givesNamedArgument self modes RParen "`)`" nested
        | False => givesOperatorSection self modes nested

theorem givesRecordFieldAfter ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (name: Word)
    (nested: Nested self) (equalsNext: Bool):
    Parse.Gives GoodItems (() => recordFieldAfter self modes name equalsNext) (found => True) :=
  match equalsNext with
    | True =>
      Parse.givesThen
        [p := () => bump()]
        [j := equals => RecordField name equals (full self modes)]
        givesBump
        (equals _ =>
          Parse.givesThen
            [p := () => self { modes, level = LevelFull }]
            [j := value => RecordField name equals value]
            (nested { modes, level = LevelFull })
            (value _ => Parse.givesDone byComputing))
    | False => Parse.givesDone byComputing

theorem givesRecordField ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self):
    Parse.Gives GoodItems (() => recordField self modes) (found => True) :=
  Parse.givesThen (givesLower modes "a field name") (name _ =>
    givesAfter0
      [p := () => modes.at Equals]
      [j := equalsNext => recordFieldAfter self modes name equalsNext]
      (reads0At modes Equals)
      (equalsNext => givesRecordFieldAfter self modes name nested equalsNext))

theorem givesRecordEnd ∀ (inner: Modes) (open: Word) (base: Option (Expr, Word)) (pair: (List Expr, Bool)):
    Parse.Gives GoodItems (() => recordEnd inner open base pair) Out :=
  match pair with
    | (fields, trailingComma) =>
      Parse.givesThen
        [p := () => inner.expect RBrace "`,` or `}`"]
        [j := close => Record open base fields trailingComma close]
        (givesExpectAny inner RBrace "`,` or `}`")
        (close _ => Parse.givesDone byComputing)

theorem givesRecordFields ∀ (self: Goal → {Parse Item} Expr) (inner: Modes) (open: Word) (base: Option (Expr, Word))
    (nested: Nested self):
    Parse.Gives GoodItems (() => recordFields self inner open base) Out :=
  Parse.givesThen (givesRecordField self inner nested) (first _ =>
    Parse.givesThen
      [p := () => Parse.mark()]
      [j := here =>
        recordEnd inner open base
          (commaList (here.left + 1) inner (count => inner.at RBrace) (() => recordField self inner) first [])]
      Parse.givesMark
      (here _ =>
        Parse.givesThen
          [p := () =>
            commaList (here.left + 1) inner (count => inner.at RBrace) (() => recordField self inner) first []]
          [j := pair => recordEnd inner open base pair]
          (givesCommaListFrom inner
            (count => inner.at RBrace)
            (() => recordField self inner)
            (found => True)
            (count => givesAt inner RBrace)
            (givesRecordField self inner nested)
            (here.left + 1)
            1
            first
            []
            byComputing
            ())
          (pair _ => givesRecordEnd inner open base pair)))

theorem givesRecordBase ∀ (self: Goal → {Parse Item} Expr) (inner: Modes)
    (nested: Nested self) (literal: Bool):
    Parse.Gives GoodItems (() => recordBase self inner literal) (found => True) :=
  match literal with
    | True => Parse.givesDone byComputing
    | False =>
      Parse.givesThen
        [p := () => self { modes = inner, level = LevelFull }]
        [j := record => recordPipe inner record]
        (nested { modes = inner, level = LevelFull })
        (record _ =>
          Parse.givesThen
            [p := () => inner.expect Pipe "`|` and the fields to update"]
            [j := bar => Some (record, bar)]
            (givesExpectAny inner Pipe "`|` and the fields to update")
            (bar _ => Parse.givesDone byComputing))

theorem givesRecordBody ∀ (self: Goal → {Parse Item} Expr) (inner: Modes) (open: Word)
    (nested: Nested self) (empty: Bool):
    Parse.Gives GoodItems (() => recordBody self inner open empty) Out :=
  match empty with
    | True => Parse.givesThen [p := () => bump()] [j := close => Record open None [] False close] givesBump (close _ =>
      Parse.givesDone byComputing)
    | False =>
      givesAfter0
        [p := () => inner.at Lower]
        [j := lower => recordLiteral self inner open lower (inner.peekAt 1)]
        (reads0At inner Lower)
        (lower =>
          givesAfter0
            [p := () => inner.peekAt 1]
            [j := second => recordLiteral self inner open lower second]
            (reads0PeekAt inner 1)
            (second =>
              Parse.givesThen
                [p := () => recordBase self inner (lower && literalSecond second)]
                [j := base => recordFields self inner open base]
                (givesRecordBase self inner nested (lower && literalSecond second))
                (base _ => givesRecordFields self inner open base nested)))

theorem givesRecordExpr ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self):
    Parse.Gives GoodItems (() => recordExpr self modes) Out :=
  Parse.givesThen (givesExpectAny modes LBrace "`{`") (open _ =>
    givesAfter0
      [p := () => modes.inBrackets.at RBrace]
      [j := empty => recordBody self modes.inBrackets open empty]
      (reads0At modes.inBrackets RBrace)
      (empty => givesRecordBody self modes.inBrackets open nested empty))

theorem givesExpectFixed ∀ (modes: Modes) (wanted: Tok) (what: Text):
    Parse.Gives GoodItems (() => modes.expectFixed wanted what) (comments => True) :=
  Parse.givesThen
    [p := () => modes.expect wanted what]
    [j := word => word.comments]
    (givesExpectAny modes wanted what)
    (found _ => Parse.givesDone byComputing)

theorem givesRowAbilities ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self) (closed pipe: Bool):
    Parse.Gives GoodItems (() => rowAbilities self modes closed pipe) (found => True) :=
  match closed || pipe with
    | True => Parse.givesDone byComputing
    | False => Parse.givesThen (nested { modes, level = LevelApp }) (first _ =>
      Parse.givesThen
        [p := () => Parse.mark()]
        [j := here =>
          rowEntries
            (commaList (here.left + 1) modes (count => False) (() => self { modes, level = LevelApp }) first [])]
        Parse.givesMark
        (here _ =>
          Parse.givesThen
            [p := () =>
              commaList (here.left + 1) modes (count => False) (() => self { modes, level = LevelApp }) first []]
            [j := pair => rowEntries pair]
            (givesCommaListFrom modes
              (count => False)
              (() => self { modes, level = LevelApp })
              (found => True)
              (count => Parse.givesDone byComputing)
              (givesSelfAny self nested { modes, level = LevelApp })
              (here.left + 1)
              1
              first
              []
              byComputing
              ())
            (pair _ => Parse.givesDone byComputing)))

theorem givesRowPart ∀ (modes: Modes) (pipe: Bool): Parse.Gives GoodItems (() => rowPart modes pipe) (found => True) :=
  match pipe with
    | True => Parse.givesThen givesFixedFrom (bar _ =>
      Parse.givesThen (givesLower modes "a row variable") (name _ => Parse.givesDone byComputing))
    | False => Parse.givesDone byComputing

theorem givesRowClose ∀ (modes: Modes) (open: Comments) (abilities: List Expr) (variable: Option (Comments, Word)):
    Parse.Gives GoodItems (() => rowClose modes open abilities variable) (row => True) :=
  Parse.givesThen
    [p := () => modes.expectFixed RBrace "`}`"]
    [j := close => { open, abilities, variable, close }]
    (givesExpectFixed modes RBrace "`}`")
    (close _ => Parse.givesDone byComputing)

theorem givesRowVariable ∀ (modes: Modes) (open: Comments) (abilities: List Expr):
    Parse.Gives GoodItems (() => rowVariable modes open abilities) (row => True) :=
  Parse.givesThen
    [p := () => rowPart modes (modes.at Pipe)]
    [j := variable => rowClose modes open abilities variable]
    (givesAfter0 [p := () => modes.at Pipe] [j := pipe => rowPart modes pipe] (reads0At modes Pipe) (pipe =>
      givesRowPart modes pipe))
    (variable _ => givesRowClose modes open abilities variable)

theorem givesRowStart ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (open: Comments)
    (nested: Nested self)
    (lower: Bool) (second: Option Tok):
    Parse.Gives GoodItems (() => rowStart self modes open lower second) (row => True) :=
  match lower && isSome Colon second with
    | True => Parse.readsFatal _ _
    | False =>
      Parse.givesThen
        [p := () => rowAbilities self modes (modes.at RBrace) (modes.at Pipe)]
        [j := abilities => rowVariable modes open abilities]
        (givesAfter0
          [p := () => modes.at RBrace]
          [j := closed => rowAbilities self modes closed (modes.at Pipe)]
          (reads0At modes RBrace)
          (closed =>
            givesAfter0
              [p := () => modes.at Pipe]
              [j := pipe => rowAbilities self modes closed pipe]
              (reads0At modes Pipe)
              (pipe => givesRowAbilities self modes nested closed pipe)))
        (abilities _ => givesRowVariable modes open abilities)

theorem givesRowOf ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self):
    Parse.Gives GoodItems (() => rowOf self modes) (row => True) :=
  Parse.givesThen (givesExpectFixed modes LBrace "`{`") (open _ =>
    givesAfter0
      [p := () => modes.at Lower]
      [j := lower => rowStart self modes open lower (modes.peekAt 1)]
      (reads0At modes Lower)
      (lower =>
        givesAfter0
          [p := () => modes.peekAt 1]
          [j := second => rowStart self modes open lower second]
          (reads0PeekAt modes 1)
          (second => givesRowStart self modes open nested lower second)))

theorem givesEffectResult ∀ (self: Goal → {Parse Item} Expr) (allowed: Modes)
    (nested: Nested self):
    Parse.Gives GoodItems (() => effectResult self allowed) Out :=
  Parse.givesThen (givesRowOf self allowed nested) (row _ =>
    Parse.givesThen
      [p := () => self { modes = allowed, level = LevelFull }]
      [j := tail => Effect row tail]
      (nested { modes = allowed, level = LevelFull })
      (tail _ => Parse.givesDone byComputing))

-- A list, read for nothing but that it is read.

theorem givesListItemsEndAny ∀ (self: Goal → {Parse Item} Expr) (inner: Modes) (open: Word) (pair: (List Expr, Bool)):
    Parse.Gives GoodItems (() => listItemsEnd self inner open pair) (found => True) :=
  match pair with
    | (items, trailingComma) =>
      Parse.givesThen
        [p := () => inner.expect RBracket "`,` or `]`"]
        [j := close => ListOf open items trailingComma close]
        (givesExpectAny inner RBracket "`,` or `]`")
        (close _ => Parse.givesDone byComputing)

theorem givesListItemAny ∀ (self: Goal → {Parse Item} Expr) (inner: Modes)
    (nested: Nested self):
    Parse.Gives GoodItems (() => listItem self inner) (found => True) :=
  Parse.givesWeaken (givesListItem self inner nested) (found parsed => byComputing)

theorem givesListItemsFromAny ∀ (self: Goal → {Parse Item} Expr) (inner: Modes) (open: Word) (first: Expr)
    (nested: Nested self):
    Parse.Gives GoodItems (() => listItemsFrom self inner open first) (found => True) :=
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
          (found => True)
          (count => givesAt inner RBracket)
          (givesListItemAny self inner nested)
          (here.left + 1)
          1
          first
          []
          byComputing
          ())
        (pair _ => givesListItemsEndAny self inner open pair))

theorem givesListItemsAny ∀ (self: Goal → {Parse Item} Expr) (inner: Modes) (open: Word)
    (nested: Nested self):
    Parse.Gives GoodItems (() => listItems self inner open) (found => True) :=
  Parse.givesThen
    [p := () => listItem self inner]
    [j := first => listItemsFrom self inner open first]
    (givesListItemAny self inner nested)
    (first _ => givesListItemsFromAny self inner open first nested)

theorem givesListAfterAny ∀ (self: Goal → {Parse Item} Expr) (inner: Modes) (open: Word)
    (nested: Nested self) (seen: Option Tok):
    Parse.Gives GoodItems (() => listAfter self inner open seen) (found => True) :=
  match seen with
    | None => givesListItemsAny self inner open nested
    | Some kind =>
      match isClose: kind == RBracket with
        | True => Parse.givesThen [p := () => bump()] [j := close => ListOf open [] False close] givesBump (close _ =>
          Parse.givesDone byComputing)
        | False => givesListItemsAny self inner open nested

theorem givesListExprAny ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self):
    Parse.Gives GoodItems (() => listExpr self modes) (found => True) :=
  Parse.givesThen givesBump (open _ =>
    givesAfter0
      [p := () => modes.inBrackets.peek]
      [j := seen => listAfter self modes.inBrackets open seen]
      (reads0Peek modes.inBrackets)
      (seen => givesListAfterAny self modes.inBrackets open nested seen))

-- The rest of what an atom can be.

theorem givesFactsEnd ∀ (kind: FactsKind) (keyword: Word) (list: Expr):
    Parse.Gives GoodItems (() => factsEnd kind keyword list) Out :=
  match hasSpread list with
    | True => Parse.readsFatal _ _
    | False => Parse.givesDone byComputing

theorem givesFacts ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (token: Tok) (kind: FactsKind)
    (nested: Nested self)
    (plain: token.wordWithin1 = False):
    Parse.Gives GoodItems (() => facts self modes token kind) Out :=
  Parse.givesThen givesBump (keyword _ =>
    givesAfter0
      [p := () => modes.at LBracket]
      [j := bracket => factsAfter self modes token kind keyword bracket]
      (reads0At modes LBracket)
      (bracket =>
        match bracket with
          | True => Parse.givesThen (givesListExprAny self modes nested) (list _ => givesFactsEnd kind keyword list)
          | False => Parse.givesDone plain))

theorem givesIncludeAtom ∀ (modes: Modes): Parse.Gives GoodItems (() => includeAtom modes) Out :=
  Parse.givesThen givesBump (keyword _ =>
    givesAfter0 [p := () => modes.at Str] [j := path => includeAfter modes keyword path] (reads0At modes Str) (path =>
      match path with
        | True => Parse.givesThen [p := () => bump()] [j := word => Include keyword word] givesBump (taken _ =>
          Parse.givesDone byComputing)
        | False => givesFail modes _))

theorem givesCasesAtom ∀ (modes: Modes): Parse.Gives GoodItems (() => casesAtom modes) Out :=
  givesAfter0 [p := () => bareCases modes] [j := bare => casesAfter modes bare] (reads0BareCases modes) (bare =>
    match bare with
      | True => Parse.givesThen givesBump (keyword _ => Parse.givesDone byComputing)
      | False => givesFail modes _)

theorem givesUniverseAtom ∀ (modes: Modes): Parse.Gives GoodItems (() => universeAtom modes) Out :=
  Parse.givesThen givesBump (keyword _ =>
    givesAfter0 [p := () => left()] [j := items => universeAfter modes keyword items] reads0Left (items =>
      match items with
        | [level, ..rest] =>
          match named: level.kind == Num && !modes.stops level with
            | True =>
              match big: (level.text.toNat |> .getOrElse 0) > 65535 with
                | True => Parse.readsFatal _ _
                | False =>
                  Parse.givesThen [p := () => bump()] [j := number => Universe keyword number] givesBump (digits _ =>
                    Parse.givesDone byComputing)
            | False => Parse.givesDone byComputing
        | [] => Parse.givesDone byComputing))

theorem givesSectionStart ∀ (modes: Modes): Parse.Gives GoodItems (() => sectionStart modes) Out :=
  Parse.givesThen givesBump (dot _ =>
    givesAfter0 [p := () => left()] [j := items => sectionAfter modes dot items] reads0Left (items =>
      match items with
        | [name, ..rest] =>
          match named: name.kind == Lower && name.glued && !isQualified name && !modes.stops name with
            | True =>
              Parse.givesThen [p := () => bump()] [j := field => FieldAccess None dot field] givesBump (field _ =>
                Parse.givesDone byComputing)
            | False => Parse.readsFatal _ _
        | [] => Parse.readsFatal _ _))

theorem givesInterpolationOpen ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self):
    Parse.Gives GoodItems (() => interpolationOpen self modes) (Parse.Perhaps (found => True)) :=
  Parse.givesThen (givesExpectAny modes InterpOpen "`\${`") (open _ =>
    Parse.givesThen (nested { modes, level = LevelFull }) (value _ =>
      Parse.givesThen (givesExpectAny modes InterpClose "`}`") (close _ => Parse.givesDone byComputing)))

theorem givesInterpolationOn ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self) (seen: Option Tok):
    Parse.Gives GoodItems (() => interpolationOn self modes seen) (Parse.Perhaps (found => True)) :=
  match isSome StrMid seen with
    | True => Parse.givesThen [p := () => bump()] [j := word => Some (TextPiece word)] givesBump (taken _ =>
      Parse.givesDone byComputing)
    | False =>
      match isSome InterpOpen seen with
        | True => givesInterpolationOpen self modes nested
        | False =>
          match isSome StrEnd seen with
            | True => Parse.givesDone byComputing
            | False => givesFail modes _

theorem givesInterpolationEnd ∀ (modes: Modes) (ended: Bool):
    Parse.Gives GoodItems (() => interpolationEnd modes ended) (word => True) :=
  match ended with
    | True => givesBump
    | False => givesFail modes _

theorem givesInterpolations ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self):
    Parse.Gives GoodItems (() => interpolations self modes) (pieces => True) :=
  Parse.givesThen
    [p := () => Parse.loop (() => interpolationStep self modes)]
    [j := pieces => interpolationLast modes pieces (modes.at StrEnd)]
    (Parse.givesWeaken
      [weaker := gathered => True]
      (Parse.givesLoop
        (givesAfter0 [p := () => modes.peek] [j := seen => interpolationOn self modes seen] (reads0Peek modes) (seen =>
          givesInterpolationOn self modes nested seen)))
      (found ok => byComputing))
    (gathered _ =>
      givesAfter0
        [p := () => modes.at StrEnd]
        [j := ended => interpolationLast modes gathered ended]
        (reads0At modes StrEnd)
        (ended => Parse.givesThen (givesInterpolationEnd modes ended) (last _ => Parse.givesDone byComputing)))

theorem givesInterpolated ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self):
    Parse.Gives GoodItems (() => interpolated self modes) Out :=
  Parse.givesThen givesBump (start _ =>
    Parse.givesThen (givesInterpolations self modes nested) (found _ => Parse.givesDone byComputing))

theorem givesAtomRest ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (kind: Tok)
    (nested: Nested self):
    Parse.Gives GoodItems (() => atomRest self modes kind) Out :=
  match kind == StrStart with
    | True => givesInterpolated self modes nested
    | False =>
      match kind == KwInclude with
        | True => givesIncludeAtom modes
        | False =>
          match kind == KwArithmetic with
            | True => givesFacts self modes KwArithmetic FactsOmega nested byComputing
            | False =>
              match kind == KwAlgebra with
                | True => givesFacts self modes KwAlgebra FactsRing nested byComputing
                | False =>
                  match kind == KwCases with
                    | True => givesCasesAtom modes
                    | False =>
                      match kind == TypeU with
                        | True => givesUniverseAtom modes
                        | False =>
                          match kind == LBrace with
                            | True => givesRecordExpr self modes nested
                            | False =>
                              match kind == Dot with
                                | True => givesSectionStart modes
                                | False => givesAtomMissing self modes

-- The pattern parser, read for nothing but that it is read: the parsers outside slice 1 that read patterns only need
-- the items they read to stay good, and that they return.

--| `pself` gives a pattern, at every goal.
def PatternNested (pself: PatternGoal → {Parse Item} Pattern): Prop :=
  ∀ (goal: PatternGoal) => Parse.Gives GoodItems (() => pself goal) (pat => True)

theorem reads0WordAhead ∀ (modes: Modes) (word: Text): Reads0 (() => wordAhead modes word) :=
  reads0Then [p := () => left()] reads0Left (items => reads0Done (wordOn modes word items))

theorem reads0CtorAhead ∀ (modes: Modes): Reads0 (() => ctorAhead modes) :=
  reads0Then
    [p := () => modes.at Upper]
    [j := upper => ctorAheadOf upper (wordAhead modes "Quot.mk")]
    (reads0At modes Upper)
    (upper =>
      reads0Then
        [p := () => wordAhead modes "Quot.mk"]
        [j := quot => ctorAheadOf upper quot]
        (reads0WordAhead modes "Quot.mk")
        (quot => reads0Done _))

theorem givesEat ∀ (modes: Modes) (wanted: Tok): Parse.Gives GoodItems (() => modes.eat wanted) (found => True) :=
  givesAfter0 [p := () => modes.at wanted] [j := at => if at then Some bump() else None] (reads0At modes wanted) (at =>
    match at with
      | True => Parse.givesThen [p := () => bump()] [j := taken => Some taken] givesBump (taken _ =>
        Parse.givesDone byComputing)
      | False => Parse.givesDone byComputing)

theorem givesNegativeDigits ∀ (modes: Modes) (minus: Word) (number: Bool):
    Parse.Gives GoodItems (() => negativeDigits modes minus number) (pat => True) :=
  match number with
    | True => Parse.givesThen [p := () => bump()] [j := digits => PatternNegative minus digits] givesBump (digits _ =>
      Parse.givesDone byComputing)
    | False => givesFail modes "a number"

theorem givesNegativePattern ∀ (modes: Modes): Parse.Gives GoodItems (() => negativePattern modes) (pat => True) :=
  Parse.givesThen givesBump (minus _ =>
    givesAfter0
      [p := () => modes.at Num]
      [j := number => negativeDigits modes minus number]
      (reads0At modes Num)
      (number => givesNegativeDigits modes minus number))

theorem givesPatternAppendOf ∀ (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes)
    (start: Pattern) (next: PatternLevel)
    (nested: PatternNested pself) (plus: Bool):
    Parse.Gives GoodItems (() => patternAppendOf pself modes start next plus) (pat => True) :=
  match plus with
    | False => Parse.givesDone byComputing
    | True =>
      match isTextPattern start with
        | True =>
          Parse.givesThen
            [p := () => bump()]
            [j := operator => PatternAppend start operator (pself { modes, level = next })]
            givesBump
            (operator _ =>
              Parse.givesThen
                [p := () => pself { modes, level = next }]
                [j := tail => PatternAppend start operator tail]
                (nested { modes, level = next })
                (tail _ => Parse.givesDone byComputing))
        | False => Parse.readsFatal _ _

theorem givesPatternAppend ∀ (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes)
    (start: Pattern) (next: PatternLevel)
    (nested: PatternNested pself):
    Parse.Gives GoodItems (() => patternAppend pself modes start next) (pat => True) :=
  givesAfter0
    [p := () => modes.at PlusPlus]
    [j := plus => patternAppendOf pself modes start next plus]
    (reads0At modes PlusPlus)
    (plus => givesPatternAppendOf pself modes start next nested plus)

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
  givesAfter0
    [p := () => left()]
    [j := items => alternativeLinksOn fuel pself modes next found items]
    reads0Left
    (items => givesAlternativeLinksOn fuel pself modes next found nested items)

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
      Parse.givesThen
        [p := () => pself { modes, level = PatternFieldValue }]
        [j := value => Some (word, value)]
        (nested { modes, level = PatternFieldValue })
        (value _ => Parse.givesDone byComputing)
    | None => Parse.givesDone byComputing

theorem givesFieldPatterns ∀ (fuel: Nat) (pself: PatternGoal → {Parse Item} Pattern)
    (modes: Modes) (found: List FieldPattern)
    (nested: PatternNested pself):
    Parse.Gives GoodItems (() => fieldPatterns fuel pself modes found) (read => True) :=
  match fuel with
    | Zero => Parse.givesDone byComputing
    | Succ more =>
      givesAfter0
        [p := () => modes.at DotDot]
        [j := dots => fieldPatternStep more pself modes found dots]
        (reads0At modes DotDot)
        (dots => givesFieldPatternStep more pself modes found nested dots)

theorem givesFieldPatternStep ∀ (more: Nat) (pself: PatternGoal → {Parse Item} Pattern)
    (modes: Modes) (found: List FieldPattern)
    (nested: PatternNested pself) (dots: Bool):
    Parse.Gives GoodItems (() => fieldPatternStep more pself modes found dots) (read => True) :=
  match dots with
    | True => Parse.givesThen givesBump (rest _ => Parse.givesDone byComputing)
    | False =>
      givesAfter0
        [p := () => modes.at RBrace]
        [j := closed => fieldPatternClose more pself modes found closed]
        (reads0At modes RBrace)
        (closed => givesFieldPatternClose more pself modes found nested closed)

theorem givesFieldPatternClose ∀ (more: Nat) (pself: PatternGoal → {Parse Item} Pattern)
    (modes: Modes) (found: List FieldPattern)
    (nested: PatternNested pself) (closed: Bool):
    Parse.Gives GoodItems (() => fieldPatternClose more pself modes found closed) (read => True) :=
  match closed with
    | True => Parse.givesDone byComputing
    | False => Parse.givesThen (givesLower modes "a field name, or `..`") (name _ =>
      Parse.givesThen
        [p := () => fieldPatternValue pself modes (modes.eat Equals)]
        (Parse.givesThen
          [p := () => modes.eat Equals]
          [j := equals => fieldPatternValue pself modes equals]
          (givesEat modes Equals)
          (equals _ => givesFieldPatternValue pself modes nested equals))
        (value _ =>
          Parse.givesThen
            [p := () => modes.eat Comma]
            [j := comma => fieldPatternNext more pself modes found { name, value } comma]
            (givesEat modes Comma)
            (comma _ => givesFieldPatternNext more pself modes found nested { name, value } comma)))

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
    | True => Parse.readsFatal _ _
    | False =>
      Parse.givesThen
        [p := () => fieldsPattern pself modes]
        [j := fields => PatternRecord fields]
        (givesFieldsPattern pself modes nested)
        (fields _ => Parse.givesDone byComputing)

theorem givesCtorArgList ∀ (fuel: Nat) (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes) (name: Word)
    (stops: Tok → Bool) (found: List Pattern)
    (nested: PatternNested pself):
    Parse.Gives GoodItems (() => ctorArgList fuel pself modes name stops found) (list => True) :=
  givesAfter0
    [p := () => modes.peek]
    [j := seen => ctorArgListOn fuel pself modes name stops found seen]
    (reads0Peek modes)
    (seen => givesCtorArgListOn fuel pself modes name stops found nested seen)

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
    | False =>
      givesAfter0
        [p := () => left()]
        [j := items => ctorArgMinus more pself modes name stops found (argumentMinus items)]
        reads0Left
        (items => givesCtorArgMinus more pself modes name stops found nested (argumentMinus items))

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
        | False => Parse.readsFatal _ _
    | None => Parse.givesDone byComputing

theorem givesCtorListEnd ∀ (name: Word) (arguments: List Pattern):
    Parse.Gives GoodItems (() => ctorListEnd name arguments) (pat => True) :=
  match arguments with
    | [] => Parse.givesDone byComputing
    | [first, ..rest] => Parse.givesDone byComputing

theorem givesCtorArgsOf ∀ (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes) (name: Word) (stops: Tok → Bool)
    (nested: PatternNested pself) (braced: Bool):
    Parse.Gives GoodItems (() => ctorArgsOf pself modes name stops braced) (pat => True) :=
  match braced with
    | True => Parse.givesThen (givesFieldsPattern pself modes nested) (fields _ =>
      givesAfter0
        [p := () => modes.peek]
        [j := seen => ctorFieldsEnd name fields stops seen]
        (reads0Peek modes)
        (seen => givesCtorFieldsEnd name fields stops seen))
    | False => Parse.givesThen Parse.givesMark (here _ =>
      Parse.givesThen (givesCtorArgList (here.left + 1) pself modes name stops [] nested) (list _ =>
        givesCtorListEnd name list))

theorem givesCtorArgs ∀ (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes) (name: Word) (stops: Tok → Bool)
    (nested: PatternNested pself):
    Parse.Gives GoodItems (() => ctorArgs pself modes name stops) (pat => True) :=
  givesAfter0
    [p := () => modes.at LBrace]
    [j := braced => ctorArgsOf pself modes name stops braced]
    (reads0At modes LBrace)
    (braced => givesCtorArgsOf pself modes name stops nested braced)

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
    | False =>
      givesAfter0
        [p := () => modes.at Minus]
        [j := minus => tupleSigned pself modes minus]
        (reads0At modes Minus)
        (minus => givesTupleSigned pself modes nested minus)

theorem givesTupleComponent ∀ (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes)
    (nested: PatternNested pself):
    Parse.Gives GoodItems (() => tupleComponent pself modes) (pat => True) :=
  givesAfter0
    [p := () => ctorAhead modes]
    [j := isCtor => tupleComponentOf pself modes isCtor]
    (reads0CtorAhead modes)
    (isCtor => givesTupleComponentOf pself modes nested isCtor)

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
  givesAfter0
    [p := () => ctorAhead modes]
    [j := isCtor => listComponentOf pself modes isCtor]
    (reads0CtorAhead modes)
    (isCtor => givesListComponentOf pself modes nested isCtor)

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
  givesAfter0
    [p := () => ctorAhead modes]
    [j := isCtor => altPatternOneOf pself modes isCtor]
    (reads0CtorAhead modes)
    (isCtor => givesAltPatternOneOf pself modes nested isCtor)

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
      Parse.givesThen
        [p := () => modes.eat Comma]
        [j := comma => listPatternNext more pself modes found entry comma]
        (givesEat modes Comma)
        (comma _ => givesListPatternNext more pself modes found entry nested comma))

theorem givesListPatternStep ∀ (more: Nat) (pself: PatternGoal → {Parse Item} Pattern)
    (modes: Modes) (found: List Pattern)
    (nested: PatternNested pself) (closed: Bool):
    Parse.Gives GoodItems (() => listPatternStep more pself modes found closed) (read => True) :=
  match closed with
    | True => Parse.givesDone byComputing
    | False =>
      givesAfter0
        [p := () => modes.at DotDot]
        [j := dots => listPatternDots more pself modes found dots]
        (reads0At modes DotDot)
        (dots => givesListPatternDots more pself modes found nested dots)

theorem givesListPatternItems ∀ (fuel: Nat) (pself: PatternGoal → {Parse Item} Pattern)
    (modes: Modes) (found: List Pattern)
    (nested: PatternNested pself):
    Parse.Gives GoodItems (() => listPatternItems fuel pself modes found) (read => True) :=
  match fuel with
    | Zero => Parse.givesDone byComputing
    | Succ more =>
      givesAfter0
        [p := () => modes.at RBracket]
        [j := closed => listPatternStep more pself modes found closed]
        (reads0At modes RBracket)
        (closed => givesListPatternStep more pself modes found nested closed)

theorem givesListPatternClose ∀ (inner: Modes) (open: Word) (items: List Pattern) (trailingComma: Bool)
    (tail: Option (Word, Pattern)) (comma: Bool):
    Parse.Gives GoodItems (() => listPatternClose inner open items trailingComma tail comma) (pat => True) :=
  match tail, comma with
    | Some pair, True => Parse.readsFatal _ _
    | Some pair, False =>
      Parse.givesThen
        [p := () => inner.expect RBracket "`]`: a `..` tail must be the last item"]
        [j := close => PatternList open items trailingComma tail close]
        (givesExpectAny inner RBracket "`]`: a `..` tail must be the last item")
        (close _ => Parse.givesDone byComputing)
    | None, comma =>
      Parse.givesThen
        [p := () => inner.expect RBracket "`,` or `]`"]
        [j := close => PatternList open items trailingComma tail close]
        (givesExpectAny inner RBracket "`,` or `]`")
        (close _ => Parse.givesDone byComputing)

theorem givesListPatternEnd ∀ (inner: Modes) (open: Word) (read: (List Pattern, Bool, Option (Word, Pattern))):
    Parse.Gives GoodItems (() => listPatternEnd inner open read) (pat => True) :=
  match read with
    | (items, trailingComma, tail) =>
      givesAfter0
        [p := () => inner.at Comma]
        [j := comma => listPatternClose inner open items trailingComma tail comma]
        (reads0At inner Comma)
        (comma => givesListPatternClose inner open items trailingComma tail comma)

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
      Parse.givesThen
        [p := () => modes.expect RParen "`)`"]
        [j := close => PatternTuple open items trailingComma close]
        (givesExpectAny modes RParen "`)`")
        (close _ => Parse.givesDone byComputing)

theorem givesParenPatternOf ∀ (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes) (open: Word) (first: Pattern)
    (nested: PatternNested pself) (comma: Bool):
    Parse.Gives GoodItems (() => parenPatternOf pself modes open first comma) (pat => True) :=
  match comma with
    | True => Parse.givesThen Parse.givesMark (here _ =>
      Parse.givesThen
        [p := () =>
          commaList
            (here.left + 1)
            modes
            (count => modes.at RParen && count >= 2)
            (() => tupleItem pself modes)
            first
            []]
        [j := pair => tuplePatternEnd modes open pair]
        (givesCommaListFrom modes
          (count => modes.at RParen && count >= 2)
          (() => tupleItem pself modes)
          (found => True)
          (count =>
            Parse.givesThen
              [p := () => modes.at RParen]
              [j := stop => stop && count >= 2]
              (givesAt modes RParen)
              (stop _ => Parse.givesDone byComputing))
          (givesTupleItem pself modes nested)
          (here.left + 1)
          1
          first
          []
          byComputing
          ())
        (pair _ => givesTuplePatternEnd modes open pair))
    | False =>
      Parse.givesThen
        [p := () => modes.expect RParen "`)`"]
        [j := close => PatternParen open first close]
        (givesExpectAny modes RParen "`)`")
        (close _ => Parse.givesDone byComputing)

theorem givesParenPatternEnd ∀ (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes) (open: Word) (first: Pattern)
    (nested: PatternNested pself):
    Parse.Gives GoodItems (() => parenPatternEnd pself modes open first) (pat => True) :=
  givesAfter0
    [p := () => modes.at Comma]
    [j := comma => parenPatternOf pself modes open first comma]
    (reads0At modes Comma)
    (comma => givesParenPatternOf pself modes open first nested comma)

-- Brackets, parentheses and the plain pattern.

theorem givesNamedPattern ∀ (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes)
    (nested: PatternNested pself):
    Parse.Gives GoodItems (() => namedPattern pself modes) (pat => True) :=
  Parse.givesThen givesBump (open _ =>
    Parse.givesThen (givesLower modes.inBrackets "a field name") (name _ =>
      Parse.givesThen givesBump (colonEq _ =>
        Parse.givesThen (nested { modes = modes.inBrackets, level = PatternPlain }) (value _ =>
          Parse.givesThen
            [p := () => modes.inBrackets.expect RBracket "`]`"]
            [j := close => PatternNamed open name colonEq value close]
            (givesExpectAny modes.inBrackets RBracket "`]`")
            (close _ => Parse.givesDone byComputing)))))

theorem givesBracketPatternOn ∀ (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes)
    (nested: PatternNested pself) (second third: Option Tok):
    Parse.Gives GoodItems (() => bracketPatternOn pself modes second third) (pat => True) :=
  match second, third with
    | Some Lower, Some ColonEq => givesNamedPattern pself modes nested
    | other, others => givesListPattern pself modes nested

theorem givesBracketPattern ∀ (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes)
    (nested: PatternNested pself) (second: Option Tok):
    Parse.Gives GoodItems (() => bracketPattern pself modes second) (pat => True) :=
  givesAfter0
    [p := () => modes.peekAt 2]
    [j := third => bracketPatternOn pself modes second third]
    (reads0PeekAt modes 2)
    (third => givesBracketPatternOn pself modes nested second third)

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
      [p := () => parenComponent pself modes.inBrackets (ctorAhead modes.inBrackets)]
      (givesAfter0
        [p := () => ctorAhead modes.inBrackets]
        [j := isCtor => parenComponent pself modes.inBrackets isCtor]
        (reads0CtorAhead modes.inBrackets)
        (isCtor => givesParenComponent pself modes.inBrackets nested isCtor))
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
    | Some RParen => Parse.givesThen givesBump (open _ =>
      Parse.givesThen [p := () => bump()] [j := close => PatternAbsurd open close] givesBump (close _ =>
        Parse.givesDone byComputing))
    | Some Minus => givesParenMinusPattern pself modes nested
    | other => givesParenOpenPattern pself modes nested

theorem givesQuotOrLower ∀ (modes: Modes) (quot: Bool):
    Parse.Gives GoodItems (() => quotOrLower modes quot) (word => True) :=
  match quot with
    | True => givesBump
    | False => givesLower modes "a pattern"

theorem givesBumpedWord ∀ (kind: Tok): Parse.Gives GoodItems (() => PatternWord kind bump()) (pat => True) :=
  Parse.givesThen [p := () => bump()] [j := bumped => PatternWord kind bumped] givesBump (bumped _ =>
    Parse.givesDone byComputing)

theorem givesPlainPatternOn ∀ (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes)
    (nested: PatternNested pself) (seen: Option Tok):
    Parse.Gives GoodItems (() => plainPatternOn pself modes seen) (pat => True) :=
  match seen with
    | Some Upper => givesBumpedWord Upper
    | Some Lower =>
      Parse.givesThen
        [p := () => quotOrLower modes (wordAhead modes "Quot.mk")]
        [j := word => PatternWord Lower word]
        (givesAfter0
          [p := () => wordAhead modes "Quot.mk"]
          [j := quot => quotOrLower modes quot]
          (reads0WordAhead modes "Quot.mk")
          (quot => givesQuotOrLower modes quot))
        (bumped _ => Parse.givesDone byComputing)
    | Some Underscore => givesBumpedWord Underscore
    | Some Num => givesBumpedWord Num
    | Some CharLit => givesBumpedWord CharLit
    | Some Str => givesBumpedWord Str
    | Some StrStart => Parse.readsFatal _ _
    | Some LBrace =>
      Parse.givesThen
        [p := () => fieldsPattern pself modes]
        [j := fields => PatternRecord fields]
        (givesFieldsPattern pself modes nested)
        (fields _ => Parse.givesDone byComputing)
    | Some LBracket =>
      givesAfter0
        [p := () => modes.peekAt 1]
        [j := second => bracketPattern pself modes second]
        (reads0PeekAt modes 1)
        (second => givesBracketPattern pself modes nested second)
    | Some LParen =>
      givesAfter0
        [p := () => modes.peekAt 1]
        [j := second => parenPattern pself modes second]
        (reads0PeekAt modes 1)
        (second => givesParenPattern pself modes nested second)
    | other => givesFailName modes "a pattern or `=`"

theorem givesPlainPattern ∀ (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes)
    (nested: PatternNested pself):
    Parse.Gives GoodItems (() => Syntax.plainPattern pself modes) (pat => True) :=
  givesAfter0 [p := () => modes.peek] [j := seen => plainPatternOn pself modes seen] (reads0Peek modes) (seen =>
    givesPlainPatternOn pself modes nested seen)

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
          givesAfter0
            [p := () => ctorAhead modes]
            [j := isCtor => fieldValuePattern pself modes isCtor]
            (reads0CtorAhead modes)
            (isCtor => givesFieldValuePattern pself modes nested isCtor)

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

-- The binder parsers, read for nothing but that they are read.

theorem givesFullAny ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self):
    Parse.Gives GoodItems (() => full self modes) (expr => True) :=
  givesSelfAny self nested { modes, level = LevelFull }

theorem givesRefuseAttributes ∀ (attributes: List Attributes) (what: Text):
    Parse.Gives GoodItems (() => refuseAttributes attributes what) (unit => True) :=
  match attributes with
    | [] => Parse.givesDone byComputing
    | [first, ..rest] => Parse.readsFatal _ _

theorem givesParamNameOn ∀ (modes: Modes) (seen: Option Tok):
    Parse.Gives GoodItems (() => paramNameOn modes seen) (word => True) :=
  match seen with
    | Some Upper => givesFail modes _
    | Some LParen => givesFail modes _
    | Some LBrace => givesFail modes _
    | other => givesLower modes "a parameter's name"

theorem givesParamName ∀ (modes: Modes): Parse.Gives GoodItems (() => paramName modes) (word => True) :=
  givesAfter0 [p := () => modes.peek] [j := seen => paramNameOn modes seen] (reads0Peek modes) (seen =>
    givesParamNameOn modes seen)

theorem givesParamNames ∀ (modes: Modes): Parse.Gives GoodItems (() => paramNames modes) (found => True) :=
  Parse.givesWeaken
    [weaker := found => True]
    (Parse.givesLoop
      [holds := word => True]
      (givesAfter0
        [p := () => modes.at Lower]
        [j := atLower => paramNameStep modes atLower]
        (reads0At modes Lower)
        (atLower =>
          match atLower with
            | True =>
              Parse.givesThen [p := () => paramName modes] [j := word => Some word] (givesParamName modes) (found _ =>
                Parse.givesDone byComputing)
            | False => Parse.givesDone byComputing)))
    (found ok => byComputing)

theorem givesLowerNames ∀ (modes: Modes): Parse.Gives GoodItems (() => lowerNames modes) (found => True) :=
  Parse.givesWeaken
    [weaker := found => True]
    (Parse.givesLoop
      [holds := word => True]
      (givesAfter0
        [p := () => modes.at Lower]
        [j := atLower => lowerNameStep modes atLower]
        (reads0At modes Lower)
        (atLower =>
          match atLower with
            | True =>
              Parse.givesThen
                [p := () => modes.lower "a name"]
                [j := word => Some word]
                (givesLower modes "a name")
                (found _ => Parse.givesDone byComputing)
            | False => Parse.givesDone byComputing)))
    (found ok => byComputing)

theorem givesConsumedBare ∀ (started: Parse.Mark Item):
    Parse.Gives GoodItems (() => consumedBare started) (found => True) :=
  Parse.givesThen Parse.givesMark (here _ => Parse.givesDone byComputing)

theorem givesAllowBrace ∀ (modes: Modes): Parse.Gives GoodItems (() => allowBrace modes) (found => True) :=
  givesAfter0 [p := () => left()] [j := items => allowBraceOn modes items] reads0Left (items =>
    Parse.givesDone byComputing)

theorem givesBinderTypeOn ∀ (self: Goal → {Parse Item} Expr) (allowed: Modes)
    (nested: Nested self)
    (seen: Option Tok) (items: List Item):
    Parse.Gives GoodItems (() => binderTypeOn self allowed seen items) (expr => True) :=
  match seen, items with
    | Some LBrace, [open, ..rest] =>
      match skipGroup [] [open, ..rest] with
        | Some [next, ..more] =>
          match typeStarts next.kind with
            | True => Parse.readsFatal _ _
            | False => givesFullAny self allowed nested
        | other => givesFullAny self allowed nested
    | other, others => givesFullAny self allowed nested

theorem givesBinderTypeSeen ∀ (self: Goal → {Parse Item} Expr) (allowed: Modes)
    (nested: Nested self) (seen: Option Tok):
    Parse.Gives GoodItems (() => binderTypeSeen self allowed seen) (expr => True) :=
  givesAfter0 [p := () => left()] [j := items => binderTypeOn self allowed seen items] reads0Left (items =>
    givesBinderTypeOn self allowed nested seen items)

theorem givesBinderType ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self):
    Parse.Gives GoodItems (() => binderType self modes) (expr => True) :=
  Parse.givesThen (givesAllowBrace modes) (allowed _ =>
    givesAfter0 [p := () => allowed.peek] [j := seen => binderTypeSeen self allowed seen] (reads0Peek allowed) (seen =>
      givesBinderTypeSeen self allowed nested seen))

theorem givesHeaderDefault ∀ (self: Goal → {Parse Item} Expr) (inner: Modes)
    (nested: Nested self) (implicit atColonEq: Bool):
    Parse.Gives GoodItems (() => headerDefault self inner implicit atColonEq) (found => True) :=
  match atColonEq with
    | True =>
      match implicit with
        | True => Parse.readsFatal _ _
        | False => Parse.givesThen givesFixedFrom (colonEq _ =>
          Parse.givesThen (givesFullAny self inner nested) (value _ => Parse.givesDone byComputing))
    | False => Parse.givesDone byComputing

theorem givesHeaderGroupEnd ∀ (kind: GroupKind) (implicit: Bool) (open: Comments) (auto: Option Comments)
    (named: List Word) (colon: Comments) (annotation: Expr) (default: Option (Comments, Expr)) (close: Comments)
    (refused: Option Text) (consumed: Bool):
    Parse.Gives GoodItems
      (() => headerGroupEnd kind implicit open auto named colon annotation default close refused consumed)
      (found => True) :=
  match refused, default with
    | Some message, Some value => Parse.readsFatal _ _
    | Some message, None => Parse.givesDone byComputing
    | None, other => Parse.givesDone byComputing

theorem givesHeaderGroupColon ∀ (self: Goal → {Parse Item} Expr) (inner: Modes)
    (nested: Nested self)
    (kind: GroupKind) (refused: Option Text) (implicit: Bool) (started: Parse.Mark Item) (open: Comments)
    (auto: Option Comments) (named: List Word) (atColon: Bool):
    Parse.Gives GoodItems
      (() => headerGroupColon self inner kind refused implicit started open auto named atColon)
      (found => True) :=
  match atColon with
    | False => Parse.readsFatal _ _
    | True => Parse.givesThen givesFixedFrom (colon _ =>
      Parse.givesThen (givesBinderType self inner nested) (annotation _ =>
        Parse.givesThen
          [p := () => headerDefault self inner implicit (inner.at ColonEq)]
          (givesAfter0
            [p := () => inner.at ColonEq]
            [j := atColonEq => headerDefault self inner implicit atColonEq]
            (reads0At inner ColonEq)
            (atColonEq => givesHeaderDefault self inner nested implicit atColonEq))
          (default _ =>
            Parse.givesThen (givesExpectFixed inner (closerOf implicit) (closeMessage implicit auto named)) (close _ =>
              Parse.givesThen (givesConsumedBare started) (consumed _ =>
                givesHeaderGroupEnd kind implicit open auto named colon annotation default close refused consumed)))))

theorem givesHeaderGroupNamed ∀ (self: Goal → {Parse Item} Expr) (inner: Modes)
    (nested: Nested self)
    (kind: GroupKind) (refused: Option Text) (implicit: Bool) (started: Parse.Mark Item)
    (open: Comments) (split: (Option Comments, List Word)):
    Parse.Gives GoodItems (() => headerGroupNamed self inner kind refused implicit started open split) (found =>
      True) :=
  match split with
    | (auto, named) =>
      givesAfter0
        [p := () => inner.at Colon]
        [j := atColon => headerGroupColon self inner kind refused implicit started open auto named atColon]
        (reads0At inner Colon)
        (atColon => givesHeaderGroupColon self inner nested kind refused implicit started open auto named atColon)

theorem givesHeaderGroupTyped ∀ (self: Goal → {Parse Item} Expr) (inner: Modes)
    (nested: Nested self)
    (kind: GroupKind) (refused: Option Text) (implicit: Bool) (started: Parse.Mark Item)
    (open: Comments) (names: List Word):
    Parse.Gives GoodItems (() => headerGroupTyped self inner kind refused implicit started open names) (found =>
      True) :=
  givesHeaderGroupNamed self inner nested kind refused implicit started open (autoSplit implicit names)

theorem givesHeaderGroupAuto ∀ (self: Goal → {Parse Item} Expr) (inner: Modes)
    (nested: Nested self)
    (kind: GroupKind) (open: Comments) (auto: Word):
    Parse.Gives GoodItems (() => headerGroupAuto self inner kind open auto) (found => True) :=
  Parse.givesThen (givesFullAny self inner nested) (annotation _ =>
    Parse.givesThen (givesExpectFixed inner RBracket "`]` to close the parameter `[auto …]`") (close _ =>
      Parse.givesDone byComputing))

theorem givesHeaderGroupNames ∀ (self: Goal → {Parse Item} Expr) (inner: Modes)
    (nested: Nested self)
    (kind: GroupKind) (refused: Option Text) (implicit: Bool) (started: Parse.Mark Item) (open: Comments)
    (names: List Word) (typeFollows: Bool):
    Parse.Gives GoodItems
      (() => headerGroupNames self inner kind refused implicit started open names typeFollows)
      (found => True) :=
  match names with
    | [auto] =>
      match implicit && auto.text == "auto" && typeFollows with
        | True => givesHeaderGroupAuto self inner nested kind open auto
        | False => givesHeaderGroupTyped self inner nested kind refused implicit started open names
    | other => givesHeaderGroupTyped self inner nested kind refused implicit started open names

theorem givesHeaderGroupParts ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (kind: GroupKind) (refused: Option Text) (implicit: Bool):
    Parse.Gives GoodItems (() => headerGroupParts self modes kind refused implicit) (found => True) :=
  Parse.givesThen Parse.givesMark (started _ =>
    Parse.givesThen givesFixedFrom (open _ =>
      Parse.givesThen (givesAttributesOf modes.inBrackets) (attributes _ =>
        Parse.givesThen (givesRefuseAttributes attributes "a definition's parameter") (refusal _ =>
          Parse.givesThen (givesParamName modes.inBrackets) (first _ =>
            Parse.givesThen (givesParamNames modes.inBrackets) (more _ =>
              Parse.givesThen (givesAt modes.inBrackets Colon) (atColon _ =>
                Parse.givesThen (givesAt modes.inBrackets RBracket) (atBracket _ =>
                  Parse.givesThen (givesOfReads0 (reads0Peek modes.inBrackets)) (peeked _ =>
                    givesHeaderGroupNames self modes.inBrackets nested kind refused implicit started open
                      [first, ..more]
                      (typeFollowsOf atColon atBracket peeked))))))))))

theorem givesHeaderGroupOn ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (kind: GroupKind) (refused: Option Text) (first second: Option Tok):
    Parse.Gives GoodItems (() => headerGroupOn self modes kind refused first second) (found => True) :=
  match first, second with
    | Some LParen, Some RParen =>
      Parse.givesThen givesFixedFrom (open _ => Parse.givesThen givesFixedFrom (close _ => Parse.givesDone byComputing))
    | Some LParen, other => givesHeaderGroupParts self modes nested kind refused False
    | Some LBracket, other => givesHeaderGroupParts self modes nested kind refused True
    | other, others => givesFail modes _

theorem givesHeaderGroup ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (kind: GroupKind) (refused: Option Text):
    Parse.Gives GoodItems (() => headerGroup self modes kind refused) (found => True) :=
  givesAfter0
    [p := () => modes.peek]
    [j := first => headerGroupSeen self modes kind refused first]
    (reads0Peek modes)
    (first =>
      givesAfter0
        [p := () => modes.peekAt 1]
        [j := second => headerGroupOn self modes kind refused first second]
        (reads0PeekAt modes 1)
        (second => givesHeaderGroupOn self modes nested kind refused first second))

theorem givesHeaderParams ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self):
    Parse.Gives GoodItems (() => headerParams self modes) (found => True) :=
  Parse.givesWeaken
    [weaker := found => True]
    (Parse.givesLoop
      [holds := group => True]
      (givesAfter0
        [p := () => modes.at Colon]
        [j := atColon => headerParamStep self modes atColon]
        (reads0At modes Colon)
        (atColon =>
          match atColon with
            | True => Parse.givesDone byComputing
            | False =>
              Parse.givesThen
                [p := () => headerGroup self modes GroupParam None]
                [j := group => Some group]
                (givesHeaderGroup self modes nested GroupParam None)
                (group _ => Parse.givesDone byComputing))))
    (found ok => byComputing)

theorem givesBinderDefault ∀ (self: Goal → {Parse Item} Expr) (inner: Modes)
    (nested: Nested self) (atColonEq: Bool):
    Parse.Gives GoodItems (() => binderDefault self inner atColonEq) (found => True) :=
  match atColonEq with
    | True => Parse.givesThen givesFixedFrom (colonEq _ =>
      Parse.givesThen (givesFullAny self inner nested) (value _ => Parse.givesDone byComputing))
    | False => Parse.givesDone byComputing

theorem givesBinderGroup ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self) (defaults: Bool):
    Parse.Gives GoodItems (() => binderGroup self modes defaults) (found => True) :=
  Parse.givesThen (givesExpectFixed modes LParen "`(`") (open _ =>
    Parse.givesThen (givesAttributesOf modes.inBrackets) (attributes _ =>
      Parse.givesThen (givesLower modes.inBrackets "a name") (first _ =>
        Parse.givesThen (givesLowerNames modes.inBrackets) (more _ =>
          Parse.givesThen (givesExpectFixed modes.inBrackets Colon "`:`") (colon _ =>
            Parse.givesThen (givesBinderType self modes.inBrackets nested) (annotation _ =>
              Parse.givesThen
                [p := () => binderDefault self modes.inBrackets (modes.inBrackets.at ColonEq)]
                (givesAfter0
                  [p := () => modes.inBrackets.at ColonEq]
                  [j := atColonEq => binderDefault self modes.inBrackets atColonEq]
                  (reads0At modes.inBrackets ColonEq)
                  (atColonEq => givesBinderDefault self modes.inBrackets nested atColonEq))
                (default _ =>
                  Parse.givesThen (givesExpectFixed modes.inBrackets RParen "`)`") (close _ =>
                    match !defaults && default.isSome with
                      | True => Parse.readsFatal _ _
                      | False => Parse.givesDone byComputing))))))))

theorem givesImplicitNamed ∀ (self: Goal → {Parse Item} Expr) (inner: Modes)
    (nested: Nested self)
    (open: Comments) (attributes: List Attributes) (split: (Option Comments, List Word)):
    Parse.Gives GoodItems (() => implicitNamed self inner open attributes split) (found => True) :=
  match split with
    | (auto, names) => Parse.givesThen (givesExpectFixed inner Colon "`:`") (colon _ =>
      Parse.givesThen (givesBinderType self inner nested) (annotation _ =>
        Parse.givesThen (givesExpectFixed inner RBracket "`]`") (close _ => Parse.givesDone byComputing)))

theorem givesImplicitBinderOf ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self) (nameless: Bool):
    Parse.Gives GoodItems (() => implicitBinderOf self modes nameless) (found => True) :=
  match nameless with
    | True => Parse.givesThen givesFixedFrom (open _ =>
      Parse.givesThen givesFixedFrom (auto _ =>
        Parse.givesThen (givesFullAny self modes.inBrackets nested) (annotation _ =>
          Parse.givesThen (givesExpectFixed modes.inBrackets RBracket "`]`") (close _ => Parse.givesDone byComputing))))
    | False => Parse.givesThen (givesExpectFixed modes LBracket "`[`") (open _ =>
      Parse.givesThen (givesAttributesOf modes.inBrackets) (attributes _ =>
        Parse.givesThen (givesLower modes.inBrackets "a name") (first _ =>
          Parse.givesThen (givesLowerNames modes.inBrackets) (rest _ =>
            givesImplicitNamed self modes.inBrackets nested open attributes (implicitAuto first rest)))))

theorem givesImplicitBinder ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self):
    Parse.Gives GoodItems (() => implicitBinder self modes) (found => True) :=
  givesAfter0
    [p := () => left()]
    [j := items => implicitBinderOf self modes (namelessAutoAt items)]
    reads0Left
    (items => givesImplicitBinderOf self modes nested (namelessAutoAt items))

-- Lambdas, quantifiers and function types.

theorem givesPatternOf ∀ (modes: Modes): Parse.Gives GoodItems (() => patternOf modes) (pat => True) :=
  givesPattern { modes, level = PatternPlain }

theorem givesLambdaPattern ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self) (typed: Bool):
    Parse.Gives GoodItems (() => lambdaPattern self modes typed) (found => True) :=
  match typed with
    | True => Parse.givesThen givesBump (open _ =>
      Parse.givesThen (givesPatternOf modes.inBrackets) (pat _ =>
        Parse.givesThen (givesExpectAny modes.inBrackets Colon "`:`") (colon _ =>
          Parse.givesThen (givesBinderType self modes.inBrackets nested) (annotation _ =>
            Parse.givesThen
              [p := () => modes.inBrackets.expect RParen "`)`"]
              [j := close => Some (TypedPattern open pat colon annotation close)]
              (givesExpectAny modes.inBrackets RParen "`)`")
              (close _ => Parse.givesDone byComputing)))))
    | False => Parse.givesThen (givesPatternOf modes) (pat _ => Parse.givesDone byComputing)

theorem givesLambdaGroup ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self):
    Parse.Gives GoodItems (() => lambdaGroup self modes) (found => True) :=
  Parse.givesThen (givesHeaderGroup self modes nested GroupLambda (Some defaultPlaces)) (group _ =>
    Parse.givesDone byComputing)

theorem givesLambdaParen ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self) (items: List Item):
    Parse.Gives GoodItems (() => lambdaParen self modes items) (found => True) :=
  match annotatedParamAhead items with
    | True => givesLambdaGroup self modes nested
    | False =>
      Parse.givesThen
        [p := () => Parse.mark()]
        [j := here => lambdaPattern self modes (annotatedPatternAhead (here.left + 1) items)]
        Parse.givesMark
        (here _ => givesLambdaPattern self modes nested (annotatedPatternAhead (here.left + 1) items))

theorem givesLambdaParam ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (items: List Item) (kind: Tok):
    Parse.Gives GoodItems (() => lambdaParam self modes items kind) (found => True) :=
  match kind with
    | Lower => Parse.givesThen (givesLower modes "a name") (name _ => Parse.givesDone byComputing)
    | Underscore => Parse.givesThen givesBump (name _ => Parse.givesDone byComputing)
    | LParen => givesLambdaParen self modes nested items
    | LBracket =>
      match implicitGroupAt items || namelessAutoAt items with
        | True => givesLambdaGroup self modes nested
        | False => Parse.givesDone byComputing
    | LBrace => Parse.givesThen (givesPatternOf modes) (found _ => Parse.givesDone byComputing)
    | other => Parse.givesDone byComputing

theorem givesLambdaStep ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self) (items: List Item):
    Parse.Gives GoodItems (() => lambdaStep self modes items) (found => True) :=
  match items with
    | [item, ..rest] =>
      match modes.stops item with
        | True => Parse.givesDone byComputing
        | False => givesLambdaParam self modes nested items item.kind
    | [] => Parse.givesDone byComputing

theorem givesLambdaParams ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self):
    Parse.Gives GoodItems (() => lambdaParams self modes) (found => True) :=
  Parse.givesWeaken
    [weaker := found => True]
    (Parse.givesLoop
      [holds := param => True]
      (givesAfter0 [p := () => left()] [j := items => lambdaStep self modes items] reads0Left (items =>
        Parse.givesWeaken (givesLambdaStep self modes nested items) (found ok =>
          match found with
            | Some param => byComputing
            | None => byComputing))))
    (found ok => byComputing)

theorem givesLambda ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (keyword: Option Word)
    (nested: Nested self):
    Parse.Gives GoodItems (() => lambda self modes keyword) Out :=
  Parse.givesThen (givesLambdaParams self modes nested) (params _ =>
    match params.isEmpty with
      | True => givesFail modes _
      | False => Parse.givesThen (givesExpectAny modes FatArrow "`=>`") (arrow _ =>
        Parse.givesThen
          [p := () => full self modes]
          [j := body => Binding (if keyword.isSome then BindsExists else BindsLambda) keyword params arrow body]
          (givesFullAny self modes nested)
          (body _ => Parse.givesDone byComputing)))

theorem givesForallGroup ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self):
    Parse.Gives GoodItems (() => forallGroup self modes) (found => True) :=
  Parse.givesThen (givesHeaderGroup self modes nested GroupLambda (Some forallDefault)) (group _ =>
    Parse.givesDone byComputing)

theorem givesForallParam ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (items: List Item) (item: Item):
    Parse.Gives GoodItems (() => forallParam self modes items item) (found => True) :=
  match item.kind with
    | Lower =>
      match isQualified item with
        | True => Parse.givesDone byComputing
        | False => Parse.givesThen givesBump (name _ => Parse.givesDone byComputing)
    | Underscore => Parse.givesThen givesBump (name _ => Parse.givesDone byComputing)
    | LParen =>
      match annotatedParamAhead items with
        | True => givesForallGroup self modes nested
        | False => Parse.givesDone byComputing
    | LBracket =>
      match implicitGroupAt items || namelessAutoAt items with
        | True => givesForallGroup self modes nested
        | False => Parse.givesDone byComputing
    | other => Parse.givesDone byComputing

theorem givesForallStep ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self) (items: List Item):
    Parse.Gives GoodItems (() => forallStep self modes items) (found => True) :=
  match items with
    | [item, ..rest] =>
      match modes.stops item with
        | True => Parse.givesDone byComputing
        | False => givesForallParam self modes nested items item
    | [] => Parse.givesDone byComputing

theorem givesForallParams ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self):
    Parse.Gives GoodItems (() => forallParams self modes) (found => True) :=
  Parse.givesWeaken
    [weaker := found => True]
    (Parse.givesLoop
      [holds := param => True]
      (givesAfter0 [p := () => left()] [j := items => forallStep self modes items] reads0Left (items =>
        Parse.givesWeaken (givesForallStep self modes nested items) (found ok =>
          match found with
            | Some param => byComputing
            | None => byComputing))))
    (found ok => byComputing)

theorem givesForallArrow ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (keyword: Word) (params: List Param) (atArrow: Bool):
    Parse.Gives GoodItems (() => forallArrow self modes keyword params atArrow) Out :=
  match atArrow with
    | True => Parse.givesThen givesBump (arrow _ =>
      Parse.givesThen
        [p := () => full self modes]
        [j := body => Binding BindsForall (Some keyword) params arrow body]
        (givesFullAny self modes nested)
        (body _ => Parse.givesDone byComputing))
    | False => givesFail modes _

theorem givesForallExpr ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self):
    Parse.Gives GoodItems (() => forallExpr self modes) Out :=
  Parse.givesThen givesBump (keyword _ =>
    Parse.givesThen (givesForallParams self modes nested) (params _ =>
      match params.isEmpty with
        | True => givesFail modes _
        | False =>
          givesAfter0
            [p := () => modes.at FatArrow]
            [j := atArrow => forallArrow self modes keyword params atArrow]
            (reads0At modes FatArrow)
            (atArrow => givesForallArrow self modes nested keyword params atArrow)))

theorem givesExistsLambda ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (keyword: Word) (ahead: Bool):
    Parse.Gives GoodItems (() => existsLambda self modes keyword ahead) Out :=
  match ahead with
    | True => givesLambda self modes (Some keyword) nested
    | False => givesFail modes _

theorem givesExistsExpr ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self):
    Parse.Gives GoodItems (() => existsExpr self modes) Out :=
  Parse.givesThen givesBump (keyword _ =>
    Parse.givesThen Parse.givesMark (here _ =>
      givesAfter0
        [p := () => left()]
        [j := items => existsLambda self modes keyword (lambdaAhead modes (here.left + 1) items)]
        reads0Left
        (items => givesExistsLambda self modes nested keyword (lambdaAhead modes (here.left + 1) items))))

theorem givesQuantifierOn ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self) (items: List Item):
    Parse.Gives GoodItems (() => quantifierOn self modes items) Out :=
  match items with
    | [item, ..rest] =>
      match item.kind == KwForall with
        | True => givesForallExpr self modes nested
        | False => givesExistsExpr self modes nested
    | [] => givesExistsExpr self modes nested

theorem givesQuantifier ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self):
    Parse.Gives GoodItems (() => Syntax.quantifier self modes) Out :=
  givesAfter0 [p := () => left()] [j := items => quantifierOn self modes items] reads0Left (items =>
    givesQuantifierOn self modes nested items)

theorem givesResultTypeAny ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self):
    Parse.Gives GoodItems (() => resultType self modes) (expr => True) :=
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
            | True => Parse.givesWeaken (givesEffectResult self allowed nested) (found out => byComputing)
            | False => givesFullAny self allowed nested))

theorem givesPiBinder ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self) (implicit: Bool):
    Parse.Gives GoodItems (() => piBinder self modes implicit) (found => True) :=
  match implicit with
    | True => givesImplicitBinder self modes nested
    | False => givesBinderGroup self modes nested False

theorem givesPiExpr ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (implicit: Bool)
    (nested: Nested self):
    Parse.Gives GoodItems (() => piExpr self modes implicit) Out :=
  Parse.givesThen (givesPiBinder self modes nested implicit) (binder _ =>
    Parse.givesThen (givesRefuseAttributes binder.attributes "a function type's parameter") (refusal _ =>
      Parse.givesThen (givesExpectAny modes Arrow "`->`") (arrow _ =>
        Parse.givesThen
          [p := () => resultType self modes]
          [j := result => FunctionType binder arrow result]
          (givesResultTypeAny self modes nested)
          (result _ => Parse.givesDone byComputing))))

-- `match`, clause lambdas, `handle`.

theorem givesScrutinee ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self):
    Parse.Gives GoodItems (() => scrutinee self modes) (found => True) :=
  Parse.givesThen (givesNamedBinder modes) (name _ =>
    Parse.givesThen (givesSelfAny self nested { modes = modes.sealed, level = LevelInline }) (value _ =>
      Parse.givesDone byComputing))

theorem givesArmColumn ∀ (column: Option Nat): Parse.Gives GoodItems (() => armColumn column) (found => True) :=
  givesAfter0 [p := () => left()] [j := items => armColumnOn column items] reads0Left (items =>
    Parse.givesDone byComputing)

theorem givesGuardAt ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self) (atIf: Bool):
    Parse.Gives GoodItems (() => guardAt self modes atIf) (found => True) :=
  match atIf with
    | True => Parse.givesThen givesBump (keyword _ =>
      Parse.givesThen (givesNamedBinder modes) (binder _ =>
        Parse.givesThen (givesFullAny self { modes | guard = True, lines = [] } nested) (condition _ =>
          Parse.givesDone byComputing)))
    | False => Parse.givesDone byComputing

theorem givesGuardOf ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self):
    Parse.Gives GoodItems (() => guardOf self modes) (found => True) :=
  givesAfter0 [p := () => modes.at KwIf] [j := atIf => guardAt self modes atIf] (reads0At modes KwIf) (atIf =>
    givesGuardAt self modes nested atIf)

theorem givesArmBodyOf ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (absurd: Bool) (what: Text) (atArrow: Bool):
    Parse.Gives GoodItems (() => armBodyOf self modes absurd what atArrow) (found => True) :=
  match absurd && !atArrow with
    | True => Parse.givesDone byComputing
    | False => Parse.givesThen (givesExpectAny modes FatArrow what) (arrow _ =>
      Parse.givesThen (givesFullAny self modes nested) (value _ => Parse.givesDone byComputing))

theorem givesArmBody ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (absurd: Bool) (what: Text):
    Parse.Gives GoodItems (() => armBody self modes absurd what) (found => True) :=
  givesAfter0
    [p := () => modes.at FatArrow]
    [j := atArrow => armBodyOf self modes absurd what atArrow]
    (reads0At modes FatArrow)
    (atArrow => givesArmBodyOf self modes nested absurd what atArrow)

theorem givesMatchArm ∀ (more: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (scrutinees: Nat) (column: Option Nat) (found: List Arm):
    Parse.Gives GoodItems (() => matchArm more self modes scrutinees column found) (arms => True) :=
  Parse.givesThen givesBump (bar _ =>
    Parse.givesThen (givesArmPatterns modes) (patterns _ =>
      match patterns.length != scrutinees with
        | True => Parse.readsFatal _ _
        | False => Parse.givesThen (givesGuardOf self modes nested) (guard _ =>
          Parse.givesThen (givesArmBody self modes nested (anyAbsurd patterns) "`=>`") (body _ =>
            givesMatchArms more self modes nested scrutinees column [{ bar, patterns, guard, body }, ..found]))))

theorem givesMatchArmsAhead ∀ (fuel: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (scrutinees: Nat) (column: Option Nat) (found: List Arm) (lined atPipe: Bool):
    Parse.Gives GoodItems (() => matchArmsAhead fuel self modes scrutinees column found lined atPipe) (arms => True) :=
  match fuel with
    | Succ more =>
      match atPipe && lined with
        | True => givesMatchArm more self modes nested scrutinees column found
        | False => Parse.givesDone byComputing
    | Zero => Parse.givesDone byComputing

theorem givesMatchArmsLined ∀ (fuel: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (scrutinees: Nat) (found: List Arm) (columned: (Bool, Option Nat)):
    Parse.Gives GoodItems (() => matchArmsLined fuel self modes scrutinees found columned) (arms => True) :=
  match columned with
    | (lined, column) =>
      givesAfter0
        [p := () => modes.at Pipe]
        [j := atPipe => matchArmsAhead fuel self modes scrutinees column found lined atPipe]
        (reads0At modes Pipe)
        (atPipe => givesMatchArmsAhead fuel self modes nested scrutinees column found lined atPipe)

theorem givesMatchArms ∀ (fuel: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (scrutinees: Nat) (column: Option Nat) (found: List Arm):
    Parse.Gives GoodItems (() => matchArms fuel self modes scrutinees column found) (arms => True) :=
  Parse.givesThen (givesArmColumn column) (columned _ =>
    givesMatchArmsLined fuel self modes nested scrutinees found columned)

theorem givesClauseMatchesBody ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self) (atArrow: Bool):
    Parse.Gives GoodItems (() => clauseMatchesBody self modes atArrow) (found => True) :=
  match atArrow with
    | True => givesArmBody self modes nested False "`=>`"
    | False => Parse.givesDone byComputing

theorem givesClauseBody ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (kind: ClauseKind) (absurd: Bool):
    Parse.Gives GoodItems (() => clauseBody self modes kind absurd) (found => True) :=
  match kind with
    | ClauseMatches =>
      givesAfter0
        [p := () => modes.at FatArrow]
        [j := atArrow => clauseMatchesBody self modes atArrow]
        (reads0At modes FatArrow)
        (atArrow => givesClauseMatchesBody self modes nested atArrow)
    | ClausePlain => givesArmBody self modes nested absurd "`=>`"
    | ClauseSome => givesArmBody self modes nested False "`=>`"

theorem givesClauseArmBody ∀ (more: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (kind: ClauseKind) (column: Option Nat) (found: List Arm) (bar: Word) (patterns: List Pattern):
    Parse.Gives GoodItems (() => clauseArmBody more self modes kind column found bar patterns) (arms => True) :=
  Parse.givesThen (givesGuardOf self modes nested) (guard _ =>
    Parse.givesThen (givesClauseBody self modes nested kind (anyAbsurd patterns)) (body _ =>
      givesClauseArms more self modes nested kind (Some patterns.length) column [
        { bar, patterns, guard, body },
        ..found
      ]))

theorem givesClauseArm ∀ (more: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (kind: ClauseKind) (count column: Option Nat) (found: List Arm):
    Parse.Gives GoodItems (() => clauseArm more self modes kind count column found) (arms => True) :=
  Parse.givesThen givesBump (bar _ =>
    Parse.givesThen (givesArmPatterns modes) (patterns _ =>
      match count with
        | Some first =>
          match first != patterns.length with
            | True => Parse.readsFatal _ _
            | False => givesClauseArmBody more self modes nested kind column found bar patterns
        | None => givesClauseArmBody more self modes nested kind column found bar patterns))

theorem givesClauseArmsAhead ∀ (fuel: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (kind: ClauseKind) (count column: Option Nat) (found: List Arm) (lined atPipe: Bool):
    Parse.Gives GoodItems (() => clauseArmsAhead fuel self modes kind count column found lined atPipe) (arms => True) :=
  match fuel with
    | Succ more =>
      match atPipe && lined with
        | True => givesClauseArm more self modes nested kind count column found
        | False => Parse.givesDone byComputing
    | Zero => Parse.givesDone byComputing

theorem givesClauseArmsLined ∀ (fuel: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (kind: ClauseKind) (count: Option Nat) (found: List Arm) (columned: (Bool, Option Nat)):
    Parse.Gives GoodItems (() => clauseArmsLined fuel self modes kind count found columned) (arms => True) :=
  match columned with
    | (lined, column) =>
      givesAfter0
        [p := () => modes.at Pipe]
        [j := atPipe => clauseArmsAhead fuel self modes kind count column found lined atPipe]
        (reads0At modes Pipe)
        (atPipe => givesClauseArmsAhead fuel self modes nested kind count column found lined atPipe)

theorem givesClauseArms ∀ (fuel: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (kind: ClauseKind) (count column: Option Nat) (found: List Arm):
    Parse.Gives GoodItems (() => clauseArms fuel self modes kind count column found) (arms => True) :=
  Parse.givesThen (givesArmColumn column) (columned _ =>
    givesClauseArmsLined fuel self modes nested kind count found columned)

theorem givesClauseLambda ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (keyword: Word)
    (word: Option Word) (kind: ClauseKind)
    (nested: Nested self):
    Parse.Gives GoodItems (() => clauseLambda self modes keyword word kind) Out :=
  Parse.givesThen Parse.givesMark (here _ =>
    Parse.givesThen (givesClauseArms (here.left + 1) self modes nested kind None None []) (arms _ =>
      match arms.isEmpty with
        | True => givesFail modes _
        | False => Parse.givesDone byComputing))

-- Handlers and `match induct` and `match reify`.

theorem givesHandlerName ∀ (modes: Modes) (what: Text) (underscore: Bool):
    Parse.Gives GoodItems (() => handlerName modes what underscore) (word => True) :=
  match underscore with
    | True => givesBump
    | False => givesLower modes what

theorem givesHandlerNameAt ∀ (modes: Modes) (what: Text):
    Parse.Gives GoodItems (() => handlerName modes what (modes.at Underscore)) (word => True) :=
  givesAfter0
    [p := () => modes.at Underscore]
    [j := underscore => handlerName modes what underscore]
    (reads0At modes Underscore)
    (underscore => givesHandlerName modes what underscore)

theorem givesOperationEnd ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (bar: Comments) (operation: Word) (argument: Pattern) (comma: Comments) (continuation: Word) (atComma: Bool):
    Parse.Gives GoodItems (() => operationEnd self modes bar operation argument comma continuation atComma) (found =>
      True) :=
  match atComma with
    | True => Parse.readsFatal _ _
    | False => Parse.givesThen (givesExpectFixed modes FatArrow "`=>`") (arrow _ =>
      Parse.givesThen
        [p := () => full self modes]
        [j := body => OperationClause bar operation argument comma continuation arrow body]
        (givesFullAny self modes nested)
        (body _ => Parse.givesDone byComputing))

theorem givesOperationClause ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (bar: Comments) (operation: Word) (argument: Pattern) (atArrow: Bool):
    Parse.Gives GoodItems (() => operationClause self modes bar operation argument atArrow) (found => True) :=
  match atArrow with
    | True => Parse.readsFatal _ _
    | False => Parse.givesThen (givesExpectFixed modes Comma "`,` and a name for the continuation") (comma _ =>
      Parse.givesThen (givesHandlerNameAt modes "a name for the continuation") (continuation _ =>
        givesAfter0
          [p := () => modes.at Comma]
          [j := atComma => operationEnd self modes bar operation argument comma continuation atComma]
          (reads0At modes Comma)
          (atComma => givesOperationEnd self modes nested bar operation argument comma continuation atComma)))

theorem givesHandlerClauseOf ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (bar: Comments) (atReturn: Bool):
    Parse.Gives GoodItems (() => handlerClauseOf self modes bar atReturn) (found => True) :=
  match atReturn with
    | True => Parse.givesThen givesFixedFrom (keyword _ =>
      Parse.givesThen (givesHandlerNameAt modes "a name for the result") (name _ =>
        Parse.givesThen (givesExpectFixed modes FatArrow "`=>`") (arrow _ =>
          Parse.givesThen
            [p := () => full self modes]
            [j := body => ReturnClause bar keyword name arrow body]
            (givesFullAny self modes nested)
            (body _ => Parse.givesDone byComputing))))
    | False => Parse.givesThen (givesLowerQualifiedAny modes "an operation, or `return`") (op _ =>
      Parse.givesThen (givesPatternOf modes) (arg _ =>
        givesAfter0
          [p := () => modes.at FatArrow]
          [j := atArrow => operationClause self modes bar op arg atArrow]
          (reads0At modes FatArrow)
          (atArrow => givesOperationClause self modes nested bar op arg atArrow)))

theorem givesHandlerClause ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self) (bar: Comments):
    Parse.Gives GoodItems (() => handlerClause self modes bar) (found => True) :=
  givesAfter0
    [p := () => modes.at KwReturn]
    [j := atReturn => handlerClauseOf self modes bar atReturn]
    (reads0At modes KwReturn)
    (atReturn => givesHandlerClauseOf self modes nested bar atReturn)

theorem givesClausesAhead ∀ (fuel: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (column: Option Nat) (found: List HandlerClause) (lined atPipe: Bool):
    Parse.Gives GoodItems (() => clausesAhead fuel self modes column found lined atPipe) (clauses => True) :=
  match fuel with
    | Succ more =>
      match atPipe && lined with
        | True => Parse.givesThen givesFixedFrom (bar _ =>
          Parse.givesThen (givesHandlerClause self modes nested bar) (clause _ =>
            givesClausesFrom more self modes nested column [clause, ..found]))
        | False => Parse.givesDone byComputing
    | Zero => Parse.givesDone byComputing

theorem givesClausesLined ∀ (fuel: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (found: List HandlerClause) (columned: (Bool, Option Nat)):
    Parse.Gives GoodItems (() => clausesLined fuel self modes found columned) (clauses => True) :=
  match columned with
    | (lined, column) =>
      givesAfter0
        [p := () => modes.at Pipe]
        [j := atPipe => clausesAhead fuel self modes column found lined atPipe]
        (reads0At modes Pipe)
        (atPipe => givesClausesAhead fuel self modes nested column found lined atPipe)

theorem givesClausesFrom ∀ (fuel: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (column: Option Nat) (found: List HandlerClause):
    Parse.Gives GoodItems (() => clausesFrom fuel self modes column found) (clauses => True) :=
  Parse.givesThen (givesArmColumn column) (columned _ => givesClausesLined fuel self modes nested found columned)

theorem givesHandlerClauses ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self):
    Parse.Gives GoodItems (() => handlerClauses self modes) (clauses => True) :=
  Parse.givesThen Parse.givesMark (here _ =>
    Parse.givesThen (givesClausesFrom (here.left + 1) self modes nested None []) (clauses _ =>
      match clauses.isEmpty with
        | True => givesFail modes _
        | False => Parse.givesDone byComputing))

theorem givesHandleExpr ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self):
    Parse.Gives GoodItems (() => handleExpr self modes) Out :=
  Parse.givesThen givesFixedFrom (keyword _ =>
    Parse.givesThen (givesSelfAny self nested { modes = modes.sealed, level = LevelInline }) (computation _ =>
      Parse.givesThen (givesExpectFixed modes KwWith "`with`") (withKeyword _ =>
        Parse.givesThen
          [p := () => handlerClauses self modes]
          [j := clauses => Handle keyword computation withKeyword clauses]
          (givesHandlerClauses self modes nested)
          (clauses _ => Parse.givesDone byComputing))))

theorem givesReifyComma ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (keyword reify: Comments) (computation: Expr) (comma: Bool):
    Parse.Gives GoodItems (() => reifyComma self modes keyword reify computation comma) Out :=
  match comma with
    | True => Parse.readsFatal _ _
    | False => Parse.givesThen (givesExpectFixed modes KwWith "`with`") (withKeyword _ =>
      Parse.givesThen
        [p := () => handlerClauses self modes]
        [j := clauses => Reify keyword reify computation withKeyword clauses]
        (givesHandlerClauses self modes nested)
        (clauses _ => Parse.givesDone byComputing))

theorem givesReifyExpr ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (keyword reify: Comments)
    (nested: Nested self):
    Parse.Gives GoodItems (() => reifyExpr self modes keyword reify) Out :=
  Parse.givesThen (givesSelfAny self nested { modes = modes.sealed, level = LevelInline }) (computation _ =>
    givesAfter0
      [p := () => modes.at Comma]
      [j := comma => reifyComma self modes keyword reify computation comma]
      (reads0At modes Comma)
      (comma => givesReifyComma self modes nested keyword reify computation comma))

theorem givesCaseNamesOn ∀ (fuel: Nat) (modes: Modes) (found: List Word) (seen: Option Tok):
    Parse.Gives GoodItems (() => caseNamesOn fuel modes found seen) (names => True) :=
  match fuel, seen with
    | Succ more, Some Lower =>
      Parse.givesThen (givesLower modes "a name") (name _ => givesCaseNames more modes [name, ..found])
    | Succ more, Some Underscore => Parse.givesThen givesBump (name _ => givesCaseNames more modes [name, ..found])
    | Succ more, other => Parse.givesDone byComputing
    | Zero, other => Parse.givesDone byComputing

theorem givesCaseNames ∀ (fuel: Nat) (modes: Modes) (found: List Word):
    Parse.Gives GoodItems (() => caseNames fuel modes found) (names => True) :=
  givesAfter0 [p := () => modes.peek] [j := seen => caseNamesOn fuel modes found seen] (reads0Peek modes) (seen =>
    givesCaseNamesOn fuel modes found seen)

theorem givesInductAhead ∀ (fuel: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (column: Option Nat) (found: List InductArm) (lined atPipe: Bool):
    Parse.Gives GoodItems (() => inductAhead fuel self modes column found lined atPipe) (arms => True) :=
  match fuel with
    | Succ more =>
      match atPipe && lined with
        | True => Parse.givesThen givesFixedFrom (bar _ =>
          Parse.givesThen (givesLower modes "the name of a case of `f.induct`") (case _ =>
            Parse.givesThen Parse.givesMark (here _ =>
              Parse.givesThen (givesCaseNames (here.left + 1) modes []) (names _ =>
                Parse.givesThen (givesExpectFixed modes FatArrow "`=>`") (arrow _ =>
                  Parse.givesThen (givesFullAny self modes nested) (body _ =>
                    givesInductArms more self modes nested column [{ bar, case, names, arrow, body }, ..found]))))))
        | False => Parse.givesDone byComputing
    | Zero => Parse.givesDone byComputing

theorem givesInductLined ∀ (fuel: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (found: List InductArm) (columned: (Bool, Option Nat)):
    Parse.Gives GoodItems (() => inductLined fuel self modes found columned) (arms => True) :=
  match columned with
    | (lined, column) =>
      givesAfter0
        [p := () => modes.at Pipe]
        [j := atPipe => inductAhead fuel self modes column found lined atPipe]
        (reads0At modes Pipe)
        (atPipe => givesInductAhead fuel self modes nested column found lined atPipe)

theorem givesInductArms ∀ (fuel: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (column: Option Nat) (found: List InductArm):
    Parse.Gives GoodItems (() => inductArms fuel self modes column found) (arms => True) :=
  Parse.givesThen (givesArmColumn column) (columned _ => givesInductLined fuel self modes nested found columned)

theorem givesInductComma ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (keyword induct: Comments) (call: Expr) (comma: Bool):
    Parse.Gives GoodItems (() => inductComma self modes keyword induct call comma) Out :=
  match comma with
    | True => Parse.readsFatal _ _
    | False => Parse.givesThen (givesExpectFixed modes KwWith "`with`") (withKeyword _ =>
      Parse.givesThen Parse.givesMark (here _ =>
        Parse.givesThen (givesInductArms (here.left + 1) self modes nested None []) (arms _ =>
          match arms.isEmpty with
            | True => givesFail modes _
            | False => Parse.givesDone byComputing)))

theorem givesInductExpr ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (keyword induct: Comments)
    (nested: Nested self):
    Parse.Gives GoodItems (() => inductExpr self modes keyword induct) Out :=
  Parse.givesThen (givesSelfAny self nested { modes = modes.sealed, level = LevelInline }) (call _ =>
    givesAfter0
      [p := () => modes.at Comma]
      [j := comma => inductComma self modes keyword induct call comma]
      (reads0At modes Comma)
      (comma => givesInductComma self modes nested keyword induct call comma))

theorem reads0SpecialAhead ∀ (modes: Modes) (word: Text): Reads0 (() => specialAhead modes word) :=
  reads0Then
    [p := () => wordAhead modes word]
    [j := found => specialOf found (modes.peekAt 1)]
    (reads0WordAhead modes word)
    (found =>
      reads0Then [p := () => modes.peekAt 1] [j := second => specialOf found second] (reads0PeekAt modes 1) (second =>
        reads0Done _))

theorem givesMatchSome ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (keyword: Word)
    (some: Bool) (second: Option Tok)
    (nested: Nested self):
    Parse.Gives GoodItems (() => matchSome self modes keyword some second) Out :=
  match some && isSome Pipe second with
    | True => Parse.givesThen givesBump (name _ => givesClauseLambda self modes keyword (Some name) ClauseSome nested)
    | False => Parse.givesThen (givesScrutinee self modes nested) (first _ =>
      Parse.givesThen Parse.givesMark (here _ =>
        Parse.givesThen
          (givesCommaListFrom modes
            (count => False)
            (() => scrutinee self modes)
            (found => True)
            (count => Parse.givesDone byComputing)
            (givesScrutinee self modes nested)
            (here.left + 1)
            1
            first
            []
            byComputing
            ())
          (pair _ =>
            Parse.givesThen (givesExpectAny modes KwWith "`with`") (withKeyword _ =>
              Parse.givesThen Parse.givesMark (there _ =>
                Parse.givesThen (givesMatchArms (there.left + 1) self modes nested pair.fst.length None []) (arms _ =>
                  match arms.isEmpty with
                    | True => givesFail modes _
                    | False => Parse.givesDone byComputing))))))

theorem givesMatchPipe ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (keyword: Word)
    (nested: Nested self) (piped: Bool):
    Parse.Gives GoodItems (() => matchPipe self modes keyword piped) Out :=
  match piped with
    | True => givesClauseLambda self modes keyword None ClausePlain nested
    | False =>
      givesAfter0
        [p := () => wordAhead modes "some"]
        [j := some => matchSome self modes keyword some (modes.peekAt 1)]
        (reads0WordAhead modes "some")
        (some =>
          givesAfter0
            [p := () => modes.peekAt 1]
            [j := second => matchSome self modes keyword some second]
            (reads0PeekAt modes 1)
            (second => givesMatchSome self modes keyword some second nested))

theorem givesMatchReify ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (keyword: Word)
    (nested: Nested self) (reify: Bool):
    Parse.Gives GoodItems (() => matchReify self modes keyword reify) Out :=
  match reify with
    | True => Parse.givesThen givesFixedFrom (name _ => givesReifyExpr self modes keyword.comments name nested)
    | False =>
      givesAfter0
        [p := () => modes.at Pipe]
        [j := piped => matchPipe self modes keyword piped]
        (reads0At modes Pipe)
        (piped => givesMatchPipe self modes keyword nested piped)

theorem givesMatchSpecial ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (keyword: Word)
    (nested: Nested self) (induct: Bool):
    Parse.Gives GoodItems (() => matchSpecial self modes keyword induct) Out :=
  match induct with
    | True => Parse.givesThen givesFixedFrom (name _ => givesInductExpr self modes keyword.comments name nested)
    | False =>
      givesAfter0
        [p := () => specialAhead modes "reify"]
        [j := reify => matchReify self modes keyword reify]
        (reads0SpecialAhead modes "reify")
        (reify => givesMatchReify self modes keyword nested reify)

theorem givesMatchExpr ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (keyword: Word)
    (nested: Nested self):
    Parse.Gives GoodItems (() => matchExpr self modes keyword) Out :=
  givesAfter0
    [p := () => specialAhead modes "induct"]
    [j := induct => matchSpecial self modes keyword induct]
    (reads0SpecialAhead modes "induct")
    (induct => givesMatchSpecial self modes keyword nested induct)

-- Definitions' arms.

theorem givesDefinitionArm ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self):
    Parse.Gives GoodItems (() => definitionArm self modes) (found => True) :=
  Parse.givesThen givesBump (bar _ =>
    Parse.givesThen (givesArmPatterns modes) (patterns _ =>
      Parse.givesThen (givesGuardOf self modes nested) (guard _ =>
        Parse.givesThen
          [p := () => armBody self modes (anyAbsurd patterns) "`=>` and the arm's body"]
          [j := body => { bar, patterns, guard, body }]
          (givesArmBody self modes nested (anyAbsurd patterns) "`=>` and the arm's body")
          (body _ => Parse.givesDone byComputing))))

theorem givesDefinitionArmStep ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (d column: Nat) (items: List Item):
    Parse.Gives GoodItems (() => definitionArmStep self modes d column items) (found => True) :=
  match items with
    | [] => Parse.givesDone byComputing
    | [next, ..rest] =>
      match !next.leaf.token.lineStart with
        | True => givesFail modes _
        | False =>
          match next.leaf.token.column <= d || next.kind == KwWhere with
            | True => Parse.givesDone byComputing
            | False =>
              match next.kind == Pipe && next.leaf.token.column == column with
                | True => Parse.givesThen [p := () => offset()] (givesOfReads0 reads0Offset) (here _ =>
                  Parse.givesThen (givesDefinitionArm self { modes | allow = Some here } nested) (arm _ =>
                    Parse.givesDone byComputing))
                | False =>
                  match next.kind == Pipe with
                    | True => Parse.readsFatal _ _
                    | False => Parse.readsFatal _ _

theorem givesDefinitionArmsFrom ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self) (d: Nat):
    Parse.Gives GoodItems (() => definitionArmsFrom self modes d) (found => True) :=
  Parse.givesWeaken
    [weaker := found => True]
    (Parse.givesLoop
      [holds := arm => True]
      (givesAfter0
        [p := () => left()]
        [j := items => definitionArmStep self modes d (modes.limit.getOrElse 0) items]
        reads0Left
        (items =>
          Parse.givesWeaken (givesDefinitionArmStep self modes nested d (modes.limit.getOrElse 0) items) (found ok =>
            match found with
              | Some arm => byComputing
              | None => byComputing))))
    (found ok => byComputing)

theorem givesDefinitionArmsOn ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (d: Nat) (items: List Item):
    Parse.Gives GoodItems (() => definitionArmsOn self modes d items) (found => True) :=
  match items with
    | [first, ..rest] =>
      match !first.leaf.token.lineStart with
        | True => Parse.readsFatal _ _
        | False =>
          match first.leaf.token.column <= d with
            | True => Parse.readsFatal _ _
            | False => givesDefinitionArmsFrom self { modes | limit = Some first.leaf.token.column } nested d
    | [] => givesFail modes _

theorem givesArmsBody ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (d: Nat)
    (nested: Nested self):
    Parse.Gives GoodItems (() => armsBody self modes d) BodyOk :=
  Parse.givesThen
    [p := () => definitionArms self modes d]
    [j := arms => Arms arms]
    (givesAfter0 [p := () => left()] [j := items => definitionArmsOn self modes d items] reads0Left (items =>
      givesDefinitionArmsOn self modes nested d items))
    (arms _ => Parse.givesDone byComputing)

-- Local definitions, `let`, `cases`.

theorem givesHereOn ∀ (items: List Item): Parse.Gives GoodItems (() => hereOn items) (found => True) := match items with
  | [item, ..rest] => Parse.givesDone byComputing
  | [] => Parse.givesThen [p := () => offset()] (givesOfReads0 reads0Offset) (here _ => Parse.givesDone byComputing)

theorem givesHere: Parse.Gives GoodItems (() => here()) (found => True) :=
  givesAfter0 [p := () => left()] [j := items => hereOn items] reads0Left (items => givesHereOn items)

theorem givesColumnHere: Parse.Gives GoodItems (() => columnHere()) (found => True) :=
  givesAfter0 [p := () => left()] [j := items => columnOn items] reads0Left (items => Parse.givesDone byComputing)

theorem givesLetPatternOf ∀ (modes: Modes) (isCtor: Bool):
    Parse.Gives GoodItems (() => letPatternOf modes isCtor) (pat => True) :=
  match isCtor with
    | True => Parse.givesThen givesBump (name _ =>
      givesCtorArgs pattern modes name (kind => kind == Equals || kind == ColonEq || kind == Colon) givesPattern)
    | False => givesPattern { modes, level = PatternTupleComponent }

theorem givesLetPattern ∀ (modes: Modes): Parse.Gives GoodItems (() => letPattern modes) (pat => True) :=
  givesAfter0 [p := () => ctorAhead modes] [j := isCtor => letPatternOf modes isCtor] (reads0CtorAhead modes) (isCtor =>
    givesLetPatternOf modes isCtor)

theorem givesLetAnnotation ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self) (atColon: Bool):
    Parse.Gives GoodItems (() => letAnnotation self modes atColon) (found => True) :=
  match atColon with
    | True => Parse.givesThen givesFixedFrom (colon _ =>
      Parse.givesThen (givesSelfAny self nested { modes = modes.sealed, level = LevelInline }) (annotation _ =>
        Parse.givesDone byComputing))
    | False => Parse.givesDone byComputing

theorem givesLetEquals ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (depth: Nat) (keyword: Comments) (pat: Pattern) (annotation: Option (Comments, Expr)) (atEquals: Bool):
    Parse.Gives GoodItems (() => letEquals self modes depth keyword pat annotation atEquals) (found => True) :=
  match atEquals with
    | True => Parse.readsFatal _ _
    | False => Parse.givesThen (givesExpectFixed modes ColonEq "`:=`") (colonEq _ =>
      Parse.givesThen (givesFullAny self { modes | letValue = Some depth } nested) (value _ =>
        Parse.givesDone byComputing))

theorem givesLetStatement ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self):
    Parse.Gives GoodItems (() => letStatement self modes) (found => True) :=
  Parse.givesThen givesHere (pair _ =>
    Parse.givesThen givesFixedFrom (keyword _ =>
      Parse.givesThen (givesLetPattern modes) (pat _ =>
        Parse.givesThen
          [p := () => letAnnotation self modes (modes.at Colon)]
          (givesAfter0
            [p := () => modes.at Colon]
            [j := atColon => letAnnotation self modes atColon]
            (reads0At modes Colon)
            (atColon => givesLetAnnotation self modes nested atColon))
          (annotation _ =>
            givesAfter0
              [p := () => modes.at Equals]
              [j := atEquals => letEquals self modes pair.snd keyword pat annotation atEquals]
              (reads0At modes Equals)
              (atEquals => givesLetEquals self modes nested pair.snd keyword pat annotation atEquals)))))

theorem givesLetEnd ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (binding: Let) (semicolon: Comments) (atEnd: Bool):
    Parse.Gives GoodItems (() => letEnd self modes binding semicolon atEnd) Out :=
  match atEnd with
    | True => Parse.readsFatal _ _
    | False =>
      Parse.givesThen
        [p := () => full self modes]
        [j := body => LetIn binding semicolon body]
        (givesFullAny self modes nested)
        (body _ => Parse.givesDone byComputing)

theorem givesLetBodyOf ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (binding: Let) (atSemi: Bool):
    Parse.Gives GoodItems (() => letBodyOf self modes binding atSemi) Out :=
  match atSemi with
    | False => givesFail modes _
    | True => Parse.givesThen givesFixedFrom (semicolon _ =>
      Parse.givesThen [p := () => left()] (givesOfReads0 reads0Left) (taken _ =>
        givesLetEnd self modes nested binding semicolon (letAtEnd taken)))

theorem givesLetBody ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self) (binding: Let):
    Parse.Gives GoodItems (() => letBody self modes binding) Out :=
  givesAfter0
    [p := () => modes.at Semi]
    [j := atSemi => letBodyOf self modes binding atSemi]
    (reads0At modes Semi)
    (atSemi => givesLetBodyOf self modes nested binding atSemi)

theorem givesLetExpr ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self):
    Parse.Gives GoodItems (() => letExpr self modes) Out :=
  Parse.givesThen (givesLetStatement self modes.sealed nested) (binding _ => givesLetBody self modes nested binding)

theorem givesCasesThen ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (keyword: Word) (atThen: Bool):
    Parse.Gives GoodItems (() => casesThen self modes keyword atThen) Out :=
  match atThen with
    | True => Parse.givesThen givesFixedFrom (thenKeyword _ =>
      Parse.givesThen
        [p := () => self { modes, level = LevelThenBody }]
        [j := body => Cases keyword.comments thenKeyword body]
        (givesSelfAny self nested { modes, level = LevelThenBody })
        (body _ => Parse.givesDone byComputing))
    | False => Parse.givesDone byComputing

theorem givesCasesIn ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (keyword: Word) (atIn: Bool):
    Parse.Gives GoodItems (() => casesIn self modes keyword atIn) Out :=
  match atIn with
    | True => Parse.readsFatal _ _
    | False =>
      givesAfter0
        [p := () => modes.at KwThen]
        [j := atThen => casesThen self modes keyword atThen]
        (reads0At modes KwThen)
        (atThen => givesCasesThen self modes nested keyword atThen)

theorem givesCasesExpr ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self):
    Parse.Gives GoodItems (() => casesExpr self modes) Out :=
  Parse.givesThen givesBump (keyword _ =>
    givesAfter0 [p := () => modes.at KwIn] [j := atIn => casesIn self modes keyword atIn] (reads0At modes KwIn) (atIn =>
      givesCasesIn self modes nested keyword atIn))

theorem givesMatchedPiped ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (indent: Nat) (matched: Expr)
    (matchedOut: Out matched) (piped: Bool)
    (pipeChains: ∀ (modes: Modes) (indent: Nat) (value: Expr) => Parse.Gives GoodItems
      (() => pipeChain self modes indent value)
      (result => result = value ∨ Out result)):
    Parse.Gives GoodItems (() => matchedPiped self modes indent matched piped) Out :=
  match piped with
    | True => Parse.givesWeaken (pipeChains modes indent matched) (result chained =>
      match chained with
        | Inl same => rewrite same then matchedOut
        | Inr out => out)
    | False => Parse.givesDone matchedOut

theorem givesMatchPiped ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (pipeChains: ∀ (modes: Modes) (indent: Nat) (value: Expr) => Parse.Gives GoodItems
      (() => pipeChain self modes indent value)
      (result => result = value ∨ Out result)):
    Parse.Gives GoodItems (() => matchPiped self modes) Out :=
  Parse.givesThen (givesOfReads0 reads0HeadIndent) (column _ =>
    Parse.givesThen givesBump (keyword _ =>
      Parse.givesThen
        [p := () => matchExpr self modes keyword]
        [j := matched => matchedPiped self modes column matched (atPipe modes)]
        (givesMatchExpr self modes keyword nested)
        (matched matchedOut =>
          givesAfter0
            [p := () => atPipe modes]
            [j := piped => matchedPiped self modes column matched piped]
            (reads0AtPipe modes)
            (piped => givesMatchedPiped self modes column matched matchedOut piped pipeChains))))

theorem givesExprKeyword ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (kind: Tok)
    (nested: Nested self)
    (rest: OutsideRest self):
    Parse.Gives GoodItems (() => exprKeyword self modes kind) Out :=
  match kind == KwHandle with
    | True => givesHandleExpr self modes nested
    | False =>
      match kind == KwLet with
        | True => givesLetExpr self modes nested
        | False =>
          match kind == KwCalc with
            | True => rest.calcs modes
            | False =>
              match kind == KwRewrite with
                | True => rest.rewrites modes
                | False =>
                  match kind == KwCases with
                    | True => givesCasesExpr self modes nested
                    | False => givesMatchPiped self modes nested rest.pipeChains

-- Statements other than expressions.

theorem givesDefinitionPartsAny ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (exportKeyword opaqueKeyword: Option Comments) (local: Option Nat)
    (nested: Nested self):
    Parse.Gives GoodItems (() => definitionParts self modes exportKeyword opaqueKeyword local) (parts => True) :=
  Parse.givesThen (givesDefKindOf modes) (kind _ =>
    Parse.givesThen givesFixedFrom (keyword _ =>
      Parse.givesThen (givesDefinitionName modes) (name nameOk =>
        Parse.givesThen (givesForallPart modes _) (forallKeyword _ =>
          Parse.givesThen (givesHeaderParams self modes.sealed nested) (params _ =>
            Parse.givesThen givesFixedFrom (colon _ =>
              Parse.givesThen (givesResultTypeAny self _ nested) (result _ =>
                Parse.givesThen (givesDecreasingPart self modes _ _ nested) (decreasingClause _ =>
                  Parse.givesThen (givesAfterDecreasingOf modes decreasingClause) (afterDecreasing _ =>
                    Parse.givesThen (givesUnfoldingPart modes afterDecreasing _) (unfoldingClause _ =>
                      Parse.givesThen (givesAfterUnfoldingOf afterDecreasing unfoldingClause) (afterUnfolding _ =>
                        givesAfter0 (reads0ClauseConflict afterUnfolding unfoldingClause) (conflict =>
                          match conflict with
                            | True => Parse.readsFatal _ _
                            | False => Parse.givesThen (givesBodyModes afterUnfolding _ local) (bodyModes _ =>
                              Parse.givesThen (givesDefinitionBody self bodyModes result _ _ nested) (body bodyOk =>
                                Parse.givesDone byComputing))))))))))))))

theorem givesLocalDef ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (attributes: List Attributes)
    (nested: Nested self):
    Parse.Gives GoodItems (() => localDef self modes attributes) StatementOk :=
  Parse.givesThen givesColumnHere (d _ =>
    Parse.givesThen (givesDefinitionPartsAny self modes None None (Some d) nested) (parts _ =>
      match parts with
        | (header, body) =>
          match header.unfoldingClause, body with
            | Some clause, other => Parse.readsFatal _ _
            | None, Primitive => Parse.readsFatal _ _
            | None, other => Parse.givesDone byComputing))

theorem givesLocalAttributed ∀ (self: Goal → {Parse Item} Expr) (allowed: Modes) (attributes: List Attributes)
    (nested: Nested self) (atDef atTheorem: Bool):
    Parse.Gives GoodItems (() => localAttributed self allowed attributes atDef atTheorem) StatementOk :=
  match atDef || atTheorem with
    | True => givesLocalDef self allowed attributes nested
    | False => Parse.readsFatal _ _

theorem givesAttributedLocal ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (attributes: List Attributes)
    (nested: Nested self) (items: List Item):
    Parse.Gives GoodItems (() => attributedLocal self modes attributes items) StatementOk :=
  givesAfter0
    [p := () => (allowedAt modes items).at KwDef]
    [j := atDef => localAttributed self (allowedAt modes items) attributes atDef ((allowedAt modes items).at KwTheorem)]
    (reads0At (allowedAt modes items) KwDef)
    (atDef =>
      givesAfter0
        [p := () => (allowedAt modes items).at KwTheorem]
        [j := atTheorem => localAttributed self (allowedAt modes items) attributes atDef atTheorem]
        (reads0At (allowedAt modes items) KwTheorem)
        (atTheorem => givesLocalAttributed self (allowedAt modes items) attributes nested atDef atTheorem))

theorem givesLetStatementEnd ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (binding: Let) (atSemi: Bool):
    Parse.Gives GoodItems (() => letStatementEnd self modes binding atSemi) StatementOk :=
  match atSemi with
    | True =>
      Parse.givesThen
        [p := () => letBody self modes binding]
        [j := body => ExprStatement body]
        (givesLetBody self modes nested binding)
        (body out => Parse.givesDone (outParsed 1 out))
    | False => Parse.givesDone byComputing

theorem givesStatementOther ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (kind: Tok)
    (nested: Nested self):
    Parse.Gives GoodItems (() => statementOther self modes kind) StatementOk :=
  match kind == KwLet with
    | True => Parse.givesThen (givesLetStatement self modes nested) (binding _ =>
      givesAfter0
        [p := () => modes.at Semi]
        [j := atSemi => letStatementEnd self modes binding atSemi]
        (reads0At modes Semi)
        (atSemi => givesLetStatementEnd self modes nested binding atSemi))
    | False =>
      match kind == KwDef || kind == KwTheorem with
        | True => givesLocalDef self modes [] nested
        | False =>
          match kind == At with
            | True => Parse.givesThen (givesAttributesOf modes) (attributes _ =>
              givesAfter0
                [p := () => left()]
                [j := items => attributedLocal self modes attributes items]
                reads0Left
                (items => givesAttributedLocal self modes attributes nested items))
            | False =>
              match kind == KwExport with
                | True => Parse.readsFatal _ _
                | False => Parse.readsFatal _ _

--| Everything `Outside` says, from what is not yet proved and `Nested`.
def outsideOf (self: Goal → {Parse Item} Expr) (nested: Nested self) (rest: OutsideRest self): Outside self := {
  matches = (modes keyword => givesMatchExpr self modes keyword nested),
  clauseLambdas = (modes keyword => givesClauseLambda self modes keyword None ClauseMatches nested),
  braceArguments = rest.braceArguments,
  records = (modes => givesRecordExpr self modes nested),
  rests = (modes kind => givesAtomRest self modes kind nested),
  missings = (modes => givesAtomMissing self modes),
  parenOthers = (modes second third => givesParenOther self modes second third nested),
  rightSections = (modes inside => givesRightSection self modes inside nested),
  annotations = (inner open first => givesAnnotated self inner open first nested),
  namedArguments = (modes closer closeText => givesNamedArgument self modes closer closeText nested),
  memberships = rest.memberships,
  comparisonChains = rest.comparisonChains,
  cmpIfs = (modes lhs operator => givesCmpIf self modes lhs operator nested),
  pipeChains = rest.pipeChains,
  iffs = rest.iffs,
  quantifiers = (modes => givesQuantifier self modes nested),
  semis = (modes value => givesSemi self modes value nested),
  keywords = (modes kind starts => givesExprKeyword self modes kind nested rest),
  lambdas = (modes => givesLambda self modes None nested),
  ifKeywords = (modes => givesIfKeyword self modes nested),
  piExprs = (modes implicit => givesPiExpr self modes implicit nested),
  effectResults = (allowed => givesEffectResult self allowed nested),
  statementOthers = (modes kind starts => givesStatementOther self modes kind nested)
}

--| What the parsers outside slice 1 give, for every `self` that gives what `GoalParsed` says, but for the facts `outsideOf` proves.
def OutsideGives: Type := ∀ (self: Goal → {Parse Item} Expr) => Nested self → OutsideRest self

--| `expressionAt`, which starts the recursion from a declaration's level, gives what `GoalParsed` says at every goal.
theorem givesExpressionAt ∀ (outside: OutsideGives): Nested expressionAt := goal =>
  Parse.givesRecursiveWith expressionRule
    (inner expr => GoalParsed inner expr)
    (self nested argument => givesExpressionRule self argument nested (outsideOf self nested (outside self nested)))
    goal

--| A whole expression read by `expression`, from good items: at the level of `expr`.
theorem givesExpression ∀ (modes: Modes) (outside: OutsideGives):
    Parse.Gives GoodItems (() => expression modes) (Parsed1 1) :=
  Parse.givesRecursiveWith expressionRule
    (inner expr => GoalParsed inner expr)
    (self nested argument => givesExpressionRule self argument nested (outsideOf self nested (outside self nested)))
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

--| What the frame of a declaration reads that is outside slice 1: attributes, and the declarations that aren't plain
--| definitions. `frameOf` proves some of these; `FrameRest` is what is left.
type Frame (self: Goal → {Parse Item} Expr) = {
  attributes: ∀ (modes: Modes) => Parse.Gives GoodItems (() => attributesOf modes) (found => True),
  namespaces: ∀ (seen: Seen) (modes: Modes) => Parse.Gives GoodItems (() => namespaceStep seen modes) DeclOut,
  imports: ∀ (seen: Seen) (modes: Modes) => Parse.Gives GoodItems (() => importStep seen modes) DeclOut,
  others: ∀ (modes: Modes) (attributes: List Attributes) (seen: Option Tok) => Parse.Gives GoodItems
    (() => declarationOther modes attributes seen)
    DeclOut
}

--| The part of `Frame` SW-4000 has not yet proved (`frameOf` gives the rest).
type FrameRest (self: Goal → {Parse Item} Expr) = {
  others: ∀ (modes: Modes) (attributes: List Attributes) (seen: Option Tok) => Parse.Gives GoodItems
    (() => declarationOther modes attributes seen)
    DeclOut
}

theorem givesForallEnd ∀ (modes: Modes) (word: Word) (paren bracket: Bool):
    Parse.Gives GoodItems (() => forallEnd modes word paren bracket) (found => True) :=
  match paren || bracket with
    | True => Parse.givesDone byComputing
    | False => givesFail modes _

theorem givesForallBump ∀ (modes: Modes): Parse.Gives GoodItems (() => forallBump modes) (found => True) :=
  Parse.givesThen givesBump (taken _ =>
    givesAfter0
      [p := () => modes.at LParen]
      [j := paren => forallEnd modes taken paren (modes.at LBracket)]
      (reads0At modes LParen)
      (paren =>
        givesAfter0
          [p := () => modes.at LBracket]
          [j := bracket => forallEnd modes taken paren bracket]
          (reads0At modes LBracket)
          (bracket => givesForallEnd modes taken paren bracket)))

theorem givesForallPart ∀ (modes: Modes) (kind: DefKind):
    Parse.Gives GoodItems (() => forallPart modes kind) (found => True) :=
  givesAfter0
    [p := () => modes.at KwForall]
    [j := found => forallAt modes kind found]
    (reads0At modes KwForall)
    (found =>
      match found with
        | True =>
          match kind != DefTheorem with
            | True => Parse.readsFatal _ _
            | False => givesForallBump modes
        | False => Parse.givesDone byComputing)

theorem givesDecreasingClauseOf ∀ (self: Goal → {Parse Item} Expr) (headerModes: Modes)
    (nested: Nested self):
    Parse.Gives GoodItems (() => decreasingClauseOf self headerModes) (found => True) :=
  Parse.givesThen givesFixedFrom (keyword _ =>
    Parse.givesThen (nested { modes = headerModes, level = LevelFull }) (tail _ => Parse.givesDone byComputing))

theorem givesDecreasingPart ∀ (self: Goal → {Parse Item} Expr) (modes headerModes: Modes) (isInstance: Bool)
    (nested: Nested self):
    Parse.Gives GoodItems (() => decreasingPart self modes headerModes isInstance) (found => True) :=
  givesAfter0
    [p := () => modes.at KwDecreasing]
    [j := found => decreasingAt self headerModes isInstance found]
    (reads0At modes KwDecreasing)
    (found =>
      match found with
        | True =>
          match isInstance with
            | True => Parse.readsFatal _ _
            | False => givesDecreasingClauseOf self headerModes nested
        | False => Parse.givesDone byComputing)

theorem givesUnfoldingName ∀ (modes: Modes) (upper: Bool):
    Parse.Gives GoodItems (() => unfoldingName modes upper) (found => True) :=
  match upper with
    | True => Parse.givesWeaken (givesUpperQualified modes _) (found ok => byComputing)
    | False => Parse.givesWeaken (givesLowerQualified modes _) (found ok => byComputing)

theorem givesUnfoldingNext ∀ (more: Nat) (modes: Modes) (found: List Word) (name: Word) (comma: Bool):
    Parse.Gives GoodItems (() => unfoldingNext more modes found name comma) (names => True) :=
  match comma with
    | True => Parse.givesThen givesBump (gone _ => givesUnfoldingNames more modes [name, ..found])
    | False => Parse.givesDone byComputing

theorem givesUnfoldingNames ∀ (fuel: Nat) (modes: Modes) (found: List Word):
    Parse.Gives GoodItems (() => unfoldingNames fuel modes found) (names => True) :=
  match fuel with
    | Zero => Parse.givesDone byComputing
    | Succ more =>
      Parse.givesThen
        [p := () => unfoldingName modes (modes.at Upper)]
        [j := name => unfoldingNext more modes found name (modes.at Comma)]
        (givesAfter0
          [p := () => modes.at Upper]
          [j := upper => unfoldingName modes upper]
          (reads0At modes Upper)
          (upper => givesUnfoldingName modes upper))
        (name _ =>
          givesAfter0
            [p := () => modes.at Comma]
            [j := comma => unfoldingNext more modes found name comma]
            (reads0At modes Comma)
            (comma => givesUnfoldingNext more modes found name comma))

theorem givesUnfoldingClauseOf ∀ (afterDecreasing: Modes):
    Parse.Gives GoodItems (() => unfoldingClauseOf afterDecreasing) (found => True) :=
  Parse.givesThen givesFixedFrom (keyword _ =>
    Parse.givesThen Parse.givesMark (here _ =>
      Parse.givesThen (givesUnfoldingNames (here.left + 1) afterDecreasing []) (names _ =>
        Parse.givesDone byComputing)))

theorem givesUnfoldingPart ∀ (modes afterDecreasing: Modes) (isInstance: Bool):
    Parse.Gives GoodItems (() => unfoldingPart modes afterDecreasing isInstance) (found => True) :=
  givesAfter0
    [p := () => afterDecreasing.at KwUnfolding]
    [j := found => unfoldingAt afterDecreasing isInstance found]
    (reads0At afterDecreasing KwUnfolding)
    (found =>
      match found with
        | True =>
          match isInstance with
            | True => Parse.readsFatal _ _
            | False => givesUnfoldingClauseOf afterDecreasing
        | False => Parse.givesDone byComputing)

theorem givesNamespaceAfter ∀ (modes: Modes) (keyword: Comments) (seen: Option Tok):
    Parse.Gives GoodItems (() => namespaceAfter modes keyword seen) DeclOut :=
  match seen with
    | Some Upper => Parse.givesThen [p := () => bump()] [j := name => Namespace keyword name] givesBump (name _ =>
      Parse.givesDone byComputing)
    | Some Lower => Parse.readsFatal _ _
    | other => givesFail modes _

theorem givesNamespaceStep ∀ (seen: Seen) (modes: Modes):
    Parse.Gives GoodItems (() => namespaceStep seen modes) DeclOut :=
  match seen.hasNamespace with
    | True => Parse.readsFatal _ _
    | False =>
      match seen.hasImports || seen.hasDecls with
        | True => Parse.readsFatal _ _
        | False => Parse.givesThen givesFixedFrom (keyword _ =>
          givesAfter0
            [p := () => modes.peek]
            [j := seen => namespaceAfter modes keyword seen]
            (reads0Peek modes)
            (seen => givesNamespaceAfter modes keyword seen))

--| Everything `Frame` says, from what is not yet proved and `Nested`.
def frameOf (self: Goal → {Parse Item} Expr) (nested: Nested self) (rest: FrameRest self): Frame self := {
  attributes = (modes => givesAttributesOf modes),
  namespaces = (seen modes => givesNamespaceStep seen modes),
  imports = (seen modes => givesImportStep seen modes),
  others = rest.others
}

theorem givesImportAliasWord ∀ (modes: Modes) (name: Word) (asWord: Comments) (items: List Item):
    Parse.Gives GoodItems (() => importAliasWord modes name asWord items) (found => True) :=
  match items with
    | [alias, ..rest] =>
      match named: (alias.kind == Lower || alias.kind == Upper) && !isQualified alias && !modes.stops alias with
        | True =>
          match startsUpper name.text != startsUpper alias.text with
            | True => Parse.readsFatal _ _
            | False => Parse.givesThen givesBump (taken _ => Parse.givesDone byComputing)
        | False => givesFail modes _
    | [] => givesFail modes _

theorem givesImportAlias ∀ (modes: Modes) (name: Word):
    Parse.Gives GoodItems (() => importAlias modes name) (found => True) :=
  givesAfter0
    [p := () => wordAhead modes "as"]
    [j := asNext => importAliasOn modes name asNext]
    (reads0WordAhead modes "as")
    (asNext =>
      match asNext with
        | True => Parse.givesThen givesFixedFrom (asWord _ =>
          givesAfter0 [p := () => left()] [j := items => importAliasWord modes name asWord items] reads0Left (items =>
            givesImportAliasWord modes name asWord items))
        | False => Parse.givesDone byComputing)

theorem givesImportStop ∀ (modes: Modes) (path: Word) (found: List ImportItem) (dots: Bool):
    Parse.Gives GoodItems (() => importStop modes path found dots) (names => True) :=
  match dots && !found.isEmpty with
    | True => Parse.readsFatal _ _
    | False => givesFail modes _

theorem givesImportItems ∀ (fuel: Nat) (modes: Modes) (path: Word) (found: List ImportItem):
    Parse.Gives GoodItems (() => importItems fuel modes path found) (names => True) :=
  givesAfter0 [p := () => left()] [j := items => importItemsOn fuel modes path found items] reads0Left (items =>
    match fuel, items with
      | Succ more, [item, ..rest] =>
        match named: (item.kind == Lower || item.kind == Upper) && !isQualified item && !modes.stops item with
          | True => Parse.givesThen givesBump (name _ =>
            Parse.givesThen (givesImportAlias modes name) (alias _ =>
              givesAfter0
                [p := () => modes.at Comma]
                [j := comma => importTail more modes path [{ name, alias }, ..found] comma]
                (reads0At modes Comma)
                (comma =>
                  match comma with
                    | True =>
                      Parse.givesThen givesBump (gone _ => givesImportItems more modes path [{ name, alias }, ..found])
                    | False => Parse.givesDone byComputing)))
          | False =>
            givesAfter0
              [p := () => modes.at DotDot]
              [j := dots => importStop modes path found dots]
              (reads0At modes DotDot)
              (dots => givesImportStop modes path found dots)
      | other, others =>
        givesAfter0
          [p := () => modes.at DotDot]
          [j := dots => importStop modes path found dots]
          (reads0At modes DotDot)
          (dots => givesImportStop modes path found dots))

theorem givesImportedOf ∀ (modes: Modes) (path: Word) (dots: Bool):
    Parse.Gives GoodItems (() => importedOf modes path dots) (found => True) :=
  match dots with
    | True => Parse.givesThen givesFixedFrom (written _ =>
      givesAfter0
        [p := () => modes.at RParen]
        [j := closed => importAllEnd path written closed]
        (reads0At modes RParen)
        (closed =>
          match closed with
            | True => Parse.givesDone byComputing
            | False => Parse.readsFatal _ _))
    | False => Parse.givesThen Parse.givesMark (here _ =>
      Parse.givesThen (givesImportItems (here.left + 1) modes path []) (imported _ => Parse.givesDone byComputing))

theorem givesImportClose ∀ (modes: Modes) (keyword: Comments) (path: Word) (open: Comments) (imported: Imported):
    Parse.Gives GoodItems (() => importClose modes keyword path open imported) DeclOut :=
  Parse.givesThen (givesExpectFixed modes RParen "`)`") (close _ => Parse.givesDone byComputing)

theorem givesImportOpen ∀ (modes: Modes) (keyword: Comments) (path: Word):
    Parse.Gives GoodItems (() => importOpen modes keyword path) DeclOut :=
  Parse.givesThen (givesExpectFixed modes LParen "`(` and the names to import") (open _ =>
    Parse.givesThen
      [p := () => importedOf modes path (modes.at DotDot)]
      [j := imported => importClose modes keyword path open imported]
      (givesAfter0
        [p := () => modes.at DotDot]
        [j := dots => importedOf modes path dots]
        (reads0At modes DotDot)
        (dots => givesImportedOf modes path dots))
      (imported _ => givesImportClose modes keyword path open imported))

theorem givesImportLine ∀ (modes: Modes): Parse.Gives GoodItems (() => importLine modes) DeclOut :=
  Parse.givesThen givesFixedFrom (keyword _ =>
    Parse.givesThen
      [p := () => importPath modes (modes.at Upper)]
      [j := path => importAfter modes keyword path (wordAhead modes "as")]
      (givesAfter0 [p := () => modes.at Upper] [j := upper => importPath modes upper] (reads0At modes Upper) (upper =>
        match upper with
          | True => givesBump
          | False => givesFail modes _))
      (path _ =>
        givesAfter0
          [p := () => wordAhead modes "as"]
          [j := asNext => importAfter modes keyword path asNext]
          (reads0WordAhead modes "as")
          (asNext =>
            match asNext with
              | True => Parse.readsFatal _ _
              | False => givesImportOpen modes keyword path)))

theorem givesImportStep ∀ (seen: Seen) (modes: Modes): Parse.Gives GoodItems (() => importStep seen modes) DeclOut :=
  match seen.hasDecls with
    | True => Parse.readsFatal _ _
    | False => givesImportLine modes

theorem givesLowerQualifiedAny ∀ (modes: Modes) (what: Text):
    Parse.Gives GoodItems (() => modes.lowerQualified what) (word => True) :=
  Parse.givesWeaken (givesLowerQualified modes what) (found ok => byComputing)

theorem givesAttributePart ∀ (modes: Modes) (dot: Bool):
    Parse.Gives GoodItems (() => attributePart modes dot) (Parse.Perhaps (found => True)) :=
  match dot with
    | True => Parse.givesThen givesFixedFrom (written _ =>
      Parse.givesThen (givesLowerQualifiedAny modes "the rest of the attribute's name") (part _ =>
        Parse.givesDone byComputing))
    | False => Parse.givesDone byComputing

theorem givesAttributeParts ∀ (modes: Modes): Parse.Gives GoodItems (() => attributeParts modes) (found => True) :=
  Parse.givesWeaken
    [weaker := found => True]
    (Parse.givesLoop
      (givesAfter0 [p := () => modes.at Dot] [j := dot => attributePart modes dot] (reads0At modes Dot) (dot =>
        givesAttributePart modes dot)))
    (found ok => byComputing)

theorem givesAttributeArgument ∀ (modes: Modes):
    Parse.Gives GoodItems (() => attributeArgument modes) (found => True) :=
  givesAfter0 [p := () => modes.peek] [j := seen => attributeArgumentOn modes seen] (reads0Peek modes) (seen =>
    match isSome Str seen with
      | True => Parse.givesThen givesBump (taken _ => Parse.givesDone byComputing)
      | False =>
        match isSome StrStart seen with
          | True => Parse.readsFatal _ _
          | False => Parse.givesDone byComputing)

theorem givesAttributeItems ∀ (fuel: Nat) (modes: Modes) (found: List Attribute):
    Parse.Gives GoodItems (() => attributeItems fuel modes found) (pair => True) :=
  match fuel with
    | Zero => Parse.givesDone byComputing
    | Succ more =>
      givesAfter0
        [p := () => modes.at RBracket]
        [j := closed => attributeItemsAt more modes found closed]
        (reads0At modes RBracket)
        (closed =>
          match closed && !found.isEmpty with
            | True => Parse.givesDone byComputing
            | False =>
              Parse.givesThen (givesLowerQualifiedAny modes "an attribute's name, such as `js.name`") (name _ =>
                Parse.givesThen (givesAttributeParts modes) (parts _ =>
                  Parse.givesThen (givesAttributeArgument modes) (written _ =>
                    givesAfter0
                      [p := () => modes.at Comma]
                      [j := comma => attributeNext more modes [{ name, parts, argument = written }, ..found] comma]
                      (reads0At modes Comma)
                      (comma =>
                        match comma with
                          | True => Parse.givesThen givesBump (gone _ =>
                            givesAttributeItems more modes [{ name, parts, argument = written }, ..found])
                          | False => Parse.givesDone byComputing)))))

theorem givesAttributeGroup ∀ (modes: Modes):
    Parse.Gives GoodItems (() => attributeGroup modes) (Parse.Perhaps (found => True)) :=
  Parse.givesThen givesFixedFrom (at _ =>
    Parse.givesThen (givesExpectFixed modes LBracket "`[`") (open _ =>
      Parse.givesThen Parse.givesMark (here _ =>
        Parse.givesThen (givesAttributeItems (here.left + 1) modes []) (pair _ =>
          match pair with
            | (items, trailingComma) =>
              Parse.givesThen (givesExpectFixed modes RBracket "`,` or `]` after the attribute") (close _ =>
                Parse.givesDone byComputing)))))

theorem givesAttributesOf ∀ (modes: Modes): Parse.Gives GoodItems (() => attributesOf modes) (found => True) :=
  Parse.givesWeaken
    [weaker := found => True]
    (Parse.givesLoop
      (givesAfter0 [p := () => modes.at At] [j := found => attributeGroupAt modes found] (reads0At modes At) (found =>
        match found with
          | True => givesAttributeGroup modes
          | False => Parse.givesDone byComputing)))
    (found ok => byComputing)

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
    (nested: Nested self):
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
                | True => givesArmsBody self modes d nested
                | False =>
                  match isEquals: kind == Equals with
                    | True => Parse.readsFatal _ _
                    | False => givesFail modes _
        | None =>
          match isEquation result with
            | True => Parse.readsFatal _ _
            | False => Parse.givesDone byComputing)

theorem givesDefinitionBody ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (result: Expr) (isInstance: Bool) (d: Nat)
    (nested: Nested self):
    Parse.Gives GoodItems (() => definitionBody self modes result isInstance d) BodyOk :=
  Parse.givesThen
    [p := () => definitionBodyOn self modes result d modes.peek]
    [j := body => definitionChecked isInstance body]
    (givesDefinitionBodyOn self modes result d nested)
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
    (outside: Outside self):
    Parse.Gives GoodItems (() => definitionParts self modes exportKeyword opaqueKeyword local) PartsOk :=
  Parse.givesThen (givesDefKindOf modes) (kind _ =>
    Parse.givesThen givesFixedFrom (keyword _ =>
      Parse.givesThen (givesDefinitionName modes) (name nameOk =>
        Parse.givesThen (givesForallPart modes _) (forallKeyword _ =>
          Parse.givesThen (givesHeaderParams self modes.sealed nested) (params _ =>
            Parse.givesThen givesFixedFrom (colon _ =>
              Parse.givesThen (givesResultType self _ nested outside) (result resultParsed =>
                Parse.givesThen (givesDecreasingPart self modes _ _ nested) (decreasingClause _ =>
                  Parse.givesThen (givesAfterDecreasingOf modes decreasingClause) (afterDecreasing _ =>
                    Parse.givesThen (givesUnfoldingPart modes afterDecreasing _) (unfoldingClause _ =>
                      Parse.givesThen (givesAfterUnfoldingOf afterDecreasing unfoldingClause) (afterUnfolding _ =>
                        givesAfter0 (reads0ClauseConflict afterUnfolding unfoldingClause) (conflict =>
                          match conflict with
                            | True => Parse.readsFatal _ _
                            | False => Parse.givesThen (givesBodyModes afterUnfolding _ local) (bodyModes _ =>
                              Parse.givesThen (givesDefinitionBody self bodyModes result _ _ nested) (body bodyOk =>
                                Parse.givesDone (resultParsed, nameOk, bodyOk)))))))))))))))

-- Declarations.

--| What a declaration the parser gives is, when it is within slice 1.
def DeclOk (decl: Decl): Prop := decl.within1 = True → decl.shaped1 = True ∧ decl.lexical1 = True

theorem declOut ∀ [decl: Decl] (out: DeclOut decl): DeclOk decl := within =>
  (Bool.falseNotTrue (rewrite out at within)).impossible

theorem headerNameLower ∀ (header: Header) (within: header.within1 = True): header.name.lexesAs Lower = True :=
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
        | None, None, DefPlain, None, [], None, None, within => Bool.andLeft within
        | other, others, kinds, foralls, parameters, decreasings, unfoldings, within =>
          (Bool.falseNotTrue within).impossible

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
        | None, None, DefPlain, None, [], None, None, within => Bool.andRight within
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
        (Both resultShaped valueShaped, Both (headerNameLower header headerWithin) (Both resultLexical valueLexical))

theorem givesDefinition ∀ (modes: Modes) (attributes: List Attributes) (exportKeyword opaqueKeyword: Option Comments)
    (nested: Nested expressionAt) (outside: Outside expressionAt):
    Parse.Gives GoodItems (() => definition modes attributes exportKeyword opaqueKeyword) DeclOk :=
  Parse.givesThen
    [p := () => definitionParts expressionAt modes exportKeyword opaqueKeyword None]
    [j := parts => definitionOf attributes parts]
    (givesDefinitionParts expressionAt modes exportKeyword opaqueKeyword None nested outside)
    (parts ok => match parts, ok with | (header, body), ok => Parse.givesDone (definitionOk attributes header body ok))

theorem givesDeclarationBody ∀ (modes: Modes) (attributes: List Attributes) (nested: Nested expressionAt)
    (outside: Outside expressionAt) (frame: Frame expressionAt):
    Parse.Gives GoodItems (() => declarationBody modes attributes) DeclOk :=
  givesAfter0 [p := () => modes.peek] [j := seen => declarationBodyOn modes attributes seen] (reads0Peek modes) (seen =>
    match seen with
      | Some kind =>
        match isDef: kind == KwDef || kind == KwTheorem with
          | True => givesDefinition modes attributes None None nested outside
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

theorem parseGroupsOk ∀ (outside: OutsideGives) (frame: FrameRest expressionAt) (seen: Seen)
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
            (givesDeclaration seen nested
              (outsideOf expressionAt nested (outside expressionAt nested))
              (frameOf expressionAt nested frame))
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
theorem parseFileOk ∀ (outside: OutsideGives) (frame: FrameRest expressionAt) (lexed: Lexed) (file: SourceFile)
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

theorem declsShapedLexical ∀ (decls: List Decl)
    (ok: List.All DeclOk decls)
    (within: decls.all Decl.within1 = True):
    decls.all Decl.shaped1 = True ∧ decls.all Decl.lexical1 = True :=
  match decls, ok, within with
    | [], ok, within => (byComputing, byComputing)
    | [decl, ..rest], (declOk, restOk), (Both declWithin restWithin) =>
      let (declShaped, declLexical) := declOk declWithin
      let (restShaped, restLexical) := declsShapedLexical rest restOk restWithin
      (Both declShaped restShaped, Both declLexical restLexical)

--| Every declaration of a file of slice 1 that the parser gives is shaped (`Shaped1`, `Decl.shaped1`).
--|
--| It assumes what the parsers outside slice 1 give that is not yet proved (`OutsideGives`, which is `OutsideRest`, and
--| `FrameRest`), and that every item of every declaration's group is good (the lexer's spelling, `GoodItem`).
theorem parseShaped1 ∀ (outside: OutsideGives) (frame: FrameRest expressionAt) (lexed: Lexed) (file: SourceFile)
    (good: List.All (group => List.All GoodItem (items group)) (groupsOf lexed.leaves))
    (parses: parseFile lexed = Ok file)
    (within: file.within1 = True):
    file.shaped1 = True :=
  (declsShapedLexical file.decls (parseFileOk outside frame lexed file good parses) within).left

--| Every word of the file lexes as one token of its kind (a definition's name as a lower-case name, which
--| `Header.within1` asks for).
theorem parseLexical1 ∀ (outside: OutsideGives) (frame: FrameRest expressionAt) (lexed: Lexed) (file: SourceFile)
    (good: List.All (group => List.All GoodItem (items group)) (groupsOf lexed.leaves))
    (parses: parseFile lexed = Ok file)
    (within: file.within1 = True):
    file.lexical1 = True :=
  (declsShapedLexical file.decls (parseFileOk outside frame lexed file good parses) within).right
