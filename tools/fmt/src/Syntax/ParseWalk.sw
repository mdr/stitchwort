--| The walk of slice 1's expression parser (docs/proposals/self-hosted-fmt-s1-sketch.md, ticket 16b): every parser
--| function from `expr` down to the atoms gives trees that are `Parsed1` (or `ArgParsed`, for an argument), given what
--| the parsers outside slice 1 give. `ParseProofs` has the operator ladder's folds and the look-aheads; this file has
--| the functions that read items by what they peek at, and ties the recursion together.

namespace Syntax.ParseWalk
import Std (Bool, DecEq, Eq, List, Nat, Option, Parse, Text)
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
  records: ∀ (modes: Modes) => Parse.Gives GoodItems (() => recordExpr self modes) (fields => True)
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
  givesAtom ArgParsed (expr out => outArg out) self modes head (bases modes) (outside.records modes)

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
