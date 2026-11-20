--| The walk of slice 1's expression parser (docs/proposals/self-hosted-fmt-s1-sketch.md, ticket 16b): every parser
--| function from `expr` down to the atoms gives trees that are `Parsed` (or `ArgParsed`, for an argument), given what
--| the parsers outside slice 1 give. `ParseProofs` has the operator ladder's folds and the look-aheads. The walk is split
--| across `ParseWalk…` files, each importing only the earlier ones it needs, so an edit rechecks that file and what
--| imports it. This file has the levels' statements (`ArgParsed`, `GoalRead`, …), what the outside parsers are assumed
--| to give (`Outside`), the combinators, and the functions from application down through the atoms, brackets and lists.

namespace Syntax.ParseWalk
import Std (Bool, DecEq, Eq, List, Nat, Option, Pair, Parse, Result, Text)
import Syntax (..)
import Fmt (..)
import Syntax.LexProofs (..)
import Syntax.ParseProofs (..)
import Fmt.Grammar1 (..)
import Fmt.Kinds (..)

-- What each level of the recursion gives.

--| A tree in the slice that is shaped, lexical and an argument: an atom, a bracket, or a sign on one.
def ArgParsed: Expr → Prop := InSlice (expr => expr.callArgument = True)

--| A tree in the slice that is shaped, lexical and an atom or a bracket: what `atom_base` reads at a token that is no
--| sign.
def AtomParsed: Expr → Prop := InSlice (expr => expr.primary = True)

--| A tree in the slice that is shaped, lexical and a call's head: an atom, a bracket, or `-` on a numeral.
def HeadParsed: Expr → Prop := InSlice (expr => expr.callHead = True)

--| The items read start with a sign, `-` or `!`.
def SignFirst (read: List Item): Prop :=
  ∃ (first: Item) (more: List Item) => read = [first, ..more] ∧ (first.kind = Minus ∨ first.kind = Bang)

--| What an argument is, by what it read: an atom or a bracket, or a sign on one if it read a sign first. So an
--| argument that starts at a token that opens an atom is no sign on anything (`f - -x` has no argument `- -x`).
def ArgRead (read: List Item) (expr: Expr): Prop :=
  (AtomParsed expr ∧ LeadRead read expr) ∨ (SignFirst read ∧ ArgParsed expr)

--| A tree in the slice starts with the word of the first item read: what a sign before it is glued to.
def LeadRead (read: List Item) (expr: Expr): Prop :=
  expr.within1 = True → ∃ (first: Item) (more: List Item) => read = [first, ..more] ∧ expr.lead = first.leaf.word

--| An atom or a bracket whose first token is `open` (if it is in the slice).
def AtomFrom (open: Word) (expr: Expr): Prop := AtomParsed expr ∧ (expr.within1 = True → expr.lead = open)

--| An atom or a bracket read at `item`: in the slice, it starts with the item's word, and what it read with the item.
def AtomAt (item: Item) (read: List Item) (expr: Expr): Prop :=
  AtomParsed expr ∧ (expr.within1 = True → expr.lead = item.leaf.word ∧ ∃ (more: List Item) => read = [item, ..more])

--| What `self` reads at a goal: `GoalParsed`, and for an argument, `ArgRead`.
def GoalRead (goal: Goal) (read: List Item) (expr: Expr): Prop := match goal.level with
  | LevelArgument => ArgRead read expr
  | other => GoalParsed goal expr

def GoalParsed (goal: Goal) (expr: Expr): Prop := match goal.level with
  | LevelArgument => ArgParsed expr
  | LevelFull | LevelInline => Parsed 1 expr
  | LevelLogic => Parsed 4 expr
  | LevelComparison => Parsed 6 expr
  | LevelAppend => Parsed 12 expr
  | LevelAdditive => Parsed 14 expr
  | LevelMultiplicative => Parsed 16 expr
  | LevelUnary => Parsed 18 expr
  | LevelApp => True
  | LevelThenBody => Parsed 1 expr

--| `self` reads, at every goal, what `GoalRead` says.
def Nested (self: Goal → {Parse Item} Expr): Prop :=
  ∀ (goal: Goal) => Parse.ReadsIn GoodItems (() => self goal) (GoalRead goal)

--| A tree outside slice 1's grammar, and so outside the driver's slice (`withinFalseOfOut`): every walk's spec holds
--| of it.
def Out (expr: Expr): Prop := expr.grammar1 = False

theorem withinFalseOfOut ∀ [expr: Expr] (out: Out expr): expr.within1 = False := Expr.withinOfGrammarFalse1 expr out

theorem inSliceOut ∀ (holds: Expr → Prop) [expr: Expr] (out: Out expr): InSlice holds expr :=
  inSliceOutside holds expr (withinFalseOfOut out)

theorem argLevel ∀ (expr: Expr) (argument: expr.callArgument = True): 18 <= expr.level := match expr, argument with
  | Atom _ _ | Paren _ _ _ | Tuple _ _ _ _ | ListOf _ _ _ _ | Prefix _ _, _ => arithmetic
  | other, argument => (Bool.falseNotTrue argument).impossible

theorem headLevel ∀ (expr: Expr) (head: expr.callHead = True): 18 <= expr.level := match expr, head with
  | Atom _ _ | Paren _ _ _ | Tuple _ _ _ _ | ListOf _ _ _ _ | Prefix _ _, _ => arithmetic
  | other, head => (Bool.falseNotTrue head).impossible

theorem atomicArgument ∀ (expr: Expr) (atomic: expr.primary = True): expr.callArgument = True := match expr, atomic with
  | Atom _ _ | Paren _ _ _ | Tuple _ _ _ _ | ListOf _ _ _ _, _ => byComputing
  | other, atomic => (Bool.falseNotTrue atomic).impossible

theorem atomicHead ∀ (expr: Expr) (atomic: expr.primary = True): expr.callHead = True := match expr, atomic with
  | Atom _ _ | Paren _ _ _ | Tuple _ _ _ _ | ListOf _ _ _ _, _ => byComputing
  | other, atomic => (Bool.falseNotTrue atomic).impossible

theorem atomArg ∀ [expr: Expr] (parsed: AtomParsed expr): ArgParsed expr :=
  inSliceWeaken (expr => expr.primary = True) (expr => expr.callArgument = True) parsed (atomic =>
    atomicArgument expr atomic)

theorem atomHead ∀ [expr: Expr] (parsed: AtomParsed expr): HeadParsed expr :=
  inSliceWeaken (expr => expr.primary = True) (expr => expr.callHead = True) parsed (atomic => atomicHead expr atomic)

theorem argReadParsed ∀ [read: List Item] [expr: Expr] (found: ArgRead read expr): ArgParsed expr := match found with
  | Inl (Both atom lead) => atomArg atom
  | Inr (Both signed parsed) => parsed

theorem signFirstAppend ∀ [read: List Item] (taken: List Item) (signed: SignFirst read): SignFirst (read ++ taken) :=
  match signed with
    | Witness first (Witness more (Both split sign)) =>
      Witness first (Witness (more ++ taken) (Both (rewrite split) sign))

theorem argReadAppend ∀ [read: List Item] [expr: Expr] (taken: List Item)
    (found: ArgRead read expr):
    ArgRead (read ++ taken) expr :=
  match found with
    | Inl (Both atom lead) =>
      Inl
        (Both atom (within =>
          let (first, more, split, same) := lead within
          (first, more ++ taken, (rewrite split), same)))
    | Inr (Both signed parsed) => Inr (Both (signFirstAppend taken signed) parsed)

--| A read that starts a list whose first item is no sign is no read that starts with a sign.
theorem signFirstNot ∀ [read rest later: List Item] [item: Item]
    (signed: SignFirst read)
    (whole: [item, ..later] = read ++ rest)
    (plain: (item.kind == Minus || item.kind == Bang) = False):
    Void :=
  match signed with
    | Witness first (Witness more (Both split sign)) =>
      let joined: [item, ..later] = [first, ..more ++ rest] := rewrite split at whole then whole
      let same: item = first := List.consInjectiveHead joined
      match sign with
        | Inl minus => Bool.trueNotFalse (rewrite same, minus at plain then plain)
        | Inr bang => Bool.trueNotFalse (rewrite same, bang at plain then plain)

--| An argument read from items whose first is no sign is an atom or a bracket.
theorem argReadPlain ∀ [read rest later: List Item] [item: Item] [expr: Expr]
    (found: ArgRead read expr)
    (whole: [item, ..later] = read ++ rest)
    (plain: (item.kind == Minus || item.kind == Bang) = False):
    AtomParsed expr :=
  (argReadLead found whole plain).left

theorem outArgRead ∀ [read: List Item] [expr: Expr] (out: Out expr): ArgRead read expr :=
  Inl
    (Both (inSliceOut (expr => expr.primary = True) out) (within =>
      (Bool.falseNotTrue (rewrite withinFalseOfOut out at within)).impossible))

--| `argReadPlain`, with the tree's first token: the first item's word.
theorem argReadLead ∀ [read rest later: List Item] [item: Item] [expr: Expr]
    (found: ArgRead read expr)
    (whole: [item, ..later] = read ++ rest)
    (plain: (item.kind == Minus || item.kind == Bang) = False):
    AtomParsed expr ∧ (expr.within1 = True → expr.lead = item.leaf.word) :=
  match found with
    | Inl (Both atom lead) => Both atom (within =>
      let (first, more, split, same) := lead within
      let joined: [item, ..later] = [first, ..more ++ rest] := rewrite split at whole then whole
      rewrite List.consInjectiveHead joined then same)
    | Inr (Both signed parsed) => (signFirstNot signed whole plain).impossible

--| An atom read at an item leads with the item's word.
theorem atomAtLead ∀ [item: Item] [read: List Item] [expr: Expr]
    (atom: AtomAt item read expr):
    AtomParsed expr ∧ LeadRead read expr :=
  Both atom.left (within =>
    let (same, more, split) := atom.right within
    (item, more, split, same))

theorem atomFromOut ∀ (open: Word) [expr: Expr] (out: Out expr): AtomFrom open expr :=
  Both (inSliceOut (expr => expr.primary = True) out) (within =>
    (Bool.falseNotTrue (rewrite withinFalseOfOut out at within)).impossible)

theorem givesOutFrom ∀ [p: () → {Parse Item} Expr] (open: Word)
    (gives: Parse.Gives GoodItems p Out):
    Parse.Gives GoodItems p (AtomFrom open) :=
  Parse.givesWeaken gives (value out => atomFromOut open out)

theorem givesOutAt ∀ [p: () → {Parse Item} Expr] (item: Item)
    (gives: Parse.Gives GoodItems p Out) (start: Parse.Mark Item)
    (fine: Parse.Fits Item GoodItems start.rest):
    Parse.ReadsAt start p (read value => AtomAt item read value) :=
  Parse.readsAtWeaken (gives start fine) (read value out =>
    Both (inSliceOut (expr => expr.primary = True) out) (within =>
      (Bool.falseNotTrue (rewrite withinFalseOfOut out at within)).impossible))

--| `bump` the item, then read a tree that starts with its word.
theorem readsAtBumpAt ∀ [start: Parse.Mark Item] [item: Item] [later: List Item] [k: Word → {Parse Item} Expr]
    (shape: start.rest = [item, ..later])
    (fine: Parse.Fits Item GoodItems start.rest)
    (rest: ∀ (after: Parse.Mark Item) => after.rest = later
      → Parse.Fits Item GoodItems after.rest
      → Parse.ReadsAt after (() => k item.leaf.word) (read value => AtomFrom item.leaf.word value)):
    Parse.ReadsAt start (() => k (bump())) (read value => AtomAt item read value) :=
  Parse.readsAtWeaken (readsAtBumpFirst shape fine rest) (read value (Both (Both atom lead) first) =>
    Both atom (within => (lead within, first)))

--| A token that opens an atom is no sign.
theorem opensPlain ∀ (kind: Tok) (opens: kind.opensAtom = True): (kind == Minus || kind == Bang) = False :=
  match kind, opens with
    | Lower | Upper | Num | Float | Str | StrStart | CharLit | LParen | LBracket | LBrace | Underscore | Question, _ =>
      byComputing
    | other, opens => (Bool.falseNotTrue opens).impossible

-- What the parsers outside slice 1 give. Each is `Out` (the tree is outside the slice) or `True` (the tree is wrapped in
-- a node that is). `outsideOf` and `frameOf` prove them; `FrameRest` is what is still assumed.

--| A line of a block is good when it is an expression that is: `let`s and local definitions are outside the slice.
def StatementOk (statement: Statement): Prop := match statement with
  | ExprStatement value => Parsed 1 value
  | other => True

--| The tier 0 of what the parsers outside slice 1 give: atoms, brackets, prefixes and the parsers the atoms hand to.
type OutsideAtoms (self: Goal → {Parse Item} Expr) = {
  matches: ∀ (modes: Modes) (keyword: Word) => Parse.Gives GoodItems (() => matchExpr self modes keyword) Out,
  clauseLambdas: ∀ (modes: Modes) (keyword: Word) => Parse.Gives GoodItems
    (() => clauseLambda self modes keyword None ClauseMatches)
    Out,
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

--| The tier 1 of what the parsers outside slice 1 give: `C { … }` arguments.
type OutsideBraced (self: Goal → {Parse Item} Expr) = {
  below: OutsideAtoms self,
  braceArguments: ∀ (modes: Modes) => Parse.Gives GoodItems (() => braceArgument self modes) Out
}

--| The tier 2 of what the parsers outside slice 1 give: pipelines.
type OutsidePiped (self: Goal → {Parse Item} Expr) = {
  below: OutsideBraced self,
  pipeChains: ∀ (modes: Modes) (indent: Nat) (value: Expr) => Parse.Gives GoodItems
    (() => pipeChain self modes indent value)
    (result => result = value ∨ Out result)
}

--| The tier 3 of what the parsers outside slice 1 give: comparisons, memberships, quantifiers and the logic ladder.
type OutsideCompared (self: Goal → {Parse Item} Expr) = {
  below: OutsidePiped self,
  memberships: ∀ (modes: Modes) (first: Option Tok) (element: Expr) => Parse.Gives GoodItems
    (() => membership self modes first element)
    Out,
  comparisonChains: ∀ (modes: Modes) (lhs: Expr) (kind: Tok) (operator: Word) (second: Expr) => Parse.Gives GoodItems
    (() => comparisonChain self modes lhs kind operator second)
    Out,
  cmpIfs: ∀ (modes: Modes) (lhs: Expr) (operator: Word) => Parse.Gives GoodItems
    (() => cmpIf self modes lhs operator)
    Out,
  quantifiers: ∀ (modes: Modes) => Parse.Gives GoodItems (() => Syntax.quantifier self modes) Out
}

--| The tier 4 of what the parsers outside slice 1 give: `<->`, effect results and sequences.
type OutsideIffed (self: Goal → {Parse Item} Expr) = {
  below: OutsideCompared self,
  iffs: ∀ (modes: Modes) (logic: Expr) => Parse.Gives GoodItems (() => iff self modes logic) Out,
  semis: ∀ (modes: Modes) (value: Expr) => Parse.Gives GoodItems (() => semiExpr self modes value) Out,
  effectResults: ∀ (allowed: Modes) => Parse.Gives GoodItems (() => effectResult self allowed) Out
}

--| The tier 5 of what the parsers outside slice 1 give: what only the top of an expression reads.
type Outside (self: Goal → {Parse Item} Expr) = {
  below: OutsideIffed self,
  keywords: ∀ (modes: Modes) (kind: Tok) => startsKeywordExpr kind = True
    → Parse.Gives GoodItems (() => exprKeyword self modes kind) Out,
  lambdas: ∀ (modes: Modes) => Parse.Gives GoodItems (() => lambda self modes None) Out,
  walks: ∀ (modes: Modes) => Parse.Gives GoodItems (() => walkExpr self modes) Out,
  ifKeywords: ∀ (modes: Modes) => Parse.Gives GoodItems (() => ifKeyword self modes) Out,
  piExprs: ∀ (modes: Modes) (implicit: Bool) => Parse.Gives GoodItems (() => piExpr self modes implicit) Out,
  statementOthers: ∀ (modes: Modes) (kind: Tok) => startsOtherStatement kind = True
    → Parse.Gives GoodItems (() => statementOther self modes kind) StatementOk
}

-- Combinators.

theorem givesOutIn ∀ [p: () → {Parse Item} Expr] (holds: Expr → Prop)
    (gives: Parse.Gives GoodItems p Out):
    Parse.Gives GoodItems p (InSlice holds) :=
  Parse.givesWeaken gives (value out => inSliceOut holds out)

theorem reads0MatchesBarAhead ∀ (modes: Modes): Reads0 (() => matchesBarAhead modes) :=
  Parse.reads0Then reads0Left (items => Parse.reads0Done (matchesBarOn modes items))

theorem minusBangSymbolic ∀ (kind: Tok) (is: (kind == Minus || kind == Bang) = True): kind.symbolic1 = True :=
  match kind, is with
    | Minus | Bang, _ => byComputing
    | other, is => (Bool.falseNotTrue is).impossible

--| A word read from a good item that is an operator of the alphabet is one `operatorTok` knows.
theorem operatorOfItem ∀ (item: Item)
    (good: GoodItem item)
    (symbolic: item.kind.symbolic1 = True):
    (operatorTok item.text).isSome = True :=
  rewrite operatorTokOfSpells item.kind item.text (good (symbolicWithin item.kind symbolic)) symbolic

theorem prefixParsed ∀ (operator: Word) (operand: Expr)
    (spelled: (operatorTok operator.text).isSome = True)
    (parsed: Parsed 18 operand):
    Parsed 18 (Prefix operator operand) :=
  within =>
    let (shaped, lexical, high) := parsed (Bool.andLeft within)
    (Both shaped high, Both spelled lexical, arithmetic)

-- Application.

theorem reads0Offset: Reads0 (() => offset()) := Parse.reads0Mark (here => here.offset)

theorem argsParsed ∀ (args: List Expr)
    (parsed: List.All ArgParsed args)
    (within: allWithin1 args = True):
    allShaped args = True ∧ allLexical args = True ∧ args.all Expr.callArgument = True :=
  match args, parsed, within with
    | [], parsed, within => (byComputing, byComputing, byComputing)
    | [first, ..rest], (firstParsed, restParsed), (Both firstWithin restWithin) =>
      let (firstShaped, firstLexical, firstArgument) := firstParsed firstWithin
      let (restShaped, restLexical, restArgument) := argsParsed rest restParsed restWithin
      (Both firstShaped restShaped, Both firstLexical restLexical, Both firstArgument restArgument)

--| A call is parsed: a head and arguments after it, at least one.
theorem appParsed ∀ (head first: Expr) (more: List Expr)
    (headParsed: HeadParsed head)
    (firstParsed: ArgParsed first)
    (moreParsed: List.All ArgParsed more):
    Parsed 18 (App head [first, ..more]) :=
  within =>
    let (headWithin, argsWithin) := within
    let (headShaped, headLexical, headHead) := headParsed headWithin
    let (argsShaped, argsLexical, argsArgument) := argsParsed [first, ..more] (firstParsed, moreParsed) argsWithin
    (Both headHead (Both headShaped (Both argsArgument argsShaped)), Both headLexical argsLexical, arithmetic)

theorem headParsedParsed ∀ [expr: Expr] (parsed: HeadParsed expr): Parsed 18 expr :=
  inSliceWeaken (expr => expr.callHead = True) (expr => 18 <= expr.level) parsed (head => headLevel expr head)

theorem givesOfReads0 ∀ [p: () → {Parse Item} a] (reads: Reads0 p): Parse.Gives GoodItems p (value => True) :=
  start fine => Parse.readsAtWeaken (reads start fine) (read value empty => byComputing)

theorem givesArgumentBrace ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (outside: OutsideBraced self) (brace: Bool):
    Parse.Gives GoodItems (() => argumentBrace self modes brace) ArgParsed :=
  match brace with
    | True => givesOutIn (expr => expr.callArgument = True) (outside.braceArguments modes)
    | False => Parse.readsWeaken (nested { modes, level = LevelArgument }) (read value found =>
      let read: ArgRead read value := found
      argReadParsed read)

theorem givesArgumentAt ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (outside: OutsideBraced self) (items: List Item):
    Parse.Gives GoodItems (() => argumentAt self modes items) ArgParsed :=
  match sectionLineAt modes items with
    | True => Parse.readsFatal
    | False =>
      Parse.givesAfter0
        [p := () => modes.at Upper && isSome LBrace (modes.peekAt 1)]
        (Parse.reads0Then (reads0At modes Upper) (upper =>
          match upper with
            | True => Parse.reads0Then (reads0PeekAt modes 1) (found => Parse.reads0Done _)
            | False => Parse.reads0Done False))
        (brace => givesArgumentBrace self modes nested outside brace)

theorem givesArgument ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (outside: OutsideBraced self):
    Parse.Gives GoodItems (() => argument self modes) ArgParsed :=
  Parse.givesAfter0 reads0Left (items => givesArgumentAt self modes nested outside items)

theorem givesArguments ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (outside: OutsideBraced self):
    Parse.Gives GoodItems (() => arguments self modes) (List.All ArgParsed) :=
  Parse.givesLoop
    (Parse.givesAfter0 (reads0StartsAtom modes) (starts =>
      match starts with
        | True => Parse.givesThen (givesArgument self modes nested outside) (value parsed => Parse.givesDone parsed)
        | False => Parse.givesDone byComputing))

--| What a call of `head` gives holds, when it holds of the call on parsed arguments.
theorem givesAppliedTo ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (outside: OutsideBraced self)
    (head: Expr) (holds: Expr → Prop)
    (applied: ∀ (first: Expr) (more: List Expr) => ArgParsed first
      → List.All ArgParsed more
      → holds (App head [first, ..more])):
    Parse.Gives GoodItems (() => appliedTo self modes head) holds :=
  Parse.givesThen (givesArgument self modes nested outside) (first firstParsed =>
    Parse.givesThen (givesArguments self modes nested outside) (more moreParsed =>
      Parse.givesDone (applied first more firstParsed moreParsed)))

theorem sectionedHolds ∀ (holds: Expr → Prop) (outs: ∀ (expr: Expr) => Out expr → holds expr) (section: Bool)
    (applied: Expr) (parsed: holds applied):
    holds (sectioned section applied) :=
  match section with
    | True => outs _ byComputing
    | False => parsed

--| What a call's tree, or its head alone, gives holds: when it holds of the head, of the call on parsed arguments,
--| and of every tree outside the slice.
theorem givesAppEnd ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (outside: OutsideBraced self)
    (section: Bool) (head: Expr) (applies: Bool) (holds: Expr → Prop) (outs: ∀ (expr: Expr) => Out expr → holds expr)
    (bare: holds head)
    (applied: ∀ (first: Expr) (more: List Expr) => ArgParsed first
      → List.All ArgParsed more
      → holds (App head [first, ..more])):
    Parse.Gives GoodItems (() => appEnd self modes section head applies) holds :=
  match applies with
    | True => Parse.givesThen (givesAppliedTo self modes nested outside head holds applied) (call callHolds =>
      Parse.givesDone (sectionedHolds holds outs section call callHolds))
    | False => Parse.givesDone (sectionedHolds holds outs section head bare)

theorem givesAppCalls ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (outside: OutsideBraced self)
    (section: Bool) (head: Expr) (holds: Expr → Prop) (outs: ∀ (expr: Expr) => Out expr → holds expr) (bare: holds head)
    (applied: ∀ (first: Expr) (more: List Expr) => ArgParsed first
      → List.All ArgParsed more
      → holds (App head [first, ..more])):
    Parse.Gives GoodItems (() => appCalls self modes section head) holds :=
  Parse.givesAfter0 (reads0StartsAtom modes) (applies =>
    givesAppEnd self modes nested outside section head applies holds outs bare applied)

--| A call of a head that is a call's head is parsed.
theorem givesAppCallsParsed ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (outside: OutsideBraced self)
    (section: Bool) (head: Expr)
    (headParsed: HeadParsed head):
    Parse.Gives GoodItems (() => appCalls self modes section head) (Parsed 18) :=
  givesAppCalls self modes nested outside section head
    (Parsed 18)
    (tree out => inSliceOut (expr => 18 <= expr.level) out)
    (headParsedParsed headParsed)
    (first more firstParsed moreParsed => appParsed head first more headParsed firstParsed moreParsed)

--| `app`, from a mark where `atom` reads a call's head: the unary level's calls, which start at no sign but a negative
--| numeral's.
theorem readsAppAt ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (outside: OutsideBraced self) (start: Parse.Mark Item)
    (fine: Parse.Fits Item GoodItems start.rest)
    (headAt: ∀ (here: Parse.Mark Item) => here.rest = start.rest
      → Parse.Fits Item GoodItems here.rest
      → Parse.ReadsAt here (() => atom self modes True) (read value => HeadParsed value)):
    Parse.ReadsAt start (() => app self modes) (read value => Parsed 18 value) :=
  Parse.readsAtAfter0 reads0Offset fine (at after same fits =>
    Parse.readsAtAfter0
      (Parse.reads0Then (reads0At modes Dot) (dot => Parse.reads0Done _))
      fits
      (section after2 same2 fits2 =>
        Parse.readsAtThen (headAt after2 (Eq.trans same2 same) fits2) (read head after3 starts headParsed =>
          Parse.readsAtWeaken
            (givesAppCallsParsed self modes nested outside section head headParsed after3
              (Parse.Fits.after fits2 starts))
            (taken value parsed => parsed))))

--| `atom_base` reads an argument: an atom or a bracket, or a sign on one if it read a sign first.
def AtomBases (self: Goal → {Parse Item} Expr): Prop :=
  ∀ (modes: Modes) => Parse.ReadsIn GoodItems (() => atomBase self modes) ArgRead

--| `app` from any mark, where its head may be any argument: nothing is known of what it gives (`self` at `LevelApp`
--| reads the types of a row and of a pattern, outside slice 1).
theorem givesAppAny ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (outside: OutsideBraced self)
    (bases: AtomBases self):
    Parse.Gives GoodItems (() => app self modes) (value => True) :=
  Parse.givesAfter0 reads0Offset (at =>
    Parse.givesAfter0 (Parse.reads0Then (reads0At modes Dot) (dot => Parse.reads0Done _)) (section =>
      Parse.givesThen
        (givesAtom
          (value => True)
          (value out => byComputing)
          self
          modes
          True
          (Parse.readsWeaken (bases modes) (read value found => byComputing))
          (Parse.givesWeaken (outside.below.records modes) (value out => byComputing)))
        (head _ =>
          givesAppCalls self modes nested outside section head
            (value => True)
            (tree out => byComputing)
            byComputing
            (first more firstParsed moreParsed => byComputing))))

--| `atom` reads what `atom_base` read, when that holds of more items read after it and of every tree outside the
--| slice (`atom` wraps its base only in trees outside it).
theorem readsAtomFrom ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (head: Bool)
    (outside: OutsideAtoms self)
    (spec: List Item → Expr → Prop)
    (keeps: ∀ (read taken: List Item) (value: Expr) => spec read value → spec (read ++ taken) value)
    (outs: ∀ (read: List Item) (value: Expr) => Out value → spec read value) (start: Parse.Mark Item)
    (fine: Parse.Fits Item GoodItems start.rest)
    (base: ∀ (here: Parse.Mark Item) => here.rest = start.rest
      → Parse.Fits Item GoodItems here.rest
      → Parse.ReadsAt here (() => atomBase self modes) spec):
    Parse.ReadsAt start (() => atom self modes head) spec :=
  Parse.readsAtAfter0 (reads0Peek modes) fine (first after same fits =>
    Parse.readsAtThen (base after same fits) (read found after2 starts foundHolds =>
      Parse.readsAtWeaken
        (givesAtomAfter
          (value => value = found ∨ Out value)
          (value out => Inr out)
          self
          modes
          head
          first
          found
          (Inl byComputing)
          (Parse.givesWeaken (outside.records modes) (value out => byComputing))
          after2
          (Parse.Fits.after fits starts))
        (taken value kept =>
          match kept with
            | Inl same => rewrite same then keeps read taken found foundHolds
            | Inr out => outs (read ++ taken) value out)))

--| An argument reads what `ArgRead` says.
theorem readsArgumentAtom ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (outside: OutsideAtoms self)
    (bases: AtomBases self):
    Parse.ReadsIn GoodItems (() => atom self modes False) ArgRead :=
  start fine =>
    readsAtomFrom self modes False outside ArgRead
      (read taken value found => argReadAppend taken found)
      (read value out => outArgRead out)
      start
      fine
      (here same fits => bases modes here fits)

--| What a parser reads, with what it read a start of the items there.
theorem readsAtPrefix ∀ [start: Parse.Mark Item] [p: () → {Parse Item} a] [spec: List Item → a → Prop]
    (reads: Parse.ReadsAt start p spec):
    Parse.ReadsAt start p (read value => spec read value ∧ ∃ (rest: List Item) => start.rest = read ++ rest) :=
  total state value after here honest h =>
    match reads total state value after here honest h with
      | Witness read (Both starts (Both honestAfter holds)) =>
        Witness read (Both starts (Both honestAfter (Both holds (Witness after.rest starts))))

--| `k (modes.peek)` from a mark is `k` of what `modes.peek` sees there.
theorem readsAtPeeked ∀ (modes: Modes) (k: Option Tok → {Parse Item} a) (spec: List Item → a → Prop)
    (start: Parse.Mark Item) (seen: Option Tok)
    (sees: peekIn modes 0 start.rest = seen)
    (each: Parse.ReadsAt start (() => k seen) spec):
    Parse.ReadsAt start (() => k modes.peek) spec :=
  total state value after here honest h =>
    let ran: Parse.runFrom state (() => (k (peekIn modes 0 state.at.rest), Parse.mark())) = Ok (value, after) := h
    each total state value after here honest (rewrite here, sees at ran then ran)

theorem peekSome ∀ (modes: Modes) (items: List Item) (item: Item) (later: List Item)
    (shape: items = [item, ..later])
    (stopped: modes.stops item = False):
    peekIn modes 0 items = Some item.kind :=
  rewrite shape, stopped

-- The atoms.

theorem givesFailName ∀ (modes: Modes) (what: Text) [holds: a → Prop]:
    Parse.Gives GoodItems (() => modes.failName what) holds :=
  Parse.givesAfter0 reads0Left (items =>
    match items with
      | [item, ..rest] =>
        match keywordHere modes item with
          | True => Parse.readsFatal
          | False => givesFail modes what
      | [] => givesFail modes what)

theorem wordWithinWithin ∀ (kind: Tok) (word: kind.wordWithin1 = True): kind.within1 = True := match kind, word with
  | Lower | Upper | Num | Float, _ => byComputing
  | other, word => (Bool.falseNotTrue word).impossible

theorem wordLexesAs ∀ (word: Word) (kind: Tok) (lexes: LexesAs word.text kind): word.lexesAs kind = True :=
  rewrite lexes then Both (DecEq.refl word.text) (DecEq.refl kind)

--| The word of a good item of the alphabet, as the atom of its kind.
theorem atomParsed ∀ (item: Item) (good: GoodItem item): AtomParsed (Atom item.kind item.leaf.word) := within =>
  (
    Bool.andLeft within,
    wordLexesAs item.leaf.word item.kind
      (lexesAsSpells item.kind item.text
        (good (wordWithinWithin item.kind (Bool.andLeft within)))
        (mayFollowEnd item.kind item.text)),
    byComputing
  )

theorem readsWordAtom ∀ (start: Parse.Mark Item) (item: Item) (later: List Item)
    (shape: start.rest = [item, ..later])
    (fine: Parse.Fits Item GoodItems start.rest):
    Parse.ReadsAt start (() => wordAtom item.kind) (read value => AtomAt item read value) :=
  readsAtBumpAt shape fine (after tail fits =>
    Parse.readsAtDone after _ (Both (atomParsed item (goodHead fine shape)) (within => byComputing)))

theorem prefixArgParsed ∀ (operator: Word) (operand: Expr)
    (spelled: (operatorTok operator.text).isSome = True)
    (parsed: AtomParsed operand)
    (quiet: operand.within1 = True → signQuiet operator operand = True):
    ArgParsed (Prefix operator operand) :=
  within =>
    let (shaped, lexical, atomic) := parsed (Bool.andLeft within)
    (
      Both shaped (argLevel operand (atomicArgument operand atomic)),
      Both spelled lexical,
      Bool.andIntro atomic (quiet (Bool.andLeft within))
    )

--| A sign and an item glued to it that opens an atom, with no comment between them, and a tree that leads with the
--| item's word: the sign is quiet before the tree.
theorem signQuietOf ∀ (sign next: Item) (operand: Expr)
    (isSign: sign.kind.signLike = True)
    (glued: next.glued = True)
    (opens: next.kind.opensAtom = True)
    (quiet: itemGlueQuiet sign next = True)
    (lead: operand.lead = next.leaf.word):
    signQuiet sign.leaf.word operand = True :=
  let both: (sign.leaf.trivia.trailing.isNone && next.leaf.trivia.leading.isEmpty) = True :=
    rewrite isSign, glued, opens at quiet then quiet
  let calm: quietBefore sign.leaf.word next.leaf.word = True :=
    quietBeforeOf sign.leaf next.leaf (Bool.andLeft both) (Bool.andRight both)
  calc signQuiet sign.leaf.word operand
    _ = quietBefore sign.leaf.word operand.lead := byComputing
    _ = True := rewrite lead then calm

theorem quietBeforeOf ∀ (sign next: Leaf)
    (untrailed: sign.trivia.trailing.isNone = True)
    (unled: next.trivia.leading.isEmpty = True):
    quietBefore sign.word next.word = True :=
  match trailing: sign.trivia.trailing, untrailed with
    | None, untrailed =>
      match leading: next.trivia.leading, unled with
        | [], unled => byComputing
        | [comment, ..more], unled => (Bool.falseNotTrue unled).impossible
    | Some comment, untrailed => (Bool.falseNotTrue untrailed).impossible

--| `left()` then `j` of the items left, from a mark; `j` is read from the mark after it, which has the same items.
theorem readsAtAfterLeft ∀ [start: Parse.Mark Item] [j: List Item → {Parse Item} b] [spec: List Item → b → Prop]
    (fine: Parse.Fits Item GoodItems start.rest)
    (rest: ∀ (after: Parse.Mark Item) => after.rest = start.rest
      → Parse.Fits Item GoodItems after.rest
      → Parse.ReadsAt after (() => j start.rest) spec):
    Parse.ReadsAt start (() => j (left())) spec :=
  Parse.readsAtThen (Parse.readsAtLeft start) (read value after starts (Both empty same) =>
    let tail: after.rest = start.rest := rewrite empty at starts then starts.flipped
    Parse.readsAtWeaken (rewrite same then rest after tail (Parse.Fits.after fine starts)) (taken result done =>
      rewrite empty then done))

--| `bump` first, then `k` of the word: what it read starts with the item.
theorem readsAtBumpFirst ∀ [start: Parse.Mark Item] [item: Item] [later: List Item]
    [k: Word → {Parse Item} b] [holds: b → Prop]
    (shape: start.rest = [item, ..later])
    (fine: Parse.Fits Item GoodItems start.rest)
    (rest: ∀ (after: Parse.Mark Item) => after.rest = later
      → Parse.Fits Item GoodItems after.rest
      → Parse.ReadsAt after (() => k item.leaf.word) (read value => holds value)):
    Parse.ReadsAt start (() => k (bump())) (read value => holds value ∧ ∃ (more: List Item) => read = [item, ..more]) :=
  Parse.readsAtThen (readsAtBump shape) (read word after starts (Both single same) =>
    let joined: [item, ..later] = [item, ..after.rest] := Eq.trans shape.flipped (rewrite single at starts then starts)
    Parse.readsAtWeaken
      (rewrite same then
        rest after (List.consInjective item later after.rest joined).flipped (Parse.Fits.after fine starts))
      (taken value holds => Both holds (Witness taken (rewrite single))))

--| A good `-` item's word is `-`.
theorem minusText ∀ (item: Item) (good: GoodItem item) (isMinus: item.kind = Minus): item.leaf.word.text = "-" :=
  let spells: Spells item.kind item.text := good (rewrite isMinus)
  rewrite isMinus at spells then spells

--| `-` on a numeral is an argument and a call's head.
theorem negativeParsed ∀ (minus number: Word) (kind: Tok)
    (minusIs: minus.text = "-")
    (numeral: kind = Num ∨ kind = Float)
    (parsed: AtomParsed (Atom kind number))
    (quiet: signQuiet minus (Atom kind number) = True):
    ArgParsed (Prefix minus (Atom kind number)) ∧ HeadParsed (Prefix minus (Atom kind number)) :=
  let spelled: (operatorTok minus.text).isSome = True := rewrite minusIs
  let head: (Prefix minus (Atom kind number)).callHead = True := match numeral with
    | Inl num | Inr num => rewrite minusIs, num, quiet
  Both
    (within =>
      let (shaped, lexical, atomic) := parsed (Bool.andLeft within)
      (Both shaped arithmetic, Both spelled lexical, Bool.andIntro atomic quiet))
    (within =>
      let (shaped, lexical, atomic) := parsed (Bool.andLeft within)
      (Both shaped arithmetic, Both spelled lexical, head))

theorem numeralOpens ∀ (kind: Tok) (numeral: kind = Num ∨ kind = Float): kind.opensAtom = True := match numeral with
  | Inl num | Inr num => rewrite num

theorem readsNegativeNumber ∀ (start: Parse.Mark Item) (minus number: Item) (later: List Item)
    (shape: start.rest = [minus, number, ..later])
    (isMinus: minus.kind = Minus)
    (numeral: number.kind = Num ∨ number.kind = Float)
    (glued: number.glued = True)
    (fine: Parse.Fits Item GoodItems start.rest):
    Parse.ReadsAt start (() => negativeNumber()) (read value =>
      (ArgParsed value ∧ HeadParsed value) ∧ ∃ (more: List Item) => read = [minus, ..more]) :=
  readsAtBumpFirst shape fine (after tail fits =>
    readsAtAfterLeft fits (after2 same fits2 =>
      rewrite tail then
        readsAtBumpThen (rewrite same, tail) fits2 (after3 fits3 =>
          Parse.readsAtDone after3
            (Prefix minus.leaf.word (Atom number.kind number.leaf.word))
            (negativeParsed minus.leaf.word number.leaf.word number.kind
              (minusText minus (goodHead fine shape) isMinus)
              numeral
              (atomParsed number (goodHead fits2 (rewrite same, tail)))
              (signQuietOf minus number
                (Atom number.kind number.leaf.word)
                (rewrite isMinus)
                glued
                (numeralOpens number.kind numeral)
                (quietPair fine shape)
                byComputing)))))

theorem signLike ∀ (kind: Tok) (sign: kind = Minus ∨ kind = Bang): kind.signLike = True := match sign with
  | Inl minus | Inr minus => rewrite minus

theorem minusSymbolic ∀ (kind: Tok) (is: kind = Minus): kind.symbolic1 = True := rewrite is

theorem bangSymbolic ∀ (kind: Tok) (is: kind = Bang): kind.symbolic1 = True := rewrite is

theorem signSymbolic ∀ (kind: Tok) (sign: kind = Minus ∨ kind = Bang): kind.symbolic1 = True := match sign with
  | Inl minus => minusSymbolic kind minus
  | Inr bang => bangSymbolic kind bang

theorem argumentMinusPrefix ∀ (items: List Item) (found: argumentMinus items = True): argumentPrefix items = True :=
  match items, found with
    | [sign, ..later], found => Bool.andRight found
    | [], found => (Bool.falseNotTrue found).impossible

theorem argumentBangPrefix ∀ (items: List Item) (found: argumentBang items = True): argumentPrefix items = True :=
  match items, found with
    | [sign, ..later], found => Bool.andRight found
    | [], found => (Bool.falseNotTrue found).impossible

--| A sign that negates an argument: it is followed by a token that opens an atom, so what it negates is an atom or a
--| bracket, never a sign (`ArgRead`).
--|
--| Proof idea: `argumentPrefix` says the item after the sign opens an atom; the argument read after the sign starts
--| there, so by `ArgRead` it is an atom or a bracket (`argReadPlain`). What the whole reads starts with the sign.
theorem readsPrefixAtom ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (negates: Bool) (start: Parse.Mark Item) (item: Item) (later: List Item)
    (shape: start.rest = [item, ..later])
    (sign: item.kind = Minus ∨ item.kind = Bang)
    (prefixes: negates = True → argumentPrefix start.rest = True)
    (fine: Parse.Fits Item GoodItems start.rest):
    Parse.ReadsAt start (() => prefixAtom self modes negates) ArgRead :=
  match negates, prefixes with
    | True, prefixes =>
      let (signItem, next, rest, split, signs, opens) := argumentPrefixOpens start.rest (prefixes byComputing)
      let tailSame: later = [next, ..rest] := Eq.cong (items => items.drop 1) (Eq.trans shape.flipped split)
      Parse.readsAtWeaken
        (readsAtBumpFirst [holds := ArgParsed] shape fine (after tail fits =>
          Parse.readsAtThen (nested { modes, level = LevelArgument } after fits) (read operand after2 starts found =>
            let foundRead: ArgRead read operand := found
            let whole: [next, ..rest] = read ++ after2.rest := calc [next, ..rest]
              _ = later := tailSame.flipped
              _ = after.rest := tail.flipped
              _ = read ++ after2.rest := starts
            let (atom, lead) := argReadLead foundRead whole (opensPlain next.kind opens)
            let pair: start.rest = [item, next, ..rest] := rewrite shape, tailSame
            Parse.readsAtDone after2 _
              (prefixArgParsed item.leaf.word operand
                (operatorOfItem item (goodHead fine shape) (signSymbolic item.kind sign))
                atom
                (within =>
                  signQuietOf item next operand
                    (signLike item.kind sign)
                    (argumentPrefixGlued start.rest (prefixes byComputing) item next rest pair)
                    opens
                    (quietPair fine pair)
                    (lead within))))))
        (read value (Both parsed (Witness more first)) =>
          Inr (Both (Witness item (Witness more (Both first sign))) parsed))
    | False, prefixes =>
      Parse.readsAtWeaken (givesFailName modes "an expression" start fine) (read value out => outArgRead out)

theorem readsNegativeAtomOn ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (items: List Item) (start: Parse.Mark Item) (item: Item) (later: List Item)
    (shape: start.rest = [item, ..later])
    (found: items = start.rest)
    (isMinus: item.kind = Minus)
    (fine: Parse.Fits Item GoodItems start.rest):
    Parse.ReadsAt start (() => negativeAtomOn self modes items) ArgRead :=
  match negative: negativeNumeral items with
    | True =>
      let (minus, number, rest, split, minusKind, numberKind) := negativeNumeralKinds items negative
      Parse.readsAtWeaken
        (readsNegativeNumber start minus number rest
          (rewrite <- found then split)
          minusKind
          numberKind
          (negativeNumeralGlued items negative minus number rest split)
          fine)
        (read value (Both (Both parsed head) (Witness more first)) =>
          Inr (Both (Witness minus (Witness more (Both first (Inl minusKind)))) parsed))
    | False =>
      readsPrefixAtom self modes nested
        (argumentMinus items)
        start
        item
        later
        shape
        (Inl isMinus)
        (holds => rewrite <- found then argumentMinusPrefix items holds)
        fine

theorem readsNegativeAtom ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (start: Parse.Mark Item) (item: Item) (later: List Item)
    (shape: start.rest = [item, ..later])
    (isMinus: item.kind = Minus)
    (fine: Parse.Fits Item GoodItems start.rest):
    Parse.ReadsAt start (() => negativeAtom self modes) ArgRead :=
  readsAtAfterLeft fine (after same fits =>
    readsNegativeAtomOn self modes nested start.rest after item later
      (rewrite same then shape)
      same.flipped
      isMinus
      fits)

--| `-` on a numeral at the head of a call: a call's head.
theorem readsNegativeAtomHead ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (start: Parse.Mark Item)
    (negative: negativeNumeral start.rest = True)
    (fine: Parse.Fits Item GoodItems start.rest):
    Parse.ReadsAt start (() => negativeAtom self modes) (read value => HeadParsed value) :=
  readsAtAfterLeft fine (after same fits =>
    match isNegative: negativeNumeral start.rest with
      | True =>
        let (minus, number, rest, split, minusKind, numberKind) := negativeNumeralKinds start.rest isNegative
        Parse.readsAtWeaken
          (readsNegativeNumber after minus number rest
            (rewrite same then split)
            minusKind
            numberKind
            (negativeNumeralGlued start.rest isNegative minus number rest split)
            fits)
          (read value (Both (Both parsed head) first) => head))

-- Comma lists.

--| The items of a comma list all hold, and there are at least as many as read so far.
theorem givesCommaListFrom ∀ (modes: Modes) (ends: Nat → {Parse Item} Bool)
    (next: () → {Parse Item} a) (holds: a → Prop)
    (endsGives: ∀ (count: Nat) => Parse.Gives GoodItems (() => ends count) (stop => True))
    (nextGives: Parse.Gives GoodItems next holds)
    (fuel count: Nat) (current: a) (found: List a) (currentHolds: holds current)
    (foundHolds: List.All holds found):
    Parse.Gives GoodItems (() => commaListFrom fuel modes ends next count current found) (pair =>
      List.All holds pair.fst ∧ found.length + 1 <= pair.fst.length) :=
  byWalking [reads0Peek modes, givesBump] then List.allConsReverse holds current found currentHolds foundHolds

-- Brackets.

theorem openSpelled ∀ (item: Item) (good: GoodItem item) (is: item.kind = LParen): item.leaf.word.text = "(" :=
  (rewrite is at good) byComputing

theorem bracketSpelled ∀ (item: Item) (good: GoodItem item) (is: item.kind = LBracket): item.leaf.word.text = "[" :=
  (rewrite is at good) byComputing

theorem closeSpelled ∀ (item: Item) (good: GoodItem item) (is: item.kind = RBracket): item.leaf.word.text = "]" :=
  (rewrite is at good) byComputing

theorem itemsParsed ∀ (floor: Nat) (items: List Expr)
    (parsed: List.All (Parsed floor) items)
    (within: allWithin1 items = True):
    allShaped items = True ∧ allLexical items = True :=
  match items, parsed, within with
    | [], parsed, within => (byComputing, byComputing)
    | [first, ..rest], (firstParsed, restParsed), (Both firstWithin restWithin) =>
      let (firstShaped, firstLexical, firstHigh) := firstParsed firstWithin
      let (restShaped, restLexical) := itemsParsed floor rest restParsed restWithin
      (Both firstShaped restShaped, Both firstLexical restLexical)

theorem parenParsed ∀ (open close: Word) (inner: Expr)
    (openText: open.text = "(")
    (closeText: close.text = ")")
    (parsed: Parsed 1 inner):
    AtomParsed (Paren open inner close) :=
  within =>
    let (shaped, lexical, high) := parsed within
    (
      shaped,
      Both (Text.beqOfEq open.text "(" openText) (Both (Text.beqOfEq close.text ")" closeText) lexical),
      byComputing
    )

theorem tupleParsed ∀ (open close: Word) (items: List Expr) (trailing: Bool)
    (openText: open.text = "(")
    (closeText: close.text = ")")
    (long: 2 <= items.length)
    (parsed: List.All (Parsed 1) items):
    AtomParsed (Tuple open items trailing close) :=
  within =>
    let (shaped, lexical) := itemsParsed 1 items parsed within
    (
      Both long shaped,
      Both (Text.beqOfEq open.text "(" openText) (Both (Text.beqOfEq close.text ")" closeText) lexical),
      byComputing
    )

theorem listParsed ∀ (open close: Word) (items: List Expr) (trailing: Bool)
    (openText: open.text = "[")
    (closeText: close.text = "]")
    (parsed: List.All (Parsed 1) items):
    AtomParsed (ListOf open items trailing close) :=
  within =>
    let (shaped, lexical) := itemsParsed 1 items parsed within
    (
      shaped,
      Both (Text.beqOfEq open.text "[" openText) (Both (Text.beqOfEq close.text "]" closeText) lexical),
      byComputing
    )

theorem givesTupleClose ∀ (modes: Modes): Parse.Gives GoodItems (() => tupleClose modes) (word => word.text = ")") :=
  Parse.givesAfter0 (reads0At modes Colon) (annotated =>
    match annotated with
      | True => Parse.readsFatal
      | False => givesExpect modes RParen _ byComputing)

theorem givesParenClose ∀ (inner: Modes) (open: Word) (first: Expr)
    (openText: open.text = "(")
    (parsed: Parsed 1 first):
    Parse.Gives GoodItems (() => parenClose inner open first) (AtomFrom open) :=
  Parse.givesThen (givesExpect inner RParen _ byComputing) (close closeText =>
    Parse.givesDone (Both (parenParsed open close first openText closeText parsed) (within => byComputing)))

theorem givesTupleEnd ∀ (self: Goal → {Parse Item} Expr) (inner: Modes) (open: Word) (items: List Expr) (trailing: Bool)
    (openText: open.text = "(")
    (long: 2 <= items.length)
    (parsed: List.All (Parsed 1) items):
    Parse.Gives GoodItems (() => tupleEnd inner open (items, trailing)) (AtomFrom open) :=
  Parse.givesThen (givesTupleClose inner) (close closeText =>
    Parse.givesDone
      (Both (tupleParsed open close items trailing openText closeText long parsed) (within => byComputing)))

theorem givesTupleEnds ∀ (inner: Modes) (count: Nat):
    Parse.Gives GoodItems (() => tupleEnds inner count) (stop => True) :=
  givesOfReads0 (Parse.reads0Then (reads0At inner RParen) (found => Parse.reads0Done _))

theorem givesTupleSecond ∀ (self: Goal → {Parse Item} Expr) (inner: Modes) (open: Word) (first: Expr)
    (fuel: Nat) (second: Expr)
    (nested: Nested self)
    (openText: open.text = "(")
    (parsed: Parsed 1 first)
    (secondParsed: Parsed 1 second):
    Parse.Gives GoodItems (() => tupleSecond self inner open first fuel second) (AtomFrom open) :=
  Parse.givesThen
    (givesCommaListFrom inner
      (tupleEnds inner)
      (() => full self inner)
      (Parsed 1)
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
    (parsed: Parsed 1 first):
    Parse.Gives GoodItems (() => tupleRest self inner open first) (AtomFrom open) :=
  Parse.givesThen Parse.givesMark (here _ =>
    Parse.givesThen givesBump (comma _ =>
      Parse.givesThen (nested { modes = inner, level = LevelFull }) (second secondParsed =>
        givesTupleSecond self inner open first here.left second nested openText parsed secondParsed)))

@[walk]
theorem givesBracketedFirst ∀ (self: Goal → {Parse Item} Expr) (inner: Modes) (open: Word) (first: Expr)
    (nested: Nested self)
    (outside: OutsideAtoms self)
    (openText: open.text = "(")
    (parsed: Parsed 1 first):
    Parse.Gives GoodItems (() => bracketedFirst self inner open first) (AtomFrom open) :=
  readsInPeeked inner
    (seen => bracketedAfter self inner open first seen) _
    (start fine stops => givesParenClose inner open first openText parsed start fine)
    (start item later shape fine stopped =>
      match isComma: item.kind == Comma with
        | True => givesTupleRest self inner open first nested openText parsed start fine
        | False =>
          match isColon: item.kind == Colon with
            | True => givesOutFrom open (outside.annotations inner open first) start fine
            | False => givesParenClose inner open first openText parsed start fine)

theorem givesBracketedTail ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (open: Word)
    (nested: Nested self)
    (outside: OutsideAtoms self)
    (openText: open.text = "("):
    Parse.Gives GoodItems (() => bracketedTail self modes open) (AtomFrom open) :=
  byWalking [unfold full]

theorem readsBracketed ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (outside: OutsideAtoms self)
    (start: Parse.Mark Item) (item: Item) (later: List Item)
    (shape: start.rest = [item, ..later])
    (isParen: item.kind = LParen)
    (fine: Parse.Fits Item GoodItems start.rest):
    Parse.ReadsAt start (() => bracketed self modes) (read value => AtomAt item read value) :=
  readsAtBumpAt shape fine (after tail fits =>
    givesBracketedTail self modes item.leaf.word nested outside
      (openSpelled item (goodHead fine shape) isParen)
      after
      fits)

theorem readsParenRest ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (outside: OutsideAtoms self)
    (items: List Item) (start: Parse.Mark Item) (item: Item) (later: List Item)
    (shape: start.rest = [item, ..later])
    (isParen: item.kind = LParen)
    (fine: Parse.Fits Item GoodItems start.rest):
    Parse.ReadsAt start (() => parenRest self modes items) (read value => AtomAt item read value) :=
  match rightOperator items with
    | Some inside => givesOutAt item (outside.rightSections modes inside) start fine
    | None => readsBracketed self modes nested outside start item later shape isParen fine

theorem readsParenOn ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (outside: OutsideAtoms self)
    (second third: Option Tok) (start: Parse.Mark Item) (item: Item) (later: List Item)
    (shape: start.rest = [item, ..later])
    (isParen: item.kind = LParen)
    (fine: Parse.Fits Item GoodItems start.rest):
    Parse.ReadsAt start (() => parenOn self modes second third) (read value => AtomAt item read value) :=
  match parenOutside second third with
    | True => givesOutAt item (outside.parenOthers modes second third) start fine
    | False => readsAtAfterLeft fine (after same fits =>
      readsParenRest self modes nested outside start.rest after item later (rewrite same then shape) isParen fits)

theorem readsParenAtom ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (outside: OutsideAtoms self)
    (start: Parse.Mark Item) (item: Item) (later: List Item)
    (shape: start.rest = [item, ..later])
    (isParen: item.kind = LParen)
    (fine: Parse.Fits Item GoodItems start.rest):
    Parse.ReadsAt start (() => parenAtom self modes) (read value => AtomAt item read value) :=
  Parse.readsAtAfter0 (reads0PeekAt modes 1) fine (second after same fits =>
    Parse.readsAtAfter0 (reads0PeekAt modes 2) fits (third after2 same2 fits2 =>
      readsParenOn self modes nested outside second third after2 item later
        (rewrite same2, same then shape)
        isParen
        fits2))

-- Lists.

theorem givesListSpread ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (dots: Word) (empty: Bool)
    (nested: Nested self):
    Parse.Gives GoodItems (() => listSpread self modes dots empty) (Parsed 1) :=
  match empty with
    | True => Parse.readsFatal
    | False => Parse.givesThen (nested { modes, level = LevelFull }) (value valueParsed =>
      Parse.givesDone (parsedOutside 1 _ byComputing))

theorem givesListItemAfter ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (spread: Bool)
    (nested: Nested self):
    Parse.Gives GoodItems (() => listItemAfter self modes spread) (Parsed 1) :=
  match spread with
    | True => Parse.givesThen givesBump (dots _ =>
      Parse.givesAfter0
        (Parse.reads0Then (reads0At modes Comma) (comma =>
          match comma with
            | True => Parse.reads0Done True
            | False => reads0At modes RBracket))
        (empty => givesListSpread self modes dots empty nested))
    | False => nested { modes, level = LevelFull }

@[walk]
theorem givesListItem ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self):
    Parse.Gives GoodItems (() => listItem self modes) (Parsed 1) :=
  Parse.givesAfter0 (reads0At modes DotDot) (spread => givesListItemAfter self modes spread nested)

theorem givesListItemsEnd ∀ (self: Goal → {Parse Item} Expr) (inner: Modes) (open: Word)
    (items: List Expr) (trailing: Bool)
    (openText: open.text = "[")
    (parsed: List.All (Parsed 1) items):
    Parse.Gives GoodItems (() => listItemsEnd self inner open (items, trailing)) (AtomFrom open) :=
  Parse.givesThen (givesExpect inner RBracket _ byComputing) (close closeText =>
    Parse.givesDone (Both (listParsed open close items trailing openText closeText parsed) (within => byComputing)))

@[walk]
theorem givesListItemsFrom ∀ (self: Goal → {Parse Item} Expr) (inner: Modes) (open: Word) (first: Expr)
    (nested: Nested self)
    (openText: open.text = "[")
    (firstParsed: Parsed 1 first):
    Parse.Gives GoodItems (() => listItemsFrom self inner open first) (AtomFrom open) :=
  Parse.givesThen Parse.givesMark (here _ =>
    Parse.givesThen
      (givesCommaListFrom inner
        (count => inner.at RBracket)
        (() => listItem self inner)
        (Parsed 1)
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
    Parse.Gives GoodItems (() => listItems self inner open) (AtomFrom open) :=
  byWalking []

theorem givesListAfter ∀ (self: Goal → {Parse Item} Expr) (inner: Modes) (open: Word)
    (nested: Nested self)
    (openText: open.text = "["):
    Parse.Gives GoodItems (() => listPeek self inner open) (AtomFrom open) :=
  readsInPeeked inner
    (seen => listAfter self inner open seen) _
    (start fine stops => givesListItems self inner open nested openText start fine)
    (start item later shaped fine stopped =>
      match isClose: item.kind == RBracket with
        | True => readsAtBumpThen shaped fine (after fits =>
          Parse.readsAtDone after
            (ListOf open [] False item.leaf.word)
            (Both
              (listParsed open item.leaf.word [] False openText
                (closeSpelled item (goodHead fine shaped) (DecEq.sound isClose))
                ())
              (within => byComputing)))
        | False => givesListItems self inner open nested openText start fine)

theorem readsListExpr ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (start: Parse.Mark Item) (item: Item) (later: List Item)
    (shape: start.rest = [item, ..later])
    (isBracket: item.kind = LBracket)
    (fine: Parse.Fits Item GoodItems start.rest):
    Parse.ReadsAt start (() => listExpr self modes) (read value => AtomAt item read value) :=
  readsAtBumpAt shape fine (after tail fits =>
    givesListAfter self modes.inBrackets item.leaf.word nested
      (bracketSpelled item (goodHead fine shape) isBracket)
      after
      fits)

theorem readsBracketAt ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (outside: OutsideAtoms self)
    (second third: Option Tok) (start: Parse.Mark Item) (item: Item) (later: List Item)
    (shape: start.rest = [item, ..later])
    (isBracket: item.kind = LBracket)
    (fine: Parse.Fits Item GoodItems start.rest):
    Parse.ReadsAt start (() => bracketAt self modes second third) (read value => AtomAt item read value) :=
  match named: (isSome Lower second || isSome KwDecreasing second) && isSome ColonEq third with
    | True => givesOutAt item (outside.namedArguments modes RBracket "`]`") start fine
    | False => readsListExpr self modes nested start item later shape isBracket fine

theorem readsBracketAtom ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (outside: OutsideAtoms self)
    (start: Parse.Mark Item) (item: Item) (later: List Item)
    (shape: start.rest = [item, ..later])
    (isBracket: item.kind = LBracket)
    (fine: Parse.Fits Item GoodItems start.rest):
    Parse.ReadsAt start (() => bracketAtom self modes) (read value => AtomAt item read value) :=
  Parse.readsAtAfter0 (reads0PeekAt modes 1) fine (second after same fits =>
    Parse.readsAtAfter0 (reads0PeekAt modes 2) fits (third after2 same2 fits2 =>
      readsBracketAt self modes nested outside second third after2 item later
        (rewrite same2, same then shape)
        isBracket
        fits2))

--| `atom_base` at a token that is no sign: an atom or a bracket (or a tree outside the slice).
theorem readsAtomPlainOf ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (outside: OutsideAtoms self)
    (start: Parse.Mark Item) (item: Item) (later: List Item)
    (shape: start.rest = [item, ..later])
    (fine: Parse.Fits Item GoodItems start.rest)
    (isMinus: (item.kind == Minus) = False)
    (isBang: (item.kind == Bang) = False):
    Parse.ReadsAt start (() => atomOf self modes item.kind) (read value => AtomAt item read value) :=
  rewrite isMinus, isBang then
    match isParen: item.kind == LParen with
      | True => readsParenAtom self modes nested outside start item later shape (DecEq.sound isParen) fine
      | False =>
        match isBracket: item.kind == LBracket with
          | True => readsBracketAtom self modes nested outside start item later shape (DecEq.sound isBracket) fine
          | False =>
            match word: isWord item.kind with
              | True => readsWordAtom start item later shape fine
              | False => givesOutAt item (outside.rests modes item.kind) start fine

theorem readsAtomOf ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (outside: OutsideAtoms self)
    (start: Parse.Mark Item) (item: Item) (later: List Item)
    (shape: start.rest = [item, ..later])
    (fine: Parse.Fits Item GoodItems start.rest):
    Parse.ReadsAt start (() => atomOf self modes item.kind) ArgRead :=
  match isMinus: item.kind == Minus with
    | True => readsNegativeAtom self modes nested start item later shape (DecEq.sound isMinus) fine
    | False =>
      match isBang: item.kind == Bang with
        | True => readsAtAfterLeft fine (after same fits =>
          readsPrefixAtom self modes nested
            (argumentBang start.rest)
            after
            item
            later
            (rewrite same then shape)
            (Inr (DecEq.sound isBang))
            (holds => rewrite same then argumentBangPrefix start.rest holds)
            fits)
        | False =>
          let plain := readsAtomPlainOf self modes nested outside start item later shape fine isMinus isBang
          rewrite isMinus, isBang at plain then Parse.readsAtWeaken plain (read value atom => Inl (atomAtLead atom))

theorem givesAtomBases ∀ (self: Goal → {Parse Item} Expr)
    (nested: Nested self)
    (outside: OutsideAtoms self):
    AtomBases self :=
  modes =>
    readsInPeeked modes
      (seen => atomBaseOn self modes seen) _
      (start fine stops => Parse.readsAtWeaken (outside.missings modes start fine) (read value out => outArgRead out))
      (start item later shape fine stopped => readsAtomOf self modes nested outside start item later shape fine)
