--| What the parser guarantees of the trees it gives in slice 1 of the proved formatter (docs/proposals/
--| self-hosted-fmt-s1-sketch.md, ticket 16a): `Shaped1` and `Lexical1` of the expression layer, proved one parser
--| function at a time with std's `Parse.Gives` lemmas.

namespace Syntax.ParseProofs
import Std (Bool, DecEq, Eq, List, Nat, Option, Parse, Text)
import Syntax (..)
import Fmt (..)
import Syntax.LexProofs (..)
import Fmt.Grammar1 (..)

--| What a parser function gives of a tree of slice 1: it is shaped and lexical, and `holds` of it. A tree outside the
--| slice says nothing, so the constructs of later slices (a `match`, a lambda, a section) need no case of their own.
def InSlice (holds: Expr → Prop) (expr: Expr): Prop :=
  expr.within1 = True → expr.shaped = True ∧ expr.lexical = True ∧ holds expr

--| At least at the level `floor` of the precedence ladder.
def Parsed (floor: Nat): Expr → Prop := InSlice (expr => floor <= expr.level)

theorem inSliceWeaken ∀ (holds weaker: Expr → Prop) [expr: Expr]
    (found: InSlice holds expr) (implies: holds expr → weaker expr):
    InSlice weaker expr :=
  within =>
    let (shaped, lexical, fact) := found within
    (shaped, lexical, implies fact)

theorem parsedWeaken ∀ [floor lower: Nat] [expr: Expr]
    (parsed: Parsed floor expr)
    (below: lower <= floor):
    Parsed lower expr :=
  inSliceWeaken (expr => floor <= expr.level) (expr => lower <= expr.level) parsed (high => arithmetic [high, below])

--| A binary operator's right operand is at the level `rightNeeds` asks, given the floor its parser reads it at: the
--| operator's own level, for a comparison (`leftNeeds` is 8) the 8 its operand needs, and for an operator that nests
--| to the left (`leftNeeds` is its own level) the next level up.
theorem rightNeedsLe ∀ (text: Text) (rightFloor: Nat)
    (allows: infixLevel InfixBinary text <= rightFloor)
    (compares: leftNeeds InfixBinary text = 8 → 8 <= rightFloor)
    (leftward: leftNeeds InfixBinary text = infixLevel InfixBinary text
      → infixLevel InfixBinary text + 2 <= rightFloor):
    rightNeeds InfixBinary text <= rightFloor :=
  match isCompare: leftNeeds InfixBinary text == 8 with
    | True => arithmetic [compares (DecEq.sound isCompare)]
    | False =>
      match isLeft: leftNeeds InfixBinary text == infixLevel InfixBinary text with
        | True => arithmetic [leftward (DecEq.sound isLeft)]
        | False => arithmetic [allows]

--| A binary operator's tree is parsed when its operands are, at levels the operator's table allows.
theorem infixParsed ∀ (left right: Expr) (operator: Word) (leftFloor rightFloor: Nat)
    (leftParsed: Parsed leftFloor left)
    (rightParsed: Parsed rightFloor right)
    (spelled: (operatorTok operator.text).isSome = True)
    (needs: leftNeeds InfixBinary operator.text <= leftFloor)
    (allows: infixLevel InfixBinary operator.text <= rightFloor)
    (compares: leftNeeds InfixBinary operator.text = 8 → 8 <= rightFloor)
    (leftward: leftNeeds InfixBinary operator.text = infixLevel InfixBinary operator.text
      → infixLevel InfixBinary operator.text + 2 <= rightFloor):
    Parsed (infixLevel InfixBinary operator.text) (Infix InfixBinary left operator right) :=
  within =>
    let (leftWithin, rightWithin, operatorWithin) := within
    let (leftShaped, leftLexical, leftHigh) := leftParsed leftWithin
    let (rightShaped, rightLexical, rightHigh) := rightParsed rightWithin
    let needed: leftNeeds InfixBinary operator.text <= left.level := arithmetic [needs, leftHigh]
    let allowed: rightNeeds InfixBinary operator.text <= right.level :=
      arithmetic [rightNeedsLe operator.text rightFloor allows compares leftward, rightHigh]
    let own: infixLevel InfixBinary operator.text <= infixLevel InfixBinary operator.text := arithmetic
    (Both leftShaped (Both rightShaped (Both needed allowed)), Both leftLexical (Both spelled rightLexical), own)

--| `infixParsed` at the operator's own level.
theorem infixParsedAt ∀ (left right: Expr) (operator: Word) (level leftFloor rightFloor: Nat)
    (leftParsed: Parsed leftFloor left)
    (rightParsed: Parsed rightFloor right)
    (spelled: (operatorTok operator.text).isSome = True)
    (needs: leftNeeds InfixBinary operator.text <= leftFloor)
    (allows: infixLevel InfixBinary operator.text <= rightFloor)
    (compares: leftNeeds InfixBinary operator.text = 8 → 8 <= rightFloor)
    (leftward: leftNeeds InfixBinary operator.text = infixLevel InfixBinary operator.text
      → infixLevel InfixBinary operator.text + 2 <= rightFloor)
    (own: infixLevel InfixBinary operator.text = level):
    Parsed level (Infix InfixBinary left operator right) :=
  rewrite <- own then
    infixParsed left right operator leftFloor rightFloor leftParsed rightParsed spelled needs allows compares leftward

--| An operator at `level` that nests to the left, with its operand at the next level up: `leftNested`'s links.
def LeftLink (level: Nat) (link: (Word, Expr)): Prop :=
  (operatorTok link.fst.text).isSome = True
    ∧ leftNeeds InfixBinary link.fst.text = level
    ∧ infixLevel InfixBinary link.fst.text = level
    ∧ Parsed (level + 2) link.snd

--| Folding links to the left keeps a tree parsed, at the links' level.
--|
--| Proof idea: by induction on the links; each link adds one `Infix` whose left operand is the tree so far, which is at
--| the level the operator needs.
theorem leftNestedParsed ∀ (level: Nat) (first: Expr) (links: List (Word, Expr))
    (firstParsed: Parsed level first)
    (linksParsed: List.All (LeftLink level) links):
    Parsed level (leftNested first links) :=
  match links, linksParsed with
    | [], _ => firstParsed
    | [(operator, next), ..rest], (Both spelled (Both needs (Both own nextParsed)), restParsed) =>
      leftNestedParsed level
        (Infix InfixBinary first operator next)
        rest
        (infixParsedAt first next operator level level
          (level + 2)
          firstParsed
          nextParsed
          spelled
          (arithmetic [needs])
          (arithmetic [own])
          (same => arithmetic [needs, same])
          (same => arithmetic [own])
          own)
        restParsed

--| An operator at `level` that nests to the right, with its operand: `rightNested`'s links.
def RightLink (level: Nat) (link: (Word, Expr)): Prop :=
  (operatorTok link.fst.text).isSome = True
    ∧ leftNeeds InfixBinary link.fst.text = level + 2
    ∧ infixLevel InfixBinary link.fst.text = level
    ∧ Parsed (level + 2) link.snd

--| Folding links to the right keeps a tree parsed: its operands are at the next level up, the nested rest at this one.
--| `high` keeps the level above a comparison's own (a comparison's right operand is read at 8).
theorem rightNestedParsed ∀ (level: Nat) (first: Expr) (links: List (Word, Expr))
    (high: 7 <= level)
    (firstParsed: Parsed (level + 2) first)
    (linksParsed: List.All (RightLink level) links):
    Parsed level (rightNested first links) :=
  match links, linksParsed with
    | [], _ => parsedWeaken firstParsed (arithmetic)
    | [(operator, next), ..rest], (Both spelled (Both needs (Both own nextParsed)), restParsed) =>
      infixParsedAt first
        (rightNested next rest)
        operator
        level
        (level + 2)
        level
        firstParsed
        (rightNestedParsed level next rest high nextParsed restParsed)
        spelled
        (arithmetic [needs])
        (arithmetic [own])
        (same => arithmetic [needs, same, high])
        (same => arithmetic [needs, own, same])
        own

-- The items.

--| What the lexer's theorems say of an item of slice 1's alphabet: its text is one the kind is spelled with.
def GoodItem (item: Item): Prop := item.kind.within1 = True → Spells item.kind item.text

--| A `-` or `!`.
def Tok.signLike (kind: Tok): Bool := kind == Minus || kind == Bang

--| What `glueQuiet` and `itemGlueQuiet` read of a sign and what follows it: if it is a sign and the next token opens
--| an atom and is glued to it, the sign has no trailing comment and the token no own-line comments.
def quietOf (sign apart opens untrailed unled: Bool): Bool := !sign || apart || !opens || (untrailed && unled)

--| A sign and the item after it: if that item opens an atom and is glued to the sign, neither has a comment between
--| them. What `argumentPrefix` and `negativeNumeral` see (`Syntax.GlueQuietProofs.settledItemsQuiet`).
def itemGlueQuiet (sign next: Item): Bool :=
  quietOf sign.kind.signLike
    !next.glued
    next.kind.opensAtom
    sign.leaf.trivia.trailing.isNone
    next.leaf.trivia.leading.isEmpty

--| `itemGlueQuiet` of each item and the one after it.
def itemsQuiet: List Item → Bool
  | [] => True
  | [first, ..rest] => itemsQuietAfter first rest

def itemsQuietAfter (previous: Item) (rest: List Item): Bool := match rest with
  | [] => True
  | [next, ..more] => itemGlueQuiet previous next && itemsQuietAfter next more

theorem itemsQuietTail ∀ (first: Item) (rest: List Item)
    (quiet: itemsQuietAfter first rest = True):
    itemsQuiet rest = True :=
  match rest with
    | [] => byComputing
    | [next, ..more] => Bool.andRight quiet

theorem itemsQuietDrop ∀ (read rest: List Item) (quiet: itemsQuiet (read ++ rest) = True): itemsQuiet rest = True :=
  match read with
    | [] => quiet
    | [first, ..more] => itemsQuietDrop more rest (itemsQuietTail first (more ++ rest) quiet)

--| Every glued sign left is quiet.
def QuietItems: Parse.Invariant Item :=
  { holds = items => itemsQuiet items = True, kept = read rest h => itemsQuietDrop read rest h }

--| The invariant the parse runs under: every item left is good, and its glued signs are quiet.
def GoodItems: Parse.Invariant Item := Parse.Invariant.both (Parse.Invariant.every GoodItem) QuietItems

--| The head of what is left is good.
theorem goodHead ∀ [start: Parse.Mark Item] [item: Item] [later: List Item]
    (fine: Parse.Fits Item GoodItems start.rest)
    (shape: start.rest = [item, ..later]):
    GoodItem item :=
  let all: List.All GoodItem start.rest := fine.holds.left
  (rewrite shape at all then all).left

theorem goodFirst ∀ [item: Item] [later: List Item] (fine: Parse.Fits Item GoodItems [item, ..later]): GoodItem item :=
  fine.holds.left.left

--| The first two items left are a quiet pair.
theorem quietPair ∀ [start: Parse.Mark Item] [first second: Item] [later: List Item]
    (fine: Parse.Fits Item GoodItems start.rest)
    (shape: start.rest = [first, second, ..later]):
    itemGlueQuiet first second = True :=
  let quiet: itemsQuiet start.rest = True := fine.holds.right
  Bool.andLeft (rewrite shape at quiet then quiet)

--| What the parse runs under, from the items' facts.
theorem goodItemsOf ∀ (items: List Item)
    (good: List.All GoodItem items)
    (quiet: itemsQuiet items = True):
    Parse.Fits Item GoodItems items :=
  { holds = (good, quiet) }

--| `bump` reads the item that is next, and gives its word.
theorem readsAtBump ∀ [start: Parse.Mark Item] [item: Item] [later: List Item]
    (shape: start.rest = [item, ..later]):
    Parse.ReadsAt start (() => bump()) (read word => read = [item] ∧ word = item.leaf.word) :=
  Parse.readsAtThen
    (Parse.readsNext [inv := Parse.Invariant.any] (item => True) start { holds = Trivial })
    (read v after starts taken =>
      match v, taken with
        | Some found, (same, passes) =>
          let split: [found, ..after.rest] = [item, ..later] := rewrite <- shape, starts, same
          let isItem: found = item := List.consInjectiveHead split
          Parse.readsAtDone after found.leaf.word (Both (rewrite same, isItem) (rewrite isItem))
        | None, empty => Parse.readsFatal [inv := Parse.Invariant.any] after { holds = Trivial })

theorem symbolicWithin ∀ (kind: Tok) (symbolic: kind.symbolic1 = True): kind.within1 = True := match kind, symbolic with
  | Lower | Upper | Num | Float | KwDef, symbolic => (Bool.falseNotTrue symbolic).impossible
  | other, symbolic => symbolic

--| What an operator's text must be for a left-nested level: its table entries.
def TextAt (needs level: Nat) (text: Text): Prop :=
  leftNeeds InfixBinary text = needs ∧ infixLevel InfixBinary text = level

--| An operator link, read: the item that is next, if it is one `takes` accepts and good, with its operand, is a link.
theorem givesOperatorStep ∀ (modes: Modes) (takes: Tok → Bool) (operand: () → {Parse Item} Expr) (floor: Nat)
    (link: (Word, Expr) → Prop)
    (linkOf: ∀ (item: Item) (value: Expr) => GoodItem item
      → takes item.kind = True
      → Parsed floor value
      → link (item.leaf.word, value))
    (operandGives: Parse.Gives GoodItems operand (Parsed floor)):
    Parse.Gives GoodItems
      (() =>
        match modes.peek with
          | Some kind if takes kind =>
            let operator := bump()
            let value := operand()
            Some (operator, value)
          | _ => None)
      (Parse.Perhaps link) :=
  Parse.readsInMark _ _ (start fine =>
    match start with
      | { rest = [], offset, left } => Parse.readsAtDone _ None byComputing
      | { rest = [item, ..later], offset, left } =>
        match stopped: modes.stops item with
          | True => Parse.readsAtDone _ None byComputing
          | False =>
            match took: takes item.kind with
              | False => Parse.readsAtDone _ None byComputing
              | True => Parse.readsAtThen (readsAtBump byComputing) (read word after starts (Both single same) =>
                Parse.readsAtThen
                  (operandGives after (Parse.Fits.after fine starts))
                  (more value later2 starts2 parsed =>
                    Parse.readsAtDone later2
                      (Some (word, value))
                      (rewrite same then linkOf item value (goodFirst fine) took parsed))))

--| What an operator's text must be for a left-nested level: its table entries.
theorem leftLinkOf ∀ (takes: Tok → Bool) (level: Nat)
    (takesGood: ∀ (kind: Tok) (text: Text) => takes kind = True
      → kind.symbolic1 = True ∧ (Spells kind text → TextAt level level text))
    (item: Item) (value: Expr)
    (good: GoodItem item)
    (took: takes item.kind = True)
    (parsed: Parsed (level + 2) value):
    LeftLink level (item.leaf.word, value) :=
  let (symbolic, texts) := takesGood item.kind item.text took
  let within: item.kind.within1 = True := symbolicWithin item.kind symbolic
  let (needs, own) := texts (good within)
  Both (rewrite (operatorTokOfSpells item.kind item.text (good within) symbolic)) (Both needs (Both own parsed))

--| The operators of one level that nest to the left, each with its operand.
theorem givesOperatorLinks ∀ (modes: Modes) (takes: Tok → Bool) (operand: () → {Parse Item} Expr) (level: Nat)
    (takesGood: ∀ (kind: Tok) (text: Text) => takes kind = True
      → kind.symbolic1 = True ∧ (Spells kind text → TextAt level level text))
    (operandGives: Parse.Gives GoodItems operand (Parsed (level + 2))):
    Parse.Gives GoodItems (() => operatorLinks modes takes operand) (List.All (LeftLink level)) :=
  Parse.givesLoop
    (givesOperatorStep modes takes operand (level + 2) (LeftLink level) (leftLinkOf takes level takesGood) operandGives)

--| A first operand and the links after it, folded to the left.
theorem givesLeftChain ∀ (modes: Modes) (takes: Tok → Bool) (first operand: () → {Parse Item} Expr) (level: Nat)
    (takesGood: ∀ (kind: Tok) (text: Text) => takes kind = True
      → kind.symbolic1 = True ∧ (Spells kind text → TextAt level level text))
    (firstGives: Parse.Gives GoodItems first (Parsed level))
    (operandGives: Parse.Gives GoodItems operand (Parsed (level + 2))):
    Parse.Gives GoodItems (() => leftNested (first()) (operatorLinks modes takes operand)) (Parsed level) :=
  Parse.givesThen firstGives (head headParsed =>
    Parse.givesThen (givesOperatorLinks modes takes operand level takesGood operandGives) (links linksParsed =>
      Parse.givesDone (leftNestedParsed level head links headParsed linksParsed)))

theorem mulTakesGood ∀ (kind: Tok) (text: Text)
    (took: (kind == Star || kind == Slash || kind == Percent) = True):
    kind.symbolic1 = True ∧ (Spells kind text → TextAt 16 16 text) :=
  match kind, took with
    | Star | Slash | Percent, _ => (byComputing, same => Both (rewrite same) (rewrite same))
    | other, took => (Bool.falseNotTrue took).impossible

theorem addTakesGood ∀ (kind: Tok) (text: Text)
    (took: (kind == Plus || kind == Minus) = True):
    kind.symbolic1 = True ∧ (Spells kind text → TextAt 14 14 text) :=
  match kind, took with
    | Plus | Minus, _ => (byComputing, same => Both (rewrite same) (rewrite same))
    | other, took => (Bool.falseNotTrue took).impossible

--| `mul_expr`, from what `unary` gives.
theorem givesMulExpr ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (unaryGives: Parse.Gives GoodItems (() => unary self modes) (Parsed 18)):
    Parse.Gives GoodItems (() => mulExpr self modes) (Parsed 16) :=
  givesLeftChain modes
    (kind => kind == Star || kind == Slash || kind == Percent)
    (() => unary self modes)
    (() => unary self modes)
    16
    mulTakesGood
    (Parse.givesWeaken unaryGives (value parsed => parsedWeaken parsed byComputing))
    unaryGives

--| `add_expr`, from what `mul_expr` gives.
theorem givesAddExpr ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (mulGives: Parse.Gives GoodItems (() => mulExpr self modes) (Parsed 16)):
    Parse.Gives GoodItems (() => addExpr self modes) (Parsed 14) :=
  givesLeftChain modes
    (kind => kind == Plus || kind == Minus)
    (() => mulExpr self modes)
    (() => mulExpr self modes)
    14
    addTakesGood
    (Parse.givesWeaken mulGives (value parsed => parsedWeaken parsed byComputing))
    mulGives

theorem appendTakesGood ∀ (kind: Tok) (text: Text)
    (took: (kind == PlusPlus) = True):
    kind.symbolic1 = True ∧ (Spells kind text → leftNeeds InfixBinary text = 14 ∧ infixLevel InfixBinary text = 12) :=
  match kind, took with
    | PlusPlus, took => (byComputing, same => Both (rewrite same) (rewrite same))
    | other, took => (Bool.falseNotTrue took).impossible

theorem rightLinkOf ∀ (takes: Tok → Bool) (level: Nat)
    (takesGood: ∀ (kind: Tok) (text: Text) => takes kind = True
      → kind.symbolic1 = True
        ∧ (Spells kind text → leftNeeds InfixBinary text = level + 2 ∧ infixLevel InfixBinary text = level))
    (chosen: Item) (value: Expr)
    (good: GoodItem chosen)
    (took: takes chosen.kind = True)
    (parsed: Parsed (level + 2) value):
    RightLink level (chosen.leaf.word, value) :=
  let (symbolic, texts) := takesGood chosen.kind chosen.text took
  let within: chosen.kind.within1 = True := symbolicWithin chosen.kind symbolic
  let (needs, own) := texts (good within)
  Both (rewrite (operatorTokOfSpells chosen.kind chosen.text (good within) symbolic)) (Both needs (Both own parsed))

--| `append_expr`, from what `add_expr` gives: `++`s nest to the right.
--|
--| Proof idea: the links are read as `givesOperatorStep` reads any (an operator and its operand), then folded by
--| `rightNestedParsed`.
theorem givesAppendExpr ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (addGives: Parse.Gives GoodItems (() => addExpr self modes) (Parsed 14)):
    Parse.Gives GoodItems (() => appendExpr self modes) (Parsed 12) :=
  Parse.givesThen addGives (first firstParsed =>
    Parse.givesThen
      (Parse.givesLoop
        (givesOperatorStep modes
          (kind => kind == PlusPlus)
          (() => addExpr self modes)
          14
          (RightLink 12)
          (rightLinkOf (kind => kind == PlusPlus) 12 appendTakesGood)
          addGives))
      (links linksParsed => Parse.givesDone (rightNestedParsed 12 first links byComputing firstParsed linksParsed)))

-- Combinators for a parser that looks at the next item and reads it.

--| `bump` then `k` of its word, from a mark whose next item is `item`: `k` of that item's word is read from after it,
--| where every item left is still good.
theorem readsAtBumpThen ∀ [start: Parse.Mark Item] [item: Item] [later: List Item]
    [k: Word → {Parse Item} b] [holds: b → Prop]
    (shape: start.rest = [item, ..later])
    (fine: Parse.Fits Item GoodItems start.rest)
    (rest: ∀ (after: Parse.Mark Item) => Parse.Fits Item GoodItems after.rest
      → Parse.ReadsAt after (() => k item.leaf.word) (read value => holds value)):
    Parse.ReadsAt start (() => k (bump())) (read value => holds value) :=
  Parse.readsAtThen (readsAtBump shape) (read word after starts (Both single same) =>
    rewrite same then rest after (Parse.Fits.after fine starts))

--| A parser that looks at what `modes.peek` sees: `k` of it, read from every mark where the item left is `item`
--| (not stopping the parse) or `modes.peek` is `None`.
theorem readsInPeeked ∀ (modes: Modes) (k: Option Tok → {Parse Item} a) (spec: List Item → a → Prop)
    (nothing: ∀ (start: Parse.Mark Item) => Parse.Fits Item GoodItems start.rest
      → (start.rest = []
        ∨ ∃ (item: Item) => ∃ (later: List Item) => start.rest = [item, ..later] ∧ modes.stops item = True)
      → Parse.ReadsAt start (() => k None) spec)
    (something: ∀ (start: Parse.Mark Item) (item: Item) (later: List Item) => start.rest = [item, ..later]
      → Parse.Fits Item GoodItems start.rest
      → modes.stops item = False
      → Parse.ReadsAt start (() => k (Some item.kind)) spec):
    Parse.ReadsIn GoodItems (() => k modes.peek) spec :=
  Parse.readsInMark (here => k (peekIn modes 0 here.rest)) spec (start fine =>
    match start with
      | { rest = [], offset, left } => nothing { rest = [], offset, left } fine (Inl byComputing)
      | { rest = [item, ..later], offset, left } =>
        match stopped: modes.stops item with
          | True =>
            nothing
              { rest = [item, ..later], offset, left }
              fine
              (Inr (Witness item (Witness later (Both byComputing stopped))))
          | False => something { rest = [item, ..later], offset, left } item later byComputing fine stopped)

-- Look-aheads: parsers that only look, and read nothing.

--| A parser that reads nothing, from every mark where the items left are good.
def Reads0 (p: () → {Parse Item} a): Prop := Parse.Reads0 GoodItems p

theorem reads0Left: Reads0 (() => left()) := Parse.reads0Mark (here => here.rest)

theorem reads0Peek ∀ (modes: Modes): Reads0 (() => modes.peek) := Parse.reads0Mark (here => peekIn modes 0 here.rest)

theorem reads0PeekAt ∀ (modes: Modes) (ahead: Nat): Reads0 (() => modes.peekAt ahead) :=
  Parse.reads0Mark (here => peekIn modes ahead here.rest)

theorem reads0At ∀ (modes: Modes) (wanted: Tok): Reads0 (() => modes.at wanted) :=
  Parse.reads0Then (reads0Peek modes) (found => Parse.reads0Done _)

theorem reads0BareCases ∀ (modes: Modes): Reads0 (() => bareCases modes) :=
  Parse.reads0Then reads0Left (items => Parse.reads0Done (bareCasesOn modes items))

theorem reads0StartsAtom ∀ (modes: Modes): Reads0 (() => startsAtom modes) :=
  Parse.reads0Then reads0Left (items => Parse.reads0Done (startsAtomOn modes items))

-- Atoms and what follows them.

--| An expression outside slice 1 satisfies every in-slice spec.
theorem inSliceOutside ∀ (holds: Expr → Prop) (expr: Expr) (outside: expr.within1 = False): InSlice holds expr :=
  within => (Bool.falseNotTrue (rewrite outside at within)).impossible

theorem parsedOutside ∀ (floor: Nat) (expr: Expr) (outside: expr.within1 = False): Parsed floor expr :=
  inSliceOutside (expr => floor <= expr.level) expr outside

@[walk]
theorem givesBump: Parse.Gives GoodItems (() => bump()) (word => True) :=
  Parse.givesThen
    [first := found => True]
    (Parse.readsWeaken (Parse.readsNext (item => True)) (read found facts => byComputing))
    (found done =>
      match found with
        | Some item => Parse.givesDone byComputing
        | None => Parse.readsFatal)

@[walk]
theorem givesLeft: Parse.Gives GoodItems (() => left()) (found => True) :=
  Parse.readsInMark (here => here.rest) _ (start fine => Parse.readsAtDone _ start.rest byComputing)

theorem givesSuffixCalled ∀ (holds: Expr → Prop) (outside: ∀ (expr: Expr) => expr.grammar1 = False → holds expr)
    (target: Expr) (callable paren: Bool) (parsed: holds target):
    Parse.Gives GoodItems (() => suffixCalled target callable paren) (holds) :=
  Parse.givesThen givesLeft (seen found =>
    match unitCall seen with
      | False => Parse.givesDone parsed
      | True =>
        match callable || (paren && callableParen target) with
          | False => Parse.givesDone parsed
          | True => Parse.givesThen givesBump (open _ =>
            Parse.givesThen givesBump (close _ =>
              Parse.givesDone (outside (App target [Unit open close]) (Bool.andFalse target.grammar1)))))

--| `suffixes` after the call: a field access starts another round on a tree outside the slice, and nothing else changes
--| the tree.
theorem givesSuffixesOn ∀ (holds: Expr → Prop) (outside: ∀ (expr: Expr) => expr.grammar1 = False → holds expr)
    (more: Nat) (modes: Modes) (called: Expr) (paren: Bool) (items: List Item) (parsed: holds called)
    (next: ∀ (target: Expr) (callable: Bool) => holds target
      → Parse.Gives GoodItems (() => suffixes more modes target callable paren) (holds)):
    Parse.Gives GoodItems (() => suffixesOn more modes called paren items) (holds) :=
  match items with
    | [dot, field, ..later] =>
      match dot.kind == Dot && !modes.stops dot && !sectionAt [dot, field, ..later] with
        | False => Parse.givesDone parsed
        | True =>
          match !((field.kind == Lower || field.kind == Upper) && !isQualified field && !modes.stops field) with
            | True => Parse.readsFatal
            | False =>
              match !dot.glued || !field.glued with
                | True => Parse.readsFatal
                | False => Parse.givesThen givesBump (dotLeaf _ =>
                  Parse.givesThen givesBump (name _ =>
                    next (FieldAccess (Some called) dotLeaf name) True (outside _ byComputing)))
    | [dot] =>
      match dot.kind == Dot && !modes.stops dot with
        | True => Parse.readsFatal
        | False => Parse.givesDone parsed
    | other => Parse.givesDone parsed

--| `suffixes` keeps a parsed tree: a call or a field access makes one outside the slice.
--|
--| Proof idea: by induction on the fuel; each round is `suffixCalled`, then `suffixesOn` with the round after it.
theorem givesSuffixes ∀ (holds: Expr → Prop) (outside: ∀ (expr: Expr) => expr.grammar1 = False → holds expr) (fuel: Nat)
    (modes: Modes) (target: Expr) (callable paren: Bool) (parsed: holds target):
    Parse.Gives GoodItems (() => suffixes fuel modes target callable paren) (holds) :=
  match fuel with
    | Zero => Parse.givesDone parsed
    | Succ more =>
      Parse.givesThen (givesSuffixCalled holds outside target callable paren parsed) (called calledParsed =>
        Parse.givesThen givesLeft (seen _ =>
          givesSuffixesOn holds outside more modes called paren seen calledParsed (later again againParsed =>
            givesSuffixes holds outside more modes later again paren againParsed)))

@[walk]
theorem givesAt ∀ (modes: Modes) (wanted: Tok): Parse.Gives GoodItems (() => modes.at wanted) (found => True) :=
  Parse.readsInMark (here => isSome wanted (peekIn modes 0 here.rest)) _ (start fine =>
    Parse.readsAtDone _ _ byComputing)

@[walk]
theorem givesPeek ∀ (modes: Modes): Parse.Gives GoodItems (() => modes.peek) (found => True) :=
  Parse.readsInMark (here => peekIn modes 0 here.rest) _ (start fine => Parse.readsAtDone _ _ byComputing)

theorem givesAtomRecord ∀ (holds: Expr → Prop) (outside: ∀ (expr: Expr) => expr.grammar1 = False → holds expr)
    (self: Goal → {Parse Item} Expr) (modes: Modes) (head upper: Bool) (base: Expr)
    (callable: Bool) (parsed: holds base)
    (recordGives: Parse.Gives GoodItems (() => recordExpr self modes) (fields => True)):
    Parse.Gives GoodItems (() => atomRecord self modes head upper base callable) (pair => holds pair.fst) :=
  match upper with
    | False => Parse.givesDone parsed
    | True =>
      match head with
        | False => Parse.givesDone parsed
        | True => Parse.givesThen (givesAt modes LBrace) (found _ =>
          match found with
            | True =>
              Parse.givesThen recordGives (fields _ => Parse.givesDone (outside (CtorFields base fields) byComputing))
            | False => Parse.givesDone parsed)

theorem givesAtomAfter ∀ (holds: Expr → Prop) (outside: ∀ (expr: Expr) => expr.grammar1 = False → holds expr)
    (self: Goal → {Parse Item} Expr) (modes: Modes) (head: Bool) (first: Option Tok) (base: Expr) (parsed: holds base)
    (recordGives: Parse.Gives GoodItems (() => recordExpr self modes) (fields => True)):
    Parse.Gives GoodItems (() => atomAfter self modes head first base) (holds) :=
  Parse.givesThen
    (givesAtomRecord holds outside self modes head
      (isSome Upper first)
      base
      (isSome Lower first || isSome Upper first || isSome Dot first)
      parsed
      recordGives)
    (pair pairParsed =>
      match pair with
        | (based, callable) => Parse.givesThen Parse.givesMark (here _ =>
          Parse.givesThen
            (givesSuffixes holds outside (here.left + 1) modes based callable (isSome LParen first) pairParsed)
            (result resultParsed =>
              match isSome Dot first && !head with
                | True => Parse.givesDone (outside (Section result) byComputing)
                | False => Parse.givesDone resultParsed)))

--| `atom`, from what `atom_base` and a record's fields give.
theorem givesAtom ∀ (holds: Expr → Prop) (outside: ∀ (expr: Expr) => expr.grammar1 = False → holds expr)
    (self: Goal → {Parse Item} Expr) (modes: Modes) (head: Bool)
    (baseGives: Parse.Gives GoodItems (() => atomBase self modes) (holds))
    (recordGives: Parse.Gives GoodItems (() => recordExpr self modes) (fields => True)):
    Parse.Gives GoodItems (() => atom self modes head) (holds) :=
  Parse.givesThen (givesPeek modes) (first _ =>
    Parse.givesThen baseGives (base baseParsed =>
      givesAtomAfter holds outside self modes head first base baseParsed recordGives))

-- Reading a token that must be there.

theorem givesUnexpected ∀ (modes: Modes) (what: Text):
    Parse.Gives GoodItems (() => modes.unexpected what) (message => True) :=
  Parse.givesThen givesLeft (seen _ => Parse.givesDone byComputing)

--| A parse that fails gives anything.
@[walk]
theorem givesFail ∀ (modes: Modes) (what: Text) [holds: a → Prop]:
    Parse.Gives GoodItems (() => modes.fail what) holds :=
  Parse.givesThen (givesUnexpected modes what) (message _ => Parse.readsFatal)

@[walk]
theorem givesFatal ∀ [a: Type] (message: Text) [holds: a → Prop]:
    Parse.Gives GoodItems (() => Syntax.fatal message) holds :=
  Parse.readsFatal

--| `expect` gives the word of a token of the kind it was asked for.
theorem givesExpect ∀ (modes: Modes) (wanted: Tok) (what: Text)
    (within: wanted.within1 = True):
    Parse.Gives GoodItems (() => modes.expect wanted what) (word => Spells wanted word.text) :=
  readsInPeeked modes
    (seen => modes.expectOn wanted what seen) _
    (start fine stops => givesFail modes what start fine)
    (start item later shape fine stopped =>
      match took: isSome wanted (Some item.kind) with
        | False => givesFail modes what start fine
        | True => Parse.readsAtWeaken (readsAtBump shape) (read word (single, same) =>
          rewrite same then
            (rewrite <- DecEq.sound took then
              goodFirst (rewrite shape at fine) (rewrite DecEq.sound took then within))))

-- Facts the pure look-aheads give.

--| A negative numeral is a `-` and a number or float.
theorem negativeNumeralKinds ∀ (items: List Item)
    (found: negativeNumeral items = True):
    ∃ (minus number: Item) (later: List Item) => items = [minus, number, ..later]
      ∧ minus.kind = Minus
      ∧ (number.kind = Num ∨ number.kind = Float) :=
  match items, found with
    | [minus, number, ..later], found =>
      match isMinus: minus.kind, found with
        | Minus, found =>
          match isNumber: number.kind, found with
            | Num, found =>
              Witness minus (Witness number (Witness later (Both byComputing (Both isMinus (Inl isNumber)))))
            | Float, found =>
              Witness minus (Witness number (Witness later (Both byComputing (Both isMinus (Inr isNumber)))))
            | other, found => (Bool.falseNotTrue found).impossible
        | other, found => (Bool.falseNotTrue found).impossible
    | [] | [_], found => (Bool.falseNotTrue found).impossible

--| A negative numeral's number is glued to its `-`.
theorem negativeNumeralGlued ∀ (items: List Item)
    (found: negativeNumeral items = True)
    (minus number: Item) (later: List Item)
    (split: items = [minus, number, ..later]):
    number.glued = True :=
  let pair: negativeNumeral [minus, number, ..later] = True := rewrite <- split then found
  Bool.andLeft (Bool.andRight (Bool.andRight pair))

--| The item an argument's sign negates is glued to it.
theorem argumentPrefixGlued ∀ (items: List Item)
    (found: argumentPrefix items = True)
    (sign next: Item) (later: List Item)
    (split: items = [sign, next, ..later]):
    next.glued = True :=
  let pair: argumentPrefix [sign, next, ..later] = True := rewrite <- split then found
  Bool.andLeft (Bool.andRight (Bool.andRight (Bool.andRight pair)))

--| A `-` or `!` that negates an argument is followed by an item that opens an atom.
theorem argumentPrefixOpens ∀ (items: List Item)
    (found: argumentPrefix items = True):
    ∃ (sign next: Item) (later: List Item) => items = [sign, next, ..later]
      ∧ (sign.kind = Minus ∨ sign.kind = Bang)
      ∧ next.kind.opensAtom = True :=
  match items, found with
    | [sign, next, ..later], found =>
      match isMinus: sign.kind, found with
        | Minus, found =>
          let (signs, operand, spaced, glued, opens) := found
          Witness sign (Witness next (Witness later (Both byComputing (Both (Inl isMinus) opens))))
        | Bang, found =>
          let (signs, operand, spaced, glued, opens) := found
          Witness sign (Witness next (Witness later (Both byComputing (Both (Inr isMinus) opens))))
        | other, found => (Bool.falseNotTrue found).impossible
    | [] | [_], found => (Bool.falseNotTrue found).impossible
