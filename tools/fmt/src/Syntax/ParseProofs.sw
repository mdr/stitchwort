--| What the parser guarantees of the trees it gives in slice 1 of the proved formatter (docs/proposals/
--| self-hosted-fmt-s1-sketch.md, ticket 16a): `Shaped1` and `Lexical1` of the expression layer, proved one parser
--| function at a time with std's `Parse.Gives` lemmas.

namespace Syntax.ParseProofs
import Std (Bool, Eq, List, Nat, Option, Parse, Text)
import Syntax (..)
import Fmt (..)
import Syntax.Proofs (..)

--| What a parser function gives, when it gives a tree of slice 1: it is shaped, lexical, and at least at the level
--| `floor` of the precedence ladder. A tree outside the slice says nothing, so the constructs of later slices (a
--| `match`, a lambda, a section) need no case of their own.
def Parsed1 (floor: Nat) (expr: Expr): Prop :=
  expr.within1 = True → expr.shaped1 = True ∧ expr.lexical1 = True ∧ floor <= expr.level

theorem parsedWeaken ∀ [floor lower: Nat] [expr: Expr]
    (parsed: Parsed1 floor expr)
    (below: lower <= floor):
    Parsed1 lower expr :=
  within =>
    let (shaped, lexical, high) := parsed within
    (shaped, lexical, arithmetic [high, below])

--| A binary operator's tree is parsed when its operands are, at levels the operator's table allows.
theorem infixParsed ∀ (left right: Expr) (operator: Word) (leftFloor rightFloor: Nat)
    (leftParsed: Parsed1 leftFloor left)
    (rightParsed: Parsed1 rightFloor right)
    (spelled: (operatorTok operator.text).isSome = True)
    (needs: leftNeeds InfixBinary operator.text <= leftFloor)
    (allows: infixLevel InfixBinary operator.text <= rightFloor):
    Parsed1 (infixLevel InfixBinary operator.text) (Infix InfixBinary left operator right) :=
  within =>
    let (leftWithin, rightWithin) := within
    let (leftShaped, leftLexical, leftHigh) := leftParsed leftWithin
    let (rightShaped, rightLexical, rightHigh) := rightParsed rightWithin
    let needed: leftNeeds InfixBinary operator.text <= left.level := arithmetic [needs, leftHigh]
    let allowed: infixLevel InfixBinary operator.text <= right.level := arithmetic [allows, rightHigh]
    let own: infixLevel InfixBinary operator.text <= infixLevel InfixBinary operator.text := arithmetic
    (Both leftShaped (Both rightShaped (Both needed allowed)), Both leftLexical (Both spelled rightLexical), own)

--| `infixParsed` at the operator's own level.
theorem infixParsedAt ∀ (left right: Expr) (operator: Word) (level leftFloor rightFloor: Nat)
    (leftParsed: Parsed1 leftFloor left)
    (rightParsed: Parsed1 rightFloor right)
    (spelled: (operatorTok operator.text).isSome = True)
    (needs: leftNeeds InfixBinary operator.text <= leftFloor)
    (allows: infixLevel InfixBinary operator.text <= rightFloor)
    (own: infixLevel InfixBinary operator.text = level):
    Parsed1 level (Infix InfixBinary left operator right) :=
  rewrite <- own then infixParsed left right operator leftFloor rightFloor leftParsed rightParsed spelled needs allows

--| An operator at `level` that nests to the left, with its operand: `leftNested`'s links.
def LeftLink (level: Nat) (link: (Word, Expr)): Prop :=
  (operatorTok link.fst.text).isSome = True
    ∧ leftNeeds InfixBinary link.fst.text = level
    ∧ infixLevel InfixBinary link.fst.text = level
    ∧ Parsed1 level link.snd

--| Folding links to the left keeps a tree parsed, at the links' level.
--|
--| Proof idea: by induction on the links; each link adds one `Infix` whose left operand is the tree so far, which is at
--| the level the operator needs.
theorem leftNestedParsed ∀ (level: Nat) (first: Expr) (links: List (Word, Expr))
    (firstParsed: Parsed1 level first)
    (linksParsed: List.All (LeftLink level) links):
    Parsed1 level (leftNested first links) :=
  match links, linksParsed with
    | [], _ => firstParsed
    | [(operator, next), ..rest], (Both spelled (Both needs (Both own nextParsed)), restParsed) =>
      leftNestedParsed level
        (Infix InfixBinary first operator next)
        rest
        (infixParsedAt first next operator level level level firstParsed nextParsed spelled
          (arithmetic [needs])
          (arithmetic [own])
          own)
        restParsed

--| An operator at `level` that nests to the right, with its operand: `rightNested`'s links.
def RightLink (level: Nat) (link: (Word, Expr)): Prop :=
  (operatorTok link.fst.text).isSome = True
    ∧ leftNeeds InfixBinary link.fst.text = level + 2
    ∧ infixLevel InfixBinary link.fst.text = level
    ∧ Parsed1 (level + 2) link.snd

--| Folding links to the right keeps a tree parsed: its operands are at the next level up, the nested rest at this one.
theorem rightNestedParsed ∀ (level: Nat) (first: Expr) (links: List (Word, Expr))
    (firstParsed: Parsed1 (level + 2) first)
    (linksParsed: List.All (RightLink level) links):
    Parsed1 level (rightNested first links) :=
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
        (rightNestedParsed level next rest nextParsed restParsed)
        spelled
        (arithmetic [needs])
        (arithmetic [own])
        own

-- The items.

--| What the lexer's theorems say of an item of slice 1's alphabet: its text is one the kind is spelled with.
def GoodItem (item: Item): Prop := item.kind.within1 = True → Spells item.kind item.text

--| The invariant the parse runs under: every item left is good.
def GoodItems: Parse.Invariant Item := Parse.Invariant.every GoodItem

--| The head of what is left is good.
theorem goodHead ∀ [start: Parse.Mark Item] [item: Item] [later: List Item]
    (fine: Parse.Fits Item GoodItems start.rest)
    (shape: start.rest = [item, ..later]):
    GoodItem item :=
  let all: List.All GoodItem start.rest := fine.holds
  (rewrite shape at all then all).left

theorem goodFirst ∀ [item: Item] [later: List Item] (fine: Parse.Fits Item GoodItems [item, ..later]): GoodItem item :=
  fine.holds.left

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
          let isItem: found = item := List.consInjectiveHead found item after.rest later split
          Parse.readsAtDone after found.leaf.word _ (Both (rewrite same, isItem) (rewrite isItem))
        | None, empty =>
          Parse.readsFatal [inv := Parse.Invariant.any] "the parser read past the end of its input" _ after {
            holds = Trivial
          })

theorem symbolicWithin ∀ (kind: Tok) (symbolic: kind.symbolic1 = True): kind.within1 = True := match kind, symbolic with
  | Lower, symbolic => (Bool.falseNotTrue symbolic).impossible
  | Upper, symbolic => (Bool.falseNotTrue symbolic).impossible
  | Num, symbolic => (Bool.falseNotTrue symbolic).impossible
  | Float, symbolic => (Bool.falseNotTrue symbolic).impossible
  | KwDef, symbolic => (Bool.falseNotTrue symbolic).impossible
  | other, symbolic => symbolic

--| What an operator's text must be for a left-nested level: its table entries.
def TextAt (needs level: Nat) (text: Text): Prop :=
  leftNeeds InfixBinary text = needs ∧ infixLevel InfixBinary text = level

--| An operator link, read: the item that is next, if it is one `takes` accepts and good, with its operand, is a link.
theorem givesOperatorStep ∀ (modes: Modes) (takes: Tok → Bool) (operand: () → {Parse Item} Expr) (floor: Nat)
    (link: (Word, Expr) → Prop)
    (linkOf: ∀ (item: Item) (value: Expr) => GoodItem item
      → takes item.kind = True
      → Parsed1 floor value
      → link (item.leaf.word, value))
    (operandGives: Parse.Gives GoodItems operand (Parsed1 floor)):
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
      | { rest = [], offset, left } => Parse.readsAtDone _ None _ byComputing
      | { rest = [item, ..later], offset, left } =>
        match stopped: modes.stops item with
          | True => Parse.readsAtDone _ None _ byComputing
          | False =>
            match took: takes item.kind with
              | False => Parse.readsAtDone _ None _ byComputing
              | True =>
                Parse.readsAtThen
                  (readsAtBump
                    [start := { rest = [item, ..later], offset, left }]
                    [item := item]
                    [later := later]
                    byComputing)
                  (read word after starts (Both single same) =>
                    Parse.readsAtThen
                      (operandGives after (Parse.Fits.after fine starts))
                      (more value later2 starts2 parsed =>
                        Parse.readsAtDone later2
                          (Some (word, value)) _
                          (rewrite same then linkOf item value (goodFirst fine) took parsed))))

--| What an operator's text must be for a left-nested level: its table entries.
theorem leftLinkOf ∀ (takes: Tok → Bool) (level: Nat)
    (takesGood: ∀ (kind: Tok) (text: Text) => takes kind = True
      → kind.symbolic1 = True ∧ (Spells kind text → TextAt level level text))
    (item: Item) (value: Expr)
    (good: GoodItem item)
    (took: takes item.kind = True)
    (parsed: Parsed1 level value):
    LeftLink level (item.leaf.word, value) :=
  let (symbolic, texts) := takesGood item.kind item.text took
  let within: item.kind.within1 = True := symbolicWithin item.kind symbolic
  let (needs, own) := texts (good within)
  Both (rewrite (operatorTokOfSpells item.kind item.text (good within) symbolic)) (Both needs (Both own parsed))

--| The operators of one level that nest to the left, each with its operand.
theorem givesOperatorLinks ∀ (modes: Modes) (takes: Tok → Bool) (operand: () → {Parse Item} Expr) (level: Nat)
    (takesGood: ∀ (kind: Tok) (text: Text) => takes kind = True
      → kind.symbolic1 = True ∧ (Spells kind text → TextAt level level text))
    (operandGives: Parse.Gives GoodItems operand (Parsed1 level)):
    Parse.Gives GoodItems (() => operatorLinks modes takes operand) (List.All (LeftLink level)) :=
  Parse.givesLoop
    (givesOperatorStep modes takes operand level (LeftLink level) (leftLinkOf takes level takesGood) operandGives)

--| A first operand and the links after it, folded to the left.
theorem givesLeftChain ∀ (modes: Modes) (takes: Tok → Bool) (first operand: () → {Parse Item} Expr) (level: Nat)
    (takesGood: ∀ (kind: Tok) (text: Text) => takes kind = True
      → kind.symbolic1 = True ∧ (Spells kind text → TextAt level level text))
    (firstGives: Parse.Gives GoodItems first (Parsed1 level))
    (operandGives: Parse.Gives GoodItems operand (Parsed1 level)):
    Parse.Gives GoodItems (() => leftNested (first()) (operatorLinks modes takes operand)) (Parsed1 level) :=
  Parse.givesThen firstGives (head headParsed =>
    Parse.givesThen (givesOperatorLinks modes takes operand level takesGood operandGives) (links linksParsed =>
      Parse.givesDone (leftNestedParsed level head links headParsed linksParsed)))

theorem mulTakesGood ∀ (kind: Tok) (text: Text)
    (took: (kind == Star || kind == Slash || kind == Percent) = True):
    kind.symbolic1 = True ∧ (Spells kind text → TextAt 16 16 text) :=
  match kind, took with
    | Star, took => (byComputing, same => Both (rewrite same) (rewrite same))
    | Slash, took => (byComputing, same => Both (rewrite same) (rewrite same))
    | Percent, took => (byComputing, same => Both (rewrite same) (rewrite same))
    | other, took => (Bool.falseNotTrue took).impossible

theorem addTakesGood ∀ (kind: Tok) (text: Text)
    (took: (kind == Plus || kind == Minus) = True):
    kind.symbolic1 = True ∧ (Spells kind text → TextAt 14 14 text) :=
  match kind, took with
    | Plus, took => (byComputing, same => Both (rewrite same) (rewrite same))
    | Minus, took => (byComputing, same => Both (rewrite same) (rewrite same))
    | other, took => (Bool.falseNotTrue took).impossible

--| `mul_expr`, from what `unary` gives.
theorem givesMulExpr ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (unaryGives: Parse.Gives GoodItems (() => unary self modes) (Parsed1 16)):
    Parse.Gives GoodItems (() => mulExpr self modes) (Parsed1 16) :=
  givesLeftChain modes
    (kind => kind == Star || kind == Slash || kind == Percent)
    (() => unary self modes)
    (() => unary self modes)
    16
    mulTakesGood
    unaryGives
    unaryGives

--| `add_expr`, from what `mul_expr` gives.
theorem givesAddExpr ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (mulGives: Parse.Gives GoodItems (() => mulExpr self modes) (Parsed1 14)):
    Parse.Gives GoodItems (() => addExpr self modes) (Parsed1 14) :=
  givesLeftChain modes
    (kind => kind == Plus || kind == Minus)
    (() => mulExpr self modes)
    (() => mulExpr self modes)
    14
    addTakesGood
    mulGives
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
    (parsed: Parsed1 (level + 2) value):
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
    (addGives: Parse.Gives GoodItems (() => addExpr self modes) (Parsed1 14)):
    Parse.Gives GoodItems (() => appendExpr self modes) (Parsed1 12) :=
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
      (links linksParsed => Parse.givesDone (rightNestedParsed 12 first links firstParsed linksParsed)))
