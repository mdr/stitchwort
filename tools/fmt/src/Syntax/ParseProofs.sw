--| What the parser guarantees of the trees it gives in slice 1 of the proved formatter (docs/proposals/
--| self-hosted-fmt-s1-sketch.md, ticket 16a): `Shaped1` and `Lexical1` of the expression layer, proved one parser
--| function at a time with std's `Parse.Gives` lemmas.

namespace Syntax.ParseProofs
import Std (Bool, DecEq, Eq, List, Nat, Option, Parse, Text)
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
def Reads0 (p: () → {Parse Item} a): Prop :=
  ∀ (start: Parse.Mark Item) => Parse.Fits Item GoodItems start.rest → Parse.ReadsAt start p (read value => read = [])

theorem reads0Done ∀ (x: a): Reads0 (() => x) := start fine => Parse.readsAtDone start x _ byComputing

--| What a mark shows, read by a pure function: nothing is read.
theorem reads0Mark ∀ (f: Parse.Mark Item → a): Reads0 (() => f (Parse.mark())) := start fine =>
  Parse.readsInMark (here => f here) _ (here fine1 => Parse.readsAtDone _ (f here) _ byComputing) start fine

theorem reads0Then ∀ [p: () → {Parse Item} a] [j: a → {Parse Item} b]
    (first: Reads0 p)
    (rest: ∀ (value: a) => Reads0 (() => j value)):
    Reads0 (() => j (p())) :=
  start fine =>
    Parse.readsAtThen (first start fine) (read value after starts empty =>
      Parse.readsAtWeaken (rest value after (Parse.Fits.after fine starts)) (taken result nothing =>
        rewrite empty then nothing))

theorem reads0Left: Reads0 (() => left()) := reads0Mark (here => here.rest)

theorem reads0If ∀ (c: Bool) [yes no: () → {Parse Item} a]
    (whenYes: Reads0 yes)
    (whenNo: Reads0 no):
    Reads0 (() => if c then yes() else no()) :=
  match c with
    | True => whenYes
    | False => whenNo

theorem reads0Peek ∀ (modes: Modes): Reads0 (() => modes.peek) := reads0Mark (here => peekIn modes 0 here.rest)

theorem reads0PeekAt ∀ (modes: Modes) (ahead: Nat): Reads0 (() => modes.peekAt ahead) :=
  reads0Mark (here => peekIn modes ahead here.rest)

theorem reads0At ∀ (modes: Modes) (wanted: Tok): Reads0 (() => modes.at wanted) :=
  reads0Then (reads0Peek modes) (found => reads0Done _)

theorem reads0BareCases ∀ (modes: Modes): Reads0 (() => bareCases modes) := reads0Then (reads0PeekAt modes 1) (found =>
  match found with
    | Some KwThen => reads0Done False
    | Some KwIn => reads0Done False
    | other => reads0Done True)

theorem reads0StartsAtom ∀ (modes: Modes): Reads0 (() => startsAtom modes) := reads0Then (reads0Peek modes) (found =>
  match found with
    | Some kind =>
      match opensArgument kind with
        | True => reads0Done True
        | False =>
          reads0Then
            (reads0If (kind == Dot) (reads0Then reads0Left (items => reads0Done (sectionAt items))) (reads0Done False))
            (dotSection =>
              match dotSection with
                | True => reads0Done True
                | False => reads0Then (reads0If (kind == KwCases) (reads0BareCases modes) (reads0Done False)) (bare =>
                  match bare with
                    | True => reads0Done True
                    | False => reads0Then reads0Left (items => reads0Done (argumentPrefix items))))
    | None => reads0Done False)

-- Atoms and what follows them.

--| An expression outside slice 1 is parsed at every floor.
theorem parsedOutside ∀ (floor: Nat) (expr: Expr) (outside: expr.within1 = False): Parsed1 floor expr := within =>
  (Bool.falseNotTrue (rewrite outside at within)).impossible

theorem givesBump: Parse.Gives GoodItems (() => bump()) (word => True) :=
  Parse.givesThen
    [first := found => True]
    (Parse.readsWeaken (Parse.readsNext (item => True)) (read found facts => byComputing))
    (found done =>
      match found with
        | Some item => Parse.givesDone byComputing
        | None => Parse.readsFatal "the parser read past the end of its input" _)

theorem givesLeft: Parse.Gives GoodItems (() => left()) (found => True) :=
  Parse.readsInMark (here => here.rest) _ (start fine => Parse.readsAtDone _ start.rest _ byComputing)

theorem givesSuffixCalled ∀ (floor: Nat) (target: Expr) (callable paren: Bool)
    (parsed: Parsed1 floor target):
    Parse.Gives GoodItems (() => suffixCalled target callable paren) (Parsed1 floor) :=
  Parse.givesThen givesLeft (seen found =>
    match unitCall seen with
      | False => Parse.givesDone parsed
      | True =>
        match callable || (paren && callableParen target) with
          | False => Parse.givesDone parsed
          | True => Parse.givesThen givesBump (open _ =>
            Parse.givesThen givesBump (close _ =>
              Parse.givesDone (parsedOutside floor (App target [Unit open close]) (Bool.andFalse target.within1)))))

--| `suffixes` after the call: a field access starts another round on a tree outside the slice, and nothing else changes
--| the tree.
theorem givesSuffixesOn ∀ (floor more: Nat) (modes: Modes) (called: Expr) (paren: Bool) (items: List Item)
    (parsed: Parsed1 floor called)
    (next: ∀ (target: Expr) (callable: Bool) => Parsed1 floor target
      → Parse.Gives GoodItems (() => suffixes more modes target callable paren) (Parsed1 floor)):
    Parse.Gives GoodItems (() => suffixesOn more modes called paren items) (Parsed1 floor) :=
  match items with
    | [dot, field, ..later] =>
      match dot.kind == Dot && !modes.stops dot && !sectionAt [dot, field, ..later] with
        | False => Parse.givesDone parsed
        | True =>
          match !((field.kind == Lower || field.kind == Upper) && !isQualified field && !modes.stops field) with
            | True => Parse.readsFatal _ _
            | False =>
              match !dot.glued || !field.glued with
                | True => Parse.readsFatal _ _
                | False => Parse.givesThen givesBump (dotLeaf _ =>
                  Parse.givesThen givesBump (name _ =>
                    next (FieldAccess (Some called) dotLeaf name) True (parsedOutside floor _ byComputing)))
    | [dot] =>
      match dot.kind == Dot && !modes.stops dot with
        | True => Parse.readsFatal _ _
        | False => Parse.givesDone parsed
    | other => Parse.givesDone parsed

--| `suffixes` keeps a parsed tree: a call or a field access makes one outside the slice.
--|
--| Proof idea: by induction on the fuel; each round is `suffixCalled`, then `suffixesOn` with the round after it.
theorem givesSuffixes ∀ (floor fuel: Nat) (modes: Modes) (target: Expr) (callable paren: Bool)
    (parsed: Parsed1 floor target):
    Parse.Gives GoodItems (() => suffixes fuel modes target callable paren) (Parsed1 floor) :=
  match fuel with
    | Zero => Parse.givesDone parsed
    | Succ more => Parse.givesThen (givesSuffixCalled floor target callable paren parsed) (called calledParsed =>
      Parse.givesThen givesLeft (seen _ =>
        givesSuffixesOn floor more modes called paren seen calledParsed (later again againParsed =>
          givesSuffixes floor more modes later again paren againParsed)))

theorem givesAt ∀ (modes: Modes) (wanted: Tok): Parse.Gives GoodItems (() => modes.at wanted) (found => True) :=
  Parse.readsInMark (here => isSome wanted (peekIn modes 0 here.rest)) _ (start fine =>
    Parse.readsAtDone _ _ _ byComputing)

theorem givesPeek ∀ (modes: Modes): Parse.Gives GoodItems (() => modes.peek) (found => True) :=
  Parse.readsInMark (here => peekIn modes 0 here.rest) _ (start fine => Parse.readsAtDone _ _ _ byComputing)

theorem givesAtomRecord ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (head upper: Bool)
    (base: Expr) (callable: Bool)
    (parsed: Parsed1 18 base)
    (recordGives: Parse.Gives GoodItems (() => recordExpr self modes) (fields => True)):
    Parse.Gives GoodItems (() => atomRecord self modes head upper base callable) (pair => Parsed1 18 pair.fst) :=
  match upper with
    | False => Parse.givesDone parsed
    | True =>
      match head with
        | False => Parse.givesDone parsed
        | True => Parse.givesThen (givesAt modes LBrace) (found _ =>
          match found with
            | True =>
              Parse.givesThen
                [p := () => recordExpr self modes]
                [j := fields => (CtorFields base fields, False)]
                recordGives
                (fields _ =>
                  Parse.givesDone
                    [x := (CtorFields base fields, False)]
                    [holds := pair => Parsed1 18 pair.fst]
                    (parsedOutside 18 (CtorFields base fields) byComputing))
            | False => Parse.givesDone parsed)

theorem givesAtomAfter ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (head: Bool) (first: Option Tok) (base: Expr)
    (parsed: Parsed1 18 base)
    (recordGives: Parse.Gives GoodItems (() => recordExpr self modes) (fields => True)):
    Parse.Gives GoodItems (() => atomAfter self modes head first base) (Parsed1 18) :=
  Parse.givesThen
    (givesAtomRecord self modes head
      (isSome Upper first)
      base
      (isSome Lower first || isSome Upper first || isSome Dot first)
      parsed
      recordGives)
    (pair pairParsed =>
      match pair with
        | (based, callable) => Parse.givesThen Parse.givesMark (here _ =>
          Parse.givesThen
            (givesSuffixes 18 (here.left + 1) modes based callable (isSome LParen first) pairParsed)
            (result resultParsed =>
              match isSome Dot first && !head with
                | True => Parse.givesDone (parsedOutside 18 (Section result) byComputing)
                | False => Parse.givesDone resultParsed)))

--| `atom`, from what `atom_base` and a record's fields give.
theorem givesAtom ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (head: Bool)
    (baseGives: Parse.Gives GoodItems (() => atomBase self modes) (Parsed1 18))
    (recordGives: Parse.Gives GoodItems (() => recordExpr self modes) (fields => True)):
    Parse.Gives GoodItems (() => atom self modes head) (Parsed1 18) :=
  Parse.givesThen (givesPeek modes) (first _ =>
    Parse.givesThen baseGives (base baseParsed => givesAtomAfter self modes head first base baseParsed recordGives))

-- Reading a token that must be there.

theorem givesUnexpected ∀ (modes: Modes) (what: Text):
    Parse.Gives GoodItems (() => modes.unexpected what) (message => True) :=
  Parse.givesThen givesLeft (seen _ => Parse.givesDone byComputing)

--| A parse that fails gives anything.
theorem givesFail ∀ (modes: Modes) (what: Text) [holds: a → Prop]:
    Parse.Gives GoodItems (() => modes.fail what) holds :=
  Parse.givesThen (givesUnexpected modes what) (message _ => Parse.readsFatal _ _)

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
              goodFirst [item := item] (rewrite shape at fine) (rewrite DecEq.sound took then within))))

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
    | [], found => (Bool.falseNotTrue found).impossible
    | [only], found => (Bool.falseNotTrue found).impossible

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
    | [], found => (Bool.falseNotTrue found).impossible
    | [only], found => (Bool.falseNotTrue found).impossible
