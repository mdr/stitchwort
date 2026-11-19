--| The parser's walk for slice 1's grammar (docs/reviews/SW-4166-carried-walk-plan.md §2, lane K1): every parser
--| function on slice 1's path gives a tree that, if it is in the grammar (`grammar1`), has the words of the items it read
--| (commas left out), their kinds (commas in, `Fmt.Kinds1.Expr.kinds1`), and is in the driver's slice (`within1`). The
--| spec is `Kept`, `Syntax.ParseCarries`' `Carried` gated on the grammar rather than the driver's slice and with two
--| more conjuncts; `carriedOfKept` gives `Carried` back.
--|
--| This file has the spec, its combinators, the atoms, brackets and comma lists, arguments and applications, `unary`
--| and the operator links up to `append_expr`: the first half of `Syntax.ParseCarries`' walk, over the same parser
--| functions with the same splits. The levels above `append_expr`, the knot, declarations and the file are lane K2's.
--|
--| A name or numeral's spelling is in the driver's slice by lane L's fact, taken here as the hypothesis `SpellsText1`
--| until it is proved.

namespace Syntax.ParseKept
import Std (Bool, DecEq, Eq, List, Nat, Option, Pair, Parse, Result, Text)
import Syntax (..)
import Fmt (..)
import Fmt.Grammar1 (..)
import Fmt.Kinds1 (..)
import Syntax.Proofs (..)
import Syntax.ParseProofs (..)
import Syntax.ParseWalk (..)
import Syntax.AutoPlaced (..)
import Syntax.ParseCarries (
  Carried,
  NestedCarries,
  OneOf,
  SameOrOut,
  codeAs,
  itemWords,
  itemWordsAfterComma,
  itemWordsAppend,
  itemWordsCode,
  itemWordsComma,
  itemWordsCons,
  oneOfWords,
  readsAfter0,
  readsAtBumpRead,
  readsAtomAfter,
  readsExpect,
  readsFail,
  readsFailName,
  readsTupleClose,
  readsTupleEnds,
  wordCode
)

-- The spec.

--| The kinds of the items a parser read, commas included.
def itemKinds (read: List Item): List Tok := read.map Item.kind

--| What a parser function gives, read from `read`: a tree of slice 1's grammar has the words of the items read for it
--| (commas left out), their kinds (commas in), and is in the driver's slice. A tree outside the grammar says nothing.
def Kept (read: List Item) (expr: Expr): Prop :=
  expr.grammar1 = True → expr.words = itemWords read ∧ expr.kinds1 = itemKinds read ∧ expr.within1 = True

--| `self` keeps its items at every goal.
def NestedKept (self: Goal → {Parse Item} Expr): Prop :=
  ∀ (goal: Goal) => Parse.ReadsIn GoodItems (() => self goal) Kept

--| `Kept` says all `Carried` does, since the driver's slice is within the grammar.
theorem carriedOfKept ∀ [read: List Item] [expr: Expr] (kept: Kept read expr): Carried read expr := within =>
  (kept (Expr.grammarOfWithin1 expr within)).left

theorem nestedCarriesOfKept ∀ [self: Goal → {Parse Item} Expr] (nested: NestedKept self): NestedCarries self := goal =>
  Parse.readsWeaken (nested goal) (read value kept => carriedOfKept kept)

--| Lane L's fact (docs/reviews/SW-4166-carried-walk-plan.md §4): a name or numeral spelled as `Spells` has it is one
--| `textSpells1` takes. A hypothesis here until it is proved; false today only for `auto`, which `textSpells1` refuses.
def SpellsText1: Prop :=
  ∀ (kind: Tok) (text: Text) => kind.atom1 = True → Spells kind text → textSpells1 kind text = True

-- Where an `auto` call may start a list (SW-4128, lane A): `KeptAt` and the step at `exprPlain`, for the walk
-- follow-up that carries them.

--| A goal that starts a full expression: `expr` and `expr_inline`, the levels whose parser reaches `exprPlain` and so
--| tests for an implicit binder.
def Goal.full (goal: Goal): Bool := match goal.level with
  | LevelFull => True
  | LevelInline => True
  | _ => False

--| `Kept`, and at a goal that starts a full expression, a tree of the grammar placed as one
--| (`Syntax.AutoPlaced.Expr.autoPlaced1`: no list at its start starts with an `auto` call). The full expressions inside
--| a node are the node's own business: the walk follow-up adds `autoPlaced1 False` to `Kept`, and `keptPlacedUp` gives
--| this conjunct at `exprPlain` from `implicitOn = False`.
def KeptAt (goal: Goal) (read: List Item) (expr: Expr): Prop :=
  Kept read expr ∧ (goal.full = True → expr.grammar1 = True → expr.autoPlaced1 True = True)

--| An `auto` call on a type's name starts with its tokens: `auto`, then an upper-case name.
theorem autoCallTokens ∀ (expr: Expr)
    (grammar: expr.grammar1 = True)
    (call: expr.autoCall1 = True):
    ∃ (auto: Word) (kinds: List Tok) (words: List Word) => expr.kinds1 = [Lower, Upper, ..kinds]
      ∧ expr.words = [auto, ..words]
      ∧ auto.text = "auto" :=
  match expr, grammar, call with
    | App (Atom headKind word) [Atom argumentKind argumentWord, ..more], _, call =>
      let isLower: headKind = Lower := DecEq.sound (Bool.andLeft call)
      let isAuto: word.text = "auto" := DecEq.sound (Bool.andLeft (Bool.andRight call))
      let isUpper: argumentKind = Upper := DecEq.sound (Bool.andRight (Bool.andRight call))
      (word, argsKinds1 more, [argumentWord, ..itemsWords more], (rewrite isLower, isUpper), byComputing, isAuto)
    | Infix InfixBinary left operator right, grammar, call =>
      let (auto, kinds, words, isKinds, isWords, isAuto) := autoCallTokens left (Bool.andLeft grammar) call
      (
        auto,
        kinds ++ [binaryKind1 operator.text, ..right.kinds1],
        words ++ [operator, ..right.words],
        (rewrite isKinds),
        (rewrite isWords),
        isAuto
      )
    | Infix InfixArrow left operator right, grammar, call =>
      let (auto, kinds, words, isKinds, isWords, isAuto) := autoCallTokens left (Bool.andLeft grammar) call
      (
        auto,
        kinds ++ [Arrow, ..right.kinds1],
        words ++ [operator, ..right.words],
        (rewrite isKinds),
        (rewrite isWords),
        isAuto
      )

--| A tree of the grammar placed inside but not at its start starts with `[auto Upper`: a list whose first item is an
--| `auto` call, at the end of its leftmost spine.
--|
--| Proof idea: by induction on the leftmost spine (a call's head, an operator's left side), where the two placements
--| differ only at the list that ends it; there `autoLeadCall` and `autoCallTokens` give the tokens.
theorem unplacedTokens ∀ (expr: Expr)
    (grammar: expr.grammar1 = True)
    (inner: expr.autoPlaced1 False = True)
    (unplaced: expr.autoPlaced1 True = False):
    ∃ (open auto: Word) (kinds: List Tok) (words: List Word) => expr.kinds1 = [LBracket, Lower, Upper, ..kinds]
      ∧ expr.words = [open, auto, ..words]
      ∧ auto.text = "auto" :=
  match expr, grammar, inner, unplaced with
    | ListOf open [one, ..others] trailing close, grammar, inner, unplaced =>
      let rest: (one.autoPlaced1 True && autoPlacedAll True others) = True := inner
      let lead: autoLead1 True one = False := match isLead: autoLead1 True one with
        | False => byComputing
        | True => (Bool.falseNotTrue (Eq.trans unplaced.flipped rest)).impossible
      let (auto, kinds, words, isKinds, isWords, isAuto) :=
        autoCallTokens one (Bool.andLeft grammar) (autoLeadCall one lead)
      (
        open,
        auto,
        kinds ++ restKinds1 RBracket trailing others,
        (words ++ itemsWords others) ++ [close],
        (rewrite isKinds),
        (rewrite isWords),
        isAuto
      )
    | App head arguments, grammar, inner, unplaced =>
      let headUnplaced: head.autoPlaced1 True = False := match isHead: head.autoPlaced1 True with
        | False => byComputing
        | True => (Bool.falseNotTrue (Eq.trans unplaced.flipped (Bool.andRight inner))).impossible
      let (open, auto, kinds, words, isKinds, isWords, isAuto) :=
        unplacedTokens head (Bool.andLeft grammar) (Bool.andLeft inner) headUnplaced
      (
        open,
        auto,
        kinds ++ argsKinds1 arguments,
        words ++ itemsWords arguments,
        (rewrite isKinds),
        (rewrite isWords),
        isAuto
      )
    | Infix InfixBinary left operator right, grammar, inner, unplaced =>
      let leftUnplaced: left.autoPlaced1 True = False := match isLeft: left.autoPlaced1 True with
        | False => byComputing
        | True => (Bool.falseNotTrue (Eq.trans unplaced.flipped (Bool.andRight inner))).impossible
      let (open, auto, kinds, words, isKinds, isWords, isAuto) :=
        unplacedTokens left (Bool.andLeft grammar) (Bool.andLeft inner) leftUnplaced
      (
        open,
        auto,
        kinds ++ [binaryKind1 operator.text, ..right.kinds1],
        words ++ [operator, ..right.words],
        (rewrite isKinds),
        (rewrite isWords),
        isAuto
      )
    | Infix InfixArrow left operator right, grammar, inner, unplaced =>
      let leftUnplaced: left.autoPlaced1 True = False := match isLeft: left.autoPlaced1 True with
        | False => byComputing
        | True => (Bool.falseNotTrue (Eq.trans unplaced.flipped (Bool.andRight inner))).impossible
      let (open, auto, kinds, words, isKinds, isWords, isAuto) :=
        unplacedTokens left (Bool.andLeft grammar) (Bool.andLeft inner) leftUnplaced
      (
        open,
        auto,
        kinds ++ [Arrow, ..right.kinds1],
        words ++ [operator, ..right.words],
        (rewrite isKinds),
        (rewrite isWords),
        isAuto
      )
    | Paren _ _ _, _, inner, unplaced => (Bool.falseNotTrue (Eq.trans unplaced.flipped inner)).impossible
    | Tuple _ _ _ _, _, inner, unplaced => (Bool.falseNotTrue (Eq.trans unplaced.flipped inner)).impossible
    | Prefix _ _, _, inner, unplaced => (Bool.falseNotTrue (Eq.trans unplaced.flipped inner)).impossible

--| Items whose kinds and words start `[auto Upper` are what `namelessAutoAt` tests for.
theorem autoItemsAhead ∀ (read rest: List Item) (kinds: List Tok) (open auto: Word) (words: List Word)
    (readKinds: itemKinds read = [LBracket, Lower, Upper, ..kinds])
    (readWords: itemWords read = [open, auto, ..words])
    (isAuto: auto.text = "auto"):
    namelessAutoAt (read ++ rest) = True :=
  match read, readKinds with
    | [first, second, third, ..more], readKinds =>
      let firstKind: first.kind = LBracket := List.consInjectiveHead _ _ _ _ readKinds
      let afterFirst := Eq.cong (.drop 1) readKinds
      let secondKind: second.kind = Lower := List.consInjectiveHead _ _ _ _ afterFirst
      let thirdKind: third.kind = Upper := List.consInjectiveHead _ _ _ _ (Eq.cong (.drop 1) afterFirst)
      let wordsAre: itemWords [first, second, third, ..more]
        = [first.leaf.word, second.leaf.word, ..itemWords [third, ..more]] :=
        rewrite itemWordsCons first [second, third, ..more] (codeAs firstKind byComputing),
            itemWordsCons second [third, ..more] (codeAs secondKind byComputing)
      let secondWord: second.leaf.word = auto :=
        List.consInjectiveHead _ _ _ _ (Eq.cong (.drop 1) (Eq.trans wordsAre.flipped readWords))
      let secondText: second.text = "auto" := Eq.trans (Eq.cong (word => word.text) secondWord) isAuto
      rewrite secondKind, secondText, thirdKind
    | _, _ => cases

--| The items of `[auto Ord]`: `autoItemsAhead`'s hypotheses hold of them.
def autoRead: List Item := match lex "[auto Ord]" with
  | Ok lexed => items lexed.leaves
  | Err _ => []

def autoWordAt (index: Nat): Word := match (itemWords autoRead).drop index with
  | [word, .._] => word
  | [] => { text = "", comments = { above = [], after = None, blankBefore = False } }

theorem autoItemsAheadExample: namelessAutoAt (autoRead ++ []) = True :=
  autoItemsAhead autoRead []
    [RBracket]
    (autoWordAt 0)
    (autoWordAt 1)
    ((itemWords autoRead).drop 2)
    byComputing
    byComputing
    byComputing

--| `KeptAt`'s full-goal conjunct at `exprPlain`: a tree of the grammar that keeps its items and is placed inside is
--| placed as a full expression, when the items ahead are no implicit binder (`implicitOn = False`, given the
--| look-ahead's first item is the `[` that would start it).
theorem keptPlacedUp ∀ (read rest: List Item) (expr: Expr)
    (kept: Kept read expr)
    (grammar: expr.grammar1 = True)
    (inner: expr.autoPlaced1 False = True)
    (noBinder: namelessAutoAt (read ++ rest) = False):
    expr.autoPlaced1 True = True :=
  match unplaced: expr.autoPlaced1 True with
    | True => byComputing
    | False =>
      let (isWords, isKinds, _) := kept grammar
      let (open, auto, kinds, words, treeKinds, treeWords, isAuto) := unplacedTokens expr grammar inner unplaced
      let ahead :=
        autoItemsAhead read rest kinds open auto words
          (Eq.trans isKinds.flipped treeKinds)
          (Eq.trans isWords.flipped treeWords)
          isAuto
      (Bool.falseNotTrue (Eq.trans noBinder.flipped ahead)).impossible

-- Kinds of items.

theorem itemKindsAppend ∀ (first rest: List Item): itemKinds (first ++ rest) = itemKinds first ++ itemKinds rest :=
  List.mapAppend first rest Item.kind

-- Combinators.

--| A tree outside the grammar keeps any items.
theorem keptOut ∀ (read: List Item) [expr: Expr] (out: Out expr): Kept read expr := grammar =>
  (Bool.falseNotTrue (rewrite out at grammar)).impossible

--| The lift of `ParseWalk`'s facts for the parsers outside the slice.
theorem readsOut ∀ [p: () → {Parse Item} Expr] (gives: Parse.Gives GoodItems p Out): Parse.ReadsIn GoodItems p Kept :=
  Parse.readsWeaken gives (read value out => keptOut read out)

--| `readsOut` at a spec about more than what this parser read.
theorem readsOutAfter ∀ (before: List Item) [p: () → {Parse Item} Expr]
    (gives: Parse.Gives GoodItems p Out):
    Parse.ReadsIn GoodItems p (read value => Kept (before ++ read) value) :=
  Parse.readsWeaken gives (read value out => keptOut _ out)

--| A tree kept, then kept as it is or replaced by one outside the grammar.
theorem keptSame ∀ [base value: Expr] [first second: List Item]
    (kept: Kept first base)
    (same: SameOrOut base second value):
    Kept (first ++ second) value :=
  match same with
    | Inr out => keptOut _ out
    | Inl (empty, same) => rewrite empty, same, List.appendNil first then kept

--| `atom`, from what `atom_base` keeps: what follows the base keeps it or leaves the grammar.
theorem readsAtom ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (head: Bool)
    (bases: Parse.ReadsIn GoodItems (() => atomBase self modes) Kept)
    (records: Parse.Gives GoodItems (() => recordExpr self modes) Out):
    Parse.ReadsIn GoodItems (() => atom self modes head) Kept :=
  readsAfter0
    [p := () => modes.peek]
    [j := first => atomAfter self modes head first (atomBase self modes)]
    (reads0Peek modes)
    (first =>
      Parse.readsThen
        [p := () => atomBase self modes]
        [j := base => atomAfter self modes head first base]
        bases
        (r1 base kept =>
          Parse.readsWeaken (readsAtomAfter self modes head first base records) (r2 value same => keptSame kept same)))

-- The atoms.

theorem wordOfAtom1 ∀ (kind: Tok) (atom: kind.atom1 = True): kind.wordWithin1 = True := match kind with
  | Lower => byComputing
  | Upper => byComputing
  | Num => byComputing
  | Float => byComputing

theorem tokWithinOfAtom1 ∀ (kind: Tok) (atom: kind.atom1 = True): kind.within1 = True := match kind with
  | Lower => byComputing
  | Upper => byComputing
  | Num => byComputing
  | Float => byComputing

--| A good item read as an atom: in the grammar, it is a name or numeral, spelled as the slice has them.
theorem keptAtom ∀ (spelled: SpellsText1) (item: Item)
    (good: GoodItem item):
    Kept [item] (Atom item.kind item.leaf.word) :=
  grammar =>
    let word := wordOfAtom1 item.kind grammar
    (
      (rewrite itemWordsCode item (wordCode item.kind word)),
      byComputing,
      Bool.andIntro word (spelled item.kind item.text grammar (good (tokWithinOfAtom1 item.kind grammar)))
    )

--| An item a prefix operator is read from: the kind and text are slice 1's, and it is no comma.
def PrefixItem (item: Item): Prop :=
  prefixKind1 item.text = item.kind ∧ prefixText1 item.text = True ∧ (item.kind == Comma) = False

theorem prefixSpells ∀ (kind: Tok) (text: Text)
    (sign: (kind == Minus || kind == Bang) = True)
    (good: kind.within1 = True → Spells kind text):
    prefixKind1 text = kind ∧ prefixText1 text = True ∧ (kind == Comma) = False :=
  match kind, sign, good with
    | Minus, sign, good => rewrite good byComputing then (byComputing, byComputing, byComputing)
    | Bang, sign, good =>
      match good byComputing with
        | Inl bang => rewrite bang then (byComputing, byComputing, byComputing)
        | Inr not => rewrite not then (byComputing, byComputing, byComputing)

theorem prefixItemOf ∀ (item: Item)
    (sign: (item.kind == Minus || item.kind == Bang) = True)
    (good: GoodItem item):
    PrefixItem item :=
  prefixSpells item.kind item.text sign good

theorem keptPrefix ∀ (item: Item) (read: List Item) (operand: Expr)
    (sign: PrefixItem item)
    (kept: Kept read operand):
    Kept [item, ..read] (Prefix item.leaf.word operand) :=
  grammar =>
    let (words, kinds, within) := kept grammar
    let (kindIs, text, code) := sign
    ((rewrite itemWordsCons item read code, words), (rewrite kinds, kindIs), Bool.andIntro within text)

theorem readsWordAtom ∀ (spelled: SpellsText1) (start: Parse.Mark Item) (item: Item) (later: List Item)
    (shape: start.rest = [item, ..later])
    (fine: Parse.Fits Item GoodItems start.rest):
    Parse.ReadsAt start (() => wordAtom item.kind) Kept :=
  readsAtBumpRead [k := word => Atom item.kind word] shape fine (after tail fits =>
    Parse.readsAtDone after _ _ (keptAtom spelled item (goodHead fine shape)))

theorem readsPrefixAtom ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: NestedKept self)
    (negates: Bool) (start: Parse.Mark Item) (item: Item) (later: List Item)
    (shape: start.rest = [item, ..later])
    (sign: (item.kind == Minus || item.kind == Bang) = True)
    (fine: Parse.Fits Item GoodItems start.rest):
    Parse.ReadsAt start (() => prefixAtom self modes negates) Kept :=
  let prefix := prefixItemOf item sign (goodHead fine shape)
  match negates with
    | True => readsAtBumpRead shape fine (after tail fits =>
      Parse.readsAtThen (nested { modes, level = LevelArgument } after fits) (read operand after2 starts kept =>
        Parse.readsAtDone after2 _ _ (rewrite List.appendNil read then keptPrefix item read operand prefix kept)))
    | False => readsFailName modes _ start fine

theorem readsNegativeNumber ∀ (spelled: SpellsText1) (start: Parse.Mark Item) (minus number: Item) (later: List Item)
    (shape: start.rest = [minus, number, ..later])
    (isMinus: minus.kind = Minus)
    (fine: Parse.Fits Item GoodItems start.rest):
    Parse.ReadsAt start (() => negativeNumber()) Kept :=
  let good: List.All GoodItem start.rest := fine.holds.left
  let (minusGood, numberGood, _) := rewrite shape at good then good
  let prefix := prefixItemOf minus (rewrite isMinus) minusGood
  readsAtBumpRead [k := word => numberAfter word left()] shape fine (after tail fits =>
    readsAtAfterLeft [j := items => numberAfter minus.leaf.word items] fits (after2 same fits2 =>
      rewrite tail then
        readsAtBumpRead
          [k := word => Prefix minus.leaf.word (Atom number.kind word)]
          (rewrite same, tail)
          fits2
          (after3 tail3 fits3 =>
            Parse.readsAtDone after3
              (Prefix minus.leaf.word (Atom number.kind number.leaf.word)) _
              (keptPrefix minus
                [number]
                (Atom number.kind number.leaf.word)
                prefix
                (keptAtom spelled number numberGood)))))

theorem readsNegativeAtomOn ∀ (spelled: SpellsText1) (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: NestedKept self)
    (items: List Item) (start: Parse.Mark Item) (item: Item) (later: List Item)
    (shape: start.rest = [item, ..later])
    (found: items = start.rest)
    (isMinus: item.kind = Minus)
    (fine: Parse.Fits Item GoodItems start.rest):
    Parse.ReadsAt start (() => negativeAtomOn self modes items) Kept :=
  match negative: negativeNumeral items with
    | True =>
      let (minus, number, rest, split, minusKind, numberKind) := negativeNumeralKinds items negative
      readsNegativeNumber spelled start minus number rest (rewrite <- found then split) minusKind fine
    | False => readsPrefixAtom self modes nested (argumentMinus items) start item later shape (rewrite isMinus) fine

theorem readsNegativeAtom ∀ (spelled: SpellsText1) (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: NestedKept self)
    (start: Parse.Mark Item) (item: Item) (later: List Item)
    (shape: start.rest = [item, ..later])
    (isMinus: item.kind = Minus)
    (fine: Parse.Fits Item GoodItems start.rest):
    Parse.ReadsAt start (() => negativeAtom self modes) Kept :=
  readsAtAfterLeft [j := items => negativeAtomOn self modes items] fine (after same fits =>
    readsNegativeAtomOn spelled self modes nested start.rest after item later
      (rewrite same then shape)
      same.flipped
      isMinus
      fits)

-- Comma lists.

--| The trees of a comma list after its first, all in the grammar, have the words of the items read for them (the
--| commas giving none), their kinds with a comma before each and a last comma if `trailing`, and are in the slice.
--| `close` is any closer after them.
def RestKept (read: List Item) (items: List Expr) (trailing: Bool): Prop :=
  allGrammar1 items = True
    → itemsWords items = itemWords read
      ∧ (∀ (close: Tok) => restKinds1 close trailing items = itemKinds read ++ [close])
      ∧ allWithin1 items = True

--| A whole comma list's trees, all in the grammar: their words, their kinds with the commas between and after them,
--| and the slice.
def ItemsKept (read: List Item) (items: List Expr) (trailing: Bool): Prop :=
  allGrammar1 items = True
    → itemsWords items = itemWords read
      ∧ (∀ (close: Tok) => itemsKinds1 close trailing items = itemKinds read ++ [close])
      ∧ allWithin1 items = True

--| What a comma list gave after the trees it already had, `prior`: more trees, kept by what it read, and whether it
--| read a last comma.
def ListKept (prior: List Expr) (read: List Item) (pair: (List Expr, Bool)): Prop :=
  ∃ (more: List Expr) => pair.fst = prior ++ more ∧ RestKept read more pair.snd

theorem restKeptNil: RestKept [] [] False := grammar => (byComputing, close => byComputing, byComputing)

--| A last comma and nothing after it.
theorem restKeptComma ∀ (comma: Item) (isComma: comma.kind = Comma): RestKept [comma] [] True := grammar =>
  ((rewrite itemWordsComma comma isComma), close => (rewrite isComma), byComputing)

--| A comma, then a tree and the rest of the list.
theorem restKeptStep ∀ [first rest: List Item] [value: Expr] [more: List Expr] [trailing: Bool] (comma: Item)
    (isComma: comma.kind = Comma)
    (kept: Kept first value)
    (others: RestKept rest more trailing):
    RestKept [comma, ..first ++ rest] [value, ..more] trailing :=
  grammar =>
    let (words, kinds, within) := kept (Bool.andLeft grammar)
    let (otherWords, otherKinds, otherWithin) := others (Bool.andRight grammar)
    (
      (rewrite itemWordsAfterComma comma (first ++ rest) isComma, itemWordsAppend first rest, words, otherWords),
      (close =>
        calc restKinds1 close trailing [value, ..more]
          _ = [Comma, ..itemKinds first ++ (itemKinds rest ++ [close])] := rewrite kinds, otherKinds close
          _ = itemKinds [comma, ..first ++ rest] ++ [close] :=
            rewrite itemKindsAppend first rest, isComma, List.appendAssoc (itemKinds first) (itemKinds rest) [close]),
      Bool.andIntro within otherWithin
    )

--| A first tree, then the rest of the list.
theorem itemsKeptCons ∀ [first rest: List Item] [value: Expr] [more: List Expr] [trailing: Bool]
    (kept: Kept first value)
    (others: RestKept rest more trailing):
    ItemsKept (first ++ rest) [value, ..more] trailing :=
  grammar =>
    let (words, kinds, within) := kept (Bool.andLeft grammar)
    let (otherWords, otherKinds, otherWithin) := others (Bool.andRight grammar)
    (
      (rewrite itemWordsAppend first rest, words, otherWords),
      (close =>
        calc itemsKinds1 close trailing [value, ..more]
          _ = itemKinds first ++ (itemKinds rest ++ [close]) := rewrite kinds, otherKinds close
          _ = itemKinds (first ++ rest) ++ [close] :=
            rewrite itemKindsAppend first rest, List.appendAssoc (itemKinds first) (itemKinds rest) [close]),
      Bool.andIntro within otherWithin
    )

theorem listKeptStep ∀ [prior: List Expr] [value: Expr] [comma: Item] [first rest: List Item] [pair: (List Expr, Bool)]
    (isComma: comma.kind = Comma)
    (kept: Kept first value)
    (listed: ListKept (prior ++ [value]) rest pair):
    ListKept prior [comma, ..first ++ rest] pair :=
  let (more, split, items) := listed
  ([value, ..more], rewrite split then List.appendAssoc prior [value] more, restKeptStep comma isComma kept items)

--| The items of a comma list after the first: each comma is read and kept as a kind, and each item is kept.
--|
--| Proof idea: as `Syntax.ParseCarries.readsCommaListFrom`, by induction on the fuel: a comma is bumped, then either the
--| list stops there with a last comma (`restKeptComma`) or another tree is kept and the rest follows
--| (`listKeptStep`); anything else stops with no more trees and no last comma.
theorem readsCommaListFrom ∀ (modes: Modes) (ends: Nat → {Parse Item} Bool) (next: () → {Parse Item} Expr)
    (endsReads: ∀ (count: Nat) => Reads0 (() => ends count))
    (nextReads: Parse.ReadsIn GoodItems next Kept)
    (fuel count: Nat) (current: Expr) (found: List Expr):
    Parse.ReadsIn GoodItems
      (() => commaListFrom fuel modes ends next count current found)
      (ListKept [current, ..found].reverse) :=
  readsInPeeked modes
    (seen => commaListOn fuel modes ends next count current found seen) _
    (start fine stops =>
      match fuel with
        | Zero => Parse.readsAtDone _ _ _ ([], (List.appendNil _).flipped, restKeptNil)
        | Succ more => Parse.readsAtDone _ _ _ ([], (List.appendNil _).flipped, restKeptNil))
    (start item later shape fine stopped =>
      match fuel with
        | Zero => Parse.readsAtDone _ _ _ ([], (List.appendNil _).flipped, restKeptNil)
        | Succ more =>
          match isComma: item.kind == Comma with
            | False => Parse.readsAtDone _ _ _ ([], (List.appendNil _).flipped, restKeptNil)
            | True =>
              readsAtBumpRead
                [k := comma => commaListAfter more modes ends next count [current, ..found] (ends count)]
                shape
                fine
                (after tail fits =>
                  Parse.readsAtThen (endsReads count after fits) (r1 stop after2 starts1 empty =>
                    match stop with
                      | True => Parse.readsAtDone after2 _ _ (
                        [],
                        (List.appendNil _).flipped,
                        (rewrite empty then restKeptComma item (DecEq.sound isComma))
                      )
                      | False =>
                        let fits2 := Parse.Fits.after fits starts1
                        Parse.readsAtThen (nextReads after2 fits2) (r2 value after3 starts2 kept =>
                          Parse.readsAtWeaken
                            (readsCommaListFrom modes ends next endsReads nextReads more
                              (count + 1)
                              value
                              [current, ..found]
                              after3
                              (Parse.Fits.after fits2 starts2))
                            (r3 pair listed =>
                              rewrite empty then
                                listKeptStep
                                  (DecEq.sound isComma)
                                  kept
                                  (rewrite <- List.reverseCons value [current, ..found] then listed))))))

-- Brackets.

theorem keptParen ∀ (open: Item) (inside rest: List Item) (inner: Expr) (close: Word)
    (isOpen: open.kind = LParen)
    (kept: Kept inside inner)
    (closeOne: OneOf RParen rest close):
    Kept [open, ..inside ++ rest] (Paren open.leaf.word inner close) :=
  grammar =>
    let (words, kinds, within) := kept grammar
    let (closeItem, single, closeKind, same) := closeOne
    (
      (rewrite itemWordsCons open (inside ++ rest) (codeAs isOpen byComputing),
          itemWordsAppend inside rest,
          words,
          oneOfWords closeOne byComputing),
      (calc (Paren open.leaf.word inner close).kinds1
        _ = [open.kind, ..itemKinds inside ++ [closeItem.kind]] := rewrite kinds, isOpen, closeKind
        _ = itemKinds [open, ..inside ++ rest] := rewrite single, itemKindsAppend inside [closeItem]),
      within
    )

theorem keptTuple ∀ (open: Item) (inside rest: List Item) (items: List Expr) (trailing: Bool) (close: Word)
    (isOpen: open.kind = LParen)
    (kept: ItemsKept inside items trailing)
    (closeOne: OneOf RParen rest close):
    Kept [open, ..inside ++ rest] (Tuple open.leaf.word items trailing close) :=
  grammar =>
    let (words, kinds, within) := kept grammar
    let (closeItem, single, closeKind, same) := closeOne
    (
      (rewrite itemWordsCons open (inside ++ rest) (codeAs isOpen byComputing),
          itemWordsAppend inside rest,
          words,
          oneOfWords closeOne byComputing),
      (calc (Tuple open.leaf.word items trailing close).kinds1
        _ = [open.kind, ..itemKinds inside ++ [closeItem.kind]] := rewrite kinds RParen, isOpen, closeKind
        _ = itemKinds [open, ..inside ++ rest] := rewrite single, itemKindsAppend inside [closeItem]),
      within
    )

theorem keptList ∀ (open: Item) (inside rest: List Item) (items: List Expr) (trailing: Bool) (close: Word)
    (isOpen: open.kind = LBracket)
    (kept: ItemsKept inside items trailing)
    (closeOne: OneOf RBracket rest close):
    Kept [open, ..inside ++ rest] (ListOf open.leaf.word items trailing close) :=
  grammar =>
    let (words, kinds, within) := kept grammar
    let (closeItem, single, closeKind, same) := closeOne
    (
      (rewrite itemWordsCons open (inside ++ rest) (codeAs isOpen byComputing),
          itemWordsAppend inside rest,
          words,
          oneOfWords closeOne byComputing),
      (calc (ListOf open.leaf.word items trailing close).kinds1
        _ = [open.kind, ..itemKinds inside ++ [closeItem.kind]] := rewrite kinds RBracket, isOpen, closeKind
        _ = itemKinds [open, ..inside ++ rest] := rewrite single, itemKindsAppend inside [closeItem]),
      within
    )

--| `)` after the first tree in brackets.
theorem readsParenClose ∀ (inner: Modes) (open: Item) (inside: List Item) (first: Expr)
    (isOpen: open.kind = LParen)
    (kept: Kept inside first):
    Parse.ReadsIn GoodItems (() => parenClose inner open.leaf.word first) (read value =>
      Kept [open, ..inside ++ read] value) :=
  Parse.readsThen (readsExpect inner RParen "`)`") (rc close one =>
    Parse.readsDone _ _ (rewrite List.appendNil rc then keptParen open inside rc first close isOpen kept one))

--| A tuple's tail, from the comma after its first tree: the comma, the second tree, the rest of the list and `)`.
--|
--| Proof idea: as `Syntax.ParseCarries.readsTupleRest`: the comma is bumped, the second tree and the rest of the list
--| are kept (`readsCommaListFrom`), and `)` is one item; the items read are regrouped by `List.appendAssoc` to the
--| shape `keptTuple` takes.
theorem readsTupleRest ∀ (self: Goal → {Parse Item} Expr) (inner: Modes) (open: Item) (inside: List Item) (first: Expr)
    (nested: NestedKept self)
    (isOpen: open.kind = LParen)
    (kept: Kept inside first)
    (start: Parse.Mark Item) (comma: Item) (later: List Item)
    (shape: start.rest = [comma, ..later])
    (isComma: comma.kind = Comma)
    (fine: Parse.Fits Item GoodItems start.rest):
    Parse.ReadsAt start (() => tupleRest self inner open.leaf.word first) (read value =>
      Kept [open, ..inside ++ read] value) :=
  readsAtAfter0
    [p := () => Parse.mark().left]
    [j := fuel => tupleFuel self inner open.leaf.word first fuel]
    (reads0Mark (here => here.left))
    fine
    (fuel after same fits =>
      readsAtBumpRead
        [k := word => tupleSecond self inner open.leaf.word first fuel (full self inner)]
        (rewrite same then shape)
        fits
        (after2 tail fits2 =>
          Parse.readsAtThen
            (nested { modes = inner, level = LevelFull } after2 fits2)
            (r2 second after3 starts2 kept2 =>
              let fits3 := Parse.Fits.after fits2 starts2
              Parse.readsAtThen
                (readsCommaListFrom inner
                  (tupleEnds inner)
                  (() => full self inner)
                  (readsTupleEnds inner)
                  (nested { modes = inner, level = LevelFull })
                  fuel
                  2
                  second
                  [first]
                  after3
                  fits3)
                (r3 pair after4 starts3 listed =>
                  match pair with
                    | (items, trailing) =>
                      Parse.readsAtThen
                        (readsTupleClose inner after4 (Parse.Fits.after fits3 starts3))
                        (rc close after5 starts4 one =>
                          let (more, split, others) := listed
                          let tail: RestKept [comma, ..r2 ++ r3] [second, ..more] trailing :=
                            restKeptStep comma isComma kept2 others
                          let all: ItemsKept (inside ++ [comma, ..r2 ++ r3]) items trailing :=
                            rewrite split then itemsKeptCons kept tail
                          let whole :=
                            keptTuple open (inside ++ [comma, ..r2 ++ r3]) rc items trailing close isOpen all one
                          Parse.readsAtDone after5 _ _
                            (rewrite List.appendNil rc then
                              rewrite List.appendAssoc inside [comma, ..r2 ++ r3] rc,
                                  List.appendAssoc r2 r3 rc at whole then
                                whole))))))

--| Proof idea: by what follows the first tree: a comma starts a tuple (`readsTupleRest`), a colon an annotation
--| (outside the grammar), and anything else, or nothing, is `)`.
theorem readsBracketedFirst ∀ (self: Goal → {Parse Item} Expr) (inner: Modes) (open: Item)
    (inside: List Item) (first: Expr)
    (nested: NestedKept self)
    (outside: OutsideAtoms self)
    (isOpen: open.kind = LParen)
    (kept: Kept inside first):
    Parse.ReadsIn GoodItems (() => bracketedFirst self inner open.leaf.word first) (read value =>
      Kept [open, ..inside ++ read] value) :=
  readsInPeeked inner
    (seen => bracketedAfter self inner open.leaf.word first seen) _
    (start fine stops => readsParenClose inner open inside first isOpen kept start fine)
    (start item later shape fine stopped =>
      match isComma: item.kind == Comma with
        | True =>
          readsTupleRest self inner open inside first nested isOpen kept start item later shape
            (DecEq.sound isComma)
            fine
        | False =>
          match isColon: item.kind == Colon with
            | True =>
              readsOutAfter
                [open, ..inside]
                [p := () => annotated self inner open.leaf.word first]
                (outside.annotations inner open.leaf.word first)
                start
                fine
            | False => readsParenClose inner open inside first isOpen kept start fine)

theorem readsBracketedTail ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (open: Item)
    (nested: NestedKept self)
    (outside: OutsideAtoms self)
    (isOpen: open.kind = LParen):
    Parse.ReadsIn GoodItems (() => bracketedTail self modes open.leaf.word) (read value => Kept [open, ..read] value) :=
  Parse.readsThen
    [p := () => full self modes.inBrackets]
    [j := first => bracketedFirst self modes.inBrackets open.leaf.word first]
    (nested { modes = modes.inBrackets, level = LevelFull })
    (inside first kept => readsBracketedFirst self modes.inBrackets open inside first nested outside isOpen kept)

theorem readsBracketed ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: NestedKept self)
    (outside: OutsideAtoms self)
    (start: Parse.Mark Item) (item: Item) (later: List Item)
    (shape: start.rest = [item, ..later])
    (isParen: item.kind = LParen)
    (fine: Parse.Fits Item GoodItems start.rest):
    Parse.ReadsAt start (() => bracketed self modes) Kept :=
  readsAtBumpRead [k := open => bracketedTail self modes open] shape fine (after tail fits =>
    readsBracketedTail self modes item nested outside isParen after fits)

theorem readsParenRest ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: NestedKept self)
    (outside: OutsideAtoms self)
    (items: List Item) (start: Parse.Mark Item) (item: Item) (later: List Item)
    (shape: start.rest = [item, ..later])
    (isParen: item.kind = LParen)
    (fine: Parse.Fits Item GoodItems start.rest):
    Parse.ReadsAt start (() => parenRest self modes items) Kept :=
  match rightOperator items with
    | Some inside =>
      readsOut [p := () => rightSection self modes inside] (outside.rightSections modes inside) start fine
    | None => readsBracketed self modes nested outside start item later shape isParen fine

theorem readsParenOn ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: NestedKept self)
    (outside: OutsideAtoms self)
    (second third: Option Tok) (start: Parse.Mark Item) (item: Item) (later: List Item)
    (shape: start.rest = [item, ..later])
    (isParen: item.kind = LParen)
    (fine: Parse.Fits Item GoodItems start.rest):
    Parse.ReadsAt start (() => parenOn self modes second third) Kept :=
  match parenOutside second third with
    | True =>
      readsOut [p := () => parenOther self modes second third] (outside.parenOthers modes second third) start fine
    | False => readsAtAfterLeft [j := items => parenRest self modes items] fine (after same fits =>
      readsParenRest self modes nested outside start.rest after item later (rewrite same then shape) isParen fits)

--| Proof idea: the two look-aheads read nothing, so the items left are still the `(` and what follows it; then
--| `readsParenOn`.
theorem readsParenAtom ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: NestedKept self)
    (outside: OutsideAtoms self)
    (start: Parse.Mark Item) (item: Item) (later: List Item)
    (shape: start.rest = [item, ..later])
    (isParen: item.kind = LParen)
    (fine: Parse.Fits Item GoodItems start.rest):
    Parse.ReadsAt start (() => parenAtom self modes) Kept :=
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

--| Proof idea: a spread (`..`) gives a `Spread`, outside the grammar whatever it read; any other item is `self` at the
--| full level.
theorem readsListItem ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: NestedKept self):
    Parse.ReadsIn GoodItems (() => listItem self modes) Kept :=
  readsAfter0
    [p := () => modes.at DotDot]
    [j := spread => listItemAfter self modes spread]
    (reads0At modes DotDot)
    (spread =>
      match spread with
        | True =>
          Parse.readsThen
            [p := () => bump()]
            [j := dots => listSpread self modes dots (modes.at Comma || modes.at RBracket)]
            givesBump
            (r1 dots _ =>
              readsAfter0
                [p := () => modes.at Comma || modes.at RBracket]
                [j := empty => listSpread self modes dots empty]
                (reads0Then [p := () => modes.at Comma] (reads0At modes Comma) (comma =>
                  match comma with
                    | True => reads0Done True
                    | False => reads0At modes RBracket))
                (empty =>
                  match empty with
                    | True => Parse.readsFatal _ _
                    | False =>
                      Parse.readsThen
                        [p := () => full self modes]
                        [j := value => Spread dots value]
                        (nested { modes, level = LevelFull })
                        (r2 value _ => Parse.readsDone _ _ (keptOut _ byComputing))))
        | False => nested { modes, level = LevelFull })

theorem readsListItemsEnd ∀ (self: Goal → {Parse Item} Expr) (inner: Modes) (open: Item) (inside: List Item)
    (items: List Expr) (trailing: Bool)
    (isOpen: open.kind = LBracket)
    (kept: ItemsKept inside items trailing):
    Parse.ReadsIn GoodItems (() => listItemsEnd self inner open.leaf.word (items, trailing)) (read value =>
      Kept [open, ..inside ++ read] value) :=
  Parse.readsThen (readsExpect inner RBracket "`,` or `]`") (rc close one =>
    Parse.readsDone _ _ (rewrite List.appendNil rc then keptList open inside rc items trailing close isOpen kept one))

--| Proof idea: the mark reads nothing; the comma list after the first item gives more trees kept by what it read
--| (`ListKept`), and `]` is one item, so `keptList` applies to the first tree and the rest together.
theorem readsListItemsFrom ∀ (self: Goal → {Parse Item} Expr) (inner: Modes) (open: Item)
    (inside: List Item) (first: Expr)
    (nested: NestedKept self)
    (isOpen: open.kind = LBracket)
    (kept: Kept inside first):
    Parse.ReadsIn GoodItems (() => listItemsFrom self inner open.leaf.word first) (read value =>
      Kept [open, ..inside ++ read] value) :=
  Parse.readsThen
    [p := () => Parse.mark()]
    [j := here =>
      listItemsEnd self inner open.leaf.word
        (commaList (here.left + 1) inner (count => inner.at RBracket) (() => listItem self inner) first [])]
    Parse.readsMark
    (r0 here empty =>
      Parse.readsThen
        [p := () => commaList (here.left + 1) inner (count => inner.at RBracket) (() => listItem self inner) first []]
        [j := pair => listItemsEnd self inner open.leaf.word pair]
        (readsCommaListFrom inner
          (count => inner.at RBracket)
          (() => listItem self inner)
          (count => reads0At inner RBracket)
          (readsListItem self inner nested)
          (here.left + 1)
          1
          first
          [])
        (r1 pair listed =>
          match pair with
            | (items, trailing) =>
              let (more, split, others) := listed
              Parse.readsWeaken
                (readsListItemsEnd self inner open
                  (inside ++ r1)
                  items
                  trailing
                  isOpen
                  (rewrite split then itemsKeptCons kept others))
                (rc value whole => rewrite empty then (rewrite List.appendAssoc inside r1 rc at whole then whole))))

theorem readsListItems ∀ (self: Goal → {Parse Item} Expr) (inner: Modes) (open: Item)
    (nested: NestedKept self)
    (isOpen: open.kind = LBracket):
    Parse.ReadsIn GoodItems (() => listItems self inner open.leaf.word) (read value => Kept [open, ..read] value) :=
  Parse.readsThen
    [p := () => listItem self inner]
    [j := first => listItemsFrom self inner open.leaf.word first]
    (readsListItem self inner nested)
    (inside first kept => readsListItemsFrom self inner open inside first nested isOpen kept)

--| An empty list's items: none, and no comma.
theorem itemsKeptNil: ItemsKept [] [] False := grammar => (byComputing, close => byComputing, byComputing)

theorem readsListPeek ∀ (self: Goal → {Parse Item} Expr) (inner: Modes) (open: Item)
    (nested: NestedKept self)
    (isOpen: open.kind = LBracket):
    Parse.ReadsIn GoodItems (() => listPeek self inner open.leaf.word) (read value => Kept [open, ..read] value) :=
  readsInPeeked inner
    (seen => listAfter self inner open.leaf.word seen) _
    (start fine stops => readsListItems self inner open nested isOpen start fine)
    (start item later shape fine stopped =>
      match isClose: item.kind == RBracket with
        | True => readsAtBumpRead [k := close => ListOf open.leaf.word [] False close] shape fine (after tail fits =>
          Parse.readsAtDone after
            (ListOf open.leaf.word [] False item.leaf.word) _
            (keptList open [] [item] [] False item.leaf.word isOpen itemsKeptNil (
              item,
              byComputing,
              DecEq.sound isClose,
              byComputing
            )))
        | False => readsListItems self inner open nested isOpen start fine)

theorem readsListExpr ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: NestedKept self)
    (start: Parse.Mark Item) (item: Item) (later: List Item)
    (shape: start.rest = [item, ..later])
    (isBracket: item.kind = LBracket)
    (fine: Parse.Fits Item GoodItems start.rest):
    Parse.ReadsAt start (() => listExpr self modes) Kept :=
  readsAtBumpRead [k := open => listTail self modes open] shape fine (after tail fits =>
    readsListPeek self modes.inBrackets item nested isBracket after fits)

theorem readsBracketAt ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: NestedKept self)
    (outside: OutsideAtoms self)
    (second third: Option Tok) (start: Parse.Mark Item) (item: Item) (later: List Item)
    (shape: start.rest = [item, ..later])
    (isBracket: item.kind = LBracket)
    (fine: Parse.Fits Item GoodItems start.rest):
    Parse.ReadsAt start (() => bracketAt self modes second third) Kept :=
  match named: (isSome Lower second || isSome KwDecreasing second) && isSome ColonEq third with
    | True =>
      readsOut
        [p := () => namedArgument self modes RBracket "`]`"]
        (outside.namedArguments modes RBracket "`]`")
        start
        fine
    | False => readsListExpr self modes nested start item later shape isBracket fine

--| Proof idea: the two look-aheads read nothing, so the items left are still the `[` and what follows it; then
--| `readsBracketAt`.
theorem readsBracketAtom ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: NestedKept self)
    (outside: OutsideAtoms self)
    (start: Parse.Mark Item) (item: Item) (later: List Item)
    (shape: start.rest = [item, ..later])
    (isBracket: item.kind = LBracket)
    (fine: Parse.Fits Item GoodItems start.rest):
    Parse.ReadsAt start (() => bracketAtom self modes) Kept :=
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

-- The atom's base, by the kind of its first item.

--| Proof idea: one case per branch of `atomOf`, each by the kind of the item peeked at: `-`, `!`, `(`, `[`, a word, and
--| the rest outside the grammar.
theorem readsAtomOf ∀ (spelled: SpellsText1) (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: NestedKept self)
    (outside: OutsideAtoms self)
    (start: Parse.Mark Item) (item: Item) (later: List Item)
    (shape: start.rest = [item, ..later])
    (fine: Parse.Fits Item GoodItems start.rest):
    Parse.ReadsAt start (() => atomOf self modes item.kind) Kept :=
  match isMinus: item.kind == Minus with
    | True => readsNegativeAtom spelled self modes nested start item later shape (DecEq.sound isMinus) fine
    | False =>
      match isBang: item.kind == Bang with
        | True => readsAtAfterLeft [j := items => prefixBangOn self modes items] fine (after same fits =>
          readsPrefixAtom self modes nested
            (argumentBang start.rest)
            after
            item
            later
            (rewrite same then shape)
            (rewrite DecEq.sound isBang)
            fits)
        | False =>
          match isParen: item.kind == LParen with
            | True => readsParenAtom self modes nested outside start item later shape (DecEq.sound isParen) fine
            | False =>
              match isBracket: item.kind == LBracket with
                | True => readsBracketAtom self modes nested outside start item later shape (DecEq.sound isBracket) fine
                | False =>
                  match word: isWord item.kind with
                    | True => readsWordAtom spelled start item later shape fine
                    | False =>
                      readsOut [p := () => atomRest self modes item.kind] (outside.rests modes item.kind) start fine

--| `atom_base` keeps its items, at every mode.
def BasesKept (self: Goal → {Parse Item} Expr): Prop :=
  ∀ (modes: Modes) => Parse.ReadsIn GoodItems (() => atomBase self modes) Kept

theorem readsAtomBases ∀ (spelled: SpellsText1) (self: Goal → {Parse Item} Expr)
    (nested: NestedKept self)
    (outside: OutsideAtoms self):
    BasesKept self :=
  modes =>
    readsInPeeked modes
      (seen => atomBaseOn self modes seen) _
      (start fine stops => readsOut [p := () => atomMissing self modes] (outside.missings modes) start fine)
      (start item later shape fine stopped => readsAtomOf spelled self modes nested outside start item later shape fine)

-- Application.

--| A call's arguments, all in the grammar: their words, their kinds, and the slice.
def ArgsKept (read: List Item) (args: List Expr): Prop :=
  allGrammar1 args = True → itemsWords args = itemWords read ∧ argsKinds1 args = itemKinds read ∧ allWithin1 args = True

theorem argsKeptNil: ArgsKept [] [] := grammar => (byComputing, byComputing, byComputing)

theorem argsKeptCons ∀ [first rest: List Item] [value: Expr] [more: List Expr]
    (kept: Kept first value)
    (others: ArgsKept rest more):
    ArgsKept (first ++ rest) [value, ..more] :=
  grammar =>
    let (words, kinds, within) := kept (Bool.andLeft grammar)
    let (otherWords, otherKinds, otherWithin) := others (Bool.andRight grammar)
    (
      (rewrite itemWordsAppend first rest, words, otherWords),
      (rewrite itemKindsAppend first rest, kinds, otherKinds),
      Bool.andIntro within otherWithin
    )

theorem keptApp ∀ [first rest: List Item] [head: Expr] [args: List Expr]
    (kept: Kept first head)
    (others: ArgsKept rest args):
    Kept (first ++ rest) (App head args) :=
  grammar =>
    let (words, kinds, within) := kept (Bool.andLeft grammar)
    let (otherWords, otherKinds, otherWithin) := others (Bool.andRight grammar)
    (
      (rewrite itemWordsAppend first rest, words, otherWords),
      (rewrite itemKindsAppend first rest, kinds, otherKinds),
      Bool.andIntro within otherWithin
    )

--| The rounds of a loop that each read a kept tree, or nothing and stopped.
theorem roundsKept ∀ [read: List Item] [values: List Expr]
    (rounds: Parse.Rounds (Parse.Maybe Kept) read values):
    ArgsKept read values :=
  match values, rounds with
    | [], none => rewrite none then argsKeptNil
    | [value, ..more], (first, rest, split, _, kept, others) => rewrite split then argsKeptCons kept (roundsKept others)

theorem readsArgumentBrace ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: NestedKept self)
    (outside: OutsideBraced self) (brace: Bool):
    Parse.ReadsIn GoodItems (() => argumentBrace self modes brace) Kept :=
  match brace with
    | True => readsOut (outside.braceArguments modes)
    | False => nested { modes, level = LevelArgument }

theorem readsArgument ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: NestedKept self)
    (outside: OutsideBraced self):
    Parse.ReadsIn GoodItems (() => argument self modes) Kept :=
  readsAfter0 [p := () => left()] [j := items => argumentAt self modes items] reads0Left (items =>
    match sectionLineAt modes items with
      | True => Parse.readsFatal _ _
      | False =>
        readsAfter0
          [p := () => modes.at Upper && isSome LBrace (modes.peekAt 1)]
          [j := brace => argumentBrace self modes brace]
          (reads0Then [p := () => modes.at Upper] (reads0At modes Upper) (upper =>
            match upper with
              | True => reads0Then [p := () => modes.peekAt 1] (reads0PeekAt modes 1) (found => reads0Done _)
              | False => reads0Done False))
          (brace => readsArgumentBrace self modes nested outside brace))

theorem readsArguments ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: NestedKept self)
    (outside: OutsideBraced self):
    Parse.ReadsIn GoodItems (() => arguments self modes) ArgsKept :=
  Parse.readsWeaken
    (Parse.readsLoop _
      (Parse.Maybe Kept)
      (readsAfter0
        [p := () => startsAtom modes]
        [j := starts => argumentStep self modes starts]
        (reads0StartsAtom modes)
        (starts =>
          match starts with
            | True => Parse.readsThen (readsArgument self modes nested outside) (read value kept =>
              Parse.readsDone (Some value) _ (rewrite List.appendNil read then kept))
            | False => Parse.readsDone None _ byComputing)))
    (read values rounds => roundsKept rounds)

theorem readsAppliedTo ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: NestedKept self)
    (outside: OutsideBraced self)
    (before: List Item) (head: Expr)
    (kept: Kept before head):
    Parse.ReadsIn GoodItems (() => appliedTo self modes head) (read value => Kept (before ++ read) value) :=
  Parse.readsThen (readsArgument self modes nested outside) (r1 first firstKept =>
    Parse.readsThen (readsArguments self modes nested outside) (r2 more others =>
      Parse.readsDone _ _ (rewrite List.appendNil r2 then keptApp kept (argsKeptCons firstKept others))))

theorem keptSectioned ∀ (section: Bool) [read: List Item] [applied: Expr]
    (kept: Kept read applied):
    Kept read (sectioned section applied) :=
  match section with
    | True => keptOut read byComputing
    | False => kept

theorem readsAppEnd ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: NestedKept self)
    (outside: OutsideBraced self)
    (section: Bool) (before: List Item) (head: Expr) (applies: Bool)
    (kept: Kept before head):
    Parse.ReadsIn GoodItems (() => appEnd self modes section head applies) (read value =>
      Kept (before ++ read) value) :=
  match applies with
    | True =>
      Parse.readsThen
        [p := () => appliedTo self modes head]
        [j := applied => sectioned section applied]
        (readsAppliedTo self modes nested outside before head kept)
        (read applied appliedKept =>
          Parse.readsDone _ _ (rewrite List.appendNil read then keptSectioned section appliedKept))
    | False => Parse.readsDone _ _ (rewrite List.appendNil before then keptSectioned section kept)

theorem readsAppHead ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: NestedKept self)
    (outside: OutsideBraced self)
    (bases: BasesKept self) (section: Bool):
    Parse.ReadsIn GoodItems (() => appHead self modes section) Kept :=
  Parse.readsThen
    [p := () => atom self modes True]
    [j := head => appCalls self modes section head]
    (readsAtom self modes True (bases modes) (outside.below.records modes))
    (before head kept =>
      readsAfter0
        [p := () => startsAtom modes]
        [j := applies => appEnd self modes section head applies]
        (reads0StartsAtom modes)
        (applies => readsAppEnd self modes nested outside section before head applies kept))

theorem readsApp ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: NestedKept self)
    (outside: OutsideBraced self)
    (bases: BasesKept self):
    Parse.ReadsIn GoodItems (() => app self modes) Kept :=
  readsAfter0 [p := () => offset()] [j := start => appAt self modes start] reads0Offset (start =>
    readsAfter0
      [p := () => modes.at Dot && modes.sectionHead != Some start]
      [j := section => appHead self modes section]
      (reads0Then [p := () => modes.at Dot] (reads0At modes Dot) (dot => reads0Done _))
      (section => readsAppHead self modes nested outside bases section))

--| An argument read by `self`: `atom` with no application.
theorem readsAtomArgument ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (head: Bool)
    (outside: OutsideAtoms self)
    (bases: BasesKept self):
    Parse.ReadsIn GoodItems (() => atom self modes head) Kept :=
  readsAtom self modes head (bases modes) (outside.records modes)

-- Unary.

theorem readsUnaryNext ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: NestedKept self)
    (app: Parse.ReadsIn GoodItems (() => app self modes) Kept)
    (start: Parse.Mark Item) (item: Item) (later items: List Item)
    (shape: start.rest = [item, ..later])
    (fine: Parse.Fits Item GoodItems start.rest):
    Parse.ReadsAt start (() => unaryNext self modes item.kind items) Kept :=
  match negative: item.kind == Minus && negativeNumeral items with
    | True => app start fine
    | False =>
      match signed: item.kind == Minus || item.kind == Bang with
        | True =>
          let prefix := prefixItemOf item signed (goodHead fine shape)
          readsAtBumpRead shape fine (after tail fits =>
            Parse.readsAtThen (nested { modes, level = LevelUnary } after fits) (read operand after2 starts kept =>
              Parse.readsAtDone after2 _ _ (rewrite List.appendNil read then keptPrefix item read operand prefix kept)))
        | False => app start fine

theorem readsUnaryBar ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: NestedKept self)
    (outside: OutsideAtoms self)
    (app: Parse.ReadsIn GoodItems (() => app self modes) Kept)
    (start: Parse.Mark Item) (item: Item) (later: List Item) (bar: Bool)
    (shape: start.rest = [item, ..later])
    (fine: Parse.Fits Item GoodItems start.rest):
    Parse.ReadsAt start (() => unaryBar self modes item.kind bar) Kept :=
  match bar with
    | True =>
      readsAtBumpRead [k := word => clauseLambda self modes word None ClauseMatches] shape fine (after tail fits =>
        readsOutAfter [item] (outside.clauseLambdas modes item.leaf.word) after fits)
    | False =>
      readsAtAfter0
        [p := () => left()]
        [j := found => unaryNext self modes item.kind found]
        reads0Left
        fine
        (found after same fits =>
          readsUnaryNext self modes nested app after item later found (rewrite same then shape) fits)

theorem readsUnarySome ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: NestedKept self)
    (outside: OutsideAtoms self)
    (app: Parse.ReadsIn GoodItems (() => app self modes) Kept)
    (start: Parse.Mark Item) (item: Item) (later: List Item)
    (shape: start.rest = [item, ..later])
    (fine: Parse.Fits Item GoodItems start.rest):
    Parse.ReadsAt start (() => unarySome self modes item.kind) Kept :=
  match isMatch: item.kind == KwMatch with
    | True => readsAtBumpRead [k := keyword => matchExpr self modes keyword] shape fine (after tail fits =>
      readsOutAfter [item] (outside.matches modes item.leaf.word) after fits)
    | False =>
      readsAtAfter0
        [p := () => matchesBarAhead modes]
        [j := bar => unaryBar self modes item.kind bar]
        (reads0MatchesBarAhead modes)
        fine
        (bar after same fits =>
          readsUnaryBar self modes nested outside app after item later bar (rewrite same then shape) fits)

--| `unary`: a `-` or `!` and its operand, or an application; a `match` or clause lambda is outside the grammar.
theorem readsUnary ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: NestedKept self)
    (outside: OutsideAtoms self)
    (app: Parse.ReadsIn GoodItems (() => app self modes) Kept):
    Parse.ReadsIn GoodItems (() => unary self modes) Kept :=
  readsInPeeked modes
    (seen => unaryOn self modes seen) _
    (start fine stops => app start fine)
    (start item later shape fine stopped => readsUnarySome self modes nested outside app start item later shape fine)

-- Operator links, for the ladder's levels: a model for the second half.

--| An item a binary operator is read from: its kind is the one its text gives, the text is one of slice 1's binary
--| operators, and it is no comma.
def BinaryItem (item: Item): Prop :=
  binaryKind1 item.text = item.kind ∧ binaryText1 item.text = True ∧ (item.kind == Comma) = False

--| An operator link, read: the operator's item, a binary one, then what its operand read.
def LinkKept (read: List Item) (link: (Word, Expr)): Prop :=
  ∃ (operator: Item) (rest: List Item) => read = [operator, ..rest]
    ∧ BinaryItem operator
    ∧ link.fst = operator.leaf.word
    ∧ Kept rest link.snd

theorem keptInfix ∀ (operator: Item) [first rest: List Item] [left right: Expr]
    (binary: BinaryItem operator)
    (leftKept: Kept first left)
    (rightKept: Kept rest right):
    Kept (first ++ [operator, ..rest]) (Infix InfixBinary left operator.leaf.word right) :=
  grammar =>
    let (kindIs, text, code) := binary
    let (leftWords, leftKinds, leftWithin) := leftKept (Bool.andLeft grammar)
    let (rightWords, rightKinds, rightWithin) := rightKept (Bool.andRight grammar)
    (
      (rewrite itemWordsAppend first [operator, ..rest], itemWordsCons operator rest code, leftWords, rightWords),
      (rewrite itemKindsAppend first [operator, ..rest], leftKinds, rightKinds, kindIs),
      Bool.andIntro leftWithin (Bool.andIntro rightWithin text)
    )

--| Folding links to the left keeps the items in the order read.
theorem keptLeftNested ∀ [first: List Item] [head: Expr] (links: List (Word, Expr)) [rest: List Item]
    (kept: Kept first head)
    (rounds: Parse.Rounds (Parse.Maybe LinkKept) rest links):
    Kept (first ++ rest) (leftNested head links) :=
  match links, rounds with
    | [], none => rewrite none, List.appendNil first then kept
    | [(word, next), ..more], (
        taken,
        others,
        split,
        _,
        (operator, operand, single, binary, same, nextKept),
        restRounds
      ) =>
      let joined := keptInfix operator binary kept nextKept
      let folded := keptLeftNested more (rewrite <- same at joined then joined) restRounds
      rewrite split, single then (rewrite List.appendAssoc first [operator, ..operand] others at folded then folded)

--| Folding links to the right keeps the items in the order read.
theorem keptRightNested ∀ [first: List Item] [head: Expr] (links: List (Word, Expr)) [rest: List Item]
    (kept: Kept first head)
    (rounds: Parse.Rounds (Parse.Maybe LinkKept) rest links):
    Kept (first ++ rest) (rightNested head links) :=
  match links, rounds with
    | [], none => rewrite none, List.appendNil first then kept
    | [(word, next), ..more], (
        taken,
        others,
        split,
        _,
        (operator, operand, single, binary, same, nextKept),
        restRounds
      ) =>
      let below := keptRightNested more nextKept restRounds
      rewrite split, single, same then keptInfix operator binary kept below

--| One round of `operatorLinks`: the next item, if `takes` accepts it, and its operand; or nothing.
--|
--| Proof idea: from the mark, the item left decides the `match` and its guard; an operator `takes` accepts is good, so
--| it is a binary one (`binary`), and is bumped; then the operand is kept, so the link is that item and what the
--| operand read.
theorem readsOperatorStep ∀ (modes: Modes) (takes: Tok → Bool) (operand: () → {Parse Item} Expr)
    (binary: ∀ (item: Item) => takes item.kind = True → GoodItem item → BinaryItem item)
    (operandReads: Parse.ReadsIn GoodItems operand Kept):
    Parse.ReadsIn GoodItems
      (() =>
        match modes.peek with
          | Some kind if takes kind =>
            let operator := bump()
            let value := operand()
            Some (operator, value)
          | _ => None)
      (Parse.Maybe LinkKept) :=
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
                  (read word after starts (single, same) =>
                    Parse.readsAtThen
                      (operandReads after (Parse.Fits.after fine starts))
                      (more value later2 starts2 kept =>
                        Parse.readsAtDone later2
                          (Some (word, value)) _
                          (rewrite single then
                            (
                              item,
                              more ++ [],
                              byComputing,
                              binary item took (goodFirst fine),
                              same,
                              rewrite List.appendNil more then kept
                            )))))

--| A first operand and the links after it, folded to the left: how `mulExpr` and `addExpr` keep their items.
theorem readsLeftChain ∀ (modes: Modes) (takes: Tok → Bool) (first operand: () → {Parse Item} Expr)
    (binary: ∀ (item: Item) => takes item.kind = True → GoodItem item → BinaryItem item)
    (firstReads: Parse.ReadsIn GoodItems first Kept)
    (operandReads: Parse.ReadsIn GoodItems operand Kept):
    Parse.ReadsIn GoodItems (() => leftNested (first()) (operatorLinks modes takes operand)) Kept :=
  Parse.readsThen firstReads (r1 head kept =>
    Parse.readsThen
      (Parse.readsLoop _ _ (readsOperatorStep modes takes operand binary operandReads))
      (r2 links rounds => Parse.readsDone _ _ (rewrite List.appendNil r2 then keptLeftNested links kept rounds)))

theorem mulSpells ∀ (kind: Tok) (text: Text)
    (took: (kind == Star || kind == Slash || kind == Percent) = True)
    (good: kind.within1 = True → Spells kind text):
    binaryKind1 text = kind ∧ binaryText1 text = True ∧ (kind == Comma) = False :=
  match kind, took, good with
    | Star, took, good => rewrite good byComputing then (byComputing, byComputing, byComputing)
    | Slash, took, good => rewrite good byComputing then (byComputing, byComputing, byComputing)
    | Percent, took, good => rewrite good byComputing then (byComputing, byComputing, byComputing)

theorem addSpells ∀ (kind: Tok) (text: Text)
    (took: (kind == Plus || kind == Minus) = True)
    (good: kind.within1 = True → Spells kind text):
    binaryKind1 text = kind ∧ binaryText1 text = True ∧ (kind == Comma) = False :=
  match kind, took, good with
    | Plus, took, good => rewrite good byComputing then (byComputing, byComputing, byComputing)
    | Minus, took, good => rewrite good byComputing then (byComputing, byComputing, byComputing)

theorem appendSpells ∀ (kind: Tok) (text: Text)
    (took: (kind == PlusPlus) = True)
    (good: kind.within1 = True → Spells kind text):
    binaryKind1 text = kind ∧ binaryText1 text = True ∧ (kind == Comma) = False :=
  match kind, took, good with
    | PlusPlus, took, good => rewrite good byComputing then (byComputing, byComputing, byComputing)

--| `mul_expr`, from what `unary` keeps: a ladder level, proved as the second half proves the others.
theorem readsMulExpr ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (unaryReads: Parse.ReadsIn GoodItems (() => unary self modes) Kept):
    Parse.ReadsIn GoodItems (() => mulExpr self modes) Kept :=
  readsLeftChain modes
    (kind => kind == Star || kind == Slash || kind == Percent)
    (() => unary self modes)
    (() => unary self modes)
    (operator took good => mulSpells operator.kind operator.text took good)
    unaryReads
    unaryReads

--| `add_expr`, from what `mul_expr` keeps.
theorem readsAddExpr ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (mulReads: Parse.ReadsIn GoodItems (() => mulExpr self modes) Kept):
    Parse.ReadsIn GoodItems (() => addExpr self modes) Kept :=
  readsLeftChain modes
    (kind => kind == Plus || kind == Minus)
    (() => mulExpr self modes)
    (() => mulExpr self modes)
    (operator took good => addSpells operator.kind operator.text took good)
    mulReads
    mulReads

--| `append_expr`, from what `add_expr` keeps: `++`s nest to the right.
theorem readsAppendExpr ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (addReads: Parse.ReadsIn GoodItems (() => addExpr self modes) Kept):
    Parse.ReadsIn GoodItems (() => appendExpr self modes) Kept :=
  Parse.readsThen addReads (r1 head kept =>
    Parse.readsThen
      (Parse.readsLoop _ _
        (readsOperatorStep modes
          (kind => kind == PlusPlus)
          (() => addExpr self modes)
          (operator took good => appendSpells operator.kind operator.text took good)
          addReads))
      (r2 links rounds => Parse.readsDone _ _ (rewrite List.appendNil r2 then keptRightNested links kept rounds)))
