--| `parseCarries1`'s walk of the parser (docs/reviews/SW-4018-parser-statements.md §2.1, ticket A): every parser
--| function on slice 1's path reads its tree's words from the items it read, commas left out. The spec is `Carried`,
--| a `Parse.ReadsIn` spec where `ParseWalk`'s is a `Parse.Gives` one, so it can speak of what was read; a tree outside
--| the slice makes it empty, so each `Out` fact of `ParseWalk` gives its lemma by `Parse.readsWeaken` (`readsOut`).
--|
--| This file has the spec, its combinators, the atoms, brackets and comma lists, arguments and applications, `unary`,
--| the operator links and the ladder from `mul_expr` to `append_expr`, and the recursion's knot (`bothExpressionAt`),
--| which takes the levels above `append_expr` as one hypothesis (`LadderCarries`) for the second half (SW-4020).

namespace Syntax.ParseCarries
import Std (Bool, DecEq, Eq, List, Nat, Option, Pair, Parse, Result, Text)
import Syntax (..)
import Fmt (..)
import Syntax.Proofs (..)
import Syntax.ParseProofs (..)
import Syntax.ParseWalk (..)

-- The spec.

--| The words the tree keeps of some leaves: every token's but a comma's, in order, each with its comments.
def codeWords (leaves: List Leaf): List Word := leaves.filter (leaf => leaf.kind != Comma) |> .map Leaf.word

--| The words of the items a parser read.
def itemWords (read: List Item): List Word := codeWords (read.map Item.leaf)

--| What a parser function gives, read as words: a tree in the slice has the words of the items read for it. A tree
--| outside the slice says nothing, as for `Parsed1`.
def Carried (read: List Item) (expr: Expr): Prop := expr.within1 = True → expr.words = itemWords read

--| `self` carries its items at every goal.
def NestedCarries (self: Goal → {Parse Item} Expr): Prop :=
  ∀ (goal: Goal) => Parse.ReadsIn GoodItems (() => self goal) Carried

-- Words of items.

theorem itemWordsNil: itemWords [] = [] := byComputing

theorem itemWordsAppend ∀ (first rest: List Item): itemWords (first ++ rest) = itemWords first ++ itemWords rest :=
  calc itemWords (first ++ rest)
    _ = codeWords (first.map Item.leaf ++ rest.map Item.leaf) := rewrite List.mapAppend first rest Item.leaf
    _ = itemWords first ++ itemWords rest :=
      rewrite List.filterAppend (first.map Item.leaf) (rest.map Item.leaf) (leaf => leaf.kind != Comma),
          List.mapAppend
            (List.filter (first.map Item.leaf) (leaf => leaf.kind != Comma))
            (List.filter (rest.map Item.leaf) (leaf => leaf.kind != Comma))
            Leaf.word

--| An item that is no comma gives its word.
theorem itemWordsCode ∀ (item: Item) (code: (item.kind == Comma) = False): itemWords [item] = [item.leaf.word] :=
  let kept: (item.leaf.kind == Comma) = False := code
  calc itemWords [item]
    _ = (List.filterStep item.leaf [] !(item.leaf.kind == Comma)).map Leaf.word := byComputing
    _ = [item.leaf.word] := rewrite kept

--| A comma gives no word.
theorem itemWordsComma ∀ (item: Item) (comma: item.kind = Comma): itemWords [item] = [] :=
  let dropped: (item.leaf.kind == Comma) = True := rewrite comma
  calc itemWords [item]
    _ = (List.filterStep item.leaf [] !(item.leaf.kind == Comma)).map Leaf.word := byComputing
    _ = [] := rewrite dropped

-- Combinators.

--| A tree outside the slice carries any items.
theorem carriedOut ∀ (read: List Item) [expr: Expr] (out: Out expr): Carried read expr := within =>
  (Bool.falseNotTrue (rewrite out at within)).impossible

--| The lift of `ParseWalk`'s facts for the parsers outside the slice: a parser whose trees are all outside the slice
--| carries its items.
theorem readsOut ∀ [p: () → {Parse Item} Expr]
    (gives: Parse.Gives GoodItems p Out):
    Parse.ReadsIn GoodItems p Carried :=
  Parse.readsWeaken gives (read value out => carriedOut read out)

--| A parser that never succeeds reads as any spec says.
theorem readsNever ∀ [p: () → {Parse Item} a] [spec: List Item → a → Prop]
    (never: ∀ (holds: a → Prop) => Parse.Gives GoodItems p holds):
    Parse.ReadsIn GoodItems p spec :=
  Parse.readsWeaken (never (value => ∀ (read: List Item) => spec read value)) (read value all => all read)

theorem readsFail ∀ (modes: Modes) (what: Text) [spec: List Item → a → Prop]:
    Parse.ReadsIn GoodItems (() => modes.fail what) spec :=
  readsNever (holds => givesFail modes what [holds := holds])

theorem readsFailName ∀ (modes: Modes) (what: Text) [spec: List Item → a → Prop]:
    Parse.ReadsIn GoodItems (() => modes.failName what) spec :=
  readsNever (holds => givesFailName modes what [holds := holds])

--| A look-ahead, then `j` of what it found: `j` reads all that is read.
theorem readsAfter0 ∀ [p: () → {Parse Item} a] [j: a → {Parse Item} b] [spec: List Item → b → Prop]
    (first: Reads0 p)
    (rest: ∀ (value: a) => Parse.ReadsIn GoodItems (() => j value) spec):
    Parse.ReadsIn GoodItems (() => j (p())) spec :=
  start fine => readsAtAfter0 first fine (value after same fits => rest value after fits)

--| `bump` then `k` of its word, from a mark whose next item is `item`: `item` is read, then what `k` reads from after
--| it.
theorem readsAtBumpRead ∀ [start: Parse.Mark Item] [item: Item] [later: List Item]
    [k: Word → {Parse Item} b] [spec: List Item → b → Prop]
    (shape: start.rest = [item, ..later])
    (fine: Parse.Fits Item GoodItems start.rest)
    (rest: ∀ (after: Parse.Mark Item) => after.rest = later
      → Parse.Fits Item GoodItems after.rest
      → Parse.ReadsAt after (() => k item.leaf.word) (read value => spec ([item] ++ read) value)):
    Parse.ReadsAt start (() => k (bump())) spec :=
  Parse.readsAtThen (readsAtBump shape) (read word after starts (Both single same) =>
    let joined: [item, ..later] = [item, ..after.rest] := Eq.trans shape.flipped (rewrite single at starts then starts)
    rewrite same, single then
      rest after (List.consInjective item later after.rest joined).flipped (Parse.Fits.after fine starts))

--| One item of the kind `wanted`, read, and its word.
def OneOf (wanted: Tok) (read: List Item) (word: Word): Prop :=
  ∃ (item: Item) => read = [item] ∧ item.kind = wanted ∧ word = item.leaf.word

--| The word of one item that is no comma is the words of what was read.
theorem oneOfWords ∀ [wanted: Tok] [read: List Item] [word: Word]
    (one: OneOf wanted read word)
    (code: (wanted == Comma) = False):
    itemWords read = [word] :=
  let (item, single, kind, same) := one
  rewrite single, same then itemWordsCode item (rewrite kind then code)

--| `expect` reads one item of the kind it was asked for.
theorem readsExpect ∀ (modes: Modes) (wanted: Tok) (what: Text):
    Parse.ReadsIn GoodItems (() => modes.expect wanted what) (OneOf wanted) :=
  readsInPeeked modes
    (seen => modes.expectOn wanted what seen) _
    (start fine stops => readsFail modes what start fine)
    (start item later shape fine stopped =>
      match took: isSome wanted (Some item.kind) with
        | False => readsFail modes what start fine
        | True =>
          Parse.readsAtWeaken (readsAtBump shape) (read word (single, same) => (item, single, DecEq.sound took, same)))

-- What follows an atom: a record's fields, calls and field accesses.

--| `value` is `target`, read from nothing, or a tree outside the slice.
def SameOrOut (target: Expr) (read: List Item) (value: Expr): Prop := (read = [] ∧ value = target) ∨ Out value

theorem sameOrOutThen ∀ [target middle value: Expr] [first second: List Item]
    (before: SameOrOut target first middle)
    (after: SameOrOut middle second value):
    SameOrOut target (first ++ second) value :=
  match after with
    | Inr out => Inr out
    | Inl (empty, same) =>
      match before with
        | Inl (emptyFirst, sameFirst) => Inl (rewrite emptyFirst, empty then byComputing, rewrite same, sameFirst)
        | Inr out => Inr (rewrite same then out)

--| A tree carried, then kept or replaced by one outside the slice.
theorem carriedSame ∀ [base value: Expr] [first second: List Item]
    (carried: Carried first base)
    (kept: SameOrOut base second value):
    Carried (first ++ second) value :=
  match kept with
    | Inr out => carriedOut _ out
    | Inl (empty, same) => rewrite empty, same, List.appendNil first then carried

theorem readsSuffixCalled ∀ (target: Expr) (callable paren: Bool):
    Parse.ReadsIn GoodItems (() => suffixCalled target callable paren) (SameOrOut target) :=
  readsAfter0 [p := () => left()] [j := seen => suffixCalledOn target callable paren seen] reads0Left (seen =>
    match unitCall seen with
      | False => Parse.readsDone _ _ (Inl (byComputing, byComputing))
      | True =>
        match callable || (paren && callableParen target) with
          | False => Parse.readsDone _ _ (Inl (byComputing, byComputing))
          | True => Parse.readsThen givesBump (r1 open _ =>
            Parse.readsThen givesBump (r2 close _ => Parse.readsDone _ _ (Inr (Bool.andFalse target.within1)))))

--| `suffixes` after the call: a field access starts another round on a tree outside the slice, and nothing else is read.
theorem readsSuffixesOn ∀ (more: Nat) (modes: Modes) (called: Expr) (paren: Bool) (items: List Item)
    (next: ∀ (target: Expr) (callable: Bool) => Out target
      → Parse.ReadsIn GoodItems (() => suffixes more modes target callable paren) (read value => Out value)):
    Parse.ReadsIn GoodItems (() => suffixesOn more modes called paren items) (SameOrOut called) :=
  match items with
    | [dot, field, ..later] =>
      match dot.kind == Dot && !modes.stops dot && !sectionAt [dot, field, ..later] with
        | False => Parse.readsDone _ _ (Inl (byComputing, byComputing))
        | True =>
          match !((field.kind == Lower || field.kind == Upper) && !isQualified field && !modes.stops field) with
            | True => Parse.readsFatal _ _
            | False =>
              match !dot.glued || !field.glued with
                | True => Parse.readsFatal _ _
                | False => Parse.readsThen givesBump (r1 dotLeaf _ =>
                  Parse.readsThen givesBump (r2 name _ =>
                    Parse.readsWeaken
                      (next (FieldAccess (Some called) dotLeaf name) True byComputing)
                      (read value out => Inr out)))
    | [dot] =>
      match dot.kind == Dot && !modes.stops dot with
        | True => Parse.readsFatal _ _
        | False => Parse.readsDone _ _ (Inl (byComputing, byComputing))
    | other => Parse.readsDone _ _ (Inl (byComputing, byComputing))

--| `suffixes` of a tree outside the slice gives one outside the slice.
theorem readsSuffixesOut ∀ (fuel: Nat) (modes: Modes) (target: Expr) (callable paren: Bool)
    (out: Out target):
    Parse.ReadsIn GoodItems (() => suffixes fuel modes target callable paren) (read value => Out value) :=
  Parse.readsWeaken (givesSuffixes Out (tree out => out) fuel modes target callable paren out) (read value out => out)

--| `suffixes` keeps the tree, reading nothing, or makes one outside the slice.
theorem readsSuffixes ∀ (fuel: Nat) (modes: Modes) (target: Expr) (callable paren: Bool):
    Parse.ReadsIn GoodItems (() => suffixes fuel modes target callable paren) (SameOrOut target) :=
  match fuel with
    | Zero => Parse.readsDone _ _ (Inl (byComputing, byComputing))
    | Succ more => Parse.readsThen (readsSuffixCalled target callable paren) (r1 called calledKept =>
      Parse.readsThen [first := read found => read = []] reads0Left (r2 seen empty =>
        Parse.readsWeaken
          (readsSuffixesOn more modes called paren seen (later again out =>
            readsSuffixesOut more modes later again paren out))
          (r3 value kept => rewrite empty then sameOrOutThen calledKept kept)))

theorem readsAtomRecord ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (head upper: Bool)
    (base: Expr) (callable: Bool)
    (records: Parse.Gives GoodItems (() => recordExpr self modes) Out):
    Parse.ReadsIn GoodItems (() => atomRecord self modes head upper base callable) (read pair =>
      SameOrOut base read pair.fst) :=
  match upper with
    | False => Parse.readsDone _ _ (Inl (byComputing, byComputing))
    | True =>
      match head with
        | False => Parse.readsDone _ _ (Inl (byComputing, byComputing))
        | True => Parse.readsThen [first := read found => read = []] (reads0At modes LBrace) (r1 found empty =>
          match found with
            | True =>
              Parse.readsThen
                [p := () => recordExpr self modes]
                [j := fields => (CtorFields base fields, False)]
                records
                (r2 fields _ => Parse.readsDone (CtorFields base fields, False) _ (Inr byComputing))
            | False => Parse.readsDone _ _ (Inl (rewrite empty then byComputing, byComputing)))

theorem readsAtomAfter ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (head: Bool) (first: Option Tok) (base: Expr)
    (records: Parse.Gives GoodItems (() => recordExpr self modes) Out):
    Parse.ReadsIn GoodItems (() => atomAfter self modes head first base) (SameOrOut base) :=
  Parse.readsThen
    (readsAtomRecord self modes head
      (isSome Upper first)
      base
      (isSome Lower first || isSome Upper first || isSome Dot first)
      records)
    (r1 pair pairKept =>
      match pair with
        | (based, callable) => Parse.readsThen Parse.readsMark (r2 here empty =>
          Parse.readsThen (readsSuffixes (here.left + 1) modes based callable (isSome LParen first)) (r3 result kept =>
            match isSome Dot first && !head with
              | True => Parse.readsDone _ _ (Inr byComputing)
              | False => Parse.readsDone _ _ (rewrite empty, List.appendNil r3 then sameOrOutThen pairKept kept))))

--| `atom`, from what `atom_base` carries: what follows the base keeps it or leaves the slice.
theorem readsAtom ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (head: Bool)
    (bases: Parse.ReadsIn GoodItems (() => atomBase self modes) Carried)
    (records: Parse.Gives GoodItems (() => recordExpr self modes) Out):
    Parse.ReadsIn GoodItems (() => atom self modes head) Carried :=
  readsAfter0
    [p := () => modes.peek]
    [j := first => atomAfter self modes head first (atomBase self modes)]
    (reads0Peek modes)
    (first =>
      Parse.readsThen
        [p := () => atomBase self modes]
        [j := base => atomAfter self modes head first base]
        bases
        (r1 base carried =>
          Parse.readsWeaken (readsAtomAfter self modes head first base records) (r2 value kept =>
            carriedSame carried kept)))

-- The atoms.

theorem itemWordsCons ∀ (item: Item) (rest: List Item)
    (code: (item.kind == Comma) = False):
    itemWords [item, ..rest] = [item.leaf.word, ..itemWords rest] :=
  rewrite itemWordsAppend [item] rest, itemWordsCode item code

--| A kind known to be one that is no comma.
theorem codeAs ∀ [kind wanted: Tok] (is: kind = wanted) (code: (wanted == Comma) = False): (kind == Comma) = False :=
  rewrite is then code

theorem wordCode ∀ (kind: Tok) (word: kind.wordWithin1 = True): (kind == Comma) = False := match kind, word with
  | Lower, word => byComputing
  | Upper, word => byComputing
  | Num, word => byComputing
  | Float, word => byComputing
  | other, word => (Bool.falseNotTrue word).impossible

theorem carriedAtom ∀ (item: Item): Carried [item] (Atom item.kind item.leaf.word) := within =>
  rewrite itemWordsCode item (wordCode item.kind (Bool.andLeft within))

--| A name with a comment, read as an atom: `carriedAtom`'s hypothesis can be met.
def nameItem: Item := {
  leaf = {
    token = { kind = Lower, text = "a", column = 0, lineStart = True },
    trivia = { leading = [], blankLines = 0, trailing = Some { text = "-- note", column = 2, blankLines = 0 } }
  },
  glued = False,
  afterOperand = False,
  afterDot = False,
  index = 0,
  depth = 0,
  lineIndent = 0
}

theorem carriedAtomExample: (Atom Lower nameItem.leaf.word).words = itemWords [nameItem] :=
  carriedAtom nameItem byComputing

theorem carriedPrefix ∀ (item: Item) (read: List Item) (operand: Expr)
    (code: (item.kind == Comma) = False)
    (carried: Carried read operand):
    Carried [item, ..read] (Prefix item.leaf.word operand) :=
  within => rewrite itemWordsCons item read code, carried within

theorem readsWordAtom ∀ (start: Parse.Mark Item) (item: Item) (later: List Item)
    (shape: start.rest = [item, ..later])
    (fine: Parse.Fits Item GoodItems start.rest):
    Parse.ReadsAt start (() => wordAtom item.kind) Carried :=
  readsAtBumpRead [k := word => Atom item.kind word] shape fine (after tail fits =>
    Parse.readsAtDone after _ _ (carriedAtom item))

theorem readsPrefixAtom ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: NestedCarries self)
    (negates: Bool) (start: Parse.Mark Item) (item: Item) (later: List Item)
    (shape: start.rest = [item, ..later])
    (code: (item.kind == Comma) = False)
    (fine: Parse.Fits Item GoodItems start.rest):
    Parse.ReadsAt start (() => prefixAtom self modes negates) Carried :=
  match negates with
    | True => readsAtBumpRead shape fine (after tail fits =>
      Parse.readsAtThen (nested { modes, level = LevelArgument } after fits) (read operand after2 starts carried =>
        Parse.readsAtDone after2 _ _ (rewrite List.appendNil read then carriedPrefix item read operand code carried)))
    | False => readsFailName modes _ start fine

theorem readsNegativeNumber ∀ (start: Parse.Mark Item) (minus number: Item) (later: List Item)
    (shape: start.rest = [minus, number, ..later])
    (isMinus: minus.kind = Minus)
    (fine: Parse.Fits Item GoodItems start.rest):
    Parse.ReadsAt start (() => negativeNumber()) Carried :=
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
              (carriedPrefix minus
                [number]
                (Atom number.kind number.leaf.word)
                (codeAs isMinus byComputing)
                (carriedAtom number)))))

theorem readsNegativeAtomOn ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: NestedCarries self)
    (items: List Item) (start: Parse.Mark Item) (item: Item) (later: List Item)
    (shape: start.rest = [item, ..later])
    (found: items = start.rest)
    (isMinus: item.kind = Minus)
    (fine: Parse.Fits Item GoodItems start.rest):
    Parse.ReadsAt start (() => negativeAtomOn self modes items) Carried :=
  match negative: negativeNumeral items with
    | True =>
      let (minus, number, rest, split, minusKind, numberKind) := negativeNumeralKinds items negative
      readsNegativeNumber start minus number rest (rewrite <- found then split) minusKind fine
    | False =>
      readsPrefixAtom self modes nested (argumentMinus items) start item later shape (codeAs isMinus byComputing) fine

theorem readsNegativeAtom ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: NestedCarries self)
    (start: Parse.Mark Item) (item: Item) (later: List Item)
    (shape: start.rest = [item, ..later])
    (isMinus: item.kind = Minus)
    (fine: Parse.Fits Item GoodItems start.rest):
    Parse.ReadsAt start (() => negativeAtom self modes) Carried :=
  readsAtAfterLeft [j := items => negativeAtomOn self modes items] fine (after same fits =>
    readsNegativeAtomOn self modes nested start.rest after item later
      (rewrite same then shape)
      same.flipped
      isMinus
      fits)

-- Comma lists.

--| Trees in the slice, all of them, have the words of the items read for them.
def ItemsCarried (read: List Item) (items: List Expr): Prop :=
  allWithin1 items = True → itemsWords items = itemWords read

--| What a comma list gave after the trees it already had, `prior`: more trees, carried by what it read (its commas
--| giving no words).
def ListCarried (prior: List Expr) (read: List Item) (pair: (List Expr, Bool)): Prop :=
  ∃ (more: List Expr) => pair.fst = prior ++ more ∧ ItemsCarried read more

theorem itemsCarriedNil: ItemsCarried [] [] := within => byComputing

theorem itemsCarriedComma ∀ (comma: Item) (isComma: comma.kind = Comma): ItemsCarried [comma] [] := within =>
  rewrite itemWordsComma comma isComma

theorem itemsCarriedCons ∀ [first rest: List Item] [value: Expr] [more: List Expr]
    (carried: Carried first value)
    (others: ItemsCarried rest more):
    ItemsCarried (first ++ rest) [value, ..more] :=
  within => rewrite itemWordsAppend first rest, carried (Bool.andLeft within), others (Bool.andRight within)

theorem itemWordsAfterComma ∀ (comma: Item) (rest: List Item)
    (isComma: comma.kind = Comma):
    itemWords [comma, ..rest] = itemWords rest :=
  rewrite itemWordsAppend [comma] rest, itemWordsComma comma isComma

--| A comma, then a tree and the rest of the list.
theorem listCarriedStep ∀ [prior: List Expr] [value: Expr] [comma: Item]
    [first rest: List Item] [pair: (List Expr, Bool)]
    (isComma: comma.kind = Comma)
    (carried: Carried first value)
    (listed: ListCarried (prior ++ [value]) rest pair):
    ListCarried prior [comma, ..first ++ rest] pair :=
  let (more, split, items) := listed
  (
    [value, ..more],
    rewrite split then List.appendAssoc prior [value] more,
    within => rewrite itemWordsAfterComma comma (first ++ rest) isComma then itemsCarriedCons carried items within
  )

--| The items of a comma list after the first: each comma is read and gives no word, and each item is carried.
theorem readsCommaListFrom ∀ (modes: Modes) (ends: Nat → {Parse Item} Bool) (next: () → {Parse Item} Expr)
    (endsReads: ∀ (count: Nat) => Reads0 (() => ends count))
    (nextReads: Parse.ReadsIn GoodItems next Carried)
    (fuel count: Nat) (current: Expr) (found: List Expr):
    Parse.ReadsIn GoodItems
      (() => commaListFrom fuel modes ends next count current found)
      (ListCarried [current, ..found].reverse) :=
  readsInPeeked modes
    (seen => commaListOn fuel modes ends next count current found seen) _
    (start fine stops =>
      match fuel with
        | Zero => Parse.readsAtDone _ _ _ ([], (List.appendNil _).flipped, itemsCarriedNil)
        | Succ more => Parse.readsAtDone _ _ _ ([], (List.appendNil _).flipped, itemsCarriedNil))
    (start item later shape fine stopped =>
      match fuel with
        | Zero => Parse.readsAtDone _ _ _ ([], (List.appendNil _).flipped, itemsCarriedNil)
        | Succ more =>
          match isComma: item.kind == Comma with
            | False => Parse.readsAtDone _ _ _ ([], (List.appendNil _).flipped, itemsCarriedNil)
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
                        (rewrite empty then itemsCarriedComma item (DecEq.sound isComma))
                      )
                      | False =>
                        let fits2 := Parse.Fits.after fits starts1
                        Parse.readsAtThen (nextReads after2 fits2) (r2 value after3 starts2 carried =>
                          Parse.readsAtWeaken
                            (readsCommaListFrom modes ends next endsReads nextReads more
                              (count + 1)
                              value
                              [current, ..found]
                              after3
                              (Parse.Fits.after fits2 starts2))
                            (r3 pair listed =>
                              rewrite empty then
                                listCarriedStep
                                  (DecEq.sound isComma)
                                  carried
                                  (rewrite <- List.reverseCons value [current, ..found] then listed))))))

-- Brackets.

theorem carriedParen ∀ (open: Item) (inside rest: List Item) (inner: Expr) (close: Word)
    (code: (open.kind == Comma) = False)
    (carried: Carried inside inner)
    (closeWords: itemWords rest = [close]):
    Carried [open, ..inside ++ rest] (Paren open.leaf.word inner close) :=
  within => rewrite itemWordsCons open (inside ++ rest) code, itemWordsAppend inside rest, carried within, closeWords

theorem carriedTuple ∀ (open: Item) (inside rest: List Item) (items: List Expr) (trailing: Bool) (close: Word)
    (code: (open.kind == Comma) = False)
    (carried: ItemsCarried inside items)
    (closeWords: itemWords rest = [close]):
    Carried [open, ..inside ++ rest] (Tuple open.leaf.word items trailing close) :=
  within => rewrite itemWordsCons open (inside ++ rest) code, itemWordsAppend inside rest, carried within, closeWords

theorem carriedList ∀ (open: Item) (inside rest: List Item) (items: List Expr) (trailing: Bool) (close: Word)
    (code: (open.kind == Comma) = False)
    (carried: ItemsCarried inside items)
    (closeWords: itemWords rest = [close]):
    Carried [open, ..inside ++ rest] (ListOf open.leaf.word items trailing close) :=
  within => rewrite itemWordsCons open (inside ++ rest) code, itemWordsAppend inside rest, carried within, closeWords

--| `)` after the first tree in brackets.
theorem readsParenClose ∀ (inner: Modes) (open: Item) (inside: List Item) (first: Expr)
    (code: (open.kind == Comma) = False)
    (carried: Carried inside first):
    Parse.ReadsIn GoodItems (() => parenClose inner open.leaf.word first) (read value =>
      Carried [open, ..inside ++ read] value) :=
  Parse.readsThen (readsExpect inner RParen "`)`") (rc close one =>
    Parse.readsDone _ _
      (rewrite List.appendNil rc then
        carriedParen open inside rc first close code carried (oneOfWords one byComputing)))

theorem readsTupleClose ∀ (modes: Modes): Parse.ReadsIn GoodItems (() => tupleClose modes) (OneOf RParen) :=
  readsAfter0
    [p := () => modes.at Colon]
    [j := annotated => tupleCloseAfter modes annotated]
    (reads0At modes Colon)
    (annotated =>
      match annotated with
        | True => Parse.readsFatal _ _
        | False => readsExpect modes RParen _)

theorem readsTupleEnds ∀ (inner: Modes) (count: Nat): Reads0 (() => tupleEnds inner count) :=
  reads0Then [p := () => inner.at RParen] (reads0At inner RParen) (found => reads0Done _)

--| A tuple's tail, from the comma after its first tree: the comma, the second tree, the rest of the list and `)`.
theorem readsTupleRest ∀ (self: Goal → {Parse Item} Expr) (inner: Modes) (open: Item) (inside: List Item) (first: Expr)
    (nested: NestedCarries self)
    (code: (open.kind == Comma) = False)
    (carried: Carried inside first)
    (start: Parse.Mark Item) (comma: Item) (later: List Item)
    (shape: start.rest = [comma, ..later])
    (isComma: comma.kind = Comma)
    (fine: Parse.Fits Item GoodItems start.rest):
    Parse.ReadsAt start (() => tupleRest self inner open.leaf.word first) (read value =>
      Carried [open, ..inside ++ read] value) :=
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
            (r2 second after3 starts2 carried2 =>
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
                          let tail: ItemsCarried [comma, ..r2 ++ r3] [second, ..more] := within =>
                            rewrite itemWordsAfterComma comma (r2 ++ r3) isComma then
                              itemsCarriedCons carried2 others within
                          let all: ItemsCarried (inside ++ [comma, ..r2 ++ r3]) items :=
                            rewrite split then itemsCarriedCons carried tail
                          let whole :=
                            carriedTuple open
                              (inside ++ [comma, ..r2 ++ r3])
                              rc
                              items
                              trailing
                              close
                              code
                              all
                              (oneOfWords one byComputing)
                          Parse.readsAtDone after5 _ _
                            (rewrite List.appendNil rc then
                              rewrite List.appendAssoc inside [comma, ..r2 ++ r3] rc,
                                  List.appendAssoc r2 r3 rc at whole then
                                whole))))))

--| `readsOut` at a spec about more than what this parser read: a tree outside the slice still says nothing.
theorem readsOutAfter ∀ (before: List Item) [p: () → {Parse Item} Expr]
    (gives: Parse.Gives GoodItems p Out):
    Parse.ReadsIn GoodItems p (read value => Carried (before ++ read) value) :=
  Parse.readsWeaken gives (read value out => carriedOut _ out)

theorem readsBracketedFirst ∀ (self: Goal → {Parse Item} Expr) (inner: Modes) (open: Item)
    (inside: List Item) (first: Expr)
    (nested: NestedCarries self)
    (outside: OutsideAtoms self)
    (code: (open.kind == Comma) = False)
    (carried: Carried inside first):
    Parse.ReadsIn GoodItems (() => bracketedFirst self inner open.leaf.word first) (read value =>
      Carried [open, ..inside ++ read] value) :=
  readsInPeeked inner
    (seen => bracketedAfter self inner open.leaf.word first seen) _
    (start fine stops => readsParenClose inner open inside first code carried start fine)
    (start item later shape fine stopped =>
      match isComma: item.kind == Comma with
        | True =>
          readsTupleRest self inner open inside first nested code carried start item later shape
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
            | False => readsParenClose inner open inside first code carried start fine)

theorem readsBracketedTail ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (open: Item)
    (nested: NestedCarries self)
    (outside: OutsideAtoms self)
    (code: (open.kind == Comma) = False):
    Parse.ReadsIn GoodItems (() => bracketedTail self modes open.leaf.word) (read value =>
      Carried [open, ..read] value) :=
  Parse.readsThen
    [p := () => full self modes.inBrackets]
    [j := first => bracketedFirst self modes.inBrackets open.leaf.word first]
    (nested { modes = modes.inBrackets, level = LevelFull })
    (inside first carried => readsBracketedFirst self modes.inBrackets open inside first nested outside code carried)

theorem readsBracketed ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: NestedCarries self)
    (outside: OutsideAtoms self)
    (start: Parse.Mark Item) (item: Item) (later: List Item)
    (shape: start.rest = [item, ..later])
    (isParen: item.kind = LParen)
    (fine: Parse.Fits Item GoodItems start.rest):
    Parse.ReadsAt start (() => bracketed self modes) Carried :=
  readsAtBumpRead [k := open => bracketedTail self modes open] shape fine (after tail fits =>
    readsBracketedTail self modes item nested outside (codeAs isParen byComputing) after fits)

theorem readsParenRest ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: NestedCarries self)
    (outside: OutsideAtoms self)
    (items: List Item) (start: Parse.Mark Item) (item: Item) (later: List Item)
    (shape: start.rest = [item, ..later])
    (isParen: item.kind = LParen)
    (fine: Parse.Fits Item GoodItems start.rest):
    Parse.ReadsAt start (() => parenRest self modes items) Carried :=
  match rightOperator items with
    | Some inside =>
      readsOut [p := () => rightSection self modes inside] (outside.rightSections modes inside) start fine
    | None => readsBracketed self modes nested outside start item later shape isParen fine

theorem readsParenOn ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: NestedCarries self)
    (outside: OutsideAtoms self)
    (second third: Option Tok) (start: Parse.Mark Item) (item: Item) (later: List Item)
    (shape: start.rest = [item, ..later])
    (isParen: item.kind = LParen)
    (fine: Parse.Fits Item GoodItems start.rest):
    Parse.ReadsAt start (() => parenOn self modes second third) Carried :=
  match parenOutside second third with
    | True =>
      readsOut [p := () => parenOther self modes second third] (outside.parenOthers modes second third) start fine
    | False => readsAtAfterLeft [j := items => parenRest self modes items] fine (after same fits =>
      readsParenRest self modes nested outside start.rest after item later (rewrite same then shape) isParen fits)

theorem readsParenAtom ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: NestedCarries self)
    (outside: OutsideAtoms self)
    (start: Parse.Mark Item) (item: Item) (later: List Item)
    (shape: start.rest = [item, ..later])
    (isParen: item.kind = LParen)
    (fine: Parse.Fits Item GoodItems start.rest):
    Parse.ReadsAt start (() => parenAtom self modes) Carried :=
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

theorem readsListItem ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: NestedCarries self):
    Parse.ReadsIn GoodItems (() => listItem self modes) Carried :=
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
                        (r2 value _ => Parse.readsDone _ _ (carriedOut _ byComputing))))
        | False => nested { modes, level = LevelFull })

theorem readsListItemsEnd ∀ (self: Goal → {Parse Item} Expr) (inner: Modes) (open: Item) (inside: List Item)
    (items: List Expr) (trailing: Bool)
    (code: (open.kind == Comma) = False)
    (carried: ItemsCarried inside items):
    Parse.ReadsIn GoodItems (() => listItemsEnd self inner open.leaf.word (items, trailing)) (read value =>
      Carried [open, ..inside ++ read] value) :=
  Parse.readsThen (readsExpect inner RBracket "`,` or `]`") (rc close one =>
    Parse.readsDone _ _
      (rewrite List.appendNil rc then
        carriedList open inside rc items trailing close code carried (oneOfWords one byComputing)))

theorem readsListItemsFrom ∀ (self: Goal → {Parse Item} Expr) (inner: Modes) (open: Item)
    (inside: List Item) (first: Expr)
    (nested: NestedCarries self)
    (code: (open.kind == Comma) = False)
    (carried: Carried inside first):
    Parse.ReadsIn GoodItems (() => listItemsFrom self inner open.leaf.word first) (read value =>
      Carried [open, ..inside ++ read] value) :=
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
                  code
                  (rewrite split then itemsCarriedCons carried others))
                (rc value whole => rewrite empty then (rewrite List.appendAssoc inside r1 rc at whole then whole))))

theorem readsListItems ∀ (self: Goal → {Parse Item} Expr) (inner: Modes) (open: Item)
    (nested: NestedCarries self)
    (code: (open.kind == Comma) = False):
    Parse.ReadsIn GoodItems (() => listItems self inner open.leaf.word) (read value => Carried [open, ..read] value) :=
  Parse.readsThen
    [p := () => listItem self inner]
    [j := first => listItemsFrom self inner open.leaf.word first]
    (readsListItem self inner nested)
    (inside first carried => readsListItemsFrom self inner open inside first nested code carried)

theorem readsListPeek ∀ (self: Goal → {Parse Item} Expr) (inner: Modes) (open: Item)
    (nested: NestedCarries self)
    (code: (open.kind == Comma) = False):
    Parse.ReadsIn GoodItems (() => listPeek self inner open.leaf.word) (read value => Carried [open, ..read] value) :=
  readsInPeeked inner
    (seen => listAfter self inner open.leaf.word seen) _
    (start fine stops => readsListItems self inner open nested code start fine)
    (start item later shape fine stopped =>
      match isClose: item.kind == RBracket with
        | True => readsAtBumpRead [k := close => ListOf open.leaf.word [] False close] shape fine (after tail fits =>
          Parse.readsAtDone after
            (ListOf open.leaf.word [] False item.leaf.word) _
            (carriedList open []
              [item]
              []
              False
              item.leaf.word
              code
              itemsCarriedNil
              (itemWordsCode item (codeAs (DecEq.sound isClose) byComputing))))
        | False => readsListItems self inner open nested code start fine)

theorem readsListExpr ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: NestedCarries self)
    (start: Parse.Mark Item) (item: Item) (later: List Item)
    (shape: start.rest = [item, ..later])
    (isBracket: item.kind = LBracket)
    (fine: Parse.Fits Item GoodItems start.rest):
    Parse.ReadsAt start (() => listExpr self modes) Carried :=
  readsAtBumpRead [k := open => listTail self modes open] shape fine (after tail fits =>
    readsListPeek self modes.inBrackets item nested (codeAs isBracket byComputing) after fits)

theorem readsBracketAt ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: NestedCarries self)
    (outside: OutsideAtoms self)
    (second third: Option Tok) (start: Parse.Mark Item) (item: Item) (later: List Item)
    (shape: start.rest = [item, ..later])
    (isBracket: item.kind = LBracket)
    (fine: Parse.Fits Item GoodItems start.rest):
    Parse.ReadsAt start (() => bracketAt self modes second third) Carried :=
  match named: (isSome Lower second || isSome KwDecreasing second) && isSome ColonEq third with
    | True =>
      readsOut
        [p := () => namedArgument self modes RBracket "`]`"]
        (outside.namedArguments modes RBracket "`]`")
        start
        fine
    | False => readsListExpr self modes nested start item later shape isBracket fine

theorem readsBracketAtom ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: NestedCarries self)
    (outside: OutsideAtoms self)
    (start: Parse.Mark Item) (item: Item) (later: List Item)
    (shape: start.rest = [item, ..later])
    (isBracket: item.kind = LBracket)
    (fine: Parse.Fits Item GoodItems start.rest):
    Parse.ReadsAt start (() => bracketAtom self modes) Carried :=
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

theorem readsAtomOf ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: NestedCarries self)
    (outside: OutsideAtoms self)
    (start: Parse.Mark Item) (item: Item) (later: List Item)
    (shape: start.rest = [item, ..later])
    (fine: Parse.Fits Item GoodItems start.rest):
    Parse.ReadsAt start (() => atomOf self modes item.kind) Carried :=
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
            (codeAs (DecEq.sound isBang) byComputing)
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
                      readsOut [p := () => atomRest self modes item.kind] (outside.rests modes item.kind) start fine

--| `atom_base` carries its items, at every mode.
def BasesCarry (self: Goal → {Parse Item} Expr): Prop :=
  ∀ (modes: Modes) => Parse.ReadsIn GoodItems (() => atomBase self modes) Carried

theorem readsAtomBases ∀ (self: Goal → {Parse Item} Expr)
    (nested: NestedCarries self)
    (outside: OutsideAtoms self):
    BasesCarry self :=
  modes =>
    readsInPeeked modes
      (seen => atomBaseOn self modes seen) _
      (start fine stops => readsOut [p := () => atomMissing self modes] (outside.missings modes) start fine)
      (start item later shape fine stopped => readsAtomOf self modes nested outside start item later shape fine)

-- Application.

theorem carriedApp ∀ [first rest: List Item] [head: Expr] [args: List Expr]
    (carried: Carried first head)
    (others: ItemsCarried rest args):
    Carried (first ++ rest) (App head args) :=
  within => rewrite itemWordsAppend first rest, carried (Bool.andLeft within), others (Bool.andRight within)

--| The rounds of a loop that each read a carried tree, or nothing and stopped.
theorem roundsCarried ∀ [read: List Item] [values: List Expr]
    (rounds: Parse.Rounds (Parse.Maybe Carried) read values):
    ItemsCarried read values :=
  match values, rounds with
    | [], none => rewrite none then itemsCarriedNil
    | [value, ..more], (first, rest, split, _, carried, others) =>
      rewrite split then itemsCarriedCons carried (roundsCarried others)

theorem readsArgumentBrace ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: NestedCarries self)
    (outside: OutsideBraced self) (brace: Bool):
    Parse.ReadsIn GoodItems (() => argumentBrace self modes brace) Carried :=
  match brace with
    | True => readsOut (outside.braceArguments modes)
    | False => nested { modes, level = LevelArgument }

theorem readsArgument ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: NestedCarries self)
    (outside: OutsideBraced self):
    Parse.ReadsIn GoodItems (() => argument self modes) Carried :=
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
    (nested: NestedCarries self)
    (outside: OutsideBraced self):
    Parse.ReadsIn GoodItems (() => arguments self modes) ItemsCarried :=
  Parse.readsWeaken
    (Parse.readsLoop _
      (Parse.Maybe Carried)
      (readsAfter0
        [p := () => startsAtom modes]
        [j := starts => argumentStep self modes starts]
        (reads0StartsAtom modes)
        (starts =>
          match starts with
            | True => Parse.readsThen (readsArgument self modes nested outside) (read value carried =>
              Parse.readsDone (Some value) _ (rewrite List.appendNil read then carried))
            | False => Parse.readsDone None _ byComputing)))
    (read values rounds => roundsCarried rounds)

theorem readsAppliedTo ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: NestedCarries self)
    (outside: OutsideBraced self)
    (before: List Item) (head: Expr)
    (carried: Carried before head):
    Parse.ReadsIn GoodItems (() => appliedTo self modes head) (read value => Carried (before ++ read) value) :=
  Parse.readsThen (readsArgument self modes nested outside) (r1 first firstCarried =>
    Parse.readsThen (readsArguments self modes nested outside) (r2 more others =>
      Parse.readsDone _ _ (rewrite List.appendNil r2 then carriedApp carried (itemsCarriedCons firstCarried others))))

theorem carriedSectioned ∀ (section: Bool) [read: List Item] [applied: Expr]
    (carried: Carried read applied):
    Carried read (sectioned section applied) :=
  match section with
    | True => carriedOut read byComputing
    | False => carried

theorem readsAppEnd ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: NestedCarries self)
    (outside: OutsideBraced self)
    (section: Bool) (before: List Item) (head: Expr) (applies: Bool)
    (carried: Carried before head):
    Parse.ReadsIn GoodItems (() => appEnd self modes section head applies) (read value =>
      Carried (before ++ read) value) :=
  match applies with
    | True =>
      Parse.readsThen
        [p := () => appliedTo self modes head]
        [j := applied => sectioned section applied]
        (readsAppliedTo self modes nested outside before head carried)
        (read applied appliedCarried =>
          Parse.readsDone _ _ (rewrite List.appendNil read then carriedSectioned section appliedCarried))
    | False => Parse.readsDone _ _ (rewrite List.appendNil before then carriedSectioned section carried)

theorem readsAppHead ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: NestedCarries self)
    (outside: OutsideBraced self)
    (bases: BasesCarry self) (section: Bool):
    Parse.ReadsIn GoodItems (() => appHead self modes section) Carried :=
  Parse.readsThen
    [p := () => atom self modes True]
    [j := head => appCalls self modes section head]
    (readsAtom self modes True (bases modes) (outside.below.records modes))
    (before head carried =>
      readsAfter0
        [p := () => startsAtom modes]
        [j := applies => appEnd self modes section head applies]
        (reads0StartsAtom modes)
        (applies => readsAppEnd self modes nested outside section before head applies carried))

theorem readsApp ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: NestedCarries self)
    (outside: OutsideBraced self)
    (bases: BasesCarry self):
    Parse.ReadsIn GoodItems (() => app self modes) Carried :=
  readsAfter0 [p := () => offset()] [j := start => appAt self modes start] reads0Offset (start =>
    readsAfter0
      [p := () => modes.at Dot && modes.sectionHead != Some start]
      [j := section => appHead self modes section]
      (reads0Then [p := () => modes.at Dot] (reads0At modes Dot) (dot => reads0Done _))
      (section => readsAppHead self modes nested outside bases section))

--| An argument read by `self`: `atom` with no application.
theorem readsAtomArgument ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (head: Bool)
    (outside: OutsideAtoms self)
    (bases: BasesCarry self):
    Parse.ReadsIn GoodItems (() => atom self modes head) Carried :=
  readsAtom self modes head (bases modes) (outside.records modes)

-- Unary.

theorem minusBangCode ∀ (kind: Tok) (is: (kind == Minus || kind == Bang) = True): (kind == Comma) = False :=
  match kind, is with
    | Minus, is => byComputing
    | Bang, is => byComputing
    | other, is => (Bool.falseNotTrue is).impossible

theorem readsUnaryNext ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: NestedCarries self)
    (app: Parse.ReadsIn GoodItems (() => app self modes) Carried)
    (start: Parse.Mark Item) (item: Item) (later items: List Item)
    (shape: start.rest = [item, ..later])
    (fine: Parse.Fits Item GoodItems start.rest):
    Parse.ReadsAt start (() => unaryNext self modes item.kind items) Carried :=
  match negative: item.kind == Minus && negativeNumeral items with
    | True => app start fine
    | False =>
      match signed: item.kind == Minus || item.kind == Bang with
        | True => readsAtBumpRead shape fine (after tail fits =>
          Parse.readsAtThen (nested { modes, level = LevelUnary } after fits) (read operand after2 starts carried =>
            Parse.readsAtDone after2 _ _
              (rewrite List.appendNil read then
                carriedPrefix item read operand (minusBangCode item.kind signed) carried)))
        | False => app start fine

theorem readsUnaryBar ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: NestedCarries self)
    (outside: OutsideAtoms self)
    (app: Parse.ReadsIn GoodItems (() => app self modes) Carried)
    (start: Parse.Mark Item) (item: Item) (later: List Item) (bar: Bool)
    (shape: start.rest = [item, ..later])
    (fine: Parse.Fits Item GoodItems start.rest):
    Parse.ReadsAt start (() => unaryBar self modes item.kind bar) Carried :=
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
    (nested: NestedCarries self)
    (outside: OutsideAtoms self)
    (app: Parse.ReadsIn GoodItems (() => app self modes) Carried)
    (start: Parse.Mark Item) (item: Item) (later: List Item)
    (shape: start.rest = [item, ..later])
    (fine: Parse.Fits Item GoodItems start.rest):
    Parse.ReadsAt start (() => unarySome self modes item.kind) Carried :=
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

--| `unary`: a `-` or `!` and its operand, or an application; a `match` or clause lambda is outside the slice.
theorem readsUnary ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: NestedCarries self)
    (outside: OutsideAtoms self)
    (app: Parse.ReadsIn GoodItems (() => app self modes) Carried):
    Parse.ReadsIn GoodItems (() => unary self modes) Carried :=
  readsInPeeked modes
    (seen => unaryOn self modes seen) _
    (start fine stops => app start fine)
    (start item later shape fine stopped => readsUnarySome self modes nested outside app start item later shape fine)

-- Operator links, for the ladder's levels: a model for the second half.

--| An operator link, read: the operator's item, no comma, then what its operand read.
def LinkCarried (read: List Item) (link: (Word, Expr)): Prop :=
  ∃ (operator: Item) (rest: List Item) => read = [operator, ..rest]
    ∧ (operator.kind == Comma) = False
    ∧ link.fst = operator.leaf.word
    ∧ Carried rest link.snd

theorem carriedInfix ∀ (operator: Item) [first rest: List Item] [left right: Expr]
    (code: (operator.kind == Comma) = False)
    (leftCarried: Carried first left)
    (rightCarried: Carried rest right):
    Carried (first ++ [operator, ..rest]) (Infix InfixBinary left operator.leaf.word right) :=
  within =>
    rewrite itemWordsAppend first [operator, ..rest],
        itemWordsCons operator rest code,
        leftCarried (Bool.andLeft within),
        rightCarried (Bool.andRight within)

--| Folding links to the left keeps the words in the order read.
theorem carriedLeftNested ∀ [first: List Item] [head: Expr] (links: List (Word, Expr)) [rest: List Item]
    (carried: Carried first head)
    (rounds: Parse.Rounds (Parse.Maybe LinkCarried) rest links):
    Carried (first ++ rest) (leftNested head links) :=
  match links, rounds with
    | [], none => rewrite none, List.appendNil first then carried
    | [(word, next), ..more], (
        taken,
        others,
        split,
        _,
        (operator, operand, single, code, same, nextCarried),
        restRounds
      ) =>
      let joined := carriedInfix operator code carried nextCarried
      let folded := carriedLeftNested more (rewrite <- same at joined then joined) restRounds
      rewrite split, single then (rewrite List.appendAssoc first [operator, ..operand] others at folded then folded)

--| Folding links to the right keeps the words in the order read.
theorem carriedRightNested ∀ [first: List Item] [head: Expr] (links: List (Word, Expr)) [rest: List Item]
    (carried: Carried first head)
    (rounds: Parse.Rounds (Parse.Maybe LinkCarried) rest links):
    Carried (first ++ rest) (rightNested head links) :=
  match links, rounds with
    | [], none => rewrite none, List.appendNil first then carried
    | [(word, next), ..more], (
        taken,
        others,
        split,
        _,
        (operator, operand, single, code, same, nextCarried),
        restRounds
      ) =>
      let below := carriedRightNested more nextCarried restRounds
      rewrite split, single, same then carriedInfix operator code carried below

--| One round of `operatorLinks`: the next item, if `takes` accepts it, and its operand; or nothing.
theorem readsOperatorStep ∀ (modes: Modes) (takes: Tok → Bool) (operand: () → {Parse Item} Expr)
    (code: ∀ (kind: Tok) => takes kind = True → (kind == Comma) = False)
    (operandReads: Parse.ReadsIn GoodItems operand Carried):
    Parse.ReadsIn GoodItems
      (() =>
        match modes.peek with
          | Some kind if takes kind =>
            let operator := bump()
            let value := operand()
            Some (operator, value)
          | _ => None)
      (Parse.Maybe LinkCarried) :=
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
                      (more value later2 starts2 carried =>
                        Parse.readsAtDone later2
                          (Some (word, value)) _
                          (rewrite single then
                            (
                              item,
                              more ++ [],
                              byComputing,
                              code item.kind took,
                              same,
                              rewrite List.appendNil more then carried
                            )))))

--| A first operand and the links after it, folded to the left: how `mulExpr` and `addExpr` carry their items.
theorem readsLeftChain ∀ (modes: Modes) (takes: Tok → Bool) (first operand: () → {Parse Item} Expr)
    (code: ∀ (kind: Tok) => takes kind = True → (kind == Comma) = False)
    (firstReads: Parse.ReadsIn GoodItems first Carried)
    (operandReads: Parse.ReadsIn GoodItems operand Carried):
    Parse.ReadsIn GoodItems (() => leftNested (first()) (operatorLinks modes takes operand)) Carried :=
  Parse.readsThen firstReads (r1 head carried =>
    Parse.readsThen (Parse.readsLoop _ _ (readsOperatorStep modes takes operand code operandReads)) (r2 links rounds =>
      Parse.readsDone _ _ (rewrite List.appendNil r2 then carriedLeftNested links carried rounds)))

theorem mulCode ∀ (kind: Tok)
    (took: (kind == Star || kind == Slash || kind == Percent) = True):
    (kind == Comma) = False :=
  match kind, took with
    | Star, took => byComputing
    | Slash, took => byComputing
    | Percent, took => byComputing
    | other, took => (Bool.falseNotTrue took).impossible

--| `mul_expr`, from what `unary` carries: a ladder level, proved as the second half proves the others.
theorem readsMulExpr ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (unaryReads: Parse.ReadsIn GoodItems (() => unary self modes) Carried):
    Parse.ReadsIn GoodItems (() => mulExpr self modes) Carried :=
  readsLeftChain modes
    (kind => kind == Star || kind == Slash || kind == Percent)
    (() => unary self modes)
    (() => unary self modes)
    mulCode
    unaryReads
    unaryReads

theorem addCode ∀ (kind: Tok) (took: (kind == Plus || kind == Minus) = True): (kind == Comma) = False :=
  match kind, took with
    | Plus, took => byComputing
    | Minus, took => byComputing
    | other, took => (Bool.falseNotTrue took).impossible

theorem appendCode ∀ (kind: Tok) (took: (kind == PlusPlus) = True): (kind == Comma) = False := match kind, took with
  | PlusPlus, took => byComputing
  | other, took => (Bool.falseNotTrue took).impossible

--| `add_expr`, from what `mul_expr` carries.
theorem readsAddExpr ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (mulReads: Parse.ReadsIn GoodItems (() => mulExpr self modes) Carried):
    Parse.ReadsIn GoodItems (() => addExpr self modes) Carried :=
  readsLeftChain modes
    (kind => kind == Plus || kind == Minus)
    (() => mulExpr self modes)
    (() => mulExpr self modes)
    addCode
    mulReads
    mulReads

--| `append_expr`, from what `add_expr` carries: `++`s nest to the right.
theorem readsAppendExpr ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (addReads: Parse.ReadsIn GoodItems (() => addExpr self modes) Carried):
    Parse.ReadsIn GoodItems (() => appendExpr self modes) Carried :=
  Parse.readsThen addReads (r1 head carried =>
    Parse.readsThen
      (Parse.readsLoop _ _
        (readsOperatorStep modes (kind => kind == PlusPlus) (() => addExpr self modes) appendCode addReads))
      (r2 links rounds => Parse.readsDone _ _ (rewrite List.appendNil r2 then carriedRightNested links carried rounds)))

-- The recursion.

--| The levels of the expression parser above `append_expr`, carried: the second half's (SW-4020) to prove, given `self` at
--| every goal and what the parsers outside slice 1 give.
type Ladder (self: Goal → {Parse Item} Expr) = {
  full: ∀ (modes: Modes) => Parse.ReadsIn GoodItems (() => expr self modes) Carried,
  inline: ∀ (modes: Modes) => Parse.ReadsIn GoodItems (() => exprInline self modes) Carried,
  logic: ∀ (modes: Modes) => Parse.ReadsIn GoodItems (() => logicLevel self modes) Carried,
  comparison: ∀ (modes: Modes) => Parse.ReadsIn GoodItems (() => cmpExpr self modes) Carried,
  thenBody: ∀ (modes: Modes) => Parse.ReadsIn GoodItems (() => thenBody self modes) Carried
}

--| The ladder carries its items for every `self` that gives what `ParseWalk` says and carries its own, given what the
--| parsers outside slice 1 give: the hypothesis the knot takes from the second half.
def LadderCarries: Type :=
  ∀ (self: Goal → {Parse Item} Expr) => Nested self → NestedCarries self → Outside self → Ladder self

--| `atom_base` carries its items, from `self` and what the parsers outside slice 1 give.
theorem basesCarry ∀ (self: Goal → {Parse Item} Expr)
    (carries: NestedCarries self)
    (outside: Outside self):
    BasesCarry self :=
  readsAtomBases self carries outside.below.below.below.below.below

--| One level of the expression parser carries its items: the levels above `append_expr` from `ladder`, the others
--| from this file's walk.
theorem readsExpressionRule ∀ (self: Goal → {Parse Item} Expr) (goal: Goal)
    (carries: NestedCarries self)
    (outside: Outside self)
    (ladder: Ladder self):
    Parse.ReadsIn GoodItems (() => expressionRule self goal) Carried :=
  let atoms := outside.below.below.below.below.below
  let braced := outside.below.below.below.below
  let bases := basesCarry self carries outside
  let unaryAt := (modes: Modes) => readsUnary self modes carries atoms (readsApp self modes carries braced bases)
  let mulAt := (modes: Modes) => readsMulExpr self modes (unaryAt modes)
  let addAt := (modes: Modes) => readsAddExpr self modes (mulAt modes)
  match goal with
    | { modes, level } =>
      match level with
        | LevelFull => ladder.full modes
        | LevelInline => ladder.inline modes
        | LevelLogic => ladder.logic modes
        | LevelComparison => ladder.comparison modes
        | LevelAppend => readsAppendExpr self modes (addAt modes)
        | LevelAdditive => addAt modes
        | LevelMultiplicative => mulAt modes
        | LevelUnary => unaryAt modes
        | LevelArgument => readsAtomArgument self modes False atoms bases
        | LevelApp => readsApp self modes carries braced bases
        | LevelThenBody => ladder.thenBody modes

--| `self` gives what `ParseWalk` says and carries its items, at every goal: the two walks' hypothesis, held together
--| so the recursion can be tied once for both.
def NestedBoth (self: Goal → {Parse Item} Expr): Prop :=
  ∀ (goal: Goal) => Parse.ReadsIn GoodItems (() => self goal) (read value => GoalParsed goal value ∧ Carried read value)

theorem nestedOfBoth ∀ [self: Goal → {Parse Item} Expr] (both: NestedBoth self): Nested self := goal =>
  Parse.readsWeaken (both goal) (read value facts => facts.left)

theorem carriesOfBoth ∀ [self: Goal → {Parse Item} Expr] (both: NestedBoth self): NestedCarries self := goal =>
  Parse.readsWeaken (both goal) (read value facts => facts.right)

--| The recursion's knot: `expressionAt` gives what `ParseWalk` says and carries its items, at every goal, once the
--| ladder does.
--|
--| Proof idea: `Parse.readsRecursiveWith` with both walks' specs at once, since the parsers outside slice 1 are proved
--| (`outsideOf`) from `ParseWalk`'s `Nested`, which this walk's levels need too; each level is `givesExpressionRule`
--| and `readsExpressionRule`, joined by `Parse.readsBoth`.
theorem bothExpressionAt ∀ (ladder: LadderCarries): NestedBoth expressionAt := goal =>
  Parse.readsRecursiveWith expressionRule
    (inner read value => GoalParsed inner value ∧ Carried read value)
    (self both argument =>
      let nested := nestedOfBoth both
      let carries := carriesOfBoth both
      let outside := outsideOf self nested
      Parse.readsBoth
        (givesExpressionRule self argument nested outside)
        (readsExpressionRule self argument carries outside (ladder self nested carries outside)))
    goal

--| `expressionAt` carries its items at every goal, once the ladder does.
theorem carriesExpressionAt ∀ (ladder: LadderCarries): NestedCarries expressionAt :=
  carriesOfBoth (bothExpressionAt ladder)
