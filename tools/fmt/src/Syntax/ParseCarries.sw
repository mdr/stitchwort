--| `parseCarries1`'s walk of the parser (docs/reviews/SW-4018-parser-statements.md §2.1, ticket A): every parser
--| function on slice 1's path reads its tree's words from the items it read, commas left out. The spec is `Carried`,
--| a `Parse.ReadsIn` spec where `ParseWalk`'s is a `Parse.Gives` one, so it can speak of what was read; a tree outside
--| the slice makes it empty, so each `Out` fact of `ParseWalk` gives its lemma by `Parse.readsWeaken` (`readsOut`).
--|
--| This file has the spec, its combinators, the atoms, brackets and comma lists, arguments and applications, `unary`,
--| and the recursion's knot (`carriesExpressionAt`), which takes the operator ladder, `expr` and blocks as one
--| hypothesis (`RuleCarries`) for the second half (SW-4020) to discharge.

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
