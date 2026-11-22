--| What `Syntax.ParseKept`'s walk of the parser and the file layers build on: the words of a list of items (commas left
--| out), the spec `Carried` that the consumers of `parseCarries1` state their facts in (`carriedOfKept` gives it from
--| `KeptTree`), and the combinators the walk's lemmas are joined with.

namespace Syntax.ParseCarries
import Std (Bool, DecEq, Eq, List, Nat, Option, Pair, Parse, Result, Text)
import Syntax (..)
import Fmt (..)
import Syntax.LexProofs (..)
import Syntax.ParseProofs (..)
import Syntax.ParseWalk (..)
import Fmt.Grammar1 (..)

-- The spec.

--| The words the tree keeps of some leaves: every token's but a comma's, in order, each with its comments.
def codeWords (leaves: List Leaf): List Word := leaves.filter (leaf => leaf.kind != Comma) |> .map Leaf.word

--| The words of the items a parser read.
def itemWords (read: List Item): List Word := codeWords (read.map Item.leaf)

-- Words of items.

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

--| A parser that never succeeds reads as any spec says.
theorem readsNever ∀ [p: () → {Parse Item} a] [spec: List Item → a → Prop]
    (never: ∀ (holds: a → Prop) => Parse.Gives GoodItems p holds):
    Parse.ReadsIn GoodItems p spec :=
  Parse.readsWeaken (never (value => ∀ (read: List Item) => spec read value)) (read value all => all read)

theorem readsFail ∀ (modes: Modes) (what: Text) [spec: List Item → a → Prop]:
    Parse.ReadsIn GoodItems (() => modes.fail what) spec :=
  readsNever (holds => givesFail modes what)

theorem readsFailName ∀ (modes: Modes) (what: Text) [spec: List Item → a → Prop]:
    Parse.ReadsIn GoodItems (() => modes.failName what) spec :=
  readsNever (holds => givesFailName modes what)

--| A look-ahead, then `j` of what it found: `j` reads all that is read.
theorem readsAfter0 ∀ [p: () → {Parse Item} a] [j: a → {Parse Item} b] [spec: List Item → b → Prop]
    (first: Reads0 p)
    (rest: ∀ (value: a) => Parse.ReadsIn GoodItems (() => j value) spec):
    Parse.ReadsIn GoodItems (() => j (p())) spec :=
  start fine => Parse.readsAtAfter0 first fine (value after same fits => rest value after fits)

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

theorem readsSuffixCalled ∀ (target: Expr) (callable paren: Bool):
    Parse.ReadsIn GoodItems (() => suffixCalled target callable paren) (SameOrOut target) :=
  readsAfter0 reads0Left (seen =>
    match unitCall seen with
      | False => Parse.readsDone _ (Inl (byComputing, byComputing))
      | True =>
        match callable || (paren && callableParen target) with
          | False => Parse.readsDone _ (Inl (byComputing, byComputing))
          | True => Parse.readsThen givesBump (r1 open _ =>
            Parse.readsThen givesBump (r2 close _ => Parse.readsDone _ (Inr (Bool.andFalse target.grammar1)))))

--| `suffixes` after the call: a field access starts another round on a tree outside the slice, and nothing else is read.
--|
--| Proof idea: a field access bumps two items and gives a `FieldAccess`, outside the slice, as is everything after it;
--| every other case reads nothing and keeps the tree.
theorem readsSuffixesOn ∀ (more: Nat) (modes: Modes) (called: Expr) (paren: Bool) (items: List Item)
    (next: ∀ (target: Expr) (callable: Bool) => Out target
      → Parse.ReadsIn GoodItems (() => suffixes more modes target callable paren) (read value => Out value)):
    Parse.ReadsIn GoodItems (() => suffixesOn more modes called paren items) (SameOrOut called) :=
  match items with
    | [dot, field, ..later] =>
      match dot.kind == Dot && !modes.stops dot && !sectionAt [dot, field, ..later] with
        | False => Parse.readsDone _ (Inl (byComputing, byComputing))
        | True =>
          match !((field.kind == Lower || field.kind == Upper) && !isQualified field && !modes.stops field) with
            | True => Parse.readsFatal
            | False =>
              match !dot.glued || !field.glued with
                | True => Parse.readsFatal
                | False => Parse.readsThen givesBump (r1 dotLeaf _ =>
                  Parse.readsThen givesBump (r2 name _ =>
                    Parse.readsWeaken
                      (next (FieldAccess (Some called) dotLeaf name) True byComputing)
                      (read value out => Inr out)))
    | [dot] =>
      match dot.kind == Dot && !modes.stops dot with
        | True => Parse.readsFatal
        | False => Parse.readsDone _ (Inl (byComputing, byComputing))
    | other => Parse.readsDone _ (Inl (byComputing, byComputing))

--| `suffixes` of a tree outside the slice gives one outside the slice.
theorem readsSuffixesOut ∀ (fuel: Nat) (modes: Modes) (target: Expr) (callable paren: Bool)
    (out: Out target):
    Parse.ReadsIn GoodItems (() => suffixes fuel modes target callable paren) (read value => Out value) :=
  Parse.readsWeaken (givesSuffixes Out (tree out => out) fuel modes target callable paren out) (read value out => out)

--| `suffixes` keeps the tree, reading nothing, or makes one outside the slice.
theorem readsSuffixes ∀ (fuel: Nat) (modes: Modes) (target: Expr) (callable paren: Bool):
    Parse.ReadsIn GoodItems (() => suffixes fuel modes target callable paren) (SameOrOut target) :=
  match fuel with
    | Zero => Parse.readsDone _ (Inl (byComputing, byComputing))
    | Succ more => Parse.readsThen (readsSuffixCalled target callable paren) (r1 called calledKept =>
      Parse.readsThen reads0Left (r2 seen empty =>
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
    | False => Parse.readsDone _ (Inl (byComputing, byComputing))
    | True =>
      match head with
        | False => Parse.readsDone _ (Inl (byComputing, byComputing))
        | True => Parse.readsThen (reads0At modes LBrace) (r1 found empty =>
          match found with
            | True =>
              Parse.readsThen records (r2 fields _ => Parse.readsDone (CtorFields base fields, False) (Inr byComputing))
            | False => Parse.readsDone _ (Inl (rewrite empty then byComputing, byComputing)))

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
              | True => Parse.readsDone _ (Inr byComputing)
              | False => Parse.readsDone _ (rewrite empty, List.appendNil r3 then sameOrOutThen pairKept kept))))

-- Words of items, continued.

theorem itemWordsCons ∀ (item: Item) (rest: List Item)
    (code: (item.kind == Comma) = False):
    itemWords [item, ..rest] = [item.leaf.word, ..itemWords rest] :=
  rewrite itemWordsAppend [item] rest, itemWordsCode item code

--| A kind known to be one that is no comma.
theorem codeAs ∀ [kind wanted: Tok] (is: kind = wanted) (code: (wanted == Comma) = False): (kind == Comma) = False :=
  rewrite is then code

theorem wordWithinNotComma ∀ (kind: Tok) (word: kind.wordWithin1 = True): (kind == Comma) = False :=
  match kind, word with
    | Lower | Upper | Num | Float, _ => byComputing
    | other, word => (Bool.falseNotTrue word).impossible

theorem itemWordsAfterComma ∀ (comma: Item) (rest: List Item)
    (isComma: comma.kind = Comma):
    itemWords [comma, ..rest] = itemWords rest :=
  rewrite itemWordsAppend [comma] rest, itemWordsComma comma isComma

-- Brackets.

theorem readsTupleClose ∀ (modes: Modes): Parse.ReadsIn GoodItems (() => tupleClose modes) (OneOf RParen) :=
  readsAfter0 (reads0At modes Colon) (annotated =>
    match annotated with
      | True => Parse.readsFatal
      | False => readsExpect modes RParen _)

theorem readsTupleEnds ∀ (inner: Modes) (count: Nat): Reads0 (() => tupleEnds inner count) :=
  Parse.reads0Then (reads0At inner RParen) (found => Parse.reads0Done _)
