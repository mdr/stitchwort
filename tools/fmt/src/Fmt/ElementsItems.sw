--| A tuple's or list's items with comments anywhere (SW-4147, piece E4 of the comments-anywhere plan, SW-4130):
--| `ItemsHang` from what each item gives where it stands as an item. An item with own-line comments above its first
--| token (`ledItemHangs`), or with a kept blank line and none (`blankItemHangs`), starts the line after them, at any
--| entry a separator leaves; any other item writes nothing before its first token and hangs as it stands.
--|
--| What each item needs of the induction is the first half of `AnyFacts` (`Fmt.ElementsProofs`, which imports this):
--| `PlainHangs`, passed in through a predicate (`facts`) and its list form (`all`), as `Fmt.ElementsApp` does.

namespace Fmt.ElementsItems
import Std (Bool, Doc, Eq, List, Nat, Option, Text, Void)
import Syntax (Expr, Note, Tok, Word)
import Fmt (..)
import Fmt.HangProofs (..)
import Fmt.ChainHangProofs (HangsAt)
import Fmt.BracketHangProofs (ItemHangs, ItemsHang)
import Fmt.SpellProofs (..)
import Fmt.TreeJoinProofs (lexKind)
import Fmt.ToldWordProofs (..)
import Fmt.ElementsKeys (ledItemHangs)
import Fmt.ElementsBlank (blankItemHangs)

--| An expression hangs as an element wherever its first token writes nothing before itself: `AnyFacts`' first half.
def PlainHangs (expr: Expr): Prop :=
  ∀ (around: Around) => (!expr.lead.leadsLine around) = True
    → HangsAt lexKind around.before expr.trails (expr.el around)

--| A token not hoisted, with no comments above it and no blank line kept above it, writes nothing before itself.
theorem unledWord ∀ (word: Word) (around: Around)
    (hoisted: around.hoisted = False)
    (unnoted: word.comments.above = [])
    (unblank: (around.item && word.comments.blankBefore) = False):
    (!word.leadsLine around) = True :=
  match word, around with
    | { text, comments = { above, after, blankBefore } }, { before, hoisted = h, item, at, inArm } =>
      match h, above, hoisted, unnoted with
        | True, _, never, _ => (Bool.trueNotFalse never).impossible
        | False, [], _, _ => rewrite unblank
        | False, [note, ..rest], _, never => cases

--| A slice 1 expression standing as an item (not hoisted) hangs as `ItemsHang` asks: with comments above its first
--| token or a kept blank line, it starts the line after them (`ledItemHangs`, `blankItemHangs`, at any entry but a
--| plain line start); otherwise it writes nothing before its first token and hangs where it stands (`plain`).
theorem itemLed ∀ (expr: Expr) (around: Around) (inset: Nat)
    (within: expr.within1 = True)
    (lexical: expr.lexical1 = True)
    (sound: expr.sound = True)
    (plain: PlainHangs expr)
    (hoisted: around.hoisted = False):
    ItemHangs lexKind (expr.el around) inset around.before expr.trails :=
  let hoistedHangs: ∀ (inset: Nat) => ElHangs lexKind
    (expr.el { around | hoisted = True })
    inset
    inset
    around.before
    expr.trails
    wordStart :=
    inset => plain { around | hoisted = True } byComputing inset inset
  match above: expr.lead.comments.above with
    | [note, ..rest] => (
      True,
      state entry fresh =>
        ledItemHangs expr around inset state entry note rest within lexical sound hoisted above hoistedHangs
    )
    | [] =>
      match kept: around.item && expr.lead.comments.blankBefore with
        | True => (
          True,
          state entry fresh =>
            blankItemHangs expr around inset state entry within sound hoisted
              (Bool.andLeft kept)
              above
              (Bool.andRight kept)
              fresh
              hoistedHangs
        )
        | False =>
          (False, state entry _ => plain around (unledWord expr.lead around hoisted above kept) inset inset state entry)

--| A bracket's items hang as `ItemsHang` asks, each where it stands as an item, from the facts of each (`facts`, its
--| first half `plain`).
theorem itemsLed ∀ (facts: Expr → Prop) (all: List Expr → Prop)
    (split: ∀ (expr: Expr) (rest: List Expr) => all [expr, ..rest] → facts expr ∧ all rest)
    (plain: ∀ (expr: Expr) => facts expr → PlainHangs expr) (inset: Nat) (bare arm before: Bool)
    (at: Nat) (items: List Expr)
    (within: allWithin1 items = True)
    (lexical: allLexical1 items = True)
    (sound: allSound items = True) (held: all items):
    ItemsHang lexKind inset bare arm before before at items :=
  match items with
    | [] => byComputing
    | [item, ..rest] =>
      let (first, others) := split item rest held
      (
        itemLed item
          (firstAround bare arm before at)
          inset
          (Bool.andLeft within)
          (Bool.andLeft lexical)
          (Bool.andLeft sound)
          (plain item first)
          byComputing,
        itemsLed facts all split plain inset False arm item.trails
          (at + item.size)
          rest
          (Bool.andRight within)
          (Bool.andRight lexical)
          (Bool.andRight sound)
          others
      )
