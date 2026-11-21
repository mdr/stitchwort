--| The line rule read from a group's tokens (H1 of SW-4121's plan): `hangs` reads tokens only, and in a group that
--| keeps it every closer and comma is inside a bracket, where the parser's line test lets it start a line.

namespace Syntax.ReadBackHungDeep
import Std (Bool, DecEq, Eq, List, Nat, Option)
import Syntax (..)
import Fmt (..)
import Syntax.SettleProofs (tokens)
import Syntax.ReadBackProofs (ItemsAt, depthPast)
import Syntax.ReadBackHung (..)

--| A step reads only the leaf's token.
theorem stepSameToken ∀ (state: HangState) (first second: Leaf)
    (same: first.token = second.token):
    state.step first = state.step second :=
  match first, second with
    | { token, trivia }, { token = token2, trivia = trivia2 } =>
      match state.blocks with
        | [] => rewrite same
        | [block, ..outer] => rewrite same

--| `hangsFrom` reads only the leaves' tokens, from any state.
theorem hangsFromTokens ∀ (state: HangState) (first second: List Leaf)
    (same: tokens first = tokens second):
    hangsFrom state first = hangsFrom state second :=
  match first, second with
    | [], [] => byComputing
    | [leaf, ..rest], [other, ..more] =>
      let head := List.consInjectiveHead same
      let tail := Eq.cong (.drop 1) same
      rewrite stepSameToken state leaf other head then
        match state.step other with
          | Some next => hangsFromTokens next rest more tail
          | None => byComputing

--| Leaves with the same tokens keep the line rule alike: `hangs` reads only their tokens.
theorem hangsTokens ∀ (first second: List Leaf) (same: tokens first = tokens second): hangs first = hangs second :=
  match first, second with
    | [], [] => byComputing
    | [leaf, ..rest], [other, ..more] =>
      let head: leaf.token = other.token := List.consInjectiveHead same
      let tail := Eq.cong (.drop 1) same
      rewrite head, hangsFromTokens HangState.initial rest more tail

--| The brackets open in the line rule's state are the items' bracket depth, and every closer and comma has one open.
theorem deepFrom ∀ (leaves: List Leaf) (state: HangState) (place: ItemsAt)
    (len: state.blocks.length = place.depth)
    (hung: hangsFrom state leaves = True):
    deepAll (place.items leaves) = True :=
  match leaves with
    | [] => byComputing
    | [leaf, ..rest] =>
      match step: state.step leaf with
        | Some next =>
          let (shape, bracket) := stepInfo state next leaf step
          let more := deepFrom rest next (place.step leaf) (rewrite <- len then shape) hung
          Bool.andIntro
            (match exempt: leaf.token.kind == Comma || leaf.token.kind.isCloser with
              | True =>
                let open := bracket exempt
                arithmetic
              | False => byComputing)
            more

--| In a group that keeps the line rule, every closer and comma item has a bracket open before it.
theorem hungDeep ∀ (group: List Leaf) (hung: hangs group = True): deepAll (items group) = True := match group with
  | [] => byComputing
  | [first, ..rest] =>
    let isDef: first.token.kind = KwDef := DecEq.sound (Bool.andLeft hung)
    let more := Bool.andRight (Bool.andRight hung)
    let len: HangState.initial.blocks.length = (ItemsAt.start.step first).depth := rewrite isDef
    Bool.andIntro (rewrite isDef) (deepFrom rest HangState.initial (ItemsAt.start.step first) len more)

--| A closer is no opener.
theorem closerNotOpener ∀ (kind: Tok) (closer: kind.isCloser = True): kind.isOpener = False := cases

--| A step over a closer pops a bracket, which was open.
theorem stepInfoCloser ∀ (state next: HangState) (leaf: Leaf)
    (step: state.step leaf = Some next)
    (closer: leaf.token.kind.isCloser = True):
    next.blocks.length = depthPast state.blocks.length leaf.token.kind ∧ state.blocks.length > 0 :=
  let notOpener := closerNotOpener leaf.token.kind closer
  cases

--| Starting an item keeps the number of brackets.
theorem startLength ∀ (fresh: Bool) (column: Nat) (blocks: List (Option Nat)):
    (startBlocks fresh column blocks).length = blocks.length :=
  match blocks with
    | [] => byComputing
    | [block, ..outer] => cases fresh then byComputing

--| A step keeps `blocks.length` the bracket depth `depthPast` counts, and a comma or closer steps only where a bracket
--| is open.
theorem stepInfo ∀ (state next: HangState) (leaf: Leaf)
    (step: state.step leaf = Some next):
    next.blocks.length = depthPast state.blocks.length leaf.token.kind
      ∧ ((leaf.token.kind == Comma || leaf.token.kind.isCloser) = True → state.blocks.length > 0) :=
  match closer: leaf.token.kind.isCloser with
    | True =>
      let (shape, nonEmpty) := stepInfoCloser state next leaf step closer
      (shape, _ => nonEmpty)
    | False =>
      match comma: leaf.token.kind == Comma with
        | True =>
          let isComma: leaf.token.kind = Comma := DecEq.sound comma
          match glue: state.glue && leaf.token.lineStart with
            | False =>
              match state.blocks with
                | [block, ..outer] =>
                  match starts: leaf.token.lineStart with
                    | False =>
                      let same := Option.someInjective step
                      rewrite <- same, isComma then (byComputing, _ => arithmetic)
        | False =>
          match glue: state.glue && leaf.token.lineStart with
            | False =>
              match assign: leaf.token.kind == ColonEq && state.blocks.isEmpty with
                | True =>
                  let isAssign: leaf.token.kind = ColonEq := DecEq.sound (Bool.andLeft assign)
                  let empty: state.blocks = [] := (Bool.andRight assign).read
                  let same := Option.someInjective step
                  rewrite <- same, isAssign, empty then (byComputing, h => (Bool.falseNotTrue h).impossible)
                | False =>
                  match right: (leaf.token.lineStart.not || inForce state.blocks state.top < leaf.token.column).not with
                    | False =>
                      match colon: leaf.token.kind == Colon && state.blocks.isEmpty with
                        | True =>
                          let isColon: leaf.token.kind = Colon := DecEq.sound (Bool.andLeft colon)
                          let empty: state.blocks = [] := (Bool.andRight colon).read
                          let same := Option.someInjective step
                          rewrite <- same, isColon, empty then (byComputing, h => (Bool.falseNotTrue h).impossible)
                        | False =>
                          let same := Option.someInjective step
                          let kept := startLength (state.start && leaf.token.lineStart) leaf.token.column state.blocks
                          rewrite <- same then
                            match opens: leaf.token.kind.isOpener with
                              | True | False => rewrite kept then (byComputing, h => (Bool.falseNotTrue h).impossible)
