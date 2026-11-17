--| The passes' steps keep `meaning` at the node they rewrite (stage 4b,
--| SW-3864): P1's and P2's by computing over the node's form; P3's at a
--| row by induction along the result's left end (`dropLeftForgotten`);
--| P3's around a binder's type layer by layer (`stripUnwrapped`).
--|
--| Not here: the traversal's generic lemma, which turns these into each
--| pass's "keeps meaning". For P1 and P2 it is the plain one (the step
--| changes a flag or keyword at the node, never a child). P3's steps
--| rebuild descendants (`dropLeft` takes pairs off the spine,
--| `dropDeclBinders` reaches into the header's type), so the lemma it needs
--| is that `meaning`'s traversal commutes with them. P4's header and
--| binding steps need `splitGroups` of merged groups to be the groups
--| merged, which rests on `Group.typeLines` (the dump) telling types apart
--| for groups with no comment.

namespace Fmt.Proofs
import Fmt (..)
import Std (Bool, Eq, List, Nat, Option, Text)
import Syntax (Attributes, DefKind, Expr, Fields, Group, Header, InfixKind, Param, Pattern, RuleSet, Tok, Word)

theorem commaExprKeepsMeaning ∀ (expr: Expr): plainExpr (withoutCommaExpr expr) = plainExpr expr := cases

theorem commaPatternKeepsMeaning ∀ (pattern: Pattern):
    plainPattern (withoutCommaPattern pattern) = plainPattern pattern :=
  cases

theorem commaFieldsKeepsMeaning ∀ (fields: Fields):
    { { fields | trailingComma = False } | trailingComma = False } = { fields | trailingComma = False } :=
  cases

theorem commaAttributesKeepsMeaning ∀ (attributes: Attributes):
    { { attributes | trailingComma = False } | trailingComma = False } = { attributes | trailingComma = False } :=
  cases

theorem commaRuleSetKeepsMeaning ∀ (set: RuleSet):
    { { set | trailingComma = False } | trailingComma = False } = { set | trailingComma = False } :=
  cases

theorem forallKeepsMeaning ∀ (header: Header): plainHeader (withForall header) = plainHeader header := match header with
  | {
      exportKeyword,
      opaqueKeyword,
      kind,
      keyword,
      name,
      forallKeyword,
      params,
      colon,
      result,
      decreasingClause,
      unfoldingClause
    } =>
    match kind, forallKeyword with
      | DefTheorem, None =>
        match explicit: params.any Group.explicit with
          | True => byComputing
          | False => byComputing
      | DefTheorem, Some _ => byComputing
      | DefPlain, _ => byComputing
      | DefInstance, _ => byComputing

-- P3 after a row: `dropLeft` removes only pairs that `forgetLeft` forgets.

theorem levelAtomic ∀ (expr: Expr) (high: 22 <= expr.level): expr.atomic = True := cases

theorem negativeKept ∀ (membership: Bool) (expr: Expr)
    (negative: expr.negativeNumeral = True):
    keepsBrackets membership expr = True :=
  match expr with
    | Prefix operator (Atom Num word) => cases
    | Prefix operator (Atom Float word) => cases

theorem enoughAbove ∀ (atomOnly: Bool) (floor more: Nat)
    (enough: atomOnly = True → 22 <= floor)
    (yes: atomOnly = True):
    22 <= Nat.max floor more :=
  arithmetic [enough yes, Nat.leMaxLeft floor more]

theorem enoughHead ∀ (floor: Nat) (yes: True = True): 22 <= Nat.max floor 22 := Nat.leMaxRight floor 22

--| A pair `dropLeft` drops is one `forgetLeft` forgets.
theorem parenForgotten ∀ (floor: Nat) (membership atomOnly: Bool) (open: Word) (inner: Expr) (close: Word)
    (enough: atomOnly = True → 22 <= floor)
    (drops: (open.bare && close.bare && !holdsFunction inner && floor <= inner.level && !keepsBrackets membership inner)
      = True):
    forgetLeft atomOnly (Paren open inner close) = forgetLeft atomOnly inner :=
  match negative: inner.negativeNumeral with
    | True =>
      let keeps := negativeKept membership inner negative
      cases
    | False =>
      match atomOnly with
        | False => cases
        | True =>
          match atomic: inner.atomic with
            | True => cases
            | False =>
              match within: floor <= inner.level with
                | False => cases
                | True =>
                  let high: 22 <= inner.level := arithmetic [enough byComputing, within]
                  let atomicAfterAll := levelAtomic inner high
                  cases

--| By induction along the left end: where `dropLeft` drops a pair, the
--| pair holds no comment, isn't a negative numeral's (`negativeKept`), and
--| below an application's head holds what binds at least as tightly as an
--| atom (`levelAtomic`), so `forgetLeft` forgets it too; everywhere else
--| the two rebuild the same node around the same left part.
theorem dropLeftForgotten ∀ (floor: Nat) (membership atomOnly: Bool) (expr: Expr)
    (enough: atomOnly = True → 22 <= floor):
    forgetLeft atomOnly (dropLeft floor membership expr) = forgetLeft atomOnly expr :=
  match expr with
    | Paren open inner close =>
      match drops: open.bare
        && close.bare
        && !holdsFunction inner
        && floor <= inner.level
        && !keepsBrackets membership inner with
        | False => byComputing
        | True =>
          rewrite parenForgotten floor membership atomOnly open inner close enough drops then
            dropLeftForgotten floor membership atomOnly inner enough
    | Infix kind left operator right =>
      rewrite dropLeftForgotten
        (Nat.max floor (leftNeeds kind operator.text))
        (membership || kind == InfixMembership)
        atomOnly
        left
        (enoughAbove atomOnly floor (leftNeeds kind operator.text) enough)
    | Chain first rest =>
      rewrite dropLeftForgotten (Nat.max floor 8) membership atomOnly first (enoughAbove atomOnly floor 8 enough)
    | App head arguments => rewrite dropLeftForgotten (Nat.max floor 22) membership True head (enoughHead floor)
    | FieldAccess (Some target) dot field =>
      rewrite dropLeftForgotten (Nat.max floor 22) membership True target (enoughHead floor)
    | _ => cases

--| P3's step at a row: the pairs it drops at the result's left end are
--| ones `meaning` forgets.
theorem rowKeepsMeaning ∀ (expr: Expr): plainExpr (dropAfterRow expr) = plainExpr expr := match expr with
  | Effect row result => rewrite dropLeftForgotten 0 False False result (never => cases)
  | _ => cases

-- P3 around a binder's whole type: `stripBinderType` drops only layers
-- `unwrapped` drops.

theorem stripUnwrapped ∀ (expr: Expr): (stripBinderType expr).unwrapped = expr.unwrapped := match expr with
  | Paren open inner close =>
    match bare: open.bare && close.bare with
      | True => stripUnwrapped inner
      | False => rewrite stripUnwrapped inner
  | _ => cases

theorem groupStripUnwrapped ∀ (group: Group): (dropGroupParens group).plainType = group.plainType := match group with
  | { kind, implicit, open, attributes, auto, names, colon, annotation, default, close, bare } =>
    match strips: !implicit && colon.isSome && default.isNone && auto.isNone with
      | False => byComputing
      | True =>
        match annotation with
          | Some written => rewrite stripUnwrapped written
          | None => byComputing

theorem paramStripUnwrapped ∀ (param: Param): (dropParam param).plainType = param.plainType := match param with
  | Grouped group => rewrite groupStripUnwrapped group
  | TypedPattern open pattern colon annotation close => rewrite stripUnwrapped annotation
  | _ => cases
