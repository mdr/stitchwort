--| What formatting must keep (docs/proposals/self-hosted-fmt.md §3.4,
--| D3678): a file's tree with each freedom the tidy passes have set to
--| one spelling. Two files are the same program when their meanings are
--| equal, and the top theorem says the formatter keeps `meaning`.
--|
--| Nothing proves this definition right, so it is meant to be read line by
--| line. It is the shared traversal (`Syntax/Traverse.sw`) with steps that
--| forget exactly what a pass changes, where the pass changes it, and
--| nothing else; comments, blank lines and every other token stay. Each
--| thing it forgets is safe because the compiler's reading of the file
--| (`crates/syntax/src/lower`, the tree the elaborator gets) doesn't see
--| it:
--|
--| - **A comma before a closer** (P2): the flag is `False` everywhere.
--|   The compiler's list, tuple, record, pattern, field, attribute and
--|   rule-set readings take the items only ("a trailing comma changes
--|   nothing", `lower/exprs.rs`, `list`).
--| - **A `∀` after a theorem's name** (P1): there whenever P1 writes it, on
--|   a theorem with an explicit `(…)` parameter. The compiler reads a
--|   theorem's parameters the same with or without it.
--| - **A round bracket pair at the left end of a row's result** (P3,
--|   `{Fail} (List Nat)`, `{IO} (f a) + 1`), holding no comment, walking
--|   in through the left operand, a chain's first operand, an
--|   application's head and a field access's target, as P3 does. The
--|   compiler reads a pair in three places only (`lower/exprs.rs`): around
--|   an application that is the head of another, `(f a) b`
--|   (`Expr::Bracketed`); around a list's one range, `[(0 ..< n)]`, which
--|   is never at a row's left end; and around a negative numeral, whose
--|   reading (`NegForm`) depends on the token before its `-`. So at an
--|   application's head, or further left inside one, a pair is forgotten
--|   only around a form that never reads as an application (`atomic`),
--|   and a pair around a negative numeral is never forgotten.
--| - **Round bracket pairs around a binder's or annotation's whole type**
--|   (P3, `(h: (∀ …))`), each layer holding no comment, in a header's
--|   parameters, a `∀`, `∃` or lambda's parameters, a function type's
--|   binder and an annotation `(e: T)`. The whole type is never an
--|   application's head or a list's item, and no `-` there follows a
--|   token that makes it an argument, so the compiler doesn't see these.
--| - **How a group of parameters is split** (P4): a header's (not an
--|   instance's) or a `∀` or lambda's (not an `∃`'s) group of several
--|   names becomes one group a name, where P4 could have made it by
--|   merging: no comment but above its bracket (`bare`), no `auto`,
--|   attributes or default, and a type that names none of its names. The
--|   compiler reads `(a b: T)` as `(a: T) (b: T)` (the Rust tree check's
--|   `one_binder_per_name`); a type naming one of the names would mean the
--|   earlier name in the split form, so such a group stays whole. The test
--|   for naming is every token's text in the type: a use of a local name
--|   is a token with that text, so it may say "names" wrongly, never
--|   "doesn't".
--|
--| `meaning` forgets less than the compiler does (any comment-free pair
--| in the middle of an expression, say): the less it forgets, the less
--| there is to trust.

namespace Fmt
import Std (Bool, Fail, List, Option, Text)
import Syntax (
  BindingKind,
  Comments,
  DefKind,
  Expr,
  Group,
  GroupKind,
  Header,
  Param,
  Pattern,
  SourceFile,
  Steps,
  Tok,
  Word
)

--| A file's tree with the formatter's freedoms set to one spelling.
--| Wrapped so that it isn't printed by mistake: it may not spell a file
--| the parser would read back to it.
type Meaning = { plain: SourceFile }

def SourceFile.meaning (file: SourceFile): Meaning := { plain = file.apply meaningSteps }

def meaningSteps: Steps := {
  expr = plainExpr,
  pattern = plainPattern,
  header = plainHeader,
  decl = (decl => decl),
  fields = (fields => { fields | trailingComma = False }),
  attributes = (attributes => { attributes | trailingComma = False }),
  ruleSet = (set => { set | trailingComma = False })
}

def plainExpr: Expr → Expr
  | Tuple open items _ close => Tuple open items False close
  | ListOf open items _ close => ListOf open items False close
  | Record open base fields _ close => Record open base fields False close
  | Effect row result => Effect row (forgetLeft False result)
  | Annotation open value colon annotation close => Annotation open value colon annotation.unwrapped close
  | FunctionType binder arrow result => FunctionType binder.plainType arrow result
  | Binding kind keyword params arrow body => Binding kind keyword (plainParams kind params) arrow body
  | other => other

def plainPattern: Pattern → Pattern
  | PatternTuple open items _ close => PatternTuple open items False close
  | PatternList open items _ tail close => PatternList open items False tail close
  | PatternRecord fields => PatternRecord { fields | trailingComma = False }
  | PatternCtorFields name fields => PatternCtorFields name { fields | trailingComma = False }
  | other => other

def plainHeader (header: Header): Header := { header |
  params = plainGroups header.kind header.params,
  forallKeyword = plainForall header.kind header.forallKeyword header.params
}

def plainGroups (kind: DefKind) (groups: List Group): List Group :=
  let typed := groups.map Group.plainType
  match kind with
    | DefInstance => typed
    | _ => splitGroups typed

def plainForall (kind: DefKind) (written: Option Word) (groups: List Group): Option Word := match kind, written with
  | DefTheorem, None if groups.any Group.explicit => Some { text = "∀", comments = noComments }
  | _, _ => written

-- Brackets.

def noComments: Comments := { above = [], after = None }

--| Without the comment-free round pairs around it; a pair with a comment
--| stays, and the pairs inside it still go.
def Expr.unwrapped: Expr → Expr
  | Paren open inner close => if open.bare && close.bare then inner.unwrapped else Paren open inner.unwrapped close
  | other => other

def Group.plainType (group: Group): Group := { group | annotation = group.annotation.map Expr.unwrapped }

def Param.plainType: Param → Param
  | Grouped group => Grouped group.plainType
  | TypedPattern open pattern colon annotation close => TypedPattern open pattern colon annotation.unwrapped close
  | other => other

--| Without the comment-free round pairs at its left end. `atomOnly` says
--| the walk has passed an application's head or a field access's target.
def forgetLeft (atomOnly: Bool): Expr → Expr
  | Paren open inner close =>
    if open.bare && close.bare && !inner.negativeNumeral && (!atomOnly || inner.atomic) then forgetLeft atomOnly inner
    else Paren open inner close
  | Infix kind left operator right => Infix kind (forgetLeft atomOnly left) operator right
  | Chain first rest => Chain (forgetLeft atomOnly first) rest
  | App head arguments => App (forgetLeft True head) arguments
  | FieldAccess (Some target) dot field => FieldAccess (Some (forgetLeft True target)) dot field
  | other => other

def Expr.negativeNumeral: Expr → Bool
  | Prefix operator (Atom Num _) => operator.text == "-"
  | Prefix operator (Atom Float _) => operator.text == "-"
  | _ => False

--| The forms that are one bracketed or single-token thing, none of which
--| the compiler reads as an application. A constructor update
--| (`C { r | x = 1 }`) lowers to one, so it isn't here.
def Expr.atomic: Expr → Bool
  | Atom _ _ => True
  | Paren _ _ _ => True
  | Unit _ _ => True
  | Universe _ _ => True
  | Include _ _ => True
  | Tuple _ _ _ _ => True
  | ListOf _ _ _ _ => True
  | Spread _ _ => True
  | Record _ _ _ _ _ => True
  | RecordField _ _ _ => True
  | CtorFields _ (Record _ (Some _) _ _ _) => False
  | CtorFields _ _ => True
  | NamedArg _ _ _ _ _ => True
  | FieldAccess (Some _) _ _ => True
  | OperatorSection _ _ _ _ _ => True
  | Annotation _ _ _ _ _ => True
  | Interpolated _ => True
  | _ => False

-- Parameter groups.

def plainParams (kind: BindingKind) (params: List Param): List Param :=
  let typed := params.map Param.plainType
  match kind with
    | BindsExists => typed
    | _ => splitParams typed

--| Whether the group's type has a token with one of its names' text.
def Group.namesItself (group: Group): Bool := match group.annotation with
  | Some written => (written.lines 0).any (line => group.names.any (name => line.trim == name.text))
  | None => True

def Group.splits (group: Group): Bool :=
  group.bare
    && group.auto.isNone
    && group.attributes.isEmpty
    && group.colon.isSome
    && group.default.isNone
    && group.names.all (name => name.text != "auto")
    && !group.namesItself

--| One group a name, the first with the group's opening bracket and its
--| comments above.
def Group.pieces (group: Group): List Group := match group.names with
  | [first, ..rest] if group.splits =>
    [{ group | names = [first] }, ..rest.map (name => { group | names = [name], open = noComments })]
  | _ => [group]

def splitGroups: List Group → List Group
  | [] => []
  | [first, ..rest] => first.pieces ++ splitGroups rest

def splitParams: List Param → List Param
  | [] => []
  | [Grouped group, ..rest] => group.pieces.map Grouped ++ splitParams rest
  | [other, ..rest] => [other, ..splitParams rest]
