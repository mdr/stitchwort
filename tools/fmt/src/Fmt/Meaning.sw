--| What formatting must keep (docs/proposals/self-hosted-fmt.md §3.4,
--| D3678): a file's tree with each freedom the tidy passes have set to
--| one spelling. Two files are the same program when their meanings are
--| equal, and the top theorem says the formatter keeps `meaning`.
--|
--| Left out on purpose, so not part of "the same program":
--|
--| - **Positions.** The tree keeps none, and every position moves under
--|   formatting. The compiler reads them only for messages (spans, and a
--|   negative numeral's `NegForm`, `lower/numbers.rs`).
--| - **Comments.** Every step blanks a node's comments before it reads
--|   it (`Fmt/Blank.sw`; `Group.bare`, a summary of comments, goes with
--|   them), and the file's end comments are blanked. The
--|   compiler reads a comment only to resolve a `--|` doc's links
--|   (`W-DOC-LINK`), and docs attach by where comments sit: both are
--|   `CommentsKept`'s job, stated over the leaves, not this one's.
--|
--| Nothing proves this definition right, so it is meant to be read line by
--| line. It is the shared traversal (`Syntax/Traverse.sw`) with steps that
--| forget what a pass changes, at least where the pass changes it; every
--| other token stays. Each thing it forgets is safe because the
--| compiler's reading of the file (`crates/syntax/src/lower`, the tree the
--| elaborator gets) doesn't see it:
--|
--| - **A comma before a closer** (P2): the flag is `False` everywhere.
--|   The compiler's list, tuple, record, pattern, field, attribute and
--|   rule-set readings take the items only ("a trailing comma changes
--|   nothing", `lower/exprs.rs`, `list`).
--| - **A `∀` after a definition's name** (P1): absent on every header.
--|   The parser allows it on a theorem only, and the lowering skips it
--|   (`lower/definitions.rs`, "cosmetic", D3472), so the term and hash are
--|   those of the header without it.
--| - **A round bracket pair at the left end of a row's result** (P3,
--|   `{Fail} (List Nat)`, `{IO} (f a) + 1`), walking in through the left
--|   operand, a chain's first operand, an application's head and a field
--|   access's target, as P3 does. The compiler reads a pair in three places
--|   only (`lower/exprs.rs`): at an application's head with arguments
--|   after it, when the head's first token is `(` and the head lowers to an
--|   application (`app`, `Expr::Bracketed`: `(f a) b`, and `(C { r | x = 1
--|   }) b`, since a constructor update lowers to `C` applied to the
--|   update); around a list's one range, `[(0 ..< n)]`, which is never at a
--|   row's left end; and around a negative numeral, whose reading
--|   (`NegForm`) depends on the token before its `-`. So at an
--|   application's head, or further left inside one, a pair is forgotten
--|   only around a form that never lowers to an application (`atomic`),
--|   and a pair around a negative numeral is never forgotten.
--| - **Round bracket pairs around a binder's or annotation's whole type**
--|   (P3, `(h: (∀ …))`), in a header's parameters, a `∀`, `∃` or lambda's
--|   parameters, a function type's binder and an annotation `(e: T)`. The
--|   whole type is never an application's head or a list's item, and no
--|   `-` there follows a token that makes it an argument, so the compiler
--|   doesn't see these.
--| - **How a group of parameters is split** (P4): a header's (not an
--|   instance's) or a `∀` or lambda's (not an `∃`'s) group of several
--|   names becomes one group a name, where P4 could have made it by
--|   merging: no `auto`, attributes or default, and a type that names none
--|   of its names. The compiler reads a group exactly as its split form
--|   (D3679: the lowering splits a group, `Written::binders` in `lower/types.rs`, so each
--|   name checks its own copy of the type and a hole in it is solved per
--|   name). A type naming one of the names would mean the
--|   earlier name in the split form, so such a group stays whole. The test
--|   for naming is every token's text in the type: a use of a local name
--|   is a token with that text, so it may say "names" wrongly, never
--|   "doesn't".
--|
--| `meaning` forgets less than the compiler does (any pair in the middle
--| of an expression, say): the less it forgets, the less there is to
--| trust.

namespace Fmt
import Std (Bool, Fail, List, Nat, Option, Text)
import Syntax (
  BindingKind,
  Comments,
  DefKind,
  Expr,
  Group,
  GroupKind,
  Header,
  Leaf,
  Lexed,
  Param,
  Pattern,
  SourceFile,
  Steps,
  Tok,
  Trivia
)

--| A file's tree with the formatter's freedoms set to one spelling.
--| Wrapped so that it isn't printed by mistake: it may not spell a file
--| the parser would read back to it.
type Meaning = { plain: SourceFile }

--| Each step blanks the node's comments (`Fmt/Blank.sw`) before it reads
--| it, so the traversal is `blankSteps`' and then these, one node at a
--| time.
def SourceFile.meaning (file: SourceFile): Meaning := { plain = file.withoutEnd.apply meaningSteps }

--| Without the comments after the last token.
def SourceFile.withoutEnd (file: SourceFile): SourceFile := { file | end = Comments.none }

def meaningSteps: Steps := {
  expr = (expr => plainExpr (blankExpr expr)),
  pattern = (pattern => plainPattern (blankPattern pattern)),
  header = (header => plainHeader (blankHeader header)),
  decl = blankDecl,
  fields = (fields => { blankFields fields | trailingComma = False }),
  attributes = (attributes => { blankAttributes attributes | trailingComma = False }),
  ruleSet = (set => { blankRuleSet set | trailingComma = False })
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

def plainHeader (header: Header): Header :=
  { header | params = plainGroups header.kind header.params, forallKeyword = None }

def plainGroups (kind: DefKind) (groups: List Group): List Group :=
  let typed := groups.map Group.plainType
  match kind with
    | DefInstance => typed
    | _ => splitGroups typed

-- Brackets.

--| Without the round pairs around it.
def Expr.unwrapped: Expr → Expr
  | Paren _ inner _ => inner.unwrapped
  | other => other

def Group.plainType (group: Group): Group := { group | annotation = group.annotation.map Expr.unwrapped }

def Param.plainType: Param → Param
  | Grouped group => Grouped group.plainType
  | TypedPattern open pattern colon annotation close => TypedPattern open pattern colon annotation.unwrapped close
  | other => other

--| Without the round pairs at its left end. `atomOnly` says
--| the walk has passed an application's head or a field access's target.
def forgetLeft (atomOnly: Bool): Expr → Expr
  | Paren open inner close =>
    if !inner.negativeNumeral && (!atomOnly || inner.atomic) then forgetLeft atomOnly inner else Paren open inner close
  | Infix kind left operator right => Infix kind (forgetLeft atomOnly left) operator right
  | Chain first rest => Chain (forgetLeft atomOnly first) rest
  | App head arguments => App (forgetLeft True head) arguments
  | FieldAccess (Some target) dot field => FieldAccess (Some (forgetLeft True target)) dot field
  | other => other

def Expr.negativeNumeral: Expr → Bool
  | Prefix operator (Atom Num _) | Prefix operator (Atom Float _) => operator.text == "-"
  | _ => False

--| The forms a pair may be forgotten around at an application's head: one
--| bracketed or single-token thing, none of which lowers to an
--| application. A list of what may go, so a form added to the tree is kept
--| until someone checks its lowering. A constructor update
--| (`C { r | x = 1 }`) lowers to an application, so it isn't here.
def Expr.atomic: Expr → Bool
  | Atom _ _ |
      Paren _ _ _ |
      Unit _ _ |
      Universe _ _ |
      Include _ _ |
      Tuple _ _ _ _ |
      ListOf _ _ _ _ |
      Spread _ _ |
      Record _ _ _ _ _ |
      RecordField _ _ _ => True
  | CtorFields _ (Record _ (Some _) _ _ _) => False
  | CtorFields _ _ |
      NamedArg _ _ _ _ _ |
      FieldAccess (Some _) _ _ |
      OperatorSection _ _ _ _ _ |
      Annotation _ _ _ _ _ |
      Interpolated _ => True
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
  group.auto.isNone
    && group.attributes.isEmpty
    && group.colon.isSome
    && group.default.isNone
    && group.names.all (name => name.text != "auto")
    && !group.namesItself

--| One group a name.
def Group.pieces (group: Group): List Group := match group.names with
  | [first, ..rest] if group.splits => [{ group | names = [first] }, ..rest.map (name => { group | names = [name] })]
  | _ => [group]

def splitGroups: List Group → List Group
  | [] => []
  | [first, ..rest] => first.pieces ++ splitGroups rest

def splitParams: List Param → List Param
  | [] => []
  | [Grouped group, ..rest] => group.pieces.map Grouped ++ splitParams rest
  | [other, ..rest] => [other, ..splitParams rest]

-- Comments: what `meaning` leaves out, stated over the leaves.

--| A comment as a reader finds it: its text, whether it is on a line of
--| its own (or trails a token), and whether a blank line is above it.
type CommentView = { text: Text, ownLine: Bool, blankAbove: Bool }

--| A token that holds comments: its text, how many own-line comments are
--| above it, whether one trails it, and whether a blank line separates
--| the last comment above from it (which decides whether they are its
--| doc, `docs.rs`, `attached`).
type Holder = { token: Text, above: Nat, trailing: Bool, blankBelow: Bool }

def Trivia.commentViews (trivia: Trivia): List CommentView :=
  trivia.leading.map (comment => { text = comment.text, ownLine = True, blankAbove = comment.blankLines > 0 })
    ++ trivia.trailing.toList.map (comment => { text = comment.text, ownLine = False, blankAbove = False })

--| Every comment in the file, in order.
def Lexed.commentViews (lexed: Lexed): List CommentView :=
  lexed.leaves.flatMap (leaf => leaf.trivia.commentViews) ++ lexed.end.commentViews

--| The tokens that hold comments, in order.
def Lexed.holders (lexed: Lexed): List Holder := lexed.leaves.filterMap (leaf => leaf.holder)

def Leaf.holder (leaf: Leaf): Option Holder :=
  if leaf.trivia.leading.isEmpty && leaf.trivia.trailing.isNone then None
  else
    Some {
      token = leaf.token.text,
      above = leaf.trivia.leading.length,
      trailing = leaf.trivia.trailing.isSome,
      blankBelow = !leaf.trivia.leading.isEmpty && leaf.trivia.blankLines > 0
    }

--| The views with the first comment's blank line above it left out: the
--| first thing printed in a file has nothing above it (D3695).
def unheaded: List CommentView → List CommentView
  | [] => []
  | [first, ..rest] => [{ first | blankAbove = False }, ..rest]

--| A holder with its blank line below left out if it is a closer's: a
--| closer is never a declaration's or member's first token, so no doc
--| reads it (D3695).
def Holder.forDocs (holder: Holder): Holder := { holder | blankBelow = holder.blankBelow && !isCloserText holder.token }

--| What formatting keeps of a file's comments, between the source's leaves
--| and the output's, each after comment placement; the source's with P2's commas
--| taken out first (`settledBare`), which moves a comment held by a
--| deleted comma to the closer after it, or to the token before it if it
--| trailed the comma (K1). Three things, the statement of
--| `tidyKeepsComments` (SW-3878 review, S1):
--|
--| 1. the comments in order, each with its text, whether it is own-line
--|    or trailing, and whether a blank line is above it (`commentViews`,
--|    the file's end included): this is `W-DOC-LINK`'s input;
--| 2. each on the same token (`holders`: the comment-holding tokens in
--|    order, each with its text and how many comments it holds; with 1,
--|    that pins every comment to its token), except a deleted comma's, as
--|    above;
--| 3. whether a blank line separates the comments above a token from it
--|    (`Holder.blankBelow`), which decides a declaration's or member's doc.
--|
--| Two blank lines are left out, as no doc depends on them (D3695, Matt,
--| 19 Nov 2026: "if there's a blank line here or there, that's not
--| something I'm interested in strictly specifying"): the one above the
--| file's first comment (`unheaded`; the printer starts a file with its
--| first comment), and the one between a closer and the comments above it
--| (`Holder.forDocs`; the printer sets a closer straight below them).
--|
--| A token holding no comment may come or go (a dropped bracket, a merged
--| group's `: T) (`, a written `∀`): P3 and P4 touch only tokens with none.
--| Slice 1's theorem is `slice1KeepsComments` (`Fmt.CommentsKeptProof`).
def CommentsKept (source output: Lexed): Prop :=
  unheaded source.settledBare.commentViews = unheaded output.settled.commentViews
    ∧ source.settledBare.holders.map Holder.forDocs = output.settled.holders.map Holder.forDocs
