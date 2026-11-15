--| The block layout rule, from the printing rules alone, at every width.
--|
--| The parser reads a statement at column `C` and turns away any later line
--| of it that starts at `C` or further left, except `else` (under its `if`)
--| and the tokens inside brackets. Line breaks are indented by the `Nest`s
--| around them, and `Nest` only adds, so every break of a statement printed
--| at `C` starts its line at `C` or deeper: the danger is a break at exactly
--| `C`. The theorems here say each such break, if the engine makes it, is
--| followed by `)`, `]`, `) =` or `else`. They are about the documents the
--| rules build, before the engine chooses between flat and broken groups,
--| `Choice` options or fill separators, so they hold whatever it chooses,
--| at every width.

namespace Toy.Fmt.Proofs
import Toy.Doc (..)
import Toy.Syntax (..)
import Toy.Fmt (..)
import Std (List, Option, Text, Void)

--| The texts the rules print right after a break at a statement's own
--| column: closing brackets, read inside their brackets where line starts
--| don't matter, and `else`, which may stand under its `if`.
def opensAtColumn: Text → Bool
  | ")" => True
  | "]" => True
  | ") =" => True
  | "else" => True
  | _ => False

--| `Some after` if every line break `doc` can make at its own indentation is
--| followed by text from `opensAtColumn` before any other text, whichever
--| way each group, choice and fill goes; `pending` says such a break has just
--| been made and waits for its text, and `after` whether one still waits at
--| the end. Breaks inside a `Nest` or `OneLineBelow` are deeper and don't
--| count. A `Fill`'s separators are breaks at its indentation, so a `Fill`
--| here is turned down (the rules nest every fill).
def Doc.scanLines: Doc → Bool → Option Bool
  | Chunk text _, pending =>
    if pending then
      (if text.isEmpty then Some True
       else if opensAtColumn text then Some False
       else None)
    else Some False
  | Line, _ => Some True
  | SoftLine, _ => Some True
  | HardLine, _ => Some True
  | Nest Zero inner, pending => inner.scanLines pending
  | Nest (Succ _) _, pending => if pending then None else Some False
  | OneLineBelow _, pending => if pending then None else Some False
  | Group inner _, pending => inner.scanLines pending
  | Flatten inner, pending => inner.scanLines pending
  | Concat docs, pending => Doc.scanSeq docs pending
  | Choice options, pending => Doc.scanChoices options pending
  | Fill _, _ => None
  | _, pending => Some pending

--| `scanLines` over docs printed one after another.
def Doc.scanSeq: List Doc → Bool → Option Bool
  | [], pending => Some pending
  | [doc, ..docs], pending =>
    match doc.scanLines pending with
      | Some next => Doc.scanSeq docs next
      | None => None

--| `scanLines` over the options of a `Choice`, any of which may be printed.
def Doc.scanChoices: List Doc → Bool → Option Bool
  | [], pending => Some pending
  | [option, ..others], pending =>
    match option.scanLines pending, Doc.scanChoices others pending with
      | Some one, Some rest => Some (one || rest)
      | _, _ => None

--| An empty doc prints nothing, so it leaves a waiting break waiting.
theorem scanEmptyDoc ∀ (doc: Doc) (pending: Bool) (empty: doc.isEmpty = True): doc.scanLines pending = Some pending :=
  cases

theorem scanSeqFilter ∀ (docs: List Doc) (pending: Bool):
    Doc.scanSeq (docs.filter (doc => not doc.isEmpty)) pending = Doc.scanSeq docs pending :=
  match docs with
    | [] => rfl
    | [doc, ..rest] =>
      match e: doc.isEmpty with
        | True => rewrite scanEmptyDoc doc pending e in scanSeqFilter rest pending
        | False =>
          match n: doc.scanLines pending with
            | Some next => scanSeqFilter rest next
            | None => rfl

theorem scanConcat ∀ (docs: List Doc) (pending: Bool): (Doc.concat docs).scanLines pending = Doc.scanSeq docs pending :=
  rewrite <- scanSeqFilter docs pending in
    match f: docs.filter (doc => not doc.isEmpty) with
      | [] => rfl
      | [only] =>
        match n: only.scanLines pending with
          | Some next => rfl
          | None => rfl
      | [first, second, ..rest] => rfl

--| The first doc of a list, scanned with no break waiting.
def headScan: List Doc → Option Bool
  | [] => None
  | [first, .._] => first.scanLines False

theorem bareScan ∀ (doc: Doc)
    (ok: doc.scanLines False = Some False) (trailing: Option Comment):
    (Doc.concat [doc, trailingComment trailing]).scanLines False = Some False :=
  rewrite scanConcat [doc, trailingComment trailing] False in
    rewrite ok in
      match trailing with
        | None => rfl
        | Some comment => rfl

theorem chainHeadScan ∀ (level: Nat) (expr: Expr)
    (whole: expr.layout.scanLines False = Some False) (more: List Doc):
    headScan (chainParts level expr ++ more) = Some False :=
  match expr with
    | Binary operator left right =>
      match same: operator.level == level with
        | True =>
          rewrite List.appendAssoc (chainParts level left) [link operator right.layout] more in
            chainHeadScan level left (exprScan left) ([link operator right.layout] ++ more)
        | False => whole
    | Var name => whole
    | NumberLiteral digits => whole
    | StringLiteral written => whole
    | Bracketed inner => whole
    | ListLiteral items => whole
    | Call callee arguments => whole
    | Field target name => whole
    | Negate operand => whole
    | If condition whenTrue whenFalse => whole

theorem ifScan ∀ (condition: Expr) (whenTrue whenFalse: Body)
    (conditionOk: condition.layout.scanLines False = Some False)
    (trueOk: (branch whenTrue).scanLines False = Some False)
    (falseOk: (elseBranch whenFalse).scanLines False = Some False):
    (ifLayout condition whenTrue whenFalse).scanLines False = Some False :=
  rewrite scanConcat
        [
          Doc.text "if ",
          condition.layout,
          Doc.text " then",
          branch whenTrue,
          Line,
          Doc.text "else",
          elseBranch whenFalse
        ]
        False in
    rewrite conditionOk, trueOk, falseOk in rfl

theorem branchBare ∀ (blankBefore: Bool) (value: Expr) (trailing: Option Comment)
    (ok: value.layout.scanLines False = Some False):
    (branch { statements = [{ blankBefore, line = Bare value trailing }] }).scanLines False = Some False :=
  rewrite bareScan value.layout ok trailing in rfl

theorem exprScan ∀ (expr: Expr): expr.layout.scanLines False = Some False := match expr with
  | Var name => rfl
  | NumberLiteral digits => rfl
  | StringLiteral written => rfl
  | Bracketed inner =>
    rewrite scanConcat [Doc.text "(", inner.layout, Doc.text ")"] False in rewrite exprScan inner in rfl
  | ListLiteral items => listScan items
  | Call callee arguments =>
    rewrite scanConcat [callee.layout, argumentsLayout arguments] False in
      rewrite exprScan callee in
        match arguments with
          | [] => rfl
          | [first, ..rest] => rfl
  | Field target name => rewrite scanConcat [target.layout, Doc.text ".${name}"] False in rewrite exprScan target in rfl
  | Negate operand =>
    rewrite scanConcat [Doc.text (if operand.startsWithMinus then "- " else "-"), operand.layout] False in
      rewrite exprScan operand in rfl
  | Binary operator left right =>
    let head := chainHeadScan operator.level left (exprScan left) [link operator right.layout]
    match parts: chainParts operator.level left ++ [link operator right.layout] with
      | [first, ..links] => rewrite scanConcat [first, Nest 2 (Doc.concat links)] False in rewrite head in rfl
  | If condition whenTrue whenFalse =>
    ifScan condition whenTrue whenFalse (exprScan condition) (branchScan whenTrue) (elseBranchScan whenFalse)

theorem listScan ∀ (items: List Item): (listLayout items).scanLines False = Some False := match items with
  | [] => rfl
  | [first, ..rest] =>
    match last: [first, ..rest].last with
      | None => rfl
      | Some { comments, value, trailing } =>
        match trailing with
          | None => rfl
          | Some comment => rfl

theorem branchScan ∀ (body: Body): (branch body).scanLines False = Some False := match body with
  | { statements = [] } => rfl
  | { statements = [{ blankBefore, line = Bare value trailing }] } =>
    branchBare blankBefore value trailing (exprScan value)
  | { statements = [{ blankBefore, line = Let name inner }] } => rfl
  | { statements = [{ blankBefore, line = StatementNote comment }] } => rfl
  | { statements = [first, second, ..rest] } => rfl

theorem elseBranchScan ∀ (body: Body): (elseBranch body).scanLines False = Some False := match body with
  | { statements = [] } => rfl
  | { statements = [{ blankBefore, line = Bare value trailing }] } =>
    match value, trailing with
      | If condition whenTrue whenFalse, None =>
        rewrite scanConcat [Doc.text " ", ifLayout condition whenTrue whenFalse] False in
          rewrite ifScan condition whenTrue whenFalse
                (exprScan condition)
                (branchScan whenTrue)
                (elseBranchScan whenFalse) in
            rfl
      | If condition whenTrue whenFalse, Some comment =>
        branchBare blankBefore (If condition whenTrue whenFalse) (Some comment) (exprScan value)
      | _, _ => branchBare blankBefore value trailing (exprScan value)
  | { statements = [{ blankBefore, line = Let name inner }] } => rfl
  | { statements = [{ blankBefore, line = StatementNote comment }] } => rfl
  | { statements = [{ blankBefore, line = Bare value trailing }, second, ..rest] } =>
    match value, trailing with
      | If condition whenTrue whenFalse, None => rfl
      | _, _ => rfl
  | { statements = [{ blankBefore, line = Let name inner }, second, ..rest] } => rfl
  | { statements = [{ blankBefore, line = StatementNote comment }, second, ..rest] } => rfl

theorem afterEqualsScan ∀ (body: Body): body.afterEquals.scanLines False = Some False := match body with
  | { statements = [] } => rfl
  | { statements = [{ blankBefore, line = Bare value trailing }] } =>
    match value with
      | ListLiteral items =>
        let doc := Doc.concat [value.layout, trailingComment trailing]
        rewrite scanConcat [Doc.text " ", doc] False in rewrite bareScan value.layout (exprScan value) trailing in rfl
      | _ => rewrite bareScan value.layout (exprScan value) trailing in rfl
  | { statements = [{ blankBefore, line = Let name inner }] } => rfl
  | { statements = [{ blankBefore, line = StatementNote comment }] } => rfl
  | { statements = [first, second, ..rest] } => rfl

--| A statement printed at column `C`: every line after its first that the
--| engine may start at `C` itself starts with `)`, `]` or `else`, whichever
--| way its groups and choices go, so at every width. Every other line of it
--| is under a `Nest` or `OneLineBelow`, so deeper than `C`, as the parser's
--| layout rule asks of a statement's continuation lines; the statements of
--| a block inside it start two columns deeper still (`below`).
theorem statementScan ∀ (statement: Statement): statement.layout.scanLines False = Some False := match statement with
  | Let name body =>
    rewrite scanConcat [Doc.text "let ${name} =", body.afterEquals] False in rewrite afterEqualsScan body in rfl
  | Bare value trailing => bareScan value.layout (exprScan value) trailing
  | StatementNote comment => rfl

--| As `statementScan`, for a declaration at column 0 the rules lay out; a
--| declaration kept as written is printed as its source text, which the
--| parser read from the same lines.
theorem declarationScan ∀ (declaration: Declaration)
    (laidOut: ∀ (text: Text) => declaration ≠ AsWritten text):
    declaration.layout.scanLines False = Some False :=
  match declaration with
    | Function name parameters body =>
      rewrite scanConcat [header name parameters, body.afterEquals] False in
        match parameters with
          | [] => rewrite afterEqualsScan body in rfl
          | [first, ..rest] => rewrite afterEqualsScan body in rfl
    | Value name body =>
      rewrite scanConcat [Doc.text "let ${name} =", body.afterEquals] False in rewrite afterEqualsScan body in rfl
    | DeclarationNote comment => rfl
    | AsWritten text => Void.exfalso (laidOut text rfl)
