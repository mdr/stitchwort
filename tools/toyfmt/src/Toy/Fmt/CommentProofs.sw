--| Trailing comments keep their owners, from the printing rules alone.
--|
--| The parser gives a trailing comment to the item or statement whose last
--| token comes right before it (Tree.sw). So nothing may be printed between
--| that token and the comment, and nothing after the comment on its line:
--| a closer there would take the comment, any other text would become part
--| of it. The engine prints a `LineSuffix` at the end of its line, so the
--| rules must follow every `LineSuffix` with a line break before any more
--| text, and must not put two on one line. `suffixScan` checks a document
--| for that, over every way its groups, choices and fills can go, so at
--| every width; the theorems here say the rules' documents pass, for every
--| tree whose comments stand where the parser puts them (`CommentsApart`).
--|
--| What the engine adds: a `Line` or `SoftLine` after a waiting comment
--| breaks, whatever its group's mode (`Printer.printDoc` tests for a waiting
--| comment there, as `FillSep` does), so the scan's line breaks are line
--| breaks in the output.

namespace Toy.Fmt.Proofs
import Toy.Doc (..)
import Toy.Syntax (..)
import Toy.Fmt (..)
import Std (List, Option, Text, Void)

--| `Some after` if, however `doc` prints, every `LineSuffix` in it is
--| followed by a line break before any text and before another
--| `LineSuffix`; `pending` says a comment waits for its line break as the
--| doc starts, and `after` whether one still waits at its end. Each break
--| of a `Fill` is a line break whenever a comment waits: the engine's
--| `FillSep` checks.
def Doc.scanSuffix: Doc → Bool → Option Bool
  | Chunk text _, pending => if pending then (if text.isEmpty then Some True else None) else Some False
  | Line, _ => Some False
  | SoftLine, _ => Some False
  | HardLine, _ => Some False
  | LineSuffix _, pending => if pending then None else Some True
  | Nest _ inner, pending => inner.scanSuffix pending
  | Group inner _, pending => inner.scanSuffix pending
  | Flatten inner, pending => inner.scanSuffix pending
  | OneLineBelow inner, _ => inner.scanSuffix False
  | Concat docs, pending => Doc.suffixSeq docs pending
  | Choice options, pending => Doc.suffixChoices options pending
  | Fill items, pending => Doc.suffixFill items pending
  | _, pending => Some pending

def Doc.suffixSeq: List Doc → Bool → Option Bool
  | [], pending => Some pending
  | [doc, ..docs], pending =>
    match doc.scanSuffix pending with
      | Some next => Doc.suffixSeq docs next
      | None => None

def Doc.suffixChoices: List Doc → Bool → Option Bool
  | [], pending => Some pending
  | [option, ..others], pending =>
    match option.scanSuffix pending, Doc.suffixChoices others pending with
      | Some one, Some rest => Some (one || rest)
      | _, _ => None

def Doc.suffixFill: List Doc → Bool → Option Bool
  | [], pending => Some pending
  | [only], pending => only.scanSuffix pending
  | [item, ..items], pending =>
    match item.scanSuffix pending with
      | Some _ => Doc.suffixFill items False
      | None => None

--| Where the parser puts trailing comments, as the rules need it: an
--| expression that ends in a comment (an `if` whose last branch has one)
--| stands only where the rules can break the line after it, and a
--| statement or last item with a comment of its own doesn't end in another.
def Expr.CommentsApart: Expr → Prop
  | Bracketed inner => inner.CommentsApart
  | ListLiteral items => ItemsApart items
  | Call callee arguments => callee.endsWithComment = False ∧ callee.CommentsApart ∧ ItemsApart arguments
  | Field target _ => target.endsWithComment = False ∧ target.CommentsApart
  | Negate operand => operand.endsWithComment = False ∧ operand.CommentsApart
  | Binary _ left right =>
    left.endsWithComment = False ∧ right.endsWithComment = False ∧ left.CommentsApart ∧ right.CommentsApart
  | If condition whenTrue whenFalse =>
    condition.endsWithComment = False ∧ condition.CommentsApart ∧ whenTrue.CommentsApart ∧ whenFalse.CommentsApart
  | _ => True

def Body.CommentsApart: Body → Prop
  | { statements } => StatementsApart statements

def StatementsApart: List (Spaced Statement) → Prop
  | [] => True
  | [{ line, .. }, ..rest] => line.CommentsApart ∧ StatementsApart rest

def Statement.CommentsApart: Statement → Prop
  | Let _ body => body.CommentsApart
  | Bare value None => value.CommentsApart
  | Bare value (Some _) => value.endsWithComment = False ∧ value.CommentsApart
  | StatementNote _ => True

def ItemsApart: List Item → Prop
  | [] => True
  | [{ value, trailing, .. }] => LastApart value trailing
  | [{ value, .. }, ..rest] => value.CommentsApart ∧ ItemsApart rest

--| The last item: the `]` or `)` after it goes below a comment of its own
--| but not below one its value ends in, so it mustn't have both.
def LastApart: Expr → Option Comment → Prop
  | value, None => value.CommentsApart
  | value, Some _ => value.endsWithComment = False ∧ value.CommentsApart

theorem suffixEmptyDoc ∀ (doc: Doc) (pending: Bool)
    (empty: doc.isEmpty = True):
    doc.scanSuffix pending = Some pending :=
  cases

theorem suffixSeqFilter ∀ (docs: List Doc) (pending: Bool):
    Doc.suffixSeq (docs.filter (doc => not doc.isEmpty)) pending = Doc.suffixSeq docs pending :=
  match docs with
    | [] => rfl
    | [doc, ..rest] =>
      match e: doc.isEmpty with
        | True => rewrite suffixEmptyDoc doc pending e in suffixSeqFilter rest pending
        | False =>
          match n: doc.scanSuffix pending with
            | Some next => suffixSeqFilter rest next
            | None => rfl

theorem suffixConcat ∀ (docs: List Doc) (pending: Bool):
    (Doc.concat docs).scanSuffix pending = Doc.suffixSeq docs pending :=
  rewrite <- suffixSeqFilter docs pending in
    match f: docs.filter (doc => not doc.isEmpty) with
      | [] => rfl
      | [only] =>
        match n: only.scanSuffix pending with
          | Some next => rfl
          | None => rfl
      | [first, second, ..rest] => rfl

--| Docs that each print with no comment waiting at either end.
def AllQuiet: List Doc → Prop
  | [] => True
  | [doc, ..docs] => doc.scanSuffix False = Some False ∧ AllQuiet docs

theorem quietSeq ∀ (docs: List Doc) (quiet: AllQuiet docs): Doc.suffixSeq docs False = Some False := match docs with
  | [] => rfl
  | [doc, ..rest] => rewrite And.left quiet in quietSeq rest (And.right quiet)

theorem quietAppend ∀ (front back: List Doc)
    (quietFront: AllQuiet front)
    (quietBack: AllQuiet back):
    AllQuiet (front ++ back) :=
  match front with
    | [] => quietBack
    | [doc, ..rest] => Both (And.left quietFront) (quietAppend rest back (And.right quietFront) quietBack)

theorem suffixSeqAppend ∀ (front back: List Doc) (pending: Bool):
    Doc.suffixSeq (front ++ back) pending
      = (match Doc.suffixSeq front pending with
        | Some next => Doc.suffixSeq back next
        | None => None) :=
  match front with
    | [] => rfl
    | [doc, ..rest] =>
      match n: doc.scanSuffix pending with
        | Some next => suffixSeqAppend rest back next
        | None => rfl

--| The comments printed above an item, each on its line.
theorem aboveQuiet ∀ (comments: List Comment):
    AllQuiet (comments.map (comment => Doc.concat [Doc.text comment.text, HardLine])) :=
  match comments with
    | [] => rfl
    | [comment, ..rest] => Both rfl (aboveQuiet rest)

--| Whether the last item ends in a comment: its own, or one its value
--| ends in.
def lastEnds (items: List Item): Bool := match items.last with
  | Some { trailing = Some _, .. } => True
  | Some { value, .. } => value.endsWithComment
  | None => False

theorem middleItemSuffix ∀ (comments: List Comment) (value: Expr) (trailing: Option Comment)
    (valueOk: value.layout.scanSuffix False = Some value.endsWithComment):
    (itemDoc comments value.layout (closeAfter value (Doc.text ",")) trailing).scanSuffix False
      = Some trailing.isSome :=
  let above := comments.map (comment => Doc.concat [Doc.text comment.text, HardLine])
  let rest := [value.layout, closeAfter value (Doc.text ","), trailingComment trailing]
  rewrite suffixConcat (above ++ rest) False in
    rewrite suffixSeqAppend above rest False in
      rewrite quietSeq above (aboveQuiet comments) in
        rewrite valueOk in
          match value.endsWithComment with
            | True =>
              match trailing with
                | None => rfl
                | Some comment => rfl
            | False =>
              match trailing with
                | None => rfl
                | Some comment => rfl

theorem lastItemSuffix ∀ (comments: List Comment) (value: Expr) (trailing: Option Comment)
    (valueOk: value.layout.scanSuffix False = Some value.endsWithComment)
    (apart: LastApart value trailing):
    (itemDoc comments value.layout Empty trailing).scanSuffix False = Some (lastEnds [{ comments, value, trailing }]) :=
  let above := comments.map (comment => Doc.concat [Doc.text comment.text, HardLine])
  let rest := [value.layout, Empty, trailingComment trailing]
  rewrite suffixConcat (above ++ rest) False in
    rewrite suffixSeqAppend above rest False in
      rewrite quietSeq above (aboveQuiet comments) in
        rewrite valueOk in
          match trailing with
            | None => rfl
            | Some comment => rewrite And.left apart in rfl

theorem fillWithFirst ∀ (opening: Doc) (docs: List Doc)
    (quiet: opening.scanSuffix False = Some False):
    Doc.suffixFill (withFirst docs opening) False = Doc.suffixFill docs False :=
  match docs with
    | [] => rfl
    | [first] =>
      rewrite suffixConcat [opening, first] False in
        rewrite quiet in
          match n: first.scanSuffix False with
            | Some next => rfl
            | None => rfl
    | [first, second, ..rest] =>
      rewrite suffixConcat [opening, first] False in
        rewrite quiet in
          match n: first.scanSuffix False with
            | Some next => rfl
            | None => rfl

theorem argumentsSuffix ∀ (arguments: List Item)
    (inside: Doc.suffixSeq (Doc.joinedWith Line (itemDocs arguments)) False = Some (lastEnds arguments)):
    (argumentsLayout arguments).scanSuffix False = Some False :=
  match arguments with
    | [] => rfl
    | [first, ..rest] =>
      rewrite suffixConcat [SoftLine, joined (itemDocs [first, ..rest]) Line] False in
        rewrite suffixConcat (Doc.joinedWith Line (itemDocs [first, ..rest])) False in rewrite inside in rfl

theorem listSuffix ∀ (items: List Item)
    (fill: Doc.suffixFill (itemDocs items) False = Some (lastEnds items)):
    (listLayout items).scanSuffix False = Some False :=
  match items with
    | [] => rfl
    | [{ comments, value, trailing }, ..rest] =>
      match comments with
        | [] =>
          match last: [{ comments, value, trailing }, ..rest].last with
            | None =>
              rewrite fillWithFirst Empty (itemDocs [{ comments, value, trailing }, ..rest]) rfl in rewrite fill in rfl
            | Some { comments = lastComments, value = lastValue, trailing = lastTrailing } =>
              match lastTrailing with
                | Some comment =>
                  rewrite fillWithFirst Empty (itemDocs [{ comments, value, trailing }, ..rest]) rfl in
                    rewrite fill in rfl
                | None =>
                  match lastValue.endsWithComment with
                    | True =>
                      rewrite fillWithFirst Empty (itemDocs [{ comments, value, trailing }, ..rest]) rfl in
                        rewrite fill in rfl
                    | False =>
                      rewrite fillWithFirst Empty (itemDocs [{ comments, value, trailing }, ..rest]) rfl in
                        rewrite fill in rfl
        | [comment, ..more] =>
          match last: [{ comments, value, trailing }, ..rest].last with
            | None =>
              rewrite fillWithFirst HardLine (itemDocs [{ comments, value, trailing }, ..rest]) rfl in
                rewrite fill in rfl
            | Some { comments = lastComments, value = lastValue, trailing = lastTrailing } =>
              match lastTrailing with
                | Some comment =>
                  rewrite fillWithFirst HardLine (itemDocs [{ comments, value, trailing }, ..rest]) rfl in
                    rewrite fill in rfl
                | None =>
                  match lastValue.endsWithComment with
                    | True =>
                      rewrite fillWithFirst HardLine (itemDocs [{ comments, value, trailing }, ..rest]) rfl in
                        rewrite fill in rfl
                    | False =>
                      rewrite fillWithFirst HardLine (itemDocs [{ comments, value, trailing }, ..rest]) rfl in
                        rewrite fill in rfl

theorem ifSuffix ∀ (condition: Expr) (whenTrue whenFalse: Body)
    (conditionOk: condition.layout.scanSuffix False = Some False)
    (trueOk: (branch whenTrue).scanSuffix False = Some whenTrue.endsWithComment)
    (falseOk: (elseBranch whenFalse).scanSuffix False = Some whenFalse.endsWithComment):
    (ifLayout condition whenTrue whenFalse).scanSuffix False = Some whenFalse.endsWithComment :=
  rewrite suffixConcat
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

theorem linkQuiet ∀ (operator: Operator) (operand: Doc)
    (ok: operand.scanSuffix False = Some False):
    (link operator operand).scanSuffix False = Some False :=
  rewrite suffixConcat [Line, Doc.text "${operator.spelling} ", operand] False in rewrite ok in rfl

--| What a comment waiting before the statements of a block (after the
--| first) leaves waiting after them: each starts on a line of its own.
def endsAfter (pending: Bool) (statements: List (Spaced Statement)): Bool := match statements with
  | [] => pending
  | _ => statementsEndWithComment statements

--| An expression laid out by the rules prints every trailing comment in it
--| at the end of its line, with only line breaks after it, and ends with a
--| comment waiting exactly when it ends in one (`Expr.endsWithComment`).
theorem exprSuffix ∀ (expr: Expr) (apart: expr.CommentsApart):
    expr.layout.scanSuffix False = Some expr.endsWithComment :=
  match expr with
    | Var name => rfl
    | NumberLiteral digits => rfl
    | StringLiteral written => rfl
    | Bracketed inner =>
      rewrite suffixConcat [Doc.text "(", inner.layout, closeAfter inner (Doc.text ")")] False in
        rewrite exprSuffix inner apart in
          match inner.endsWithComment with
            | True => rfl
            | False => rfl
    | ListLiteral items => listSuffix items (itemsFill items apart)
    | Call callee arguments =>
      rewrite suffixConcat [callee.layout, argumentsLayout arguments] False in
        rewrite exprSuffix callee (And.left (And.right apart)) in
          rewrite And.left apart in
            rewrite argumentsSuffix arguments (itemsJoined arguments (And.right (And.right apart))) in rfl
    | Field target name =>
      rewrite suffixConcat [target.layout, Doc.text ".${name}"] False in
        rewrite exprSuffix target (And.right apart) in rewrite And.left apart in rfl
    | Negate operand =>
      rewrite suffixConcat [Doc.text (if operand.startsWithMinus then "- " else "-"), operand.layout] False in
        rewrite exprSuffix operand (And.right apart) in rewrite And.left apart in rfl
    | Binary operator left right =>
      let leftApart := And.left (And.right (And.right apart))
      let leftRaw := exprSuffix left leftApart
      let leftOk := rewrite And.left apart at leftRaw in leftRaw
      let rightRaw := exprSuffix right (And.right (And.right (And.right apart)))
      let rightOk := rewrite And.left (And.right apart) at rightRaw in rightRaw
      let quiet :=
        quietAppend
          (chainParts operator.level left)
          [link operator right.layout]
          (chainQuiet operator.level left leftOk leftApart)
          (Both (linkQuiet operator right.layout rightOk) rfl)
      match parts: chainParts operator.level left ++ [link operator right.layout] with
        | [first, ..links] =>
          rewrite suffixConcat [first, Nest 2 (Doc.concat links)] False in
            rewrite And.left quiet in
              rewrite suffixConcat links False in rewrite quietSeq links (And.right quiet) in rfl
        | [] => rfl
    | If condition whenTrue whenFalse =>
      let conditionRaw := exprSuffix condition (And.left (And.right apart))
      let conditionOk := rewrite And.left apart at conditionRaw in conditionRaw
      ifSuffix condition whenTrue whenFalse conditionOk
        (branchSuffix whenTrue (And.left (And.right (And.right apart))))
        (elseBranchSuffix whenFalse (And.right (And.right (And.right apart))))

theorem chainQuiet ∀ (level: Nat) (expr: Expr)
    (whole: expr.layout.scanSuffix False = Some False) (apart: expr.CommentsApart):
    AllQuiet (chainParts level expr) :=
  match expr with
    | Binary operator left right =>
      match same: operator.level == level with
        | True =>
          let leftApart := And.left (And.right (And.right apart))
          let leftRaw := exprSuffix left leftApart
          let leftOk := rewrite And.left apart at leftRaw in leftRaw
          let rightRaw := exprSuffix right (And.right (And.right (And.right apart)))
          let rightOk := rewrite And.left (And.right apart) at rightRaw in rightRaw
          quietAppend
            (chainParts level left)
            [link operator right.layout]
            (chainQuiet level left leftOk leftApart)
            (Both (linkQuiet operator right.layout rightOk) rfl)
        | False => Both whole rfl
    | Var name => Both whole rfl
    | NumberLiteral digits => Both whole rfl
    | StringLiteral written => Both whole rfl
    | Bracketed inner => Both whole rfl
    | ListLiteral items => Both whole rfl
    | Call callee arguments => Both whole rfl
    | Field target name => Both whole rfl
    | Negate operand => Both whole rfl
    | If condition whenTrue whenFalse => Both whole rfl

theorem itemDocsCons ∀ (first second: Item) (rest: List Item):
    itemDocs [first, second, ..rest]
      = [
        itemDoc first.comments first.value.layout (closeAfter first.value (Doc.text ",")) first.trailing,
        ..itemDocs [second, ..rest]
      ] :=
  match first, second with
    | { comments, value, trailing }, { comments = secondComments, value = secondValue, trailing = secondTrailing } =>
      rfl

theorem joinedWithCons ∀ (separator first: Doc) (docs: List Doc) (more: docs = [] → Void):
    Doc.joinedWith separator [first, ..docs] = [first, separator, ..Doc.joinedWith separator docs] :=
  match docs with
    | [] => Void.exfalso (more rfl)
    | [second, ..rest] => rfl

theorem itemDocsNotEmpty ∀ (first: Item) (rest: List Item) (empty: itemDocs [first, ..rest] = []): Void :=
  match first, rest with | { comments, value, trailing }, [second, ..more] => cases

theorem itemsJoined ∀ (items: List Item)
    (apart: ItemsApart items):
    Doc.suffixSeq (Doc.joinedWith Line (itemDocs items)) False = Some (lastEnds items) :=
  match items with
    | [] => rfl
    | [{ comments, value, trailing }] =>
      match trailing with
        | None => rewrite lastItemSuffix comments value None (exprSuffix value apart) apart in rfl
        | Some comment =>
          rewrite lastItemSuffix comments value (Some comment) (exprSuffix value (And.right apart)) apart in rfl
    | [{ comments, value, trailing }, second, ..rest] =>
      rewrite itemDocsCons { comments, value, trailing } second rest in
        rewrite joinedWithCons Line
              (itemDoc comments value.layout (closeAfter value (Doc.text ",")) trailing)
              (itemDocs [second, ..rest])
              (itemDocsNotEmpty second rest) in
          rewrite middleItemSuffix comments value trailing (exprSuffix value (And.left apart)) in
            itemsJoined [second, ..rest] (And.right apart)

theorem itemsFill ∀ (items: List Item)
    (apart: ItemsApart items):
    Doc.suffixFill (itemDocs items) False = Some (lastEnds items) :=
  match items with
    | [] => rfl
    | [{ comments, value, trailing }] =>
      match trailing with
        | None => lastItemSuffix comments value None (exprSuffix value apart) apart
        | Some comment => lastItemSuffix comments value (Some comment) (exprSuffix value (And.right apart)) apart
    | [{ comments, value, trailing }, second, ..rest] =>
      rewrite itemDocsCons { comments, value, trailing } second rest in
        let tail := itemsFill [second, ..rest] (And.right apart)
        match docs: itemDocs [second, ..rest] with
          | [] => Void.exfalso (itemDocsNotEmpty second rest docs)
          | [next, ..later] =>
            rewrite middleItemSuffix comments value trailing (exprSuffix value (And.left apart)) in tail

theorem singleBranch ∀ (blankBefore: Bool) (line: Statement)
    (lineOk: line.layout.scanSuffix False = Some line.endsWithComment):
    (branch { statements = [{ blankBefore, line }] }).scanSuffix False = Some line.endsWithComment :=
  match line with
    | Bare value trailing =>
      rewrite suffixConcat [HardLine, Doc.concat [value.layout, trailingComment trailing]] False in
        rewrite lineOk in
          match (Bare value trailing).endsWithComment with
            | True => rfl
            | False => rfl
    | Let name inner =>
      rewrite suffixConcat [HardLine, Body.block { statements = [{ blankBefore, line = Let name inner }] }] False in
        rewrite suffixConcat (statementLines 0 [{ blankBefore, line = Let name inner }]) False in rewrite lineOk in rfl
    | StatementNote comment => rfl

theorem branchSuffix ∀ (body: Body) (apart: body.CommentsApart):
    (branch body).scanSuffix False = Some body.endsWithComment :=
  match body with
    | { statements } =>
      let blockOk := blockSuffix statements apart
      match statements with
        | [] => rfl
        | [{ blankBefore, line }] => singleBranch blankBefore line (statementSuffix line (And.left apart))
        | [{ blankBefore, line }, second, ..rest] =>
          match line with
            | Bare value trailing =>
              rewrite suffixConcat
                    [
                      HardLine,
                      Body.block { statements = [{ blankBefore, line = Bare value trailing }, second, ..rest] }
                    ]
                    False in
                rewrite blockOk in rfl
            | Let name inner =>
              rewrite suffixConcat
                    [HardLine, Body.block { statements = [{ blankBefore, line = Let name inner }, second, ..rest] }]
                    False in
                rewrite blockOk in rfl
            | StatementNote comment =>
              rewrite suffixConcat
                    [
                      HardLine,
                      Body.block { statements = [{ blankBefore, line = StatementNote comment }, second, ..rest] }
                    ]
                    False in
                rewrite blockOk in rfl

theorem elseBranchSuffix ∀ (body: Body) (apart: body.CommentsApart):
    (elseBranch body).scanSuffix False = Some body.endsWithComment :=
  match body with
    | { statements } =>
      let blockOk := blockSuffix statements apart
      match statements with
        | [] => rfl
        | [{ blankBefore, line }] =>
          let lineOk := statementSuffix line (And.left apart)
          match line with
            | Bare value trailing =>
              match value, trailing with
                | If condition whenTrue whenFalse, None =>
                  let conditionRaw := exprSuffix condition (And.left (And.right (And.left apart)))
                  let conditionOk := rewrite And.left (And.left apart) at conditionRaw in conditionRaw
                  rewrite suffixConcat [Doc.text " ", ifLayout condition whenTrue whenFalse] False in
                    rewrite ifSuffix condition whenTrue whenFalse conditionOk
                          (branchSuffix whenTrue (And.left (And.right (And.right (And.left apart)))))
                          (elseBranchSuffix whenFalse (And.right (And.right (And.right (And.left apart))))) in
                      rfl
                | _, _ => singleBranch blankBefore (Bare value trailing) lineOk
            | Let name inner => singleBranch blankBefore (Let name inner) lineOk
            | StatementNote comment => rfl
        | [{ blankBefore, line }, second, ..rest] =>
          match line with
            | Bare value trailing =>
              match value, trailing with
                | If condition whenTrue whenFalse, None =>
                  rewrite suffixConcat
                        [
                          HardLine,
                          Body.block { statements = [{ blankBefore, line = Bare value trailing }, second, ..rest] }
                        ]
                        False in
                    rewrite blockOk in rfl
                | _, _ =>
                  rewrite suffixConcat
                        [
                          HardLine,
                          Body.block { statements = [{ blankBefore, line = Bare value trailing }, second, ..rest] }
                        ]
                        False in
                    rewrite blockOk in rfl
            | Let name inner =>
              rewrite suffixConcat
                    [HardLine, Body.block { statements = [{ blankBefore, line = Let name inner }, second, ..rest] }]
                    False in
                rewrite blockOk in rfl
            | StatementNote comment =>
              rewrite suffixConcat
                    [
                      HardLine,
                      Body.block { statements = [{ blankBefore, line = StatementNote comment }, second, ..rest] }
                    ]
                    False in
                rewrite blockOk in rfl

theorem statementSuffix ∀ (statement: Statement) (apart: statement.CommentsApart):
    statement.layout.scanSuffix False = Some statement.endsWithComment :=
  match statement with
    | Let name body =>
      rewrite suffixConcat [Doc.text "let ${name} =", body.afterEquals] False in
        rewrite afterEqualsSuffix body apart in rfl
    | Bare value None => rewrite suffixConcat [value.layout, Empty] False in rewrite exprSuffix value apart in rfl
    | Bare value (Some comment) =>
      rewrite suffixConcat [value.layout, LineSuffix comment.text] False in
        rewrite exprSuffix value (And.right apart) in rewrite And.left apart in rfl
    | StatementNote comment => rfl

theorem afterEqualsSuffix ∀ (body: Body) (apart: body.CommentsApart):
    body.afterEquals.scanSuffix False = Some body.endsWithComment :=
  match body with
    | { statements } =>
      let blockOk := blockSuffix statements apart
      match statements with
        | [] => rfl
        | [{ blankBefore, line }] =>
          let lineOk := statementSuffix line (And.left apart)
          match line with
            | Bare value trailing =>
              match value with
                | ListLiteral items =>
                  rewrite suffixConcat
                        [Doc.text " ", Doc.concat [(ListLiteral items).layout, trailingComment trailing]]
                        False in
                    rewrite lineOk in
                      match (Bare (ListLiteral items) trailing).endsWithComment with
                        | True => rfl
                        | False => rfl
                | _ =>
                  rewrite suffixConcat [HardLine, Doc.concat [value.layout, trailingComment trailing]] False in
                    rewrite lineOk in
                      match (Bare value trailing).endsWithComment with
                        | True => rfl
                        | False => rfl
            | Let name inner =>
              rewrite suffixConcat
                    [HardLine, Body.block { statements = [{ blankBefore, line = Let name inner }] }]
                    False in
                rewrite blockOk in rfl
            | StatementNote comment => rfl
        | [{ blankBefore, line }, second, ..rest] =>
          match line with
            | Bare value trailing =>
              rewrite suffixConcat
                    [
                      HardLine,
                      Body.block { statements = [{ blankBefore, line = Bare value trailing }, second, ..rest] }
                    ]
                    False in
                rewrite blockOk in rfl
            | Let name inner =>
              rewrite suffixConcat
                    [HardLine, Body.block { statements = [{ blankBefore, line = Let name inner }, second, ..rest] }]
                    False in
                rewrite blockOk in rfl
            | StatementNote comment =>
              rewrite suffixConcat
                    [
                      HardLine,
                      Body.block { statements = [{ blankBefore, line = StatementNote comment }, second, ..rest] }
                    ]
                    False in
                rewrite blockOk in rfl

theorem blockSuffix ∀ (statements: List (Spaced Statement))
    (apart: StatementsApart statements):
    (Body.block { statements }).scanSuffix False = Some (statementsEndWithComment statements) :=
  rewrite suffixConcat (statementLines 0 statements) False in
    match statements with
      | [] => rfl
      | [{ blankBefore, line }, ..rest] =>
        rewrite statementSuffix line (And.left apart) in
          rewrite linesSuffix 0 rest line.endsWithComment (And.right apart) in
            match rest with
              | [] => rfl
              | [next, ..more] => rfl

--| The statements of a block after its first: each starts its own line,
--| so a comment waiting before them doesn't reach them.
theorem linesSuffix ∀ (index: Nat) (statements: List (Spaced Statement)) (pending: Bool)
    (apart: StatementsApart statements):
    Doc.suffixSeq (statementLines (Succ index) statements) pending = Some (endsAfter pending statements) :=
  match statements with
    | [] => rfl
    | [{ blankBefore, line }, ..rest] =>
      match blankBefore with
        | True =>
          rewrite statementSuffix line (And.left apart) in
            rewrite linesSuffix (index + 1) rest line.endsWithComment (And.right apart) in
              match rest with
                | [] => rfl
                | [next, ..more] => rfl
        | False =>
          rewrite statementSuffix line (And.left apart) in
            rewrite linesSuffix (index + 1) rest line.endsWithComment (And.right apart) in
              match rest with
                | [] => rfl
                | [next, ..more] => rfl

--| Declarations: their comments stand where statements' do.
def Declaration.CommentsApart: Declaration → Prop
  | Function _ _ body => body.CommentsApart
  | Value _ body => body.CommentsApart
  | DeclarationNote _ => True
  | AsWritten _ => True

theorem asWrittenSuffix ∀ (lines: List Text):
    Doc.suffixSeq (Doc.joinedWith HardLine (lines.map Doc.text)) False = Some False :=
  match lines with
    | [] => rfl
    | [only] => rfl
    | [line, next, ..rest] => asWrittenSuffix [next, ..rest]

theorem parametersSuffix ∀ (names: List Text):
    Doc.suffixSeq (Doc.joinedWith (Doc.concat [Doc.text ",", Line]) (names.map Doc.text)) False = Some False :=
  match names with
    | [] => rfl
    | [only] => rfl
    | [name, next, ..rest] => parametersSuffix [next, ..rest]

--| A declaration laid out by the rules: every trailing comment in it ends
--| its line, with only line breaks after it, and it ends with a comment
--| waiting exactly when its body ends in one; a declaration kept as written
--| holds no trailing comment the engine places.
theorem declarationSuffix ∀ (declaration: Declaration) (apart: declaration.CommentsApart):
    declaration.layout.scanSuffix False
      = Some
        (match declaration with
          | Function _ _ body => body.endsWithComment
          | Value _ body => body.endsWithComment
          | _ => False) :=
  match declaration with
    | Function name parameters body =>
      rewrite suffixConcat [header name parameters, body.afterEquals] False in
        match parameters with
          | [] => rewrite afterEqualsSuffix body apart in rfl
          | [first, ..rest] =>
            let separator := Doc.concat [Doc.text ",", Line]
            rewrite suffixConcat [SoftLine, joined ([first, ..rest].map Doc.text) separator] False in
              rewrite suffixConcat (Doc.joinedWith separator ([first, ..rest].map Doc.text)) False in
                rewrite parametersSuffix [first, ..rest] in rewrite afterEqualsSuffix body apart in rfl
    | Value name body =>
      rewrite suffixConcat [Doc.text "let ${name} =", body.afterEquals] False in
        rewrite afterEqualsSuffix body apart in rfl
    | DeclarationNote comment => rfl
    | AsWritten text =>
      rewrite suffixConcat (Doc.joinedWith HardLine (text.lines.map Doc.text)) False in asWrittenSuffix text.lines
