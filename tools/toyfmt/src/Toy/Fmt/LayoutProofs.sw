--| The block layout rule, from the printing rules alone, at every width.
--|
--| The parser reads a statement at column `C` and turns away any later line
--| of it that starts at `C` or further left, except `else` (under its `if`)
--| and the tokens inside brackets. Line breaks are indented by the `Nest`s
--| around them, and `Nest` only adds, so every break of a statement printed
--| at `C` starts its line at `C` or deeper: the danger is a line at exactly
--| `C`. The theorems here say each such line, if the engine makes it,
--| starts with `)`, `]` or `else`, or holds an own-line comment, which the
--| parser doesn't read as a token. They are about the documents the rules
--| build, before the engine chooses between flat and broken groups,
--| `Choice` options or fill separators, so they hold whatever it chooses,
--| at every width.
--|
--| Comment breaks are deeper than the line they break by construction
--| (`Toy.Doc.Proofs.continuationDeeper`); a `LineStart` is one, unless a
--| line starts there anyway.

namespace Toy.Fmt.Proofs
import Toy.Doc (..)
import Toy.Syntax (..)
import Toy.Fmt (..)
import Std (Bool, List, Option, Text, Void)

--| The texts the rules print first on a line at a statement's own column:
--| closing brackets, read inside their brackets where line starts don't
--| matter, and `else`, which may stand under its `if`.
def opensAtColumn: Text → Bool
  | ")" => True
  | "]" => True
  | "else" => True
  | _ => False

--| Where a scan of a document stands: on a line deeper than the
--| statement's column (or its first line); after a line break at that
--| column, waiting for the line's first text; or on a line at that column
--| that started with a text, which `opens` says is one of `opensAtColumn`.
--| A line at the column that ends in `CommentEnd` holds an own-line
--| comment, whatever its text, and the next line is at the column again.
type Scan = | Clear | Waiting | Started (opens: Bool)

--| A scan may end, or go on into anything, here.
def Scan.settled: Scan → Bool
  | Clear => True
  | Waiting => False
  | Started opens => opens

def Scan.text (scan: Scan) (opens: Bool): Scan := match scan with
  | Waiting => Started opens
  | _ => scan

--| A line break at the doc's own indentation.
def Scan.lineBreak: Scan → Option Scan
  | Clear => Some Waiting
  | Waiting => Some Waiting
  | Started opens => if opens then Some Waiting else None

def Scan.commentEnd: Scan → Scan
  | Clear => Clear
  | _ => Waiting

--| A break deeper than the doc's indentation; a line still waiting at the
--| column would be left without its text.
def Scan.deeper: Scan → Option Scan
  | Clear => Some Clear
  | Waiting => None
  | Started opens => if opens then Some Clear else None

--| A `LineStart` does nothing at the start of a line, and is a comment
--| break, deeper, anywhere else.
def Scan.lineStart: Scan → Option Scan
  | Waiting => Some Waiting
  | scan => scan.deeper

--| Into a `Nest` deeper than the doc: its breaks are deeper, except that a
--| closer's comments (`closer`) start by moving a waiting line there.
def Scan.intoNest (scan: Scan) (inner: Doc): Option Scan := match scan with
  | Waiting => if inner.startsHere then Some Clear else None
  | _ => scan.deeper

def Doc.startsHere: Doc → Bool
  | Concat [LineStartHere, .._] => True
  | _ => False

--| Where any of a `Choice`'s options may leave the scan; settled scans that
--| differ join as the stricter `Started True`.
def Scan.join: Scan → Scan → Option Scan
  | Clear, Clear => Some Clear
  | Waiting, Waiting => Some Waiting
  | one, other => if one.settled && other.settled then Some (Started True) else None

--| The scan after `doc`, or `None` if a line at the statement's column
--| could start with anything else, whichever way each group, choice and
--| fill goes. A `Fill`'s separators are breaks at its indentation, so a
--| `Fill` here is turned down (the rules nest every fill).
def Doc.scanLines: Doc → Scan → Option Scan
  | Chunk text _, scan => Some (scan.text (opensAtColumn text))
  | Line, scan => scan.lineBreak
  | SoftLine, scan => scan.lineBreak
  | HardLine, scan => scan.lineBreak
  | CommentEnd, scan => Some scan.commentEnd
  | LineStart, scan => scan.lineStart
  | Nest Zero inner, scan => inner.scanLines scan
  | Nest (Succ _) inner, scan => scan.intoNest inner
  | OneLineBelow _, scan => scan.deeper
  | Group inner _, scan => inner.scanLines scan
  | Flatten inner, scan => inner.scanLines scan
  | Concat docs, scan => Doc.scanSeq docs scan
  | Choice options, scan => Doc.scanChoices options scan
  | Fill _, _ => None
  | _, scan => Some scan

--| `scanLines` over docs printed one after another.
def Doc.scanSeq: List Doc → Scan → Option Scan
  | [], scan => Some scan
  | [doc, ..docs], scan =>
    match doc.scanLines scan with
      | Some next => Doc.scanSeq docs next
      | None => None

--| `scanLines` over the options of a `Choice`, any of which may be printed.
def Doc.scanChoices: List Doc → Scan → Option Scan
  | [], scan => Some scan
  | [option, ..others], scan =>
    match option.scanLines scan, Doc.scanChoices others scan with
      | Some one, Some rest => Scan.join one rest
      | _, _ => None

--| An empty doc prints nothing, so it leaves the scan as it is.
theorem scanEmptyDoc ∀ (doc: Doc) (scan: Scan) (empty: doc.isEmpty = True): doc.scanLines scan = Some scan := cases

theorem scanSeqFilter ∀ (docs: List Doc) (scan: Scan):
    Doc.scanSeq (docs.filter (doc => not doc.isEmpty)) scan = Doc.scanSeq docs scan :=
  match docs with
    | [] => rfl
    | [doc, ..rest] =>
      match e: doc.isEmpty with
        | True => rewrite scanEmptyDoc doc scan e in scanSeqFilter rest scan
        | False =>
          match n: doc.scanLines scan with
            | Some next => scanSeqFilter rest next
            | None => rfl

theorem scanConcat ∀ (docs: List Doc) (scan: Scan): (Doc.concat docs).scanLines scan = Doc.scanSeq docs scan :=
  rewrite <- scanSeqFilter docs scan in
    match f: docs.filter (doc => not doc.isEmpty) with
      | [] => rfl
      | [only] =>
        match n: only.scanLines scan with
          | Some next => rfl
          | None => rfl
      | [first, second, ..rest] => rfl

-- What the settled scans do.

theorem textSettled ∀ (scan: Scan) (settled: scan.settled = True) (opens: Bool): scan.text opens = scan :=
  match scan with
    | Clear => rfl
    | Started found => rfl

theorem lineBreakSettled ∀ (scan: Scan) (settled: scan.settled = True): scan.lineBreak = Some Waiting := match scan with
  | Clear => rfl
  | Started True => rfl

theorem deeperSettled ∀ (scan: Scan) (settled: scan.settled = True): scan.deeper = Some Clear := match scan with
  | Clear => rfl
  | Started True => rfl

theorem lineStartSettled ∀ (scan: Scan) (settled: scan.settled = True): scan.lineStart = Some Clear := match scan with
  | Clear => rfl
  | Started True => rfl

theorem intoNestSettled ∀ (scan: Scan) (settled: scan.settled = True) (inner: Doc): scan.intoNest inner = Some Clear :=
  match scan with
    | Clear => rfl
    | Started True => rfl

theorem joinSettled ∀ (one other: Scan)
    (oneSettled: one.settled = True)
    (otherSettled: other.settled = True):
    ∃ (joined: Scan) => Scan.join one other = Some joined ∧ joined.settled = True :=
  match one, other with
    | Clear, Clear => Witness Clear (Both rfl rfl)
    | Clear, Started opens => rewrite otherSettled in Witness (Started True) (Both rfl rfl)
    | Started opens, Clear => rewrite oneSettled in Witness (Started True) (Both rfl rfl)
    | Started a, Started b => rewrite oneSettled, otherSettled in Witness (Started True) (Both rfl rfl)

-- Docs that keep a settled scan settled.

--| From any settled scan, `doc` leaves the scan settled.
def Keeps (doc: Doc): Prop :=
  ∀ (scan: Scan) => scan.settled = True → ∃ (after: Scan) => doc.scanLines scan = Some after ∧ after.settled = True

def KeepsSeq (docs: List Doc): Prop :=
  ∀ (scan: Scan) => scan.settled = True → ∃ (after: Scan) => Doc.scanSeq docs scan = Some after ∧ after.settled = True

def KeepsChoices (options: List Doc): Prop :=
  ∀ (scan: Scan) => scan.settled = True
    → ∃ (after: Scan) => Doc.scanChoices options scan = Some after ∧ after.settled = True

theorem keepsSeqNil: KeepsSeq [] := scan settled => Witness scan (Both rfl settled)

theorem keepsSeqCons ∀ (doc: Doc) (docs: List Doc) (first: Keeps doc) (rest: KeepsSeq docs): KeepsSeq [doc, ..docs] :=
  scan settled =>
    match first scan settled with | Witness next (Both ran nextSettled) => rewrite ran in rest next nextSettled

theorem keepsConcat ∀ (docs: List Doc) (all: KeepsSeq docs): Keeps (Doc.concat docs) := scan settled =>
  rewrite scanConcat docs scan in all scan settled

theorem keepsChoicesNil: KeepsChoices [] := scan settled => Witness scan (Both rfl settled)

theorem keepsChoicesCons ∀ (option: Doc) (others: List Doc)
    (first: Keeps option)
    (rest: KeepsChoices others):
    KeepsChoices [option, ..others] :=
  scan settled =>
    match first scan settled, rest scan settled with
      | Witness one (Both ranOne oneSettled), Witness other (Both ranOther otherSettled) =>
        rewrite ranOne, ranOther in joinSettled one other oneSettled otherSettled

theorem keepsChoice ∀ (options: List Doc) (all: KeepsChoices options): Keeps (Choice options) := all

theorem keepsGroup ∀ (inner: Doc) (ok: Keeps inner): Keeps (Doc.group inner) := ok

theorem keepsFlatten ∀ (inner: Doc) (ok: Keeps inner): Keeps (Flatten inner) := ok

theorem keepsChunk ∀ (text: Text) (width: Nat): Keeps (Chunk text width) := scan settled =>
  rewrite textSettled scan settled (opensAtColumn text) in Witness scan (Both rfl settled)

theorem keepsText ∀ (text: Text): Keeps (Doc.text text) := keepsChunk text text.length

theorem keepsEmpty: Keeps Empty := scan settled => Witness scan (Both rfl settled)

--| Breaks inside a deeper `Nest` are deeper than the statement's column.
theorem keepsNest ∀ (more: Nat) (inner: Doc): Keeps (Nest (Succ more) inner) := scan settled =>
  rewrite intoNestSettled scan settled inner in Witness Clear (Both rfl rfl)

theorem keepsOneLineBelow ∀ (inner: Doc): Keeps (OneLineBelow inner) := scan settled =>
  rewrite deeperSettled scan settled in Witness Clear (Both rfl rfl)

theorem keepsTrailing ∀ (trailing: Option Comment): Keeps (trailingComment trailing) := match trailing with
  | None => keepsEmpty
  | Some comment => scan settled => Witness scan (Both rfl settled)

--| A line break at the doc's indentation, then a doc that, from there,
--| starts its line with one of `opensAtColumn`.
theorem keepsSeqBreak ∀ (break opener: Doc) (docs: List Doc)
    (breaks: ∀ (scan: Scan) => scan.settled = True → break.scanLines scan = Some Waiting)
    (opens: opener.scanLines Waiting = Some (Started True))
    (rest: KeepsSeq docs):
    KeepsSeq [break, opener, ..docs] :=
  scan settled => rewrite breaks scan settled, opens in rest (Started True) rfl

theorem lineBreaks ∀ (scan: Scan) (settled: scan.settled = True): Doc.scanLines Line scan = Some Waiting :=
  lineBreakSettled scan settled

theorem softLineBreaks ∀ (scan: Scan) (settled: scan.settled = True): Doc.scanLines SoftLine scan = Some Waiting :=
  lineBreakSettled scan settled

theorem hardLineBreaks ∀ (scan: Scan) (settled: scan.settled = True): Doc.scanLines HardLine scan = Some Waiting :=
  lineBreakSettled scan settled

-- Tokens and their comments.

def commentLines (comments: List Comment): List Doc :=
  comments.map (comment => Doc.concat [Doc.text comment.text, CommentEnd])

--| Own-line comments on deeper lines leave the scan there.
theorem commentLinesClear ∀ (comments: List Comment): Doc.scanSeq (commentLines comments) Clear = Some Clear :=
  match comments with
    | [] => rfl
    | [comment, ..rest] => commentLinesClear rest

--| Own-line comments on lines at the statement's column don't count: the
--| next line is at the column again, waiting for its text.
theorem commentLinesWaiting ∀ (comments: List Comment): Doc.scanSeq (commentLines comments) Waiting = Some Waiting :=
  match comments with
    | [] => rfl
    | [comment, ..rest] => commentLinesWaiting rest

theorem commentsAboveSettled ∀ (comments: List Comment) (scan: Scan)
    (settled: scan.settled = True):
    (commentsAbove comments).scanLines scan
      = Some
        (match comments with
          | [] => scan
          | _ => Clear) :=
  match comments with
    | [] => rfl
    | [comment, ..rest] =>
      rewrite scanConcat [LineStart, ..commentLines [comment, ..rest]] scan in
        rewrite lineStartSettled scan settled in commentLinesClear [comment, ..rest]

theorem keepsCommentsAbove ∀ (comments: List Comment): Keeps (commentsAbove comments) := scan settled =>
  rewrite commentsAboveSettled comments scan settled in
    match comments with
      | [] => Witness scan (Both rfl settled)
      | [comment, ..rest] => Witness Clear (Both rfl rfl)

theorem commentsAboveWaiting ∀ (comments: List Comment): (commentsAbove comments).scanLines Waiting = Some Waiting :=
  match comments with
    | [] => rfl
    | [comment, ..rest] =>
      rewrite scanConcat [LineStart, ..commentLines [comment, ..rest]] Waiting in commentLinesWaiting [comment, ..rest]

theorem keepsToken ∀ (comments: Comments) (text: Text): Keeps (token comments text) :=
  keepsConcat
    [commentsAbove comments.above, Doc.text text, trailingComment comments.after]
    (keepsSeqCons
      (commentsAbove comments.above)
      [Doc.text text, trailingComment comments.after]
      (keepsCommentsAbove comments.above)
      (keepsSeqCons
        (Doc.text text)
        [trailingComment comments.after]
        (keepsText text)
        (keepsSeqCons (trailingComment comments.after) [] (keepsTrailing comments.after) keepsSeqNil)))

theorem trailingStarted ∀ (trailing: Option Comment):
    (trailingComment trailing).scanLines (Started True) = Some (Started True) :=
  match trailing with
    | None => rfl
    | Some comment => rfl

--| A token that may start a line at the statement's column (`else`, `)`,
--| `]`), after a break there: its own-line comments don't count.
theorem tokenOpens ∀ (comments: Comments) (text: Text)
    (opens: opensAtColumn text = True):
    (token comments text).scanLines Waiting = Some (Started True) :=
  rewrite scanConcat [commentsAbove comments.above, Doc.text text, trailingComment comments.after] Waiting in
    rewrite commentsAboveWaiting comments.above in rewrite opens, trailingStarted comments.after in rfl

-- Closing brackets.

--| A closer after a break at the statement's column: its own-line
--| comments move that line to its items' indentation, and the closer goes
--| on the line below, at the column.
theorem closerOpens ∀ (comments: Comments) (text: Text)
    (opens: opensAtColumn text = True):
    (closer comments text).scanLines Waiting = Some (Started True) :=
  match comments with
    | { above = [], after } => tokenOpens { above = [], after } text opens
    | { above = [comment], after } =>
      rewrite opens in
        match after with
          | None => rfl
          | Some trailing => rfl
    | { above = [comment, next, ..rest], after } =>
      rewrite opens in
        match after with
          | None => rfl
          | Some trailing => rfl

theorem keepsCloser ∀ (comments: Comments) (text: Text)
    (opens: opensAtColumn text = True):
    Keeps (closer comments text) :=
  match comments with
    | { above = [], after } => keepsToken { above = [], after } text
    | { above = [comment, ..rest], after } =>
      let lines := [comment, ..rest].map (comment => Doc.text comment.text) |> joined HardLine
      keepsConcat
        [Nest 2 (Doc.concat [LineStartHere, lines]), HardLine, Doc.text text, trailingComment after]
        (keepsSeqCons
          (Nest 2 (Doc.concat [LineStartHere, lines]))
          [HardLine, Doc.text text, trailingComment after]
          (keepsNest 1 (Doc.concat [LineStartHere, lines]))
          (scan settled =>
            rewrite hardLineBreaks scan settled, opens, trailingStarted after in Witness (Started True) (Both rfl rfl)))

--| `closeAfter` with a closer: on the line below when the expression ends
--| in a trailing comment.
theorem keepsCloseAfter ∀ (expr: Expr) (comments: Comments) (text: Text)
    (opens: opensAtColumn text = True):
    Keeps (closeAfter expr (closer comments text)) :=
  match expr.endsWithComment with
    | True => keepsConcat [HardLine, closer comments text] (scan settled =>
      rewrite hardLineBreaks scan settled, closerOpens comments text opens in Witness (Started True) (Both rfl rfl))
    | False => keepsCloser comments text opens

-- The rules.

theorem keepsTwo ∀ (first second: Doc) (one: Keeps first) (two: Keeps second): Keeps (Doc.concat [first, second]) :=
  keepsConcat [first, second] (keepsSeqCons first [second] one (keepsSeqCons second [] two keepsSeqNil))

theorem keepsThree ∀ (first second third: Doc)
    (one: Keeps first)
    (two: Keeps second)
    (three: Keeps third):
    Keeps (Doc.concat [first, second, third]) :=
  keepsConcat
    [first, second, third]
    (keepsSeqCons first [second, third] one (keepsSeqCons second [third] two (keepsSeqCons third [] three keepsSeqNil)))

--| A doc that starts with a closer, after a break at the statement's
--| column, then docs that keep the scan settled.
theorem closerThen ∀ (comments: Comments) (text: Text)
    (opens: opensAtColumn text = True) (docs: List Doc)
    (rest: KeepsSeq docs):
    ∃ (after: Scan) => (Doc.concat [closer comments text, ..docs]).scanLines Waiting = Some after
      ∧ after.settled = True :=
  rewrite scanConcat [closer comments text, ..docs] Waiting, closerOpens comments text opens in rest (Started True) rfl

--| A line break at the doc's indentation, then a doc that from there
--| leaves the scan settled.
theorem keepsSeqBreakThen ∀ (break opener: Doc) (docs: List Doc)
    (breaks: ∀ (scan: Scan) => scan.settled = True → break.scanLines scan = Some Waiting)
    (opens: ∃ (after: Scan) => opener.scanLines Waiting = Some after ∧ after.settled = True)
    (rest: KeepsSeq docs):
    KeepsSeq [break, opener, ..docs] :=
  scan settled =>
    match opens with | Witness next (Both ran nextSettled) => rewrite breaks scan settled, ran in rest next nextSettled

def HeadKeeps: List Doc → Prop
  | [] => False
  | [first, .._] => Keeps first

theorem chainHeadKeeps ∀ (level: Nat) (expr: Expr)
    (whole: Keeps expr.layout) (more: List Doc):
    HeadKeeps (chainParts level expr ++ more) :=
  match expr with
    | Binary operator sign left right =>
      match same: operator.level == level with
        | True =>
          rewrite List.appendAssoc (chainParts level left) [link operator sign right.layout] more in
            chainHeadKeeps level left (exprKeeps left) ([link operator sign right.layout] ++ more)
        | False => whole
    | Var name comments => whole
    | NumberLiteral digits comments => whole
    | StringLiteral written comments => whole
    | Bracketed open inner close => whole
    | ListLiteral open items close => whole
    | Call callee open arguments close => whole
    | Field target dot name nameComments => whole
    | Negate minus operand => whole
    | If ifComments condition thenComments whenTrue elseComments whenFalse => whole

theorem ifKeeps ∀ (ifComments: Comments) (condition: Expr) (thenComments: Comments) (whenTrue: Body)
    (elseComments: Comments) (whenFalse: Body)
    (conditionOk: Keeps condition.layout)
    (trueOk: Keeps (branch whenTrue))
    (falseOk: Keeps (elseBranch elseComments whenFalse)):
    Keeps (ifLayout ifComments condition thenComments whenTrue elseComments whenFalse) :=
  keepsConcat
    [
      token ifComments "if",
      Doc.text " ",
      condition.layout,
      Doc.text " ",
      token thenComments "then",
      branch whenTrue,
      Line,
      token elseComments "else",
      elseBranch elseComments whenFalse
    ]
    (keepsSeqCons _ _
      (keepsToken ifComments "if")
      (keepsSeqCons _ _
        (keepsText " ")
        (keepsSeqCons _ _ conditionOk
          (keepsSeqCons _ _
            (keepsText " ")
            (keepsSeqCons _ _
              (keepsToken thenComments "then")
              (keepsSeqCons _ _ trueOk
                (keepsSeqBreak Line
                  (token elseComments "else")
                  [elseBranch elseComments whenFalse]
                  lineBreaks
                  (tokenOpens elseComments "else" rfl)
                  (keepsSeqCons _ [] falseOk keepsSeqNil))))))))

theorem keepsBelow ∀ (doc: Doc): Keeps (below doc) := keepsNest 1 (Doc.concat [HardLine, doc])

theorem branchBare ∀ (value: Expr)
    (ok: Keeps value.layout):
    Keeps (Choice [Doc.concat [Doc.text " ", Flatten value.layout], below value.layout]) :=
  keepsChoice _
    (keepsChoicesCons _ _
      (keepsTwo _ _ (keepsText " ") (keepsFlatten _ ok))
      (keepsChoicesCons _ _ (keepsBelow value.layout) keepsChoicesNil))

theorem exprKeeps ∀ (expr: Expr): Keeps expr.layout := match expr with
  | Var name comments => keepsToken comments name
  | NumberLiteral digits comments => keepsToken comments digits
  | StringLiteral written comments => keepsToken comments written
  | Bracketed open inner close =>
    keepsThree _ _ _ (keepsToken open "(") (exprKeeps inner) (keepsCloseAfter inner close ")" rfl)
  | ListLiteral open items close => listKeeps open items close
  | Call callee open arguments close => keepsTwo _ _ (exprKeeps callee) (argumentsKeeps open arguments close)
  | Field target dot name nameComments =>
    keepsThree _ _ _ (exprKeeps target) (keepsToken dot ".") (keepsToken nameComments name)
  | Negate minus operand =>
    keepsThree _ _ _
      (keepsToken minus "-")
      (keepsText (if operand.startsWithMinus then " " else ""))
      (exprKeeps operand)
  | Binary operator sign left right =>
    let head := chainHeadKeeps operator.level left (exprKeeps left) [link operator sign right.layout]
    match parts: chainParts operator.level left ++ [link operator sign right.layout] with
      | [first, ..links] => keepsGroup _ (keepsTwo _ _ head (keepsNest 1 (Doc.concat links)))
  | If ifComments condition thenComments whenTrue elseComments whenFalse =>
    ifKeeps ifComments condition thenComments whenTrue elseComments whenFalse
      (exprKeeps condition)
      (branchKeeps whenTrue)
      (elseBranchKeeps elseComments whenFalse)

theorem listKeeps ∀ (open: Comments) (items: List Item) (close: Comments): Keeps (listLayout open items close) :=
  match items.last with
    | None => keepsTwo _ _ (keepsToken open "[") (keepsCloser close "]" rfl)
    | Some last =>
      keepsGroup _
        (keepsThree _ _ _
          (keepsToken open "[")
          (keepsNest 1 (Fill (itemDocs items)))
          (keepsCloseAfter last.value close "]" rfl))

theorem argumentsKeeps ∀ (open: Comments) (arguments: List Item) (close: Comments):
    Keeps (argumentsLayout open arguments close) :=
  match arguments with
    | [] => keepsTwo _ _ (keepsToken open "(") (keepsCloser close ")" rfl)
    | [first, ..rest] =>
      keepsGroup _
        (keepsConcat _
          (keepsSeqCons _ _
            (keepsToken open "(")
            (keepsSeqCons _ _
              (keepsNest 1 (Doc.concat [SoftLine, itemDocs [first, ..rest] |> joined Line]))
              (keepsSeqBreak SoftLine (closer close ")") [] softLineBreaks (closerOpens close ")" rfl) keepsSeqNil))))

theorem branchKeeps ∀ (body: Body): Keeps (branch body) := match body with
  | { statements = [] } => keepsBelow _
  | { statements = [{ blankBefore, line = Bare value }] } => branchBare value (exprKeeps value)
  | { statements = [{ blankBefore, line = Let letComments name nameComments equals inner }] } => keepsBelow _
  | { statements = [{ blankBefore, line = StatementNote comment }] } => keepsBelow _
  | { statements = [first, second, ..rest] } => keepsBelow _

theorem elseBranchKeeps ∀ (elseComments: Comments) (body: Body): Keeps (elseBranch elseComments body) := match body with
  | { statements = [{ blankBefore, line = Bare value }] } =>
    match value with
      | If ifComments condition thenComments whenTrue innerElse whenFalse =>
        match g: elseComments.after.isNone && ifComments.above.isEmpty with
          | True =>
            keepsTwo
              (Doc.text " ")
              (ifLayout ifComments condition thenComments whenTrue innerElse whenFalse)
              (keepsText " ")
              (ifKeeps ifComments condition thenComments whenTrue innerElse whenFalse
                (exprKeeps condition)
                (branchKeeps whenTrue)
                (elseBranchKeeps innerElse whenFalse))
          | False => branchKeeps { statements = [{ blankBefore, line = Bare value }] }
      | _ => branchKeeps { statements = [{ blankBefore, line = Bare value }] }
  | { statements = [] } => branchKeeps { statements = [] }
  | { statements = [{ blankBefore, line = Let letComments name nameComments equals inner }] } =>
    branchKeeps { statements = [{ blankBefore, line = Let letComments name nameComments equals inner }] }
  | { statements = [{ blankBefore, line = StatementNote comment }] } =>
    branchKeeps { statements = [{ blankBefore, line = StatementNote comment }] }
  | { statements = [{ blankBefore, line = Bare value }, second, ..rest] } =>
    match value with
      | If ifComments condition thenComments whenTrue innerElse whenFalse =>
        branchKeeps { statements = [{ blankBefore, line = Bare value }, second, ..rest] }
      | _ => branchKeeps { statements = [{ blankBefore, line = Bare value }, second, ..rest] }
  | { statements = [{ blankBefore, line = Let letComments name nameComments equals inner }, second, ..rest] } =>
    branchKeeps {
      statements = [{ blankBefore, line = Let letComments name nameComments equals inner }, second, ..rest]
    }
  | { statements = [{ blankBefore, line = StatementNote comment }, second, ..rest] } =>
    branchKeeps { statements = [{ blankBefore, line = StatementNote comment }, second, ..rest] }

theorem afterEqualsKeeps ∀ (body: Body) (equals: Comments): Keeps (body.afterEquals equals) := match body with
  | { statements = [{ blankBefore, line = Bare value }] } =>
    match g: equals.after.isNone with
      | True =>
        match value with
          | ListLiteral open items close =>
            keepsChoice _
              (keepsChoicesCons _ _
                (keepsTwo _ _ (keepsText " ") (keepsFlatten _ (exprKeeps value)))
                (keepsChoicesCons _ _ (keepsTwo _ _ (keepsText " ") (exprKeeps value)) keepsChoicesNil))
          | _ =>
            keepsChoice _
              (keepsChoicesCons _ _
                (keepsTwo _ _ (keepsText " ") (keepsFlatten _ (exprKeeps value)))
                (keepsChoicesCons _ _
                  (keepsOneLineBelow value.layout)
                  (keepsChoicesCons _ _ (keepsBelow value.layout) keepsChoicesNil)))
      | False => keepsBelow _
  | _ => keepsBelow _

theorem bindingKeeps ∀ (letComments: Comments) (name: Text) (nameComments equals: Comments) (body: Body):
    Keeps (binding letComments name nameComments equals body) :=
  keepsConcat _
    (keepsSeqCons _ _
      (keepsToken letComments "let")
      (keepsSeqCons _ _
        (keepsText " ")
        (keepsSeqCons _ _
          (keepsToken nameComments name)
          (keepsSeqCons _ _
            (keepsText " ")
            (keepsSeqCons _ _ (keepsToken equals "=") (keepsSeqCons _ _ (afterEqualsKeeps body equals) keepsSeqNil))))))

theorem headerKeeps ∀ (fnComments: Comments) (name: Text) (nameComments open: Comments)
    (parameters: List Parameter) (close equals: Comments):
    Keeps (header fnComments name nameComments open parameters close equals) :=
  let opening: Keeps (Doc.concat [token fnComments "fn", Doc.text " ", token nameComments name, token open "("]) :=
    keepsConcat _
      (keepsSeqCons _ _
        (keepsToken fnComments "fn")
        (keepsSeqCons _ _
          (keepsText " ")
          (keepsSeqCons _ _ (keepsToken nameComments name) (keepsSeqCons _ _ (keepsToken open "(") keepsSeqNil))))
  let rest: KeepsSeq [Doc.text " ", token equals "="] :=
    keepsSeqCons _ _ (keepsText " ") (keepsSeqCons _ _ (keepsToken equals "=") keepsSeqNil)
  match parameters with
    | [] => keepsTwo _ _ opening (keepsConcat _ (keepsSeqCons _ _ (keepsCloser close ")" rfl) rest))
    | [first, ..others] =>
      keepsGroup _
        (keepsConcat _
          (keepsSeqCons _ _ opening
            (keepsSeqCons _ _
              (keepsNest 3 (Doc.concat [SoftLine, parameterDocs [first, ..others] |> joined Line]))
              (keepsSeqBreakThen SoftLine _ [] softLineBreaks (closerThen close ")" rfl _ rest) keepsSeqNil))))

--| A statement printed at column `C`: every line after its first that the
--| engine may start at `C` itself starts with `)`, `]` or `else` or holds
--| an own-line comment, whichever way its groups and choices go, so at
--| every width. Every other line of it is under a `Nest`,
--| `OneLineBelow` or comment break, so deeper than `C`, as the parser's
--| layout rule asks of a statement's continuation lines; the statements of
--| a block inside it start two columns deeper still (`below`).
theorem statementScan ∀ (statement: Statement):
    ∃ (after: Scan) => statement.layout.scanLines Clear = Some after ∧ after.settled = True :=
  match statement with
    | Let letComments name nameComments equals body => bindingKeeps letComments name nameComments equals body Clear rfl
    | Bare value => exprKeeps value Clear rfl
    | StatementNote comment => keepsText comment.text Clear rfl

--| As `statementScan`, for a declaration at column 0.
theorem declarationScan ∀ (declaration: Declaration):
    ∃ (after: Scan) => declaration.layout.scanLines Clear = Some after ∧ after.settled = True :=
  match declaration with
    | Function fnComments name nameComments open parameters close equals body =>
      keepsTwo _ _
        (headerKeeps fnComments name nameComments open parameters close equals)
        (afterEqualsKeeps body equals)
        Clear
        rfl
    | Value letComments name nameComments equals body =>
      bindingKeeps letComments name nameComments equals body Clear rfl
    | DeclarationNote comment => keepsText comment.text Clear rfl
