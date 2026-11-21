--| `calmTop` (`calm`, and the file's first flag cleared) keeps what `calm` keeps: within slice 1, comma-free, one
--| line, the printed text and `meaning`. The flag it clears is the file loop's, which no rule's document reads.

namespace Fmt.CalmTopProofs
import Std (Bool, Doc, Eq, List, Option, Text)
import Syntax (..)
import Fmt (..)
import Fmt.CalmProofs (declDocCalm, plainDef, plainDefIs, printDeclsCalm)
import Fmt.OutputStatements (..)
import Fmt.PassProofs (..)
import Fmt.Driver1 (..)
import Fmt.Walk (..)
import Fmt.BlankProofs (..)
import Fmt.MeaningProofs (..)
import Fmt.MergeProofs (..)

--| `plainDef` reads no blank-line flag of the keyword: the `def` is hoisted, and its own-line comments and blank
--| line are the file loop's.
theorem plainDefTopped ∀ (keyword: Comments) (name: Word) (colon: Comments) (result: Expr)
    (colonEq: Comments) (value: Expr):
    plainDef keyword.topped name colon result colonEq value = plainDef keyword name colon result colonEq value :=
  match keyword with
    | { above, after, blankBefore } =>
      match name with
        | { text, comments } =>
          let closer: Bool := isCloserText text
          match above with
            | [] => cases closer then byComputing
            | [first, ..rest] => cases closer then byComputing

--| A declaration with the first token's blank-line flags cleared, as `calmTop` clears them.
def Decl.topFlag: Decl → Decl
  | Definition attributes header body => Definition attributes { header | keyword = header.keyword.topped } body
  | other => other

--| `calmTop` of a file whose first declaration is a definition: the first declaration calmed and its flags cleared.
theorem calmTopDefinition ∀ (attributes: List Attributes) (header: Header) (body: DefBody)
    (rest: List Decl) (end: Comments):
    SourceFile.calmTop { decls = [Definition attributes header body, ..rest], end }
      = {
        decls = [(Definition attributes header body).calm.topFlag, ..rest.map Decl.calm],
        end = { end | blankBefore = False }
      } :=
  match body with | Assigned _ _ | Primitive | Arms _ => byComputing

theorem headerToppedWithin ∀ (header: Header)
    (within: header.within1 = True):
    ({ header | keyword = header.keyword.topped }: Header).within1 = True :=
  match header with
    | {
        exportKeyword = None,
        opaqueKeyword = None,
        kind = DefPlain,
        keyword = { above = ([] | [_, .._]), after, blankBefore },
        name,
        forallKeyword = None,
        params = [],
        colon,
        result,
        decreasingClause = None,
        unfoldingClause = None
      } => within

theorem topFlagWithin ∀ (decl: Decl) (within: decl.within1 = True): decl.topFlag.within1 = True := match decl with
  | Definition [] header (Assigned colonEq value) =>
    Bool.andIntro (headerToppedWithin header (Bool.andLeft within)) (Bool.andRight within)

theorem topFlagCommaFree ∀ (decl: Decl): decl.topFlag.commaFree = decl.commaFree := match decl with
  | Definition attributes header (Assigned colonEq value) => byComputing
  | _ => cases

--| The flags `calmTop` clears are no rule's: a slice 1 header's document is the same without them.
--|
--| Proof idea: `plainDefIs` on both sides and `plainDefTopped` between.
theorem defDocTopped ∀ (header: Header) (colonEq: Comments) (value: Expr)
    (within: header.within1 = True):
    defDoc { header | keyword = header.keyword.topped } colonEq value = defDoc header colonEq value :=
  match header with
    | {
        exportKeyword = None,
        opaqueKeyword = None,
        kind = DefPlain,
        keyword,
        name,
        forallKeyword = None,
        params = [],
        colon,
        result,
        decreasingClause = None,
        unfoldingClause = None
      } =>
      calc defDoc
        {
          exportKeyword = None,
          opaqueKeyword = None,
          kind = DefPlain,
          keyword = keyword.topped,
          name,
          forallKeyword = None,
          params = [],
          colon,
          result,
          decreasingClause = None,
          unfoldingClause = None
        }
        colonEq
        value
        _ = plainDef keyword.topped name colon result colonEq value :=
          plainDefIs keyword.topped name colon result colonEq value
        _ = plainDef keyword name colon result colonEq value := plainDefTopped keyword name colon result colonEq value
        _ = defDoc
            {
              exportKeyword = None,
              opaqueKeyword = None,
              kind = DefPlain,
              keyword,
              name,
              forallKeyword = None,
              params = [],
              colon,
              result,
              decreasingClause = None,
              unfoldingClause = None
            }
            colonEq
            value := (plainDefIs keyword name colon result colonEq value).flipped

theorem topFlagDoc ∀ (decl: Decl) (within: decl.within1 = True): decl.topFlag.doc1 = decl.doc1 := match decl with
  | Definition [] header (Assigned colonEq value) =>
    Eq.cong (doc => Some doc) (defDocTopped header colonEq value (Bool.andLeft within))

theorem topFlagPrinted ∀ (decl: Decl) (within: decl.within1 = True): decl.topFlag.printed1 = decl.printed1 :=
  rewrite topFlagWithin decl within, within, topFlagDoc decl within

--| The flags `calmTop` clears are blanked by `meaning` anyway.
theorem topFlagWalk ∀ (attributes: List Attributes) (header: Header) (body: DefBody):
    (Definition attributes header body).topFlag.walk meaningPure
      = (Definition attributes header body).walk meaningPure :=
  match header with
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
      } => cases body then byComputing

--| `calmTopWithin`: `calmTop` stays within slice 1.
theorem calmTopWithin ∀ (file: SourceFile) (within: file.within1 = True): file.calmTop.within1 = True := match file with
  | { decls, end } =>
    match decls with
      | [] => byComputing
      | [Definition [] header (Assigned colonEq value), ..rest] =>
        rewrite calmTopDefinition [] header (Assigned colonEq value) rest end then
          Bool.andIntro
            (topFlagWithin
              (Definition [] header (Assigned colonEq value)).calm
              (Eq.trans (declCalmWithinEq (Definition [] header (Assigned colonEq value))) (Bool.andLeft within)))
            (Eq.trans (declsCalmWithin rest) (Bool.andRight within))
      | _ => cases

-- `calm` keeps a tree free of last commas: it clears flags and keeps the commas.

theorem exprCalmCommaFree ∀ (expr: Expr) (item: Bool): (expr.calm item).commaFree = expr.commaFree := match expr with
  | Atom kind word => byComputing
  | Paren open inner close => rewrite exprCalmCommaFree inner False
  | Tuple open items comma close => rewrite calmAllCommaFree items True
  | ListOf open items comma close => rewrite pickCommaFree items (items.all Expr.plainItem)
  | App head arguments => rewrite exprCalmCommaFree head item, calmAllCommaFree arguments False
  | Infix kind left operator right => rewrite exprCalmCommaFree left item, exprCalmCommaFree right False
  | Prefix operator operand => rewrite exprCalmCommaFree operand False
  | _ => cases

theorem calmAllCommaFree ∀ (items: List Expr) (item: Bool): allCommaFree (calmAll item items) = allCommaFree items :=
  match items with
    | [] => byComputing
    | [first, ..rest] => rewrite exprCalmCommaFree first item, calmAllCommaFree rest item

theorem calmLeadCommaFree ∀ (items: List Expr): allCommaFree (calmLead items) = allCommaFree items := match items with
  | [] => byComputing
  | [first, ..rest] => rewrite exprCalmCommaFree first False, calmAllCommaFree rest True

theorem pickCommaFree ∀ (items: List Expr) (plain: Bool): allCommaFree (pickItems plain items) = allCommaFree items :=
  match plain with
    | True => calmLeadCommaFree items
    | False => calmAllCommaFree items True

theorem declCalmCommaFree ∀ (decl: Decl): decl.calm.commaFree = decl.commaFree := match decl with
  | Definition attributes header (Assigned colonEq value) =>
    rewrite exprCalmCommaFree header.result False, exprCalmCommaFree value False
  | _ => cases

theorem declsCalmCommaFree ∀ (decls: List Decl): (decls.map Decl.calm).all Decl.commaFree = decls.all Decl.commaFree :=
  match decls with
    | [] => byComputing
    | [first, ..rest] => rewrite declCalmCommaFree first, declsCalmCommaFree rest

--| `calmTopCommaFree`: `calmTop` keeps a tree free of last commas.
--|
--| Proof idea: `calm` keeps every comma (`declsCalmCommaFree`), and `topFlag` touches only the first keyword's flags.
theorem calmTopCommaFree ∀ (file: SourceFile)
    (within: file.within1 = True)
    (commaFree: file.commaFree = True):
    file.calmTop.commaFree = True :=
  match file with
    | { decls, end } =>
      match decls with
        | [] => byComputing
        | [Definition [] header (Assigned colonEq value), ..rest] =>
          let declaration: Decl := Definition [] header (Assigned colonEq value)
          let firstFree: declaration.calm.topFlag.commaFree = True := calc declaration.calm.topFlag.commaFree
            _ = declaration.calm.commaFree := topFlagCommaFree declaration.calm
            _ = declaration.commaFree := declCalmCommaFree declaration
            _ = True := Bool.andLeft commaFree
          rewrite calmTopDefinition [] header (Assigned colonEq value) rest end then
            Bool.andIntro firstFree (Eq.trans (declsCalmCommaFree rest) (Bool.andRight commaFree))
        | _ => cases

--| `calmTopWalk`: `calmTop` walks to what `calm` walks to: `meaning`'s walk blanks the keyword's comments first.
theorem calmTopWalk ∀ (file: SourceFile):
    walkDecls meaningPure file.calmTop.decls = walkDecls meaningPure file.calm.decls :=
  match file with
    | { decls, end } =>
      match decls with
        | [] => byComputing
        | [Definition attributes header body, ..rest] =>
          rewrite calmTopDefinition attributes header body rest end then
            match body with
              | Assigned colonEq value =>
                rewrite topFlagWalk attributes header.calm (Assigned (colonEq.kept False False) (value.calm False))
              | Primitive => rewrite topFlagWalk attributes header Primitive
              | Arms arms => rewrite topFlagWalk attributes header (Arms arms)
        | _ => cases decls then byComputing

--| `calmTopMeans`: `calmTop` keeps `meaning` (`calmMeans`; `meaning` reads no comment).
theorem calmTopMeans ∀ (file: SourceFile): file.calmTop.meaning = file.meaning :=
  rewrite applyWalk file.calmTop.withoutEnd meaningSteps meaningPure meaningAgrees,
      applyWalk file.withoutEnd meaningSteps meaningPure meaningAgrees,
      calmTopWalk file,
      declsCalmWalk file.decls

--| The file loop reads the first declaration's flags only after something is written above it, so with nothing
--| written, `topFlag` changes no output.
theorem printDeclsTopFlag ∀ (printed: Decl → Option Text) (attributes: List Attributes) (header: Header)
    (body: DefBody) (rest: List Decl)
    (same: printed (Definition attributes header body).topFlag = printed (Definition attributes header body)):
    printDecls printed { pieces = [], empty = True } [(Definition attributes header body).topFlag, ..rest]
      = printDecls printed { pieces = [], empty = True } [Definition attributes header body, ..rest] :=
  match header with
    | {
        exportKeyword,
        opaqueKeyword,
        kind,
        keyword = { above = ([] | [_, .._]), after, blankBefore },
        name,
        forallKeyword,
        params,
        colon,
        result,
        decreasingClause,
        unfoldingClause
      } => rewrite same

--| What the file loop writes after the declarations: the file's end comments, if anything was written at all.
def finishFile (body: Output) (above: List Note): Text :=
  let done := body.notes above
  if done.empty then "" else Text.concat ["\n", ..done.pieces].reverse

theorem printedFinish ∀ (file: SourceFile):
    file.printed1 = finishFile (printDecls Decl.printed1 { pieces = [], empty = True } file.decls) file.end.above :=
  byComputing

theorem finishCong ∀ (body body': Output) (above above': List Note)
    (sameBody: body = body')
    (sameAbove: above = above'):
    finishFile body above = finishFile body' above' :=
  rewrite sameBody, sameAbove

--| `calmTopPrints`: `calmTop` prints the same file (`calmPrints`, and the file loop prints no blank line above the
--| first thing in the file).
--|
--| Proof idea: the file loop's text is `finishFile` of the declarations' output; `calmTop`'s declarations print as
--| `calm`'s (`topFlag` changes no printed text, and the file loop reads its flags only after something is written:
--| `printDeclsTopFlag`), which print as the file's (`printDeclsCalm`). An empty file's end comments are written to
--| an empty output, which ignores their first flag.
theorem calmTopPrints ∀ (file: SourceFile)
    (within: file.within1 = True)
    (lexical: file.lexical = True):
    file.calmTop.printed1 = file.printed1 :=
  match file with
    | { decls, end } =>
      match decls with
        | [] =>
          match end with
            | { above = [], after, blankBefore } => byComputing
            | { above = [first, ..more], after, blankBefore } => byComputing
        | [Definition [] header (Assigned colonEq value), ..rest] =>
          let declaration: Decl := Definition [] header (Assigned colonEq value)
          let calmed: Decl := Definition [] header.calm (Assigned (colonEq.kept False False) (value.calm False))
          let output: Output := { pieces = [], empty = True }
          let withinCalmed: calmed.within1 = True := Eq.trans (declCalmWithinEq declaration) (Bool.andLeft within)
          calc ({ decls = [declaration, ..rest], end }: SourceFile).calmTop.printed1
            _ = finishFile
                (printDecls Decl.printed1 output [calmed.topFlag, ..rest.map Decl.calm])
                ({ end | blankBefore = False }).above :=
              Eq.trans
                (Eq.cong (file => file.printed1) (calmTopDefinition [] header (Assigned colonEq value) rest end))
                (printedFinish _)
            _ = finishFile (printDecls Decl.printed1 output [calmed, ..rest.map Decl.calm]) end.above :=
              finishCong _ _ _ _
                (printDeclsTopFlag Decl.printed1 [] header.calm
                  (Assigned (colonEq.kept False False) (value.calm False))
                  (rest.map Decl.calm)
                  (topFlagPrinted calmed withinCalmed))
                byComputing
            _ = finishFile (printDecls Decl.printed1 output [declaration, ..rest]) end.above :=
              finishCong _ _ _ _ (printDeclsCalm output [declaration, ..rest] within lexical) byComputing
            _ = ({ decls = [declaration, ..rest], end }: SourceFile).printed1 := (printedFinish _).flipped
        | _ => cases
