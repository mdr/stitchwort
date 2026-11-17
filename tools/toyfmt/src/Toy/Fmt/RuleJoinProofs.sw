--| Every rule joins. For a tree whose texts are the lexer's
--| (`LexicalFile`: each name a word, each number digits, each string
--| closed, each comment a comment, and each body ending in a statement,
--| not a comment line), the document the rules build puts next to each
--| token only what the token is still read whole before, through every
--| layout (`fileJoins`). With the engine's half, a file printed at any
--| width lexes to its pieces (`printedTokens`).

namespace Toy.Fmt.Proofs
import Toy.Doc (..)
import Toy.Doc.Proofs (..)
import Toy.Syntax (..)
import Toy.Syntax.Proofs (..)
import Toy.Fmt (..)
import Std (Bool, DecEq, Eq, List, Nat, Option, Parse, Text, Void)

-- What the parser guarantees about a tree's texts.

--| Every text in the expression is the lexer's, and every body in it
--| ends in a statement.
def Lexical: Expr → Prop
  | Var name comments => IsName name ∧ Fine comments
  | NumberLiteral digits comments => IsDigits digits ∧ Fine comments
  | StringLiteral written comments => IsString written ∧ Fine comments
  | Bracketed open inner close => Fine open ∧ Lexical inner ∧ Fine close
  | ListLiteral open items trailingComma close => Fine open ∧ LexicalItems items ∧ Fine close
  | Call callee open arguments trailingComma close => Lexical callee ∧ Fine open ∧ LexicalItems arguments ∧ Fine close
  | Field target dot name nameComments => Lexical target ∧ Fine dot ∧ IsName name ∧ Fine nameComments
  | Negate minus operand => Fine minus ∧ Lexical operand
  | Binary operator sign left right => Fine sign ∧ Lexical left ∧ Lexical right
  | If ifComments condition thenComments whenTrue elseComments whenFalse =>
    Fine ifComments
      ∧ Lexical condition
      ∧ Fine thenComments
      ∧ LexicalBody whenTrue
      ∧ Fine elseComments
      ∧ LexicalBody whenFalse

def LexicalItems: List Expr → Prop
  | [] => True
  | [value, ..rest] => Lexical value ∧ LexicalItems rest

def LexicalBody: Body → Prop
  | { statements } => LexicalLines statements ∧ ClosedLines statements

def LexicalLines: List (Spaced Statement) → Prop
  | [] => True
  | [{ line, .. }, ..rest] => LexicalStatement line ∧ LexicalLines rest

def LexicalStatement: Statement → Prop
  | Let letComments name nameComments equals body =>
    Fine letComments ∧ IsName name ∧ Fine nameComments ∧ Fine equals ∧ LexicalBody body
  | Bare value => Lexical value
  | StatementNote comment => IsComment comment.text

def LexicalNamed (named: Named): Prop := IsName named.name ∧ Fine named.comments

def LexicalNames: List Named → Prop
  | [] => True
  | [named, ..rest] => LexicalNamed named ∧ LexicalNames rest

def LexicalType: TypeExpr → Prop
  | TypeName name comments => IsName name ∧ Fine comments
  | TypeBracketed open inner close => Fine open ∧ LexicalType inner ∧ Fine close

def LexicalGroup: ParameterGroup → Prop
  | Untyped parameter => LexicalNamed parameter
  | Typed names colon annotation =>
    LexicalNamed names.head ∧ LexicalNames names.tail ∧ Fine colon ∧ LexicalType annotation

def LexicalParameters: List ParameterGroup → Prop
  | [] => True
  | [group, ..rest] => LexicalGroup group ∧ LexicalParameters rest

--| `takes`, if it was written, holds the lexer's comments.
def FineTakes (takes: Option Comments): Prop := Parse.Perhaps Fine takes

def LexicalDeclaration: Declaration → Prop
  | Function fnComments name nameComments takes open parameters trailingComma close equals body =>
    Fine fnComments
      ∧ IsName name
      ∧ Fine nameComments
      ∧ FineTakes takes
      ∧ Fine open
      ∧ LexicalParameters parameters
      ∧ Fine close
      ∧ Fine equals
      ∧ LexicalBody body
  | Value letComments name nameComments equals body =>
    Fine letComments ∧ IsName name ∧ Fine nameComments ∧ Fine equals ∧ LexicalBody body
  | DeclarationNote comment => IsComment comment.text

def LexicalDeclarations: List (Spaced Declaration) → Prop
  | [] => True
  | [{ line, .. }, ..rest] => LexicalDeclaration line ∧ LexicalDeclarations rest

--| Every text in the file is the lexer's, and every body ends in a
--| statement: what the parser guarantees of its trees, as far as the
--| printed text's lexing needs it.
def LexicalFile: SourceFile → Prop
  | { declarations } => LexicalDeclarations declarations

-- More triples.

theorem passesGroup ∀ (inner: Doc) (pre post: Edge → Prop)
    (passes: Passes inner pre post):
    Passes (Doc.group inner) pre post :=
  passes

theorem passesFlatten ∀ (inner: Doc) (pre post: Edge → Prop)
    (passes: Passes inner pre post):
    Passes (Flatten inner) pre post :=
  passes

theorem passesEmpty ∀ (pre: Edge → Prop): Passes Empty pre pre :=
  (byComputing, (edge next holds after => after edge holds))

theorem passesBlank ∀ (pre: Edge → Prop): Passes Blank pre pre :=
  (byComputing, (edge next holds after => after edge holds))

theorem tokenMeets ∀ (comments: Comments) (text: Text)
    (fine: Fine comments)
    (spelled: TokenText text):
    Passes (token comments text) (Admits text) Meets :=
  match spelled with
    | (solid, ends) => passesTo _ _ _ Meets (tokenPasses comments text fine ((solid, ends))) (leftMeets text ends)

--| A token after a bracket or a dot.
theorem freeToken ∀ (comments: Comments) (text: Text)
    (fine: Fine comments)
    (spelled: TokenText text):
    Passes (token comments text) Free Meets :=
  passesFrom _ _ Free _ (tokenMeets comments text fine spelled) (freeAdmits text)

--| Each document from where anything may come next, to where a space or
--| a closing sign may.
def EachPasses: List Doc → Prop
  | [] => True
  | [doc, ..rest] => Passes doc Free Meets ∧ EachPasses rest

theorem eachProper ∀ (docs: List Doc) (each: EachPasses docs): AllProper (wordsAll docs) := match docs, each with
  | [], _ => byComputing
  | [doc, ..rest], Both (Both proper _) others => properAppend doc.words (wordsAll rest) proper (eachProper rest others)

theorem sepsPass ∀ (docs: List Doc) (edge: Edge) (next: Edge → Prop)
    (each: EachPasses docs)
    (meets: Meets edge) (after: ∀ (left: Edge) => Meets left → next left):
    SepsJoin standsBefore docs edge next :=
  match docs, each with
    | [], _ => after edge meets
    | [item, ..more], Both (Both _ joins) others =>
      let onward: Joins standsBefore item (Plain None) (reached => SepsJoin standsBefore more reached next) :=
        joins (Plain None) (reached => SepsJoin standsBefore more reached next) byComputing (reached met =>
          sepsPass more reached next others met after)
      match edge, meets with
        | Plain None, _ => (byComputing, onward)
        | Plain (Some word), any => ((any " " shutsSpace), onward)
        | Edge.Waiting _, _ => onward

--| A fill: its items with a space or a line break between each two.
theorem fillPasses ∀ (docs: List Doc) (each: EachPasses docs): Passes (Fill docs) Free Meets := match docs, each with
  | [], _ => (byComputing, (edge next free after => after edge (freeMeets edge free)))
  | [first, ..others], Both (Both proper joins) rest => (
    (properAppend first.words (wordsAll others) proper (eachProper others rest)),
    (edge next free after =>
      joins edge (reached => SepsJoin standsBefore others reached next) free (reached met =>
        sepsPass others reached next rest met after))
  )

theorem joinedLines ∀ (docs: List Doc) (each: EachPasses docs): PassesAll (Doc.joinedWith Line docs) Free Meets :=
  match docs, each with
    | [], _ => passesNil Free Meets freeMeets
    | [only], Both passes _ => passesLast only Free Meets passes
    | [doc, second, ..rest], Both passes others =>
      passesCons doc _ Free Meets Meets passes
        (passesCons Line _ Meets Gapped Meets passesLineGap
          (allFrom _ Free Gapped Meets (joinedLines [second, ..rest] others) gappedFree))

--| Items with a `Line` between each two.
theorem joinedPasses ∀ (docs: List Doc) (each: EachPasses docs): Passes (joined docs Line) Free Meets :=
  passesConcat _ Free Meets (joinedLines docs each)

theorem openSign ∀ (same: OpenParen = Defines): Void := cases

theorem closeSign ∀ (same: CloseParen = Defines): Void := cases

theorem squareSign ∀ (same: OpenSquare = Defines): Void := cases

theorem closeSquareSign ∀ (same: CloseSquare = Defines): Void := cases

theorem commaSign ∀ (same: Comma = Defines): Void := cases

theorem dotSign ∀ (same: Dot = Defines): Void := cases

theorem minusEnds: Ends "-" := match operatorToken Minus with | (_, ends) => ends

-- Expressions.

--| A name, number or string: one token.
theorem leafPasses ∀ (expr: Expr) (comments: Comments) (text: Text)
    (fine: Fine comments)
    (spelled: TokenText text)
    (opens: Opens text):
    Passes (token comments text) (Enters expr) Meets :=
  passesFrom _ _ (Enters expr) _ (tokenMeets comments text fine spelled) (entersAdmits expr text opens)

theorem negateAdmits ∀ (minus: Comments) (operand: Expr) (edge: Edge)
    (enters: Enters (Negate minus operand) edge):
    Admits "-" edge :=
  match edge, enters with
    | Plain (Some word), Both _ startsMinus => startsMinus byComputing
    | _, _ => cases

--| After a `-`: a space before an operand that starts with `-`, else
--| the operand at once.
theorem operandPasses ∀ (operand: Expr)
    (passes: Passes operand.layout (Enters operand) Meets):
    PassesAll [Doc.text (if operand.startsWithMinus then " " else ""), operand.layout] (Left "-") Meets :=
  match found: operand.startsWithMinus with
    | True =>
      passesCons
        (Doc.text " ")
        [operand.layout]
        (Left "-")
        Loose
        Meets
        (passesFrom _ Meets (Left "-") Loose passesSpace (leftMeets "-" minusEnds))
        (passesLast _ Loose Meets (passesFrom _ _ Loose _ passes (looseEnters operand)))
    | False =>
      passesCons
        (Doc.text "")
        [operand.layout]
        (Left "-")
        (Left "-")
        Meets
        (passesNothing (Left "-"))
        (passesLast _
          (Left "-")
          Meets
          (passesFrom _ _ (Left "-") _ passes (edge left => minusEnters operand edge found left)))

--| A chain's head and its links, grouped.
theorem chainGroup ∀ (first: Doc) (links: List Doc) (pre post: Edge → Prop)
    (parts: PassesAll [first, ..links] pre post):
    Passes (Doc.group (Doc.concat [first, Nest 2 (Doc.concat links)])) pre post :=
  match parts with
    | (proper, joins) =>
      let words: AllProper (wordsAll [first, Nest 2 (Doc.concat links)]) :=
        rewrite List.appendNil (Doc.concat links).words, concatWords links then proper
      (
        (rewrite concatWords [first, Nest 2 (Doc.concat links)] then words),
        (edge next holds after =>
          concatJoins
            [first, Nest 2 (Doc.concat links)]
            edge
            next
            (joinsWeaker standsBefore first edge
              (between => JoinsAll standsBefore links between next)
              (between => JoinsAll standsBefore [Nest 2 (Doc.concat links)] between next)
              (between reached =>
                concatJoins links between
                  (final => JoinsAll standsBefore [] final next)
                  (allWeaker standsBefore links between next
                    (final => JoinsAll standsBefore [] final next)
                    (final done => done)
                    reached))
              (joins edge next holds after)))
      )

--| An operator and its right side, after a space or a line break.
theorem linkPasses ∀ (operator: Operator) (sign: Comments) (operand: Doc)
    (fine: Fine sign)
    (passes: Passes operand Loose Meets):
    Passes (link operator sign operand) Meets Meets :=
  passesConcat
    [Line, token sign operator.spelling, Doc.text " ", operand]
    Meets
    Meets
    (passesCons Line _ Meets Loose Meets passesLine
      (passesCons
        (token sign operator.spelling) _
        Loose
        Meets
        Meets
        (passesFrom _ _ Loose _
          (tokenMeets sign operator.spelling fine (operatorToken operator))
          (looseAdmits operator.spelling))
        (passesCons (Doc.text " ") _ Meets Loose Meets passesSpace (passesLast operand Loose Meets passes))))

theorem looseKeyword ∀ (comments: Comments) (keyword: Keyword)
    (fine: Fine comments):
    Passes (token comments keyword.spelling) Loose Meets :=
  passesFrom _ _ Loose _
    (tokenMeets comments keyword.spelling fine (keywordToken keyword))
    (looseAdmits keyword.spelling)

theorem ifPasses ∀ (ifComments: Comments) (condition: Expr) (thenComments: Comments) (whenTrue: Body)
    (elseComments: Comments) (whenFalse: Body)
    (fineIf: Fine ifComments)
    (fineThen: Fine thenComments)
    (fineElse: Fine elseComments)
    (conditionPasses: Passes condition.layout (Enters condition) Meets)
    (truePasses: Passes (branch thenComments whenTrue) Meets Meets)
    (falsePasses: Passes (elseBranch elseComments whenFalse) Meets Meets):
    Passes (ifLayout ifComments condition thenComments whenTrue elseComments whenFalse) (Admits "if") Meets :=
  passesGroup _
    (Admits "if")
    Meets
    (passesConcat _
      (Admits "if")
      Meets
      (passesCons
        (token ifComments "if") _
        (Admits "if")
        Meets
        Meets
        (tokenMeets ifComments "if" fineIf (keywordToken IfKeyword))
        (passesCons
          (Doc.text " ") _
          Meets
          Loose
          Meets
          passesSpace
          (passesCons condition.layout _ Loose Meets Meets
            (passesFrom _ _ Loose _ conditionPasses (looseEnters condition))
            (passesCons
              (Doc.text " ") _
              Meets
              Loose
              Meets
              passesSpace
              (passesCons
                (token thenComments "then") _
                Loose
                Meets
                Meets
                (looseKeyword thenComments ThenKeyword fineThen)
                (passesCons
                  (branch thenComments whenTrue) _
                  Meets
                  Meets
                  Meets
                  truePasses
                  (passesCons Line _ Meets Loose Meets passesLine
                    (passesCons
                      (token elseComments "else") _
                      Loose
                      Meets
                      Meets
                      (looseKeyword elseComments ElseKeyword fineElse)
                      (passesLast _ Meets Meets falsePasses))))))))))

theorem succNotZero ∀ (index: Nat) (zero: (index + 1 == 0) = True): Void := cases

--| What starts a line of a vertical list: nothing for the first line,
--| which must start fresh already; a line break for the others.
theorem lineStartPasses ∀ (index: Nat) (blankBefore: Bool)
    (pre: Edge → Prop) (first: (index == 0) = True → ∀ (edge: Edge) => pre edge → Loose edge):
    Passes (lineStart index blankBefore) pre Loose :=
  match zero: index == 0 with
    | True => (byComputing, (edge next holds after => after edge (first zero edge holds)))
    | False =>
      match blankBefore with
        | True => passesTwo HardLine Blank pre Loose Loose (passesHard pre) (passesBlank Loose)
        | False =>
          passesConcat
            [HardLine, Empty]
            pre
            Loose
            (passesCons HardLine
              [Empty]
              pre
              Loose
              Loose
              (passesHard pre)
              (passesLast Empty Loose Loose (passesEmpty Loose)))

--| What a statement leaves: a comment line, only itself; a statement, a
--| token a space or closing sign may follow.
def Leaves (statement: Statement) (edge: Edge): Prop := match statement with
  | StatementNote _ => True
  | _ => Meets edge

theorem codedMeets ∀ (statement: Statement)
    (coded: Coded statement) (edge: Edge)
    (leaves: Leaves statement edge):
    Meets edge :=
  match statement, coded, leaves with
    | Let _ _ _ _ _, _, meets => meets
    | Bare _, _, meets => meets
    | StatementNote _, never, _ =>
      match never with
        | ()

theorem bareBranchPasses ∀ (value: Expr)
    (whole: Passes value.layout Loose Meets):
    Passes (Choice [Doc.concat [Doc.text " ", Flatten value.layout], below value.layout]) Meets Meets :=
  passesChoiceTwo _ _ Meets Meets
    (passesTwo (Doc.text " ") (Flatten value.layout) Meets Loose Meets passesSpace whole)
    (passesBelow _ Meets Meets whole)

theorem chainPasses ∀ (level: Nat) (expr: Expr)
    (lexical: Lexical expr)
    (whole: Passes expr.layout (Enters expr) Meets)
    (more: List Doc) (post: Edge → Prop)
    (rest: PassesAll more Meets post):
    PassesAll (chainParts level expr ++ more) (Enters expr) post :=
  match expr, lexical with
    | Binary operator sign left right, Both fineSign (Both lexLeft lexRight) =>
      match same: operator.level == level with
        | True =>
          rewrite List.appendAssoc (chainParts level left) [link operator sign right.layout] more then
            chainPasses level left lexLeft
              (exprPasses left lexLeft)
              ([link operator sign right.layout] ++ more)
              post
              (passesCons _ more Meets Meets post
                (linkPasses operator sign right.layout fineSign
                  (passesFrom _ _ Loose _ (exprPasses right lexRight) (looseEnters right)))
                rest)
        | False => passesCons _ _ _ Meets post whole rest
    | Var name comments, _ => passesCons _ _ _ Meets post whole rest
    | NumberLiteral digits comments, _ => passesCons _ _ _ Meets post whole rest
    | StringLiteral written comments, _ => passesCons _ _ _ Meets post whole rest
    | Bracketed open inner close, _ => passesCons _ _ _ Meets post whole rest
    | ListLiteral open items trailingComma close, _ => passesCons _ _ _ Meets post whole rest
    | Call callee open arguments trailingComma close, _ => passesCons _ _ _ Meets post whole rest
    | Field target dot name nameComments, _ => passesCons _ _ _ Meets post whole rest
    | Negate minus operand, _ => passesCons _ _ _ Meets post whole rest
    | If ifComments condition thenComments whenTrue elseComments whenFalse, _ => passesCons _ _ _ Meets post whole rest

--| An expression's document joins from any edge its first token may
--| follow, and leaves one a space or a closing sign may follow.
theorem exprPasses ∀ (expr: Expr) (lexical: Lexical expr): Passes expr.layout (Enters expr) Meets :=
  match expr, lexical with
    | Var name comments, Both (Both word _) fine =>
      leafPasses (Var name comments) comments name fine (wordToken name word) (wordOpens name word)
    | NumberLiteral digits comments, Both number fine =>
      leafPasses
        (NumberLiteral digits comments)
        comments
        digits
        fine
        (digitsToken digits number)
        (digitsOpen digits number)
    | StringLiteral written comments, Both string fine =>
      leafPasses
        (StringLiteral written comments)
        comments
        written
        fine
        (stringToken written string)
        (stringOpens written string)
    | Bracketed open inner close, Both fineOpen (Both lexInner fineClose) =>
      passesConcat
        [token open "(", inner.layout, closeAfter inner close ")"]
        (Enters (Bracketed open inner close))
        Meets
        (passesCons _ _
          (Enters (Bracketed open inner close))
          Free
          Meets
          (openingToken open OpenParen
            (Enters (Bracketed open inner close))
            fineOpen
            openSign
            (entersAdmits (Bracketed open inner close) "(" (later => byComputing)))
          (passesCons _ _ Free Meets Meets
            (passesFrom _ _ Free _ (exprPasses inner lexInner) (freeEnters inner))
            (passesLast _ Meets Meets
              (closeAfterPasses inner close ")" fineClose (signToken CloseParen closeSign) shutsClose))))
    | ListLiteral open items trailingComma close, Both fineOpen (Both lexItems fineClose) =>
      listPasses open items close
        (Enters (ListLiteral open items trailingComma close))
        fineOpen
        fineClose
        (itemDocsPass items lexItems)
        (entersAdmits (ListLiteral open items trailingComma close) "[" (later => byComputing))
    | Call callee open arguments trailingComma close, Both lexCallee (Both fineOpen (Both lexArguments fineClose)) =>
      passesTwo callee.layout
        (argumentsLayout open arguments close)
        (Enters (Call callee open arguments trailingComma close))
        Meets
        Meets
        (passesFrom _
          (Enters callee)
          (Enters (Call callee open arguments trailingComma close))
          Meets
          (exprPasses callee lexCallee)
          (edge enters => enters))
        (argumentsPass open arguments close fineOpen fineClose (itemDocsPass arguments lexArguments))
    | Field target dot name nameComments, Both lexTarget (Both fineDot (Both (Both word _) fineName)) =>
      passesConcat
        [target.layout, token dot ".", token nameComments name]
        (Enters (Field target dot name nameComments))
        Meets
        (passesCons _ _
          (Enters (Field target dot name nameComments))
          Meets
          Meets
          (passesFrom _
            (Enters target)
            (Enters (Field target dot name nameComments))
            Meets
            (exprPasses target lexTarget)
            (edge enters => enters))
          (passesCons _ _ Meets Free Meets
            (openingToken dot Dot Meets fineDot dotSign (meetsAdmits "." shutsDot))
            (passesLast _ Free Meets (freeToken nameComments name fineName (wordToken name word)))))
    | Negate minus operand, Both fineMinus lexOperand =>
      passesConcat
        [token minus "-", Doc.text (if operand.startsWithMinus then " " else ""), operand.layout]
        (Enters (Negate minus operand))
        Meets
        (passesCons _ _
          (Enters (Negate minus operand))
          (Left "-")
          Meets
          (passesFrom _
            (Admits "-")
            (Enters (Negate minus operand))
            (Left "-")
            (tokenPasses minus "-" fineMinus (operatorToken Minus))
            (negateAdmits minus operand))
          (operandPasses operand (exprPasses operand lexOperand)))
    | Binary operator sign left right, Both fineSign (Both lexLeft lexRight) =>
      let parts :=
        chainPasses operator.level left lexLeft
          (exprPasses left lexLeft)
          [link operator sign right.layout]
          Meets
          (passesLast _ Meets Meets
            (linkPasses operator sign right.layout fineSign
              (passesFrom _ _ Loose _ (exprPasses right lexRight) (looseEnters right))))
      match found: chainParts operator.level left ++ [link operator sign right.layout] with
        | [first, ..links] => chainGroup first links (Enters left) Meets parts
        | [] => parts
    | If ifComments condition thenComments whenTrue elseComments whenFalse, Both fineIf
        (Both lexCondition (Both fineThen (Both lexTrue (Both fineElse lexFalse)))) =>
      passesFrom _
        (Admits "if")
        (Enters (If ifComments condition thenComments whenTrue elseComments whenFalse))
        Meets
        (ifPasses ifComments condition thenComments whenTrue elseComments whenFalse fineIf fineThen fineElse
          (exprPasses condition lexCondition)
          (branchPasses thenComments whenTrue lexTrue)
          (elseBranchPasses elseComments whenFalse lexFalse))
        (entersAdmits (If ifComments condition thenComments whenTrue elseComments whenFalse) "if" (later =>
          byComputing))

--| A comma holds no comments.
theorem fineNone: Fine Comments.none := (byComputing, byComputing)

theorem itemDocsPass ∀ (items: List Expr) (lexical: LexicalItems items): EachPasses (itemDocs items) :=
  match items, lexical with
    | [], _ => byComputing
    | [value], Both lexValue _ => ((passesFrom _ _ Free _ (exprPasses value lexValue) (freeEnters value)), byComputing)
    | [value, next, ..rest], Both lexValue others => (
      (passesTwo value.layout
        (Closing ",")
        Free
        Meets
        Meets
        (passesFrom _ _ Free _ (exprPasses value lexValue) (freeEnters value))
        (closingPasses "," (signToken Comma commaSign) shutsComma)),
      (itemDocsPass [next, ..rest] others)
    )

theorem listPasses ∀ (open: Comments) (items: List Expr) (close: Comments) (pre: Edge → Prop)
    (fineOpen: Fine open)
    (fineClose: Fine close)
    (each: EachPasses (itemDocs items)) (admitted: ∀ (edge: Edge) => pre edge → Admits "[" edge):
    Passes (listLayout open items close) pre Meets :=
  match items with
    | [] =>
      passesTwo
        (token open "[")
        (closer close "]")
        pre
        Free
        Meets
        (openingToken open OpenSquare pre fineOpen squareSign admitted)
        (passesFrom _ Meets Free Meets
          (meetingCloser close "]" fineClose (signToken CloseSquare closeSquareSign) shutsSquare)
          freeMeets)
    | [first, ..rest] =>
      match lastOfCons first rest with
        | (last, found) =>
          rewrite found then
            passesGroup _ pre Meets
              (passesConcat _ pre Meets
                (passesCons
                  (token open "[") _
                  pre
                  Free
                  Meets
                  (openingToken open OpenSquare pre fineOpen squareSign admitted)
                  (passesCons
                    (Nest 2 (Fill (itemDocs [first, ..rest]))) _
                    Free
                    Meets
                    Meets
                    (fillPasses (itemDocs [first, ..rest]) each)
                    (passesLast _ Meets Meets
                      (closeAfterPasses last close "]" fineClose
                        (signToken CloseSquare closeSquareSign)
                        shutsSquare)))))

theorem argumentsPass ∀ (open: Comments) (arguments: List Expr) (close: Comments)
    (fineOpen: Fine open)
    (fineClose: Fine close)
    (each: EachPasses (itemDocs arguments)):
    Passes (argumentsLayout open arguments close) Meets Meets :=
  match arguments with
    | [] =>
      passesTwo
        (token open "(")
        (closer close ")")
        Meets
        Free
        Meets
        (openingToken open OpenParen Meets fineOpen openSign (meetsAdmits "(" shutsOpen))
        (passesFrom _ Meets Free Meets
          (meetingCloser close ")" fineClose (signToken CloseParen closeSign) shutsClose)
          freeMeets)
    | [first, ..rest] =>
      passesChoiceTwo _ _ Meets Meets
        (passesFlatten _ Meets Meets
          (passesConcat _ Meets Meets
            (passesCons
              (token open "(") _
              Meets
              Free
              Meets
              (openingToken open OpenParen Meets fineOpen openSign (meetsAdmits "(" shutsOpen))
              (passesCons
                (itemDocs [first, ..rest] |> joined Line) _
                Free
                Meets
                Meets
                (joinedPasses (itemDocs [first, ..rest]) each)
                (passesLast _ Meets Meets
                  (meetingCloser close ")" fineClose (signToken CloseParen closeSign) shutsClose))))))
        (passesGroup _ Meets Meets
          (passesConcat _ Meets Meets
            (passesCons
              (token open "(") _
              Meets
              Free
              Meets
              (openingToken open OpenParen Meets fineOpen openSign (meetsAdmits "(" shutsOpen))
              (passesCons
                (Nest 2 (Doc.concat [SoftLine, itemDocs [first, ..rest] |> joined Line])) _
                Free
                Meets
                Meets
                (passesTwo SoftLine
                  (itemDocs [first, ..rest] |> joined Line)
                  Free
                  Free
                  Meets
                  (passesSoft Free Free (edge holds => holds) byComputing)
                  (joinedPasses (itemDocs [first, ..rest]) each))
                (passesCons SoftLine _ Meets Meets Meets
                  (passesSoft Meets Meets (edge holds => holds) byComputing)
                  (passesLast _ Meets Meets
                    (meetingCloser close ")" fineClose (signToken CloseParen closeSign) shutsClose)))))))

theorem linesPass ∀ (index: Nat) (statements: List (Spaced Statement))
    (pre: Edge → Prop) (first: (index == 0) = True → ∀ (edge: Edge) => pre edge → Loose edge)
    (lexical: LexicalLines statements)
    (closed: ClosedLines statements):
    PassesAll (statementLines index statements) pre Meets :=
  match statements, lexical, closed with
    | [], _, never => (Bool.falseNotTrue never).impossible
    | [{ blankBefore, line }], Both lexLine _, coded =>
      passesCons _ _ pre Loose Meets
        (lineStartPasses index blankBefore pre first)
        (passesLast _ Loose Meets
          (passesTo _ _ (Leaves line) Meets (statementPasses line lexLine) (codedMeets line coded)))
    | [{ blankBefore, line }, next, ..rest], Both lexLine others, closed =>
      passesCons _ _ pre Loose Meets
        (lineStartPasses index blankBefore pre first)
        (passesCons _ _ Loose Open Meets
          (passesTo _ _ (Leaves line) Open (statementPasses line lexLine) (edge reached => byComputing))
          (linesPass (index + 1) [next, ..rest] Open (zero => (succNotZero index zero).impossible) others closed))

--| A block: its statements one a line, below.
theorem blockPasses ∀ (statements: List (Spaced Statement)) (pre: Edge → Prop)
    (lexical: LexicalLines statements)
    (closed: ClosedLines statements):
    Passes (below (Doc.concat (statementLines 0 statements))) pre Meets :=
  passesBelow _ pre Meets
    (passesConcat _ Loose Meets (linesPass 0 statements Loose (zero edge holds => holds) lexical closed))

theorem statementPasses ∀ (statement: Statement)
    (lexical: LexicalStatement statement):
    Passes statement.layout Loose (Leaves statement) :=
  match statement, lexical with
    | Let letComments name nameComments equals body, Both fineLet
        (Both (Both word _) (Both fineName (Both fineEquals lexBody))) =>
      bindingPasses letComments name nameComments equals body fineLet word fineName fineEquals lexBody
    | Bare value, lexValue => passesFrom _ _ Loose _ (exprPasses value lexValue) (looseEnters value)
    | StatementNote comment, fine => passesComment comment fine

theorem branchPasses ∀ (keyword: Comments) (body: Body)
    (lexical: LexicalBody body):
    Passes (branch keyword body) Meets Meets :=
  match body, lexical with
    | { statements = [] }, Both _ never => (Bool.falseNotTrue never).impossible
    | { statements = [{ blankBefore, line = Bare value }] }, Both (Both lexValue _) _ =>
      let whole := passesFrom value.layout (Enters value) Loose Meets (exprPasses value lexValue) (looseEnters value)
      match g: keyword.after.isNone with
        | True => bareBranchPasses value whole
        | False => passesBelow _ Meets Meets whole
    | { statements = [{ blankBefore, line = Let letComments name nameComments equals inner }] }, Both lexLines closed =>
      blockPasses [{ blankBefore, line = Let letComments name nameComments equals inner }] Meets lexLines closed
    | { statements = [{ blankBefore, line = StatementNote comment }] }, Both lexLines closed =>
      blockPasses [{ blankBefore, line = StatementNote comment }] Meets lexLines closed
    | { statements = [first, second, ..rest] }, Both lexLines closed =>
      blockPasses [first, second, ..rest] Meets lexLines closed

theorem elseBranchPasses ∀ (elseComments: Comments) (body: Body)
    (lexical: LexicalBody body):
    Passes (elseBranch elseComments body) Meets Meets :=
  match body, lexical with
    | { statements = [{ blankBefore, line = Bare value }] }, lexical =>
      match value, lexical with
        | If ifComments condition thenComments whenTrue innerElse whenFalse, lexical =>
          match g: elseComments.after.isNone && ifComments.above.isEmpty with
            | True =>
              match lexical with
                | (((((fineIf, lexCondition, fineThen, lexTrue, fineElse, lexFalse)), _)), _) =>
                  passesTwo
                    (Doc.text " ")
                    (ifLayout ifComments condition thenComments whenTrue innerElse whenFalse)
                    Meets
                    Loose
                    Meets
                    passesSpace
                    (passesFrom _
                      (Admits "if")
                      Loose
                      Meets
                      (ifPasses ifComments condition thenComments whenTrue innerElse whenFalse fineIf fineThen fineElse
                        (exprPasses condition lexCondition)
                        (branchPasses thenComments whenTrue lexTrue)
                        (elseBranchPasses innerElse whenFalse lexFalse))
                      (looseAdmits "if"))
            | False => branchPasses elseComments { statements = [{ blankBefore, line = Bare value }] } lexical
        | _, lexical => branchPasses elseComments { statements = [{ blankBefore, line = Bare value }] } lexical
    | { statements = [] }, lexical => branchPasses elseComments { statements = [] } lexical
    | { statements = [{ blankBefore, line = Let letComments name nameComments equals inner }] }, lexical =>
      branchPasses elseComments
        { statements = [{ blankBefore, line = Let letComments name nameComments equals inner }] }
        lexical
    | { statements = [{ blankBefore, line = StatementNote comment }] }, lexical =>
      branchPasses elseComments { statements = [{ blankBefore, line = StatementNote comment }] } lexical
    | { statements = [{ blankBefore, line = Bare value }, second, ..rest] }, lexical =>
      match value, lexical with
        | If ifComments condition thenComments whenTrue innerElse whenFalse, lexical =>
          branchPasses elseComments { statements = [{ blankBefore, line = Bare value }, second, ..rest] } lexical
        | _, lexical =>
          branchPasses elseComments { statements = [{ blankBefore, line = Bare value }, second, ..rest] } lexical
    | {
        statements = [{ blankBefore, line = Let letComments name nameComments equals inner }, second, ..rest]
      }, lexical =>
      branchPasses elseComments
        { statements = [{ blankBefore, line = Let letComments name nameComments equals inner }, second, ..rest] }
        lexical
    | { statements = [{ blankBefore, line = StatementNote comment }, second, ..rest] }, lexical =>
      branchPasses elseComments { statements = [{ blankBefore, line = StatementNote comment }, second, ..rest] } lexical

theorem afterEqualsPasses ∀ (body: Body) (equals: Comments)
    (lexical: LexicalBody body):
    Passes (body.afterEquals equals) Meets Meets :=
  match body, lexical with
    | { statements = [{ blankBefore, line = Bare value }] }, Both (Both lexValue _) _ =>
      let whole := passesFrom value.layout (Enters value) Loose Meets (exprPasses value lexValue) (looseEnters value)
      match g: equals.after.isNone with
        | True =>
          match value with
            | ListLiteral open items trailingComma close =>
              passesChoiceTwo _ _ Meets Meets
                (passesTwo
                  (Doc.text " ")
                  (Flatten (ListLiteral open items trailingComma close).layout)
                  Meets
                  Loose
                  Meets
                  passesSpace
                  whole)
                (passesTwo
                  (Doc.text " ")
                  (ListLiteral open items trailingComma close).layout
                  Meets
                  Loose
                  Meets
                  passesSpace
                  whole)
            | _ =>
              passesChoiceThree _ _ _ Meets Meets
                (passesTwo (Doc.text " ") (Flatten value.layout) Meets Loose Meets passesSpace whole)
                (passesOneLineBelow _ Meets Meets whole)
                (passesBelow _ Meets Meets whole)
        | False => passesBelow _ Meets Meets whole
    | { statements = [] }, Both _ never => (Bool.falseNotTrue never).impossible
    | { statements = [{ blankBefore, line = Let letComments name nameComments equals inner }] }, Both lexLines closed =>
      blockPasses [{ blankBefore, line = Let letComments name nameComments equals inner }] Meets lexLines closed
    | { statements = [{ blankBefore, line = StatementNote comment }] }, Both lexLines closed =>
      blockPasses [{ blankBefore, line = StatementNote comment }] Meets lexLines closed
    | { statements = [first, second, ..rest] }, Both lexLines closed =>
      blockPasses [first, second, ..rest] Meets lexLines closed

theorem bindingPasses ∀ (letComments: Comments) (name: Text) (nameComments equals: Comments) (body: Body)
    (fineLet: Fine letComments)
    (word: IsWord name)
    (fineName: Fine nameComments)
    (fineEquals: Fine equals)
    (lexBody: LexicalBody body):
    Passes (binding letComments name nameComments equals body) Loose Meets :=
  passesConcat _ Loose Meets
    (passesCons
      (token letComments "let") _
      Loose
      Meets
      Meets
      (looseKeyword letComments LetKeyword fineLet)
      (passesCons
        (Doc.text " ") _
        Meets
        Loose
        Meets
        passesSpace
        (passesCons
          (token nameComments name) _
          Loose
          Meets
          Meets
          (looseToken nameComments name fineName (wordToken name word))
          (passesCons
            (Doc.text " ") _
            Meets
            Loose
            Meets
            passesSpace
            (passesCons
              (token equals "=") _
              Loose
              Meets
              Meets
              (looseToken equals "=" fineEquals definesToken)
              (passesLast _ Meets Meets (afterEqualsPasses body equals lexBody)))))))

-- Declarations and the file.

theorem colonSign ∀ (same: Colon = Defines): Void := cases

theorem shutsColon: Shuts ":" := later => (byComputing, byComputing, byComputing)

theorem typePasses ∀ (annotation: TypeExpr) (lexical: LexicalType annotation): Passes annotation.layout Free Meets :=
  match annotation, lexical with
    | TypeName name comments, Both (Both word _) fine => freeToken comments name fine (wordToken name word)
    | TypeBracketed open inner close, Both fineOpen (Both lexInner fineClose) =>
      passesConcat _ Free Meets
        (passesCons _ _ Free Free Meets
          (openingToken open OpenParen Free fineOpen openSign (freeAdmits "("))
          (passesCons _ _ Free Meets Meets
            (typePasses inner lexInner)
            (passesLast _ Meets Meets (meetingCloser close ")" fineClose (signToken CloseParen closeSign) shutsClose))))

theorem namesAfterPasses ∀ (names: List Named) (lexical: LexicalNames names): Passes (namesAfter names) Meets Meets :=
  match names, lexical with
    | [], _ => passesEmpty Meets
    | [{ name, comments }, ..rest], Both (Both (Both word _) fine) others =>
      passesConcat _ Meets Meets
        (passesCons
          (Doc.text " ") _
          Meets
          Loose
          Meets
          passesSpace
          (passesCons _ _ Loose Meets Meets
            (looseToken comments name fine (wordToken name word))
            (passesLast _ Meets Meets (namesAfterPasses rest others))))

--| A group from after `(` or `,`: its names, `:` against the last, then a
--| space and the type.
theorem groupPasses ∀ (group: ParameterGroup) (lexical: LexicalGroup group): Passes group.layout Free Meets :=
  match group, lexical with
    | Untyped { name, comments }, Both (Both word _) fine => freeToken comments name fine (wordToken name word)
    | Typed names colon annotation, Both (Both (Both word _) fine) (Both lexNames (Both fineColon lexType)) =>
      passesConcat _ Free Meets
        (passesCons _ _ Free Meets Meets
          (freeToken names.head.comments names.head.name fine (wordToken names.head.name word))
          (passesCons _ _ Meets Meets Meets
            (namesAfterPasses names.tail lexNames)
            (passesCons _ _ Meets Meets Meets
              (meetingToken colon ":" fineColon (signToken Colon colonSign) shutsColon)
              (passesCons
                (Doc.text " ") _
                Meets
                Gapped
                Meets
                passesGap
                (passesLast _ Gapped Meets (passesFrom _ _ Gapped _ (typePasses annotation lexType) gappedFree))))))

theorem parameterDocsPass ∀ (parameters: List ParameterGroup)
    (lexical: LexicalParameters parameters):
    EachPasses (parameterDocs parameters) :=
  match parameters, lexical with
    | [], _ => byComputing
    | [group], Both lexGroup _ => ((groupPasses group lexGroup), byComputing)
    | [group, next, ..rest], Both lexGroup others => (
      (passesTwo group.layout
        (Closing ",")
        Free
        Meets
        Meets
        (groupPasses group lexGroup)
        (closingPasses "," (signToken Comma commaSign) shutsComma)),
      (parameterDocsPass [next, ..rest] others)
    )

theorem takesPasses ∀ (takes: Option Comments) (fine: FineTakes takes): Passes (takesDoc takes) Meets Meets :=
  match takes, fine with
    | None, _ => passesEmpty Meets
    | Some comments, fineTakes =>
      passesConcat _ Meets Meets
        (passesCons
          (Doc.text " ") _
          Meets
          Loose
          Meets
          passesSpace
          (passesCons _ _ Loose Meets Meets
            (looseKeyword comments TakesKeyword fineTakes)
            (passesLast _ Meets Meets (passesTo _ _ Gapped Meets passesGap gappedMeets))))

theorem headerPasses ∀ (fnComments: Comments) (name: Text) (nameComments: Comments) (takes: Option Comments)
    (open: Comments) (parameters: List ParameterGroup) (close equals: Comments)
    (fineFn: Fine fnComments)
    (word: IsWord name)
    (fineName: Fine nameComments)
    (fineTakes: FineTakes takes)
    (fineOpen: Fine open)
    (lexParameters: LexicalParameters parameters)
    (fineClose: Fine close)
    (fineEquals: Fine equals):
    Passes (header fnComments name nameComments takes open parameters close equals) Loose Meets :=
  let opening: Passes
    (Doc.concat [token fnComments "fn", Doc.text " ", token nameComments name, takesDoc takes, token open "("])
    Loose
    Free :=
    passesConcat _ Loose Free
      (passesCons
        (token fnComments "fn") _
        Loose
        Meets
        Free
        (looseKeyword fnComments FnKeyword fineFn)
        (passesCons
          (Doc.text " ") _
          Meets
          Loose
          Free
          passesSpace
          (passesCons
            (token nameComments name) _
            Loose
            Meets
            Free
            (looseToken nameComments name fineName (wordToken name word))
            (passesCons _ _ Meets Meets Free
              (takesPasses takes fineTakes)
              (passesLast _ Meets Free
                (openingToken open OpenParen Meets fineOpen openSign (meetsAdmits "(" shutsOpen)))))))
  let closing: Passes (Doc.concat [closer close ")", Doc.text " ", token equals "="]) Meets Meets :=
    passesConcat _ Meets Meets
      (passesCons
        (closer close ")") _
        Meets
        Meets
        Meets
        (meetingCloser close ")" fineClose (signToken CloseParen closeSign) shutsClose)
        (passesCons
          (Doc.text " ") _
          Meets
          Loose
          Meets
          passesSpace
          (passesLast _ Loose Meets (looseToken equals "=" fineEquals definesToken))))
  match parameters with
    | [] => passesTwo _ _ Loose Free Meets opening (passesFrom _ Meets Free Meets closing freeMeets)
    | [first, ..others] =>
      passesGroup _ Loose Meets
        (passesConcat _ Loose Meets
          (passesCons _ _ Loose Free Meets opening
            (passesCons
              (Nest 4 (Doc.concat [SoftLine, parameterDocs [first, ..others] |> joined Line])) _
              Free
              Meets
              Meets
              (passesTwo SoftLine
                (parameterDocs [first, ..others] |> joined Line)
                Free
                Free
                Meets
                (passesSoft Free Free (edge holds => holds) byComputing)
                (joinedPasses (parameterDocs [first, ..others]) (parameterDocsPass [first, ..others] lexParameters)))
              (passesCons SoftLine _ Meets Meets Meets
                (passesSoft Meets Meets (edge holds => holds) byComputing)
                (passesLast _ Meets Meets closing)))))

theorem declarationPasses ∀ (declaration: Declaration)
    (lexical: LexicalDeclaration declaration):
    Passes declaration.layout Loose Open :=
  match declaration, lexical with
    | Function fnComments name nameComments takes open parameters trailingComma close equals body, (
        fineFn,
        (word, _),
        fineName,
        fineTakes,
        fineOpen,
        lexParameters,
        fineClose,
        fineEquals,
        lexBody
      ) =>
      passesTo _ _ Meets Open
        (passesTwo
          (header fnComments name nameComments takes open parameters close equals)
          (body.afterEquals equals)
          Loose
          Meets
          Meets
          (headerPasses fnComments name nameComments takes open parameters close equals fineFn word fineName fineTakes
              fineOpen lexParameters fineClose fineEquals)
          (afterEqualsPasses body equals lexBody))
        (edge reached => byComputing)
    | Value letComments name nameComments equals body, Both fineLet
        (Both (Both word _) (Both fineName (Both fineEquals lexBody))) =>
      passesTo _ _ Meets Open
        (bindingPasses letComments name nameComments equals body fineLet word fineName fineEquals lexBody)
        (edge reached => byComputing)
    | DeclarationNote comment, fine => passesComment comment fine

theorem declarationLinesPass ∀ (index: Nat) (declarations: List (Spaced Declaration))
    (pre: Edge → Prop) (first: (index == 0) = True → ∀ (edge: Edge) => pre edge → Loose edge)
    (lexical: LexicalDeclarations declarations):
    PassesAll (declarationLines index declarations) pre Open :=
  match declarations, lexical with
    | [], _ => passesNil pre Open (edge holds => byComputing)
    | [{ blankBefore, line }, ..rest], Both lexLine others =>
      passesCons _ _ pre Open Open
        (passesTwo
          (lineStart index blankBefore)
          line.layout
          pre
          Loose
          Open
          (lineStartPasses index blankBefore pre first)
          (declarationPasses line lexLine))
        (declarationLinesPass (index + 1) rest Open (zero => (succNotZero index zero).impossible) others)

--| The document the rules build for a file joins from a line start, and
--| its words are proper: each token is put only before what it is still
--| read whole before, whichever way the layout goes.
theorem fileJoins ∀ (file: SourceFile) (lexical: LexicalFile file): Passes file.layout Loose Open :=
  match file, lexical with
    | { declarations = [] }, _ => (byComputing, (edge next holds after => after edge byComputing))
    | { declarations = [first, ..rest] }, lexical =>
      passesTwo
        (Doc.concat (declarationLines 0 [first, ..rest]))
        HardLine
        Loose
        Open
        Open
        (passesConcat _ Loose Open (declarationLinesPass 0 [first, ..rest] Loose (zero edge holds => holds) lexical))
        (passesTo _ _ Loose Open (passesHard Open) (edge reached => byComputing))

--| `LexicalFile` can be met: the tree of `let x = 1`.
theorem lexicalExample: LexicalFile {
      declarations = [
        {
          blankBefore = False,
          line = Value Comments.none "x" Comments.none Comments.none {
            statements = [{ blankBefore = False, line = Bare (NumberLiteral "1" Comments.none) }]
          }
        }
      ]
    } :=
  (
    ((
      ((byComputing, byComputing)),
      (((('x', [], byComputing, byComputing, byComputing)), byComputing)),
      ((byComputing, byComputing)),
      ((byComputing, byComputing)),
      (((((('1', [], byComputing, byComputing, byComputing)), byComputing, byComputing)), byComputing)),
      byComputing
    )),
    byComputing
  )
