--| The rules print every token of the tree, and its comments, once and in
--| the tree's order, at every width.
--|
--| A tree's pieces (`SourceFile.pieces`) are its tokens' texts and its
--| comments' as the source has them: a token's own-line comments, the
--| token, its trailing comment, construct by construct. The document the
--| rules build for a tree has exactly those words, and every option of
--| each of its choices has the same (`fileWrites`), so by the engine's
--| `printWords` the printed text is those pieces with only layout between
--| them (`printPieces`): no token or comment is lost, repeated or moved,
--| whatever fits.

namespace Toy.Fmt.Proofs
import Toy.Doc (..)
import Toy.Doc.Proofs (..)
import Toy.Syntax (..)
import Toy.Fmt (..)
import Std (Bool, Eq, List, Option, Text, Void)

--| `doc` writes `pieces`: its words are those of the pieces that aren't
--| layout, whichever option its choices take.
def Writes (doc: Doc) (pieces: List Text): Prop := Uniform doc ∧ doc.words = wordsOf pieces

--| The documents, one after another, write `pieces`.
def WritesAll (docs: List Doc) (pieces: List Text): Prop := AllUniform docs ∧ wordsAll docs = wordsOf pieces

theorem writesNil: WritesAll [] [] := Both rfl rfl

theorem writesCons ∀ (doc: Doc) (docs: List Doc) (pieces later: List Text)
    (first: Writes doc pieces)
    (rest: WritesAll docs later):
    WritesAll [doc, ..docs] (pieces ++ later) :=
  match first, rest with
    | Both uniform words, Both restUniform restWords =>
      Both
        (Both uniform restUniform)
        (rewrite words, restWords in Eq.sym (List.filterAppend pieces later (piece => not (isLayout piece))))

theorem writesLast ∀ (doc: Doc) (pieces: List Text) (only: Writes doc pieces): WritesAll [doc] pieces :=
  rewrite <- List.appendNil pieces in writesCons doc [] pieces [] only writesNil

theorem emptyNoWords ∀ (doc: Doc) (empty: doc.isEmpty = True): doc.words = [] := match doc, empty with | Empty, _ => rfl

theorem filterWords ∀ (docs: List Doc): wordsAll (docs.filter (doc => not doc.isEmpty)) = wordsAll docs :=
  match docs with
    | [] => rfl
    | [doc, ..rest] =>
      match empty: doc.isEmpty with
        | True => rewrite emptyNoWords doc empty in filterWords rest
        | False => Eq.cong (later => doc.words ++ later) (filterWords rest)

theorem filterUniform ∀ (docs: List Doc)
    (uniform: AllUniform docs):
    AllUniform (docs.filter (doc => not doc.isEmpty)) :=
  match docs, uniform with
    | [], _ => rfl
    | [doc, ..rest], Both first others =>
      match empty: doc.isEmpty with
        | True => filterUniform rest others
        | False => Both first (filterUniform rest others)

theorem writesConcat ∀ (docs: List Doc) (pieces: List Text)
    (each: WritesAll docs pieces):
    Writes (Doc.concat docs) pieces :=
  match each with
    | Both uniform words =>
      let keptUniform := filterUniform docs uniform
      let keptWords := filterWords docs
      match kept: docs.filter (doc => not doc.isEmpty) with
        | [] => Both rfl (Eq.trans keptWords words)
        | [only] =>
          match keptUniform with
            | Both first _ => Both first (Eq.trans (Eq.sym (List.appendNil only.words)) (Eq.trans keptWords words))
        | [first, second, ..rest] => Both keptUniform (Eq.trans keptWords words)

theorem writesEmpty: Writes Empty [] := Both rfl rfl

theorem writesText ∀ (text: Text): Writes (Doc.text text) [text] := Both rfl rfl

--| A space between tokens is layout.
theorem writesSpace: Writes (Doc.text " ") [] := Both rfl rfl

theorem writesNest ∀ (indent: Nat) (inner: Doc) (pieces: List Text)
    (writes: Writes inner pieces):
    Writes (Nest indent inner) pieces :=
  writes

theorem writesGroup ∀ (inner: Doc) (pieces: List Text) (writes: Writes inner pieces): Writes (Doc.group inner) pieces :=
  writes

theorem writesFlatten ∀ (inner: Doc) (pieces: List Text) (writes: Writes inner pieces): Writes (Flatten inner) pieces :=
  writes

theorem writesOneLineBelow ∀ (inner: Doc) (pieces: List Text)
    (writes: Writes inner pieces):
    Writes (OneLineBelow inner) pieces :=
  writes

theorem writesFill ∀ (items: List Doc) (pieces: List Text) (each: WritesAll items pieces): Writes (Fill items) pieces :=
  each

theorem writesTwo ∀ (first second: Doc) (pieces later: List Text)
    (one: Writes first pieces)
    (two: Writes second later):
    Writes (Doc.concat [first, second]) (pieces ++ later) :=
  writesConcat _ _ (writesCons _ _ _ _ one (writesLast _ _ two))

theorem writesBelow ∀ (doc: Doc) (pieces: List Text) (writes: Writes doc pieces): Writes (below doc) pieces :=
  writesConcat
    [HardLine, doc]
    pieces
    (writesCons HardLine [doc] [] pieces (Both rfl rfl) (writesLast doc pieces writes))

theorem writesChoiceTwo ∀ (first second: Doc) (pieces: List Text)
    (one: Writes first pieces)
    (two: Writes second pieces):
    Writes (Choice [first, second]) pieces :=
  match one, two with
    | Both uniform words, Both secondUniform secondWords =>
      Both
        (Both (Both uniform (Both secondUniform rfl)) (Both rfl (Both (Eq.trans secondWords (Eq.sym words)) rfl)))
        words

theorem writesChoiceThree ∀ (first second third: Doc) (pieces: List Text)
    (one: Writes first pieces)
    (two: Writes second pieces)
    (three: Writes third pieces):
    Writes (Choice [first, second, third]) pieces :=
  match one, two, three with
    | Both uniform words, Both secondUniform secondWords, Both thirdUniform thirdWords =>
      Both
        (Both
          (Both uniform (Both secondUniform (Both thirdUniform rfl)))
          (Both rfl (Both (Eq.trans secondWords (Eq.sym words)) (Both (Eq.trans thirdWords (Eq.sym words)) rfl))))
        words

-- The tree's pieces.

def commentTexts: List Comment → List Text
  | [] => []
  | [comment, ..rest] => [comment.text, ..commentTexts rest]

def afterTexts: Option Comment → List Text
  | None => []
  | Some comment => [comment.text]

--| A token as the source has it: its own-line comments, its text, its
--| trailing comment.
def tokenPieces (comments: Comments) (text: Text): List Text :=
  commentTexts comments.above ++ [text, ..afterTexts comments.after]

theorem writesTrailing ∀ (after: Option Comment): Writes (trailingComment after) (afterTexts after) := match after with
  | None => Both rfl rfl
  | Some comment => Both rfl rfl

theorem writesCommentLines ∀ (comments: List Comment):
    WritesAll (comments.map (comment => Doc.concat [Doc.text comment.text, CommentEnd])) (commentTexts comments) :=
  match comments with
    | [] => writesNil
    | [comment, ..rest] =>
      writesCons _ _
        [comment.text]
        (commentTexts rest)
        (writesConcat
          [Doc.text comment.text, CommentEnd]
          [comment.text]
          (writesCons _ _ [comment.text] [] (writesText comment.text) (writesLast CommentEnd [] (Both rfl rfl))))
        (writesCommentLines rest)

theorem writesCommentsAbove ∀ (comments: List Comment): Writes (commentsAbove comments) (commentTexts comments) :=
  match comments with
    | [] => writesEmpty
    | [comment, ..rest] =>
      writesConcat _ _
        (writesCons LineStart _ []
          (commentTexts [comment, ..rest])
          (Both rfl rfl)
          (writesCommentLines [comment, ..rest]))

--| A token is written with its comments around it.
theorem writesToken ∀ (comments: Comments) (text: Text): Writes (token comments text) (tokenPieces comments text) :=
  writesConcat _ _
    (writesCons _ _
      (commentTexts comments.above)
      [text, ..afterTexts comments.after]
      (writesCommentsAbove comments.above)
      (writesCons _ _
        [text]
        (afterTexts comments.after)
        (writesText text)
        (writesLast _ _ (writesTrailing comments.after))))

theorem writesCloserLines ∀ (comments: List Comment):
    WritesAll (Doc.joinedWith HardLine (comments.map (comment => Doc.text comment.text))) (commentTexts comments) :=
  match comments with
    | [] => writesNil
    | [only] => writesLast _ _ (writesText only.text)
    | [comment, next, ..rest] =>
      writesCons _ _
        [comment.text]
        (commentTexts [next, ..rest])
        (writesText comment.text)
        (writesCons HardLine _ [] (commentTexts [next, ..rest]) (Both rfl rfl) (writesCloserLines [next, ..rest]))

--| A closing bracket is written as any token: its comments, itself, its
--| trailing comment.
theorem writesCloser ∀ (comments: Comments) (text: Text): Writes (closer comments text) (tokenPieces comments text) :=
  match comments with
    | { above = [], after } => writesToken { above = [], after } text
    | { above = [comment, ..rest], after } =>
      let lines := [comment, ..rest].map (comment => Doc.text comment.text) |> joined HardLine
      writesConcat
        [Nest 2 (Doc.concat [LineStartHere, lines]), HardLine, Doc.text text, trailingComment after]
        (commentTexts [comment, ..rest] ++ [text, ..afterTexts after])
        (writesCons _ _
          (commentTexts [comment, ..rest])
          [text, ..afterTexts after]
          (writesConcat
            [LineStartHere, lines]
            (commentTexts [comment, ..rest])
            (writesCons LineStartHere
              [lines]
              []
              (commentTexts [comment, ..rest])
              (Both rfl rfl)
              (writesLast lines _ (writesConcat _ _ (writesCloserLines [comment, ..rest])))))
          (writesCons HardLine _ []
            [text, ..afterTexts after]
            (Both rfl rfl)
            (writesCons _ _ [text] (afterTexts after) (writesText text) (writesLast _ _ (writesTrailing after)))))

def itemPieces: List Item → List Text
  | [] => []
  | [{ value, .. }] => value.pieces
  | [{ value, comma }, ..rest] => (value.pieces ++ tokenPieces comma ",") ++ itemPieces rest

--| The expression's tokens and comments, in the source's order. The last
--| item of a list or call has no comma.
def Expr.pieces: Expr → List Text
  | Var name comments => tokenPieces comments name
  | NumberLiteral digits comments => tokenPieces comments digits
  | StringLiteral written comments => tokenPieces comments written
  | Bracketed open inner close => tokenPieces open "(" ++ (inner.pieces ++ tokenPieces close ")")
  | ListLiteral open items close => tokenPieces open "[" ++ (itemPieces items ++ tokenPieces close "]")
  | Call callee open arguments close =>
    callee.pieces ++ (tokenPieces open "(" ++ (itemPieces arguments ++ tokenPieces close ")"))
  | Field target dot name nameComments => target.pieces ++ (tokenPieces dot "." ++ tokenPieces nameComments name)
  | Negate minus operand => tokenPieces minus "-" ++ operand.pieces
  | Binary operator sign left right => left.pieces ++ (tokenPieces sign operator.spelling ++ right.pieces)
  | If ifComments condition thenComments whenTrue elseComments whenFalse =>
    tokenPieces ifComments "if"
      ++ (condition.pieces
        ++ (tokenPieces thenComments "then"
          ++ (whenTrue.pieces ++ (tokenPieces elseComments "else" ++ whenFalse.pieces))))

def Body.pieces: Body → List Text
  | { statements } => linePieces statements

def linePieces: List (Spaced Statement) → List Text
  | [] => []
  | [{ line, .. }] => line.pieces
  | [{ line, .. }, ..rest] => line.pieces ++ linePieces rest

def Statement.pieces: Statement → List Text
  | Let letComments name nameComments equals body => bindingPieces letComments name nameComments equals body.pieces
  | Bare value => value.pieces
  | StatementNote comment => [comment.text]

def bindingPieces (letComments: Comments) (name: Text) (nameComments equals: Comments) (body: List Text): List Text :=
  tokenPieces letComments "let" ++ (tokenPieces nameComments name ++ (tokenPieces equals "=" ++ body))

--| Each parameter, and its comma but the last's.
def parameterPieces: List Parameter → List Text
  | [] => []
  | [{ name, comments, .. }] => tokenPieces comments name
  | [{ name, comments, comma }, ..rest] => (tokenPieces comments name ++ tokenPieces comma ",") ++ parameterPieces rest

def headerPieces (fnComments: Comments) (name: Text) (nameComments open: Comments)
    (parameters: List Parameter) (close equals: Comments):
    List Text :=
  (tokenPieces fnComments "fn" ++ (tokenPieces nameComments name ++ tokenPieces open "("))
    ++ (parameterPieces parameters ++ (tokenPieces close ")" ++ tokenPieces equals "="))

def Declaration.pieces: Declaration → List Text
  | Function fnComments name nameComments open parameters close equals body =>
    headerPieces fnComments name nameComments open parameters close equals ++ body.pieces
  | Value letComments name nameComments equals body => bindingPieces letComments name nameComments equals body.pieces
  | DeclarationNote comment => [comment.text]

def declarationPieces: List (Spaced Declaration) → List Text
  | [] => []
  | [{ line, .. }, ..rest] => line.pieces ++ declarationPieces rest

--| The file's tokens and comments, in the source's order.
def SourceFile.pieces (file: SourceFile): List Text := declarationPieces file.declarations

-- The rules write the pieces.

theorem writesLayout ∀ (doc: Doc) (uniform: Uniform doc) (none: doc.words = []): Writes doc [] := Both uniform none

theorem writesThree ∀ (first second third: Doc) (pieces later last: List Text)
    (one: Writes first pieces)
    (two: Writes second later)
    (three: Writes third last):
    Writes (Doc.concat [first, second, third]) (pieces ++ (later ++ last)) :=
  writesConcat _ _ (writesCons _ _ _ _ one (writesCons _ _ _ _ two (writesLast _ _ three)))

theorem writesCloseAfter ∀ (expr: Expr) (doc: Doc) (pieces: List Text)
    (writes: Writes doc pieces):
    Writes (closeAfter expr doc) pieces :=
  match expr.endsWithComment with
    | True =>
      writesConcat
        [HardLine, doc]
        pieces
        (writesCons HardLine [doc] [] pieces (Both rfl rfl) (writesLast doc pieces writes))
    | False => writes

theorem joinedWithWords ∀ (separator: Doc) (docs: List Doc)
    (none: separator.words = []):
    wordsAll (Doc.joinedWith separator docs) = wordsAll docs :=
  match docs with
    | [] => rfl
    | [only] => rfl
    | [doc, next, ..rest] =>
      rewrite none in Eq.cong (later => doc.words ++ later) (joinedWithWords separator [next, ..rest] none)

theorem joinedWithUniform ∀ (separator: Doc) (docs: List Doc)
    (uniform: Uniform separator)
    (each: AllUniform docs):
    AllUniform (Doc.joinedWith separator docs) :=
  match docs, each with
    | [], _ => rfl
    | [only], given => given
    | [doc, next, ..rest], Both first others =>
      Both first (Both uniform (joinedWithUniform separator [next, ..rest] uniform others))

--| Documents joined by layout write what they write one after another.
theorem writesJoined ∀ (docs: List Doc) (separator: Doc) (pieces: List Text)
    (layout: Writes separator [])
    (each: WritesAll docs pieces):
    Writes (joined docs separator) pieces :=
  match layout, each with
    | Both uniform none, Both eachUniform words =>
      writesConcat
        (Doc.joinedWith separator docs)
        pieces
        (Both
          (joinedWithUniform separator docs uniform eachUniform)
          (Eq.trans (joinedWithWords separator docs none) words))

theorem writesLink ∀ (operator: Operator) (sign: Comments) (operand: Doc) (pieces: List Text)
    (writes: Writes operand pieces):
    Writes (link operator sign operand) (tokenPieces sign operator.spelling ++ pieces) :=
  writesConcat _ _
    (writesCons Line _ []
      (tokenPieces sign operator.spelling ++ pieces)
      (Both rfl rfl)
      (writesCons _ _
        (tokenPieces sign operator.spelling)
        pieces
        (writesToken sign operator.spelling)
        (writesCons (Doc.text " ") _ [] pieces writesSpace (writesLast operand pieces writes))))

theorem concatWords ∀ (docs: List Doc): (Doc.concat docs).words = wordsAll docs :=
  let keptWords := filterWords docs
  match kept: docs.filter (doc => not doc.isEmpty) with
    | [] => keptWords
    | [only] => Eq.trans (Eq.sym (List.appendNil only.words)) keptWords
    | [first, second, ..rest] => keptWords

theorem concatUniform ∀ (docs: List Doc) (uniform: AllUniform docs): Uniform (Doc.concat docs) :=
  let keptUniform := filterUniform docs uniform
  match kept: docs.filter (doc => not doc.isEmpty) with
    | [] => rfl
    | [only] =>
      (match keptUniform with
        | Both first _ => first)
    | [first, second, ..rest] => keptUniform

--| A chain's head and its links, grouped, write what the parts write.
theorem writesChain ∀ (first: Doc) (links: List Doc) (pieces: List Text)
    (parts: WritesAll [first, ..links] pieces):
    Writes (Doc.group (Doc.concat [first, Nest 2 (Doc.concat links)])) pieces :=
  match parts with
    | Both (Both uniform linksUniform) words =>
      let inner: first.words ++ ((Doc.concat links).words ++ []) = wordsOf pieces :=
        rewrite List.appendNil (Doc.concat links).words, concatWords links in words
      Both
        (concatUniform [first, Nest 2 (Doc.concat links)] (Both uniform (Both (concatUniform links linksUniform) rfl)))
        (Eq.trans (concatWords [first, Nest 2 (Doc.concat links)]) inner)

theorem lastOfCons ∀ (first: a) (rest: List a): ∃ (last: a) => [first, ..rest].last = Some last := match rest with
  | [] => Witness first rfl
  | [next, ..more] => lastOfCons next more

theorem writesLineStart ∀ (index: Nat) (blankBefore: Bool): Writes (lineStart index blankBefore) [] :=
  match index == 0 with
    | True => writesEmpty
    | False =>
      match blankBefore with
        | True => Both (Both rfl (Both rfl rfl)) rfl
        | False => Both rfl rfl

theorem ifWrites ∀ (ifComments: Comments) (condition: Expr) (thenComments: Comments) (whenTrue: Body)
    (elseComments: Comments) (whenFalse: Body)
    (conditionWrites: Writes condition.layout condition.pieces)
    (trueWrites: Writes (branch thenComments whenTrue) whenTrue.pieces)
    (falseWrites: Writes (elseBranch elseComments whenFalse) whenFalse.pieces):
    Writes
      (ifLayout ifComments condition thenComments whenTrue elseComments whenFalse)
      (If ifComments condition thenComments whenTrue elseComments whenFalse).pieces :=
  let afterElse := tokenPieces elseComments "else" ++ whenFalse.pieces
  let afterThen := tokenPieces thenComments "then" ++ (whenTrue.pieces ++ afterElse)
  writesGroup _ _
    (writesConcat _ _
      (writesCons _ _
        (tokenPieces ifComments "if")
        (condition.pieces ++ afterThen)
        (writesToken ifComments "if")
        (writesCons
          (Doc.text " ") _
          []
          (condition.pieces ++ afterThen)
          writesSpace
          (writesCons _ _ condition.pieces afterThen conditionWrites
            (writesCons
              (Doc.text " ") _
              []
              afterThen
              writesSpace
              (writesCons _ _
                (tokenPieces thenComments "then")
                (whenTrue.pieces ++ afterElse)
                (writesToken thenComments "then")
                (writesCons _ _ whenTrue.pieces afterElse trueWrites
                  (writesCons Line _ [] afterElse
                    (Both rfl rfl)
                    (writesCons _ _
                      (tokenPieces elseComments "else")
                      whenFalse.pieces
                      (writesToken elseComments "else")
                      (writesLast _ _ falseWrites))))))))))

theorem chainWrites ∀ (level: Nat) (expr: Expr)
    (whole: Writes expr.layout expr.pieces)
    (more: List Doc) (morePieces: List Text)
    (rest: WritesAll more morePieces):
    WritesAll (chainParts level expr ++ more) (expr.pieces ++ morePieces) :=
  match expr with
    | Binary operator sign left right =>
      match same: operator.level == level with
        | True =>
          let linkPieces := tokenPieces sign operator.spelling ++ right.pieces
          rewrite List.appendAssoc (chainParts level left) [link operator sign right.layout] more,
              List.appendAssoc left.pieces linkPieces morePieces in
            chainWrites level left
              (exprWrites left)
              ([link operator sign right.layout] ++ more)
              (linkPieces ++ morePieces)
              (writesCons _ _ linkPieces morePieces
                (writesLink operator sign right.layout right.pieces (exprWrites right))
                rest)
        | False => writesCons _ _ _ _ whole rest
    | Var name comments => writesCons _ _ _ _ whole rest
    | NumberLiteral digits comments => writesCons _ _ _ _ whole rest
    | StringLiteral written comments => writesCons _ _ _ _ whole rest
    | Bracketed open inner close => writesCons _ _ _ _ whole rest
    | ListLiteral open items close => writesCons _ _ _ _ whole rest
    | Call callee open arguments close => writesCons _ _ _ _ whole rest
    | Field target dot name nameComments => writesCons _ _ _ _ whole rest
    | Negate minus operand => writesCons _ _ _ _ whole rest
    | If ifComments condition thenComments whenTrue elseComments whenFalse => writesCons _ _ _ _ whole rest

--| An expression's document writes its tokens and comments in order.
theorem exprWrites ∀ (expr: Expr): Writes expr.layout expr.pieces := match expr with
  | Var name comments => writesToken comments name
  | NumberLiteral digits comments => writesToken comments digits
  | StringLiteral written comments => writesToken comments written
  | Bracketed open inner close =>
    writesThree _ _ _ _ _ _
      (writesToken open "(")
      (exprWrites inner)
      (writesCloseAfter inner _ _ (writesCloser close ")"))
  | ListLiteral open items close => listWrites open items close
  | Call callee open arguments close => writesTwo _ _ _ _ (exprWrites callee) (argumentsWrite open arguments close)
  | Field target dot name nameComments =>
    writesThree _ _ _ _ _ _ (exprWrites target) (writesToken dot ".") (writesToken nameComments name)
  | Negate minus operand =>
    writesThree _ _ _
      (tokenPieces minus "-")
      []
      operand.pieces
      (writesToken minus "-")
      (match operand.startsWithMinus with
        | True => Both rfl rfl
        | False => Both rfl rfl)
      (exprWrites operand)
  | Binary operator sign left right =>
    let parts :=
      chainWrites operator.level left
        (exprWrites left)
        [link operator sign right.layout]
        (tokenPieces sign operator.spelling ++ right.pieces)
        (writesLast _ _ (writesLink operator sign right.layout right.pieces (exprWrites right)))
    match found: chainParts operator.level left ++ [link operator sign right.layout] with
      | [first, ..links] => writesChain first links _ parts
      | [] =>
        Both rfl
          (match parts with
            | Both _ words => words)
  | If ifComments condition thenComments whenTrue elseComments whenFalse =>
    ifWrites ifComments condition thenComments whenTrue elseComments whenFalse
      (exprWrites condition)
      (branchWrites thenComments whenTrue)
      (elseBranchWrites elseComments whenFalse)

theorem itemDocsWrite ∀ (items: List Item): WritesAll (itemDocs items) (itemPieces items) := match items with
  | [] => writesNil
  | [{ value, comma }] => writesLast _ _ (exprWrites value)
  | [{ value, comma }, next, ..rest] =>
    writesCons _ _
      (value.pieces ++ tokenPieces comma ",")
      (itemPieces [next, ..rest])
      (writesTwo _ _ _ _ (exprWrites value) (writesCloseAfter value _ _ (writesToken comma ",")))
      (itemDocsWrite [next, ..rest])

theorem listWrites ∀ (open: Comments) (items: List Item) (close: Comments):
    Writes (listLayout open items close) (ListLiteral open items close).pieces :=
  match items with
    | [] => writesTwo _ _ _ _ (writesToken open "[") (writesCloser close "]")
    | [first, ..rest] =>
      match lastOfCons first rest with
        | Witness last found =>
          rewrite found in
            writesGroup _ _
              (writesThree _ _ _ _ _ _
                (writesToken open "[")
                (writesNest 2 _ _ (writesFill _ _ (itemDocsWrite [first, ..rest])))
                (writesCloseAfter last.value _ _ (writesCloser close "]")))

theorem argumentsWrite ∀ (open: Comments) (arguments: List Item) (close: Comments):
    Writes
      (argumentsLayout open arguments close)
      (tokenPieces open "(" ++ (itemPieces arguments ++ tokenPieces close ")")) :=
  match arguments with
    | [] => writesTwo _ _ _ _ (writesToken open "(") (writesCloser close ")")
    | [first, ..rest] =>
      writesGroup _ _
        (writesConcat _ _
          (writesCons _ _
            (tokenPieces open "(")
            (itemPieces [first, ..rest] ++ tokenPieces close ")")
            (writesToken open "(")
            (writesCons _ _
              (itemPieces [first, ..rest])
              (tokenPieces close ")")
              (writesNest 2 _ _
                (writesConcat
                  [SoftLine, itemDocs [first, ..rest] |> joined Line]
                  (itemPieces [first, ..rest])
                  (writesCons SoftLine _ []
                    (itemPieces [first, ..rest])
                    (Both rfl rfl)
                    (writesLast _ _ (writesJoined _ Line _ (Both rfl rfl) (itemDocsWrite [first, ..rest]))))))
              (writesCons SoftLine _ []
                (tokenPieces close ")")
                (Both rfl rfl)
                (writesLast _ _ (writesCloser close ")"))))))

theorem linesWrite ∀ (index: Nat) (statements: List (Spaced Statement)):
    WritesAll (statementLines index statements) (linePieces statements) :=
  match statements with
    | [] => writesNil
    | [{ blankBefore, line }] =>
      writesCons _ _ [] line.pieces (writesLineStart index blankBefore) (writesLast _ _ (statementWrites line))
    | [{ blankBefore, line }, next, ..rest] =>
      writesCons _ _ []
        (line.pieces ++ linePieces [next, ..rest])
        (writesLineStart index blankBefore)
        (writesCons _ _ line.pieces
          (linePieces [next, ..rest])
          (statementWrites line)
          (linesWrite (index + 1) [next, ..rest]))

theorem blockWrites ∀ (statements: List (Spaced Statement)):
    Writes (below (Doc.concat (statementLines 0 statements))) (linePieces statements) :=
  writesBelow _ _ (writesConcat _ _ (linesWrite 0 statements))

theorem statementWrites ∀ (statement: Statement): Writes statement.layout statement.pieces := match statement with
  | Let letComments name nameComments equals body => bindingWrites letComments name nameComments equals body
  | Bare value => exprWrites value
  | StatementNote comment => writesText comment.text

theorem branchBareWrites ∀ (value: Expr)
    (writes: Writes value.layout value.pieces):
    Writes (Choice [Doc.concat [Doc.text " ", Flatten value.layout], below value.layout]) value.pieces :=
  writesChoiceTwo _ _ _ (writesTwo _ _ [] value.pieces writesSpace (writesFlatten _ _ writes)) (writesBelow _ _ writes)

theorem branchWrites ∀ (keyword: Comments) (body: Body): Writes (branch keyword body) body.pieces := match body with
  | { statements = [] } => blockWrites []
  | { statements = [{ blankBefore, line = Bare value }] } =>
    match g: keyword.after.isNone with
      | True => branchBareWrites value (exprWrites value)
      | False => writesBelow _ _ (exprWrites value)
  | { statements = [{ blankBefore, line = Let letComments name nameComments equals inner }] } =>
    blockWrites [{ blankBefore, line = Let letComments name nameComments equals inner }]
  | { statements = [{ blankBefore, line = StatementNote comment }] } =>
    blockWrites [{ blankBefore, line = StatementNote comment }]
  | { statements = [first, second, ..rest] } => blockWrites [first, second, ..rest]

theorem elseBranchWrites ∀ (elseComments: Comments) (body: Body): Writes (elseBranch elseComments body) body.pieces :=
  match body with
    | { statements = [{ blankBefore, line = Bare value }] } =>
      match value with
        | If ifComments condition thenComments whenTrue innerElse whenFalse =>
          match g: elseComments.after.isNone && ifComments.above.isEmpty with
            | True =>
              writesTwo
                (Doc.text " ")
                (ifLayout ifComments condition thenComments whenTrue innerElse whenFalse)
                []
                (If ifComments condition thenComments whenTrue innerElse whenFalse).pieces
                writesSpace
                (ifWrites ifComments condition thenComments whenTrue innerElse whenFalse
                  (exprWrites condition)
                  (branchWrites thenComments whenTrue)
                  (elseBranchWrites innerElse whenFalse))
            | False => branchWrites elseComments { statements = [{ blankBefore, line = Bare value }] }
        | _ => branchWrites elseComments { statements = [{ blankBefore, line = Bare value }] }
    | { statements = [] } => branchWrites elseComments { statements = [] }
    | { statements = [{ blankBefore, line = Let letComments name nameComments equals inner }] } =>
      branchWrites elseComments {
        statements = [{ blankBefore, line = Let letComments name nameComments equals inner }]
      }
    | { statements = [{ blankBefore, line = StatementNote comment }] } =>
      branchWrites elseComments { statements = [{ blankBefore, line = StatementNote comment }] }
    | { statements = [{ blankBefore, line = Bare value }, second, ..rest] } =>
      match value with
        | If ifComments condition thenComments whenTrue innerElse whenFalse =>
          branchWrites elseComments { statements = [{ blankBefore, line = Bare value }, second, ..rest] }
        | _ => branchWrites elseComments { statements = [{ blankBefore, line = Bare value }, second, ..rest] }
    | { statements = [{ blankBefore, line = Let letComments name nameComments equals inner }, second, ..rest] } =>
      branchWrites elseComments {
        statements = [{ blankBefore, line = Let letComments name nameComments equals inner }, second, ..rest]
      }
    | { statements = [{ blankBefore, line = StatementNote comment }, second, ..rest] } =>
      branchWrites elseComments { statements = [{ blankBefore, line = StatementNote comment }, second, ..rest] }

theorem afterEqualsWrites ∀ (body: Body) (equals: Comments): Writes (body.afterEquals equals) body.pieces :=
  match body with
    | { statements = [{ blankBefore, line = Bare value }] } =>
      match g: equals.after.isNone with
        | True =>
          match value with
            | ListLiteral open items close =>
              writesChoiceTwo _ _ _
                (writesTwo _ _ [] _ writesSpace (writesFlatten _ _ (exprWrites (ListLiteral open items close))))
                (writesTwo _ _ [] _ writesSpace (exprWrites (ListLiteral open items close)))
            | _ =>
              writesChoiceThree _ _ _ _
                (writesTwo _ _ [] _ writesSpace (writesFlatten _ _ (exprWrites value)))
                (writesOneLineBelow _ _ (exprWrites value))
                (writesBelow _ _ (exprWrites value))
        | False => writesBelow _ _ (exprWrites value)
    | { statements = [] } => blockWrites []
    | { statements = [{ blankBefore, line = Let letComments name nameComments equals inner }] } =>
      blockWrites [{ blankBefore, line = Let letComments name nameComments equals inner }]
    | { statements = [{ blankBefore, line = StatementNote comment }] } =>
      blockWrites [{ blankBefore, line = StatementNote comment }]
    | { statements = [first, second, ..rest] } => blockWrites [first, second, ..rest]

theorem bindingWrites ∀ (letComments: Comments) (name: Text) (nameComments equals: Comments) (body: Body):
    Writes
      (binding letComments name nameComments equals body)
      (bindingPieces letComments name nameComments equals body.pieces) :=
  let afterName := tokenPieces equals "=" ++ body.pieces
  writesConcat _ _
    (writesCons _ _
      (tokenPieces letComments "let")
      (tokenPieces nameComments name ++ afterName)
      (writesToken letComments "let")
      (writesCons
        (Doc.text " ") _
        []
        (tokenPieces nameComments name ++ afterName)
        writesSpace
        (writesCons _ _
          (tokenPieces nameComments name)
          afterName
          (writesToken nameComments name)
          (writesCons
            (Doc.text " ") _
            []
            afterName
            writesSpace
            (writesCons _ _
              (tokenPieces equals "=")
              body.pieces
              (writesToken equals "=")
              (writesLast _ _ (afterEqualsWrites body equals)))))))

theorem parameterDocsWrite ∀ (parameters: List Parameter):
    WritesAll (parameterDocs parameters) (parameterPieces parameters) :=
  match parameters with
    | [] => writesNil
    | [{ name, comments, comma }] => writesLast _ _ (writesToken comments name)
    | [{ name, comments, comma }, next, ..rest] =>
      writesCons _ _
        (tokenPieces comments name ++ tokenPieces comma ",")
        (parameterPieces [next, ..rest])
        (writesTwo _ _ _ _ (writesToken comments name) (writesToken comma ","))
        (parameterDocsWrite [next, ..rest])

theorem headerWrites ∀ (fnComments: Comments) (name: Text) (nameComments open: Comments)
    (parameters: List Parameter) (close equals: Comments):
    Writes
      (header fnComments name nameComments open parameters close equals)
      (headerPieces fnComments name nameComments open parameters close equals) :=
  let openingPieces := tokenPieces fnComments "fn" ++ (tokenPieces nameComments name ++ tokenPieces open "(")
  let closingPieces := tokenPieces close ")" ++ tokenPieces equals "="
  let opening: Writes
    (Doc.concat [token fnComments "fn", Doc.text " ", token nameComments name, token open "("])
    openingPieces :=
    writesConcat _ _
      (writesCons _ _
        (tokenPieces fnComments "fn")
        (tokenPieces nameComments name ++ tokenPieces open "(")
        (writesToken fnComments "fn")
        (writesCons
          (Doc.text " ") _
          []
          (tokenPieces nameComments name ++ tokenPieces open "(")
          writesSpace
          (writesCons _ _
            (tokenPieces nameComments name)
            (tokenPieces open "(")
            (writesToken nameComments name)
            (writesLast _ _ (writesToken open "(")))))
  let closing: Writes (Doc.concat [closer close ")", Doc.text " ", token equals "="]) closingPieces :=
    writesConcat _ _
      (writesCons _ _
        (tokenPieces close ")")
        (tokenPieces equals "=")
        (writesCloser close ")")
        (writesCons (Doc.text " ") _ [] (tokenPieces equals "=") writesSpace (writesLast _ _ (writesToken equals "="))))
  match parameters with
    | [] => writesTwo _ _ openingPieces closingPieces opening closing
    | [first, ..others] =>
      writesGroup _ _
        (writesConcat _ _
          (writesCons _ _ openingPieces
            (parameterPieces [first, ..others] ++ closingPieces)
            opening
            (writesCons _ _
              (parameterPieces [first, ..others])
              closingPieces
              (writesNest 4 _ _
                (writesConcat
                  [SoftLine, parameterDocs [first, ..others] |> joined Line]
                  (parameterPieces [first, ..others])
                  (writesCons SoftLine _ []
                    (parameterPieces [first, ..others])
                    (Both rfl rfl)
                    (writesLast _ _ (writesJoined _ Line _ (Both rfl rfl) (parameterDocsWrite [first, ..others]))))))
              (writesCons SoftLine _ [] closingPieces (Both rfl rfl) (writesLast _ _ closing)))))

--| A declaration's document writes its tokens and comments in order.
theorem declarationWrites ∀ (declaration: Declaration): Writes declaration.layout declaration.pieces :=
  match declaration with
    | Function fnComments name nameComments open parameters close equals body =>
      writesTwo _ _ _ _
        (headerWrites fnComments name nameComments open parameters close equals)
        (afterEqualsWrites body equals)
    | Value letComments name nameComments equals body => bindingWrites letComments name nameComments equals body
    | DeclarationNote comment => writesText comment.text

theorem declarationLinesWrite ∀ (index: Nat) (declarations: List (Spaced Declaration)):
    WritesAll (declarationLines index declarations) (declarationPieces declarations) :=
  match declarations with
    | [] => writesNil
    | [{ blankBefore, line }, ..rest] =>
      writesCons _ _ line.pieces
        (declarationPieces rest)
        (writesTwo _ _ [] line.pieces (writesLineStart index blankBefore) (declarationWrites line))
        (declarationLinesWrite (index + 1) rest)

--| The document the rules build for a file writes the file's tokens and
--| comments, in the source's order, whichever option each choice takes.
theorem fileWrites ∀ (file: SourceFile): Writes file.layout file.pieces := match file with
  | { declarations = [] } => writesEmpty
  | { declarations = [first, ..rest] } =>
    rewrite <- List.appendNil (declarationPieces [first, ..rest]) in
      writesTwo _ HardLine
        (declarationPieces [first, ..rest])
        []
        (writesConcat _ _ (declarationLinesWrite 0 [first, ..rest]))
        (Both rfl rfl)

--| A file printed, at every width, is its tokens and comments in the
--| source's order with only layout (spaces, indentation, line breaks)
--| between and around them: the text is `printed` joined, and the pieces
--| of `printed` that aren't layout are those of the file. No token or
--| comment is lost, repeated or moved, and a trailing comment is written
--| before the token after it.
theorem printPieces ∀ (file: SourceFile) (width: Nat):
    ∃ (printed: List Text) => (file.print width).text = printed.joinWith "" ∧ wordsOf printed = wordsOf file.pieces :=
  match fileWrites file with
    | Both uniform words =>
      match printWords file.layout width uniform with
        | Witness printed (Both joins printedWords) => Witness printed (Both joins (Eq.trans printedWords words))
