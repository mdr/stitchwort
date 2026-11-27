--| The rules for the slices' constructs (docs/proposals/
--| self-hosted-fmt-proof-plan.md §1.2): how a declaration of the tidied
--| tree becomes a layout document (`Std.Doc`), ported from
--| `crates/fmt/src/printer/rules.rs` function by function for the parts
--| slice 1 meets: `decl` and `header` for `def name: T := e`, `body_after`,
--| `app` with `last_argument` and `fill_call`, `chain` for `Binary` and
--| `Arrow`, `paren`, `comma_bracket` for tuples and lists, and `join` for
--| `Prefix`, with `el`, `leaf`, `leading` and `trailing` for comments;
--| for slice 2's binders, `header` with `premises`, `lambda_both` and
--| `quantifier`; for slice 3's layout, `block`, `let_line`, `sequence`,
--| `if_`, `alternatives` and `arm`; for slice 4a, `join` for
--| `FieldAccess`; for slice 5a, `decl` for `test` and for a definition's
--| arms, `import` and `join` for `namespace`; for slice 4c,
--| `comma_bracket` with brace edges for records and record patterns, and
--| `join` for membership, spreads and a record's fields; for slice 6a,
--| `rewrite`, `comma_bracket` for `repeatedly`'s rules, `calc` and
--| `calc_step`, `chain` for `↔`, and `join` for facts and `cases then`.
--|
--| The Rust rules read a token's neighbours by its index in the file.
--| Here what a rule needs of a token's surroundings travels down the tree
--| as an `Around`: whether the code before it ends its line with a comment,
--| whether an enclosing element already printed its own-line comments,
--| whether it starts an item of a comma bracket, and the number of tokens
--| before it in the declaration, which gives each `IdGroup` and each
--| `Mark` a key of its own as the Rust token index does.
--|
--| A node outside the slices prints as nothing: the caller asks `within5a`
--| (or an earlier slice's test) first (`Fmt.Slice5a`).

namespace Fmt
import Std (Bool, Doc, List, Nat, Option, Text)
import Std.Doc (..)
import Syntax (
  Arm,
  BindingKind,
  Comments,
  DefKind,
  Expr,
  FieldPattern,
  FieldsPattern,
  Guard,
  Header,
  Imported,
  ImportItem,
  InfixKind,
  Let,
  Note,
  Param,
  Pattern,
  CalcStep,
  RewriteRule,
  Row,
  RuleSet,
  Rules,
  Scrutinee,
  Statement,
  Tok,
  Word
)

--| What a rule needs to know of where a token or element stands.
type Around = {
  --| The code before it, closers aside, ends its line with a comment
  --| (`ends_line_with_comment_before`).
  before: Bool,
  --| Its first token's own-line comments are printed by an enclosing
  --| element, or by the file for a declaration's first token (`hoisted`,
  --| `file_comments`).
  hoisted: Bool,
  --| It starts an item of a comma bracket, where an author's blank line
  --| above it is kept (`keep_blank`, E4).
  item: Bool,
  --| The tokens before it in the declaration, commas not counted.
  at: Nat,
  --| It is inside an alternative of a `match` (or is the `match` an
  --| operator continues), where a `match` with one arm puts it on a line
  --| of its own (`arm_depth`).
  inArm: Bool
}

--| A later child of an element, `skipped` tokens after the element's
--| first: none of the first token's facts carry to it.
def Around.next (around: Around) (before: Bool) (skipped: Nat): Around :=
  { before, hoisted = False, item = False, at = around.at + skipped, inArm = around.inArm }

--| A token with no comments: what a node outside the slice starts with.
def Word.none: Word := { text = "", comments = { above = [], after = None, blankBefore = False } }

--| A fixed token, held in the tree as its comments only.
def fixedWord (text: Text) (comments: Comments): Word := { text, comments }

def Word.trails (word: Word): Bool := word.comments.after.isSome

def Word.noted (word: Word): Bool := !word.comments.above.isEmpty

def isCloserText (text: Text): Bool := text == ")" || text == "]" || text == "}"

--| A token's text: a closer or comma is a `Closing`, which stays on its
--| line before a waiting trailing comment, as Rust's engine treats a text
--| of only closers and commas.
def piece (text: Text): Doc := if isCloserText text || text == "," then Closing text else Doc.text text

-- Tokens and their comments.

--| The comment after the token on its line (`trailing`).
def Word.trailing (word: Word): List Doc := match word.comments.after with
  | Some comment => [LineSuffix comment]
  | None => []

--| Own-line comments before a closer, at its items' indentation (S40).
def closerNotes: List Note → List Doc
  | [] => []
  | [note, ..rest] => (if note.blankBefore then [Blank] else []) ++ [Doc.text note.text] ++ laterCloserNotes rest

def laterCloserNotes: List Note → List Doc
  | [] => []
  | [note, ..rest] =>
    [HardLine] ++ (if note.blankBefore then [Blank] else []) ++ [Doc.text note.text] ++ laterCloserNotes rest

--| Own-line comments, each on its line, with the blank lines above them.
def notesAbove: List Note → List Doc
  | [] => []
  | [note, ..rest] => (if note.blankBefore then [Blank] else []) ++ [Doc.text note.text, HardLine] ++ notesAbove rest

--| Own-line comments and kept blank lines before a token (`leading`).
--| `key` is its bracket pair's, for a closer. An item's blank line with
--| no comments above breaks the separator before it (`BreakParent`), so
--| its `LineStart` writes nothing; it is there for `Lays`, which doesn't
--| follow modes and would otherwise lay the separator as a space too,
--| with no blank line (`Doc.Proofs.blankAfterLineExample`).
def Word.leading (word: Word) (around: Around) (key: Nat): List Doc :=
  let comments := word.comments
  if around.hoisted then []
  else if comments.above.isEmpty then
    (if around.item && comments.blankBefore then [BreakParent, LineStart, Blank] else [])
  else if isCloserText word.text then
    [BreakParent, Nest 2 (Doc.concat [LineStartHere, ..closerNotes comments.above]), CloserLine key]
  else [BreakParent, LineStart, ..notesAbove comments.above] ++ (if comments.blankBefore then [Blank] else [])

--| A token on its own (`leaf`). A closer after code that ends its line
--| with a comment, and with a comment of its own, keeps a line of its own
--| (S39): printed before the waiting comment, it would leave two comments
--| on one line. That line is left of the lines inside its brackets, as
--| after own-line comments: at the indentation in force, which a
--| declaration's type shares with its contents, the closer would read as
--| their block's next line (SW-3962).
def Word.leaf (word: Word) (around: Around) (key: Nat): Doc :=
  let ownLine := isCloserText word.text && !word.noted && around.before && word.trails
  Doc.concat
    (word.leading around key ++ (if ownLine then [CloserLine key] else []) ++ [piece word.text] ++ word.trailing)

--| An opening bracket: with a `Mark` when its closer may take a line of
--| its own (own-line comments before it, or a comment after it), which
--| may then go back to this line's indentation.
def Word.opening (word: Word) (around: Around) (closer: Word): Doc :=
  let mark := if closer.noted || closer.trails then [Mark around.at] else []
  Doc.concat (word.leading around around.at ++ mark ++ [piece word.text] ++ word.trailing)

-- What rules read of an expression's tokens.

--| The expression's tokens in order, commas left out.
def Expr.words: Expr → List Word
  | Atom _ word => [word]
  | Paren open inner close => [open, ..inner.words] ++ [close]
  | Tuple open items _ close | ListOf open items _ close => [open, ..itemsWords items] ++ [close]
  | App head arguments => head.words ++ itemsWords arguments
  | Infix _ left operator right => left.words ++ [operator, ..right.words]
  | Prefix operator operand => [operator, ..operand.words]
  | Binding _ keyword params arrow body => optionWords keyword ++ paramsWords params ++ [arrow, ..body.words]
  | Effect row result => rowWords row ++ result.words
  | If keyword _ condition thenKeyword whenTrue elseKeyword whenFalse =>
    [keyword, ..condition.words] ++ [thenKeyword, ..whenTrue.words] ++ [elseKeyword, ..whenFalse.words]
  | Match keyword scrutinees withKeyword arms =>
    [keyword, ..scrutineesWords scrutinees] ++ [withKeyword, ..armsWords arms]
  | Block first rest result => first.words ++ statementsWords rest ++ result.words
  | LetIn binding semicolon body => letWords binding ++ [fixedWord ";" semicolon, ..body.words]
  | FieldAccess (Some target) dot field => target.words ++ [dot, field]
  | NamedArg open name colonEq value close => [open, name, colonEq, ..value.words] ++ [close]
  | Annotation open value colon annotation close => [open, ..value.words] ++ [colon, ..annotation.words] ++ [close]
  | Spread dots list => [dots, ..list.words]
  | Record open base fields _ close => [open, ..baseWords base] ++ itemsWords fields ++ [close]
  | RecordField name equals value => [name, equals, ..value.words]
  | CtorFields ctor record => ctor.words ++ record.words
  | Rewrite keyword rules target body =>
    [fixedWord "rewrite" keyword, ..rules.words] ++ afterWords "at" target ++ afterWords "then" body
  | Facts _ keyword facts => [keyword, ..facts.words]
  | Cases keyword targets body => [fixedWord "cases" keyword, ..targets] ++ afterWords "then" body
  | Walk keyword items body => [fixedWord "byWalking" keyword, ..items.words] ++ afterWords "then" body
  | Calc keyword first steps => [fixedWord "calc" keyword, ..first.words] ++ stepsWords steps
  | _ => []

--| An update's record and its `|`.
def baseWords: Option (Expr, Word) → List Word
  | Some (record, bar) => record.words ++ [bar]
  | None => []

def scrutineesWords: List Scrutinee → List Word
  | [] => []
  | [{ value, .. }, ..rest] => value.words ++ scrutineesWords rest

def armsWords: List Arm → List Word
  | [] => []
  | [arm, ..rest] => arm.words ++ armsWords rest

--| An arm's tokens: `|`, the patterns', the guard's, `=>`, the body's.
def Arm.words (arm: Arm): List Word := match arm with
  | { bar, patterns, guard, body } => [bar, ..patternsWords patterns] ++ guardWords guard ++ armBodyWords body

def guardWords: Option Guard → List Word
  | Some { keyword, condition, .. } => [keyword, ..condition.words]
  | None => []

def armBodyWords: Option (Word, Expr) → List Word
  | Some (arrow, body) => [arrow, ..body.words]
  | None => []

def Pattern.words: Pattern → List Word
  | PatternWord _ word => [word]
  | PatternCtor name arguments => [name, ..patternsWords arguments]
  | PatternParen open inner close => [open, ..inner.words] ++ [close]
  | PatternTuple open items _ close => [open, ..patternsWords items] ++ [close]
  | PatternList open items _ tail close => [open, ..patternsWords items] ++ tailWords tail ++ [close]
  | PatternAbsurd open close => [open, close]
  | PatternRecord fields => fields.words
  | PatternCtorFields name fields => [name, ..fields.words]
  | _ => []

--| A record pattern's tokens: `{`, the fields', `..`, `}`.
def FieldsPattern.words (fields: FieldsPattern): List Word := match fields with
  | { open, fields, rest, close, .. } => [open, ..fieldPatternsWords fields] ++ optionWords rest ++ [close]

def fieldPatternsWords: List FieldPattern → List Word
  | [] => []
  | [field, ..rest] => field.words ++ fieldPatternsWords rest

--| `x`, or `x`, `=` and the pattern's.
def FieldPattern.words (field: FieldPattern): List Word := match field with
  | { name, value = Some (equals, pattern) } => [name, equals, ..pattern.words]
  | { name, value = None } => [name]

--| A list pattern's `..rest`.
def tailWords: Option (Word, Pattern) → List Word
  | Some (dots, rest) => [dots, ..rest.words]
  | None => []

def patternsWords: List Pattern → List Word
  | [] => []
  | [pattern, ..rest] => pattern.words ++ patternsWords rest

def Statement.words: Statement → List Word
  | LetStatement binding => letWords binding
  | ExprStatement value => value.words
  | _ => []

def statementsWords: List Statement → List Word
  | [] => []
  | [statement, ..rest] => statement.words ++ statementsWords rest

--| A `let`'s tokens: `let`, the pattern's, `:` and the type's, `:=`, the
--| value's.
def letWords (binding: Let): List Word := match binding with
  | { keyword, pattern, annotation, colonEq, value } =>
    [fixedWord "let" keyword, ..pattern.words] ++ annotationWords annotation ++ [fixedWord ":=" colonEq, ..value.words]

def annotationWords: Option (Comments, Expr) → List Word
  | Some (colon, annotation) => [fixedWord ":" colon, ..annotation.words]
  | None => []

def itemsWords: List Expr → List Word
  | [] => []
  | [item, ..rest] => item.words ++ itemsWords rest

def optionWords: Option Word → List Word
  | Some word => [word]
  | None => []

def paramsWords: List Param → List Word
  | [] => []
  | [NameParam word, ..rest] | [PatternParam (PatternWord _ word), ..rest] => [word, ..paramsWords rest]
  | [Grouped group, ..rest] => groupWords group ++ paramsWords rest
  | [_, ..rest] => paramsWords rest

--| A group's brackets, as tokens.
def groupOpen (group: Syntax.Group): Word := fixedWord (if group.implicit then "[" else "(") group.open

def groupClose (group: Syntax.Group): Word := fixedWord (if group.implicit then "]" else ")") group.close

def groupColon (group: Syntax.Group): Word := fixedWord ":" (group.colon.getOrElse Comments.none)

--| A parameter group's tokens: `(`, the names, `:`, the type's, `)`.
def groupWords (group: Syntax.Group): List Word := match group with
  | { annotation = Some annotation, .. } =>
    [groupOpen group, ..group.names] ++ [groupColon group, ..annotation.words] ++ [groupClose group]
  | { annotation = None, .. } => [groupOpen group, ..group.names] ++ [groupClose group]

def groupsWords: List Syntax.Group → List Word
  | [] => []
  | [group, ..rest] => groupWords group ++ groupsWords rest

--| An ability row's tokens: `{`, the abilities, `}`.
def rowWords (row: Row): List Word := match row with
  | { open, abilities, variable, close } =>
    [fixedWord "{" open, ..itemsWords abilities]
      ++ (match variable with
        | Some (bar, name) => [fixedWord "|" bar, name]
        | None => [])
      ++ [fixedWord "}" close]

def Expr.size (expr: Expr): Nat := expr.words.length

def Expr.firstWord (expr: Expr): Word := expr.words.headOr Word.none

--| Whether a comment ends the element's line: on its last token, or on a
--| closer after it (`ends_with_comment`, `comment_at_end`).
def Expr.trails (expr: Expr): Bool := trailsBack expr.words.reverse

def trailsBack: List Word → Bool
  | [] => False
  | [word, ..rest] => word.trails || (isCloserText word.text && trailsBack rest)

--| Whether a comment ends a line inside the element, with code after it
--| (`holds_trailing_comment`): any trailing comment but the one ending its
--| line.
def Expr.holdsTrailingComment (expr: Expr): Bool :=
  let count := expr.words.filter Word.trails |> .length
  count > (if expr.trails then 1 else 0)

--| Whether own-line comments come before the element (`has_leading`).
def Expr.noted (expr: Expr): Bool := expr.firstWord.noted

-- Elements.

--| An element (`el`): a token as a leaf; a node by its rule (`node`),
--| given the node's parts so every call goes to a smaller tree.
def Expr.el (expr: Expr) (around: Around): Doc :=
  let inside := { around | hoisted = True }
  match expr with
    | Atom _ word => word.leaf around around.at
    | Paren open inner close => expr.framed around (parenDoc open inner close inside)
    | Tuple open items _ close => expr.framed around (commaBracket (list := False) open items close inside)
    | ListOf open items _ close => expr.framed around (commaBracket (list := True) open items close inside)
    | App head arguments => expr.framed around (appDocs head arguments inside).doc
    | Infix InfixBinary left operator right | Infix InfixArrow left operator right =>
      expr.framed around (chain expr.chainLevel left operator right inside)
    | Prefix operator operand =>
      expr.framed around
        (Doc.concat [
          operator.leaf inside around.at,
          prefixGap operator operand,
          operand.el (around.next operator.trails 1)
        ])
    | Binding BindsLambda keyword params arrow body =>
      let start := match keyword with
        | Some word => around.next word.trails 1
        | None => inside
      let (flat, _) := lambdaBoth params arrow body False start
      let keywordDoc := match keyword with
        | Some word => [word.leaf around around.at, Doc.text " "]
        | None => []
      expr.framed around (Doc.concat (keywordDoc ++ [flat]))
    | Binding BindsForall (Some keyword) params arrow body =>
      expr.framed around (quantifier (existential := False) keyword params arrow body inside)
    | Binding BindsExists (Some keyword) params arrow body =>
      expr.framed around (quantifier (existential := True) keyword params arrow body inside)
    | Effect row result => expr.framed around (effectDoc row result inside)
    | Block first rest result => expr.framed around (blockDoc first rest result inside)
    | LetIn binding semicolon body => expr.framed around (letInDoc binding semicolon body inside)
    | If keyword None condition thenKeyword whenTrue elseKeyword whenFalse =>
      expr.framed around (Doc.group (ifDoc keyword condition thenKeyword whenTrue elseKeyword whenFalse inside))
    | Match keyword scrutinees withKeyword arms =>
      expr.framed around (matchParts keyword scrutinees withKeyword arms inside).doc
    | FieldAccess (Some target) dot field =>
      let size := target.size
      expr.framed around
        (Doc.concat [
          target.el inside,
          dot.leaf (around.next target.trails size) (around.at + size),
          field.leaf (around.next False (size + 1)) (around.at + size + 1)
        ])
    | NamedArg open name colonEq value close => expr.framed around (namedArgDoc open name colonEq value close inside)
    | Annotation open value colon annotation close =>
      expr.framed around (annotationDoc open value colon annotation close inside)
    | Infix InfixMembership left operator right => expr.framed around (membershipDoc left operator right inside)
    | Spread dots list =>
      expr.framed around (Doc.concat [dots.leaf inside around.at, list.el (around.next dots.trails 1)])
    | Record open base fields _ close => expr.framed around (Doc.group (recordContent open base fields close inside))
    | RecordField name equals value => expr.framed around (recordFieldDoc name equals value inside)
    | CtorFields ctor record =>
      expr.framed around (Doc.concat [ctor.el inside, Doc.text " ", record.el (around.next ctor.trails ctor.size)])
    | Infix InfixIff left operator right => expr.framed around (chain None left operator right inside)
    | Rewrite keyword rules target body => expr.framed around (rewriteDoc keyword rules target body inside)
    | Facts _ keyword facts =>
      expr.framed around
        (Doc.concat [keyword.leaf inside around.at, Doc.text " ", facts.el (around.next keyword.trails 1)])
    | Calc keyword first steps => expr.framed around (calcDoc keyword first steps inside)
    | Cases keyword targets body =>
      let casesWord := fixedWord "cases" keyword
      expr.framed around (Doc.concat [casesWord.leaf inside around.at, ..casesRest around casesWord targets body])
    | Walk keyword items body =>
      let walkWord := fixedWord "byWalking" keyword
      expr.framed around
        (Doc.concat [
          walkWord.leaf inside around.at,
          Doc.text " ",
          items.el (around.next walkWord.trails 1),
          ..walkThenDocs body (around.next items.trails (1 + items.size))
        ])
    | _ => Nothing

--| What follows the word `last` of a `cases`, which stands at `around`: the names to split after it, a comma after
--| each but the last, then the `then` and body if there (`join`).
def casesRest (around: Around) (last: Word) (targets: List Word) (body: Option (Comments, Expr)): List Doc :=
  let next := around.next last.trails 1
  match targets with
    | [] => walkThenDocs body next
    | [word] => [Doc.text " ", word.leaf next next.at, ..casesRest next word [] body]
    | [word, ..rest] => [Doc.text " ", word.leaf next next.at, Closing ",", ..casesRest next word rest body]

--| A walk's `then` and body, if there, after its items (`join`); `around` is where the `then` stands.
def walkThenDocs (body: Option (Comments, Expr)) (around: Around): List Doc := match body with
  | Some (comments, value) =>
    let thenWord := fixedWord "then" comments
    [Doc.text " ", thenWord.leaf around around.at, value.after (around.next thenWord.trails 1)]
  | None => []

--| A node's document with its first token's own-line comments before it,
--| displaced as `Word.displaces` says.
def Expr.framed (expr: Expr) (around: Around) (doc: Doc): Doc := framedBy expr.firstWord around doc

--| Whether a node starting with `first` is displaced: its first line is
--| put below where its construct would by own-line comments above it, by
--| a blank line kept before it as an item (both start a line, at a column
--| that may be right of the indentation), or by a comment waiting before it.
--| Printed, a kept blank line always follows a line break, where
--| `Displaced` lays at the indentation as the node alone does.
def Word.displaces (first: Word) (around: Around): Bool :=
  first.noted || (around.item && first.comments.blankBefore) || around.before

def framedBy (first: Word) (around: Around) (doc: Doc): Doc :=
  let placed := if first.displaces around then Displaced doc else doc
  Doc.concat [Doc.concat (first.leading around around.at), placed]

-- Binders.

--| A parameter of a lambda or quantifier: a name, `_`, or a group.
def Param.el (param: Param) (around: Around): Doc := match param with
  | NameParam word | PatternParam (PatternWord _ word) => word.leaf around around.at
  | Grouped group => groupDoc group around
  | _ => Nothing

--| The docs of parameters, each standing after the one before it.
def paramDocs (around: Around): List Param → List Doc
  | [] => []
  | [param, ..rest] =>
    let words := paramsWords [param]
    [param.el around, ..paramDocs (around.next (trailsBack words.reverse) words.length) rest]

--| A parameter group (Rust's `Param` or `LambdaParam`, printed by `join`):
--| `(x y: A)` or `[a: Type]`, nothing inside the brackets, `:` against the
--| last name.
def groupDoc (group: Syntax.Group) (around: Around): Doc := match group with
  | { annotation = Some annotation, names, .. } =>
    let open := groupOpen group
    let close := groupClose group
    let colon := groupColon group
    let count := names.length
    let lastName := names.reverse.headOr open
    let doc := Doc.concat [
      open.opening { around | hoisted = True } close,
      spaced (nameDocs around.inArm open.trails (around.at + 1) names),
      colon.leaf (around.next lastName.trails (1 + count)) (around.at + 1 + count),
      Doc.text " ",
      annotation.el (around.next colon.trails (2 + count)),
      close.leaf (around.next annotation.trails (2 + count + annotation.size)) around.at
    ]
    framedBy open around doc
  | _ => Nothing

def nameDocs (arm before: Bool) (at: Nat): List Word → List Doc
  | [] => []
  | [name, ..rest] =>
    [name.leaf { before, hoisted = False, item = False, at, inArm = arm } at, ..nameDocs arm name.trails (at + 1) rest]

def paramTrails (param: Param): Bool := trailsBack (paramsWords [param]).reverse

def paramNoted (param: Param): Bool := (paramsWords [param]).headOr Word.none |> .noted

--| A lambda (`lambda_both`, S30), and the same lambda opened downwards for
--| a hug or the `:=` line (S23, D3568): the body after `=>` if it fits,
--| else below at 2. Only the first breaks its parameters, filling lines
--| at 4 like a header's (S22), when no comment sits among them. A lambda
--| just before a `;` (`semi`, an expression `let`'s value) keeps its body
--| after `=>`: a body starting a line would be a block, which the `;`
--| would end.
def lambdaBoth (params: List Param) (arrow: Word) (body: Expr) (semi: Bool) (around: Around): (Doc, Doc) :=
  let docs := paramDocs around params
  let words := paramsWords params
  let size := words.length
  let arrowDoc := arrow.leaf (around.next (trailsBack words.reverse) size) (around.at + size)
  let bodyDoc := body.el (around.next arrow.trails (size + 1))
  let items := docs ++ [arrowDoc]
  let head := spaced items
  let commented := (params.drop 1 |> .any paramNoted) || params.any paramTrails || arrow.noted
  let filled := if params.length < 2 || commented then head else Nest 4 (Fill items)
  if semi then
    let doc := Doc.concat [head, Doc.text " ", bodyDoc]
    (doc, doc)
  else
    (
      Doc.group (Doc.concat [filled, Nest 2 (Doc.concat [Line, bodyDoc])]),
      Doc.concat [head, Nest 2 (Doc.concat [HardLine, bodyDoc])]
    )

--| `∀ binders => body` and `∃ binders => body` (`quantifier`, S28): the
--| body after `=>` if it fits, else breaking from there, else below at 2.
--| An `∃`'s binders never break.
def quantifier (existential: Bool) (keyword: Word) (params: List Param) (arrow: Word) (body: Expr) (around: Around):
    Doc :=
  let words := paramsWords params
  let size := words.length
  let docs := paramDocs (around.next keyword.trails 1) params
  let arrowDoc := arrow.leaf (around.next (trailsBack (words.reverse ++ [keyword])) (1 + size)) (around.at + 1 + size)
  let bodyDoc := body.el (around.next arrow.trails (2 + size))
  let joined := spaced ([keyword.leaf around around.at, ..docs] ++ [arrowDoc])
  let head := if existential then Flatten joined else joined
  let below := Doc.concat [head, Nest 2 (Doc.concat [HardLine, bodyDoc])]
  if body.noted then below
  else
    let inline := Doc.concat [head, Doc.text " ", bodyDoc]
    Choice [Flatten inline, inline, below]

--| `{A, B} T` (Rust's `Effect` and `Row`, printed by `join`): nothing
--| inside the row's braces (D1037), a space after each comma and before
--| the type.
def effectDoc (row: Row) (result: Expr) (around: Around): Doc := match row with
  | { open, abilities, variable = None, close } =>
    let openWord := fixedWord "{" open
    let closeWord := fixedWord "}" close
    let size := (rowWords row).length
    let rowDoc :=
      Doc.concat
        ([openWord.opening around closeWord]
          ++ rowItems around.inArm openWord.trails (around.at + 1) abilities
          ++ [closeWord.leaf (around.next (trailsBack ((rowWords row).reverse.drop 1)) (size - 1)) around.at])
    Doc.concat [framedBy openWord around rowDoc, Doc.text " ", result.el (around.next closeWord.trails size)]
  | _ => Nothing

--| A row's abilities, a comma and a space between each two.
def rowItems (arm before: Bool) (at: Nat): List Expr → List Doc
  | [] => []
  | [item] => [item.el { before, hoisted = False, item = False, at, inArm = arm }]
  | [item, ..rest] => [
    item.el { before, hoisted = False, item = False, at, inArm = arm },
    Closing ",",
    Doc.text " ",
    ..rowItems arm item.trails (at + item.size) rest
  ]

--| `( … )` (`paren`): nothing between the brackets and what they hold. A
--| bracketed `if` keeps its `else` lines under the `if` (S19); a block opens
--| below the bracket at 2 (S17), since its lines go at the indentation in
--| force and after the bracket would sit left of its first.
def parenDoc (open: Word) (inner: Expr) (close: Word) (around: Around): Doc := Doc.concat [
  open.opening around close,
  parenInner inner (around.next open.trails 1),
  close.leaf (around.next inner.trails (1 + inner.size)) around.at
]

--| What stands between a `paren`'s brackets, `inner` standing where `innerAround` says.
def parenInner (inner: Expr) (innerAround: Around): Doc := match inner with
  | Block _ _ _ => Nest 2 (Doc.concat [HardLine, inner.el innerAround])
  | If _ _ _ _ _ _ _ => Align (inner.el innerAround)
  | _ => inner.el innerAround

-- Comma brackets.

--| A tuple or list (`comma_bracket`): flat if it fits, else broken.
def commaBracket (list: Bool) (open: Word) (items: List Expr) (close: Word) (around: Around): Doc :=
  Doc.group (bracketContent list open items close around)

--| Where an item stands: after the opener (`before` says whether that
--| ends its line with a comment), then after a comma.
def itemAround (arm before: Bool) (at: Nat): Around := { before, hoisted = False, item = True, at, inArm = arm }

--| Where a list's first item stands: `bare` (a list of only plain values)
--| makes it no item for blank lines, as its blank line would write nothing
--| mid-line when the list fills, yet still break the groups around it
--| (SW-3963).
def firstAround (bare arm before: Bool) (at: Nat): Around := { itemAround arm before at | item = !bare }

--| A plain value of a list that fills its lines (D3572).
def Expr.plainItem: Expr → Bool
  | Atom kind word =>
    !word.noted && (kind == Lower || kind == Num || kind == Float || kind == Str || kind == CharLit || kind == Upper)
  | _ => False

--| The parts of a tuple or list, not yet grouped (`comma_bracket_content`):
--| a list of only plain values fills its lines, the bracket staying on the
--| first (D3572); otherwise each item is on a line of its own at 2 when
--| broken. The last item has no comma after it (P2).
def bracketContent (list: Bool) (open: Word) (items: List Expr) (close: Word) (around: Around): Doc :=
  let whole := ListOf open items False close
  let closeAround := around.next whole.trailsBeforeClose (whole.size - 1)
  let closer := close.leaf closeAround around.at
  let prefix := open.opening around close
  let bare := list && items.all Expr.plainItem
  if items.isEmpty then Doc.concat [prefix, closer]
  else if list && !whole.holdsTrailingComment && items.all Expr.plainItem then
    Doc.concat [prefix, Nest 2 (Fill (cells bare around.inArm open.trails (around.at + 1) items)), closer]
  else
    let parts := [
      prefix,
      Nest 2 (Doc.concat (brokenItems bare around.inArm True open.trails (around.at + 1) items)),
      SoftLine,
      closer
    ]
    Doc.concat (if whole.holdsTrailingComment then parts ++ [BreakParent] else parts)

--| Whether the code before a bracket's closer, closers aside, ends its line
--| with a comment: what its last item ends with.
def Expr.trailsBeforeClose (expr: Expr): Bool := trailsBack (expr.words.reverse.drop 1)

--| A filled list's cells: each item with its comma. Each later cell stands after the item before it, as `brokenItems`
--| do (a filled list holds no comment before more code, so that item's trails are False).
def cells (bare arm before: Bool) (at: Nat): List Expr → List Doc
  | [] => []
  | [item] => [item.el (firstAround bare arm before at)]
  | [item, ..rest] => [
    Doc.concat [item.el (firstAround bare arm before at), Closing ","],
    ..cells False arm item.trails (at + item.size) rest
  ]

--| A broken bracket's items: each starts a line, with its comma after it.
def brokenItems (bare arm first before: Bool) (at: Nat): List Expr → List Doc
  | [] => []
  | [item] => [if first then SoftLine else Line, item.el (firstAround bare arm before at)]
  | [item, ..rest] => [
    if first then SoftLine else Line,
    item.el (firstAround bare arm before at),
    Closing ",",
    ..brokenItems False arm False item.trails (at + item.size) rest
  ]

-- Calls.

def optionList (option: Option Doc): List Doc := match option with
  | Some doc => [doc]
  | None => []

--| A call's document, and its hug if its last argument can hug (S23).
type Applied = { doc: Doc, hug: Option Doc }

--| A call's last argument and its hug, the same argument opening
--| downwards (`last_argument`): a tuple, a list, or a lambda or block in
--| brackets can hug.
def lastArgument (argument: Expr) (around: Around): (Doc, Option Doc) := match argument with
  | Tuple open items _ close => huggedBracket False open items close around
  | ListOf open items _ close => huggedBracket True open items close around
  | Paren open (Binding BindsLambda _ params arrow body) close => huggedLambda open params arrow body close around
  | Paren open (Block first rest result) close => huggedBlock open first rest result close around
  | Record open base fields _ close => huggedRecord open base fields close around
  | _ => (argument.el around, None)

--| `(x => body)` as a last argument: the lambda as it is, and opened,
--| its body below at 2.
def huggedLambda (open: Word) (params: List Param) (arrow: Word) (body: Expr) (close: Word) (around: Around):
    (Doc, Option Doc) :=
  let lambda := Binding BindsLambda None params arrow body
  let openDoc := open.opening { around | hoisted = True } close
  let closeDoc := close.leaf (around.next lambda.trails (1 + lambda.size)) around.at
  let (flat, opened) := lambdaBoth params arrow body False (around.next open.trails 1)
  (
    framedBy open around (Doc.concat [openDoc, flat, closeDoc]),
    Some (framedBy open around (Doc.concat [openDoc, opened, closeDoc]))
  )

--| `( block )` as a last argument: the block below the bracket at 2, the
--| same as it is and opened.
def huggedBlock (open: Word) (first: Statement) (rest: List Statement) (result: Expr) (close: Word) (around: Around):
    (Doc, Option Doc) :=
  let block := Block first rest result
  let inner := around.next open.trails 1
  let doc :=
    framedBy open around
      (Doc.concat [
        open.opening { around | hoisted = True } close,
        Nest 2 (Doc.concat [HardLine, block.framed inner (blockDoc first rest result { inner | hoisted = True })]),
        close.leaf (around.next block.trails (1 + block.size)) around.at
      ])
  (doc, Some doc)

--| A tuple or list as a last argument: as it is, and opened. Framed as any node is, so a comment
--| that puts the bracket on a line of its own lays its items under it and its closer at its column.
def huggedBracket (list: Bool) (open: Word) (items: List Expr) (close: Word) (around: Around): (Doc, Option Doc) :=
  let content := bracketContent list open items close { around | hoisted = True }
  (framedBy open around (Group content content.forcesBreak), Some (framedBy open around (Group content True)))

--| Whether an argument may stay on the call's line when the others go
--| below (`simple`): a token, `[]`, a prefix operator on a token, or a
--| field of one of those (`x.f.g`).
def Expr.simple: Expr → Bool
  | Atom _ _ => True
  | FieldAccess (Some target) _ _ => target.simple
  | Tuple _ items _ _ | ListOf _ items _ _ => items.isEmpty
  | Prefix _ (Atom _ _) => True
  | _ => False

--| How many of the call's elements stay on its line when it breaks: the
--| function and the simple arguments right after it, up to one after a
--| comment (`keep`).
def keptFront (previous: Expr): List Expr → Nat
  | [] => 0
  | [argument, ..rest] => if argument.simple && !previous.trails then 1 + keptFront argument rest else 0

--| Whether a comment sits between the elements (`comment_between`).
def commentBetween (previous: Expr): List Expr → Bool
  | [] => False
  | [next, ..rest] => next.noted || previous.trails || commentBetween next rest

--| Docs on one line, a space between each two: between a call's elements
--| every gap in slice 1 is a space (`f (x)` included, D1039).
def spaced (docs: List Doc): Doc := Doc.joined docs (Doc.text " ")

--| The docs of all but the last argument, and the last's with its hug.
--| Each argument stands after the element before it.
def argumentDocs (arm: Bool) (previous: Expr) (at: Nat): List Expr → (List Doc, Option (Doc, Option Doc))
  | [] => ([], None)
  | [argument] =>
    ([], Some (lastArgument argument { before = previous.trails, hoisted = False, item = False, at, inArm = arm }))
  | [argument, ..rest] =>
    let (docs, last) := argumentDocs arm argument (at + argument.size) rest
    ([argument.el { before = previous.trails, hoisted = False, item = False, at, inArm = arm }, ..docs], last)

--| A call (`app`, S23, D3567 (c)): on one line if it fits; else hugging its
--| last argument if that can and the line up to it fits; else the function
--| and its leading simple arguments on the line and each other argument on
--| its own line at 2. Plain arguments only (all simple) fill lines at 4
--| (D3569). The `IdGroup` of a filled front is keyed by the call's first
--| token, which no other call in the declaration starts with.
def appDocs (head: Expr) (arguments: List Expr) (around: Around): Applied :=
  let headDoc := head.el around
  let (front, last) := argumentDocs around.inArm head (around.at + head.size) arguments
  let (lastDoc, hug) := last.getOrElse (Nothing, None)
  let keep := 1 + keptFront head arguments
  appFrom
    (around.at + 1)
    keep
    (commentBetween head arguments)
    (commentBetween head (arguments.take (keep - 1)))
    headDoc
    front
    lastDoc
    hug

--| `appDocs` from what it reads of the call's elements: `keep` of them stay on its line when it breaks, a comment
--| sits between the elements (`between`) or between those kept (`betweenFront`), and the documents of the function,
--| the arguments before the last, the last, and the last's hug. `id` keys the filled front's `IdGroup`.
def appFrom (id keep: Nat) (between betweenFront: Bool) (headDoc: Doc) (front: List Doc)
    (lastDoc: Doc) (hug: Option Doc):
    Applied :=
  let docs := [headDoc, ..front] ++ [lastDoc]
  let all := spaced docs
  if keep == docs.length then { doc = if between then all else Nest 4 (Fill docs), hug = None }
  else
    let hugged := hug.map (open => Doc.concat [Flatten (spaced [headDoc, ..front]), Doc.text " ", open])
    let fillFront := keep > 2 && !betweenFront
    let kept := docs.take keep
    let frontDoc := if fillFront then IdGroup id (Nest 4 (Fill kept)) False else spaced kept
    let rest := Doc.concat (docs.drop keep |> .concatMap (doc => [HardLine, doc]))
    let restDoc := if fillFront then IfBroken id (Nest 4 rest) (Nest 2 rest) else Nest 2 rest
    let options := [Flatten all] ++ optionList hugged ++ [Doc.concat [frontDoc, restDoc]]
    { doc = Choice options, hug = hugged }

-- Operator chains.

--| A token's level among the operators that chain (`level`, S27): a broken
--| chain puts each operator of its level at the start of a line.
def Tok.chainLevel: Tok → Option Nat
  | IffArrow => Some 0
  | Arrow => Some 1
  | OrOr => Some 2
  | AndAnd => Some 3
  | Equals | EqEq | NotEq | Lt | Le | Gt | Ge => Some 4
  | PlusPlus => Some 5
  | Plus | Minus => Some 6
  | Star | Slash | Percent => Some 7
  | PipeGt => Some 8
  | _ => None

--| An operator's level, by its spelling.
def operatorLevel (operator: Word): Option Nat := Option.flatMap (operatorTok operator.text) Tok.chainLevel

--| A chain node's operator level, for `Binary` and `Arrow`.
def Expr.chainLevel: Expr → Option Nat
  | Infix InfixBinary _ operator _ | Infix InfixArrow _ operator _ => operatorLevel operator
  | _ => None

--| Whether a node is part of the chain at `level`: a `Binary` or `Arrow`
--| of that level (`chain_parts`).
def Expr.inChain (expr: Expr) (level: Option Nat): Bool := match expr with
  | Infix InfixBinary _ _ _ | Infix InfixArrow _ _ _ => level.isSome && expr.chainLevel == level
  | _ => False

--| An operator chain (`chain`, S27, S29): on one line if it fits,
--| otherwise each operator of its level starting a line at 2. The nested
--| chains of the same level are flattened into this one (`chain_parts`):
--| the first operand is the head, each operator and operand after it a
--| line of the tail.
--|
--| A chain whose first operand is a `match` is always broken, its arms on
--| lines of their own (SW-3680), and its operators stay at the chain's
--| column, where they can't read as part of the last arm.
def chain (level: Option Nat) (left: Expr) (operator: Word) (right: Expr) (around: Around): Doc :=
  chainOf (left.opensArms level) (chainLinks level True left operator right around)

--| A chain's docs, the first operand's and then the lines: grouped, the lines indented 2 unless the chain's
--| operators stay at its column (`arms`).
def chainOf (arms: Bool) (links: List Doc): Doc := match links with
  | [head, ..tail] => Doc.group (Doc.concat [head, Nest (if arms then 0 else 2) (Doc.concat tail)])
  | [] => Nothing

--| Whether the chain's first operand is a `match`.
def Expr.opensArms (expr: Expr) (level: Option Nat): Bool := match expr with
  | Match _ _ _ _ => True
  | Infix InfixBinary left _ _ | Infix InfixArrow left _ _ => expr.inChain level && left.opensArms level
  | _ => False

--| The flattened chain's docs: the first operand's, then for each operator
--| a `Line`, the operator, a space and its operand; a block operand starts
--| a line of its own below its operator. `first` says `left` starts the
--| chain.
def chainLinks (level: Option Nat) (first: Bool) (left: Expr) (operator: Word) (right: Expr) (around: Around):
    List Doc :=
  let operatorAround := around.next left.trails left.size
  let rightAround := around.next operator.trails (left.size + 1)
  linkDocs level first left around
    ++ [Line, operator.leaf operatorAround operatorAround.at, ..chainRight level right rightAround]

--| What follows a chain's operator: a block on a line of its own below it, else a space and the operand.
def chainRight (level: Option Nat) (right: Expr) (rightAround: Around): List Doc := match right with
  | Block _ _ _ => [Nest 2 (Doc.concat [HardLine, right.el rightAround])]
  | _ => [Doc.text " ", ..linkDocs level False right rightAround]

--| An operand of the chain: its docs if it is a chain of the same level,
--| else the element. A `match` that starts the chain is inside an arm for
--| its own arms' sake (`arm_depth`).
def linkDocs (level: Option Nat) (first: Bool) (expr: Expr) (around: Around): List Doc := match expr with
  | Infix InfixBinary left operator right | Infix InfixArrow left operator right =>
    if expr.inChain level then chainLinks level first left operator right around else [expr.el around]
  | Match _ _ _ _ => [expr.el (if first then { around | inArm = True } else around)]
  | _ => [expr.el around]

-- Declarations.

--| A declaration's keyword, as written.
def DefKind.keywordText: DefKind → Text
  | DefPlain => "def"
  | DefTheorem => "theorem"
  | DefInstance => "instance"

--| `def name: T := e`, `theorem name ∀ (x: A) [b: B]: P := e` (`decl`,
--| `header`, S6 to S12): the header in an `IdGroup`, then the body after
--| `:=` as `bodyAfter` chooses, or below at 2 when the header broke. The
--| declaration's first token's own-line comments are the file's to print.
def defDoc (header: Header) (colonEq: Comments) (value: Expr): Doc :=
  let keyword := fixedWord header.kind.keywordText header.keyword
  let colon := fixedWord ":" header.colon
  let assign := fixedWord ":=" colonEq
  let result := header.result
  let start: Around := { before = False, hoisted = True, item = False, at = 0, inArm = False }
  let headWords := [keyword, header.name] ++ optionWords header.forallKeyword
  let headSize := headWords.length
  let paramWords := groupsWords header.params
  let colonAt := headSize + paramWords.length
  let colonAround := start.next (trailsBack (paramWords.reverse ++ headWords.reverse)) colonAt
  let typeDoc := result.el (start.next colon.trails (colonAt + 1))
  let headDoc := spaced (headDocs start headWords)
  let headerDoc := match header.params with
    | [] =>
      let typed := if colon.trails then [Nest 4 (Doc.concat [HardLine, typeDoc])] else [Doc.text " ", Nest 4 typeDoc]
      Doc.concat ([headDoc, colon.leaf colonAround colonAt] ++ typed)
    | params =>
      paramsHeader headDoc (start.next (trailsBack headWords.reverse) headSize) params colon colonAround typeDoc
  let lastItem := match header.params.reverse with
    | [group, .._] => groupWords group
    | [] => headWords
  let inside :=
    (headWords.reverse.drop 1 |> .any Word.trails)
      || header.params.any groupHoldsComment
      || colon.trails
      || (result.words.reverse.drop 1 |> .any Word.trails)
      || (value.layoutBody && (lastCode lastItem).trails)
  let body := bodyAfter value assign (start.next assign.trails (colonAt + 2 + result.size)) False
  defFrom headerDoc
    (headerDoc.forcesBreak || inside)
    (assign.leaf (start.next result.trails (colonAt + 1 + result.size)) (colonAt + 1 + result.size))
    body.fst
    body.snd

--| A definition's document from its parts: the header, whether it must break, the `:=`, and the body's two forms.
def defFrom (headerDoc: Doc) (breaks: Bool) (assignDoc below choice: Doc): Doc :=
  Doc.concat [IdGroup 0 headerDoc breaks, Doc.text " ", assignDoc, IfBroken 0 below choice]

--| A body whose layout is measured from the header's last line: a comment
--| after the last parameter makes the header break, since the `:` can't
--| join the comment's line.
def Expr.layoutBody: Expr → Bool
  | Match _ _ _ _ | If _ _ _ _ _ _ _ | Block _ _ _ | Calc _ _ _ => True
  | _ => False

--| The last token that is no closer (`last_code`).
def lastCode (words: List Word): Word := words.reverse.dropWhile (word => isCloserText word.text) |> .headOr Word.none

--| The head's words, the keyword first: each stands after the one before.
def headDocs (around: Around): List Word → List Doc
  | [] => []
  | [word, ..rest] => [word.leaf around around.at, ..headDocs (around.next word.trails 1) rest]

--| Whether a comment ends a line inside a parameter group, rather than
--| after its last code token, where the header's lines may break anyway
--| (`comment_inside`'s `item_ends`).
def groupHoldsComment (group: Syntax.Group): Bool :=
  let back := (groupWords group).reverse
  let closers := back.takeWhile (word => isCloserText word.text)
  (closers.any Word.trails) || (back.drop (closers.length + 1) |> .any Word.trails)

--| A header with parameters (`header`, S6 to S8, D3564): on one line if it
--| fits; else the parameters fill lines at 4, each premise on a line of
--| its own, the type after the `:` on a line of its own at 4.
def paramsHeader (headDoc: Doc) (around: Around) (params: List Syntax.Group) (colon: Word)
    (colonAround: Around) (typeDoc: Doc):
    Doc :=
  let colonDoc := colon.leaf colonAround colonAround.at
  let colonBelow := colon.noted
  let docs := groupDocs around params
  let joined := if colonBelow then docs else attachLast docs colonDoc
  let runs := headerRuns [] [headDoc] True False (joined.zip (premisesOf [] params))
  let colonApart := colonBelow || colonAround.before
  let gap :=
    if !colonApart then Line
    else if colon.trails then HardLine
    else Doc.text " "
  Nest 4 (Doc.concat (Doc.joinedWith Line runs ++ (if colonBelow then [Line, colonDoc] else []) ++ [gap, typeDoc]))

def groupDocs (around: Around): List Syntax.Group → List Doc
  | [] => []
  | [group, ..rest] =>
    let words := groupWords group
    [groupDoc group around, ..groupDocs (around.next (trailsBack words.reverse) words.length) rest]

--| The docs with `last` written against the last of them.
def attachLast (docs: List Doc) (last: Doc): List Doc := match docs.reverse with
  | [] => [last]
  | [final, ..earlier] => [Doc.concat [final, last], ..earlier].reverse

--| The header's lines: runs of variables, each a balanced fill, the first
--| starting with the head; each premise alone; a single variable between
--| premises on the line of the premise before it (D3571). `done` and
--| `run` are newest first.
def headerRuns (done run: List Doc) (first previous: Bool): List (Doc, Bool) → List Doc
  | [] => (if run.isEmpty then done else [balancedFill run.reverse first, ..done]).reverse
  | [(doc, True), ..rest] =>
    let flushed := if run.isEmpty then done else [balancedFill run.reverse first, ..done]
    headerRuns [doc, ..flushed] [] (first && run.isEmpty) True rest
  | [(doc, False), ..rest] =>
    let nextPremise := match rest with
      | [] => True
      | [(_, premise), .._] => premise
    match done with
      | [premise, ..earlier] if run.isEmpty && previous && nextPremise =>
        headerRuns [Fill [premise, doc], ..earlier] [] first False rest
      | _ => headerRuns done [doc, ..run] first False rest

--| A run of a header's variables as a fill, except that the last line never
--| holds one variable alone when the line above could give it a companion
--| (`balanced_fill`, SW-3193): that line's last variable moves down to it.
--| `first` says the run starts with the head, on the declaration's line;
--| the other lines start at the header's indentation, 4.
def balancedFill (items: List Doc) (first: Bool): Doc := match items.map Doc.flatWidth |> allSome with
  | Some [firstWidth, ..widths] =>
    let starts := [0, ..fillStarts 1 (if first then firstWidth else 4 + firstWidth) widths]
    let lone := items.length - 1
    match starts.reverse with
      | [last, above, .._] =>
        let movedWidth := [firstWidth, ..widths].drop (lone - 1) |> .headOr 0
        let loneWidth := widths.reverse.headOr 0
        if last != lone || above + 1 >= last || 4 + movedWidth + 1 + loneWidth > width then Fill items
        else Doc.concat [Fill (items.take (lone - 1)), Line, Fill (items.drop (lone - 1))]
      | _ => Fill items
  | _ => Fill items

--| Where a greedy fill at 120 columns starts each line after the first:
--| item `k` on, at `column`.
def fillStarts (k column: Nat): List Nat → List Nat
  | [] => []
  | [next, ..rest] =>
    if column + 1 + next > width then [k, ..fillStarts (k + 1) (4 + next) rest]
    else fillStarts (k + 1) (column + 1 + next) rest

def allSome: List (Option Nat) → Option (List Nat)
  | [] => Some []
  | [None, .._] => None
  | [Some value, ..rest] => (allSome rest).map (values => [value, ..values])

-- Premises (D3564).

--| Which parameters are premises: the type has a relation or connective at
--| its top, or at the end of its `→`/`∀` chain, or applies a capitalised
--| name to an earlier parameter that is not a type (`premises`).
def premisesOf (earlier: List Text): List Syntax.Group → List Bool
  | [] => []
  | [group, ..rest] =>
    match group.annotation with
      | Some annotation =>
        let names := group.names.filter (name => name.text != "_") |> .map (name => name.text)
        [propositionIn earlier annotation, ..premisesOf (if annotation.isSort then earlier else earlier ++ names) rest]
      | None => [False, ..premisesOf earlier rest]

def Expr.isBlock: Expr → Bool
  | Block _ _ _ => True
  | _ => False

--| A value's element; a lambda just before a `;` keeps its body on its
--| line (`lambdaBoth`).
def valueEl (value: Expr) (around: Around) (semi: Bool): Doc := match value with
  | Binding BindsLambda _ params arrow body =>
    if semi then
      let (doc, _) := lambdaBoth params arrow body True { around | hoisted = True }
      value.framed around doc
    else value.el around
  | _ => value.el around

def Expr.isSort: Expr → Bool
  | Atom TypeU _ | Atom PropU _ | Universe _ _ => True
  | _ => False

--| Whether a type reads as a proposition (`is_proposition`).
def propositionIn (earlier: List Text): Expr → Bool
  | Infix InfixBinary _ operator _ => (operatorTok operator.text).any Tok.relation
  | Infix InfixArrow _ _ right => propositionIn earlier right
  | Infix InfixMembership _ _ _ | Infix InfixIff _ _ _ | Chain _ _ | Binding BindsExists _ _ _ _ => True
  | Binding BindsForall _ _ _ body => propositionIn earlier body
  | Prefix operator _ => operatorTok operator.text == Some Bang
  | Paren _ inner _ => propositionIn earlier inner
  | App (Atom _ head) arguments =>
    capitalised head.text && arguments.any (argument => argument.words.any (word => earlier.contains word.text))
  | _ => False

--| The operators whose application is a proposition.
def Tok.relation: Tok → Bool
  | Equals | NotEq | Lt | Le | Gt | Ge | AndAnd | OrOr | EqEq => True
  | _ => False

--| Whether a name's last part starts with a capital: `Even`, `List.Sorted`.
def capitalised (name: Text): Bool :=
  name.splitOn "." |> .reverse |> .headOr "" |> .toList |> .headOr ' ' |> .isAsciiUppercase

--| What follows a `:=` or an arm's `=>` (`body_after`, S12, S17): the doc
--| for a header that broke (the value below at 2), and the choice for one
--| that didn't: on the line if all of it fits; a tuple, list or hugging
--| call below if it fits on one line there (D3571); a `match` whose `match
--| … with` fits on the line (D3553), a tuple or list on the line, a call
--| hugging its last argument, or a lambda with its body below (D3568); else
--| below. A block always goes below. `semi` says a `;` follows the value.
def bodyAfter (value: Expr) (assign: Word) (around: Around) (semi: Bool): (Doc, Doc) :=
  let inside := { around | hoisted = True }
  let matched := value.matchedParts inside
  let doc := bodyDoc value matched around semi
  let below := Nest 2 (Doc.concat [HardLine, doc])
  if assign.trails || value.noted || value.isBlock then (below, below)
  else
    let hug := value.callHug inside
    let opens := value.opensBracket
    let lambda := value.lambdaHug semi inside doc
    let matchHug := matched.map (parts => parts.hug)
    let oneLineBelow := if opens || hug.isSome then [OneLineBelow doc] else []
    let onLine :=
      if opens then [Doc.concat [Doc.text " ", doc]]
      else optionList (((matchHug.orElse lambda).orElse hug).map (open => Doc.concat [Doc.text " ", open]))
    (below, Choice ([Flatten (Doc.concat [Doc.text " ", doc])] ++ oneLineBelow ++ onLine ++ [below]))

--| The parts of a `match` value, for its first line to stay on the `:=`'s.
def Expr.matchedParts (value: Expr) (inside: Around): Option Matched := match value with
  | Match keyword scrutinees withKeyword arms => Some (matchParts keyword scrutinees withKeyword arms inside)
  | _ => None

--| The value's document, from its `match` parts if it is one.
def bodyDoc (value: Expr) (matched: Option Matched) (around: Around) (semi: Bool): Doc := match matched with
  | Some parts => value.framed around parts.doc
  | None => valueEl value around semi

--| A call's hug, which may go on the `:=`'s line.
def Expr.callHug (value: Expr) (inside: Around): Option Doc := match value with
  | App head arguments => (appDocs head arguments inside).hug
  | _ => None

--| A value that opens its brackets on the `:=`'s line: a tuple, list or record.
def Expr.opensBracket: Expr → Bool
  | Tuple _ _ _ _ | ListOf _ _ _ _ | Record _ _ _ _ _ => True
  | _ => False

--| A lambda's opened form, with its body below; a `calc` joins the line when `calc` and its first expression fit
--| there, as a comma bracket does, but never goes one line below (`doc` is the value's document).
def Expr.lambdaHug (value: Expr) (semi: Bool) (inside: Around) (doc: Doc): Option Doc := match value with
  | Binding BindsLambda _ params arrow body =>
    let (_, opened) := lambdaBoth params arrow body semi inside
    Some opened
  | Calc _ _ _ => Some doc
  | _ => None

-- Layout: blocks, `let`, `if` and `match` (slice 3).

--| An element after a space on its line; a block starts a line of its own
--| below at 2 instead (`join`, S12, S17).
def Expr.after (expr: Expr) (around: Around): Doc := match expr with
  | Block _ _ _ => Nest 2 (Doc.concat [HardLine, expr.el around])
  | _ => Doc.concat [Doc.text " ", expr.el around]

--| A block's lines, each at the block's column (`block`, S17); an author's
--| blank line above a line after the first is kept.
def blockDoc (first: Statement) (rest: List Statement) (result: Expr) (around: Around): Doc :=
  Doc.concat [first.el around, ..laterLines around.inArm result first.trails (around.at + first.size) rest]

def laterLines (arm: Bool) (result: Expr) (before: Bool) (at: Nat): List Statement → List Doc
  | [] => [HardLine, result.el { before, hoisted = False, item = True, at, inArm = arm }]
  | [statement, ..rest] => [
    HardLine,
    statement.el { before, hoisted = False, item = True, at, inArm = arm },
    ..laterLines arm result statement.trails (at + statement.size) rest
  ]

def Statement.trails (statement: Statement): Bool := trailsBack statement.words.reverse

def Statement.size (statement: Statement): Nat := statement.words.length

--| A block's line before its value: a `let` or an expression.
def Statement.el (statement: Statement) (around: Around): Doc := match statement with
  | LetStatement binding =>
    framedBy (fixedWord "let" binding.keyword) around (letDoc binding False { around | hoisted = True })
  | ExprStatement value => value.el around
  | _ => Nothing

--| `let p := value` or `let p: T := value` (`let_line`, S17): the value as
--| a body after `:=` (S12), below when the line up to `:=` broke. An
--| expression `let`'s value (`exprLet`, before its `;`) never goes below
--| the line: starting a line it would be a block, whose `;` would be a
--| sequence's. It starts on the `:=` line unless a comment puts it below.
def letDoc (binding: Let) (exprLet: Bool) (around: Around): Doc := match binding with
  | { keyword, pattern, annotation, colonEq, value } =>
    let letWord := fixedWord "let" keyword
    let assign := fixedWord ":=" colonEq
    let patternSize := pattern.words.length
    let annotationSize := (annotationWords annotation).length
    let assignAt := 1 + patternSize + annotationSize
    let typed := match annotation with
      | Some (colonComments, typeExpr) =>
        let colon := fixedWord ":" colonComments
        let colonAround := around.next (trailsBack pattern.words.reverse) (1 + patternSize)
        [colon.leaf colonAround colonAround.at, Doc.text " ", typeExpr.el (around.next colon.trails (2 + patternSize))]
      | None => []
    let assignAround := around.next (trailsBack ((letWords binding).reverse.drop (1 + value.size))) assignAt
    let head :=
      Doc.concat
        ([letWord.leaf around around.at, Doc.text " ", pattern.el (around.next letWord.trails 1)]
          ++ typed
          ++ [Doc.text " ", assign.leaf assignAround assignAround.at])
    let valueAround := around.next assign.trails (assignAt + 1)
    let (below, choice) := bodyAfter value assign valueAround exprLet
    if exprLet then
      if assign.trails || value.noted then Doc.concat [head, HardLine, value.el valueAround]
      else if value.isBlock then Doc.concat [head, choice]
      else Doc.concat [head, Doc.text " ", valueEl value valueAround True]
    else
      let id := around.at + 1
      Doc.concat [IdGroup id head head.forcesBreak, IfBroken id below choice]

--| `let x := e; body` (`sequence`, S18): on one line if it fits, otherwise
--| a line break after the `;`, the body lined up where the `let` starts.
def letInDoc (binding: Let) (semicolon: Comments) (body: Expr) (around: Around): Doc :=
  let size := (letWords binding).length
  let semi := fixedWord ";" semicolon
  let letPart := framedBy (fixedWord "let" binding.keyword) around (letDoc binding True around)
  let semiAround := around.next (trailsBack (letWords binding).reverse) size
  let bodyEl := body.el (around.next semi.trails (size + 1))
  if binding.valueBelow then Doc.group (Doc.concat [letPart, semi.leaf semiAround semiAround.at, Doc.text " ", bodyEl])
  else Doc.group (Align (Doc.concat [letPart, semi.leaf semiAround semiAround.at, Line, bodyEl]))

--| Whether a comment puts an expression `let`'s value on the line below its `:=`: an own-line comment before it,
--| or a trailing comment ending the `:=` line. The value then stays at the indentation in force, a continuation of
--| the `:=` line, and the body after the `;` stays on the value's line: a line starting at the `let`'s column, or
--| a value at +2, would be a block that ends at the `;` (SW-4922, `let_value_comment_below`).
def Let.valueBelow (binding: Let): Bool := match binding with
  | { colonEq, value, .. } => colonEq.after.isSome || value.noted

--| `if c then a else b` (`if_`, S19), its clauses not yet grouped: on one
--| line if it fits, otherwise one clause a line at the `if`'s column, each
--| branch after its keyword if it fits, else below at 2. A chain with an
--| `else if` is a table of cases, never one line (D3605).
def ifDoc (keyword: Word) (condition: Expr) (thenKeyword: Word) (whenTrue: Expr) (elseKeyword: Word)
    (whenFalse: Expr) (around: Around):
    Doc :=
  let clauses := ifClauses Nothing keyword condition thenKeyword whenTrue elseKeyword whenFalse around
  Doc.concat ((if clauses.length > 2 then [BreakParent] else []) ++ Doc.joinedWith Line clauses)

--| The clauses of an `if` and of the `else if`s after it, each a group;
--| `prefix` is the `else ` before an `else if`'s `if`. An `if` that a
--| comment puts on the line after its `else` is a branch of its own.
def ifClauses (prefix: Doc) (keyword: Word) (condition: Expr) (thenKeyword: Word) (whenTrue: Expr) (elseKeyword: Word)
    (whenFalse: Expr) (around: Around):
    List Doc :=
  let thenAt := 1 + condition.size
  let elseAt := thenAt + 1 + whenTrue.size
  let thenAround := around.next condition.trails thenAt
  let elseAround := around.next whenTrue.trails elseAt
  let otherAround := around.next elseKeyword.trails (elseAt + 1)
  let head := Doc.concat [
    prefix,
    keyword.leaf around around.at,
    condition.after (around.next keyword.trails 1),
    Doc.text " ",
    thenKeyword.leaf thenAround thenAround.at
  ]
  let clause :=
    Doc.group (Doc.concat [head, Nest 2 (Doc.concat [Line, whenTrue.el (around.next thenKeyword.trails (thenAt + 1))])])
  let elseDoc := elseKeyword.leaf elseAround elseAround.at
  match whenFalse with
    | If nextKeyword None nextCondition nextThen nextTrue nextElse nextFalse if !whenFalse.noted
        && !elseKeyword.trails => [
      clause,
      ..ifClauses
        (Doc.concat [elseDoc, Doc.text " "])
        nextKeyword
        nextCondition
        nextThen
        nextTrue
        nextElse
        nextFalse
        otherAround
    ]
    | _ => [clause, Doc.group (Doc.concat [elseDoc, Nest 2 (Doc.concat [Line, whenFalse.el otherAround])])]

--| A `match`'s document, and the form that hugs a `:=` line, its `match …
--| with` unbroken (D3553).
type Matched = { doc: Doc, hug: Doc }

--| `match e, f with` and its arms (`alternatives`, S20, D3566): two or more
--| arms one a line at 2; one may share the line, but not inside another
--| `match`'s arm, where the arms after it would read as its own.
def matchParts (keyword: Word) (scrutinees: List Scrutinee) (withKeyword: Word) (arms: List Arm) (around: Around):
    Matched :=
  let words := scrutineesWords scrutinees
  let withAt := 1 + words.length
  let withAround := around.next (trailsBack (words.reverse ++ [keyword])) withAt
  let head :=
    Doc.concat
      ([keyword.leaf around around.at]
        ++ scrutineeDocs around.inArm True keyword.trails (around.at + 1) scrutinees
        ++ [Doc.text " ", withKeyword.leaf withAround withAround.at])
  let many := arms.length >= 2 || around.inArm
  let armsDoc := Nest 2 (Doc.concat (armLines many withKeyword.trails (around.at + withAt + 1) arms))
  let doc := Doc.concat [head, armsDoc]
  let hug := Doc.concat [Flatten head, armsDoc]
  if many then { doc, hug } else { doc = Doc.group doc, hug = Doc.group hug }

--| The matched expressions, a comma and a space between each two.
def scrutineeDocs (arm first before: Bool) (at: Nat): List Scrutinee → List Doc
  | [] => []
  | [{ value, .. }, ..rest] =>
    let around := { before, hoisted = False, item = False, at, inArm = arm }
    (if first then [] else [Closing ","])
      ++ [value.after around, ..scrutineeDocs arm False value.trails (at + value.size) rest]

--| Each arm on a line at 2 (or, alone, perhaps on the `with` line), an
--| author's blank line above it kept.
def armLines (many before: Bool) (at: Nat): List Arm → List Doc
  | [] => []
  | [arm, ..rest] =>
    let words := arm.words
    [
      if many then HardLine else Line,
      arm.el { before, hoisted = False, item = True, at, inArm = True },
      ..armLines many (trailsBack words.reverse) (at + words.length) rest
    ]

def Arm.el (arm: Arm) (around: Around): Doc := framedBy arm.bar around (armDoc arm { around | hoisted = True })

--| `| p, q if c => body` (`arm`, S21): the patterns continuing at 4 from
--| the `|` if too long; the body as after `:=`, but a `match` always below.
--| An absurd arm, with no `=>`, is its tokens on a line (`join`).
def armDoc (arm: Arm) (around: Around): Doc := match arm with
  | { bar, patterns, guard, body = Some (arrow, value) } =>
    let patternWords := patternsWords patterns
    let guardSize := (guardWords guard).length
    let arrowAt := 1 + patternWords.length + guardSize
    let guardAround := around.next (trailsBack ([bar, ..patternWords].reverse)) (1 + patternWords.length)
    let arrowAround := around.next (trailsBack ([bar, ..patternWords] ++ guardWords guard).reverse) arrowAt
    let head :=
      Nest 2
        (Doc.concat
          ([bar.leaf around around.at]
            ++ patternDocs around.inArm True bar.trails (around.at + 1) patterns
            ++ guardDocs guard guardAround
            ++ [Doc.text " ", arrow.leaf arrowAround arrowAround.at]))
    let valueAround := around.next arrow.trails (arrowAt + 1)
    match value with
      | Match _ _ _ _ => Doc.concat [head, Nest 2 (Doc.concat [HardLine, value.el valueAround])]
      | Calc _ _ _ => Doc.concat [head, Nest 2 (Doc.concat [HardLine, value.el valueAround])]
      | _ =>
        let (_, choice) := bodyAfter value arrow valueAround False
        Doc.concat [head, choice]
  | { bar, patterns, guard, body = None } =>
    let patternWords := patternsWords patterns
    let guardAround := around.next (trailsBack ([bar, ..patternWords].reverse)) (1 + patternWords.length)
    Doc.concat
      ([bar.leaf around around.at]
        ++ patternDocs around.inArm True bar.trails (around.at + 1) patterns
        ++ guardDocs guard guardAround)

--| An arm's patterns, after the `|`, a comma and a space between each two.
def patternDocs (arm first before: Bool) (at: Nat): List Pattern → List Doc
  | [] => []
  | [pattern, ..rest] =>
    let words := pattern.words
    (if first then [] else [Closing ","])
      ++ [
        Doc.text " ",
        pattern.el { before, hoisted = False, item = False, at, inArm = arm },
        ..patternDocs arm False (trailsBack words.reverse) (at + words.length) rest
      ]

--| ` if c` after an arm's patterns.
def guardDocs (guard: Option Guard) (around: Around): List Doc := match guard with
  | Some { keyword, condition, .. } =>
    let doc :=
      Doc.concat [keyword.leaf { around | hoisted = True } around.at, condition.after (around.next keyword.trails 1)]
    [Doc.text " ", framedBy keyword around doc]
  | None => []

--| A pattern: a name, `_`, a literal, or a constructor applied to those,
--| which prints as a call of plain arguments (`app`, D3569); from slice 4b,
--| `(p)` and `()` (`join`), tuples and lists (`comma_bracket`), and a
--| constructor applied to those (`app`).
def Pattern.el (pattern: Pattern) (around: Around): Doc :=
  let inside := { around | hoisted = True }
  match pattern with
    | PatternWord _ word => word.leaf around around.at
    | PatternCtor name arguments =>
      if arguments.all Pattern.simple then
        let docs := [name.leaf inside around.at, ..argumentPatterns around.inArm name.trails (around.at + 1) arguments]
        let commented := wordsCommented name (patternsWords arguments)
        framedBy name around (if commented then spaced docs else Nest 4 (Fill (patternItems docs arguments)))
      else framedBy name around (patternApp name arguments inside)
    | PatternParen open inner close =>
      framedBy open around
        (Doc.concat [
          open.opening inside close,
          inner.el (around.next open.trails 1),
          close.leaf (around.next (trailsBack inner.words.reverse) (1 + inner.words.length)) around.at
        ])
    | PatternAbsurd open close =>
      framedBy open around (Doc.concat [open.opening inside close, close.leaf (around.next open.trails 1) around.at])
    | PatternTuple open items _ close =>
      framedBy open around (Doc.group (patternBracket (tuple := True) open items [] None close inside))
    | PatternList open items _ tail close =>
      let at := around.at + 1 + (patternsWords items).length
      let tailDoc := match tail with
        | Some (dots, rest) =>
          let start := itemAround around.inArm (items.isEmpty && open.trails) at
          Some (Doc.concat [dots.leaf start at, rest.el (start.next dots.trails 1)])
        | None => None
      framedBy open around
        (Doc.group (patternBracket (tuple := False) open items (tailWords tail) tailDoc close inside))
    | PatternRecord fields => framedBy fields.open around (Doc.group (fieldsContent fields inside))
    | PatternCtorFields name fields =>
      framedBy name around
        (Doc.concat [name.leaf inside around.at, Doc.text " ", fieldsJoined fields (around.next name.trails 1)])
    | _ => Nothing

def argumentPatterns (arm before: Bool) (at: Nat): List Pattern → List Doc
  | [] => []
  | [pattern, ..rest] =>
    let words := pattern.words
    [
      pattern.el { before, hoisted = False, item = False, at, inArm = arm },
      ..argumentPatterns arm (trailsBack words.reverse) (at + words.length) rest
    ]

--| Whether a comment sits between the words, after `previous` (whose
--| arguments are single words, `comment_between`).
def wordsCommented (previous: Word): List Word → Bool
  | [] => False
  | [next, ..rest] => previous.trails || next.noted || wordsCommented next rest

--| A pattern call's fill items: a `_` can't start a line, so it joins the
--| item before it (`fill_items`). `docs` has the constructor's first.
def patternItems (docs: List Doc) (arguments: List Pattern): List Doc := match docs with
  | [] => []
  | [head, ..rest] => mergeUnderscores head (rest.zip arguments)

def mergeUnderscores (current: Doc): List (Doc, Pattern) → List Doc
  | [] => [current]
  | [(doc, PatternWord Underscore _), ..rest] => mergeUnderscores (Doc.concat [current, Doc.text " ", doc]) rest
  | [(doc, _), ..rest] => [current, ..mergeUnderscores doc rest]

-- Slice 4b's patterns.

--| Whether a pattern may stay on its constructor's line when the others
--| go below (`simple`): a token. Rust's `[]` pattern is no `List` node, so
--| it is not simple, unlike the expression.
def Pattern.simple: Pattern → Bool
  | PatternWord _ _ => True
  | _ => False

--| A constructor with an argument that is no token (`app`, with no hug: no
--| pattern can hug): on one line if it fits, else the constructor and its
--| leading tokens on the line (filling lines at 4 when there are two or
--| more) and each other argument on its own line, as `appDocs`.
def patternApp (name: Word) (arguments: List Pattern) (around: Around): Doc :=
  let docs := [name.leaf around around.at, ..argumentPatterns around.inArm name.trails (around.at + 1) arguments]
  let keep := 1 + keptPatterns name arguments
  let kept := docs.take keep
  let fillFront := keep > 2 && !wordsCommented name (patternsWords (arguments.take (keep - 1)))
  let id := around.at + 1
  let frontDoc := if fillFront then IdGroup id (Nest 4 (Fill (patternItems kept arguments))) False else spaced kept
  let rest := Doc.concat (docs.drop keep |> .concatMap (doc => [HardLine, doc]))
  let restDoc := if fillFront then IfBroken id (Nest 4 rest) (Nest 2 rest) else Nest 2 rest
  Choice [Flatten (spaced docs), Doc.concat [frontDoc, restDoc]]

--| How many of a constructor's arguments stay on its line (`keep`): the
--| tokens right after it, up to one after a comment.
def keptPatterns (previous: Word): List Pattern → Nat
  | [] => 0
  | [argument, ..rest] =>
    if argument.simple && !previous.trails then 1 + keptPatterns (argument.words.headOr Word.none) rest else 0

--| A tuple or list pattern's parts, not yet grouped (`comma_bracket_content`):
--| a tuple of only names and `_` fills its lines (D3572, proof-tuples.md
--| §5); otherwise each item is on a line of its own at 2 when broken, a
--| list's `..rest` the last (`tail`, its words in `rest`), the `..` and
--| the pattern with nothing between. `[]` is its two brackets (`join`).
def patternBracket (tuple: Bool) (open: Word) (items: List Pattern) (rest: List Word) (tail: Option Doc)
    (close: Word) (around: Around):
    Doc :=
  let words := [open, ..patternsWords items] ++ rest ++ [close]
  let closer := close.leaf (around.next (trailsBack (words.reverse.drop 1)) (words.length - 1)) around.at
  let prefix := open.opening around close
  let bare := tuple && items.all Pattern.plainName
  let holds := (words.filter Word.trails |> .length) > (if trailsBack words.reverse then 1 else 0)
  if items.isEmpty && tail.isNone then Doc.concat [prefix, closer]
  else if tuple && !holds && items.all Pattern.plainName then
    Doc.concat [prefix, Nest 2 (Fill (patternCells bare around.inArm open.trails (around.at + 1) items)), closer]
  else
    let body := brokenPatterns bare around.inArm True open.trails (around.at + 1) items tail
    let parts := [prefix, Nest 2 (Doc.concat body), SoftLine, closer]
    Doc.concat (if holds then parts ++ [BreakParent] else parts)

--| A name or `_` with no comment above it: what a filled tuple pattern holds.
def Pattern.plainName: Pattern → Bool
  | PatternWord Lower word | PatternWord Underscore word => !word.noted
  | _ => False

--| A filled tuple pattern's cells: each item with its comma.
def patternCells (bare arm before: Bool) (at: Nat): List Pattern → List Doc
  | [] => []
  | [item] => [item.el (firstAround bare arm before at)]
  | [item, ..rest] => [
    Doc.concat [item.el (firstAround bare arm before at), Closing ","],
    ..patternCells False arm False (at + item.words.length) rest
  ]

--| A broken tuple or list pattern's items, as `brokenItems`, then a list's
--| `..rest`.
def brokenPatterns (bare arm first before: Bool) (at: Nat) (items: List Pattern) (tail: Option Doc): List Doc :=
  match items with
    | [] =>
      match tail with
        | Some doc => [if first then SoftLine else Line, doc]
        | None => []
    | [item, ..rest] =>
      let more := !rest.isEmpty || tail.isSome
      [if first then SoftLine else Line, item.el (firstAround bare arm before at)]
        ++ (if more then [Closing ","] else [])
        ++ brokenPatterns False arm False False (at + item.words.length) rest tail

--| `(name := value)`, a named argument (`join`: no rule of its own).
def namedArgDoc (open name colonEq: Word) (value: Expr) (close: Word) (around: Around): Doc := Doc.concat [
  open.opening around close,
  name.leaf (around.next open.trails 1) (around.at + 1),
  Doc.text " ",
  colonEq.leaf (around.next name.trails 2) (around.at + 2),
  Doc.text " ",
  value.el (around.next colonEq.trails 3),
  close.leaf (around.next value.trails (3 + value.size)) around.at
]

--| `(value: T)`, a type annotation (`join`: no rule of its own), the `:`
--| touching the value as in a parameter (R3).
def annotationDoc (open: Word) (value: Expr) (colon: Word) (annotation: Expr) (close: Word) (around: Around): Doc :=
  let colonAt := 1 + value.size
  Doc.concat [
    open.opening around close,
    value.el (around.next open.trails 1),
    colon.leaf (around.next value.trails colonAt) (around.at + colonAt),
    Doc.text " ",
    annotation.el (around.next colon.trails (colonAt + 1)),
    close.leaf (around.next annotation.trails (colonAt + 1 + annotation.size)) around.at
  ]

-- Slice 4c's records and membership.

--| `x ∈ s` (`join`: Rust has no rule of its own for `Membership`): never
--| breaks between its operands.
def membershipDoc (left: Expr) (operator: Word) (right: Expr) (around: Around): Doc :=
  let operatorAround := around.next left.trails left.size
  Doc.concat [
    left.el around,
    Doc.text " ",
    operator.leaf operatorAround operatorAround.at,
    right.after (around.next operator.trails (left.size + 1))
  ]

--| `name = value` in a record (`join`).
def recordFieldDoc (name equals: Word) (value: Expr) (around: Around): Doc := Doc.concat [
  name.leaf around around.at,
  Doc.text " ",
  equals.leaf (around.next name.trails 1) (around.at + 1),
  value.after (around.next equals.trails 2)
]

--| A record's parts, not yet grouped (`comma_bracket_content` with brace
--| edges): `{ a = 1, b }` flat, else each field on a line of its own at 2
--| and `}` alone. An update's record and its `|` stay on the `{` line.
--| Unlike a list, a record never fills its lines.
def recordContent (open: Word) (base: Option (Expr, Word)) (fields: List Expr) (close: Word) (around: Around): Doc :=
  let whole := Record open base fields False close
  let closer := close.leaf (around.next whole.trailsBeforeClose (whole.size - 1)) around.at
  let opener := open.opening around close
  let (prefix, before, at) := match base with
    | Some (record, bar) =>
      let barAround := around.next record.trails (1 + record.size)
      (
        Doc.concat [
          opener,
          Doc.text " ",
          record.el (around.next open.trails 1),
          Doc.text " ",
          bar.leaf barAround barAround.at
        ],
        bar.trails,
        around.at + 2 + record.size
      )
    | None => (opener, open.trails, around.at + 1)
  let parts := [prefix, Nest 2 (Doc.concat (recordItems around.inArm before at fields)), Line, closer]
  Doc.concat (if whole.holdsTrailingComment then parts ++ [BreakParent] else parts)

--| A broken record's fields: each starts a line, with its comma after it.
def recordItems (arm before: Bool) (at: Nat): List Expr → List Doc
  | [] => []
  | [item] => [Line, item.el (itemAround arm before at)]
  | [item, ..rest] =>
    [Line, item.el (itemAround arm before at), Closing ",", ..recordItems arm False (at + item.size) rest]

--| A record as a call's last argument: as it is, and opened.
def huggedRecord (open: Word) (base: Option (Expr, Word)) (fields: List Expr) (close: Word) (around: Around):
    (Doc, Option Doc) :=
  let content := recordContent open base fields close { around | hoisted = True }
  (framedBy open around (Group content content.forcesBreak), Some (framedBy open around (Group content True)))

--| `x` or `x = p` in a record pattern (`join`: Rust's tree has no node
--| for it).
def FieldPattern.el (field: FieldPattern) (around: Around): Doc := match field with
  | { name, value = Some (equals, pattern) } => Doc.concat [
    name.leaf around around.at,
    Doc.text " ",
    equals.leaf (around.next name.trails 1) (around.at + 1),
    Doc.text " ",
    pattern.el (around.next equals.trails 2)
  ]
  | { name, value = None } => name.leaf around around.at

--| A record pattern's parts, not yet grouped (`comma_bracket_content`
--| with brace edges): flat, else each field and the `..` on a line of
--| their own at 2 and `}` alone.
def fieldsContent (fields: FieldsPattern) (around: Around): Doc := match fields with
  | { open, fields = items, rest, close, .. } =>
    let words := fields.words
    let closer := close.leaf (around.next (trailsBack (words.reverse.drop 1)) (words.length - 1)) around.at
    let holds := (words.filter Word.trails |> .length) > (if trailsBack words.reverse then 1 else 0)
    let body := fieldItems around.inArm open.trails (around.at + 1) items rest
    let parts := [open.opening around close, Nest 2 (Doc.concat body), Line, closer]
    Doc.concat (if holds then parts ++ [BreakParent] else parts)

--| A broken record pattern's fields, then its `..`.
def fieldItems (arm before: Bool) (at: Nat) (items: List FieldPattern) (rest: Option Word): List Doc := match items with
  | [] =>
    match rest with
      | Some dots => [Line, dots.leaf (itemAround arm before at) at]
      | None => []
  | [field, ..others] =>
    let more := !others.isEmpty || rest.isSome
    [Line, field.el (itemAround arm before at)]
      ++ (if more then [Closing ","] else [])
      ++ fieldItems arm False (at + field.words.length) others rest

--| `C { x, y = p, .. }`'s braces and fields (`join`: in Rust's tree they
--| are the constructor's children, not a bracket node), on one line. The
--| slice has them without comments.
def fieldsJoined (fields: FieldsPattern) (around: Around): Doc := match fields with
  | { open, fields = items, rest, close, .. } =>
    let words := fields.words
    let restAt := around.at + 1 + (fieldPatternsWords items).length
    let restDocs := match rest with
      | Some dots => [dots.leaf (around.next False (restAt - around.at)) restAt]
      | None => []
    Doc.concat [
      open.leaf around around.at,
      Doc.text " ",
      Doc.joined (joinedFields around.inArm (around.at + 1) items ++ restDocs) (Doc.concat [Closing ",", Doc.text " "]),
      Doc.text " ",
      close.leaf (around.next False (words.length - 1)) around.at
    ]

def joinedFields (arm: Bool) (at: Nat): List FieldPattern → List Doc
  | [] => []
  | [field, ..rest] => [
    field.el { before = False, hoisted = False, item = False, at, inArm = arm },
    ..joinedFields arm (at + field.words.length) rest
  ]

-- Slice 5a's declarations.

--| Where a declaration's first token stands: its own-line comments are
--| the file's to print (`file_comments`).
def declStart (arm: Bool): Around := { before = False, hoisted = True, item = False, at = 0, inArm = arm }

--| `namespace Name` (`join`: the node has no rule of its own).
def namespaceDoc (keyword: Comments) (name: Word): Doc :=
  let keywordWord := fixedWord "namespace" keyword
  let start := declStart False
  Doc.concat [keywordWord.leaf start 0, Doc.text " ", name.leaf (start.next keywordWord.trails 1) 1]

--| `test "name" := e` (`decl` with a head and a body only): the head in an
--| `IdGroup`, which a comment after `test` breaks, then the body after
--| `:=` as `bodyAfter` chooses.
def testDoc (keyword: Comments) (name: Word) (colonEq: Comments) (value: Expr): Doc :=
  let keywordWord := fixedWord "test" keyword
  let assign := fixedWord ":=" colonEq
  let start := declStart False
  let headDoc := spaced (headDocs start [keywordWord, name])
  let (below, choice) := bodyAfter value assign (start.next assign.trails 3) False
  Doc.concat [
    IdGroup 0 headDoc (headDoc.forcesBreak || keywordWord.trails),
    Doc.text " ",
    assign.leaf (start.next name.trails 2) 2,
    IfBroken 0 below choice
  ]

--| `import M (a, b as c)` or `import M (..)` (`import`, `comma_bracket`):
--| flat if it fits, else one item a line at 2, the `)` on its own line.
--| Each item is a node in Rust's tree, so a comment before it displaces
--| it.
def importDoc (keyword: Comments) (path: Word) (open: Comments) (imported: Imported) (close: Comments): Doc :=
  let keywordWord := fixedWord "import" keyword
  let openWord := fixedWord "(" open
  let closeWord := fixedWord ")" close
  let start := declStart False
  let inner := importedWords imported
  let all := [keywordWord, path, openWord, ..inner] ++ [closeWord]
  let holds := (all.filter Word.trails |> .length) > (if trailsBack all.reverse then 1 else 0)
  let prefix := Doc.concat [
    keywordWord.leaf start 0,
    Doc.text " ",
    path.leaf (start.next keywordWord.trails 1) 1,
    Doc.text " ",
    openWord.opening (start.next path.trails 2) closeWord
  ]
  let items := match imported with
    | ImportAll dots => [SoftLine, (fixedWord ".." dots).leaf (itemAround False openWord.trails 3) 3]
    | ImportItems list => importItemDocs True openWord.trails 3 list
  let closer := closeWord.leaf (start.next (trailsBack [openWord, ..inner].reverse) (3 + inner.length)) 2
  let parts := [prefix, Nest 2 (Doc.concat items), SoftLine, closer]
  Doc.group (Doc.concat (if holds then parts ++ [BreakParent] else parts))

--| The tokens between an import's brackets, commas left out.
def importedWords: Imported → List Word
  | ImportAll dots => [fixedWord ".." dots]
  | ImportItems items => importItemsWords items

def importItemsWords: List ImportItem → List Word
  | [] => []
  | [item, ..rest] => item.words ++ importItemsWords rest

def ImportItem.words (item: ImportItem): List Word := match item.alias with
  | Some (asComments, alias) => [item.name, fixedWord "as" asComments, alias]
  | None => [item.name]

--| A broken import's items, as `brokenItems`: each starts a line, with its
--| comma after it.
def importItemDocs (first before: Bool) (at: Nat): List ImportItem → List Doc
  | [] => []
  | [item] => [if first then SoftLine else Line, item.el (itemAround False before at)]
  | [item, ..rest] =>
    let words := item.words
    [
      if first then SoftLine else Line,
      item.el (itemAround False before at),
      Closing ",",
      ..importItemDocs False (trailsBack words.reverse) (at + words.length) rest
    ]

--| `name` or `name as alias`, framed as a node.
def ImportItem.el (item: ImportItem) (around: Around): Doc :=
  let inside := { around | hoisted = True }
  let named := item.name.leaf inside around.at
  let doc := match item.alias with
    | Some (asComments, alias) =>
      let asWord := fixedWord "as" asComments
      Doc.concat [
        named,
        Doc.text " ",
        asWord.leaf (around.next item.name.trails 1) (around.at + 1),
        Doc.text " ",
        alias.leaf (around.next asWord.trails 2) (around.at + 2)
      ]
    | None => named
  framedBy item.name around doc

--| `def f: A → B` and its arms (`decl` with `Arms`): the header as
--| `defDoc`'s, inside the arms' depth (`arm_depth`), then each arm on a
--| line of its own at 2.
def defArmsDoc (header: Header) (arms: List Arm): Doc :=
  let keyword := fixedWord header.kind.keywordText header.keyword
  let colon := fixedWord ":" header.colon
  let result := header.result
  let start := declStart True
  let headWords := [keyword, header.name] ++ optionWords header.forallKeyword
  let headSize := headWords.length
  let paramWords := groupsWords header.params
  let colonAt := headSize + paramWords.length
  let colonAround := start.next (trailsBack (paramWords.reverse ++ headWords.reverse)) colonAt
  let typeDoc := result.el (start.next colon.trails (colonAt + 1))
  let headDoc := spaced (headDocs start headWords)
  let headerDoc := match header.params with
    | [] =>
      let typed := if colon.trails then [Nest 4 (Doc.concat [HardLine, typeDoc])] else [Doc.text " ", Nest 4 typeDoc]
      Doc.concat ([headDoc, colon.leaf colonAround colonAt] ++ typed)
    | params =>
      paramsHeader headDoc (start.next (trailsBack headWords.reverse) headSize) params colon colonAround typeDoc
  let inside :=
    (headWords.reverse.drop 1 |> .any Word.trails)
      || header.params.any groupHoldsComment
      || colon.trails
      || (result.words.reverse.drop 1 |> .any Word.trails)
  let headerWords := headWords ++ paramWords ++ [colon] ++ result.words
  Doc.concat [
    IdGroup 0 headerDoc (headerDoc.forcesBreak || inside),
    Nest 2 (Doc.concat (armLines True (trailsBack headerWords.reverse) (colonAt + 1 + result.size) arms))
  ]

-- Proof steps: `rewrite` (slice 6a).

--| A fixed token and the expression after it, if they are there.
def afterWords (text: Text): Option (Comments, Expr) → List Word
  | Some (comments, value) => [fixedWord text comments, ..value.words]
  | None => []

--| A rule's tokens: `<` and `-` when it is reversed, then the rule's.
def RewriteRule.words (rule: RewriteRule): List Word := match rule with
  | { reverse = Some (less, minus), rule = value } => [fixedWord "<" less, fixedWord "-" minus, ..value.words]
  | { reverse = None, rule = value } => value.words

def rulesWords: List RewriteRule → List Word
  | [] => []
  | [rule, ..rest] => rule.words ++ rulesWords rest

--| The rules' tokens: the list's, or `repeatedly` and the set's.
def Rules.words: Rules → List Word
  | RuleList rules => rulesWords rules
  | Repeatedly word set => [fixedWord "repeatedly" word, ..set.words]

def RuleSet.words (set: RuleSet): List Word := match set with
  | { open, rules, close, .. } => [fixedWord "[" open, ..rulesWords rules] ++ [fixedWord "]" close]

--| `rewrite rules then body` (`rewrite`, S36, D3668): on one line if it
--| fits; otherwise the body below at 2, and if the rules don't fit on the
--| `rewrite` line, one rule a line at 4 with `then` at the end of the
--| last. Without `then`, several rules lay out as they do before one, and
--| a single rule (with its `at`) is joined by spaces. The `at` and its
--| target stay with the last rule; `repeatedly` and its set are one item.
def rewriteDoc (keyword: Comments) (rules: Rules) (target body: Option (Comments, Expr)) (around: Around): Doc :=
  let word := fixedWord "rewrite" keyword
  let keywordDoc := word.leaf around around.at
  let rulesAround := around.next word.trails 1
  let ruled := match rules with
    | RuleList list => ruleDocs target rulesAround list
    | Repeatedly repeatedly set =>
      let repeatedlyWord := fixedWord "repeatedly" repeatedly
      let setWords := set.words
      [
        repeatedlyWord.leaf rulesAround rulesAround.at,
        Doc.text " ",
        ruleSetDoc set (rulesAround.next repeatedlyWord.trails 1),
        ..targetDocs target (rulesAround.next (trailsBack setWords.reverse) (1 + setWords.length))
      ]
  let several := match rules with
    | RuleList [_, _, .._] => True
    | _ => False
  let ruledWords := [word, ..rules.words] ++ afterWords "at" target
  match body with
    | None =>
      if several then Doc.group (Doc.concat [keywordDoc, Doc.text " ", Nest 4 (Doc.concat ruled)])
      else Doc.concat [keywordDoc, Doc.text " ", ..ruled]
    | Some (thenComments, value) =>
      let thenWord := fixedWord "then" thenComments
      let offset := ruledWords.length
      let thenAround := around.next (trailsBack ruledWords.reverse) offset
      let head :=
        Doc.group
          (Doc.concat [
            keywordDoc,
            Doc.text " ",
            Nest 4 (Doc.concat ruled),
            Doc.text " ",
            thenWord.leaf thenAround thenAround.at
          ])
      Doc.group (Doc.concat [head, Nest 2 (Doc.concat [Line, value.el (around.next thenWord.trails (offset + 1))])])

--| `at` and its target after the last rule, if there; `around` is where
--| the `at` stands.
def targetDocs (target: Option (Comments, Expr)) (around: Around): List Doc := match target with
  | Some (atComments, value) =>
    let atWord := fixedWord "at" atComments
    [Doc.text " ", atWord.leaf around around.at, Doc.text " ", value.el (around.next atWord.trails 1)]
  | None => []

--| The rules, each with its comma and a `Line` after it, the last followed
--| by `at` and its target.
def ruleDocs (target: Option (Comments, Expr)) (around: Around): List RewriteRule → List Doc
  | [] => []
  | [last] =>
    let words := last.words
    [last.el around, ..targetDocs target (around.next (trailsBack words.reverse) words.length)]
  | [rule, ..rest] =>
    let words := rule.words
    [rule.el around, Closing ",", Line, ..ruleDocs target (around.next (trailsBack words.reverse) words.length) rest]

--| `[r1, <- r2]` after `repeatedly` (`comma_bracket` for `RewriteRules`):
--| flat if it fits, else each rule on a line at 2 and `]` alone; never
--| filled.
def ruleSetDoc (set: RuleSet) (around: Around): Doc := match set with
  | { open, rules, close, .. } =>
    let openWord := fixedWord "[" open
    let closeWord := fixedWord "]" close
    let words := set.words
    let holds := (words.filter Word.trails |> .length) > (if trailsBack words.reverse then 1 else 0)
    let closer := closeWord.leaf (around.next (trailsBack (words.reverse.drop 1)) (words.length - 1)) around.at
    let parts := [
      openWord.opening around closeWord,
      Nest 2 (Doc.concat (brokenRules around.inArm True openWord.trails (around.at + 1) rules)),
      SoftLine,
      closer
    ]
    Doc.group (Doc.concat (if holds then parts ++ [BreakParent] else parts))

--| A broken set's rules, as `brokenItems`: each starts a line, with its
--| comma after it.
def brokenRules (arm first before: Bool) (at: Nat): List RewriteRule → List Doc
  | [] => []
  | [rule] => [if first then SoftLine else Line, rule.el (itemAround arm before at)]
  | [rule, ..rest] =>
    let words := rule.words
    [
      if first then SoftLine else Line,
      rule.el (itemAround arm before at),
      Closing ",",
      ..brokenRules arm False (trailsBack words.reverse) (at + words.length) rest
    ]

--| A rule as the node it is in Rust's tree (`RewriteRule`, printed by
--| `join`): `<-` glued, a space, the rule.
def RewriteRule.el (rule: RewriteRule) (around: Around): Doc :=
  let inside := { around | hoisted = True }
  match rule with
    | { reverse = Some (less, minus), rule = value } =>
      let lessWord := fixedWord "<" less
      let minusWord := fixedWord "-" minus
      framedBy lessWord around
        (Doc.concat [
          lessWord.leaf inside around.at,
          minusWord.leaf (around.next lessWord.trails 1) (around.at + 1),
          Doc.text " ",
          value.el (around.next minusWord.trails 2)
        ])
    | { reverse = None, rule = value } => framedBy value.firstWord around (value.el inside)

--| `calc e0` and its steps, one a line at 2 (`calc`, S35); a blank line
--| above a step is kept. The first expression doesn't hug (`no_hug`): what
--| it opened downwards would share the steps' column, so the slice keeps
--| out a first expression that could (`hugsNowhere`).
def calcDoc (keyword: Comments) (first: Expr) (steps: List CalcStep) (around: Around): Doc :=
  let calcWord := fixedWord "calc" keyword
  Doc.concat [
    calcWord.leaf around around.at,
    Doc.text " ",
    first.el (around.next calcWord.trails 1),
    Nest 2 (Doc.concat (stepLines first.trails (around.at + 1 + first.size) around.inArm steps))
  ]

def stepLines (before: Bool) (at: Nat) (arm: Bool): List CalcStep → List Doc
  | [] => []
  | [step, ..rest] =>
    let words := step.words
    [
      HardLine,
      step.el { before, hoisted = False, item = True, at, inArm = arm },
      ..stepLines (trailsBack words.reverse) (at + words.length) arm rest
    ]

def CalcStep.words (step: CalcStep): List Word := match step with
  | { underscore, relation, operand, proof } =>
    [fixedWord "_" underscore, relation, ..operand.words] ++ afterWords ":=" proof

def stepsWords: List CalcStep → List Word
  | [] => []
  | [step, ..rest] => step.words ++ stepsWords rest

--| `_ R e := proof` (`calc_step`, S35): on one line if it fits, otherwise
--| the proof below at 2 as after a declaration's `:=`; `_ R e` itself
--| breaks at 2. A step is a node in Rust's tree, framed by its `_`.
def CalcStep.el (step: CalcStep) (around: Around): Doc := match step with
  | { underscore, relation, operand, proof } =>
    let underscoreWord := fixedWord "_" underscore
    let inside := { around | hoisted = True }
    let relationDoc := Doc.concat [
      underscoreWord.leaf inside around.at,
      Doc.text " ",
      relation.leaf (around.next underscoreWord.trails 1) (around.at + 1),
      Doc.text " ",
      operand.el (around.next relation.trails 2)
    ]
    let doc := match proof with
      | None => relationDoc
      | Some (colonEq, value) =>
        let assign := fixedWord ":=" colonEq
        let assignAt := 2 + operand.size
        let (_, choice) := bodyAfter value assign (around.next assign.trails (assignAt + 1)) False
        Doc.concat [
          Nest 2 relationDoc,
          Doc.text " ",
          assign.leaf (around.next operand.trails assignAt) (around.at + assignAt),
          choice
        ]
    framedBy underscoreWord around doc
