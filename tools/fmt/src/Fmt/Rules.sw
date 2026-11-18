--| The rules for slice 1's constructs (docs/proposals/
--| self-hosted-fmt-proof-plan.md §1.2): how a declaration of the tidied
--| tree becomes a layout document (`Std.Doc`), ported from
--| `crates/fmt/src/printer/rules.rs` function by function for the parts
--| slice 1 meets: `decl` and `header` for `def name: T := e`, `body_after`,
--| `app` with `last_argument` and `fill_call`, `chain` for `Binary` and
--| `Arrow`, `paren`, `comma_bracket` for tuples and lists, and `join` for
--| `Prefix`, with `el`, `leaf`, `leading` and `trailing` for comments.
--|
--| The Rust rules read a token's neighbours by its index in the file.
--| Here what a rule needs of a token's surroundings travels down the tree
--| as an `Around`: whether the code before it ends its line with a comment,
--| whether an enclosing element already printed its own-line comments,
--| whether it starts an item of a comma bracket, and the number of tokens
--| before it in the declaration, which gives each `IdGroup` and each
--| `Mark` a key of its own as the Rust token index does.
--|
--| A node outside slice 1 prints as nothing: the caller asks `within1`
--| first (`Fmt.Slice1`).

namespace Fmt
import Std (Bool, Doc, List, Nat, Option, Text)
import Std.Doc (..)
import Syntax (BindingKind, Comments, DefKind, Expr, Header, InfixKind, Note, Param, Pattern, Row, Tok, Word)

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
  at: Nat
}

--| A later child of an element, `skipped` tokens after the element's
--| first: none of the first token's facts carry to it.
def Around.next (around: Around) (before: Bool) (skipped: Nat): Around :=
  { before, hoisted = False, item = False, at = around.at + skipped }

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
  | [note, ..rest] => [Doc.text note.text, ..laterCloserNotes rest]

def laterCloserNotes: List Note → List Doc
  | [] => []
  | [note, ..rest] =>
    [HardLine] ++ (if note.blankBefore then [Blank] else []) ++ [Doc.text note.text] ++ laterCloserNotes rest

--| Own-line comments, each on its line; a blank line above the first is
--| kept only before an item (`keep`).
def notesAbove (keep: Bool): List Note → List Doc
  | [] => []
  | [note, ..rest] =>
    (if note.blankBefore && keep then [Blank] else []) ++ [Doc.text note.text, HardLine] ++ notesAbove True rest

--| Own-line comments and kept blank lines before a token (`leading`).
--| `key` is its bracket pair's, for a closer.
def Word.leading (word: Word) (around: Around) (key: Nat): List Doc :=
  let comments := word.comments
  if around.hoisted then []
  else if comments.above.isEmpty then (if around.item && comments.blankBefore then [BreakParent, Blank] else [])
  else if isCloserText word.text then
    [BreakParent, Nest 2 (Doc.concat [LineStartHere, ..closerNotes comments.above]), CloserLine key]
  else
    [BreakParent, LineStart, ..notesAbove around.item comments.above] ++ (if comments.blankBefore then [Blank] else [])

--| A token on its own (`leaf`). A closer after code that ends its line
--| with a comment, and with a comment of its own, keeps a line of its own
--| (S39): printed before the waiting comment, it would leave two comments
--| on one line.
def Word.leaf (word: Word) (around: Around) (key: Nat): Doc :=
  let ownLine := isCloserText word.text && !word.noted && around.before && word.trails
  Doc.concat (word.leading around key ++ (if ownLine then [HardLine] else []) ++ [piece word.text] ++ word.trailing)

--| An opening bracket: with a `Mark` when own-line comments come before
--| its closer, which may then go back to this line's indentation.
def Word.opening (word: Word) (around: Around) (closer: Word): Doc :=
  let mark := if closer.noted then [Mark around.at] else []
  Doc.concat (word.leading around around.at ++ mark ++ [piece word.text] ++ word.trailing)

-- What rules read of an expression's tokens.

--| The expression's tokens in order, commas left out.
def Expr.words: Expr → List Word
  | Atom _ word => [word]
  | Paren open inner close => [open, ..inner.words] ++ [close]
  | Tuple open items _ close => [open, ..itemsWords items] ++ [close]
  | ListOf open items _ close => [open, ..itemsWords items] ++ [close]
  | App head arguments => head.words ++ itemsWords arguments
  | Infix _ left operator right => left.words ++ [operator, ..right.words]
  | Prefix operator operand => [operator, ..operand.words]
  | Binding _ keyword params arrow body => optionWords keyword ++ paramsWords params ++ [arrow, ..body.words]
  | Effect row result => rowWords row ++ result.words
  | _ => []

def itemsWords: List Expr → List Word
  | [] => []
  | [item, ..rest] => item.words ++ itemsWords rest

def optionWords: Option Word → List Word
  | Some word => [word]
  | None => []

def paramsWords: List Param → List Word
  | [] => []
  | [NameParam word, ..rest] => [word, ..paramsWords rest]
  | [PatternParam (PatternWord _ word), ..rest] => [word, ..paramsWords rest]
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
    | Infix InfixBinary left operator right => expr.framed around (chain expr.chainLevel left operator right inside)
    | Infix InfixArrow left operator right => expr.framed around (chain expr.chainLevel left operator right inside)
    | Prefix operator operand =>
      expr.framed around
        (Doc.concat [
          operator.leaf inside around.at,
          prefixGap operator operand,
          operand.el (around.next operator.trails 1)
        ])
    | Binding BindsLambda _ params arrow body =>
      let (flat, _) := lambdaBoth params arrow body inside
      expr.framed around flat
    | Binding BindsForall (Some keyword) params arrow body =>
      expr.framed around (quantifier (existential := False) keyword params arrow body inside)
    | Binding BindsExists (Some keyword) params arrow body =>
      expr.framed around (quantifier (existential := True) keyword params arrow body inside)
    | Effect row result => expr.framed around (effectDoc row result inside)
    | _ => Nothing

--| A node's document with its first token's own-line comments before it,
--| displaced when a comment puts its first line below where its
--| construct would.
def Expr.framed (expr: Expr) (around: Around) (doc: Doc): Doc := framedBy expr.firstWord around doc

def framedBy (first: Word) (around: Around) (doc: Doc): Doc :=
  let placed := if first.noted || around.before then Displaced doc else doc
  Doc.concat [Doc.concat (first.leading around around.at), placed]

-- Binders.

--| A parameter of a lambda or quantifier: a name, `_`, or a group.
def Param.el (param: Param) (around: Around): Doc := match param with
  | NameParam word => word.leaf around around.at
  | PatternParam (PatternWord _ word) => word.leaf around around.at
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
      spaced (nameDocs open.trails (around.at + 1) names),
      colon.leaf (around.next lastName.trails (1 + count)) (around.at + 1 + count),
      Doc.text " ",
      annotation.el (around.next colon.trails (2 + count)),
      close.leaf (around.next annotation.trails (2 + count + annotation.size)) around.at
    ]
    framedBy open around doc
  | _ => Nothing

def nameDocs (before: Bool) (at: Nat): List Word → List Doc
  | [] => []
  | [name, ..rest] => [name.leaf { before, hoisted = False, item = False, at } at, ..nameDocs name.trails (at + 1) rest]

def paramTrails (param: Param): Bool := trailsBack (paramsWords [param]).reverse

def paramNoted (param: Param): Bool := (paramsWords [param]).headOr Word.none |> .noted

--| A lambda (`lambda_both`, S30), and the same lambda opened downwards for
--| a hug or the `:=` line (S23, D3568): the body after `=>` if it fits,
--| else below at 2. Only the first breaks its parameters, filling lines
--| at 4 like a header's (S22), when no comment sits among them.
def lambdaBoth (params: List Param) (arrow: Word) (body: Expr) (around: Around): (Doc, Doc) :=
  let docs := paramDocs around params
  let words := paramsWords params
  let size := words.length
  let arrowDoc := arrow.leaf (around.next (trailsBack words.reverse) size) (around.at + size)
  let bodyDoc := body.el (around.next arrow.trails (size + 1))
  let items := docs ++ [arrowDoc]
  let head := spaced items
  let commented := (params.drop 1 |> .any paramNoted) || params.any paramTrails || arrow.noted
  let filled := if params.length < 2 || commented then head else Nest 4 (Fill items)
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
          ++ rowItems openWord.trails (around.at + 1) abilities
          ++ [closeWord.leaf (around.next (trailsBack ((rowWords row).reverse.drop 1)) (size - 1)) around.at])
    Doc.concat [framedBy openWord around rowDoc, Doc.text " ", result.el (around.next closeWord.trails size)]
  | _ => Nothing

--| A row's abilities, a comma and a space between each two.
def rowItems (before: Bool) (at: Nat): List Expr → List Doc
  | [] => []
  | [item] => [item.el { before, hoisted = False, item = False, at }]
  | [item, ..rest] => [
    item.el { before, hoisted = False, item = False, at },
    Closing ",",
    Doc.text " ",
    ..rowItems item.trails (at + item.size) rest
  ]

--| `( … )` (`paren`): nothing between the brackets and what they hold.
def parenDoc (open: Word) (inner: Expr) (close: Word) (around: Around): Doc := Doc.concat [
  open.opening around close,
  inner.el (around.next open.trails 1),
  close.leaf (around.next inner.trails (1 + inner.size)) around.at
]

-- Comma brackets.

--| A tuple or list (`comma_bracket`): flat if it fits, else broken.
def commaBracket (list: Bool) (open: Word) (items: List Expr) (close: Word) (around: Around): Doc :=
  Doc.group (bracketContent list open items close around)

--| Where an item stands: after the opener (`before` says whether that
--| ends its line with a comment), then after a comma.
def itemAround (before: Bool) (at: Nat): Around := { before, hoisted = False, item = True, at }

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
  if items.isEmpty then Doc.concat [prefix, closer]
  else if list && !whole.holdsTrailingComment && items.all Expr.plainItem then
    Doc.concat [prefix, Nest 2 (Fill (cells open.trails (around.at + 1) items)), closer]
  else
    let parts := [prefix, Nest 2 (Doc.concat (brokenItems True open.trails (around.at + 1) items)), SoftLine, closer]
    Doc.concat (if whole.holdsTrailingComment then parts ++ [BreakParent] else parts)

--| Whether the code before a bracket's closer, closers aside, ends its line
--| with a comment: what its last item ends with.
def Expr.trailsBeforeClose (expr: Expr): Bool := trailsBack (expr.words.reverse.drop 1)

--| A filled list's cells: each item with its comma.
def cells (before: Bool) (at: Nat): List Expr → List Doc
  | [] => []
  | [item] => [item.el (itemAround before at)]
  | [item, ..rest] => [Doc.concat [item.el (itemAround before at), Closing ","], ..cells False (at + item.size) rest]

--| A broken bracket's items: each starts a line, with its comma after it.
def brokenItems (first before: Bool) (at: Nat): List Expr → List Doc
  | [] => []
  | [item] => [if first then SoftLine else Line, item.el (itemAround before at)]
  | [item, ..rest] => [
    if first then SoftLine else Line,
    item.el (itemAround before at),
    Closing ",",
    ..brokenItems False False (at + item.size) rest
  ]

-- Calls.

def optionList (option: Option Doc): List Doc := match option with
  | Some doc => [doc]
  | None => []

--| A call's document, and its hug if its last argument can hug (S23).
type Applied = { doc: Doc, hug: Option Doc }

--| A call's last argument and its hug, the same argument opening
--| downwards (`last_argument`): a tuple, a list or a lambda in brackets
--| can hug.
def lastArgument (argument: Expr) (around: Around): (Doc, Option Doc) := match argument with
  | Tuple open items _ close => huggedBracket False open items close around
  | ListOf open items _ close => huggedBracket True open items close around
  | Paren open (Binding BindsLambda _ params arrow body) close => huggedLambda open params arrow body close around
  | _ => (argument.el around, None)

--| `(x => body)` as a last argument: the lambda as it is, and opened,
--| its body below at 2.
def huggedLambda (open: Word) (params: List Param) (arrow: Word) (body: Expr) (close: Word) (around: Around):
    (Doc, Option Doc) :=
  let lambda := Binding BindsLambda None params arrow body
  let leading := Doc.concat (open.leading around around.at)
  let openDoc := open.opening { around | hoisted = True } close
  let closeDoc := close.leaf (around.next lambda.trails (1 + lambda.size)) around.at
  let (flat, opened) := lambdaBoth params arrow body (around.next open.trails 1)
  (Doc.concat [leading, openDoc, flat, closeDoc], Some (Doc.concat [leading, openDoc, opened, closeDoc]))

def huggedBracket (list: Bool) (open: Word) (items: List Expr) (close: Word) (around: Around): (Doc, Option Doc) :=
  let leading := Doc.concat (open.leading around around.at)
  let content := bracketContent list open items close { around | hoisted = True }
  (Doc.concat [leading, Group content content.forcesBreak], Some (Doc.concat [leading, Group content True]))

--| Whether an argument may stay on the call's line when the others go
--| below (`simple`): a token, `[]`, or a prefix operator on a token.
def Expr.simple: Expr → Bool
  | Atom _ _ => True
  | Tuple _ items _ _ => items.isEmpty
  | ListOf _ items _ _ => items.isEmpty
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
def argumentDocs (previous: Expr) (at: Nat): List Expr → (List Doc, Option (Doc, Option Doc))
  | [] => ([], None)
  | [argument] => ([], Some (lastArgument argument { before = previous.trails, hoisted = False, item = False, at }))
  | [argument, ..rest] =>
    let (docs, last) := argumentDocs argument (at + argument.size) rest
    ([argument.el { before = previous.trails, hoisted = False, item = False, at }, ..docs], last)

--| A call (`app`, S23, D3567 (c)): on one line if it fits; else hugging its
--| last argument if that can and the line up to it fits; else the function
--| and its leading simple arguments on the line and each other argument on
--| its own line at 2. Plain arguments only (all simple) fill lines at 4
--| (D3569). The `IdGroup` of a filled front is keyed by the call's first
--| token, which no other call in the declaration starts with.
def appDocs (head: Expr) (arguments: List Expr) (around: Around): Applied :=
  let headDoc := head.el around
  let (front, last) := argumentDocs head (around.at + head.size) arguments
  let (lastDoc, hug) := last.getOrElse (Nothing, None)
  let docs := [headDoc, ..front] ++ [lastDoc]
  let all := spaced docs
  let keep := 1 + keptFront head arguments
  if keep == docs.length then { doc = if commentBetween head arguments then all else Nest 4 (Fill docs), hug = None }
  else
    let hugged := hug.map (open => Doc.concat [Flatten (spaced [headDoc, ..front]), Doc.text " ", open])
    let fillFront := keep > 2 && !commentBetween head (arguments.take (keep - 1))
    let id := around.at + 1
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
  | Equals => Some 4
  | EqEq => Some 4
  | NotEq => Some 4
  | Lt => Some 4
  | Le => Some 4
  | Gt => Some 4
  | Ge => Some 4
  | PlusPlus => Some 5
  | Plus => Some 6
  | Minus => Some 6
  | Star => Some 7
  | Slash => Some 7
  | Percent => Some 7
  | PipeGt => Some 8
  | _ => None

--| An operator's level, by its spelling.
def operatorLevel (operator: Word): Option Nat := Option.flatMap (operatorTok operator.text) Tok.chainLevel

--| A chain node's operator level, for `Binary` and `Arrow`.
def Expr.chainLevel: Expr → Option Nat
  | Infix InfixBinary _ operator _ => operatorLevel operator
  | Infix InfixArrow _ operator _ => operatorLevel operator
  | _ => None

--| Whether a node is part of the chain at `level`: a `Binary` or `Arrow`
--| of that level (`chain_parts`).
def Expr.inChain (expr: Expr) (level: Option Nat): Bool := match expr with
  | Infix InfixBinary _ _ _ => level.isSome && expr.chainLevel == level
  | Infix InfixArrow _ _ _ => level.isSome && expr.chainLevel == level
  | _ => False

--| An operator chain (`chain`, S27, S29): on one line if it fits,
--| otherwise each operator of its level starting a line at 2. The nested
--| chains of the same level are flattened into this one (`chain_parts`):
--| the first operand is the head, each operator and operand after it a
--| line of the tail.
def chain (level: Option Nat) (left: Expr) (operator: Word) (right: Expr) (around: Around): Doc :=
  match chainLinks level left operator right around with
    | [head, ..tail] => Doc.group (Doc.concat [head, Nest 2 (Doc.concat tail)])
    | [] => Nothing

--| The flattened chain's docs: the first operand's, then for each operator
--| a `Line`, the operator, a space and its operand.
def chainLinks (level: Option Nat) (left: Expr) (operator: Word) (right: Expr) (around: Around): List Doc :=
  let operatorAround := around.next left.trails left.size
  let rightAround := around.next operator.trails (left.size + 1)
  linkDocs level left around
    ++ [Line, operator.leaf operatorAround operatorAround.at, Doc.text " "]
    ++ linkDocs level right rightAround

--| An operand of the chain: its docs if it is a chain of the same level,
--| else the element.
def linkDocs (level: Option Nat) (expr: Expr) (around: Around): List Doc := match expr with
  | Infix InfixBinary left operator right =>
    if expr.inChain level then chainLinks level left operator right around else [expr.el around]
  | Infix InfixArrow left operator right =>
    if expr.inChain level then chainLinks level left operator right around else [expr.el around]
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
  let start: Around := { before = False, hoisted = True, item = False, at = 0 }
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
  let (below, choice) := bodyAfter value assign (start.next assign.trails (colonAt + 2 + result.size))
  Doc.concat [
    IdGroup 0 headerDoc (headerDoc.forcesBreak || inside),
    Doc.text " ",
    assign.leaf (start.next result.trails (colonAt + 1 + result.size)) (colonAt + 1 + result.size),
    IfBroken 0 below choice
  ]

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

def Expr.isSort: Expr → Bool
  | Atom TypeU _ => True
  | Atom PropU _ => True
  | Universe _ _ => True
  | _ => False

--| Whether a type reads as a proposition (`is_proposition`).
def propositionIn (earlier: List Text): Expr → Bool
  | Infix InfixBinary _ operator _ => (operatorTok operator.text).any Tok.relation
  | Infix InfixArrow _ _ right => propositionIn earlier right
  | Infix InfixMembership _ _ _ => True
  | Infix InfixIff _ _ _ => True
  | Chain _ _ => True
  | Binding BindsExists _ _ _ _ => True
  | Binding BindsForall _ _ _ body => propositionIn earlier body
  | Prefix operator _ => operatorTok operator.text == Some Bang
  | Paren _ inner _ => propositionIn earlier inner
  | App (Atom _ head) arguments =>
    capitalised head.text && arguments.any (argument => argument.words.any (word => earlier.contains word.text))
  | _ => False

--| The operators whose application is a proposition.
def Tok.relation: Tok → Bool
  | Equals => True
  | NotEq => True
  | Lt => True
  | Le => True
  | Gt => True
  | Ge => True
  | AndAnd => True
  | OrOr => True
  | EqEq => True
  | _ => False

--| Whether a name's last part starts with a capital: `Even`, `List.Sorted`.
def capitalised (name: Text): Bool :=
  name.splitOn "." |> .reverse |> .headOr "" |> .toList |> .headOr ' ' |> .isAsciiUppercase

--| What follows a `:=` (`body_after`, S12, S17): the doc for a header that
--| broke (the value below at 2), and the choice for one that didn't: on the
--| line if all of it fits; a tuple, list or hugging call below if it fits
--| on one line there (D3571); a tuple or list on the line, a call hugging
--| its last argument, or a lambda with its body below (D3568); else below.
def bodyAfter (value: Expr) (assign: Word) (around: Around): (Doc, Doc) :=
  let doc := value.el around
  let below := Nest 2 (Doc.concat [HardLine, doc])
  if assign.trails || value.noted then (below, below)
  else
    let inside := { around | hoisted = True }
    let hug := match value with
      | App head arguments => (appDocs head arguments inside).hug
      | _ => None
    let opens := match value with
      | Tuple _ _ _ _ => True
      | ListOf _ _ _ _ => True
      | _ => False
    let lambda := match value with
      | Binding BindsLambda _ params arrow body =>
        let (_, opened) := lambdaBoth params arrow body inside
        Some opened
      | _ => None
    let oneLineBelow := if opens || hug.isSome then [OneLineBelow doc] else []
    let onLine :=
      if opens then [Doc.concat [Doc.text " ", doc]]
      else optionList ((lambda.orElse hug).map (open => Doc.concat [Doc.text " ", open]))
    (below, Choice ([Flatten (Doc.concat [Doc.text " ", doc])] ++ oneLineBelow ++ onLine ++ [below]))
