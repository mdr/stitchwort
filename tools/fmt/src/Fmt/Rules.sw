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
import Syntax (Comments, Expr, Header, InfixKind, Note, Tok, Word)

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
  | _ => []

def itemsWords: List Expr → List Word
  | [] => []
  | [item, ..rest] => item.words ++ itemsWords rest

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
    | _ => Nothing

--| A node's document with its first token's own-line comments before it,
--| displaced when a comment puts its first line below where its
--| construct would.
def Expr.framed (expr: Expr) (around: Around) (doc: Doc): Doc :=
  let first := expr.firstWord
  let placed := if first.noted || around.before then Displaced doc else doc
  Doc.concat [Doc.concat (first.leading around around.at), placed]

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
--| downwards (`last_argument`): a tuple or list can hug.
def lastArgument (argument: Expr) (around: Around): (Doc, Option Doc) := match argument with
  | Tuple open items _ close => huggedBracket False open items close around
  | ListOf open items _ close => huggedBracket True open items close around
  | _ => (argument.el around, None)

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

--| `def name: T := e` (`decl`, `header`, S6 to S12): the header in an
--| `IdGroup`, then the body after `:=` as `bodyAfter` chooses, or below
--| at 2 when the header broke. The declaration's first token's own-line
--| comments are the file's to print.
def defDoc (header: Header) (colonEq: Comments) (value: Expr): Doc :=
  let keyword := fixedWord "def" header.keyword
  let colon := fixedWord ":" header.colon
  let assign := fixedWord ":=" colonEq
  let result := header.result
  let start: Around := { before = False, hoisted = True, item = False, at = 0 }
  let nameAround := start.next keyword.trails 1
  let colonAround := start.next header.name.trails 2
  let resultAround := start.next colon.trails 3
  let typeDoc := result.el resultAround
  let head := Doc.concat [keyword.leaf start 0, Doc.text " ", header.name.leaf nameAround 1]
  let typed := if colon.trails then [Nest 4 (Doc.concat [HardLine, typeDoc])] else [Doc.text " ", Nest 4 typeDoc]
  let headerDoc := Doc.concat ([head, colon.leaf colonAround 2] ++ typed)
  let inside := keyword.trails || colon.trails || (result.words.reverse.drop 1 |> .any Word.trails)
  let (below, choice) := bodyAfter value assign (start.next assign.trails (4 + result.size))
  Doc.concat [
    IdGroup 0 headerDoc (headerDoc.forcesBreak || inside),
    Doc.text " ",
    assign.leaf (start.next result.trails (3 + result.size)) (3 + result.size),
    IfBroken 0 below choice
  ]

--| What follows a `:=` (`body_after`, S12, S17): the doc for a header that
--| broke (the value below at 2), and the choice for one that didn't: on the
--| line if all of it fits; a tuple, list or hugging call below if it fits
--| on one line there (D3571); a tuple or list on the line, or a call
--| hugging its last argument; else below.
def bodyAfter (value: Expr) (assign: Word) (around: Around): (Doc, Doc) :=
  let doc := value.el around
  let below := Nest 2 (Doc.concat [HardLine, doc])
  if assign.trails || value.noted then (below, below)
  else
    let hug := match value with
      | App head arguments => (appDocs head arguments { around | hoisted = True }).hug
      | _ => None
    let opens := match value with
      | Tuple _ _ _ _ => True
      | ListOf _ _ _ _ => True
      | _ => False
    let oneLineBelow := if opens || hug.isSome then [OneLineBelow doc] else []
    let onLine :=
      if opens then [Doc.concat [Doc.text " ", doc]] else optionList (hug.map (open => Doc.concat [Doc.text " ", open]))
    (below, Choice ([Flatten (Doc.concat [Doc.text " ", doc])] ++ oneLineBelow ++ onLine ++ [below]))
