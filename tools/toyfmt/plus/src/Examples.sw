--| The sketch's definitions on small cases, each checked by computing.

namespace Toy.Plus.Examples
import Toy.Plus (..)
import Toy.Plus.Proofs (..)
import Toy.Syntax (Comment, Comments, Lexed, Operator, Spaced, Token, Trivia, lex)
import Std (Bool, Eq, List, Nat, NonEmptyList, Option, Parse, Result, Text)

--| Where each token's trailing comment is after rule N, by the token's
--| offset, and the comments above each token that has some.
def trailingAt (source: Text): List (Nat, Text) := match lex source with
  | Err _ => []
  | Ok lexed =>
    lexed.settled.tokens.filterMap (token => token.value.trailing.map (comment => (token.offset, comment.value.text)))

def allComments (source: Text): List Text := match lex source with
  | Err _ => []
  | Ok lexed => (commentsOf lexed.settled.tokens lexed.settled.endTrivia).map (comment => comment.text)

--| A comment after a closer belongs to the last token before it.
theorem afterCloser: trailingAt "[a, b] -- c" = [(4, "-- c")] := byComputing

--| Through several closers and a comma.
theorem afterClosers: trailingAt "f(g(x)), -- c\n" = [(4, "-- c")] := byComputing

--| Never onto a token that has a comment: `place_comments` loses `-- c1`
--| here. The second stays on the first `)`, which starts no line.
theorem keepsBoth: trailingAt "g(f(x) -- c1\n) -- c2" = [(4, "-- c1"), (5, "-- c2")] := byComputing

theorem losesNone: allComments "g(f(x) -- c1\n) -- c2" = ["-- c1", "-- c2"] := byComputing

--| A comma's own-line comments go above the token after it.
theorem commaAbove: allComments "[a\n-- c\n, b -- d\n]" = ["-- c", "-- d"] := byComputing

def none: Comments := Comments.none

def a: Expr := Var "a" none

def b: Expr := Var "b" none

def c: Expr := Var "c" none

def pair (inner: Expr): Expr := Bracketed none inner none

def inStatement: Position := { bracketed = False, slot = Whole }

--| `(a * b) + c` loses its pair; `(a + b) * c` keeps it.
theorem dropsTighter: (Binary Plus none (pair (Binary Times none a b)) c).walk dropPair inStatement
      = Binary Plus none (Binary Times none a b) c :=
  byComputing

theorem keepsLooser: (Binary Times none (pair (Binary Plus none a b)) c).walk dropPair inStatement
      = Binary Times none (pair (Binary Plus none a b)) c :=
  byComputing

--| Nested pairs go in one run.
theorem dropsNested: (pair (pair (pair a))).walk dropPair inStatement = a := byComputing

--| `a - (b - c)` keeps its pair, `(a - b) - c` loses it.
theorem keepsRight: (Binary Minus none a (pair (Binary Minus none b c))).walk dropPair inStatement
      = Binary Minus none a (pair (Binary Minus none b c)) :=
  byComputing

theorem dropsLeft: (Binary Minus none (pair (Binary Minus none a b)) c).walk dropPair inStatement
      = Binary Minus none (Binary Minus none a b) c :=
  byComputing

def noted: Comments := { above = [{ text = "-- why" }], after = None }

def oneLine (value: Expr): Body := { statements = [{ blankBefore = False, line = Bare value }] }

--| An `if` whose branch has a comment above it can be read only inside
--| brackets (outside, the comment would make the branch a block), so its
--| pair stays in a statement and goes inside another pair.
def notedIf: Expr := If none a none (oneLine (Var "b" noted)) none (oneLine c)

theorem keepsNotedIf: (pair notedIf).walk dropPair inStatement = pair notedIf := byComputing

theorem dropsNotedIfInside: (pair (pair notedIf)).walk dropPair inStatement = pair notedIf := byComputing

def int: TypeExpr := TypeName "Int" none

def named (name: Text): NonEmptyList Named := NonEmptyList.singleton { name, comments = none }

--| `(w: Int, h: Int)` merges to `(w h: Int)`, and both mean the same.
theorem merges: mergeGroups [Typed (named "w") none int, Typed (named "h") none int]
      = [Typed { head = { name = "w", comments = none }, tail = [{ name = "h", comments = none }] } none int] :=
  byComputing

theorem mergedMeansSame: plainGroups (mergeGroups [Typed (named "w") none int, Typed (named "h") none int])
      = plainGroups [Typed (named "w") none int, Typed (named "h") none int] :=
  byComputing

--| `(w: (Int), h: Int)` merges only once its brackets are gone.
theorem mergeNeedsBrackets: mergeGroups [
      Typed (named "w") none (TypeBracketed none int none),
      Typed (named "h") none int
    ]
      = [Typed (named "w") none (TypeBracketed none int none), Typed (named "h") none int] :=
  byComputing

--| Route (A): a comment after `)` that rule N would have moved is moved.
theorem closedMoves: closed none a { above = [], after = Some { text = "-- c" } }
      = Bracketed none (Var "a" { above = [], after = Some { text = "-- c" } }) none :=
  byComputing
