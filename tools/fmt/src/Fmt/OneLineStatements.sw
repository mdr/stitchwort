--| `declElementsOneLine1` (`Fmt.TopStatements`) in two halves that meet at a test on the tree, `Decl.edgeQuiet1`
--| (SW-4096; docs/reviews/SW-4096-one-line-elements.md):
--|
--| - `edgeQuietOneLine1` (open, the link): a slice 1 declaration that prints on one line is `edgeQuiet1`. It reads the
--|   printed line starts back to the tree's comments.
--| - `edgeElements1` (proved in `Fmt.EdgeDeclProofs`, the hangs): an `edgeQuiet1` slice 1 declaration meets
--|   `DeclElements`. It says nothing of the printed text.
--|
--| `edgeQuiet1`: the only comments in the type and the value are at their edges. One may follow the last word that
--| is no closer (the printer writes it after the closers that follow, so it ends the line), and the value's first
--| word may have comments above it (it then starts the value's line, which `oneLine1` allows). The test is made of
--| the calmed type and value (`Expr.calm`): a blank line the rules never read is no part of it, and the driver's
--| tree is not calmed.

namespace Fmt.OneLineStatements
import Std (Bool, List, Option, Text)
import Syntax (Decl, DefBody, Expr, SourceFile, Word)
import Fmt (..)
import Fmt.Driver1 (..)
import Fmt.OutputStatements (tidiedOf)
import Fmt.ExprHangProofs (..)
import Fmt.DeclFactsProofs (DeclElements)
import Fmt.TreeJoinProofs (lexKind)

-- The class.

--| A token of an edge-quiet expression. Its first token (`lead`) may have own-line comments above it, and a blank
--| line kept below them; any other has neither. The last token that is no closer (`end`) may have a comment after it;
--| any other has none.
def Word.edge1 (word: Word) (lead end: Bool): Bool :=
  (if lead then word.noted || !word.comments.blankBefore else !word.noted && !word.comments.blankBefore)
    && (end || !word.trails)

--| An expression quiet (`Expr.quiet1`) but at its edges: with `lead`, its first token may have own-line comments
--| above it; with `end`, its last token that is no closer may have a comment after it (an empty list's is its
--| opener). With neither it is `quiet1`; `lead` alone differs from `leadQuiet1` only in the blank line below the
--| comments. Every call has an argument, as in `quiet1`.
def Expr.edgeQuiet1 (expr: Expr) (lead end: Bool): Bool := match expr with
  | Atom _ word => word.edge1 lead end
  | Paren open inner close => open.edge1 lead False && inner.edgeQuiet1 False end && close.quiet1
  | Tuple open items _ close => open.edge1 lead False && lastEdgeQuiet1 end items && close.quiet1
  | ListOf open items _ close => open.edge1 lead (end && items.isEmpty) && lastEdgeQuiet1 end items && close.quiet1
  | App head arguments => !arguments.isEmpty && head.edgeQuiet1 lead False && lastEdgeQuiet1 end arguments
  | Infix _ left operator right => left.edgeQuiet1 lead False && operator.quiet1 && right.edgeQuiet1 False end
  | Prefix operator operand => operator.edge1 lead False && operand.edgeQuiet1 False end
  | _ => False

--| Items or arguments, quiet but the last, whose last token that is no closer may have a comment after it (`end`).
def lastEdgeQuiet1 (end: Bool) (items: List Expr): Bool := match items with
  | [] => True
  | [last] => last.edgeQuiet1 False end
  | [expr, ..rest] => expr.quiet1 && lastEdgeQuiet1 end rest

--| A declaration whose type and value, calmed, hold comments only at their edges: one after the type's last token
--| that is no closer, and in the value that and own-line comments above its first token. Comments above and after
--| the name, the `:` and the `:=` are not looked at.
def Decl.edgeQuiet1: Decl → Bool
  | Definition [] header (Assigned _ value) =>
    (header.result.calm False).edgeQuiet1 False True && (value.calm False).edgeQuiet1 True True
  | _ => False

-- The two halves.

--| The link (open, SW-4096's A): a slice 1 declaration that prints on one line (`oneLine1`) is `edgeQuiet1`.
--|
--| Proof idea, without `standsOfDoc` (it needs `DeclHangs`, which this feeds): by contraposition, on the printed
--| pieces. `printedSpellsSettled` says the printed words less the closers are the tree's tokens and comments in
--| order, and less the comments its tokens, closers and commas in order; `CommentsEnd` (`printedJoins`) that a line
--| break follows each printed comment, so the next token laid (`Laid.lay`, `Decl.leaves1`) has `lineStart`. A
--| comment above a token is printed before it, so that token starts a line; a comment after a token that is not the
--| type's or value's last but for closers is printed before a later token of the same part, which starts a line
--| (`settled1`'s `homedBack` puts a closer's comment below one on the code before it, so that closer starts a line
--| too). `onLine1` allows a line start only at the `:=` and the value's first token, which leaves `edge1`'s cases.
--| The blank lines: a calmed flag left set is one the rules read (`Word.leading`), as a `Blank` after a line start.
theorem edgeQuietOneLine1 ∀ (decl: Decl)
    (within: decl.within1 = True)
    (shaped: decl.shaped1 = True)
    (settled: decl.settled1 = True)
    (lexical: decl.lexical1 = True)
    (oneLine: decl.oneLine1 = True):
    decl.edgeQuiet1 = True :=
  ?

-- Sources the two statements apply to (D3684).

--| The halves' hypotheses and the test between them, run on a source's printed tree: the four tree facts, each
--| declaration on one line, and each `edgeQuiet1`.
def edgeHoldsOn (source: Text): Bool := match tidiedOf source with
  | None => False
  | Some file =>
    file.within1 && file.shaped1 && file.settled1 && file.lexical1 && file.oneLine1 && file.decls.all Decl.edgeQuiet1

--| A source in the slice that fails both the one-line test and `edgeQuiet1`: a comment the test must refuse.
def edgeFailsOn (source: Text): Bool := match tidiedOf source with
  | None => False
  | Some file =>
    file.within1 && file.shaped1 && file.settled1 && file.lexical1 && !file.oneLine1 && !file.decls.all Decl.edgeQuiet1

--| Comments after the last tokens with closers after them, in the type and in a list (`def x: F (a) -- c`, then
--| `:=`, then `[b, d] -- e`).
theorem heldClosersEdge: edgeHoldsOn "def x: F (a -- c\n  ) := [b, d -- e\n  ]\n" = True := byComputing

--| A comment after the type, one after the `:=`, two above the value's first token with a blank line kept below
--| them, and one after a tuple's last item.
theorem everyEdge: edgeHoldsOn "def x: F a -- c\n  := -- d\n  -- e\n  -- f\n\n  g (b, c -- h\n  )\n" = True :=
  byComputing

--| Nested closers after the comment, a comment after an empty list's opener, after an operand and after a sign's.
theorem deepEdges: edgeHoldsOn
        "def x: T := f (g [a -- c\n  ])\ndef y: T := [ -- c\n  ]\ndef z: A -> B -- c\n  := a + b -- c\ndef w: T := -a -- c\n"
      = True :=
  byComputing

--| A blank line the rules never read (above an argument) is no part of the test.
theorem unreadBlankEdge: edgeHoldsOn "def x: T := f\n\n  [a -- c\n  ]\n" = True := byComputing

--| Refused: a comment above a later token of the value, above the type's first token, after an argument that is
--| not the last, after a closer below a comment, and above a closer.
theorem insideFails: (edgeFailsOn "def x: T := f a\n  -- c\n  b\n"
      && edgeFailsOn "def x:\n  -- c\n  T := b\n"
      && edgeFailsOn "def x: T := f (a -- c\n  ) b\n"
      && edgeFailsOn "def x: T := f (a -- c\n  ) -- d\n"
      && edgeFailsOn "def x: T := (a\n  -- c\n  )\n")
      = True :=
  byComputing

--| Refused: a blank line the rules read, above a list's later item.
theorem readBlankFails: edgeFailsOn "def x: T := [a,\n\n  b]\n" = True := byComputing
