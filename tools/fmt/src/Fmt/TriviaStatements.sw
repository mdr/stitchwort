--| Where the comments and blank lines of a printed declaration stand, stated and not yet proved (SW-4042; the reasons
--| are in docs/reviews/SW-4042-trivia-statement.md). `printedSpells` gives the printed texts in order and `hangs`
--| the columns of the tokens that start lines; neither says which token the lexer gives a comment to, which is what
--| comment placement reads. `stands` says it, of the leaves the printed text lexes to against the tree's words, and
--| `printedSettle1` (Fmt.SettleOutputProofs) follows from it.

namespace Fmt.TriviaStatements
import Std (Bool, List, Nat, Option, Text)
import Syntax (..)
import Fmt (..)
import Fmt.OutputStatements (..)

--| A comma, or a closer whose word has no comment of its own, on a line that the comment `owed` may be waiting to
--| end: what is still owed after it, or `None` if the leaf can't stand there. With a comment owed the leaf doesn't
--| start a line, and holds that comment or none; with none owed it holds none.
def tucked (owed: Option Text) (leaf: Leaf): Option (Option Text) := match owed, leaf.trivia.trailing with
  | None, None => Some None
  | None, Some _ => None
  | Some _, None => if leaf.token.lineStart then None else Some owed
  | Some text, Some comment => if leaf.token.lineStart || !(comment.text == text) then None else Some None

--| The leaf has the word's text, its own-line comments above it with their blank lines, and the word's blank line.
def Leaf.headedAs (leaf: Leaf) (word: Word): Bool :=
  leaf.token.text == word.text
    && leaf.word.comments.above == word.comments.above
    && leaf.word.comments.blankBefore == word.comments.blankBefore

--| Whether `leaves` are `words` as the lexer reads them printed. `owed`: the trailing comment of a word already
--| passed, which the lexer has not yet seen, as closers and commas follow the word on its line.
--|
--| - A comma has no comment above it and no blank line. It holds a comment only if one is owed.
--| - Any other leaf is the next word: its text, its own-line comments and blank-line flags.
--| - A word's trailing comment is on the word's leaf or owed on. While one is owed, each leaf is a comma, or a closer
--|   whose word has no comment after it; none starts a line; and the first that holds a comment holds the one owed.
--| - A closer whose word has a comment after it starts its line.
--| - At the end nothing is owed.
def stands (owed: Option Text) (words: List Word) (leaves: List Leaf): Bool := match leaves with
  | [] => words.isEmpty && owed.isNone
  | [leaf, ..rest] =>
    if leaf.kind == Comma then
      leaf.trivia.leading.isEmpty
        && leaf.trivia.blankLines == 0
        && (match tucked owed leaf with
          | None => False
          | Some still => stands still words rest)
    else
      match words with
        | [] => False
        | [word, ..later] =>
          leaf.headedAs word
            && (match owed, word.comments.after with
              | Some _, Some _ => False
              | Some _, None =>
                leaf.kind.isCloser
                  && (match tucked owed leaf with
                    | None => False
                    | Some still => stands still later rest)
              | None, None => leaf.trivia.trailing.isNone && stands None later rest
              | None, Some text =>
                (!leaf.kind.isCloser || leaf.token.lineStart)
                  && (match leaf.trivia.trailing with
                    | None => stands (Some text) later rest
                    | Some comment => comment.text == text && stands None later rest))

--| The declaration's words as its own printed text has them: `calm`'s, without the `def`'s own-line comments and
--| blank line, which the file loop prints.
def Decl.stood (decl: Decl): List Word := match decl.calm.words with
  | [] => []
  | [first, ..rest] =>
    [{ first | comments = { above = [], after = first.comments.after, blankBefore = False } }, ..rest]

def Decl.stands (decl: Decl): Bool := stands None decl.stood decl.leaves

--| Every declaration's printed leaves have the tree's comments where `stands` says.
def SourceFile.stood (file: SourceFile): Bool := file.decls.all Decl.stands

-- `printedStands1`, that `stands` holds of a slice 1 declaration, is proved in `Fmt.StandsProofs`, with two
-- hypotheses beyond the four tree facts: no comment ends in a carriage return (`unreturned`; the statement is false without it) and the facts `printedHangs` takes (`DeclHangs`).

-- Cases the statement applies to, and what it is for.

--| The statement on one source's tidied tree: its hypotheses, then its conclusion.
def standsOn (source: Text): Bool := match tidiedOf source with
  | None => False
  | Some file => file.within1 && file.shaped && file.settled && file.lexical && file.stood

--| Comments in every kind of place (`holdsOnExample`'s source): above declarations, after an opener, after a comma,
--| above an item after a blank line, after a closer, and after a `->` in the source.
theorem standsOnExample: standsOn
        "-- top\n\n-- two\ndef d: A -> -- x\n  B := g [ -- open\n    a, -- first\n\n    -- above\n    b,\n  ] -- close\n\n\ndef e: C := -1 + f x -- end\n-- last\n\n-- more\n"
      = True :=
  byComputing

--| Closers that hold comments: after an item that ends with a comment, on a line of its own under own-line comments,
--| and after a closer between it and the comment before (`)` stays on `a`'s line, `]` takes its own).
theorem standsOnClosers: (standsOn "def d: A := f [a, -- c\n    b -- e\n  ] (c -- d\n    -- o\n  ) -- p\n"
      && standsOn "def d: A := [(a -- x\n  )\n] -- c\n")
      = True :=
  byComputing

--| A comment owed past two closers and a comma: `((a -- c⏎), b)` prints `a` and the first `)` and the comma, then
--| the comment.
theorem standsOnTucked: standsOn "def d: A := g ((a -- c\n  ), b)\n" = True := byComputing

--| `def d: A := (b) -- c` as a tree no parse gives: the `)` holds a comment though `b`, before it, ends with none, so
--| the tree is not `settled`.
def unsettledParen: SourceFile := {
  decls = [
    Definition []
      {
        exportKeyword = None,
        opaqueKeyword = None,
        kind = DefPlain,
        keyword = Comments.none,
        name = fixedWord "d" Comments.none,
        forallKeyword = None,
        params = [],
        colon = Comments.none,
        result = Atom Upper (fixedWord "A" Comments.none),
        decreasingClause = None,
        unfoldingClause = None
      }
      (Assigned Comments.none
        (Paren
          (fixedWord "(" Comments.none)
          (Atom Lower (fixedWord "b" Comments.none))
          (fixedWord ")" { above = [], after = Some "-- c", blankBefore = False })))
  ],
  end = Comments.none
}

--| `settled` is needed: in `unsettledParen` the rules leave the `)` on `b`'s line, where it starts none, and the
--| statement fails, with every other hypothesis.
theorem unsettledFalls: (unsettledParen.within1
      && unsettledParen.shaped
      && unsettledParen.lexical
      && !unsettledParen.settled
      && !unsettledParen.stood)
      = True :=
  byComputing

--| `stands` alone does not give `printedSettle1`: `unsettledFile` (`[a -- x⏎, b] -- c`) stands, as its list breaks
--| and the `]` starts a line, yet comment placement takes the `]`'s comment back to `b` (`settledNeeded`). `printedSettle1`
--| reads `settled` a second time, for where the back-walk stops.
theorem unsettledStands: (unsettledFile.stood && !wordsBack unsettledFile) = True := byComputing
