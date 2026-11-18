--| What slice 1's proofs still have to say about the formatter's output, stated and not yet proved (SW-4025; the
--| reasons are in docs/reviews/SW-4025-output-statements.md). The output is the text the file loop prints for a
--| tidied tree; the second run of the formatter lexes it, settles it with rule N and parses it.
--|
--| - The file level: the text lexes to leaves written out here (`SourceFile.lexed1`), one group a declaration, which
--|   pass the alphabet, have no last comma and are `plain1`.
--| - Rule N on those leaves: it is not idle (a comment after `a,` or `b)` is the comma's or the closer's to the
--|   lexer, and rule N takes it back to `a` or `b`: `outputNotIdle`). What holds is `printedSettle1`: the settled
--|   leaves' words are the tree's, with the blank-line flags the rules never read cleared.
--|
--| Each open goal is a proof ticket.

namespace Fmt.OutputStatements
import Std (Bool, Doc, Eq, List, Nat, Option, Result, Text)
import Std.Doc.Proofs (printedPieces)
import Syntax (..)
import Syntax.Proofs (Laid)
import Fmt (..)
import Fmt.PrintLexProofs (pieceFold)
import Fmt.SpellProofs (..)
import Fmt.TreeJoinProofs (lexKind)
import Syntax.ParseCarries (codeWords)
import Syntax.SettleProofs (alphabet1, plain1, tokens)
import Syntax.SettleBareProofs (noLast)

-- One declaration's leaves.

--| The layout the lexer's proofs read a printed document as (`printLexes1Tree`), at the formatter's width.
def laidOf (doc: Doc): Laid := (pieceFold lexKind (printedPieces doc width)).foldLeft Laid.start Laid.lay

--| The leaves of a declaration's printed text, lexed alone: `printLexes1Tree`'s, so `printedHangs` is `hangs` of
--| these. The declaration's own-line comments are not among them: the file loop prints those.
def Decl.leaves1 (decl: Decl): List Leaf := match decl.doc1 with
  | Some doc => (laidOf doc).leaves.reverse
  | None => []

def tokenTexts (leaves: List Leaf): List Text := leaves.map (leaf => leaf.token.text)

--| The leaf's kind is the one the lexer gives its text alone.
def Leaf.kinded (leaf: Leaf): Bool := leaf.token.kind == lexKind leaf.token.text

-- `printedTokens1`, that a declaration's printed tokens are the texts the rules spell for it without the comments, each of
-- the lexer's kind, is proved in `Fmt.TokenProofs`.

-- The file's leaves.

--| An own-line comment the file loop printed, as the lexer reads it back: at column 0, after one blank line or none,
--| without a carriage return at its end (the lexer strips them and the spaces among them, `Fmt.FileLexProofs.crDropped`).
def noteComment (note: Note): Comment :=
  { text = withoutReturn note.text, column = 0, blankLines = if note.blankBefore then 1 else 0 }

--| A run of own-line comments as the file loop lays them; `empty`: nothing is printed before them, so the first has
--| no blank line above it whatever its flag says (`Output.item`).
def laidNotes (empty: Bool): List Note → List Comment
  | [] => []
  | [first, ..rest] =>
    [{ noteComment first | blankLines = if empty then 0 else (noteComment first).blankLines }, ..rest.map noteComment]

--| Leaves with the first given these own-line comments and blank lines.
def headed (above: List Comment) (blank: Nat): List Leaf → List Leaf
  | [] => []
  | [first, ..rest] => [{ first | trivia = { first.trivia | leading = above, blankLines = blank } }, ..rest]

--| A declaration's leaves as they stand in the file's text: its own, the `def` holding the declaration's own-line
--| comments and blank line as the file loop printed them.
def Decl.laid1 (decl: Decl) (empty: Bool): List Leaf :=
  let first := decl.firstComments
  let blank := if first.blankBefore && !(empty && first.above.isEmpty) then 1 else 0
  headed (laidNotes empty first.above) blank decl.leaves1

--| Each declaration's leaves in the file; `empty`: no declaration comes before.
def groupsFrom (empty: Bool): List Decl → List (List Leaf)
  | [] => []
  | [decl, ..rest] => [decl.laid1 empty, ..groupsFrom False rest]

--| What the lexer reads of `file.printed1`.
def SourceFile.lexed1 (file: SourceFile): Lexed := {
  leaves = (groupsFrom True file.decls).concat,
  end = { leading = laidNotes file.decls.isEmpty file.end.above, blankLines = 0, trailing = None }
}

--| Every declaration's printed leaves keep the line rule: what `printedHangs` gives of each (SW-4034).
def SourceFile.hung1 (file: SourceFile): Bool := file.decls.all (decl => hangs decl.leaves1)

-- `printedFileLexes1`, that the file loop's text lexes to `SourceFile.lexed1`, is proved in `Fmt.FileLexProofs`.

-- `printedAlphabet1`, that the output passes the alphabet, is proved in `Fmt.OutputFileProofs`.

-- `printedNoLast1`, that the output has no last comma, is proved in `Fmt.OutputFileProofs`.

-- `printedPlain1`, that the output is `plain1`, is proved in `Fmt.OutputFileProofs`.

-- `printedGroups1`, that the parser's groups of the output are the declarations' leaves, is proved in
-- `Fmt.OutputFileProofs`.

-- Rule N on the output.

--| The comments of the first thing in the file, without the blank-line flag the file loop never reads: nothing is
--| printed above it.
def Comments.topped (comments: Comments): Comments := match comments.above with
  | [] => { comments | blankBefore = False }
  | [first, ..rest] => { comments | above = [{ first | blankBefore = False }, ..rest] }

--| `calm`, and the flag of the file's first comment or declaration cleared. `calm` keeps that flag, the file loop
--| drops its blank line, and the lexer reads none back: so the output's tree has `calmTop` of the printed tree, not
--| `calm` (`topFlagLost`).
def SourceFile.calmTop (file: SourceFile): SourceFile := match file.calm.decls with
  | [Definition attributes header body, ..rest] =>
    { decls = [Definition attributes { header | keyword = header.keyword.topped } body, ..rest], end = file.calm.end }
  | [] => { decls = [], end = file.calm.end.topped }
  | _ => file.calm

-- `printedSettle1`, that rule N on the output gives the tree's words back (each group of the settled leaves, commas
-- left out, is its declaration's words, and the end's comments are the file's), is in `Fmt.SettleOutputProofs`
-- (SW-4043), with `printedStands1`'s conclusion and no own-line comment ending in a carriage return as hypotheses.

-- Cases the statements apply to, so their hypotheses can be met; and two that show what is not true.

def sameLexed (first second: Lexed): Bool := first.dump == second.dump

def sameGroups (first second: List (List Leaf)): Bool :=
  first.map (group => ({ leaves = group, end = Trivia.empty }: Lexed).dump)
    == second.map (group => ({ leaves = group, end = Trivia.empty }: Lexed).dump)

--| The tidied tree of a source, as the driver prints it.
def tidiedOf (source: Text): Option SourceFile := match lex source with
  | Err _ => None
  | Ok lexed =>
    match lexed.tidied with
      | Err _ => None
      | Ok tidied => Some tidied.fourth

--| What the statements above say of one source's tidied tree, as a test: their hypotheses, then each conclusion,
--| then what they are for: the output's parse is `calmTop` of the tree, word for word, and prints the same text.
def holdsOn (source: Text): Bool := match tidiedOf source with
  | None => False
  | Some file =>
    match lex file.printed1 with
      | Err _ => False
      | Ok lexed =>
        file.within1
          && file.shaped1
          && file.settled1
          && file.lexical1
          && file.hung1
          && file.decls.all (decl => tokenTexts decl.leaves1 == decl.spelt.filter notComment)
          && file.decls.all (decl => decl.leaves1.all Leaf.kinded)
          && sameLexed lexed file.lexed1
          && alphabet1 lexed.leaves
          && noLast [] lexed.leaves
          && plain1 (tokens lexed.leaves)
          && sameGroups (groupsOf lexed.leaves) (groupsFrom True file.decls)
          && (groupsOf lexed.settled.leaves).map codeWords == file.calmTop.decls.map Decl.words
          && lexed.settled.end.comments == file.calmTop.end
          && readsBack lexed file

def readsBack (lexed: Lexed) (file: SourceFile): Bool := match parseFile lexed.settledOnce with
  | Err _ => False
  | Ok read =>
    read.decls.map Decl.words == file.calmTop.decls.map Decl.words
      && read.end == file.calmTop.end
      && read.dump == file.dump
      && read.printed1 == file.printed1

--| Comments in every kind of place: above declarations and at the end, after an opener, after a comma, above an
--| item after a blank line, after a closer, and before a `->`.
theorem holdsOnExample: holdsOn
        "-- top\n\n-- two\ndef d: A -> -- x\n  B := g [ -- open\n    a, -- first\n\n    -- above\n    b,\n  ] -- close\n\n\ndef e: C := -1 + f x -- end\n-- last\n\n-- more\n"
      = True :=
  byComputing

--| Closers that hold comments, one after an item that ends with a comment and one on a line of its own.
theorem holdsOnClosers: holdsOn "def d: A := f [a, -- c\n    b -- e\n  ] (c -- d\n    -- o\n  ) -- p\n" = True :=
  byComputing

--| A file that starts with blank lines, and one of comments only.
theorem holdsOnTop: (holdsOn "\n\n-- a\n\ndef d: A := b\n" && holdsOn "\n\n-- a\n\n-- b\n" && holdsOn "") = True :=
  byComputing

--| Whether rule N leaves the lexed output of a source as it is.
def idleOn (source: Text): Bool := match tidiedOf source with
  | None => False
  | Some file =>
    match lex file.printed1 with
      | Err _ => False
      | Ok lexed => sameLexed lexed.settled lexed

--| Rule N is not idle on the output: in `(a, b) -- c` the lexer gives the comment to `)`, and rule N takes it back
--| to `b`, where the tree has it. Likewise after a comma. So "the output's leaves are settled" is false, and
--| `printedSettle1` is about the leaves after rule N.
theorem outputNotIdle: (idleOn "def d: A := (a, b -- c\n  )\n" || idleOn "def d: A := [\n  a, -- c\n  b\n]\n")
      = False :=
  byComputing

--| Whether the output's parse has the tree's `calm`, by its words.
def calmOn (source: Text): Bool := match tidiedOf source with
  | None => False
  | Some file =>
    match lex file.printed1 with
      | Err _ => False
      | Ok lexed =>
        match parseFile lexed.settledOnce with
          | Err _ => False
          | Ok read =>
            read.calm.decls.map Decl.words == file.calm.decls.map Decl.words && read.calm.end == file.calm.end

--| `calm` is not kept by print and parse: a source that starts with a blank line has the flag on its first `def`
--| (or first comment), `calm` keeps it, and the output has no blank line there. `calmTop` clears it.
theorem topFlagLost: (calmOn "\n\ndef d: A := b\n" || calmOn "\n\n-- a\n\n-- b\n") = False := byComputing

--| `def d: A := f [a -- x⏎, b] -- c` as a tree no parse gives: the `]` holds a comment though `b`, before it, ends
--| with none, so the tree is not `settled1`.
def unsettledFile: SourceFile := {
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
        (App (Atom Lower (fixedWord "f" Comments.none)) [
          ListOf
            (fixedWord "[" Comments.none)
            [
              Atom Lower (fixedWord "a" { above = [], after = Some "-- x", blankBefore = False }),
              Atom Lower (fixedWord "b" Comments.none)
            ]
            False
            (fixedWord "]" { above = [], after = Some "-- c", blankBefore = False })
        ]))
  ],
  end = Comments.none
}

--| `printedSettle1`'s conclusion, as a test.
def wordsBack (file: SourceFile): Bool :=
  (groupsOf file.lexed1.settled.leaves).map codeWords == file.calmTop.decls.map Decl.words
    && file.lexed1.settled.end.comments == file.calmTop.end

--| `printedSettle1` needs `settled1`: of a tree with every other hypothesis, whose `]` holds a comment rule N would
--| have moved, the output's `]` holds it on the lexer's reading too, and rule N then gives it to `b`.
theorem settledNeeded: (unsettledFile.within1
      && unsettledFile.shaped1
      && unsettledFile.lexical1
      && unsettledFile.hung1
      && !unsettledFile.settled1
      && !wordsBack unsettledFile)
      = True :=
  byComputing
