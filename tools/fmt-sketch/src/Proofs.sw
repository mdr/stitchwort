--| Every layer's statements for the real formatter's proof
--| (self-hosted-fmt.md §7.2, §8 stage 3), top-down. Each `?` is stage
--| 8's work; `../SKETCH.md` says which layer and how many lemmas stand
--| behind it. The theorems of the last section (`tidy`'s, `printParses`,
--| `format`'s) are proved from the open ones, so the statements fit
--| together.

namespace Fmt.Sketch.Proofs
import Fmt.Sketch (..)
import Fmt.Sketch.Settled (..)
import Syntax (Comment, Leaf, Lexed, Tok, Trivia, lex, trimEnd)
import Std (Bool, Eq, List, Nat, Option, Result, Text)

-- Definitions the statements use.

def triviaComments (trivia: Trivia): List Text := match trivia.trailing with
  | Some comment => trivia.leading.map (each => each.text) ++ [comment.text]
  | None => trivia.leading.map (each => each.text)

def leavesComments: List Leaf → List Text
  | [] => []
  | [first, ..rest] => triviaComments first.trivia ++ leavesComments rest

--| Every comment of a lexed file, in the order of its tokens: stage 1's
--| types, read directly.
def Lexed.comments (lexed: Lexed): List Text := leavesComments lexed.leaves ++ triviaComments lexed.end

--| Every comment the tree holds, in the order of its tokens, then the
--| file's last comments.
def SourceFile.comments (file: SourceFile): List Text := ?

--| The grammar's shape: each constructor carries a kind it may carry;
--| each construct stands where the grammar reads it without brackets
--| (an operator's sides by precedence, an application's head and
--| arguments, a tuple of two or more); a bracket that takes no trailing
--| comma has none.
def Shaped (file: SourceFile): Prop := ?

--| Rule N's result, said of the tree, with no layout (spike K1,
--| `Settled.sw`): the tree's leaves in order are `homed`, that is, a
--| closing bracket or a record update's `|` has a trailing comment only
--| when it has own-line comments above it, or the code before it ends
--| with a comment, looking back past closers, commas and bars (not only
--| on the token just before); no `->` has one, nor has the type after it
--| comments above; no comment's text ends in a space. Which of two
--| closers holds a comment is the tree's to say: both are settled, and
--| the printer starts a line at the one that holds it.
def Settled (file: SourceFile): Prop := ?

--| Each `Word` lexes to one token of the kind its place asks, each
--| comment is one comment line, and no blank line is kept where the
--| rules keep none.
def Lexical (file: SourceFile): Prop := ?

--| What the parser guarantees of a tree, and every pass keeps. No
--| source is mentioned, so a tree a pass built qualifies.
def Parsed (file: SourceFile): Prop := Shaped file ∧ Settled file ∧ Lexical file ∧ file.refusal = None

--| These settled leaves spell the file: they are the tree's tokens in
--| order, commas between items, each with the tree's comments, at
--| columns and line starts the grammar's layout rules read as this
--| tree. (The toy's `spellsFile` and `SpelledFile`, joined.)
def Spells (file: SourceFile) (lexed: Lexed): Prop := ?

--| The lexer's leaves of the printed text, before rule N: the tree's
--| tokens in order, but for each trailing comment the engine wrote after
--| the closers on its line, which the lexer gives to the last of them.
--| Every closer or bar the tree has a trailing comment on starts its
--| line (`printedKeeping`).
def Printed (file: SourceFile) (lexed: Lexed): Prop := ?

-- Layer 1, the engine. The toy's engine and theory (`Toy.Doc`, about
-- 300 theorems) move to std; these are what changes on the way.

--| The engine's step budget with SW-3452 in (`fits` measures from the
--| new line after a trailing comment): the text is the same at any
--| budget from `3 * size + 3` up. `render` is the engine under `print`.
def renderWith (budget: Nat) (file: SourceFile) (width: Nat): Option Text := ?

theorem renderBudgetEnough ∀ (file: SourceFile) (width budget: Nat)
    (parsed: Parsed file):
    ∃ (enough: Nat) => renderWith (enough + budget) file width = Some (file.print width) :=
  ?

-- Layer 2, the lexer and rule N: stated against stage 1's code.

--| Rule N moves comments and nothing else: the tokens are the lexer's.
theorem settledKeepsTokens ∀ (lexed: Lexed):
    lexed.settled.leaves.map (leaf => leaf.token) = lexed.leaves.map (leaf => leaf.token) :=
  ?

--| Rule N keeps every comment, in order, less the spaces at its end.
theorem settledKeepsComments ∀ (lexed: Lexed): lexed.settled.comments = lexed.comments.map trimEnd := ?

--| Applying rule N to its own result changes nothing, for leaves the
--| lexer could give (`Lexed.laid`) that are `plain`. Without `plain` it is
--| false (SW-3825): `-> ->`, a bar before a closer, and a trailing comma
--| that starts the closer's line each move a comment the second time.
theorem settledIdempotent ∀ (lexed: Lexed) (choices: List Bool)
    (plainly: plain (lexed.laid False choices).leaves = True):
    (lexed.laid False choices).settled.settled = (lexed.laid False choices).settled :=
  ?

def bareComma (leaf: Leaf): Bool := match leaf.token.kind with
  | Tok.Comma => leaf.trivia.leading.isEmpty && leaf.trivia.trailing.isNone
  | _ => True

--| After rule N no comma holds a comment, so the tree needs no place for
--| one.
theorem settledCommasBare ∀ (lexed: Lexed): lexed.settled.leaves.all bareComma = True := ?

--| No `->` that a token follows has a trailing comment. (The last leaf
--| of a file may: rule N has no token to move its comment before, and
--| no file that parses ends in `->`.)
def arrowsBare: List Leaf → Bool
  | [] => True
  | [last] => True
  | [first, ..rest] => (first.token.kind != Tok.Arrow || first.trivia.trailing.isNone) && arrowsBare rest

theorem settledArrowsBare ∀ (lexed: Lexed): arrowsBare lexed.settled.leaves = True := ?

theorem settledTrimmed ∀ (lexed: Lexed): lexed.settled.comments.map trimEnd = lexed.settled.comments := ?

--| A file's comments, between two texts, through the lexer alone.
theorem lexSettledComments ∀ (source: Text) (lexed: Lexed)
    (lexes: lex source = Ok lexed):
    lexed.settled.comments = lexed.comments.map trimEnd :=
  settledKeepsComments lexed

-- Layer 3, the parser: the joint walk, the carry, the read-back.

theorem parseShaped ∀ (source: Text) (file: SourceFile) (parses: parse source = Ok file): Shaped file := ?

theorem parseSettled ∀ (source: Text) (file: SourceFile) (parses: parse source = Ok file): Settled file := ?

theorem parseLexical ∀ (source: Text) (file: SourceFile) (parses: parse source = Ok file): Lexical file := ?

theorem parseAccepted ∀ (source: Text) (file: SourceFile) (parses: parse source = Ok file): file.refusal = None := ?

--| The carry: the tree holds exactly the comments rule N left on the
--| tokens, in order. The parser copies and decides nothing from them.
theorem parseCarries ∀ (source: Text) (lexed: Lexed) (file: SourceFile)
    (lexes: lex source = Ok lexed)
    (parses: parse source = Ok file):
    file.comments = lexed.settled.comments :=
  ?

--| The read-back: the parser reads what spells a tree as that tree.
theorem readsBack ∀ (file: SourceFile) (lexed: Lexed)
    (parsed: Parsed file)
    (spells: Spells file lexed):
    parseLexed lexed = Ok file :=
  ?

--| No file is refused for want of fuel: more changes no answer.
theorem fuelEnough ∀ (lexed: Lexed) (extra: Nat):
    grammarWith (lexed.leaves.length + 1 + extra) lexed = grammarWith (lexed.leaves.length + 1) lexed :=
  ?

-- Layer 4, `meaning` and the passes, on the shared traversal.

theorem traverseKeep ∀ (file: SourceFile): file.traverse Steps.keep = file := ?

--| A pass's steps are absorbed by `meaning`'s when the plain traversal
--| of what a step returns is the plain traversal of what it was given.
def Absorbed (steps: Steps): Prop :=
  (∀ (slot: Slot) (expr: Expr) => ((steps.term) slot expr).traverse plainSteps slot = expr.traverse plainSteps slot)
    ∧ (∀ (found: List Parameter) => splitGroups (traverseParameters plainSteps ((steps.parameters) found))
      = splitGroups (traverseParameters plainSteps found))
    ∧ (∀ (found: Declaration) => ((steps.declaration) found).traverse plainSteps = found.traverse plainSteps)

--| The generic lemma behind every "keeps `meaning`": one induction over
--| the tree, for all passes.
theorem traverseKeepsMeaning ∀ (steps: Steps) (file: SourceFile)
    (absorbed: Absorbed steps):
    (file.traverse steps).meaning = file.meaning :=
  ?

--| What a step returns, once what is inside it has been traversed, needs
--| no second traversal.
def Settles (steps: Steps): Prop :=
  (∀ (slot: Slot) (expr: Expr) => expr.traverseInside steps = expr
    → ((steps.term) slot expr).traverse steps slot = (steps.term) slot expr)
    ∧ (∀ (found: List Parameter) => traverseParameters steps found = found
      → (steps.parameters) (traverseParameters steps ((steps.parameters) found)) = (steps.parameters) found)
    ∧ (∀ (flag: Bool) => (steps.comma) ((steps.comma) flag) = (steps.comma) flag)
    ∧ (∀ (found: Declaration) => ((steps.declaration) found).traverse steps = (steps.declaration) found)

--| The generic lemma behind every "idempotent".
theorem traverseIdempotent ∀ (steps: Steps) (file: SourceFile)
    (settles: Settles steps):
    (file.traverse steps).traverse steps = file.traverse steps :=
  ?

-- P1.

theorem forallKeepsMeaning ∀ (file: SourceFile): file.withForall.meaning = file.meaning := ?

theorem forallIdempotent ∀ (file: SourceFile): file.withForall.withForall = file.withForall := ?

theorem forallKeepsParsed ∀ (file: SourceFile) (parsed: Parsed file): Parsed file.withForall := ?

theorem forallKeepsComments ∀ (file: SourceFile): file.withForall.comments = file.comments := ?

-- P2.

theorem commasKeepMeaning ∀ (file: SourceFile): file.withoutTrailingCommas.meaning = file.meaning := ?

theorem commasIdempotent ∀ (file: SourceFile):
    file.withoutTrailingCommas.withoutTrailingCommas = file.withoutTrailingCommas :=
  ?

theorem commasKeepParsed ∀ (file: SourceFile) (parsed: Parsed file): Parsed file.withoutTrailingCommas := ?

theorem commasKeepComments ∀ (file: SourceFile): file.withoutTrailingCommas.comments = file.comments := ?

theorem commasKeepForall ∀ (file: SourceFile)
    (done: file.withForall = file):
    file.withoutTrailingCommas.withForall = file.withoutTrailingCommas :=
  ?

-- P3.

theorem bracketsKeepMeaning ∀ (file: SourceFile): file.withoutSpareBrackets.meaning = file.meaning := ?

theorem bracketsIdempotent ∀ (file: SourceFile):
    file.withoutSpareBrackets.withoutSpareBrackets = file.withoutSpareBrackets :=
  ?

--| The precedence argument: a pair goes only where the grammar reads its
--| content as the pair was read, so the tree is still one the parser
--| could give.
theorem bracketsKeepParsed ∀ (file: SourceFile) (parsed: Parsed file): Parsed file.withoutSpareBrackets := ?

theorem bracketsKeepComments ∀ (file: SourceFile): file.withoutSpareBrackets.comments = file.comments := ?

theorem bracketsKeepForall ∀ (file: SourceFile)
    (done: file.withForall = file):
    file.withoutSpareBrackets.withForall = file.withoutSpareBrackets :=
  ?

theorem bracketsKeepCommas ∀ (file: SourceFile)
    (done: file.withoutTrailingCommas = file):
    file.withoutSpareBrackets.withoutTrailingCommas = file.withoutSpareBrackets :=
  ?

-- P4.

theorem mergeKeepsMeaning ∀ (file: SourceFile): file.withMergedParameters.meaning = file.meaning := ?

theorem mergeIdempotent ∀ (file: SourceFile):
    file.withMergedParameters.withMergedParameters = file.withMergedParameters :=
  ?

theorem mergeKeepsParsed ∀ (file: SourceFile) (parsed: Parsed file): Parsed file.withMergedParameters := ?

theorem mergeKeepsComments ∀ (file: SourceFile): file.withMergedParameters.comments = file.comments := ?

theorem mergeKeepsForall ∀ (file: SourceFile)
    (done: file.withForall = file):
    file.withMergedParameters.withForall = file.withMergedParameters :=
  ?

theorem mergeKeepsCommas ∀ (file: SourceFile)
    (done: file.withoutTrailingCommas = file):
    file.withMergedParameters.withoutTrailingCommas = file.withMergedParameters :=
  ?

--| The one real ordering fact: merging groups uncovers no spare pair.
--| (The other way round it is false: a pair around one of two equal
--| types hides a merge, so P3 runs first.)
theorem mergeKeepsBrackets ∀ (file: SourceFile)
    (done: file.withoutSpareBrackets = file):
    file.withMergedParameters.withoutSpareBrackets = file.withMergedParameters :=
  ?

--| The four passes are one traversal. Not needed by any theorem below.
theorem tidyFused ∀ (file: SourceFile): file.tidy = file.traverse tidySteps := ?

-- Layer 5, the rules and spelling.

--| The printed text lexes, to the tokens the rules wrote.
theorem printLexes ∀ (file: SourceFile) (width: Nat)
    (parsed: Parsed file)
    (bare: file.withoutTrailingCommas = file):
    ∃ (lexed: Lexed) => lex (file.print width) = Ok lexed ∧ Printed file lexed :=
  ?

--| The printer's half of `printedSettle`: the printed leaves are leaves
--| that spell the tree, `homed` since the tree is `Settled`, in a layout
--| that starts a line at each closer or bar holding a comment
--| (`Lexed.laid`, keeping). Rule N's half is `settledAnyLayout`: such a
--| layout settles to the leaves it was made from.
theorem printedKeeping ∀ (file: SourceFile) (lexed: Lexed)
    (parsed: Parsed file)
    (printed: Printed file lexed):
    ∃ (spelled: Lexed) => ∃ (choices: List Bool) => Spells file spelled
      ∧ homed spelled.leaves = True
      ∧ lexed.bare = (spelled.laid True choices).bare :=
  ?

--| Rule N takes each comment the engine wrote after closers back to the
--| token the tree has it on, and then the leaves spell the file. From
--| `printedKeeping` and `SettledProofs.settledAnyLayout`; the tree has no
--| line starts to consult, and needs none.
theorem printedSettle ∀ (file: SourceFile) (lexed: Lexed)
    (parsed: Parsed file)
    (printed: Printed file lexed):
    Spells file lexed.settled :=
  ?

--| The printer chooses only white space and comment places: without
--| spaces and line breaks, the printed text is the tree's tokens and
--| comments.
def SourceFile.spelling (file: SourceFile): List Text := ?

theorem printWords ∀ (file: SourceFile) (width: Nat) (parsed: Parsed file): (file.print width).words = file.spelling :=
  ?

--| Width changes only white space.
theorem printWidths ∀ (file: SourceFile) (first second: Nat)
    (parsed: Parsed file):
    (file.print first).words = (file.print second).words :=
  ?

-- Layer 6, the glue: proved from the statements above.

theorem formattedInjective ∀ (a b: Text) (h: Formatted a = Formatted b): a = b := cases

theorem refusedInjective ∀ (a b: Text) (h: Refused a = Refused b): a = b := cases

theorem parseParsed ∀ (source: Text) (file: SourceFile) (parses: parse source = Ok file): Parsed file := (
  parseShaped source file parses,
  parseSettled source file parses,
  parseLexical source file parses,
  parseAccepted source file parses
)

theorem parseReads ∀ (source: Text) (lexed: Lexed) (file: SourceFile)
    (lexes: lex source = Ok lexed)
    (reads: parseLexed lexed.settled = Ok file):
    parse source = Ok file :=
  rewrite lexes then reads

--| The printed text of a tree with the parser's guarantees and no
--| trailing comma parses to the same tree, at every width.
theorem printParses ∀ (file: SourceFile) (width: Nat)
    (parsed: Parsed file)
    (bare: file.withoutTrailingCommas = file):
    parse (file.print width) = Ok file :=
  match printLexes file width parsed bare with
    | (lexed, lexes, printed) =>
      parseReads
        (file.print width)
        lexed
        file
        lexes
        (readsBack file lexed.settled parsed (printedSettle file lexed parsed printed))

theorem tidyKeepsMeaning ∀ (file: SourceFile): file.tidy.meaning = file.meaning := calc file.tidy.meaning
  _ = file.withForall.withoutTrailingCommas.withoutSpareBrackets.meaning :=
    mergeKeepsMeaning file.withForall.withoutTrailingCommas.withoutSpareBrackets
  _ = file.withForall.withoutTrailingCommas.meaning := bracketsKeepMeaning file.withForall.withoutTrailingCommas
  _ = file.withForall.meaning := commasKeepMeaning file.withForall
  _ = file.meaning := forallKeepsMeaning file

theorem tidyKeepsComments ∀ (file: SourceFile): file.tidy.comments = file.comments := calc file.tidy.comments
  _ = file.withForall.withoutTrailingCommas.withoutSpareBrackets.comments :=
    mergeKeepsComments file.withForall.withoutTrailingCommas.withoutSpareBrackets
  _ = file.withForall.withoutTrailingCommas.comments := bracketsKeepComments file.withForall.withoutTrailingCommas
  _ = file.withForall.comments := commasKeepComments file.withForall
  _ = file.comments := forallKeepsComments file

theorem tidyParsed ∀ (file: SourceFile) (parsed: Parsed file): Parsed file.tidy :=
  mergeKeepsParsed file.withForall.withoutTrailingCommas.withoutSpareBrackets
    (bracketsKeepParsed file.withForall.withoutTrailingCommas
      (commasKeepParsed file.withForall (forallKeepsParsed file parsed)))

theorem tidyForall ∀ (file: SourceFile): file.tidy.withForall = file.tidy :=
  mergeKeepsForall file.withForall.withoutTrailingCommas.withoutSpareBrackets
    (bracketsKeepForall file.withForall.withoutTrailingCommas
      (commasKeepForall file.withForall (forallIdempotent file)))

theorem tidyBare ∀ (file: SourceFile): file.tidy.withoutTrailingCommas = file.tidy :=
  mergeKeepsCommas file.withForall.withoutTrailingCommas.withoutSpareBrackets
    (bracketsKeepCommas file.withForall.withoutTrailingCommas (commasIdempotent file.withForall))

theorem tidyBrackets ∀ (file: SourceFile): file.tidy.withoutSpareBrackets = file.tidy :=
  mergeKeepsBrackets file.withForall.withoutTrailingCommas.withoutSpareBrackets
    (bracketsIdempotent file.withForall.withoutTrailingCommas)

theorem tidyMerged ∀ (file: SourceFile): file.tidy.withMergedParameters = file.tidy :=
  mergeIdempotent file.withForall.withoutTrailingCommas.withoutSpareBrackets

theorem tidyIdempotent ∀ (file: SourceFile): file.tidy.tidy = file.tidy := calc file.tidy.tidy
  _ = file.tidy.withForall.withoutTrailingCommas.withoutSpareBrackets.withMergedParameters := byComputing
  _ = file.tidy.withoutTrailingCommas.withoutSpareBrackets.withMergedParameters :=
    Eq.cong
      ((tree: SourceFile) => tree.withoutTrailingCommas.withoutSpareBrackets.withMergedParameters)
      (tidyForall file)
  _ = file.tidy.withoutSpareBrackets.withMergedParameters :=
    Eq.cong ((tree: SourceFile) => tree.withoutSpareBrackets.withMergedParameters) (tidyBare file)
  _ = file.tidy.withMergedParameters := Eq.cong ((tree: SourceFile) => tree.withMergedParameters) (tidyBrackets file)
  _ = file.tidy := tidyMerged file

-- The top theorems.

--| Totality, and the refusals: `format` answers every source, with its
--| tree tidied and printed if it parses, and it refuses only what the
--| parser refuses.
theorem formatAnswers ∀ (source: Text) (width: Nat) (tree: SourceFile)
    (parsed: parse source = Ok tree):
    format source width = Formatted (tree.tidy.print width) :=
  rewrite parsed

theorem formatRefuses ∀ (source: Text) (width: Nat) (message: Text)
    (refused: parse source = Err message):
    format source width = Refused message :=
  rewrite refused

theorem formatRefusesOnly ∀ (source: Text) (width: Nat) (message: Text)
    (refused: format source width = Refused message):
    parse source = Err message :=
  match e: parse source with | Err found => rewrite refusedInjective found message refused

--| Round trip: the output parses to the source's tree as the passes
--| leave it.
theorem formatRoundTrip ∀ (source: Text) (width: Nat) (output: Text)
    (h: format source width = Formatted output):
    ∃ (tree: SourceFile) => parse source = Ok tree ∧ output = tree.tidy.print width ∧ parse output = Ok tree.tidy :=
  match e: parse source with
    | Ok tree =>
      let same := formattedInjective (tree.tidy.print width) output h
      (
        tree,
        byComputing,
        same.flipped,
        (rewrite <- same then printParses tree.tidy width (tidyParsed tree (parseParsed source tree e)) (tidyBare tree))
      )

--| The same program: the output parses, to a tree with the source's
--| meaning.
theorem formatKeepsMeaning ∀ (source: Text) (width: Nat) (output: Text)
    (h: format source width = Formatted output):
    ∃ (before after: SourceFile) => parse source = Ok before
      ∧ parse output = Ok after
      ∧ after.meaning = before.meaning :=
  match formatRoundTrip source width output h with
    | (tree, parsed, _, reparsed) => (tree, tree.tidy, parsed, reparsed, tidyKeepsMeaning tree)

--| Idempotence: formatting the output again, at the same width, gives
--| the output.
theorem formatIdempotent ∀ (source: Text) (width: Nat) (output: Text)
    (h: format source width = Formatted output):
    format output width = Formatted output :=
  match formatRoundTrip source width output h with
    | (tree, parsed, same, reparsed) =>
      calc format output width
        _ = Formatted (tree.tidy.tidy.print width) := formatAnswers output width tree.tidy reparsed
        _ = Formatted (tree.tidy.print width) :=
          Eq.cong ((tidied: SourceFile) => Formatted (tidied.print width)) (tidyIdempotent tree)
        _ = Formatted output := Eq.cong Formatted same.flipped

--| The output depends on the source only through its tree.
theorem formatSameTree ∀ (first second: Text) (width: Nat) (tree: SourceFile)
    (parsesFirst: parse first = Ok tree)
    (parsesSecond: parse second = Ok tree):
    format first width = format second width :=
  rewrite formatAnswers first width tree parsesFirst, formatAnswers second width tree parsesSecond

--| Every comment kept, between the two texts, through the lexer and rule
--| N only: neither side goes through the parser's tree or the printer.
theorem formatKeepsComments ∀ (source output: Text) (width: Nat) (before after: Lexed)
    (formats: format source width = Formatted output)
    (lexedBefore: lex source = Ok before)
    (lexedAfter: lex output = Ok after):
    after.settled.comments = before.settled.comments :=
  match formatRoundTrip source width output formats with
    | (tree, parsed, same, reparsed) =>
      calc after.settled.comments
        _ = tree.tidy.comments := (parseCarries output after tree.tidy lexedAfter reparsed).flipped
        _ = tree.comments := tidyKeepsComments tree
        _ = before.settled.comments := parseCarries source before tree lexedBefore parsed
