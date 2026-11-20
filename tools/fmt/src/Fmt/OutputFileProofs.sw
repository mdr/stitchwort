--| The output's leaves, file level (SW-4040, ticket C of docs/reviews/SW-4025-output-statements.md): the alphabet, no
--| last comma, `plain1` and the groups, from `printedTokens1`.
--|
--| One pass over a declaration's printed texts (`Scan.run`) checks what the first three need: every token of the
--| alphabet, no token that can't follow the one before (a comma before a closer, `->` before a comma, closer or
--| `->`) and no closer without an open bracket. A comment is skipped. `exprRuns` takes the pass along an expression,
--| `declRuns` along a declaration, and `leafScan` carries it to the leaves, whose kinds are the lexer's
--| (`printedTokens1`).
--|
--| The groups (`printedGroups1`) also need three facts of the leaves: a leaf in column 0 starts its line (the
--| layout, `declColLines`), a leaf that starts its line in column 0 is a closer or `:=` (`hangs`, `hangsCol`), and a
--| closer has its bracket open (`declDepth`); `groupsSplit` runs the parser's splitter over them.

namespace Fmt.OutputFileProofs
import Std (Bool, Char, DecEq, Eq, List, Nat, Option, Text, Void)
import Syntax (..)
import Syntax.LexProofs (AllPlain, Laid, Piece, Spells, utf8Chars, utf8OfText)
import Syntax.SettleProofs (alphabet1, arrowFollow, plain1, plainFrom, tokens, within1Not)
import Syntax.SettleBareProofs (noLast)
import Fmt (..)
import Fmt.OperatorList (operators1, operatorListed)
import Fmt.SpellProofs (..)
import Fmt.TreeJoinProofs (..)
import Fmt.TokenProofs (declRealOfLexical, printedTokens1)
import Fmt.OutputStatements (..)
import Fmt.FileLexProofs (..)
import Syntax.ReadBackHungAtomsLemmas (hungStep)

-- One pass over the texts.

--| The token `kind` may follow the token `previous`: `->` is followed by an operand's first token, and a comma by
--| an item's.
def pairOk (previous kind: Tok): Bool :=
  (!arrowFollow kind || !(previous == Arrow)) && (!kind.isCloser || !(previous == Comma))

--| Where the pass is: the last token's kind and the number of open brackets.
type Scan = { previous: Option Tok, open: Nat }

def prevOk (previous: Option Tok) (kind: Tok): Bool := match previous with
  | Some before => pairOk before kind
  | None => True

--| One token: in the alphabet, allowed to follow the last, and closing a bracket only where one is open.
def Scan.go (scan: Scan) (kind: Tok): Option Scan :=
  if kind.within1 && prevOk scan.previous kind && (!kind.isCloser || scan.open > 0) then
    Some {
      previous = Some kind,
      open = if kind.isOpener then scan.open + 1
      else if kind.isCloser then scan.open - 1
      else scan.open
    }
  else None

--| One text: a comment changes nothing.
def Scan.step (scan: Scan) (text: Text): Option Scan :=
  if text.startsWith "--" then Some scan else scan.go (lexKind text)

def Scan.run (scan: Scan): List Text → Option Scan
  | [] => Some scan
  | [text, ..rest] =>
    match scan.step text with
      | Some next => next.run rest
      | None => None

theorem runAppend ∀ (xs ys: List Text) (scan mid: Scan)
    (first: scan.run xs = Some mid):
    scan.run (xs ++ ys) = mid.run ys :=
  match xs with
    | [] => rewrite Option.someInjective first
    | [text, ..rest] =>
      match step: scan.step text with
        | Some next => runAppend rest ys next mid first

--| A token that is neither a bracket nor a comma or `->`: anything may come before it.
theorem goFlat ∀ (scan: Scan) (kind: Tok)
    (within: kind.within1 = True)
    (lead: arrowFollow kind = False)
    (opens: kind.isOpener = False)
    (closes: kind.isCloser = False):
    scan.go kind = Some { previous = Some kind, open = scan.open } :=
  match scan.previous with
    | None => rewrite within, opens, closes
    | Some before => rewrite within, lead, opens, closes

--| An opening bracket.
theorem goOpen ∀ (scan: Scan) (kind: Tok)
    (within: kind.within1 = True)
    (lead: arrowFollow kind = False)
    (opens: kind.isOpener = True)
    (closes: kind.isCloser = False):
    scan.go kind = Some { previous = Some kind, open = scan.open + 1 } :=
  match scan.previous with
    | None => rewrite within, opens, closes
    | Some before => rewrite within, lead, opens, closes

-- What may come before a token.

--| A token that may be the last before anything: no `->` and no comma.
def quietLast (kind: Tok): Bool := !(kind == Arrow) && !(kind == Comma)

theorem pairQuiet ∀ (last kind: Tok) (quiet: quietLast last = True): pairOk last kind = True :=
  rewrite Bool.notTrue _ (Bool.andLeft quiet),
      Bool.notTrue _ (Bool.andRight quiet),
      Bool.orTrue (!arrowFollow kind),
      Bool.orTrue (!kind.isCloser)

theorem goQuiet ∀ (scan: Scan) (last kind: Tok)
    (before: scan.previous = Some last)
    (quiet: quietLast last = True)
    (within: kind.within1 = True)
    (opens: kind.isOpener = False)
    (closes: kind.isCloser = False):
    scan.go kind = Some { previous = Some kind, open = scan.open } :=
  rewrite within, opens, closes, before, pairQuiet last kind quiet

--| A closing bracket, with the bracket it closes open.
theorem goClose ∀ (scan: Scan) (last kind: Tok) (depth: Nat)
    (before: scan.previous = Some last)
    (quiet: quietLast last = True)
    (within: kind.within1 = True)
    (opens: kind.isOpener = False)
    (closes: kind.isCloser = True)
    (deep: scan.open = depth + 1):
    scan.go kind = Some { previous = Some kind, open = depth } :=
  rewrite within, opens, closes, before, deep, pairQuiet last kind quiet

-- A token's own words.

theorem stepComment ∀ (scan: Scan) (text: Text) (comment: commentText text = True): scan.step text = Some scan :=
  rewrite Bool.andLeft comment

theorem stepToken ∀ (scan: Scan) (text: Text) (kind: Tok)
    (lexes: lexKind text = kind)
    (plain: text.startsWith "--" = False):
    scan.step text = scan.go kind :=
  rewrite plain, lexes

theorem runNotes ∀ (notes: List Note) (scan: Scan)
    (sound: notesSound notes = True):
    scan.run (notes.map (note => note.text)) = Some scan :=
  match notes with
    | [] => byComputing
    | [note, ..rest] =>
      rewrite stepComment scan note.text (Bool.andLeft sound) then runNotes rest scan (Bool.andRight sound)

theorem runAfter ∀ (after: Option Text) (scan: Scan)
    (sound: afterSound after = True):
    scan.run after.toList = Some scan :=
  match after with
    | None => byComputing
    | Some comment => rewrite stepComment scan comment sound

--| A token with its comments: they change nothing, the token takes `scan` to `next`.
theorem wordRun ∀ (word: Word) (hoisted: Bool) (scan next: Scan)
    (sound: word.sound = True)
    (step: scan.step word.text = Some next):
    scan.run (word.spelledAt hoisted) = Some next :=
  let front: scan.run (if hoisted then [] else word.comments.above.map (note => note.text)) = Some scan :=
    match hoisted with
      | True => byComputing
      | False => runNotes word.comments.above scan (Bool.andLeft (Bool.andRight sound))
  rewrite runAppend
        (if hoisted then [] else word.comments.above.map (note => note.text))
        ([word.text] ++ word.comments.after.toList)
        scan
        scan
        front,
      step then
    runAfter word.comments.after next (Bool.andRight (Bool.andRight sound))

--| What the passes need of a run of texts: from any state it comes back to the same number of open brackets, the
--| last token one that may be followed by anything.
def Runs (texts: List Text): Prop :=
  ∀ (scan: Scan) => ∃ (last: Tok) => scan.run texts = Some { previous = Some last, open = scan.open }
    ∧ quietLast last = True

--| The same, from a state whose last token is such a one.
def RunsAfter (texts: List Text): Prop :=
  ∀ (scan: Scan) (before: Tok) => scan.previous = Some before
    → quietLast before = True
    → ∃ (last: Tok) => scan.run texts = Some { previous = Some last, open = scan.open } ∧ quietLast last = True

theorem runsAfter ∀ (texts: List Text) (runs: Runs texts): RunsAfter texts := scan before same quiet => runs scan

-- The tokens the tree's operators are.

--| The kind the lexer gives a text is a token of the alphabet that is no bracket.
def opKind (text: Text): Bool := (lexKind text).within1 && !(lexKind text).isOpener && !(lexKind text).isCloser

--| An infix operator `within1` lets through has such a kind.
theorem opKindOf ∀ (text: Text) (listed: operatorText1 text = True): opKind text = True :=
  List.allMember opKind operators1 byComputing text (operatorListed text listed)

-- The tokens of an expression.

--| A name or numeral, which anything may precede and follow.
theorem atomRuns ∀ (word: Word) (kind: Tok) (hoisted: Bool)
    (sound: word.sound = True)
    (spells: Spells kind word.text)
    (within: kind.within1 = True)
    (lead: arrowFollow kind = False)
    (opens: kind.isOpener = False)
    (closes: kind.isCloser = False)
    (quiet: quietLast kind = True):
    Runs (word.spelledAt hoisted) :=
  scan =>
    Witness kind (
      wordRun word hoisted scan
        { previous = Some kind, open = scan.open }
        sound
        (Eq.trans
          (stepToken scan word.text kind
            (lexKindOfSpells kind word.text spells)
            (spellsNotComment kind word.text spells))
          (goFlat scan kind within lead opens closes)),
      quiet
    )

--| A bracketed run: the opening bracket, what is inside it and the closing bracket.
theorem runsBracket ∀ (open close: Word) (opening closing: Tok) (hoisted: Bool) (middle: List Text)
    (soundOpen: open.sound = True)
    (soundClose: close.sound = True)
    (spellsOpen: Spells opening open.text)
    (spellsClose: Spells closing close.text)
    (withinOpen: opening.within1 = True)
    (leadOpen: arrowFollow opening = False)
    (opens: opening.isOpener = True)
    (notCloser: opening.isCloser = False)
    (quietOpen: quietLast opening = True)
    (withinClose: closing.within1 = True)
    (notOpener: closing.isOpener = False)
    (closes: closing.isCloser = True)
    (quietClose: quietLast closing = True)
    (inside: RunsAfter middle):
    Runs (open.spelledAt hoisted ++ middle ++ close.spelledAt False) :=
  scan =>
    let first: Scan := { previous = Some opening, open = scan.open + 1 }
    let openRun: scan.run (open.spelledAt hoisted) = Some first :=
      wordRun open hoisted scan first soundOpen
        (Eq.trans
          (stepToken scan open.text opening
            (lexKindOfSpells opening open.text spellsOpen)
            (spellsNotComment opening open.text spellsOpen))
          (goOpen scan opening withinOpen leadOpen opens notCloser))
    match inside first opening byComputing quietOpen with
      | Witness last (middleRun, quietMiddle) =>
        let second: Scan := { previous = Some last, open = scan.open + 1 }
        let closeRun: second.run (close.spelledAt False) = Some { previous = Some closing, open = scan.open } :=
          wordRun close False second
            { previous = Some closing, open = scan.open }
            soundClose
            (Eq.trans
              (stepToken second close.text closing
                (lexKindOfSpells closing close.text spellsClose)
                (spellsNotComment closing close.text spellsClose))
              (goClose second last closing scan.open byComputing quietMiddle withinClose notOpener closes byComputing))
        Witness closing (
          rewrite runAppend (open.spelledAt hoisted) (middle ++ close.spelledAt False) scan first openRun,
              runAppend middle (close.spelledAt False) first second middleRun then
            closeRun,
          quietClose
        )

theorem commaStep ∀ (scan: Scan) (last: Tok)
    (before: scan.previous = Some last)
    (quiet: quietLast last = True):
    scan.step "," = Some { previous = Some Comma, open = scan.open } :=
  Eq.trans
    (stepToken scan "," Comma byComputing byComputing)
    (goQuiet scan last Comma before quiet byComputing byComputing byComputing)

--| The tokens of an expression, whatever the state before and after it, leave the brackets as they were.
--|
--| Proof idea: Induction on the expression; a name's or operator's token is in the alphabet and may follow any
--| token that isn't `->` or a comma, an expression's first token may follow anything, its last token is neither, and a
--| closing bracket finds its opening one.
theorem exprRuns ∀ (expr: Expr) (hoisted: Bool)
    (within: expr.within1 = True)
    (sound: expr.sound = True)
    (lexical: expr.lexical = True) (spelled: expr.operators):
    Runs (expr.spelt hoisted) :=
  match expr, spelled with
    | Atom kind word, _ =>
      match kind, within with
        | Lower, within =>
          atomRuns word Lower hoisted sound
            (spellsOfText1 Lower word.text within)
            byComputing
            byComputing
            byComputing
            byComputing
            byComputing
        | Upper, within =>
          atomRuns word Upper hoisted sound
            (spellsOfText1 Upper word.text within)
            byComputing
            byComputing
            byComputing
            byComputing
            byComputing
        | Num, within =>
          atomRuns word Num hoisted sound
            (spellsOfText1 Num word.text within)
            byComputing
            byComputing
            byComputing
            byComputing
            byComputing
        | Float, within =>
          atomRuns word Float hoisted sound
            (spellsOfText1 Float word.text within)
            byComputing
            byComputing
            byComputing
            byComputing
            byComputing
        | other, within => (Bool.falseNotTrue within).impossible
    | Paren open inner close, innerSpelled =>
      runsBracket open close LParen RParen hoisted
        (inner.spelt False)
        (Bool.andLeft sound)
        (Bool.andRight (Bool.andRight sound))
        (DecEq.sound (Bool.andLeft lexical))
        (DecEq.sound (Bool.andLeft (Bool.andRight lexical)))
        byComputing
        byComputing
        byComputing
        byComputing
        byComputing
        byComputing
        byComputing
        byComputing
        byComputing
        (runsAfter
          (inner.spelt False)
          (exprRuns inner False within
            (Bool.andLeft (Bool.andRight sound))
            (Bool.andRight (Bool.andRight lexical))
            innerSpelled))
    | Tuple open items comma close, itemsSpelled =>
      runsBracket open close LParen RParen hoisted
        (commaSpelt items)
        (Bool.andLeft sound)
        (Bool.andRight (Bool.andRight sound))
        (DecEq.sound (Bool.andLeft lexical))
        (DecEq.sound (Bool.andLeft (Bool.andRight lexical)))
        byComputing
        byComputing
        byComputing
        byComputing
        byComputing
        byComputing
        byComputing
        byComputing
        byComputing
        (commaRunsAfter items within
          (Bool.andLeft (Bool.andRight sound))
          (Bool.andRight (Bool.andRight lexical))
          itemsSpelled)
    | ListOf open items comma close, itemsSpelled =>
      runsBracket open close LBracket RBracket hoisted
        (commaSpelt items)
        (Bool.andLeft sound)
        (Bool.andRight (Bool.andRight sound))
        (DecEq.sound (Bool.andLeft lexical))
        (DecEq.sound (Bool.andLeft (Bool.andRight lexical)))
        byComputing
        byComputing
        byComputing
        byComputing
        byComputing
        byComputing
        byComputing
        byComputing
        byComputing
        (commaRunsAfter items within
          (Bool.andLeft (Bool.andRight sound))
          (Bool.andRight (Bool.andRight lexical))
          itemsSpelled)
    | App head arguments, (headSpelled, argumentsSpelled) =>
      let headRuns :=
        exprRuns head hoisted (Bool.andLeft within) (Bool.andLeft sound) (Bool.andLeft lexical) headSpelled
      let argumentsRuns :=
        argsRunsAfter arguments (Bool.andRight within) (Bool.andRight sound) (Bool.andRight lexical) argumentsSpelled
      scan =>
        match headRuns scan with
          | Witness lastHead (headRun, quietHead) =>
            match argumentsRuns { previous = Some lastHead, open = scan.open } lastHead byComputing quietHead with
              | Witness lastArgs (argsRun, quietArgs) => Witness lastArgs (
                rewrite runAppend
                      (head.spelt hoisted)
                      (argumentsSpelt arguments)
                      scan
                      { previous = Some lastHead, open = scan.open }
                      headRun then
                  argsRun,
                quietArgs
              )
    | Infix kind left operator right, (leftSpelled, (kindOfOperator, (operatorSpells, quiet)), rightSpelled) =>
      let (leftWithin, rightWithin) := infixWithin kind left operator right within
      let listed: operatorText1 operator.text = True := infixListed kind left operator right within
      let flat := opKindOf operator.text listed
      let leftRuns := exprRuns left hoisted leftWithin (Bool.andLeft sound) (Bool.andLeft lexical) leftSpelled
      let rightRuns :=
        exprRuns right False rightWithin
          (Bool.andRight (Bool.andRight sound))
          (Bool.andRight (Bool.andRight lexical))
          rightSpelled
      scan =>
        match leftRuns scan with
          | Witness lastLeft (leftRun, quietLeft) =>
            let middle: Scan := { previous = Some lastLeft, open = scan.open }
            let operatorRun: middle.run (operator.spelledAt False)
              = Some { previous = Some (lexKind operator.text), open = scan.open } :=
              wordRun operator False middle
                { previous = Some (lexKind operator.text), open = scan.open }
                (Bool.andLeft (Bool.andRight sound))
                (Eq.trans
                  (stepToken middle operator.text
                    (lexKind operator.text)
                    byComputing
                    (spellsNotComment kindOfOperator operator.text operatorSpells))
                  (goQuiet middle lastLeft
                    (lexKind operator.text)
                    byComputing
                    quietLeft
                    (Bool.andLeft flat)
                    (Bool.notTrue _ (Bool.andLeft (Bool.andRight flat)))
                    (Bool.notTrue _ (Bool.andRight (Bool.andRight flat)))))
            match rightRuns { previous = Some (lexKind operator.text), open = scan.open } with
              | Witness lastRight (rightRun, quietRight) => Witness lastRight (
                rewrite runAppend
                      (left.spelt hoisted)
                      (operator.spelledAt False ++ right.spelt False)
                      scan
                      middle
                      leftRun,
                    runAppend
                      (operator.spelledAt False)
                      (right.spelt False)
                      middle
                      { previous = Some (lexKind operator.text), open = scan.open }
                      operatorRun then
                  rightRun,
                quietRight
              )
    | Prefix operator operand, (prefix, operandSpelled) =>
      let operandRuns :=
        exprRuns operand False (Bool.andLeft within) (Bool.andRight sound) (Bool.andRight lexical) operandSpelled
      let operatorSound := Bool.andLeft sound
      scan =>
        match prefixStep scan operator.text prefix with
          | Witness kind step =>
            let operatorRun: scan.run (operator.spelledAt hoisted) = Some { previous = Some kind, open = scan.open } :=
              wordRun operator hoisted scan { previous = Some kind, open = scan.open } operatorSound step
            match operandRuns { previous = Some kind, open = scan.open } with
              | Witness lastOperand (operandRun, quietOperand) => Witness lastOperand (
                rewrite runAppend
                      (operator.spelledAt hoisted)
                      (operand.spelt False)
                      scan
                      { previous = Some kind, open = scan.open }
                      operatorRun then
                  operandRun,
                quietOperand
              )

theorem prefixStep ∀ (scan: Scan) (text: Text)
    (prefix: PrefixSpells text):
    ∃ (kind: Tok) => scan.step text = Some { previous = Some kind, open = scan.open } :=
  match prefix with
    | Inl same =>
      Witness Minus
        (rewrite same then
          Eq.trans
            (stepToken scan "-" Minus byComputing byComputing)
            (goFlat scan Minus byComputing byComputing byComputing byComputing))
    | Inr (Inl same) =>
      Witness Bang
        (rewrite same then
          Eq.trans
            (stepToken scan "!" Bang byComputing byComputing)
            (goFlat scan Bang byComputing byComputing byComputing byComputing))
    | Inr (Inr same) =>
      Witness Bang
        (rewrite same then
          Eq.trans
            (stepToken scan "¬" Bang byComputing byComputing)
            (goFlat scan Bang byComputing byComputing byComputing byComputing))

--| A bracket's items, with the commas between them: a run from any state when there is an item.
theorem commaRuns ∀ (first: Expr) (rest: List Expr)
    (within: allWithin1 [first, ..rest] = True)
    (sound: allSound [first, ..rest] = True)
    (lexical: allLexical [first, ..rest] = True)
    (spelled: AllOperators [first, ..rest]):
    Runs (commaSpelt [first, ..rest]) :=
  match rest, spelled with
    | [], (firstSpelled, _) =>
      exprRuns first False (Bool.andLeft within) (Bool.andLeft sound) (Bool.andLeft lexical) firstSpelled
    | [next, ..more], (firstSpelled, othersSpelled) =>
      let firstRuns :=
        exprRuns first False (Bool.andLeft within) (Bool.andLeft sound) (Bool.andLeft lexical) firstSpelled
      let restRuns :=
        commaRuns next more (Bool.andRight within) (Bool.andRight sound) (Bool.andRight lexical) othersSpelled
      scan =>
        match firstRuns scan with
          | Witness lastFirst (firstRun, quietFirst) =>
            let afterFirst: Scan := { previous = Some lastFirst, open = scan.open }
            let afterComma: Scan := { previous = Some Comma, open = scan.open }
            match restRuns afterComma with
              | Witness lastRest (restRun, quietRest) => Witness lastRest (
                rewrite runAppend (first.spelt False) ([","] ++ commaSpelt [next, ..more]) scan afterFirst firstRun,
                    commaStep afterFirst lastFirst byComputing quietFirst then
                  restRun,
                quietRest
              )

theorem commaRunsAfter ∀ (items: List Expr)
    (within: allWithin1 items = True)
    (sound: allSound items = True)
    (lexical: allLexical items = True)
    (spelled: AllOperators items):
    RunsAfter (commaSpelt items) :=
  match items with
    | [] => scan before same quiet =>
      match scan with
        | { previous, open } => Witness before ((rewrite same), quiet)
    | [first, ..rest] => runsAfter (commaSpelt [first, ..rest]) (commaRuns first rest within sound lexical spelled)

--| A call's arguments.
theorem argsRunsAfter ∀ (arguments: List Expr)
    (within: allWithin1 arguments = True)
    (sound: allSound arguments = True)
    (lexical: allLexical arguments = True)
    (spelled: AllOperators arguments):
    RunsAfter (argumentsSpelt arguments) :=
  match arguments, spelled with
    | [], _ => scan before same quiet =>
      match scan with
        | { previous, open } => Witness before ((rewrite same), quiet)
    | [argument, ..rest], (firstSpelled, othersSpelled) =>
      let firstRuns :=
        exprRuns argument False (Bool.andLeft within) (Bool.andLeft sound) (Bool.andLeft lexical) firstSpelled
      let restRuns :=
        argsRunsAfter rest (Bool.andRight within) (Bool.andRight sound) (Bool.andRight lexical) othersSpelled
      scan before same quiet =>
        match firstRuns scan with
          | Witness lastFirst (firstRun, quietFirst) =>
            match restRuns { previous = Some lastFirst, open = scan.open } lastFirst byComputing quietFirst with
              | Witness lastRest (restRun, quietRest) => Witness lastRest (
                rewrite runAppend
                      (argument.spelt False)
                      (argumentsSpelt rest)
                      scan
                      { previous = Some lastFirst, open = scan.open }
                      firstRun then
                  restRun,
                quietRest
              )

-- A declaration.

--| A name's kind, lower case or upper case, is a plain token: no arrow follows it, and it opens and closes nothing.
theorem nameKindFlat ∀ (kind: Tok)
    (isName: kind = Lower ∨ kind = Upper):
    kind.within1 = True ∧ arrowFollow kind = False ∧ kind.isOpener = False ∧ kind.isCloser = False :=
  match isName with | Inl same | Inr same => rewrite same then (byComputing, byComputing, byComputing, byComputing)

def Scan.start: Scan := { previous = None, open = 0 }

--| A declaration's printed texts pass the scan from the start of the file and end with no bracket open, the last
--| token one that may be followed by anything.
--|
--| Proof idea: the keyword, name, colon and `:=` are tokens of a plain kind that any token may follow
--| (`goFlat`), the type and the value are `exprRuns`.
theorem declRuns ∀ (decl: Decl)
    (within: decl.within1 = True)
    (sound: decl.sound = True)
    (lexical: decl.lexical = True) (spelled: decl.operators):
    ∃ (last: Tok) => Scan.start.run decl.spelt = Some { previous = Some last, open = 0 } ∧ quietLast last = True :=
  match decl with
    | Definition [] header (Assigned colonEq value) =>
      match header with
        | {
            exportKeyword = None,
            opaqueKeyword = None,
            kind = DefPlain,
            keyword,
            name,
            forallKeyword = None,
            params = [],
            colon,
            result,
            decreasingClause = None,
            unfoldingClause = None
          } =>
          let (resultSpelled, valueSpelled) := spelled
          let (nameKind, nameSpells, _, nameIsName) := nameKinded name (Bool.andLeft (Bool.andLeft within))
          let (nameWithinKind, nameLead, nameOpens, nameCloses) := nameKindFlat nameKind nameIsName
          let keywordWord := fixedWord "def" keyword
          let colonWord := fixedWord ":" colon
          let assignWord := fixedWord ":=" colonEq
          let resultRuns :=
            exprRuns result False
              (Bool.andRight (Bool.andLeft within))
              (Bool.andLeft (Bool.andRight (Bool.andRight (Bool.andRight sound))))
              (Bool.andLeft (Bool.andRight lexical))
              resultSpelled
          let valueRuns :=
            exprRuns value False
              (Bool.andRight within)
              (Bool.andRight (Bool.andRight (Bool.andRight (Bool.andRight (Bool.andRight sound)))))
              (Bool.andRight (Bool.andRight lexical))
              valueSpelled
          let afterKeyword: Scan := { previous = Some KwDef, open = 0 }
          let afterName: Scan := { previous = Some nameKind, open = 0 }
          let afterColon: Scan := { previous = Some Colon, open = 0 }
          let keywordRun: Scan.start.run (keywordWord.spelledAt True) = Some afterKeyword :=
            wordRun keywordWord True Scan.start afterKeyword
              (Bool.andLeft sound)
              (Eq.trans
                (stepToken Scan.start "def" KwDef byComputing byComputing)
                (goFlat Scan.start KwDef byComputing byComputing byComputing byComputing))
          let nameRun: afterKeyword.run (name.spelledAt False) = Some afterName :=
            wordRun name False afterKeyword afterName
              (Bool.andLeft (Bool.andRight sound))
              (Eq.trans
                (stepToken afterKeyword name.text nameKind
                  (lexKindOfSpells nameKind name.text nameSpells)
                  (spellsNotComment nameKind name.text nameSpells))
                (goFlat afterKeyword nameKind nameWithinKind nameLead nameOpens nameCloses))
          let colonRun: afterName.run (colonWord.spelledAt False) = Some afterColon :=
            wordRun colonWord False afterName afterColon
              (Bool.andLeft (Bool.andRight (Bool.andRight sound)))
              (Eq.trans
                (stepToken afterName ":" Colon byComputing byComputing)
                (goFlat afterName Colon byComputing byComputing byComputing byComputing))
          match resultRuns afterColon with
            | Witness lastResult (resultRun, quietResult) =>
              let afterResult: Scan := { previous = Some lastResult, open = 0 }
              let afterAssign: Scan := { previous = Some ColonEq, open = 0 }
              let assignRun: afterResult.run (assignWord.spelledAt False) = Some afterAssign :=
                wordRun assignWord False afterResult afterAssign
                  (Bool.andLeft (Bool.andRight (Bool.andRight (Bool.andRight (Bool.andRight sound)))))
                  (Eq.trans
                    (stepToken afterResult ":=" ColonEq byComputing byComputing)
                    (goFlat afterResult ColonEq byComputing byComputing byComputing byComputing))
              match valueRuns afterAssign with
                | Witness lastValue (valueRun, quietValue) =>
                  let front: Scan.start.run (keywordWord.spelledAt True ++ name.spelledAt False) = Some afterName :=
                    rewrite runAppend
                          (keywordWord.spelledAt True)
                          (name.spelledAt False)
                          Scan.start
                          afterKeyword
                          keywordRun then
                      nameRun
                  let middle: afterName.run (colonWord.spelledAt False ++ result.spelt False) = Some afterResult :=
                    rewrite runAppend
                          (colonWord.spelledAt False)
                          (result.spelt False)
                          afterName
                          afterColon
                          colonRun then
                      resultRun
                  let head: Scan.start.run
                    ((keywordWord.spelledAt True ++ name.spelledAt False)
                      ++ colonWord.spelledAt False
                      ++ result.spelt False)
                    = Some afterResult :=
                    rewrite runAppend
                          (keywordWord.spelledAt True ++ name.spelledAt False)
                          (colonWord.spelledAt False ++ result.spelt False)
                          Scan.start
                          afterName
                          front then
                      middle
                  Witness lastValue (
                    rewrite runAppend
                          ((keywordWord.spelledAt True ++ name.spelledAt False)
                            ++ colonWord.spelledAt False
                            ++ result.spelt False)
                          (assignWord.spelledAt False ++ value.spelt False)
                          Scan.start
                          afterResult
                          head,
                        runAppend
                          (assignWord.spelledAt False)
                          (value.spelt False)
                          afterResult
                          afterAssign
                          assignRun then
                      valueRun,
                    quietValue
                  )
        | _ => cases

-- From the texts to the leaves.

theorem filterNotComment ∀ (texts: List Text): ((texts.filter notComment).all notComment) = True := match texts with
  | [] => byComputing
  | [text, ..rest] =>
    match notComment text with
      | True => rewrite filterNotComment rest
      | False => filterNotComment rest

theorem stepStarts ∀ (scan: Scan) (text: Text) (comment: text.startsWith "--" = True): scan.step text = Some scan :=
  rewrite comment

--| Comments aren't scanned, so the scan of the texts is the scan of those that aren't comments.
theorem runFilter ∀ (texts: List Text) (scan: Scan): scan.run texts = scan.run (texts.filter notComment) :=
  match texts with
    | [] => byComputing
    | [text, ..rest] =>
      match step: scan.step text with
        | Some next =>
          match comment: text.startsWith "--" with
            | True => rewrite Option.someInjective step then runFilter rest next
            | False => runFilter rest next
        | None =>
          match comment: text.startsWith "--" with
            | False => rewrite step

theorem goFacts ∀ (scan next: Scan) (kind: Tok)
    (go: scan.go kind = Some next):
    (kind.within1 && prevOk scan.previous kind) = True ∧ next.previous = Some kind :=
  match ok: kind.within1 && prevOk scan.previous kind && (!kind.isCloser || scan.open > 0) with
    | True => (Bool.andIntro (Bool.andLeft ok) (Bool.andLeft (Bool.andRight ok)), rewrite <- Option.someInjective go)

theorem runStep ∀ (scan end: Scan) (text: Text) (rest: List Text)
    (run: scan.run [text, ..rest] = Some end):
    ∃ (next: Scan) => scan.step text = Some next ∧ next.run rest = Some end :=
  match step: scan.step text with | Some next => Witness next (step, run)

--| Whether a token of kind `first` may follow the scan's last.
def headOk (scan: Scan) (leaves: List Leaf): Bool := match leaves with
  | [first, .._] => prevOk scan.previous first.token.kind
  | [] => True

--| Each leaf of the list may follow the one before.
def leafPairs: List Leaf → Bool
  | [first, second, ..rest] => pairOk first.token.kind second.token.kind && leafPairs [second, ..rest]
  | _ => True

def leafWithin (leaves: List Leaf): Bool := leaves.all (leaf => leaf.token.kind.within1)

--| What a successful scan of the leaves' texts says of the leaves, whose kinds are the lexer's.
theorem leafScan ∀ (leaves: List Leaf) (scan end: Scan)
    (kinded: leaves.all Leaf.kinded = True)
    (plain: (tokenTexts leaves).all notComment = True)
    (run: scan.run (tokenTexts leaves) = Some end):
    leafWithin leaves = True ∧ leafPairs leaves = True ∧ headOk scan leaves = True :=
  match leaves with
    | [] => (byComputing, byComputing, byComputing)
    | [leaf, ..rest] =>
      match runStep scan end leaf.token.text (tokenTexts rest) run with
        | Witness next (step, restRun) =>
          let lexes: lexKind leaf.token.text = leaf.token.kind := (DecEq.sound (Bool.andLeft kinded)).flipped
          let go: scan.go leaf.token.kind = Some next :=
            Eq.trans
              (stepToken scan leaf.token.text leaf.token.kind lexes (Bool.notTrue _ (Bool.andLeft plain))).flipped
              step
          let facts := goFacts scan next leaf.token.kind go
          let (within, pairs, head) := leafScan rest next end (Bool.andRight kinded) (Bool.andRight plain) restRun
          (
            Bool.andIntro (Bool.andLeft facts.left) within,
            match rest with
              | [] => byComputing
              | [second, ..more] => Bool.andIntro (rewrite facts.right at head then head) pairs,
            Bool.andRight facts.left
          )

-- A declaration's leaves.

--| The leaves of a declaration are in the alphabet, and each may follow the one before.
theorem declLeaves ∀ (decl: Decl)
    (within: decl.within1 = True)
    (shaped: decl.shaped = True)
    (settled: decl.settled = True)
    (lexical: decl.lexical = True):
    leafWithin decl.leaves = True ∧ leafPairs decl.leaves = True :=
  let sound := declSoundOfSettled decl within settled (declRealOfLexical decl within lexical)
  let (texts, kinded) := printedTokens1 decl within shaped settled lexical
  match declRuns decl within sound lexical (declOperators decl within) with
    | Witness last (run, quiet) =>
      let filtered: Scan.start.run (decl.spelt.filter notComment) = Some { previous = Some last, open = 0 } :=
        Eq.trans (runFilter decl.spelt Scan.start).flipped run
      let plain: (tokenTexts decl.leaves).all notComment = True := rewrite texts then filterNotComment decl.spelt
      let (within, pairs, head) :=
        leafScan decl.leaves Scan.start { previous = Some last, open = 0 } kinded plain (rewrite texts then filtered)
      (within, pairs)

theorem leafWithinAppend ∀ (xs ys: List Leaf): leafWithin (xs ++ ys) = (leafWithin xs && leafWithin ys) := match xs with
  | [] => byComputing
  | [first, ..rest] =>
    match first.token.kind.within1 with
      | True => leafWithinAppend rest ys
      | False => byComputing

theorem headedWithin ∀ (above: List Comment) (blank: Nat) (leaves: List Leaf):
    leafWithin (headed above blank leaves) = leafWithin leaves :=
  match leaves with | [] | [_, .._] => byComputing

theorem declLaidWithin ∀ (decl: Decl) (empty: Bool)
    (within: leafWithin decl.leaves = True):
    leafWithin (decl.laid empty) = True :=
  rewrite headedWithin
        (laidNotes empty decl.firstComments.above)
        (if decl.firstComments.blankBefore && !(empty && decl.firstComments.above.isEmpty) then 1 else 0)
        decl.leaves then
    within

theorem groupsWithin ∀ (empty: Bool) (decls: List Decl)
    (within: decls.all Decl.within1 = True)
    (shaped: decls.all Decl.shaped = True)
    (settled: decls.all Decl.settled = True)
    (lexical: decls.all Decl.lexical = True):
    leafWithin (groupsFrom empty decls).concat = True :=
  match decls with
    | [] => byComputing
    | [decl, ..rest] =>
      let (leavesWithin, leavesPairs) :=
        declLeaves decl (Bool.andLeft within) (Bool.andLeft shaped) (Bool.andLeft settled) (Bool.andLeft lexical)
      rewrite leafWithinAppend (decl.laid empty) (groupsFrom False rest).concat,
          declLaidWithin decl empty leavesWithin then
        groupsWithin False rest
          (Bool.andRight within)
          (Bool.andRight shaped)
          (Bool.andRight settled)
          (Bool.andRight lexical)

-- The brackets a declaration's leaves open.

--| The open brackets after a token of kind `kind`.
def bump (open: Nat) (kind: Tok): Nat :=
  if kind.isOpener then open + 1
  else if kind.isCloser then open - 1
  else open

--| Each closer finds a bracket open, `open` the number open before the leaves.
def closersDeep (open: Nat): List Leaf → Bool
  | [] => True
  | [leaf, ..rest] => (!leaf.token.kind.isCloser || open > 0) && closersDeep (bump open leaf.token.kind) rest

--| The number of brackets open after the leaves.
def bumpAll (open: Nat): List Leaf → Nat
  | [] => open
  | [leaf, ..rest] => bumpAll (bump open leaf.token.kind) rest

theorem goDepth ∀ (scan next: Scan) (kind: Tok)
    (go: scan.go kind = Some next):
    (!kind.isCloser || scan.open > 0) = True ∧ next.open = bump scan.open kind :=
  match ok: kind.within1 && prevOk scan.previous kind && (!kind.isCloser || scan.open > 0) with
    | True => (Bool.andRight (Bool.andRight ok), rewrite <- Option.someInjective go)

--| What a successful scan of the leaves' texts says of their brackets.
theorem leafDepth ∀ (leaves: List Leaf) (scan end: Scan)
    (kinded: leaves.all Leaf.kinded = True)
    (plain: (tokenTexts leaves).all notComment = True)
    (run: scan.run (tokenTexts leaves) = Some end):
    closersDeep scan.open leaves = True ∧ bumpAll scan.open leaves = end.open :=
  match leaves with
    | [] => (byComputing, rewrite Option.someInjective run)
    | [leaf, ..rest] =>
      match runStep scan end leaf.token.text (tokenTexts rest) run with
        | Witness next (step, restRun) =>
          let lexes: lexKind leaf.token.text = leaf.token.kind := (DecEq.sound (Bool.andLeft kinded)).flipped
          let go: scan.go leaf.token.kind = Some next :=
            Eq.trans
              (stepToken scan leaf.token.text leaf.token.kind lexes (Bool.notTrue _ (Bool.andLeft plain))).flipped
              step
          let facts := goDepth scan next leaf.token.kind go
          let (deep, total) := leafDepth rest next end (Bool.andRight kinded) (Bool.andRight plain) restRun
          (Bool.andIntro facts.left (rewrite facts.right at deep then deep), rewrite facts.right at total then total)

--| A declaration's brackets are balanced, each closer after its opener.
theorem declDepth ∀ (decl: Decl)
    (within: decl.within1 = True)
    (shaped: decl.shaped = True)
    (settled: decl.settled = True)
    (lexical: decl.lexical = True):
    closersDeep 0 decl.leaves = True ∧ bumpAll 0 decl.leaves = 0 :=
  let sound := declSoundOfSettled decl within settled (declRealOfLexical decl within lexical)
  let (texts, kinded) := printedTokens1 decl within shaped settled lexical
  match declRuns decl within sound lexical (declOperators decl within) with
    | Witness last (run, quiet) =>
      let filtered: Scan.start.run (decl.spelt.filter notComment) = Some { previous = Some last, open = 0 } :=
        Eq.trans (runFilter decl.spelt Scan.start).flipped run
      let plain: (tokenTexts decl.leaves).all notComment = True := rewrite texts then filterNotComment decl.spelt
      leafDepth decl.leaves Scan.start { previous = Some last, open = 0 } kinded plain (rewrite texts then filtered)

-- Where `hangs` lets a leaf stand in column 0.

--| A leaf that starts a line in column 0 is a closer or `:=`.
def colStarts (leaves: List Leaf): Bool := leaves.all (leaf =>
  !(leaf.token.column == 0 && leaf.token.lineStart) || leaf.token.kind.isCloser || leaf.token.kind == ColonEq)

theorem stepColNone ∀ (state: HangState) (leaf: Leaf)
    (zero: (leaf.token.column == 0) = True)
    (starts: leaf.token.lineStart = True)
    (notCloser: leaf.token.kind.isCloser = False)
    (notAssign: (leaf.token.kind == ColonEq) = False):
    state.step leaf = None :=
  rewrite DecEq.sound zero, starts, notCloser, notAssign then
    match state.glue with
      | True => byComputing
      | False =>
        match isComma: leaf.token.kind == Comma with
          | True =>
            match state.blocks with
              | [] => byComputing
              | [block, ..outer] => rewrite starts
          | False => byComputing

theorem stepColCont ∀ (state: HangState) (leaf: Leaf) (next: HangState)
    (step: state.step leaf = Some next)
    (zero: (leaf.token.column == 0) = True)
    (starts: leaf.token.lineStart = True)
    (notCloser: leaf.token.kind.isCloser = False)
    (notAssign: (leaf.token.kind == ColonEq) = False):
    Void :=
  (Option.noneNotSome next (Eq.trans (stepColNone state leaf zero starts notCloser notAssign).flipped step)).impossible

theorem stepCol ∀ (state: HangState) (leaf: Leaf) (next: HangState)
    (step: state.step leaf = Some next):
    (!(leaf.token.column == 0 && leaf.token.lineStart) || leaf.token.kind.isCloser || leaf.token.kind == ColonEq)
      = True :=
  let cont := stepColCont state leaf next step
  match flat: leaf.token.column == 0 && leaf.token.lineStart with
    | False => byComputing
    | True =>
      match closer: leaf.token.kind.isCloser with
        | True => byComputing
        | False =>
          match assign: leaf.token.kind == ColonEq with
            | True => byComputing
            | False => (cont (Bool.andLeft flat) (Bool.andRight flat) closer assign).impossible

theorem hangsFromCol ∀ (leaves: List Leaf) (state: HangState)
    (hung: hangsFrom state leaves = True):
    colStarts leaves = True :=
  match leaves with
    | [] => byComputing
    | [leaf, ..rest] =>
      match hungStep state leaf rest hung with
        | Witness next (step, more) => Bool.andIntro (stepCol state leaf next step) (hangsFromCol rest next more)

-- A leaf in column 0 starts its line.

--| A leaf in column 0 starts its line.
def colLines (leaves: List Leaf): Bool := leaves.all (leaf => !(leaf.token.column == 0) || leaf.token.lineStart)

--| The layout so far: the line has a token on it or the column isn't 0, and each leaf made keeps `colLines`.
def laidOk (laid: Laid): Bool := (laid.freshLine || !(laid.column == 0)) && colLines laid.leaves

--| A text that isn't empty has bytes.
theorem textBytes ∀ (text: Text) (filled: text.toList ≠ []): (text.utf8Length == 0) = False :=
  rewrite utf8OfText text then
    match text.toList with
      | [] => (filled byComputing).impossible
      | [char, ..more] => Nat.addNeZeroLeft (Char.utf8 char).length (utf8Chars more) (Char.utf8LengthNeZero char)

theorem colLinesWithTrailing ∀ (leaves: List Leaf) (comment: Comment):
    colLines (withTrailing leaves comment) = colLines leaves :=
  match leaves with | [] | [_, .._] => byComputing

theorem layOk ∀ (laid: Laid) (piece: Piece)
    (ok: laidOk laid = True) (plain: piece.Plain):
    laidOk (laid.lay piece) = True :=
  match piece with
    | Code kind text =>
      Bool.andIntro
        (rewrite Nat.addNeZeroRight text.utf8Length laid.column (textBytes text plain.left))
        (Bool.andIntro (Bool.orSwapTrue _ _ (Bool.andLeft ok)) (Bool.andRight ok))
    | Gap count =>
      match laid.freshLine with
        | True => ok
        | False =>
          Bool.andIntro
            (rewrite Nat.addNeZeroLeft laid.column count (Bool.notTrue _ (Bool.andLeft ok)))
            (Bool.andRight ok)
    | Break => Bool.andRight ok
    | Remark text =>
      match laid.freshLine with
        | True => ok
        | False =>
          Bool.andIntro
            (rewrite Nat.addNeZeroLeft laid.column text.utf8Length (Bool.notTrue _ (Bool.andLeft ok)))
            (rewrite colLinesWithTrailing laid.leaves {
                  text = withoutReturn text,
                  column = laid.column,
                  blankLines = 0
                } then
              Bool.andRight ok)

theorem foldOk ∀ (pieces: List Piece) (laid: Laid)
    (ok: laidOk laid = True)
    (plain: AllPlain pieces):
    laidOk (pieces.foldLeft laid Laid.lay) = True :=
  match pieces with
    | [] => ok
    | [piece, ..rest] => foldOk rest (laid.lay piece) (layOk laid piece ok plain.left) plain.right

--| A declaration's leaves in column 0 start their lines.
theorem declColLines ∀ (decl: Decl)
    (within: decl.within1 = True)
    (shaped: decl.shaped = True)
    (settled: decl.settled = True)
    (lexical: decl.lexical = True):
    colLines decl.leaves = True :=
  let (plain, _, _, _) := declPiecesOk decl within shaped settled lexical
  let made := Bool.andRight (foldOk decl.pieces Laid.start byComputing plain)
  rewrite leavesOfPieces decl then
    List.allReverseOntoTrue
      (leaf => !(leaf.token.column == 0) || leaf.token.lineStart)
      (decl.pieces.foldLeft Laid.start Laid.lay).leaves
      []
      made
      byComputing

-- The parser's groups.

--| The splitter in a declaration, `open` brackets open.
def Splitter.at (open: Nat): Splitter := { depth = 0, opening = False, attributesOnly = False, openBrackets = open }

--| A leaf after a declaration's `def` starts no group: it is not in column 0, or is `:=`, or is a comma or closer
--| inside a bracket.
def stays (open: Nat) (leaf: Leaf): Bool :=
  !(leaf.token.column == 0
    && leaf.token.kind != ColonEq
    && !(open > 0 && (leaf.token.kind == Comma || leaf.token.kind.isCloser)))

def Stays (open: Nat): List Leaf → Bool
  | [] => True
  | [leaf, ..rest] => stays open leaf && Stays (bump open leaf.token.kind) rest

--| A leaf that starts no group leaves the splitter in a declaration, with the bracket counted.
theorem splitStay ∀ (open: Nat) (current: List Leaf) (groups: List (List Leaf)) (leaf: Leaf) (rest: List Leaf)
    (within: leaf.token.kind.within1 = True)
    (stay: stays open leaf = True):
    splitFrom (Splitter.at open) current groups [leaf, ..rest]
      = splitFrom (Splitter.at (bump open leaf.token.kind)) [leaf, ..current] groups rest :=
  rewrite within1Not leaf.token.kind At byComputing within then
    match zero: leaf.token.column == 0 with
      | False => rewrite Bool.andFalse leaf.token.kind.isOpener, Bool.andFalse leaf.token.kind.isCloser
      | True =>
        match assign: leaf.token.kind != ColonEq with
          | False => rewrite Bool.andFalse leaf.token.kind.isOpener, Bool.andFalse leaf.token.kind.isCloser
          | True =>
            match inner: open > 0 && (leaf.token.kind == Comma || leaf.token.kind.isCloser) with
              | True => rewrite Bool.andFalse leaf.token.kind.isOpener, Bool.andFalse leaf.token.kind.isCloser

--| A declaration's `def`, in column 0, starts a group; the leaves are then the group's.
theorem splitStart ∀ (current: List Leaf) (groups: List (List Leaf)) (leaf: Leaf) (rest: List Leaf)
    (zero: (leaf.token.column == 0) = True)
    (keyword: (leaf.token.kind == KwDef) = True):
    splitFrom (Splitter.at 0) current groups [leaf, ..rest]
      = splitFrom (Splitter.at 0) [leaf] (if current.isEmpty then groups else [current.reverse, ..groups]) rest :=
  rewrite DecEq.sound zero, DecEq.sound keyword

theorem tailSplit ∀ (tail: List Leaf) (open: Nat) (current: List Leaf) (groups: List (List Leaf)) (rest: List Leaf)
    (within: leafWithin tail = True)
    (stay: Stays open tail = True):
    splitFrom (Splitter.at open) current groups (tail ++ rest)
      = splitFrom (Splitter.at (bumpAll open tail)) (tail.reverseOnto current) groups rest :=
  match tail with
    | [] => byComputing
    | [leaf, ..more] =>
      Eq.trans
        (splitStay open current groups leaf (more ++ rest) (Bool.andLeft within) (Bool.andLeft stay))
        (tailSplit more
          (bump open leaf.token.kind)
          [leaf, ..current]
          groups
          rest
          (Bool.andRight within)
          (Bool.andRight stay))

--| A declaration's leaves, from its `def`, are one group.
theorem declSplit ∀ (above: List Comment) (blank: Nat) (first: Leaf)
    (tail rest current: List Leaf) (groups: List (List Leaf))
    (zero: (first.token.column == 0) = True)
    (keyword: (first.token.kind == KwDef) = True)
    (within: leafWithin tail = True)
    (stay: Stays 0 tail = True)
    (balanced: bumpAll 0 tail = 0):
    splitFrom (Splitter.at 0) current groups (headed above blank [first, ..tail] ++ rest)
      = splitFrom
        (Splitter.at 0)
        (headed above blank [first, ..tail]).reverse
        (if current.isEmpty then groups else [current.reverse, ..groups])
        rest :=
  let tailRun :=
    tailSplit tail 0
      [{ first | trivia = { first.trivia | leading = above, blankLines = blank } }]
      (if current.isEmpty then groups else [current.reverse, ..groups])
      rest
      within
      stay
  Eq.trans
    (splitStart current groups
      { first | trivia = { first.trivia | leading = above, blankLines = blank } }
      (tail ++ rest)
      zero
      keyword)
    (rewrite balanced at tailRun then tailRun)

--| No leaf after a declaration's `def` starts a group: in column 0 a leaf starts its line (`colLines`), so it is a
--| closer, which finds its bracket open (`closersDeep`), or `:=` (`colStarts`).
theorem staysOf ∀ (open: Nat) (tail: List Leaf)
    (deep: closersDeep open tail = True)
    (lines: colLines tail = True)
    (starts: colStarts tail = True):
    Stays open tail = True :=
  match tail with
    | [] => byComputing
    | [leaf, ..rest] =>
      let deeper := Bool.andLeft deep
      let lined := Bool.andLeft lines
      let started := Bool.andLeft starts
      let recur :=
        staysOf (bump open leaf.token.kind) rest (Bool.andRight deep) (Bool.andRight lines) (Bool.andRight starts)
      match zero: leaf.token.column == 0 with
        | False => Bool.andIntro byComputing recur
        | True =>
          match closer: leaf.token.kind.isCloser with
            | True =>
              Bool.andIntro
                (rewrite Bool.orTrue (leaf.token.kind == Comma), deeper, Bool.andFalse (leaf.token.kind != ColonEq))
                recur
            | False =>
              match assign: leaf.token.kind == ColonEq with
                | True => Bool.andIntro byComputing recur
                | False => (Bool.falseNotTrue (rewrite lined at started then started)).impossible

--| `hangs` gives the leaves after `def` their line rule: none in column 0 but a closer or `:=` starts a line.
theorem hangsCol ∀ (first: Leaf) (tail: List Leaf) (hung: hangs [first, ..tail] = True): colStarts tail = True :=
  hangsFromCol tail HangState.initial (Bool.andRight (Bool.andRight hung))

--| One declaration's leaves, as laid in the file, are one group: the splitter reads them from a state that is
--| outside any declaration, and leaves it so.
theorem laidSplit ∀ (decl: Decl) (empty: Bool) (rest current: List Leaf) (groups: List (List Leaf))
    (within: decl.within1 = True)
    (shaped: decl.shaped = True)
    (settled: decl.settled = True)
    (lexical: decl.lexical = True)
    (hung: hangs decl.leaves = True):
    splitFrom (Splitter.at 0) current groups (decl.laid empty ++ rest)
      = splitFrom
        (Splitter.at 0)
        (decl.laid empty).reverse
        (if current.isEmpty then groups else [current.reverse, ..groups])
        rest :=
  let (leavesWithin, _) := declLeaves decl within shaped settled lexical
  let (deepAll, balancedAll) := declDepth decl within shaped settled lexical
  let lined := declColLines decl within shaped settled lexical
  let starts := declStartsKw decl within shaped settled lexical
  match shows: decl.leaves with
    | [first, ..tail] =>
      let keyword: (first.token.kind == KwDef) = True := Bool.andLeft hung
      let zero: (first.token.column == 0) = True := Bool.andLeft (Bool.andRight hung)
      let deep: closersDeep 0 tail = True := rewrite DecEq.sound keyword at deepAll then deepAll
      let balanced: bumpAll 0 tail = 0 := rewrite DecEq.sound keyword at balancedAll then balancedAll
      declSplit
        (laidNotes empty decl.firstComments.above)
        (if decl.firstComments.blankBefore && !(empty && decl.firstComments.above.isEmpty) then 1 else 0)
        first
        tail
        rest
        current
        groups
        zero
        keyword
        (Bool.andRight leavesWithin)
        (staysOf 0 tail deep (Bool.andRight lined) (hangsCol first tail hung))
        balanced

theorem flushLaid ∀ (laid: List Leaf) (groups: List (List Leaf))
    (filled: kindFirst laid = True):
    (if laid.reverse.isEmpty then groups else [laid.reverse.reverse, ..groups]) = [laid, ..groups] :=
  match laid with
    | [first, ..rest] => rewrite List.reverseOntoNonEmpty rest [first] byComputing, List.reverseReverse [first, ..rest]

--| The splitter cuts the file's leaves into the declarations'.
theorem groupsSplit ∀ (empty: Bool) (decls: List Decl) (current: List Leaf) (groups: List (List Leaf))
    (within: decls.all Decl.within1 = True)
    (shaped: decls.all Decl.shaped = True)
    (settled: decls.all Decl.settled = True)
    (lexical: decls.all Decl.lexical = True)
    (hung: decls.all (decl => hangs decl.leaves) = True):
    splitFrom (Splitter.at 0) current groups (groupsFrom empty decls).concat
      = (if current.isEmpty then groups else [current.reverse, ..groups]).reverse ++ groupsFrom empty decls :=
  match decls with
    | [] => Eq.flipped (List.appendNil _)
    | [decl, ..rest] =>
      let first :=
        declStartsKw decl (Bool.andLeft within) (Bool.andLeft shaped) (Bool.andLeft settled) (Bool.andLeft lexical)
      let laidFirst: kindFirst (decl.laid empty) = True :=
        rewrite headedFirst
              (laidNotes empty decl.firstComments.above)
              (if decl.firstComments.blankBefore && !(empty && decl.firstComments.above.isEmpty) then 1 else 0)
              decl.leaves then
          first
      let flushed := if current.isEmpty then groups else [current.reverse, ..groups]
      let rec :=
        groupsSplit False rest
          (decl.laid empty).reverse
          flushed
          (Bool.andRight within)
          (Bool.andRight shaped)
          (Bool.andRight settled)
          (Bool.andRight lexical)
          (Bool.andRight hung)
      calc splitFrom (Splitter.at 0) current groups (decl.laid empty ++ (groupsFrom False rest).concat)
        _ = splitFrom (Splitter.at 0) (decl.laid empty).reverse flushed (groupsFrom False rest).concat :=
          laidSplit decl empty
            (groupsFrom False rest).concat
            current
            groups
            (Bool.andLeft within)
            (Bool.andLeft shaped)
            (Bool.andLeft settled)
            (Bool.andLeft lexical)
            (Bool.andLeft hung)
        _ = (if (decl.laid empty).reverse.isEmpty then flushed
             else [(decl.laid empty).reverse.reverse, ..flushed]).reverse
            ++ groupsFrom False rest := rec
        _ = flushed.reverse ++ [decl.laid empty, ..groupsFrom False rest] :=
          rewrite flushLaid (decl.laid empty) flushed laidFirst, List.reverseCons (decl.laid empty) flushed then
            List.appendAssoc flushed.reverse [decl.laid empty] (groupsFrom False rest)

-- Where a declaration starts.

def defFirst (texts: List Text): Bool := match texts with
  | [first, .._] => first == "def"
  | [] => False

def kindFirst (leaves: List Leaf): Bool := match leaves with
  | [first, .._] => first.token.kind == KwDef
  | [] => False

theorem declStartsDef ∀ (decl: Decl) (within: decl.within1 = True): defFirst (decl.spelt.filter notComment) = True :=
  match decl with
    | Definition [] header (Assigned colonEq value) =>
      match header with
        | {
            exportKeyword = None,
            opaqueKeyword = None,
            kind = DefPlain,
            keyword,
            name,
            forallKeyword = None,
            params = [],
            colon,
            result,
            decreasingClause = None,
            unfoldingClause = None
          } => byComputing
        | _ => cases

theorem leavesStartDef ∀ (leaves: List Leaf) (texts: List Text)
    (kinded: leaves.all Leaf.kinded = True)
    (same: tokenTexts leaves = texts)
    (first: defFirst texts = True):
    kindFirst leaves = True :=
  match leaves with
    | [] => (Bool.falseNotTrue (rewrite <- same at first then first)).impossible
    | [leaf, ..rest] =>
      let text: (leaf.token.text == "def") = True := rewrite <- same at first then first
      rewrite DecEq.sound (Bool.andLeft kinded), DecEq.sound text

--| A declaration's leaves start with `def`.
theorem declStartsKw ∀ (decl: Decl)
    (within: decl.within1 = True)
    (shaped: decl.shaped = True)
    (settled: decl.settled = True)
    (lexical: decl.lexical = True):
    kindFirst decl.leaves = True :=
  let (texts, kinded) := printedTokens1 decl within shaped settled lexical
  leavesStartDef decl.leaves (decl.spelt.filter notComment) kinded texts (declStartsDef decl within)

theorem headedFirst ∀ (above: List Comment) (blank: Nat) (leaves: List Leaf):
    kindFirst (headed above blank leaves) = kindFirst leaves :=
  match leaves with | [] | [_, .._] => byComputing

theorem headedPairs ∀ (above: List Comment) (blank: Nat) (leaves: List Leaf):
    leafPairs (headed above blank leaves) = leafPairs leaves :=
  match leaves with | [] | [_] | [_, _, .._] => byComputing

-- Each leaf may follow the one before, across the file.

--| The leaves are empty or start with `def`.
def startsDef (leaves: List Leaf): Bool := match leaves with
  | [first, .._] => first.token.kind == KwDef
  | [] => True

--| Pairs of leaves, with a declaration after them: its `def` may follow anything.
theorem leafPairsAppend ∀ (xs ys: List Leaf)
    (front: leafPairs xs = True)
    (back: leafPairs ys = True)
    (starts: startsDef ys = True):
    leafPairs (xs ++ ys) = True :=
  match xs with
    | [] => back
    | [last] =>
      match ys with
        | [] => byComputing
        | [first, ..rest] => Bool.andIntro (rewrite DecEq.sound starts) back
    | [x, y, ..more] =>
      Bool.andIntro (Bool.andLeft front) (leafPairsAppend [y, ..more] ys (Bool.andRight front) back starts)

theorem startsAppend ∀ (xs ys: List Leaf) (first: kindFirst xs = True): startsDef (xs ++ ys) = True := match xs with
  | [x, ..rest] => first

--| Each declaration's leaves may follow the one before, and they start with `def`.
theorem groupsPairs ∀ (empty: Bool) (decls: List Decl)
    (within: decls.all Decl.within1 = True)
    (shaped: decls.all Decl.shaped = True)
    (settled: decls.all Decl.settled = True)
    (lexical: decls.all Decl.lexical = True):
    leafPairs (groupsFrom empty decls).concat = True ∧ startsDef (groupsFrom empty decls).concat = True :=
  match decls with
    | [] => (byComputing, byComputing)
    | [decl, ..rest] =>
      let (leavesWithin, leavesPairs) :=
        declLeaves decl (Bool.andLeft within) (Bool.andLeft shaped) (Bool.andLeft settled) (Bool.andLeft lexical)
      let first :=
        declStartsKw decl (Bool.andLeft within) (Bool.andLeft shaped) (Bool.andLeft settled) (Bool.andLeft lexical)
      let (restPairs, restStarts) :=
        groupsPairs False rest
          (Bool.andRight within)
          (Bool.andRight shaped)
          (Bool.andRight settled)
          (Bool.andRight lexical)
      let laidFirst: kindFirst (decl.laid empty) = True :=
        rewrite headedFirst
              (laidNotes empty decl.firstComments.above)
              (if decl.firstComments.blankBefore && !(empty && decl.firstComments.above.isEmpty) then 1 else 0)
              decl.leaves then
          first
      let laidPairs: leafPairs (decl.laid empty) = True :=
        rewrite headedPairs
              (laidNotes empty decl.firstComments.above)
              (if decl.firstComments.blankBefore && !(empty && decl.firstComments.above.isEmpty) then 1 else 0)
              decl.leaves then
          leavesPairs
      (
        leafPairsAppend (decl.laid empty) (groupsFrom False rest).concat laidPairs restPairs restStarts,
        startsAppend (decl.laid empty) (groupsFrom False rest).concat laidFirst
      )

-- No last comma.

theorem lastPairFalse ∀ (above: Tok) (comma: Leaf) (older: List Leaf)
    (ok: (!above.isCloser || !(comma.token.kind == Comma)) = True):
    lastPair above comma older = False :=
  match c: comma.token.kind == Comma with
    | True =>
      match d: above.isCloser with
        | False => byComputing
    | False => byComputing

--| Leaves that may each follow the one before have no last comma.
theorem noLastOfPairs ∀ (leaves behind: List Leaf) (pairs: leafPairs leaves = True): noLast behind leaves = True :=
  match leaves with
    | [] | [_] => byComputing
    | [leaf, closer, ..more] =>
      Bool.andIntro
        (rewrite lastPairFalse closer.token.kind leaf behind (Bool.andRight (Bool.andLeft pairs)))
        (noLastOfPairs [closer, ..more] [leaf, ..behind] (Bool.andRight pairs))

--| `printedNoLast1`: the output has no comma directly before a closer, so `settledOnce` of it is `settled`
--| (`settledOnceNone`). It holds whatever the tree's trailing-comma flags say: the rules never print one.
--|
--| Proof idea: by `printedTokens1` the tokens are `decl.spelt`'s, where a comma stands only between two items
--| (`commaSpelt`), and an item starts with no closer. That is the scan's rule for what may follow a comma
--| (`declRuns`); a declaration's `def` follows anything, so it holds across the file.
theorem printedNoLast1 ∀ (file: SourceFile)
    (within: file.within1 = True)
    (shaped: file.shaped = True)
    (settled: file.settled = True)
    (lexical: file.lexical = True):
    noLast [] file.lexed.leaves = True :=
  noLastOfPairs file.lexed.leaves [] (groupsPairs True file.decls within shaped (Bool.andLeft settled) lexical).left

-- No comma starts a line.

--| No comma starts its line.
def commaFlat (leaves: List Leaf): Bool := leaves.all (leaf => !(leaf.token.kind == Comma && leaf.token.lineStart))

--| `hangs` refuses a comma that starts its line.
theorem stepCommaNone ∀ (state: HangState) (leaf: Leaf)
    (isComma: (leaf.token.kind == Comma) = True)
    (starts: leaf.token.lineStart = True):
    state.step leaf = None :=
  rewrite DecEq.sound isComma, starts then
    match state.glue with
      | True => byComputing
      | False =>
        match state.blocks with
          | [] => byComputing
          | [block, ..outer] => rewrite starts

theorem stepFlat ∀ (state: HangState) (leaf: Leaf) (next: HangState)
    (step: state.step leaf = Some next):
    (!(leaf.token.kind == Comma && leaf.token.lineStart)) = True :=
  match flat: leaf.token.kind == Comma && leaf.token.lineStart with
    | True =>
      (Option.noneNotSome next
        (Eq.trans (stepCommaNone state leaf (Bool.andLeft flat) (Bool.andRight flat)).flipped step)).impossible
    | False => byComputing

theorem hangsFromFlat ∀ (leaves: List Leaf) (state: HangState)
    (hung: hangsFrom state leaves = True):
    commaFlat leaves = True :=
  match leaves with
    | [] => byComputing
    | [leaf, ..rest] =>
      match hungStep state leaf rest hung with
        | Witness next (step, more) => Bool.andIntro (stepFlat state leaf next step) (hangsFromFlat rest next more)

theorem hangsFlat ∀ (leaves: List Leaf) (hung: hangs leaves = True): commaFlat leaves = True := match leaves with
  | [] => byComputing
  | [first, ..rest] =>
    Bool.andIntro
      (rewrite DecEq.sound (Bool.andLeft hung))
      (hangsFromFlat rest HangState.initial (Bool.andRight (Bool.andRight hung)))

--| Leaves that may each follow the one before, no comma starting a line, are `plain` from the second token on.
theorem plainOfPairs ∀ (leaves: List Leaf)
    (pairs: leafPairs leaves = True)
    (flat: commaFlat leaves = True):
    plainFrom (tokens leaves) = True :=
  match leaves with
    | [] | [_] => byComputing
    | [first, second, ..rest] =>
      Bool.andIntro
        (Bool.orSwapTrue _ _ (Bool.andLeft (Bool.andLeft pairs)))
        (Bool.andIntro
          (rewrite Bool.andLeft flat)
          (plainOfPairs [second, ..rest] (Bool.andRight pairs) (Bool.andRight flat)))

theorem plainOfLeaves ∀ (leaves: List Leaf)
    (pairs: leafPairs leaves = True)
    (flat: commaFlat leaves = True)
    (starts: startsDef leaves = True):
    plain1 (tokens leaves) = True :=
  match leaves with
    | [] => byComputing
    | [first, ..rest] => Bool.andIntro (rewrite DecEq.sound starts) (plainOfPairs [first, ..rest] pairs flat)

theorem commaFlatAppend ∀ (xs ys: List Leaf): commaFlat (xs ++ ys) = (commaFlat xs && commaFlat ys) := match xs with
  | [] => byComputing
  | [first, ..rest] =>
    match !(first.token.kind == Comma && first.token.lineStart) with
      | True => commaFlatAppend rest ys
      | False => byComputing

theorem headedFlat ∀ (above: List Comment) (blank: Nat) (leaves: List Leaf):
    commaFlat (headed above blank leaves) = commaFlat leaves :=
  match leaves with | [] | [_, .._] => byComputing

theorem groupsFlat ∀ (empty: Bool) (decls: List Decl)
    (hung: decls.all (decl => hangs decl.leaves) = True):
    commaFlat (groupsFrom empty decls).concat = True :=
  match decls with
    | [] => byComputing
    | [decl, ..rest] =>
      rewrite commaFlatAppend (decl.laid empty) (groupsFrom False rest).concat,
          headedFlat
            (laidNotes empty decl.firstComments.above)
            (if decl.firstComments.blankBefore && !(empty && decl.firstComments.above.isEmpty) then 1 else 0)
            decl.leaves,
          hangsFlat decl.leaves (Bool.andLeft hung) then
        groupsFlat False rest (Bool.andRight hung)

-- The statements.

--| `printedAlphabet1`: the output passes the alphabet, the driver's first test on the second run.
--|
--| Proof idea: by `printedTokens1` a token's text is a comma or a word's of the tree and its kind the lexer's for
--| that text; `lexical` and `within1` put every word's kind in the alphabet. The kinds are one pass over a
--| declaration's texts (`declRuns`), whose steps `exprRuns` takes along the expression.
theorem printedAlphabet1 ∀ (file: SourceFile)
    (within: file.within1 = True)
    (shaped: file.shaped = True)
    (settled: file.settled = True)
    (lexical: file.lexical = True):
    alphabet1 file.lexed.leaves = True :=
  Eq.trans
    (List.allMapBool file.lexed.leaves (token => token.kind.within1) (leaf => leaf.token))
    (groupsWithin True file.decls within shaped (Bool.andLeft settled) lexical)

--| `printedPlain1`: the output is `plain1`, which rule N's theorems ask and the driver tests: its first token is a
--| `def`, what follows a `->` is an operand's first token (no comma, closer or `->`), and no comma starts a line.
--|
--| Proof idea: the token order is `printedTokens1`'s; the scan's rule for what may follow `->` is `plainFrom`'s, a
--| declaration's `def` follows anything, and `hangs` refuses a comma that starts its line.
theorem printedPlain1 ∀ (file: SourceFile)
    (within: file.within1 = True)
    (shaped: file.shaped = True)
    (settled: file.settled = True)
    (lexical: file.lexical = True)
    (hung: file.hung = True):
    plain1 (tokens file.lexed.leaves) = True :=
  let (pairs, starts) := groupsPairs True file.decls within shaped (Bool.andLeft settled) lexical
  plainOfLeaves file.lexed.leaves pairs (groupsFlat True file.decls hung) starts

--| `printedGroups1`: the parser's groups of the output are the declarations' leaves, one group a declaration.
--|
--| Proof idea: a group starts at a token in column 0 that is no `:=`, outside brackets or not a closer or comma;
--| each declaration starts with `def` in column 0, and by `hangs` its later leaves that start a line stand right of
--| column 0 unless they are a closer or `:=`. A leaf in column 0 starts its line (the layout, `foldOk`), a closer
--| in column 0 has its bracket open (the scan's count, `declDepth`), and the declaration's brackets balance, so the
--| splitter is outside every declaration when the next `def` comes (`groupsSplit`).
theorem printedGroups1 ∀ (file: SourceFile)
    (within: file.within1 = True)
    (shaped: file.shaped = True)
    (settled: file.settled = True)
    (lexical: file.lexical = True)
    (hung: file.hung = True):
    groupsOf file.lexed.leaves = groupsFrom True file.decls :=
  groupsSplit True file.decls [] [] within shaped (Bool.andLeft settled) lexical hung

-- Cases the lemmas apply to, so their hypotheses can be met.

theorem stepCommentExample: Scan.start.step "-- a" = Some Scan.start := stepComment Scan.start "-- a" byComputing

theorem goCloseExample: ({ previous = Some Lower, open = 1 }: Scan).go RParen
      = Some { previous = Some RParen, open = 0 } :=
  goClose
    { previous = Some Lower, open = 1 }
    Lower
    RParen
    0
    byComputing
    byComputing
    byComputing
    byComputing
    byComputing
    byComputing

theorem wordRunExample: Scan.start.run ((fixedWord "a" Comments.none).spelledAt False)
      = Some { previous = Some Lower, open = 0 } :=
  wordRun (fixedWord "a" Comments.none) False Scan.start { previous = Some Lower, open = 0 } byComputing byComputing

theorem opKindOfExample: opKind "+" = True := opKindOf "+" byComputing

theorem leavesStartDefExample: kindFirst exampleDecl.leaves = True :=
  leavesStartDef exampleDecl.leaves (exampleDecl.spelt.filter notComment) byComputing byComputing byComputing
