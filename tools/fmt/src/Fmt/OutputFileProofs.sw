--| The output's leaves, file level (SW-4040, ticket C of docs/reviews/SW-4025-output-statements.md): the alphabet, no
--| last comma, `plain1` and the groups, from `printedTokens1`.
--|
--| One pass over a declaration's printed texts (`Scan.run`) checks what the first three need: every token of the
--| alphabet, no token that can't follow the one before (a comma before a closer, `->` before a comma, closer or
--| `->`) and no closer without an open bracket. A comment is skipped.

namespace Fmt.OutputFileProofs
import Std (Bool, DecEq, Eq, List, Nat, Option, Text)
import Syntax (..)
import Syntax.Proofs (Spells)
import Syntax.SettleProofs (alphabet1)
import Syntax.SettleBareProofs (fwdPair, lastPair, noLast)
import Syntax.SettleProofs (arrowFollow, passableKind)
import Fmt (..)
import Fmt.SpellProofs (..)
import Fmt.TreeJoinProofs (..)
import Fmt.TokenProofs (declRealOfLexical, printedTokens1)
import Fmt.OutputStatements (..)

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

theorem orTrue ∀ (x: Bool): (x || True) = True := match x with
  | True => byComputing
  | False => byComputing

theorem pairQuiet ∀ (last kind: Tok) (quiet: quietLast last = True): pairOk last kind = True :=
  rewrite Bool.notTrue _ (Bool.andLeft quiet),
      Bool.notTrue _ (Bool.andRight quiet),
      orTrue (!arrowFollow kind),
      orTrue (!kind.isCloser)

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

theorem opCase ∀ (text literal: Text)
    (same: (text == literal) = True)
    (facts: opKind literal = True):
    opKind text = True :=
  rewrite DecEq.sound same then facts

theorem opKindA ∀ (text: Text) (listed: operatorTextA1 text = True): opKind text = True := match a0: text == "->" with
  | True => opCase text "->" a0 byComputing
  | False =>
    match a1: text == "→" with
      | True => opCase text "→" a1 byComputing
      | False =>
        match a2: text == "||" with
          | True => opCase text "||" a2 byComputing
          | False =>
            match a3: text == "∨" with
              | True => opCase text "∨" a3 byComputing
              | False =>
                match a4: text == "&&" with
                  | True => opCase text "&&" a4 byComputing
                  | False =>
                    match a5: text == "∧" with
                      | True => opCase text "∧" a5 byComputing

theorem opKindB ∀ (text: Text) (listed: operatorTextB1 text = True): opKind text = True := match a0: text == "+" with
  | True => opCase text "+" a0 byComputing
  | False =>
    match a1: text == "++" with
      | True => opCase text "++" a1 byComputing
      | False =>
        match a2: text == "-" with
          | True => opCase text "-" a2 byComputing
          | False =>
            match a3: text == "*" with
              | True => opCase text "*" a3 byComputing
              | False =>
                match a4: text == "/" with
                  | True => opCase text "/" a4 byComputing
                  | False =>
                    match a5: text == "%" with
                      | True => opCase text "%" a5 byComputing

theorem opKindC ∀ (text: Text) (listed: operatorTextC1 text = True): opKind text = True := match a0: text == "!=" with
  | True => opCase text "!=" a0 byComputing
  | False =>
    match a1: text == "≠" with
      | True => opCase text "≠" a1 byComputing
      | False =>
        match a2: text == "<" with
          | True => opCase text "<" a2 byComputing
          | False =>
            match a3: text == "<=" with
              | True => opCase text "<=" a3 byComputing
              | False =>
                match a4: text == "≤" with
                  | True => opCase text "≤" a4 byComputing

theorem opKindD ∀ (text: Text) (listed: operatorTextD1 text = True): opKind text = True := match a0: text == ">" with
  | True => opCase text ">" a0 byComputing
  | False =>
    match a1: text == ">=" with
      | True => opCase text ">=" a1 byComputing
      | False =>
        match a2: text == "≥" with
          | True => opCase text "≥" a2 byComputing
          | False =>
            match a3: text == "==" with
              | True => opCase text "==" a3 byComputing
              | False =>
                match a4: text == "=" with
                  | True => opCase text "=" a4 byComputing

--| An infix operator `within1` lets through has such a kind.
theorem opKindOf ∀ (text: Text) (listed: operatorText1 text = True): opKind text = True :=
  match first: operatorTextA1 text with
    | True => opKindA text first
    | False =>
      match second: operatorTextB1 text with
        | True => opKindB text second
        | False =>
          match third: operatorTextC1 text with
            | True => opKindC text third
            | False => opKindD text listed

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
    (lexical: expr.lexical1 = True) (spelled: expr.operators1):
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
      let listed: operatorText1 operator.text = True := match kind with
        | InfixBinary => Bool.andRight (Bool.andRight within)
        | InfixArrow => Bool.andRight (Bool.andRight within)
        | _ => cases
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
    (lexical: allLexical1 [first, ..rest] = True)
    (spelled: AllOperators1 [first, ..rest]):
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
    (lexical: allLexical1 items = True)
    (spelled: AllOperators1 items):
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
    (lexical: allLexical1 arguments = True)
    (spelled: AllOperators1 arguments):
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

def Scan.start: Scan := { previous = None, open = 0 }

--| A declaration's printed texts pass the scan from the start of the file and end with no bracket open, the last
--| token one that may be followed by anything.
--|
--| Proof idea: the keyword, name, colon and `:=` are tokens of a plain kind that any token may follow
--| (`goFlat`), the type and the value are `exprRuns`.
theorem declRuns ∀ (decl: Decl)
    (within: decl.within1 = True)
    (sound: decl.sound = True)
    (lexical: decl.lexical1 = True) (spelled: decl.operators1):
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
          let nameSpells := spellsOfText1 Lower name.text (Bool.andRight (Bool.andLeft (Bool.andLeft within)))
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
          let afterName: Scan := { previous = Some Lower, open = 0 }
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
                (stepToken afterKeyword name.text Lower
                  (lexKindOfSpells Lower name.text nameSpells)
                  (spellsNotComment Lower name.text nameSpells))
                (goFlat afterKeyword Lower byComputing byComputing byComputing byComputing))
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
    (shaped: decl.shaped1 = True)
    (settled: decl.settled1 = True)
    (lexical: decl.lexical1 = True):
    leafWithin decl.leaves1 = True ∧ leafPairs decl.leaves1 = True :=
  let sound := declSoundOfSettled decl within settled (declRealOfLexical decl within lexical)
  let (texts, kinded) := printedTokens1 decl within shaped settled lexical
  match declRuns decl within sound lexical (declOperators decl within) with
    | Witness last (run, quiet) =>
      let filtered: Scan.start.run (decl.spelt.filter notComment) = Some { previous = Some last, open = 0 } :=
        Eq.trans (runFilter decl.spelt Scan.start).flipped run
      let plain: (tokenTexts decl.leaves1).all notComment = True := rewrite texts then filterNotComment decl.spelt
      let (within, pairs, head) :=
        leafScan decl.leaves1 Scan.start { previous = Some last, open = 0 } kinded plain (rewrite texts then filtered)
      (within, pairs)

theorem leafWithinAppend ∀ (xs ys: List Leaf): leafWithin (xs ++ ys) = (leafWithin xs && leafWithin ys) := match xs with
  | [] => byComputing
  | [first, ..rest] =>
    match first.token.kind.within1 with
      | True => leafWithinAppend rest ys
      | False => byComputing

theorem headedWithin ∀ (above: List Comment) (blank: Nat) (leaves: List Leaf):
    leafWithin (headed above blank leaves) = leafWithin leaves :=
  match leaves with
    | [] => byComputing
    | [first, ..rest] => byComputing

theorem declLaidWithin ∀ (decl: Decl) (empty: Bool)
    (within: leafWithin decl.leaves1 = True):
    leafWithin (decl.laid1 empty) = True :=
  rewrite headedWithin
        (laidNotes empty decl.firstComments.above)
        (if decl.firstComments.blankBefore && !(empty && decl.firstComments.above.isEmpty) then 1 else 0)
        decl.leaves1 then
    within

theorem groupsWithin ∀ (empty: Bool) (decls: List Decl)
    (within: decls.all Decl.within1 = True)
    (shaped: decls.all Decl.shaped1 = True)
    (settled: decls.all Decl.settled1 = True)
    (lexical: decls.all Decl.lexical1 = True):
    leafWithin (groupsFrom empty decls).concat = True :=
  match decls with
    | [] => byComputing
    | [decl, ..rest] =>
      let (leavesWithin, leavesPairs) :=
        declLeaves decl (Bool.andLeft within) (Bool.andLeft shaped) (Bool.andLeft settled) (Bool.andLeft lexical)
      rewrite leafWithinAppend (decl.laid1 empty) (groupsFrom False rest).concat,
          declLaidWithin decl empty leavesWithin then
        groupsWithin False rest
          (Bool.andRight within)
          (Bool.andRight shaped)
          (Bool.andRight settled)
          (Bool.andRight lexical)

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
    (shaped: decl.shaped1 = True)
    (settled: decl.settled1 = True)
    (lexical: decl.lexical1 = True):
    kindFirst decl.leaves1 = True :=
  let (texts, kinded) := printedTokens1 decl within shaped settled lexical
  leavesStartDef decl.leaves1 (decl.spelt.filter notComment) kinded texts (declStartsDef decl within)

theorem headedFirst ∀ (above: List Comment) (blank: Nat) (leaves: List Leaf):
    kindFirst (headed above blank leaves) = kindFirst leaves :=
  match leaves with
    | [] => byComputing
    | [first, ..rest] => byComputing

theorem headedPairs ∀ (above: List Comment) (blank: Nat) (leaves: List Leaf):
    leafPairs (headed above blank leaves) = leafPairs leaves :=
  match leaves with
    | [] => byComputing
    | [first] => byComputing
    | [first, second, ..rest] => byComputing

-- Each leaf may follow the one before, across the file.

--| The leaves are empty or start with `def`.
def startsDef (leaves: List Leaf): Bool := match leaves with
  | [first, .._] => first.token.kind == KwDef
  | [] => True

--| Pairs of leaves, with a declaration after them: its `def` may follow anything.
theorem pairsAppend ∀ (xs ys: List Leaf)
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
      Bool.andIntro (Bool.andLeft front) (pairsAppend [y, ..more] ys (Bool.andRight front) back starts)

theorem startsAppend ∀ (xs ys: List Leaf) (first: kindFirst xs = True): startsDef (xs ++ ys) = True := match xs with
  | [x, ..rest] => first

--| Each declaration's leaves may follow the one before, and they start with `def`.
theorem groupsPairs ∀ (empty: Bool) (decls: List Decl)
    (within: decls.all Decl.within1 = True)
    (shaped: decls.all Decl.shaped1 = True)
    (settled: decls.all Decl.settled1 = True)
    (lexical: decls.all Decl.lexical1 = True):
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
      let laidFirst: kindFirst (decl.laid1 empty) = True :=
        rewrite headedFirst
              (laidNotes empty decl.firstComments.above)
              (if decl.firstComments.blankBefore && !(empty && decl.firstComments.above.isEmpty) then 1 else 0)
              decl.leaves1 then
          first
      let laidPairs: leafPairs (decl.laid1 empty) = True :=
        rewrite headedPairs
              (laidNotes empty decl.firstComments.above)
              (if decl.firstComments.blankBefore && !(empty && decl.firstComments.above.isEmpty) then 1 else 0)
              decl.leaves1 then
          leavesPairs
      (
        pairsAppend (decl.laid1 empty) (groupsFrom False rest).concat laidPairs restPairs restStarts,
        startsAppend (decl.laid1 empty) (groupsFrom False rest).concat laidFirst
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
    | [] => byComputing
    | [leaf] => byComputing
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
    (shaped: file.shaped1 = True)
    (settled: file.settled1 = True)
    (lexical: file.lexical1 = True):
    noLast [] file.lexed1.leaves = True :=
  noLastOfPairs file.lexed1.leaves [] (groupsPairs True file.decls within shaped (Bool.andLeft settled) lexical).left

-- The statements.

--| `printedAlphabet1`: the output passes the alphabet, the driver's first test on the second run.
--|
--| Proof idea: by `printedTokens1` a token's text is a comma or a word's of the tree and its kind the lexer's for
--| that text; `lexical1` and `within1` put every word's kind in the alphabet. The kinds are one pass over a
--| declaration's texts (`declRuns`), whose steps `exprRuns` takes along the expression.
theorem printedAlphabet1 ∀ (file: SourceFile)
    (within: file.within1 = True)
    (shaped: file.shaped1 = True)
    (settled: file.settled1 = True)
    (lexical: file.lexical1 = True):
    alphabet1 file.lexed1.leaves = True :=
  Eq.trans
    (List.allMapBool file.lexed1.leaves (token => token.kind.within1) (leaf => leaf.token))
    (groupsWithin True file.decls within shaped (Bool.andLeft settled) lexical)
