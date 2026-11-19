--| `wordsEdgeOneLine`: a slice 1 declaration that prints on one line has its comments on tokens that are no closers
--| only at the edges `wordsEdge1` allows (SW-4107, the route of SW-4096's steps 1 to 4).
--|
--| The printed tokens with a comment since the token before them start their lines (`declCovered`), which `onLine1`
--| allows only at the `:=` and at the value's first token (`lineCov`). Over the tokens that are no closers, the
--| printed words' marks are the tree's (`spreadMarked`, `printedSpellsSettled`), so the tree's comments fall only
--| where `wordsEdgeOfMarks` needs them.

namespace Fmt.WordsEdgeLine
import Std (Bool, DecEq, Doc, Eq, List, Nat, Option, Text)
import Std.Doc.Proofs (printedPieces, wordsOf)
import Syntax (Decl, DefBody, DefKind, Expr, Header, InfixKind, Leaf, Tok, Token, Word)
import Syntax.SettleProofs (tokens)
import Fmt (..)
import Fmt.SpellProofs (..)
import Fmt.TreeJoinProofs (
  OperatorSpells,
  declOperators,
  declReal,
  lexKind,
  lexKindOfSpells,
  operatorSpellsOf,
  spellsOfText1,
  wordQuiet
)
import Fmt.OutputStatements (..)
import Fmt.TokenProofs (declRealOfLexical, printedTokens1)
import Fmt.Driver1 (..)
import Fmt.CalmProofs (headerResultWithin)
import Fmt.NoteMarks (..)
import Fmt.NoteLines (..)
import Fmt.WordsEdge (..)

-- What `onLine1` says of the marks.

--| A token whose kind is the lexer's for its text.
def Token.kinded1 (token: Token): Bool := token.kind == lexKind token.text

--| `onLine1` read off marks: after three tokens, none of the type's tokens is marked, nor any of the value's after
--| its first.
def marksOnLine: List (Text, Bool) → Bool
  | [_, _, _, ..rest] => typeMarks rest
  | _ => False

def typeMarks: List (Text, Bool) → Bool
  | [] => True
  | [(text, mark), ..rest] => if lexKind text == ColonEq then valueMarks rest else !mark && typeMarks rest

def valueMarks: List (Text, Bool) → Bool
  | [] => True
  | [_, ..rest] => !anyMarked rest

theorem markClear ∀ (mark start: Bool) (step: (!mark || start) = True) (fresh: start = False): mark = False :=
  match mark, start, step, fresh with
    | False, _, _, _ => byComputing
    | True, True, _, never => (Bool.trueNotFalse never).impossible

theorem quietCov ∀ (marks: List (Text, Bool)) (tokens: List Token)
    (cov: Cov marks tokens = True)
    (quiet: tokens.all (token => !token.lineStart) = True):
    anyMarked marks = False :=
  match marks, tokens, cov with
    | [], [], _ => byComputing
    | [(text, mark), ..rest], [token, ..others], cov =>
      let clear := markClear mark token.lineStart (Bool.andLeft cov) (Bool.notTrue _ (Bool.andLeft quiet))
      rewrite clear then quietCov rest others (Bool.andRight cov) (Bool.andRight quiet)

theorem valueCov ∀ (marks: List (Text, Bool)) (tokens: List Token)
    (cov: Cov marks tokens = True)
    (line: valueOnLine1 tokens = True):
    valueMarks marks = True :=
  match marks, tokens, cov with
    | [], [], _ => byComputing
    | [(text, mark), ..rest], [token, ..others], cov => rewrite quietCov rest others (Bool.andRight cov) line

theorem typeCov ∀ (marks: List (Text, Bool)) (tokens: List Token)
    (cov: Cov marks tokens = True)
    (texts: marks.map Pair.fst = tokens.map (token => token.text))
    (kinded: tokens.all Token.kinded1 = True)
    (line: typeOnLine1 tokens = True):
    typeMarks marks = True :=
  match marks, tokens, cov with
    | [], [], _ => byComputing
    | [(text, mark), ..rest], [token, ..others], cov =>
      let sameText: text = token.text := List.consInjectiveHead _ _ _ _ texts
      let restTexts: rest.map Pair.fst = others.map (token => token.text) :=
        Eq.cong ((list: List Text) => list.drop 1) texts
      let kindEq: token.kind = lexKind text := rewrite sameText then DecEq.sound (Bool.andLeft kinded)
      rewrite <- kindEq then
        match colon: token.kind == ColonEq with
          | True => valueCov rest others (Bool.andRight cov) line
          | False =>
            let clear := markClear mark token.lineStart (Bool.andLeft cov) (Bool.notTrue _ (Bool.andLeft line))
            rewrite clear then
              typeCov rest others (Bool.andRight cov) restTexts (Bool.andRight kinded) (Bool.andRight line)

theorem lineCov ∀ (marks: List (Text, Bool)) (tokens: List Token)
    (cov: Cov marks tokens = True)
    (texts: marks.map Pair.fst = tokens.map (token => token.text))
    (kinded: tokens.all Token.kinded1 = True)
    (line: onLine1 tokens = True):
    marksOnLine marks = True :=
  match tokens, line with
    | [t1, t2, t3, ..others], line =>
      match marks, cov with
        | [(a1, x1)], cov => (Bool.falseNotTrue (Bool.andRight cov)).impossible
        | [(a1, x1), (a2, x2)], cov => (Bool.falseNotTrue (Bool.andRight (Bool.andRight cov))).impossible
        | [(a1, x1), (a2, x2), (a3, x3), ..rest], cov =>
          typeCov rest others
            (Bool.andRight (Bool.andRight (Bool.andRight cov)))
            (Eq.cong ((list: List Text) => list.drop 3) texts)
            (Bool.andRight (Bool.andRight (Bool.andRight kinded)))
            line

theorem kindedTokens ∀ (leaves: List Leaf)
    (kinded: leaves.all Leaf.kinded = True):
    (tokens leaves).all Token.kinded1 = True :=
  match leaves with
    | [] => byComputing
    | [leaf, ..rest] => Bool.andIntro (Bool.andLeft kinded) (kindedTokens rest (Bool.andRight kinded))

theorem textsTokens ∀ (leaves: List Leaf): (tokens leaves).map (token => token.text) = tokenTexts leaves :=
  match leaves with
    | [] => byComputing
    | [leaf, ..rest] => rewrite textsTokens rest

-- Splitting marks by their texts.

theorem splitMap ∀ (pairs: List (Text, Bool)) (front back: List Text)
    (same: pairs.map Pair.fst = front ++ back):
    ∃ (first second: List (Text, Bool)) => pairs = first ++ second
      ∧ first.map Pair.fst = front
      ∧ second.map Pair.fst = back :=
  match front with
    | [] => ([], pairs, byComputing, byComputing, same)
    | [text, ..texts] =>
      match pairs, same with
        | [], never => cases
        | [pair, ..rest], same =>
          let head: pair.fst = text := List.consInjectiveHead _ _ _ _ same
          let (first, second, split, firstTexts, secondTexts) :=
            splitMap rest texts back (Eq.cong ((list: List Text) => list.drop 1) same)
          ([pair, ..first], second, (rewrite split), (rewrite head, firstTexts), secondTexts)

theorem threeOf ∀ (pairs: List (Text, Bool)) (a b c: Text)
    (same: pairs.map Pair.fst = [a, b, c]):
    ∃ (x y z: Bool) => pairs = [(a, x), (b, y), (c, z)] :=
  match pairs, same with
    | [], never => cases
    | [_], never => cases
    | [_, _], never => cases
    | [_, _, _, _, .._], never => cases
    | [(p, x), (q, y), (r, z)], same =>
      let pa: p = a := List.consInjectiveHead _ _ _ _ same
      let qb: q = b := List.consInjectiveHead _ _ _ _ (Eq.cong ((list: List Text) => list.drop 1) same)
      let rc: r = c := List.consInjectiveHead _ _ _ _ (Eq.cong ((list: List Text) => list.drop 2) same)
      (x, y, z, rewrite pa, qb, rc)

theorem oneOf ∀ (pairs: List (Text, Bool)) (a: Text)
    (same: pairs.map Pair.fst = [a]):
    ∃ (x: Bool) => pairs = [(a, x)] :=
  match pairs, same with
    | [], never => cases
    | [_, _, .._], never => cases
    | [(p, x)], same => (x, rewrite List.consInjectiveHead _ _ _ _ same)

--| A text the lexer reads as no `:=`.
def notAssign (text: Text): Bool := !(lexKind text == ColonEq)

theorem typeSplit ∀ (front back: List (Text, Bool))
    (noAssign: (front.map Pair.fst).all notAssign = True)
    (line: typeMarks (front ++ back) = True):
    anyMarked front = False ∧ typeMarks back = True :=
  match front with
    | [] => (byComputing, line)
    | [(text, mark), ..rest] =>
      let notColon: (lexKind text == ColonEq) = False := Bool.notTrue _ (Bool.andLeft noAssign)
      let stepped: (!mark && typeMarks (rest ++ back)) = True := rewrite notColon at line then line
      let clear: mark = False := Bool.notTrue _ (Bool.andLeft stepped)
      let (quiet, after) := typeSplit rest back (Bool.andRight noAssign) (Bool.andRight stepped)
      ((rewrite clear then quiet), after)

-- The tokens the rules spell.

theorem wordTokens ∀ (word: Word) (hoisted: Bool)
    (token: notComment word.text = True)
    (sound: word.sound = True):
    (word.spelledAt hoisted).filter notComment = [word.text] :=
  let none := notesNoTokens word.comments.after.toList (wordAfter word sound)
  match hoisted with
    | True => rewrite List.filterAppend [word.text] word.comments.after.toList notComment, token, none
    | False =>
      rewrite List.filterAppend word.notes ([word.text] ++ word.comments.after.toList) notComment,
          List.filterAppend [word.text] word.comments.after.toList notComment,
          notesNoTokens word.notes (wordNotes word sound),
          token,
          none

--| A token the lexer reads as no `:=`, its comments left out.
theorem wordAssign ∀ (word: Word) (hoisted: Bool)
    (token: notComment word.text = True)
    (sound: word.sound = True)
    (other: notAssign word.text = True):
    ((word.spelledAt hoisted).filter notComment).all notAssign = True :=
  rewrite wordTokens word hoisted token sound then Bool.andIntro other byComputing

theorem fixedAssign ∀ (word: Word) (fixed: Text)
    (same: (word.text == fixed) = True)
    (facts: notComment fixed = True ∧ notAssign fixed = True):
    notComment word.text = True ∧ notAssign word.text = True :=
  rewrite DecEq.sound same then facts

theorem kindAssign ∀ (kind: Tok) (text: Text)
    (spells: Syntax.Proofs.Spells kind text)
    (other: (text == ":=") = False):
    notAssign text = True :=
  match colon: kind == ColonEq with
    | True =>
      let assign: text = ":=" := rewrite DecEq.sound colon at spells then spells
      (Bool.trueNotFalse (rewrite assign at other then other)).impossible
    | False => rewrite lexKindOfSpells kind text spells, colon

theorem atomAssign ∀ (kind: Tok) (word: Word) (within: (Atom kind word).within1 = True): notAssign word.text = True :=
  rewrite lexKindOfSpells kind word.text (spellsOfText1 kind word.text (Bool.andRight within)) then
    match kind, within with
      | Lower, _ => byComputing
      | Upper, _ => byComputing
      | Num, _ => byComputing
      | Float, _ => byComputing

theorem operatorAssign ∀ (text: Text) (listed: operatorText1 text = True): notAssign text = True :=
  let (kind, spells, _) := operatorSpellsOf text listed
  match assign: text == ":=" with
    | True => (Bool.falseNotTrue (rewrite DecEq.sound assign at listed then listed)).impossible
    | False => kindAssign kind text spells assign

theorem prefixAssign ∀ (text: Text) (listed: prefixText1 text = True): notAssign text = True :=
  match a: text == "-" with
    | True => rewrite DecEq.sound a
    | False =>
      match b: text == "!" with
        | True => rewrite DecEq.sound b
        | False =>
          match c: text == "¬" with
            | True => rewrite DecEq.sound c

--| No token of an expression of the slice is read as `:=`.
--|
--| Proof idea: induction on the expression; each token is a name or numeral, a bracket, a comma or an operator of
--| the slice's table, none of which the lexer reads as `:=`.
theorem exprAssign ∀ (expr: Expr)
    (within: expr.within1 = True)
    (lexical: expr.lexical1 = True)
    (sound: expr.sound = True):
    ((expr.spelt False).filter notComment).all notAssign = True :=
  match expr with
    | Atom kind word => wordAssign word False (atomPlain kind word within).right sound (atomAssign kind word within)
    | Paren open inner close =>
      let (openText, closeText, innerLexical) := lexical
      let (openSound, innerSound, closeSound) := sound
      let (openToken, openOther) := fixedAssign open "(" openText (byComputing, byComputing)
      let (closeToken, closeOther) := fixedAssign close ")" closeText (byComputing, byComputing)
      rewrite List.filterAppend (open.spelledAt False) (inner.spelt False ++ close.spelledAt False) notComment,
          List.filterAppend (inner.spelt False) (close.spelledAt False) notComment then
        allTexts _ _ notAssign
          (wordAssign open False openToken openSound openOther)
          (allTexts _ _ notAssign
            (exprAssign inner within innerLexical innerSound)
            (wordAssign close False closeToken closeSound closeOther))
    | Tuple open items comma close =>
      let (openText, closeText, itemsLexical) := lexical
      let (openSound, itemsSound, closeSound) := sound
      let (openToken, openOther) := fixedAssign open "(" openText (byComputing, byComputing)
      let (closeToken, closeOther) := fixedAssign close ")" closeText (byComputing, byComputing)
      rewrite List.filterAppend (open.spelledAt False) (commaSpelt items ++ close.spelledAt False) notComment,
          List.filterAppend (commaSpelt items) (close.spelledAt False) notComment then
        allTexts _ _ notAssign
          (wordAssign open False openToken openSound openOther)
          (allTexts _ _ notAssign
            (commaAssign items within itemsLexical itemsSound)
            (wordAssign close False closeToken closeSound closeOther))
    | ListOf open items comma close =>
      let (openText, closeText, itemsLexical) := lexical
      let (openSound, itemsSound, closeSound) := sound
      let (openToken, openOther) := fixedAssign open "[" openText (byComputing, byComputing)
      let (closeToken, closeOther) := fixedAssign close "]" closeText (byComputing, byComputing)
      rewrite List.filterAppend (open.spelledAt False) (commaSpelt items ++ close.spelledAt False) notComment,
          List.filterAppend (commaSpelt items) (close.spelledAt False) notComment then
        allTexts _ _ notAssign
          (wordAssign open False openToken openSound openOther)
          (allTexts _ _ notAssign
            (commaAssign items within itemsLexical itemsSound)
            (wordAssign close False closeToken closeSound closeOther))
    | App head arguments =>
      rewrite List.filterAppend (head.spelt False) (argumentsSpelt arguments) notComment then
        allTexts _ _ notAssign
          (exprAssign head (Bool.andLeft within) (Bool.andLeft lexical) (Bool.andLeft sound))
          (argumentsAssign arguments (Bool.andRight within) (Bool.andRight lexical) (Bool.andRight sound))
    | Infix kind left operator right =>
      match kind with
        | InfixBinary =>
          let (leftWithin, rightWithin, listed) := within
          infixAssign left operator right leftWithin rightWithin listed lexical sound
        | InfixArrow =>
          let (leftWithin, rightWithin, listed) := within
          infixAssign left operator right leftWithin rightWithin listed lexical sound
        | _ => cases
    | Prefix operator operand =>
      let (operandWithin, listed) := within
      let (operatorSound, operandSound) := sound
      rewrite List.filterAppend (operator.spelledAt False) (operand.spelt False) notComment then
        allTexts _ _ notAssign
          (wordAssign operator False
            (prefixPlain operator.text listed).right
            operatorSound
            (prefixAssign operator.text listed))
          (exprAssign operand operandWithin (Bool.andRight lexical) operandSound)

theorem infixAssign ∀ (left: Expr) (operator: Word) (right: Expr)
    (leftWithin: left.within1 = True)
    (rightWithin: right.within1 = True)
    (listed: operatorText1 operator.text = True)
    (lexical: (left.lexical1 && (operatorTok operator.text).isSome && right.lexical1) = True)
    (sound: (left.sound && operator.sound && right.sound) = True):
    (((left.spelt False ++ operator.spelledAt False ++ right.spelt False).filter notComment).all notAssign) = True :=
  let (leftLexical, _, rightLexical) := lexical
  let (leftSound, operatorSound, rightSound) := sound
  rewrite List.filterAppend (left.spelt False) (operator.spelledAt False ++ right.spelt False) notComment,
      List.filterAppend (operator.spelledAt False) (right.spelt False) notComment then
    allTexts _ _ notAssign
      (exprAssign left leftWithin leftLexical leftSound)
      (allTexts _ _ notAssign
        (wordAssign operator False
          (operatorPlain operator.text listed).right
          operatorSound
          (operatorAssign operator.text listed))
        (exprAssign right rightWithin rightLexical rightSound))

theorem commaAssign ∀ (items: List Expr)
    (within: allWithin1 items = True)
    (lexical: allLexical1 items = True)
    (sound: allSound items = True):
    ((commaSpelt items).filter notComment).all notAssign = True :=
  match items with
    | [] => byComputing
    | [item] => exprAssign item (Bool.andLeft within) (Bool.andLeft lexical) (Bool.andLeft sound)
    | [item, next, ..more] =>
      rewrite List.filterAppend (item.spelt False) ([","] ++ commaSpelt [next, ..more]) notComment then
        allTexts
          ((item.spelt False).filter notComment)
          [",", ..(commaSpelt [next, ..more]).filter notComment]
          notAssign
          (exprAssign item (Bool.andLeft within) (Bool.andLeft lexical) (Bool.andLeft sound))
          (Bool.andIntro byComputing
            (commaAssign [next, ..more] (Bool.andRight within) (Bool.andRight lexical) (Bool.andRight sound)))

theorem argumentsAssign ∀ (arguments: List Expr)
    (within: allWithin1 arguments = True)
    (lexical: allLexical1 arguments = True)
    (sound: allSound arguments = True):
    ((argumentsSpelt arguments).filter notComment).all notAssign = True :=
  match arguments with
    | [] => byComputing
    | [argument, ..rest] =>
      rewrite List.filterAppend (argument.spelt False) (argumentsSpelt rest) notComment then
        allTexts _ _ notAssign
          (exprAssign argument (Bool.andLeft within) (Bool.andLeft lexical) (Bool.andLeft sound))
          (argumentsAssign rest (Bool.andRight within) (Bool.andRight lexical) (Bool.andRight sound))

-- The declaration.

theorem headerNameWithin ∀ (header: Header) (within: header.within1 = True): header.name.nameWithin1 = True :=
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
      } => Bool.andLeft within

--| A definition's spelling at its type: the head (`def`, the name and `:`), the type, the `:=` and the value.
theorem speltParts ∀ (header: Header) (colonEq: Syntax.Comments) (value: Expr):
    (Definition [] header (Assigned colonEq value)).spelt
      = (((fixedWord "def" header.keyword).spelledAt True ++ header.name.spelledAt False)
        ++ (fixedWord ":" header.colon).spelledAt False)
        ++ (header.result.spelt False ++ ((fixedWord ":=" colonEq).spelledAt False ++ value.spelt False)) :=
  rewrite List.appendAssoc
        ((fixedWord "def" header.keyword).spelledAt True ++ header.name.spelledAt False)
        ((fixedWord ":" header.colon).spelledAt False ++ header.result.spelt False)
        ((fixedWord ":=" colonEq).spelledAt False ++ value.spelt False),
      List.appendAssoc
        ((fixedWord ":" header.colon).spelledAt False)
        (header.result.spelt False)
        ((fixedWord ":=" colonEq).spelledAt False ++ value.spelt False),
      List.appendAssoc
        ((fixedWord "def" header.keyword).spelledAt True ++ header.name.spelledAt False)
        ((fixedWord ":" header.colon).spelledAt False)
        (header.result.spelt False ++ ((fixedWord ":=" colonEq).spelledAt False ++ value.spelt False))

theorem valueQuiet ∀ (pairs: List (Text, Bool))
    (line: valueMarks pairs = True):
    tailQuiet (spread False pairs) = True :=
  match pairs with
    | [] => byComputing
    | [pair, ..rest] => spreadValue [pair, ..rest] (Bool.notTrue _ line)

--| The marks of a declaration's printed tokens, read as `onLine1` reads their line starts, put the tree's comments
--| where `wordsEdge1` allows them.
--|
--| Proof idea: the marks' texts are the declaration's tokens, so they split into the head's three, the type's, the
--| `:=` and the value's; `marksOnLine` leaves the type's and the value's after its first unmarked. Over the tokens that
--| are no closers the marks are the tree's (`spreaded`), and the lengths of the parts match, so the type's marks are
--| all clear and the value's clear after its first: `wordsEdgeOfMarks` on each, through `calm`.
theorem wordsEdgeOfPairs ∀ (decl: Decl) (pairs: List (Text, Bool))
    (within: decl.within1 = True)
    (shaped: decl.shaped1 = True)
    (settled: decl.settled1 = True)
    (lexical: decl.lexical1 = True)
    (texts: pairs.map Pair.fst = decl.spelt.filter notComment)
    (spreaded: spread False pairs = marks False (decl.spelt.filter notCloser))
    (line: marksOnLine pairs = True):
    decl.wordsEdge1 = True :=
  match decl with
    | Definition [] header (Assigned colonEq value) =>
      let (headerWithin, valueWithin) := within
      let resultWithin := headerResultWithin header headerWithin
      let nameWithin := headerNameWithin header headerWithin
      let (nameCloser, nameToken) :=
        kindPlain Lower header.name.text
          (spellsOfText1 Lower header.name.text (Bool.andRight nameWithin))
          (wordQuiet Lower byComputing)
      let (resultShaped, valueShaped) := shaped
      let (_, resultLexical, valueLexical) := lexical
      let sound := declSoundOfSettled _ within settled (declRealOfLexical _ within lexical)
      let (defSound, nameSound, colonSound, resultSound, assignSound, valueSound) := sound
      let head :=
        ((fixedWord "def" header.keyword).spelledAt True ++ header.name.spelledAt False)
          ++ (fixedWord ":" header.colon).spelledAt False
      let typeSpelt := header.result.spelt False
      let assign := (fixedWord ":=" colonEq).spelledAt False
      let body := value.spelt False
      let parts := speltParts header colonEq value
      let headTokens: head.filter notComment = ["def", header.name.text, ":"] :=
        rewrite List.filterAppend
              ((fixedWord "def" header.keyword).spelledAt True ++ header.name.spelledAt False)
              ((fixedWord ":" header.colon).spelledAt False)
              notComment,
            List.filterAppend
              ((fixedWord "def" header.keyword).spelledAt True)
              (header.name.spelledAt False)
              notComment,
            wordTokens (fixedWord "def" header.keyword) True byComputing defSound,
            wordTokens header.name False nameToken nameSound,
            wordTokens (fixedWord ":" header.colon) False byComputing colonSound
      let assignTokens: assign.filter notComment = [":="] :=
        wordTokens (fixedWord ":=" colonEq) False byComputing assignSound
      let tokensSplit: (head ++ (typeSpelt ++ (assign ++ body))).filter notComment
        = ["def", header.name.text, ":"] ++ (typeSpelt.filter notComment ++ ([":="] ++ body.filter notComment)) :=
        rewrite List.filterAppend head (typeSpelt ++ (assign ++ body)) notComment,
            List.filterAppend typeSpelt (assign ++ body) notComment,
            List.filterAppend assign body notComment,
            headTokens,
            assignTokens
      let pairsTexts: pairs.map Pair.fst
        = ["def", header.name.text, ":"] ++ (typeSpelt.filter notComment ++ ([":="] ++ body.filter notComment)) :=
        calc pairs.map Pair.fst
          _ = (Definition [] header (Assigned colonEq value)).spelt.filter notComment := texts
          _ = (head ++ (typeSpelt ++ (assign ++ body))).filter notComment :=
            Eq.cong ((spelt: List Text) => spelt.filter notComment) parts
          _ = ["def", header.name.text, ":"] ++ (typeSpelt.filter notComment ++ ([":="] ++ body.filter notComment)) :=
            tokensSplit
      let (front, rest, split1, frontTexts, restTexts) :=
        splitMap pairs
          ["def", header.name.text, ":"]
          (typeSpelt.filter notComment ++ ([":="] ++ body.filter notComment))
          pairsTexts
      let (typePairs, later, split2, typeTexts, laterTexts) :=
        splitMap rest (typeSpelt.filter notComment) ([":="] ++ body.filter notComment) restTexts
      let (assignPairs, valuePairs, split3, assignTexts, valueTexts) :=
        splitMap later [":="] (body.filter notComment) laterTexts
      let (x, y, z, frontIs) := threeOf front "def" header.name.text ":" frontTexts
      let (w, assignIs) := oneOf assignPairs ":=" assignTexts
      let whole: pairs = [("def", x), (header.name.text, y), (":", z)] ++ (typePairs ++ ([(":=", w)] ++ valuePairs)) :=
        rewrite split1, split2, split3, frontIs, assignIs
      let typeLine: typeMarks (typePairs ++ ([(":=", w)] ++ valuePairs)) = True := rewrite whole at line then line
      let typeNoAssign: (typePairs.map Pair.fst).all notAssign = True :=
        rewrite typeTexts then exprAssign header.result resultWithin resultLexical resultSound
      let (typeQuiet, afterType) := typeSplit typePairs ([(":=", w)] ++ valuePairs) typeNoAssign typeLine
      let valueLine: valueMarks valuePairs = True := afterType
      let spreadPairs: spread False pairs = [x, y, z] ++ (spread False typePairs ++ ([w] ++ spread False valuePairs)) :=
        rewrite whole, nameCloser, spreadAppend typePairs ([(":=", w)] ++ valuePairs) typeQuiet
      let headF := head.filter notCloser
      let typeF := typeSpelt.filter notCloser
      let assignF := assign.filter notCloser
      let bodyF := body.filter notCloser
      let typePending := pendingAfter False headF
      let assignPending := pendingAfter typePending typeF
      let valuePending := pendingAfter assignPending assignF
      let marksSplit: marks False ((head ++ (typeSpelt ++ (assign ++ body))).filter notCloser)
        = marks False headF ++ (marks typePending typeF ++ (marks assignPending assignF ++ marks valuePending bodyF)) :=
        rewrite List.filterAppend head (typeSpelt ++ (assign ++ body)) notCloser,
            List.filterAppend typeSpelt (assign ++ body) notCloser,
            List.filterAppend assign body notCloser,
            marksAppend False headF (typeF ++ (assignF ++ bodyF)),
            marksAppend typePending typeF (assignF ++ bodyF),
            marksAppend assignPending assignF bodyF
      let equal: marks False headF
        ++ (marks typePending typeF ++ (marks assignPending assignF ++ marks valuePending bodyF))
        = [x, y, z] ++ (spread False typePairs ++ ([w] ++ spread False valuePairs)) :=
        calc marks False headF ++ (marks typePending typeF ++ (marks assignPending assignF ++ marks valuePending bodyF))
          _ = marks False ((head ++ (typeSpelt ++ (assign ++ body))).filter notCloser) := marksSplit.flipped
          _ = marks False ((Definition [] header (Assigned colonEq value)).spelt.filter notCloser) :=
            (Eq.cong ((spelt: List Text) => marks False (spelt.filter notCloser)) parts).flipped
          _ = spread False pairs := spreaded.flipped
          _ = [x, y, z] ++ (spread False typePairs ++ ([w] ++ spread False valuePairs)) := spreadPairs
      let headLength: (marks False headF).length = [x, y, z].length :=
        rewrite lengthMarks False headF, filterSwap notCloser notComment head, headTokens, nameCloser
      let typeLength: (marks typePending typeF).length = (spread False typePairs).length :=
        rewrite lengthMarks typePending typeF,
            filterSwap notCloser notComment typeSpelt,
            lengthSpread False typePairs,
            typeTexts
      let assignLength: (marks assignPending assignF).length = [w].length :=
        rewrite lengthMarks assignPending assignF, filterSwap notCloser notComment assign, assignTokens
      let typeM := marks typePending typeF
      let assignM := marks assignPending assignF
      let valueM := marks valuePending bodyF
      let typeS := spread False typePairs
      let valueS := spread False valuePairs
      let afterHead: typeM ++ (assignM ++ valueM) = typeS ++ ([w] ++ valueS) :=
        appendCancel
          (marks False headF)
          (typeM ++ (assignM ++ valueM))
          [x, y, z]
          (typeS ++ ([w] ++ valueS))
          headLength
          equal
      let typeMarksEq: typeM = typeS :=
        appendCancelFront typeM (assignM ++ valueM) typeS ([w] ++ valueS) typeLength afterHead
      let afterTypeMarks: assignM ++ valueM = [w] ++ valueS :=
        appendCancel typeM (assignM ++ valueM) typeS ([w] ++ valueS) typeLength afterHead
      let valueMarksEq: valueM = valueS := appendCancel assignM valueM [w] valueS assignLength afterTypeMarks
      let typeAll: (marks typePending typeF).all (mark => !mark) = True :=
        rewrite typeMarksEq then spreadQuiet typePairs typeQuiet
      let (typeFirst, typeTail) := quietAll typeM typeAll
      let typeEdges: EdgeMarks typePending typeF False True :=
        (_ => typeFirst, typeTail, never => (Bool.trueNotFalse never).impossible)
      let valueEdges: EdgeMarks valuePending bodyF True True := (
        never => (Bool.trueNotFalse never).impossible,
        rewrite valueMarksEq then valueQuiet valuePairs valueLine,
        never => (Bool.trueNotFalse never).impossible
      )
      rewrite wordsEdgeCalm header.result False False True resultWithin,
          wordsEdgeCalm value False True True valueWithin then
        Bool.andIntro
          (wordsEdgeOfMarks header.result False True typePending resultWithin resultShaped resultLexical resultSound
              typeEdges)
          (wordsEdgeOfMarks value True True valuePending valueWithin valueShaped valueLexical valueSound valueEdges)

--| `wordsEdgeOneLine1`: a slice 1 declaration that prints on one line has comments on tokens that are no closers
--| only at the edges `wordsEdge1` allows.
--|
--| Proof idea: the printed tokens with a comment since the one before start their lines (`declCovered`), which
--| `onLine1` allows only at the `:=` and the value's first token (`lineCov`); the printed words agree with the tree's
--| once the closers or the comments are left out (`printedSpellsSettled`), so the marks carry over to the tree's
--| tokens that are no closers (`spreadMarked`), and `wordsEdgeOfPairs` reads them.
theorem wordsEdgeOneLine ∀ (decl: Decl)
    (within: decl.within1 = True)
    (shaped: decl.shaped1 = True)
    (settled: decl.settled1 = True)
    (lexical: decl.lexical1 = True)
    (oneLine: decl.oneLine1 = True):
    decl.wordsEdge1 = True :=
  match shows: decl.doc1 with
    | Some doc =>
      let (spelledF, spelledG) :=
        printedSpellsSettled decl doc width within settled (declRealOfLexical decl within lexical) shows
      let cov := declCovered decl doc within shaped settled lexical shows
      let (texts, kinded) := printedTokens1 decl within shaped settled lexical
      let printed := wordsOf (printedPieces doc width)
      let pairsSpelt: (marked False printed).map Pair.fst = decl.spelt.filter notComment :=
        Eq.trans (fstMarked False printed) spelledG
      let pairsTokens: (marked False printed).map Pair.fst = (tokens decl.leaves1).map (token => token.text) :=
        calc (marked False printed).map Pair.fst
          _ = decl.spelt.filter notComment := pairsSpelt
          _ = tokenTexts decl.leaves1 := texts.flipped
          _ = (tokens decl.leaves1).map (token => token.text) := (textsTokens decl.leaves1).flipped
      let line :=
        lineCov (marked False printed) (tokens decl.leaves1) cov pairsTokens (kindedTokens decl.leaves1 kinded) oneLine
      let spreaded: spread False (marked False printed) = marks False (decl.spelt.filter notCloser) :=
        rewrite spreadMarked printed False False, spelledF
      wordsEdgeOfPairs decl (marked False printed) within shaped settled lexical pairsSpelt spreaded line

-- Closed examples.

theorem operatorAssignExample: notAssign "==" = True := operatorAssign "==" byComputing

--| `def x: T := a` printed on one line, with no marks.
def lineTokens: List Token := [
  { kind = KwDef, text = "def", column = 0, lineStart = True },
  { kind = Lower, text = "x", column = 4, lineStart = False },
  { kind = Colon, text = ":", column = 5, lineStart = False },
  { kind = Upper, text = "T", column = 7, lineStart = False },
  { kind = ColonEq, text = ":=", column = 9, lineStart = False },
  { kind = Lower, text = "a", column = 12, lineStart = False }
]

theorem lineCovExample: marksOnLine [
      ("def", True),
      ("x", False),
      (":", False),
      ("T", False),
      (":=", False),
      ("a", False)
    ]
      = True :=
  lineCov
    [("def", True), ("x", False), (":", False), ("T", False), (":=", False), ("a", False)]
    lineTokens
    byComputing
    byComputing
    byComputing
    byComputing
