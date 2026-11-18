--| `printedSpelledPlain1` (SW-4085): the output's names and numerals are spelled plainly.
--|
--| The texts the rules print for a declaration (`Decl.spelt`) are the tree's words' texts, commas and comments. A text
--| passes (`passText`) when it is a comment, or the kind the lexer gives it is no name or numeral, or it is spelled
--| as slice 1 spells one (`textSpells1`). Every text of a declaration passes: a name's or numeral's by `within1`, an
--| operator's, bracket's and keyword's because its kind is none of a word's. `printedTokens1` carries the texts to
--| the declaration's leaves, and the file's leaves are its declarations' (`printedSpelledPlain1`).

namespace Fmt.SpelledOutputProofs
import Std (Bool, DecEq, Eq, List, Nat, Option, Text)
import Syntax (..)
import Syntax.GoodItemProofs (..)
import Syntax.SettleProofs (tokens)
import Fmt (..)
import Fmt.SpellProofs (..)
import Fmt.TreeJoinProofs (..)
import Fmt.TokenProofs (declRealOfLexical, printedTokens1)
import Fmt.OutputStatements (..)
import Fmt.FileLexProofs (..)

--| The text, lexed alone, is no name or numeral, or is spelled plainly as its kind.
def spellText (text: Text): Bool := !(lexKind text).wordWithin1 || textSpells1 (lexKind text) text

def passText (text: Text): Bool := !notComment text || spellText text

theorem allPassAppend ∀ (xs ys: List Text): (xs ++ ys).all passText = (xs.all passText && ys.all passText) :=
  match xs with
    | [] => byComputing
    | [first, ..rest] =>
      match passText first with
        | True => allPassAppend rest ys
        | False => byComputing

-- A token.

--| A name or numeral, as `within1` spells it.
theorem spellOfWord ∀ (kind: Tok) (text: Text)
    (within: (kind.wordWithin1 && textSpells1 kind text) = True):
    passText text = True :=
  let spells := spellsOfText1 kind text (Bool.andRight within)
  rewrite lexKindOfSpells kind text spells then Bool.orRight (Bool.orRight (Bool.andRight within))

--| A text that is a comment passes.
theorem passComment ∀ (text: Text) (comment: commentText text = True): passText text = True :=
  rewrite Bool.andLeft comment

theorem passNotes ∀ (notes: List Note)
    (sound: notesSound notes = True):
    (notes.map (note => note.text)).all passText = True :=
  match notes with
    | [] => byComputing
    | [note, ..rest] => rewrite passComment note.text (Bool.andLeft sound) then passNotes rest (Bool.andRight sound)

theorem passAfter ∀ (after: Option Text) (sound: afterSound after = True): after.toList.all passText = True :=
  match after with
    | None => byComputing
    | Some comment => rewrite passComment comment sound

--| A token with its comments passes when its text does.
theorem wordPass ∀ (word: Word) (hoisted: Bool)
    (sound: word.sound = True)
    (text: passText word.text = True):
    (word.spelledAt hoisted).all passText = True :=
  let front: (if hoisted then [] else word.comments.above.map (note => note.text)).all passText = True :=
    match hoisted with
      | True => byComputing
      | False => passNotes word.comments.above (Bool.andLeft (Bool.andRight sound))
  rewrite allPassAppend
        (if hoisted then [] else word.comments.above.map (note => note.text))
        ([word.text] ++ word.comments.after.toList),
      allPassAppend [word.text] word.comments.after.toList,
      front,
      text,
      passAfter word.comments.after (Bool.andRight (Bool.andRight sound))

theorem passJoin ∀ [xs ys: List Text]
    (first: xs.all passText = True)
    (second: ys.all passText = True):
    (xs ++ ys).all passText = True :=
  rewrite allPassAppend xs ys, first, second

-- Operators.

theorem opLit ∀ (text literal: Text)
    (same: (text == literal) = True)
    (facts: passText literal = True):
    passText text = True :=
  rewrite DecEq.sound same then facts

theorem passA ∀ (text: Text) (listed: operatorTextA1 text = True): passText text = True := match a0: text == "->" with
  | True => opLit text "->" a0 byComputing
  | False =>
    match a1: text == "→" with
      | True => opLit text "→" a1 byComputing
      | False =>
        match a2: text == "||" with
          | True => opLit text "||" a2 byComputing
          | False =>
            match a3: text == "∨" with
              | True => opLit text "∨" a3 byComputing
              | False =>
                match a4: text == "&&" with
                  | True => opLit text "&&" a4 byComputing
                  | False =>
                    match a5: text == "∧" with
                      | True => opLit text "∧" a5 byComputing

theorem passB ∀ (text: Text) (listed: operatorTextB1 text = True): passText text = True := match a0: text == "+" with
  | True => opLit text "+" a0 byComputing
  | False =>
    match a1: text == "++" with
      | True => opLit text "++" a1 byComputing
      | False =>
        match a2: text == "-" with
          | True => opLit text "-" a2 byComputing
          | False =>
            match a3: text == "*" with
              | True => opLit text "*" a3 byComputing
              | False =>
                match a4: text == "/" with
                  | True => opLit text "/" a4 byComputing
                  | False =>
                    match a5: text == "%" with
                      | True => opLit text "%" a5 byComputing

theorem passC ∀ (text: Text) (listed: operatorTextC1 text = True): passText text = True := match a0: text == "!=" with
  | True => opLit text "!=" a0 byComputing
  | False =>
    match a1: text == "≠" with
      | True => opLit text "≠" a1 byComputing
      | False =>
        match a2: text == "<" with
          | True => opLit text "<" a2 byComputing
          | False =>
            match a3: text == "<=" with
              | True => opLit text "<=" a3 byComputing
              | False =>
                match a4: text == "≤" with
                  | True => opLit text "≤" a4 byComputing

theorem passD ∀ (text: Text) (listed: operatorTextD1 text = True): passText text = True := match a0: text == ">" with
  | True => opLit text ">" a0 byComputing
  | False =>
    match a1: text == ">=" with
      | True => opLit text ">=" a1 byComputing
      | False =>
        match a2: text == "≥" with
          | True => opLit text "≥" a2 byComputing
          | False =>
            match a3: text == "==" with
              | True => opLit text "==" a3 byComputing
              | False =>
                match a4: text == "=" with
                  | True => opLit text "=" a4 byComputing

--| An infix operator `within1` lets through passes.
theorem passOperator ∀ (text: Text) (listed: operatorText1 text = True): passText text = True :=
  match first: operatorTextA1 text with
    | True => passA text first
    | False =>
      match second: operatorTextB1 text with
        | True => passB text second
        | False =>
          match third: operatorTextC1 text with
            | True => passC text third
            | False => passD text listed

--| A prefix operator `within1` lets through passes.
theorem passPrefix ∀ (text: Text) (listed: prefixText1 text = True): passText text = True := match a0: text == "-" with
  | True => opLit text "-" a0 byComputing
  | False =>
    match a1: text == "!" with
      | True => opLit text "!" a1 byComputing
      | False =>
        match a2: text == "¬" with
          | True => opLit text "¬" a2 byComputing

-- Expressions.

theorem passComma ∀ (first: Expr) (rest: List Expr)
    (within: allWithin1 [first, ..rest] = True)
    (sound: allSound [first, ..rest] = True)
    (lexical: allLexical1 [first, ..rest] = True):
    (commaSpelt [first, ..rest]).all passText = True :=
  match rest with
    | [] => exprPass first False (Bool.andLeft within) (Bool.andLeft sound) (Bool.andLeft lexical)
    | [next, ..more] =>
      rewrite allPassAppend (first.spelt False) ([","] ++ commaSpelt [next, ..more]),
          exprPass first False (Bool.andLeft within) (Bool.andLeft sound) (Bool.andLeft lexical),
          allPassAppend [","] (commaSpelt [next, ..more]),
          passComma next more (Bool.andRight within) (Bool.andRight sound) (Bool.andRight lexical)

theorem passItems ∀ (items: List Expr)
    (within: allWithin1 items = True)
    (sound: allSound items = True)
    (lexical: allLexical1 items = True):
    (commaSpelt items).all passText = True :=
  match items with
    | [] => byComputing
    | [first, ..rest] => passComma first rest within sound lexical

theorem passArguments ∀ (arguments: List Expr)
    (within: allWithin1 arguments = True)
    (sound: allSound arguments = True)
    (lexical: allLexical1 arguments = True):
    (argumentsSpelt arguments).all passText = True :=
  match arguments with
    | [] => byComputing
    | [argument, ..rest] =>
      rewrite allPassAppend (argument.spelt False) (argumentsSpelt rest),
          exprPass argument False (Bool.andLeft within) (Bool.andLeft sound) (Bool.andLeft lexical),
          passArguments rest (Bool.andRight within) (Bool.andRight sound) (Bool.andRight lexical)

--| Every text the rules print for an expression of the slice passes.
--|
--| Proof idea: Induction on the expression; a name's or numeral's text by `within1` (`spellOfWord`), an operator's
--| by its list (`passOperator`), a bracket's and a comma's by computing, comments pass, and the parts are appended.
theorem exprPass ∀ (expr: Expr) (hoisted: Bool)
    (within: expr.within1 = True)
    (sound: expr.sound = True)
    (lexical: expr.lexical1 = True):
    (expr.spelt hoisted).all passText = True :=
  match expr with
    | Atom kind word => wordPass word hoisted sound (spellOfWord kind word.text within)
    | Paren open inner close =>
      let openPass: passText open.text = True := rewrite DecEq.sound (Bool.andLeft lexical)
      let closePass: passText close.text = True := rewrite DecEq.sound (Bool.andLeft (Bool.andRight lexical))
      rewrite allPassAppend (open.spelledAt hoisted) (inner.spelt False ++ close.spelledAt False),
          allPassAppend (inner.spelt False) (close.spelledAt False),
          wordPass open hoisted (Bool.andLeft sound) openPass,
          exprPass inner False within (Bool.andLeft (Bool.andRight sound)) (Bool.andRight (Bool.andRight lexical)),
          wordPass close False (Bool.andRight (Bool.andRight sound)) closePass
    | Tuple open items comma close =>
      let openPass: passText open.text = True := rewrite DecEq.sound (Bool.andLeft lexical)
      let closePass: passText close.text = True := rewrite DecEq.sound (Bool.andLeft (Bool.andRight lexical))
      rewrite allPassAppend (open.spelledAt hoisted) (commaSpelt items ++ close.spelledAt False),
          allPassAppend (commaSpelt items) (close.spelledAt False),
          wordPass open hoisted (Bool.andLeft sound) openPass,
          passItems items within (Bool.andLeft (Bool.andRight sound)) (Bool.andRight (Bool.andRight lexical)),
          wordPass close False (Bool.andRight (Bool.andRight sound)) closePass
    | ListOf open items comma close =>
      let openPass: passText open.text = True := rewrite DecEq.sound (Bool.andLeft lexical)
      let closePass: passText close.text = True := rewrite DecEq.sound (Bool.andLeft (Bool.andRight lexical))
      rewrite allPassAppend (open.spelledAt hoisted) (commaSpelt items ++ close.spelledAt False),
          allPassAppend (commaSpelt items) (close.spelledAt False),
          wordPass open hoisted (Bool.andLeft sound) openPass,
          passItems items within (Bool.andLeft (Bool.andRight sound)) (Bool.andRight (Bool.andRight lexical)),
          wordPass close False (Bool.andRight (Bool.andRight sound)) closePass
    | App head arguments =>
      rewrite allPassAppend (head.spelt hoisted) (argumentsSpelt arguments),
          exprPass head hoisted (Bool.andLeft within) (Bool.andLeft sound) (Bool.andLeft lexical),
          passArguments arguments (Bool.andRight within) (Bool.andRight sound) (Bool.andRight lexical)
    | Infix kind left operator right =>
      let (leftWithin, rightWithin) := infixWithin kind left operator right within
      let listed: operatorText1 operator.text = True := match kind with
        | InfixBinary => Bool.andRight (Bool.andRight within)
        | InfixArrow => Bool.andRight (Bool.andRight within)
        | _ => cases
      rewrite allPassAppend (left.spelt hoisted) (operator.spelledAt False ++ right.spelt False),
          allPassAppend (operator.spelledAt False) (right.spelt False),
          exprPass left hoisted leftWithin (Bool.andLeft sound) (Bool.andLeft lexical),
          wordPass operator False (Bool.andLeft (Bool.andRight sound)) (passOperator operator.text listed),
          exprPass right False rightWithin (Bool.andRight (Bool.andRight sound)) (Bool.andRight (Bool.andRight lexical))
    | Prefix operator operand =>
      rewrite allPassAppend (operator.spelledAt hoisted) (operand.spelt False),
          wordPass operator hoisted (Bool.andLeft sound) (passPrefix operator.text (Bool.andRight within)),
          exprPass operand False (Bool.andLeft within) (Bool.andRight sound) (Bool.andRight lexical)

-- A declaration.

--| Every text the rules print for a declaration passes.
theorem declPass ∀ (decl: Decl)
    (within: decl.within1 = True)
    (sound: decl.sound = True)
    (lexical: decl.lexical1 = True):
    decl.spelt.all passText = True :=
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
          let namePass :=
            spellOfWord Lower name.text (Bool.andIntro byComputing (Bool.andRight (Bool.andLeft (Bool.andLeft within))))
          let resultPass :=
            exprPass result False
              (Bool.andRight (Bool.andLeft within))
              (Bool.andLeft (Bool.andRight (Bool.andRight (Bool.andRight sound))))
              (Bool.andLeft (Bool.andRight lexical))
          let valuePass :=
            exprPass value False
              (Bool.andRight within)
              (Bool.andRight (Bool.andRight (Bool.andRight (Bool.andRight (Bool.andRight sound)))))
              (Bool.andRight (Bool.andRight lexical))
          let keywordPass := wordPass (fixedWord "def" keyword) True (Bool.andLeft sound) byComputing
          let nameWordPass := wordPass name False (Bool.andLeft (Bool.andRight sound)) namePass
          let colonPass :=
            wordPass (fixedWord ":" colon) False (Bool.andLeft (Bool.andRight (Bool.andRight sound))) byComputing
          let assignPass :=
            wordPass
              (fixedWord ":=" colonEq)
              False
              (Bool.andLeft (Bool.andRight (Bool.andRight (Bool.andRight (Bool.andRight sound)))))
              byComputing
          passJoin
            (passJoin (passJoin keywordPass nameWordPass) (passJoin colonPass resultPass))
            (passJoin assignPass valuePass)
        | _ => cases

-- Leaves.

--| The texts that are no comments are spelled plainly.
theorem filterPass ∀ (texts: List Text)
    (pass: texts.all passText = True):
    (texts.filter notComment).all spellText = True :=
  match texts with
    | [] => byComputing
    | [text, ..rest] =>
      match comment: notComment text with
        | True =>
          let here: passText text = True := Bool.andLeft pass
          let spell: spellText text = True := rewrite comment at here then here
          rewrite spell then filterPass rest (Bool.andRight pass)
        | False => filterPass rest pass

def leafSpelled (leaves: List Leaf): Bool := leaves.all (leaf => leaf.token.spelledPlain1)

--| Leaves of the lexer's kinds for their texts, which are spelled plainly, are spelled plainly.
theorem leavesSpelled ∀ (leaves: List Leaf)
    (kinded: leaves.all Leaf.kinded = True)
    (spelled: (tokenTexts leaves).all spellText = True):
    leafSpelled leaves = True :=
  match leaves with
    | [] => byComputing
    | [leaf, ..rest] =>
      let lexes: lexKind leaf.token.text = leaf.token.kind := (DecEq.sound (Bool.andLeft kinded)).flipped
      let here: spellText leaf.token.text = True := Bool.andLeft spelled
      rewrite lexes at here then Bool.andIntro here (leavesSpelled rest (Bool.andRight kinded) (Bool.andRight spelled))

--| A declaration's printed leaves are spelled plainly.
theorem declLeavesSpelled ∀ (decl: Decl)
    (within: decl.within1 = True)
    (shaped: decl.shaped1 = True)
    (settled: decl.settled1 = True)
    (lexical: decl.lexical1 = True):
    leafSpelled decl.leaves1 = True :=
  let sound := declSoundOfSettled decl within settled (declRealOfLexical decl within lexical)
  let (texts, kinded) := printedTokens1 decl within shaped settled lexical
  leavesSpelled decl.leaves1 kinded (rewrite texts then filterPass decl.spelt (declPass decl within sound lexical))

theorem leafSpelledAppend ∀ (xs ys: List Leaf): leafSpelled (xs ++ ys) = (leafSpelled xs && leafSpelled ys) :=
  match xs with
    | [] => byComputing
    | [first, ..rest] =>
      match first.token.spelledPlain1 with
        | True => leafSpelledAppend rest ys
        | False => byComputing

theorem headedSpelled ∀ (above: List Comment) (blank: Nat) (leaves: List Leaf):
    leafSpelled (headed above blank leaves) = leafSpelled leaves :=
  match leaves with
    | [] => byComputing
    | [first, ..rest] => byComputing

theorem declLaidSpelled ∀ (decl: Decl) (empty: Bool)
    (spelled: leafSpelled decl.leaves1 = True):
    leafSpelled (decl.laid1 empty) = True :=
  rewrite headedSpelled
        (laidNotes empty decl.firstComments.above)
        (if decl.firstComments.blankBefore && !(empty && decl.firstComments.above.isEmpty) then 1 else 0)
        decl.leaves1 then
    spelled

theorem groupsSpelled ∀ (empty: Bool) (decls: List Decl)
    (within: decls.all Decl.within1 = True)
    (shaped: decls.all Decl.shaped1 = True)
    (settled: decls.all Decl.settled1 = True)
    (lexical: decls.all Decl.lexical1 = True):
    leafSpelled (groupsFrom empty decls).concat = True :=
  match decls with
    | [] => byComputing
    | [decl, ..rest] =>
      rewrite leafSpelledAppend (decl.laid1 empty) (groupsFrom False rest).concat,
          declLaidSpelled decl empty
            (declLeavesSpelled decl
              (Bool.andLeft within)
              (Bool.andLeft shaped)
              (Bool.andLeft settled)
              (Bool.andLeft lexical)) then
        groupsSpelled False rest
          (Bool.andRight within)
          (Bool.andRight shaped)
          (Bool.andRight settled)
          (Bool.andRight lexical)

--| `printedSpelledPlain1`: the output's names and numerals are spelled plainly, so the second run passes the driver's
--| `spelledPlain1` test.
--|
--| Proof idea: every text the rules print for a declaration passes (`declPass`: a name's or numeral's by `within1`, any
--| other token's kind is no word's), `printedTokens1` makes them the declaration's leaves' texts, each of the lexer's
--| kind, and the file's leaves are its declarations' (`groupsSpelled`).
theorem printedSpelledPlain1 ∀ (file: SourceFile)
    (within: file.within1 = True)
    (shaped: file.shaped1 = True)
    (settled: file.settled1 = True)
    (lexical: file.lexical1 = True):
    spelledPlain1 file.lexed1.leaves = True :=
  Eq.trans
    (List.allMapBool file.lexed1.leaves (token => token.spelledPlain1) (leaf => leaf.token))
    (groupsSpelled True file.decls within shaped (Bool.andLeft settled) lexical)
