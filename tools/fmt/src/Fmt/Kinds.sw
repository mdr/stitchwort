--| A slice 1 tree's token kinds, commas included (docs/reviews/SW-4166-carried-walk-plan.md §2.1), and the facts that
--| tie the driver's slice (`within1`) to the grammar's (`grammar1`): `within1` asks all `grammar1` does and more.
--|
--| `Expr.words` leaves commas out, so it can't say where a tuple's or a list's commas are; `Expr.kinds` keeps them, at
--| the places `Fmt.SourcePlainProofs.itemsShapes` has them. An operator's kind is read off its text: the one token kind
--| `Syntax.LexProofs.Spells` spells with it.

namespace Fmt.Kinds
import Std (Bool, DecEq, List, Option, Result, Text)
import Fmt (..)
import Syntax (Decl, DefBody, DefKind, Expr, Header, InfixKind, SourceFile, Tok, Word, lex)
import Fmt.Grammar1 (..)

-- Kinds.

--| The kind of a binary operator's token, from its text: the one whose spellings include it. A text that spells no
--| binary operator of slice 1 gets `Plus`; `within1` keeps such a node out of the slice.
def binaryKind (text: Text): Tok :=
  if text == "||" || text == "∨" then OrOr
  else if text == "&&" || text == "∧" then AndAnd
  else if text == "++" then PlusPlus
  else if text == "-" then Minus
  else if text == "*" then Star
  else if text == "/" then Slash
  else if text == "%" then Percent
  else if text == "!=" || text == "≠" then NotEq
  else if text == "<" then Lt
  else if text == "<=" || text == "≤" then Le
  else if text == ">" then Gt
  else if text == ">=" || text == "≥" then Ge
  else if text == "==" then EqEq
  else if text == "=" then Equals
  else Plus

--| The kind of a prefix operator's token, from its text: `-` is `Minus`, and `!` and `¬` are `Bang`.
def prefixKind (text: Text): Tok := if text == "-" then Minus else Bang

--| Every token's kind, commas included, in order. Brackets are the kinds the parser reads them as: `(` and `)` for a
--| parenthesis and a tuple, `[` and `]` for a list.
def Expr.kinds: Expr → List Tok
  | Atom kind _ => [kind]
  | Paren _ inner _ => [LParen, ..inner.kinds ++ [RParen]]
  | Tuple _ items trailing _ => [LParen, ..itemsKinds RParen trailing items]
  | ListOf _ items trailing _ => [LBracket, ..itemsKinds RBracket trailing items]
  | App head arguments => head.kinds ++ argsKinds arguments
  | Infix InfixBinary left operator right => left.kinds ++ [binaryKind operator.text, ..right.kinds]
  | Infix InfixArrow left _ right => left.kinds ++ [Arrow, ..right.kinds]
  | Prefix operator operand => [prefixKind operator.text, ..operand.kinds]
  | _ => []

--| A comma list's items, the commas between them, a last comma if `trailing`, and the closer.
def itemsKinds (close: Tok) (trailing: Bool): List Expr → List Tok
  | [] => [close]
  | [first, ..rest] => first.kinds ++ restKinds close trailing rest

def restKinds (close: Tok) (trailing: Bool): List Expr → List Tok
  | [] => if trailing then [Comma, close] else [close]
  | [next, ..rest] => [Comma, ..next.kinds ++ restKinds close trailing rest]

def argsKinds: List Expr → List Tok
  | [] => []
  | [argument, ..rest] => argument.kinds ++ argsKinds rest

-- The driver's slice is within the grammar.

--| An atom's kind outside the driver's slice is outside the grammar: the two lists of kinds are the same.
theorem Tok.atomFalseOfWord1 ∀ (kind: Tok) (plain: kind.wordWithin1 = False): kind.atom1 = False := match kind with
  | Lower | Upper | Num | Float => plain
  | other => byComputing

--| A name `within1` lets through is one name, as the grammar asks.
theorem textLexesName ∀ (text: Text) (kind: Tok)
    (lexes: textLexesAs text kind = True)
    (name: (kind == Lower || kind == Upper) = True):
    isName1 text = True :=
  match lexed: lex text, lexes with
    | Err message, lexes => (Bool.falseNotTrue lexes).impossible
    | Ok found, lexes =>
      match found.leaves, lexes with
        | [], lexes => (Bool.falseNotTrue lexes).impossible
        | [leaf], lexes =>
          let same: (leaf.token.text == text) = True := Bool.andLeft lexes
          let kindIs: (leaf.token.kind == kind) = True := Bool.andRight lexes
          rewrite same, DecEq.sound kindIs then name
        | [leaf, second, ..more], lexes => (Bool.falseNotTrue lexes).impossible

theorem Word.nameGrammar1 ∀ (word: Word) (within: word.nameWithin1 = True): isName1 word.text = True :=
  match (Bool.orReads _ _).forward within with
    | Inl lower => textLexesName word.text Lower (Bool.andLeft lower) byComputing
    | Inr upper => textLexesName word.text Upper (Bool.andLeft upper) byComputing

--| A tree `within1` lets through is in the grammar: `within1` tests each node as `grammar1` does, and texts too.
theorem Expr.grammarOfWithin1 ∀ (expr: Expr) (within: expr.within1 = True): expr.grammar1 = True := match expr with
  | Atom kind word => Bool.andLeft within
  | Paren open inner close => Expr.grammarOfWithin1 inner within
  | Tuple _ items _ _ | ListOf _ items _ _ => allGrammarOfWithin1 items within
  | App head arguments =>
    Bool.andIntro
      (Expr.grammarOfWithin1 head (Bool.andLeft within))
      (allGrammarOfWithin1 arguments (Bool.andRight within))
  | Infix InfixBinary left _ right | Infix InfixArrow left _ right =>
    Bool.andIntro
      (Expr.grammarOfWithin1 left (Bool.andLeft within))
      (Expr.grammarOfWithin1 right (Bool.andLeft (Bool.andRight within)))
  | Prefix operator operand => Expr.grammarOfWithin1 operand (Bool.andLeft within)

theorem allGrammarOfWithin1 ∀ (exprs: List Expr) (within: allWithin1 exprs = True): allGrammar1 exprs = True :=
  match exprs with
    | [] => byComputing
    | [expr, ..rest] =>
      Bool.andIntro (Expr.grammarOfWithin1 expr (Bool.andLeft within)) (allGrammarOfWithin1 rest (Bool.andRight within))

--| Outside the grammar is outside the driver's slice.
theorem Expr.withinOfGrammarFalse1 ∀ (expr: Expr) (out: expr.grammar1 = False): expr.within1 = False :=
  match within: expr.within1 with
    | False => byComputing
    | True => (Bool.trueNotFalse (rewrite Expr.grammarOfWithin1 expr within at out then out)).impossible

theorem Header.grammarOfWithin1 ∀ (header: Header) (within: header.within1 = True): header.grammar1 = True :=
  match header with
    | {
        exportKeyword,
        opaqueKeyword,
        kind,
        keyword,
        name,
        forallKeyword,
        params,
        colon,
        result,
        decreasingClause,
        unfoldingClause
      } =>
      match exportKeyword, opaqueKeyword, kind, forallKeyword, params, decreasingClause, unfoldingClause, within with
        | None, None, DefPlain, None, [], None, None, within =>
          Bool.andIntro
            (Word.nameGrammar1 name (Bool.andLeft within))
            (Expr.grammarOfWithin1 result (Bool.andRight within))
        | other, others, kinds, foralls, parameters, decreasings, unfoldings, within =>
          (Bool.falseNotTrue within).impossible

theorem Decl.grammarOfWithin1 ∀ (decl: Decl) (within: decl.within1 = True): decl.grammar1 = True := match decl with
  | Definition [] header (Assigned colonEq value) =>
    Bool.andIntro
      (Header.grammarOfWithin1 header (Bool.andLeft within))
      (Expr.grammarOfWithin1 value (Bool.andRight within))

theorem Decl.withinOfGrammarFalse1 ∀ (decl: Decl) (out: decl.grammar1 = False): decl.within1 = False :=
  match within: decl.within1 with
    | False => byComputing
    | True => (Bool.trueNotFalse (rewrite Decl.grammarOfWithin1 decl within at out then out)).impossible
