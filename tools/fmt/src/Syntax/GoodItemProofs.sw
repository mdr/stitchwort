--| `GoodItem` for the items of a source in slice 1 (SW-4018 ticket F, docs/reviews/SW-4018-parser-statements.md §5.1):
--| the parser theorems' `good` hypothesis, from the lexer.
--|
--| Two halves, as D-A chose (`within1` checks a name's or numeral's text, `textSpells1`):
--|
--| - A token of fixed spelling (`def`, a bracket, `:`, an operator) has its kind's text: the lexer's soundness
--|   (`lexFixed`), what a successful `lex` of any source gave.
--| - A name or numeral is spelled plainly (no `.`, no exponent) only if the source says so: `List.map` lexes as one
--|   `Lower` token and `1e3` as a `Float`, both in slice 1's alphabet, and `GoodItem` is false of them. So that half is a
--|   test on the lexed leaves (`spelledPlain1`), the same `textSpells1` that `within1` makes of the tree's words, which
--|   slice 1's driver makes of the source as it tests the alphabet.

namespace Syntax.GoodItemProofs
import Std (Bool, DecEq, Eq, List, Nat, Option, Parse, Result, Text, Void)
import Syntax (..)
import Fmt (..)
import Syntax.Proofs (Spells)
import Syntax.ParseProofs (GoodItem)
import Syntax.SettleProofs (alphabet1, plain1, plainFromOf, settledKeepsTokens, tokens)
import Syntax.SettleBareProofs (tokensBare)
import Syntax.SettleSplitProofs (groupsConcat)
import Fmt.TreeJoinProofs (spellsOfText1)

-- The two tests.

--| A token of fixed spelling has its kind's text (`Spells`); a name, a numeral and a token outside slice 1's alphabet
--| pass.
def fixedSpells1 (kind: Tok) (text: Text): Bool := match kind with
  | KwDef => text == "def"
  | Colon => text == ":"
  | ColonEq => text == ":="
  | LParen => text == "("
  | RParen => text == ")"
  | LBracket => text == "["
  | RBracket => text == "]"
  | Comma => text == ","
  | OrOr => text == "||" || text == "∨"
  | AndAnd => text == "&&" || text == "∧"
  | Equals => text == "="
  | EqEq => text == "=="
  | NotEq => text == "!=" || text == "≠"
  | Lt => text == "<"
  | Le => text == "<=" || text == "≤"
  | Gt => text == ">"
  | Ge => text == ">=" || text == "≥"
  | PlusPlus => text == "++"
  | Plus => text == "+"
  | Minus => text == "-"
  | Star => text == "*"
  | Slash => text == "/"
  | Percent => text == "%"
  | Bang => text == "!" || text == "¬"
  | Arrow => text == "->" || text == "→"
  | _ => True

def Token.fixed1 (token: Token): Bool := fixedSpells1 token.kind token.text

--| A name or numeral is spelled as slice 1 has it (`textSpells1`); every other token passes.
def Token.spelledPlain1 (token: Token): Bool := !token.kind.wordWithin1 || textSpells1 token.kind token.text

--| The source's side of `GoodItem`, for slice 1's driver to test beside `alphabet1`: every name and numeral is
--| spelled plainly.
def spelledPlain1 (leaves: List Leaf): Bool := (tokens leaves).all Token.spelledPlain1

-- From the tests to `GoodItem`.

--| A token of slice 1's alphabet that passes both tests is spelled as its kind is.
theorem spellsOfTests ∀ (kind: Tok) (text: Text)
    (within: kind.within1 = True)
    (plain: (!kind.wordWithin1 || textSpells1 kind text) = True)
    (fixed: fixedSpells1 kind text = True):
    Spells kind text :=
  match kind, within, plain, fixed with
    | Lower, _, plain, _ => spellsOfText1 Lower text plain
    | Upper, _, plain, _ => spellsOfText1 Upper text plain
    | Num, _, plain, _ => spellsOfText1 Num text plain
    | Float, _, plain, _ => spellsOfText1 Float text plain
    | KwDef, _, _, fixed => DecEq.sound fixed
    | Colon, _, _, fixed => DecEq.sound fixed
    | ColonEq, _, _, fixed => DecEq.sound fixed
    | LParen, _, _, fixed => DecEq.sound fixed
    | RParen, _, _, fixed => DecEq.sound fixed
    | LBracket, _, _, fixed => DecEq.sound fixed
    | RBracket, _, _, fixed => DecEq.sound fixed
    | Comma, _, _, fixed => DecEq.sound fixed
    | Equals, _, _, fixed => DecEq.sound fixed
    | EqEq, _, _, fixed => DecEq.sound fixed
    | Lt, _, _, fixed => DecEq.sound fixed
    | Gt, _, _, fixed => DecEq.sound fixed
    | PlusPlus, _, _, fixed => DecEq.sound fixed
    | Plus, _, _, fixed => DecEq.sound fixed
    | Minus, _, _, fixed => DecEq.sound fixed
    | Star, _, _, fixed => DecEq.sound fixed
    | Slash, _, _, fixed => DecEq.sound fixed
    | Percent, _, _, fixed => DecEq.sound fixed
    | OrOr, _, _, fixed => eitherText fixed
    | AndAnd, _, _, fixed => eitherText fixed
    | NotEq, _, _, fixed => eitherText fixed
    | Le, _, _, fixed => eitherText fixed
    | Ge, _, _, fixed => eitherText fixed
    | Bang, _, _, fixed => eitherText fixed
    | Arrow, _, _, fixed => eitherText fixed
    | _, within, _, _ => (Bool.falseNotTrue within).impossible

--| A text that is one of two.
theorem eitherText ∀ [text first second: Text]
    (either: (text == first || text == second) = True):
    text = first ∨ text = second :=
  match (Bool.orReads (text == first) (text == second)).forward either with
    | Inl one => Inl (DecEq.sound one)
    | Inr other => Inr (DecEq.sound other)

--| An item whose token passes both tests is good.
theorem goodOfToken ∀ (item: Item)
    (plain: item.leaf.token.spelledPlain1 = True)
    (fixed: item.leaf.token.fixed1 = True):
    GoodItem item :=
  within => spellsOfTests item.kind item.text within plain fixed

-- From the leaves to the items of each group.

--| Every item stands for its leaf, in order.
theorem itemsAfterAll ∀ (p: Leaf → Prop) (before: Option Token) (index depth lineIndent: Nat) (leaves: List Leaf)
    (all: List.All p leaves):
    List.All (item => p item.leaf) (itemsAfter before index depth lineIndent leaves) :=
  match leaves, all with
    | [], _ => Trivial
    | [leaf, ..rest], (first, later) => (first, itemsAfterAll p _ _ _ _ rest later)

--| What holds of every part of a list's concatenation holds of every part of every list.
theorem allOfConcat ∀ (p: a → Prop) (lists: List (List a))
    (all: List.All p lists.concat):
    List.All (part => List.All p part) lists :=
  match lists with
    | [] => Trivial
    | [first, ..rest] =>
      let split: List.All p (first ++ rest.concat) := all
      (List.allAppendLeft p first rest.concat split, allOfConcat p rest (List.allAppendRight p first rest.concat split))

--| Leaves whose tokens pass both tests give good items in every group.
theorem goodOfTokens ∀ (leaves: List Leaf)
    (plain: (tokens leaves).all Token.spelledPlain1 = True)
    (fixed: (tokens leaves).all Token.fixed1 = True):
    List.All (group => List.All GoodItem (items group)) (groupsOf leaves) :=
  let both: List.All (leaf => leaf.token.spelledPlain1 = True ∧ leaf.token.fixed1 = True) leaves :=
    leavesBoth leaves plain fixed
  let whole: List.All (leaf => leaf.token.spelledPlain1 = True ∧ leaf.token.fixed1 = True) (groupsOf leaves).concat :=
    rewrite groupsConcat leaves then both
  List.allImplies _ _
    (group groupBoth =>
      List.allImplies
        (entry => entry.leaf.token.spelledPlain1 = True ∧ entry.leaf.token.fixed1 = True)
        GoodItem
        (entry both => goodOfToken entry both.left both.right)
        (items group)
        (itemsAfterAll _ None 0 0 0 group groupBoth))
    (groupsOf leaves)
    (allOfConcat _ (groupsOf leaves) whole)

--| Two tests of every leaf's token, as one fact of each leaf.
theorem leavesBoth ∀ (leaves: List Leaf)
    (plain: (tokens leaves).all Token.spelledPlain1 = True)
    (fixed: (tokens leaves).all Token.fixed1 = True):
    List.All (leaf => leaf.token.spelledPlain1 = True ∧ leaf.token.fixed1 = True) leaves :=
  match leaves with
    | [] => Trivial
    | [leaf, ..rest] =>
      ((Bool.andLeft plain, Bool.andLeft fixed), leavesBoth rest (Bool.andRight plain) (Bool.andRight fixed))

-- The lexer's soundness for tokens of fixed spelling.

--| A lexeme of fixed spelling is spelled as its kind is, where it stands in the source.
def lexemeFixed (source: Text) (lexeme: Parse.Located Lexeme): Bool := match lexeme.value with
  | TokenLexeme kind => fixedSpells1 kind (source.slice lexeme.offset (lexeme.offset + lexeme.length))
  | _ => True

--| The lexemes of any source that lexes are spelled as their kinds are.
--|
--| Not yet proved: it is a walk of `lexemesIn` (every lexeme a `located` from the mark it starts at, so its text is the
--| characters it read), which needs `Parse` facts that keep the mark in step with the source (`start.rest =
--| source.toList.drop start.offset`). `Parse.ReadsIn`'s invariant is of the input left alone, and its spec can't name
--| where the run started, so a lexeme's absolute offset can't be tied to the source with it.
theorem lexemesFixed ∀ (source: Text) (found: List (Parse.Located Lexeme))
    (lexes: lexemes source = Ok found):
    found.all (lexemeFixed source) = True :=
  ?

def Assembly.fixed1 (assembly: Assembly): Bool := (tokens assembly.leaves).all Token.fixed1

--| A trailing comment keeps the leaves' tokens.
theorem withTrailingTokens ∀ (leaves: List Leaf) (comment: Comment):
    tokens (withTrailing leaves comment) = tokens leaves :=
  match leaves with
    | [] => byComputing
    | [last, ..earlier] => byComputing

--| Adding a lexeme of fixed spelling keeps every token spelled.
theorem addFixed ∀ (assembly: Assembly) (source: Text) (lexeme: Parse.Located Lexeme)
    (fixed: assembly.fixed1 = True)
    (lexemeOk: lexemeFixed source lexeme = True):
    (assembly.add source lexeme).fixed1 = True :=
  match lexeme with
    | { value = Spaces, offset, length } => fixed
    | { value = LineBreak, offset, length } => fixed
    | { value = CommentLexeme, offset, length } =>
      match assembly.freshLine with
        | True => fixed
        | False => rewrite withTrailingTokens assembly.leaves _ then fixed
    | { value = TokenLexeme kind, offset, length } => Bool.andIntro lexemeOk fixed

--| Folding lexemes of fixed spelling keeps every token spelled.
theorem foldFixed ∀ (source: Text) (lexemes: List (Parse.Located Lexeme)) (assembly: Assembly)
    (fixed: assembly.fixed1 = True)
    (all: lexemes.all (lexemeFixed source) = True):
    (lexemes.foldLeft assembly (done lexeme => done.add source lexeme)).fixed1 = True :=
  match lexemes with
    | [] => fixed
    | [lexeme, ..rest] =>
      foldFixed source rest
        (assembly.add source lexeme)
        (addFixed assembly source lexeme fixed (Bool.andLeft all))
        (Bool.andRight all)

--| `lexFixed`: every token of fixed spelling that `lex` gives has its kind's text.
theorem lexFixed ∀ (source: Text) (lexed: Lexed)
    (lexes: lex source = Ok lexed):
    (tokens lexed.leaves).all Token.fixed1 = True :=
  match found: lexemes source, lexes with
    | Ok lexemesFound, lexes =>
      let done := lexemesFound.foldLeft Assembly.start (assembly lexeme => assembly.add source lexeme)
      let doneFixed: done.fixed1 = True :=
        foldFixed source lexemesFound Assembly.start byComputing (lexemesFixed source lexemesFound found)
      let same: assemble source lexemesFound = lexed := Result.okInjective lexes
      rewrite <- same then reversedFixed done.leaves doneFixed
    | Err _, lexes => (Result.errNotOk lexes).impossible

--| Reversing leaves keeps every token spelled.
theorem reversedFixed ∀ (leaves: List Leaf)
    (fixed: (tokens leaves).all Token.fixed1 = True):
    (tokens leaves.reverse).all Token.fixed1 = True :=
  let each := List.allReverse _ (tokens leaves) (List.allToAll Token.fixed1 (tokens leaves) fixed)
  rewrite List.mapReverse leaves (leaf => leaf.token) then List.allOfAll Token.fixed1 _ each

-- The statement.

--| `GoodItem` for every item of every group of a lexed source, given that its names and numerals are spelled
--| plainly: the `good` of `parseCarries1` and `parseSettled1` on the leaves `lex` gave.
theorem lexGood ∀ (source: Text) (lexed: Lexed)
    (lexes: lex source = Ok lexed)
    (spelled: spelledPlain1 lexed.leaves = True):
    List.All (group => List.All GoodItem (items group)) (groupsOf lexed.leaves) :=
  goodOfTokens lexed.leaves spelled (lexFixed source lexed lexes)

--| Rule N, with the last commas made bare first, keeps every token's kind and text, for `plain` leaves.
theorem settledOnceTokens ∀ (lexed: Lexed)
    (plain: plain1 (tokens lexed.leaves) = True):
    tokens lexed.settledOnce.leaves = tokens lexed.leaves :=
  let bare: Lexed := { lexed | leaves = withBareLastCommas [] lexed.leaves }
  calc tokens lexed.settledOnce.leaves
    _ = tokens bare.leaves := settledKeepsTokens bare
    _ = tokens lexed.leaves := tokensBare lexed.leaves (plainFromOf (tokens lexed.leaves) plain)

--| `GoodItem` for the leaves the formatter parses, `settledOnce` of the lexed source.
theorem settledGood ∀ (source: Text) (lexed: Lexed)
    (lexes: lex source = Ok lexed)
    (spelled: spelledPlain1 lexed.leaves = True)
    (plain: plain1 (tokens lexed.leaves) = True):
    List.All (group => List.All GoodItem (items group)) (groupsOf lexed.settledOnce.leaves) :=
  let same := settledOnceTokens lexed plain
  goodOfTokens lexed.settledOnce.leaves (rewrite same then spelled) (rewrite same then lexFixed source lexed lexes)

-- Where the source's test is needed, and where it passes.

--| A source in slice 1's alphabet whose names or numerals are not all spelled plainly.
def alphabetNotPlain (source: Text): Bool := match lex source with
  | Ok lexed => alphabet1 lexed.leaves && !spelledPlain1 lexed.leaves
  | Err _ => False

--| A qualified name is in the alphabet and fails the test.
theorem qualifiedNotPlain: alphabetNotPlain "def d: A := List.map\n" = True := byComputing

--| So does a number with an exponent.
theorem exponentNotPlain: alphabetNotPlain "def d: A := 1e3\n" = True := byComputing

--| And `GoodItem` is false of the qualified name's item: `Spells Lower` has no `.`.
theorem qualifiedNotSpelled ∀ (spells: Spells Lower "List.map"): Void :=
  let (first, others, chars, _, rest, _) := spells
  let tail: ['i', 's', 't', '.', 'm', 'a', 'p'] = others := Eq.cong ((list: List Char) => list.drop 1) chars
  let stuck: (['i', 's', 't', '.', 'm', 'a', 'p']: List Char).all isWordChar = True := rewrite tail then rest
  Bool.falseNotTrue stuck

--| A source that lexes and passes the test, so `lexGood` applies to it.
def lexesPlain (source: Text): Bool := match lex source with
  | Ok lexed => alphabet1 lexed.leaves && spelledPlain1 lexed.leaves
  | Err _ => False

theorem lexesPlainExample: lexesPlain "def d: A -> (B) := g [a, b] -- end\n\ndef e: C := -1 + f x 2.5\n" = True :=
  byComputing
