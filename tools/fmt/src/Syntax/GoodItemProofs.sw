--| `GoodItem` for the items of a source in slice 1 (SW-4018 ticket F, docs/reviews/SW-4018-parser-statements.md §5.1):
--| the parser theorems' `good` hypothesis, from the lexer.
--|
--| Every token `lex` gives of a source in slice 1's alphabet is spelled as its kind is (`lexFixed`): a token of fixed
--| spelling (`def`, a bracket, `:`, an operator) has its kind's text, and a name or numeral is spelled as slice 1 has
--| it (`textSpells1`: a plain or qualified name, `auto` too, or a numeral with a fraction or an exponent). The walk
--| of the lexer's `item` (`itemFixed`) proves it round by round, joined as in `Syntax.LexReadsProofs`'s `lexemesRounds`
--| (`lexemesFixed`); the words come from what `wordFrom` and `numberFrom` read (`wordFine`, `numberFine`). So `GoodItem`
--| needs nothing of the source beyond the alphabet (`lexGood`), and `spelledPlain1`, the test the driver made of it, is
--| implied (`spelledOfFixedAll`). `textSpellsOfSpells` is the converse of `spellsOfText1`: a name or numeral that
--| `Spells` describes passes `textSpells1`.

namespace Syntax.GoodItemProofs
import Std (Bool, Char, DecEq, Empty, Eq, List, Nat, Option, Pair, Parse, Result, Text, Void)
import Syntax (..)
import Fmt (..)
import Syntax.LexProofs (
  ExponentAs,
  FloatTailAs,
  FractionAs,
  NameKind,
  QualTail,
  Spells,
  letterWordChar,
  qualChars,
  qualFound,
  qualFoundSome,
  qualLast
)
import Syntax.ParseProofs (GoodItem)
import Syntax.SettleProofs (alphabet1, settledWithKeepsTokens, sourcePlain1, tokens)
import Syntax.SettleBareProofs (tokensBare)
import Syntax.SettleSplitProofs (groupsConcat)
import Fmt.TreeJoinProofs (spellsOfText1)
import Syntax.LexLaidProofs (assembleWithin)
import Syntax.LexReadsProofs (..)
import Syntax.SharedFacts (wordStartChar)

-- The two tests.

--| A token of fixed spelling has its kind's text (`Spells`); a name, a numeral and a token outside slice 1's alphabet
--| pass.
def fixedKind1 (kind: Tok) (text: Text): Bool := match kind with
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

--| A token's text is spelled as its kind is: a token of fixed spelling has its kind's text, and a name or numeral is
--| spelled as slice 1 has it (`textSpells1`, which takes `auto`: to the lexer it is a name like any other).
def fixedSpells1 (kind: Tok) (text: Text): Bool := fixedKind1 kind text && (!kind.wordWithin1 || textSpells1 kind text)

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
    (fixed: fixedKind1 kind text = True):
    Spells kind text :=
  match kind, within, plain, fixed with
    | Lower, _, plain, _ => spellsOfText1 Lower text plain
    | Upper, _, plain, _ => spellsOfText1 Upper text plain
    | Num, _, plain, _ => spellsOfText1 Num text plain
    | Float, _, plain, _ => spellsOfText1 Float text plain
    | KwDef |
        Colon |
        ColonEq |
        LParen |
        RParen |
        LBracket |
        RBracket |
        Comma |
        Equals |
        EqEq |
        Lt |
        Gt |
        PlusPlus |
        Plus |
        Minus |
        Star |
        Slash |
        Percent, _, _, fixed => DecEq.sound fixed
    | OrOr | AndAnd | NotEq | Le | Ge | Bang | Arrow, _, _, fixed => Text.eqOfOrBeq fixed
    | _, within, _, _ => (Bool.falseNotTrue within).impossible

--| An item whose token passes both tests is good.
theorem goodOfToken ∀ (item: Item)
    (plain: item.leaf.token.spelledPlain1 = True)
    (fixed: item.leaf.token.fixed1 = True):
    GoodItem item :=
  within => spellsOfTests item.kind item.text within plain (Bool.andLeft fixed)

-- From the leaves to the items of each group.

--| Every item stands for its leaf, in order.
theorem itemsAfterAll ∀ (p: Leaf → Prop) (before: Option Token) (index depth lineIndent: Nat) (leaves: List Leaf)
    (all: List.All p leaves):
    List.All (item => p item.leaf) (itemsAfter before index depth lineIndent leaves) :=
  match leaves, all with
    | [], _ => Trivial
    | [leaf, ..rest], (first, later) => (first, itemsAfterAll p _ _ _ _ rest later)

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
    (List.allOfConcat _ (groupsOf leaves) whole)

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

def Assembly.fixed1 (assembly: Assembly): Bool := (tokens assembly.leaves).all Token.fixed1

--| A trailing comment keeps the leaves' tokens.
theorem withTrailingTokens ∀ (leaves: List Leaf) (comment: Comment):
    tokens (withTrailing leaves comment) = tokens leaves :=
  match leaves with | [] | [_, .._] => byComputing

--| Adding a lexeme of fixed spelling keeps every token spelled.
theorem addFixed ∀ (assembly: Assembly) (source: Text) (lexeme: Parse.Located Lexeme)
    (fixed: assembly.fixed1 = True)
    (lexemeOk: lexemeFixed source lexeme = True):
    (assembly.add source lexeme).fixed1 = True :=
  match lexeme with
    | { value = Spaces, offset, length } | { value = LineBreak, offset, length } => fixed
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
    (lexes: lex source = Ok lexed)
    (alphabet: alphabet1 lexed.leaves = True):
    (tokens lexed.leaves).all Token.fixed1 = True :=
  match found: lexemes source, lexes with
    | Ok lexemesFound, lexes =>
      let same: assemble source lexemesFound = lexed := Result.okInjective lexes
      let within := assembleWithin source lexemesFound (rewrite same then alphabet)
      let done := lexemesFound.foldLeft Assembly.start (assembly lexeme => assembly.add source lexeme)
      let doneFixed: done.fixed1 = True :=
        foldFixed source lexemesFound Assembly.start byComputing (lexemesFixed source lexemesFound found within)
      rewrite <- same then reversedFixed done.leaves doneFixed
    | Err _, lexes => (Result.errNotOk lexes).impossible

--| Reversing leaves keeps every token spelled.
theorem reversedFixed ∀ (leaves: List Leaf)
    (fixed: (tokens leaves).all Token.fixed1 = True):
    (tokens leaves.reverse).all Token.fixed1 = True :=
  let each := List.allReverse _ (tokens leaves) (List.allToAll Token.fixed1 (tokens leaves) fixed)
  rewrite List.mapReverse leaves (leaf => leaf.token) then List.allOfAll Token.fixed1 _ each

-- The statement.

--| A token that passes the lexer's test passes the test of slice 1's spelling: they are the same for a name or numeral.
theorem spelledOfFixed ∀ (token: Token) (fixed: token.fixed1 = True): token.spelledPlain1 = True := Bool.andRight fixed

--| Every token of the leaves is spelled as slice 1 has it, when it is as its kind is.
theorem spelledOfFixedAll ∀ (leaves: List Leaf)
    (fixed: (tokens leaves).all Token.fixed1 = True):
    (tokens leaves).all Token.spelledPlain1 = True :=
  List.allOfAll Token.spelledPlain1 _
    (List.allImplies
      (token => token.fixed1 = True)
      (token => token.spelledPlain1 = True)
      spelledOfFixed
      (tokens leaves)
      (List.allToAll Token.fixed1 (tokens leaves) fixed))

--| `GoodItem` for every item of every group of a lexed source: the `good` of `parseCarries1` and `parseSettled1` on the
--| leaves `lex` gave. A name or numeral the lexer gives is spelled as slice 1 has it, so the source needs no test of
--| its own beside the alphabet (`lexFixed`).
theorem lexGood ∀ (source: Text) (lexed: Lexed)
    (lexes: lex source = Ok lexed)
    (alphabet: alphabet1 lexed.leaves = True):
    List.All (group => List.All GoodItem (items group)) (groupsOf lexed.leaves) :=
  let fixed := lexFixed source lexed lexes alphabet
  goodOfTokens lexed.leaves (spelledOfFixedAll lexed.leaves fixed) fixed

--| Rule N, with the last commas made bare first, keeps every token: the leaves the formatter parses have the lexer's
--| tokens.
theorem settledOnceTokens ∀ (lexed: Lexed): tokens lexed.settledOnce.leaves = tokens lexed.leaves :=
  let bare: Lexed := { lexed | leaves = withBareLastCommas [] lexed.leaves }
  calc tokens lexed.settledOnce.leaves
    _ = tokens bare.leaves := settledWithKeepsTokens bare True
    _ = tokens lexed.leaves := tokensBare lexed.leaves

--| `GoodItem` for the leaves the formatter parses, `settledOnce` of the lexed source. Spelling reads only a token's
--| kind and text, which the move of a last comma keeps.
theorem settledGood ∀ (source: Text) (lexed: Lexed)
    (lexes: lex source = Ok lexed)
    (alphabet: alphabet1 lexed.leaves = True)
    (plain: sourcePlain1 (tokens lexed.leaves) = True):
    List.All (group => List.All GoodItem (items group)) (groupsOf lexed.settledOnce.leaves) :=
  let fixed: (tokens lexed.settledOnce.leaves).all Token.fixed1 = True :=
    rewrite settledOnceTokens lexed then lexFixed source lexed lexes alphabet
  goodOfTokens lexed.settledOnce.leaves (spelledOfFixedAll lexed.settledOnce.leaves fixed) fixed

-- Where the source's test is needed, and where it passes.

--| A source that lexes and passes the test, so `lexGood` applies to it.
def lexesPlain (source: Text): Bool := match lex source with
  | Ok lexed => alphabet1 lexed.leaves && spelledPlain1 lexed.leaves
  | Err _ => False

theorem lexesPlainExample: lexesPlain "def d: A -> (B) := g [a, b] -- end\n\ndef e: C := -1 + f x 2.5\n" = True :=
  byComputing

-- What the lexer's choices of kind say of the text, for the walk of `lexemesIn` (`lexemesFixed`).

--| A Unicode character the lexer reads as a token of fixed spelling is that token's text.
theorem unicodeFixed ∀ (char: Char) (kind: Tok)
    (alias: Tok.unicodeAlias char = Some kind):
    fixedSpells1 kind (Text.fromList [char]) = True :=
  cases

theorem unicodeFixedExample: fixedSpells1 Arrow (Text.fromList ['→']) = True := unicodeFixed '→' Arrow byComputing

--| A mark in step with the source: what is left is the source from the mark's offset. `Parse.ReadsIn` can't say this
--| (its invariant is of the input left alone), so a lexeme's offset couldn't be tied to the source with it.
def InStep (chars: List Char) (at: Parse.Mark Char): Prop := at.rest = chars.drop at.offset

-- Reading from one mark, where the offsets are needed.

--| [`Parse.readsAtThen`], with the mark the rest starts at moved on by what was read.
theorem readsAtThenMoved ∀ [start: Parse.Mark Char] [p: () → {Parse Char} a] [j: a → {Parse Char} b]
    [first: List Char → a → Prop] [spec: List Char → b → Prop]
    (readsFirst: Parse.ReadsAt start p first)
    (rest: ∀ (read: List Char) (v: a) (after: Parse.Mark Char) => start.rest = read ++ after.rest
      → after.offset = start.offset + read.length
      → first read v
      → Parse.ReadsAt after (() => j v) (taken w => spec (read ++ taken) w)):
    Parse.ReadsAt start (() => j (p())) spec :=
  total state value after here honest h =>
    match Parse.runFromThenOk2 p state j _ _ h with
      | Witness v (Witness middle (Both ran restRun)) =>
        match readsFirst total state v middle.at here honest ran with
          | Witness firstRead (Both starts1 (Both honest1 holds1)) =>
            match rest firstRead v middle.at starts1
              (Parse.honestMoved honest honest1 starts1)
              holds1
              total
              middle
              value
              after
              byComputing
              honest1
              restRun with
              | Witness nextRead (Both starts2 (Both honest2 holds2)) =>
                Witness
                  (firstRead ++ nextRead)
                  (Both
                    (rewrite starts1, starts2, List.appendAssoc firstRead nextRead after.rest)
                    (Both honest2 holds2))

--| A lexeme from a mark in step, to where reading `read` took it, is `read` in the source.
theorem sliceRead ∀ (source: Text) (start after: Parse.Mark Char) (read: List Char)
    (step: InStep source.toList start)
    (moved: after.offset = start.offset + read.length):
    source.slice start.offset (start.offset + (after.offset - start.offset))
      = Text.fromList (start.rest.take read.length) :=
  let length: start.offset + (after.offset - start.offset) - start.offset = read.length := arithmetic [moved]
  calc source.slice start.offset (start.offset + (after.offset - start.offset))
    _ = Text.fromList
        ((source.toList.drop start.offset).take (start.offset + (after.offset - start.offset) - start.offset)) :=
      byComputing
    _ = Text.fromList (start.rest.take read.length) := rewrite length, <- step

--| `tokenOf kind count`, from a mark in step with the source, gives a lexeme of `kind` whose text in the source is
--| the first `count` characters left.
theorem tokenOfText ∀ (source: Text) (kind: Tok) (count: Nat) (start: Parse.Mark Char)
    (step: InStep source.toList start):
    Parse.ReadsAt start (() => tokenOf kind count) (read lexeme =>
      lexeme.value = TokenLexeme kind
        ∧ source.slice lexeme.offset (lexeme.offset + lexeme.length) = Text.fromList (start.rest.take count)) :=
  Parse.readsAtMark
    (from =>
      let skipped := skip count
      located (TokenLexeme kind) from) _
    start
    (readsAtThenMoved (atSkip count start) (read u after starts moved taken =>
      Parse.readsAtMark
        (to => { value = TokenLexeme kind, offset = start.offset, length = to.offset - start.offset }) _
        after
        (Parse.readsAtDone after _
          (Both byComputing
            (rewrite sliceRead source start after read step moved, taken, List.takeOwnLength start.rest count)))))

--| `symbol`'s choice, tested: a token of fixed spelling is its text.
def symbolFixed1 (input: List Char): Bool := match symbol input with
  | Some (kind, count) => fixedSpells1 kind (Text.fromList (input.take count))
  | None => True

--| `symbol`'s choice is spelled as its kind is: by the same match as `symbol`'s, so each arm computes.
theorem symbolFixed ∀ (input: List Char): symbolFixed1 input = True := match input with
  | ['(', .._] |
      [')', .._] |
      ['[', .._] |
      [']', .._] |
      ['{', .._] |
      ['}', .._] |
      [',', .._] |
      [';', .._] |
      [':', '=', .._] |
      [':', .._] |
      ['=', '=', .._] |
      ['=', '>', .._] |
      ['=', .._] |
      ['|', '|', .._] |
      ['|', '>', .._] |
      ['|', .._] |
      ['&', '&', .._] |
      ['+', '+', .._] |
      ['+', .._] |
      ['-', '>', .._] |
      ['-', .._] |
      ['*', .._] |
      ['/', .._] |
      ['%', .._] |
      ['!', '=', .._] => byComputing
  | ['!', 'i', 'n', next, .._] if !isWordChar next => cases
  | ['!', 'i', 'n'] => byComputing
  | ['!', .._] => cases
  | ['<', '-', '>', .._] |
      ['<', '=', .._] |
      ['<', .._] |
      ['>', '=', .._] |
      ['>', .._] |
      ['?', .._] |
      ['@', '[', .._] |
      [_, .._] |
      [] => byComputing

--| A word is `def` when the lexer says so: by the same match as `wordKind`'s and `Tok.keyword`'s, so each arm computes.
theorem wordKindFixed ∀ (afterDot: Bool) (word: Text): fixedKind1 (wordKind afterDot word) word = True :=
  match word with
    | "_" |
        "Type" |
        "Prop" |
        "ability" |
        "algebra" |
        "arithmetic" |
        "byWalking" |
        "calc" |
        "cases" |
        "decreasing" |
        "def" |
        "else" => byComputing
    | "exists" => cases
    | "export" => byComputing
    | "forall" => cases
    | "handle" |
        "if" |
        "import" |
        "in" |
        "include" |
        "instance" |
        "interface" |
        "let" |
        "match" |
        "namespace" |
        "opaque" |
        "return" |
        "rewrite" |
        "test" |
        "then" |
        "theorem" |
        "type" |
        "unfolding" |
        "where" |
        "with" => byComputing
    | _ => cases

-- The lexer's parts whose values are not in question: each succeeds only having read a start of its input.

--| `located value from`, read at `start`, is the lexeme from `from` to `start`.
theorem readsAtLocated ∀ (value: Lexeme) (from start: Parse.Mark Char):
    Parse.ReadsAt start (() => located value from) (read lexeme =>
      lexeme = { value, offset = from.offset, length = start.offset - from.offset }) :=
  Parse.readsAtMark
    (to => { value, offset = from.offset, length = to.offset - from.offset }) _
    start
    (Parse.readsAtDone start _ byComputing)

--| A name's word characters go on in `qualScan1` without changing what it has.
theorem qualScanWord ∀ (upper last: Bool) (word rest: List Char)
    (all: word.all isWordChar = True):
    qualScan1 upper last (word ++ rest) = qualScan1 upper last rest :=
  match word with
    | [] => byComputing
    | [char, ..more] =>
      let first: isWordChar char = True := Bool.andLeft all
      rewrite first then qualScanWord upper last more rest (Bool.andRight all)

theorem wordWithinCases ∀ (kind: Tok):
    kind.wordWithin1 = False ∨ kind = Lower ∨ kind = Upper ∨ kind = Num ∨ kind = Float :=
  match kind with
    | Lower => Inr (Inl byComputing)
    | Upper => Inr (Inr (Inl byComputing))
    | Num => Inr (Inr (Inr (Inl byComputing)))
    | Float => Inr (Inr (Inr (Inr byComputing)))
    | _ => Inl byComputing

--| What `qualified` read: nothing, giving what was found before; or a `.` and what follows it, which `qualScan1`
--| scans to what it gave.
def QualScanned (upper: Bool) (found: Option Bool) (read: List Char) (value: Option Bool): Prop :=
  (read = [] ∧ value = found)
    ∨ ((∃ (rest: List Char) => read = ['.', ..rest]) ∧ qualScan1 upper upper read = value ∧ value.isSome = True)

theorem readsAtQualified ∀ (fuel: Nat) (upper: Bool) (found: Option Bool) (start: Parse.Mark Char):
    Parse.ReadsAt start (() => qualified fuel upper found) (QualScanned upper found) :=
  match fuel with
    | Zero => Parse.readsAtDone start found (Inl (Both byComputing byComputing))
    | Succ more =>
      Parse.readsAtMark
        (at => qualifiedOn more upper found at.rest) _
        start
        (readsAtQualifiedOn more upper found start start.rest byComputing)

theorem readsAtQualifiedOn ∀ (more: Nat) (upper: Bool) (found: Option Bool) (start: Parse.Mark Char) (input: List Char)
    (here: start.rest = input):
    Parse.ReadsAt start (() => qualifiedOn more upper found input) (QualScanned upper found) :=
  match input with
    | ['.', next, ..rest] =>
      match guard: upper && next.isAsciiLetter with
        | False => Parse.readsAtDone start found (Inl (Both byComputing byComputing))
        | True =>
          let letter: next.isAsciiLetter = True := Bool.andRight guard
          let isUpper: upper = True := Bool.andLeft guard
          readsAtThenMoved (atSkip 1 start) (read1 u after1 starts1 moved1 took1 =>
            readsAtThenMoved (Parse.readsAtSpan after1 isWordChar) (read2 name after2 starts2 moved2 spanned2 =>
              Parse.readsAtWeaken
                (readsAtQualified more next.isAsciiUppercase (Some next.isAsciiUppercase) after2)
                (taken v q =>
                  let isSome: v.isSome = True := match q with
                    | Inl (none, same) => rewrite same
                    | Inr (_, _, some) => some
                  let r1: read1 = ['.'] := rewrite here at took1 then took1
                  let rest1: after1.rest = [next, ..rest] :=
                    (List.consInjective '.'
                      [next, ..rest]
                      after1.rest
                      (rewrite r1, here at starts1 then starts1)).flipped
                  let r2: read2 = [next, ..rest.takeWhile isWordChar] :=
                    rewrite spanned2.left, spanned2.right, rest1, letterWordChar next letter
                  let allWord: (rest.takeWhile isWordChar).all isWordChar = True := List.allTakeWhile isWordChar rest
                  let scan: qualScan1 upper upper (read1 ++ (read2 ++ taken))
                    = qualScan1 next.isAsciiUppercase next.isAsciiUppercase taken :=
                    rewrite r1, r2, isUpper, letter then
                      qualScanWord next.isAsciiUppercase next.isAsciiUppercase (rest.takeWhile isWordChar) taken allWord
                  let ended: qualScan1 next.isAsciiUppercase next.isAsciiUppercase taken = v := match q with
                    | Inl (none, same) => rewrite none, same
                    | Inr (_, scanned, _) => scanned
                  Inr (Both (Witness (read2 ++ taken) (rewrite r1)) (Both (Eq.trans scan ended) isSome)))))
    | _ => Parse.readsAtDone start found (Inl (Both byComputing byComputing))

--| Num and Float.
def Tok.isNumeral: Tok → Bool
  | Num | Float => True
  | _ => False

theorem wordKindNotNumeral ∀ (afterDot: Bool) (word: Text): (wordKind afterDot word).isNumeral = False :=
  match word with
    | "_" |
        "Type" |
        "Prop" |
        "ability" |
        "algebra" |
        "arithmetic" |
        "byWalking" |
        "calc" |
        "cases" |
        "decreasing" |
        "def" |
        "else" => byComputing
    | "exists" => cases
    | "export" => byComputing
    | "forall" => cases
    | "handle" |
        "if" |
        "import" |
        "in" |
        "include" |
        "instance" |
        "interface" |
        "let" |
        "match" |
        "namespace" |
        "opaque" |
        "return" |
        "rewrite" |
        "test" |
        "then" |
        "theorem" |
        "type" |
        "unfolding" |
        "where" |
        "with" => byComputing
    | _ => cases

--| What a word's kind is, after the word characters `first`: what `wordKind` makes of them when nothing more is read; or,
--| after a qualified name's components, a name's, as the components scan.
def KindScanned (first read: List Char) (kind: Tok): Prop :=
  (read = [] ∧ kind = wordKind False (Text.fromList first))
    ∨ (((∃ (rest: List Char) => read = ['.', ..rest])
      ∧ qualScan1
        (first.head.map (char => char.isAsciiUppercase) |> .getOrElse False)
        (first.head.map (char => char.isAsciiUppercase) |> .getOrElse False)
        read
        = Some (kind == Upper))
      ∧ (kind = Upper ∨ kind = Lower))

--| A word and what follows it that the lexer read as one token is spelled as its kind is.
theorem wordTextSpelled ∀ (c: Char) (word read: List Char) (kind: Tok)
    (starts: isWordStart c = True)
    (all: word.all isWordChar = True)
    (kinded: KindScanned [c, ..word] read kind):
    fixedSpells1 kind (Text.fromList ([c, ..word] ++ read)) = True :=
  match kinded with
    | Inl (none, kindIs) =>
      let same: Text.fromList ([c, ..word] ++ read) = Text.fromList [c, ..word] := rewrite none, List.appendNil word
      rewrite same then
        Bool.andIntro
          (rewrite kindIs then wordKindFixed False (Text.fromList [c, ..word]))
          (match wordWithinCases kind with
            | Inl notWord => rewrite notWord
            | Inr (Inl lower) =>
              let named: wordKind False (Text.fromList [c, ..word]) = Lower := Eq.trans kindIs.flipped lower
              rewrite lower then Bool.andIntro starts (rewrite all, named then DecEq.refl Lower)
            | Inr (Inr (Inl upper)) =>
              let named: wordKind False (Text.fromList [c, ..word]) = Upper := Eq.trans kindIs.flipped upper
              rewrite upper then Bool.andIntro starts (rewrite all, named then DecEq.refl Upper)
            | Inr (Inr (Inr (Inl num))) =>
              let numeral: (wordKind False (Text.fromList [c, ..word])).isNumeral = True := rewrite <- kindIs, num
              (Bool.falseNotTrue
                (Eq.trans (wordKindNotNumeral False (Text.fromList [c, ..word])).flipped numeral)).impossible
            | Inr (Inr (Inr (Inr float))) =>
              let numeral: (wordKind False (Text.fromList [c, ..word])).isNumeral = True := rewrite <- kindIs, float
              (Bool.falseNotTrue
                (Eq.trans (wordKindNotNumeral False (Text.fromList [c, ..word])).flipped numeral)).impossible)
    | Inr (Both (Both (Witness rest isDot) scanned) which) =>
      let notAll: (word ++ read).all isWordChar = False := rewrite List.allAppendAnd word read isWordChar, all, isDot
      let scan: qualScan1 c.isAsciiUppercase c.isAsciiUppercase (word ++ read) = Some (kind == Upper) :=
        rewrite qualScanWord c.isAsciiUppercase c.isAsciiUppercase word read all then scanned
      match which with
        | Inl upper =>
          rewrite upper at scan then
            let spelled: textSpells1 Upper (Text.fromList ([c, ..word] ++ read)) = True :=
              Bool.andIntro starts (rewrite notAll, scan)
            rewrite upper then Bool.andIntro byComputing spelled
        | Inr lower =>
          rewrite lower at scan then
            let spelled: textSpells1 Lower (Text.fromList ([c, ..word] ++ read)) = True :=
              Bool.andIntro starts (rewrite notAll, scan)
            rewrite lower then Bool.andIntro byComputing spelled

--| A word, from a mark in step, is spelled as its kind is: a name, or `def` only if its text is `def`
--| (`wordKindFixed`).
--|
--| Proof idea: the lexeme's text is the characters the word read (`sliceRead`): the `span` of word characters and what
--| the qualified name's components read after it. With no components the kind is `wordKind`'s of the characters; with
--| some it is the last component's case, as `qualScan1` scans them (`wordTextSpelled`).
theorem wordFine ∀ (source: Text) (from: Parse.Mark Char) (c: Char) (more: List Char)
    (step: InStep source.toList from)
    (here: from.rest = [c, ..more])
    (starts: isWordStart c = True):
    Parse.ReadsAt from (() => wordFrom False from) (read lexeme => lexemeFixed source lexeme = True) :=
  readsAtThenMoved (Parse.readsAtSpan from isWordChar) (read1 first after1 starts1 moved1 spanned =>
    let upper := first.head.map (char => char.isAsciiUppercase) |> .getOrElse False
    readsAtThenMoved
      [p := () =>
        match qualified (from.left + 1) upper None with
          | Some lastUpper => if lastUpper then Upper else Lower
          | None => wordKind False (Text.fromList first)]
      [j := kind => located (TokenLexeme kind) from]
      [spec := read lexeme => lexemeFixed source lexeme = True]
      (readsAtThenMoved
        [spec := KindScanned first]
        (readsAtQualified (from.left + 1) upper None after1)
        (read2 found after2 starts2 moved2 q =>
          match found, q with
            | Some last, Inl (_, same) => (Option.someNotNone last same).impossible
            | Some last, Inr (Both (Witness rest isDot) (Both scanned some)) =>
              let dotted: ∃ (more: List Char) => read2 ++ [] = ['.', ..more] :=
                Witness rest (rewrite List.appendNil read2, isDot)
              let scan: qualScan1 upper upper (read2 ++ []) = Some last := rewrite List.appendNil read2 then scanned
              match last with
                | True =>
                  Parse.readsAtDone after2 Upper
                    [spec := (taken kind => KindScanned first (read2 ++ taken) kind)]
                    (Inr (Both (Both dotted (rewrite scan)) (Inl byComputing)))
                | False =>
                  Parse.readsAtDone after2 Lower
                    [spec := (taken kind => KindScanned first (read2 ++ taken) kind)]
                    (Inr (Both (Both dotted (rewrite scan)) (Inr byComputing)))
            | None, Inr (_, _, some) => (Bool.falseNotTrue some).impossible
            | None, Inl (none, same) =>
              Parse.readsAtDone after2
                (wordKind False (Text.fromList first))
                [spec := (taken kind => KindScanned first (read2 ++ taken) kind)]
                (Inl (Both (rewrite none) byComputing))))
      (readKind kind after3 starts3 moved3 kindRead =>
        Parse.readsAtWeaken (readsAtLocated (TokenLexeme kind) from after3) (taken lexeme same =>
          match spanned with
            | Both isFirst firstIs =>
              let head: read1 = [c, ..more.takeWhile isWordChar] :=
                rewrite isFirst, firstIs then
                  List.takeWhileConsOf isWordChar from.rest c more here (wordStartChar c starts)
              let firstHead: first = [c, ..more.takeWhile isWordChar] := rewrite <- isFirst then head
              let moved: after3.offset = from.offset + (read1 ++ readKind).length :=
                arithmetic [moved1, moved3, List.lengthAppend read1 readKind]
              let whole: from.rest = (read1 ++ readKind) ++ after3.rest :=
                rewrite starts1, starts3, List.appendAssoc read1 readKind after3.rest
              let text: Text.fromList (from.rest.take (read1 ++ readKind).length) = Text.fromList (read1 ++ readKind) :=
                rewrite whole, List.takeAppend (read1 ++ readKind) after3.rest
              rewrite same, sliceRead source from after3 (read1 ++ readKind) step moved, text, head then
                wordTextSpelled c
                  (more.takeWhile isWordChar)
                  readKind
                  kind
                  starts
                  (List.allTakeWhile isWordChar more)
                  (rewrite firstHead at kindRead then kindRead))))

--| A fraction's characters are a `.`, a digit and digits.
theorem fractionAheadShape ∀ (input: List Char)
    (ahead: fractionAhead input = True):
    ∃ (next: Char) (more: List Char) => input = ['.', next, ..more] ∧ next.isAsciiDigit = True :=
  match input with | ['.', next, ..more] => Witness next (Witness more (Both byComputing ahead))

--| What `exponentSkip` found: the marker `e` or `E` and a digit (one character to skip), or the marker, a sign and a
--| digit (two).
def ExponentShape (input: List Char) (count: Nat): Prop :=
  (∃ (marker next: Char) (rest: List Char) => input = [marker, next, ..rest]
    ∧ (marker == 'e' || marker == 'E') = True
    ∧ next.isAsciiDigit = True
    ∧ count = 1)
    ∨ (∃ (marker sign next: Char) (rest: List Char) => input = [marker, sign, next, ..rest]
      ∧ (marker == 'e' || marker == 'E') = True
      ∧ (sign == '+' || sign == '-') = True
      ∧ next.isAsciiDigit = True
      ∧ count = 2)

theorem exponentSkipShape ∀ (input: List Char) (count: Nat)
    (found: exponentSkip input = Some count):
    ExponentShape input count :=
  match input with
    | [e, sign, next, ..rest] =>
      match lead: (e == 'e' || e == 'E') with
        | True =>
          match signed: (sign == '+' || sign == '-') with
            | False =>
              match first: sign.isAsciiDigit with
                | True =>
                  let one: count = 1 := (Option.someInjective found).flipped
                  Inl
                    (Witness e (Witness sign (Witness [next, ..rest] (Both byComputing (Both lead (Both first one))))))
            | True =>
              match digit: next.isAsciiDigit with
                | True =>
                  let two: count = 2 := (Option.someInjective found).flipped
                  Inr
                    (Witness e
                      (Witness sign
                        (Witness next (Witness rest (Both byComputing (Both lead (Both signed (Both digit two))))))))
                | False => cases
    | [e, next, ..rest] =>
      match lead: (e == 'e' || e == 'E') with
        | True =>
          match digit: next.isAsciiDigit with
            | True =>
              let one: count = 1 := (Option.someInjective found).flipped
              Inl (Witness e (Witness next (Witness rest (Both byComputing (Both lead (Both digit one))))))

--| What a number's fraction read: nothing, giving `False`; or a `.`, a digit and digits, giving `True`.
def FractionRead (read: List Char) (found: Bool): Prop :=
  (read = [] ∧ found = False)
    ∨ (found = True
      ∧ ∃ (digit: Char) (digits: List Char) => read = ['.', digit, ..digits]
        ∧ digit.isAsciiDigit = True
        ∧ digits.all Char.isAsciiDigit = True)

--| What a number's exponent read: nothing, giving `False`; or an exponent as slice 1 spells one, giving `True`.
def ExponentRead (read: List Char) (found: Bool): Prop :=
  (read = [] ∧ found = False) ∨ (found = True ∧ exponentText1 read = True)

theorem readsAtFraction ∀ (at: Parse.Mark Char): Parse.ReadsAt at (() => fractionFrom at) FractionRead :=
  match ahead: fractionAhead at.rest with
    | True =>
      let found := fractionAheadShape at.rest ahead
      match found with
        | Witness next (Witness more (Both shape digit)) =>
          readsAtThenMoved
            [p := () => skip 1]
            [spec := FractionRead]
            (atSkip 1 at)
            (read1 u after1 starts1 moved1 took1 =>
              readsAtThenMoved
                (Parse.readsAtSpan after1 Char.isAsciiDigit)
                (read2 decimals after2 starts2 moved2 spanned2 =>
                  let r1: read1 = ['.'] := rewrite shape at took1 then took1
                  let rest1: after1.rest = [next, ..more] :=
                    (List.consInjective '.'
                      [next, ..more]
                      after1.rest
                      (rewrite r1, shape at starts1 then starts1)).flipped
                  let r2: read2 = [next, ..more.takeWhile Char.isAsciiDigit] :=
                    rewrite spanned2.left, spanned2.right, rest1, digit
                  Parse.readsAtDone after2 True
                    (Inr
                      (Both byComputing
                        (Witness next
                          (Witness
                            (more.takeWhile Char.isAsciiDigit)
                            (Both
                              (rewrite r1, r2, List.appendNil (more.takeWhile Char.isAsciiDigit))
                              (Both digit (List.allTakeWhile Char.isAsciiDigit more)))))))))
    | False => Parse.readsAtDone at False (Inl (Both byComputing byComputing))

theorem readsAtExponent ∀ (at: Parse.Mark Char): Parse.ReadsAt at (() => exponentFrom at) ExponentRead :=
  match e: exponentSkip at.rest with
    | Some count =>
      let found := exponentSkipShape at.rest count e
      readsAtThenMoved (atSkip count at) (read1 u after1 starts1 moved1 took1 =>
        readsAtThenMoved (Parse.readsAtSpan after1 Char.isAsciiDigit) (read2 power after2 starts2 moved2 spanned2 =>
          match found with
            | Inl (Witness marker (Witness next (Witness rest (Both shape (Both lead (Both digit one)))))) =>
              let r1: read1 = [marker] := rewrite shape, one at took1 then took1
              let rest1: after1.rest = [next, ..rest] :=
                (List.consInjective marker
                  [next, ..rest]
                  after1.rest
                  (rewrite r1, shape at starts1 then starts1)).flipped
              let r2: read2 = [next, ..rest.takeWhile Char.isAsciiDigit] :=
                rewrite spanned2.left, spanned2.right, rest1, digit
              let text: exponentText1 (read1 ++ (read2 ++ [])) = True :=
                rewrite r1,
                    r2,
                    List.appendNil [next, ..rest.takeWhile Char.isAsciiDigit],
                    Char.beqFalseOfDigit next '+' digit byComputing,
                    Char.beqFalseOfDigit next '-' digit byComputing then
                  Bool.andIntro lead (Bool.andIntro digit (List.allTakeWhile Char.isAsciiDigit rest))
              Parse.readsAtDone after2 True (Inr (Both byComputing text))
            | Inr
                (Witness marker
                  (Witness sign
                    (Witness next (Witness rest (Both shape (Both lead (Both signed (Both digit two)))))))) =>
              let r1: read1 = [marker, sign] := rewrite shape, two at took1 then took1
              let rest1: after1.rest = [next, ..rest] :=
                (List.consInjective sign
                  [next, ..rest]
                  after1.rest
                  (List.consInjective marker
                    [sign, next, ..rest]
                    [sign, ..after1.rest]
                    (rewrite r1, shape at starts1 then starts1))).flipped
              let r2: read2 = [next, ..rest.takeWhile Char.isAsciiDigit] :=
                rewrite spanned2.left, spanned2.right, rest1, digit
              let text: exponentText1 (read1 ++ (read2 ++ [])) = True :=
                rewrite r1, r2, List.appendNil [next, ..rest.takeWhile Char.isAsciiDigit], signed then
                  Bool.andIntro lead (Bool.andIntro digit (List.allTakeWhile Char.isAsciiDigit rest))
              Parse.readsAtDone after2 True (Inr (Both byComputing text))))
    | None => Parse.readsAtDone at False (Inl (Both byComputing byComputing))

--| What a number's fraction and exponent read: nothing, giving `False`; or what follows the digits as slice 1's
--| `floatRest1` takes it, giving `True`.
def NumberTail (read: List Char) (float: Bool): Prop :=
  (read = [] ∧ float = False)
    ∨ (float = True ∧ ∀ (digits: List Char) => digits.all Char.isAsciiDigit = True → floatRest1 (digits ++ read) = True)

theorem floatRestSkip ∀ (digits rest: List Char)
    (all: digits.all Char.isAsciiDigit = True):
    floatRest1 (digits ++ rest) = floatRest1 rest :=
  match digits with
    | [] => byComputing
    | [char, ..more] =>
      let first: char.isAsciiDigit = True := Bool.andLeft all
      rewrite first then floatRestSkip more rest (Bool.andRight all)

theorem fractionRestSkip ∀ (digits rest: List Char)
    (all: digits.all Char.isAsciiDigit = True):
    fractionRest1 (digits ++ rest) = fractionRest1 rest :=
  match digits with
    | [] => byComputing
    | [char, ..more] =>
      let first: char.isAsciiDigit = True := Bool.andLeft all
      rewrite first then fractionRestSkip more rest (Bool.andRight all)

theorem markerNotDigit ∀ (marker: Char) (lead: (marker == 'e' || marker == 'E') = True): marker.isAsciiDigit = False :=
  cases

theorem markerNotDot ∀ (marker: Char) (lead: (marker == 'e' || marker == 'E') = True): (marker == '.') = False := cases

--| An exponent that slice 1 spells is what a float's rest, or a fraction's rest, goes on with.
theorem exponentRest ∀ (exponent: List Char)
    (spelled: exponentText1 exponent = True):
    floatRest1 exponent = True ∧ fractionRest1 exponent = True :=
  match exponent with
    | [marker, ..more] =>
      let lead: (marker == 'e' || marker == 'E') = True := Bool.andLeft spelled
      rewrite markerNotDigit marker lead, markerNotDot marker lead then (spelled, spelled)

theorem readsAtNumberTail ∀ (start: Parse.Mark Char): Parse.ReadsAt start (() => numberTail False) NumberTail :=
  readsAtThenMoved
    (Parse.readsAtMark fractionFrom _ start (readsAtFraction start))
    (readF fraction after1 starts1 moved1 fractionRead =>
      readsAtThenMoved
        (Parse.readsAtMark exponentFrom _ after1 (readsAtExponent after1))
        (readE exponent after2 starts2 moved2 exponentRead =>
          match fractionRead, exponentRead with
            | Inl (noFraction, isFalse), Inl (noExponent, exponentFalse) =>
              Parse.readsAtDone after2
                (fraction || exponent)
                (Inl (Both (rewrite noFraction, noExponent) (rewrite isFalse, exponentFalse)))
            | Inl (noFraction, isFalse), Inr (exponentTrue, spelled) =>
              Parse.readsAtDone after2
                (fraction || exponent)
                (Inr
                  (Both (rewrite isFalse, exponentTrue) (digits all =>
                    rewrite noFraction, List.appendNil readE, floatRestSkip digits readE all then
                      (exponentRest readE spelled).left)))
            | Inr (isTrue, Witness digit (Witness more (Both shape (Both first allMore)))), Inl
                (noExponent, exponentFalse) =>
              Parse.readsAtDone after2
                (fraction || exponent)
                (Inr
                  (Both (rewrite isTrue) (digits all =>
                    rewrite shape, noExponent then
                      Eq.trans
                        (floatRestSkip digits _ all)
                        (Bool.andIntro first (Eq.trans (fractionRestSkip more _ allMore) byComputing)))))
            | Inr (isTrue, Witness digit (Witness more (Both shape (Both first allMore)))), Inr
                (exponentTrue, spelled) =>
              Parse.readsAtDone after2
                (fraction || exponent)
                (Inr
                  (Both (rewrite isTrue) (digits all =>
                    rewrite shape then
                      Eq.trans
                        (floatRestSkip digits _ all)
                        (Bool.andIntro first
                          (Eq.trans
                            (fractionRestSkip more _ allMore)
                            (rewrite List.appendNil readE then (exponentRest readE spelled).right))))))))

--| A number, from a mark in step, is spelled as its kind is: digits for a `Num`, and for a `Float` digits followed by
--| a fraction, an exponent or both (`floatText1`).
theorem numberFine ∀ (source: Text) (from: Parse.Mark Char) (c: Char) (more: List Char)
    (step: InStep source.toList from)
    (here: from.rest = [c, ..more])
    (digit: c.isAsciiDigit = True):
    Parse.ReadsAt from (() => numberFrom False from) (read lexeme => lexemeFixed source lexeme = True) :=
  readsAtThenMoved (Parse.readsAtSpan from Char.isAsciiDigit) (read1 digits after1 starts1 moved1 spanned =>
    readsAtThenMoved (readsAtNumberTail after1) (readT float after2 starts2 moved2 tail =>
      Parse.readsAtWeaken
        (readsAtLocated (TokenLexeme (if float then Float else Num)) from after2)
        (taken lexeme same =>
          match spanned with
            | Both isDigits digitsAre =>
              let head: read1 = [c, ..more.takeWhile Char.isAsciiDigit] :=
                rewrite isDigits, digitsAre then List.takeWhileConsOf Char.isAsciiDigit from.rest c more here digit
              let moved: after2.offset = from.offset + (read1 ++ readT).length :=
                arithmetic [moved1, moved2, List.lengthAppend read1 readT]
              let whole: from.rest = (read1 ++ readT) ++ after2.rest :=
                rewrite starts1, starts2, List.appendAssoc read1 readT after2.rest
              let text: Text.fromList (from.rest.take (read1 ++ readT).length) = Text.fromList (read1 ++ readT) :=
                rewrite whole, List.takeAppend (read1 ++ readT) after2.rest
              let allDigits: (more.takeWhile Char.isAsciiDigit).all Char.isAsciiDigit = True :=
                List.allTakeWhile Char.isAsciiDigit more
              rewrite same, sliceRead source from after2 (read1 ++ readT) step moved, text, head then
                match tail with
                  | Inl (none, isFalse) =>
                    rewrite isFalse, none, List.appendNil (more.takeWhile Char.isAsciiDigit) then
                      Bool.andIntro byComputing (Bool.andIntro digit allDigits)
                  | Inr (isTrue, floated) =>
                    rewrite isTrue then Bool.andIntro byComputing (Bool.andIntro digit (floated _ allDigits)))))

-- What a name or numeral that `Spells` describes passes: `Spells` implies `textSpells1`.

--| Scanning a qualified name's components, each after an upper-case one, ends at the last component's case.
theorem qualScanComps ∀ (upper last: Bool) (comps: List (Pair Char (List Char)))
    (tail: QualTail upper comps):
    qualScan1 upper last (qualChars comps) = Some (qualLast last comps) :=
  match comps with
    | [] => byComputing
    | [(letter, word), ..more] =>
      match tail with
        | Both isUpper (Both isLetter (Both allWord rest)) =>
          rewrite isUpper, isLetter then
            Eq.trans
              (qualScanWord letter.isAsciiUppercase letter.isAsciiUppercase word (qualChars more) allWord)
              (qualScanComps letter.isAsciiUppercase letter.isAsciiUppercase more rest)

--| A name that `Spells` describes is spelled as `textSpells1` has names.
theorem nameSpellsText ∀ (kind: Tok) (text: Text) (first: Char)
    (others: List Char) (comps: List (Pair Char (List Char)))
    (same: text.toList = [first, ..others] ++ qualChars comps)
    (starts: isWordStart first = True)
    (all: others.all isWordChar = True)
    (tail: QualTail first.isAsciiUppercase comps)
    (named: NameKind kind text comps):
    nameText1 kind text.toList = True :=
  let same2: text.toList = [first, ..(others ++ qualChars comps)] := same
  let textIs: Text.fromList [first, ..(others ++ qualChars comps)] = text := rewrite <- same2 then Text.fromToList text
  rewrite same2 then
    Bool.andIntro starts
      (match comps with
        | [] =>
          let kinded: wordKind False text = kind := named
          rewrite textIs, List.appendNil others, all, kinded then DecEq.refl kind
        | [(letter, word), ..more] =>
          match named with
            | Witness lastUpper (Both found which) =>
              let notAll: (others ++ qualChars [(letter, word), ..more]).all isWordChar = False :=
                rewrite List.allAppendAnd others (qualChars [(letter, word), ..more]) isWordChar, all
              let scanned: qualScan1 first.isAsciiUppercase first.isAsciiUppercase
                (others ++ qualChars [(letter, word), ..more])
                = Some (qualLast first.isAsciiUppercase [(letter, word), ..more]) :=
                Eq.trans
                  (qualScanWord first.isAsciiUppercase first.isAsciiUppercase others _ all)
                  (qualScanComps first.isAsciiUppercase first.isAsciiUppercase [(letter, word), ..more] tail)
              let lastIs: qualLast first.isAsciiUppercase [(letter, word), ..more] = lastUpper :=
                Option.someInjective (Eq.trans (qualFoundSome letter.isAsciiUppercase more).flipped found)
              rewrite textIs, notAll, scanned, lastIs then
                match lastUpper with
                  | True => rewrite <- which
                  | False => rewrite <- which)

--| A number's exponent that `ExponentAs` describes is spelled as `exponentText1` has it.
theorem exponentOfAs ∀ (exponent: List Char) (shape: ExponentAs exponent): exponentText1 exponent = True :=
  match shape with
    | Inl (Witness marker (Witness digit (Witness digits (Both same (Both lead (Both isDigit all)))))) =>
      rewrite same,
          Char.beqFalseOfDigit digit '+' isDigit byComputing,
          Char.beqFalseOfDigit digit '-' isDigit byComputing then
        Bool.andIntro lead (Bool.andIntro isDigit all)
    | Inr
        (Witness marker
          (Witness sign (Witness digit (Witness digits (Both same (Both lead (Both signed (Both isDigit all)))))))) =>
      rewrite same, signed then Bool.andIntro lead (Bool.andIntro isDigit all)

--| What follows a float's digits, as `FloatTailAs` has it, is what `floatRest1` takes.
theorem floatTailRest ∀ (tail: List Char) (shape: FloatTailAs tail): floatRest1 tail = True := match shape with
  | Inl
      (Witness fraction
        (Witness exponent
          (Both same (Both (Witness second (Witness more (Both isFraction (Both isDigit all)))) exponentShape)))) =>
    rewrite same, isFraction then
      Bool.andIntro isDigit
        (Eq.trans (fractionRestSkip more _ all) (exponentRest exponent (exponentOfAs exponent exponentShape)).right)
  | Inr (Inl (Witness second (Witness more (Both isFraction (Both isDigit all))))) =>
    let skipped := fractionRestSkip more [] all
    rewrite isFraction then Bool.andIntro isDigit (rewrite List.appendNil more at skipped then skipped)
  | Inr (Inr exponentShape) => (exponentRest tail (exponentOfAs tail exponentShape)).left

--| Every name or numeral that `Spells` describes passes `textSpells1`; every other kind passes trivially.
theorem textSpellsOfSpells ∀ (kind: Tok) (text: Text)
    (spells: Spells kind text):
    (!kind.wordWithin1 || textSpells1 kind text) = True :=
  match kind, spells with
    | Lower, Witness first (Witness others (Witness comps (Both same (Both starts (Both all (Both tail named)))))) =>
      nameSpellsText Lower text first others comps same starts all tail named
    | Upper, Witness first (Witness others (Witness comps (Both same (Both starts (Both all (Both tail named)))))) =>
      nameSpellsText Upper text first others comps same starts all tail named
    | Num, Witness first (Witness others (Both same (Both isDigit all))) => rewrite same then Bool.andIntro isDigit all
    | Float, Witness first (Witness others (Witness tail (Both same (Both isDigit (Both all shape))))) =>
      rewrite same then Bool.andIntro isDigit (Eq.trans (floatRestSkip others _ all) (floatTailRest tail shape))
    | _, _ => byComputing

-- The walk of `item`.

--| Every lexeme of a list is spelled as its kind is.
def lexemesFine (source: Text) (values: List (Parse.Located Lexeme)): Bool := values.all (lexemeFixed source)

--| A lexeme that isn't a token.
def Lexeme.free: Lexeme → Bool
  | TokenLexeme _ => False
  | _ => True

--| A lexeme `located` with a value that isn't a token, as a list of one.
theorem oneLocated ∀ (source: Text) (value: Lexeme) (from: Parse.Mark Char)
    (free: value.free = True):
    Parse.Gives Parse.Invariant.any (() => [located value from]) (values => lexemesFine source values = True) :=
  Parse.givesThen (givesLocated value from) (lexeme same =>
    Parse.givesDone
      (Bool.andIntro
        (match value, same, free with
          | TokenLexeme kind, _, free => (Bool.falseNotTrue free).impossible
          | Spaces | LineBreak, same, _ => rewrite same
          | CommentLexeme, same, _ => rewrite same)
        byComputing))

--| A round that gives what it gives wherever it is read from.
theorem roundOfGivesFine ∀ [start: Parse.Mark Char]
    [p: () → {Parse Char} List (Parse.Located Lexeme)] [holds: List (Parse.Located Lexeme) → Prop]
    (gives: Parse.Gives Parse.Invariant.any p holds):
    RoundOk start p (read values => holds values) :=
  total state value after here honest h => Inr (gives start { holds = Trivial } total state value after here honest h)

--| A token, from a mark in step, spelled as its kind is when what it reads is.
theorem tokenFixed ∀ (source: Text) (kind: Tok) (count: Nat) (start: Parse.Mark Char)
    (step: InStep source.toList start)
    (spelled: fixedSpells1 kind (Text.fromList (start.rest.take count)) = True):
    Parse.ReadsAt start (() => [tokenOf kind count]) (read values => lexemesFine source values = True) :=
  atThen (tokenOfText source kind count start step) (read lexeme after starts moved made =>
    match made with
      | Both isToken text =>
        let fixed: lexemeFixed source lexeme = True := rewrite isToken, text then spelled
        Parse.readsAtDone after _ (Bool.andIntro fixed byComputing))

--| `symbol`'s token, read from where the input is, is spelled as its kind is.
theorem symbolSpelled ∀ (start: Parse.Mark Char) (input: List Char) (kind: Tok) (count: Nat)
    (here: start.rest = input)
    (e: symbol input = Some (kind, count)):
    fixedSpells1 kind (Text.fromList (start.rest.take count)) = True :=
  let fixed: symbolFixed1 input = True := symbolFixed input
  rewrite here then (rewrite e at fixed then fixed)

theorem symbolSpelledExample: fixedSpells1 Arrow (Text.fromList ((Parse.State.start ['-', '>', 'x']).at.rest.take 2))
      = True :=
  symbolSpelled (Parse.State.start ['-', '>', 'x']).at ['-', '>', 'x'] Arrow 2 byComputing byComputing

--| One round of `item` at the top level, from a mark in step with the source: unless it gave a token outside the
--| alphabet, every lexeme it gave is spelled as its kind is. By the same match as `itemOn`'s, so each arm computes.
theorem itemFixed ∀ (self: Place → {Parse Char} List (Parse.Located Lexeme)) (source: Text)
    (start: Parse.Mark Char) (input: List Char)
    (step: InStep source.toList start)
    (here: start.rest = input):
    RoundOk start (() => itemOn self source TopLevel start input) (read values => lexemesFine source values = True) :=
  match input with
    | [] => roundOfYields (yieldsStop _)
    | ['\n', ..more] =>
      roundOfGivesFine (Parse.readsThen (soundSkip 1) (read u h => oneLocated source LineBreak start byComputing))
    | ['}', ..more] => roundOfReads (tokenFixed source RBrace 1 start step byComputing)
    | ['{', ..more] => roundOfReads (tokenFixed source LBrace 1 start step byComputing)
    | [' ', .._] | ['\r', .._] =>
      roundOfGivesFine (Parse.readsThen (soundSpan _) (read run h => oneLocated source Spaces start byComputing))
    | ['\t', ..more] => roundOfYields (yieldsFatal tabs _)
    | ['-', ..more] =>
      match more with
        | ['-', ..rest] =>
          roundOfGivesFine
            (Parse.readsThen (soundSpan _) (read text h =>
              Parse.readsThen soundMark (read2 at h2 => oneLocated source CommentLexeme start byComputing)))
        | [] => roundOfReads (tokenFixed source Minus 1 start step (rewrite here))
        | [next, ..rest] =>
          match s: symbol ['-', next, ..rest] with
            | Some (kind, count) =>
              roundOfReads
                (tokenFixed source kind count start step (symbolSpelled start ['-', next, ..rest] kind count here s))
            | None => roundOfYields (yieldsFatal (unexpected '-') _)
    | ['"', ..more] => roundOfYields (textForeign self source TopLevel)
    | ['\'', ..more] => roundOfGives givesChar
    | ['.', ..more] => roundOfGives givesDots
    | [other, ..more] =>
      match w: isWordStart other with
        | True =>
          roundOfReads
            (atThen
              (Parse.readsAtMarkThen [j := from => wordFrom False from] (wordFine source start other more step here w))
              (read lexeme after starts moved fine => Parse.readsAtDone after _ (Bool.andIntro fine byComputing)))
        | False =>
          match d: other.isAsciiDigit with
            | True =>
              roundOfReads
                (atThen
                  (Parse.readsAtMarkThen
                    [j := from => numberFrom False from]
                    (numberFine source start other more step here d))
                  (read lexeme after starts moved fine => Parse.readsAtDone after _ (Bool.andIntro fine byComputing)))
            | False =>
              match u: other.toNat >= 128 with
                | True =>
                  match a: Tok.unicodeAlias other with
                    | Some kind =>
                      roundOfReads (tokenFixed source kind 1 start step (rewrite here then unicodeFixed other kind a))
                    | None => roundOfYields [p := () => fail (unexpected other)] (yieldsFatal (unexpected other) _)
                | False =>
                  match s: symbol [other, ..more] with
                    | Some (kind, count) =>
                      roundOfReads
                        [p := () => [tokenOf kind count]]
                        (tokenFixed source kind count start step
                          (symbolSpelled start [other, ..more] kind count here s))
                    | None =>
                      roundOfYields
                        [p := () => fail (if other == '@' then strayAt else unexpected other)]
                        (yieldsFatal (if other == '@' then strayAt else unexpected other) _)

-- The lexer at the top level: rounds of `item`, each spelled.

--| A round from `offset`, where `rest` is left: when `rest` is the source from `offset` and the round gave only
--| tokens of the alphabet, its lexemes are spelled as their kinds are.
def FixedAt (source: Text) (offset: Nat) (rest read: List Char) (values: List (Parse.Located Lexeme)): Prop :=
  rest = source.toList.drop offset
    → values.all (lexeme => lexeme.value.within) = True
    → lexemesFine source values = True

--| A round of `item` at the top level, from any mark: `itemFixed` when the mark is in step.
theorem itemFixedAt ∀ (self: Place → {Parse Char} List (Parse.Located Lexeme)) (source: Text) (start: Parse.Mark Char):
    RoundOk start (() => item self source TopLevel) (FixedAt source start.offset start.rest) :=
  total state value after here honest h =>
    let marked := Eq.trans (Parse.runFromMark state (m => (itemAt self source TopLevel m, Parse.mark()))).flipped h
    let given: Parse.runFrom state (() => (itemOn self source TopLevel start start.rest, Parse.mark()))
      = Ok (value, after) :=
      rewrite here at marked then marked
    match itemRound self source start start.rest byComputing total state value after here honest given with
      | Inl outside => Inl outside
      | Inr (Witness read (Both starts (Both honestAfter _))) =>
        Inr
          (Witness read
            (Both starts
              (Both honestAfter (step within =>
                match itemFixed self source start start.rest step byComputing total state value after here honest
                    given with
                  | Inl outside => (Bool.trueNotFalse (Eq.trans within.flipped outside)).impossible
                  | Inr (Witness read2 (Both starts2 (Both honest2 fixed))) => fixed))))

--| Rounds each spelled, read in turn from where the source is at `offset`: those of the alphabet are spelled.
theorem eachFixed ∀ (source: Text) (rounds: List (List (Parse.Located Lexeme))) (offset: Nat) (rest read: List Char)
    (each: EachAt (FixedAt source) offset rest read rounds)
    (step: rest = source.toList.drop offset)
    (within: rounds.all (round => round.all (lexeme => lexeme.value.within)) = True):
    rounds.all (lexemesFine source) = True :=
  match rounds, each with
    | [], _ => byComputing
    | [round, ..more], Witness first (Witness later (Both _ (Both fixed eachMore))) =>
      let next: rest.drop first.length = source.toList.drop (offset + first.length) :=
        rewrite step, List.dropAdd offset first.length source.toList
      Bool.andIntro
        (fixed step (Bool.andLeft within))
        (eachFixed source more
          (offset + first.length)
          (rest.drop first.length)
          later
          eachMore
          next
          (Bool.andRight within))

theorem concatFine ∀ (source: Text) (rounds: List (List (Parse.Located Lexeme))):
    lexemesFine source rounds.concat = rounds.all (lexemesFine source) :=
  match rounds with
    | [] => byComputing
    | [round, ..more] => rewrite List.allAppendAnd round more.concat (lexemeFixed source), concatFine source more

--| The lexemes of any source that lexes, all of slice 1's alphabet, are spelled as their kinds are, where they stand
--| in the source.
--|
--| Proof idea: as `lexemesRounds`, the lexemes are rounds of `item` joined, read in turn from the start of the source
--| (`atManyFromOr`); each round of the alphabet is spelled (`itemFixedAt`), since each begins where the source is
--| (`eachFixed`).
theorem lexemesFixed ∀ (source: Text) (found: List (Parse.Located Lexeme))
    (lexes: lexemes source = Ok found)
    (within: found.all (lexeme => lexeme.value.within) = True):
    found.all (lexemeFixed source) = True :=
  let body := (self: Place → {Parse Char} List (Parse.Located Lexeme)) (inner: Place) =>
    Parse.many (() => item self source inner) |> List.concat
  let self0 := (inner: Place) => Parse.recursiveWithFuel source.toList.length body inner
  let first := Parse.State.start source.toList
  match r: Parse.run source.toList (() => lexemesIn source TopLevel) with
    | Ok got =>
      let gotFound: got = found := Result.okInjective lexes
      let r1 := Eq.trans (Parse.runFromMark first (at => Parse.recursiveWithFuel (at.left + 1) body TopLevel)).flipped r
      let r2: Parse.runFrom first (() => List.concat (Parse.many (() => item self0 source TopLevel))) = Ok got := r1
      match Parse.runFromThenOk
        (() => Parse.many (() => item self0 source TopLevel))
        first
        (rounds => List.concat rounds)
        got
        r2 with
        | Witness rounds (Witness after (Both ranMany restRun)) =>
          let joined: Ok rounds.concat = Ok got := Eq.trans (Parse.runFromPure after rounds.concat).flipped restRun
          let foundIs: found = rounds.concat := rewrite <- gotFound then (Result.okInjective joined).flipped
          let ranMany2 :=
            Eq.trans
              (Parse.runFromMark first (m =>
                (Parse.manyFrom (m.left + 1) (() => item self0 source TopLevel) [] m, Parse.mark()))).flipped
              ranMany
          let honest: Parse.Honest source.toList.length first.at := Both byComputing (arithmetic [])
          let all: rounds.concat.all (lexeme => lexeme.value.within) = True := rewrite <- foundIs then within
          let roundsWithin: rounds.all (round => round.all (lexeme => lexeme.value.within)) = True :=
            rewrite concatWithin rounds at all then all
          match atManyFromOr
            (() => item self0 source TopLevel)
            (FixedAt source)
            (start => itemFixedAt self0 source start)
            (first.at.left + 1)
            []
            source.toList.length
            first
            rounds
            after.at
            honest
            ranMany2 with
            | Inl outside => (Bool.trueNotFalse (Eq.trans roundsWithin.flipped outside)).impossible
            | Inr (Witness read (Both starts (Both honest2 (Witness more (Both same each))))) =>
              let roundsAre: rounds = more := same
              let fine: rounds.all (lexemesFine source) = True :=
                rewrite roundsAre at roundsWithin then
                  rewrite roundsAre then eachFixed source more 0 source.toList read each byComputing roundsWithin
              let joinedFine: lexemesFine source rounds.concat = True := rewrite concatFine source rounds then fine
              rewrite foundIs then joinedFine
