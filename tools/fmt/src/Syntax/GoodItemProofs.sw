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
import Std (Bool, Char, DecEq, Empty, Eq, List, Nat, Option, Pair, Parse, Result, Text, Void)
import Syntax (..)
import Fmt (..)
import Syntax.Proofs (Spells)
import Syntax.ParseProofs (GoodItem)
import Syntax.SettleProofs (alphabet1, plain1, plainFromOf, settledKeepsTokens, tokens)
import Syntax.SettleBareProofs (tokensBare)
import Syntax.SettleSplitProofs (groupsConcat)
import Fmt.TreeJoinProofs (spellsOfText1)
import Syntax.LexReadsProofs (
  RoundOk,
  atMarkThen,
  atThen,
  givesChar,
  givesDots,
  roundOfGives,
  roundOfReads,
  roundOfYields,
  soundMark,
  soundSkip,
  soundSpan,
  textForeign,
  yieldsFatal,
  yieldsStop
)

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
--| Not yet proved: the walk of `lexemesIn`, below this file's reading lemmas. Done: reading in step with the source
--| (`Lexes`, with bind, mark, many and `recursiveWith`), `tokenOfText` (a token's text is what it read), and the kinds
--| of fixed spelling (`symbolFixed`, `unicodeFixed`, `wordFine`, `givesNumber`). Left: `itemOn`'s arms, with `dots`,
--| `charLiteral` and `textLiteral` (`pieces`, `segment`, `closeBlock`) as `Goes`-style lemmas whose tokens are of no
--| fixed spelling, and the run of `lexemes` from the start mark.
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

-- What the lexer's choices of kind say of the text, for the walk of `lexemesIn` (`lexemesFixed`).

--| A Unicode character the lexer reads as a token of fixed spelling is that token's text.
theorem unicodeFixed ∀ (char: Char) (kind: Tok)
    (alias: Tok.unicodeAlias char = Some kind):
    fixedSpells1 kind (Text.fromList [char]) = True :=
  cases

theorem unicodeFixedExample: fixedSpells1 Arrow (Text.fromList ['→']) = True := unicodeFixed '→' Arrow byComputing

-- Reading in step with the source: what a parser gives from any mark whose input left is the source from its offset.
-- `Parse.ReadsIn` can't say this (its invariant is of the input left alone), so a lexeme's offset couldn't be tied to
-- the source with it.

--| A mark in step with the source: what is left is the source from the mark's offset.
def InStep (chars: List Char) (at: Parse.Mark Char): Prop := at.rest = chars.drop at.offset

--| What `parser` gives, run from any mark in step with `chars`: `holds` of its value.
def Lexes (chars: List Char) (parser: () → {Parse Char} a) (holds: a → Prop): Prop :=
  ∀ (start: Parse.Mark Char) => InStep chars start → Parse.ReadsAt start parser (read value => holds value)

--| Reading keeps a mark in step.
theorem inStepAfter ∀ [chars: List Char] [total: Nat] [start after: Parse.Mark Char] [read: List Char]
    (step: InStep chars start)
    (before: Parse.Honest total start)
    (now: Parse.Honest total after)
    (starts: start.rest = read ++ after.rest):
    InStep chars after :=
  let moved: after.offset = start.offset + read.length := Parse.honestMoved before now starts
  let wanted: after.rest = chars.drop after.offset := calc after.rest
    _ = (read ++ after.rest).drop read.length := (List.dropAppend read after.rest).flipped
    _ = start.rest.drop read.length := rewrite starts
    _ = (chars.drop start.offset).drop read.length := rewrite step
    _ = chars.drop (start.offset + read.length) := (List.dropAdd start.offset read.length chars).flipped
    _ = chars.drop after.offset := rewrite moved
  wanted

--| A parser read from every mark gives what it gives from marks in step.
theorem lexesOfReads ∀ [chars: List Char] [parser: () → {Parse Char} a] [holds: a → Prop]
    (reads: Parse.Reads parser (read value => holds value)):
    Lexes chars parser holds :=
  start step => reads start { holds = Trivial }

theorem lexesWeaken ∀ [chars: List Char] [parser: () → {Parse Char} a] [holds weaker: a → Prop]
    (lexes: Lexes chars parser holds) (implies: ∀ (value: a) => holds value → weaker value):
    Lexes chars parser weaker :=
  start step => Parse.readsAtWeaken (lexes start step) (read value => implies value)

--| `p`, then `j` of its value.
theorem lexesBind ∀ [chars: List Char] (p: () → {Parse Char} a) (j: a → {Parse Char} b)
    [first: a → Prop] [next: b → Prop]
    (lexesFirst: Lexes chars p first)
    (lexesNext: ∀ (v: a) => first v → Lexes chars (() => j v) next):
    Lexes chars (() => j (p())) next :=
  start step total state value after here honest h =>
    match Parse.runFromThenOk2 p state j _ _ h with
      | Witness v (Witness middle (Both ran restRun)) =>
        match lexesFirst start step total state v middle.at here honest ran with
          | Witness firstRead (Both starts1 (Both honest1 holds1)) =>
            match lexesNext v holds1 middle.at
              (inStepAfter step honest honest1 starts1)
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

--| A parser that looks at where it is, `k (Parse.mark())`.
theorem lexesMark ∀ [chars: List Char] (k: Parse.Mark Char → {Parse Char} a) [holds: a → Prop]
    (each: ∀ (start: Parse.Mark Char) => InStep chars start
      → Parse.ReadsAt start (() => k start) (read value => holds value)):
    Lexes chars (() => k (Parse.mark())) holds :=
  start step total state value after here honest h =>
    let ran: Parse.runFrom state (() => (k state.at, Parse.mark())) = Ok (value, after) := h
    each start step total state value after here honest (rewrite <- here then ran)

--| `manyFrom` from a mark in step, after values found that hold: every value holds.
--|
--| Proof idea: `Parse.readsManyFrom`'s induction on the fuel, the mark kept in step by `inStepAfter` where that keeps
--| the invariant.
theorem lexesManyFrom ∀ [chars: List Char] (p: () → {Parse Char} a) (holds: a → Prop)
    (lexes: Lexes chars p holds)
    (fuel: Nat) (found: List a)
    (foundHolds: List.All holds found)
    (total: Nat) (state: Parse.State Char) (value: List a) (after: Parse.Mark Char)
    (step: InStep chars state.at)
    (honest: Parse.Honest total state.at)
    (h: Parse.runFrom state (() => (Parse.manyFrom fuel p found state.at, Parse.mark())) = Ok (value, after)):
    ∃ (read: List Char) => state.at.rest = read ++ after.rest ∧ Parse.Honest total after ∧ List.All holds value :=
  match fuel with
    | Zero =>
      match Parse.readsPure
        [inv := Parse.Invariant.any]
        (List.reverse found)
        state.at
        { holds = Trivial }
        total
        state
        value
        after
        byComputing
        honest
        h with
        | Witness read (Both starts (Both honestAfter (Both none same))) =>
          Witness read (Both starts (Both honestAfter (rewrite same then List.allReverse holds found foundHolds)))
    | Succ more =>
      match Parse.runFromOptionalFromOk2 p state.at state
        (found2 => Parse.manyRound more p found state.at found2)
        (x => (x, Parse.mark()))
        (value, after)
        h with
        | Inl (Witness v (Witness middle (Both ran rest))) =>
          match lexes state.at step total state v middle.at byComputing honest ran with
            | Witness read1 (Both starts1 (Both honest1 holds1)) =>
              match Parse.runFromIfOk
                (middle.at.offset > state.at.offset)
                (() => Parse.manyFrom more p [v, ..found] middle.at)
                (() => Empty.absurd (Parse.fatal "`many`: the parser matched without reading anything"))
                middle
                value
                after
                rest with
                | Inl (Both isTrue yesRun) =>
                  match lexesManyFrom p holds lexes more
                    [v, ..found]
                    (holds1, foundHolds)
                    total
                    middle
                    value
                    after
                    (inStepAfter step honest honest1 starts1)
                    honest1
                    yesRun with
                    | Witness read2 (Both starts2 (Both honest2 all2)) =>
                      Witness
                        (read1 ++ read2)
                        (Both (rewrite starts1, starts2, List.appendAssoc read1 read2 after.rest) (Both honest2 all2))
                | Inr (Both isFalse noRun) => (Result.errNotOk noRun).impossible
        | Inr (Witness middle (Both back rest)) =>
          match Parse.readsPure
            [inv := Parse.Invariant.any]
            (List.reverse found)
            middle.at
            { holds = Trivial }
            total
            middle
            value
            after
            byComputing
            (rewrite back then honest)
            rest with
            | Witness read (Both starts (Both honestAfter (Both none same))) =>
              Witness []
                (Both
                  (rewrite <- back then (rewrite none at starts then starts))
                  (Both honestAfter (rewrite same then List.allReverse holds found foundHolds)))

--| `many p` gives values that all hold, when `p` gives one that does.
theorem lexesMany ∀ [chars: List Char] (p: () → {Parse Char} a) (holds: a → Prop)
    (lexes: Lexes chars p holds):
    Lexes chars (() => Parse.many p) (values => List.All holds values) :=
  start step total state value after here honest h =>
    rewrite <- here then
      lexesManyFrom p holds lexes
        (state.at.left + 1)
        []
        Trivial
        total
        state
        value
        after
        (rewrite here then step)
        (rewrite here then honest)
        h

theorem lexesRecursiveWithFuel ∀ [chars: List Char] (body: (b → {Parse Char} a) → b → {Parse Char} a) (holds: a → Prop)
    (lexesBody: ∀ (self: b → {Parse Char} a) => (∀ (inner: b) => Lexes chars (() => self inner) holds)
      → ∀ (argument: b) => Lexes chars (() => body self argument) holds)
    (fuel: Nat) (argument: b):
    Lexes chars (() => Parse.recursiveWithFuel fuel body argument) holds :=
  match fuel with
    | Zero => lexesOfReads (Parse.readsFatal _ _)
    | Succ more =>
      lexesBody
        (inner => Parse.recursiveWithFuel more body inner)
        (inner => lexesRecursiveWithFuel body holds lexesBody more inner)
        argument

--| `recursiveWith body argument` gives what holds, when `body` does given a nested parser that does.
theorem lexesRecursiveWith ∀ [chars: List Char] (body: (b → {Parse Char} a) → b → {Parse Char} a) (holds: a → Prop)
    (lexesBody: ∀ (self: b → {Parse Char} a) => (∀ (inner: b) => Lexes chars (() => self inner) holds)
      → ∀ (argument: b) => Lexes chars (() => body self argument) holds) (argument: b):
    Lexes chars (() => Parse.recursiveWith body argument) holds :=
  lexesMark (at => Parse.recursiveWithFuel (at.left + 1) body argument) (start step =>
    lexesRecursiveWithFuel body holds lexesBody (start.left + 1) argument start step)

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

--| `k (Parse.mark())` from `start` is `k start`.
theorem readsAtMark ∀ (k: Parse.Mark Char → {Parse Char} a) (spec: List Char → a → Prop) (start: Parse.Mark Char)
    (each: Parse.ReadsAt start (() => k start) spec):
    Parse.ReadsAt start (() => k (Parse.mark())) spec :=
  total state value after here honest h =>
    let ran: Parse.runFrom state (() => (k state.at, Parse.mark())) = Ok (value, after) := h
    each total state value after here honest (rewrite <- here then ran)

--| `next` of anything reads the first character left, if there is one.
theorem readsAtNextAny ∀ (start: Parse.Mark Char):
    Parse.ReadsAt start (() => Parse.next (char => True)) (read v => read = start.rest.take 1) :=
  total state value after here honest h =>
    let honestAt: Parse.Honest total state.at := rewrite here then honest
    rewrite <- here then
      match e: state.at.rest with
        | [] =>
          let same := Result.okInjective h
          let atSame: state.at = after := Pair.mkInjectiveSnd same
          Witness [] (rewrite <- atSame, e then Both byComputing (Both honestAt byComputing))
        | [char, ..more] =>
          let same := Result.okInjective h
          let atSame: (state.advance more 1).at = after := Pair.mkInjectiveSnd same
          let counted: state.at.left = more.length + 1 := honestAt.left
          Witness
            [char]
            (rewrite <- atSame then
              Both byComputing (Both (Both (arithmetic [counted]) (arithmetic [counted, honestAt.right])) byComputing))

--| `skip count` reads the first `count` characters left, or all of them if there are fewer.
theorem readsAtSkip ∀ (count: Nat) (start: Parse.Mark Char):
    Parse.ReadsAt start (() => skip count) (read u => read = start.rest.take count) :=
  match count with
    | Zero => Parse.readsAtDone start () _ byComputing
    | Succ more => readsAtThenMoved (readsAtNextAny start) (read v after starts moved took =>
      Parse.readsAtWeaken (readsAtSkip more after) (taken u rest =>
        match e: start.rest with
          | [] =>
            let none: read = [] := took
            let emptyAfter: after.rest = [] := rewrite <- (rewrite none at starts then starts)
            rewrite none, rest, emptyAfter then List.takeNil more
          | [char, ..others] =>
            let one: read = [char] := took
            let tail: after.rest = others :=
              (List.consInjective char others after.rest (rewrite one at starts then starts)).flipped
            rewrite one, rest, tail))

--| Taking as many as a take gave takes the same.
theorem takeOwnLength ∀ (chars: List Char) (count: Nat): chars.take (chars.take count).length = chars.take count :=
  match chars, count with
    | [], count => rewrite List.takeNil count
    | [char, ..rest], Zero => byComputing
    | [char, ..rest], Succ more => rewrite takeOwnLength rest more

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
  readsAtMark
    (from =>
      let skipped := skip count
      located (TokenLexeme kind) from) _
    start
    (readsAtThenMoved (readsAtSkip count start) (read u after starts moved taken =>
      readsAtMark
        (to => { value = TokenLexeme kind, offset = start.offset, length = to.offset - start.offset }) _
        after
        (Parse.readsAtDone after _ _
          (Both byComputing
            (rewrite sliceRead source start after read step moved, taken, takeOwnLength start.rest count)))))

--| `symbol`'s choice, tested: a token of fixed spelling is its text.
def symbolFixed1 (input: List Char): Bool := match symbol input with
  | Some (kind, count) => fixedSpells1 kind (Text.fromList (input.take count))
  | None => True

--| `symbol`'s choice is spelled as its kind is: by the same match as `symbol`'s, so each arm computes.
theorem symbolFixed ∀ (input: List Char): symbolFixed1 input = True := match input with
  | ['(', .._] => byComputing
  | [')', .._] => byComputing
  | ['[', .._] => byComputing
  | [']', .._] => byComputing
  | ['{', .._] => byComputing
  | ['}', .._] => byComputing
  | [',', .._] => byComputing
  | [';', .._] => byComputing
  | [':', '=', .._] => byComputing
  | [':', .._] => byComputing
  | ['=', '=', .._] => byComputing
  | ['=', '>', .._] => byComputing
  | ['=', .._] => byComputing
  | ['|', '|', .._] => byComputing
  | ['|', '>', .._] => byComputing
  | ['|', .._] => byComputing
  | ['&', '&', .._] => byComputing
  | ['+', '+', .._] => byComputing
  | ['+', .._] => byComputing
  | ['-', '>', .._] => byComputing
  | ['-', .._] => byComputing
  | ['*', .._] => byComputing
  | ['/', .._] => byComputing
  | ['%', .._] => byComputing
  | ['!', '=', .._] => byComputing
  | ['!', 'i', 'n', next, .._] if !isWordChar next => cases
  | ['!', 'i', 'n'] => byComputing
  | ['!', .._] => cases
  | ['<', '-', '>', .._] => byComputing
  | ['<', '=', .._] => byComputing
  | ['<', .._] => byComputing
  | ['>', '=', .._] => byComputing
  | ['>', .._] => byComputing
  | ['?', .._] => byComputing
  | ['@', '[', .._] => byComputing
  | [_, .._] => byComputing
  | [] => byComputing

--| A word is `def` when the lexer says so: by the same match as `wordKind`'s and `Tok.keyword`'s, so each arm computes.
theorem wordKindFixed ∀ (afterDot: Bool) (word: Text): fixedSpells1 (wordKind afterDot word) word = True :=
  match word with
    | "_" => byComputing
    | "Type" => byComputing
    | "Prop" => byComputing
    | "ability" => byComputing
    | "algebra" => byComputing
    | "arithmetic" => byComputing
    | "calc" => byComputing
    | "cases" => byComputing
    | "decreasing" => byComputing
    | "def" => byComputing
    | "else" => byComputing
    | "exists" => cases
    | "export" => byComputing
    | "forall" => cases
    | "handle" => byComputing
    | "if" => byComputing
    | "import" => byComputing
    | "in" => byComputing
    | "include" => byComputing
    | "instance" => byComputing
    | "interface" => byComputing
    | "let" => byComputing
    | "match" => byComputing
    | "namespace" => byComputing
    | "opaque" => byComputing
    | "return" => byComputing
    | "rewrite" => byComputing
    | "test" => byComputing
    | "then" => byComputing
    | "theorem" => byComputing
    | "type" => byComputing
    | "unfolding" => byComputing
    | "where" => byComputing
    | "with" => byComputing
    | _ => cases

-- The lexer's parts whose values are not in question: each succeeds only having read a start of its input.

--| `parser`, run from any mark, reads a start of its input and stops at an honest mark.
def Goes (parser: () → {Parse Char} a): Prop := Parse.Gives Parse.Invariant.any parser (value => Std.Unit)

theorem goesSkip ∀ (count: Nat): Goes (() => skip count) := start fine =>
  Parse.readsAtWeaken (readsAtSkip count start) (read u taken => Trivial)

theorem goesSpan ∀ (passes: Char → Bool): Goes (() => Parse.span passes) :=
  Parse.readsWeaken [p := () => Parse.span passes] (Parse.readsSpan passes) (read taken spanned => Trivial)

--| `located value from` gives a lexeme of that value.
theorem givesLocated ∀ (value: Lexeme) (from: Parse.Mark Char):
    Parse.Gives Parse.Invariant.any (() => located value from) (lexeme => lexeme.value = value) :=
  Parse.readsWithMark (to => { value, offset = from.offset, length = to.offset - from.offset }) _ (to fine =>
    Parse.givesDone byComputing)

theorem goesReadEscape ∀ (rest: List Char): Goes (() => readEscape rest) := match escapeLength rest with
  | Ok count => Parse.givesThen (goesSkip count) (u done => Parse.givesDone Trivial)
  | Err message => Parse.readsFatal message _

theorem goesFraction: Goes (() => fractionPart()) := Parse.readsWithMark fractionFrom _ (at fine =>
  match fractionAhead at.rest with
    | True => Parse.givesThen (goesSkip 1) (u skipped =>
      Parse.givesThen (goesSpan Char.isAsciiDigit) (decimals read => Parse.givesDone Trivial))
    | False => Parse.givesDone Trivial)

theorem goesExponent: Goes (() => exponentPart()) := Parse.readsWithMark exponentFrom _ (at fine =>
  match exponentSkip at.rest with
    | Some count => Parse.givesThen (goesSkip count) (u skipped =>
      Parse.givesThen (goesSpan Char.isAsciiDigit) (power read => Parse.givesDone Trivial))
    | None => Parse.givesDone Trivial)

theorem goesNumberTail ∀ (afterDot: Bool): Goes (() => numberTail afterDot) := match afterDot with
  | True => Parse.givesDone Trivial
  | False => Parse.givesThen goesFraction (fraction read =>
    Parse.givesThen goesExponent (exponent read => Parse.givesDone Trivial))

--| A number is a `Num` or a `Float`, of no fixed spelling.
theorem givesNumber ∀ (source: Text) (afterDot: Bool):
    Parse.Gives Parse.Invariant.any (() => number afterDot) (lexeme => lexemeFixed source lexeme = True) :=
  Parse.readsWithMark (numberFrom afterDot) _ (from fine =>
    Parse.givesThen (goesSpan Char.isAsciiDigit) (digits read =>
      Parse.givesThen (goesNumberTail afterDot) (float read =>
        Parse.givesWeaken (givesLocated (TokenLexeme (if float then Float else Num)) from) (lexeme same =>
          rewrite same then cases))))

--| What `qualified` read: nothing, giving what was found before, or a component, giving `Some`.
def QualifiedRead (found: Option Bool) (read: List Char) (value: Option Bool): Prop :=
  value = found ∧ read = [] ∨ value.isSome = True

theorem readsQualified ∀ (fuel: Nat) (upper: Bool) (found: Option Bool):
    Parse.Reads (() => qualified fuel upper found) (QualifiedRead found) :=
  match fuel with
    | Zero => Parse.readsDone found _ (Inl (Both byComputing byComputing))
    | Succ more => Parse.readsWithMark (at => qualifiedOn more upper found at.rest) _ (at fine =>
      readsQualifiedOn more upper found at.rest)

theorem readsQualifiedOn ∀ (more: Nat) (upper: Bool) (found: Option Bool) (input: List Char):
    Parse.Reads (() => qualifiedOn more upper found input) (QualifiedRead found) :=
  match input with
    | ['.', next, .._] =>
      match guard: upper && next.isAsciiLetter with
        | False => Parse.readsDone found _ (Inl (Both byComputing byComputing))
        | True =>
          let component: Option Bool := Some next.isAsciiUppercase
          Parse.readsThen
            [p := () => skip 1]
            [j := u =>
              let name := Parse.span isWordChar
              qualified more next.isAsciiUppercase component]
            [spec := QualifiedRead found]
            (goesSkip 1)
            (dot u done =>
              Parse.readsThen
                [p := () => Parse.span isWordChar]
                [spec := read value => QualifiedRead found (dot ++ read) value]
                (goesSpan isWordChar)
                (name taken spanned =>
                  Parse.readsWeaken (readsQualified more next.isAsciiUppercase component) (read value q =>
                    let some: value.isSome = True := match q with
                      | Inl (same, none) => rewrite same
                      | Inr some => some
                    Inr some)))
    | _ => Parse.readsDone found _ (Inl (Both byComputing byComputing))

--| `located value from`, read at `start`, is the lexeme from `from` to `start`.
theorem readsAtLocated ∀ (value: Lexeme) (from start: Parse.Mark Char):
    Parse.ReadsAt start (() => located value from) (read lexeme =>
      lexeme = { value, offset = from.offset, length = start.offset - from.offset }) :=
  readsAtMark
    (to => { value, offset = from.offset, length = to.offset - from.offset }) _
    start
    (Parse.readsAtDone start _ _ byComputing)

--| What a word's kind is: a name's, after a qualified name, or else what `wordKind` makes of the word characters, with
--| nothing more read.
def KindRead (afterDot: Bool) (first read: List Char) (kind: Tok): Prop :=
  kind = Upper ∨ kind = Lower ∨ read = [] ∧ kind = wordKind afterDot (Text.fromList first)

--| A word, from a mark in step, is spelled as its kind is: a name, or `def` only if its text is `def`
--| (`wordKindFixed`).
--|
--| Proof idea: the lexeme's text is the characters the word read; when no qualified name follows, that is the `span`
--| of word characters (`sliceRead`), whose kind `wordKind` gives; with one, the kind is a name's.
theorem wordFine ∀ (source: Text) (afterDot: Bool) (from: Parse.Mark Char)
    (step: InStep source.toList from):
    Parse.ReadsAt from (() => wordFrom afterDot from) (read lexeme => lexemeFixed source lexeme = True) :=
  readsAtThenMoved (Parse.readsAtSpan from isWordChar) (read1 first after1 starts1 moved1 spanned =>
    let upper := first.head.map (char => char.isAsciiUppercase) |> .getOrElse False
    readsAtThenMoved
      [p := () =>
        match qualified (from.left + 1) upper None with
          | Some lastUpper => if lastUpper then Upper else Lower
          | None => wordKind afterDot (Text.fromList first)]
      [j := kind => located (TokenLexeme kind) from]
      [spec := read lexeme => lexemeFixed source lexeme = True]
      (readsAtThenMoved
        [p := () => qualified (from.left + 1) upper None]
        [spec := KindRead afterDot first]
        (readsQualified (from.left + 1) upper None after1 { holds = Trivial })
        (read2 found after2 starts2 moved2 q =>
          match found, q with
            | Some last, _ =>
              match last with
                | True =>
                  Parse.readsAtDone after2 Upper
                    (taken kind => KindRead afterDot first (read2 ++ taken) kind)
                    (Inl byComputing)
                | False =>
                  Parse.readsAtDone after2 Lower
                    (taken kind => KindRead afterDot first (read2 ++ taken) kind)
                    (Inr (Inl byComputing))
            | None, Inr isSome => (Bool.falseNotTrue isSome).impossible
            | None, Inl (_, none) =>
              Parse.readsAtDone after2
                (wordKind afterDot (Text.fromList first))
                (taken kind => KindRead afterDot first (read2 ++ taken) kind)
                (Inr (Inr (Both (rewrite none) byComputing)))))
      (readKind kind after3 starts3 moved3 kindRead =>
        Parse.readsAtWeaken (readsAtLocated (TokenLexeme kind) from after3) (taken lexeme same =>
          rewrite same then
            match kindRead with
              | Inl upperKind => rewrite upperKind
              | Inr (Inl lowerKind) => rewrite lowerKind
              | Inr (Inr (none, wordKindIs)) =>
                let empty: readKind.length = 0 := rewrite none
                let moved: after3.offset = from.offset + read1.length := arithmetic [moved1, moved3, empty]
                let text: Text.fromList (from.rest.take read1.length) = Text.fromList first :=
                  rewrite starts1, List.takeAppend read1 after1.rest, spanned.left
                rewrite wordKindIs, sliceRead source from after3 read1 step moved, text then
                  wordKindFixed afterDot (Text.fromList first))))

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
          | Spaces, same, _ => rewrite same
          | LineBreak, same, _ => rewrite same
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
  atThen
    [p := () => tokenOf kind count]
    [j := made => [made]]
    (tokenOfText source kind count start step)
    (read lexeme after starts moved made =>
      match made with
        | Both isToken text =>
          let fixed: lexemeFixed source lexeme = True := rewrite isToken, text then spelled
          Parse.readsAtDone after _ _ (Bool.andIntro fixed byComputing))

--| `symbol`'s token, read from where the input is, is spelled as its kind is.
theorem symbolSpelled ∀ (start: Parse.Mark Char) (input: List Char) (kind: Tok) (count: Nat)
    (here: start.rest = input)
    (e: symbol input = Some (kind, count)):
    fixedSpells1 kind (Text.fromList (start.rest.take count)) = True :=
  let fixed: symbolFixed1 input = True := symbolFixed input
  rewrite here then (rewrite e at fixed then fixed)

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
    | [' ', ..more] =>
      roundOfGivesFine (Parse.readsThen (soundSpan _) (read run h => oneLocated source Spaces start byComputing))
    | ['\r', ..more] =>
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
            | None => roundOfYields [p := () => fail (unexpected '-')] (yieldsFatal (unexpected '-') _)
    | ['"', ..more] => roundOfYields (textForeign self source TopLevel)
    | ['\'', ..more] => roundOfGives givesChar
    | ['.', ..more] => roundOfGives givesDots
    | [other, ..more] =>
      match w: isWordStart other with
        | True =>
          roundOfReads
            (atThen
              [p := () => word False]
              [j := made => [made]]
              (atMarkThen [j := from => wordFrom False from] (wordFine source False start step))
              (read lexeme after starts moved fine => Parse.readsAtDone after _ _ (Bool.andIntro fine byComputing)))
        | False =>
          match d: other.isAsciiDigit with
            | True =>
              roundOfGivesFine
                (Parse.givesThen (givesNumber source False) (lexeme fine =>
                  Parse.givesDone (Bool.andIntro fine byComputing)))
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
