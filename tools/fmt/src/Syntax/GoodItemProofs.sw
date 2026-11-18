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
import Std (Bool, DecEq, Empty, Eq, List, Nat, Option, Parse, Result, Text, Void)
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
--| Not yet proved (SW-4024's report has the plan): a walk of `lexemesIn`, every token lexeme a `located` from the mark
--| it starts at, so its text is the characters read from there (`symbol`'s, `unicodeFixed`'s, or a word's, which is
--| `def` only when `wordKind` says `KwDef`). It needs `Parse` facts that keep a mark in step with the source
--| (`start.rest = source.toList.drop start.offset`): `Parse.ReadsIn`'s invariant is of the input left, and its spec
--| can't name where a run started, so it can't tie a lexeme's offset to the source.
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
