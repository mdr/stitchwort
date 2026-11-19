--| `printLexes1` from the tree's facts (docs/proposals/self-hosted-fmt-s1-sketch.md §1.5, ticket 18c): `printLexes1`
--| (`Fmt.JoinProofs`) takes `DeclJoins` and `Every Printable`, which are facts about the declaration's tokens' spellings
--| and what may follow them; this file derives both from the tree's facts (`within1`, `sound`, `lexical1`, `shaped1`)
--| alone, with `kinds` the lexer's kind of each text (`lexKind`).
--|
--| A name or numeral's spelling comes from `within1` (`textSpells1`, `spellsOfText1`): `lexesAs` alone is too weak,
--| since a qualified name (`List.map`) lexes as one `Lower` token and a numeral with an exponent (`1e3`) as one `Float`,
--| and neither is a text `Spells` that kind (`qualifiedLexes`, `exponentLexes`), so `within1` leaves them out. An
--| operator's token is narrowed the same way: `within1` lets an infix operator through only if some token of the
--| alphabet is spelled with its text, and a prefix only if it is `-`, `!` or `¬` (`withinOperators`, giving
--| `operators1`), so `|>` is out (`pipedOut`, `pipedNotSpelled`).

namespace Fmt.TreeJoinProofs
import Std (Bool, Char, DecEq, Doc, Eq, List, Nat, Option, Pair, Result, Text, Void, byDecision)
import Std.Doc.Proofs (Every, everyAppend, isLayout, printedPieces)
import Syntax (
  Comments,
  Decl,
  DefBody,
  DefKind,
  Expr,
  Header,
  InfixKind,
  Note,
  Tok,
  Word,
  isWordChar,
  isWordStart,
  lex,
  wordKind
)
import Syntax.Proofs (
  ExponentAs,
  FloatTailAs,
  FractionAs,
  Laid,
  LexesAs,
  MayFollow,
  NameKind,
  QualTail,
  Spells,
  lexesAsSpells,
  mayFollowEnd,
  qualChars,
  qualFoundSome,
  qualLast,
  qualCharsStops
)
import Fmt (..)
import Fmt.PrintLexProofs (Follows, Printable, pieceFold)
import Fmt.SpellProofs (..)
import Fmt.JoinProofs (DeclJoins, Joinable, AllJoinable, WordJoins, CloserJoins, OpenerJoins, Token, printLexes1)

-- The lexer's kind of a text, and where `lexesAs` is too weak.

--| The kind the lexer gives a text that lexes as one token (any kind for another).
def lexKind (text: Text): Tok := match lex text with
  | Ok lexed =>
    match lexed.leaves with
      | [leaf] => leaf.token.kind
      | _ => Lower
  | Err _ => Lower

--| A text that spells a token of a kind is read by the lexer as that kind.
theorem lexKindOfSpells ∀ (kind: Tok) (text: Text) (spells: Spells kind text): lexKind text = kind :=
  let ran := lexesAsSpells kind text spells (mayFollowEnd kind text)
  rewrite ran

-- What a token's spelling says of the text.

--| A kind that is no comma or closer.
def Quiet (kind: Tok): Prop := Comma ≠ kind ∧ RParen ≠ kind ∧ RBracket ≠ kind ∧ RBrace ≠ kind

theorem startNotDash ∀ (first: Char) (starts: isWordStart first = True): ('-' == first) = False := cases

theorem digitNotDash ∀ (first: Char) (starts: first.isAsciiDigit = True): ('-' == first) = False := cases

theorem headNotDash ∀ (text: Text) (first: Char) (others: List Char)
    (split: text.toList = [first, ..others])
    (differs: ('-' == first) = False):
    text.startsWith "--" = False :=
  rewrite split, Text.sameCharEq '-' first, differs

--| No spelling of a token is a comment.
--|
--| Proof idea: Each fixed spelling by computing; a name or numeral starts with a character that is no `-`.
theorem spellsNotComment ∀ (kind: Tok) (text: Text) (spells: Spells kind text): text.startsWith "--" = False :=
  match kind, spells with
    | LParen, same => rewrite same
    | RParen, same => rewrite same
    | LBracket, same => rewrite same
    | RBracket, same => rewrite same
    | Comma, same => rewrite same
    | Colon, same => rewrite same
    | ColonEq, same => rewrite same
    | Equals, same => rewrite same
    | EqEq, same => rewrite same
    | Arrow, Inl same => rewrite same
    | Arrow, Inr same => rewrite same
    | OrOr, Inl same => rewrite same
    | OrOr, Inr same => rewrite same
    | AndAnd, Inl same => rewrite same
    | AndAnd, Inr same => rewrite same
    | Plus, same => rewrite same
    | PlusPlus, same => rewrite same
    | Minus, same => rewrite same
    | Star, same => rewrite same
    | Slash, same => rewrite same
    | Percent, same => rewrite same
    | NotEq, Inl same => rewrite same
    | NotEq, Inr same => rewrite same
    | Lt, same => rewrite same
    | Le, Inl same => rewrite same
    | Le, Inr same => rewrite same
    | Gt, same => rewrite same
    | Ge, Inl same => rewrite same
    | Ge, Inr same => rewrite same
    | Bang, Inl same => rewrite same
    | Bang, Inr same => rewrite same
    | KwDef, same => rewrite same
    | Lower, Witness first (Witness others (Witness comps (Both split (Both starts rest)))) =>
      headNotDash text first (others ++ qualChars comps) split (startNotDash first starts)
    | Upper, Witness first (Witness others (Witness comps (Both split (Both starts rest)))) =>
      headNotDash text first (others ++ qualChars comps) split (startNotDash first starts)
    | Num, Witness first (Witness others (Both split (Both digit rest))) =>
      headNotDash text first others split (digitNotDash first digit)
    | Float, Witness first (Witness others (Witness tail (Both split (Both digit rest)))) =>
      headNotDash text first (others ++ tail) split (digitNotDash first digit)

--| A text that spells a token of another kind than `other` doesn't spell it.
theorem notFixed ∀ (kind: Tok) (text other: Text)
    (spells: Spells kind text)
    (differs: lexKind other ≠ kind):
    (text == other) = False :=
  match eq: text == other with
    | True =>
      let kindOf := lexKindOfSpells kind text spells
      (differs (rewrite DecEq.sound eq at kindOf then kindOf)).impossible
    | False => eq

--| The text of a token that is no comma or closer is neither.
theorem spellsQuiet ∀ (kind: Tok) (text: Text)
    (spells: Spells kind text)
    (quiet: Quiet kind):
    (text == ",") = False ∧ isCloserText text = False :=
  let (comma, paren, square, brace) := quiet
  let notComma := notFixed kind text "," spells (same => comma (Eq.trans byComputing same))
  let notParen := notFixed kind text ")" spells (same => paren (Eq.trans byComputing same))
  let notSquare := notFixed kind text "]" spells (same => square (Eq.trans byComputing same))
  let notBrace := notFixed kind text "}" spells (same => brace (Eq.trans byComputing same))
  (notComma, rewrite notParen, notSquare, notBrace)

--| What `printLexes1` needs of a word that spells a token of a kind that is no comma or closer.
theorem spellsJoins ∀ (word: Word) (kind: Tok)
    (sound: word.sound = True)
    (spells: Spells kind word.text)
    (quiet: Quiet kind):
    WordJoins word :=
  let (comma, closer) := spellsQuiet kind word.text spells quiet
  (sound, spellsNotComment kind word.text spells, comma, closer)

-- What may follow a prefix operator.

--| The texts an expression's first token may be.
def Leads (text: Text): Prop :=
  text = "("
    ∨ text = "["
    ∨ text = "-"
    ∨ text = "!"
    ∨ text = "¬"
    ∨ Spells Lower text
    ∨ Spells Upper text
    ∨ Spells Num text
    ∨ Spells Float text

theorem startBeq ∀ (first: Char)
    (starts: isWordStart first = True):
    (first == '-') = False ∧ (first == '>') = False ∧ (first == '=') = False :=
  cases

theorem digitBeq ∀ (first: Char)
    (digit: first.isAsciiDigit = True):
    (first == '-') = False ∧ (first == '>') = False ∧ (first == '=') = False :=
  cases

--| An expression's first token that isn't `-` starts with a character that is no `-`, `>` or `=`.
theorem leadsHead ∀ (text: Text)
    (leads: Leads text)
    (notMinus: (text == "-") = False):
    ∃ (first: Char) (others: List Char) => text.toList = [first, ..others]
      ∧ (first == '-') = False
      ∧ (first == '>') = False
      ∧ (first == '=') = False :=
  match leads with
    | Inl same => ('(', [], (rewrite same), byComputing, byComputing, byComputing)
    | Inr (Inl same) => ('[', [], (rewrite same), byComputing, byComputing, byComputing)
    | Inr (Inr (Inl same)) =>
      (Bool.falseNotTrue (rewrite same at notMinus then Eq.trans notMinus.flipped byComputing)).impossible
    | Inr (Inr (Inr (Inl same))) => ('!', [], (rewrite same), byComputing, byComputing, byComputing)
    | Inr (Inr (Inr (Inr (Inl same)))) => ('¬', [], (rewrite same), byComputing, byComputing, byComputing)
    | Inr
        (Inr
          (Inr (Inr (Inr (Inl (Witness first (Witness others (Witness comps (Both split (Both starts rest)))))))))) =>
      let (dash, greater, equals) := startBeq first starts
      (first, others ++ qualChars comps, split, dash, greater, equals)
    | Inr
        (Inr
          (Inr
            (Inr
              (Inr (Inr (Inl (Witness first (Witness others (Witness comps (Both split (Both starts rest))))))))))) =>
      let (dash, greater, equals) := startBeq first starts
      (first, others ++ qualChars comps, split, dash, greater, equals)
    | Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inl (Witness first (Witness others (Both split (Both digit rest))))))))))) =>
      let (dash, greater, equals) := digitBeq first digit
      (first, others, split, dash, greater, equals)
    | Inr
        (Inr
          (Inr
            (Inr
              (Inr
                (Inr (Inr (Inr (Witness first (Witness others (Witness tail (Both split (Both digit rest)))))))))))) =>
      let (dash, greater, equals) := digitBeq first digit
      (first, others ++ tail, split, dash, greater, equals)

theorem digitWordChar ∀ (first: Char) (digit: first.isAsciiDigit = True): isWordChar first = True := cases

theorem digitNotI ∀ (first: Char) (digit: first.isAsciiDigit = True): (first == 'i') = False := cases

--| A name no keyword spells isn't `in` (so `!in` isn't read as `!in`'s operator).
theorem wordNotIn ∀ (kind: Tok) (text: Text) (first: Char) (others: List Char)
    (split: text.toList = [first, ..others])
    (starts: isWordStart first = True)
    (word: others.all isWordChar = True)
    (kinded: wordKind False text = kind)
    (notIn: wordKind False "in" ≠ kind):
    text.toList.takeWhile isWordChar ≠ ['i', 'n'] :=
  same =>
    let whole: text.toList.takeWhile isWordChar = text.toList :=
      rewrite split, Syntax.SharedFacts.wordStartChar first starts, List.takeWhileOfAll isWordChar others word
    let named: text = "in" := Eq.trans (Text.fromToList text).flipped (rewrite (Eq.trans whole.flipped same))
    notIn (rewrite named at kinded then kinded)

--| A name, plain or qualified, isn't `in` where it starts.
theorem nameNotIn ∀ (kind: Tok) (text: Text) (first: Char) (others: List Char) (comps: List (Pair Char (List Char)))
    (split: text.toList = [first, ..others] ++ qualChars comps)
    (starts: isWordStart first = True)
    (word: others.all isWordChar = True)
    (tail: QualTail first.isAsciiUppercase comps)
    (kinded: NameKind kind text comps)
    (notIn: wordKind False "in" ≠ kind):
    text.toList.takeWhile isWordChar ≠ ['i', 'n'] :=
  match comps, split, tail, kinded with
    | [], split, tail, kinded =>
      wordNotIn kind text first others (Eq.trans split (List.appendNil [first, ..others])) starts word kinded notIn
    | [(letter, letters), ..more], split, Both isUpper rest, kinded => same =>
      let whole: text.toList.takeWhile isWordChar = [first, ..others] :=
        rewrite split then
          List.takeWhileAppendThenStops isWordChar
            [first, ..others]
            (qualChars [(letter, letters), ..more])
            (Bool.andIntro (Syntax.SharedFacts.wordStartChar first starts) word)
            byComputing
      let head := List.consInjectiveHead first 'i' others ['n'] (Eq.trans whole.flipped same)
      let notUpper: first.isAsciiUppercase = False := rewrite head
      Bool.falseNotTrue (Eq.trans notUpper.flipped isUpper)

--| What follows `!`: nothing that makes it the operator `!in`.
theorem leadsNotIn ∀ (text: Text) (leads: Leads text): text.toList.takeWhile isWordChar ≠ ['i', 'n'] := match leads with
  | Inl same => rewrite same then byDecision
  | Inr (Inl same) => rewrite same then byDecision
  | Inr (Inr (Inl same)) => rewrite same then byDecision
  | Inr (Inr (Inr (Inl same))) => rewrite same then byDecision
  | Inr (Inr (Inr (Inr (Inl same)))) => rewrite same then byDecision
  | Inr
      (Inr
        (Inr
          (Inr
            (Inr
              (Inl
                (Witness first
                  (Witness others (Witness comps (Both split (Both starts (Both word (Both tail kinded)))))))))))) =>
    nameNotIn Lower text first others comps split starts word tail kinded byDecision
  | Inr
      (Inr
        (Inr
          (Inr
            (Inr
              (Inr
                (Inl
                  (Witness first
                    (Witness others (Witness comps (Both split (Both starts (Both word (Both tail kinded))))))))))))) =>
    nameNotIn Upper text first others comps split starts word tail kinded byDecision
  | Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inl (Witness first (Witness others (Both split (Both digit rest))))))))))) =>
    same =>
      let wordChar := digitWordChar first digit
      let head := List.consInjectiveHead first 'i' _ ['n'] (rewrite split, wordChar at same then same)
      DecEq.soundFalse first 'i' (digitNotI first digit) head
  | Inr
      (Inr
        (Inr
          (Inr
            (Inr (Inr (Inr (Inr (Witness first (Witness others (Witness tail (Both split (Both digit rest)))))))))))) =>
    same =>
      let wordChar := digitWordChar first digit
      let head := List.consInjectiveHead first 'i' _ ['n'] (rewrite split, wordChar at same then same)
      DecEq.soundFalse first 'i' (digitNotI first digit) head

theorem minusFollows ∀ (text: Text)
    (leads: Leads text)
    (notMinus: (text == "-") = False):
    MayFollow Minus "-" text.toList :=
  let (first, others, split, dash, greater, equals) := leadsHead text leads notMinus
  (
    List.headNeOfHead text.toList first '-' (rewrite split) (Char.neOfBeqFalse first '-' dash),
    List.headNeOfHead text.toList first '>' (rewrite split) (Char.neOfBeqFalse first '>' greater)
  )

theorem leadsNotEquals ∀ (text: Text) (leads: Leads text): text.toList.head ≠ Some '=' := match dash: text == "-" with
  | True => rewrite DecEq.sound dash then byDecision
  | False =>
    let (first, others, split, dash, greater, equals) := leadsHead text leads dash
    List.headNeOfHead text.toList first '=' (rewrite split) (Char.neOfBeqFalse first '=' equals)

theorem bangFollows ∀ (text: Text) (leads: Leads text): MayFollow Bang "!" text.toList := same =>
  (leadsNotEquals text leads, leadsNotIn text leads)

--| What a prefix operator is: `-`, `!` or `¬`.
def PrefixSpells (text: Text): Prop := text = "-" ∨ text = "!" ∨ text = "¬"

--| A prefix operator's operand may follow it where the rules write no gap.
theorem prefixFollows ∀ (operator: Word) (operand: Expr)
    (within: operand.within1 = True)
    (prefix: PrefixSpells operator.text)
    (leads: Leads operand.lead.text)
    (empty: (prefixGap operator operand).isEmpty = True):
    Follows lexKind operator.text operand.lead.text :=
  match spaced: operator.text == "-" && (operand.firstWord.text == "-" || operand.numeralApplication) with
    | False =>
      match prefix with
        | Inl same =>
          let first := Bool.orFalseLeft _ _ (rewrite same at spaced then spaced)
          rewrite same then
            (byComputing, minusFollows operand.lead.text leads (rewrite <- firstWordLead operand within then first))
        | Inr (Inl same) => rewrite same then (byComputing, bangFollows operand.lead.text leads)
        | Inr (Inr same) =>
          rewrite same then (byComputing, (isBang => (DecEq.soundFalse "¬" "!" byComputing isBang).impossible))

-- A name or numeral's spelling, from `within1`.

--| What `qualScan1` reads from a name's characters after the first is a run of word characters and the components
--| `qualified` reads.
theorem scanComps ∀ (chars: List Char) (upper last result: Bool)
    (scan: qualScan1 upper last chars = Some result):
    ∃ (run: List Char) (comps: List (Pair Char (List Char))) => chars = run ++ qualChars comps
      ∧ run.all isWordChar = True
      ∧ QualTail upper comps
      ∧ qualLast last comps = result :=
  match chars with
    | [] => ([], [], byComputing, byComputing, byComputing, Option.someInjective scan)
    | [char, ..more] =>
      match word: isWordChar char with
        | True =>
          let (run, comps, split, runWord, tail, found) := scanComps more upper last result scan
          ([char, ..run], comps, (rewrite split), Bool.andIntro word runWord, tail, found)
        | False =>
          match dot: char == '.' with
            | True =>
              match more with
                | [next, ..rest] =>
                  match start: upper && next.isAsciiLetter with
                    | True =>
                      let (run, comps, split, runWord, tail, found) :=
                        scanComps rest next.isAsciiUppercase next.isAsciiUppercase result scan
                      (
                        [],
                        [(next, run), ..comps],
                        (rewrite DecEq.sound dot, split),
                        byComputing,
                        (Bool.andLeft start, Bool.andRight start, runWord, tail),
                        found
                      )

--| A name's text, as `textSpells1` reads it, is one `Spells` says.
theorem nameSpells ∀ (kind: Tok) (text: Text) (chars: List Char)
    (same: text.toList = chars)
    (spells: nameText1 kind chars = True)
    (rightKind: (if kind == Upper then Upper else Lower) = kind):
    ∃ (first: Char) (others: List Char) (comps: List (Pair Char (List Char))) => text.toList
      = [first, ..others] ++ qualChars comps
      ∧ isWordStart first = True
      ∧ others.all isWordChar = True
      ∧ QualTail first.isAsciiUppercase comps
      ∧ NameKind kind text comps :=
  match chars, same, spells with
    | [first, ..others], same, spells =>
      let named: text = Text.fromList [first, ..others] := Eq.trans (Text.fromToList text).flipped (rewrite same)
      let starts := Bool.andLeft spells
      match word: others.all isWordChar with
        | True => (
          first,
          others,
          [],
          Eq.trans same (List.appendNil [first, ..others]).flipped,
          starts,
          word,
          byComputing,
          (rewrite named then DecEq.sound (Bool.andRight spells))
        )
        | False =>
          let scan := DecEq.sound (Bool.andRight spells)
          let (run, comps, split, runWord, tail, found) :=
            scanComps others first.isAsciiUppercase first.isAsciiUppercase (kind == Upper) scan
          match comps with
            | [] =>
              (Bool.falseNotTrue (Eq.trans word.flipped (rewrite split, List.appendNil run then runWord))).impossible
            | [(letter, letters), ..more] => (
              first,
              run,
              [(letter, letters), ..more],
              (rewrite same, split),
              starts,
              runWord,
              tail,
              (kind == Upper, Eq.trans (qualFoundSome letter.isAsciiUppercase more) (rewrite found), rightKind)
            )

theorem digitsSpells ∀ (text: Text) (chars: List Char)
    (same: text.toList = chars)
    (spells: numberText1 chars = True):
    ∃ (first: Char) (others: List Char) => text.toList = [first, ..others]
      ∧ first.isAsciiDigit = True
      ∧ others.all Char.isAsciiDigit = True :=
  match chars, same, spells with
    | [first, ..others], same, spells => (first, others, same, Bool.andLeft spells, Bool.andRight spells)

--| An exponent's text, as `exponentText1` reads it, is one `ExponentAs` says.
theorem exponentSpells ∀ (chars: List Char) (spells: exponentText1 chars = True): ExponentAs chars :=
  match chars, spells with
    | [marker, ..more], spells =>
      let isMarker := Bool.andLeft spells
      let digits := Bool.andRight spells
      match more, digits with
        | [char, ..rest], digits =>
          match sign: (char == '+' || char == '-') with
            | True =>
              match rest, digits with
                | [first, ..others], digits => Inr (
                  marker,
                  char,
                  first,
                  others,
                  byComputing,
                  isMarker,
                  sign,
                  Bool.andLeft digits,
                  Bool.andRight digits
                )
            | False => Inl (marker, char, rest, byComputing, isMarker, Bool.andLeft digits, Bool.andRight digits)

--| What `fractionRest1` reads after a fraction's first digit: digits, then perhaps an exponent.
theorem fractionRestSpells ∀ (chars: List Char)
    (spells: fractionRest1 chars = True):
    ∃ (digits: List Char) (exponent: List Char) => chars = digits ++ exponent
      ∧ digits.all Char.isAsciiDigit = True
      ∧ (exponent = [] ∨ ExponentAs exponent) :=
  match chars with
    | [] => ([], [], byComputing, byComputing, Inl byComputing)
    | [char, ..rest] =>
      match digit: char.isAsciiDigit with
        | True =>
          let (digits, exponent, split, all, shape) := fractionRestSpells rest spells
          ([char, ..digits], exponent, (rewrite split), Bool.andIntro digit all, shape)
        | False => ([], [char, ..rest], byComputing, byComputing, Inr (exponentSpells [char, ..rest] spells))

--| What `floatRest1` reads after a float's first digit is digits and a tail of a float.
theorem floatRestSpells ∀ (chars: List Char)
    (spells: floatRest1 chars = True):
    ∃ (digits: List Char) (tail: List Char) => chars = digits ++ tail
      ∧ digits.all Char.isAsciiDigit = True
      ∧ FloatTailAs tail :=
  match chars with
    | [char, ..rest] =>
      match digit: char.isAsciiDigit with
        | True =>
          let (digits, tail, split, all, shape) := floatRestSpells rest spells
          ([char, ..digits], tail, (rewrite split), Bool.andIntro digit all, shape)
        | False =>
          match dot: char == '.' with
            | True =>
              match rest, spells with
                | [second, ..more], spells =>
                  let (digits, exponent, split, all, shape) := fractionRestSpells more (Bool.andRight spells)
                  let fraction: FractionAs ['.', second, ..digits] :=
                    (second, digits, byComputing, Bool.andLeft spells, all)
                  match shape with
                    | Inl none =>
                      let moreIs: more = digits := rewrite split, none then List.appendNil digits
                      (
                        [],
                        ['.', second, ..more],
                        (rewrite DecEq.sound dot),
                        byComputing,
                        Inr (Inl (second, more, byComputing, Bool.andLeft spells, rewrite moreIs then all))
                      )
                    | Inr exponentShape => (
                      [],
                      ['.', second, ..more],
                      (rewrite DecEq.sound dot),
                      byComputing,
                      Inl (['.', second, ..digits], exponent, (rewrite split), fraction, exponentShape)
                    )
            | False => ([], [char, ..rest], byComputing, byComputing, Inr (Inr (exponentSpells [char, ..rest] spells)))

--| A name or numeral `within1` lets through is a text its kind is spelled with.
theorem spellsOfText1 ∀ (kind: Tok) (text: Text) (spells: textSpells1 kind text = True): Spells kind text :=
  match kind, spells with
    | Lower, spells => nameSpells Lower text text.toList byComputing spells byComputing
    | Upper, spells => nameSpells Upper text text.toList byComputing spells byComputing
    | Num, spells => digitsSpells text text.toList byComputing spells
    | Float, spells =>
      match text.toList, spells with
        | [first, ..rest], spells =>
          let (digits, tail, split, all, shape) := floatRestSpells rest (Bool.andRight spells)
          (first, digits, tail, (rewrite split), Bool.andLeft spells, all, shape)
    | other, spells => (Bool.falseNotTrue spells).impossible

-- The tree's spellings.

--| An infix operator's text spells a token that is no comma or closer.
def OperatorSpells (text: Text): Prop := ∃ (kind: Tok) => Spells kind text ∧ Quiet kind

--| What the parser's leaves spell, which `lexical1` doesn't say (the header): each name and numeral is a text its
--| kind is spelled with, each infix operator a token's and each prefix operator `-`, `!` or `¬`.
def Expr.operators1: Expr → Prop
  | Atom _ _ => True
  | Paren _ inner _ => inner.operators1
  | Tuple _ items _ _ => AllOperators1 items
  | ListOf _ items _ _ => AllOperators1 items
  | App head arguments => head.operators1 ∧ AllOperators1 arguments
  | Infix _ left operator right => left.operators1 ∧ OperatorSpells operator.text ∧ right.operators1
  | Prefix operator operand => PrefixSpells operator.text ∧ operand.operators1
  | _ => False

def AllOperators1: List Expr → Prop
  | [] => True
  | [expr, ..rest] => expr.operators1 ∧ AllOperators1 rest

def Decl.operators1: Decl → Prop
  | Definition _ header (Assigned _ value) => header.result.operators1 ∧ value.operators1
  | _ => False

--| An infix operator `within1` lets through is a text some token of the alphabet is spelled with.
--|
--| Proof idea: `operatorText1` is four chains of tests of the text against each spelling; the first chain that holds
--| (`operatorSpellsA` and the rest) has a test that names the token, and a chain running out contradicts the hypothesis.
theorem operatorSpellsA ∀ (text: Text) (listed: operatorTextA1 text = True): OperatorSpells text :=
  match a0: text == "->" with
    | True => Witness Arrow (Both (Inl (DecEq.sound a0)) byDecision)
    | False =>
      match a1: text == "→" with
        | True => Witness Arrow (Both (Inr (DecEq.sound a1)) byDecision)
        | False =>
          match a2: text == "||" with
            | True => Witness OrOr (Both (Inl (DecEq.sound a2)) byDecision)
            | False =>
              match a3: text == "∨" with
                | True => Witness OrOr (Both (Inr (DecEq.sound a3)) byDecision)
                | False =>
                  match a4: text == "&&" with
                    | True => Witness AndAnd (Both (Inl (DecEq.sound a4)) byDecision)
                    | False =>
                      match a5: text == "∧" with
                        | True => Witness AndAnd (Both (Inr (DecEq.sound a5)) byDecision)

theorem operatorSpellsB ∀ (text: Text) (listed: operatorTextB1 text = True): OperatorSpells text :=
  match a0: text == "+" with
    | True => Witness Plus (Both (DecEq.sound a0) byDecision)
    | False =>
      match a1: text == "++" with
        | True => Witness PlusPlus (Both (DecEq.sound a1) byDecision)
        | False =>
          match a2: text == "-" with
            | True => Witness Minus (Both (DecEq.sound a2) byDecision)
            | False =>
              match a3: text == "*" with
                | True => Witness Star (Both (DecEq.sound a3) byDecision)
                | False =>
                  match a4: text == "/" with
                    | True => Witness Slash (Both (DecEq.sound a4) byDecision)
                    | False =>
                      match a5: text == "%" with
                        | True => Witness Percent (Both (DecEq.sound a5) byDecision)

theorem operatorSpellsC ∀ (text: Text) (listed: operatorTextC1 text = True): OperatorSpells text :=
  match a0: text == "!=" with
    | True => Witness NotEq (Both (Inl (DecEq.sound a0)) byDecision)
    | False =>
      match a1: text == "≠" with
        | True => Witness NotEq (Both (Inr (DecEq.sound a1)) byDecision)
        | False =>
          match a2: text == "<" with
            | True => Witness Lt (Both (DecEq.sound a2) byDecision)
            | False =>
              match a3: text == "<=" with
                | True => Witness Le (Both (Inl (DecEq.sound a3)) byDecision)
                | False =>
                  match a4: text == "≤" with
                    | True => Witness Le (Both (Inr (DecEq.sound a4)) byDecision)

theorem operatorSpellsD ∀ (text: Text) (listed: operatorTextD1 text = True): OperatorSpells text :=
  match a0: text == ">" with
    | True => Witness Gt (Both (DecEq.sound a0) byDecision)
    | False =>
      match a1: text == ">=" with
        | True => Witness Ge (Both (Inl (DecEq.sound a1)) byDecision)
        | False =>
          match a2: text == "≥" with
            | True => Witness Ge (Both (Inr (DecEq.sound a2)) byDecision)
            | False =>
              match a3: text == "==" with
                | True => Witness EqEq (Both (DecEq.sound a3) byDecision)
                | False =>
                  match a4: text == "=" with
                    | True => Witness Equals (Both (DecEq.sound a4) byDecision)

theorem operatorSpellsOf ∀ (text: Text) (listed: operatorText1 text = True): OperatorSpells text :=
  match first: operatorTextA1 text with
    | True => operatorSpellsA text first
    | False =>
      match second: operatorTextB1 text with
        | True => operatorSpellsB text second
        | False =>
          match third: operatorTextC1 text with
            | True => operatorSpellsC text third
            | False => operatorSpellsD text listed

--| A prefix operator `within1` lets through is `-`, `!` or `¬`.
theorem prefixSpellsOf ∀ (text: Text) (listed: prefixText1 text = True): PrefixSpells text :=
  match minus: text == "-" with
    | True => Inl (DecEq.sound minus)
    | False =>
      match bang: text == "!" with
        | True => Inr (Inl (DecEq.sound bang))
        | False =>
          match not: text == "¬" with
            | True => Inr (Inr (DecEq.sound not))

--| What `within1` says of an expression's operators is `operators1`: the slice's alphabet spells each.
--|
--| Proof idea: Induction on the expression; an operator is `operatorSpellsOf` or `prefixSpellsOf`.
theorem withinOperators ∀ (expr: Expr) (within: expr.within1 = True): expr.operators1 := match expr, within with
  | Atom kind word, within => byComputing
  | Paren open inner close, within => withinOperators inner within
  | Tuple open items comma close, within => allWithinOperators items within
  | ListOf open items comma close, within => allWithinOperators items within
  | App head arguments, within =>
    (withinOperators head (Bool.andLeft within), allWithinOperators arguments (Bool.andRight within))
  | Infix kind left operator right, within =>
    match kind with
      | InfixBinary => (
        withinOperators left (Bool.andLeft within),
        operatorSpellsOf operator.text (Bool.andLeft (Bool.andRight (Bool.andRight within))),
        withinOperators right (Bool.andLeft (Bool.andRight within))
      )
      | InfixArrow => (
        withinOperators left (Bool.andLeft within),
        operatorSpellsOf operator.text (arrowListed operator.text (Bool.andRight (Bool.andRight within))),
        withinOperators right (Bool.andLeft (Bool.andRight within))
      )
      | _ => cases
  | Prefix operator operand, within =>
    (prefixSpellsOf operator.text (Bool.andRight within), withinOperators operand (Bool.andLeft within))

theorem allWithinOperators ∀ (items: List Expr) (within: allWithin1 items = True): AllOperators1 items :=
  match items with
    | [] => byComputing
    | [item, ..rest] => (withinOperators item (Bool.andLeft within), allWithinOperators rest (Bool.andRight within))

theorem declOperators ∀ (decl: Decl) (within: decl.within1 = True): decl.operators1 := match decl with
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
        (withinOperators result (Bool.andRight (Bool.andLeft within)), withinOperators value (Bool.andRight within))
      | _ => cases

theorem wordQuiet ∀ (kind: Tok) (word: kind.wordWithin1 = True): Quiet kind := match kind, word with
  | Lower, word => byDecision
  | Upper, word => byDecision
  | Num, word => byDecision
  | Float, word => byDecision
  | other, word => (Bool.falseNotTrue word).impossible

theorem minusQuiet: Quiet Minus := byDecision

theorem bangQuiet: Quiet Bang := byDecision

theorem lowerQuiet: Quiet Lower := byDecision

theorem upperQuiet: Quiet Upper := byDecision

--| A header's name that `within1` lets through spells a token of one of the two name kinds.
theorem nameKinded ∀ (name: Word)
    (within: name.nameWithin1 = True):
    ∃ (kind: Tok) => Spells kind name.text ∧ Quiet kind ∧ (kind = Lower ∨ kind = Upper) :=
  match (Bool.orReads _ _).forward within with
    | Inl lower => (Lower, spellsOfText1 Lower name.text (Bool.andRight lower), lowerQuiet, Inl byComputing)
    | Inr upper => (Upper, spellsOfText1 Upper name.text (Bool.andRight upper), upperQuiet, Inr byComputing)

--| Where the first token of an expression is `-`, `!`, `¬`, a bracket, or spelled as a name or numeral.
--|
--| Proof idea: Induction down the first operands.
theorem leadsOf ∀ (expr: Expr)
    (within: expr.within1 = True)
    (lexical: expr.lexical1 = True) (spelled: expr.operators1):
    Leads expr.lead.text :=
  match expr, spelled with
    | Atom kind word, _ =>
      match kind, within with
        | Lower, within => Inr (Inr (Inr (Inr (Inr (Inl (spellsOfText1 Lower word.text within))))))
        | Upper, within => Inr (Inr (Inr (Inr (Inr (Inr (Inl (spellsOfText1 Upper word.text within)))))))
        | Num, within => Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inl (spellsOfText1 Num word.text within))))))))
        | Float, within => Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inr (spellsOfText1 Float word.text within))))))))
        | other, within => (Bool.falseNotTrue within).impossible
    | Paren open inner close, _ => Inl (DecEq.sound (Bool.andLeft lexical))
    | Tuple open items comma close, _ => Inl (DecEq.sound (Bool.andLeft lexical))
    | ListOf open items comma close, _ => Inr (Inl (DecEq.sound (Bool.andLeft lexical)))
    | App head arguments, (headSpells, _) => leadsOf head (Bool.andLeft within) (Bool.andLeft lexical) headSpells
    | Infix kind left operator right, (leftSpells, _) =>
      match kind with
        | InfixBinary => leadsOf left (Bool.andLeft within) (Bool.andLeft lexical) leftSpells
        | InfixArrow => leadsOf left (Bool.andLeft within) (Bool.andLeft lexical) leftSpells
        | _ => cases
    | Prefix operator operand, (Inl same, _) => Inr (Inr (Inl same))
    | Prefix operator operand, (Inr (Inl same), _) => Inr (Inr (Inr (Inl same)))
    | Prefix operator operand, (Inr (Inr same), _) => Inr (Inr (Inr (Inr (Inl same))))

theorem notNil ∀ (arguments: List Expr) (filled: (¬arguments.isEmpty) = True): arguments ≠ [] := same =>
  (Bool.falseNotTrue (rewrite same at filled then filled)).impossible

--| An opening bracket spelled as a token of a kind that may be followed by anything.
theorem bracketOpener ∀ (open: Word) (kind: Tok)
    (sound: open.sound = True)
    (spells: Spells kind open.text)
    (quiet: Quiet kind)
    (free: ∀ (text: Text) (rest: List Char) => MayFollow kind text rest):
    OpenerJoins lexKind open :=
  (
    spellsJoins open kind sound spells quiet,
    next =>
      (
        spellsNotComment kind open.text spells,
        rewrite lexKindOfSpells kind open.text spells then free open.text next.toList
      )
  )

theorem infixWithin ∀ (kind: InfixKind) (left: Expr) (operator: Word) (right: Expr)
    (within: (Infix kind left operator right).within1 = True):
    left.within1 = True ∧ right.within1 = True :=
  match kind with
    | InfixBinary => (Bool.andLeft within, Bool.andLeft (Bool.andRight within))
    | InfixArrow => (Bool.andLeft within, Bool.andLeft (Bool.andRight within))

--| An arrow's text is one of slice 1's operators.
theorem arrowListed ∀ (text: Text) (arrow: arrowText1 text = True): operatorText1 text = True :=
  match a0: text == "->" with
    | True => byComputing
    | False =>
      match a1: text == "→" with
        | True => byComputing

theorem arrowListedExample: operatorText1 "→" = True := arrowListed "→" byComputing

--| The operator of an infix `within1` lets through is one of slice 1's.
theorem infixListed ∀ (kind: InfixKind) (left: Expr) (operator: Word) (right: Expr)
    (within: (Infix kind left operator right).within1 = True):
    operatorText1 operator.text = True :=
  match kind with
    | InfixBinary => Bool.andLeft (Bool.andRight (Bool.andRight within))
    | InfixArrow => arrowListed operator.text (Bool.andRight (Bool.andRight within))

--| `printLexes1`'s facts about the tokens of an expression, from the tree's.
--|
--| Proof idea: Induction on the expression; each token is `spellsJoins` of its spelling (an opening bracket
--| `bracketOpener`, a closing one by its text), an application's arguments are not empty by `shaped1`, and a prefix
--| operator's operand may follow it by `prefixFollows`.
theorem joinable ∀ (expr: Expr)
    (within: expr.within1 = True)
    (shaped: expr.shaped1 = True)
    (sound: expr.sound = True)
    (lexical: expr.lexical1 = True) (spelled: expr.operators1):
    Joinable lexKind expr :=
  match expr, spelled with
    | Atom kind word, _ =>
      spellsJoins word kind sound
        (spellsOfText1 kind word.text (Bool.andRight within))
        (wordQuiet kind (Bool.andLeft within))
    | Paren open inner close, innerSpelled => (
      bracketOpener open LParen (Bool.andLeft sound) (DecEq.sound (Bool.andLeft lexical)) byDecision (text rest =>
        byComputing),
      (Bool.andRight (Bool.andRight sound), rewrite DecEq.sound (Bool.andLeft (Bool.andRight lexical))),
      joinable inner within shaped
        (Bool.andLeft (Bool.andRight sound))
        (Bool.andRight (Bool.andRight lexical))
        innerSpelled
    )
    | Tuple open items comma close, itemsSpelled => (
      bracketOpener open LParen (Bool.andLeft sound) (DecEq.sound (Bool.andLeft lexical)) byDecision (text rest =>
        byComputing),
      (Bool.andRight (Bool.andRight sound), rewrite DecEq.sound (Bool.andLeft (Bool.andRight lexical))),
      allJoinable items within
        (Bool.andRight shaped)
        (Bool.andLeft (Bool.andRight sound))
        (Bool.andRight (Bool.andRight lexical))
        itemsSpelled
    )
    | ListOf open items comma close, itemsSpelled => (
      bracketOpener open LBracket (Bool.andLeft sound) (DecEq.sound (Bool.andLeft lexical)) byDecision (text rest =>
        byComputing),
      (Bool.andRight (Bool.andRight sound), rewrite DecEq.sound (Bool.andLeft (Bool.andRight lexical))),
      allJoinable items within shaped
        (Bool.andLeft (Bool.andRight sound))
        (Bool.andRight (Bool.andRight lexical))
        itemsSpelled
    )
    | App head arguments, (headSpelled, argumentsSpelled) => (
      joinable head
        (Bool.andLeft within)
        (Bool.andLeft (Bool.andRight shaped))
        (Bool.andLeft sound)
        (Bool.andLeft lexical)
        headSpelled,
      allJoinable arguments
        (Bool.andRight within)
        (Bool.andRight (Bool.andRight (Bool.andRight (Bool.andRight shaped))))
        (Bool.andRight sound)
        (Bool.andRight lexical)
        argumentsSpelled,
      notNil arguments (Bool.andLeft (Bool.andRight (Bool.andRight shaped)))
    )
    | Infix kind left operator right, (leftSpelled, (kindOfOperator, (operatorSpells, quiet)), rightSpelled) =>
      let (leftWithin, rightWithin) := infixWithin kind left operator right within
      (
        joinable left leftWithin (Bool.andLeft shaped) (Bool.andLeft sound) (Bool.andLeft lexical) leftSpelled,
        spellsJoins operator kindOfOperator (Bool.andLeft (Bool.andRight sound)) operatorSpells quiet,
        joinable right rightWithin
          (Bool.andLeft (Bool.andRight shaped))
          (Bool.andRight (Bool.andRight sound))
          (Bool.andRight (Bool.andRight lexical))
          rightSpelled
      )
    | Prefix operator operand, (prefix, operandSpelled) =>
      let operatorSound := Bool.andLeft sound
      (
        match prefix with
          | Inl same => spellsJoins operator Minus operatorSound same minusQuiet
          | Inr (Inl same) => spellsJoins operator Bang operatorSound (Inl same) bangQuiet
          | Inr (Inr same) => spellsJoins operator Bang operatorSound (Inr same) bangQuiet,
        joinable operand
          (Bool.andLeft within)
          (Bool.andLeft shaped)
          (Bool.andRight sound)
          (Bool.andRight lexical)
          operandSpelled,
        empty =>
          prefixFollows operator operand
            (Bool.andLeft within)
            prefix
            (leadsOf operand (Bool.andLeft within) (Bool.andRight lexical) operandSpelled)
            empty
      )

theorem allJoinable ∀ (items: List Expr)
    (within: allWithin1 items = True)
    (shaped: allShaped1 items = True)
    (sound: allSound items = True)
    (lexical: allLexical1 items = True)
    (spelled: AllOperators1 items):
    AllJoinable lexKind items :=
  match items, spelled with
    | [], _ => byComputing
    | [item, ..rest], (first, others) => (
      joinable item (Bool.andLeft within) (Bool.andLeft shaped) (Bool.andLeft sound) (Bool.andLeft lexical) first,
      allJoinable rest
        (Bool.andRight within)
        (Bool.andRight shaped)
        (Bool.andRight sound)
        (Bool.andRight lexical)
        others
    )

-- The printed texts.

--| A comment as rule N leaves it is a piece the lexer proofs can read.
theorem commentPrintable ∀ (kinds: Text → Tok) (text: Text) (comment: commentText text = True): Printable kinds text :=
  Inr (Inl (Bool.andLeft comment, Bool.notTrue _ (Bool.andLeft (Bool.andRight comment))))

--| A token that spells its kind, as the rules print it, is a piece the lexer proofs can read.
theorem tokenPrintable ∀ (text: Text) (kind: Tok)
    (solid: isLayout text = False)
    (spells: Spells kind text):
    Printable lexKind text :=
  Inr (Inr (rewrite lexKindOfSpells kind text spells then spells, solid, spellsNotComment kind text spells))

theorem notesPrintable ∀ (notes: List Note)
    (sound: notesSound notes = True):
    Every (Printable lexKind) (notes.map (note => note.text)) :=
  match notes with
    | [] => byComputing
    | [note, ..rest] =>
      (commentPrintable lexKind note.text (Bool.andLeft sound), notesPrintable rest (Bool.andRight sound))

theorem afterPrintable ∀ (after: Option Text)
    (sound: afterSound after = True):
    Every (Printable lexKind) after.toList :=
  match after with
    | None => byComputing
    | Some comment => (commentPrintable lexKind comment sound, byComputing)

--| A token's own-line comments, text and trailing comment are pieces the lexer proofs can read.
theorem wordPrintable ∀ (word: Word) (kind: Tok) (hoisted: Bool)
    (sound: word.sound = True)
    (spells: Spells kind word.text):
    Every (Printable lexKind) (word.spelledAt hoisted) :=
  let solid := Bool.notTrue _ (Bool.andLeft sound)
  let notes := Bool.andLeft (Bool.andRight sound)
  let after := Bool.andRight (Bool.andRight sound)
  let text: Every (Printable lexKind) [word.text] := (tokenPrintable word.text kind solid spells, byComputing)
  let trailing := afterPrintable word.comments.after after
  let front: Every (Printable lexKind) (if hoisted then [] else word.comments.above.map (note => note.text)) :=
    match hoisted with
      | True => byComputing
      | False => notesPrintable word.comments.above notes
  everyAppend
    (Printable lexKind)
    (if hoisted then [] else word.comments.above.map (note => note.text))
    ([word.text] ++ word.comments.after.toList)
    front
    (everyAppend (Printable lexKind) [word.text] word.comments.after.toList text trailing)

theorem everyThree ∀ (holds: Text → Prop) (front middle back: List Text)
    (first: Every holds front)
    (second: Every holds middle)
    (third: Every holds back):
    Every holds (front ++ middle ++ back) :=
  everyAppend holds front (middle ++ back) first (everyAppend holds middle back second third)

theorem commaTextPrintable: Printable lexKind "," := tokenPrintable "," Comma byComputing byComputing

--| A bracket's items, with the commas between them, are pieces the lexer proofs can read.
theorem commaPrintable ∀ (items: List Expr)
    (within: allWithin1 items = True)
    (sound: allSound items = True)
    (lexical: allLexical1 items = True)
    (spelled: AllOperators1 items):
    Every (Printable lexKind) (commaSpelt items) :=
  match items, spelled with
    | [], _ => byComputing
    | [item], (first, _) =>
      exprPrintable item False (Bool.andLeft within) (Bool.andLeft sound) (Bool.andLeft lexical) first
    | [item, next, ..rest], (first, others) =>
      everyThree
        (Printable lexKind)
        (item.spelt False)
        [","]
        (commaSpelt [next, ..rest])
        (exprPrintable item False (Bool.andLeft within) (Bool.andLeft sound) (Bool.andLeft lexical) first)
        (commaTextPrintable, byComputing)
        (commaPrintable [next, ..rest] (Bool.andRight within) (Bool.andRight sound) (Bool.andRight lexical) others)

--| A call's arguments are pieces the lexer proofs can read.
theorem argumentsPrintable ∀ (arguments: List Expr)
    (within: allWithin1 arguments = True)
    (sound: allSound arguments = True)
    (lexical: allLexical1 arguments = True)
    (spelled: AllOperators1 arguments):
    Every (Printable lexKind) (argumentsSpelt arguments) :=
  match arguments, spelled with
    | [], _ => byComputing
    | [argument, ..rest], (first, others) =>
      everyAppend
        (Printable lexKind)
        (argument.spelt False)
        (argumentsSpelt rest)
        (exprPrintable argument False (Bool.andLeft within) (Bool.andLeft sound) (Bool.andLeft lexical) first)
        (argumentsPrintable rest (Bool.andRight within) (Bool.andRight sound) (Bool.andRight lexical) others)

--| The tokens of an expression, with their comments, are pieces the lexer proofs can read.
--|
--| Proof idea: Induction on the expression: each token by `wordPrintable` with its spelling, the pieces in order by
--| `everyAppend`.
theorem exprPrintable ∀ (expr: Expr) (hoisted: Bool)
    (within: expr.within1 = True)
    (sound: expr.sound = True)
    (lexical: expr.lexical1 = True) (spelled: expr.operators1):
    Every (Printable lexKind) (expr.spelt hoisted) :=
  match expr, spelled with
    | Atom kind word, _ => wordPrintable word kind hoisted sound (spellsOfText1 kind word.text (Bool.andRight within))
    | Paren open inner close, innerSpelled =>
      everyThree
        (Printable lexKind)
        (open.spelledAt hoisted)
        (inner.spelt False)
        (close.spelledAt False)
        (wordPrintable open LParen hoisted (Bool.andLeft sound) (DecEq.sound (Bool.andLeft lexical)))
        (exprPrintable inner False within
          (Bool.andLeft (Bool.andRight sound))
          (Bool.andRight (Bool.andRight lexical))
          innerSpelled)
        (wordPrintable close RParen False
          (Bool.andRight (Bool.andRight sound))
          (DecEq.sound (Bool.andLeft (Bool.andRight lexical))))
    | Tuple open items comma close, itemsSpelled =>
      everyThree
        (Printable lexKind)
        (open.spelledAt hoisted)
        (commaSpelt items)
        (close.spelledAt False)
        (wordPrintable open LParen hoisted (Bool.andLeft sound) (DecEq.sound (Bool.andLeft lexical)))
        (commaPrintable items within
          (Bool.andLeft (Bool.andRight sound))
          (Bool.andRight (Bool.andRight lexical))
          itemsSpelled)
        (wordPrintable close RParen False
          (Bool.andRight (Bool.andRight sound))
          (DecEq.sound (Bool.andLeft (Bool.andRight lexical))))
    | ListOf open items comma close, itemsSpelled =>
      everyThree
        (Printable lexKind)
        (open.spelledAt hoisted)
        (commaSpelt items)
        (close.spelledAt False)
        (wordPrintable open LBracket hoisted (Bool.andLeft sound) (DecEq.sound (Bool.andLeft lexical)))
        (commaPrintable items within
          (Bool.andLeft (Bool.andRight sound))
          (Bool.andRight (Bool.andRight lexical))
          itemsSpelled)
        (wordPrintable close RBracket False
          (Bool.andRight (Bool.andRight sound))
          (DecEq.sound (Bool.andLeft (Bool.andRight lexical))))
    | App head arguments, (headSpelled, argumentsSpelled) =>
      everyAppend
        (Printable lexKind)
        (head.spelt hoisted)
        (argumentsSpelt arguments)
        (exprPrintable head hoisted (Bool.andLeft within) (Bool.andLeft sound) (Bool.andLeft lexical) headSpelled)
        (argumentsPrintable arguments
          (Bool.andRight within)
          (Bool.andRight sound)
          (Bool.andRight lexical)
          argumentsSpelled)
    | Infix kind left operator right, (leftSpelled, (kindOfOperator, (operatorSpells, quiet)), rightSpelled) =>
      let (leftWithin, rightWithin) := infixWithin kind left operator right within
      everyThree
        (Printable lexKind)
        (left.spelt hoisted)
        (operator.spelledAt False)
        (right.spelt False)
        (exprPrintable left hoisted leftWithin (Bool.andLeft sound) (Bool.andLeft lexical) leftSpelled)
        (wordPrintable operator kindOfOperator False (Bool.andLeft (Bool.andRight sound)) operatorSpells)
        (exprPrintable right False rightWithin
          (Bool.andRight (Bool.andRight sound))
          (Bool.andRight (Bool.andRight lexical))
          rightSpelled)
    | Prefix operator operand, (prefix, operandSpelled) =>
      everyAppend
        (Printable lexKind)
        (operator.spelledAt hoisted)
        (operand.spelt False)
        (match prefix with
          | Inl same => wordPrintable operator Minus hoisted (Bool.andLeft sound) same
          | Inr (Inl same) => wordPrintable operator Bang hoisted (Bool.andLeft sound) (Inl same)
          | Inr (Inr same) => wordPrintable operator Bang hoisted (Bool.andLeft sound) (Inr same))
        (exprPrintable operand False (Bool.andLeft within) (Bool.andRight sound) (Bool.andRight lexical) operandSpelled)

-- A declaration.

--| `DeclJoins`, from the tree's facts.
--|
--| Proof idea: The keyword, colon and `:=` are fixed spellings, the name's spelling is `operators1`'s; the type and the
--| value are `joinable`.
theorem declJoins ∀ (decl: Decl)
    (within: decl.within1 = True)
    (shaped: decl.shaped1 = True)
    (sound: decl.sound = True)
    (lexical: decl.lexical1 = True) (spelled: decl.operators1):
    DeclJoins lexKind decl :=
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
          let (nameKind, nameSpelled, nameQuiet, nameIsName) := nameKinded name (Bool.andLeft (Bool.andLeft within))
          (
            spellsJoins (fixedWord "def" keyword) KwDef (Bool.andLeft sound) byComputing byDecision,
            spellsJoins name nameKind (Bool.andLeft (Bool.andRight sound)) nameSpelled nameQuiet,
            spellsJoins
              (fixedWord ":" colon)
              Colon
              (Bool.andLeft (Bool.andRight (Bool.andRight sound)))
              byComputing
              byDecision,
            joinable result
              (Bool.andRight (Bool.andLeft within))
              (Bool.andLeft shaped)
              (Bool.andLeft (Bool.andRight (Bool.andRight (Bool.andRight sound))))
              (Bool.andLeft (Bool.andRight lexical))
              resultSpelled,
            spellsJoins
              (fixedWord ":=" colonEq)
              ColonEq
              (Bool.andLeft (Bool.andRight (Bool.andRight (Bool.andRight (Bool.andRight sound)))))
              byComputing
              byDecision,
            joinable value
              (Bool.andRight within)
              (Bool.andRight shaped)
              (Bool.andRight (Bool.andRight (Bool.andRight (Bool.andRight (Bool.andRight sound)))))
              (Bool.andRight (Bool.andRight lexical))
              valueSpelled
          )
        | _ => cases

--| The tokens of a declaration, with their comments, are pieces the lexer proofs can read.
theorem declPrintable ∀ (decl: Decl)
    (within: decl.within1 = True)
    (sound: decl.sound = True)
    (lexical: decl.lexical1 = True) (spelled: decl.operators1):
    Every (Printable lexKind) decl.spelt :=
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
          let (nameKind, nameSpelled, nameQuiet, nameIsName) := nameKinded name (Bool.andLeft (Bool.andLeft within))
          let keywordWord := fixedWord "def" keyword
          let colonWord := fixedWord ":" colon
          let assignWord := fixedWord ":=" colonEq
          everyAppend
            (Printable lexKind)
            ((keywordWord.spelledAt True ++ name.spelledAt False) ++ colonWord.spelledAt False ++ result.spelt False)
            (assignWord.spelledAt False ++ value.spelt False)
            (everyAppend
              (Printable lexKind)
              (keywordWord.spelledAt True ++ name.spelledAt False)
              (colonWord.spelledAt False ++ result.spelt False)
              (everyAppend
                (Printable lexKind)
                (keywordWord.spelledAt True)
                (name.spelledAt False)
                (wordPrintable keywordWord KwDef True (Bool.andLeft sound) byComputing)
                (wordPrintable name nameKind False (Bool.andLeft (Bool.andRight sound)) nameSpelled))
              (everyAppend
                (Printable lexKind)
                (colonWord.spelledAt False)
                (result.spelt False)
                (wordPrintable colonWord Colon False (Bool.andLeft (Bool.andRight (Bool.andRight sound))) byComputing)
                (exprPrintable result False
                  (Bool.andRight (Bool.andLeft within))
                  (Bool.andLeft (Bool.andRight (Bool.andRight (Bool.andRight sound))))
                  (Bool.andLeft (Bool.andRight lexical))
                  resultSpelled)))
            (everyAppend
              (Printable lexKind)
              (assignWord.spelledAt False)
              (value.spelt False)
              (wordPrintable assignWord ColonEq False
                (Bool.andLeft (Bool.andRight (Bool.andRight (Bool.andRight (Bool.andRight sound)))))
                byComputing)
              (exprPrintable value False
                (Bool.andRight within)
                (Bool.andRight (Bool.andRight (Bool.andRight (Bool.andRight (Bool.andRight sound)))))
                (Bool.andRight (Bool.andRight lexical))
                valueSpelled))
        | _ => cases

--| `printLexes1Tree`: the text the rules print for a slice 1 declaration, at any width, lexes to the leaves of the
--| printed pieces' layout, from the declaration's tree facts: that it is within slice 1, sound, shaped as the parser
--| gives it, and its leaves lex as their kinds. `kinds` is the lexer's kind of each text.
--|
--| Proof idea: `printLexes1`, with its two hypotheses derived: `declJoins` and `declPrintable`, from `declOperators`
--| (`within1` says each operator is one the alphabet spells).
theorem printLexes1Tree ∀ (decl: Decl) (doc: Doc) (width: Nat)
    (within: decl.within1 = True)
    (shaped: decl.shaped1 = True)
    (sound: decl.sound = True)
    (lexical: decl.lexical1 = True)
    (shows: decl.doc1 = Some doc):
    lex (Doc.print doc width)
      = Ok {
        leaves = ((pieceFold lexKind (printedPieces doc width)).foldLeft Laid.start Laid.lay).leaves.reverse,
        end = {
          leading = ((pieceFold lexKind (printedPieces doc width)).foldLeft Laid.start Laid.lay).pending.reverse,
          blankLines = ((pieceFold lexKind (printedPieces doc width)).foldLeft Laid.start Laid.lay).blankRun,
          trailing = None
        }
      } :=
  printLexes1 lexKind decl doc width within sound
    (declJoins decl within shaped sound lexical (declOperators decl within))
    (declPrintable decl within sound lexical (declOperators decl within))
    shows

-- No token is layout.

theorem startNotLayout ∀ (first: Char)
    (starts: isWordStart first = True):
    (first == ' ') = False ∧ (first == '\n') = False :=
  cases

theorem digitNotLayout ∀ (first: Char)
    (digit: first.isAsciiDigit = True):
    (first == ' ') = False ∧ (first == '\n') = False :=
  cases

theorem headNotLayout ∀ (text: Text) (first: Char) (others: List Char)
    (split: text.toList = [first, ..others])
    (space: (first == ' ') = False)
    (line: (first == '\n') = False):
    isLayout text = False :=
  let blanks: text.all (char => char == ' ') = False := rewrite split, space
  match isLine: text == "\n" with
    | True =>
      let same := DecEq.sound isLine
      let head := List.consInjectiveHead '\n' first [] others (rewrite same at split then split)
      (DecEq.soundFalse first '\n' line head.flipped).impossible
    | False => rewrite blanks

--| No spelling of a token is layout.
theorem spellsNotLayout ∀ (kind: Tok) (text: Text) (spells: Spells kind text): isLayout text = False :=
  match kind, spells with
    | LParen, same => rewrite same
    | RParen, same => rewrite same
    | LBracket, same => rewrite same
    | RBracket, same => rewrite same
    | Comma, same => rewrite same
    | Colon, same => rewrite same
    | ColonEq, same => rewrite same
    | Equals, same => rewrite same
    | EqEq, same => rewrite same
    | Arrow, Inl same => rewrite same
    | Arrow, Inr same => rewrite same
    | OrOr, Inl same => rewrite same
    | OrOr, Inr same => rewrite same
    | AndAnd, Inl same => rewrite same
    | AndAnd, Inr same => rewrite same
    | Plus, same => rewrite same
    | PlusPlus, same => rewrite same
    | Minus, same => rewrite same
    | Star, same => rewrite same
    | Slash, same => rewrite same
    | Percent, same => rewrite same
    | NotEq, Inl same => rewrite same
    | NotEq, Inr same => rewrite same
    | Lt, same => rewrite same
    | Le, Inl same => rewrite same
    | Le, Inr same => rewrite same
    | Gt, same => rewrite same
    | Ge, Inl same => rewrite same
    | Ge, Inr same => rewrite same
    | Bang, Inl same => rewrite same
    | Bang, Inr same => rewrite same
    | KwDef, same => rewrite same
    | Lower, Witness first (Witness others (Witness comps (Both split (Both starts rest)))) =>
      let (space, line) := startNotLayout first starts
      headNotLayout text first (others ++ qualChars comps) split space line
    | Upper, Witness first (Witness others (Witness comps (Both split (Both starts rest)))) =>
      let (space, line) := startNotLayout first starts
      headNotLayout text first (others ++ qualChars comps) split space line
    | Num, Witness first (Witness others (Both split (Both digit rest))) =>
      let (space, line) := digitNotLayout first digit
      headNotLayout text first others split space line
    | Float, Witness first (Witness others (Witness tail (Both split (Both digit rest)))) =>
      let (space, line) := digitNotLayout first digit
      headNotLayout text first (others ++ tail) split space line

def Word.real (word: Word): Bool := !isLayout word.text

theorem wordReal ∀ (word: Word) (kind: Tok) (spells: Spells kind word.text): word.real = True :=
  rewrite spellsNotLayout kind word.text spells

theorem realAppend ∀ (front back: List Word)
    (first: front.all Word.real = True)
    (second: back.all Word.real = True):
    (front ++ back).all Word.real = True :=
  rewrite allAppendBool front back Word.real then Bool.andIntro first second

--| The tokens of an expression are not layout.
--|
--| Proof idea: Induction on the expression: a name or numeral is `spellsOfText1`, a bracket or operator a fixed
--| spelling, and the lists join by `allAppendBool`.
theorem exprReal ∀ (expr: Expr)
    (within: expr.within1 = True)
    (lexical: expr.lexical1 = True) (spelled: expr.operators1):
    expr.words.all Word.real = True :=
  match expr, spelled with
    | Atom kind word, _ =>
      Bool.andIntro (wordReal word kind (spellsOfText1 kind word.text (Bool.andRight within))) byComputing
    | Paren open inner close, _ =>
      realAppend
        [open, ..inner.words]
        [close]
        (Bool.andIntro
          (wordReal open LParen (DecEq.sound (Bool.andLeft lexical)))
          (exprReal inner within (Bool.andRight (Bool.andRight lexical)) spelled))
        (Bool.andIntro (wordReal close RParen (DecEq.sound (Bool.andLeft (Bool.andRight lexical)))) byComputing)
    | Tuple open items comma close, _ =>
      realAppend
        [open, ..itemsWords items]
        [close]
        (Bool.andIntro
          (wordReal open LParen (DecEq.sound (Bool.andLeft lexical)))
          (itemsReal items within (Bool.andRight (Bool.andRight lexical)) spelled))
        (Bool.andIntro (wordReal close RParen (DecEq.sound (Bool.andLeft (Bool.andRight lexical)))) byComputing)
    | ListOf open items comma close, _ =>
      realAppend
        [open, ..itemsWords items]
        [close]
        (Bool.andIntro
          (wordReal open LBracket (DecEq.sound (Bool.andLeft lexical)))
          (itemsReal items within (Bool.andRight (Bool.andRight lexical)) spelled))
        (Bool.andIntro (wordReal close RBracket (DecEq.sound (Bool.andLeft (Bool.andRight lexical)))) byComputing)
    | App head arguments, (headSpelled, argumentsSpelled) =>
      realAppend head.words
        (itemsWords arguments)
        (exprReal head (Bool.andLeft within) (Bool.andLeft lexical) headSpelled)
        (itemsReal arguments (Bool.andRight within) (Bool.andRight lexical) argumentsSpelled)
    | Infix kind left operator right, (leftSpelled, (kindOfOperator, (operatorSpells, quiet)), rightSpelled) =>
      let (leftWithin, rightWithin) := infixWithin kind left operator right within
      realAppend left.words
        [operator, ..right.words]
        (exprReal left leftWithin (Bool.andLeft lexical) leftSpelled)
        (Bool.andIntro
          (wordReal operator kindOfOperator operatorSpells)
          (exprReal right rightWithin (Bool.andRight (Bool.andRight lexical)) rightSpelled))
    | Prefix operator operand, (prefix, operandSpelled) =>
      Bool.andIntro
        (match prefix with
          | Inl same => wordReal operator Minus same
          | Inr (Inl same) => wordReal operator Bang (Inl same)
          | Inr (Inr same) => wordReal operator Bang (Inr same))
        (exprReal operand (Bool.andLeft within) (Bool.andRight lexical) operandSpelled)

theorem itemsReal ∀ (items: List Expr)
    (within: allWithin1 items = True)
    (lexical: allLexical1 items = True)
    (spelled: AllOperators1 items):
    (itemsWords items).all Word.real = True :=
  match items, spelled with
    | [], _ => byComputing
    | [item, ..rest], (first, others) =>
      realAppend item.words
        (itemsWords rest)
        (exprReal item (Bool.andLeft within) (Bool.andLeft lexical) first)
        (itemsReal rest (Bool.andRight within) (Bool.andRight lexical) others)

--| The tokens of a slice 1 declaration are not layout, from the tree's facts: `Decl.real`.
theorem declReal ∀ (decl: Decl)
    (within: decl.within1 = True)
    (lexical: decl.lexical1 = True) (spelled: decl.operators1):
    decl.real = True :=
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
          let (nameKind, nameSpelled, nameQuiet, nameIsName) := nameKinded name (Bool.andLeft (Bool.andLeft within))
          let assignWord := fixedWord ":=" colonEq
          realAppend
            [fixedWord "def" keyword, name, fixedWord ":" colon]
            (result.words ++ [assignWord, ..value.words])
            (Bool.andIntro
              (wordReal (fixedWord "def" keyword) KwDef byComputing)
              (Bool.andIntro
                (wordReal name nameKind nameSpelled)
                (Bool.andIntro (wordReal (fixedWord ":" colon) Colon byComputing) byComputing)))
            (realAppend result.words
              [assignWord, ..value.words]
              (exprReal result
                (Bool.andRight (Bool.andLeft within))
                (Bool.andLeft (Bool.andRight lexical))
                resultSpelled)
              (Bool.andIntro
                (wordReal assignWord ColonEq byComputing)
                (exprReal value (Bool.andRight within) (Bool.andRight (Bool.andRight lexical)) valueSpelled)))
        | _ => cases
