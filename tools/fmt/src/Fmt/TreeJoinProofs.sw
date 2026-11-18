--| `printLexes1` from the tree's facts (docs/proposals/self-hosted-fmt-s1-sketch.md §1.5, ticket 18c): `printLexes1`
--| (`Fmt.JoinProofs`) takes `DeclJoins` and `Every Printable`, which are facts about the declaration's tokens' spellings
--| and what may follow them; this file derives both from the tree's facts (`within1`, `sound`, `lexical1`, `shaped1`)
--| and `spelled1`, with `kinds` the lexer's kind of each text (`lexKind`).
--|
--| `spelled1` is the one fact `lexical1` doesn't give. `lexical1` says each name and numeral lexes as one token of its
--| kind; but a qualified name (`List.map`) lexes as one `Lower` token and a numeral with an exponent (`1e5`) as one
--| `Float`, and neither is a text `Spells` that kind. So no lexer inversion gives `Spells` from `lexesAs`
--| (`qualifiedLexes`, `exponentLexes`), and the parser must say what its leaves spell.

namespace Fmt.TreeJoinProofs
import Std (Bool, Char, DecEq, Doc, Eq, List, Nat, Option, Result, Text, Void, byDecision)
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
import Syntax.Proofs (Laid, LexesAs, MayFollow, Spells, lexesAsSpells, mayFollowEnd)
import Fmt (..)
import Fmt.PrintLexProofs (Follows, Printable, pieceFold)
import Fmt.SpellProofs (..)
import Fmt.JoinProofs (
  DeclJoins,
  headDiffers,
  Joinable,
  AllJoinable,
  WordJoins,
  CloserJoins,
  OpenerJoins,
  Token,
  printLexes1
)

-- The lexer's kind of a text, and where `lexesAs` is too weak.

--| The kind the lexer gives a text that lexes as one token (any kind for another).
def lexKind (text: Text): Tok := match lex text with
  | Ok lexed =>
    match lexed.leaves with
      | [leaf] => leaf.token.kind
      | _ => Lower
  | Err _ => Lower

--| A qualified name lexes as one `Lower` token, though its text has a `.` that no `Spells Lower` text has.
theorem qualifiedLexes: textLexesAs "List.map" Lower = True := byComputing

--| A numeral with an exponent lexes as one `Float`, though `Spells Float` wants a fraction.
theorem exponentLexes: textLexesAs "1e5" Float = True := byComputing

--| A text that spells a token of a kind is read by the lexer as that kind.
theorem lexKindOfSpells ∀ (kind: Tok) (text: Text) (spells: Spells kind text): lexKind text = kind :=
  let ran := lexesAsSpells kind text spells (mayFollowEnd kind text)
  rewrite ran

theorem lexKindLParen: lexKind "(" = LParen := byComputing

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
    | Lower, Witness first (Witness others (Both split (Both starts rest))) =>
      headNotDash text first others split (startNotDash first starts)
    | Upper, Witness first (Witness others (Both split (Both starts rest))) =>
      headNotDash text first others split (startNotDash first starts)
    | Num, Witness first (Witness others (Both split (Both digit rest))) =>
      headNotDash text first others split (digitNotDash first digit)
    | Float, Witness first (Witness others (Witness second (Witness more (Both split (Both digit rest))))) =>
      headNotDash text first (others ++ ['.', second, ..more]) split (digitNotDash first digit)

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

theorem takeWhileAll ∀ (passes: Char → Bool) (chars: List Char)
    (all: chars.all passes = True):
    chars.takeWhile passes = chars :=
  match chars with
    | [] => byComputing
    | [char, ..rest] => rewrite Bool.andLeft all, takeWhileAll passes rest (Bool.andRight all)

theorem startBeq ∀ (first: Char)
    (starts: isWordStart first = True):
    (first == '-') = False ∧ (first == '>') = False ∧ (first == '=') = False :=
  cases

theorem digitBeq ∀ (first: Char)
    (digit: first.isAsciiDigit = True):
    (first == '-') = False ∧ (first == '>') = False ∧ (first == '=') = False :=
  cases

theorem charNe ∀ (first other: Char) (differs: (first == other) = False): first ≠ other := same =>
  DecEq.soundFalse first other differs same

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
    | Inr (Inr (Inr (Inr (Inr (Inl (Witness first (Witness others (Both split (Both starts rest))))))))) =>
      let (dash, greater, equals) := startBeq first starts
      (first, others, split, dash, greater, equals)
    | Inr (Inr (Inr (Inr (Inr (Inr (Inl (Witness first (Witness others (Both split (Both starts rest)))))))))) =>
      let (dash, greater, equals) := startBeq first starts
      (first, others, split, dash, greater, equals)
    | Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inl (Witness first (Witness others (Both split (Both digit rest))))))))))) =>
      let (dash, greater, equals) := digitBeq first digit
      (first, others, split, dash, greater, equals)
    | Inr
        (Inr
          (Inr
            (Inr
              (Inr
                (Inr
                  (Inr
                    (Inr
                      (Witness first
                        (Witness others (Witness second (Witness more (Both split (Both digit rest))))))))))))) =>
      let (dash, greater, equals) := digitBeq first digit
      (first, others ++ ['.', second, ..more], split, dash, greater, equals)

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
      rewrite split, Syntax.Proofs.wordStartIsChar first starts, takeWhileAll isWordChar others word
    let named: text = "in" := Eq.trans (Text.fromToList text).flipped (rewrite (Eq.trans whole.flipped same))
    notIn (rewrite named at kinded then kinded)

--| What follows `!`: nothing that makes it the operator `!in`.
theorem leadsNotIn ∀ (text: Text) (leads: Leads text): text.toList.takeWhile isWordChar ≠ ['i', 'n'] := match leads with
  | Inl same => rewrite same then byDecision
  | Inr (Inl same) => rewrite same then byDecision
  | Inr (Inr (Inl same)) => rewrite same then byDecision
  | Inr (Inr (Inr (Inl same))) => rewrite same then byDecision
  | Inr (Inr (Inr (Inr (Inl same)))) => rewrite same then byDecision
  | Inr (Inr (Inr (Inr (Inr (Inl (Witness first (Witness others (Both split (Both starts (Both word kinded)))))))))) =>
    wordNotIn Lower text first others split starts word kinded byDecision
  | Inr
      (Inr
        (Inr (Inr (Inr (Inr (Inl (Witness first (Witness others (Both split (Both starts (Both word kinded))))))))))) =>
    wordNotIn Upper text first others split starts word kinded byDecision
  | Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inl (Witness first (Witness others (Both split (Both digit rest))))))))))) =>
    same =>
      let wordChar := digitWordChar first digit
      let head := List.consInjectiveHead first 'i' _ ['n'] (rewrite split, wordChar at same then same)
      DecEq.soundFalse first 'i' (digitNotI first digit) head
  | Inr
      (Inr
        (Inr
          (Inr
            (Inr
              (Inr
                (Inr
                  (Inr
                    (Witness first
                      (Witness others (Witness second (Witness more (Both split (Both digit rest))))))))))))) => same =>
    let wordChar := digitWordChar first digit
    let head := List.consInjectiveHead first 'i' _ ['n'] (rewrite split, wordChar at same then same)
    DecEq.soundFalse first 'i' (digitNotI first digit) head

theorem minusFollows ∀ (text: Text)
    (leads: Leads text)
    (notMinus: (text == "-") = False):
    MayFollow Minus "-" text.toList :=
  let (first, others, split, dash, greater, equals) := leadsHead text leads notMinus
  (
    headDiffers text.toList first '-' (rewrite split) (charNe first '-' dash),
    headDiffers text.toList first '>' (rewrite split) (charNe first '>' greater)
  )

theorem leadsNotEquals ∀ (text: Text) (leads: Leads text): text.toList.head ≠ Some '=' := match dash: text == "-" with
  | True => rewrite DecEq.sound dash then byDecision
  | False =>
    let (first, others, split, dash, greater, equals) := leadsHead text leads dash
    headDiffers text.toList first '=' (rewrite split) (charNe first '=' equals)

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

-- The tree's spellings.

--| An infix operator's text spells a token that is no comma or closer.
def OperatorSpells (text: Text): Prop := ∃ (kind: Tok) => Spells kind text ∧ Quiet kind

--| What the parser's leaves spell, which `lexical1` doesn't say (the header): each name and numeral is a text its
--| kind is spelled with, each infix operator a token's and each prefix operator `-`, `!` or `¬`.
def Expr.spelled1: Expr → Prop
  | Atom kind word => Spells kind word.text
  | Paren _ inner _ => inner.spelled1
  | Tuple _ items _ _ => AllSpelled1 items
  | ListOf _ items _ _ => AllSpelled1 items
  | App head arguments => head.spelled1 ∧ AllSpelled1 arguments
  | Infix _ left operator right => left.spelled1 ∧ OperatorSpells operator.text ∧ right.spelled1
  | Prefix operator operand => PrefixSpells operator.text ∧ operand.spelled1
  | _ => False

def AllSpelled1: List Expr → Prop
  | [] => True
  | [expr, ..rest] => expr.spelled1 ∧ AllSpelled1 rest

def Decl.spelled1: Decl → Prop
  | Definition _ header (Assigned _ value) => Spells Lower header.name.text ∧ header.result.spelled1 ∧ value.spelled1
  | _ => False

theorem wordQuiet ∀ (kind: Tok) (word: kind.wordWithin1 = True): Quiet kind := match kind, word with
  | Lower, word => byDecision
  | Upper, word => byDecision
  | Num, word => byDecision
  | Float, word => byDecision
  | other, word => (Bool.falseNotTrue word).impossible

theorem minusQuiet: Quiet Minus := byDecision

theorem bangQuiet: Quiet Bang := byDecision

theorem lowerQuiet: Quiet Lower := byDecision

--| Where the first token of an expression is `-`, `!`, `¬`, a bracket, or spelled as a name or numeral.
--|
--| Proof idea: Induction down the first operands.
theorem leadsOf ∀ (expr: Expr)
    (within: expr.within1 = True)
    (lexical: expr.lexical1 = True) (spelled: expr.spelled1):
    Leads expr.lead.text :=
  match expr, spelled with
    | Atom kind word, spells =>
      match kind, within with
        | Lower, _ => Inr (Inr (Inr (Inr (Inr (Inl spells)))))
        | Upper, _ => Inr (Inr (Inr (Inr (Inr (Inr (Inl spells))))))
        | Num, _ => Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inl spells)))))))
        | Float, _ => Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inr spells)))))))
        | other, word => (Bool.falseNotTrue word).impossible
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
    | InfixBinary => (Bool.andLeft within, Bool.andRight within)
    | InfixArrow => (Bool.andLeft within, Bool.andRight within)

--| `printLexes1`'s facts about the tokens of an expression, from the tree's.
--|
--| Proof idea: Induction on the expression; each token is `spellsJoins` of its spelling (an opening bracket
--| `bracketOpener`, a closing one by its text), an application's arguments are not empty by `shaped1`, and a prefix
--| operator's operand may follow it by `prefixFollows`.
theorem joinable ∀ (expr: Expr)
    (within: expr.within1 = True)
    (shaped: expr.shaped1 = True)
    (sound: expr.sound = True)
    (lexical: expr.lexical1 = True) (spelled: expr.spelled1):
    Joinable lexKind expr :=
  match expr, spelled with
    | Atom kind word, spells => spellsJoins word kind sound spells (wordQuiet kind within)
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
        joinable operand within (Bool.andLeft shaped) (Bool.andRight sound) (Bool.andRight lexical) operandSpelled,
        empty =>
          prefixFollows operator operand within prefix
            (leadsOf operand within (Bool.andRight lexical) operandSpelled)
            empty
      )

theorem allJoinable ∀ (items: List Expr)
    (within: allWithin1 items = True)
    (shaped: allShaped1 items = True)
    (sound: allSound items = True)
    (lexical: allLexical1 items = True)
    (spelled: AllSpelled1 items):
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
    (spelled: AllSpelled1 items):
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
    (spelled: AllSpelled1 arguments):
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

--| An opening or closing bracket's words are pieces the lexer proofs can read.
theorem bracketPrintable ∀ (word: Word) (kind: Tok) (hoisted: Bool)
    (sound: word.sound = True)
    (spells: Spells kind word.text):
    Every (Printable lexKind) (word.spelledAt hoisted) :=
  wordPrintable word kind hoisted sound spells

--| The tokens of an expression, with their comments, are pieces the lexer proofs can read.
--|
--| Proof idea: Induction on the expression: each token by `wordPrintable` with its spelling, the pieces in order by
--| `everyAppend`.
theorem exprPrintable ∀ (expr: Expr) (hoisted: Bool)
    (within: expr.within1 = True)
    (sound: expr.sound = True)
    (lexical: expr.lexical1 = True) (spelled: expr.spelled1):
    Every (Printable lexKind) (expr.spelt hoisted) :=
  match expr, spelled with
    | Atom kind word, spells => wordPrintable word kind hoisted sound spells
    | Paren open inner close, innerSpelled =>
      everyThree
        (Printable lexKind)
        (open.spelledAt hoisted)
        (inner.spelt False)
        (close.spelledAt False)
        (bracketPrintable open LParen hoisted (Bool.andLeft sound) (DecEq.sound (Bool.andLeft lexical)))
        (exprPrintable inner False within
          (Bool.andLeft (Bool.andRight sound))
          (Bool.andRight (Bool.andRight lexical))
          innerSpelled)
        (bracketPrintable close RParen False
          (Bool.andRight (Bool.andRight sound))
          (DecEq.sound (Bool.andLeft (Bool.andRight lexical))))
    | Tuple open items comma close, itemsSpelled =>
      everyThree
        (Printable lexKind)
        (open.spelledAt hoisted)
        (commaSpelt items)
        (close.spelledAt False)
        (bracketPrintable open LParen hoisted (Bool.andLeft sound) (DecEq.sound (Bool.andLeft lexical)))
        (commaPrintable items within
          (Bool.andLeft (Bool.andRight sound))
          (Bool.andRight (Bool.andRight lexical))
          itemsSpelled)
        (bracketPrintable close RParen False
          (Bool.andRight (Bool.andRight sound))
          (DecEq.sound (Bool.andLeft (Bool.andRight lexical))))
    | ListOf open items comma close, itemsSpelled =>
      everyThree
        (Printable lexKind)
        (open.spelledAt hoisted)
        (commaSpelt items)
        (close.spelledAt False)
        (bracketPrintable open LBracket hoisted (Bool.andLeft sound) (DecEq.sound (Bool.andLeft lexical)))
        (commaPrintable items within
          (Bool.andLeft (Bool.andRight sound))
          (Bool.andRight (Bool.andRight lexical))
          itemsSpelled)
        (bracketPrintable close RBracket False
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
        (exprPrintable operand False within (Bool.andRight sound) (Bool.andRight lexical) operandSpelled)

-- A declaration.

--| `DeclJoins`, from the tree's facts.
--|
--| Proof idea: The keyword, colon and `:=` are fixed spellings, the name's spelling is `spelled1`'s; the type and the
--| value are `joinable`.
theorem declJoins ∀ (decl: Decl)
    (within: decl.within1 = True)
    (shaped: decl.shaped1 = True)
    (sound: decl.sound = True)
    (lexical: decl.lexical1 = True) (spelled: decl.spelled1):
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
          let (nameSpelled, resultSpelled, valueSpelled) := spelled
          (
            spellsJoins (fixedWord "def" keyword) KwDef (Bool.andLeft sound) byComputing byDecision,
            spellsJoins name Lower (Bool.andLeft (Bool.andRight sound)) nameSpelled lowerQuiet,
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
    (lexical: decl.lexical1 = True) (spelled: decl.spelled1):
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
          let (nameSpelled, resultSpelled, valueSpelled) := spelled
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
                (wordPrintable name Lower False (Bool.andLeft (Bool.andRight sound)) nameSpelled))
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
--| gives it, its leaves lex as their kinds and spell as `spelled1` says. `kinds` is the lexer's kind of each text.
--|
--| Proof idea: `printLexes1`, with its two hypotheses derived: `declJoins` and `declPrintable`.
theorem printLexes1Tree ∀ (decl: Decl) (doc: Doc) (width: Nat)
    (within: decl.within1 = True)
    (shaped: decl.shaped1 = True)
    (sound: decl.sound = True)
    (lexical: decl.lexical1 = True) (spelled: decl.spelled1)
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
    (declJoins decl within shaped sound lexical spelled)
    (declPrintable decl within sound lexical spelled)
    shows

-- Examples: the tree's facts of `exampleDecl` give `printLexes1`'s; and a declaration with a qualified name that
-- has every tree fact but `spelled1`, so `lexical1` can't give it.

theorem exampleSpelled: exampleDecl.spelled1 := (
  ('d', [], byComputing, byComputing, byComputing, byComputing),
  ('A', [], byComputing, byComputing, byComputing, byComputing),
  ('g', [], byComputing, byComputing, byComputing, byComputing),
  ((
    (
      ('a', [], byComputing, byComputing, byComputing, byComputing),
      ('b', [], byComputing, byComputing, byComputing, byComputing),
      byComputing
    ),
    byComputing
  ))
)

--| `def d: A := List.map`.
def qualifiedDecl: Decl :=
  Definition []
    {
      exportKeyword = None,
      opaqueKeyword = None,
      kind = DefPlain,
      keyword = Comments.none,
      name = fixedWord "d" Comments.none,
      forallKeyword = None,
      params = [],
      colon = Comments.none,
      result = Atom Upper (fixedWord "A" Comments.none),
      decreasingClause = None,
      unfoldingClause = None
    }
    (Assigned Comments.none (Atom Lower (fixedWord "List.map" Comments.none)))

theorem qualifiedTreeFacts: qualifiedDecl.within1 = True
      ∧ qualifiedDecl.shaped1 = True
      ∧ qualifiedDecl.sound = True
      ∧ qualifiedDecl.lexical1 = True :=
  (byComputing, byComputing, byComputing, byComputing)

--| No text with a `.` spells `Lower`.
theorem qualifiedNotSpelled: Spells Lower "List.map" → Void := spells =>
  match spells with
    | Witness first (Witness others (Both split (Both starts (Both word kinded)))) =>
      let tail: others = ['i', 's', 't', '.', 'm', 'a', 'p'] := (Eq.cong (chars => chars.drop 1) split).flipped
      (Bool.falseNotTrue (rewrite tail at word then word)).impossible

--| So `qualifiedDecl` has the tree facts `lexical1` gives and not `spelled1`, and `Every Printable` fails for it.
theorem qualifiedNotSpelled1: qualifiedDecl.spelled1 → Void := (nameSpelled, resultSpelled, valueSpelled) =>
  qualifiedNotSpelled valueSpelled

theorem exampleDeclJoinsTree: DeclJoins lexKind exampleDecl :=
  declJoins exampleDecl byComputing byComputing byComputing byComputing exampleSpelled

--| `def d: A := a |> b`: the operator `|>` is no token of slice 1's alphabet, but it is one of `operatorTok`'s.
def pipedDecl: Decl :=
  Definition []
    {
      exportKeyword = None,
      opaqueKeyword = None,
      kind = DefPlain,
      keyword = Comments.none,
      name = fixedWord "d" Comments.none,
      forallKeyword = None,
      params = [],
      colon = Comments.none,
      result = Atom Upper (fixedWord "A" Comments.none),
      decreasingClause = None,
      unfoldingClause = None
    }
    (Assigned Comments.none
      (Infix InfixBinary
        (Atom Lower (fixedWord "a" Comments.none))
        (fixedWord "|>" Comments.none)
        (Atom Lower (fixedWord "b" Comments.none))))

theorem pipedTreeFacts: pipedDecl.within1 = True
      ∧ pipedDecl.shaped1 = True
      ∧ pipedDecl.sound = True
      ∧ pipedDecl.lexical1 = True :=
  (byComputing, byComputing, byComputing, byComputing)

theorem pipeNotSpelled ∀ (spells: Spells (lexKind "|>") "|>"): Void := cases

--| No token of slice 1's alphabet is spelled `|>`, so `pipedDecl` has no `spelled1`: the tree alone doesn't say its
--| operators are in the alphabet.
theorem pipedNotSpelled: OperatorSpells "|>" → Void := (Witness kind (Both spells quiet)) =>
  pipeNotSpelled (rewrite <- lexKindOfSpells kind "|>" spells at spells then spells)
