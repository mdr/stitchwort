--| Slice 1's read-back, the look-aheads (docs/proposals/self-hosted-fmt-s1-sketch.md §2, ticket 17d): the pure tests
--| `Syntax.ReadBackTree`'s rungs take as hypotheses, discharged from what slice 1's items can be. Two kinds of fact
--| do it: what follows an expression (`EndKind`: a `:=`, comma or closer ends every reading), and the alphabet of the
--| items from the type on (`plainAll`: no `=>`, `:`, `_` or `{`, so no lambda, binder or record look-ahead fires).

namespace Syntax.ReadBackEnds
import Std (Bool, Eq, List, Nat, Option, Parse, Text, Void, byDecision)
import Syntax (..)
import Fmt (..)
import Syntax.ReadBackProofs (..)
import Syntax.ReadBackRuns (..)
import Syntax.ReadBackRuns (plainHeader)
import Syntax.ReadBackTree (..)

--| The kinds that end every expression they follow in slice 1: the `:=` after a type, a comma or closer after a
--| bracket's element.
def endsOperand: Tok → Bool
  | ColonEq | Comma | RParen | RBracket => True
  | _ => False

def endsHere: List Item → Bool
  | [] => True
  | [next, .._] => endsOperand next.kind

theorem peekEnds ∀ (modes: Modes) (next: Item) (later: List Item):
    peekIn modes 0 [next, ..later] = None ∨ peekIn modes 0 [next, ..later] = Some next.kind :=
  match stops: modes.stops next with
    | True => Inl byComputing
    | False => Inr byComputing

theorem takesEnds ∀ (modes: Modes) (takes: Tok → Bool) (next: Item) (later: List Item)
    (no: takes next.kind = False):
    takesAhead modes takes [next, ..later] = False :=
  match peekEnds modes next later with
    | Inl none => rewrite none
    | Inr some => rewrite some then no

--| A kind no rung of the ladder continues with: no call, field, argument, operator, range, pipe, `->` or `;`.
type EndKind (kind: Tok): Prop = {
  notOpen: (kind == LParen) = False,
  notDot: (kind == Dot) = False,
  notArgument: opensArgument kind = False,
  notCases: (kind == KwCases) = False,
  unsigned: (kind == Minus || kind == Bang) = False,
  notMul: (kind == Star || kind == Slash || kind == Percent) = False,
  notAdd: (kind == Plus || kind == Minus) = False,
  notAppend: (kind == PlusPlus) = False,
  notRange: (kind == DotDot || kind == DotDotLt || kind == DotDotEq) = False,
  notPipe: (kind == PipeGt) = False,
  notCmp: (kind == KwIn || kind == NotIn || kind.isComparison) = False,
  notAndOr: (kind == AndAnd || kind == OrOr) = False,
  notIff: (kind == IffArrow) = False,
  notArrow: (kind == Arrow) = False,
  notSemi: (kind == Semi) = False
}

theorem endKind ∀ (kind: Tok) (ends: endsOperand kind = True): EndKind kind := match kind, ends with
  | ColonEq, _ => {
    notOpen = byComputing,
    notDot = byComputing,
    notArgument = byComputing,
    notCases = byComputing,
    unsigned = byComputing,
    notMul = byComputing,
    notAdd = byComputing,
    notAppend = byComputing,
    notRange = byComputing,
    notPipe = byComputing,
    notCmp = byComputing,
    notAndOr = byComputing,
    notIff = byComputing,
    notArrow = byComputing,
    notSemi = byComputing
  }
  | Comma, _ => {
    notOpen = byComputing,
    notDot = byComputing,
    notArgument = byComputing,
    notCases = byComputing,
    unsigned = byComputing,
    notMul = byComputing,
    notAdd = byComputing,
    notAppend = byComputing,
    notRange = byComputing,
    notPipe = byComputing,
    notCmp = byComputing,
    notAndOr = byComputing,
    notIff = byComputing,
    notArrow = byComputing,
    notSemi = byComputing
  }
  | RParen, _ => {
    notOpen = byComputing,
    notDot = byComputing,
    notArgument = byComputing,
    notCases = byComputing,
    unsigned = byComputing,
    notMul = byComputing,
    notAdd = byComputing,
    notAppend = byComputing,
    notRange = byComputing,
    notPipe = byComputing,
    notCmp = byComputing,
    notAndOr = byComputing,
    notIff = byComputing,
    notArrow = byComputing,
    notSemi = byComputing
  }
  | RBracket, _ => {
    notOpen = byComputing,
    notDot = byComputing,
    notArgument = byComputing,
    notCases = byComputing,
    unsigned = byComputing,
    notMul = byComputing,
    notAdd = byComputing,
    notAppend = byComputing,
    notRange = byComputing,
    notPipe = byComputing,
    notCmp = byComputing,
    notAndOr = byComputing,
    notIff = byComputing,
    notArrow = byComputing,
    notSemi = byComputing
  }
  | other, never => (Bool.falseNotTrue never).impossible

--| An `EndKind` next ends an operand at every rung.
theorem operandEndsAt ∀ (modes: Modes) (next: Item) (later: List Item)
    (ends: EndKind next.kind):
    OperandEnds modes [next, ..later] :=
  {
    noCall = (match later with
      | [] => byComputing
      | [close, .._] => (rewrite ends.notOpen)),
    noDot = (rewrite ends.notDot),
    noArgument = (match peekEnds modes next later with
      | Inl none => rewrite none
      | Inr some =>
        rewrite some then
          (match later with
            | [] => rewrite ends.notArgument, ends.notDot, ends.notCases
            | [_, .._] => rewrite ends.notArgument, ends.notDot, ends.notCases, ends.unsigned)),
    noMul = takesEnds modes _ next later ends.notMul,
    noAdd = takesEnds modes _ next later ends.notAdd,
    noAppend = takesEnds modes _ next later ends.notAppend,
    noRange = (match peekEnds modes next later with
      | Inl none => rewrite none
      | Inr some => rewrite some then ends.notRange),
    noPipe = (rewrite ends.notPipe),
    noCmp = (match peekEnds modes next later with
      | Inl none => rewrite none
      | Inr some => rewrite some then ends.notCmp),
    noAndOr = (match peekEnds modes next later with
      | Inl none => rewrite none
      | Inr some => rewrite some then ends.notAndOr),
    noIff = (match peekEnds modes next later with
      | Inl none => rewrite none
      | Inr some => rewrite some then ends.notIff),
    noEnd = (match peekEnds modes next later with
      | Inl none => rewrite none
      | Inr some => rewrite some then (rewrite ends.notArrow, ends.notSemi))
  }

--| The kinds of slice 1's items from a declaration's type on: its alphabet less `def` and `:`.
def plainKind: Tok → Bool
  | Lower |
      Upper |
      Num |
      Float |
      ColonEq |
      LParen |
      RParen |
      LBracket |
      RBracket |
      Comma |
      OrOr |
      AndAnd |
      Equals |
      EqEq |
      NotEq |
      Lt |
      Le |
      Gt |
      Ge |
      PlusPlus |
      Plus |
      Minus |
      Star |
      Slash |
      Percent |
      Bang |
      Arrow => True
  | _ => False

def plainAll: List Item → Bool
  | [] => True
  | [item, ..rest] => plainKind item.kind && plainAll rest

--| What `skipGroup` leaves of plain items is plain.
theorem skipPlain ∀ (open: List Tok) (items after: List Item)
    (plain: plainAll items = True)
    (skips: skipGroup open items = Some after):
    plainAll after = True :=
  match items, plain, skips with
    | [], _, skips => (Option.noneNotSome after skips).impossible
    | [item, ..rest], plain, skips =>
      let later: plainAll rest = True := Bool.andRight plain
      match item.kind.isOpener, skips with
        | True, skips => skipPlain [item.kind, ..open] rest after later skips
        | False, skips =>
          match item.kind.isCloser, skips with
            | False, skips => skipPlain open rest after later skips
            | True, skips =>
              match open, skips with
                | [], skips => skipPlain [] rest after later skips
                | [innermost, ..outer], skips =>
                  match pairs innermost item.kind, skips with
                    | False, skips => skipPlain [innermost, ..outer] rest after later skips
                    | True, skips =>
                      match outer, skips with
                        | [], skips => rewrite <- Option.someInjective skips then later
                        | [next, ..more], skips => skipPlain [next, ..more] rest after later skips

--| No lambda ahead: plain items have no `=>`.
theorem lambdaPlain ∀ (fuel: Nat) (modes: Modes) (count: Nat) (items: List Item)
    (plain: plainAll items = True):
    lambdaAheadFrom fuel modes count items = False :=
  match fuel, items with
    | Zero, _ => byComputing
    | Succ more, [] => byComputing
    | Succ more, [item, ..rest] =>
      let later: plainAll rest = True := Bool.andRight plain
      let grouped: afterGroup more modes count [item, ..rest] = False := match skips: skipGroup [] [item, ..rest] with
        | None => byComputing
        | Some after => lambdaPlain more modes (count + 1) after (skipPlain [] [item, ..rest] after plain skips)
      match modes.stops item with
        | True => byComputing
        | False =>
          match kind: item.kind, plain with
            | Lower, _ =>
              match isQualified item with
                | True => byComputing
                | False => lambdaPlain more modes (count + 1) rest later
            | LParen, _ => grouped
            | LBracket, _ =>
              match implicitGroupAt [item, ..rest] || namelessAutoAt [item, ..rest] with
                | True => grouped
                | False => byComputing
            | Underscore, never => (Bool.falseNotTrue never).impossible
            | LBrace, never => (Bool.falseNotTrue never).impossible
            | FatArrow, never => (Bool.falseNotTrue never).impossible
            | other, _ => byComputing

theorem plainNotColon ∀ (kind: Tok) (plain: plainKind kind = True): (kind == Colon) = False := match kind, plain with
  | Colon, never => (Bool.falseNotTrue never).impossible
  | other, _ => byComputing

--| No lambda with a result type ahead: plain items have no `:`.
theorem resultPlain ∀ (modes: Modes) (fuel: Nat) (bracketedLast: Bool) (items: List Item)
    (plain: plainAll items = True):
    lambdaResultType modes fuel bracketedLast items = False :=
  match fuel, items with
    | Zero, _ => byComputing
    | Succ more, [] => byComputing
    | Succ more, [item, ..rest] =>
      let later: plainAll rest = True := Bool.andRight plain
      let noColon: (bracketedLast && item.kind == Colon && resultArrowAhead modes more rest) = False :=
        rewrite plainNotColon item.kind (Bool.andLeft plain) then
          Bool.andFalseMiddle bracketedLast (resultArrowAhead modes more rest)
      let grouped: afterBracket modes more [item, ..rest] = False := match skips: skipGroup [] [item, ..rest] with
        | None => byComputing
        | Some after => resultPlain modes more True after (skipPlain [] [item, ..rest] after plain skips)
      match modes.stops item with
        | True => noColon
        | False =>
          match kind: item.kind, plain with
            | Lower, _ =>
              match isQualified item with
                | True => noColon
                | False => resultPlain modes more False rest later
            | LParen, _ => grouped
            | LBracket, _ => grouped
            | Underscore, never => (Bool.falseNotTrue never).impossible
            | other, _ => noColon

theorem namesPlain ∀ (items: List Item) (count: Nat) (accepts: Tok → Bool)
    (refuses: ∀ (kind: Tok) => plainKind kind = True → accepts kind = False)
    (plain: plainAll items = True):
    namesThen items count accepts = False :=
  match items with
    | [] => byComputing
    | [item, ..rest] =>
      match item.kind == Lower with
        | True => namesPlain rest (count + 1) accepts refuses (Bool.andRight plain)
        | False => rewrite refuses item.kind (Bool.andLeft plain) then cases

theorem pastPlain ∀ (fuel: Nat) (items: List Item) (plain: plainAll items = True): pastAttributes fuel items = items :=
  match fuel, items with
    | Zero, _ => byComputing
    | Succ more, [] => byComputing
    | Succ more, [item, ..rest] =>
      match kind: item.kind, plain with
        | At, never => (Bool.falseNotTrue never).impossible
        | other, _ => byComputing

--| No implicit binder ahead, unless the items start `[auto Upper`: plain items have no `:` after the names.
theorem implicitPlain ∀ (fuel: Nat) (item: Item) (rest: List Item)
    (plain: plainAll [item, ..rest] = True)
    (noAuto: (item.kind == LBracket && namelessAutoAt [item, ..rest]) = False):
    implicitOn fuel [item, ..rest] (Some item.kind) = False :=
  let later: plainAll rest = True := Bool.andRight plain
  match item.kind == LBracket, noAuto with
    | False, _ => byComputing
    | True, noAuto =>
      rewrite noAuto, pastPlain fuel rest later, namesPlain rest 0 (kind => kind == Colon) plainNotColon later

--| No `(x: A) ->` binder ahead: plain items have no `:` after the names.
theorem piPlain ∀ (item: Item) (rest: List Item)
    (plain: plainAll [item, ..rest] = True):
    piOn [item, ..rest] (Some item.kind) = False :=
  let later: plainAll rest = True := Bool.andRight plain
  match item.kind == LParen with
    | False => byComputing
    | True => rewrite namesPlain rest 0 (kind => kind == Colon) plainNotColon later

theorem plainNotKeyword ∀ (kind: Tok)
    (plain: plainKind kind = True):
    startsKeywordExpr kind = False ∧ (kind == KwExists || kind == KwForall) = False ∧ (kind == KwIf) = False :=
  cases

--| `exprInline`'s look-aheads before an operator expression all say no on plain items not starting `[auto Upper` or
--| a walk.
theorem inlinePlainOf ∀ (modes: Modes) (item: Item) (rest: List Item)
    (plain: plainAll [item, ..rest] = True)
    (noAuto: (item.kind == LBracket && namelessAutoAt [item, ..rest]) = False)
    (noWalk: walkOn modes [item, ..rest] = False):
    InlinePlain modes item [item, ..rest] :=
  let (notKeyword, notQuantifier, notIf) := plainNotKeyword item.kind (Bool.andLeft plain)
  {
    notKeyword,
    noWalk,
    noLambda = lambdaPlain ([item, ..rest].length + 1) modes 0 [item, ..rest] plain,
    noResult = resultPlain modes ([item, ..rest].length + 1) False [item, ..rest] plain,
    notQuantifier,
    notIf,
    noImplicit = implicitPlain ([item, ..rest].length + 1) item rest plain noAuto,
    noPi = piPlain item rest plain
  }

theorem operandEndsNil ∀ (modes: Modes): OperandEnds modes [] := {
  noCall = byComputing,
  noDot = byComputing,
  noArgument = byComputing,
  noMul = byComputing,
  noAdd = byComputing,
  noAppend = byComputing,
  noRange = byComputing,
  noPipe = byComputing,
  noCmp = byComputing,
  noAndOr = byComputing,
  noIff = byComputing,
  noEnd = byComputing
}

theorem noBarOne ∀ (modes: Modes) (item: Item): matchesBarOn modes [item] = False :=
  let noPipe: isSome Pipe (peekIn modes 1 [item]) = False := match modes.stops item with | True | False => byComputing
  rewrite noPipe then
    Bool.andFalseMiddle
      (wordOn modes "matches" [item])
      (!(isSome Lower (peekIn modes 2 [item]) && isSome Equals (peekIn modes 3 [item])))

theorem plainNotPipe ∀ (kind: Tok) (plain: plainKind kind = True): (kind == Pipe) = False := cases

theorem noBarPlain ∀ (modes: Modes) (item next: Item) (rest: List Item)
    (plain: plainKind next.kind = True):
    matchesBarOn modes [item, next, ..rest] = False :=
  let items := [item, next, ..rest]
  let noPipe: isSome Pipe (peekIn modes 1 items) = False := match modes.stops item with
    | True => byComputing
    | False =>
      match peekEnds modes next rest with
        | Inl none => rewrite none
        | Inr some => rewrite some then plainNotPipe next.kind plain
  rewrite noPipe then
    Bool.andFalseMiddle
      (wordOn modes "matches" items)
      (!(isSome Lower (peekIn modes 2 items) && isSome Equals (peekIn modes 3 items)))

--| The word kinds of slice 1 are words to the parser, and plain.
theorem wordPlain ∀ (kind: Tok) (word: kind.wordWithin1 = True): isWord kind = True ∧ plainKind kind = True := cases

theorem wordNotBracket ∀ (kind: Tok) (word: kind.wordWithin1 = True): (kind == LBracket) = False := cases

--| An item for the witnesses below: a token on the first line, unglued, at bracket depth 0.
def wordItem (kind: Tok) (text: Text) (index: Nat): Item := {
  leaf = { token = { kind, text, column = index, lineStart = False }, trivia = Trivia.empty },
  glued = False,
  afterOperand = False,
  afterDot = False,
  index,
  depth = 0,
  lineIndent = 0
}

--| `()` skips to nothing after it: `skipPlain`'s hypotheses can hold.
theorem skipPlainExample: plainAll [] = True :=
  skipPlain [] [wordItem LParen "(" 0, wordItem RParen ")" 1] [] byComputing byComputing
