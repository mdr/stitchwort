--| Slice 1's read-back on one line (ticket 17d, first part): a declaration whose type and value are words,
--| parentheses, tuples and lists, all on the `def`'s line, parses to that declaration (`readsBackLine`).
--|
--| The items are related to the tree by `Spelt` (each node's tokens in order, each item carrying the node's word, a
--| comma between bracket items and none after the last); the look-aheads are discharged by `Syntax.ReadBackEnds`
--| from the item kinds (`lineAll`: words, brackets, commas and `:=`) and from what follows each node. On one line
--| the modes never stop (`Quiet`), so no block starts and the line rule never applies: `hangs` holds trivially, and
--| none of `FullReads`' block reading is needed. Calls, `-`, `!`, operators and lines starting inside the
--| declaration are not here yet.

namespace Syntax.ReadBackLine
import Std (Bool, Eq, List, Nat, Option, Parse, Void)
import Syntax (..)
import Fmt (..)
import Syntax.ReadBackProofs (..)
import Syntax.ReadBackRuns (..)
import Syntax.ReadBackRuns (plainHeader)
import Syntax.ReadBackTree (..)
import Syntax.ReadBackEnds (..)

--| Modes in which nothing stops a reading: no guard, `calc`, `rewrite` rule or line limit, as in a declaration's
--| type and body and inside their brackets.
type Quiet (modes: Modes): Prop = {
  noGuard: modes.guard = False,
  noCalc: modes.inCalc = False,
  noRule: modes.rewriteRule = None,
  noLimit: modes.limit = None
}

theorem quietStops ∀ (modes: Modes) (item: Item) (quiet: Quiet modes): modes.stops item = False :=
  rewrite quiet.noGuard, quiet.noCalc, quiet.noRule, quiet.noLimit

theorem quietPeek ∀ (modes: Modes) (item: Item) (later: List Item)
    (quiet: Quiet modes):
    peekIn modes 0 [item, ..later] = Some item.kind :=
  rewrite quietStops modes item quiet

theorem quietPeekSecond ∀ (modes: Modes) (first second: Item) (later: List Item)
    (quiet: Quiet modes):
    peekIn modes 1 [first, second, ..later] = Some second.kind :=
  rewrite quietStops modes first quiet, quietStops modes second quiet

theorem quietBrackets ∀ (modes: Modes) (quiet: Quiet modes): Quiet modes.inBrackets :=
  { noGuard = byComputing, noCalc = quiet.noCalc, noRule = quiet.noRule, noLimit = quiet.noLimit }

--| The kinds of a one-line declaration's items from its type on, in this part: words, brackets, commas and `:=`.
def lineKind: Tok → Bool
  | Lower => True
  | Upper => True
  | Num => True
  | Float => True
  | ColonEq => True
  | LParen => True
  | RParen => True
  | LBracket => True
  | RBracket => True
  | Comma => True
  | _ => False

def lineAll: List Item → Bool
  | [] => True
  | [item, ..rest] => lineKind item.kind && lineAll rest

--| The kinds an expression of this part starts with.
def startKind: Tok → Bool
  | Lower => True
  | Upper => True
  | Num => True
  | Float => True
  | LParen => True
  | LBracket => True
  | _ => False

--| `read` spells `expr`: the node's tokens in order, each an item of the token's kind carrying the node's word, a
--| comma between each two bracket items and none after the last (`comma = False`); a tuple has two items or more.
def Spelt: Expr → List Item → Prop
  | Atom kind word, read =>
    ∃ (item: Item) => read = [item] ∧ item.kind = kind ∧ item.leaf.word = word ∧ kind.wordWithin1 = True
  | Paren open inner close, read =>
    ∃ (first: Item) (inside: List Item) (last: Item) => read = [first, ..inside ++ [last]]
      ∧ first.kind = LParen
      ∧ first.leaf.word = open
      ∧ last.kind = RParen
      ∧ last.leaf.word = close
      ∧ Spelt inner inside
  | Tuple open [one, two, ..others] comma close, read =>
    ∃ (first: Item) (read1: List Item) (separator: Item) (read2: List Item) (steps: List (Item, List Item, Expr)) (last: Item) =>
      read = [first, ..read1 ++ ([separator, ..read2] ++ (commaReads steps ++ [last]))]
        ∧ comma = False
        ∧ first.kind = LParen
        ∧ first.leaf.word = open
        ∧ separator.kind = Comma
        ∧ last.kind = RParen
        ∧ last.leaf.word = close
        ∧ Spelt one read1
        ∧ Spelt two read2
        ∧ SpeltSteps others steps
  | ListOf open [] comma close, read =>
    ∃ (first last: Item) => read = [first, last]
      ∧ comma = False
      ∧ first.kind = LBracket
      ∧ first.leaf.word = open
      ∧ last.kind = RBracket
      ∧ last.leaf.word = close
  | ListOf open [one, ..others] comma close, read =>
    ∃ (first: Item) (read1: List Item) (steps: List (Item, List Item, Expr)) (last: Item) => read
      = [first, ..read1 ++ (commaReads steps ++ [last])]
      ∧ comma = False
      ∧ first.kind = LBracket
      ∧ first.leaf.word = open
      ∧ last.kind = RBracket
      ∧ last.leaf.word = close
      ∧ Spelt one read1
      ∧ SpeltSteps others steps
  | _, _ => Void

--| The bracket items after the first (or first two), as `CommaReads`' steps: a comma, then an item's reading.
def SpeltSteps: List Expr → List (Item, List Item, Expr) → Prop
  | [], steps => steps = []
  | [expr, ..rest], steps =>
    ∃ (comma: Item) (read: List Item) (later: List (Item, List Item, Expr)) => steps = [(comma, read, expr), ..later]
      ∧ comma.kind = Comma
      ∧ Spelt expr read
      ∧ SpeltSteps rest later

--| How deep `self` calls nest when the parser reads the expression: one more for each bracket.
def Expr.nest1: Expr → Nat
  | Paren _ inner _ => inner.nest1 + 1
  | Tuple _ items _ _ => nestAll items + 1
  | ListOf _ items _ _ => nestAll items + 1
  | _ => 0

def nestAll: List Expr → Nat
  | [] => 0
  | [expr, ..rest] => expr.nest1 + nestAll rest

theorem wordStart ∀ (kind: Tok) (word: kind.wordWithin1 = True): startKind kind = True := cases

theorem speltStarts ∀ (expr: Expr) (read: List Item)
    (spelt: Spelt expr read):
    ∃ (item: Item) (more: List Item) => read = [item, ..more] ∧ startKind item.kind = True :=
  match expr, spelt with
    | Atom kind word, (item, isRead, isKind, _, word) => (item, [], isRead, rewrite isKind then wordStart kind word)
    | Paren _ _ _, (first, inside, last, isRead, isOpen, _) => (first, inside ++ [last], isRead, rewrite isOpen)
    | Tuple _ [_, _, .._] _ _, (first, read1, separator, read2, steps, last, isRead, _, isOpen, _) =>
      (first, read1 ++ ([separator, ..read2] ++ (commaReads steps ++ [last])), isRead, rewrite isOpen)
    | ListOf _ [] _ _, (first, last, isRead, _, isOpen, _) => (first, [last], isRead, rewrite isOpen)
    | ListOf _ [_, .._] _ _, (first, read1, steps, last, isRead, _, isOpen, _) =>
      (first, read1 ++ (commaReads steps ++ [last]), isRead, rewrite isOpen)
    | _, never => Void.impossible never

--| The kinds inside an expression of this part: `lineKind` without `:=`.
def exprKind: Tok → Bool
  | Lower => True
  | Upper => True
  | Num => True
  | Float => True
  | LParen => True
  | RParen => True
  | LBracket => True
  | RBracket => True
  | Comma => True
  | _ => False

def exprAll: List Item → Bool
  | [] => True
  | [item, ..rest] => exprKind item.kind && exprAll rest

theorem exprAppend ∀ (first rest: List Item): exprAll (first ++ rest) = (exprAll first && exprAll rest) :=
  match first with
    | [] => byComputing
    | [item, ..more] =>
      rewrite exprAppend more rest then
        match exprKind item.kind with
          | True => byComputing
          | False => byComputing

theorem wordExpr ∀ (kind: Tok) (word: kind.wordWithin1 = True): exprKind kind = True := cases

theorem speltExpr ∀ (expr: Expr) (read: List Item) (spelt: Spelt expr read): exprAll read = True :=
  match expr, spelt with
    | Atom kind word, (item, isRead, isKind, _, word) => rewrite isRead, isKind, wordExpr kind word
    | Paren _ inner _, (first, inside, last, isRead, isOpen, _, isClose, _, innerSpelt) =>
      rewrite isRead, isOpen, exprAppend inside [last], speltExpr inner inside innerSpelt, isClose
    | Tuple _ [one, two, ..others] _ _, (first, read1, separator, read2, steps, last, isRead, _, isOpen, _, isComma,
        isClose, _, oneSpelt, twoSpelt, stepsSpelt) =>
      rewrite isRead,
          isOpen,
          exprAppend read1 ([separator, ..read2] ++ (commaReads steps ++ [last])),
          speltExpr one read1 oneSpelt,
          isComma,
          exprAppend read2 (commaReads steps ++ [last]),
          speltExpr two read2 twoSpelt,
          exprAppend (commaReads steps) [last],
          stepsExpr others steps stepsSpelt,
          isClose
    | ListOf _ [] _ _, (first, last, isRead, _, isOpen, _, isClose, _) => rewrite isRead, isOpen, isClose
    | ListOf _ [one, ..others] _ _, (first, read1, steps, last, isRead, _, isOpen, _, isClose, _, oneSpelt,
        stepsSpelt) =>
      rewrite isRead,
          isOpen,
          exprAppend read1 (commaReads steps ++ [last]),
          speltExpr one read1 oneSpelt,
          exprAppend (commaReads steps) [last],
          stepsExpr others steps stepsSpelt,
          isClose
    | _, never => Void.impossible never

theorem stepsExpr ∀ (exprs: List Expr) (steps: List (Item, List Item, Expr))
    (spelt: SpeltSteps exprs steps):
    exprAll (commaReads steps) = True :=
  match exprs, spelt with
    | [], isEmpty => rewrite isEmpty
    | [expr, ..rest], (comma, read, later, isSteps, isComma, exprSpelt, restSpelt) =>
      rewrite isSteps,
          isComma,
          exprAppend read (commaReads later),
          speltExpr expr read exprSpelt,
          stepsExpr rest later restSpelt

theorem exprNotColonEq ∀ (kind: Tok) (expr: exprKind kind = True): (kind == ColonEq) = False := cases

theorem startOutside ∀ (first second: Tok)
    (starts: startKind first = True)
    (expr: exprKind second = True):
    parenOutside (Some first) (Some second) = False :=
  match first, starts with
    | Lower, _ => rewrite exprNotColonEq second expr
    | Upper, _ => byComputing
    | Num, _ => byComputing
    | Float, _ => byComputing
    | LParen, _ => byComputing
    | LBracket, _ => byComputing
    | other, never => (Bool.falseNotTrue never).impossible

theorem startBracketPlain ∀ (first second: Tok)
    (starts: startKind first = True)
    (expr: exprKind second = True):
    ((isSome Lower (Some first) || isSome KwDecreasing (Some first)) && isSome ColonEq (Some second)) = False :=
  match first, starts with
    | Lower, _ => rewrite exprNotColonEq second expr
    | Upper, _ => byComputing
    | Num, _ => byComputing
    | Float, _ => byComputing
    | LParen, _ => byComputing
    | LBracket, _ => byComputing
    | other, never => (Bool.falseNotTrue never).impossible

def exprHead: List Item → Bool
  | [] => False
  | [item, .._] => exprKind item.kind

theorem peekTwo ∀ (modes: Modes)
    (quiet: Quiet modes)
    (first second: Item) (more tail: List Item)
    (kinds: exprAll more = True)
    (head: exprHead tail = True):
    ∃ (kind: Tok) => peekIn modes 2 [first, second, ..more ++ tail] = Some kind ∧ exprKind kind = True :=
  match more, kinds with
    | [], _ =>
      match tail, head with
        | [], never => (Bool.falseNotTrue never).impossible
        | [next, .._], head => (
          next.kind,
          (rewrite quietStops modes first quiet, quietStops modes second quiet, quietStops modes next quiet),
          head
        )
    | [third, .._], kinds => (
      third.kind,
      (rewrite quietStops modes first quiet, quietStops modes second quiet, quietStops modes third quiet),
      Bool.andLeft kinds
    )

--| The first item is no section operator.
def headPlain: List Item → Bool
  | [] => True
  | [item, .._] => !item.kind.isSectionOperator

theorem lineSection ∀ (kind: Tok) (line: lineKind kind = True): kind.isSectionOperator = False := cases

--| `groupInside` gives what it has collected when the group closes, newest first reversed; on these kinds none is a
--| section operator, so neither is the last item inside.
--|
--| Proof idea: by induction on the items, as `groupInside` steps; when the group closes, the items collected are
--| `found`, whose head the invariant `headPlain` covers.
theorem groupLine ∀ (open: List Tok) (found items inside: List Item)
    (plain: headPlain found = True)
    (line: lineAll items = True)
    (groups: groupInside open found items = Some inside):
    headPlain inside.reverse = True :=
  match items, line, groups with
    | [], _, never => (Option.noneNotSome inside never).impossible
    | [item, ..rest], line, groups =>
      let later: lineAll rest = True := Bool.andRight line
      let fresh: headPlain [item, ..found] = True := rewrite lineSection item.kind (Bool.andLeft line)
      match item.kind.isOpener, groups with
        | True, groups => groupLine [item.kind, ..open] [item, ..found] rest inside fresh later groups
        | False, groups =>
          match item.kind.isCloser, groups with
            | False, groups => groupLine open [item, ..found] rest inside fresh later groups
            | True, groups =>
              match open, groups with
                | [], groups => groupLine [] [item, ..found] rest inside fresh later groups
                | [innermost, ..outer], groups =>
                  match pairs innermost item.kind, groups with
                    | False, groups => groupLine [innermost, ..outer] [item, ..found] rest inside fresh later groups
                    | True, groups =>
                      match outer, groups with
                        | [], groups => rewrite <- Option.someInjective groups, List.reverseReverse found then plain
                        | [next, ..more], groups =>
                          groupLine [next, ..more] [item, ..found] rest inside fresh later groups

theorem notTrueFalse ∀ (b: Bool) (no: (!b) = True): b = False := match b, no with
  | False, _ => byComputing
  | True, never => (Bool.falseNotTrue never).impossible

--| No `(k +)` section: no item of this part is a section operator.
theorem rightLine ∀ (first: Item) (rest: List Item) (line: lineAll rest = True): rightOperator [first, ..rest] = None :=
  match groups: groupInside [LParen] [] rest with
    | None => byComputing
    | Some inside =>
      let plain := groupLine [LParen] [] rest inside byComputing line groups
      match backwards: inside.reverse with
        | [] => byComputing
        | [last, ..more] =>
          let lastPlain: headPlain [last, ..more] = True := rewrite <- backwards then plain
          rewrite notTrueFalse last.kind.isSectionOperator lastPlain

theorem startFacts ∀ (kind: Tok)
    (starts: startKind kind = True):
    (kind == Dot) = False ∧ (kind == KwMatch) = False ∧ (kind == Minus || kind == Bang) = False :=
  cases

--| An atom on its line's middle that nothing continues reads as a full expression: every rung above the atom with no
--| links, no block starting.
--|
--| Proof idea: `fullWord`'s ladder, for any atom: an application with no arguments, then each chain with no links,
--| no comparison, logic or end; the first item doesn't start a line, so `FullReads` asks for no block.
theorem fullOfAtom ∀ (sub: Goal → List Item → List Item → Expr → Prop) (modes: Modes) (item: Item)
    (more rest: List Item) (value: Expr)
    (inLine: item.leaf.token.lineStart = False)
    (open: modes.stops item = False)
    (starts: startKind item.kind = True)
    (noBar: matchesBarOn modes [item, ..more ++ rest] = False)
    (inline: InlinePlain modes item [item, ..more ++ rest])
    (ends: OperandEnds modes rest)
    (atomReads: AtomReads sub modes True [item, ..more] rest value):
    FullReads sub modes [item, ..more] rest value :=
  let read := [item, ..more]
  let (notDot, notMatch, unsigned) := startFacts item.kind starts
  let noSection: isSome Dot (peekIn modes 0 (read ++ rest)) = False :=
    rewrite peekFirst modes item (more ++ rest) open then notDot
  let noLinks: read = read ++ Parse.loopReads [] (linkSteps []) := (List.appendNil read).flipped
  let unaryReads: UnaryReads sub modes read rest value :=
    Inr (item, more, byComputing, open, notMatch, noBar, Inl unsigned, Inl (noSection, atomReads, ends.noArgument))
  let mulReads: MulReads sub modes read rest value := (read, value, [], noLinks, byComputing, unaryReads, ends.noMul)
  let addReads: AddReads sub modes read rest value := (read, value, [], noLinks, byComputing, mulReads, ends.noAdd)
  let appendReads: AppendReads sub modes read rest value :=
    (read, value, [], noLinks, byComputing, addReads, ends.noAppend)
  let whole: read = read ++ [] ++ [] := (List.appendNil read).flipped
  let operatorReads: OperatorReads sub modes read rest value := (
    read,
    [],
    [],
    value,
    value,
    whole,
    rewrite List.appendNil read then noSection,
    Inl ((ends.noRange, ends.noPipe, appendReads), ends.noCmp),
    Inl (byComputing, byComputing, ends.noAndOr),
    ends.noIff,
    Inl (byComputing, byComputing, ends.noEnd)
  )
  let never: startsBlock modes True item = False := rewrite inLine
  (
    item,
    more,
    byComputing,
    (open, inline, operatorReads),
    blockStarts => (Bool.falseNotTrue (Eq.trans never.flipped blockStarts)).impossible
  )

def inLineAll: List Item → Bool
  | [] => True
  | [item, ..rest] => !item.leaf.token.lineStart && inLineAll rest

theorem lineAppend ∀ (first rest: List Item): lineAll (first ++ rest) = (lineAll first && lineAll rest) :=
  match first with
    | [] => byComputing
    | [item, ..more] =>
      rewrite lineAppend more rest then
        match lineKind item.kind with
          | True => byComputing
          | False => byComputing

theorem inLineAppend ∀ (first rest: List Item): inLineAll (first ++ rest) = (inLineAll first && inLineAll rest) :=
  match first with
    | [] => byComputing
    | [item, ..more] =>
      rewrite inLineAppend more rest then
        match item.leaf.token.lineStart with
          | True => byComputing
          | False => byComputing

theorem andBoth ∀ (a b: Bool) (both: (a && b) = True): a = True ∧ b = True := (Bool.andLeft both, Bool.andRight both)

theorem linePlainKind ∀ (kind: Tok) (line: lineKind kind = True): plainKind kind = True := cases

theorem linePlain ∀ (items: List Item) (line: lineAll items = True): plainAll items = True := match items with
  | [] => byComputing
  | [item, ..rest] => rewrite linePlainKind item.kind (Bool.andLeft line), linePlain rest (Bool.andRight line)

theorem noBarLine ∀ (modes: Modes) (item: Item) (later: List Item)
    (line: lineAll later = True):
    matchesBarOn modes [item, ..later] = False :=
  match later with
    | [] => noBarOne modes item
    | [next, ..rest] => noBarPlain modes item next rest (linePlainKind next.kind (Bool.andLeft line))

theorem endsOperandOf ∀ (modes: Modes) (rest: List Item) (ends: endsHere rest = True): OperandEnds modes rest :=
  match rest with
    | [] => operandEndsNil modes
    | [next, ..later] => operandEndsAt modes next later (endKind next.kind ends)

theorem endsNotBrace ∀ (kind: Tok) (ends: endsOperand kind = True): (kind == LBrace) = False := cases

theorem endsAtom ∀ (modes: Modes)
    (quiet: Quiet modes)
    (head: Bool) (kind: Tok) (rest: List Item)
    (ends: endsHere rest = True):
    AtomEnds modes head kind rest :=
  let operand := endsOperandOf modes rest ends
  let plain: (isSome Upper (Some kind) && head && isSome LBrace (peekIn modes 0 rest)) = False := match rest with
    | [] => andFalseRight (isSome Upper (Some kind)) head _ byComputing
    | [next, ..later] =>
      andFalseRight
        (isSome Upper (Some kind))
        head _
        (rewrite quietPeek modes next later quiet then endsNotBrace next.kind ends)
  { plain, noCall = operand.noCall, noDot = operand.noDot }

theorem endsSteps ∀ (exprs: List Expr) (steps: List (Item, List Item, Expr)) (last: Item) (rest: List Item)
    (spelt: SpeltSteps exprs steps)
    (isEnd: endsOperand last.kind = True):
    endsHere (commaReads steps ++ [last, ..rest]) = True :=
  match exprs, spelt with
    | [], isEmpty => rewrite isEmpty then isEnd
    | [_, .._], (comma, _, _, isSteps, isComma, _, _) => rewrite isSteps, isComma

theorem andRightFalse ∀ (a b: Bool) (no: b = False): (a && b) = False :=
  rewrite no then
    match a with
      | True => byComputing
      | False => byComputing

theorem endsNotUpper ∀ (kind: Tok) (ends: endsOperand kind = True): (kind == Upper) = False := cases

theorem autoSecond ∀ (item second: Item) (later: List Item)
    (no: (second.kind == Lower) = False):
    namelessAutoAt [item, second, ..later] = False :=
  match later with
    | [] => byComputing
    | [_, .._] => rewrite no

theorem autoAfterWord ∀ (item second: Item) (later: List Item)
    (ends: endsHere later = True):
    namelessAutoAt [item, second, ..later] = False :=
  match later with
    | [] => byComputing
    | [third, .._] => andFalseRight _ _ _ (endsNotUpper third.kind ends)

theorem firstKind ∀ (item first: Item) (more inside: List Item)
    (isRead: [item, ..more] = [first, ..inside]):
    item.kind = first.kind :=
  rewrite List.consInjectiveHead item first more inside isRead

--| No `[auto Upper` starts a list on one line with no calls: a word inside is followed by a comma or `]`.
--| No `[auto Upper` starts a list in this part, which has no calls: a word inside is followed by a comma or `]`.
--|
--| Proof idea: only a list starts with `[`; its first item's first token is a bracket, or a word followed by a comma
--| or the `]`.
theorem noAutoLine ∀ (expr: Expr) (item: Item) (more rest: List Item)
    (spelt: Spelt expr [item, ..more]):
    (item.kind == LBracket && namelessAutoAt [item, ..more ++ rest]) = False :=
  match expr, spelt with
    | Atom kind word, (first, isRead, isKind, _, word) =>
      rewrite firstKind item first more [] isRead, isKind, wordNotBracket kind word
    | Paren _ _ _, (first, inside, _, isRead, isOpen, _) => rewrite firstKind item first more _ isRead, isOpen
    | Tuple _ [_, _, .._] _ _, (first, _, _, _, _, _, isRead, _, isOpen, _) =>
      rewrite firstKind item first more _ isRead, isOpen
    | ListOf _ [] _ _, (first, last, isRead, _, _, _, isClose, _) =>
      let isMore: more = [last] := Eq.cong (.drop 1) isRead
      rewrite isMore then andRightFalse _ _ (autoSecond item last rest (rewrite isClose))
    | ListOf _ [one, ..others] _ _, (first, read1, steps, last, isRead, _, _, _, isClose, _, oneSpelt, stepsSpelt) =>
      let isMore: more = read1 ++ (commaReads steps ++ [last]) := Eq.cong (.drop 1) isRead
      let tail: (commaReads steps ++ [last]) ++ rest = commaReads steps ++ [last, ..rest] :=
        List.appendAssoc (commaReads steps) [last] rest
      let after := endsSteps others steps last rest stepsSpelt (rewrite isClose)
      rewrite isMore then
        match one, oneSpelt with
          | Atom _ _, (second, isRead1, _) =>
            rewrite isRead1, tail then andRightFalse _ _ (autoAfterWord item second _ after)
          | Paren _ _ _, (second, _, _, isRead1, isOpen, _) =>
            rewrite isRead1 then andRightFalse _ _ (autoSecond item second _ (rewrite isOpen))
          | Tuple _ [_, _, .._] _ _, (second, _, _, _, _, _, isRead1, _, isOpen, _) =>
            rewrite isRead1 then andRightFalse _ _ (autoSecond item second _ (rewrite isOpen))
          | ListOf _ [] _ _, (second, _, isRead1, _, isOpen, _) =>
            rewrite isRead1, isOpen then andRightFalse _ _ byComputing
          | ListOf _ [_, .._] _ _, (second, _, _, _, isRead1, _, isOpen, _) =>
            rewrite isRead1 then andRightFalse _ _ (autoSecond item second _ (rewrite isOpen))
          | _, never => Void.impossible never
    | _, never => Void.impossible never

theorem commaDoneSteps ∀ (exprs: List Expr) (steps: List (Item, List Item, Expr)) (current: Expr) (found: List Expr)
    (spelt: SpeltSteps exprs steps):
    commaDone current found steps = found.reverse ++ [current, ..exprs] :=
  match exprs, spelt with
    | [], isEmpty => rewrite isEmpty then List.reverseCons current found
    | [expr, ..rest], (_, _, later, isSteps, _, _, restSpelt) =>
      rewrite isSteps, commaDoneSteps rest later expr [current, ..found] restSpelt, List.reverseCons current found then
        List.appendAssoc found.reverse [current] [expr, ..rest]

theorem exprHeadSteps ∀ (exprs: List Expr) (steps: List (Item, List Item, Expr)) (last: Item) (rest: List Item)
    (spelt: SpeltSteps exprs steps)
    (lastExpr: exprKind last.kind = True):
    exprHead ((commaReads steps ++ [last]) ++ rest) = True :=
  match exprs, spelt with
    | [], isEmpty => rewrite isEmpty then lastExpr
    | [_, .._], (comma, _, _, isSteps, isComma, _, _) => rewrite isSteps, isComma

theorem startNotClose ∀ (kind: Tok)
    (starts: startKind kind = True):
    (kind == RParen) = False ∧ (kind == RBracket) = False ∧ (kind == DotDot) = False :=
  cases

theorem lineJoin ∀ (first rest: List Item)
    (lineFirst: lineAll first = True)
    (lineRest: lineAll rest = True):
    lineAll (first ++ rest) = True :=
  rewrite lineAppend first rest, lineFirst, lineRest

theorem lineSplit ∀ (first rest: List Item)
    (line: lineAll (first ++ rest) = True):
    lineAll first = True ∧ lineAll rest = True :=
  andBoth _ _ (rewrite <- lineAppend first rest then line)

theorem inLineSplit ∀ (first rest: List Item)
    (line: inLineAll (first ++ rest) = True):
    inLineAll first = True ∧ inLineAll rest = True :=
  andBoth _ _ (rewrite <- inLineAppend first rest then line)

--| A spelt expression is what `expr` reads in quiet modes, at any depth its nesting fits in: its atom reading
--| (`atomLine`) lifted by `fullOfAtom`, the look-aheads from the kinds and what follows.
theorem fullLine ∀ (modes: Modes)
    (quiet: Quiet modes)
    (expr: Expr) (read rest: List Item) (depth: Nat)
    (deep: expr.nest1 <= depth)
    (spelt: Spelt expr read)
    (lineRead: lineAll read = True)
    (lineRest: lineAll rest = True)
    (inLine: inLineAll read = True)
    (ends: endsHere rest = True):
    FullReads (TreeN depth) modes read rest expr :=
  let atom := atomLine modes quiet True expr read rest depth deep spelt lineRead lineRest inLine ends
  let (item, more, isRead, starts) := speltStarts expr read spelt
  let sameSpelt: Spelt expr [item, ..more] := rewrite <- isRead then spelt
  let lineItems: lineAll [item, ..more] = True := rewrite <- isRead then lineRead
  let inItems: inLineAll [item, ..more] = True := rewrite <- isRead then inLine
  let lineAfter: lineAll (more ++ rest) = True := lineJoin more rest (Bool.andRight lineItems) lineRest
  rewrite isRead then
    fullOfAtom
      (TreeN depth)
      modes
      item
      more
      rest
      expr
      (notTrueFalse _ (Bool.andLeft inItems))
      (quietStops modes item quiet)
      starts
      (noBarLine modes item (more ++ rest) lineAfter)
      (inlinePlainOf modes item
        (more ++ rest)
        (linePlain [item, ..more ++ rest] (lineJoin [item, ..more] rest lineItems lineRest))
        (noAutoLine expr item more rest sameSpelt))
      (endsOperandOf modes rest ends)
      (rewrite <- isRead then atom)

--| A spelt expression is what `atom` reads, at any depth its nesting fits in.
--|
--| Proof idea: by induction on the expression, with `fullLine` for the brackets' items one level down
--| (`tupleSteps` and `listSteps` for the items after the first). A word is `WordBase`; a bracket is its base with
--| the look-aheads from the first two items inside (`startOutside`, `startBracketPlain`, `peekTwo`) and the kinds
--| (`rightLine`), each item followed by a comma or the closer.
theorem atomLine ∀ (modes: Modes)
    (quiet: Quiet modes)
    (head: Bool) (expr: Expr) (read rest: List Item) (depth: Nat)
    (deep: expr.nest1 <= depth)
    (spelt: Spelt expr read)
    (lineRead: lineAll read = True)
    (lineRest: lineAll rest = True)
    (inLine: inLineAll read = True)
    (ends: endsHere rest = True):
    AtomReads (TreeN depth) modes head read rest expr :=
  let inner := modes.inBrackets
  let innerQuiet := quietBrackets modes quiet
  match expr, spelt with
    | Atom kind word, (item, isRead, isKind, isWord, word) =>
      rewrite isRead then
        (
          item,
          [],
          byComputing,
          quietStops modes item quiet,
          endsAtom modes quiet head item.kind rest ends,
          Inl (byComputing, (rewrite isKind, isWord), rewrite isKind then (wordPlain kind word).left)
        )
    | Paren open body close, (first, inside, last, isRead, isOpen, isOpenWord, isClose, isCloseWord, bodySpelt) =>
      match depth, deep with
        | Zero, deep => Void.impossible (arithmetic [deep])
        | Succ below, deep =>
          let lineItems: lineAll [first, ..inside ++ [last]] = True := rewrite <- isRead then lineRead
          let inItems: inLineAll [first, ..inside ++ [last]] = True := rewrite <- isRead then inLine
          let (lineInside, lineLast) := lineSplit inside [last] (Bool.andRight lineItems)
          let (inInside, _) := inLineSplit inside [last] (Bool.andRight inItems)
          let bodyTree: TreeN (Succ below) { modes = inner, level = LevelFull } inside [last, ..rest] body :=
            fullLine inner innerQuiet body inside
              [last, ..rest]
              below
              (arithmetic [deep])
              bodySpelt
              lineInside
              (lineJoin [last] rest lineLast lineRest)
              inInside
              (rewrite isClose)
          let (second, more, isInside, starts) := speltStarts body inside bodySpelt
          let kinds: exprAll [second, ..more] = True := rewrite <- isInside then speltExpr body inside bodySpelt
          let (kind, peek2, kindExpr) :=
            peekTwo modes quiet first second more [last, ..rest] (Bool.andRight kinds) (rewrite isClose)
          let assoc: (inside ++ [last]) ++ rest = inside ++ [last, ..rest] := List.appendAssoc inside [last] rest
          let plain: ParenPlain modes [first, ..(inside ++ [last]) ++ rest] := {
            notOutside = rewrite assoc,
                isInside,
                quietPeekSecond modes first second (more ++ [last, ..rest]) quiet,
                peek2 then
              startOutside second.kind kind starts kindExpr,
            noRight = rightLine first
              ((inside ++ [last]) ++ rest)
              (lineJoin (inside ++ [last]) rest (Bool.andRight lineItems) lineRest)
          }
          rewrite isRead then
            (
              first,
              inside ++ [last],
              byComputing,
              quietStops modes first quiet,
              endsAtom modes quiet head first.kind rest ends,
              Inr
                (Inl (
                  inside,
                  last,
                  body,
                  byComputing,
                  (rewrite isOpenWord, isCloseWord),
                  isOpen,
                  plain,
                  bodyTree,
                  quietStops inner last innerQuiet,
                  isClose
                ))
            )
    | Tuple open [one, two, ..others] comma close, (first, read1, separator, read2, steps, last, isRead, isBare, isOpen,
        isOpenWord, isComma, isClose, isCloseWord, oneSpelt, twoSpelt, stepsSpelt) =>
      match depth, deep with
        | Zero, deep => Void.impossible (arithmetic [deep])
        | Succ below, deep =>
          let elements := [separator, ..read2] ++ (commaReads steps ++ [last])
          let lineItems: lineAll [first, ..read1 ++ elements] = True := rewrite <- isRead then lineRead
          let inItems: inLineAll [first, ..read1 ++ elements] = True := rewrite <- isRead then inLine
          let (line1, lineElements) := lineSplit read1 elements (Bool.andRight lineItems)
          let (line2, lineSteps) := lineSplit read2 (commaReads steps ++ [last]) (Bool.andRight lineElements)
          let (lineCommas, lineLast) := lineSplit (commaReads steps) [last] lineSteps
          let (in1, inElements) := inLineSplit read1 elements (Bool.andRight inItems)
          let (in2, inSteps) := inLineSplit read2 (commaReads steps ++ [last]) (Bool.andRight inElements)
          let (inCommas, _) := inLineSplit (commaReads steps) [last] inSteps
          let goal: Goal := { modes = inner, level = LevelFull }
          let oneTree: TreeN (Succ below) goal read1 (elements ++ rest) one :=
            fullLine inner innerQuiet one read1
              (elements ++ rest)
              below
              (arithmetic [deep])
              oneSpelt
              line1
              (lineJoin elements rest lineElements lineRest)
              in1
              (rewrite isComma)
          let twoTree: TreeN (Succ below) goal read2 ((commaReads steps ++ [last]) ++ rest) two :=
            fullLine inner innerQuiet two read2
              ((commaReads steps ++ [last]) ++ rest)
              below
              (arithmetic [deep])
              twoSpelt
              line2
              (lineJoin (commaReads steps ++ [last]) rest lineSteps lineRest)
              in2
              (rewrite List.appendAssoc (commaReads steps) [last] rest then
                endsSteps others steps last rest stepsSpelt (rewrite isClose))
          let rounds: CommaReads inner (tupleEnds inner) (TreeN (Succ below) goal) 2 steps [last, ..rest] :=
            tupleSteps inner innerQuiet others steps 2 last rest below
              (arithmetic [deep])
              stepsSpelt
              lineCommas
              (lineJoin [last] rest lineLast lineRest)
              inCommas
              isClose
          let (second, more, isRead1, starts) := speltStarts one read1 oneSpelt
          let kinds: exprAll [second, ..more] = True := rewrite <- isRead1 then speltExpr one read1 oneSpelt
          let (kind, peek2, kindExpr) :=
            peekTwo modes quiet first second more (elements ++ rest) (Bool.andRight kinds) (rewrite isComma)
          let assoc: (read1 ++ elements) ++ rest = read1 ++ (elements ++ rest) := List.appendAssoc read1 elements rest
          let plain: ParenPlain modes [first, ..(read1 ++ elements) ++ rest] := {
            notOutside = rewrite assoc,
                isRead1,
                quietPeekSecond modes first second (more ++ (elements ++ rest)) quiet,
                peek2 then
              startOutside second.kind kind starts kindExpr,
            noRight = rightLine first
              ((read1 ++ elements) ++ rest)
              (lineJoin (read1 ++ elements) rest (Bool.andRight lineItems) lineRest)
          }
          rewrite isRead then
            (
              first,
              read1 ++ elements,
              byComputing,
              quietStops modes first quiet,
              endsAtom modes quiet head first.kind rest ends,
              Inr
                (Inr
                  (Inl (
                    read1,
                    separator,
                    read2,
                    steps,
                    last,
                    one,
                    two,
                    byComputing,
                    (rewrite isBare, isOpenWord, isCloseWord, commaDoneSteps others steps two [one] stepsSpelt),
                    isOpen,
                    plain,
                    oneTree,
                    quietStops inner separator innerQuiet,
                    isComma,
                    twoTree,
                    rounds,
                    quietStops inner last innerQuiet,
                    isClose
                  )))
            )
    | ListOf open [] comma close, (first, last, isRead, isBare, isOpen, isOpenWord, isClose, isCloseWord) =>
      rewrite isRead then
        (
          first,
          [last],
          byComputing,
          quietStops modes first quiet,
          endsAtom modes quiet head first.kind rest ends,
          Inr
            (Inr
              (Inr
                (Inl (
                  last,
                  byComputing,
                  (rewrite isBare, isOpenWord, isCloseWord),
                  isOpen,
                  (rewrite quietPeekSecond modes first last rest quiet, isClose),
                  quietStops inner last innerQuiet,
                  isClose
                ))))
        )
    | ListOf open [one, ..others] comma close, (first, read1, steps, last, isRead, isBare, isOpen, isOpenWord, isClose,
        isCloseWord, oneSpelt, stepsSpelt) =>
      match depth, deep with
        | Zero, deep => Void.impossible (arithmetic [deep])
        | Succ below, deep =>
          let elements := commaReads steps ++ [last]
          let lineItems: lineAll [first, ..read1 ++ elements] = True := rewrite <- isRead then lineRead
          let inItems: inLineAll [first, ..read1 ++ elements] = True := rewrite <- isRead then inLine
          let (line1, lineElements) := lineSplit read1 elements (Bool.andRight lineItems)
          let (lineCommas, lineLast) := lineSplit (commaReads steps) [last] lineElements
          let (in1, inElements) := inLineSplit read1 elements (Bool.andRight inItems)
          let (inCommas, _) := inLineSplit (commaReads steps) [last] inElements
          let goal: Goal := { modes = inner, level = LevelFull }
          let (second, more, isRead1, starts) := speltStarts one read1 oneSpelt
          let (_, notBracket, notSpread) := startNotClose second.kind starts
          let oneTree: TreeN (Succ below) goal read1 (elements ++ rest) one :=
            fullLine inner innerQuiet one read1
              (elements ++ rest)
              below
              (arithmetic [deep])
              oneSpelt
              line1
              (lineJoin elements rest lineElements lineRest)
              in1
              (rewrite List.appendAssoc (commaReads steps) [last] rest then
                endsSteps others steps last rest stepsSpelt (rewrite isClose))
          let rounds: CommaReads inner (count => inner.at RBracket) (ListElement (TreeN (Succ below)) inner) 1 steps [
            last,
            ..rest
          ] :=
            listSteps inner innerQuiet others steps 1 last rest below
              (arithmetic [deep])
              stepsSpelt
              lineCommas
              (lineJoin [last] rest lineLast lineRest)
              inCommas
              isClose
          let kinds: exprAll [second, ..more] = True := rewrite <- isRead1 then speltExpr one read1 oneSpelt
          let (kind, peek2, kindExpr) :=
            peekTwo modes quiet first second more
              (elements ++ rest)
              (Bool.andRight kinds)
              (exprHeadSteps others steps last rest stepsSpelt (rewrite isClose))
          let assoc: (read1 ++ elements) ++ rest = read1 ++ (elements ++ rest) := List.appendAssoc read1 elements rest
          let firstPeek: peekIn inner 0 ((read1 ++ elements) ++ rest) = Some second.kind :=
            rewrite assoc, isRead1 then quietPeek inner second (more ++ (elements ++ rest)) innerQuiet
          let elementPeek: peekIn inner 0 (read1 ++ (elements ++ rest)) = Some second.kind :=
            rewrite isRead1 then quietPeek inner second (more ++ (elements ++ rest)) innerQuiet
          rewrite isRead then
            (
              first,
              read1 ++ elements,
              byComputing,
              quietStops modes first quiet,
              endsAtom modes quiet head first.kind rest ends,
              Inr
                (Inr
                  (Inr
                    (Inr
                      (Inl (
                        read1,
                        steps,
                        last,
                        one,
                        byComputing,
                        (rewrite isBare, isOpenWord, isCloseWord, commaDoneSteps others steps one [] stepsSpelt),
                        isOpen,
                        (rewrite assoc,
                            isRead1,
                            quietPeekSecond modes first second (more ++ (elements ++ rest)) quiet,
                            peek2 then
                          startBracketPlain second.kind kind starts kindExpr),
                        (rewrite firstPeek then notBracket),
                        ((rewrite elementPeek then notSpread), oneTree),
                        rounds,
                        quietStops inner last innerQuiet,
                        isClose
                      )))))
            )
    | _, never => Void.impossible never

--| A tuple's items after the second, spelt, are its `CommaReads`, each read by `fullLine`.
theorem tupleSteps ∀ (modes: Modes)
    (quiet: Quiet modes)
    (exprs: List Expr) (steps: List (Item, List Item, Expr)) (count: Nat) (last: Item) (rest: List Item) (depth: Nat)
    (deep: nestAll exprs <= depth)
    (spelt: SpeltSteps exprs steps)
    (lineSteps: lineAll (commaReads steps) = True)
    (lineRest: lineAll [last, ..rest] = True)
    (inSteps: inLineAll (commaReads steps) = True)
    (isClose: last.kind = RParen):
    CommaReads modes (tupleEnds modes) (TreeN (Succ depth) { modes, level = LevelFull }) count steps [last, ..rest] :=
  match exprs, spelt with
    | [], isEmpty => rewrite isEmpty, quietPeek modes last rest quiet, isClose
    | [expr, ..more], (comma, read, later, isSteps, isComma, exprSpelt, moreSpelt) =>
      let lineAll1: lineAll [comma, ..read ++ commaReads later] = True :=
        Eq.trans (Eq.cong (taken => lineAll (commaReads taken)) isSteps).flipped lineSteps
      let inAll1: inLineAll [comma, ..read ++ commaReads later] = True :=
        Eq.trans (Eq.cong (taken => inLineAll (commaReads taken)) isSteps).flipped inSteps
      let (lineRead, lineLater) := lineSplit read (commaReads later) (Bool.andRight lineAll1)
      let (inRead, inLater) := inLineSplit read (commaReads later) (Bool.andRight inAll1)
      let (first, inside, isRead, starts) := speltStarts expr read exprSpelt
      let (notClose, _, _) := startNotClose first.kind starts
      rewrite isSteps then
        (
          quietStops modes comma quiet,
          isComma,
          runsTupleEndsGo modes count
            (read ++ commaReads later ++ [last, ..rest])
            (rewrite isRead, quietPeek modes first (inside ++ commaReads later ++ [last, ..rest]) quiet then notClose),
          fullLine modes quiet expr read
            (commaReads later ++ [last, ..rest])
            depth
            (arithmetic [deep])
            exprSpelt
            lineRead
            (lineJoin (commaReads later) [last, ..rest] lineLater lineRest)
            inRead
            (endsSteps more later last rest moreSpelt (rewrite isClose)),
          tupleSteps modes quiet more later
            (count + 1)
            last
            rest
            depth
            (arithmetic [deep])
            moreSpelt
            lineLater
            lineRest
            inLater
            isClose
        )

--| A list's items after the first, spelt, are its `CommaReads`, each read by `fullLine` after no `..`.
theorem listSteps ∀ (modes: Modes)
    (quiet: Quiet modes)
    (exprs: List Expr) (steps: List (Item, List Item, Expr)) (count: Nat) (last: Item) (rest: List Item) (depth: Nat)
    (deep: nestAll exprs <= depth)
    (spelt: SpeltSteps exprs steps)
    (lineSteps: lineAll (commaReads steps) = True)
    (lineRest: lineAll [last, ..rest] = True)
    (inSteps: inLineAll (commaReads steps) = True)
    (isClose: last.kind = RBracket):
    CommaReads modes (count => modes.at RBracket) (ListElement (TreeN (Succ depth)) modes) count steps [last, ..rest] :=
  match exprs, spelt with
    | [], isEmpty => rewrite isEmpty, quietPeek modes last rest quiet, isClose
    | [expr, ..more], (comma, read, later, isSteps, isComma, exprSpelt, moreSpelt) =>
      let lineAll1: lineAll [comma, ..read ++ commaReads later] = True :=
        Eq.trans (Eq.cong (taken => lineAll (commaReads taken)) isSteps).flipped lineSteps
      let inAll1: inLineAll [comma, ..read ++ commaReads later] = True :=
        Eq.trans (Eq.cong (taken => inLineAll (commaReads taken)) isSteps).flipped inSteps
      let (lineRead, lineLater) := lineSplit read (commaReads later) (Bool.andRight lineAll1)
      let (inRead, inLater) := inLineSplit read (commaReads later) (Bool.andRight inAll1)
      let (first, inside, isRead, starts) := speltStarts expr read exprSpelt
      let (_, notBracket, notSpread) := startNotClose first.kind starts
      let firstPeek: peekIn modes 0 (read ++ commaReads later ++ [last, ..rest]) = Some first.kind :=
        rewrite isRead then quietPeek modes first (inside ++ commaReads later ++ [last, ..rest]) quiet
      rewrite isSteps then
        (
          quietStops modes comma quiet,
          isComma,
          (rewrite <- (rewrite firstPeek then notBracket: isSome RBracket
                (peekIn modes 0 (read ++ commaReads later ++ [last, ..rest]))
                = False) then
            runsAtOn modes RBracket (read ++ commaReads later ++ [last, ..rest])),
          (
            (rewrite firstPeek then notSpread),
            fullLine modes quiet expr read
              (commaReads later ++ [last, ..rest])
              depth
              (arithmetic [deep])
              exprSpelt
              lineRead
              (lineJoin (commaReads later) [last, ..rest] lineLater lineRest)
              inRead
              (endsSteps more later last rest moreSpelt (rewrite isClose))
          ),
          listSteps modes quiet more later
            (count + 1)
            last
            rest
            depth
            (arithmetic [deep])
            moreSpelt
            lineLater
            lineRest
            inLater
            isClose
        )

theorem startNotBrace ∀ (kind: Tok) (starts: startKind kind = True): (kind == LBrace) = False := cases

--| The read-back of a one-line declaration (ticket 17d, first part): `def name: A := b`, with `A` and `b` words,
--| parentheses, tuples and lists spelt by the items between `:` and `:=` and after `:=`, none starting a line, parses
--| as `parseGroups` runs it to that definition, the words being the items'.
--|
--| Proof idea: `declarationTree`, with the type and value as `fullLine` trees at their nesting depth, the modes of the
--| start and the body being quiet.
theorem readsBackLine ∀ (seen: Seen) (keyword name colon colonEq: Item)
    (typeRead valueRead: List Item) (result value: Expr)
    (isDef: keyword.kind = KwDef)
    (isLower: name.kind = Lower)
    (isColon: colon.kind = Colon)
    (isColonEq: colonEq.kind = ColonEq)
    (typeSpelt: Spelt result typeRead)
    (valueSpelt: Spelt value valueRead)
    (typeLine: lineAll typeRead = True)
    (valueLine: lineAll valueRead = True)
    (typeInLine: inLineAll typeRead = True)
    (valueInLine: inLineAll valueRead = True):
    Parse.run [keyword, name, colon, ..typeRead ++ [colonEq, ..valueRead]] (() =>
      let decl := declaration seen
      decl)
      = Ok (Definition [] (plainHeader keyword name colon result) (Assigned colonEq.leaf.word.comments value)) :=
  let startQuiet: Quiet Modes.start :=
    { noGuard = byComputing, noCalc = byComputing, noRule = byComputing, noLimit = byComputing }
  let body := { Modes.start | recover = True }
  let bodyQuiet: Quiet body :=
    { noGuard = byComputing, noCalc = byComputing, noRule = byComputing, noLimit = byComputing }
  let after := [colonEq, ..valueRead]
  let lineAfter: lineAll after = True := rewrite isColonEq, valueLine
  let (first, more, isType, starts) := speltStarts result typeRead typeSpelt
  let allowed: allowBraceOn Modes.start (typeRead ++ after) = Modes.start := rewrite isType
  let noRow: rowOn
    (isSome LBrace (peekIn (allowBraceOn Modes.start (typeRead ++ after)) 0 (typeRead ++ after)))
    (typeRead ++ after)
    = False :=
    rewrite allowed, isType, quietPeek Modes.start first (more ++ after) startQuiet, startNotBrace first.kind starts
  let typeTree: Tree { modes = allowBraceOn Modes.start (typeRead ++ after), level = LevelFull } typeRead after
      result :=
    rewrite allowed then
      (
        Succ result.nest1,
        fullLine Modes.start startQuiet result typeRead after result.nest1
          (arithmetic [])
          typeSpelt
          typeLine
          lineAfter
          typeInLine
          (rewrite isColonEq)
      )
  let valueTree: Tree { modes = body, level = LevelFull } valueRead [] value := (
    Succ value.nest1,
    fullLine body bodyQuiet value valueRead [] value.nest1
      (arithmetic [])
      valueSpelt
      valueLine
      byComputing
      valueInLine
      byComputing
  )
  declarationTree seen keyword name colon colonEq typeRead valueRead result value {
    isDef,
    isLower,
    isColon,
    isColonEq,
    typeReads = (noRow, typeTree),
    valueTree
  }

--| `(a, [b])`, as `wordItem`s from index 5: the value of `readsBackLineExample`.
def exampleItems: List Item := [
  wordItem LParen "(" 5,
  wordItem Lower "a" 6,
  wordItem Comma "," 7,
  wordItem LBracket "[" 8,
  wordItem Lower "b" 9,
  wordItem RBracket "]" 10,
  wordItem RParen ")" 11
]

def exampleValue: Expr :=
  Tuple
    (wordItem LParen "(" 5).leaf.word
    [
      Atom Lower (wordItem Lower "a" 6).leaf.word,
      ListOf
        (wordItem LBracket "[" 8).leaf.word
        [Atom Lower (wordItem Lower "b" 9).leaf.word]
        False
        (wordItem RBracket "]" 10).leaf.word
    ]
    False
    (wordItem RParen ")" 11).leaf.word

--| `def d: A := (a, [b])` on one line: `readsBackLine`'s hypotheses can hold.
theorem readsBackLineExample: Parse.run
      [
        wordItem KwDef "def" 0,
        wordItem Lower "d" 1,
        wordItem Colon ":" 2,
        ..[wordItem Upper "A" 3] ++ [wordItem ColonEq ":=" 4, ..exampleItems]
      ]
      (() =>
        let decl := declaration Seen.start
        decl)
      = Ok
        (Definition []
          (plainHeader
            (wordItem KwDef "def" 0)
            (wordItem Lower "d" 1)
            (wordItem Colon ":" 2)
            (Atom Upper (wordItem Upper "A" 3).leaf.word))
          (Assigned (wordItem ColonEq ":=" 4).leaf.word.comments exampleValue)) :=
  readsBackLine Seen.start
    (wordItem KwDef "def" 0)
    (wordItem Lower "d" 1)
    (wordItem Colon ":" 2)
    (wordItem ColonEq ":=" 4)
    [wordItem Upper "A" 3]
    exampleItems
    (Atom Upper (wordItem Upper "A" 3).leaf.word)
    exampleValue
    byComputing
    byComputing
    byComputing
    byComputing
    (wordItem Upper "A" 3, byComputing, byComputing, byComputing, byComputing)
    (
      wordItem LParen "(" 5,
      [wordItem Lower "a" 6],
      wordItem Comma "," 7,
      [wordItem LBracket "[" 8, wordItem Lower "b" 9, wordItem RBracket "]" 10],
      [],
      wordItem RParen ")" 11,
      byComputing,
      byComputing,
      byComputing,
      byComputing,
      byComputing,
      byComputing,
      byComputing,
      (wordItem Lower "a" 6, byComputing, byComputing, byComputing, byComputing),
      (
        wordItem LBracket "[" 8,
        [wordItem Lower "b" 9],
        [],
        wordItem RBracket "]" 10,
        byComputing,
        byComputing,
        byComputing,
        byComputing,
        byComputing,
        byComputing,
        (wordItem Lower "b" 9, byComputing, byComputing, byComputing, byComputing),
        byComputing
      ),
      byComputing
    )
    byComputing
    byComputing
    byComputing
    byComputing

--| A group closed at once: `groupLine`'s hypotheses can hold.
theorem groupLineExample: headPlain [wordItem Lower "a" 1].reverse = True :=
  groupLine
    [LParen]
    []
    [wordItem Lower "a" 1, wordItem RParen ")" 2]
    [wordItem Lower "a" 1]
    byComputing
    byComputing
    byComputing

theorem firstKindExample: (wordItem Lower "a" 0).kind = (wordItem Lower "a" 0).kind :=
  firstKind (wordItem Lower "a" 0) (wordItem Lower "a" 0) [] [] byComputing
