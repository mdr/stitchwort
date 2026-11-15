--| The expression parser read backwards: on tokens that spell an
--| expression (`Spelled`) of the shape the parser gives (`Shaped`),
--| `expression` gives that expression back. Built from std's completeness
--| lemmas (`Parse.Runs`), `Parse.runsOperators` for the operator chains.

namespace Toy.Syntax.Proofs
import Toy.Syntax (..)
import Std.Parse.Associativity (LeftAssociative)
import Std.Parse.OperatorTree (Joined, Operand)
import Std (Bool, Eq, List, Option, Parse, Text, Void)

theorem runsSkip ∀ (token: Parse.Located Token) (rest: List (Parse.Located Token)):
    Parse.Runs (() => skip()) [token] rest () :=
  Parse.runsMap
    (() => Parse.next (token => True))
    (skipped => ())
    [token]
    rest
    (Some token)
    (Parse.runsNext (token => True) token rest rfl)

theorem runsSign ∀ (layout: Layout) (what: Text) (wanted: Punctuation)
    (token: Parse.Located Token) (rest: List (Parse.Located Token))
    (signed: token.value.kind = Sign wanted)
    (allowed: layout.allows token = True):
    Parse.Runs (() => sign layout what wanted) [token] rest () :=
  Parse.runsOne what
    (selectAllowed layout (signIs wanted))
    token
    ()
    rest
    (rewrite allowed, signed in
      match wanted with
        | OpenParen => rfl
        | CloseParen => rfl
        | OpenSquare => rfl
        | CloseSquare => rfl
        | Comma => rfl
        | Dot => rfl
        | Defines => rfl)

theorem runsName ∀ (layout: Layout) (token: Parse.Located Token) (text: Text) (rest: List (Parse.Located Token))
    (named: token.value.kind = Name text)
    (allowed: layout.allows token = True):
    Parse.Runs (() => name layout) [token] rest text :=
  Parse.runsOne "a name" (selectAllowed layout nameOf) token text rest (rewrite allowed, named in rfl)

theorem runsAtomNumber ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout)
    (token: Parse.Located Token) (digits: Text) (rest: List (Parse.Located Token))
    (numbered: token.value.kind = Number digits)
    (allowed: layout.allows token = True):
    Parse.Runs (() => atom self layout) [token] rest (NumberLiteral digits) :=
  state starts honest =>
    let lengths: state.at.rest.length = rest.length + 1 := rewrite starts in rfl
    Witness
      (state.advance rest 1).at
      (Both (rewrite starts, allowed, numbered, starts in rfl) (Both rfl (Both (omega [honest, lengths]) rfl)))

theorem runsAtomString ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout)
    (token: Parse.Located Token) (written: Text) (rest: List (Parse.Located Token))
    (quoted: token.value.kind = Str written)
    (allowed: layout.allows token = True):
    Parse.Runs (() => atom self layout) [token] rest (StringLiteral written) :=
  state starts honest =>
    let lengths: state.at.rest.length = rest.length + 1 := rewrite starts in rfl
    Witness
      (state.advance rest 1).at
      (Both (rewrite starts, allowed, quoted, starts in rfl) (Both rfl (Both (omega [honest, lengths]) rfl)))

theorem runsAtomBracketed ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout)
    (open close: Parse.Located Token) (innerTokens rest: List (Parse.Located Token)) (inner: Expr)
    (opens: open.value.kind = Sign OpenParen)
    (allowed: layout.allows open = True)
    (closes: close.value.kind = Sign CloseParen)
    (runsInner: Parse.Runs (() => self InBrackets) innerTokens [close, ..rest] inner):
    Parse.Runs (() => atom self layout) [open, ..innerTokens ++ [close]] rest (Bracketed inner) :=
  state starts honest =>
    let core :=
      Parse.runsBind
        (() => skip())
        (skipped =>
          let inner := self InBrackets
          sign InBrackets "')'" CloseParen
          Bracketed inner)
        [open]
        (innerTokens ++ [close])
        [open, ..innerTokens ++ [close]]
        rest
        ()
        (Bracketed inner)
        rfl
        (runsSkip open ((innerTokens ++ [close]) ++ rest))
        (Parse.runsBind
          (() => self InBrackets)
          (inner =>
            sign InBrackets "')'" CloseParen
            Bracketed inner)
          innerTokens
          [close]
          (innerTokens ++ [close])
          rest
          inner
          (Bracketed inner)
          rfl
          runsInner
          (Parse.runsMap
            (() => sign InBrackets "')'" CloseParen)
            (closed => Bracketed inner)
            [close]
            rest
            ()
            (runsSign InBrackets "')'" CloseParen close rest closes rfl)))
    match core state starts honest with
      | Witness m (Both ran others) => Witness m (Both (rewrite starts, allowed, opens in ran) others)

--| A round of `suffixesFrom` that reads a field: `.`, a name, and on from
--| the target with the field.
theorem runsSuffixesField ∀ (more: Nat) (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout)
    (target: Expr) (dot named: Parse.Located Token) (field: Text) (after rest: List (Parse.Located Token)) (value: Expr)
    (dotted: dot.value.kind = Sign Dot)
    (dotAllowed: layout.allows dot = True)
    (isName: named.value.kind = Name field)
    (nameAllowed: layout.allows named = True)
    (runsMore: Parse.Runs (() => suffixesFrom more self layout (Field target field)) after rest value):
    Parse.Runs (() => suffixesFrom (Succ more) self layout target) [dot, named, ..after] rest value :=
  state starts honest =>
    let core :=
      Parse.runsBind
        (() =>
          Parse.optional (() =>
            skip()
            Field target (name layout)))
        (suffixesAfter more self layout target)
        [dot, named]
        after
        [dot, named, ..after]
        rest
        (Some (Field target field))
        value
        rfl
        (Parse.runsOptional
          (() =>
            skip()
            Field target (name layout))
          [dot, named]
          (after ++ rest)
          (Field target field)
          (Parse.runsBind
            (() => skip())
            (skipped => Field target (name layout))
            [dot]
            [named]
            [dot, named]
            (after ++ rest)
            ()
            (Field target field)
            rfl
            (runsSkip dot [named, ..after ++ rest])
            (Parse.runsMap
              (() => name layout)
              (found => Field target found)
              [named]
              (after ++ rest)
              field
              (runsName layout named field (after ++ rest) isName nameAllowed))))
        runsMore
    match core state starts honest with
      | Witness m (Both ran others) => Witness m (Both (rewrite starts, dotAllowed, dotted in ran) others)

--| A round of `negationsFrom` that reads a `-`.
theorem runsNegation ∀ (more: Nat) (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout)
    (minus: Parse.Located Token) (tokens rest: List (Parse.Located Token)) (operand: Expr)
    (isMinusSign: minus.value.kind = Op Minus)
    (allowed: layout.allows minus = True)
    (runsOperand: Parse.Runs (() => negationsFrom more self layout) tokens rest operand):
    Parse.Runs (() => negationsFrom (Succ more) self layout) [minus, ..tokens] rest (Negate operand) :=
  state starts honest =>
    let core :=
      Parse.runsBind
        (() => skip())
        (skipped => Negate (negationsFrom more self layout))
        [minus]
        tokens
        [minus, ..tokens]
        rest
        ()
        (Negate operand)
        rfl
        (runsSkip minus (tokens ++ rest))
        (Parse.runsMap (() => negationsFrom more self layout) (inner => Negate inner) tokens rest operand runsOperand)
    match core state starts honest with
      | Witness m (Both ran others) => Witness m (Both (rewrite starts, allowed, isMinusSign in ran) others)

--| An atom, then its suffixes: what `negationsFrom` reads once the `-`s
--| are done. The suffix loop's fuel is the tokens left, so `runsSuffixes`
--| is asked for any fuel above what it reads.
theorem runsAtomThenSuffixes ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout)
    (atomTokens more rest: List (Parse.Located Token)) (first value: Expr)
    (runsAtom: Parse.Runs (() => atom self layout) atomTokens (more ++ rest) first)
    (runsSuffixes: ∀ (fuel: Nat) => more.length < fuel
      → Parse.Runs (() => suffixesFrom fuel self layout first) more rest value):
    Parse.Runs
      (() =>
        let first := atom self layout
        suffixesFrom (Parse.mark().left + 1) self layout first)
      (atomTokens ++ more)
      rest
      value :=
  state =>
    Parse.runsFromBind state
      (() => atom self layout)
      (first => suffixesFrom (Parse.mark().left + 1) self layout first)
      atomTokens
      more
      (atomTokens ++ more)
      rest
      first
      value
      rfl
      runsAtom
      (middle atRest honest offset =>
        let lengths: middle.at.rest.length = more.length + rest.length := rewrite atRest in List.lengthAppend more rest
        Parse.runsFromMark middle
          (at => suffixesFrom (at.left + 1) self layout first)
          more
          rest
          value
          (runsSuffixes (middle.at.left + 1) (omega [honest, lengths]) middle))

--| An expression that `atom` and `suffixesFrom` read: an atom with its
--| calls and fields.
def Expr.isPostfix: Expr → Bool
  | Var _ => True
  | NumberLiteral _ => True
  | StringLiteral _ => True
  | Bracketed _ => True
  | ListLiteral _ => True
  | Call _ _ => True
  | Field _ _ => True
  | _ => False

--| An operand of an operator chain: a postfix expression, or `-` before
--| an operand.
def Expr.isOperand: Expr → Bool
  | Negate _ => True
  | expr => expr.isPostfix

--| An operator chain or an operand: any expression but an `if`, which
--| stands only as a whole expression.
def Expr.isChain: Expr → Bool
  | Binary _ _ _ => True
  | expr => expr.isOperand

--| The level of a chain's outermost operator; 7, past every level, for an
--| operand.
def Expr.chainLevel: Expr → Nat
  | Binary operator _ _ => operator.level
  | _ => 7

--| The shape of the expressions the parser gives, for the forms covered so
--| far (names, numbers, strings, brackets, fields, negation and operators;
--| lists, calls and `if` are not covered yet, so they are not `Shaped`): a
--| field's target is a postfix expression, `-` stands before an operand,
--| and an operator's sides are grouped by precedence, the same level
--| chaining from the left.
def Shaped: Expr → Prop
  | Var _ => True
  | NumberLiteral _ => True
  | StringLiteral _ => True
  | Bracketed inner => Shaped inner
  | Field target _ => target.isPostfix = True ∧ Shaped target
  | Negate operand => operand.isOperand = True ∧ Shaped operand
  | Binary operator left right =>
    operator.level ≤ left.chainLevel
      ∧ operator.level < right.chainLevel
      ∧ left.isChain = True
      ∧ right.isChain = True
      ∧ Shaped left
      ∧ Shaped right
  | _ => False

--| `tokens` spell `expr` at `layout`: its tokens in order, each of the kind
--| the expression has there and standing where the layout allows it
--| (anywhere, inside brackets). For the forms `Shaped` covers.
def Spelled (layout: Layout) (expr: Expr) (tokens: List (Parse.Located Token)): Prop := match expr with
  | Var name =>
    ∃ (token: Parse.Located Token) => tokens = [token] ∧ token.value.kind = Name name ∧ layout.allows token = True
  | NumberLiteral digits =>
    ∃ (token: Parse.Located Token) => tokens = [token] ∧ token.value.kind = Number digits ∧ layout.allows token = True
  | StringLiteral written =>
    ∃ (token: Parse.Located Token) => tokens = [token] ∧ token.value.kind = Str written ∧ layout.allows token = True
  | Bracketed inner =>
    ∃ (open: Parse.Located Token) => ∃ (innerTokens: List (Parse.Located Token)) => ∃ (close: Parse.Located Token) =>
      tokens = [open, ..innerTokens ++ [close]]
        ∧ open.value.kind = Sign OpenParen
        ∧ layout.allows open = True
        ∧ close.value.kind = Sign CloseParen
        ∧ Spelled InBrackets inner innerTokens
  | Field target name =>
    ∃ (targetTokens: List (Parse.Located Token)) => ∃ (dot: Parse.Located Token) => ∃ (named: Parse.Located Token) =>
      tokens = targetTokens ++ [dot, named]
        ∧ dot.value.kind = Sign Dot
        ∧ layout.allows dot = True
        ∧ named.value.kind = Name name
        ∧ layout.allows named = True
        ∧ Spelled layout target targetTokens
  | Negate operand =>
    ∃ (minus: Parse.Located Token) => ∃ (operandTokens: List (Parse.Located Token)) => tokens = [minus, ..operandTokens]
      ∧ minus.value.kind = Op Minus
      ∧ layout.allows minus = True
      ∧ Spelled layout operand operandTokens
  | Binary operator left right =>
    ∃ (leftTokens: List (Parse.Located Token)) => ∃ (sign: Parse.Located Token) =>
      ∃ (rightTokens: List (Parse.Located Token)) => tokens = leftTokens ++ [sign, ..rightTokens]
        ∧ sign.value.kind = Op operator
        ∧ layout.allows sign = True
        ∧ Spelled layout left leftTokens
        ∧ Spelled layout right rightTokens
  | _ => False

--| What may follow an expression at `layout`: no call or field of its last
--| operand, and no operator.
def EndsExpression (layout: Layout) (rest: List (Parse.Located Token)): Prop :=
  endsSuffixes (suffixKind layout rest) = True ∧ Parse.operatorAhead (operatorLevels layout) 0 rest = False

--| What the expression parser is assumed to do for the nested expressions
--| of one being read: it reads each well-shaped, well-spelled expression of
--| fewer than `bound` tokens, at any layout.
def ReadsNested (self: Layout → {Parse (Parse.Located Token)} Expr) (bound: Nat): Prop :=
  ∀ (layout: Layout) (expr: Expr) (tokens rest: List (Parse.Located Token)) => Shaped expr
    → Spelled layout expr tokens
    → EndsExpression layout rest
    → tokens.length < bound
    → Parse.Runs (() => self layout) tokens rest expr

--| Whether a `-` the layout allows comes next: what `negationsFrom` reads.
def minusAhead (layout: Layout) (input: List (Parse.Located Token)): Bool := match input with
  | [token, .._] => isMinus layout token
  | [] => False

--| Whether an `if` the layout allows comes next: what makes
--| `expressionRule` read an `if`.
def ifAhead (layout: Layout) (input: List (Parse.Located Token)): Bool := match input with
  | [token, .._] => isIf layout token
  | [] => False

--| A postfix expression starts with neither `-` nor `if`.
theorem postfixStart ∀ (layout: Layout) (expr: Expr) (tokens rest: List (Parse.Located Token))
    (postfix: expr.isPostfix = True)
    (shaped: Shaped expr)
    (spelled: Spelled layout expr tokens):
    minusAhead layout (tokens ++ rest) = False ∧ ifAhead layout (tokens ++ rest) = False :=
  match expr with
    | Var name =>
      match spelled with
        | Witness token (Both split (Both kind allowed)) => rewrite split, kind, allowed in Both rfl rfl
    | NumberLiteral digits =>
      match spelled with
        | Witness token (Both split (Both kind allowed)) => rewrite split, kind, allowed in Both rfl rfl
    | StringLiteral written =>
      match spelled with
        | Witness token (Both split (Both kind allowed)) => rewrite split, kind, allowed in Both rfl rfl
    | Bracketed inner =>
      match spelled with
        | Witness open (Witness innerTokens (Witness close (Both split (Both opens (Both allowed others))))) =>
          rewrite split, opens, allowed in Both rfl rfl
    | Field target name =>
      match spelled with
        | Witness targetTokens
            (Witness dot
              (Witness named
                (Both split (Both dotted (Both dotAllowed (Both isName (Both nameAllowed spelledTarget))))))) =>
          rewrite split, List.appendAssoc targetTokens [dot, named] rest in
            postfixStart layout target targetTokens [dot, named, ..rest] shaped.left shaped.right spelledTarget

theorem negationsEndRun ∀ (fuel: Nat) (self: Layout → {Parse (Parse.Located Token)} Expr)
    (layout: Layout) (input: List (Parse.Located Token))
    (noMinus: minusAhead layout input = False) (state: Parse.State (Parse.Located Token))
    (starts: state.at.rest = input):
    Parse.runFrom state (() => (negationsFrom fuel self layout, Parse.mark()))
      = Parse.runFrom state (() => (postfix self layout, Parse.mark())) :=
  match fuel with
    | Zero => rfl
    | Succ more =>
      rewrite starts in
        match input with
          | [] => rfl
          | [token, ..later] => rewrite noMinus in rfl

--| With no `-` next, `negationsFrom` reads a postfix expression.
theorem runsNegationsEnd ∀ (fuel: Nat) (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout)
    (tokens rest: List (Parse.Located Token)) (value: Expr)
    (noMinus: minusAhead layout (tokens ++ rest) = False)
    (runsPostfix: Parse.Runs (() => postfix self layout) tokens rest value):
    Parse.Runs (() => negationsFrom fuel self layout) tokens rest value :=
  state starts honest =>
    match runsPostfix state starts honest with
      | Witness m (Both ran others) =>
        Witness m (Both (Eq.trans (negationsEndRun fuel self layout (tokens ++ rest) noMinus state starts) ran) others)

theorem operatorOfSign ∀ (layout: Layout) (level: Nat) (token: Parse.Located Token) (punctuation: Punctuation)
    (signed: token.value.kind = Sign punctuation):
    operatorOf layout level token = None :=
  rewrite signed in rfl

--| No operator is ahead where a punctuation sign comes next.
theorem noOperatorAtSign ∀ (layout: Layout) (lowest: Nat) (token: Parse.Located Token)
    (punctuation: Punctuation) (rest: List (Parse.Located Token))
    (signed: token.value.kind = Sign punctuation):
    Parse.operatorAhead (operatorLevels layout) lowest [token, ..rest] = False :=
  rewrite operatorOfSign layout 1 token punctuation signed,
      operatorOfSign layout 2 token punctuation signed,
      operatorOfSign layout 3 token punctuation signed,
      operatorOfSign layout 4 token punctuation signed,
      operatorOfSign layout 5 token punctuation signed,
      operatorOfSign layout 6 token punctuation signed in
    rfl

theorem endsAtClose ∀ (close: Parse.Located Token) (rest: List (Parse.Located Token))
    (closes: close.value.kind = Sign CloseParen):
    EndsExpression InBrackets [close, ..rest] :=
  Both (rewrite closes in rfl) (noOperatorAtSign InBrackets 0 close CloseParen rest closes)

--| `postfix`'s atom and suffix loop read a postfix expression as the start
--| of a longer one: after its tokens the loop holds the expression, and
--| `continues` says what it does with `more`, the tokens after. By
--| induction on the expression: a field's target is such a start, and the
--| field is the loop's next round.
theorem runsPostfixPrefix ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout) (bound: Nat)
    (nested: ReadsNested self bound)
    (expr: Expr) (tokens more rest: List (Parse.Located Token)) (value: Expr)
    (postfix: expr.isPostfix = True)
    (shaped: Shaped expr)
    (spelled: Spelled layout expr tokens)
    (small: tokens.length <= bound)
    (continues: ∀ (fuel: Nat) => more.length < fuel
      → Parse.Runs (() => suffixesFrom fuel self layout expr) more rest value):
    Parse.Runs
      (() =>
        let first := atom self layout
        suffixesFrom (Parse.mark().left + 1) self layout first)
      (tokens ++ more)
      rest
      value :=
  match expr with
    | Var name =>
      match spelled with
        | Witness token (Both split (Both kind allowed)) =>
          rewrite split in
            runsAtomThenSuffixes self layout
              [token]
              more
              rest
              (Var name)
              value
              (runsAtomName self layout token name (more ++ rest) kind allowed)
              continues
    | NumberLiteral digits =>
      match spelled with
        | Witness token (Both split (Both kind allowed)) =>
          rewrite split in
            runsAtomThenSuffixes self layout
              [token]
              more
              rest
              (NumberLiteral digits)
              value
              (runsAtomNumber self layout token digits (more ++ rest) kind allowed)
              continues
    | StringLiteral written =>
      match spelled with
        | Witness token (Both split (Both kind allowed)) =>
          rewrite split in
            runsAtomThenSuffixes self layout
              [token]
              more
              rest
              (StringLiteral written)
              value
              (runsAtomString self layout token written (more ++ rest) kind allowed)
              continues
    | Bracketed inner =>
      match spelled with
        | Witness open
            (Witness innerTokens (Witness close (Both split (Both opens (Both allowed (Both closes spelledInner)))))) =>
          let size: tokens.length = (innerTokens ++ [close]).length + 1 := rewrite split in rfl
          let sizes: (innerTokens ++ [close]).length = innerTokens.length + 1 := List.lengthAppend innerTokens [close]
          rewrite split in
            runsAtomThenSuffixes self layout
              [open, ..innerTokens ++ [close]]
              more
              rest
              (Bracketed inner)
              value
              (runsAtomBracketed self layout open close innerTokens
                (more ++ rest)
                inner
                opens
                allowed
                closes
                (nested InBrackets inner innerTokens
                  [close, ..more ++ rest]
                  shaped
                  spelledInner
                  (endsAtClose close (more ++ rest) closes)
                  (omega [small, size, sizes])))
              continues
    | Field target name =>
      match spelled with
        | Witness targetTokens
            (Witness dot
              (Witness named
                (Both split (Both dotted (Both dotAllowed (Both isName (Both nameAllowed spelledTarget))))))) =>
          let size: tokens.length = targetTokens.length + 2 :=
            rewrite split in List.lengthAppend targetTokens [dot, named]
          rewrite split, List.appendAssoc targetTokens [dot, named] more in
            runsPostfixPrefix self layout bound nested target targetTokens
              [dot, named, ..more]
              rest
              value
              shaped.left
              shaped.right
              spelledTarget
              (omega [small, size])
              (fuel enough =>
                match fuel with
                  | Succ less =>
                    runsSuffixesField less self layout target dot named name more rest value dotted dotAllowed isName
                        nameAllowed
                        (continues less (omega [enough])))

theorem runsNegationsPostfix ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout) (bound: Nat)
    (nested: ReadsNested self bound)
    (expr: Expr) (fuel: Nat) (tokens rest: List (Parse.Located Token))
    (postfix: expr.isPostfix = True)
    (shaped: Shaped expr)
    (spelled: Spelled layout expr tokens)
    (ends: endsSuffixes (suffixKind layout rest) = True)
    (small: tokens.length <= bound):
    Parse.Runs (() => negationsFrom fuel self layout) tokens rest expr :=
  runsNegationsEnd fuel self layout tokens rest expr
    (postfixStart layout expr tokens rest postfix shaped spelled).left
    (Parse.runsBind
      (() => Parse.note (Parse.Problem.Expected "an expression"))
      (noted =>
        let first := atom self layout
        suffixesFrom (Parse.mark().left + 1) self layout first)
      []
      tokens
      tokens
      rest
      ()
      expr
      rfl
      (Parse.runsNote (Parse.Problem.Expected "an expression") (tokens ++ rest))
      (rewrite <- List.appendNil tokens in
        runsPostfixPrefix self layout bound nested expr tokens [] rest expr postfix shaped spelled small
          (fuel positive => runsSuffixesEnd fuel self layout expr rest ends)))

--| `negationsFrom` reads an operand: its `-`s, then the postfix expression
--| under them.
theorem runsNegations ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout) (bound: Nat)
    (nested: ReadsNested self bound)
    (expr: Expr) (fuel: Nat) (tokens rest: List (Parse.Located Token))
    (operand: expr.isOperand = True)
    (shaped: Shaped expr)
    (spelled: Spelled layout expr tokens)
    (ends: endsSuffixes (suffixKind layout rest) = True)
    (small: tokens.length <= bound)
    (enough: tokens.length < fuel):
    Parse.Runs (() => negationsFrom fuel self layout) tokens rest expr :=
  match expr with
    | Negate inner =>
      match spelled, fuel with
        | Witness minus (Witness operandTokens (Both split (Both kind (Both allowed spelledInner)))), Succ more =>
          let size: tokens.length = operandTokens.length + 1 := rewrite split in rfl
          rewrite split in
            runsNegation more self layout minus operandTokens rest inner kind allowed
              (runsNegations self layout bound nested inner more operandTokens rest shaped.left shaped.right
                  spelledInner ends
                  (omega [small, size])
                  (omega [enough, size]))
    | Var name =>
      runsNegationsPostfix self layout bound nested (Var name) fuel tokens rest rfl shaped spelled ends small
    | NumberLiteral digits =>
      runsNegationsPostfix self layout bound nested
        (NumberLiteral digits)
        fuel
        tokens
        rest
        rfl
        shaped
        spelled
        ends
        small
    | StringLiteral written =>
      runsNegationsPostfix self layout bound nested
        (StringLiteral written)
        fuel
        tokens
        rest
        rfl
        shaped
        spelled
        ends
        small
    | Bracketed inner =>
      runsNegationsPostfix self layout bound nested (Bracketed inner) fuel tokens rest rfl shaped spelled ends small
    | Field target name =>
      runsNegationsPostfix self layout bound nested (Field target name) fuel tokens rest rfl shaped spelled ends small

--| `operand` reads an operand that is spelled and shaped as one, where no
--| call or field follows it.
theorem runsOperand ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout) (bound: Nat)
    (nested: ReadsNested self bound)
    (expr: Expr) (tokens rest: List (Parse.Located Token))
    (isOperand: expr.isOperand = True)
    (shaped: Shaped expr)
    (spelled: Spelled layout expr tokens)
    (ends: endsSuffixes (suffixKind layout rest) = True)
    (small: tokens.length <= bound):
    Parse.Runs (() => operand self layout) tokens rest expr :=
  state starts honest =>
    let lengths: state.at.rest.length = tokens.length + rest.length := rewrite starts in List.lengthAppend tokens rest
    Parse.runsFromMark state
      (at => negationsFrom (at.left + 1) self layout)
      tokens
      rest
      expr
      (runsNegations self layout bound nested expr
        (state.at.left + 1)
        tokens
        rest
        isOperand
        shaped
        spelled
        ends
        small
        (omega [honest, lengths])
        state)
      starts
      honest

--| What `operatorOf` gives at `level` for the token of `operator`.
def operatorAt (operator: Operator) (level: Nat): Option (Expr → Expr → Expr) :=
  if operator.level == level then Some (Binary operator) else None

theorem operatorOfOp ∀ (layout: Layout) (level: Nat) (sign: Parse.Located Token) (operator: Operator)
    (kind: sign.value.kind = Op operator)
    (allowed: layout.allows sign = True):
    operatorOf layout level sign = operatorAt operator level :=
  rewrite kind, allowed in
    match same: operator.level == level with
      | True => rfl
      | False => rfl

theorem levelRange ∀ (operator: Operator): 1 <= operator.level ∧ operator.level <= 6 := match operator with
  | Or => Both (omega []) (omega [])
  | And => Both (omega []) (omega [])
  | EqualTo => Both (omega []) (omega [])
  | NotEqual => Both (omega []) (omega [])
  | LessThan => Both (omega []) (omega [])
  | LessEqual => Both (omega []) (omega [])
  | Append => Both (omega []) (omega [])
  | Plus => Both (omega []) (omega [])
  | Minus => Both (omega []) (omega [])
  | Times => Both (omega []) (omega [])
  | Divide => Both (omega []) (omega [])
  | Remainder => Both (omega []) (omega [])

--| The token of an operator the layout allows is found at its level's
--| place in `operatorLevels`, chaining from the left.
theorem operatorFound ∀ (layout: Layout) (sign: Parse.Located Token) (operator: Operator)
    (kind: sign.value.kind = Op operator)
    (allowed: layout.allows sign = True):
    Parse.operatorFrom sign 0 (operatorLevels layout) = Some (operator.level - 1, LeftAssociative, Binary operator) :=
  let at1 := operatorOfOp layout 1 sign operator kind allowed
  let at2 := operatorOfOp layout 2 sign operator kind allowed
  let at3 := operatorOfOp layout 3 sign operator kind allowed
  let at4 := operatorOfOp layout 4 sign operator kind allowed
  let at5 := operatorOfOp layout 5 sign operator kind allowed
  let at6 := operatorOfOp layout 6 sign operator kind allowed
  match operator with
    | Or => rewrite at1 in rfl
    | And => rewrite at1, at2 in rfl
    | EqualTo => rewrite at1, at2, at3 in rfl
    | NotEqual => rewrite at1, at2, at3 in rfl
    | LessThan => rewrite at1, at2, at3 in rfl
    | LessEqual => rewrite at1, at2, at3 in rfl
    | Append => rewrite at1, at2, at3, at4 in rfl
    | Plus => rewrite at1, at2, at3, at4, at5 in rfl
    | Minus => rewrite at1, at2, at3, at4, at5 in rfl
    | Times => rewrite at1, at2, at3, at4, at5, at6 in rfl
    | Divide => rewrite at1, at2, at3, at4, at5, at6 in rfl
    | Remainder => rewrite at1, at2, at3, at4, at5, at6 in rfl

theorem chainTreeOperand ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout) (bound: Nat)
    (nested: ReadsNested self bound)
    (expr: Expr) (tokens rest: List (Parse.Located Token))
    (isOperand: expr.isOperand = True)
    (level: expr.chainLevel = 7)
    (shaped: Shaped expr)
    (spelled: Spelled layout expr tokens)
    (ends: endsSuffixes (suffixKind layout rest) = True)
    (small: tokens.length <= bound):
    ∃ (tree: Parse.OperatorTree (Parse.Located Token) Expr) => tree.reads = tokens
      ∧ tree.value = expr
      ∧ tree.Formed (operatorLevels layout) 6
      ∧ tree.RunsEach (() => operand self layout) rest
      ∧ tree.top 6 + 1 = expr.chainLevel
      ∧ (∀ (below: Nat) => below + 1 <= expr.chainLevel → below < 6 → below < tree.bound 6) :=
  Witness
    (Operand tokens expr)
    (Both rfl
      (Both rfl
        (Both rfl
          (Both
            (runsOperand self layout bound nested expr tokens rest isOperand shaped spelled ends small)
            (Both (Eq.sym level) (below fits under => under))))))

--| An operator chain as the tree `Parse.runsOperators` reads: its
--| operators in the tree's shape, each at its level's place, and its
--| operands read by `operand` where they stand.
theorem chainTree ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout) (bound: Nat)
    (nested: ReadsNested self bound)
    (expr: Expr) (tokens rest: List (Parse.Located Token))
    (chain: expr.isChain = True)
    (shaped: Shaped expr)
    (spelled: Spelled layout expr tokens)
    (ends: endsSuffixes (suffixKind layout rest) = True)
    (small: tokens.length <= bound):
    ∃ (tree: Parse.OperatorTree (Parse.Located Token) Expr) => tree.reads = tokens
      ∧ tree.value = expr
      ∧ tree.Formed (operatorLevels layout) 6
      ∧ tree.RunsEach (() => operand self layout) rest
      ∧ tree.top 6 + 1 = expr.chainLevel
      ∧ (∀ (below: Nat) => below + 1 <= expr.chainLevel → below < 6 → below < tree.bound 6) :=
  match expr with
    | Binary operator left right =>
      match shaped, spelled with
        | Both leftLevel
            (Both rightLevel (Both leftChain (Both rightChain (Both shapedLeft shapedRight)))), Witness leftTokens
            (Witness sign
              (Witness rightTokens (Both split (Both kind (Both allowed (Both spelledLeft spelledRight)))))) =>
          let size: tokens.length = leftTokens.length + (rightTokens.length + 1) :=
            rewrite split in List.lengthAppend leftTokens [sign, ..rightTokens]
          let signEnds: endsSuffixes (suffixKind layout [sign, ..rightTokens ++ rest]) = True :=
            rewrite allowed, kind in rfl
          let range := levelRange operator
          let leftResult :=
            chainTree self layout bound nested left leftTokens
              [sign, ..rightTokens ++ rest]
              leftChain
              shapedLeft
              spelledLeft
              signEnds
              (omega [small, size])
          let rightResult :=
            chainTree self layout bound nested right rightTokens rest rightChain shapedRight spelledRight ends
              (omega [small, size])
          match leftResult, rightResult with
            | Witness leftTree
                (Both leftReads
                  (Both leftValue (Both leftFormed (Both leftRuns (Both leftTop leftBound))))), Witness rightTree
                (Both rightReads (Both rightValue (Both rightFormed (Both rightRuns (Both rightTop rightBound))))) =>
              Witness
                (Joined sign (operator.level - 1) LeftAssociative (Binary operator) leftTree rightTree)
                (Both
                  (rewrite leftReads, rightReads, split in rfl)
                  (Both
                    (rewrite leftValue, rightValue in rfl)
                    (Both
                      (Both
                        (operatorFound layout sign operator kind allowed)
                        (Both
                          (omega [range.right, range.left])
                          (Both
                            (leftBound
                              (operator.level - 1)
                              (omega [leftLevel, range.left])
                              (omega [range.right, range.left]))
                            (Both (omega [rightLevel, rightTop, range.left]) (Both leftFormed rightFormed)))))
                      (Both
                        (Both (rewrite rightReads in leftRuns) rightRuns)
                        (Both (omega [range.left]) (below fits under => omega [fits, range.left]))))))
    | Negate inner =>
      chainTreeOperand self layout bound nested (Negate inner) tokens rest rfl rfl shaped spelled ends small
    | Var name => chainTreeOperand self layout bound nested (Var name) tokens rest rfl rfl shaped spelled ends small
    | NumberLiteral digits =>
      chainTreeOperand self layout bound nested (NumberLiteral digits) tokens rest rfl rfl shaped spelled ends small
    | StringLiteral written =>
      chainTreeOperand self layout bound nested (StringLiteral written) tokens rest rfl rfl shaped spelled ends small
    | Bracketed inner =>
      chainTreeOperand self layout bound nested (Bracketed inner) tokens rest rfl rfl shaped spelled ends small
    | Field target name =>
      chainTreeOperand self layout bound nested (Field target name) tokens rest rfl rfl shaped spelled ends small

--| A chain starts with no `if`.
theorem chainStart ∀ (layout: Layout) (expr: Expr) (tokens rest: List (Parse.Located Token))
    (chain: expr.isChain = True)
    (shaped: Shaped expr)
    (spelled: Spelled layout expr tokens):
    ifAhead layout (tokens ++ rest) = False :=
  match expr with
    | Binary operator left right =>
      match shaped, spelled with
        | Both leftLevel
            (Both rightLevel (Both leftChain (Both rightChain (Both shapedLeft shapedRight)))), Witness leftTokens
            (Witness sign
              (Witness rightTokens (Both split (Both kind (Both allowed (Both spelledLeft spelledRight)))))) =>
          rewrite split, List.appendAssoc leftTokens [sign, ..rightTokens] rest in
            chainStart layout left leftTokens [sign, ..rightTokens ++ rest] leftChain shapedLeft spelledLeft
    | Negate inner =>
      match spelled with
        | Witness minus (Witness operandTokens (Both split (Both kind (Both allowed spelledInner)))) =>
          rewrite split, kind, allowed in rfl
    | Var name => (postfixStart layout (Var name) tokens rest rfl shaped spelled).right
    | NumberLiteral digits => (postfixStart layout (NumberLiteral digits) tokens rest rfl shaped spelled).right
    | StringLiteral written => (postfixStart layout (StringLiteral written) tokens rest rfl shaped spelled).right
    | Bracketed inner => (postfixStart layout (Bracketed inner) tokens rest rfl shaped spelled).right
    | Field target name => (postfixStart layout (Field target name) tokens rest rfl shaped spelled).right

theorem chainRuleRun ∀ (self: Layout → {Parse (Parse.Located Token)} Expr)
    (layout: Layout) (state: Parse.State (Parse.Located Token))
    (noIf: ifAhead layout state.at.rest = False):
    Parse.runFrom state (() => (expressionRule self layout, Parse.mark()))
      = Parse.runFrom state (() =>
        (Parse.operators "an operator" (operatorLevels layout) (() => operand self layout), Parse.mark())) :=
  match state with
    | { at = { rest = [], offset, left }, furthest, expected, messages } => rfl
    | { at = { rest = [token, ..later], offset, left }, furthest, expected, messages } => rewrite noIf in rfl

--| Every expression of the forms covered so far is a chain.
theorem shapedIsChain ∀ (expr: Expr) (shaped: Shaped expr): expr.isChain = True := match expr with
  | Var name => rfl
  | NumberLiteral digits => rfl
  | StringLiteral written => rfl
  | Bracketed inner => rfl
  | Field target name => rfl
  | Negate operand => rfl
  | Binary operator left right => rfl

--| One level of the expression parser: `expressionRule` reads a chain,
--| given that `self` reads the expressions nested in it.
theorem runsExpressionRule ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout) (bound: Nat)
    (nested: ReadsNested self bound)
    (expr: Expr) (tokens rest: List (Parse.Located Token))
    (shaped: Shaped expr)
    (spelled: Spelled layout expr tokens)
    (ends: EndsExpression layout rest)
    (small: tokens.length <= bound):
    Parse.Runs (() => expressionRule self layout) tokens rest expr :=
  let chain := shapedIsChain expr shaped
  match chainTree self layout bound nested expr tokens rest chain shaped spelled ends.left small with
    | Witness tree (Both reads (Both value (Both formed (Both runsEach others)))) =>
      let runs: Parse.Runs
        (() => Parse.operators "an operator" (operatorLevels layout) (() => operand self layout))
        tokens
        rest
        expr :=
        rewrite <- reads, <- value in
          Parse.runsOperators "an operator"
            (operatorLevels layout)
            (() => operand self layout)
            tree
            rest
            formed
            runsEach
            ends.right
      state starts honest =>
        match runs state starts honest with
          | Witness m (Both ran after) =>
            Witness m
              (Both
                (Eq.trans
                  (chainRuleRun self layout state
                    (rewrite starts in chainStart layout expr tokens rest chain shaped spelled))
                  ran)
                after)

--| What `expression` reads: an expression of the parser's shape, spelled at
--| the layout, with nothing after it that would continue it.
def GoodExpression (layout: Layout) (tokens rest: List (Parse.Located Token)) (expr: Expr): Prop :=
  Shaped expr ∧ Spelled layout expr tokens ∧ EndsExpression layout rest

--| The parser reads back what spells an expression: on tokens that spell
--| `expr` at `layout` (`Spelled`), for an `expr` of the parser's shape
--| (`Shaped`), followed by nothing that continues an expression,
--| `expression layout` reads exactly those tokens and gives `expr`.
theorem runsExpression ∀ (layout: Layout) (expr: Expr) (tokens rest: List (Parse.Located Token))
    (shaped: Shaped expr)
    (spelled: Spelled layout expr tokens)
    (ends: EndsExpression layout rest):
    Parse.Runs (() => expression layout) tokens rest expr :=
  Parse.runsRecursiveWith expressionRule GoodExpression
    (self argument read after value good nestedRuns =>
      runsExpressionRule self argument read.length
        (nestedLayout nestedExpr nestedTokens nestedRest nestedShaped nestedSpelled nestedEnds shorter =>
          nestedRuns nestedLayout nestedTokens nestedRest nestedExpr
            (Both nestedShaped (Both nestedSpelled nestedEnds))
            shorter)
        value
        read
        after
        good.left
        good.right.left
        good.right.right
        (omega []))
    layout
    tokens
    rest
    expr
    (Both shaped (Both spelled ends))
