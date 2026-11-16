--| The parser's half of `formatKeepsComments`, on today's toy: a walk over
--| the parser's functions, as `Toy.Fmt.Proofs`'s walk is, but with specs
--| that tie each value to the tokens it was read from (`Parse.ReadsIn`
--| with the read, where that walk's `Parse.Gives` ignores it).
--|
--| A token read at a layout gives the tree `layout.comments token`, which
--| leaves out the own-line comments above the statement's first token
--| (they are note lines). So a value read at `layout` holds its first
--| token's comments as the layout keeps them and every comment of the
--| others, provided none of the others is the statement's first
--| (`Opened`); a value read after the first token holds every comment of
--| its tokens (`Inner`). `Onto` is `Inner` in the form a chain of steps
--| builds up. This file has the specs and the chain lemmas; the walk
--| itself is in CarryWalk.sw.

namespace Toy.Fmt.Carry
import Toy.Fmt (..)
import Toy.Fmt.Proofs (OperatorCarries, operatorCarries, selectedComments)
import Toy.Syntax (..)
import Toy.Syntax.Proofs (..)
import Std (And, Bool, Eq, List, Nat, Option, Pair, Parse, Result, Text, Void)

-- The comments a tree holds, token by token in source order.

def Comments.all (comments: Comments): List Comment := comments.above ++ comments.after.toList

def Expr.comments: Expr → List Comment
  | Var _ comments => comments.all
  | NumberLiteral _ comments => comments.all
  | StringLiteral _ comments => comments.all
  | Bracketed open inner close => open.all ++ inner.comments ++ close.all
  | ListLiteral open items close => open.all ++ itemsComments items ++ close.all
  | Call callee open arguments close => callee.comments ++ open.all ++ itemsComments arguments ++ close.all
  | Field target dot _ nameComments => target.comments ++ dot.all ++ nameComments.all
  | Negate minus operand => minus.all ++ operand.comments
  | Binary _ sign left right => left.comments ++ sign.all ++ right.comments
  | If ifComments condition thenComments whenTrue elseComments whenFalse =>
    ifComments.all
      ++ condition.comments
      ++ thenComments.all
      ++ whenTrue.comments
      ++ elseComments.all
      ++ whenFalse.comments

def itemsComments: List Item → List Comment
  | [] => []
  | [{ value, comma }, ..rest] => value.comments ++ comma.all ++ itemsComments rest

def Body.comments: Body → List Comment
  | { statements } => linesComments statements

def linesComments: List (Spaced Statement) → List Comment
  | [] => []
  | [{ blankBefore, line }, ..rest] => line.comments ++ linesComments rest

def Statement.comments: Statement → List Comment
  | Let letComments _ nameComments equals body => letComments.all ++ nameComments.all ++ equals.all ++ body.comments
  | Bare value => value.comments
  | StatementNote comment => [comment]

def Parameter.allComments (parameter: Parameter): List Comment := parameter.comments.all ++ parameter.comma.all

def Declaration.comments: Declaration → List Comment
  | Function fnComments _ nameComments open parameters close equals body =>
    fnComments.all
      ++ nameComments.all
      ++ open.all
      ++ parameters.flatMap Parameter.allComments
      ++ close.all
      ++ equals.all
      ++ body.comments
  | Value letComments _ nameComments equals body => letComments.all ++ nameComments.all ++ equals.all ++ body.comments
  | DeclarationNote comment => [comment]

def SourceFile.comments (file: SourceFile): List Comment := file.declarations.flatMap (spaced => spaced.line.comments)

type Tok = Parse.Located Token

--| Every comment the tokens hold, in order.
def allCarried (tokens: List Tok): List Comment := tokens.flatMap (token => token.value.comments)

--| The comments of `token` the tree keeps when it is read at `layout`.
def Layout.kept (layout: Layout) (token: Tok): List Comment := (layout.comments token).all

--| `token` is not the first token of the statement `layout` is in, so its
--| own-line comments are kept.
def Layout.past (layout: Layout) (token: Tok): Prop := match layout with
  | InBrackets => True
  | InStatement _ start => (token.offset == start) = False

-- A token's comments, the tree's way and the lexer's.

theorem ownLinesSame ∀ (trivia: List Trivia): ownLineComments trivia = trivia.flatMap Trivia.comments :=
  match trivia with
    | [] => byComputing
    | [OwnLine comment, ..rest] => rewrite ownLinesSame rest
    | [BlankLine, ..rest] => rewrite ownLinesSame rest

theorem bracketsKept ∀ (token: Tok): Layout.kept InBrackets token = token.value.comments :=
  match trailing: token.value.trailing with
    | Some located => rewrite ownLinesSame token.value.above
    | None => rewrite ownLinesSame token.value.above

theorem keptPast ∀ (layout: Layout) (token: Tok) (past: layout.past token): layout.kept token = token.value.comments :=
  match layout, past with
    | InBrackets, _ => bracketsKept token
    | InStatement column start, apart =>
      match same: token.offset == start with
        | False => bracketsKept token

-- Sums over the tokens read.

theorem allCarriedAppend ∀ (first second: List Tok):
    allCarried (first ++ second) = allCarried first ++ allCarried second :=
  match first with
    | [] => byComputing
    | [head, ..tail] =>
      rewrite allCarriedAppend tail second then
        (List.appendAssoc head.value.comments (allCarried tail) (allCarried second)).flipped

theorem bracketsPast ∀ (tokens: List Tok): List.All (Layout.past InBrackets) tokens := match tokens with
  | [] => ()
  | [head, ..tail] => (byComputing, (bracketsPast tail))

theorem allCarriedOne ∀ (token: Tok): allCarried [token] = token.value.comments := List.appendNil token.value.comments

-- What the lexer's tokens are like: the walk's invariant.

--| A token that doesn't start a line has no own-line comments above it:
--| the lexer gives those to the first token of the next line.
def Tidy (token: Tok): Prop := token.value.startsLine = False → token.value.above.flatMap Trivia.comments = []

--| Each token's offset is below those of all after it, so no two tokens
--| start at one place and only a statement's first token is at its
--| layout's `start`.
def Rising: List Tok → Prop
  | [] => True
  | [first, ..later] => List.All (other => first.offset < other.offset) later ∧ Rising later

theorem risingAfter ∀ (read rest: List Tok) (rising: Rising (read ++ rest)): Rising rest := match read, rising with
  | [], rising => rising
  | [head, ..tail], Both apart later => risingAfter tail rest later

--| What the walk assumes of the input left: tidy tokens at rising offsets.
def Lexer: Parse.Invariant Tok :=
  Parse.Invariant.both (Parse.Invariant.every Tidy) { holds = Rising, kept = risingAfter }

-- The specs.

--| A value read after its layout's first token holds its tokens' comments.
def Inner (layout: Layout) (measure: a → List Comment) (read: List Tok) (value: a): Prop :=
  List.All layout.past read → measure value = allCarried read

--| `Inner` as a chain of steps builds it: `before` is what the steps so
--| far add in front of the comments still to be read, and `extra` is
--| anything else the chain's value must satisfy.
def Onto (layout: Layout) (before: List Comment → List Comment) (measure: a → List Comment) (extra: a → Prop)
    (read: List Tok) (value: a):
    Prop :=
  extra value ∧ (List.All layout.past read → measure value = before (allCarried read))

--| A value read from the layout's first token on: it read a token, and
--| holds that token's comments as the layout keeps them, then the others'.
def Opened (layout: Layout) (measure: a → List Comment) (read: List Tok) (value: a): Prop := match read with
  | [] => Void
  | [head, ..tail] => List.All layout.past tail → measure value = layout.kept head ++ allCarried tail

--| `Opened` where the first token is known to be `token`.
def Started (layout: Layout) (token: Tok) (measure: a → List Comment) (extra: a → Prop) (read: List Tok) (value: a):
    Prop :=
  ∃ (more: List Tok) => read = [token, ..more]
    ∧ extra value
    ∧ (List.All layout.past more → measure value = layout.kept token ++ allCarried more)

--| An expression read at `layout`: `Opened`, its first token allowed
--| there, and that token's comments above it the expression's
--| `firstAbove` (which `Layout.headed` drops).
def ExprSpec (layout: Layout) (read: List Tok) (value: Expr): Prop := match read with
  | [] => Void
  | [head, ..tail] =>
    layout.allows head = True
      ∧ value.firstAbove = (layout.comments head).above
      ∧ (List.All layout.past tail → value.comments = layout.kept head ++ allCarried tail)

theorem startedOpened ∀ [measure: a → List Comment] [extra: a → Prop] (layout: Layout) (token: Tok)
    (read: List Tok) (value: a)
    (started: Started layout token measure extra read value):
    Opened layout measure read value :=
  match started with | (more, split, holds, carried) => rewrite split then carried

theorem startedExpr ∀ (layout: Layout) (token: Tok)
    (allowed: layout.allows token = True)
    (read: List Tok) (value: Expr)
    (started: Started layout token Expr.comments
      (found => found.firstAbove = (layout.comments token).above)
      read
      value):
    ExprSpec layout read value :=
  match started with | (more, split, above, carried) => rewrite split then (allowed, above, carried)

theorem startedInner ∀ [measure: a → List Comment] [extra: a → Prop] (layout: Layout) (token: Tok)
    (read: List Tok) (value: a)
    (started: Started layout token measure extra read value):
    Inner layout measure read value :=
  match started with
    | (more, split, holds, carried) =>
      rewrite split then
        (past =>
          match past with
            | Both tokenPast morePast => rewrite <- keptPast layout token tokenPast then carried morePast)

theorem openedInner ∀ [measure: a → List Comment] (layout: Layout) (read: List Tok) (value: a)
    (opened: Opened layout measure read value):
    Inner layout measure read value :=
  match read, opened with
    | [], never => never.impossible
    | [head, ..tail], carried => past =>
      match past with
        | Both headPast tailPast => rewrite <- keptPast layout head headPast then carried tailPast

theorem exprOpened ∀ (layout: Layout) (read: List Tok) (value: Expr)
    (spec: ExprSpec layout read value):
    Opened layout Expr.comments read value :=
  match read, spec with
    | [], never => never.impossible
    | [head, ..tail], known => known.right.right

theorem exprInner ∀ (layout: Layout) (read: List Tok) (value: Expr)
    (spec: ExprSpec layout read value):
    Inner layout Expr.comments read value :=
  openedInner layout read value (exprOpened layout read value spec)

--| Inside brackets every token is past, so what was read there is `Inner`
--| at any layout.
theorem bracketsInner ∀ [measure: a → List Comment] (layout: Layout) (read: List Tok) (value: a)
    (inner: Inner InBrackets measure read value):
    Inner layout measure read value :=
  past => inner (bracketsPast read)

theorem exprBrackets ∀ (layout: Layout) (read: List Tok) (value: Expr)
    (spec: ExprSpec InBrackets read value):
    Inner layout Expr.comments read value :=
  bracketsInner layout read value (exprInner InBrackets read value spec)

--| One token read at `layout`, after its first.
theorem innerOne ∀ [measure: a → List Comment] (layout: Layout) (token: Tok) (value: a)
    (same: measure value = (layout.comments token).all):
    Inner layout measure [token] value :=
  past =>
    calc measure value
      _ = layout.kept token := same
      _ = token.value.comments := keptPast layout token past.left
      _ = allCarried [token] := (allCarriedOne token).flipped

-- From one mark. A parser that looks at the next token and then skips it
-- can only be followed from the mark it looked at, where the token it
-- skips is the one it saw.

--| `skip` where `token` is next reads it.
theorem readsSkipAt ∀ (start: Parse.Mark Tok) (token: Tok) (later: List Tok)
    (shape: start.rest = [token, ..later]):
    Parse.ReadsAt start (() => skip()) (read done => read = [token]) :=
  Parse.readsAtThen
    [first := read skipped => read = [token]]
    (total state value after here honest h =>
      match Parse.nextTakes total state value after token later
        (rewrite here then shape)
        (rewrite here then honest)
        h with
        | (isSome, starts, honestAfter) => ([token], (rewrite <- here then starts), honestAfter, byComputing))
    (read skipped middle starts single => Parse.readsAtDone middle () _ (rewrite single))

--| `skip` of the layout's first token, seen at `start`, then the rest.
theorem skipStarted ∀ [inv: Parse.Invariant Tok] [j: () → {Parse Tok} b] [measure: b → List Comment] [extra: b → Prop]
    (layout: Layout) (start: Parse.Mark Tok) (token: Tok) (later: List Tok)
    (fine: Parse.Fits Tok inv [token, ..later])
    (shape: start.rest = [token, ..later])
    (rest: ∀ (done: ()) => Parse.ReadsIn inv
      (() => j done)
      (Onto layout (more => layout.kept token ++ more) measure extra)):
    Parse.ReadsAt start (() => j (skip())) (Started layout token measure extra) :=
  Parse.readsAtThen (readsSkipAt start token later shape) (read done after starts single =>
    Parse.readsAtWeaken (rest done after (fine.after (rewrite <- shape then starts))) (taken value onto =>
      (taken, (rewrite single), onto.left, onto.right)))

--| `skip` of a later token, seen at `start` and kept as the layout keeps
--| it, then the rest.
theorem skipOnto ∀ [inv: Parse.Invariant Tok] [j: () → {Parse Tok} b] [measure: b → List Comment] [extra: b → Prop]
    [before: List Comment → List Comment] (layout: Layout) (start: Parse.Mark Tok) (token: Tok) (later: List Tok)
    (fine: Parse.Fits Tok inv [token, ..later])
    (shape: start.rest = [token, ..later])
    (rest: ∀ (done: ()) => Parse.ReadsIn inv
      (() => j done)
      (Onto layout (more => before (layout.kept token ++ more)) measure extra)):
    Parse.ReadsAt start (() => j (skip())) (Onto layout before measure extra) :=
  Parse.readsAtThen (readsSkipAt start token later shape) (read done after starts single =>
    Parse.readsAtWeaken (rest done after (fine.after (rewrite <- shape then starts))) (taken value onto =>
      (
        onto.left,
        (rewrite single then
          (past =>
            match past with
              | Both tokenPast morePast => rewrite <- keptPast layout token tokenPast then onto.right morePast))
      )))

-- Chains of steps after the layout's first token.

--| A step, then the rest.
theorem andThen ∀ [inv: Parse.Invariant Tok] [p: () → {Parse Tok} a] [j: a → {Parse Tok} b] [first: a → List Comment]
    [measure: b → List Comment] [extra: b → Prop] [layout: Layout] [before: List Comment → List Comment]
    (readsFirst: Parse.ReadsIn inv p (Inner layout first))
    (rest: ∀ (v: a) => Parse.ReadsIn inv (() => j v) (Onto layout (later => before (first v ++ later)) measure extra)):
    Parse.ReadsIn inv (() => j (p())) (Onto layout before measure extra) :=
  Parse.readsThen readsFirst (firstRead v carried =>
    Parse.readsWeaken (rest v) (read w onward =>
      (
        onward.left,
        (past =>
          let firstSum: first v = allCarried firstRead := carried (List.allAppendLeft layout.past firstRead read past)
          let whole := onward.right (List.allAppendRight layout.past firstRead read past)
          rewrite allCarriedAppend firstRead read, <- firstSum then whole)
      )))

--| The last step: a value whose measure is what the chain built.
theorem ontoDone ∀ [inv: Parse.Invariant Tok] [measure: a → List Comment] [extra: a → Prop] [layout: Layout]
    [before: List Comment → List Comment] [x: a] (holds: extra x)
    (same: measure x = before []):
    Parse.ReadsIn inv (() => x) (Onto layout before measure extra) :=
  Parse.readsDone x _ (holds, (past => same))
