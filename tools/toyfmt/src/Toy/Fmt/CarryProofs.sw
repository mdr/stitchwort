--| The parser's half of `formatKeepsComments`, on today's toy: a walk over
--| the parser's functions, as `Toy.Fmt.Proofs`'s walk is, but with specs
--| that tie each value to the tokens it was read from (`Parse.ReadsIn`
--| with the read, where that walk's `Parse.Gives` ignores it).
--|
--| A token read at a layout gives the tree `layout.comments token`, which
--| leaves out the own-line comments above the statement's first token
--| (they are note lines). So a value read at `layout` holds
--| `layout.keptAll read`: the first token's comments as the layout keeps
--| them, and every comment of the others, provided no other token is the
--| statement's first (`PastTail`). `Onto` is that spec in the form a chain
--| of steps builds up.

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

--| What a value read at `layout` from `tokens` holds.
def Layout.keptAll (layout: Layout): List Tok → List Comment
  | [] => []
  | [head, ..tail] => layout.kept head ++ allCarried tail

--| No token after the first is the statement's first.
def PastTail (layout: Layout): List Tok → Prop
  | [] => True
  | [head, ..tail] => List.All layout.past tail

-- A token's comments, the tree's way and the lexer's.

theorem ownLinesSame ∀ (trivia: List Trivia): ownLineComments trivia = trivia.flatMap Trivia.comments :=
  match trivia with
    | [] => byComputing
    | [OwnLine comment, ..rest] => rewrite ownLinesSame rest then byComputing
    | [BlankLine, ..rest] => rewrite ownLinesSame rest then byComputing

theorem bracketsKept ∀ (token: Tok): Layout.kept InBrackets token = token.value.comments :=
  match trailing: token.value.trailing with
    | Some located => rewrite ownLinesSame token.value.above then byComputing
    | None => rewrite ownLinesSame token.value.above then byComputing

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

theorem keptAllPast ∀ (layout: Layout) (tokens: List Tok)
    (past: List.All layout.past tokens):
    layout.keptAll tokens = allCarried tokens :=
  match tokens, past with
    | [], _ => byComputing
    | [head, ..tail], Both headPast tailPast => rewrite keptPast layout head headPast then byComputing

theorem allPastTail ∀ (layout: Layout) (tokens: List Tok) (past: List.All layout.past tokens): PastTail layout tokens :=
  match tokens, past with
    | [], _ => byComputing
    | [head, ..tail], Both headPast tailPast => tailPast

theorem pastTailLeft ∀ (layout: Layout) (first second: List Tok)
    (past: PastTail layout (first ++ second)):
    PastTail layout first :=
  match first, past with
    | [], _ => byComputing
    | [head, ..tail], all => List.allAppendLeft layout.past tail second all

--| What `second` needs after `first`: all of it past if `first` read a
--| token, else as `first ++ second` is.
theorem pastTailRight ∀ (layout: Layout) (first second: List Tok)
    (past: PastTail layout (first ++ second)):
    PastTail layout second :=
  match first, past with
    | [], all => all
    | [head, ..tail], all => allPastTail layout second (List.allAppendRight layout.past tail second all)

theorem keptAllAppend ∀ (layout: Layout) (first second: List Tok)
    (past: PastTail layout (first ++ second)):
    layout.keptAll (first ++ second) = layout.keptAll first ++ layout.keptAll second :=
  match first, past with
    | [], _ => byComputing
    | [head, ..tail], all =>
      rewrite keptAllPast layout second (List.allAppendRight layout.past tail second all),
          allCarriedAppend tail second then
        (List.appendAssoc (layout.kept head) (allCarried tail) (allCarried second)).flipped

theorem bracketsPast ∀ (tokens: List Tok): List.All (Layout.past InBrackets) tokens := match tokens with
  | [] => ()
  | [head, ..tail] => (byComputing, (bracketsPast tail))

-- The spec a chain of steps builds.

--| What is asked of the tokens a step read: before a token has been read
--| at this layout (`started = False`), only those after the first must be
--| past; after, all.
def Seen (layout: Layout) (started: Bool) (read: List Tok): Prop := match started with
  | True => List.All layout.past read
  | False => PastTail layout read

def sumOf (layout: Layout) (started: Bool) (read: List Tok): List Comment := match started with
  | True => allCarried read
  | False => layout.keptAll read

--| `measure` of the value is `before` and then the comments of what was
--| read.
def Onto (layout: Layout) (started: Bool) (before: List Comment) (measure: a → List Comment)
    (read: List Tok) (value: a):
    Prop :=
  Seen layout started read → measure value = before ++ sumOf layout started read

--| A value read at `layout` holds the comments of its tokens.
def Carries (layout: Layout) (measure: a → List Comment): List Tok → a → Prop := Onto layout False [] measure

--| The same of a value read after the layout's first token.
def Inner (layout: Layout) (measure: a → List Comment): List Tok → a → Prop := Onto layout True [] measure

theorem carriesInner ∀ [measure: a → List Comment] (layout: Layout) (read: List Tok) (value: a)
    (carries: Carries layout measure read value):
    Inner layout measure read value :=
  past => rewrite <- keptAllPast layout read past then carries (allPastTail layout read past)

theorem bracketsInner ∀ [measure: a → List Comment] (layout: Layout) (read: List Tok) (value: a)
    (carries: Carries InBrackets measure read value):
    Inner layout measure read value :=
  past =>
    rewrite <- keptAllPast InBrackets read (bracketsPast read) then
      carries (allPastTail InBrackets read (bracketsPast read))

--| A step that may be the layout's first, then the rest.
theorem thenFresh ∀ [inv: Parse.Invariant Tok] [p: () → {Parse Tok} a] [j: a → {Parse Tok} b] [first: a → List Comment]
    [measure: b → List Comment] (layout: Layout) (before: List Comment)
    (readsFirst: Parse.ReadsIn inv p (Carries layout first))
    (rest: ∀ (v: a) => Parse.ReadsIn inv (() => j v) (Onto layout False (before ++ first v) measure)):
    Parse.ReadsIn inv (() => j (p())) (Onto layout False before measure) :=
  Parse.readsThen readsFirst (firstRead v carried =>
    Parse.readsWeaken (rest v) (read w onward past =>
      let firstSum: first v = layout.keptAll firstRead := carried (pastTailLeft layout firstRead read past)
      let whole := onward (pastTailRight layout firstRead read past)
      rewrite keptAllAppend layout firstRead read past,
          <- firstSum,
          <- List.appendAssoc before (first v) (layout.keptAll read) then
        whole))

--| A step after the layout's first token, then the rest.
theorem thenInner ∀ [inv: Parse.Invariant Tok] [p: () → {Parse Tok} a] [j: a → {Parse Tok} b] [first: a → List Comment]
    [measure: b → List Comment] (layout: Layout) (before: List Comment)
    (readsFirst: Parse.ReadsIn inv p (Inner layout first))
    (rest: ∀ (v: a) => Parse.ReadsIn inv (() => j v) (Onto layout True (before ++ first v) measure)):
    Parse.ReadsIn inv (() => j (p())) (Onto layout True before measure) :=
  Parse.readsThen readsFirst (firstRead v carried =>
    Parse.readsWeaken (rest v) (read w onward past =>
      let firstSum: first v = allCarried firstRead := carried (List.allAppendLeft layout.past firstRead read past)
      let whole := onward (List.allAppendRight layout.past firstRead read past)
      rewrite allCarriedAppend firstRead read, <- firstSum, <- List.appendAssoc before (first v) (allCarried read) then
        whole))

--| The last step: a value whose measure is what the chain built.
theorem ontoDone ∀ [inv: Parse.Invariant Tok] [measure: a → List Comment] (layout: Layout) (started: Bool)
    (before: List Comment) (x: a)
    (same: measure x = before):
    Parse.ReadsIn inv (() => x) (Onto layout started before measure) :=
  Parse.readsDone x _ (seen =>
    match started with
      | True => rewrite same then (List.appendNil before).flipped
      | False => rewrite same then (List.appendNil before).flipped)
