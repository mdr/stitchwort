--| Slice 1's read-back for a whole tree (docs/proposals/self-hosted-fmt-s1-sketch.md §2, ticket 17c): a relation
--| between items and the tree they read as, rung by rung down the parser's ladder, and the knot that ties
--| `expressionAt` to it. `Tree goal read rest value` says that `read`, followed by `rest`, is what the parser at
--| `goal` should read as `value`; `runsTree` proves that `expressionAt goal` does.
--|
--| Each rung is a `Prop` about one node that names its children's reads through `sub`, the relation for the calls
--| the parser makes to itself (brackets' elements, arguments, a prefix's operand, the result after `->`), and never
--| itself: so the rungs need no recursion on the tree, and `Tree` ties them with an index that bounds the nesting.
--| The look-aheads each rung needs are its hypotheses, pure tests of the items, for ticket 17d to discharge from
--| `hangs` and the glue facts.

namespace Syntax.ReadBackTree
import Std (Bool, DecEq, Eq, List, Nat, Option, Parse, Text, Void)
import Syntax (..)
import Syntax.ReadBackProofs (..)
import Syntax.ReadBackRuns (..)

-- The calls the parser makes to itself.

--| `self` reads every read `sub` holds of that is shorter than `bound`: what `Parse.runsRecursiveWith` hands a
--| step, the bound being the length of the step's own read.
def SelfRuns (sub: Goal → List Item → List Item → Expr → Prop) (self: Goal → {Parse Item} Expr) (bound: Nat): Prop :=
  ∀ (goal: Goal) (read rest: List Item) (value: Expr) => sub goal read rest value
    → read.length < bound
    → Parse.Runs (() => self goal) read rest value

-- Atoms: what `atomOf` reads from its first item.

--| A name or numeral.
def WordBase (item: Item) (more: List Item) (value: Expr): Prop :=
  more = [] ∧ value = Atom item.kind item.leaf.word ∧ isWord item.kind = True

--| What `parenAtom` looks at before `bracketed`: no `()`, named argument or operator section.
type ParenPlain (modes: Modes) (items: List Item): Prop = {
  notOutside: parenOutside (peekIn modes 1 items) (peekIn modes 2 items) = False,
  noRight: rightOperator items = None
}

--| `(e)`.
def ParenBase (sub: Goal → List Item → List Item → Expr → Prop) (modes: Modes) (item: Item)
    (more rest: List Item) (value: Expr):
    Prop :=
  ∃ (inner: List Item) (close: Item) (first: Expr) => more = inner ++ [close]
    ∧ value = Paren item.leaf.word first close.leaf.word
    ∧ item.kind = LParen
    ∧ ParenPlain modes [item, ..more ++ rest]
    ∧ sub { modes = modes.inBrackets, level = LevelFull } inner [close, ..rest] first
    ∧ modes.inBrackets.stops close = False
    ∧ close.kind = RParen

--| The steps of a comma list after its first element, as `CommaRuns` has them, each element one that `element`
--| holds of.
def CommaReads (modes: Modes) (ends: Nat → {Parse Item} Bool)
    (element: List Item → List Item → Expr → Prop) (count: Nat):
    List (Item, List Item, Expr) → List Item → Prop
  | [], rest => isSome Comma (peekIn modes 0 rest) = False
  | [(comma, read, value), ..steps], rest =>
    modes.stops comma = False
      ∧ comma.kind = Comma
      ∧ Parse.Runs (() => ends count) [] (read ++ commaReads steps ++ rest) False
      ∧ element read (commaReads steps ++ rest) value
      ∧ CommaReads modes ends element (count + 1) steps rest

--| `(a, b, …)`.
def TupleBase (sub: Goal → List Item → List Item → Expr → Prop) (modes: Modes) (item: Item)
    (more rest: List Item) (value: Expr):
    Prop :=
  ∃ (read1: List Item) (comma: Item) (read2: List Item) (steps: List (Item, List Item, Expr)) (close: Item) (first second: Expr) =>
    more = read1 ++ ([comma, ..read2] ++ (commaReads steps ++ [close]))
      ∧ value = Tuple item.leaf.word (commaDone second [first] steps) False close.leaf.word
      ∧ item.kind = LParen
      ∧ ParenPlain modes [item, ..more ++ rest]
      ∧ sub
        { modes = modes.inBrackets, level = LevelFull }
        read1
        (([comma, ..read2] ++ (commaReads steps ++ [close])) ++ rest)
        first
      ∧ modes.inBrackets.stops comma = False
      ∧ comma.kind = Comma
      ∧ sub { modes = modes.inBrackets, level = LevelFull } read2 ((commaReads steps ++ [close]) ++ rest) second
      ∧ CommaReads modes.inBrackets
        (tupleEnds modes.inBrackets)
        (sub { modes = modes.inBrackets, level = LevelFull })
        2
        steps
        [close, ..rest]
      ∧ modes.inBrackets.stops close = False
      ∧ close.kind = RParen

--| What `bracketAtom` looks at before `listExpr`: no named argument.
def bracketPlain (modes: Modes) (items: List Item): Bool :=
  (isSome Lower (peekIn modes 1 items) || isSome KwDecreasing (peekIn modes 1 items))
    && isSome ColonEq (peekIn modes 2 items)

--| `[]`.
def EmptyListBase (modes: Modes) (item: Item) (more rest: List Item) (value: Expr): Prop :=
  ∃ (close: Item) => more = [close]
    ∧ value = ListOf item.leaf.word [] False close.leaf.word
    ∧ item.kind = LBracket
    ∧ bracketPlain modes [item, ..more ++ rest] = False
    ∧ modes.inBrackets.stops close = False
    ∧ close.kind = RBracket

--| A list element: no spread, then an expression.
def ListElement (sub: Goal → List Item → List Item → Expr → Prop) (inner: Modes) (read rest: List Item) (value: Expr):
    Prop :=
  isSome DotDot (peekIn inner 0 (read ++ rest)) = False ∧ sub { modes = inner, level = LevelFull } read rest value

--| `[a, b, …]`.
def ListBase (sub: Goal → List Item → List Item → Expr → Prop) (modes: Modes) (item: Item)
    (more rest: List Item) (value: Expr):
    Prop :=
  ∃ (read1: List Item) (steps: List (Item, List Item, Expr)) (close: Item) (first: Expr) => more
    = read1 ++ (commaReads steps ++ [close])
    ∧ value = ListOf item.leaf.word (commaDone first [] steps) False close.leaf.word
    ∧ item.kind = LBracket
    ∧ bracketPlain modes [item, ..more ++ rest] = False
    ∧ isSome RBracket (peekIn modes.inBrackets 0 ((read1 ++ (commaReads steps ++ [close])) ++ rest)) = False
    ∧ ListElement sub modes.inBrackets read1 ((commaReads steps ++ [close]) ++ rest) first
    ∧ CommaReads modes.inBrackets (count => modes.inBrackets.at RBracket) (ListElement sub modes.inBrackets) 1 steps [
      close,
      ..rest
    ]
    ∧ modes.inBrackets.stops close = False
    ∧ close.kind = RBracket

--| `-1`, glued, as an argument.
def NumberBase (item: Item) (more rest: List Item) (value: Expr): Prop :=
  ∃ (number: Item) => more = [number]
    ∧ value = Prefix item.leaf.word (Atom number.kind number.leaf.word)
    ∧ item.kind = Minus
    ∧ negativeNumeral [item, number, ..rest] = True

--| `-x` or `!x` as an argument: the sign, glued to an argument.
def SignBase (sub: Goal → List Item → List Item → Expr → Prop) (modes: Modes) (item: Item)
    (more rest: List Item) (value: Expr):
    Prop :=
  ∃ (operand: Expr) => value = Prefix item.leaf.word operand
    ∧ ((item.kind = Minus
      ∧ negativeNumeral [item, ..more ++ rest] = False
      ∧ argumentMinus [item, ..more ++ rest] = True)
      ∨ (item.kind = Bang ∧ argumentBang [item, ..more ++ rest] = True))
    ∧ sub { modes, level = LevelArgument } more rest operand

--| What `atomOf` reads from `item` on, in slice 1.
def BaseReads (sub: Goal → List Item → List Item → Expr → Prop) (modes: Modes) (item: Item)
    (more rest: List Item) (value: Expr):
    Prop :=
  WordBase item more value
    ∨ ParenBase sub modes item more rest value
    ∨ TupleBase sub modes item more rest value
    ∨ EmptyListBase modes item more rest value
    ∨ ListBase sub modes item more rest value
    ∨ NumberBase item more rest value
    ∨ SignBase sub modes item more rest value

--| What `atom` looks at after its base: no record's fields, no `()` call, no field access.
type AtomEnds (modes: Modes) (head: Bool) (kind: Tok) (rest: List Item): Prop = {
  plain: (isSome Upper (Some kind) && head && isSome LBrace (peekIn modes 0 rest)) = False,
  noCall: unitCall rest = False,
  noDot: dotAhead modes rest = False
}

--| What `atom self modes head` reads.
def AtomReads (sub: Goal → List Item → List Item → Expr → Prop) (modes: Modes) (head: Bool)
    (read rest: List Item) (value: Expr):
    Prop :=
  ∃ (item: Item) (more: List Item) => read = [item, ..more]
    ∧ modes.stops item = False
    ∧ AtomEnds modes head item.kind rest
    ∧ BaseReads sub modes item more rest value

-- From the rungs to runs: atoms.

--| `atomOf` at a `(` that starts no `()`, named argument or section: `bracketed`.
--|
--| Proof idea: `atomOf` at `(` is `parenAtom`, which peeks two items ahead and then looks at `rightOperator`;
--| the look-aheads say no to both, leaving `bracketed`.
theorem runsParenAtomOf ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (item: Item)
    (more rest: List Item) (value: Expr)
    (isOpen: item.kind = LParen)
    (plain: ParenPlain modes [item, ..more ++ rest])
    (bracketedRuns: Parse.Runs (() => bracketed self modes) [item, ..more] rest value):
    Parse.Runs (() => atomOf self modes item.kind) [item, ..more] rest value :=
  rewrite isOpen then
    runsLook
      (() => modes.peekAt 1)
      (second => parenSecond self modes second)
      (peekIn modes 1 [item, ..more ++ rest])
      [item, ..more]
      rest
      value
      (runsPeekAtOn modes 1 [item, ..more ++ rest])
      (runsLook
        (() => modes.peekAt 2)
        (third => parenOn self modes (peekIn modes 1 [item, ..more ++ rest]) third)
        (peekIn modes 2 [item, ..more ++ rest])
        [item, ..more]
        rest
        value
        (runsPeekAtOn modes 2 [item, ..more ++ rest])
        (rewrite plain.notOutside then
          runsLook
            (() => left())
            (items => parenRest self modes items)
            [item, ..more ++ rest]
            [item, ..more]
            rest
            value
            (runsLeftOn [item, ..more ++ rest])
            (rewrite plain.noRight then bracketedRuns)))

--| `atomOf` at a `[` that starts no named argument: `listExpr`.
--|
--| Proof idea: `atomOf` at `[` is `bracketAtom`, which peeks two items ahead; the look-ahead says no named
--| argument, leaving `listExpr`.
theorem runsBracketAtomOf ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (item: Item)
    (more rest: List Item) (value: Expr)
    (isOpen: item.kind = LBracket)
    (plain: bracketPlain modes [item, ..more ++ rest] = False)
    (listRuns: Parse.Runs (() => listExpr self modes) [item, ..more] rest value):
    Parse.Runs (() => atomOf self modes item.kind) [item, ..more] rest value :=
  rewrite isOpen then
    runsLook
      (() => modes.peekAt 1)
      (second => bracketSecond self modes second)
      (peekIn modes 1 [item, ..more ++ rest])
      [item, ..more]
      rest
      value
      (runsPeekAtOn modes 1 [item, ..more ++ rest])
      (runsLook
        (() => modes.peekAt 2)
        (third => bracketAt self modes (peekIn modes 1 [item, ..more ++ rest]) third)
        (peekIn modes 2 [item, ..more ++ rest])
        [item, ..more]
        rest
        value
        (runsPeekAtOn modes 2 [item, ..more ++ rest])
        (rewrite (plain: ((isSome Lower (peekIn modes 1 [item, ..more ++ rest])
              || isSome KwDecreasing (peekIn modes 1 [item, ..more ++ rest]))
              && isSome ColonEq (peekIn modes 2 [item, ..more ++ rest]))
              = False) then
          listRuns))

--| `CommaReads` gives `CommaRuns` where each element `element` holds of is one `next` reads.
--|
--| Proof idea: step by step; each step's element is shorter than the steps' reads, by the comma before it.
theorem commaRunsOf ∀ (modes: Modes) (ends: Nat → {Parse Item} Bool) (element: List Item → List Item → Expr → Prop)
    (next: () → {Parse Item} Expr) (bound count: Nat) (steps: List (Item, List Item, Expr)) (rest: List Item)
    (converts: ∀ (read later: List Item) (value: Expr) => element read later value
      → read.length < bound
      → Parse.Runs next read later value)
    (small: (commaReads steps).length <= bound)
    (reads: CommaReads modes ends element count steps rest):
    CommaRuns modes ends next count steps rest :=
  match steps, small, reads with
    | [], _, reads => reads
    | [(comma, read, value), ..later], small, (open, isComma, ended, holds, more) =>
      let lengths := List.lengthAppend [comma, ..read] (commaReads later)
      (
        open,
        isComma,
        ended,
        converts read (commaReads later ++ rest) value holds (arithmetic [small, lengths]),
        commaRunsOf modes ends element next bound (count + 1) later rest converts (arithmetic [small, lengths]) more
      )

--| A base that `BaseReads` holds of is what `atomOf` reads from its first item, given the calls to `self` on what
--| it holds of inside.
--|
--| Proof idea: one case per base. A word is `runsAtomOfWord`; a bracket goes to `bracketed` or `listExpr` past
--| the look-aheads, and then `runsBracketed`, `runsTuple`, `runsListEmpty` or `runsList`, with the elements from
--| `selfRuns`, each shorter than the whole; a sign is `runsNegativeNumber`, `runsNegativeAtom` or
--| `runsPrefixBang`.
theorem runsBase ∀ (sub: Goal → List Item → List Item → Expr → Prop) (self: Goal → {Parse Item} Expr) (bound: Nat)
    (modes: Modes) (item: Item) (more rest: List Item) (value: Expr)
    (selfRuns: SelfRuns sub self bound)
    (small: [item, ..more].length <= bound)
    (reads: BaseReads sub modes item more rest value):
    Parse.Runs (() => atomOf self modes item.kind) [item, ..more] rest value :=
  match reads with
    | Inl (isMore, isValue, word) => rewrite isMore, isValue then runsAtomOfWord self modes item rest word
    | Inr (Inl (inner, close, first, isMore, isValue, isOpen, plain, innerReads, closes, isClose)) =>
      let lengths := List.lengthAppend inner [close]
      let shorter: inner.length < bound := arithmetic [small, Eq.cong List.length isMore, lengths]
      runsParenAtomOf self modes item more rest value isOpen plain
        (rewrite isMore, isValue then
          runsBracketed self modes item close inner rest first
            (selfRuns { modes = modes.inBrackets, level = LevelFull } inner [close, ..rest] first innerReads shorter)
            closes
            isClose)
    | Inr
        (Inr
          (Inl
            (read1, comma, read2, steps, close, first, second, isMore, isValue, isOpen, plain, firstReads, commaOpen,
              isComma, secondReads, others, closes, isClose))) =>
      let inner: Goal := { modes = modes.inBrackets, level = LevelFull }
      let tail := [comma, ..read2] ++ (commaReads steps ++ [close])
      let lengths := (
        List.lengthAppend read1 tail,
        List.lengthAppend [comma, ..read2] (commaReads steps ++ [close]),
        List.lengthAppend (commaReads steps) [close]
      )
      let (whole, middle, last) := lengths
      let sized := Eq.cong List.length isMore
      runsParenAtomOf self modes item more rest value isOpen plain
        (rewrite isMore, isValue then
          runsTuple self modes item comma close read1 read2 rest first second steps
            (selfRuns inner read1 (tail ++ rest) first firstReads (arithmetic [small, sized, whole]))
            commaOpen
            isComma
            (selfRuns inner read2
              ((commaReads steps ++ [close]) ++ rest)
              second
              secondReads
              (arithmetic [small, sized, whole, middle, last]))
            (commaRunsOf modes.inBrackets
              (tupleEnds modes.inBrackets)
              (sub inner)
              (() => full self modes.inBrackets)
              bound
              2
              steps
              [close, ..rest]
              (selfRuns inner)
              (arithmetic [small, sized, whole, middle, last])
              others)
            closes
            isClose)
    | Inr (Inr (Inr (Inl (close, isMore, isValue, isOpen, plain, closes, isClose)))) =>
      runsBracketAtomOf self modes item more rest value isOpen plain
        (rewrite isMore, isValue then runsListEmpty self modes item close rest closes isClose)
    | Inr
        (Inr
          (Inr
            (Inr
              (Inl
                (read1, steps, close, first, isMore, isValue, isOpen, plain, notEmpty, firstReads, others, closes,
                  isClose))))) =>
      let tail := commaReads steps ++ [close]
      let whole := List.lengthAppend read1 tail
      let last := List.lengthAppend (commaReads steps) [close]
      let sized := Eq.cong List.length isMore
      let elements: ∀ (read later: List Item) (element: Expr) => ListElement sub modes.inBrackets read later element
        → read.length < bound
        → Parse.Runs (() => listItem self modes.inBrackets) read later element :=
        read later element (noSpread, holds) shorter =>
          runsListItem self modes.inBrackets read later element noSpread
            (selfRuns { modes = modes.inBrackets, level = LevelFull } read later element holds shorter)
      runsBracketAtomOf self modes item more rest value isOpen plain
        (rewrite isMore, isValue then
          runsList self modes item close read1 rest first steps notEmpty
            (elements read1 (tail ++ rest) first firstReads (arithmetic [small, sized, whole]))
            (commaRunsOf modes.inBrackets
              (count => modes.inBrackets.at RBracket)
              (ListElement sub modes.inBrackets)
              (() => listItem self modes.inBrackets)
              bound
              1
              steps
              [close, ..rest]
              elements
              (arithmetic [small, sized, whole, last])
              others)
            closes
            isClose)
    | Inr (Inr (Inr (Inr (Inr (Inl (number, isMore, isValue, isMinus, numeral)))))) =>
      rewrite isMore, isValue, isMinus then runsNegativeNumber self modes item number rest numeral
    | Inr (Inr (Inr (Inr (Inr (Inr (operand, isValue, signed, operandReads)))))) =>
      let operandRuns := selfRuns { modes, level = LevelArgument } more rest operand operandReads (arithmetic [small])
      match signed with
        | Inl (isMinus, notNumeral, negates) =>
          rewrite isValue, isMinus then
            runsNegativeAtom self modes item more rest operand notNumeral negates operandRuns
        | Inr (isBang, negates) =>
          rewrite isValue, isBang then runsPrefixBang self modes item more rest operand negates operandRuns

--| A base's first item is no `.`.
theorem baseNotDot ∀ (sub: Goal → List Item → List Item → Expr → Prop) (modes: Modes) (item: Item)
    (more rest: List Item) (value: Expr)
    (reads: BaseReads sub modes item more rest value):
    (item.kind == Dot) = False :=
  match reads with
    | Inl (_, _, word) => (wordKinds item.kind word).right.right.right.right
    | Inr (Inl (_, _, _, _, _, isOpen, _)) => rewrite isOpen
    | Inr (Inr (Inl (_, _, _, _, _, _, _, _, _, isOpen, _))) => rewrite isOpen
    | Inr (Inr (Inr (Inl (_, _, _, isOpen, _)))) => rewrite isOpen
    | Inr (Inr (Inr (Inr (Inl (_, _, _, _, _, _, isOpen, _))))) => rewrite isOpen
    | Inr (Inr (Inr (Inr (Inr (Inl (_, _, _, isMinus, _)))))) => rewrite isMinus
    | Inr (Inr (Inr (Inr (Inr (Inr (_, _, signed, _)))))) =>
      match signed with
        | Inl (isMinus, _) => rewrite isMinus
        | Inr (isBang, _) => rewrite isBang

--| What `AtomReads` holds of, `atom` reads.
theorem runsAtomTree ∀ (sub: Goal → List Item → List Item → Expr → Prop) (self: Goal → {Parse Item} Expr) (bound: Nat)
    (modes: Modes) (head: Bool) (read rest: List Item) (value: Expr)
    (selfRuns: SelfRuns sub self bound)
    (small: read.length <= bound)
    (reads: AtomReads sub modes head read rest value):
    Parse.Runs (() => atom self modes head) read rest value :=
  let (item, more, isRead, open, ends, base) := reads
  rewrite isRead then
    runsAtomFrom self modes head item more rest value open
      (runsBase sub self bound modes item more rest value selfRuns
        (arithmetic [small, Eq.cong List.length isRead])
        base)
      (baseNotDot sub modes item more rest value base)
      ends.plain
      ends.noCall
      ends.noDot

-- Applications.

--| An argument: no method section starting a line, no constructor's fields, then what `self` reads at the
--| argument level.
def ArgumentReads (sub: Goal → List Item → List Item → Expr → Prop) (modes: Modes) (read rest: List Item) (value: Expr):
    Prop :=
  sectionLineAt modes (read ++ rest) = False
    ∧ (isSome Upper (peekIn modes 0 (read ++ rest)) && isSome LBrace (peekIn modes 1 (read ++ rest))) = False
    ∧ sub { modes, level = LevelArgument } read rest value

--| The arguments after the first, as `Parse.LoopRuns` has `arguments`' rounds: each starts an atom and is an
--| argument; after the last, nothing starts one.
def ArgsReads (sub: Goal → List Item → List Item → Expr → Prop) (modes: Modes):
    List (List Item, Expr) → List Item → Prop
  | [], rest => startsAtomOn modes rest = False
  | [(read, value), ..steps], rest =>
    read ≠ []
      ∧ startsAtomOn modes (read ++ Parse.loopReads [] steps ++ rest) = True
      ∧ ArgumentReads sub modes read (Parse.loopReads [] steps ++ rest) value
      ∧ ArgsReads sub modes steps rest

--| What `app` reads: a head atom, alone or with arguments.
def AppReads (sub: Goal → List Item → List Item → Expr → Prop) (modes: Modes) (read rest: List Item) (value: Expr):
    Prop :=
  (isSome Dot (peekIn modes 0 (read ++ rest)) = False
    ∧ AtomReads sub modes True read rest value
    ∧ startsAtomOn modes rest = False)
    ∨ (∃ (headRead read1: List Item) (steps: List (List Item, Expr)) (head first: Expr) => read
      = headRead ++ (read1 ++ Parse.loopReads [] steps)
      ∧ value = App head [first, ..Parse.stepValues steps]
      ∧ isSome Dot (peekIn modes 0 (read ++ rest)) = False
      ∧ AtomReads sub modes True headRead ((read1 ++ Parse.loopReads [] steps) ++ rest) head
      ∧ startsAtomOn modes ((read1 ++ Parse.loopReads [] steps) ++ rest) = True
      ∧ ArgumentReads sub modes read1 (Parse.loopReads [] steps ++ rest) first
      ∧ ArgsReads sub modes steps rest)

-- Unary.

--| What `unary` reads: a sign and what `self` reads at the unary level; or an application, after a `-1` or after
--| no sign.
def UnaryReads (sub: Goal → List Item → List Item → Expr → Prop) (modes: Modes) (read rest: List Item) (value: Expr):
    Prop :=
  (∃ (sign: Item) (more: List Item) (operand: Expr) => read = [sign, ..more]
    ∧ value = Prefix sign.leaf.word operand
    ∧ modes.stops sign = False
    ∧ (sign.kind == Minus || sign.kind == Bang) = True
    ∧ matchesBarOn modes [sign, ..more ++ rest] = False
    ∧ (sign.kind == Minus && negativeNumeral [sign, ..more ++ rest]) = False
    ∧ sub { modes, level = LevelUnary } more rest operand)
    ∨ (∃ (item: Item) (more: List Item) => read = [item, ..more]
      ∧ modes.stops item = False
      ∧ (item.kind == KwMatch) = False
      ∧ matchesBarOn modes [item, ..more ++ rest] = False
      ∧ ((item.kind == Minus || item.kind == Bang) = False
        ∨ ((item.kind == Minus) = True ∧ negativeNumeral [item, ..more ++ rest] = True))
      ∧ AppReads sub modes read rest value)

-- The operator ladder.

--| The links of a chain, as `LinkRuns` has them, each operand one that `operand` holds of.
def LinkReads (modes: Modes) (takes: Tok → Bool) (operand: List Item → List Item → Expr → Prop):
    List (Item, List Item, Expr) → List Item → Prop
  | [], rest => takesAhead modes takes rest = False
  | [(operator, read, value), ..links], rest =>
    modes.stops operator = False
      ∧ takes operator.kind = True
      ∧ operand read (Parse.loopReads [] (linkSteps links) ++ rest) value
      ∧ LinkReads modes takes operand links rest

--| A chain: a first operand, then links; `nested` is how the parser builds it (`leftNested` or `rightNested`).
def ChainReads (modes: Modes) (takes: Tok → Bool) (nested: Expr → List (Word, Expr) → Expr)
    (first operand: List Item → List Item → Expr → Prop) (read rest: List Item) (value: Expr):
    Prop :=
  ∃ (headRead: List Item) (head: Expr) (links: List (Item, List Item, Expr)) => read
    = headRead ++ Parse.loopReads [] (linkSteps links)
    ∧ value = nested head (Parse.stepValues (linkSteps links))
    ∧ first headRead (Parse.loopReads [] (linkSteps links) ++ rest) head
    ∧ LinkReads modes takes operand links rest

def MulReads (sub: Goal → List Item → List Item → Expr → Prop) (modes: Modes) (read rest: List Item) (value: Expr):
    Prop :=
  ChainReads modes
    (kind => kind == Star || kind == Slash || kind == Percent)
    leftNested
    (UnaryReads sub modes)
    (UnaryReads sub modes)
    read
    rest
    value

def AddReads (sub: Goal → List Item → List Item → Expr → Prop) (modes: Modes) (read rest: List Item) (value: Expr):
    Prop :=
  ChainReads modes
    (kind => kind == Plus || kind == Minus)
    leftNested
    (MulReads sub modes)
    (MulReads sub modes)
    read
    rest
    value

def AppendReads (sub: Goal → List Item → List Item → Expr → Prop) (modes: Modes) (read rest: List Item) (value: Expr):
    Prop :=
  ChainReads modes (kind => kind == PlusPlus) rightNested (AddReads sub modes) (AddReads sub modes) read rest value

--| No range or pipe after.
def PipedReads (sub: Goal → List Item → List Item → Expr → Prop) (modes: Modes) (read rest: List Item) (value: Expr):
    Prop :=
  rangeAhead modes rest = False ∧ atPipeOn modes rest = False ∧ AppendReads sub modes read rest value

--| What `cmpExpr` reads: a piped operand, alone or compared with one more.
def CmpReads (sub: Goal → List Item → List Item → Expr → Prop) (modes: Modes) (read rest: List Item) (value: Expr):
    Prop :=
  (PipedReads sub modes read rest value ∧ cmpAhead modes rest = False)
    ∨ (∃ (read1: List Item) (operator: Item) (read2: List Item) (lhs second: Expr) => read
      = read1 ++ [operator, ..read2]
      ∧ value = Infix InfixBinary lhs operator.leaf.word second
      ∧ PipedReads sub modes read1 ([operator, ..read2] ++ rest) lhs
      ∧ modes.stops operator = False
      ∧ (operator.kind == KwIn || operator.kind == NotIn) = False
      ∧ operator.kind.isComparison = True
      ∧ isSome KwIf (peekIn modes 0 (read2 ++ rest)) = False
      ∧ PipedReads sub modes read2 rest second
      ∧ cmpAhead modes rest = False)

--| The `&&` and `||` links, as `LogicRuns` has them.
def LogicReads (sub: Goal → List Item → List Item → Expr → Prop) (modes: Modes):
    List (Item, List Item, Expr) → List Item → Prop
  | [], rest => andOrOn modes rest = False
  | [(operator, read, value), ..links], rest =>
    modes.stops operator = False
      ∧ (operator.kind == AndAnd || operator.kind == OrOr) = True
      ∧ isSome KwExists (peekIn modes 0 (read ++ Parse.loopReads [] (linkSteps links) ++ rest)) = False
      ∧ isSome KwForall (peekIn modes 0 (read ++ Parse.loopReads [] (linkSteps links) ++ rest)) = False
      ∧ CmpReads sub modes read (Parse.loopReads [] (linkSteps links) ++ rest) value
      ∧ LogicReads sub modes links rest

--| What `logicAfter` reads after `compared`: nothing, or `&&` and `||` links.
def LogicAfterReads (sub: Goal → List Item → List Item → Expr → Prop) (modes: Modes) (compared: Expr)
    (read rest: List Item) (value: Expr):
    Prop :=
  (read = [] ∧ value = compared ∧ andOrOn modes rest = False)
    ∨ (∃ (links: List (Item, List Item, Expr)) => read = Parse.loopReads [] (linkSteps links)
      ∧ value
        = groupLogic ((Parse.stepValues (linkSteps links)).length + 1) compared (Parse.stepValues (linkSteps links))
      ∧ andOrOn modes (read ++ rest) = True
      ∧ LogicReads sub modes links rest)

--| A result type with no ability row: what `self` reads in full in the modes `allowBrace` gives.
def ResultReads (sub: Goal → List Item → List Item → Expr → Prop) (modes: Modes) (read rest: List Item) (value: Expr):
    Prop :=
  rowOn (isSome LBrace (peekIn (allowBraceOn modes (read ++ rest)) 0 (read ++ rest))) (read ++ rest) = False
    ∧ sub { modes = allowBraceOn modes (read ++ rest), level = LevelFull } read rest value

--| What `opEnd` reads after `logic`: nothing, or `->` and a result type.
def EndReads (sub: Goal → List Item → List Item → Expr → Prop) (modes: Modes) (logic: Expr) (sequence: Bool)
    (read rest: List Item) (value: Expr):
    Prop :=
  (read = [] ∧ value = logic ∧ opEndsAhead modes sequence rest = False)
    ∨ (∃ (arrow: Item) (more: List Item) (result: Expr) => read = [arrow, ..more]
      ∧ value = Infix InfixArrow logic arrow.leaf.word result
      ∧ modes.stops arrow = False
      ∧ arrow.kind = Arrow
      ∧ ResultReads sub modes more rest result)

--| What `operatorExpr` reads: a comparison, its logic links, no `<->`, and its end.
def OperatorReads (sub: Goal → List Item → List Item → Expr → Prop) (modes: Modes) (read rest: List Item) (value: Expr):
    Prop :=
  ∃ (read1 read2 read3: List Item) (compared logic: Expr) => read = read1 ++ read2 ++ read3
    ∧ isSome Dot (peekIn modes 0 ((read1 ++ read2 ++ read3) ++ rest)) = False
    ∧ CmpReads sub modes read1 (read2 ++ read3 ++ rest) compared
    ∧ LogicAfterReads sub modes compared read2 (read3 ++ rest) logic
    ∧ isSome IffArrow (peekIn modes 0 (read3 ++ rest)) = False
    ∧ EndReads sub modes logic (sequenceOn modes (read3 ++ rest)) read3 rest value

-- Expressions in full.

--| What `exprInline` reads from `item` on.
def InlineAt (sub: Goal → List Item → List Item → Expr → Prop) (modes: Modes) (item: Item)
    (more rest: List Item) (value: Expr):
    Prop :=
  modes.stops item = False
    ∧ InlinePlain modes item [item, ..more ++ rest]
    ∧ OperatorReads sub modes [item, ..more] rest value

--| What `exprBlock` reads from `item` on: one line at its column, right of the limit, read inline in every line
--| mode `block` may give it.
def BlockAt (sub: Goal → List Item → List Item → Expr → Prop) (modes: Modes) (item: Item)
    (more rest: List Item) (value: Expr):
    Prop :=
  rightOfLimit item.leaf.token.column modes.limit = True
    ∧ continuesAt item.leaf.token.column rest = False
    ∧ startsOtherStatement item.kind = False
    ∧ ∀ (kind: LineKind) (before: Nat) => InlineAt sub
      (lineModes (blockModes modes item.leaf.token.column True) item.leaf.token.column True before kind)
      item
      more
      rest
      value

--| What `expr` reads: inline (as at the start of the input, where no block starts); and a block where one starts.
def FullReads (sub: Goal → List Item → List Item → Expr → Prop) (modes: Modes) (read rest: List Item) (value: Expr):
    Prop :=
  ∃ (item: Item) (more: List Item) => read = [item, ..more]
    ∧ InlineAt sub modes item more rest value
    ∧ (startsBlock modes True item = True → BlockAt sub modes item more rest value)

-- The relation.

--| One rung for each level the parser calls itself at in slice 1, the calls inside named through `sub`.
def Layer (sub: Goal → List Item → List Item → Expr → Prop) (goal: Goal) (read rest: List Item) (value: Expr): Prop :=
  match goal.level with
    | LevelFull => FullReads sub goal.modes read rest value
    | LevelUnary => UnaryReads sub goal.modes read rest value
    | LevelArgument => AtomReads sub goal.modes False read rest value
    | _ => Void

--| `Layer` nested at most `depth` deep.
def TreeN: Nat → Goal → List Item → List Item → Expr → Prop
  | Zero, _, _, _, _ => Void
  | Succ depth, goal, read, rest, value => Layer (TreeN depth) goal read rest value

--| The tree-to-items relation: `read`, followed by `rest`, is what the parser at `goal` should read as `value`.
def Tree (goal: Goal) (read rest: List Item) (value: Expr): Prop := ∃ (depth: Nat) => TreeN depth goal read rest value

-- From the rungs to runs: applications and unary.

--| The later arguments' rounds, each read by `argument` through `self`.
--|
--| Proof idea: round by round, `runsArgumentStepSome` with `runsArgument` and `selfRuns`, each argument within
--| the bound; after the last, `runsArgumentStepNone`.
theorem argsRunsOf ∀ (sub: Goal → List Item → List Item → Expr → Prop) (self: Goal → {Parse Item} Expr) (bound: Nat)
    (modes: Modes) (steps: List (List Item, Expr)) (rest: List Item)
    (selfRuns: SelfRuns sub self bound)
    (small: (Parse.loopReads [] steps).length < bound)
    (reads: ArgsReads sub modes steps rest):
    Parse.LoopRuns (() => argumentStep self modes (startsAtom modes)) [] steps rest :=
  match steps, small, reads with
    | [], _, ends => runsArgumentStepNone self modes rest ends
    | [(read, value), ..later], small, (nonEmpty, starts, (noLine, noBrace, holds), more) =>
      let lengths := List.lengthAppend read (Parse.loopReads [] later)
      (
        nonEmpty,
        runsArgumentStepSome self modes read
          (Parse.loopReads [] later ++ rest)
          value
          starts
          (runsArgument self modes read
            (Parse.loopReads [] later ++ rest)
            value
            noLine
            noBrace
            (selfRuns
              { modes, level = LevelArgument }
              read
              (Parse.loopReads [] later ++ rest)
              value
              holds
              (arithmetic [small, lengths]))),
        argsRunsOf sub self bound modes later rest selfRuns (arithmetic [small, lengths]) more
      )

--| What `AppReads` holds of, `app` reads.
--|
--| Proof idea: from any start, a head alone is `runsAppAtHead`; with arguments, `runsAppAtCall`, the head by
--| `runsAtomTree`, the arguments through `selfRuns`, each shorter than the whole since the head reads an item.
theorem runsAppTree ∀ (sub: Goal → List Item → List Item → Expr → Prop) (self: Goal → {Parse Item} Expr) (bound: Nat)
    (modes: Modes) (read rest: List Item) (value: Expr)
    (selfRuns: SelfRuns sub self bound)
    (small: read.length <= bound)
    (reads: AppReads sub modes read rest value):
    Parse.Runs (() => app self modes) read rest value :=
  runsApp self modes read rest value (start =>
    match reads with
      | Inl (noSection, atomReads, ends) =>
        runsAppAtHead self modes start read rest value noSection
          (runsAtomTree sub self bound modes True read rest value selfRuns small atomReads)
          ends
      | Inr (headRead, read1, steps, head, first, isRead, isValue, noSection, headReads, starts, firstReads, more) =>
        let (item, itemMore, isHead, _) := headReads
        let (noLine, noBrace, firstHolds) := firstReads
        let loops := Parse.loopReads [] steps
        let sizes := (
          Eq.cong List.length isRead,
          List.lengthAppend headRead (read1 ++ loops),
          List.lengthAppend read1 loops,
          Eq.cong List.length isHead
        )
        let (whole, split, args, headSize) := sizes
        rewrite isRead, isValue then
          runsAppAtCall self modes start headRead read1 rest head first steps
            (rewrite <- isRead then noSection)
            (runsAtomTree sub self bound modes True headRead
              ((read1 ++ loops) ++ rest)
              head
              selfRuns
              (arithmetic [small, whole, split])
              headReads)
            starts
            (runsArgument self modes read1
              (loops ++ rest)
              first
              noLine
              noBrace
              (selfRuns
                { modes, level = LevelArgument }
                read1
                (loops ++ rest)
                first
                firstHolds
                (arithmetic [small, whole, split, args, headSize])))
            (argsRunsOf sub self bound modes steps rest selfRuns
              (arithmetic [small, whole, split, args, headSize])
              more))

--| A sign is no `match`.
theorem signNotMatch ∀ (kind: Tok) (signed: (kind == Minus || kind == Bang) = True): (kind == KwMatch) = False :=
  match kind, signed with
    | Minus, _ => byComputing
    | Bang, _ => byComputing
    | other, signed => (Bool.falseNotTrue signed).impossible

--| What `UnaryReads` holds of, `unary` reads.
--|
--| Proof idea: a sign is `runsUnaryPrefix` with the operand through `selfRuns`; otherwise `runsUnaryApp` or, after
--| a `-1`, `runsUnaryNumeral`, with `runsAppTree`.
theorem runsUnaryTree ∀ (sub: Goal → List Item → List Item → Expr → Prop) (self: Goal → {Parse Item} Expr) (bound: Nat)
    (modes: Modes) (read rest: List Item) (value: Expr)
    (selfRuns: SelfRuns sub self bound)
    (small: read.length <= bound)
    (reads: UnaryReads sub modes read rest value):
    Parse.Runs (() => unary self modes) read rest value :=
  match reads with
    | Inl (sign, more, operand, isRead, isValue, open, signed, noBar, notNumeral, operandReads) =>
      let shorter: more.length < bound := arithmetic [small, Eq.cong List.length isRead]
      rewrite isRead, isValue then
        runsUnaryPrefix self modes sign more rest operand open signed
          (signNotMatch sign.kind signed)
          noBar
          notNumeral
          (selfRuns { modes, level = LevelUnary } more rest operand operandReads shorter)
    | Inr (item, more, isRead, open, notMatch, noBar, route, appReads) =>
      let appRuns := runsAppTree sub self bound modes read rest value selfRuns small appReads
      match route with
        | Inl unsigned =>
          rewrite isRead then
            runsUnaryApp self modes item more rest value open notMatch noBar unsigned (rewrite <- isRead then appRuns)
        | Inr (minus, numeral) =>
          rewrite isRead then
            runsUnaryNumeral self modes item more rest value open minus noBar numeral (rewrite <- isRead then appRuns)

-- From the rungs to runs: the operator ladder.

--| `LinkReads` gives `LinkRuns` where each operand `operandReads` holds of is one `operand` reads.
theorem linkRunsOf ∀ (modes: Modes) (takes: Tok → Bool) (operandReads: List Item → List Item → Expr → Prop)
    (operand: () → {Parse Item} Expr) (bound: Nat) (links: List (Item, List Item, Expr)) (rest: List Item)
    (converts: ∀ (read later: List Item) (value: Expr) => operandReads read later value
      → read.length <= bound
      → Parse.Runs operand read later value)
    (small: (Parse.loopReads [] (linkSteps links)).length <= bound)
    (reads: LinkReads modes takes operandReads links rest):
    LinkRuns modes takes operand links rest :=
  match links, small, reads with
    | [], _, ends => ends
    | [(operator, read, value), ..later], small, (open, took, holds, more) =>
      let lengths := List.lengthAppend [operator, ..read] (Parse.loopReads [] (linkSteps later))
      (
        open,
        took,
        converts read (Parse.loopReads [] (linkSteps later) ++ rest) value holds (arithmetic [small, lengths]),
        linkRunsOf modes takes operandReads operand bound later rest converts (arithmetic [small, lengths]) more
      )

--| What `MulReads` holds of, `mulExpr` reads.
--|
--| Proof idea: `runsMulExpr`, the first operand and each link's by `runsUnaryTree`, each within the bound since
--| the chain's reads add up to the whole.
theorem runsMulTree ∀ (sub: Goal → List Item → List Item → Expr → Prop) (self: Goal → {Parse Item} Expr) (bound: Nat)
    (modes: Modes) (read rest: List Item) (value: Expr)
    (selfRuns: SelfRuns sub self bound)
    (small: read.length <= bound)
    (reads: MulReads sub modes read rest value):
    Parse.Runs (() => mulExpr self modes) read rest value :=
  let (headRead, head, links, isRead, isValue, headReads, linkReads) := reads
  let loops := Parse.loopReads [] (linkSteps links)
  let whole := Eq.cong List.length isRead
  let split := List.lengthAppend headRead loops
  rewrite isRead, isValue then
    runsMulExpr self modes headRead rest head links
      (runsUnaryTree sub self bound modes headRead
        (loops ++ rest)
        head
        selfRuns
        (arithmetic [small, whole, split])
        headReads)
      (linkRunsOf modes
        (kind => kind == Star || kind == Slash || kind == Percent)
        (UnaryReads sub modes)
        (() => unary self modes)
        bound
        links
        rest
        (operandRead later operand holds short =>
          runsUnaryTree sub self bound modes operandRead later operand selfRuns short holds)
        (arithmetic [small, whole, split])
        linkReads)

--| What `AddReads` holds of, `addExpr` reads.
--|
--| Proof idea: as `runsMulTree`, one rung up: `runsAddExpr` with the operands by `runsMulTree`.
theorem runsAddTree ∀ (sub: Goal → List Item → List Item → Expr → Prop) (self: Goal → {Parse Item} Expr) (bound: Nat)
    (modes: Modes) (read rest: List Item) (value: Expr)
    (selfRuns: SelfRuns sub self bound)
    (small: read.length <= bound)
    (reads: AddReads sub modes read rest value):
    Parse.Runs (() => addExpr self modes) read rest value :=
  let (headRead, head, links, isRead, isValue, headReads, linkReads) := reads
  let loops := Parse.loopReads [] (linkSteps links)
  let whole := Eq.cong List.length isRead
  let split := List.lengthAppend headRead loops
  rewrite isRead, isValue then
    runsAddExpr self modes headRead rest head links
      (runsMulTree sub self bound modes headRead
        (loops ++ rest)
        head
        selfRuns
        (arithmetic [small, whole, split])
        headReads)
      (linkRunsOf modes
        (kind => kind == Plus || kind == Minus)
        (MulReads sub modes)
        (() => mulExpr self modes)
        bound
        links
        rest
        (operandRead later operand holds short =>
          runsMulTree sub self bound modes operandRead later operand selfRuns short holds)
        (arithmetic [small, whole, split])
        linkReads)

--| What `AppendReads` holds of, `appendExpr` reads.
--|
--| Proof idea: as `runsMulTree`, with `runsAppendExpr` (nested to the right) and the operands by `runsAddTree`.
theorem runsAppendTree ∀ (sub: Goal → List Item → List Item → Expr → Prop) (self: Goal → {Parse Item} Expr) (bound: Nat)
    (modes: Modes) (read rest: List Item) (value: Expr)
    (selfRuns: SelfRuns sub self bound)
    (small: read.length <= bound)
    (reads: AppendReads sub modes read rest value):
    Parse.Runs (() => appendExpr self modes) read rest value :=
  let (headRead, head, links, isRead, isValue, headReads, linkReads) := reads
  let loops := Parse.loopReads [] (linkSteps links)
  let whole := Eq.cong List.length isRead
  let split := List.lengthAppend headRead loops
  rewrite isRead, isValue then
    runsAppendExpr self modes headRead rest head links
      (runsAddTree sub self bound modes headRead
        (loops ++ rest)
        head
        selfRuns
        (arithmetic [small, whole, split])
        headReads)
      (linkRunsOf modes
        (kind => kind == PlusPlus)
        (AddReads sub modes)
        (() => addExpr self modes)
        bound
        links
        rest
        (operandRead later operand holds short =>
          runsAddTree sub self bound modes operandRead later operand selfRuns short holds)
        (arithmetic [small, whole, split])
        linkReads)

--| What `PipedReads` holds of, `pipedRange` reads.
theorem runsPipedTree ∀ (sub: Goal → List Item → List Item → Expr → Prop) (self: Goal → {Parse Item} Expr) (bound: Nat)
    (modes: Modes) (read rest: List Item) (value: Expr)
    (selfRuns: SelfRuns sub self bound)
    (small: read.length <= bound)
    (reads: PipedReads sub modes read rest value):
    Parse.Runs (() => pipedRange self modes) read rest value :=
  let (noRange, noPipe, appendReads) := reads
  runsPipedRange self modes read rest value noRange noPipe
    (runsAppendTree sub self bound modes read rest value selfRuns small appendReads)

--| What `CmpReads` holds of, `cmpExpr` reads.
--|
--| Proof idea: alone, `runsCmpPlain`; compared, `runsCmpCompare`, each side by `runsPipedTree`.
theorem runsCmpTree ∀ (sub: Goal → List Item → List Item → Expr → Prop) (self: Goal → {Parse Item} Expr) (bound: Nat)
    (modes: Modes) (read rest: List Item) (value: Expr)
    (selfRuns: SelfRuns sub self bound)
    (small: read.length <= bound)
    (reads: CmpReads sub modes read rest value):
    Parse.Runs (() => cmpExpr self modes) read rest value :=
  match reads with
    | Inl (pipedReads, noCmp) =>
      runsCmpPlain self modes read rest value
        (runsPipedTree sub self bound modes read rest value selfRuns small pipedReads)
        noCmp
    | Inr
        (read1, operator, read2, lhs, second, isRead, isValue, firstReads, open, notIn, compares, noIf, secondReads,
          noChain) =>
      let whole := Eq.cong List.length isRead
      let split := List.lengthAppend read1 [operator, ..read2]
      rewrite isRead, isValue then
        runsCmpCompare self modes read1 read2 rest lhs second operator
          (runsPipedTree sub self bound modes read1
            ([operator, ..read2] ++ rest)
            lhs
            selfRuns
            (arithmetic [small, whole, split])
            firstReads)
          open
          notIn
          compares
          noIf
          (runsPipedTree sub self bound modes read2 rest second selfRuns (arithmetic [small, whole, split]) secondReads)
          noChain

--| `LogicReads` gives `LogicRuns`.
--|
--| Proof idea: link by link, each comparison by `runsCmpTree`.
theorem logicRunsOf ∀ (sub: Goal → List Item → List Item → Expr → Prop) (self: Goal → {Parse Item} Expr) (bound: Nat)
    (modes: Modes) (links: List (Item, List Item, Expr)) (rest: List Item)
    (selfRuns: SelfRuns sub self bound)
    (small: (Parse.loopReads [] (linkSteps links)).length <= bound)
    (reads: LogicReads sub modes links rest):
    LogicRuns self modes links rest :=
  match links, small, reads with
    | [], _, ends => ends
    | [(operator, read, value), ..later], small, (open, andOr, noExists, noForall, holds, more) =>
      let lengths := List.lengthAppend [operator, ..read] (Parse.loopReads [] (linkSteps later))
      (
        open,
        andOr,
        noExists,
        noForall,
        runsCmpTree sub self bound modes read
          (Parse.loopReads [] (linkSteps later) ++ rest)
          value
          selfRuns
          (arithmetic [small, lengths])
          holds,
        logicRunsOf sub self bound modes later rest selfRuns (arithmetic [small, lengths]) more
      )

--| What `LogicAfterReads` holds of, `logicAfter` reads.
theorem runsLogicAfterTree ∀ (sub: Goal → List Item → List Item → Expr → Prop) (self: Goal → {Parse Item} Expr)
    (bound: Nat) (modes: Modes) (compared: Expr) (read rest: List Item) (value: Expr)
    (selfRuns: SelfRuns sub self bound)
    (small: read.length <= bound)
    (reads: LogicAfterReads sub modes compared read rest value):
    Parse.Runs (() => logicAfter self modes compared) read rest value :=
  match reads with
    | Inl (isRead, isValue, ends) => rewrite isRead, isValue then runsLogicAfterNone self modes compared rest ends
    | Inr (links, isRead, isValue, ahead, linkReads) =>
      rewrite isRead, isValue then
        runsLogicAfterChain self modes compared links rest
          (rewrite <- isRead then ahead)
          (logicRunsOf sub self bound modes links rest selfRuns (rewrite <- isRead then small) linkReads)

--| What `EndReads` holds of, `opEnd` reads: the result after `->` is a call to `self`, shorter than the whole.
theorem runsEndTree ∀ (sub: Goal → List Item → List Item → Expr → Prop) (self: Goal → {Parse Item} Expr) (bound: Nat)
    (modes: Modes) (logic: Expr) (sequence: Bool) (read rest: List Item) (value: Expr)
    (selfRuns: SelfRuns sub self bound)
    (small: read.length <= bound)
    (reads: EndReads sub modes logic sequence read rest value):
    Parse.Runs (() => opEnd self modes logic sequence modes.peek) read rest value :=
  match reads with
    | Inl (isRead, isValue, ends) => rewrite isRead, isValue then runsOpEndNone self modes logic sequence rest ends
    | Inr (arrow, more, result, isRead, isValue, open, isArrow, (noRow, resultHolds)) =>
      let shorter: more.length < bound := arithmetic [small, Eq.cong List.length isRead]
      rewrite isRead, isValue then
        runsOpEndArrow self modes logic result sequence arrow more rest open isArrow
          (runsResultPlain self modes more rest result noRow
            (selfRuns
              { modes = allowBraceOn modes (more ++ rest), level = LevelFull }
              more
              rest
              result
              resultHolds
              shorter))

--| What `OperatorReads` holds of, `operatorExpr` reads.
--|
--| Proof idea: `runsOpStartWith` from any start, its three parts by `runsCmpTree`, `runsLogicAfterTree` and
--| `runsEndTree`, each part within the bound.
theorem runsOperatorTree ∀ (sub: Goal → List Item → List Item → Expr → Prop) (self: Goal → {Parse Item} Expr)
    (bound: Nat) (modes: Modes) (read rest: List Item) (value: Expr)
    (selfRuns: SelfRuns sub self bound)
    (small: read.length <= bound)
    (reads: OperatorReads sub modes read rest value):
    Parse.Runs (() => operatorExpr self modes) read rest value :=
  let (read1, read2, read3, compared, logic, isRead, noSection, cmpReads, logicReads, noIff, endReads) := reads
  let sizes := (Eq.cong List.length isRead, List.lengthAppend read1 (read2 ++ read3), List.lengthAppend read2 read3)
  let (whole, first, later) := sizes
  runsOperatorExpr self modes read rest value (start =>
    rewrite isRead then
      runsOpStartWith self modes start read1 read2 read3 rest compared logic value noSection
        (runsCmpTree sub self bound modes read1
          (read2 ++ read3 ++ rest)
          compared
          selfRuns
          (arithmetic [small, whole, first])
          cmpReads)
        (runsLogicAfterTree sub self bound modes compared read2
          (read3 ++ rest)
          logic
          selfRuns
          (arithmetic [small, whole, first, later])
          logicReads)
        noIff
        (runsEndTree sub self bound modes logic
          (sequenceOn modes (read3 ++ rest))
          read3
          rest
          value
          selfRuns
          (arithmetic [small, whole, first, later])
          endReads))

-- Expressions in full, and the knot.

--| What `InlineAt` holds of, `exprInline` reads.
theorem runsInlineTree ∀ (sub: Goal → List Item → List Item → Expr → Prop) (self: Goal → {Parse Item} Expr) (bound: Nat)
    (modes: Modes) (item: Item) (more rest: List Item) (value: Expr)
    (selfRuns: SelfRuns sub self bound)
    (small: [item, ..more].length <= bound)
    (reads: InlineAt sub modes item more rest value):
    Parse.Runs (() => exprInline self modes) [item, ..more] rest value :=
  let (open, inline, operatorReads) := reads
  runsExprInline self modes item more rest value open inline.notKeyword inline.noLambda inline.noResult
      inline.notQuantifier inline.notIf inline.noImplicit inline.noPi
      (runsOperatorTree sub self bound modes [item, ..more] rest value selfRuns small operatorReads)

--| What `BlockAt` holds of, `exprBlock` reads: one line at the item's column.
--|
--| Proof idea: `runsExprBlock` and `runsBlockLine`, the line in each line mode by `runsStatementValue` and
--| `runsInlineTree`.
theorem runsBlockTree ∀ (sub: Goal → List Item → List Item → Expr → Prop) (self: Goal → {Parse Item} Expr) (bound: Nat)
    (modes: Modes) (item: Item) (more rest: List Item) (value: Expr)
    (selfRuns: SelfRuns sub self bound)
    (small: [item, ..more].length <= bound)
    (reads: BlockAt sub modes item more rest value):
    Parse.Runs (() => exprBlock self modes item) [item, ..more] rest value :=
  let (right, ends, notOther, lines) := reads
  let column := item.leaf.token.column
  runsExprBlock self modes item
    [item, ..more]
    rest
    value
    right
    (runsBlockLine self modes column
      [item, ..more]
      rest
      value
      (kind before =>
        let lined := lineModes (blockModes modes column True) column True before kind
        let line := lines kind before
        runsStatementValue self lined item more rest value line.left notOther
          (runsInlineTree sub self bound lined item more rest value selfRuns small line))
      ends)

theorem andFalseMiddle ∀ (a c: Bool): (a && False && c) = False := match a with
  | True => byComputing
  | False => byComputing

--| A block starts only after the input's first item.
theorem startsBlockLater ∀ (modes: Modes) (later: Bool) (item: Item)
    (starts: startsBlock modes later item = True):
    startsBlock modes True item = True :=
  match later, starts with
    | True, starts => starts
    | False, starts =>
      let never: startsBlock modes False item = False :=
        andFalseMiddle item.leaf.token.lineStart (modes.allow != Some item.index && !modes.endsConstruct item)
      (Bool.falseNotTrue (Eq.trans never.flipped starts)).impossible

--| What `FullReads` holds of, `expr` reads, from any state.
--|
--| Proof idea: `exprLater` for either answer of `offset() > 0`: where no block starts, `runsInlineTree`; where
--| one does, the input's first item is behind (`startsBlockLater`), so `BlockAt` holds and `runsBlockTree`.
theorem runsFullTree ∀ (sub: Goal → List Item → List Item → Expr → Prop) (self: Goal → {Parse Item} Expr) (bound: Nat)
    (modes: Modes) (read rest: List Item) (value: Expr)
    (selfRuns: SelfRuns sub self bound)
    (small: read.length <= bound)
    (reads: FullReads sub modes read rest value):
    Parse.Runs (() => expr self modes) read rest value :=
  let (item, more, isRead, inlineAt, blockAt) := reads
  let sized: [item, ..more].length <= bound := arithmetic [small, Eq.cong List.length isRead]
  let later: ∀ (later: Bool) => Parse.Runs (() => exprLater self modes later) [item, ..more] rest value := later =>
    match starts: startsBlock modes later item with
      | False =>
        runsExprLaterInline self modes later item more rest value starts
          (runsInlineTree sub self bound modes item more rest value selfRuns sized inlineAt)
      | True =>
        runsExprLaterBlock self modes later item more rest value starts
          (runsBlockTree sub self bound modes item more rest value selfRuns sized
            (blockAt (startsBlockLater modes later item starts)))
  rewrite isRead then
    state => runsFromExpr self modes state [item, ..more] rest value (later (state.at.offset > 0) state)

--| One step of the knot: `expressionRule` reads what `Tree` holds of, given that `self` reads the shorter ones.
--|
--| Proof idea: the depth is a successor, so `Layer` holds of `TreeN` one less, whose reads `nested` runs; then the
--| rung for the goal's level: `runsFullTree`, `runsUnaryTree` or `runsAtomTree`, the bound being the read's own
--| length.
theorem treeStep ∀ (self: Goal → {Parse Item} Expr) (goal: Goal) (read rest: List Item) (value: Expr)
    (tree: Tree goal read rest value)
    (nested: ∀ (inner: Goal) (innerRead innerRest: List Item) (innerValue: Expr) => Tree inner innerRead innerRest
        innerValue
      → innerRead.length < read.length
      → Parse.Runs (() => self inner) innerRead innerRest innerValue):
    Parse.Runs (() => expressionRule self goal) read rest value :=
  let (depth, holds) := tree
  match depth, holds with
    | Zero, never => Void.impossible never
    | Succ inner, layer =>
      let selfRuns: SelfRuns (TreeN inner) self read.length :=
        innerGoal innerRead innerRest innerValue innerHolds shorter =>
          nested innerGoal innerRead innerRest innerValue (inner, innerHolds) shorter
      match goal, layer with
        | { modes, level }, layer =>
          match level, layer with
            | LevelFull, layer =>
              runsFullTree (TreeN inner) self read.length modes read rest value selfRuns (arithmetic []) layer
            | LevelUnary, layer =>
              runsUnaryTree (TreeN inner) self read.length modes read rest value selfRuns (arithmetic []) layer
            | LevelArgument, layer =>
              runsAtomTree (TreeN inner) self read.length modes False read rest value selfRuns (arithmetic []) layer
            | other, layer => Void.impossible layer

--| The knot for a whole tree (ticket 17c): `expressionAt` reads every tree the relation holds of.
theorem runsTree ∀ (goal: Goal) (read rest: List Item) (value: Expr)
    (tree: Tree goal read rest value):
    Parse.Runs (() => expressionAt goal) read rest value :=
  Parse.runsRecursiveWith expressionRule Tree treeStep goal read rest value tree

-- A declaration read whole.

--| What a declaration `def name: type := value` needs read back (ticket 17d's target): the frame's four kinds,
--| the type as `resultType` reads it, and the value in full in the body's modes, each a tree the relation holds
--| of, the look-aheads inside.
type DeclarationTree (keyword name colon colonEq: Item) (typeRead valueRead: List Item) (result value: Expr): Prop = {
  isDef: keyword.kind = KwDef,
  isLower: name.kind = Lower,
  isColon: colon.kind = Colon,
  isColonEq: colonEq.kind = ColonEq,
  typeReads: ResultReads Tree Modes.start typeRead [colonEq, ..valueRead] result,
  valueTree: Tree { modes = { Modes.start | recover = True }, level = LevelFull } valueRead [] value
}

--| Ticket 17c's result: a declaration whose type and value are trees the relation holds of parses, as `parseGroups`
--| runs it, to the definition of that type and value.
theorem declarationTree ∀ (seen: Seen) (keyword name colon colonEq: Item)
    (typeRead valueRead: List Item) (result value: Expr)
    (reads: DeclarationTree keyword name colon colonEq typeRead valueRead result value):
    Parse.run [keyword, name, colon, ..typeRead ++ [colonEq, ..valueRead]] (() =>
      let decl := declaration seen
      decl)
      = Ok (Definition [] (plainHeader keyword name colon result) (Assigned colonEq.leaf.word.comments value)) :=
  let (noRow, typeTree) := reads.typeReads
  declarationRuns seen keyword name colon colonEq typeRead valueRead result value reads.isDef reads.isLower
      reads.isColon
      (runsResultPlain expressionAt Modes.start typeRead
        [colonEq, ..valueRead]
        result
        noRow
        (runsTree _ typeRead [colonEq, ..valueRead] result typeTree))
      reads.isColonEq
      (runsTree _ valueRead [] value reads.valueTree)

-- Building trees: each rung is monotone in `sub`, so children of different depths meet at the deepest.

--| The rungs are monotone in `sub`: what holds of children through one relation holds through a weaker one.
theorem commaMono ∀ (modes: Modes) (ends: Nat → {Parse Item} Bool) (before after: List Item → List Item → Expr → Prop)
    (count: Nat) (steps: List (Item, List Item, Expr))
    (rest: List Item) (map: ∀ (read later: List Item) (value: Expr) => before read later value → after read later value)
    (reads: CommaReads modes ends before count steps rest):
    CommaReads modes ends after count steps rest :=
  match steps, reads with
    | [], ended => ended
    | [(comma, read, value), ..later], (open, isComma, ended, holds, more) => (
      open,
      isComma,
      ended,
      map read (commaReads later ++ rest) value holds,
      commaMono modes ends before after (count + 1) later rest map more
    )

--| `BaseReads` is monotone in `sub`.
--|
--| Proof idea: case by case, mapping each child's fact and the comma lists by `commaMono`.
theorem baseMono ∀ (before after: Goal → List Item → List Item → Expr → Prop)
    (map: ∀ (goal: Goal) (read rest: List Item) (value: Expr) => before goal read rest value
      → after goal read rest value) (modes: Modes) (item: Item) (more rest: List Item) (value: Expr)
    (reads: BaseReads before modes item more rest value):
    BaseReads after modes item more rest value :=
  let inner: Goal := { modes = modes.inBrackets, level = LevelFull }
  let elements: ∀ (read later: List Item) (element: Expr) => ListElement before modes.inBrackets read later element
    → ListElement after modes.inBrackets read later element :=
    read later element (noSpread, holds) => (noSpread, map inner read later element holds)
  match reads with
    | Inl word => Inl word
    | Inr (Inl (innerRead, close, first, isMore, isValue, isOpen, plain, innerReads, closes, isClose)) =>
      Inr
        (Inl (
          innerRead,
          close,
          first,
          isMore,
          isValue,
          isOpen,
          plain,
          map inner innerRead [close, ..rest] first innerReads,
          closes,
          isClose
        ))
    | Inr
        (Inr
          (Inl
            (read1, comma, read2, steps, close, first, second, isMore, isValue, isOpen, plain, firstReads, commaOpen,
              isComma, secondReads, others, closes, isClose))) =>
      Inr
        (Inr
          (Inl (
            read1,
            comma,
            read2,
            steps,
            close,
            first,
            second,
            isMore,
            isValue,
            isOpen,
            plain,
            map inner read1 _ first firstReads,
            commaOpen,
            isComma,
            map inner read2 _ second secondReads,
            commaMono modes.inBrackets
              (tupleEnds modes.inBrackets)
              (before inner)
              (after inner)
              2
              steps
              [close, ..rest]
              (map inner)
              others,
            closes,
            isClose
          )))
    | Inr (Inr (Inr (Inl empty))) => Inr (Inr (Inr (Inl empty)))
    | Inr
        (Inr
          (Inr
            (Inr
              (Inl
                (read1, steps, close, first, isMore, isValue, isOpen, plain, notEmpty, firstReads, others, closes,
                  isClose))))) =>
      Inr
        (Inr
          (Inr
            (Inr
              (Inl (
                read1,
                steps,
                close,
                first,
                isMore,
                isValue,
                isOpen,
                plain,
                notEmpty,
                elements read1 _ first firstReads,
                commaMono modes.inBrackets
                  (count => modes.inBrackets.at RBracket)
                  (ListElement before modes.inBrackets)
                  (ListElement after modes.inBrackets)
                  1
                  steps
                  [close, ..rest]
                  elements
                  others,
                closes,
                isClose
              )))))
    | Inr (Inr (Inr (Inr (Inr (Inl number))))) => Inr (Inr (Inr (Inr (Inr (Inl number)))))
    | Inr (Inr (Inr (Inr (Inr (Inr (operand, isValue, signed, operandReads)))))) =>
      Inr
        (Inr
          (Inr
            (Inr
              (Inr
                (Inr (
                  operand,
                  isValue,
                  signed,
                  map { modes, level = LevelArgument } more rest operand operandReads
                ))))))

theorem atomMono ∀ (before after: Goal → List Item → List Item → Expr → Prop)
    (map: ∀ (goal: Goal) (read rest: List Item) (value: Expr) => before goal read rest value
      → after goal read rest value) (modes: Modes) (head: Bool) (read rest: List Item) (value: Expr)
    (reads: AtomReads before modes head read rest value):
    AtomReads after modes head read rest value :=
  let (item, more, isRead, open, ends, base) := reads
  (item, more, isRead, open, ends, baseMono before after map modes item more rest value base)

theorem argsMono ∀ (before after: Goal → List Item → List Item → Expr → Prop)
    (map: ∀ (goal: Goal) (read rest: List Item) (value: Expr) => before goal read rest value
      → after goal read rest value) (modes: Modes) (steps: List (List Item, Expr)) (rest: List Item)
    (reads: ArgsReads before modes steps rest):
    ArgsReads after modes steps rest :=
  match steps, reads with
    | [], ends => ends
    | [(read, value), ..later], (nonEmpty, starts, (noLine, noBrace, holds), more) => (
      nonEmpty,
      starts,
      (noLine, noBrace, map { modes, level = LevelArgument } read _ value holds),
      argsMono before after map modes later rest more
    )

--| `AppReads` is monotone in `sub`.
--|
--| Proof idea: the head by `atomMono`, the first argument by `map` and the rest by `argsMono`.
theorem appMono ∀ (before after: Goal → List Item → List Item → Expr → Prop)
    (map: ∀ (goal: Goal) (read rest: List Item) (value: Expr) => before goal read rest value
      → after goal read rest value) (modes: Modes) (read rest: List Item) (value: Expr)
    (reads: AppReads before modes read rest value):
    AppReads after modes read rest value :=
  match reads with
    | Inl (noSection, atomReads, ends) =>
      Inl (noSection, atomMono before after map modes True read rest value atomReads, ends)
    | Inr
        (
          headRead,
          read1,
          steps,
          head,
          first,
          isRead,
          isValue,
          noSection,
          headReads,
          starts,
          (noLine, noBrace, firstHolds),
          more
        ) => Inr (
      headRead,
      read1,
      steps,
      head,
      first,
      isRead,
      isValue,
      noSection,
      atomMono before after map modes True headRead _ head headReads,
      starts,
      (noLine, noBrace, map { modes, level = LevelArgument } read1 _ first firstHolds),
      argsMono before after map modes steps rest more
    )

--| `UnaryReads` is monotone in `sub`: the operand by `map`, an application by `appMono`.
theorem unaryMono ∀ (before after: Goal → List Item → List Item → Expr → Prop)
    (map: ∀ (goal: Goal) (read rest: List Item) (value: Expr) => before goal read rest value
      → after goal read rest value) (modes: Modes) (read rest: List Item) (value: Expr)
    (reads: UnaryReads before modes read rest value):
    UnaryReads after modes read rest value :=
  match reads with
    | Inl (sign, more, operand, isRead, isValue, open, signed, noBar, notNumeral, operandReads) => Inl (
      sign,
      more,
      operand,
      isRead,
      isValue,
      open,
      signed,
      noBar,
      notNumeral,
      map { modes, level = LevelUnary } more rest operand operandReads
    )
    | Inr (item, more, isRead, open, notMatch, noBar, route, appReads) =>
      Inr (item, more, isRead, open, notMatch, noBar, route, appMono before after map modes read rest value appReads)

theorem linkMono ∀ (modes: Modes) (takes: Tok → Bool) (before after: List Item → List Item → Expr → Prop)
    (links: List (Item, List Item, Expr))
    (rest: List Item) (map: ∀ (read later: List Item) (value: Expr) => before read later value → after read later value)
    (reads: LinkReads modes takes before links rest):
    LinkReads modes takes after links rest :=
  match links, reads with
    | [], ends => ends
    | [(operator, read, value), ..later], (open, took, holds, more) =>
      (open, took, map read _ value holds, linkMono modes takes before after later rest map more)

theorem chainMono ∀ (modes: Modes) (takes: Tok → Bool) (nested: Expr → List (Word, Expr) → Expr)
    (before after: List Item → List Item → Expr → Prop) (read rest: List Item)
    (value: Expr) (map: ∀ (read later: List Item) (value: Expr) => before read later value → after read later value)
    (reads: ChainReads modes takes nested before before read rest value):
    ChainReads modes takes nested after after read rest value :=
  let (headRead, head, links, isRead, isValue, headReads, linkReads) := reads
  (
    headRead,
    head,
    links,
    isRead,
    isValue,
    map headRead _ head headReads,
    linkMono modes takes before after links rest map linkReads
  )

theorem mulMono ∀ (before after: Goal → List Item → List Item → Expr → Prop)
    (map: ∀ (goal: Goal) (read rest: List Item) (value: Expr) => before goal read rest value
      → after goal read rest value) (modes: Modes) (read rest: List Item) (value: Expr)
    (reads: MulReads before modes read rest value):
    MulReads after modes read rest value :=
  chainMono modes
    (kind => kind == Star || kind == Slash || kind == Percent)
    leftNested
    (UnaryReads before modes)
    (UnaryReads after modes)
    read
    rest
    value
    (unaryMono before after map modes)
    reads

theorem addMono ∀ (before after: Goal → List Item → List Item → Expr → Prop)
    (map: ∀ (goal: Goal) (read rest: List Item) (value: Expr) => before goal read rest value
      → after goal read rest value) (modes: Modes) (read rest: List Item) (value: Expr)
    (reads: AddReads before modes read rest value):
    AddReads after modes read rest value :=
  chainMono modes
    (kind => kind == Plus || kind == Minus)
    leftNested
    (MulReads before modes)
    (MulReads after modes)
    read
    rest
    value
    (mulMono before after map modes)
    reads

theorem appendMono ∀ (before after: Goal → List Item → List Item → Expr → Prop)
    (map: ∀ (goal: Goal) (read rest: List Item) (value: Expr) => before goal read rest value
      → after goal read rest value) (modes: Modes) (read rest: List Item) (value: Expr)
    (reads: AppendReads before modes read rest value):
    AppendReads after modes read rest value :=
  chainMono modes
    (kind => kind == PlusPlus)
    rightNested
    (AddReads before modes)
    (AddReads after modes)
    read
    rest
    value
    (addMono before after map modes)
    reads

theorem pipedMono ∀ (before after: Goal → List Item → List Item → Expr → Prop)
    (map: ∀ (goal: Goal) (read rest: List Item) (value: Expr) => before goal read rest value
      → after goal read rest value) (modes: Modes) (read rest: List Item) (value: Expr)
    (reads: PipedReads before modes read rest value):
    PipedReads after modes read rest value :=
  let (noRange, noPipe, appendReads) := reads
  (noRange, noPipe, appendMono before after map modes read rest value appendReads)

--| `CmpReads` is monotone in `sub`: each side by `pipedMono`.
theorem cmpMono ∀ (before after: Goal → List Item → List Item → Expr → Prop)
    (map: ∀ (goal: Goal) (read rest: List Item) (value: Expr) => before goal read rest value
      → after goal read rest value) (modes: Modes) (read rest: List Item) (value: Expr)
    (reads: CmpReads before modes read rest value):
    CmpReads after modes read rest value :=
  match reads with
    | Inl (pipedReads, noCmp) => Inl (pipedMono before after map modes read rest value pipedReads, noCmp)
    | Inr
        (read1, operator, read2, lhs, second, isRead, isValue, firstReads, open, notIn, compares, noIf, secondReads,
          noChain) => Inr (
      read1,
      operator,
      read2,
      lhs,
      second,
      isRead,
      isValue,
      pipedMono before after map modes read1 _ lhs firstReads,
      open,
      notIn,
      compares,
      noIf,
      pipedMono before after map modes read2 rest second secondReads,
      noChain
    )

theorem logicMono ∀ (before after: Goal → List Item → List Item → Expr → Prop)
    (map: ∀ (goal: Goal) (read rest: List Item) (value: Expr) => before goal read rest value
      → after goal read rest value) (modes: Modes) (links: List (Item, List Item, Expr)) (rest: List Item)
    (reads: LogicReads before modes links rest):
    LogicReads after modes links rest :=
  match links, reads with
    | [], ends => ends
    | [(operator, read, value), ..later], (open, andOr, noExists, noForall, holds, more) => (
      open,
      andOr,
      noExists,
      noForall,
      cmpMono before after map modes read _ value holds,
      logicMono before after map modes later rest more
    )

theorem logicAfterMono ∀ (before after: Goal → List Item → List Item → Expr → Prop)
    (map: ∀ (goal: Goal) (read rest: List Item) (value: Expr) => before goal read rest value
      → after goal read rest value) (modes: Modes) (compared: Expr) (read rest: List Item) (value: Expr)
    (reads: LogicAfterReads before modes compared read rest value):
    LogicAfterReads after modes compared read rest value :=
  match reads with
    | Inl none => Inl none
    | Inr (links, isRead, isValue, ahead, linkReads) =>
      Inr (links, isRead, isValue, ahead, logicMono before after map modes links rest linkReads)

theorem endMono ∀ (before after: Goal → List Item → List Item → Expr → Prop)
    (map: ∀ (goal: Goal) (read rest: List Item) (value: Expr) => before goal read rest value
      → after goal read rest value) (modes: Modes) (logic: Expr) (sequence: Bool) (read rest: List Item) (value: Expr)
    (reads: EndReads before modes logic sequence read rest value):
    EndReads after modes logic sequence read rest value :=
  match reads with
    | Inl none => Inl none
    | Inr (arrow, more, result, isRead, isValue, open, isArrow, (noRow, resultHolds)) => Inr (
      arrow,
      more,
      result,
      isRead,
      isValue,
      open,
      isArrow,
      (noRow, map { modes = allowBraceOn modes (more ++ rest), level = LevelFull } more rest result resultHolds)
    )

theorem operatorMono ∀ (before after: Goal → List Item → List Item → Expr → Prop)
    (map: ∀ (goal: Goal) (read rest: List Item) (value: Expr) => before goal read rest value
      → after goal read rest value) (modes: Modes) (read rest: List Item) (value: Expr)
    (reads: OperatorReads before modes read rest value):
    OperatorReads after modes read rest value :=
  let (read1, read2, read3, compared, logic, isRead, noSection, cmpReads, logicReads, noIff, endReads) := reads
  (
    read1,
    read2,
    read3,
    compared,
    logic,
    isRead,
    noSection,
    cmpMono before after map modes read1 _ compared cmpReads,
    logicAfterMono before after map modes compared read2 _ logic logicReads,
    noIff,
    endMono before after map modes logic _ read3 rest value endReads
  )

theorem inlineMono ∀ (before after: Goal → List Item → List Item → Expr → Prop)
    (map: ∀ (goal: Goal) (read rest: List Item) (value: Expr) => before goal read rest value
      → after goal read rest value) (modes: Modes) (item: Item) (more rest: List Item) (value: Expr)
    (reads: InlineAt before modes item more rest value):
    InlineAt after modes item more rest value :=
  let (open, inline, operatorReads) := reads
  (open, inline, operatorMono before after map modes [item, ..more] rest value operatorReads)

--| `FullReads` is monotone in `sub`.
--|
--| Proof idea: the inline reading by `inlineMono`, and the block's in every line mode.
theorem fullMono ∀ (before after: Goal → List Item → List Item → Expr → Prop)
    (map: ∀ (goal: Goal) (read rest: List Item) (value: Expr) => before goal read rest value
      → after goal read rest value) (modes: Modes) (read rest: List Item) (value: Expr)
    (reads: FullReads before modes read rest value):
    FullReads after modes read rest value :=
  let (item, more, isRead, inlineAt, blockAt) := reads
  (
    item,
    more,
    isRead,
    inlineMono before after map modes item more rest value inlineAt,
    starts =>
      let (right, ends, notOther, lines) := blockAt starts
      (
        right,
        ends,
        notOther,
        kind previous =>
          inlineMono before after map
            (lineModes (blockModes modes item.leaf.token.column True) item.leaf.token.column True previous kind)
            item
            more
            rest
            value
            (lines kind previous)
      )
  )

--| `Layer` is monotone in `sub`: the rung for each level by its own lemma.
theorem layerMono ∀ (before after: Goal → List Item → List Item → Expr → Prop)
    (map: ∀ (goal: Goal) (read rest: List Item) (value: Expr) => before goal read rest value
      → after goal read rest value) (goal: Goal) (read rest: List Item) (value: Expr)
    (layer: Layer before goal read rest value):
    Layer after goal read rest value :=
  match goal, layer with
    | { modes, level }, layer =>
      match level, layer with
        | LevelFull, layer => fullMono before after map modes read rest value layer
        | LevelUnary, layer => unaryMono before after map modes read rest value layer
        | LevelArgument, layer => atomMono before after map modes False read rest value layer
        | other, layer => Void.impossible layer

--| A tree nested `low` deep is nested at most any deeper.
theorem treeNRaise ∀ (low high: Nat) (goal: Goal) (read rest: List Item) (value: Expr)
    (le: low <= high)
    (holds: TreeN low goal read rest value):
    TreeN high goal read rest value :=
  match low, high, holds with
    | Zero, _, never => Void.impossible never
    | Succ below, Succ above, layer =>
      layerMono
        (TreeN below)
        (TreeN above)
        (innerGoal innerRead innerRest innerValue inner =>
          treeNRaise below above innerGoal innerRead innerRest innerValue (arithmetic [le]) inner)
        goal
        read
        rest
        value
        layer

--| A rung whose children are trees nested at most `depth` deep is a tree.
theorem treeOfLayer ∀ (depth: Nat) (goal: Goal) (read rest: List Item) (value: Expr)
    (layer: Layer (TreeN depth) goal read rest value):
    Tree goal read rest value :=
  (Succ depth, layer)

-- One word: the relation holds where `runsExpressionWord` does.

--| A word in the middle of a line, that nothing after it continues, is what `expr` should read, with no calls to
--| `self`.
--|
--| Proof idea: every rung with no links and nothing after, as `runsWordOperator` goes down the ladder; no block
--| starts, the word being in the middle of a line.
theorem fullWord ∀ (sub: Goal → List Item → List Item → Expr → Prop) (modes: Modes) (item: Item) (rest: List Item)
    (inLine: item.leaf.token.lineStart = False)
    (open: modes.stops item = False)
    (word: isWord item.kind = True)
    (plain: (isSome Upper (Some item.kind) && True && isSome LBrace (peekIn modes 0 rest)) = False)
    (noBar: matchesBarOn modes [item, ..rest] = False)
    (inline: InlinePlain modes item [item, ..rest])
    (ends: OperandEnds modes rest):
    FullReads sub modes [item] rest (Atom item.kind item.leaf.word) :=
  let atomValue := Atom item.kind item.leaf.word
  let (_, _, _, _, notDot) := wordKinds item.kind word
  let (notMatch, unsigned) := wordUnsigned item.kind word
  let noSection: isSome Dot (peekIn modes 0 [item, ..rest]) = False :=
    rewrite peekFirst modes item rest open then notDot
  let atomReads: AtomReads sub modes True [item] rest atomValue := (
    item,
    [],
    byComputing,
    open,
    { plain, noCall = ends.noCall, noDot = ends.noDot },
    Inl (byComputing, byComputing, word)
  )
  let unaryReads: UnaryReads sub modes [item] rest atomValue :=
    Inr (item, [], byComputing, open, notMatch, noBar, Inl unsigned, Inl (noSection, atomReads, ends.noArgument))
  let mulReads: MulReads sub modes [item] rest atomValue :=
    ([item], atomValue, [], byComputing, byComputing, unaryReads, ends.noMul)
  let addReads: AddReads sub modes [item] rest atomValue :=
    ([item], atomValue, [], byComputing, byComputing, mulReads, ends.noAdd)
  let appendReads: AppendReads sub modes [item] rest atomValue :=
    ([item], atomValue, [], byComputing, byComputing, addReads, ends.noAppend)
  let operatorReads: OperatorReads sub modes [item] rest atomValue := (
    [item],
    [],
    [],
    atomValue,
    atomValue,
    byComputing,
    noSection,
    Inl ((ends.noRange, ends.noPipe, appendReads), ends.noCmp),
    Inl (byComputing, byComputing, ends.noAndOr),
    ends.noIff,
    Inl (byComputing, byComputing, ends.noEnd)
  )
  let never: startsBlock modes True item = False := rewrite inLine
  (
    item,
    [],
    byComputing,
    (open, inline, operatorReads),
    starts => (Bool.falseNotTrue (Eq.trans never.flipped starts)).impossible
  )

--| The same as a tree: `runsTree` gives `runsExpressionWord` back.
theorem treeWord ∀ (modes: Modes) (item: Item) (rest: List Item)
    (inLine: item.leaf.token.lineStart = False)
    (open: modes.stops item = False)
    (word: isWord item.kind = True)
    (plain: (isSome Upper (Some item.kind) && True && isSome LBrace (peekIn modes 0 rest)) = False)
    (noBar: matchesBarOn modes [item, ..rest] = False)
    (inline: InlinePlain modes item [item, ..rest])
    (ends: OperandEnds modes rest):
    Tree { modes, level = LevelFull } [item] rest (Atom item.kind item.leaf.word) :=
  treeOfLayer 0
    { modes, level = LevelFull }
    [item]
    rest
    (Atom item.kind item.leaf.word)
    (fullWord (TreeN 0) modes item rest inLine open word plain noBar inline ends)

-- Items through `ItemsAt`.

--| A node's leaves between others: its items are read from the place its first leaf is at, and what follows it from
--| the place past it. Each rung's reads are the items of a node's leaves cut this way.
theorem itemsAround ∀ (place: ItemsAt) (before inner after: List Leaf):
    place.items (before ++ inner ++ after)
      = place.items before ++ (place.past before).items inner ++ ((place.past before).past inner).items after :=
  rewrite itemsAppend place before (inner ++ after), itemsAppend (place.past before) inner after

--| A declaration `def name: type := value`'s items: the type's are read from the place after the `:`, the value's
--| from the place after the `:=`; `typeRead` and `valueRead` of `DeclarationTree`.
theorem declarationItems ∀ (keyword name colon colonEq: Leaf) (typeLeaves valueLeaves: List Leaf):
    let typeAt := ItemsAt.start.past [keyword, name, colon]
    let colonEqAt := typeAt.past typeLeaves
    items [keyword, name, colon, ..typeLeaves ++ [colonEq, ..valueLeaves]]
      = ItemsAt.start.items [keyword, name, colon]
        ++ (typeAt.items typeLeaves ++ (colonEqAt.items [colonEq] ++ (colonEqAt.step colonEq).items valueLeaves)) :=
  rewrite itemsStart [keyword, name, colon, ..typeLeaves ++ [colonEq, ..valueLeaves]],
      itemsAppend ItemsAt.start [keyword, name, colon] (typeLeaves ++ [colonEq, ..valueLeaves]),
      itemsAppend (ItemsAt.start.past [keyword, name, colon]) typeLeaves [colonEq, ..valueLeaves]
