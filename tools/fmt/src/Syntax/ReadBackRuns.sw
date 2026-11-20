--| Slice 1's read-back, the completeness half per parser function (docs/proposals/self-hosted-fmt-s1-sketch.md §2,
--| ticket 17b): each function, run on the items of what it should read, followed by items its look-aheads stop at,
--| reads exactly those and gives the expected tree. Bottom up: the primitive steps, then atoms.

namespace Syntax.ReadBackRuns
import Std (Bool, DecEq, Eq, List, Nat, Option, Parse, Text)
import Syntax (..)
import Fmt (..)
import Syntax.ReadBackProofs (..)

-- Steps that read nothing or one item.

--| A step that reads nothing and gives `v`, then `j v`: what `j` reads is what the whole reads.
theorem runsLook ∀ (p: () → {Parse t} a) (j: a → {Parse t} b) (v: a) (read rest: List t) (value: b)
    (looks: Parse.Runs p [] (read ++ rest) v)
    (next: Parse.Runs (() => j v) read rest value):
    Parse.Runs (() => j (p())) read rest value :=
  Parse.runsBind p j [] read read rest v value byComputing looks next

--| `runsLook` at the end of the input.
theorem runsLookEnd ∀ (p: () → {Parse t} a) (j: a → {Parse t} b) (v: a) (read: List t) (value: b)
    (looks: Parse.Runs p [] read v)
    (next: Parse.Runs (() => j v) read [] value):
    Parse.Runs (() => j (p())) read [] value :=
  runsLook p j v read [] value (rewrite List.appendNil read then looks) next

--| `runsBind` at the end of the input: `p` reads `first` before `next`, which `j` reads to the end.
theorem runsBindEnd ∀ (p: () → {Parse t} a) (j: a → {Parse t} b) (first next read: List t) (v: a) (value: b)
    (joined: read = first ++ next)
    (runsFirst: Parse.Runs p first next v)
    (runsNext: Parse.Runs (() => j v) next [] value):
    Parse.Runs (() => j (p())) read [] value :=
  Parse.runsBind p j first next read [] v value joined (rewrite List.appendNil next then runsFirst) runsNext

--| A parser's run gives whatever its value equals.
theorem runsSame ∀ (p: () → {Parse t} a) (read rest: List t) (v w: a)
    (same: v = w)
    (runs: Parse.Runs p read rest v):
    Parse.Runs p read rest w :=
  rewrite <- same then runs

theorem runsLeftOn ∀ (rest: List Item): Parse.Runs (() => left()) [] rest rest := state starts honest =>
  Parse.runsFromMark state
    (here => here.rest)
    []
    rest
    rest
    (Parse.runsFromPureEq state _ rest rest starts)
    starts
    honest

theorem runsPeekOn ∀ (modes: Modes) (rest: List Item): Parse.Runs (() => modes.peek) [] rest (peekIn modes 0 rest) :=
  state starts honest =>
    Parse.runsFromMark state
      (here => peekIn modes 0 here.rest)
      []
      rest
      (peekIn modes 0 rest)
      (Parse.runsFromPureEq state _ _ rest (Eq.cong (peekIn modes 0) starts))
      starts
      honest

theorem runsPeekAtOn ∀ (modes: Modes) (ahead: Nat) (rest: List Item):
    Parse.Runs (() => modes.peekAt ahead) [] rest (peekIn modes ahead rest) :=
  state starts honest =>
    Parse.runsFromMark state
      (here => peekIn modes ahead here.rest)
      []
      rest
      (peekIn modes ahead rest)
      (Parse.runsFromPureEq state _ _ rest (Eq.cong (peekIn modes ahead) starts))
      starts
      honest

theorem runsAtOn ∀ (modes: Modes) (wanted: Tok) (rest: List Item):
    Parse.Runs (() => modes.at wanted) [] rest (isSome wanted (peekIn modes 0 rest)) :=
  Parse.runsMap (() => modes.peek) (isSome wanted) [] rest (peekIn modes 0 rest) (runsPeekOn modes rest)

--| `bump` reads the next item and gives its word.
theorem runsBump ∀ (item: Item) (rest: List Item): Parse.Runs (() => bump()) [item] rest item.leaf.word :=
  Parse.runsBind
    (() => Parse.next (item => True)) _
    [item]
    []
    [item]
    rest
    (Some item)
    item.leaf.word
    byComputing
    (Parse.runsNext (item => True) item rest byComputing)
    (Parse.runsPure item.leaf.word rest)

-- Atoms: a word, with nothing after it that `suffixes` reads.

--| A `.` that `suffixesOn` would take for a field access comes next.
def dotAhead (modes: Modes): List Item → Bool
  | [dot, .._] => dot.kind == Dot && !modes.stops dot
  | [] => False

theorem runsSuffixCalledEnd ∀ (target: Expr) (callable paren: Bool) (rest: List Item)
    (noCall: unitCall rest = False):
    Parse.Runs (() => suffixCalled target callable paren) [] rest target :=
  runsLook
    (() => left())
    (items => suffixCalledOn target callable paren items)
    rest
    []
    rest
    target
    (runsLeftOn rest)
    (rewrite noCall then Parse.runsPure target rest)

theorem runsSuffixesOnEnd ∀ (more: Nat) (modes: Modes) (called: Expr) (paren: Bool) (rest: List Item)
    (noDot: dotAhead modes rest = False):
    Parse.Runs (() => suffixesOn more modes called paren rest) [] rest called :=
  match rest, noDot with
    | [dot, field, ..later], noDot =>
      let stops: (dot.kind == Dot && !modes.stops dot && !sectionAt [dot, field, ..later]) = False :=
        Bool.andFalseLeftOf _ _ _ noDot
      rewrite stops then Parse.runsPure called [dot, field, ..later]
    | [dot], noDot =>
      let stops: (dot.kind == Dot && !modes.stops dot) = False := noDot
      rewrite stops then Parse.runsPure called [dot]
    | [], noDot => Parse.runsPure called []

--| `suffixes` where no glued `()` and no field access follows: it reads nothing.
theorem runsSuffixesEnd ∀ (fuel: Nat) (modes: Modes) (target: Expr) (callable paren: Bool) (rest: List Item)
    (noCall: unitCall rest = False)
    (noDot: dotAhead modes rest = False):
    Parse.Runs (() => suffixes fuel modes target callable paren) [] rest target :=
  match fuel with
    | Zero => Parse.runsPure target rest
    | Succ more =>
      Parse.runsBind
        (() => suffixCalled target callable paren)
        (called => suffixesAfterCall more modes called paren)
        []
        []
        []
        rest
        target
        target
        byComputing
        (runsSuffixCalledEnd target callable paren rest noCall)
        (runsLook
          (() => left())
          (items => suffixesOn more modes target paren items)
          rest
          []
          rest
          target
          (runsLeftOn rest)
          (runsSuffixesOnEnd more modes target paren rest noDot))

--| `atomRecord` where no record's fields follow the constructor: it reads nothing.
theorem runsAtomRecordPlain ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (head upper: Bool) (base: Expr)
    (callable: Bool) (rest: List Item)
    (plain: (upper && head && isSome LBrace (peekIn modes 0 rest)) = False):
    Parse.Runs (() => atomRecord self modes head upper base callable) [] rest (base, callable) :=
  match upper, head, plain with
    | False, _, plain => Parse.runsPure (base, callable) rest
    | True, False, plain => Parse.runsPure (base, callable) rest
    | True, True, plain =>
      runsLook
        (() => modes.at LBrace) _
        (isSome LBrace (peekIn modes 0 rest))
        []
        rest
        (base, callable)
        (runsAtOn modes LBrace rest)
        (rewrite plain then Parse.runsPure (base, callable) rest)

--| `atomAfter` of a base that didn't start with `.`, with nothing after it that it reads: it gives the base.
theorem runsAtomAfterPlain ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (head: Bool) (kind: Tok)
    (base: Expr) (rest: List Item)
    (noSection: (kind == Dot) = False)
    (plain: (isSome Upper (Some kind) && head && isSome LBrace (peekIn modes 0 rest)) = False)
    (noCall: unitCall rest = False)
    (noDot: dotAhead modes rest = False):
    Parse.Runs (() => atomAfter self modes head (Some kind) base) [] rest base :=
  Parse.runsBind
    (() =>
      atomRecord self modes head
        (isSome Upper (Some kind))
        base
        (isSome Lower (Some kind) || isSome Upper (Some kind) || isSome Dot (Some kind))) _
    []
    []
    []
    rest
    (base, isSome Lower (Some kind) || isSome Upper (Some kind) || isSome Dot (Some kind))
    base
    byComputing
    (runsAtomRecordPlain self modes head _ base _ rest plain)
    (state starts honest =>
      Parse.runsFromMark state _ [] rest base
        (Parse.runsFromBind state
          (() =>
            suffixes
              (state.at.left + 1)
              modes
              base
              (isSome Lower (Some kind) || isSome Upper (Some kind) || isSome Dot (Some kind))
              (isSome LParen (Some kind))) _
          []
          []
          []
          rest
          base
          base
          byComputing
          (runsSuffixesEnd (state.at.left + 1) modes base _ _ rest noCall noDot)
          (middle _ _ _ => rewrite noSection then Parse.runsPure base rest middle))
        starts
        honest)

--| A word's kind is none of the kinds `atomOf` and `atomAfter` test for before it.
theorem wordKinds ∀ (kind: Tok)
    (word: isWord kind = True):
    (kind == Minus) = False
      ∧ (kind == Bang) = False
      ∧ (kind == LParen) = False
      ∧ (kind == LBracket) = False
      ∧ (kind == Dot) = False :=
  match kind, word with
    | Lower | Upper | Num | Float | Str | CharLit | Underscore | Question | PropU, _ =>
      (byComputing, byComputing, byComputing, byComputing, byComputing)
    | other, word => (Bool.falseNotTrue word).impossible

--| The next item, when it doesn't stop what is being read, is what `peek` sees.
theorem peekFirst ∀ (modes: Modes) (item: Item) (rest: List Item)
    (open: modes.stops item = False):
    peekIn modes 0 [item, ..rest] = Some item.kind :=
  rewrite open

theorem runsWordAtom ∀ (kind: Tok) (item: Item) (rest: List Item):
    Parse.Runs (() => wordAtom kind) [item] rest (Atom kind item.leaf.word) :=
  Parse.runsMap (() => bump()) (word => Atom kind word) [item] rest item.leaf.word (runsBump item rest)

theorem runsAtomOfWord ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (item: Item) (rest: List Item)
    (word: isWord item.kind = True):
    Parse.Runs (() => atomOf self modes item.kind) [item] rest (Atom item.kind item.leaf.word) :=
  let (minus, bang, paren, bracket, _) := wordKinds item.kind word
  rewrite minus, bang, paren, bracket, word then runsWordAtom item.kind item rest

--| `atom` of what `atomOf` reads from its first item, with nothing after it that `atom` would read on.
theorem runsAtomFrom ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (head: Bool) (item: Item)
    (more rest: List Item) (base: Expr)
    (open: modes.stops item = False)
    (based: Parse.Runs (() => atomOf self modes item.kind) [item, ..more] rest base)
    (noSection: (item.kind == Dot) = False)
    (plain: (isSome Upper (Some item.kind) && head && isSome LBrace (peekIn modes 0 rest)) = False)
    (noCall: unitCall rest = False)
    (noDot: dotAhead modes rest = False):
    Parse.Runs (() => atom self modes head) [item, ..more] rest base :=
  runsLook
    (() => modes.peek) _
    (Some item.kind)
    [item, ..more]
    rest _
    (rewrite <- peekFirst modes item (more ++ rest) open then runsPeekOn modes [item, ..more ++ rest])
    (Parse.runsBind
      (() => atomBase self modes) _
      [item, ..more]
      []
      [item, ..more]
      rest
      base
      base
      (List.appendNil [item, ..more]).flipped
      (runsLook
        (() => modes.peek)
        (seen => atomBaseOn self modes seen)
        (Some item.kind)
        [item, ..more]
        rest _
        (rewrite <- peekFirst modes item (more ++ rest) open then runsPeekOn modes [item, ..more ++ rest])
        based)
      (runsAtomAfterPlain self modes head item.kind base rest noSection plain noCall noDot))

-- Prefixes on an argument.

--| `prefixAtom` that negates: the sign, then an argument.
theorem runsPrefixAtom ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (sign: Item)
    (read rest: List Item) (operand: Expr)
    (argument: Parse.Runs (() => self { modes, level = LevelArgument }) read rest operand):
    Parse.Runs (() => prefixAtom self modes True) [sign, ..read] rest (Prefix sign.leaf.word operand) :=
  Parse.runsBind
    (() => bump()) _
    [sign]
    read
    [sign, ..read]
    rest
    sign.leaf.word _
    byComputing
    (runsBump sign (read ++ rest))
    (Parse.runsMap (() => self { modes, level = LevelArgument }) (Prefix sign.leaf.word) read rest operand argument)

--| `-` on an argument that isn't a glued numeral.
theorem runsNegativeAtom ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (sign: Item)
    (read rest: List Item) (operand: Expr)
    (notNumeral: negativeNumeral [sign, ..read ++ rest] = False)
    (negates: argumentMinus [sign, ..read ++ rest] = True)
    (argument: Parse.Runs (() => self { modes, level = LevelArgument }) read rest operand):
    Parse.Runs (() => negativeAtom self modes) [sign, ..read] rest (Prefix sign.leaf.word operand) :=
  runsLook
    (() => left())
    (items => negativeAtomOn self modes items)
    [sign, ..read ++ rest]
    [sign, ..read]
    rest _
    (runsLeftOn [sign, ..read ++ rest])
    (rewrite notNumeral, negates then runsPrefixAtom self modes sign read rest operand argument)

--| `-1`, a glued numeral: read as one atom.
theorem runsNegativeNumber ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (minus number: Item) (rest: List Item)
    (numeral: negativeNumeral [minus, number, ..rest] = True):
    Parse.Runs
      (() => negativeAtom self modes)
      [minus, number]
      rest
      (Prefix minus.leaf.word (Atom number.kind number.leaf.word)) :=
  runsLook
    (() => left())
    (items => negativeAtomOn self modes items)
    [minus, number, ..rest]
    [minus, number]
    rest _
    (runsLeftOn [minus, number, ..rest])
    (rewrite numeral then
      Parse.runsBind
        (() => bump()) _
        [minus]
        [number]
        [minus, number]
        rest
        minus.leaf.word _
        byComputing
        (runsBump minus [number, ..rest])
        (runsLook
          (() => left())
          (items => numberAfter minus.leaf.word items)
          [number, ..rest]
          [number]
          rest _
          (runsLeftOn [number, ..rest])
          (Parse.runsMap
            (() => bump())
            (word => Prefix minus.leaf.word (Atom number.kind word))
            [number]
            rest
            number.leaf.word
            (runsBump number rest))))

--| `!` on an argument.
theorem runsPrefixBang ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (sign: Item)
    (read rest: List Item) (operand: Expr)
    (negates: argumentBang [sign, ..read ++ rest] = True)
    (argument: Parse.Runs (() => self { modes, level = LevelArgument }) read rest operand):
    Parse.Runs (() => prefixBang self modes) [sign, ..read] rest (Prefix sign.leaf.word operand) :=
  runsLook
    (() => left())
    (items => prefixBangOn self modes items)
    [sign, ..read ++ rest]
    [sign, ..read]
    rest _
    (runsLeftOn [sign, ..read ++ rest])
    (rewrite negates then runsPrefixAtom self modes sign read rest operand argument)

-- Brackets.

--| `expect` where the next item is the one wanted: it reads it.
theorem runsExpect ∀ (modes: Modes) (wanted: Tok) (what: Text) (item: Item) (rest: List Item)
    (open: modes.stops item = False)
    (is: (item.kind == wanted) = True):
    Parse.Runs (() => modes.expect wanted what) [item] rest item.leaf.word :=
  runsLook
    (() => modes.peek)
    (seen => modes.expectOn wanted what seen)
    (Some item.kind)
    [item]
    rest _
    (rewrite <- peekFirst modes item rest open then runsPeekOn modes [item, ..rest])
    (rewrite is then runsBump item rest)

--| `(e)`: the opener, an expression in brackets, and its `)`.
theorem runsBracketed ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (open close: Item)
    (read rest: List Item) (first: Expr)
    (inner: Parse.Runs (() => full self modes.inBrackets) read [close, ..rest] first)
    (closes: modes.inBrackets.stops close = False)
    (isClose: close.kind = RParen):
    Parse.Runs
      (() => bracketed self modes)
      ([open, ..read] ++ [close])
      rest
      (Paren open.leaf.word first close.leaf.word) :=
  Parse.runsBind
    (() => bump()) _
    [open]
    (read ++ [close])
    ([open, ..read] ++ [close])
    rest
    open.leaf.word _
    byComputing
    (runsBump open ((read ++ [close]) ++ rest))
    (Parse.runsBind
      (() => full self modes.inBrackets) _
      read
      [close]
      (read ++ [close])
      rest
      first _
      byComputing
      inner
      (runsLook
        (() => modes.inBrackets.peek) _
        (Some close.kind)
        [close]
        rest _
        (rewrite <- peekFirst modes.inBrackets close rest closes then runsPeekOn modes.inBrackets [close, ..rest])
        (rewrite isClose then
          Parse.runsMap
            (() => modes.inBrackets.expect RParen "`)`")
            (Paren open.leaf.word first)
            [close]
            rest
            close.leaf.word
            (runsExpect modes.inBrackets RParen "`)`" close rest closes (rewrite isClose)))))

-- Comma lists.

--| What the rest of a comma list reads: each step's comma, then the items its element reads.
def commaReads: List (Item, List Item, a) → List Item
  | [] => []
  | [(comma, read, _), ..steps] => [comma, ..read] ++ commaReads steps

--| The elements a comma list gives, `current` the newest read and `found` the earlier ones, newest first.
def commaDone (current: a) (found: List a): List (Item, List Item, a) → List a
  | [] => [current, ..found].reverse
  | [(_, _, value), ..steps] => commaDone value [current, ..found] steps

--| The steps of a comma list after its first element: each is a comma the modes don't stop at, `ends` saying go on,
--| and an element that `next` reads; after the last, no comma follows (no trailing comma).
def CommaRuns (modes: Modes) (ends: Nat → {Parse Item} Bool) (next: () → {Parse Item} a) (count: Nat):
    List (Item, List Item, a) → List Item → Prop
  | [], rest => isSome Comma (peekIn modes 0 rest) = False
  | [(comma, read, value), ..steps], rest =>
    modes.stops comma = False
      ∧ comma.kind = Comma
      ∧ Parse.Runs (() => ends count) [] (read ++ commaReads steps ++ rest) False
      ∧ Parse.Runs next read (commaReads steps ++ rest) value
      ∧ CommaRuns modes ends next (count + 1) steps rest

--| `commaListFrom` over a comma list without a trailing comma, with fuel for each comma: it reads the list and gives
--| its elements.
--|
--| Proof idea: by induction on the steps; a step peeks its comma, reads it, asks `ends` (which says go on), reads the
--| element and goes round with the element as the newest.
theorem runsCommaListFrom ∀ (modes: Modes) (ends: Nat → {Parse Item} Bool) (next: () → {Parse Item} a)
    (steps: List (Item, List Item, a)) (rest: List Item) (fuel count: Nat) (current: a) (found: List a)
    (enough: steps.length < fuel)
    (runs: CommaRuns modes ends next count steps rest):
    Parse.Runs (() => commaListFrom fuel modes ends next count current found) (commaReads steps) rest (
      commaDone current found steps,
      False
    ) :=
  match steps, fuel, enough, runs with
    | [], fuel, enough, closing =>
      runsLook
        (() => modes.peek) _
        (peekIn modes 0 rest)
        []
        rest _
        (runsPeekOn modes rest)
        (match fuel, peekIn modes 0 rest, closing with
          | Succ more, Some kind, noComma =>
            let no: (kind == Comma) = False := noComma
            rewrite no then Parse.runsPure ([current, ..found].reverse, False) rest
          | Succ more, None, noComma => Parse.runsPure ([current, ..found].reverse, False) rest)
    | [(comma, read, value), ..later], Succ more, enough, (open, isComma, goesOn, element, others) =>
      let inside :=
        runsCommaListFrom modes ends next later rest more
          (count + 1)
          value
          [current, ..found]
          (arithmetic [enough])
          others
      runsLook
        (() => modes.peek) _
        (Some comma.kind)
        ([comma, ..read] ++ commaReads later)
        rest _
        (rewrite <- peekFirst modes comma ((read ++ commaReads later) ++ rest) open then
          runsPeekOn modes [comma, ..(read ++ commaReads later) ++ rest])
        (rewrite isComma then
          Parse.runsBind
            (() => bump()) _
            [comma]
            (read ++ commaReads later)
            ([comma, ..read] ++ commaReads later)
            rest
            comma.leaf.word _
            byComputing
            (runsBump comma ((read ++ commaReads later) ++ rest))
            (Parse.runsBind
              (() => ends count) _
              []
              (read ++ commaReads later)
              (read ++ commaReads later)
              rest
              False _
              byComputing
              (rewrite <- List.appendAssoc read (commaReads later) rest at goesOn then goesOn)
              (Parse.runsBind next _ read
                (commaReads later)
                (read ++ commaReads later)
                rest
                value _
                byComputing
                element
                inside)))

theorem commaReadsLength ∀ (steps: List (Item, List Item, a)): steps.length <= (commaReads steps).length :=
  match steps with
    | [] => arithmetic
    | [(comma, read, value), ..later] => arithmetic [List.lengthAppend read (commaReads later), commaReadsLength later]

--| The items left after a tuple's first element outnumber the steps after its second: `tupleFuel`'s fuel is enough.
theorem tupleFuelEnough ∀ (comma close: Item) (read2 rest: List Item) (steps: List (Item, List Item, Expr)):
    steps.length < (([comma, ..read2] ++ (commaReads steps ++ [close])) ++ rest).length :=
  let long := commaReadsLength steps
  arithmetic [
    List.lengthAppend [comma, ..read2] (commaReads steps ++ [close]),
    List.lengthAppend ([comma, ..read2] ++ (commaReads steps ++ [close])) rest,
    List.lengthAppend (commaReads steps) [close],
    long
  ]

--| The `)` after a tuple's elements.
theorem runsTupleClose ∀ (inner: Modes) (close: Item) (rest: List Item)
    (closes: inner.stops close = False)
    (isClose: close.kind = RParen):
    Parse.Runs (() => tupleClose inner) [close] rest close.leaf.word :=
  runsLook
    (() => inner.at Colon)
    (annotated => tupleCloseAfter inner annotated)
    False
    [close]
    rest _
    (rewrite <- (rewrite peekFirst inner close rest closes, isClose: isSome Colon (peekIn inner 0 [close, ..rest])
          = False) then
      runsAtOn inner Colon [close, ..rest])
    (runsExpect inner RParen "`)`" close rest closes (rewrite isClose))

--| `(a, b, …)`: a tuple, its first two elements read by `bracketed` and `tupleFuel`, the rest by `commaListFrom`.
--|
--| Proof idea: `bracketed` reads the opener and the first element and, seeing a comma, goes to `tupleFuel`, whose fuel
--| (the items left) `tupleFuelEnough` bounds; then the comma, the second element, `runsCommaListFrom` for the others
--| and `runsTupleClose`.
theorem runsTuple ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (open comma close: Item)
    (read1 read2 rest: List Item) (first second: Expr) (steps: List (Item, List Item, Expr))
    (firstRuns: Parse.Runs
      (() => full self modes.inBrackets)
      read1
      (([comma, ..read2] ++ (commaReads steps ++ [close])) ++ rest)
      first)
    (commaOpen: modes.inBrackets.stops comma = False)
    (isComma: comma.kind = Comma)
    (secondRuns: Parse.Runs (() => full self modes.inBrackets) read2 ((commaReads steps ++ [close]) ++ rest) second)
    (others: CommaRuns modes.inBrackets (tupleEnds modes.inBrackets) (() => full self modes.inBrackets) 2 steps [
      close,
      ..rest
    ])
    (closes: modes.inBrackets.stops close = False)
    (isClose: close.kind = RParen):
    Parse.Runs
      (() => bracketed self modes)
      ([open, ..read1] ++ ([comma, ..read2] ++ (commaReads steps ++ [close])))
      rest
      (Tuple open.leaf.word (commaDone second [first] steps) False close.leaf.word) :=
  let inner := modes.inBrackets
  let after := [comma, ..read2] ++ (commaReads steps ++ [close])
  Parse.runsBind
    (() => bump()) _
    [open]
    (read1 ++ after)
    ([open, ..read1] ++ after)
    rest
    open.leaf.word _
    byComputing
    (runsBump open ((read1 ++ after) ++ rest))
    (Parse.runsBind
      (() => full self inner)
      (first => bracketedFirst self inner open.leaf.word first)
      read1
      after
      (read1 ++ after)
      rest
      first _
      byComputing
      firstRuns
      (runsLook
        (() => inner.peek)
        (seen => bracketedAfter self inner open.leaf.word first seen)
        (Some comma.kind)
        after
        rest _
        (rewrite <- peekFirst inner comma ((read2 ++ (commaReads steps ++ [close])) ++ rest) commaOpen then
          runsPeekOn inner (after ++ rest))
        (rewrite isComma then
          state starts honest =>
            let enough: steps.length < state.at.left :=
              rewrite honest, starts then tupleFuelEnough comma close read2 rest steps
            Parse.runsFromMark state
              (here => tupleFuel self inner open.leaf.word first here.left)
              after
              rest _
              (Parse.runsBind
                (() => bump())
                (comma => tupleSecond self inner open.leaf.word first state.at.left (full self inner))
                [comma]
                (read2 ++ (commaReads steps ++ [close]))
                after
                rest
                comma.leaf.word _
                byComputing
                (runsBump comma ((read2 ++ (commaReads steps ++ [close])) ++ rest))
                (Parse.runsBind
                  (() => full self inner)
                  (second => tupleSecond self inner open.leaf.word first state.at.left second)
                  read2
                  (commaReads steps ++ [close])
                  (read2 ++ (commaReads steps ++ [close]))
                  rest
                  second _
                  byComputing
                  secondRuns
                  (Parse.runsBind
                    (() => commaListFrom state.at.left inner (tupleEnds inner) (() => full self inner) 2 second [first])
                    (pair => tupleEnd inner open.leaf.word pair)
                    (commaReads steps)
                    [close]
                    (commaReads steps ++ [close])
                    rest
                    (commaDone second [first] steps, False) _
                    byComputing
                    (runsCommaListFrom inner
                      (tupleEnds inner)
                      (() => full self inner)
                      steps
                      [close, ..rest]
                      state.at.left
                      2
                      second
                      [first]
                      enough
                      others)
                    (Parse.runsMap
                      (() => tupleClose inner)
                      (Tuple open.leaf.word (commaDone second [first] steps) False)
                      [close]
                      rest
                      close.leaf.word
                      (runsTupleClose inner close rest closes isClose))))
                state)
              starts
              honest)))

--| `tupleEnds` before an element: no `)` comes next, so the list goes on.
theorem runsTupleEndsGo ∀ (inner: Modes) (count: Nat) (items: List Item)
    (noClose: isSome RParen (peekIn inner 0 items) = False):
    Parse.Runs (() => tupleEnds inner count) [] items False :=
  runsLook
    (() => inner.at RParen)
    (closed => closed && count >= 2)
    False
    []
    items
    False
    (rewrite <- noClose then runsAtOn inner RParen items)
    (Parse.runsPure False items)

-- Lists.

--| A list's element that isn't a spread: what `full` reads.
theorem runsListItem ∀ (self: Goal → {Parse Item} Expr) (inner: Modes) (read rest: List Item) (value: Expr)
    (noSpread: isSome DotDot (peekIn inner 0 (read ++ rest)) = False)
    (element: Parse.Runs (() => full self inner) read rest value):
    Parse.Runs (() => listItem self inner) read rest value :=
  runsLook
    (() => inner.at DotDot)
    (spread => listItemAfter self inner spread)
    False
    read
    rest
    value
    (rewrite <- noSpread then runsAtOn inner DotDot (read ++ rest))
    element

--| `listAfter` where the list doesn't close at once: its items.
theorem runsListAfterItems ∀ (self: Goal → {Parse Item} Expr) (inner: Modes) (open: Word) (seen: Option Tok)
    (read rest: List Item) (value: Expr)
    (notEmpty: isSome RBracket seen = False)
    (items: Parse.Runs (() => listItems self inner open) read rest value):
    Parse.Runs (() => listAfter self inner open seen) read rest value :=
  match seen, notEmpty with
    | Some kind, notEmpty =>
      let no: (kind == RBracket) = False := notEmpty
      rewrite no then items
    | None, notEmpty => items

--| `[]`.
theorem runsListEmpty ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (open close: Item) (rest: List Item)
    (closes: modes.inBrackets.stops close = False)
    (isClose: close.kind = RBracket):
    Parse.Runs (() => listExpr self modes) [open, close] rest (ListOf open.leaf.word [] False close.leaf.word) :=
  Parse.runsBind
    (() => bump())
    (open => listTail self modes open)
    [open]
    [close]
    [open, close]
    rest
    open.leaf.word _
    byComputing
    (runsBump open [close, ..rest])
    (runsLook
      (() => modes.inBrackets.peek)
      (seen => listAfter self modes.inBrackets open.leaf.word seen)
      (Some close.kind)
      [close]
      rest _
      (rewrite <- peekFirst modes.inBrackets close rest closes then runsPeekOn modes.inBrackets [close, ..rest])
      (rewrite isClose then
        Parse.runsMap
          (() => bump())
          (ListOf open.leaf.word [] False)
          [close]
          rest
          close.leaf.word
          (runsBump close rest)))

theorem listFuelEnough ∀ (close: Item) (rest: List Item) (steps: List (Item, List Item, Expr)):
    steps.length < ((commaReads steps ++ [close]) ++ rest).length + 1 :=
  let long := commaReadsLength steps
  arithmetic [List.lengthAppend (commaReads steps ++ [close]) rest, List.lengthAppend (commaReads steps) [close], long]

--| `[a, b, …]`: the opener, the first element, the others by `commaListFrom`, and `]`.
--|
--| Proof idea: `listAfter` sees no `]` and goes to `listItems`, which reads the first element and hands `commaList`
--| fuel of the items left and one more, which `listFuelEnough` bounds; `runsCommaListFrom` reads the rest.
theorem runsList ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (open close: Item) (read1 rest: List Item)
    (first: Expr) (steps: List (Item, List Item, Expr))
    (notEmpty: isSome RBracket (peekIn modes.inBrackets 0 ((read1 ++ (commaReads steps ++ [close])) ++ rest)) = False)
    (firstRuns: Parse.Runs (() => listItem self modes.inBrackets) read1 ((commaReads steps ++ [close]) ++ rest) first)
    (others: CommaRuns modes.inBrackets
      (count => modes.inBrackets.at RBracket)
      (() => listItem self modes.inBrackets)
      1
      steps
      [close, ..rest])
    (closes: modes.inBrackets.stops close = False)
    (isClose: close.kind = RBracket):
    Parse.Runs
      (() => listExpr self modes)
      ([open, ..read1] ++ (commaReads steps ++ [close]))
      rest
      (ListOf open.leaf.word (commaDone first [] steps) False close.leaf.word) :=
  let inner := modes.inBrackets
  let after := commaReads steps ++ [close]
  Parse.runsBind
    (() => bump())
    (open => listTail self modes open)
    [open]
    (read1 ++ after)
    ([open, ..read1] ++ after)
    rest
    open.leaf.word _
    byComputing
    (runsBump open ((read1 ++ after) ++ rest))
    (runsLook
      (() => inner.peek)
      (seen => listAfter self inner open.leaf.word seen)
      (peekIn inner 0 ((read1 ++ after) ++ rest))
      (read1 ++ after)
      rest _
      (runsPeekOn inner ((read1 ++ after) ++ rest))
      (runsListAfterItems self inner open.leaf.word _
        (read1 ++ after)
        rest _
        notEmpty
        (Parse.runsBind
          (() => listItem self inner)
          (first => listItemsFrom self inner open.leaf.word first)
          read1
          after
          (read1 ++ after)
          rest
          first _
          byComputing
          firstRuns
          (state starts honest =>
            let enough: steps.length < state.at.left + 1 := rewrite honest, starts then listFuelEnough close rest steps
            Parse.runsFromMark state
              (here =>
                listItemsEnd self inner open.leaf.word
                  (commaList (here.left + 1) inner (count => inner.at RBracket) (() => listItem self inner) first []))
              after
              rest _
              (Parse.runsBind
                (() =>
                  commaListFrom
                    (state.at.left + 1)
                    inner
                    (count => inner.at RBracket)
                    (() => listItem self inner)
                    1
                    first
                    [])
                (pair => listItemsEnd self inner open.leaf.word pair)
                (commaReads steps)
                [close]
                after
                rest
                (commaDone first [] steps, False) _
                byComputing
                (runsCommaListFrom inner
                  (count => inner.at RBracket)
                  (() => listItem self inner)
                  steps
                  [close, ..rest]
                  (state.at.left + 1)
                  1
                  first
                  []
                  enough
                  others)
                (Parse.runsMap
                  (() => inner.expect RBracket "`,` or `]`")
                  (ListOf open.leaf.word (commaDone first [] steps) False)
                  [close]
                  rest
                  close.leaf.word
                  (runsExpect inner RBracket "`,` or `]`" close rest closes (rewrite isClose)))
                state)
              starts
              honest))))

-- Applications.

theorem runsStartsAtom ∀ (modes: Modes) (items: List Item):
    Parse.Runs (() => startsAtom modes) [] items (startsAtomOn modes items) :=
  Parse.runsMap (() => left()) (startsAtomOn modes) [] items items (runsLeftOn items)

--| An argument: not a method section starting a line, and not a constructor's record fields; `self` reads it.
theorem runsArgument ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (read rest: List Item) (value: Expr)
    (noLine: sectionLineAt modes (read ++ rest) = False)
    (noBrace: (isSome Upper (peekIn modes 0 (read ++ rest)) && isSome LBrace (peekIn modes 1 (read ++ rest))) = False)
    (selfRuns: Parse.Runs (() => self { modes, level = LevelArgument }) read rest value):
    Parse.Runs (() => argument self modes) read rest value :=
  runsLook
    (() => left())
    (items => argumentAt self modes items)
    (read ++ rest)
    read
    rest
    value
    (runsLeftOn (read ++ rest))
    (rewrite noLine then
      match upper: isSome Upper (peekIn modes 0 (read ++ rest)) with
        | False =>
          runsLook
            (() => modes.at Upper)
            (upper => argumentBrace self modes (upper && isSome LBrace (modes.peekAt 1)))
            False
            read
            rest
            value
            (rewrite <- upper then runsAtOn modes Upper (read ++ rest))
            selfRuns
        | True =>
          let noBrace1: isSome LBrace (peekIn modes 1 (read ++ rest)) = False := noBrace
          runsLook
            (() => modes.at Upper)
            (upper => argumentBrace self modes (upper && isSome LBrace (modes.peekAt 1)))
            True
            read
            rest
            value
            (rewrite <- upper then runsAtOn modes Upper (read ++ rest))
            (runsLook
              (() => modes.peekAt 1)
              (second => argumentBrace self modes (isSome LBrace second))
              (peekIn modes 1 (read ++ rest))
              read
              rest
              value
              (runsPeekAtOn modes 1 (read ++ rest))
              (rewrite noBrace1 then selfRuns)))

--| A round of `arguments` that reads one.
theorem runsArgumentStepSome ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (read rest: List Item) (value: Expr)
    (starts: startsAtomOn modes (read ++ rest) = True)
    (argumentRuns: Parse.Runs (() => argument self modes) read rest value):
    Parse.Runs (() => argumentStep self modes (startsAtom modes)) read rest (Some value) :=
  runsLook
    (() => startsAtom modes)
    (starts => argumentStep self modes starts)
    True
    read
    rest _
    (rewrite <- starts then runsStartsAtom modes (read ++ rest))
    (Parse.runsMap (() => argument self modes) Some read rest value argumentRuns)

--| The round of `arguments` that ends it.
theorem runsArgumentStepNone ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (rest: List Item)
    (ends: startsAtomOn modes rest = False):
    Parse.Runs (() => argumentStep self modes (startsAtom modes)) [] rest None :=
  runsLook
    (() => startsAtom modes)
    (starts => argumentStep self modes starts)
    False
    []
    rest _
    (rewrite <- ends then runsStartsAtom modes rest)
    (Parse.runsPure None rest)

--| `appAt` of a head with nothing after it that starts an argument.
theorem runsAppAtHead ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (start: Nat) (read rest: List Item) (head: Expr)
    (noSection: isSome Dot (peekIn modes 0 (read ++ rest)) = False)
    (headRuns: Parse.Runs (() => atom self modes True) read rest head)
    (ends: startsAtomOn modes rest = False):
    Parse.Runs (() => appAt self modes start) read rest head :=
  runsLook
    (() => modes.at Dot)
    (dot => appHead self modes (dot && modes.sectionHead != Some start))
    False
    read
    rest
    head
    (rewrite <- noSection then runsAtOn modes Dot (read ++ rest))
    (Parse.runsBind
      (() => atom self modes True)
      (head => appCalls self modes False head)
      read
      []
      read
      rest
      head
      head
      (List.appendNil read).flipped
      headRuns
      (runsLook
        (() => startsAtom modes)
        (applies => appEnd self modes False head applies)
        False
        []
        rest
        head
        (rewrite <- ends then runsStartsAtom modes rest)
        (Parse.runsPure head rest)))

--| `appAt` of a head and its arguments: the first, which `startsAtom` promised, then `arguments`' rounds.
theorem runsAppAtCall ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (start: Nat) (read read1 rest: List Item)
    (head first: Expr) (steps: List (List Item, Expr))
    (noSection: isSome Dot (peekIn modes 0 ((read ++ (read1 ++ Parse.loopReads [] steps)) ++ rest)) = False)
    (headRuns: Parse.Runs (() => atom self modes True) read ((read1 ++ Parse.loopReads [] steps) ++ rest) head)
    (starts: startsAtomOn modes ((read1 ++ Parse.loopReads [] steps) ++ rest) = True)
    (firstRuns: Parse.Runs (() => argument self modes) read1 (Parse.loopReads [] steps ++ rest) first)
    (more: Parse.LoopRuns (() => argumentStep self modes (startsAtom modes)) [] steps rest):
    Parse.Runs
      (() => appAt self modes start)
      (read ++ (read1 ++ Parse.loopReads [] steps))
      rest
      (App head [first, ..Parse.stepValues steps]) :=
  let after := read1 ++ Parse.loopReads [] steps
  runsLook
    (() => modes.at Dot)
    (dot => appHead self modes (dot && modes.sectionHead != Some start))
    False
    (read ++ after)
    rest _
    (rewrite <- noSection then runsAtOn modes Dot ((read ++ after) ++ rest))
    (Parse.runsBind
      (() => atom self modes True)
      (head => appCalls self modes False head)
      read
      after
      (read ++ after)
      rest
      head _
      byComputing
      headRuns
      (runsLook
        (() => startsAtom modes)
        (applies => appEnd self modes False head applies)
        True
        after
        rest _
        (rewrite <- starts then runsStartsAtom modes (after ++ rest))
        (Parse.runsMap
          (() => appliedTo self modes head)
          (sectioned False)
          after
          rest
          (App head [first, ..Parse.stepValues steps])
          (Parse.runsBind
            (() => argument self modes)
            (first =>
              let more := arguments self modes
              App head [first, ..more])
            read1
            (Parse.loopReads [] steps)
            after
            rest
            first _
            byComputing
            firstRuns
            (Parse.runsMap
              (() => arguments self modes)
              (more => App head [first, ..more])
              (Parse.loopReads [] steps)
              rest
              (Parse.stepValues steps)
              (Parse.runsLoop (() => argumentStep self modes (startsAtom modes)) [] steps rest more))))))

-- The operator ladder: links of an operator and an operand.

--| The next item is an operator `takes` accepts, and the modes don't stop at it.
def takesAhead (modes: Modes) (takes: Tok → Bool) (items: List Item): Bool := match peekIn modes 0 items with
  | Some kind => takes kind
  | None => False

--| A round of `operatorLinks` that reads an operator and its operand.
theorem runsOperatorStepSome ∀ (modes: Modes) (takes: Tok → Bool) (operand: () → {Parse Item} Expr) (operator: Item)
    (read rest: List Item) (value: Expr)
    (open: modes.stops operator = False)
    (took: takes operator.kind = True)
    (operandRuns: Parse.Runs operand read rest value):
    Parse.Runs
      (() =>
        match modes.peek with
          | Some kind if takes kind =>
            let operator := bump()
            let value := operand()
            Some (operator, value)
          | _ => None)
      [operator, ..read]
      rest
      (Some (operator.leaf.word, value)) :=
  runsLook
    (() => modes.peek) _
    (Some operator.kind)
    [operator, ..read]
    rest _
    (rewrite <- peekFirst modes operator (read ++ rest) open then runsPeekOn modes [operator, ..read ++ rest])
    (rewrite took then
      Parse.runsBind
        (() => bump()) _
        [operator]
        read
        [operator, ..read]
        rest
        operator.leaf.word _
        byComputing
        (runsBump operator (read ++ rest))
        (Parse.runsMap operand (value => Some (operator.leaf.word, value)) read rest value operandRuns))

--| The round of `operatorLinks` that ends it: no operator it takes comes next.
theorem runsOperatorStepNone ∀ (modes: Modes) (takes: Tok → Bool) (operand: () → {Parse Item} Expr) (rest: List Item)
    (ends: takesAhead modes takes rest = False):
    Parse.Runs
      (() =>
        match modes.peek with
          | Some kind if takes kind =>
            let operator := bump()
            let value := operand()
            Some (operator, value)
          | _ => None)
      []
      rest
      None :=
  runsLook
    (() => modes.peek) _
    (peekIn modes 0 rest)
    []
    rest _
    (runsPeekOn modes rest)
    (match peekIn modes 0 rest, ends with
      | Some kind, ends => rewrite ends then Parse.runsPure None rest
      | None, ends => Parse.runsPure None rest)

--| The links of an operator chain as `operatorLinks`' rounds: each reads its operator and operand.
def linkSteps: List (Item, List Item, Expr) → List (List Item, (Word, Expr))
  | [] => []
  | [(operator, read, value), ..links] => [([operator, ..read], (operator.leaf.word, value)), ..linkSteps links]

--| Each link's operator is one `takes` accepts, not stopped at, and `operand` reads what follows it; after the last, no
--| operator `takes` accepts comes next.
def LinkRuns (modes: Modes) (takes: Tok → Bool) (operand: () → {Parse Item} Expr):
    List (Item, List Item, Expr) → List Item → Prop
  | [], rest => takesAhead modes takes rest = False
  | [(operator, read, value), ..links], rest =>
    modes.stops operator = False
      ∧ takes operator.kind = True
      ∧ Parse.Runs operand read (Parse.loopReads [] (linkSteps links) ++ rest) value
      ∧ LinkRuns modes takes operand links rest

theorem linkLoopRuns ∀ (modes: Modes) (takes: Tok → Bool) (operand: () → {Parse Item} Expr)
    (links: List (Item, List Item, Expr)) (rest: List Item)
    (runs: LinkRuns modes takes operand links rest):
    Parse.LoopRuns
      (() =>
        match modes.peek with
          | Some kind if takes kind =>
            let operator := bump()
            let value := operand()
            Some (operator, value)
          | _ => None)
      []
      (linkSteps links)
      rest :=
  match links, runs with
    | [], ends => runsOperatorStepNone modes takes operand rest ends
    | [(operator, read, value), ..later], (open, took, operandRuns, others) =>
      Both
        (List.consNotNil operator read)
        (Both
          (runsOperatorStepSome modes takes operand operator read
            (Parse.loopReads [] (linkSteps later) ++ rest)
            value
            open
            took
            operandRuns)
          (linkLoopRuns modes takes operand later rest others))

--| `operatorLinks` over links that `LinkRuns` describes: it reads them and gives each operator's word and operand.
theorem runsOperatorLinks ∀ (modes: Modes) (takes: Tok → Bool) (operand: () → {Parse Item} Expr)
    (links: List (Item, List Item, Expr)) (rest: List Item)
    (runs: LinkRuns modes takes operand links rest):
    Parse.Runs
      (() => operatorLinks modes takes operand)
      (Parse.loopReads [] (linkSteps links))
      rest
      (Parse.stepValues (linkSteps links)) :=
  Parse.runsLoop _ [] (linkSteps links) rest (linkLoopRuns modes takes operand links rest runs)

--| A first operand and the links after it, folded to the left (`mulExpr`, `addExpr`).
theorem runsLeftChain ∀ (modes: Modes) (takes: Tok → Bool) (first operand: () → {Parse Item} Expr)
    (read rest: List Item) (head: Expr) (links: List (Item, List Item, Expr))
    (firstRuns: Parse.Runs first read (Parse.loopReads [] (linkSteps links) ++ rest) head)
    (runs: LinkRuns modes takes operand links rest):
    Parse.Runs
      (() => leftNested (first()) (operatorLinks modes takes operand))
      (read ++ Parse.loopReads [] (linkSteps links))
      rest
      (leftNested head (Parse.stepValues (linkSteps links))) :=
  Parse.runsBind first
    (head => leftNested head (operatorLinks modes takes operand))
    read
    (Parse.loopReads [] (linkSteps links))
    (read ++ Parse.loopReads [] (linkSteps links))
    rest
    head _
    byComputing
    firstRuns
    (Parse.runsMap
      (() => operatorLinks modes takes operand)
      (leftNested head)
      (Parse.loopReads [] (linkSteps links))
      rest
      (Parse.stepValues (linkSteps links))
      (runsOperatorLinks modes takes operand links rest runs))

--| The same, folded to the right (`appendExpr`).
theorem runsRightChain ∀ (modes: Modes) (takes: Tok → Bool) (first operand: () → {Parse Item} Expr)
    (read rest: List Item) (head: Expr) (links: List (Item, List Item, Expr))
    (firstRuns: Parse.Runs first read (Parse.loopReads [] (linkSteps links) ++ rest) head)
    (runs: LinkRuns modes takes operand links rest):
    Parse.Runs
      (() => rightNested (first()) (operatorLinks modes takes operand))
      (read ++ Parse.loopReads [] (linkSteps links))
      rest
      (rightNested head (Parse.stepValues (linkSteps links))) :=
  Parse.runsBind first
    (head => rightNested head (operatorLinks modes takes operand))
    read
    (Parse.loopReads [] (linkSteps links))
    (read ++ Parse.loopReads [] (linkSteps links))
    rest
    head _
    byComputing
    firstRuns
    (Parse.runsMap
      (() => operatorLinks modes takes operand)
      (rightNested head)
      (Parse.loopReads [] (linkSteps links))
      rest
      (Parse.stepValues (linkSteps links))
      (runsOperatorLinks modes takes operand links rest runs))

theorem runsMulExpr ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (read rest: List Item)
    (head: Expr) (links: List (Item, List Item, Expr))
    (firstRuns: Parse.Runs (() => unary self modes) read (Parse.loopReads [] (linkSteps links) ++ rest) head)
    (runs: LinkRuns modes
      (kind => kind == Star || kind == Slash || kind == Percent)
      (() => unary self modes)
      links
      rest):
    Parse.Runs
      (() => mulExpr self modes)
      (read ++ Parse.loopReads [] (linkSteps links))
      rest
      (leftNested head (Parse.stepValues (linkSteps links))) :=
  runsLeftChain modes _ (() => unary self modes) (() => unary self modes) read rest head links firstRuns runs

theorem runsAddExpr ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (read rest: List Item)
    (head: Expr) (links: List (Item, List Item, Expr))
    (firstRuns: Parse.Runs (() => mulExpr self modes) read (Parse.loopReads [] (linkSteps links) ++ rest) head)
    (runs: LinkRuns modes (kind => kind == Plus || kind == Minus) (() => mulExpr self modes) links rest):
    Parse.Runs
      (() => addExpr self modes)
      (read ++ Parse.loopReads [] (linkSteps links))
      rest
      (leftNested head (Parse.stepValues (linkSteps links))) :=
  runsLeftChain modes _ (() => mulExpr self modes) (() => mulExpr self modes) read rest head links firstRuns runs

theorem runsAppendExpr ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (read rest: List Item)
    (head: Expr) (links: List (Item, List Item, Expr))
    (firstRuns: Parse.Runs (() => addExpr self modes) read (Parse.loopReads [] (linkSteps links) ++ rest) head)
    (runs: LinkRuns modes (kind => kind == PlusPlus) (() => addExpr self modes) links rest):
    Parse.Runs
      (() => appendExpr self modes)
      (read ++ Parse.loopReads [] (linkSteps links))
      rest
      (rightNested head (Parse.stepValues (linkSteps links))) :=
  runsRightChain modes _ (() => addExpr self modes) (() => addExpr self modes) read rest head links firstRuns runs

-- Prefixes and applications at the unary level.

theorem runsMatchesBar ∀ (modes: Modes) (items: List Item):
    Parse.Runs (() => matchesBarAhead modes) [] items (matchesBarOn modes items) :=
  Parse.runsMap (() => left()) (matchesBarOn modes) [] items items (runsLeftOn items)

--| `app`, from `appAt` at every offset it may start at.
theorem runsApp ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (read rest: List Item) (value: Expr)
    (at: ∀ (start: Nat) => Parse.Runs (() => appAt self modes start) read rest value):
    Parse.Runs (() => app self modes) read rest value :=
  state starts honest =>
    Parse.runsFromMark state
      (here => appAt self modes here.offset)
      read
      rest
      value
      (at state.at.offset state)
      starts
      honest

--| `unary` on what isn't a `match`, a `matches` lambda or a sign: an application.
theorem runsUnaryApp ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (item: Item) (more rest: List Item) (value: Expr)
    (open: modes.stops item = False)
    (notMatch: (item.kind == KwMatch) = False)
    (noBar: matchesBarOn modes [item, ..more ++ rest] = False)
    (unsigned: (item.kind == Minus || item.kind == Bang) = False)
    (appRuns: Parse.Runs (() => app self modes) [item, ..more] rest value):
    Parse.Runs (() => unary self modes) [item, ..more] rest value :=
  let notMinus: (item.kind == Minus) = False := Bool.orFalseLeft _ _ unsigned
  let notBang: (item.kind == Bang) = False := Bool.orFalseRight _ _ unsigned
  runsLook
    (() => modes.peek)
    (seen => unaryOn self modes seen)
    (Some item.kind)
    [item, ..more]
    rest
    value
    (rewrite <- peekFirst modes item (more ++ rest) open then runsPeekOn modes [item, ..more ++ rest])
    (rewrite notMatch then
      runsLook
        (() => matchesBarAhead modes)
        (bar => unaryBar self modes item.kind bar)
        False
        [item, ..more]
        rest
        value
        (runsSame _ [] _ _ False noBar (runsMatchesBar modes [item, ..more ++ rest]))
        (runsLook
          (() => left())
          (items => unaryNext self modes item.kind items)
          [item, ..more ++ rest]
          [item, ..more]
          rest
          value
          (runsLeftOn [item, ..more ++ rest])
          (rewrite notMinus, notBang then appRuns)))

--| `unary` on `-1`, a glued numeral: an application whose head is the numeral.
theorem runsUnaryNumeral ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (item: Item)
    (more rest: List Item) (value: Expr)
    (open: modes.stops item = False)
    (minus: (item.kind == Minus) = True)
    (noBar: matchesBarOn modes [item, ..more ++ rest] = False)
    (numeral: negativeNumeral [item, ..more ++ rest] = True)
    (appRuns: Parse.Runs (() => app self modes) [item, ..more] rest value):
    Parse.Runs (() => unary self modes) [item, ..more] rest value :=
  let notMatch: (item.kind == KwMatch) = False := rewrite DecEq.sound minus
  runsLook
    (() => modes.peek)
    (seen => unaryOn self modes seen)
    (Some item.kind)
    [item, ..more]
    rest
    value
    (rewrite <- peekFirst modes item (more ++ rest) open then runsPeekOn modes [item, ..more ++ rest])
    (rewrite notMatch then
      runsLook
        (() => matchesBarAhead modes)
        (bar => unaryBar self modes item.kind bar)
        False
        [item, ..more]
        rest
        value
        (runsSame _ [] _ _ False noBar (runsMatchesBar modes [item, ..more ++ rest]))
        (runsLook
          (() => left())
          (items => unaryNext self modes item.kind items)
          [item, ..more ++ rest]
          [item, ..more]
          rest
          value
          (runsLeftOn [item, ..more ++ rest])
          (rewrite minus, numeral then appRuns)))

--| `unary` on a sign that isn't a glued numeral's: the sign, then `self` at the unary level.
theorem runsUnaryPrefix ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (sign: Item)
    (read rest: List Item) (operand: Expr)
    (open: modes.stops sign = False)
    (signed: (sign.kind == Minus || sign.kind == Bang) = True)
    (notMatch: (sign.kind == KwMatch) = False)
    (noBar: matchesBarOn modes [sign, ..read ++ rest] = False)
    (notNumeral: (sign.kind == Minus && negativeNumeral [sign, ..read ++ rest]) = False)
    (operandRuns: Parse.Runs (() => self { modes, level = LevelUnary }) read rest operand):
    Parse.Runs (() => unary self modes) [sign, ..read] rest (Prefix sign.leaf.word operand) :=
  runsLook
    (() => modes.peek)
    (seen => unaryOn self modes seen)
    (Some sign.kind)
    [sign, ..read]
    rest _
    (rewrite <- peekFirst modes sign (read ++ rest) open then runsPeekOn modes [sign, ..read ++ rest])
    (rewrite notMatch then
      runsLook
        (() => matchesBarAhead modes)
        (bar => unaryBar self modes sign.kind bar)
        False
        [sign, ..read]
        rest _
        (runsSame _ [] _ _ False noBar (runsMatchesBar modes [sign, ..read ++ rest]))
        (runsLook
          (() => left())
          (items => unaryNext self modes sign.kind items)
          [sign, ..read ++ rest]
          [sign, ..read]
          rest _
          (runsLeftOn [sign, ..read ++ rest])
          (rewrite notNumeral, signed then
            Parse.runsBind
              (() => bump()) _
              [sign]
              read
              [sign, ..read]
              rest
              sign.leaf.word _
              byComputing
              (runsBump sign (read ++ rest))
              (Parse.runsMap
                (() => self { modes, level = LevelUnary })
                (Prefix sign.leaf.word)
                read
                rest
                operand
                operandRuns))))

-- Ranges, pipes and comparisons.

--| A range's operator, which `rangeOn` reads or refuses, comes next.
def rangeAhead (modes: Modes) (items: List Item): Bool := match peekIn modes 0 items with
  | Some kind => kind == DotDot || kind == DotDotLt || kind == DotDotEq
  | None => False

--| `pipedRange` of an `appendExpr` that no range or pipe follows.
theorem runsPipedRange ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (read rest: List Item) (value: Expr)
    (noRange: rangeAhead modes rest = False)
    (noPipe: atPipeOn modes rest = False)
    (appendRuns: Parse.Runs (() => appendExpr self modes) read rest value):
    Parse.Runs (() => pipedRange self modes) read rest value :=
  let rangeRuns: Parse.Runs (() => rangeExpr self modes) read rest value :=
    Parse.runsBind
      (() => appendExpr self modes)
      (low => rangeFrom self modes low)
      read
      []
      read
      rest
      value
      value
      (List.appendNil read).flipped
      appendRuns
      (runsLook
        (() => modes.peek)
        (seen => rangeOn self modes value seen)
        (peekIn modes 0 rest)
        []
        rest
        value
        (runsPeekOn modes rest)
        (match peekIn modes 0 rest, noRange with
          | Some kind, noRange =>
            let notDots: (kind == DotDot) = False := Bool.orFalseLeft _ _ noRange
            let notHigh: (kind == DotDotLt || kind == DotDotEq) = False := Bool.orFalseRight _ _ noRange
            rewrite notDots, notHigh then Parse.runsPure value rest
          | None, noRange => Parse.runsPure value rest))
  runsLook
    (() => headIndent())
    (indent => pipedAt self modes indent)
    (headIndentOn (read ++ rest))
    read
    rest
    value
    (Parse.runsMap (() => left()) headIndentOn [] (read ++ rest) (read ++ rest) (runsLeftOn (read ++ rest)))
    (Parse.runsBind
      (() => rangeExpr self modes)
      (range => pipedAfter self modes (headIndentOn (read ++ rest)) range)
      read
      []
      read
      rest
      value
      value
      (List.appendNil read).flipped
      rangeRuns
      (runsLook
        (() => atPipe modes)
        (pipe => pipedEnd self modes (headIndentOn (read ++ rest)) value pipe)
        False
        []
        rest
        value
        (runsSame _ [] rest _ False noPipe
          (Parse.runsMap (() => left()) (atPipeOn modes) [] rest rest (runsLeftOn rest)))
        (Parse.runsPure value rest)))

--| A comparison's operator, or a membership's, comes next.
def cmpAhead (modes: Modes) (items: List Item): Bool := match peekIn modes 0 items with
  | Some kind => kind == KwIn || kind == NotIn || kind.isComparison
  | None => False

--| `cmpExpr` with no comparison: its operand.
theorem runsCmpPlain ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (read rest: List Item) (value: Expr)
    (pipedRuns: Parse.Runs (() => pipedRange self modes) read rest value)
    (noCmp: cmpAhead modes rest = False):
    Parse.Runs (() => cmpExpr self modes) read rest value :=
  runsLook
    (() => left())
    (items => cmpFirst self modes (items.head.map Item.kind))
    (read ++ rest)
    read
    rest
    value
    (runsLeftOn (read ++ rest))
    (Parse.runsBind
      (() => pipedRange self modes)
      (lhs => cmpPiped self modes ((read ++ rest).head.map Item.kind) lhs)
      read
      []
      read
      rest
      value
      value
      (List.appendNil read).flipped
      pipedRuns
      (runsLook
        (() => modes.peek)
        (seen => cmpOn self modes ((read ++ rest).head.map Item.kind) value seen)
        (peekIn modes 0 rest)
        []
        rest
        value
        (runsPeekOn modes rest)
        (match peekIn modes 0 rest, noCmp with
          | Some kind, noCmp =>
            let others: (kind == NotIn || kind.isComparison) = False := Bool.orFalseRight _ _ noCmp
            let notIn: (kind == KwIn || kind == NotIn) = False :=
              Bool.orFalseIntro _ _ (Bool.orFalseLeft _ _ noCmp) (Bool.orFalseLeft _ _ others)
            let notCmp: kind.isComparison = False := Bool.orFalseRight _ _ others
            rewrite notIn, notCmp then Parse.runsPure value rest
          | None, noCmp => Parse.runsPure value rest)))

--| `cmpExpr` with one comparison, not chained and not followed by `if`.
--|
--| Proof idea: `cmpOn` sees the operator, `cmpCompare` reads it and, with no `if` next, `cmpSecond` reads the second
--| operand; `cmpChain` sees no other comparison after it.
theorem runsCmpCompare ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (read1 read2 rest: List Item)
    (lhs second: Expr) (operator: Item)
    (pipedFirst: Parse.Runs (() => pipedRange self modes) read1 ([operator, ..read2] ++ rest) lhs)
    (open: modes.stops operator = False)
    (notIn: (operator.kind == KwIn || operator.kind == NotIn) = False)
    (compares: operator.kind.isComparison = True)
    (noIf: isSome KwIf (peekIn modes 0 (read2 ++ rest)) = False)
    (pipedSecond: Parse.Runs (() => pipedRange self modes) read2 rest second)
    (noChain: cmpAhead modes rest = False):
    Parse.Runs
      (() => cmpExpr self modes)
      (read1 ++ [operator, ..read2])
      rest
      (Infix InfixBinary lhs operator.leaf.word second) :=
  let whole := (read1 ++ [operator, ..read2]) ++ rest
  runsLook
    (() => left())
    (items => cmpFirst self modes (items.head.map Item.kind))
    whole
    (read1 ++ [operator, ..read2])
    rest _
    (runsLeftOn whole)
    (Parse.runsBind
      (() => pipedRange self modes)
      (lhs => cmpPiped self modes (whole.head.map Item.kind) lhs)
      read1
      [operator, ..read2]
      (read1 ++ [operator, ..read2])
      rest
      lhs _
      byComputing
      pipedFirst
      (runsLook
        (() => modes.peek)
        (seen => cmpOn self modes (whole.head.map Item.kind) lhs seen)
        (Some operator.kind)
        [operator, ..read2]
        rest _
        (rewrite <- peekFirst modes operator (read2 ++ rest) open then runsPeekOn modes [operator, ..read2 ++ rest])
        (rewrite notIn, compares then
          Parse.runsBind
            (() => bump()) _
            [operator]
            read2
            [operator, ..read2]
            rest
            operator.leaf.word _
            byComputing
            (runsBump operator (read2 ++ rest))
            (runsLook
              (() => modes.at KwIf)
              (conditional => cmpAfter self modes lhs operator.kind operator.leaf.word conditional)
              False
              read2
              rest _
              (runsSame _ [] _ _ False noIf (runsAtOn modes KwIf (read2 ++ rest)))
              (Parse.runsBind
                (() => pipedRange self modes)
                (second => cmpSecond self modes lhs operator.kind operator.leaf.word second)
                read2
                []
                read2
                rest
                second _
                (List.appendNil read2).flipped
                pipedSecond
                (runsLook
                  (() => modes.peek)
                  (seen => cmpChain self modes lhs operator.kind operator.leaf.word second seen)
                  (peekIn modes 0 rest)
                  []
                  rest _
                  (runsPeekOn modes rest)
                  (match peekIn modes 0 rest, noChain with
                    | Some next, noChain =>
                      let others: (next == NotIn || next.isComparison) = False := Bool.orFalseRight _ _ noChain
                      let notIn2: (next == KwIn || next == NotIn) = False :=
                        Bool.orFalseIntro _ _ (Bool.orFalseLeft _ _ noChain) (Bool.orFalseLeft _ _ others)
                      let notCmp: next.isComparison = False := Bool.orFalseRight _ _ others
                      rewrite notCmp, notIn2 then Parse.runsPure (Infix InfixBinary lhs operator.leaf.word second) rest
                    | None, noChain => Parse.runsPure (Infix InfixBinary lhs operator.leaf.word second) rest)))))))

-- `&&` and `||`.

--| `quantifierAhead` where neither quantifier comes next.
theorem runsQuantifierNone ∀ (modes: Modes) (items: List Item)
    (noExists: isSome KwExists (peekIn modes 0 items) = False)
    (noForall: isSome KwForall (peekIn modes 0 items) = False):
    Parse.Runs (() => quantifierAhead modes) [] items False :=
  runsLook
    (() => modes.at KwExists)
    (found => found || modes.at KwForall)
    False
    []
    items
    False
    (runsSame _ [] _ _ False noExists (runsAtOn modes KwExists items))
    (runsSame _ [] _ _ False noForall (runsAtOn modes KwForall items))

--| Each link is a `&&` or `||` the modes don't stop at, then a comparison that isn't a quantifier; after the last, no
--| `&&` or `||` comes next.
def LogicRuns (self: Goal → {Parse Item} Expr) (modes: Modes): List (Item, List Item, Expr) → List Item → Prop
  | [], rest => andOrOn modes rest = False
  | [(operator, read, value), ..links], rest =>
    modes.stops operator = False
      ∧ (operator.kind == AndAnd || operator.kind == OrOr) = True
      ∧ isSome KwExists (peekIn modes 0 (read ++ Parse.loopReads [] (linkSteps links) ++ rest)) = False
      ∧ isSome KwForall (peekIn modes 0 (read ++ Parse.loopReads [] (linkSteps links) ++ rest)) = False
      ∧ Parse.Runs (() => cmpExpr self modes) read (Parse.loopReads [] (linkSteps links) ++ rest) value
      ∧ LogicRuns self modes links rest

theorem runsLogicStepSome ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (operator: Item)
    (read rest: List Item) (value: Expr)
    (open: modes.stops operator = False)
    (andOr: (operator.kind == AndAnd || operator.kind == OrOr) = True)
    (noExists: isSome KwExists (peekIn modes 0 (read ++ rest)) = False)
    (noForall: isSome KwForall (peekIn modes 0 (read ++ rest)) = False)
    (cmpRuns: Parse.Runs (() => cmpExpr self modes) read rest value):
    Parse.Runs (() => logicOn self modes modes.peek) [operator, ..read] rest (Some (operator.leaf.word, value)) :=
  runsLook
    (() => modes.peek)
    (seen => logicOn self modes seen)
    (Some operator.kind)
    [operator, ..read]
    rest _
    (rewrite <- peekFirst modes operator (read ++ rest) open then runsPeekOn modes [operator, ..read ++ rest])
    (rewrite andOr then
      Parse.runsBind
        (() => bump())
        (word => logicOperand self modes word (quantifierAhead modes))
        [operator]
        read
        [operator, ..read]
        rest
        operator.leaf.word _
        byComputing
        (runsBump operator (read ++ rest))
        (runsLook
          (() => quantifierAhead modes)
          (quantified => logicOperand self modes operator.leaf.word quantified)
          False
          read
          rest _
          (runsQuantifierNone modes (read ++ rest) noExists noForall)
          (Parse.runsMap
            (() => cmpExpr self modes)
            (operand => Some (operator.leaf.word, operand))
            read
            rest
            value
            cmpRuns)))

theorem runsLogicStepNone ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (rest: List Item)
    (ends: andOrOn modes rest = False):
    Parse.Runs (() => logicOn self modes modes.peek) [] rest None :=
  runsLook
    (() => modes.peek)
    (seen => logicOn self modes seen)
    (peekIn modes 0 rest)
    []
    rest
    None
    (runsPeekOn modes rest)
    (match peekIn modes 0 rest, ends with
      | Some kind, ends => rewrite ends then Parse.runsPure None rest
      | None, ends => Parse.runsPure None rest)

theorem logicLoopRuns ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (links: List (Item, List Item, Expr)) (rest: List Item)
    (runs: LogicRuns self modes links rest):
    Parse.LoopRuns (() => logicOn self modes modes.peek) [] (linkSteps links) rest :=
  match links, runs with
    | [], ends => runsLogicStepNone self modes rest ends
    | [(operator, read, value), ..later], (open, andOr, noExists, noForall, cmpRuns, others) =>
      Both
        (List.consNotNil operator read)
        (Both
          (runsLogicStepSome self modes operator read
            (Parse.loopReads [] (linkSteps later) ++ rest)
            value
            open
            andOr
            noExists
            noForall
            cmpRuns)
          (logicLoopRuns self modes later rest others))

--| `logicAfter` where no `&&` or `||` follows: what was compared.
theorem runsLogicAfterNone ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (compared: Expr) (rest: List Item)
    (ends: andOrOn modes rest = False):
    Parse.Runs (() => logicAfter self modes compared) [] rest compared :=
  runsLook
    (() => andOrAhead modes)
    (ahead => logicOf self modes compared ahead)
    False
    []
    rest
    compared
    (runsSame _ [] _ _ False ends (Parse.runsMap (() => left()) (andOrOn modes) [] rest rest (runsLeftOn rest)))
    (Parse.runsPure compared rest)

--| `logicAfter` where links follow: they are read and grouped by `groupLogic`.
theorem runsLogicAfterChain ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (first: Expr)
    (links: List (Item, List Item, Expr)) (rest: List Item)
    (ahead: andOrOn modes (Parse.loopReads [] (linkSteps links) ++ rest) = True)
    (runs: LogicRuns self modes links rest):
    Parse.Runs
      (() => logicAfter self modes first)
      (Parse.loopReads [] (linkSteps links))
      rest
      (groupLogic ((Parse.stepValues (linkSteps links)).length + 1) first (Parse.stepValues (linkSteps links))) :=
  runsLook
    (() => andOrAhead modes)
    (ahead => logicOf self modes first ahead)
    True
    (Parse.loopReads [] (linkSteps links))
    rest _
    (runsSame _ [] _ _ True ahead
      (Parse.runsMap
        (() => left())
        (andOrOn modes)
        []
        (Parse.loopReads [] (linkSteps links) ++ rest)
        (Parse.loopReads [] (linkSteps links) ++ rest)
        (runsLeftOn (Parse.loopReads [] (linkSteps links) ++ rest))))
    (Parse.runsMap
      (() => logicLinks self modes)
      (links => groupLogic (links.length + 1) first links)
      (Parse.loopReads [] (linkSteps links))
      rest
      (Parse.stepValues (linkSteps links))
      (Parse.runsLoop
        (() => logicOn self modes modes.peek)
        []
        (linkSteps links)
        rest
        (logicLoopRuns self modes links rest runs)))

-- The operators' top: `<->`, `->` and `;`.

--| What `opEnd` reads on after a value: `->`, or `;` where a sequence may be.
def opEndsAhead (modes: Modes) (sequence: Bool) (items: List Item): Bool := match peekIn modes 0 items with
  | Some kind => kind == Arrow || (kind == Semi && sequence)
  | None => False

--| `opStart` after its comparison and logic: no `<->`, then `opEnd`'s look at what follows.
theorem runsOpStartWith ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (start: Nat)
    (read1 read2 read3 rest: List Item) (compared logic value: Expr)
    (noSection: isSome Dot (peekIn modes 0 ((read1 ++ read2 ++ read3) ++ rest)) = False)
    (cmpRuns: Parse.Runs (() => cmpExpr self modes) read1 (read2 ++ read3 ++ rest) compared)
    (logicRuns: Parse.Runs (() => logicAfter self modes compared) read2 (read3 ++ rest) logic)
    (noIff: isSome IffArrow (peekIn modes 0 (read3 ++ rest)) = False)
    (ending: Parse.Runs (() => opEnd self modes logic (sequenceOn modes (read3 ++ rest)) modes.peek) read3 rest value):
    Parse.Runs (() => opStart self modes start) (read1 ++ read2 ++ read3) rest value :=
  runsLook
    (() => modes.at Dot)
    (section => opSection self modes start section)
    False
    (read1 ++ read2 ++ read3)
    rest
    value
    (runsSame _ [] _ _ False noSection (runsAtOn modes Dot ((read1 ++ read2 ++ read3) ++ rest)))
    (Parse.runsBind
      (() => cmpExpr self modes)
      (compared => opCompared self modes False compared)
      read1
      (read2 ++ read3)
      (read1 ++ read2 ++ read3)
      rest
      compared
      value
      byComputing
      (rewrite List.appendAssoc read2 read3 rest then cmpRuns)
      (Parse.runsBind
        (() => logicAfter self modes compared)
        (logic => opLogic self modes False logic)
        read2
        read3
        (read2 ++ read3)
        rest
        logic
        value
        byComputing
        logicRuns
        (runsLook
          (() => modes.at IffArrow)
          (ahead => opIffed self modes False (iffOf self modes logic ahead))
          False
          read3
          rest
          value
          (runsSame _ [] _ _ False noIff (runsAtOn modes IffArrow (read3 ++ rest)))
          (runsLook
            (() => sequenceAhead modes)
            (sequence => opSequence self modes logic sequence)
            (sequenceOn modes (read3 ++ rest))
            read3
            rest
            value
            (Parse.runsMap
              (() => left())
              (sequenceOn modes)
              []
              (read3 ++ rest)
              (read3 ++ rest)
              (runsLeftOn (read3 ++ rest)))
            ending))))

--| `opEnd` with nothing after the value that it reads.
theorem runsOpEndNone ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (value: Expr) (sequence: Bool) (rest: List Item)
    (ends: opEndsAhead modes sequence rest = False):
    Parse.Runs (() => opEnd self modes value sequence modes.peek) [] rest value :=
  runsLook
    (() => modes.peek)
    (seen => opEnd self modes value sequence seen)
    (peekIn modes 0 rest)
    []
    rest
    value
    (runsPeekOn modes rest)
    (match peekIn modes 0 rest, ends with
      | Some kind, ends =>
        let notArrow: (kind == Arrow) = False := Bool.orFalseLeft _ _ ends
        let notSemi: (kind == Semi && sequence) = False := Bool.orFalseRight _ _ ends
        rewrite notArrow, notSemi then Parse.runsPure value rest
      | None, ends => Parse.runsPure value rest)

--| `opEnd` at a `->`: the arrow, then a result type.
theorem runsOpEndArrow ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (value result: Expr) (sequence: Bool)
    (arrow: Item) (read rest: List Item)
    (open: modes.stops arrow = False)
    (isArrow: arrow.kind = Arrow)
    (resultRuns: Parse.Runs (() => resultType self modes) read rest result):
    Parse.Runs
      (() => opEnd self modes value sequence modes.peek)
      [arrow, ..read]
      rest
      (Infix InfixArrow value arrow.leaf.word result) :=
  runsLook
    (() => modes.peek)
    (seen => opEnd self modes value sequence seen)
    (Some arrow.kind)
    [arrow, ..read]
    rest _
    (rewrite <- peekFirst modes arrow (read ++ rest) open then runsPeekOn modes [arrow, ..read ++ rest])
    (rewrite isArrow then
      Parse.runsBind
        (() => bump())
        (word => arrowEnd self modes value word)
        [arrow]
        read
        [arrow, ..read]
        rest
        arrow.leaf.word _
        byComputing
        (runsBump arrow (read ++ rest))
        (Parse.runsMap
          (() => resultType self modes)
          (Infix InfixArrow value arrow.leaf.word)
          read
          rest
          result
          resultRuns))

--| `operatorExpr`, from `opStart` at every offset it may start at.
theorem runsOperatorExpr ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (read rest: List Item) (value: Expr)
    (at: ∀ (start: Nat) => Parse.Runs (() => opStart self modes start) read rest value):
    Parse.Runs (() => operatorExpr self modes) read rest value :=
  state starts honest =>
    Parse.runsFromMark state
      (here => opStart self modes here.offset)
      read
      rest
      value
      (at state.at.offset state)
      starts
      honest

-- An expression on its line: the look-aheads for what isn't an operator expression.

theorem runsLambdaHere ∀ (modes: Modes) (items: List Item)
    (no: lambdaAhead modes (items.length + 1) items = False):
    Parse.Runs (() => lambdaHere modes) [] items False :=
  state starts honest =>
    let none: lambdaAhead modes (state.at.left + 1) state.at.rest = False := rewrite honest, starts then no
    Parse.runsFromMark state
      (here => lambdaAhead modes (here.left + 1) here.rest)
      []
      items
      False
      (Parse.runsFromPureEq state _ False items none)
      starts
      honest

theorem runsLambdaResultHere ∀ (modes: Modes) (items: List Item)
    (no: lambdaResultType modes (items.length + 1) False items = False):
    Parse.Runs (() => lambdaResultHere modes) [] items False :=
  state starts honest =>
    let none: lambdaResultType modes (state.at.left + 1) False state.at.rest = False := rewrite honest, starts then no
    Parse.runsFromMark state
      (here => lambdaResultType modes (here.left + 1) False here.rest)
      []
      items
      False
      (Parse.runsFromPureEq state _ False items none)
      starts
      honest

theorem runsImplicitHere ∀ (modes: Modes) (items: List Item)
    (no: implicitOn (items.length + 1) items (peekIn modes 0 items) = False):
    Parse.Runs (() => implicitHere modes) [] items False :=
  state starts honest =>
    let none: implicitOn (state.at.left + 1) items (peekIn modes 0 items) = False := rewrite honest, starts then no
    Parse.runsFromMark state
      (here => implicitOn (here.left + 1) left() modes.peek)
      []
      items
      False
      (runsLook
        (() => left())
        (later => implicitOn (state.at.left + 1) later modes.peek)
        items
        []
        items
        False
        (runsLeftOn items)
        (runsLook
          (() => modes.peek)
          (seen => implicitOn (state.at.left + 1) items seen)
          (peekIn modes 0 items)
          []
          items
          False
          (runsPeekOn modes items)
          (runsSame _ [] items _ False none (Parse.runsPure _ items)))
        state)
      starts
      honest

theorem runsPiHere ∀ (modes: Modes) (items: List Item)
    (no: piOn items (peekIn modes 0 items) = False):
    Parse.Runs (() => piHere modes) [] items False :=
  runsLook
    (() => left())
    (later => piOn later modes.peek)
    items
    []
    items
    False
    (runsLeftOn items)
    (runsLook
      (() => modes.peek)
      (seen => piOn items seen)
      (peekIn modes 0 items)
      []
      items
      False
      (runsPeekOn modes items)
      (runsSame _ [] items _ False no (Parse.runsPure _ items)))

--| `exprInline` of an operator expression: none of the keywords, lambdas, quantifiers, `if` or binders it looks for
--| first.
theorem runsExprInline ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (item: Item)
    (more rest: List Item) (value: Expr)
    (open: modes.stops item = False)
    (notKeyword: startsKeywordExpr item.kind = False)
    (noLambda: lambdaAhead modes ([item, ..more ++ rest].length + 1) [item, ..more ++ rest] = False)
    (noResult: lambdaResultType modes ([item, ..more ++ rest].length + 1) False [item, ..more ++ rest] = False)
    (notQuantifier: (item.kind == KwExists || item.kind == KwForall) = False)
    (notIf: (item.kind == KwIf) = False)
    (noImplicit: implicitOn ([item, ..more ++ rest].length + 1) [item, ..more ++ rest] (Some item.kind) = False)
    (noPi: piOn [item, ..more ++ rest] (Some item.kind) = False)
    (opRuns: Parse.Runs (() => operatorExpr self modes) [item, ..more] rest value):
    Parse.Runs (() => exprInline self modes) [item, ..more] rest value :=
  let items := [item, ..more ++ rest]
  let peeked: peekIn modes 0 items = Some item.kind := peekFirst modes item (more ++ rest) open
  runsLook
    (() => modes.peek)
    (seen => exprInlineOn self modes seen)
    (Some item.kind)
    [item, ..more]
    rest
    value
    (rewrite <- peeked then runsPeekOn modes items)
    (rewrite notKeyword then
      runsLook
        (() => lambdaHere modes)
        (lambdas => exprLambda self modes lambdas)
        False
        [item, ..more]
        rest
        value
        (runsLambdaHere modes items noLambda)
        (runsLook
          (() => lambdaResultHere modes)
          (refused => exprResult self modes refused)
          False
          [item, ..more]
          rest
          value
          (runsLambdaResultHere modes items noResult)
          (runsLook
            (() => modes.peek)
            (seen => exprBinder self modes seen)
            (Some item.kind)
            [item, ..more]
            rest
            value
            (rewrite <- peeked then runsPeekOn modes items)
            (rewrite notQuantifier, notIf then
              runsLook
                (() => implicitHere modes)
                (implicit => exprImplicit self modes implicit)
                False
                [item, ..more]
                rest
                value
                (runsImplicitHere modes items (rewrite peeked then noImplicit))
                (runsLook
                  (() => piHere modes)
                  (pi => exprPi self modes pi)
                  False
                  [item, ..more]
                  rest
                  value
                  (runsPiHere modes items (rewrite peeked then noPi))
                  opRuns)))))

-- Lines and blocks.

--| A line that is an expression: `statement` reads it with `exprInline`.
theorem runsStatementValue ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (item: Item)
    (more rest: List Item) (value: Expr)
    (open: modes.stops item = False)
    (notOther: startsOtherStatement item.kind = False)
    (inline: Parse.Runs (() => exprInline self modes) [item, ..more] rest value):
    Parse.Runs (() => statement self modes) [item, ..more] rest (ExprStatement value) :=
  runsLook
    (() => modes.peek)
    (seen => statementOn self modes seen)
    (Some item.kind)
    [item, ..more]
    rest _
    (rewrite <- peekFirst modes item (more ++ rest) open then runsPeekOn modes [item, ..more ++ rest])
    (rewrite notOther then Parse.runsMap (() => exprInline self modes) ExprStatement [item, ..more] rest value inline)

--| A column right of the block limit in force, if any.
def rightOfLimit (column: Nat): Option Nat → Bool
  | None => True
  | Some limit => column > limit

--| `exprBlock` at a line start right of the limit: a block at that column.
theorem runsExprBlock ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (item: Item)
    (read rest: List Item) (value: Expr)
    (right: rightOfLimit item.leaf.token.column modes.limit = True)
    (blockRuns: Parse.Runs (() => block self modes item.leaf.token.column True) read rest value):
    Parse.Runs (() => exprBlock self modes item) read rest value :=
  match limit: modes.limit, right with
    | None, right => blockRuns
    | Some limit, right =>
      let past: (item.leaf.token.column > limit) = True := right
      rewrite past then blockRuns

--| `expr` where its first item starts no block: `exprInline`.
theorem runsExprOfInline ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (item: Item)
    (more rest: List Item) (value: Expr)
    (inline: startsBlock modes item = False)
    (inlineRuns: Parse.Runs (() => exprInline self modes) [item, ..more] rest value):
    Parse.Runs (() => expr self modes) [item, ..more] rest value :=
  runsLook
    (() => left())
    (items => exprOn self modes items)
    [item, ..more ++ rest]
    [item, ..more]
    rest
    value
    (runsLeftOn [item, ..more ++ rest])
    (rewrite inline then inlineRuns)

--| `expr` where its first item starts a block: `exprBlock`.
theorem runsExprOfBlock ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (item: Item)
    (more rest: List Item) (value: Expr)
    (starts: startsBlock modes item = True)
    (blockRuns: Parse.Runs (() => exprBlock self modes item) [item, ..more] rest value):
    Parse.Runs (() => expr self modes) [item, ..more] rest value :=
  runsLook
    (() => left())
    (items => exprOn self modes items)
    [item, ..more ++ rest]
    [item, ..more]
    rest
    value
    (runsLeftOn [item, ..more ++ rest])
    (rewrite starts then blockRuns)

--| A block at `column` of one line: `runsBlockOneLine` from a line that `statement` reads in any of its line modes,
--| allowing the line's first item.
theorem runsBlockLine ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (column: Nat)
    (read rest: List Item) (value: Expr)
    (line: ∀ (kind: LineKind) => Parse.Runs
      (() => statement self (lineModes (blockModes modes column True) column True (nextIndex (read ++ rest)) kind))
      read
      rest
      (ExprStatement value))
    (ends: continuesAt column rest = False):
    Parse.Runs (() => block self modes column True) read rest value :=
  state => runsBlockOneLine self modes column True state read rest value (kind middle _ => line kind middle) ends

-- The `def` frame.

theorem runsFixedFrom ∀ (item: Item) (rest: List Item):
    Parse.Runs (() => fixedFrom()) [item] rest item.leaf.word.comments :=
  Parse.runsMap (() => bump()) (word => word.comments) [item] rest item.leaf.word (runsBump item rest)

--| `:=` and the value, at the end of the declaration's items: `Assigned`.
theorem runsDefinitionBody ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (result: Expr) (colonEq: Item)
    (read: List Item) (value: Expr)
    (open: modes.stops colonEq = False)
    (isColonEq: colonEq.kind = ColonEq)
    (valueRuns: Parse.Runs (() => self { modes, level = LevelFull }) read [] value):
    Parse.Runs
      (() => definitionBody self modes result False 0)
      [colonEq, ..read]
      []
      (Assigned colonEq.leaf.word.comments value) :=
  runsLook
    (() => modes.peek)
    (seen => definitionChecked False (definitionBodyOn self modes result 0 seen))
    (Some colonEq.kind)
    [colonEq, ..read]
    [] _
    (rewrite <- peekFirst modes colonEq (read ++ []) open then runsPeekOn modes [colonEq, ..read ++ []])
    (Parse.runsBind
      (() => definitionBodyOn self modes result 0 (Some colonEq.kind))
      (body => definitionChecked False body)
      [colonEq, ..read]
      []
      [colonEq, ..read]
      []
      (Assigned colonEq.leaf.word.comments value) _
      (List.appendNil [colonEq, ..read]).flipped
      (rewrite isColonEq then
        Parse.runsBind
          (() => fixedFrom()) _
          [colonEq]
          read
          [colonEq, ..read]
          []
          colonEq.leaf.word.comments _
          byComputing
          (runsFixedFrom colonEq (read ++ []))
          (Parse.runsBind
            (() => self { modes, level = LevelFull })
            (value => assignedValue modes colonEq.leaf.word.comments value)
            read
            []
            read
            []
            value _
            (List.appendNil read).flipped
            valueRuns
            (runsLook
              (() => modes.at Pipe)
              (arms => assignedEnd colonEq.leaf.word.comments value arms)
              False
              []
              [] _
              (runsAtOn modes Pipe [])
              (Parse.runsPure (Assigned colonEq.leaf.word.comments value) []))))
      (runsLook
        (() => left())
        (items => definitionWhere False (Assigned colonEq.leaf.word.comments value) items)
        []
        []
        [] _
        (runsLeftOn [])
        (Parse.runsPure (Assigned colonEq.leaf.word.comments value) [])))

--| What `modes.at wanted` sees at an item the modes don't stop at.
theorem runsAtFirst ∀ (modes: Modes) (wanted: Tok) (item: Item) (rest: List Item)
    (open: modes.stops item = False):
    Parse.Runs (() => modes.at wanted) [] [item, ..rest] (item.kind == wanted) :=
  runsSame
    (() => modes.at wanted)
    [] _ _ _
    (rewrite peekFirst modes item rest open)
    (runsAtOn modes wanted [item, ..rest])

theorem runsDefKind ∀ (modes: Modes) (keyword: Item) (rest: List Item)
    (open: modes.stops keyword = False)
    (isDef: keyword.kind = KwDef):
    Parse.Runs (() => defKindOf modes) [] [keyword, ..rest] DefPlain :=
  runsSame
    (() => defKindOf modes)
    [] _ _ _
    (rewrite isDef)
    (Parse.runsMap
      (() => modes.peek)
      defKindOn
      []
      [keyword, ..rest]
      (Some keyword.kind)
      (runsSame (() => modes.peek) [] _ _ _ (peekFirst modes keyword rest open) (runsPeekOn modes [keyword, ..rest])))

--| A definition's name, an item of the lower-case kind or the upper-case one.
theorem runsDefinitionName ∀ (modes: Modes) (name: Item) (rest: List Item)
    (open: modes.stops name = False)
    (isLower: name.kind = Lower ∨ name.kind = Upper):
    Parse.Runs (() => definitionName modes) [name] rest name.leaf.word :=
  match isLower with
    | Inl isLower =>
      runsLook
        (() => modes.at Upper)
        (upper => definitionNameAfter modes upper)
        False
        [name]
        rest _
        (runsSame (() => modes.at Upper) [] _ _ _ (rewrite isLower) (runsAtFirst modes Upper name rest open))
        (runsLook
          (() => modes.peek)
          (seen => modes.lowerQualifiedOn "a name" seen)
          (Some name.kind)
          [name]
          rest _
          (runsSame (() => modes.peek) [] _ _ _ (peekFirst modes name rest open) (runsPeekOn modes [name, ..rest]))
          (rewrite isLower then runsBump name rest))
    | Inr isUpper =>
      runsLook
        (() => modes.at Upper)
        (upper => definitionNameAfter modes upper)
        True
        [name]
        rest _
        (runsSame (() => modes.at Upper) [] _ _ _ (rewrite isUpper) (runsAtFirst modes Upper name rest open))
        (runsLook
          (() => modes.peek)
          (seen => modes.upperQualifiedOn "a name" seen)
          (Some name.kind)
          [name]
          rest _
          (runsSame (() => modes.peek) [] _ _ _ (peekFirst modes name rest open) (runsPeekOn modes [name, ..rest]))
          (rewrite isUpper then runsBump name rest))

theorem runsForallNone ∀ (modes: Modes) (kind: DefKind) (next: Item) (rest: List Item)
    (open: modes.stops next = False)
    (notForall: (next.kind == KwForall) = False):
    Parse.Runs (() => forallPart modes kind) [] [next, ..rest] None :=
  runsLook
    (() => modes.at KwForall)
    (found => forallAt modes kind found)
    False
    []
    [next, ..rest]
    None
    (runsSame _ [] _ _ _ notForall (runsAtFirst modes KwForall next rest open))
    (Parse.runsPure None [next, ..rest])

--| No parameters: `headerParams` sees the `:` at once.
theorem runsHeaderParamsNone ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (colon: Item) (rest: List Item)
    (open: modes.stops colon = False)
    (isColon: colon.kind = Colon):
    Parse.Runs (() => headerParams self modes) [] [colon, ..rest] [] :=
  Parse.runsLoop _ [] []
    [colon, ..rest]
    (runsLook
      (() => modes.at Colon)
      (found => if !found then Some (headerGroup self modes GroupParam None) else None)
      True
      []
      [colon, ..rest]
      None
      (runsSame (() => modes.at Colon) [] _ _ _ (rewrite isColon) (runsAtFirst modes Colon colon rest open))
      (Parse.runsPure None [colon, ..rest]))

theorem runsDecreasingNone ∀ (self: Goal → {Parse Item} Expr) (modes headerModes: Modes) (next: Item) (rest: List Item)
    (open: modes.stops next = False)
    (notDecreasing: (next.kind == KwDecreasing) = False):
    Parse.Runs (() => decreasingPart self modes headerModes False) [] [next, ..rest] None :=
  runsLook
    (() => modes.at KwDecreasing)
    (found => decreasingAt self headerModes False found)
    False
    []
    [next, ..rest]
    None
    (runsSame _ [] _ _ _ notDecreasing (runsAtFirst modes KwDecreasing next rest open))
    (Parse.runsPure None [next, ..rest])

theorem runsUnfoldingNone ∀ (modes afterDecreasing: Modes) (next: Item) (rest: List Item)
    (open: afterDecreasing.stops next = False)
    (notUnfolding: (next.kind == KwUnfolding) = False):
    Parse.Runs (() => unfoldingPart modes afterDecreasing False) [] [next, ..rest] None :=
  runsLook
    (() => afterDecreasing.at KwUnfolding)
    (found => unfoldingAt afterDecreasing False found)
    False
    []
    [next, ..rest]
    None
    (runsSame _ [] _ _ _ notUnfolding (runsAtFirst afterDecreasing KwUnfolding next rest open))
    (Parse.runsPure None [next, ..rest])

theorem runsConflictNone ∀ (modes: Modes) (rest: List Item):
    Parse.Runs (() => clauseConflict modes None) [] rest False :=
  runsLook
    (() => modes.at KwDecreasing)
    (found => conflictOn found None)
    (isSome KwDecreasing (peekIn modes 0 rest))
    []
    rest
    False
    (runsAtOn modes KwDecreasing rest)
    (runsSame _ [] _ _ _ (Bool.andFalse _) (Parse.runsPure _ rest))

--| A top-level body at `:=` recovers from errors (`recovers`).
theorem runsBodyModes ∀ (modes: Modes) (colonEq: Item) (rest: List Item)
    (open: modes.stops colonEq = False)
    (isColonEq: colonEq.kind = ColonEq):
    Parse.Runs (() => bodyModesOf modes False None) [] [colonEq, ..rest] { modes | recover = True } :=
  runsLook
    (() => modes.at ColonEq)
    (found => recoverMode modes False (found || modes.at Pipe))
    True
    []
    [colonEq, ..rest] _
    (runsSame (() => modes.at ColonEq) [] _ _ _ (rewrite isColonEq) (runsAtFirst modes ColonEq colonEq rest open))
    (Parse.runsPure { modes | recover = True } [colonEq, ..rest])

--| The header slice 1 has: `def`, a lower-case name, no `∀` or parameters, `:` and the type, no `decreasing` or
--| `unfolding`.
def plainHeader (keyword name colon: Item) (result: Expr): Header := {
  exportKeyword = None,
  opaqueKeyword = None,
  kind = DefPlain,
  keyword = keyword.leaf.word.comments,
  name = name.leaf.word,
  forallKeyword = None,
  params = [],
  colon = colon.leaf.word.comments,
  result,
  decreasingClause = None,
  unfoldingClause = None
}

--| `definitionParts` of a top-level `def name: type := value`, the declaration's items to their end.
--|
--| Proof idea: step by step through `definitionParts`' lets: the kind and the keyword, the name, no `∀` or parameters
--| (the `:` is next), the colon, the type, then at `:=` no `decreasing`, `unfolding` or clash, and a body that recovers.
theorem runsDefinitionParts ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (keyword name colon colonEq: Item)
    (typeRead valueRead: List Item) (result value: Expr)
    (keywordOpen: modes.stops keyword = False)
    (isDef: keyword.kind = KwDef)
    (nameOpen: modes.stops name = False)
    (isLower: name.kind = Lower ∨ name.kind = Upper)
    (colonOpen: modes.stops colon = False)
    (colonSealed: modes.sealed.stops colon = False)
    (isColon: colon.kind = Colon)
    (resultRuns: Parse.Runs (() => resultType self modes) typeRead [colonEq, ..valueRead] result)
    (colonEqOpen: modes.stops colonEq = False)
    (colonEqBody: { modes | recover = True }.stops colonEq = False)
    (isColonEq: colonEq.kind = ColonEq)
    (valueRuns: Parse.Runs (() => self { modes = { modes | recover = True }, level = LevelFull }) valueRead [] value):
    Parse.Runs
      (() => definitionParts self modes None None None)
      [keyword, name, colon, ..typeRead ++ [colonEq, ..valueRead]]
      []
      (plainHeader keyword name colon result, Assigned colonEq.leaf.word.comments value) :=
  let tail := typeRead ++ [colonEq, ..valueRead]
  let atColonEq := [colonEq, ..valueRead]
  let notDecreasing: (colonEq.kind == KwDecreasing) = False := rewrite isColonEq
  let notUnfolding: (colonEq.kind == KwUnfolding) = False := rewrite isColonEq
  runsBindEnd
    (() => defKindOf modes) _
    []
    [keyword, name, colon, ..tail]
    [keyword, name, colon, ..tail]
    DefPlain
    (plainHeader keyword name colon result, Assigned colonEq.leaf.word.comments value)
    byComputing
    (runsDefKind modes keyword [name, colon, ..tail] keywordOpen isDef)
    (runsBindEnd
      (() => fixedFrom()) _
      [keyword]
      [name, colon, ..tail]
      [keyword, name, colon, ..tail] _ _
      byComputing
      (runsFixedFrom keyword [name, colon, ..tail])
      (runsBindEnd
        (() => definitionName modes) _
        [name]
        [colon, ..tail]
        [name, colon, ..tail] _ _
        byComputing
        (runsDefinitionName modes name [colon, ..tail] nameOpen isLower)
        (runsBindEnd
          (() => forallPart modes DefPlain) _
          []
          [colon, ..tail]
          [colon, ..tail]
          None _
          byComputing
          (runsForallNone modes DefPlain colon tail colonOpen (rewrite isColon))
          (runsBindEnd
            (() => headerParams self modes.sealed) _
            []
            [colon, ..tail]
            [colon, ..tail]
            [] _
            byComputing
            (runsHeaderParamsNone self modes.sealed colon tail colonSealed isColon)
            (runsBindEnd
              (() => fixedFrom()) _
              [colon]
              tail
              [colon, ..tail] _ _
              byComputing
              (runsFixedFrom colon tail)
              (runsBindEnd
                (() => resultType self modes) _
                typeRead
                atColonEq
                tail
                result _
                byComputing
                resultRuns
                (runsBindEnd
                  (() => decreasingPart self modes modes False) _
                  []
                  atColonEq
                  atColonEq
                  None _
                  byComputing
                  (runsDecreasingNone self modes modes colonEq valueRead colonEqOpen notDecreasing)
                  (runsBindEnd
                    (() => afterDecreasingOf modes None) _
                    []
                    atColonEq
                    atColonEq
                    modes _
                    byComputing
                    (Parse.runsPure modes atColonEq)
                    (runsBindEnd
                      (() => unfoldingPart modes modes False) _
                      []
                      atColonEq
                      atColonEq
                      None _
                      byComputing
                      (runsUnfoldingNone modes modes colonEq valueRead colonEqOpen notUnfolding)
                      (runsBindEnd
                        (() => afterUnfoldingOf modes None) _
                        []
                        atColonEq
                        atColonEq
                        modes _
                        byComputing
                        (Parse.runsPure modes atColonEq)
                        (runsBindEnd
                          (() => clauseConflict modes None) _
                          []
                          atColonEq
                          atColonEq
                          False _
                          byComputing
                          (runsConflictNone modes atColonEq)
                          (runsBindEnd
                            (() => bodyModesOf modes False None) _
                            []
                            atColonEq
                            atColonEq
                            { modes | recover = True } _
                            byComputing
                            (runsBodyModes modes colonEq valueRead colonEqOpen isColonEq)
                            (Parse.runsMap
                              (() => definitionBody self { modes | recover = True } result False 0)
                              (body => (plainHeader keyword name colon result, body))
                              atColonEq
                              []
                              (Assigned colonEq.leaf.word.comments value)
                              (runsDefinitionBody self
                                { modes | recover = True }
                                result
                                colonEq
                                valueRead
                                value
                                colonEqBody
                                isColonEq
                                valueRuns))))))))))))))

--| A declaration's modes stop at nothing: no limit, guard, `calc` or `rewrite` is in force.
theorem startOpen ∀ (item: Item): Modes.start.stops item = False := byComputing

theorem recoverOpen ∀ (item: Item): { Modes.start | recover = True }.stops item = False := byComputing

theorem sealedOpen ∀ (item: Item): Modes.start.sealed.stops item = False := byComputing

--| No attributes: `attributesOf` sees no `@`.
theorem runsAttributesNone ∀ (modes: Modes) (item: Item) (rest: List Item)
    (open: modes.stops item = False)
    (notAt: (item.kind == At) = False):
    Parse.Runs (() => attributesOf modes) [] [item, ..rest] [] :=
  Parse.runsLoop _ [] []
    [item, ..rest]
    (runsLook
      (() => modes.at At)
      (found => attributeGroupAt modes found)
      False
      []
      [item, ..rest]
      None
      (runsSame (() => modes.at At) [] _ _ _ notAt (runsAtFirst modes At item rest open))
      (Parse.runsPure None [item, ..rest]))

--| The frame (sketch §2, ticket 17): a declaration group `def name: type := value`, from `def` to its last item, is read
--| by `declaration` as the definition of the type and value that `expressionAt` reads.
--|
--| Proof idea: no attributes, nothing to refuse, `declarationKind` and `declarationBody` see `def`, then
--| `runsDefinitionParts`; nothing is left for `declarationEnd`.
theorem runsDeclarationDef ∀ (seen: Seen) (keyword name colon colonEq: Item)
    (typeRead valueRead: List Item) (result value: Expr)
    (isDef: keyword.kind = KwDef)
    (isLower: name.kind = Lower ∨ name.kind = Upper)
    (isColon: colon.kind = Colon)
    (resultRuns: Parse.Runs (() => resultType expressionAt Modes.start) typeRead [colonEq, ..valueRead] result)
    (isColonEq: colonEq.kind = ColonEq)
    (valueRuns: Parse.Runs
      (() => expressionAt { modes = { Modes.start | recover = True }, level = LevelFull })
      valueRead
      []
      value):
    Parse.Runs
      (() => declaration seen)
      [keyword, name, colon, ..typeRead ++ [colonEq, ..valueRead]]
      []
      (Definition [] (plainHeader keyword name colon result) (Assigned colonEq.leaf.word.comments value)) :=
  let modes := Modes.start
  let whole := [keyword, name, colon, ..typeRead ++ [colonEq, ..valueRead]]
  let decl := Definition [] (plainHeader keyword name colon result) (Assigned colonEq.leaf.word.comments value)
  let notAt: (keyword.kind == At) = False := rewrite isDef
  let notNamespace: (keyword.kind == KwNamespace) = False := rewrite isDef
  let notImport: (keyword.kind == KwImport) = False := rewrite isDef
  let peeked: Parse.Runs (() => modes.peek) [] whole (Some keyword.kind) :=
    runsSame
      (() => modes.peek)
      [] _ _ _
      (peekFirst modes keyword [name, colon, ..typeRead ++ [colonEq, ..valueRead]] (startOpen keyword))
      (runsPeekOn modes whole)
  runsBindEnd
    (() => attributesOf modes)
    (attributes => declarationAttributes seen modes attributes)
    []
    whole
    whole
    []
    decl
    byComputing
    (runsAttributesNone modes keyword _ (startOpen keyword) notAt)
    (runsLookEnd
      (() => modes.peek)
      (next => declarationRefusal seen modes [] next)
      (Some keyword.kind)
      whole
      decl
      peeked
      (runsLookEnd
        (() => modes.peek)
        (next => declarationFinish modes (declarationKind seen modes [] next))
        (Some keyword.kind)
        whole
        decl
        peeked
        (rewrite notNamespace, notImport then
          runsBindEnd
            (() => declarationBody modes [])
            (found => declarationFinish modes found)
            whole
            []
            whole
            decl
            decl
            (List.appendNil whole).flipped
            (runsLookEnd
              (() => modes.peek)
              (next => declarationBodyOn modes [] next)
              (Some keyword.kind)
              whole
              decl
              peeked
              (rewrite isDef then
                Parse.runsMap
                  (() => definitionParts expressionAt modes None None None)
                  (definitionOf [])
                  whole
                  []
                  (plainHeader keyword name colon result, Assigned colonEq.leaf.word.comments value)
                  (runsDefinitionParts expressionAt modes keyword name colon colonEq typeRead valueRead result value
                    (startOpen keyword)
                    isDef
                    (startOpen name)
                    isLower
                    (startOpen colon)
                    (sealedOpen colon)
                    isColon
                    resultRuns
                    (startOpen colonEq)
                    (recoverOpen colonEq)
                    isColonEq
                    valueRuns)))
            (runsLook
              (() => left())
              (items => declarationEnd modes decl items)
              []
              []
              []
              decl
              (runsLeftOn [])
              (Parse.runsPure decl [])))))

--| A group read whole: `parseGroups`' `Parse.run` of it gives the definition.
theorem declarationRuns ∀ (seen: Seen) (keyword name colon colonEq: Item)
    (typeRead valueRead: List Item) (result value: Expr)
    (isDef: keyword.kind = KwDef)
    (isLower: name.kind = Lower ∨ name.kind = Upper)
    (isColon: colon.kind = Colon)
    (resultRuns: Parse.Runs (() => resultType expressionAt Modes.start) typeRead [colonEq, ..valueRead] result)
    (isColonEq: colonEq.kind = ColonEq)
    (valueRuns: Parse.Runs
      (() => expressionAt { modes = { Modes.start | recover = True }, level = LevelFull })
      valueRead
      []
      value):
    Parse.run [keyword, name, colon, ..typeRead ++ [colonEq, ..valueRead]] (() =>
      let decl := declaration seen
      decl)
      = Ok (Definition [] (plainHeader keyword name colon result) (Assigned colonEq.leaf.word.comments value)) :=
  Parse.runsRun
    (() =>
      let decl := declaration seen
      decl)
    [keyword, name, colon, ..typeRead ++ [colonEq, ..valueRead]] _
    (Parse.runsMap
      (() => declaration seen)
      (decl => decl)
      [keyword, name, colon, ..typeRead ++ [colonEq, ..valueRead]]
      [] _
      (runsDeclarationDef seen keyword name colon colonEq typeRead valueRead result value isDef isLower isColon
          resultRuns isColonEq valueRuns))

-- What ends an operand, at every level of the ladder.

--| What follows an operand, read at every level of the ladder, ends it: no call, field, argument, operator, range,
--| pipe, comparison, `&&` or `||`, `<->`, `->` or `;`.
type OperandEnds (modes: Modes) (rest: List Item): Prop = {
  noCall: unitCall rest = False,
  noDot: dotAhead modes rest = False,
  noArgument: startsAtomOn modes rest = False,
  noMul: takesAhead modes (kind => kind == Star || kind == Slash || kind == Percent) rest = False,
  noAdd: takesAhead modes (kind => kind == Plus || kind == Minus) rest = False,
  noAppend: takesAhead modes (kind => kind == PlusPlus) rest = False,
  noRange: rangeAhead modes rest = False,
  noPipe: atPipeOn modes rest = False,
  noCmp: cmpAhead modes rest = False,
  noAndOr: andOrOn modes rest = False,
  noIff: isSome IffArrow (peekIn modes 0 rest) = False,
  noEnd: opEndsAhead modes (sequenceOn modes rest) rest = False
}

--| A result type with no ability row: `full` in the modes `allowBrace` gives.
theorem runsResultPlain ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (read rest: List Item) (value: Expr)
    (noRow: rowOn (isSome LBrace (peekIn (allowBraceOn modes (read ++ rest)) 0 (read ++ rest))) (read ++ rest) = False)
    (fullRuns: Parse.Runs
      (() => self { modes = allowBraceOn modes (read ++ rest), level = LevelFull })
      read
      rest
      value):
    Parse.Runs (() => resultType self modes) read rest value :=
  let allowed := allowBraceOn modes (read ++ rest)
  runsLook
    (() => allowBrace modes)
    (allowed => resultAllowed self allowed)
    allowed
    read
    rest
    value
    (Parse.runsMap (() => left()) (allowBraceOn modes) [] (read ++ rest) (read ++ rest) (runsLeftOn (read ++ rest)))
    (runsLook
      (() => rowAhead allowed)
      (row => resultRow self allowed row)
      False
      read
      rest
      value
      (runsSame
        (() => rowAhead allowed)
        [] _ _
        False
        noRow
        (runsLook
          (() => allowed.at LBrace)
          (atBrace => rowOn atBrace left()) _
          []
          (read ++ rest) _
          (runsAtOn allowed LBrace (read ++ rest))
          (Parse.runsMap
            (() => left())
            (rowOn (isSome LBrace (peekIn allowed 0 (read ++ rest))))
            []
            (read ++ rest)
            (read ++ rest)
            (runsLeftOn (read ++ rest)))))
      fullRuns)

--| What `exprInline` looks for before an operator expression, none of it there.
type InlinePlain (modes: Modes) (item: Item) (items: List Item): Prop = {
  notKeyword: startsKeywordExpr item.kind = False,
  noLambda: lambdaAhead modes (items.length + 1) items = False,
  noResult: lambdaResultType modes (items.length + 1) False items = False,
  notQuantifier: (item.kind == KwExists || item.kind == KwForall) = False,
  notIf: (item.kind == KwIf) = False,
  noImplicit: implicitOn (items.length + 1) items (Some item.kind) = False,
  noPi: piOn items (Some item.kind) = False
}
