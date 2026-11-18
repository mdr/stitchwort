--| Proofs about `bareSettles` (`Syntax/Settle.sw`): rule N on the leaves with
--| bare last commas, with those commas dropped, is rule N on the leaves
--| without them (SW-4006).

namespace Syntax.SettleBareProofs
import Std (Bool, Char, DecEq, Eq, Finite, List, Nat, Option, Text, Void)
import Syntax (..)
import Fmt (..)
import Syntax.SettleProofs (..)

--| Rule 1's walk back from `current` under slice 1's alphabet: how many
--| leaves a trailing comment moves (`stepsBack` without its running count).
def walk1 (current: Leaf) (behind: List Leaf): Nat := match behind with
  | [] => 0
  | [previous, ..earlier] =>
    if !passable current then 0
    else if stopsAt current behind then 0
    else Succ (walk1 previous earlier)

theorem stepsBackShift ∀ (current: Leaf) (behind ahead: List Leaf) (steps: Nat)
    (within: current.kind.within1 = True)
    (behindWithin: behind.all (leaf => leaf.kind.within1) = True):
    stepsBack current behind ahead steps = steps + walk1 current behind :=
  match behind with
    | [] => byComputing
    | [previous, ..earlier] =>
      let skips: skipped current [previous, ..earlier] ahead = passable current :=
        skippedQuiet1 current [previous, ..earlier] ahead within
      let ends: endsWithComment [previous, ..earlier] [current, ..ahead] = endsOn [previous, ..earlier] :=
        endsOnQuiet1 [previous, ..earlier] [current, ..ahead] behindWithin
      let stopEq: stopsAt current [previous, ..earlier]
        = (current.token.lineStart
          && (!current.trivia.leading.isEmpty || endsWithComment [previous, ..earlier] [current, ..ahead])) :=
        rewrite ends
      match pass: passable current with
        | False => rewrite skips
        | True =>
          match stops: current.token.lineStart
            && (!current.trivia.leading.isEmpty || endsWithComment [previous, ..earlier] [current, ..ahead]) with
            | True => rewrite skips, stopEq
            | False =>
              rewrite skips,
                  stopEq,
                  stepsBackShift previous earlier
                    [current, ..ahead]
                    (Succ steps)
                    (Bool.andLeft behindWithin)
                    (Bool.andRight behindWithin) then
                arithmetic

--| Whether rule 1 may move a trailing comment from the leaf, under slice 1's alphabet.
def movable1 (leaf: Leaf): Bool := (leaf.kind == Comma && !leaf.token.lineStart) || leaf.kind.isCloser

--| Rule 1 under slice 1's alphabet: no bars, so nothing bumps and a walk
--| needs no leaves ahead.
def home1 (behind rest: List Leaf): List Leaf := match rest with
  | [] => behind.reverse
  | [leaf, ..after] =>
    match leaf.trivia.trailing with
      | Some comment if movable1 leaf =>
        match walk1 leaf behind with
          | Zero => home1 [leaf, ..behind] after
          | steps => home1 [leaf.withTrailing None, ..trailingAt behind steps comment] after
      | _ => home1 [leaf, ..behind] after

theorem homeFromHome1 ∀ (behind rest: List Leaf)
    (behindWithin: behind.all (leaf => leaf.kind.within1) = True)
    (within: rest.all (leaf => leaf.kind.within1) = True):
    homeFrom behind None rest = home1 behind rest :=
  match rest with
    | [] => byComputing
    | [leaf, ..after] =>
      let leafWithin := Bool.andLeft within
      let afterWithin := Bool.andRight within
      let next := homeFromHome1 [leaf, ..behind] after (rewrite leafWithin then behindWithin) afterWithin
      let same: movable leaf behind after = movable1 leaf := movableQuiet1 leaf behind after leafWithin
      match trailing: leaf.trivia.trailing with
        | None => next
        | Some comment =>
          match fixed: movable leaf behind after with
            | False => rewrite <- same then next
            | True =>
              let shift: stepsBack leaf behind after 0 = walk1 leaf behind :=
                rewrite stepsBackShift leaf behind after 0 leafWithin behindWithin then arithmetic
              rewrite <- same, shift then
                match steps: walk1 leaf behind with
                  | Zero => rewrite barsQuiet1 leaf behind after leafWithin then next
                  | Succ more =>
                    homeFromHome1
                      [leaf.withTrailing None, ..trailingAt behind (Succ more) comment]
                      after
                      (Bool.andIntro leafWithin
                        (withinOfTokens
                          (trailingAt behind (Succ more) comment)
                          behind
                          (trailingAtTokens behind (Succ more) comment)
                          behindWithin))
                      afterWithin

-- Last commas read newest first. A last comma is one directly before a
-- closer, after an item (`hasItem`): in a list newest first, the closer, the
-- comma, then the older leaves.

--| Whether `comma`, just older than a leaf of kind `above`, with `older`
--| behind it, is a last comma.
def lastPair (above: Tok) (comma: Leaf) (older: List Leaf): Bool :=
  comma.token.kind == Comma && above.isCloser && hasItem older

--| What `withBareLastCommas` adds and rule N leaves, `behind` (newest first)
--| after the leaf of kind `above`, without the last commas.
def dr (above: Tok) (behind: List Leaf): List Leaf := match behind with
  | [] => []
  | [comma, ..older] if lastPair above comma older =>
    match older with
      | [] => []
      | [next, ..more] => [next, ..dr next.token.kind more]
  | [leaf, ..rest] => [leaf, ..dr leaf.token.kind rest]

--| The leaves newest first without their last commas.
def dropRev (leaves: List Leaf): List Leaf := match leaves with
  | [] => []
  | [leaf, ..rest] => [leaf, ..dr leaf.token.kind rest]

--| The last commas after `above` hold nothing, and start a line only if
--| the closer does.
def barish (above: Token) (behind: List Leaf): Bool := match behind with
  | [] => True
  | [comma, ..older] if lastPair above.kind comma older =>
    comma.trivia.leading.isEmpty
      && comma.trivia.trailing.isNone
      && (!comma.token.lineStart || above.lineStart)
      && match older with
        | [] => True
        | [next, ..more] => barish next.token more
  | [leaf, ..rest] => barish leaf.token rest

theorem hasItemNonEmpty ∀ (older: List Leaf) (item: hasItem older = True): older.isEmpty = False := match older with
  | [x, ..more] => byComputing

theorem drEmpty ∀ (above: Tok) (behind: List Leaf): (dr above behind).isEmpty = behind.isEmpty := match behind with
  | [] => byComputing
  | [x, ..rest] =>
    match pair: lastPair above x rest with
      | True =>
        match rest with
          | [] => cases
          | [next, ..more] => byComputing
      | False => byComputing

theorem endsCons ∀ (x: Leaf) (rest rest': List Leaf)
    (empty: rest'.isEmpty = rest.isEmpty)
    (same: endsOn rest' = endsOn rest):
    endsOn [x, ..rest'] = endsOn [x, ..rest] :=
  rewrite empty, same

--| What a line's end looks like is unchanged by dropping the last commas.
theorem endsDrop ∀ (above: Token) (behind: List Leaf)
    (ok: barish above behind = True):
    endsOn behind = endsOn (dr above.kind behind) :=
  match behind with
    | [] => byComputing
    | [x, ..rest] =>
      match pair: lastPair above.kind x rest with
        | True =>
          match rest with
            | [] => cases
            | [next, ..more] =>
              let isComma: (x.token.kind == Comma) = True := Bool.andLeft pair
              let olderOk: barish next.token more = True := Bool.andRight (Bool.andRight (Bool.andRight ok))
              let tail: endsOn [next, ..more] = endsOn [next, ..dr next.token.kind more] :=
                (endsCons next more
                  (dr next.token.kind more)
                  (drEmpty next.token.kind more)
                  (endsDrop next.token more olderOk).flipped).flipped
              match trailing: x.trivia.trailing with
                | None => rewrite isComma then tail
                | Some comment => cases
        | False =>
          (endsCons x rest
            (dr x.token.kind rest)
            (drEmpty x.token.kind rest)
            (endsDrop x.token rest ok).flipped).flipped

def isZero (n: Nat): Bool := match n with
  | Zero => True
  | _ => False

theorem drNop ∀ (above: Tok) (x: Leaf) (rest: List Leaf)
    (nop: lastPair above x rest = False):
    dr above [x, ..rest] = [x, ..dr x.token.kind rest] :=
  match pair: lastPair above x rest with | False => byComputing

theorem drPair ∀ (above: Tok) (x next: Leaf) (more: List Leaf)
    (pair: lastPair above x [next, ..more] = True):
    dr above [x, next, ..more] = [next, ..dr next.token.kind more] :=
  match pair2: lastPair above x [next, ..more] with | True => byComputing

--| A walk that stops at once on both sides moves nothing.
theorem walkZero ∀ (current: Leaf) (behind behindA: List Leaf) (comment: Comment)
    (ok: barish current.token behind = True)
    (same: dr current.token.kind behind = behindA)
    (here: walk1 current behind = 0)
    (there: walk1 current behindA = 0):
    isZero (walk1 current behind) = isZero (walk1 current behindA)
      ∧ dr current.token.kind (trailingAt behind (walk1 current behind) comment)
        = trailingAt behindA (walk1 current behindA) comment
      ∧ barish current.token (trailingAt behind (walk1 current behind) comment) = True :=
  rewrite here, there, trailingAtZero behind comment, trailingAtZero behindA comment, same then
    (byComputing, byComputing, ok)

--| Rule 1's walk from `current`, with the last commas in `behind` or not,
--| stops in the same case, moves the comment to the same leaf, and leaves
--| the last commas bare.
--|
--| Proof idea: by induction on `behind`; a walk that passes a last comma and
--| its closer passes two leaves where the one without the comma passes one,
--- and the comma never stops it: if the comma starts its line so does its
--| closer, which would have stopped first.
theorem hasItemTrailingAt ∀ (behind: List Leaf) (steps: Nat) (comment: Comment):
    hasItem (trailingAt behind steps comment) = hasItem behind :=
  match behind, steps with
    | [], _ => byComputing
    | [leaf, ..earlier], Zero => byComputing
    | [leaf, ..earlier], Succ Zero => byComputing
    | [leaf, ..earlier], Succ (Succ more) => byComputing

theorem barishNop ∀ (above: Token) (x: Leaf) (rest: List Leaf)
    (nop: lastPair above.kind x rest = False):
    barish above [x, ..rest] = barish x.token rest :=
  match pair: lastPair above.kind x rest with | False => byComputing

theorem barishPair ∀ (above: Token) (x next: Leaf) (more: List Leaf)
    (pair: lastPair above.kind x [next, ..more] = True)
    (leadEmpty: x.trivia.leading.isEmpty = True)
    (trailNone: x.trivia.trailing.isNone = True)
    (lineOk: (!x.token.lineStart || above.lineStart) = True)
    (olderOk: barish next.token more = True):
    barish above [x, next, ..more] = True :=
  match pair2: lastPair above.kind x [next, ..more] with | True => rewrite leadEmpty, trailNone, lineOk, olderOk

--| A last comma that doesn't start its closer's line, or whose closer's
--| walk didn't stop, doesn't stop the walk that comes through it.
theorem commaNoStop ∀ (current prev next: Leaf) (more: List Leaf)
    (leadEmpty: prev.trivia.leading.isEmpty = True)
    (trailNone: prev.trivia.trailing.isNone = True)
    (isComma: (prev.token.kind == Comma) = True)
    (lineOk: (!prev.token.lineStart || current.token.lineStart) = True)
    (stops: stopsAt current [prev, next, ..more] = False):
    stopsAt prev [next, ..more] = False :=
  match ls: prev.token.lineStart with
    | False => byComputing
    | True =>
      match trailing: prev.trivia.trailing with
        | None => rewrite leadEmpty then rewrite isComma, lineOk at stops then Bool.orFalseRight _ _ stops

theorem walkDrop ∀ (current: Leaf) (behind behindA: List Leaf) (comment: Comment)
    (ok: barish current.token behind = True)
    (same: dr current.token.kind behind = behindA):
    isZero (walk1 current behind) = isZero (walk1 current behindA)
      ∧ dr current.token.kind (trailingAt behind (walk1 current behind) comment)
        = trailingAt behindA (walk1 current behindA) comment
      ∧ barish current.token (trailingAt behind (walk1 current behind) comment) = True :=
  match behind with
    | [] => rewrite <- same then (byComputing, byComputing, byComputing)
    | [prev, ..earlier] =>
      match pair: lastPair current.token.kind prev earlier with
        | False =>
          let eqDr := drNop current.token.kind prev earlier pair
          let stopEq: stopsAt current [prev, ..earlier] = stopsAt current [prev, ..dr prev.token.kind earlier] :=
            rewrite endsDrop current.token [prev, ..earlier] ok, eqDr
          let eqA: behindA = [prev, ..dr prev.token.kind earlier] := Eq.trans same.flipped eqDr
          rewrite eqA then
            match pass: passable current with
              | False =>
                walkZero current
                  [prev, ..earlier]
                  [prev, ..dr prev.token.kind earlier]
                  comment
                  ok
                  eqDr
                  (rewrite pass)
                  (rewrite pass)
              | True =>
                match stops: stopsAt current [prev, ..earlier] with
                  | True => rewrite stopEq.flipped then (byComputing, eqDr, ok)
                  | False =>
                    let (zeq, teq, bar) := walkDrop prev earlier (dr prev.token.kind earlier) comment ok byComputing
                    let w1: walk1 current [prev, ..earlier] = Succ (walk1 prev earlier) := rewrite pass, stops
                    let wA: walk1 current [prev, ..dr prev.token.kind earlier]
                      = Succ (walk1 prev (dr prev.token.kind earlier)) :=
                      rewrite pass, stopEq.flipped
                    rewrite stopEq.flipped then
                      match walked: walk1 prev earlier with
                        | Zero =>
                          match walkedA: walk1 prev (dr prev.token.kind earlier) with
                            | Zero => (
                              byComputing,
                              drNop current.token.kind (prev.withTrailing (Some comment)) earlier pair,
                              (rewrite barishNop current.token (prev.withTrailing (Some comment)) earlier pair then ok)
                            )
                        | Succ more =>
                          let nop2: lastPair current.token.kind prev (trailingAt earlier (Succ more) comment) = False :=
                            rewrite hasItemTrailingAt earlier (Succ more) comment then pair
                          match walkedA: walk1 prev (dr prev.token.kind earlier) with
                            | Succ moreA => (
                              byComputing,
                              (rewrite drNop current.token.kind prev (trailingAt earlier (Succ more) comment) nop2,
                                  teq),
                              (rewrite barishNop current.token prev (trailingAt earlier (Succ more) comment) nop2 then
                                bar)
                            )
        | True =>
          match earlier with
            | [] => cases
            | [next, ..more] =>
              let isComma: (prev.token.kind == Comma) = True := Bool.andLeft pair
              let closer: current.token.kind.isCloser = True := Bool.andLeft (Bool.andRight pair)
              let passes: passable current = True := Bool.orRight closer
              let leadEmpty := Bool.andLeft ok
              let trailNone := Bool.andLeft (Bool.andRight ok)
              let lineOk := Bool.andLeft (Bool.andRight (Bool.andRight ok))
              let olderOk := Bool.andRight (Bool.andRight (Bool.andRight ok))
              let eqDr := drPair current.token.kind prev next more pair
              let eqA: behindA = [next, ..dr next.token.kind more] := Eq.trans same.flipped eqDr
              let stopEq: stopsAt current [prev, next, ..more] = stopsAt current [next, ..dr next.token.kind more] :=
                rewrite endsDrop current.token [prev, next, ..more] ok, eqDr
              rewrite eqA then
                match stops: stopsAt current [prev, next, ..more] with
                  | True => rewrite stopEq.flipped, passes then (byComputing, eqDr, ok)
                  | False =>
                    let (zeq, teq, bar) := walkDrop next more (dr next.token.kind more) comment olderOk byComputing
                    let inner: stopsAt prev [next, ..more] = False :=
                      commaNoStop current prev next more leadEmpty trailNone isComma lineOk stops
                    let prevPasses: passable prev = True := Bool.orLeft isComma
                    let wB: walk1 prev [next, ..more] = Succ (walk1 next more) := rewrite prevPasses, inner
                    rewrite wB, stopEq.flipped, closer, Bool.orTrue then
                      match walked: walk1 next more with
                        | Zero =>
                          match walkedA: walk1 next (dr next.token.kind more) with
                            | Zero => (
                              byComputing,
                              drPair current.token.kind prev (next.withTrailing (Some comment)) more pair,
                              barishPair current.token prev
                                (next.withTrailing (Some comment))
                                more
                                pair
                                leadEmpty
                                trailNone
                                lineOk
                                olderOk
                            )
                        | Succ w =>
                          match walkedA: walk1 next (dr next.token.kind more) with
                            | Succ wA => (
                              byComputing,
                              (rewrite drPair current.token.kind prev next (trailingAt more (Succ w) comment) pair,
                                  teq),
                              barishPair current.token prev next
                                (trailingAt more (Succ w) comment)
                                pair
                                leadEmpty
                                trailNone
                                lineOk
                                bar
                            )
