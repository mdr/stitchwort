--| Comment placement on the leaves with marked last commas (`withMarkedLastCommas`: bare,
--| each closer after one starting its line if the comma did), with those
--| commas dropped, is comment placement on the leaves without them (`markedSettles`,
--| SW-4006). `Syntax.SettleMarkProofs` carries it to the leaves the
--| formatter parses (`bareSettles`).

namespace Syntax.SettleBareProofs
import Std (Bool, Char, DecEq, Eq, Finite, List, Nat, Option, Text, Void)
import Syntax (..)
import Fmt (..)
import Syntax.SettleProofs (..)
import Syntax.SharedFacts (commaNotCloser)

--| The back-walk back from `current` under slice 1's alphabet: how many
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
    stepsBack False current behind ahead steps = steps + walk1 current behind :=
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

--| Whether the back-walk may move a trailing comment from the leaf, under slice 1's alphabet.
def movable1 (leaf: Leaf): Bool := (leaf.kind == Comma && !leaf.token.lineStart) || leaf.kind.isCloser

--| The back-walk under slice 1's alphabet, newest first: no bars, so nothing bumps
--| and a walk needs no leaves ahead.
def home1 (behind rest: List Leaf): List Leaf := match rest with
  | [] => behind
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
    homeFrom False behind None rest = (home1 behind rest).reverse :=
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
              let shift: stepsBack False leaf behind after 0 = walk1 leaf behind :=
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

--| What `withMarkedLastCommas` adds and comment placement leaves, `behind` (newest first)
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

--| The back-walk from `current`, with the last commas in `behind` or not,
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
    | [_, .._], Zero | Succ Zero | Succ (Succ _) => byComputing

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

-- The same last commas read forwards, with the leaves before them
-- (`behind`, newest first) for what comes before a comma.

--| The leaves without their last commas, `behind` the leaves before.
def dropF (behind rest: List Leaf): List Leaf := match rest with
  | [] => []
  | [comma, closer, ..after] if lastPair closer.token.kind comma behind =>
    [closer, ..dropF [closer, comma, ..behind] after]
  | [leaf, ..after] => [leaf, ..dropF [leaf, ..behind] after]

--| `barish`, read forwards.
def barishF (behind rest: List Leaf): Bool := match rest with
  | [] => True
  | [comma, closer, ..after] if lastPair closer.token.kind comma behind =>
    comma.trivia.leading.isEmpty
      && comma.trivia.trailing.isNone
      && (!comma.token.lineStart || closer.token.lineStart)
      && barishF [closer, comma, ..behind] after
  | [leaf, ..after] => barishF [leaf, ..behind] after

--| `barish` of the newest leaf and the leaves before it.
def barishTop (behind: List Leaf): Bool := match behind with
  | [] => True
  | [leaf, ..older] => barish leaf.token older

--| No last comma straddles the leaves done and the leaves to come: the
--| newest leaf done isn't a comma that the next leaf closes.
def gapOk (behind rest: List Leaf): Bool := match behind, rest with
  | [comma, ..older], [next, .._] => !lastPair next.token.kind comma older
  | _, _ => True

theorem drNopTop ∀ (leaf: Leaf) (behind: List Leaf)
    (gap: gapOk behind [leaf, ..[]] = True):
    dr leaf.token.kind behind = dropRev behind :=
  match behind with
    | [] => byComputing
    | [x, ..older] =>
      match pair: lastPair leaf.token.kind x older with
        | False => byComputing

theorem drPairTop ∀ (closer comma: Leaf) (behind: List Leaf)
    (pair: lastPair closer.token.kind comma behind = True):
    dr closer.token.kind [comma, ..behind] = dropRev behind :=
  match behind with
    | [] => cases
    | [next, ..more] => drPair closer.token.kind comma next more pair

theorem closerNotComma ∀ (kind: Tok) (closer: kind.isCloser = True): (kind == Comma) = False := cases

--| What the forward reading does with the leaves before it depends only on
--| whether the newest one is an item.
theorem dropFItem ∀ (b b' rest: List Leaf) (same: hasItem b = hasItem b'): dropF b rest = dropF b' rest :=
  match rest with
    | [] => byComputing
    | [leaf, ..after] =>
      match after with
        | [] => byComputing
        | [closer, ..after2] =>
          match pair: lastPair closer.token.kind leaf b with
            | True =>
              let pair': lastPair closer.token.kind leaf b' = True := rewrite <- same then pair
              rewrite pair', dropFItem [closer, leaf, ..b] [closer, leaf, ..b'] after2 byComputing
            | False =>
              let pair': lastPair closer.token.kind leaf b' = False := rewrite <- same then pair
              rewrite pair', dropFItem [leaf, ..b] [leaf, ..b'] [closer, ..after2] byComputing

theorem barishFItem ∀ (b b' rest: List Leaf) (same: hasItem b = hasItem b'): barishF b rest = barishF b' rest :=
  match rest with
    | [] => byComputing
    | [leaf, ..after] =>
      match after with
        | [] => byComputing
        | [closer, ..after2] =>
          match pair: lastPair closer.token.kind leaf b with
            | True =>
              let pair': lastPair closer.token.kind leaf b' = True := rewrite <- same then pair
              rewrite pair', barishFItem [closer, leaf, ..b] [closer, leaf, ..b'] after2 byComputing
            | False =>
              let pair': lastPair closer.token.kind leaf b' = False := rewrite <- same then pair
              rewrite pair', barishFItem [leaf, ..b] [leaf, ..b'] [closer, ..after2] byComputing

--| Whether `leaf`, with `after` the leaves to come and `behind` those done,
--| is a last comma.
def fwdPair (behind: List Leaf) (leaf: Leaf) (after: List Leaf): Bool := match after with
  | [closer, .._] => lastPair closer.token.kind leaf behind
  | [] => False

theorem dropFNop ∀ (leaf: Leaf) (behind after: List Leaf)
    (nop: fwdPair behind leaf after = False):
    dropF behind [leaf, ..after] = [leaf, ..dropF [leaf, ..behind] after] :=
  match after with
    | [] => byComputing
    | [closer, ..after2] =>
      match pair: lastPair closer.token.kind leaf behind with
        | False => byComputing

theorem barishFNop ∀ (leaf: Leaf) (behind after: List Leaf)
    (nop: fwdPair behind leaf after = False):
    barishF behind [leaf, ..after] = barishF [leaf, ..behind] after :=
  match after with
    | [] => byComputing
    | [closer, ..after2] =>
      match pair: lastPair closer.token.kind leaf behind with
        | False => byComputing

theorem gapAfterNop ∀ (leaf: Leaf) (behind after: List Leaf)
    (nop: fwdPair behind leaf after = False):
    gapOk [leaf, ..behind] after = True :=
  match after with
    | [] => byComputing
    | [closer, ..after2] => rewrite nop

theorem barishAfterNop ∀ (leaf: Leaf) (behind after: List Leaf)
    (gap: gapOk behind [leaf, ..after] = True)
    (okB: barishTop behind = True):
    barish leaf.token behind = True :=
  match behind with
    | [] => byComputing
    | [x, ..older] =>
      match pair: lastPair leaf.token.kind x older with
        | False => okB

--| What the back-walk does to the leaves, newest first, without the last commas is
--| what it does with them, without them. The claim for the leaves to come.
def Home1Drop (after: List Leaf): Prop :=
  ∀ (b: List Leaf) => gapOk b after = True
    → barishTop b = True
    → barishF b after = True
    → home1 (dropRev b) (dropF b after) = dropRev (home1 b after) ∧ barishTop (home1 b after) = True

--| One step of `home1Drop` at a leaf that doesn't start a last comma.
theorem stepNormal ∀ (leaf: Leaf) (behind after: List Leaf)
    (gap: gapOk behind [leaf, ..after] = True)
    (okB: barishTop behind = True)
    (okF: barishF behind [leaf, ..after] = True)
    (nop: fwdPair behind leaf after = False)
    (ih: Home1Drop after):
    home1 (dropRev behind) (dropF behind [leaf, ..after]) = dropRev (home1 behind [leaf, ..after])
      ∧ barishTop (home1 behind [leaf, ..after]) = True :=
  let top: dr leaf.token.kind behind = dropRev behind := drNopTop leaf behind gap
  let okLeaf: barish leaf.token behind = True := barishAfterNop leaf behind after gap okB
  let gap': gapOk [leaf, ..behind] after = True := gapAfterNop leaf behind after nop
  let okF': barishF [leaf, ..behind] after = True := rewrite <- barishFNop leaf behind after nop then okF
  let plain: home1 [leaf, ..dropRev behind] (dropF [leaf, ..behind] after) = dropRev (home1 [leaf, ..behind] after)
    ∧ barishTop (home1 [leaf, ..behind] after) = True :=
    let claim := ih [leaf, ..behind] gap' okLeaf okF'
    rewrite top at claim then claim
  rewrite dropFNop leaf behind after nop then
    match trailing: leaf.trivia.trailing with
      | None => plain
      | Some comment =>
        match fixed: movable1 leaf with
          | False => plain
          | True =>
            let (zeq, teq, bar) := walkDrop leaf behind (dropRev behind) comment okLeaf top
            match walked: walk1 leaf behind with
              | Zero =>
                match walkedA: walk1 leaf (dropRev behind) with
                  | Zero => plain
              | Succ w =>
                match walkedA: walk1 leaf (dropRev behind) with
                  | Succ wA =>
                    let gap2: gapOk [leaf.withTrailing None, ..trailingAt behind (Succ w) comment] after = True :=
                      match after with
                        | [] => byComputing
                        | [closer, ..more] => rewrite hasItemTrailingAt behind (Succ w) comment, nop
                    let okF2: barishF [leaf.withTrailing None, ..trailingAt behind (Succ w) comment] after = True :=
                      rewrite barishFItem
                            [leaf.withTrailing None, ..trailingAt behind (Succ w) comment]
                            [leaf, ..behind]
                            after
                            byComputing then
                        okF'
                    let claim := ih [leaf.withTrailing None, ..trailingAt behind (Succ w) comment] gap2 bar okF2
                    let dF :=
                      dropFItem
                        [leaf.withTrailing None, ..trailingAt behind (Succ w) comment]
                        [leaf, ..behind]
                        after
                        byComputing
                    rewrite teq, dF at claim then claim

theorem dropFPair ∀ (comma closer: Leaf) (behind after: List Leaf)
    (pair: lastPair closer.token.kind comma behind = True):
    dropF behind [comma, closer, ..after] = [closer, ..dropF [closer, comma, ..behind] after] :=
  match pair2: lastPair closer.token.kind comma behind with | True => byComputing

theorem barishFPair ∀ (comma closer: Leaf) (behind after: List Leaf)
    (pair: lastPair closer.token.kind comma behind = True):
    barishF behind [comma, closer, ..after]
      = (comma.trivia.leading.isEmpty
        && comma.trivia.trailing.isNone
        && (!comma.token.lineStart || closer.token.lineStart)
        && barishF [closer, comma, ..behind] after) :=
  match pair2: lastPair closer.token.kind comma behind with | True => byComputing

theorem barishPairTop ∀ (comma closer: Leaf) (behind: List Leaf)
    (pair: lastPair closer.token.kind comma behind = True)
    (leadEmpty: comma.trivia.leading.isEmpty = True)
    (trailNone: comma.trivia.trailing.isNone = True)
    (lineOk: (!comma.token.lineStart || closer.token.lineStart) = True)
    (okB: barishTop behind = True):
    barish closer.token [comma, ..behind] = True :=
  match behind with
    | [] => cases
    | [next, ..more] => barishPair closer.token comma next more pair leadEmpty trailNone lineOk okB

theorem gapAfterPair ∀ (comma closer: Leaf) (behind after: List Leaf)
    (pair: lastPair closer.token.kind comma behind = True):
    gapOk [closer, comma, ..behind] after = True :=
  let isCloser: closer.token.kind.isCloser = True := Bool.andLeft (Bool.andRight pair)
  match after with
    | [] => byComputing
    | [next, ..more] => rewrite closerNotComma closer.token.kind isCloser

--| One step of `home1Drop` at a last comma and its closer.
theorem stepPair ∀ (comma closer: Leaf) (behind after: List Leaf)
    (pair: lastPair closer.token.kind comma behind = True)
    (okB: barishTop behind = True)
    (okF: barishF behind [comma, closer, ..after] = True)
    (ih: Home1Drop after):
    home1 (dropRev behind) (dropF behind [comma, closer, ..after]) = dropRev (home1 behind [comma, closer, ..after])
      ∧ barishTop (home1 behind [comma, closer, ..after]) = True :=
  let parts := rewrite barishFPair comma closer behind after pair at okF then okF
  let leadEmpty := Bool.andLeft parts
  let trailNone := Bool.andLeft (Bool.andRight parts)
  let lineOk := Bool.andLeft (Bool.andRight (Bool.andRight parts))
  let okF': barishF [closer, comma, ..behind] after = True := Bool.andRight (Bool.andRight (Bool.andRight parts))
  let okLeaf: barish closer.token [comma, ..behind] = True :=
    barishPairTop comma closer behind pair leadEmpty trailNone lineOk okB
  let top: dr closer.token.kind [comma, ..behind] = dropRev behind := drPairTop closer comma behind pair
  let gap': gapOk [closer, comma, ..behind] after = True := gapAfterPair comma closer behind after pair
  let plain: home1 [closer, ..dropRev behind] (dropF [closer, comma, ..behind] after)
    = dropRev (home1 [closer, comma, ..behind] after)
    ∧ barishTop (home1 [closer, comma, ..behind] after) = True :=
    let claim := ih [closer, comma, ..behind] gap' okLeaf okF'
    rewrite top at claim then claim
  rewrite dropFPair comma closer behind after pair then
    match commaTrailing: comma.trivia.trailing with
      | None =>
        match trailing: closer.trivia.trailing with
          | None => plain
          | Some comment =>
            match fixed: movable1 closer with
              | False => plain
              | True =>
                let (zeq, teq, bar) := walkDrop closer [comma, ..behind] (dropRev behind) comment okLeaf top
                match walked: walk1 closer [comma, ..behind] with
                  | Zero =>
                    match walkedA: walk1 closer (dropRev behind) with
                      | Zero => plain
                  | Succ w =>
                    match walkedA: walk1 closer (dropRev behind) with
                      | Succ wA =>
                        let isCloser: closer.token.kind.isCloser = True := Bool.andLeft (Bool.andRight pair)
                        let gap2: gapOk
                          [closer.withTrailing None, ..trailingAt [comma, ..behind] (Succ w) comment]
                          after
                          = True :=
                          match after with
                            | [] => byComputing
                            | [next, ..more] => rewrite closerNotComma closer.token.kind isCloser
                        let okF2: barishF
                          [closer.withTrailing None, ..trailingAt [comma, ..behind] (Succ w) comment]
                          after
                          = True :=
                          rewrite barishFItem
                                [closer.withTrailing None, ..trailingAt [comma, ..behind] (Succ w) comment]
                                [closer, comma, ..behind]
                                after
                                byComputing then
                            okF'
                        let claim :=
                          ih [closer.withTrailing None, ..trailingAt [comma, ..behind] (Succ w) comment] gap2 bar okF2
                        let dF :=
                          dropFItem
                            [closer.withTrailing None, ..trailingAt [comma, ..behind] (Succ w) comment]
                            [closer, comma, ..behind]
                            after
                            byComputing
                        rewrite teq, dF at claim then claim

--| The back-walk under slice 1's alphabet on leaves with last commas, with the last
--| commas then dropped, is the back-walk on the leaves without them.
--|
--| Proof idea: by induction on the leaves to come; a leaf that starts no last
--| comma is one step on both sides, with the comment's walk the same
--| (`walkDrop`); a last comma, bare, and its closer are two steps on one side
--| and one on the other.
theorem home1Drop ∀ (behind rest: List Leaf)
    (gap: gapOk behind rest = True)
    (okB: barishTop behind = True)
    (okF: barishF behind rest = True):
    home1 (dropRev behind) (dropF behind rest) = dropRev (home1 behind rest) ∧ barishTop (home1 behind rest) = True :=
  match rest with
    | [] => (byComputing, okB)
    | [leaf, ..after] =>
      match pair: fwdPair behind leaf after with
        | False => stepNormal leaf behind after gap okB okF pair (b g o f => home1Drop b after g o f)
        | True =>
          match after with
            | [closer, ..after2] =>
              stepPair leaf closer behind after2 pair okB okF (b g o f => home1Drop b after2 g o f)

-- Between the passes, leaves go from newest first to in order and back.

--| The leaves without their last commas, read forwards, and bare.
def DropRel (dropped leaves: List Leaf): Prop := dropped = dropF [] leaves ∧ barishF [] leaves = True

theorem dropRevOnto ∀ (rest acc: List Leaf)
    (gap: gapOk acc rest = True):
    dropRev (rest.reverseOnto acc) = (dropF acc rest).reverseOnto (dropRev acc) :=
  match induct (dropF acc rest) with
    | eq1 _ => byComputing
    | eq2 behind comma closer after pair ih =>
      let claim := ih (gapAfterPair comma closer behind after pair)
      rewrite drPairTop closer comma behind pair at claim then claim
    | eq3 behind leaf after notArm2 ih =>
      let claim := ih (gapAfterNop leaf behind after (fwdPairOfNotArm leaf behind after notArm2))
      rewrite drNopTop leaf behind gap at claim then claim

theorem barishSuffix ∀ (y: Leaf) (ys: List Leaf) (ok: barishTop [y, ..ys] = True): barishTop ys = True := match ys with
  | [] => byComputing
  | [x, ..older] =>
    match pair: lastPair y.token.kind x older with
      | False => ok
      | True =>
        match older with
          | [] => cases
          | [n, ..m] =>
            let isComma: (x.token.kind == Comma) = True := Bool.andLeft pair
            let tailOk: barish n.token m = True := Bool.andRight (Bool.andRight (Bool.andRight ok))
            let nop: lastPair x.token.kind n m = False := rewrite commaNotCloser x.token.kind isComma, Bool.andFalse
            rewrite barishNop x.token n m nop then tailOk

theorem barishSuffixOnto ∀ (rest acc: List Leaf) (ok: barishTop (rest.reverseOnto acc) = True): barishTop acc = True :=
  match rest with
    | [] => ok
    | [x, ..more] => barishSuffix x acc (barishSuffixOnto more [x, ..acc] ok)

theorem barishPairEq ∀ (comma closer: Leaf) (behind: List Leaf)
    (pair: lastPair closer.token.kind comma behind = True):
    barish closer.token [comma, ..behind]
      = (comma.trivia.leading.isEmpty
        && comma.trivia.trailing.isNone
        && (!comma.token.lineStart || closer.token.lineStart)
        && barishTop behind) :=
  match behind with
    | [] => cases
    | [n, ..m] =>
      match pair2: lastPair closer.token.kind comma [n, ..m] with
        | True => byComputing

theorem barishFOnto ∀ (rest acc: List Leaf)
    (gap: gapOk acc rest = True)
    (ok: barishTop (rest.reverseOnto acc) = True):
    barishF acc rest = True :=
  match induct (barishF acc rest) with
    | eq1 _ => byComputing
    | eq2 behind comma closer after pair ih =>
      let here: barishTop [closer, comma, ..behind] = True := barishSuffixOnto after [closer, comma, ..behind] ok
      let parts := rewrite barishPairEq comma closer behind pair at here then here
      Bool.andIntro
        (Bool.andLeft parts)
        (Bool.andIntro
          (Bool.andLeft (Bool.andRight parts))
          (Bool.andIntro
            (Bool.andLeft (Bool.andRight (Bool.andRight parts)))
            (ih (gapAfterPair comma closer behind after pair) ok)))
    | eq3 behind leaf after notArm2 ih =>
      ih (gapAfterNop leaf behind after (fwdPairOfNotArm leaf behind after notArm2)) ok

--| Leaves newest first, without their last commas and bare, are in order
--| what the forward reading gives.
theorem dropRelOfRev ∀ (leaves dropped: List Leaf)
    (same: dropRev leaves = dropped)
    (ok: barishTop leaves = True):
    DropRel dropped.reverse leaves.reverse :=
  let viaOnto := dropRevOnto leaves.reverse [] byComputing
  let twice: leaves.reverse.reverseOnto [] = leaves := List.reverseReverse leaves
  let viaOnto' := rewrite twice at viaOnto then viaOnto
  let eq: dropped = (dropF [] leaves.reverse).reverse := Eq.trans same.flipped viaOnto'
  (
    (rewrite eq, List.reverseReverse (dropF [] leaves.reverse)),
    barishFOnto leaves.reverse [] byComputing (rewrite twice then ok)
  )

-- Step 2

--| `commasFrom` with the leaves done left newest first.
def commasR (done: List Leaf) (carried: Option Carried) (rest: List Leaf) (end: Trivia): Lexed :=
  let receive := (trivia: Trivia) => carried.map (carry => carry.into trivia) |> .getOrElse trivia
  match rest with
    | [] => { leaves = done, end = receive end }
    | [leaf, ..after] =>
      let leaf := { leaf | trivia = receive leaf.trivia }
      match commaCarries leaf.trivia with
        | Some carry if leaf.kind == Comma => commasR [{ leaf | trivia = Trivia.empty }, ..done] (Some carry) after end
        | _ => commasR [leaf, ..done] None after end

theorem commasFromR ∀ (done: List Leaf) (carried: Option Carried) (rest: List Leaf) (end: Trivia):
    commasFrom done carried rest end
      = { leaves = (commasR done carried rest end).leaves.reverse, end = (commasR done carried rest end).end } :=
  match rest with
    | [] => byComputing
    | [leaf, ..after] =>
      match cc: commaCarries
        { leaf | trivia = (carried.map (carry => carry.into leaf.trivia) |> .getOrElse leaf.trivia) }.trivia with
        | None =>
          commasFromR
            [{ leaf | trivia = (carried.map (carry => carry.into leaf.trivia) |> .getOrElse leaf.trivia) }, ..done]
            None
            after
            end
        | Some carry =>
          match isComma: leaf.token.kind == Comma with
            | True =>
              commasFromR
                [
                  { { leaf | trivia = (carried.map (carry => carry.into leaf.trivia) |> .getOrElse leaf.trivia) } |
                    trivia = Trivia.empty
                  },
                  ..done
                ]
                (Some carry)
                after
                end
            | False =>
              commasFromR
                [{ leaf | trivia = (carried.map (carry => carry.into leaf.trivia) |> .getOrElse leaf.trivia) }, ..done]
                None
                after
                end

--| A comment still carried comes right after a comma.
def carriedQuiet (carried: Option Carried) (done: List Leaf): Bool := match carried with
  | None => True
  | Some _ => !hasItem done

theorem hasItemComma ∀ (leaf: Leaf) (rest: List Leaf)
    (isComma: (leaf.token.kind == Comma) = True):
    hasItem [leaf, ..rest] = False :=
  let same: leaf.token.kind = Comma := DecEq.sound isComma
  rewrite same

def Commas2Drop (after: List Leaf) (end: Trivia): Prop :=
  ∀ (done: List Leaf) (carried: Option Carried) => gapOk done after = True
    → barishTop done = True
    → barishF done after = True
    → carriedQuiet carried done = True
    → (commasR (dropRev done) carried (dropF done after) end).leaves = dropRev (commasR done carried after end).leaves
      ∧ (commasR (dropRev done) carried (dropF done after) end).end = (commasR done carried after end).end
      ∧ barishTop (commasR done carried after end).leaves = True

theorem commasDrop ∀ (done rest: List Leaf) (carried: Option Carried) (end: Trivia)
    (gap: gapOk done rest = True)
    (okB: barishTop done = True)
    (okF: barishF done rest = True)
    (quiet: carriedQuiet carried done = True):
    (commasR (dropRev done) carried (dropF done rest) end).leaves = dropRev (commasR done carried rest end).leaves
      ∧ (commasR (dropRev done) carried (dropF done rest) end).end = (commasR done carried rest end).end
      ∧ barishTop (commasR done carried rest end).leaves = True :=
  match rest with
    | [] => (byComputing, byComputing, okB)
    | [leaf, ..after] =>
      match pair: fwdPair done leaf after with
        | False =>
          stepNormal2 leaf done after carried end gap okB okF pair (d c g o f q => commasDrop d after c end g o f q)
        | True =>
          match after with
            | [closer, ..after2] => stepPair2 leaf closer done after2 carried end pair okB okF quiet (d c g o f q =>
              commasDrop d after2 c end g o f q)

theorem gapAfterNopT ∀ (leaf: Leaf) (trivia: Trivia) (behind after: List Leaf)
    (nop: fwdPair behind leaf after = False):
    gapOk [{ leaf | trivia }, ..behind] after = True :=
  match after with
    | [] => byComputing
    | [closer, ..after2] => rewrite nop

theorem barishFNopT ∀ (leaf: Leaf) (trivia: Trivia) (behind after: List Leaf)
    (nop: fwdPair behind leaf after = False):
    barishF behind [leaf, ..after] = barishF [{ leaf | trivia }, ..behind] after :=
  Eq.trans
    (barishFNop leaf behind after nop)
    (barishFItem [leaf, ..behind] [{ leaf | trivia }, ..behind] after byComputing)

theorem stepGo ∀ (leaf: Leaf) (trivia: Trivia) (done after: List Leaf) (carried: Option Carried) (end: Trivia)
    (gap: gapOk done [leaf, ..after] = True)
    (okB: barishTop done = True)
    (okF: barishF done [leaf, ..after] = True)
    (nop: fwdPair done leaf after = False)
    (quiet: carriedQuiet carried [{ leaf | trivia }, ..done] = True)
    (ih: Commas2Drop after end):
    (commasR [{ leaf | trivia }, ..dropRev done] carried (dropF [leaf, ..done] after) end).leaves
      = dropRev (commasR [{ leaf | trivia }, ..done] carried after end).leaves
      ∧ (commasR [{ leaf | trivia }, ..dropRev done] carried (dropF [leaf, ..done] after) end).end
        = (commasR [{ leaf | trivia }, ..done] carried after end).end
      ∧ barishTop (commasR [{ leaf | trivia }, ..done] carried after end).leaves = True :=
  let top: dr leaf.token.kind done = dropRev done := drNopTop leaf done gap
  let okLeaf: barish leaf.token done = True := barishAfterNop leaf done after gap okB
  let gap': gapOk [{ leaf | trivia }, ..done] after = True := gapAfterNopT leaf trivia done after nop
  let okF': barishF [{ leaf | trivia }, ..done] after = True :=
    rewrite <- barishFNopT leaf trivia done after nop then okF
  let claim := ih [{ leaf | trivia }, ..done] carried gap' okLeaf okF' quiet
  let items := dropFItem [leaf, ..done] [{ leaf | trivia }, ..done] after byComputing
  rewrite items then rewrite top at claim then claim

theorem stepNormal2 ∀ (leaf: Leaf) (done after: List Leaf) (carried: Option Carried) (end: Trivia)
    (gap: gapOk done [leaf, ..after] = True)
    (okB: barishTop done = True)
    (okF: barishF done [leaf, ..after] = True)
    (nop: fwdPair done leaf after = False)
    (ih: Commas2Drop after end):
    (commasR (dropRev done) carried (dropF done [leaf, ..after]) end).leaves
      = dropRev (commasR done carried [leaf, ..after] end).leaves
      ∧ (commasR (dropRev done) carried (dropF done [leaf, ..after]) end).end
        = (commasR done carried [leaf, ..after] end).end
      ∧ barishTop (commasR done carried [leaf, ..after] end).leaves = True :=
  rewrite dropFNop leaf done after nop then
    match cc: commaCarries (carried.map (carry => carry.into leaf.trivia) |> .getOrElse leaf.trivia) with
      | None =>
        stepGo leaf
          (carried.map (carry => carry.into leaf.trivia) |> .getOrElse leaf.trivia)
          done
          after
          None
          end
          gap
          okB
          okF
          nop
          byComputing
          ih
      | Some carry =>
        match isComma: leaf.token.kind == Comma with
          | True =>
            stepGo leaf Trivia.empty done after
              (Some carry)
              end
              gap
              okB
              okF
              nop
              (rewrite hasItemComma { leaf | trivia = Trivia.empty } done isComma)
              ih
          | False =>
            stepGo leaf
              (carried.map (carry => carry.into leaf.trivia) |> .getOrElse leaf.trivia)
              done
              after
              None
              end
              gap
              okB
              okF
              nop
              byComputing
              ih

theorem carriesOfBare ∀ (trivia: Trivia)
    (leadEmpty: trivia.leading.isEmpty = True)
    (trailNone: trivia.trailing.isNone = True):
    commaCarries trivia = None :=
  match trivia.leading, trivia.trailing with | [], None => byComputing

theorem stepPair2 ∀ (comma closer: Leaf) (done after: List Leaf) (carried: Option Carried) (end: Trivia)
    (pair: lastPair closer.token.kind comma done = True)
    (okB: barishTop done = True)
    (okF: barishF done [comma, closer, ..after] = True)
    (quiet: carriedQuiet carried done = True)
    (ih: Commas2Drop after end):
    (commasR (dropRev done) carried (dropF done [comma, closer, ..after]) end).leaves
      = dropRev (commasR done carried [comma, closer, ..after] end).leaves
      ∧ (commasR (dropRev done) carried (dropF done [comma, closer, ..after]) end).end
        = (commasR done carried [comma, closer, ..after] end).end
      ∧ barishTop (commasR done carried [comma, closer, ..after] end).leaves = True :=
  let parts := rewrite barishFPair comma closer done after pair at okF then okF
  let leadEmpty := Bool.andLeft parts
  let trailNone := Bool.andLeft (Bool.andRight parts)
  let lineOk := Bool.andLeft (Bool.andRight (Bool.andRight parts))
  let okF': barishF [closer, comma, ..done] after = True := Bool.andRight (Bool.andRight (Bool.andRight parts))
  let okLeaf: barish closer.token [comma, ..done] = True :=
    barishPairTop comma closer done pair leadEmpty trailNone lineOk okB
  let top: dr closer.token.kind [comma, ..done] = dropRev done := drPairTop closer comma done pair
  let gap': gapOk [closer, comma, ..done] after = True := gapAfterPair comma closer done after pair
  let item: hasItem done = True := Bool.andRight (Bool.andRight pair)
  let notComma: (closer.token.kind == Comma) = False :=
    closerNotComma closer.token.kind (Bool.andLeft (Bool.andRight pair))
  rewrite dropFPair comma closer done after pair then
    match carried with
      | Some c => rewrite item at quiet then cases
      | None =>
        let claim := ih [closer, comma, ..done] None gap' okLeaf okF' byComputing
        let items := dropFItem [closer, comma, ..done] [closer, comma, ..done] after byComputing
        rewrite carriesOfBare comma.trivia leadEmpty trailNone then
          rewrite top at claim then
            match cc: commaCarries closer.trivia with
              | None => claim
              | Some carry =>
                match isComma: closer.token.kind == Comma with
                  | False => claim

-- Step 3

--| `arrowsFrom` with the leaves done and the current one left newest first.
def arrowsR (done: List Leaf) (current: Leaf) (rest: List Leaf): List Leaf := match rest with
  | [] => [current, ..done]
  | [next, ..more] =>
    if current.kind == Arrow && (!next.trivia.leading.isEmpty || current.trivia.trailing.isSome) then
      let own := current.trivia.trailing.map (comment => [comment.unspaced]) |> .getOrElse []
      let current := { current |
        trivia = { current.trivia | leading = current.trivia.leading ++ own ++ next.trivia.leading, trailing = None }
      }
      arrowsR [current, ..done] (next.withLeading []) more
    else arrowsR [current, ..done] next more

theorem arrowsFromR ∀ (done: List Leaf) (current: Leaf) (rest: List Leaf):
    arrowsFrom done current rest = (arrowsR done current rest).reverse :=
  match rest with
    | [] => byComputing
    | [next, ..more] =>
      match arrow: current.token.kind == Arrow && (!next.trivia.leading.isEmpty || current.trivia.trailing.isSome) with
        | True =>
          arrowsFromR
            [
              { current |
                trivia = { current.trivia |
                  leading = current.trivia.leading
                    ++ (current.trivia.trailing.map (comment => [comment.unspaced]) |> .getOrElse [])
                    ++ next.trivia.leading,
                  trailing = None
                }
              },
              ..done
            ]
            (next.withLeading [])
            more
        | False => arrowsFromR [current, ..done] next more

theorem gapOkItem ∀ (x: Leaf) (older older' rest: List Leaf)
    (same: hasItem older = hasItem older'):
    gapOk [x, ..older] rest = gapOk [x, ..older'] rest :=
  match rest with
    | [] => byComputing
    | [next, ..more] => rewrite same

def ArrowsDrop (more: List Leaf): Prop :=
  ∀ (done: List Leaf) (current: Leaf) => gapOk [current, ..done] more = True
    → barishTop [current, ..done] = True
    → barishF [current, ..done] more = True
    → arrowFrom (tokens [current, ..more]) = True
    → arrowsR (dr current.token.kind done) current (dropF [current, ..done] more) = dropRev (arrowsR done current more)
      ∧ barishTop (arrowsR done current more) = True

--| One step of the arrow lift at a leaf and the next, which is no last comma, with
--| the leaves they become.
theorem arrowGo ∀ (cur nxt: Leaf) (curT nxtT: Trivia) (done more: List Leaf)
    (gap: gapOk [cur, ..done] [nxt, ..more] = True)
    (okB: barishTop [cur, ..done] = True)
    (okF: barishF [cur, ..done] [nxt, ..more] = True)
    (nop: fwdPair [cur, ..done] nxt more = False)
    (plain: arrowFrom (tokens [nxt, ..more]) = True)
    (ih: ArrowsDrop more):
    arrowsR [{ cur | trivia = curT }, ..dr cur.token.kind done] { nxt | trivia = nxtT } (dropF [nxt, cur, ..done] more)
      = dropRev (arrowsR [{ cur | trivia = curT }, ..done] { nxt | trivia = nxtT } more)
      ∧ barishTop (arrowsR [{ cur | trivia = curT }, ..done] { nxt | trivia = nxtT } more) = True :=
  let gapX: gapOk [{ cur | trivia = curT }, ..done] [{ nxt | trivia = nxtT }, ..more] = True := gap
  let top := drNopTop { nxt | trivia = nxtT } [{ cur | trivia = curT }, ..done] gapX
  let gap2: gapOk [{ nxt | trivia = nxtT }, { cur | trivia = curT }, ..done] more = True :=
    Eq.trans
      (gapOkItem { nxt | trivia = nxtT } [{ cur | trivia = curT }, ..done] [cur, ..done] more byComputing)
      (gapAfterNopT nxt nxtT [cur, ..done] more nop)
  let okBc: barishTop [{ cur | trivia = curT }, ..done] = True := okB
  let okB2: barishTop [{ nxt | trivia = nxtT }, { cur | trivia = curT }, ..done] = True :=
    barishAfterNop { nxt | trivia = nxtT } [{ cur | trivia = curT }, ..done] more gapX okBc
  let okF1: barishF [{ nxt | trivia = nxtT }, cur, ..done] more = True :=
    rewrite <- barishFNopT nxt nxtT [cur, ..done] more nop then okF
  let okF2: barishF [{ nxt | trivia = nxtT }, { cur | trivia = curT }, ..done] more = True :=
    rewrite <- barishFItem
          [{ nxt | trivia = nxtT }, cur, ..done]
          [{ nxt | trivia = nxtT }, { cur | trivia = curT }, ..done]
          more
          byComputing then
      okF1
  let claim := ih [{ cur | trivia = curT }, ..done] { nxt | trivia = nxtT } gap2 okB2 okF2 plain
  let items := dropFItem [nxt, cur, ..done] [{ nxt | trivia = nxtT }, { cur | trivia = curT }, ..done] more byComputing
  rewrite items then rewrite top at claim then claim

theorem arrowsDrop ∀ (done: List Leaf) (current: Leaf) (rest: List Leaf)
    (gap: gapOk [current, ..done] rest = True)
    (okB: barishTop [current, ..done] = True)
    (okF: barishF [current, ..done] rest = True)
    (plain: arrowFrom (tokens [current, ..rest]) = True):
    arrowsR (dr current.token.kind done) current (dropF [current, ..done] rest) = dropRev (arrowsR done current rest)
      ∧ barishTop (arrowsR done current rest) = True :=
  match rest with
    | [] => (byComputing, okB)
    | [next, ..more] =>
      match pair: fwdPair [current, ..done] next more with
        | False =>
          rewrite dropFNop next [current, ..done] more pair then
            match arrow: current.token.kind == Arrow
              && (!next.trivia.leading.isEmpty || current.trivia.trailing.isSome) with
              | True =>
                arrowGo current next
                  { current.trivia |
                    leading = current.trivia.leading
                      ++ (current.trivia.trailing.map (comment => [comment.unspaced]) |> .getOrElse [])
                      ++ next.trivia.leading,
                    trailing = None
                  }
                  { next.trivia | leading = [] }
                  done
                  more
                  gap
                  okB
                  okF
                  pair
                  (Bool.andRight plain)
                  (d c g o f p => arrowsDrop d c more g o f p)
              | False =>
                arrowGo current next current.trivia next.trivia done more gap okB okF pair
                  (Bool.andRight plain)
                  (d c g o f p => arrowsDrop d c more g o f p)
        | True =>
          match more with
            | [closer, ..more2] =>
              let parts := rewrite barishFPair next closer [current, ..done] more2 pair at okF then okF
              let leadEmpty := Bool.andLeft parts
              let trailNone := Bool.andLeft (Bool.andRight parts)
              let lineOk := Bool.andLeft (Bool.andRight (Bool.andRight parts))
              let okF': barishF [closer, next, current, ..done] more2 = True :=
                Bool.andRight (Bool.andRight (Bool.andRight parts))
              let okLeaf: barish closer.token [next, current, ..done] = True :=
                barishPairTop next closer [current, ..done] pair leadEmpty trailNone lineOk okB
              let top: dr closer.token.kind [next, current, ..done] = dropRev [current, ..done] :=
                drPairTop closer next [current, ..done] pair
              let gap': gapOk [closer, next, current, ..done] more2 = True :=
                gapAfterPair next closer [current, ..done] more2 pair
              let isComma: (next.token.kind == Comma) = True := Bool.andLeft pair
              let first := Bool.andLeft plain
              let notArrow: (current.token.kind == Arrow) = False := match isArrow: current.token.kind == Arrow with
                | False => byComputing
                | True => rewrite isComma at first then cases
              let nextNotArrow: (next.token.kind == Arrow) = False := rewrite DecEq.sound isComma
              let claim :=
                arrowsDrop [next, current, ..done] closer more2 gap' okLeaf okF' (Bool.andRight (Bool.andRight plain))
              rewrite dropFPair next closer [current, ..done] more2 pair, notArrow, nextNotArrow then
                rewrite top at claim then claim

-- The leaves with the last commas bare, and without them

--| `withBareLastCommas` with the leaves done returned newest first.
def withBareR (behind rest: List Leaf): List Leaf := match rest with
  | [] => behind
  | [comma, closer, ..after] if lastPair closer.token.kind comma behind =>
    let (moved, earlier) := commaMoved comma closer behind
    withBareR [moved, { comma | trivia = Trivia.empty }, ..earlier] after
  | [leaf, ..after] => withBareR [leaf, ..behind] after

--| The last commas made bare as `withBareLastCommas` makes them, but with the
--| closer after each taking the comma's line start, as deleting the comma
--| from the text would leave it (`commaDeleted`). Comment placement on these leaves, by
--| `startsWalk False`, is comment placement on the bare ones by `startsWalk True`, but
--| for those line starts (`Syntax.SettleMarkProofs`); it is the form the
--| proofs below relate to the leaves without the commas.
def withMarkedLastCommas (behind rest: List Leaf): List Leaf := match rest with
  | [] => behind.reverse
  | [comma, closer, ..after] if lastPair closer.token.kind comma behind =>
    let (moved, earlier) := commaDeleted comma closer behind
    withMarkedLastCommas [moved, { comma | trivia = Trivia.empty }, ..earlier] after
  | [leaf, ..after] => withMarkedLastCommas [leaf, ..behind] after

--| `withMarkedLastCommas` with the leaves done returned newest first.
def withMarkedR (behind rest: List Leaf): List Leaf := match rest with
  | [] => behind
  | [comma, closer, ..after] if lastPair closer.token.kind comma behind =>
    let (moved, earlier) := commaDeleted comma closer behind
    withMarkedR [moved, { comma | trivia = Trivia.empty }, ..earlier] after
  | [leaf, ..after] => withMarkedR [leaf, ..behind] after

--| `withoutLastCommas` with the leaves done returned newest first.
def withoutR (behind rest: List Leaf): List Leaf := match rest with
  | [] => behind
  | [comma, closer, ..after] if lastPair closer.token.kind comma behind =>
    let (moved, earlier) := commaDeleted comma closer behind
    withoutR [moved, ..earlier] after
  | [leaf, ..after] => withoutR [leaf, ..behind] after

theorem withBareFromR ∀ (behind rest: List Leaf): withBareLastCommas behind rest = (withBareR behind rest).reverse :=
  match induct (withBareLastCommas behind rest) with
    | eq1 _ => byComputing
    | eq2 behind comma closer after guard ih => rewrite withBareR.eq2 behind comma closer after guard then ih
    | eq3 behind leaf after notArm2 ih => rewrite withBareR.eq3 behind leaf after notArm2 then ih

theorem withMarkedFromR ∀ (behind rest: List Leaf):
    withMarkedLastCommas behind rest = (withMarkedR behind rest).reverse :=
  match induct (withMarkedLastCommas behind rest) with
    | eq1 _ => byComputing
    | eq2 behind comma closer after guard ih => rewrite withMarkedR.eq2 behind comma closer after guard then ih
    | eq3 behind leaf after notArm2 ih => rewrite withMarkedR.eq3 behind leaf after notArm2 then ih

theorem withoutFromR ∀ (behind rest: List Leaf): withoutLastCommas behind rest = (withoutR behind rest).reverse :=
  match induct (withoutLastCommas behind rest) with
    | eq1 _ => byComputing
    | eq2 behind comma closer after guard ih => rewrite withoutR.eq2 behind comma closer after guard then ih
    | eq3 behind leaf after notArm2 ih => rewrite withoutR.eq3 behind leaf after notArm2 then ih

--| Moving a last comma's comments off the leaves with the commas in, then
--| dropping the commas, is moving them off the leaves without.
theorem commaDeletedDrop ∀ (comma closer: Leaf) (behind: List Leaf)
    (pair: lastPair closer.token.kind comma behind = True):
    (commaDeleted comma closer (dropRev behind)).fst = (commaDeleted comma closer behind).fst
      ∧ (commaDeleted comma closer (dropRev behind)).snd = dropRev (commaDeleted comma closer behind).snd
      ∧ hasItem (commaDeleted comma closer behind).snd = hasItem behind
      ∧ (barishTop behind = True → barishTop (commaDeleted comma closer behind).snd = True) :=
  match behind with
    | [] => cases
    | [prev, ..tail] =>
      match trailing: comma.trivia.trailing with
        | None => (byComputing, byComputing, byComputing, ok => ok)
        | Some comment =>
          match starts: comma.token.lineStart with
            | True => (byComputing, byComputing, byComputing, ok => ok)
            | False => (byComputing, byComputing, byComputing, ok => ok)

--| The third case of `match induct` on the comma-dropping walkers (`withoutR` and its siblings share a guard) says,
--| as `notArm2`, that the leaf is no last comma: the pair test fails.
theorem fwdPairOfNotArm ∀ (leaf: Leaf) (behind after: List Leaf)
    (notArm2: ∀ (closer: Leaf) (after1: List Leaf) => after = [closer, ..after1]
      → lastPair closer.token.kind leaf behind = False):
    fwdPair behind leaf after = False :=
  match after with
    | [] => byComputing
    | [closer, ..after1] => notArm2 closer after1 byComputing

--| The walkers' `notArm2` for a leaf that is no last comma.
theorem notArmOfFwdPair ∀ (leaf: Leaf) (behind after: List Leaf)
    (nop: fwdPair behind leaf after = False)
    (closer: Leaf) (after1: List Leaf)
    (same: after = [closer, ..after1]):
    lastPair closer.token.kind leaf behind = False :=
  rewrite same at nop then nop

theorem hasItemDropRev ∀ (behind: List Leaf): hasItem (dropRev behind) = hasItem behind := match behind with
  | [] | [_, .._] => byComputing

theorem fwdPairDrop ∀ (behind: List Leaf) (leaf: Leaf) (after: List Leaf):
    fwdPair (dropRev behind) leaf after = fwdPair behind leaf after :=
  match after with
    | [] => byComputing
    | [closer, ..more] => rewrite hasItemDropRev behind

theorem commaDeletedFst ∀ (comma closer: Leaf) (behind: List Leaf):
    (commaDeleted comma closer behind).fst.token.kind = closer.token.kind
      ∧ (commaDeleted comma closer behind).fst.token.lineStart = (comma.token.lineStart || closer.token.lineStart) :=
  match trailing: comma.trivia.trailing with
    | None => (byComputing, byComputing)
    | Some comment =>
      match behind with
        | [] => (byComputing, byComputing)
        | [prev, ..tail] =>
          match starts: comma.token.lineStart with
            | True => (byComputing, byComputing)
            | False => (byComputing, byComputing)

theorem buildDrop ∀ (behind rest: List Leaf)
    (gap: gapOk behind rest = True)
    (okB: barishTop behind = True):
    withoutR (dropRev behind) rest = dropRev (withMarkedR behind rest) ∧ barishTop (withMarkedR behind rest) = True :=
  match induct (withMarkedR behind rest) with
    | eq1 _ => (byComputing, okB)
    | eq2 behind comma closer after guard ih =>
      let (isComma, isCloser, item) := guard
      let pair: lastPair closer.token.kind comma behind = True := (isComma, Bool.andIntro isCloser item)
      let (hFst, hSnd, hItem, hBar) := commaDeletedDrop comma closer behind pair
      let (kindEq, startEq) := commaDeletedFst comma closer behind
      let pairA: lastPair closer.token.kind comma (dropRev behind) = True := rewrite hasItemDropRev behind then pair
      let itemE: hasItem (commaDeleted comma closer behind).snd = True := rewrite hItem then item
      let pair2: lastPair
        (commaDeleted comma closer behind).fst.token.kind
        { comma | trivia = Trivia.empty }
        (commaDeleted comma closer behind).snd
        = True :=
        rewrite kindEq, itemE then Bool.andIntro isComma (Bool.andIntro isCloser byComputing)
      let lineOk: (!comma.token.lineStart || (commaDeleted comma closer behind).fst.token.lineStart) = True :=
        rewrite startEq then
          match s: comma.token.lineStart with
            | True => byComputing
            | False => byComputing
      let okE: barishTop (commaDeleted comma closer behind).snd = True := hBar okB
      let okB2: barishTop [
        (commaDeleted comma closer behind).fst,
        { comma | trivia = Trivia.empty },
        ..(commaDeleted comma closer behind).snd
      ]
        = True :=
        barishPairTop
          { comma | trivia = Trivia.empty }
          (commaDeleted comma closer behind).fst
          (commaDeleted comma closer behind).snd
          pair2
          byComputing
          byComputing
          lineOk
          okE
      let gap2 :=
        gapAfterPair
          { comma | trivia = Trivia.empty }
          (commaDeleted comma closer behind).fst
          (commaDeleted comma closer behind).snd
          after
          pair2
      let claim := ih gap2 okB2
      let top :=
        drPairTop
          (commaDeleted comma closer behind).fst
          { comma | trivia = Trivia.empty }
          (commaDeleted comma closer behind).snd
          pair2
      rewrite withoutR.eq2 (dropRev behind) comma closer after pairA, hFst, hSnd then rewrite top at claim then claim
    | eq3 behind leaf after notArm2 ih =>
      let pair := fwdPairOfNotArm leaf behind after notArm2
      let claim := ih (gapAfterNop leaf behind after pair) (barishAfterNop leaf behind after gap okB)
      rewrite withoutR.eq3
            (dropRev behind)
            leaf
            after
            (notArmOfFwdPair leaf (dropRev behind) after (rewrite fwdPairDrop behind leaf after then pair)) then
        rewrite drNopTop leaf behind gap at claim then claim

-- Making the last commas bare moves no token: `commaMoved` leaves the closer's token as it was.

theorem tokenEta ∀ (token: Token): { token | lineStart = token.lineStart } = token := match token with
  | { kind, text, column, lineStart } => byComputing

theorem commaMovedTokens ∀ (comma closer: Leaf) (behind: List Leaf):
    (commaMoved comma closer behind).fst.token = closer.token
      ∧ tokens (commaMoved comma closer behind).snd = tokens behind :=
  match trailing: comma.trivia.trailing with
    | None => (byComputing, byComputing)
    | Some comment =>
      match behind with
        | [] => (byComputing, byComputing)
        | [prev, ..tail] =>
          match starts: comma.token.lineStart with
            | True => (byComputing, byComputing)
            | False => (byComputing, byComputing)

theorem plainTail ∀ (x: Leaf) (xs: List Leaf)
    (plain: plainFrom (tokens [x, ..xs]) = True):
    plainFrom (tokens xs) = True :=
  match xs with
    | [] => byComputing
    | [y, ..ys] => Bool.andRight (Bool.andRight plain)

theorem withBareRTokens ∀ (behind rest: List Leaf): tokens (withBareR behind rest) = tokens (rest.reverseOnto behind) :=
  match induct (withBareR behind rest) with
    | eq1 _ => byComputing
    | eq2 behind comma closer after _ ih =>
      let (fstTok, sndToks) := commaMovedTokens comma closer behind
      rewrite tokensReverseOnto after [closer, comma, ..behind] then
        rewrite tokensReverseOnto after [
              (commaMoved comma closer behind).fst,
              { comma | trivia = Trivia.empty },
              ..(commaMoved comma closer behind).snd
            ],
            fstTok,
            sndToks at ih then
          ih
    | eq3 _ _ _ _ ih => ih

-- The passes

theorem dropFAll ∀ (p: Leaf → Bool) (behind rest: List Leaf)
    (all: rest.all p = True):
    (dropF behind rest).all p = True :=
  match rest with
    | [] => byComputing
    | [leaf, ..after] =>
      match after with
        | [] => Bool.andIntro (Bool.andLeft all) byComputing
        | [closer, ..after2] =>
          match pair: lastPair closer.token.kind leaf behind with
            | True =>
              Bool.andIntro
                (Bool.andLeft (Bool.andRight all))
                (dropFAll p [closer, leaf, ..behind] after2 (Bool.andRight (Bool.andRight all)))
            | False =>
              Bool.andIntro (Bool.andLeft all) (dropFAll p [leaf, ..behind] [closer, ..after2] (Bool.andRight all))

theorem rule1Drop ∀ (leaves dropped: List Leaf)
    (rel: DropRel dropped leaves)
    (within: leaves.all (leaf => leaf.kind.within1) = True):
    DropRel (homeFrom False [] None dropped) (homeFrom False [] None leaves) :=
  let (same, bare) := rel
  let withinDropped: dropped.all (leaf => leaf.kind.within1) = True :=
    rewrite same then dropFAll (leaf => leaf.kind.within1) [] leaves within
  let (result, barished) := home1Drop [] leaves byComputing byComputing bare
  let result': home1 [] dropped = dropRev (home1 [] leaves) := rewrite same then result
  rewrite homeFromHome1 [] leaves byComputing within, homeFromHome1 [] dropped byComputing withinDropped then
    dropRelOfRev (home1 [] leaves) (home1 [] dropped) result'.flipped barished

theorem rule2Drop ∀ (leaves dropped: List Leaf) (end: Trivia)
    (rel: DropRel dropped leaves):
    DropRel (commasFrom [] None dropped end).leaves (commasFrom [] None leaves end).leaves
      ∧ (commasFrom [] None dropped end).end = (commasFrom [] None leaves end).end :=
  let (same, bare) := rel
  let (leavesEq, endEq, barished) := commasDrop [] leaves None end byComputing byComputing bare byComputing
  rewrite same, commasFromR [] None leaves end, commasFromR [] None (dropF [] leaves) end then
    (
      dropRelOfRev
        (commasR [] None leaves end).leaves
        (commasR [] None (dropF [] leaves) end).leaves
        leavesEq.flipped
        barished,
      endEq
    )

theorem rule3Drop ∀ (leaves dropped: List Leaf)
    (rel: DropRel dropped leaves)
    (plain: arrowFrom (tokens leaves) = True):
    DropRel (arrows dropped) (arrows leaves) :=
  let (same, bare) := rel
  match leaves with
    | [] => rewrite same then (byComputing, byComputing)
    | [first, ..rest] =>
      let nop: fwdPair [] first rest = False := match rest with
        | [] => byComputing
        | [next, ..more] => rewrite Bool.andFalse, Bool.andFalse
      let (result, barished) :=
        arrowsDrop [] first rest
          (gapAfterNop first [] rest nop)
          byComputing
          (rewrite <- barishFNop first [] rest nop then bare)
          plain
      rewrite same,
          dropFNop first [] rest nop,
          arrowsFromR [] first (dropF [first] rest),
          arrowsFromR [] first rest then
        dropRelOfRev (arrowsR [] first rest) (arrowsR [] first (dropF [first] rest)) result.flipped barished

--| Trim's step on one leaf.
def trim (leaf: Leaf): Leaf := { leaf | trivia = leaf.trivia.trimmed }

theorem dropFTrim ∀ (b b' rest: List Leaf)
    (same: hasItem b' = hasItem b):
    dropF b' (rest.map trim) = (dropF b rest).map trim :=
  match rest with
    | [] => byComputing
    | [leaf, ..after] =>
      match after with
        | [] => byComputing
        | [closer, ..after2] =>
          match pair: lastPair closer.token.kind leaf b with
            | True =>
              let pair': lastPair closer.token.kind leaf b' = True := rewrite same then pair
              rewrite pair' then
                Eq.cong
                  (tail => [trim closer, ..tail])
                  (dropFTrim [closer, leaf, ..b] [trim closer, trim leaf, ..b'] after2 byComputing)
            | False =>
              let pair': lastPair closer.token.kind leaf b' = False := rewrite same then pair
              rewrite pair' then
                Eq.cong
                  (tail => [trim leaf, ..tail])
                  (dropFTrim [leaf, ..b] [trim leaf, ..b'] [closer, ..after2] byComputing)

--| Comment placement on leaves with last commas, with the last commas then dropped, is
--| comment placement on the leaves dropped, for leaves the back-walk, comma carry and arrow lift treat alike.
theorem passesDrop ∀ (leaves dropped: List Leaf) (end: Trivia)
    (rel: DropRel dropped leaves)
    (within: alphabet1 leaves = True)
    (plain: arrowFrom (tokens leaves) = True):
    dropF [] ((letsFrom [] (arrows (commasFrom [] None (homeFrom False [] None leaves) end).leaves)).map trim)
      = (letsFrom [] (arrows (commasFrom [] None (homeFrom False [] None dropped) end).leaves)).map trim
      ∧ (commasFrom [] None (homeFrom False [] None dropped) end).end
        = (commasFrom [] None (homeFrom False [] None leaves) end).end :=
  let r1 := rule1Drop leaves dropped rel (alphabet1Leaves leaves within)
  let (r2, endEq) := rule2Drop (homeFrom False [] None leaves) (homeFrom False [] None dropped) end r1
  let cB := (commasFrom [] None (homeFrom False [] None leaves) end).leaves
  let cA := (commasFrom [] None (homeFrom False [] None dropped) end).leaves
  let tokCommas: tokens cB = tokens leaves :=
    Eq.trans (commasFromTokens [] None (homeFrom False [] None leaves) end) (homeFromTokens False [] None leaves)
  let r3 := rule3Drop cB cA r2 (rewrite tokCommas then plain)
  let (arrowsEq, arrowsBare) := r3
  let tokArrows: tokens (arrows cB) = tokens leaves := Eq.trans (arrowsTokens cB) tokCommas
  let withinArrows: alphabet1 (arrows cB) = True := rewrite tokArrows then within
  let withinArrowsB: (arrows cB).all (leaf => leaf.kind.within1) = True := alphabet1Leaves (arrows cB) withinArrows
  let withinArrowsA: (arrows cA).all (leaf => leaf.kind.within1) = True :=
    rewrite arrowsEq then dropFAll (leaf => leaf.kind.within1) [] (arrows cB) withinArrowsB
  let letsB: letsFrom [] (arrows cB) = arrows cB := letsQuiet1 [] (arrows cB) byComputing withinArrowsB
  let letsA: letsFrom [] (arrows cA) = arrows cA := letsQuiet1 [] (arrows cA) byComputing withinArrowsA
  (rewrite letsB, letsA, arrowsEq then dropFTrim [] [] (arrows cB) byComputing, endEq)

theorem relBare ∀ (leaves: List Leaf): DropRel (withoutLastCommas [] leaves) (withMarkedLastCommas [] leaves) :=
  let (eq, bare) := buildDrop [] leaves byComputing byComputing
  rewrite withoutFromR [] leaves, withMarkedFromR [] leaves then
    dropRelOfRev (withMarkedR [] leaves) (withoutR [] leaves) eq.flipped bare

--| Making the last commas bare keeps every token.
theorem tokensBare ∀ (leaves: List Leaf): tokens (withBareLastCommas [] leaves) = tokens leaves := calc tokens
  (withBareLastCommas [] leaves)
  _ = tokens ((withBareR [] leaves).reverseOnto []) := rewrite withBareFromR [] leaves
  _ = (tokens (withBareR [] leaves)).reverseOnto [] := tokensReverseOnto (withBareR [] leaves) []
  _ = (tokens (leaves.reverseOnto [])).reverseOnto [] := rewrite withBareRTokens [] leaves
  _ = ((tokens leaves).reverseOnto []).reverseOnto [] := rewrite tokensReverseOnto leaves []
  _ = tokens leaves := List.reverseReverse (tokens leaves)

-- Deleting a last comma moves no token, line starts aside: a comma that starts its line gives its line start to the
-- closer after it (`commaDeleted`).

theorem commaDeletedToken ∀ (comma closer: Leaf) (behind: List Leaf):
    (commaDeleted comma closer behind).fst.token
      = { closer.token | lineStart = (comma.token.lineStart || closer.token.lineStart) }
      ∧ tokens (commaDeleted comma closer behind).snd = tokens behind :=
  match comma.trivia.trailing with
    | None => (byComputing, byComputing)
    | Some comment =>
      match behind with
        | [] => (byComputing, byComputing)
        | [previous, ..earlier] =>
          match starts: comma.token.lineStart with
            | True => (byComputing, byComputing)
            | False => (byComputing, byComputing)

theorem commaDeletedKind ∀ (comma closer: Leaf) (behind: List Leaf):
    (commaDeleted comma closer behind).fst.token.kind = closer.token.kind :=
  rewrite (commaDeletedToken comma closer behind).left

theorem commaDeletedFlat ∀ (comma closer: Leaf) (behind: List Leaf):
    flatToken (commaDeleted comma closer behind).fst.token = flatToken closer.token :=
  rewrite (commaDeletedToken comma closer behind).left

theorem flatReverseOnto ∀ (xs a b: List Token)
    (same: a.map flatToken = b.map flatToken):
    (xs.reverseOnto a).map flatToken = (xs.reverseOnto b).map flatToken :=
  rewrite List.mapReverseOnto xs a flatToken, List.mapReverseOnto xs b flatToken, same

--| Marking the last commas changes no token but the line start of a closer after a comma that starts its line.
theorem withMarkedRFlat ∀ (behind rest: List Leaf):
    (tokens (withMarkedR behind rest)).map flatToken = (tokens (rest.reverseOnto behind)).map flatToken :=
  match induct (withMarkedR behind rest) with
    | eq1 _ => byComputing
    | eq2 behind comma closer after _ ih =>
      let (movedToken, movedTokens) := commaDeletedToken comma closer behind
      let accSame: (tokens [
            (commaDeleted comma closer behind).fst,
            { comma | trivia = Trivia.empty },
            ..(commaDeleted comma closer behind).snd
          ]).map flatToken
        = (tokens [closer, comma, ..behind]).map flatToken :=
        rewrite commaDeletedFlat comma closer behind, movedTokens
      rewrite ih,
          tokensReverseOnto after [
            (commaDeleted comma closer behind).fst,
            { comma | trivia = Trivia.empty },
            ..(commaDeleted comma closer behind).snd
          ],
          tokensReverseOnto after [closer, comma, ..behind] then
        flatReverseOnto (tokens after) _ _ accSame
    | eq3 _ _ _ _ ih => ih

theorem tokensMarkedFlat ∀ (leaves: List Leaf):
    (tokens (withMarkedLastCommas [] leaves)).map flatToken = (tokens leaves).map flatToken :=
  calc (tokens (withMarkedLastCommas [] leaves)).map flatToken
    _ = (tokens ((withMarkedR [] leaves).reverseOnto [])).map flatToken := rewrite withMarkedFromR [] leaves
    _ = ((tokens (withMarkedR [] leaves)).reverseOnto []).map flatToken :=
      rewrite tokensReverseOnto (withMarkedR [] leaves) []
    _ = ((tokens (withMarkedR [] leaves)).map flatToken).reverseOnto [] :=
      List.mapReverseOnto (tokens (withMarkedR [] leaves)) [] flatToken
    _ = ((tokens (leaves.reverseOnto [])).map flatToken).reverseOnto [] := rewrite withMarkedRFlat [] leaves
    _ = (((tokens leaves).reverseOnto []).map flatToken).reverseOnto [] := rewrite tokensReverseOnto leaves []
    _ = (((tokens leaves).map flatToken).reverseOnto []).reverseOnto [] :=
      rewrite List.mapReverseOnto (tokens leaves) [] flatToken
    _ = (tokens leaves).map flatToken := List.reverseReverse ((tokens leaves).map flatToken)

--| Comment placement on the leaves with the last commas marked (`withMarkedLastCommas`).
def Lexed.settledMarked (lexed: Lexed): Lexed := { lexed | leaves = withMarkedLastCommas [] lexed.leaves }.settled

--| Comment placement on the leaves with their last commas marked, then the last commas
--| dropped, is comment placement on the leaves without them (S1 sketch §3.4).
--|
--| The statement holds for leaves with the last commas, so under `sourcePlain1` (no `->` before a comma, closer
--| or `->`; no comma that starts its line before a comma or closer, but a last
--| comma; no comma or closer first) and slice 1's alphabet. Only the `->` clause is used.
--| No layout is assumed.
--|
--| Proof idea: the bare last commas change nothing the back-walk, comma carry and arrow lift do to the
--| leaves around them: the back-walk passes one leaf more and never stops on
--| the comma (if it starts its line so does its closer, which stops first), so
--| the comment lands on the same leaf; the comma carry carries nothing from a bare
--| comma; the arrow lift skips it, since no `->` comes before it (`arrowFrom`). So each pass on
--| the leaves with commas, then dropped, is the pass on the leaves without
--| them (`rule1Drop`, `rule2Drop`, `rule3Drop`); the let lift and trim act leaf by leaf.
theorem markedSettles ∀ (lexed: Lexed)
    (within: alphabet1 lexed.leaves = True)
    (plain: sourcePlain1 (tokens lexed.leaves) = True):
    dropF [] lexed.settledMarked.leaves = lexed.settledBare.leaves ∧ lexed.settledMarked.end = lexed.settledBare.end :=
  let arrowF := arrowOfSource False (tokens lexed.leaves) (sourcePlainFromOf (tokens lexed.leaves) plain)
  let tokB := tokensMarkedFlat lexed.leaves
  let (leavesEq, endEq) :=
    passesDrop
      (withMarkedLastCommas [] lexed.leaves)
      (withoutLastCommas [] lexed.leaves)
      lexed.end
      (relBare lexed.leaves)
      (rewrite allFlat (token => token.kind.within1) (token => rewrite flatKind token) _ _ tokB then within)
      (rewrite arrowFromFlat _ _ tokB then arrowF)
  (leavesEq, rewrite endEq)

-- Without a last comma, the leaves are comment placement's own.

--| No leaf from `rest` on is a last comma, `behind` the leaves before.
def noLast (behind rest: List Leaf): Bool := match rest with
  | [] => True
  | [leaf, ..after] => !fwdPair behind leaf after && noLast [leaf, ..behind] after

theorem withBareRNone ∀ (behind rest: List Leaf)
    (none: noLast behind rest = True):
    withBareR behind rest = rest.reverseOnto behind :=
  match induct (withBareR behind rest) with
    | eq1 _ => byComputing
    | eq2 behind comma closer after guard ih =>
      let (isComma, isCloser, item) := guard
      let pair: lastPair closer.token.kind comma behind = True := (isComma, Bool.andIntro isCloser item)
      rewrite pair at none then cases
    | eq3 _ _ _ _ ih => ih (Bool.andRight none)

-- The back-walk with bare last commas (`startsWalk True`) reads a line start
-- other than the token's own only at a closer right after a last comma that
-- starts its line. Where there is none, it is the plain walk.

--| `hasItem`, on the tokens.
def itemT: List Token → Bool
  | [] => False
  | [token, .._] =>
    match token.kind with
      | Comma => False
      | Pipe => False
      | kind => !kind.isOpener

theorem hasItemT ∀ (leaves: List Leaf): hasItem leaves = itemT (tokens leaves) := match leaves with
  | [] | [_, .._] => byComputing

--| No closer in `tokens` (newest first) right after a last comma that starts its line.
def pairFreeT: List Token → Bool
  | [] => True
  | [token, ..older] =>
    match older with
      | [] => True
      | [comma, ..more] =>
        !(token.kind.isCloser && comma.kind == Comma && comma.lineStart && itemT more) && pairFreeT older

theorem pairFreeTail ∀ (token: Token) (older: List Token)
    (free: pairFreeT [token, ..older] = True):
    pairFreeT older = True :=
  match older with
    | [] => byComputing
    | [comma, ..more] => Bool.andRight free

theorem pairFreeSuffix ∀ (xs ys: List Token) (free: pairFreeT (xs.reverseOnto ys) = True): pairFreeT ys = True :=
  match xs with
    | [] => free
    | [x, ..rest] => pairFreeTail x ys (pairFreeSuffix rest [x, ..ys] free)

theorem startsPairFree ∀ (current: Leaf) (behind: List Leaf)
    (free: pairFreeT (tokens [current, ..behind]) = True):
    startsWalk True current behind = current.token.lineStart :=
  match behind with
    | [] => byComputing
    | [previous, ..earlier] =>
      let extraF: (current.kind.isCloser && previous.kind == Comma && previous.token.lineStart && hasItem earlier)
        = False :=
        rewrite hasItemT earlier then Bool.notTrue _ (Bool.andLeft free)
      let unfolded: startsWalk True current [previous, ..earlier]
        = (current.token.lineStart
          || (current.kind.isCloser && previous.kind == Comma && previous.token.lineStart && hasItem earlier)) :=
        byComputing
      Eq.trans unfolded (rewrite extraF then Bool.orFalse current.token.lineStart)

theorem stepsPairFree ∀ (current: Leaf) (behind ahead: List Leaf) (steps: Nat)
    (free: pairFreeT (tokens [current, ..behind]) = True):
    stepsBack True current behind ahead steps = stepsBack False current behind ahead steps :=
  match behind with
    | [] => byComputing
    | [previous, ..earlier] =>
      rewrite startsPairFree current [previous, ..earlier] free,
          stepsPairFree previous earlier
            [current, ..ahead]
            (steps + 1)
            (pairFreeTail current.token (tokens [previous, ..earlier]) free)

--| The back-walk with bare last commas is plain back-walk where no closer follows a last comma that starts its line.
theorem homePairFree ∀ (behind: List Leaf) (bumped: Option Comment) (rest: List Leaf)
    (free: pairFreeT (tokens (rest.reverseOnto behind)) = True):
    homeFrom True behind bumped rest = homeFrom False behind bumped rest :=
  match rest with
    | [] => byComputing
    | [leaf, ..after] =>
      let next := (x: Leaf) (settled: List Leaf) (bump: Option Comment) (same: x.token = leaf.token) (sameBehind: tokens
          settled
        = tokens behind) =>
        let sameAll: tokens (after.reverseOnto [x, ..settled]) = tokens (after.reverseOnto [leaf, ..behind]) :=
          rewrite tokensReverseOnto after [x, ..settled], tokensReverseOnto after [leaf, ..behind], same, sameBehind
        homePairFree [x, ..settled] bump after (rewrite sameAll then free)
      let headFree: pairFreeT (tokens [leaf, ..behind]) = True :=
        pairFreeSuffix
          (tokens after)
          (tokens [leaf, ..behind])
          (rewrite <- tokensReverseOnto after [leaf, ..behind] then free)
      match bumped with
        | None =>
          match trailing: leaf.trivia.trailing with
            | None => next leaf behind None byComputing byComputing
            | Some comment =>
              match movable leaf behind after with
                | False => next leaf behind None byComputing byComputing
                | True =>
                  rewrite stepsPairFree leaf behind after 0 headFree then
                    match stepsBack False leaf behind after 0 with
                      | Zero =>
                        match barBelow leaf behind after with
                          | True => next (leaf.withTrailing None) behind (Some comment.unspaced) byComputing byComputing
                          | False => next leaf behind None byComputing byComputing
                      | Succ more =>
                        next
                          (leaf.withTrailing None)
                          (trailingAt behind (Succ more) comment)
                          None
                          byComputing
                          (trailingAtTokens behind (Succ more) comment)
        | Some bump =>
          let lifted := leaf.withLeading [bump, ..leaf.trivia.leading]
          let liftedFree: pairFreeT (tokens [lifted, ..behind]) = True := headFree
          match lifted.trivia.trailing with
            | None => next lifted behind None byComputing byComputing
            | Some comment =>
              match movable lifted behind after with
                | False => next lifted behind None byComputing byComputing
                | True =>
                  rewrite stepsPairFree lifted behind after 0 liftedFree then
                    match stepsBack False lifted behind after 0 with
                      | Zero =>
                        match barBelow lifted behind after with
                          | True =>
                            next (lifted.withTrailing None) behind (Some comment.unspaced) byComputing byComputing
                          | False => next lifted behind None byComputing byComputing
                      | Succ more =>
                        next
                          (lifted.withTrailing None)
                          (trailingAt behind (Succ more) comment)
                          None
                          byComputing
                          (trailingAtTokens behind (Succ more) comment)

--| Leaves with no last comma before their closers have no closer after one.
theorem pairFreeOfNoLast ∀ (behind rest: List Leaf)
    (none: noLast behind rest = True)
    (gap: gapOk behind rest = True)
    (free: pairFreeT (tokens behind) = True):
    pairFreeT (tokens (rest.reverseOnto behind)) = True :=
  match rest with
    | [] => free
    | [leaf, ..after] =>
      let nop: fwdPair behind leaf after = False := Bool.notTrue _ (Bool.andLeft none)
      let headFree: pairFreeT (tokens [leaf, ..behind]) = True := match behind with
        | [] => byComputing
        | [comma, ..more] =>
          let notPair: lastPair leaf.token.kind comma more = False := Bool.notTrue _ gap
          let extraF: (leaf.token.kind.isCloser
            && comma.token.kind == Comma
            && comma.token.lineStart
            && itemT (tokens more))
            = False :=
            match k: leaf.token.kind.isCloser, c: comma.token.kind == Comma, l: comma.token.lineStart with
              | False, _, _ => byComputing
              | True, False, _ => byComputing
              | True, True, False => byComputing
              | True, True, True => rewrite <- hasItemT more then notPair
          Bool.andIntro (Bool.notOfFalse _ extraF) free
      pairFreeOfNoLast [leaf, ..behind] after (Bool.andRight none) (gapAfterNop leaf behind after nop) headFree

--| With no comma directly before a closer after an item, making the last
--| commas bare changes nothing, so the leaves comment placement settles are `settled`'s:
--| on every text the formatter prints, `parse1` parses what `parse` does.
theorem settledOnceNone ∀ (lexed: Lexed) (none: noLast [] lexed.leaves = True): lexed.settledOnce = lexed.settled :=
  let bare: withBareLastCommas [] lexed.leaves = lexed.leaves :=
    Eq.trans
      (withBareFromR [] lexed.leaves)
      (rewrite withBareRNone [] lexed.leaves none then List.reverseReverse lexed.leaves)
  let free := pairFreeOfNoLast [] lexed.leaves none byComputing byComputing
  rewrite bare, homePairFree [] None lexed.leaves free
