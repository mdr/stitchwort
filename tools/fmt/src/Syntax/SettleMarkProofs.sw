--| Comment placement as the formatter runs it (`settledOnce`: the last commas bare, and the walk reading a closer right after one
--| that starts its line as starting it, `startsWalk True`) against comment placement on the same leaves with that line start
--| written into each such closer's token (`settledMarked`, which `Syntax.SettleBareProofs` relates to the leaves
--| without the last commas): the two differ only in line starts (`onceMarked`). So `settledOnce`, its last commas
--| dropped, holds `settledBare`'s comments (`bareSettles`).

namespace Syntax.SettleMarkProofs
import Std (Bool, Eq, List, Nat, Option, Text, Void)
import Syntax (..)
import Fmt (..)
import Syntax.SettleProofs (..)
import Syntax.SettleBareProofs (..)
import Syntax.SharedFacts (commaNotCloser)

-- Line starts as the back-walk with bare last commas reads them.

--| The leaf, starting its line as the back-walk with bare last commas takes it to, `behind` the leaves before it,
--| newest first.
def Leaf.markedOn (leaf: Leaf) (behind: List Leaf): Leaf := leaf.startingLine (startsWalk True leaf behind)

--| Each leaf of `leaves` (newest first) marked.
def markRev: List Leaf → List Leaf
  | [] => []
  | [leaf, ..older] => [leaf.markedOn older, ..markRev older]

--| Each leaf of `rest` marked, read forwards, `behind` the leaves before them, newest first.
def markFwd (behind rest: List Leaf): List Leaf := match rest with
  | [] => []
  | [leaf, ..after] => [leaf.markedOn behind, ..markFwd [leaf, ..behind] after]

--| The leaf without its line start: leaves compared up to line starts.
def Leaf.unstarted (leaf: Leaf): Leaf := leaf.startingLine False

--| `startsWalk True`, on the tokens.
def startsT (token: Token) (older: List Token): Bool := match older with
  | [] => token.lineStart
  | [comma, ..more] => token.lineStart || (token.kind.isCloser && comma.kind == Comma && comma.lineStart && itemT more)

theorem startsWalkT ∀ (current: Leaf) (behind: List Leaf):
    startsWalk True current behind = startsT current.token (tokens behind) :=
  match behind with
    | [] => byComputing
    | [previous, ..earlier] =>
      let unfolded: startsWalk True current [previous, ..earlier]
        = (current.token.lineStart
          || (current.kind.isCloser && previous.kind == Comma && previous.token.lineStart && hasItem earlier)) :=
        byComputing
      Eq.trans unfolded (rewrite hasItemT earlier)

theorem markedOnTokens ∀ (leaf: Leaf) (one two: List Leaf)
    (same: tokens one = tokens two):
    leaf.markedOn one = leaf.markedOn two :=
  let starts: startsWalk True leaf one = startsWalk True leaf two := calc startsWalk True leaf one
    _ = startsT leaf.token (tokens one) := startsWalkT leaf one
    _ = startsT leaf.token (tokens two) := rewrite same
    _ = startsWalk True leaf two := (startsWalkT leaf two).flipped
  Eq.cong (start => leaf.startingLine start) starts

theorem markFwdTokens ∀ (one two rest: List Leaf)
    (same: tokens one = tokens two):
    markFwd one rest = markFwd two rest :=
  match rest with
    | [] => byComputing
    | [leaf, ..after] =>
      let head := markedOnTokens leaf one two same
      let tail := markFwdTokens [leaf, ..one] [leaf, ..two] after (Eq.cong (list => [leaf.token, ..list]) same)
      rewrite head, tail

theorem markRevReverse ∀ (done rest: List Leaf):
    (markRev done).reverseOnto (markFwd done rest) = markFwd [] (done.reverseOnto rest) :=
  match done with
    | [] => byComputing
    | [leaf, ..older] => markRevReverse older [leaf, ..rest]

theorem leafEta ∀ (leaf: Leaf): leaf.startingLine leaf.token.lineStart = leaf := match leaf with
  | { token, trivia } => rewrite tokenEta token

theorem markedTrailing ∀ (leaf: Leaf) (behind: List Leaf) (trailing: Option Comment):
    (leaf.markedOn behind).withTrailing trailing = (leaf.withTrailing trailing).markedOn behind :=
  match behind with | [] | [_, .._] => byComputing

theorem markRevTrailingAt ∀ (behind: List Leaf) (steps: Nat) (comment: Comment):
    markRev (trailingAt behind steps comment) = trailingAt (markRev behind) steps comment :=
  match behind, steps with
    | [], _ => byComputing
    | [leaf, ..earlier], Zero => byComputing
    | [leaf, ..earlier], Succ Zero => rewrite markedTrailing leaf earlier (Some comment)
    | [leaf, ..earlier], Succ (Succ more) =>
      rewrite markedOnTokens leaf
            (trailingAt earlier (Succ more) comment)
            earlier
            (trailingAtTokens earlier (Succ more) comment),
          markRevTrailingAt earlier (Succ more) comment

theorem markRevEmpty ∀ (behind: List Leaf): (markRev behind).isEmpty = behind.isEmpty := match behind with
  | [] | [_, .._] => byComputing

theorem endsOnMark ∀ (behind: List Leaf): endsOn (markRev behind) = endsOn behind := match behind with
  | [] => byComputing
  | [leaf, ..older] => rewrite markRevEmpty older, endsOnMark older

theorem markRevWithin ∀ (behind: List Leaf)
    (within: behind.all (leaf => leaf.kind.within1) = True):
    (markRev behind).all (leaf => leaf.kind.within1) = True :=
  match behind with
    | [] => byComputing
    | [leaf, ..older] => Bool.andIntro (Bool.andLeft within) (markRevWithin older (Bool.andRight within))

theorem hasItemMark ∀ (behind: List Leaf): hasItem (markRev behind) = hasItem behind := match behind with
  | [] | [_, .._] => byComputing

theorem fwdPairMark ∀ (behind: List Leaf) (leaf: Leaf) (after: List Leaf):
    fwdPair (markRev behind) leaf after = fwdPair behind leaf after :=
  match after with
    | [] => byComputing
    | [closer, ..more] => rewrite hasItemMark behind

--| A leaf that is no closer starts its line as its token says.
theorem startsNotCloser ∀ (leaf: Leaf) (behind: List Leaf)
    (notCloser: leaf.kind.isCloser = False):
    startsWalk True leaf behind = leaf.token.lineStart :=
  match behind with
    | [] => byComputing
    | [previous, ..earlier] =>
      let unfolded: startsWalk True leaf [previous, ..earlier]
        = (leaf.token.lineStart
          || (leaf.kind.isCloser && previous.kind == Comma && previous.token.lineStart && hasItem earlier)) :=
        byComputing
      Eq.trans unfolded (rewrite notCloser then Bool.orFalse leaf.token.lineStart)

--| A closer after a comma that isn't a last comma starts its line as its token says.
theorem startsNoPair ∀ (leaf comma: Leaf) (older: List Leaf)
    (notPair: lastPair leaf.token.kind comma older = False):
    startsWalk True leaf [comma, ..older] = leaf.token.lineStart :=
  let unfolded: startsWalk True leaf [comma, ..older]
    = (leaf.token.lineStart
      || (leaf.token.kind.isCloser && comma.token.kind == Comma && comma.token.lineStart && hasItem older)) :=
    byComputing
  let extraF: (leaf.token.kind.isCloser && comma.token.kind == Comma && comma.token.lineStart && hasItem older)
    = False :=
    match k: leaf.token.kind.isCloser, c: comma.token.kind == Comma, l: comma.token.lineStart with
      | False, _, _ => byComputing
      | True, False, _ => byComputing
      | True, True, False => byComputing
      | True, True, True => notPair
  Eq.trans unfolded (rewrite extraF then Bool.orFalse leaf.token.lineStart)

-- The back-walk, with bare last commas and with marked ones.

--| The back-walk on marked leaves by their tokens' line starts is its walk on the bare ones with bare last commas.
theorem walkMark ∀ (current: Leaf) (behind ahead ahead2: List Leaf) (steps: Nat)
    (within: current.kind.within1 = True)
    (behindWithin: behind.all (leaf => leaf.kind.within1) = True):
    stepsBack False (current.markedOn behind) (markRev behind) ahead2 steps
      = stepsBack True current behind ahead steps :=
  match behind with
    | [] => byComputing
    | [previous, ..earlier] =>
      let marked := current.markedOn [previous, ..earlier]
      let skipsM: skipped marked (markRev [previous, ..earlier]) ahead2
        = (marked.kind == Comma || marked.kind.isCloser) :=
        skippedQuiet1 marked (markRev [previous, ..earlier]) ahead2 within
      let skips: skipped current [previous, ..earlier] ahead = (current.kind == Comma || current.kind.isCloser) :=
        skippedQuiet1 current [previous, ..earlier] ahead within
      let endsM: endsWithComment (markRev [previous, ..earlier]) [marked, ..ahead2] = endsOn [previous, ..earlier] :=
        Eq.trans
          (endsOnQuiet1
            (markRev [previous, ..earlier])
            [marked, ..ahead2]
            (markRevWithin [previous, ..earlier] behindWithin))
          (endsOnMark [previous, ..earlier])
      let ends: endsWithComment [previous, ..earlier] [current, ..ahead] = endsOn [previous, ..earlier] :=
        endsOnQuiet1 [previous, ..earlier] [current, ..ahead] behindWithin
      rewrite skipsM,
          skips,
          endsM,
          ends,
          walkMark previous earlier
            [current, ..ahead]
            [marked, ..ahead2]
            (steps + 1)
            (Bool.andLeft behindWithin)
            (Bool.andRight behindWithin)

theorem movableMark ∀ (leaf: Leaf) (behind ahead ahead2: List Leaf)
    (within: leaf.kind.within1 = True):
    movable (leaf.markedOn behind) (markRev behind) ahead2 = movable leaf behind ahead :=
  let marked := leaf.markedOn behind
  rewrite movableQuiet1 marked (markRev behind) ahead2 within, movableQuiet1 leaf behind ahead within then
    match closer: leaf.kind.isCloser with
      | True => Eq.trans (Bool.orTrue _) (Bool.orTrue _).flipped
      | False => rewrite startsNotCloser leaf behind closer

--| The back-walk on marked leaves by their tokens' line starts gives the marked result of the back-walk on the bare ones with bare
--| last commas.
--|
--| Proof idea: by induction on the leaves to come, keeping the leaves done (newest first) marked: each step reads
--| the same trailing comment, the same `movable` (a leaf whose mark changes is a closer, movable either way) and the
--| same walk (`walkMark`), and the leaves it pushes are marked as the bare ones are, since marking reads only tokens
--| (`markRevTrailingAt`, `markedTrailing`).
theorem homeMark ∀ (behind rest: List Leaf)
    (behindWithin: behind.all (leaf => leaf.kind.within1) = True)
    (within: rest.all (leaf => leaf.kind.within1) = True):
    homeFrom False (markRev behind) None (markFwd behind rest) = markFwd [] (homeFrom True behind None rest) :=
  match rest with
    | [] => markRevReverse behind []
    | [leaf, ..after] =>
      let leafWithin: leaf.kind.within1 = True := Bool.andLeft within
      let afterWithin := Bool.andRight within
      let next := (pushed marked: List Leaf) (markedEq: marked = markRev pushed) (sameTokens: tokens pushed
        = tokens [leaf, ..behind]) (pushedWithin: pushed.all (leaf => leaf.kind.within1) = True) =>
        let fwd: markFwd [leaf, ..behind] after = markFwd pushed after :=
          markFwdTokens [leaf, ..behind] pushed after sameTokens.flipped
        let claim: homeFrom False marked None (markFwd [leaf, ..behind] after)
          = markFwd [] (homeFrom True pushed None after) :=
          rewrite markedEq, fwd then homeMark pushed after pushedWithin afterWithin
        claim
      let marked := leaf.markedOn behind
      let pushedWithin: [leaf, ..behind].all (leaf => leaf.kind.within1) = True := Bool.andIntro leafWithin behindWithin
      match trailing: leaf.trivia.trailing with
        | None => next [leaf, ..behind] [marked, ..markRev behind] byComputing byComputing pushedWithin
        | Some comment =>
          rewrite movableMark leaf behind after (markFwd [leaf, ..behind] after) leafWithin then
            match mov: movable leaf behind after with
              | False => next [leaf, ..behind] [marked, ..markRev behind] byComputing byComputing pushedWithin
              | True =>
                rewrite walkMark leaf behind after (markFwd [leaf, ..behind] after) 0 leafWithin behindWithin then
                  match walk: stepsBack True leaf behind after 0 with
                    | Zero =>
                      rewrite barsQuiet1 marked (markRev behind) (markFwd [leaf, ..behind] after) leafWithin,
                          barsQuiet1 leaf behind after leafWithin then
                        next [leaf, ..behind] [marked, ..markRev behind] byComputing byComputing pushedWithin
                    | Succ more =>
                      let target := trailingAt behind (Succ more) comment
                      let targetTokens: tokens target = tokens behind := trailingAtTokens behind (Succ more) comment
                      let markedEq: [marked.withTrailing None, ..trailingAt (markRev behind) (Succ more) comment]
                        = markRev [leaf.withTrailing None, ..target] :=
                        rewrite markedTrailing leaf behind None,
                            markedOnTokens (leaf.withTrailing None) target behind targetTokens,
                            markRevTrailingAt behind (Succ more) comment
                      next
                        [leaf.withTrailing None, ..target]
                        [marked.withTrailing None, ..trailingAt (markRev behind) (Succ more) comment]
                        markedEq
                        (rewrite targetTokens)
                        (Bool.andIntro leafWithin (withinOfTokens target behind targetTokens behindWithin))

theorem markFwdUnstarted ∀ (behind rest: List Leaf):
    (markFwd behind rest).map Leaf.unstarted = rest.map Leaf.unstarted :=
  match rest with
    | [] => byComputing
    | [leaf, ..after] => rewrite markFwdUnstarted [leaf, ..behind] after

-- The last commas, marked.

theorem commaMovedFstAny ∀ (comma closer: Leaf) (one two: List Leaf):
    (commaMoved comma closer one).fst = (commaMoved comma closer two).fst :=
  cases comma, one, two then byComputing

theorem commaMovedSndMark ∀ (comma closer: Leaf) (behind: List Leaf):
    (commaMoved comma closer (markRev behind)).snd = markRev (commaMoved comma closer behind).snd :=
  match trailing: comma.trivia.trailing with
    | None => byComputing
    | Some comment =>
      match behind with
        | [] => byComputing
        | [previous, ..earlier] =>
          match starts: comma.token.lineStart with
            | True => byComputing
            | False => rewrite markedTrailing previous earlier (Some comment)

theorem markedGap ∀ (leaf: Leaf) (behind after: List Leaf)
    (gap: gapOk behind [leaf, ..after] = True):
    leaf.markedOn behind = leaf :=
  match behind with
    | [] => leafEta leaf
    | [comma, ..older] =>
      let starts := startsNoPair leaf comma older (Bool.notTrue _ gap)
      Eq.trans (Eq.cong (start => leaf.startingLine start) starts) (leafEta leaf)

--| Marking the bare last commas' closers gives the leaves with the last commas marked.
theorem markedBareR ∀ (behind rest: List Leaf)
    (gap: gapOk behind rest = True):
    withMarkedR (markRev behind) rest = markRev (withBareR behind rest) :=
  match induct (withBareR behind rest) with
    | eq1 _ => byComputing
    | eq2 behind comma closer after guard ih =>
      let pair: lastPair closer.token.kind comma behind = True :=
        let (isComma, isCloser, item) := guard
        (isComma, Bool.andIntro isCloser item)
      let pairM: lastPair closer.token.kind comma (markRev behind) = True :=
        rewrite fwdPairMark behind comma [closer, ..after] then pair
      let moved := commaMoved comma closer behind
      let bare := { comma | trivia = Trivia.empty }
      let (fstTok, sndToks) := commaMovedTokens comma closer behind
      let isComma: (comma.token.kind == Comma) = True := Bool.andLeft pair
      let isCloser: closer.token.kind.isCloser = True := Bool.andLeft (Bool.andRight pair)
      let item: hasItem behind = True := Bool.andRight (Bool.andRight pair)
      let itemMoved: hasItem moved.snd = True := rewrite hasItemT moved.snd, sndToks, <- hasItemT behind then item
      let pair2: lastPair moved.fst.token.kind bare moved.snd = True :=
        rewrite fstTok, itemMoved then Bool.andIntro isComma (Bool.andIntro isCloser byComputing)
      let barePlain: bare.markedOn moved.snd = bare :=
        Eq.trans
          (Eq.cong
            (start => bare.startingLine start)
            (startsNotCloser bare moved.snd (commaNotCloser comma.token.kind isComma)))
          (leafEta bare)
      let startsMoved: startsWalk True moved.fst [bare, ..moved.snd]
        = (comma.token.lineStart || closer.token.lineStart) :=
        let unfolded: startsWalk True moved.fst [bare, ..moved.snd]
          = (moved.fst.token.lineStart
            || (moved.fst.token.kind.isCloser
              && bare.token.kind == Comma
              && bare.token.lineStart
              && hasItem moved.snd)) :=
          byComputing
        Eq.trans unfolded
          (rewrite fstTok, isCloser, isComma, itemMoved then
            match l: comma.token.lineStart, c: closer.token.lineStart with
              | True, True => byComputing
              | True, False => byComputing
              | False, True => byComputing
              | False, False => byComputing)
      let fstEq: (commaDeleted comma closer (markRev behind)).fst = moved.fst.markedOn [bare, ..moved.snd] :=
        rewrite commaMovedFstAny comma closer (markRev behind) behind then
          Eq.cong (start => moved.fst.startingLine start) startsMoved.flipped
      let accEq: [
        (commaDeleted comma closer (markRev behind)).fst,
        bare,
        ..(commaDeleted comma closer (markRev behind)).snd
      ]
        = markRev [moved.fst, bare, ..moved.snd] :=
        rewrite fstEq, barePlain, commaMovedSndMark comma closer behind
      rewrite withMarkedR.eq2 (markRev behind) comma closer after pairM then
        Eq.trans (Eq.cong (acc => withMarkedR acc after) accEq) (ih (gapAfterPair bare moved.fst moved.snd after pair2))
    | eq3 behind leaf after notArm2 ih =>
      let pair := fwdPairOfNotArm leaf behind after notArm2
      let pairM: fwdPair (markRev behind) leaf after = False := rewrite fwdPairMark behind leaf after then pair
      let same: leaf.markedOn behind = leaf := markedGap leaf behind after gap
      let swap: withMarkedR [leaf, ..markRev behind] after
        = withMarkedR [leaf.markedOn behind, ..markRev behind] after :=
        Eq.cong (x => withMarkedR [x, ..markRev behind] after) same.flipped
      rewrite withMarkedR.eq3 (markRev behind) leaf after (notArmOfFwdPair leaf (markRev behind) after pairM) then
        Eq.trans swap (ih (gapAfterNop leaf behind after pair))

theorem markedOfBare ∀ (leaves: List Leaf):
    withMarkedLastCommas [] leaves = markFwd [] (withBareLastCommas [] leaves) :=
  rewrite withMarkedFromR [] leaves, withBareFromR [] leaves then
    calc (withMarkedR [] leaves).reverse
      _ = (markRev (withBareR [] leaves)).reverse := rewrite markedBareR [] leaves byComputing
      _ = markFwd [] (withBareR [] leaves).reverse := markRevReverse (withBareR [] leaves) []

-- The comma carry, arrow lift, let lift and trim read no line start.

theorem commasUnstarted ∀ (done: List Leaf) (carried: Option Carried) (rest: List Leaf) (end: Trivia):
    (commasFrom (done.map Leaf.unstarted) carried (rest.map Leaf.unstarted) end).leaves
      = (commasFrom done carried rest end).leaves.map Leaf.unstarted
      ∧ (commasFrom (done.map Leaf.unstarted) carried (rest.map Leaf.unstarted) end).end
        = (commasFrom done carried rest end).end :=
  match rest with
    | [] =>
      let leavesEq: (done.map Leaf.unstarted).reverse = done.reverse.map Leaf.unstarted :=
        (List.mapReverse done Leaf.unstarted).flipped
      let endEq: (commasFrom (done.map Leaf.unstarted) carried [] end).end = (commasFrom done carried [] end).end :=
        byComputing
      (leavesEq, endEq)
    | [leaf, ..after] =>
      let step := (x: Leaf) (next: Option Carried) => commasUnstarted [x, ..done] next after end
      match carried with
        | None =>
          match commaCarries leaf.trivia with
            | None => step leaf None
            | Some carry =>
              match leaf.kind == Comma with
                | True => step { leaf | trivia = Trivia.empty } (Some carry)
                | False => step leaf None
        | Some held =>
          let received := { leaf | trivia = held.into leaf.trivia }
          match commaCarries received.trivia with
            | None => step received None
            | Some carry =>
              match leaf.kind == Comma with
                | True => step { leaf | trivia = Trivia.empty } (Some carry)
                | False => step received None

theorem arrowsFromUnstarted ∀ (done: List Leaf) (current: Leaf) (rest: List Leaf):
    arrowsFrom (done.map Leaf.unstarted) current.unstarted (rest.map Leaf.unstarted)
      = (arrowsFrom done current rest).map Leaf.unstarted :=
  match rest with
    | [] => rewrite List.mapReverse [current, ..done] Leaf.unstarted
    | [next, ..more] =>
      match current.kind == Arrow && (!next.trivia.leading.isEmpty || current.trivia.trailing.isSome) with
        | True =>
          let moved := { current |
            trivia = { current.trivia |
              leading = current.trivia.leading
                ++ (current.trivia.trailing.map (comment => [comment.unspaced]) |> .getOrElse [])
                ++ next.trivia.leading,
              trailing = None
            }
          }
          arrowsFromUnstarted [moved, ..done] (next.withLeading []) more
        | False => arrowsFromUnstarted [current, ..done] next more

theorem arrowsUnstarted ∀ (leaves: List Leaf):
    arrows (leaves.map Leaf.unstarted) = (arrows leaves).map Leaf.unstarted :=
  match leaves with
    | [] => byComputing
    | [first, ..rest] => arrowsFromUnstarted [] first rest

theorem letBeforeUnstarted ∀ (behind: List Leaf) (depth: Nat):
    letBefore (behind.map Leaf.unstarted) depth = letBefore behind depth :=
  match behind with
    | [] => byComputing
    | [leaf, ..earlier] =>
      match leaf.kind.isCloser with
        | True => letBeforeUnstarted earlier (depth + 1)
        | False =>
          match leaf.kind.isOpener with
            | True => rewrite letBeforeUnstarted earlier (depth - 1)
            | False =>
              match depth > 0 with
                | True => letBeforeUnstarted earlier depth
                | False =>
                  match leaf.kind == KwLet with
                    | True => byComputing
                    | False =>
                      match leaf.kind == Semi || leaf.kind == FatArrow || leaf.kind.startsDeclaration with
                        | True => byComputing
                        | False => letBeforeUnstarted earlier depth

theorem semicolonAfterUnstarted ∀ (ahead: List Leaf) (depth: Nat):
    semicolonAfter (ahead.map Leaf.unstarted) depth = semicolonAfter ahead depth :=
  match ahead with
    | [] => byComputing
    | [leaf, ..later] =>
      match leaf.kind.isOpener with
        | True => semicolonAfterUnstarted later (depth + 1)
        | False =>
          match leaf.kind.isCloser with
            | True => rewrite semicolonAfterUnstarted later (depth - 1)
            | False =>
              match leaf.kind == Semi && depth == 0 with
                | True => byComputing
                | False => semicolonAfterUnstarted later depth

theorem letsFromUnstarted ∀ (behind rest: List Leaf):
    letsFrom (behind.map Leaf.unstarted) (rest.map Leaf.unstarted) = (letsFrom behind rest).map Leaf.unstarted :=
  match rest with
    | [] => rewrite List.mapReverse behind Leaf.unstarted
    | [leaf, ..after] =>
      match leaf.trivia.trailing with
        | None => letsFromUnstarted [leaf, ..behind] after
        | Some comment =>
          rewrite letBeforeUnstarted behind 0, semicolonAfterUnstarted after 0 then
            match leaf.kind == ColonEq && letBefore behind 0 && semicolonAfter after 0 with
              | True =>
                let moved := { leaf |
                  trivia = { leaf.trivia | leading = leaf.trivia.leading ++ [comment.unspaced], trailing = None }
                }
                letsFromUnstarted [moved, ..behind] after
              | False => letsFromUnstarted [leaf, ..behind] after

theorem trimUnstarted ∀ (leaves: List Leaf):
    (leaves.map Leaf.unstarted).map (leaf => { leaf | trivia = leaf.trivia.trimmed })
      = (leaves.map (leaf => { leaf | trivia = leaf.trivia.trimmed })).map Leaf.unstarted :=
  match leaves with
    | [] => byComputing
    | [leaf, ..rest] => rewrite trimUnstarted rest

--| The comma carry, arrow lift, let lift and trim, on leaves the same up to line starts.
def laterPasses (leaves: List Leaf) (end: Trivia): List Leaf :=
  (letsFrom [] (arrows (commasFrom [] None leaves end).leaves)).map (leaf => { leaf | trivia = leaf.trivia.trimmed })

--| The comma carry, arrow lift, let lift and trim on leaves the same up to line starts give leaves the same up to line starts, and the same end.
theorem passesUnstarted ∀ (one two: List Leaf) (end: Trivia)
    (same: one.map Leaf.unstarted = two.map Leaf.unstarted):
    (laterPasses one end).map Leaf.unstarted = (laterPasses two end).map Leaf.unstarted
      ∧ (commasFrom [] None one end).end = (commasFrom [] None two end).end :=
  let (oneLeaves, oneEnd) := commasUnstarted [] None one end
  let (twoLeaves, twoEnd) := commasUnstarted [] None two end
  let commasSame: (commasFrom [] None one end).leaves.map Leaf.unstarted
    = (commasFrom [] None two end).leaves.map Leaf.unstarted :=
    calc (commasFrom [] None one end).leaves.map Leaf.unstarted
      _ = (commasFrom [] None (one.map Leaf.unstarted) end).leaves := oneLeaves.flipped
      _ = (commasFrom [] None (two.map Leaf.unstarted) end).leaves := rewrite same
      _ = (commasFrom [] None two end).leaves.map Leaf.unstarted := twoLeaves
  let letsOf: ∀ (leaves: List Leaf) => (letsFrom [] (arrows leaves)).map Leaf.unstarted
    = letsFrom [] (arrows (leaves.map Leaf.unstarted)) :=
    leaves => rewrite arrowsUnstarted leaves then (letsFromUnstarted [] (arrows leaves)).flipped
  let leavesEq: (laterPasses one end).map Leaf.unstarted = (laterPasses two end).map Leaf.unstarted :=
    rewrite <- trimUnstarted (letsFrom [] (arrows (commasFrom [] None one end).leaves)),
        <- trimUnstarted (letsFrom [] (arrows (commasFrom [] None two end).leaves)),
        letsOf (commasFrom [] None one end).leaves,
        letsOf (commasFrom [] None two end).leaves,
        commasSame
  let endEq: (commasFrom [] None one end).end = (commasFrom [] None two end).end := calc (commasFrom [] None one
      end).end
    _ = (commasFrom [] None (one.map Leaf.unstarted) end).end := oneEnd.flipped
    _ = (commasFrom [] None (two.map Leaf.unstarted) end).end := rewrite same
    _ = (commasFrom [] None two end).end := twoEnd
  (leavesEq, endEq)

-- Comment placement.

--| Comment placement as the formatter runs it, with the last commas bare, gives the leaves of comment placement on the leaves with the last
--| commas marked, up to line starts, and the same end.
theorem onceMarked ∀ (lexed: Lexed)
    (within: alphabet1 lexed.leaves = True):
    lexed.settledOnce.leaves.map Leaf.unstarted = lexed.settledMarked.leaves.map Leaf.unstarted
      ∧ lexed.settledOnce.end = lexed.settledMarked.end :=
  let bare := withBareLastCommas [] lexed.leaves
  let bareWithin: bare.all (leaf => leaf.kind.within1) = True :=
    withinOfTokens bare lexed.leaves (tokensBare lexed.leaves) (alphabet1Leaves lexed.leaves within)
  let homedNew := homeFrom True [] None bare
  let homedOld := homeFrom False [] None (withMarkedLastCommas [] lexed.leaves)
  let homedEq: homedOld = markFwd [] homedNew :=
    rewrite markedOfBare lexed.leaves then homeMark [] bare byComputing bareWithin
  let homedSame: homedNew.map Leaf.unstarted = homedOld.map Leaf.unstarted :=
    rewrite homedEq, markFwdUnstarted [] homedNew
  let (leavesEq, endEq) := passesUnstarted homedNew homedOld lexed.end homedSame
  (leavesEq, Eq.cong (trivia => trivia.trimmed) endEq)

--| Comment placement on the leaves with their last commas made bare, then the last commas dropped, is comment placement on the leaves
--| without them (`settledBare`), up to line starts: the leaves the formatter parses, less the commas the P2 pass
--| deletes, hold the comments `settledBare` holds, with the same end (S1 sketch §3.4).
--|
--| Under slice 1's alphabet and `sourcePlain1`, as `markedSettles`. The line starts differ only at a closer after a
--| last comma that starts its line: deleting the comma from the text, as `settledBare` does, makes the closer start
--| it; the formatter keeps the comma and the token, and comment placement reads the closer as starting the line instead.
--|
--| Proof idea: `settledOnce` is `settledMarked` up to line starts (`onceMarked`), and `markedSettles` relates that to
--| `settledBare`; dropping the last commas reads only kinds, so it keeps leaves the same up to line starts.
theorem bareSettles ∀ (lexed: Lexed)
    (within: alphabet1 lexed.leaves = True)
    (plain: sourcePlain1 (tokens lexed.leaves) = True):
    (dropF [] lexed.settledOnce.leaves).map Leaf.unstarted = lexed.settledBare.leaves.map Leaf.unstarted
      ∧ lexed.settledOnce.end = lexed.settledBare.end :=
  let (onceLeaves, onceEnd) := onceMarked lexed within
  let (markedLeaves, markedEnd) := markedSettles lexed within plain
  let leavesEq: (dropF [] lexed.settledOnce.leaves).map Leaf.unstarted = lexed.settledBare.leaves.map Leaf.unstarted :=
    calc (dropF [] lexed.settledOnce.leaves).map Leaf.unstarted
      _ = dropF [] (lexed.settledOnce.leaves.map Leaf.unstarted) := (dropFUnstarted [] lexed.settledOnce.leaves).flipped
      _ = dropF [] (lexed.settledMarked.leaves.map Leaf.unstarted) := rewrite onceLeaves
      _ = (dropF [] lexed.settledMarked.leaves).map Leaf.unstarted := dropFUnstarted [] lexed.settledMarked.leaves
      _ = lexed.settledBare.leaves.map Leaf.unstarted := rewrite markedLeaves
  (leavesEq, Eq.trans onceEnd markedEnd)

theorem dropFUnstarted ∀ (behind rest: List Leaf):
    dropF (behind.map Leaf.unstarted) (rest.map Leaf.unstarted) = (dropF behind rest).map Leaf.unstarted :=
  match rest with
    | [] => byComputing
    | [leaf, ..after] =>
      match after with
        | [] => byComputing
        | [closer, ..after2] =>
          let itemSame: hasItem (behind.map Leaf.unstarted) = hasItem behind := cases behind then byComputing
          rewrite itemSame then
            match pair: lastPair closer.token.kind leaf behind with
              | True => rewrite dropFUnstarted [closer, leaf, ..behind] after2
              | False => rewrite dropFUnstarted [leaf, ..behind] [closer, ..after2]
