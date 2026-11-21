--| Proofs about `settledOnce` (`Syntax/Settle.sw`): the leaves the formatter parses are settled, read as words
--| (SW-4022, `onceWordsSettled1`).

namespace Syntax.SettleOnceProofs
import Std (Bool, Char, DecEq, Eq, List, Nat, Option, Text)
import Syntax (..)
import Fmt (..)
import Syntax.SettleProofs (
  alphabet1,
  alphabet1Leaves,
  arrowFrom,
  bareComma,
  endsOn,
  homedBehind,
  homedLeaf,
  leavesTextsSplit,
  laidOut,
  lexedTexts,
  arrowFollow,
  backOk,
  leafTexts,
  optionText,
  passable,
  passableKind,
  plain1,
  plainFrom,
  plainFromOf,
  flatToken,
  itemKind,
  settledArrowsBare1,
  settledCommasBare,
  settledHomed,
  settledKeepsComments,
  settledKeepsTokens,
  sourcePlain1,
  sourcePlainFrom,
  sourcePlainFromOf,
  stopsAt,
  tokens,
  tokensReverseOnto,
  triviaTexts
)
import Syntax.SettleBareProofs (..)
import Syntax.SettleMarkProofs (..)

--| What `commaDeleted` leaves behind a last comma that doesn't start its line: a trailing comment goes to the
--| leaf before.
def parked (trailing: Option Comment) (behind: List Leaf): List Leaf := match trailing, behind with
  | Some comment, [previous, ..earlier] => [previous.withTrailing (Some comment), ..earlier]
  | _, _ => behind

theorem commaDeletedPlain ∀ (comma closer: Leaf) (behind: List Leaf)
    (nostart: comma.token.lineStart = False)
    (nolead: comma.trivia.leading = []):
    (commaDeleted comma closer behind).fst = closer
      ∧ (commaDeleted comma closer behind).snd = parked comma.trivia.trailing behind :=
  match closer with
    | { token = closerToken, trivia = closerTrivia } =>
      match closerTrivia with
        | { leading = closerLeading, blankLines = closerBlank, trailing = closerTrailing } =>
          match closerToken with
            | { kind, text, column, lineStart } =>
              match comma with
                | { token = commaToken, trivia = commaTrivia } =>
                  match commaTrivia with
                    | { leading = commaLeading, blankLines = commaBlank, trailing = commaTrailing } =>
                      match commaToken with
                        | { kind = commaKind, text = commaText, column = commaColumn, lineStart = commaStart } =>
                          rewrite nostart, nolead then
                            match closerLeading with
                              | [] =>
                                match commaTrailing with
                                  | None => (byComputing, byComputing)
                                  | Some comment =>
                                    match behind with
                                      | [] => (byComputing, byComputing)
                                      | [previous, ..earlier] => (byComputing, byComputing)
                              | [first, ..others] =>
                                match commaTrailing with
                                  | None => (byComputing, byComputing)
                                  | Some comment =>
                                    match behind with
                                      | [] => (byComputing, byComputing)
                                      | [previous, ..earlier] => (byComputing, byComputing)

-- Leaves laid out, read newest first.

--| Whether the newest leaf has a trailing comment: what the next leaf is laid out after.
def pendB: List Leaf → Bool
  | [] => False
  | [leaf, .._] => leaf.trivia.trailing.isSome

--| `laidOut`, newest leaf first: each leaf with own-line comments, or after a trailing comment, starts its line.
def laidBack: List Leaf → Bool
  | [] => True
  | [leaf, ..older] =>
    (leaf.trivia.leading.isEmpty || leaf.token.lineStart) && (!pendB older || leaf.token.lineStart) && laidBack older

theorem laidNop ∀ (leaf: Leaf) (behind after: List Leaf)
    (back: laidBack behind = True)
    (fwd: laidOut (pendB behind) [leaf, ..after] = True):
    laidBack [leaf, ..behind] = True ∧ laidOut (pendB [leaf, ..behind]) after = True :=
  (
    Bool.andIntro (Bool.andLeft fwd) (Bool.andIntro (Bool.andLeft (Bool.andRight fwd)) back),
    Bool.andRight (Bool.andRight fwd)
  )

theorem laidParkedBack ∀ (previous: Leaf) (tail: List Leaf) (trailing: Option Comment):
    laidBack [previous.withTrailing trailing, ..tail] = laidBack [previous, ..tail] :=
  match previous with
    | { token, trivia } =>
      match trivia with
        | { leading, blankLines, trailing = old } => byComputing

theorem laidPair ∀ (comma closer previous: Leaf) (tail after: List Leaf)
    (nostart: comma.token.lineStart = False)
    (back: laidBack [previous, ..tail] = True)
    (fwd: laidOut (pendB [previous, ..tail]) [comma, closer, ..after] = True):
    laidBack [closer, ..parked comma.trivia.trailing [previous, ..tail]] = True
      ∧ laidOut (pendB [closer, ..parked comma.trivia.trailing [previous, ..tail]]) after = True :=
  let commaOk := Bool.andLeft fwd
  let commaPending := Bool.andLeft (Bool.andRight fwd)
  let closerPart := Bool.andRight (Bool.andRight fwd)
  let closerLead := Bool.andLeft closerPart
  let closerPending := Bool.andLeft (Bool.andRight closerPart)
  let closerRest := Bool.andRight (Bool.andRight closerPart)
  let noPending: previous.trivia.trailing.isSome = False :=
    Bool.notOrFalse previous.trivia.trailing.isSome (rewrite nostart at commaPending then commaPending)
  match trailing: comma.trivia.trailing with
    | None => (Bool.andIntro closerLead (Bool.andIntro (rewrite noPending) back), closerRest)
    | Some comment =>
      let closerStarts: closer.token.lineStart = True := closerPending
      (
        Bool.andIntro closerLead
          (Bool.andIntro (rewrite closerStarts) (rewrite laidParkedBack previous tail (Some comment) then back)),
        closerRest
      )

--| What `commaDeleted` leaves behind for a last comma that starts its line: the leaves before it, untouched.
theorem commaDeletedStartsSnd ∀ (comma closer: Leaf) (behind: List Leaf)
    (starts: comma.token.lineStart = True):
    (commaDeleted comma closer behind).snd = behind :=
  match comma.trivia.trailing with
    | None => byComputing
    | Some comment =>
      match behind with
        | [] => byComputing
        | [previous, ..earlier] =>
          match comma.token.lineStart with
            | True => byComputing

--| The closer after a last comma keeps its own trailing comment.
theorem commaDeletedTrailing ∀ (comma closer: Leaf) (behind: List Leaf):
    (commaDeleted comma closer behind).fst.trivia.trailing = closer.trivia.trailing :=
  match comma.trivia.trailing with
    | None => byComputing
    | Some comment =>
      match behind with
        | [] => byComputing
        | [previous, ..earlier] =>
          match comma.token.lineStart with
            | True => byComputing
            | False => byComputing

--| Laid out stays laid out through the move of a last comma that starts its line: the closer then starts its line
--| and holds the comma's comments, and the leaf before is untouched.
theorem laidMovedStarts ∀ (comma closer previous: Leaf) (tail after: List Leaf)
    (starts: comma.token.lineStart = True)
    (back: laidBack [previous, ..tail] = True)
    (fwd: laidOut (pendB [previous, ..tail]) [comma, closer, ..after] = True):
    laidBack [(commaDeleted comma closer [previous, ..tail]).fst, ..(commaDeleted comma closer [previous, ..tail]).snd]
      = True
      ∧ laidOut
        (pendB [
          (commaDeleted comma closer [previous, ..tail]).fst,
          ..(commaDeleted comma closer [previous, ..tail]).snd
        ])
        after
        = True :=
  let (tok, _) := commaDeletedToken comma closer [previous, ..tail]
  let same := commaDeletedStartsSnd comma closer [previous, ..tail] starts
  let fstStart: (commaDeleted comma closer [previous, ..tail]).fst.token.lineStart = True := rewrite tok, starts
  let trail := commaDeletedTrailing comma closer [previous, ..tail]
  let closerRest := Bool.andRight (Bool.andRight (Bool.andRight (Bool.andRight fwd)))
  rewrite same, fstStart, trail then (Bool.andIntro (Bool.orTrue _) (Bool.andIntro (Bool.orTrue _) back), closerRest)

--| `laidMoved` for a last comma that doesn't start its line.
theorem laidMovedPlain ∀ (comma closer previous: Leaf) (tail after: List Leaf)
    (starts: comma.token.lineStart = False)
    (back: laidBack [previous, ..tail] = True)
    (fwd: laidOut (pendB [previous, ..tail]) [comma, closer, ..after] = True):
    laidBack [(commaDeleted comma closer [previous, ..tail]).fst, ..(commaDeleted comma closer [previous, ..tail]).snd]
      = True
      ∧ laidOut
        (pendB [
          (commaDeleted comma closer [previous, ..tail]).fst,
          ..(commaDeleted comma closer [previous, ..tail]).snd
        ])
        after
        = True :=
  let nolead: comma.trivia.leading = [] :=
    List.eqNilOfIsEmpty comma.trivia.leading
      (Bool.orOfRightFalse comma.trivia.leading.isEmpty comma.token.lineStart (Bool.andLeft fwd) starts)
  let (b, f) := laidPair comma closer previous tail after starts back fwd
  let (movedFst, movedSnd) := commaDeletedPlain comma closer [previous, ..tail] starts nolead
  rewrite movedFst, movedSnd then (b, f)

--| Laid out stays laid out through the move of a last comma, wherever it starts.
theorem laidMoved ∀ (comma closer previous: Leaf) (tail after: List Leaf)
    (back: laidBack [previous, ..tail] = True)
    (fwd: laidOut (pendB [previous, ..tail]) [comma, closer, ..after] = True):
    laidBack [(commaDeleted comma closer [previous, ..tail]).fst, ..(commaDeleted comma closer [previous, ..tail]).snd]
      = True
      ∧ laidOut
        (pendB [
          (commaDeleted comma closer [previous, ..tail]).fst,
          ..(commaDeleted comma closer [previous, ..tail]).snd
        ])
        after
        = True :=
  match starts: comma.token.lineStart with
    | True => laidMovedStarts comma closer previous tail after starts back fwd
    | False => laidMovedPlain comma closer previous tail after starts back fwd

--| Laid out stays laid out through `withoutLastCommas`: the closer after a dropped comma holds the comma's comments
--| and starts its line if the comma did; a last comma that doesn't start its line holds no own-line comment, so only
--| its trailing comment moves, to the leaf before.
theorem laidWithout ∀ (behind rest: List Leaf)
    (back: laidBack behind = True)
    (fwd: laidOut (pendB behind) rest = True):
    laidBack (withoutR behind rest) = True :=
  match induct (withoutR behind rest) with
    | eq1 _ => back
    | eq2 behind comma closer after guard ih =>
      match behind with
        | [previous, ..tail] =>
          let (b, f) := laidMoved comma closer previous tail after back fwd
          ih b f
        | [] => cases
    | eq3 behind leaf after _ ih =>
      let (b, f) := laidNop leaf behind after back fwd
      ih b f

-- Plain, read newest first.

theorem plainBackConverse ∀ (ahead: List Token) (newest: Token) (behind: List Token)
    (ok: backOk (ahead.reverseOnto [newest, ..behind]) = True):
    plainFrom [newest, ..ahead] = True ∧ backOk [newest, ..behind] = True :=
  match ahead with
    | [] => (byComputing, ok)
    | [next, ..rest] =>
      let (more, older) := plainBackConverse rest next [newest, ..behind] ok
      (
        Bool.andIntro (Bool.andLeft older) (Bool.andIntro (Bool.andLeft (Bool.andRight older)) more),
        Bool.andRight (Bool.andRight older)
      )

theorem plainOfBack ∀ (forward: List Token) (ok: backOk (forward.reverseOnto []) = True): plain1 forward = True :=
  match forward with
    | [] => byComputing
    | [first, ..ahead] =>
      let (more, only) := plainBackConverse ahead first [] ok
      Bool.andIntro only more

--| The first of the leaves to come is no comma or closer.
def startOk: List Leaf → Bool
  | [] => True
  | [first, .._] => !passableKind first.token.kind

--| The clauses of `plainFrom` between the newest leaf done and the first to come.
def linkOk (newest: Token) (rest: List Leaf): Bool := match rest with
  | [] => True
  | [next, .._] =>
    (!(newest.kind == Arrow) || !arrowFollow next.token.kind)
      && (!(newest.kind == Comma && newest.lineStart) || !passableKind next.token.kind)

--| The leaves done, newest first, read as `plain` (`backOk`), and linked to the leaves to come. The leaves to come are
--| `sourcePlain`, which `plainWithout` carries beside this.
def sourceJoin (behind rest: List Leaf): Bool := match behind with
  | [] => startOk rest
  | [newest, .._] => backOk (tokens behind) && linkOk newest.token rest

theorem joinStart ∀ (leaves: List Leaf) (plain: sourcePlain1 (tokens leaves) = True): sourceJoin [] leaves = True :=
  match leaves with
    | [] => byComputing
    | [first, .._] => Bool.andLeft plain

theorem linkStrict ∀ (isComma start pass closer item: Bool)
    (clause: (!(isComma && start) || !pass || (closer && item)) = True)
    (notPair: (isComma && closer && item) = False):
    (!(isComma && start) || !pass) = True :=
  cases

theorem sourceTail ∀ (item: Bool) (x: Leaf) (xs: List Leaf)
    (plain: sourcePlainFrom item (tokens [x, ..xs]) = True):
    sourcePlainFrom (itemKind x.token.kind) (tokens xs) = True :=
  match xs with
    | [] => byComputing
    | [y, ..ys] => Bool.andRight (Bool.andRight plain)

theorem sourceNop ∀ (leaf: Leaf) (behind after: List Leaf)
    (join: sourceJoin behind [leaf, ..after] = True)
    (plain: sourcePlainFrom (hasItem behind) (tokens [leaf, ..after]) = True)
    (nop: fwdPair behind leaf after = False):
    sourceJoin [leaf, ..behind] after = True :=
  let link: linkOk leaf.token after = True := match after with
    | [] => byComputing
    | [next, ..more] =>
      let notPair: (leaf.token.kind == Comma && next.token.kind.isCloser && hasItem behind) = False := nop
      Bool.andIntro (Bool.andLeft plain) (linkStrict _ _ _ _ _ (Bool.andLeft (Bool.andRight plain)) notPair)
  match behind with
    | [] => Bool.andIntro join link
    | [newest, ..older] =>
      let kept := Bool.andRight join
      Bool.andIntro (Bool.andIntro (Bool.andLeft kept) (Bool.andIntro (Bool.andRight kept) (Bool.andLeft join))) link

theorem itemNotComma ∀ (previous: Leaf) (tail: List Leaf)
    (item: hasItem [previous, ..tail] = True):
    (previous.token.kind == Comma) = False :=
  match isComma: previous.token.kind == Comma with
    | False => byComputing
    | True =>
      let nothing: hasItem [previous, ..tail] = False := hasItemComma previous tail isComma
      rewrite nothing at item then cases

theorem notArrowBeforeComma ∀ (x: Bool) (h: (!x || !arrowFollow Comma) = True): x = False := cases

theorem itemOfKind ∀ (fst closer: Leaf) (snd: List Leaf)
    (same: fst.token.kind = closer.token.kind):
    hasItem [fst, ..snd] = itemKind closer.token.kind :=
  rewrite same

theorem sourcePair ∀ (comma closer previous: Leaf) (tail after: List Leaf)
    (isComma: (comma.token.kind == Comma) = True)
    (isCloser: closer.token.kind.isCloser = True)
    (item: hasItem [previous, ..tail] = True)
    (join: sourceJoin [previous, ..tail] [comma, closer, ..after] = True)
    (plain: sourcePlainFrom (hasItem [previous, ..tail]) (tokens [comma, closer, ..after]) = True):
    sourceJoin
      [(commaDeleted comma closer [previous, ..tail]).fst, ..(commaDeleted comma closer [previous, ..tail]).snd]
      after
      = True :=
  let (tok, sndToks) := commaDeletedToken comma closer [previous, ..tail]
  let kind := commaDeletedKind comma closer [previous, ..tail]
  let back := Bool.andLeft join
  let first := Bool.andLeft (Bool.andRight join)
  let notComma := itemNotComma previous tail item
  let notArrow: (previous.token.kind == Arrow) = False :=
    notArrowBeforeComma (previous.token.kind == Arrow) (rewrite DecEq.sound isComma at first then first)
  let backNew: backOk [(commaDeleted comma closer [previous, ..tail]).fst.token, previous.token, ..tokens tail]
    = True :=
    Bool.andIntro (rewrite notArrow) (Bool.andIntro (rewrite notComma) back)
  let linkNew: linkOk (commaDeleted comma closer [previous, ..tail]).fst.token after = True := match after with
    | [] => byComputing
    | [next, ..more] =>
      let clause := Bool.andLeft (Bool.andRight (Bool.andRight plain))
      let closerPlain: (closer.token.kind == Comma) = False := closerNotComma closer.token.kind isCloser
      Bool.andIntro (rewrite kind then clause) (rewrite kind, closerPlain)
  Bool.andIntro (rewrite sndToks then backNew) linkNew

--| The leaves without their last commas, read as `plain`, from the source's test: the closer after a dropped comma
--| follows an item, which is neither `->` (the comma after it was allowed) nor a comma.
theorem plainWithout ∀ (behind rest: List Leaf)
    (join: sourceJoin behind rest = True)
    (plain: sourcePlainFrom (hasItem behind) (tokens rest) = True):
    sourceJoin (withoutR behind rest) [] = True :=
  match induct (withoutR behind rest) with
    | eq1 _ => join
    | eq2 behind comma closer after guard ih =>
      match behind with
        | [previous, ..tail] =>
          let (isComma, isCloser, item) := guard
          let kind := commaDeletedKind comma closer [previous, ..tail]
          let tailPlain :=
            sourceTail
              (itemKind comma.token.kind)
              closer
              after
              (sourceTail (hasItem [previous, ..tail]) comma [closer, ..after] plain)
          ih
            (sourcePair comma closer previous tail after isComma isCloser item join plain)
            (rewrite itemOfKind
                  (commaDeleted comma closer [previous, ..tail]).fst
                  closer
                  (commaDeleted comma closer [previous, ..tail]).snd
                  kind then
              tailPlain)
        | [] => cases
    | eq3 behind leaf after notArm2 ih =>
      ih
        (sourceNop leaf behind after join plain (fwdPairOfNotArm leaf behind after notArm2))
        (sourceTail (hasItem behind) leaf after plain)

-- What the leaves hold stays what they hold.

--| `withoutLastCommas` keeps every token, but the commas it drops (and the line start of a closer after one that
--| started its line): a test on every token that reads no line start still holds.
theorem allTokensWithout ∀ (q: Token → Bool)
    (blind: ∀ (token: Token) (start: Bool) => q { token | lineStart = start } = q token) (behind rest: List Leaf)
    (kept: (tokens behind).all q = True)
    (coming: (tokens rest).all q = True):
    (tokens (withoutR behind rest)).all q = True :=
  match induct (withoutR behind rest) with
    | eq1 _ => kept
    | eq2 behind comma closer after guard ih =>
      let (tok, sndToks) := commaDeletedToken comma closer behind
      let qfst: q (commaDeleted comma closer behind).fst.token = True :=
        rewrite tok, blind closer.token (comma.token.lineStart || closer.token.lineStart) then
          Bool.andLeft (Bool.andRight coming)
      ih (rewrite sndToks then Bool.andIntro qfst kept) (Bool.andRight (Bool.andRight coming))
    | eq3 behind leaf after _ ih => ih (Bool.andIntro (Bool.andLeft coming) kept) (Bool.andRight coming)

theorem textsCons ∀ (leaf: Leaf) (rest: List Leaf):
    leafTexts [leaf, ..rest] = triviaTexts leaf.trivia ++ leafTexts rest :=
  byComputing

theorem textsParked ∀ (q: Text → Bool) (comment: Comment) (previous: Leaf) (earlier: List Leaf)
    (kept: (leafTexts [previous, ..earlier]).all q = True)
    (said: q comment.text = True):
    (leafTexts [previous.withTrailing (Some comment), ..earlier]).all q = True :=
  match previous with
    | { token, trivia } =>
      match trivia with
        | { leading, blankLines, trailing } =>
          let split :=
            rewrite textsCons { token, trivia = { leading, blankLines, trailing } } earlier,
                List.allAppendAnd (triviaTexts { leading, blankLines, trailing }) (leafTexts earlier) q at kept then
              kept
          let triv := Bool.andLeft split
          let lead: (leading.map (c => c.text)).all q = True :=
            Bool.andLeft
              (rewrite List.allAppendAnd (leading.map (c => c.text)) (optionText trailing) q at triv then triv)
          rewrite textsCons { token, trivia = { leading, blankLines, trailing = Some comment } } earlier,
              List.allAppendAnd
                (triviaTexts { leading, blankLines, trailing = Some comment })
                (leafTexts earlier)
                q then
            Bool.andIntro
              (rewrite List.allAppendAnd (leading.map (c => c.text)) (optionText (Some comment)) q then
                Bool.andIntro lead (Bool.andIntro said byComputing))
              (Bool.andRight split)

theorem textsParkedAll ∀ (q: Text → Bool) (trailing: Option Comment) (behind: List Leaf)
    (kept: (leafTexts behind).all q = True)
    (said: (optionText trailing).all q = True):
    (leafTexts (parked trailing behind)).all q = True :=
  match trailing with
    | None => kept
    | Some comment =>
      match behind with
        | [] => kept
        | [previous, ..earlier] => textsParked q comment previous earlier kept (Bool.andLeft said)

--| The texts of a trivia's own-line comments and of its trailing comment each pass a test, if the trivia's do.
theorem splitTexts ∀ (q: Text → Bool) (trivia: Trivia)
    (all: (triviaTexts trivia).all q = True):
    (trivia.leading.map (comment => comment.text)).all q = True ∧ (optionText trivia.trailing).all q = True :=
  match trivia with
    | { leading, blankLines, trailing } =>
      let split :=
        rewrite List.allAppendAnd (leading.map (comment => comment.text)) (optionText trailing) q at all then all
      (Bool.andLeft split, Bool.andRight split)

theorem textsOfAppend ∀ (q: Text → Bool) (xs ys: List Comment)
    (hx: (xs.map (comment => comment.text)).all q = True)
    (hy: (ys.map (comment => comment.text)).all q = True):
    ((xs ++ ys).map (comment => comment.text)).all q = True :=
  rewrite List.mapAppend xs ys (comment => comment.text),
      List.allAppendAnd (xs.map (comment => comment.text)) (ys.map (comment => comment.text)) q then
    Bool.andIntro hx hy

theorem textsOfLeading ∀ (q: Text → Bool) (xs ys: List Comment) (ot: List Text)
    (hx: (xs.map (comment => comment.text)).all q = True)
    (hy: (ys.map (comment => comment.text)).all q = True)
    (ho: ot.all q = True):
    ((xs ++ ys).map (comment => comment.text) ++ ot).all q = True :=
  rewrite List.mapAppend xs ys (comment => comment.text),
      List.allAppendAnd ((xs.map (comment => comment.text)) ++ (ys.map (comment => comment.text))) ot q,
      List.allAppendAnd (xs.map (comment => comment.text)) (ys.map (comment => comment.text)) q then
    Bool.andIntro (Bool.andIntro hx hy) ho

--| A last comma that starts its line moves its comments above the closer: the texts move with them.
theorem movedTextsStarts ∀ (q: Text → Bool) (comma closer: Leaf) (behind: List Leaf)
    (starts: comma.token.lineStart = True)
    (hc: (triviaTexts comma.trivia).all q = True)
    (hk: (triviaTexts closer.trivia).all q = True):
    (triviaTexts (commaDeleted comma closer behind).fst.trivia).all q = True :=
  match closer with
    | { token = closerToken, trivia = closerTrivia } =>
      match closerTrivia with
        | { leading = closerLeading, blankLines = closerBlank, trailing = closerTrailing } =>
          match closerToken with
            | { kind, text, column, lineStart } =>
              match comma with
                | { token = commaToken, trivia = commaTrivia } =>
                  match commaTrivia with
                    | { leading = commaLeading, blankLines = commaBlank, trailing = commaTrailing } =>
                      match commaToken with
                        | { kind = commaKind, text = commaText, column = commaColumn, lineStart = commaStart } =>
                          let (hcl, hct) := splitTexts q commaTrivia hc
                          let (hkl, hkt) := splitTexts q closerTrivia hk
                          rewrite starts then
                            match closerLeading with
                              | [] =>
                                match commaTrailing with
                                  | None => textsOfLeading q commaLeading [] (optionText closerTrailing) hcl hkl hkt
                                  | Some comment =>
                                    match behind with
                                      | [] =>
                                        textsOfLeading q
                                          (commaLeading ++ [{ comment | blankLines = commaBlank }])
                                          []
                                          (optionText closerTrailing)
                                          (textsOfAppend q commaLeading [{ comment | blankLines = commaBlank }] hcl hct)
                                          hkl
                                          hkt
                                      | [previous, ..earlier] =>
                                        textsOfLeading q
                                          (commaLeading ++ [{ comment | blankLines = commaBlank }])
                                          []
                                          (optionText closerTrailing)
                                          (textsOfAppend q commaLeading [{ comment | blankLines = commaBlank }] hcl hct)
                                          hkl
                                          hkt
                              | [first, ..others] =>
                                match commaTrailing with
                                  | None =>
                                    textsOfLeading q commaLeading
                                      [{ first | blankLines = 1 }, ..others]
                                      (optionText closerTrailing)
                                      hcl
                                      hkl
                                      hkt
                                  | Some comment =>
                                    match behind with
                                      | [] =>
                                        textsOfLeading q
                                          (commaLeading ++ [{ comment | blankLines = commaBlank }])
                                          [first, ..others]
                                          (optionText closerTrailing)
                                          (textsOfAppend q commaLeading [{ comment | blankLines = commaBlank }] hcl hct)
                                          hkl
                                          hkt
                                      | [previous, ..earlier] =>
                                        textsOfLeading q
                                          (commaLeading ++ [{ comment | blankLines = commaBlank }])
                                          [first, ..others]
                                          (optionText closerTrailing)
                                          (textsOfAppend q commaLeading [{ comment | blankLines = commaBlank }] hcl hct)
                                          hkl
                                          hkt

--| `textsMoved` for a last comma that doesn't start its line: its trailing comment goes to the leaf before.
theorem textsMovedPlain ∀ (q: Text → Bool) (comma closer previous: Leaf) (tail after: List Leaf)
    (starts: comma.token.lineStart = False)
    (back: laidBack [previous, ..tail] = True)
    (fwd: laidOut (pendB [previous, ..tail]) [comma, closer, ..after] = True)
    (kept: (leafTexts [previous, ..tail]).all q = True)
    (coming: (leafTexts [comma, closer, ..after]).all q = True):
    (leafTexts [
          (commaDeleted comma closer [previous, ..tail]).fst,
          ..(commaDeleted comma closer [previous, ..tail]).snd
        ]).all q
      = True
      ∧ (leafTexts after).all q = True :=
  let nolead: comma.trivia.leading = [] :=
    List.eqNilOfIsEmpty comma.trivia.leading
      (Bool.orOfRightFalse comma.trivia.leading.isEmpty comma.token.lineStart (Bool.andLeft fwd) starts)
  let (movedFst, movedSnd) := commaDeletedPlain comma closer [previous, ..tail] starts nolead
  let split1 :=
    rewrite textsCons comma [closer, ..after],
        List.allAppendAnd (triviaTexts comma.trivia) (leafTexts [closer, ..after]) q at coming then
      coming
  let commaHeld := Bool.andLeft split1
  let commaAll: (optionText comma.trivia.trailing).all q = True := rewrite nolead at commaHeld then commaHeld
  let closerPart := Bool.andRight split1
  let split2 :=
    rewrite textsCons closer after, List.allAppendAnd (triviaTexts closer.trivia) (leafTexts after) q at closerPart then
      closerPart
  let parkedAll := textsParkedAll q comma.trivia.trailing [previous, ..tail] kept commaAll
  rewrite movedFst, movedSnd then
    (
      rewrite textsCons closer (parked comma.trivia.trailing [previous, ..tail]),
          List.allAppendAnd
            (triviaTexts closer.trivia)
            (leafTexts (parked comma.trivia.trailing [previous, ..tail]))
            q then
        Bool.andIntro (Bool.andLeft split2) parkedAll,
      Bool.andRight split2
    )

--| `textsMoved` for a last comma that starts its line: its comments go above the closer, and the leaf before is
--| untouched.
theorem textsMovedStarts ∀ (q: Text → Bool) (comma closer previous: Leaf) (tail after: List Leaf)
    (starts: comma.token.lineStart = True)
    (kept: (leafTexts [previous, ..tail]).all q = True)
    (coming: (leafTexts [comma, closer, ..after]).all q = True):
    (leafTexts [
          (commaDeleted comma closer [previous, ..tail]).fst,
          ..(commaDeleted comma closer [previous, ..tail]).snd
        ]).all q
      = True
      ∧ (leafTexts after).all q = True :=
  let split1 :=
    rewrite textsCons comma [closer, ..after],
        List.allAppendAnd (triviaTexts comma.trivia) (leafTexts [closer, ..after]) q at coming then
      coming
  let closerPart := Bool.andRight split1
  let split2 :=
    rewrite textsCons closer after, List.allAppendAnd (triviaTexts closer.trivia) (leafTexts after) q at closerPart then
      closerPart
  let movedAll := movedTextsStarts q comma closer [previous, ..tail] starts (Bool.andLeft split1) (Bool.andLeft split2)
  rewrite commaDeletedStartsSnd comma closer [previous, ..tail] starts then
    (
      rewrite textsCons (commaDeleted comma closer [previous, ..tail]).fst [previous, ..tail],
          List.allAppendAnd
            (triviaTexts (commaDeleted comma closer [previous, ..tail]).fst.trivia)
            (leafTexts [previous, ..tail])
            q then
        Bool.andIntro movedAll kept,
      Bool.andRight split2
    )

--| A last comma's move keeps the texts that pass a test, wherever the comma starts.
theorem textsMoved ∀ (q: Text → Bool) (comma closer previous: Leaf) (tail after: List Leaf)
    (back: laidBack [previous, ..tail] = True)
    (fwd: laidOut (pendB [previous, ..tail]) [comma, closer, ..after] = True)
    (kept: (leafTexts [previous, ..tail]).all q = True)
    (coming: (leafTexts [comma, closer, ..after]).all q = True):
    (leafTexts [
          (commaDeleted comma closer [previous, ..tail]).fst,
          ..(commaDeleted comma closer [previous, ..tail]).snd
        ]).all q
      = True
      ∧ (leafTexts after).all q = True :=
  match starts: comma.token.lineStart with
    | True => textsMovedStarts q comma closer previous tail after starts kept coming
    | False => textsMovedPlain q comma closer previous tail after starts back fwd kept coming

--| `withoutLastCommas` keeps every comment but the text it moves is the same text: a test on every comment text
--| still holds.
theorem textsWithout ∀ (q: Text → Bool) (behind rest: List Leaf)
    (back: laidBack behind = True)
    (fwd: laidOut (pendB behind) rest = True)
    (kept: (leafTexts behind).all q = True)
    (coming: (leafTexts rest).all q = True):
    (leafTexts (withoutR behind rest)).all q = True :=
  match induct (withoutR behind rest) with
    | eq1 _ => kept
    | eq2 behind comma closer after guard ih =>
      match behind with
        | [previous, ..tail] =>
          let (b, f) := laidMoved comma closer previous tail after back fwd
          let (keptNew, comingNew) := textsMoved q comma closer previous tail after back fwd kept coming
          ih b f keptNew comingNew
        | [] => cases
    | eq3 behind leaf after _ ih =>
      let (b, f) := laidNop leaf behind after back fwd
      let split :=
        rewrite textsCons leaf after, List.allAppendAnd (triviaTexts leaf.trivia) (leafTexts after) q at coming then
          coming
      ih b f
        (rewrite textsCons leaf behind, List.allAppendAnd (triviaTexts leaf.trivia) (leafTexts behind) q then
          Bool.andIntro (Bool.andLeft split) kept)
        (Bool.andRight split)

-- A comment trimmed of the spaces at its end is still a comment, and the lexer's test of one holds.

--| A comment's characters without those at their end that are spaces (`trimEnd`).
def trimChars (chars: List Char): List Char := (chars.reverse.dropWhile (char => char == ' ')).reverse

theorem trimCharsSecond ∀ (first second: Char) (rest: List Char)
    (stops: (second == ' ') = False):
    trimChars [first, second, ..rest] = [first, second, ..trimChars rest] :=
  let reversed: [first, second, ..rest].reverse = rest.reverse ++ [second, first] := calc [
    first,
    second,
    ..rest
  ].reverse
    _ = [second, ..rest].reverse ++ [first] := List.reverseCons first [second, ..rest]
    _ = (rest.reverse ++ [second]) ++ [first] := rewrite List.reverseCons second rest
    _ = rest.reverse ++ [second, first] := List.appendAssoc rest.reverse [second] [first]
  calc trimChars [first, second, ..rest]
    _ = ((rest.reverse ++ [second, first]).dropWhile (char => char == ' ')).reverse := rewrite reversed
    _ = (rest.reverse.dropWhile (char => char == ' ') ++ [second, first]).reverse :=
      rewrite List.dropWhileAppendStop (char => char == ' ') rest.reverse second [first] stops
    _ = [first, second, ..trimChars rest] :=
      rewrite List.reverseAppend (rest.reverse.dropWhile (char => char == ' ')) [second, first]

theorem trimStartsDashes ∀ (chars: List Char)
    (h: Text.startsWithChars ['-', '-'] chars = True):
    Text.startsWithChars ['-', '-'] (trimChars chars) = True :=
  match chars with
    | [only] => cases
    | [first, second, ..rest] =>
      match same1: Text.sameChar '-' first with
        | True =>
          match same2: Text.sameChar '-' second with
            | True =>
              let equal: Char.toNat '-' = Char.toNat second := Nat.equalSound (Char.toNat '-') (Char.toNat second) same2
              let stops: (second == ' ') = False := rewrite <- equal
              rewrite trimCharsSecond first second rest stops

theorem trimSplit ∀ (chars: List Char):
    trimChars chars ++ (chars.reverse.takeWhile (char => char == ' ')).reverse = chars :=
  calc trimChars chars ++ (chars.reverse.takeWhile (char => char == ' ')).reverse
    _ = ((chars.reverse.takeWhile (char => char == ' ')) ++ chars.reverse.dropWhile (char => char == ' ')).reverse :=
      (List.reverseAppend
        (chars.reverse.takeWhile (char => char == ' '))
        (chars.reverse.dropWhile (char => char == ' '))).flipped
    _ = chars.reverse.reverse := rewrite List.takeWhileDropWhile (char => char == ' ') chars.reverse
    _ = chars := List.reverseReverse chars

theorem trimNoNewline ∀ (chars: List Char)
    (h: Text.containsChars ['\n'] chars = False):
    Text.containsChars ['\n'] (trimChars chars) = False :=
  match found: Text.containsChars ['\n'] (trimChars chars) with
    | False => byComputing
    | True =>
      let big :=
        Text.containsCharsAppendLeft
          ['\n']
          (trimChars chars)
          (chars.reverse.takeWhile (char => char == ' ')).reverse
          found
      rewrite trimSplit chars at big then rewrite h at big then cases

--| A comment as the lexer reads it (`--`, no line break) is one the formatter's `commentText` accepts once its
--| trailing spaces are trimmed.
theorem trimmedComment ∀ (text: Text)
    (starts: text.startsWith "--" = True)
    (single: text.contains "\n" = False):
    commentText (trimEnd text) = True :=
  match spaced: text.endsWith " " with
    | False => rewrite starts, single
    | True =>
      let kept := (text.toList.reverseOnto []).dropWhile (char => char == ' ')
      let back: (kept.reverseOnto []).reverseOnto [] = kept := List.reverseReverse kept
      let startsOk := trimStartsDashes text.toList starts
      let singleOk := trimNoNewline text.toList single
      rewrite startsOk, singleOk, back, Text.startsWithSpaceDropWhile (text.toList.reverseOnto [])

-- From leaves to words: comments.

--| `codeWords` of `Syntax.ParseSettledStatements`, which imports this file.
def wordsOf (leaves: List Leaf): List Word := leaves.filter (leaf => leaf.kind != Comma) |> .map Leaf.word

theorem noteTexts ∀ (comments: List Comment):
    (comments.map (comment => { text = comment.text, blankBefore = comment.blankLines > 0 })).map (note => note.text)
      = comments.map (comment => comment.text) :=
  match comments with
    | [] => byComputing
    | [comment, ..rest] => Eq.cong (tail => [comment.text, ..tail]) (noteTexts rest)

theorem optionTexts ∀ (trailing: Option Comment):
    (trailing.map (comment => comment.text)).toList = optionText trailing :=
  match trailing with | None | Some _ => byComputing

--| A leaf's word holds the comment texts the leaf does.
theorem wordTexts ∀ (leaf: Leaf): leaf.word.comments.texts = triviaTexts leaf.trivia :=
  rewrite noteTexts leaf.trivia.leading, optionTexts leaf.trivia.trailing

theorem leavesCommentTexts ∀ (leaves: List Leaf)
    (all: (leafTexts leaves).all commentText = True):
    leaves.all (leaf => (triviaTexts leaf.trivia).all commentText) = True :=
  match leaves with
    | [] => byComputing
    | [leaf, ..rest] =>
      let split :=
        rewrite textsCons leaf rest,
            List.allAppendAnd (triviaTexts leaf.trivia) (leafTexts rest) commentText at all then
          all
      Bool.andIntro (Bool.andLeft split) (leavesCommentTexts rest (Bool.andRight split))

theorem wordsCommentTexts ∀ (leaves: List Leaf)
    (all: leaves.all (leaf => (triviaTexts leaf.trivia).all commentText) = True):
    (wordsOf leaves).all (word => word.comments.texts.all commentText) = True :=
  match leaves with
    | [] => byComputing
    | [leaf, ..rest] =>
      match comma: leaf.kind != Comma with
        | False => wordsCommentTexts rest (Bool.andRight all)
        | True =>
          Bool.andIntro (rewrite wordTexts leaf then Bool.andLeft all) (wordsCommentTexts rest (Bool.andRight all))

-- From leaves to words: closers homed.

--| `Leaf.marked` of `Syntax.ParseSettledStatements`: a leaf's text says whether it is a closer and whether it is `->`
--| as its kind does.
def isMarked (leaf: Leaf): Bool :=
  isCloserText leaf.token.text == leaf.token.kind.isCloser
    && (operatorTok leaf.token.text == Some Arrow) == (leaf.token.kind == Arrow)

theorem wordsOfComma ∀ (leaf: Leaf) (rest: List Leaf)
    (isComma: (leaf.token.kind == Comma) = True):
    wordsOf [leaf, ..rest] = wordsOf rest :=
  rewrite isComma

theorem wordsOfItem ∀ (leaf: Leaf) (rest: List Leaf)
    (notComma: (leaf.token.kind == Comma) = False):
    wordsOf [leaf, ..rest] = [leaf.word, ..wordsOf rest] :=
  rewrite notComma

theorem wordTrails ∀ (leaf: Leaf): leaf.word.trails = leaf.trivia.trailing.isSome := match leaf.trivia.trailing with
  | None | Some _ => byComputing

theorem wordNoted ∀ (leaf: Leaf): leaf.word.noted = !leaf.trivia.leading.isEmpty := match leaf.trivia.leading with
  | [] | [_, .._] => byComputing

theorem endsOnStep ∀ (leaf: Leaf) (earlier: List Leaf):
    endsOn [leaf, ..earlier]
      = (leaf.trivia.trailing.isSome || (!(earlier.isEmpty || !passable leaf) && endsOn earlier)) :=
  match some: leaf.trivia.trailing.isSome with
    | True => byComputing
    | False =>
      match empty: earlier.isEmpty || !passable leaf with
        | True => byComputing
        | False => byComputing

theorem noneNotSome ∀ (option: Option Comment) (none: option.isNone = True): option.isSome = False := match option with
  | None => byComputing

theorem stopOfPassable ∀ (empty passes: Bool) (h: (!(empty || !passes)) = True): passes = True := cases

theorem endsOnTrailsComma ∀ (leaf: Leaf) (earlier: List Leaf)
    (isComma: (leaf.token.kind == Comma) = True)
    (ends: endsOn [leaf, ..earlier] = True)
    (bare: bareComma leaf = True)
    (rec: endsOn earlier = True → trailsBack (wordsOf earlier) = True):
    trailsBack (wordsOf [leaf, ..earlier]) = True :=
  let step: (leaf.trivia.trailing.isSome || (!(earlier.isEmpty || !passable leaf) && endsOn earlier)) = True :=
    rewrite endsOnStep leaf earlier at ends then ends
  let kept :=
    Bool.orOfNotTrue
      (leaf.trivia.leading.isEmpty && leaf.trivia.trailing.isNone)
      (leaf.token.kind == Comma)
      bare
      isComma
  let notSome: leaf.trivia.trailing.isSome = False := noneNotSome leaf.trivia.trailing (Bool.andRight kept)
  let rest :=
    Bool.orOfLeftFalse leaf.trivia.trailing.isSome (!(earlier.isEmpty || !passable leaf) && endsOn earlier) step notSome
  rewrite wordsOfComma leaf earlier isComma then rec (Bool.andRight rest)

theorem endsOnTrailsItem ∀ (leaf: Leaf) (earlier: List Leaf)
    (notComma: (leaf.token.kind == Comma) = False)
    (ends: endsOn [leaf, ..earlier] = True)
    (marked: isMarked leaf = True)
    (rec: endsOn earlier = True → trailsBack (wordsOf earlier) = True):
    trailsBack (wordsOf [leaf, ..earlier]) = True :=
  let step: (leaf.trivia.trailing.isSome || (!(earlier.isEmpty || !passable leaf) && endsOn earlier)) = True :=
    rewrite endsOnStep leaf earlier at ends then ends
  let item := wordsOfItem leaf earlier notComma
  match some: leaf.trivia.trailing.isSome with
    | True => rewrite item then Bool.orLeft (rewrite wordTrails leaf then some)
    | False =>
      let rest :=
        Bool.orOfLeftFalse leaf.trivia.trailing.isSome
          (!(earlier.isEmpty || !passable leaf) && endsOn earlier)
          step
          some
      let passes := stopOfPassable earlier.isEmpty (passable leaf) (Bool.andLeft rest)
      let closer: leaf.token.kind.isCloser = True :=
        Bool.orOfLeftFalse (leaf.token.kind == Comma) leaf.token.kind.isCloser passes notComma
      let marker := Bool.eqOfBeq (isCloserText leaf.token.text) leaf.token.kind.isCloser (Bool.andLeft marked)
      let word: isCloserText leaf.token.text = True := rewrite closer at marker then marker
      rewrite item then Bool.orRight (Bool.andIntro word (rec (Bool.andRight rest)))

--| `trailsBack` of the words of leaves, newest first: a comment ends the line wherever the back-walk would put one, since
--| commas hold none (the leaves are settled), and the closers are the words that are closers.
theorem endsOnTrails ∀ (older: List Leaf)
    (ends: endsOn older = True)
    (bare: older.all bareComma = True)
    (marked: older.all isMarked = True):
    trailsBack (wordsOf older) = True :=
  match older with
    | [leaf, ..earlier] =>
      let rec := (more => endsOnTrails earlier more (Bool.andRight bare) (Bool.andRight marked))
      match isComma: leaf.token.kind == Comma with
        | True => endsOnTrailsComma leaf earlier isComma ends (Bool.andLeft bare) rec
        | False => endsOnTrailsItem leaf earlier isComma ends (Bool.andLeft marked) rec

theorem homedCore ∀ (tr cl ct lead em wem ls ends tb: Bool)
    (there: (!tr || (!cl || em || (ls && (!lead || ends)))) = True)
    (marker: (ct == cl) = True)
    (empty: (!em || wem) = True)
    (trails: (!ends || tb) = True):
    (!(ct && tr) || wem || !lead || tb) = True :=
  match tr with
    | False => cases
    | True =>
      match cl with
        | False => rewrite Bool.eqOfBeq ct False marker
        | True =>
          rewrite Bool.eqOfBeq ct True marker then
            match em with
              | True => rewrite empty
              | False =>
                match lead with
                  | False => cases
                  | True => cases

theorem wordsEmpty ∀ (leaves: List Leaf) (empty: leaves.isEmpty = True): (wordsOf leaves).isEmpty = True :=
  match leaves with | [] => byComputing

theorem noneIsNot ∀ (option: Option Comment): option.isNone = !option.isSome := match option with
  | None | Some _ => byComputing

--| A closer that keeps a trailing comment stops the back-walk, in the leaves, so it has own-line comments or follows
--| code that ends with a comment, which the words say too.
theorem homedWordsLeaf ∀ (leaf: Leaf) (earlier: List Leaf)
    (there: homedLeaf leaf earlier = True)
    (marked: isMarked leaf = True)
    (bare: earlier.all bareComma = True)
    (markedEarlier: earlier.all isMarked = True):
    (!(isCloserText leaf.word.text && leaf.word.trails)
      || (wordsOf earlier).isEmpty
      || leaf.word.noted
      || trailsBack (wordsOf earlier))
      = True :=
  let thereNone: (leaf.trivia.trailing.isNone || (!leaf.token.kind.isCloser || earlier.isEmpty || stopsAt leaf earlier))
    = True :=
    Bool.orAndLeft _ _ _ there
  let tr: (!leaf.trivia.trailing.isSome
    || (!leaf.token.kind.isCloser
      || earlier.isEmpty
      || (leaf.token.lineStart && (!leaf.trivia.leading.isEmpty || endsOn earlier))))
    = True :=
    rewrite noneIsNot leaf.trivia.trailing at thereNone then thereNone
  let marker: (isCloserText leaf.token.text == leaf.token.kind.isCloser) = True := Bool.andLeft marked
  let empty: (!earlier.isEmpty || (wordsOf earlier).isEmpty) = True := match e: earlier.isEmpty with
    | True => rewrite wordsEmpty earlier e
    | False => byComputing
  let trails: (!endsOn earlier || trailsBack (wordsOf earlier)) = True := match e: endsOn earlier with
    | True => rewrite endsOnTrails earlier e bare markedEarlier
    | False => byComputing
  let core :=
    homedCore leaf.trivia.trailing.isSome leaf.token.kind.isCloser
      (isCloserText leaf.token.text)
      leaf.trivia.leading.isEmpty
      earlier.isEmpty
      (wordsOf earlier).isEmpty
      leaf.token.lineStart
      (endsOn earlier)
      (trailsBack (wordsOf earlier))
      tr
      marker
      empty
      trails
  rewrite wordTrails leaf, wordNoted leaf then core

--| A closer's trailing comment is where the back-walk leaves it: homed as the leaves read it, so homed as the words read
--| it (K1's `homed`, whose look back sees no commas).
theorem homedWords ∀ (older: List Leaf)
    (homed: homedBehind older = True)
    (bare: older.all bareComma = True)
    (marked: older.all isMarked = True):
    homedBack (wordsOf older) = True :=
  match older with
    | [] => byComputing
    | [leaf, ..earlier] =>
      let more := homedWords earlier (Bool.andRight homed) (Bool.andRight bare) (Bool.andRight marked)
      match isComma: leaf.token.kind == Comma with
        | True => more
        | False =>
          Bool.andIntro
            (homedWordsLeaf leaf earlier
              (Bool.andLeft homed)
              (Bool.andLeft marked)
              (Bool.andRight bare)
              (Bool.andRight marked))
            more

-- From leaves to words: `->` bare.

theorem arrowsBareCons ∀ (word: Word) (words: List Word)
    (notArrow: ((operatorTok word.text != Some Arrow): Bool) = True)
    (rest: arrowsBare words = True):
    arrowsBare [word, ..words] = True :=
  match words with
    | [] => byComputing
    | [next, ..more] => Bool.andIntro (Bool.orLeft notArrow) rest

theorem followFacts ∀ (kind: Tok) (h: arrowFollow kind = False): (kind == Comma) = False ∧ (kind == Arrow) = False := (
  Bool.orFalseLeft (kind == Comma) kind.isCloser (Bool.orFalseLeft (passableKind kind) (kind == Arrow) h),
  Bool.orFalseRight (passableKind kind) (kind == Arrow) h
)

theorem arrowsWordsPlain ∀ (first: Leaf) (rest: List Leaf)
    (notComma: (first.token.kind == Comma) = False)
    (notArrow: (first.token.kind == Arrow) = False)
    (marked: isMarked first = True)
    (ih: arrowsBare (wordsOf rest) = True):
    arrowsBare (wordsOf [first, ..rest]) = True :=
  let marker :=
    Bool.eqOfBeq (operatorTok first.token.text == Some Arrow) (first.token.kind == Arrow) (Bool.andRight marked)
  let notOperator: (operatorTok first.token.text == Some Arrow) = False := rewrite notArrow at marker then marker
  rewrite wordsOfItem first rest notComma then arrowsBareCons first.word (wordsOf rest) (rewrite notOperator) ih

theorem arrowsWordsArrow ∀ (first next: Leaf) (more: List Leaf)
    (notComma: (first.token.kind == Comma) = False)
    (leafArrows: (first.trivia.trailing.isNone && (next.trivia.leading.isEmpty || next.token.kind == Arrow)) = True)
    (plain: (!arrowFollow next.token.kind) = True)
    (ih: arrowsBare (wordsOf [next, ..more]) = True):
    arrowsBare (wordsOf [first, next, ..more]) = True :=
  let follow: arrowFollow next.token.kind = False := Bool.notTrue _ plain
  let (nextComma, nextNotArrow) := followFacts next.token.kind follow
  let own := Bool.andLeft leafArrows
  let noOwn: next.trivia.leading.isEmpty = True := Bool.orOfRightFalse _ _ (Bool.andRight leafArrows) nextNotArrow
  let noTrail: first.trivia.trailing.isSome = False := noneNotSome first.trivia.trailing own
  let rest := rewrite wordsOfItem next more nextComma at ih then ih
  rewrite wordsOfItem first [next, ..more] notComma, wordsOfItem next more nextComma then
    Bool.andIntro
      (Bool.orRight (Bool.andIntro (rewrite wordTrails first, noTrail) (rewrite wordNoted next, noOwn)))
      rest

theorem arrowsWordsSingle ∀ (leaf: Leaf): arrowsBare (wordsOf [leaf]) = True :=
  match isComma: leaf.token.kind == Comma with | True | False => byComputing

--| `->` keeps no comment after it as the leaves say it, so as the words say it: no comma follows a `->` (`plain`),
--| so the token after it is the word after it.
theorem arrowsWords ∀ (leaves: List Leaf)
    (arrows: Syntax.SettleProofs.arrowsBare leaves = True)
    (plain: plainFrom (tokens leaves) = True)
    (marked: leaves.all isMarked = True):
    arrowsBare (wordsOf leaves) = True :=
  match leaves with
    | [] => byComputing
    | [first, ..rest] =>
      match rest with
        | [] => arrowsWordsSingle first
        | [next, ..more] =>
          let ih :=
            arrowsWords
              [next, ..more]
              (Bool.andRight arrows)
              (plainTail first [next, ..more] plain)
              (Bool.andRight marked)
          match isComma: first.token.kind == Comma with
            | True => ih
            | False =>
              match isArrow: first.token.kind == Arrow with
                | False => arrowsWordsPlain first [next, ..more] isComma isArrow (Bool.andLeft marked) ih
                | True => arrowsWordsArrow first next more isComma (Bool.andLeft arrows) (Bool.andLeft plain) ih

-- Reading the leaves the other way round.

theorem textsReverseOnto ∀ (q: Text → Bool) (xs acc: List Leaf):
    (leafTexts (xs.reverseOnto acc)).all q = ((leafTexts xs).all q && (leafTexts acc).all q) :=
  match xs with
    | [] => byComputing
    | [x, ..rest] =>
      calc (leafTexts (rest.reverseOnto [x, ..acc])).all q
        _ = ((leafTexts rest).all q && (leafTexts [x, ..acc]).all q) := textsReverseOnto q rest [x, ..acc]
        _ = ((leafTexts rest).all q && ((triviaTexts x.trivia).all q && (leafTexts acc).all q)) :=
          rewrite textsCons x acc, List.allAppendAnd (triviaTexts x.trivia) (leafTexts acc) q
        _ = ((triviaTexts x.trivia).all q && ((leafTexts rest).all q && (leafTexts acc).all q)) :=
          Bool.andLeftComm _ _ _
        _ = ((leafTexts [x, ..rest]).all q && (leafTexts acc).all q) :=
          rewrite textsCons x rest, List.allAppendAnd (triviaTexts x.trivia) (leafTexts rest) q then cases

theorem laidOnto ∀ (behind rest: List Leaf)
    (back: laidBack behind = True)
    (fwd: laidOut (pendB behind) rest = True):
    laidOut False (behind.reverseOnto rest) = True :=
  match behind with
    | [] => fwd
    | [leaf, ..older] =>
      laidOnto older
        [leaf, ..rest]
        (Bool.andRight (Bool.andRight back))
        (Bool.andIntro (Bool.andLeft back) (Bool.andIntro (Bool.andLeft (Bool.andRight back)) fwd))

theorem plainOfJoin ∀ (out: List Leaf) (join: sourceJoin out [] = True): plain1 (tokens (out.reverseOnto [])) = True :=
  match out with
    | [] => byComputing
    | [newest, ..older] =>
      plainOfBack
        (tokens ([newest, ..older].reverseOnto []))
        (rewrite tokensReverseOnto [newest, ..older] [], List.reverseReverse (tokens [newest, ..older]) then
          Bool.andLeft join)

--| `isMarked`, of the token alone.
def markedToken (token: Token): Bool :=
  isCloserText token.text == token.kind.isCloser && (operatorTok token.text == Some Arrow) == (token.kind == Arrow)

theorem markedTokens ∀ (leaves: List Leaf): leaves.all isMarked = (tokens leaves).all markedToken := match leaves with
  | [] => byComputing
  | [leaf, ..rest] => rewrite markedTokens rest

theorem wordsOfReverseOnto ∀ (xs acc: List Leaf):
    wordsOf (xs.reverseOnto acc) = (wordsOf xs).reverseOnto (wordsOf acc) :=
  match xs with
    | [] => byComputing
    | [x, ..rest] =>
      match isComma: x.token.kind == Comma with
        | True =>
          calc wordsOf (rest.reverseOnto [x, ..acc])
            _ = (wordsOf rest).reverseOnto (wordsOf [x, ..acc]) := wordsOfReverseOnto rest [x, ..acc]
            _ = (wordsOf rest).reverseOnto (wordsOf acc) := rewrite wordsOfComma x acc isComma
        | False =>
          calc wordsOf (rest.reverseOnto [x, ..acc])
            _ = (wordsOf rest).reverseOnto (wordsOf [x, ..acc]) := wordsOfReverseOnto rest [x, ..acc]
            _ = (wordsOf rest).reverseOnto [x.word, ..wordsOf acc] := rewrite wordsOfItem x acc isComma

theorem allTrimmed ∀ (texts: List Text)
    (raw: texts.all (text => text.startsWith "--" && !text.contains "\n") = True):
    (texts.map trimEnd).all commentText = True :=
  match texts with
    | [] => byComputing
    | [text, ..rest] =>
      Bool.andIntro
        (trimmedComment text (Bool.andLeft (Bool.andLeft raw)) (Bool.andRight (Bool.andLeft raw)).read)
        (allTrimmed rest (Bool.andRight raw))

-- The end of the file.

theorem intoTrailing ∀ (carry: Carried) (trivia: Trivia): (carry.into trivia).trailing = trivia.trailing :=
  match trivia with | { leading, blankLines, trailing } => cases leading then byComputing

--| The comma carry leaves the end's trailing comment as it was: a carried comment goes in front of the own-line ones.
theorem commasEndTrailing ∀ (done: List Leaf) (carried: Option Carried) (rest: List Leaf) (end: Trivia):
    (commasFrom done carried rest end).end.trailing = end.trailing :=
  match rest with
    | [] =>
      match carried with
        | None => byComputing
        | Some held => intoTrailing held end
    | [leaf, ..after] =>
      let step := (x: Leaf) (next: Option Carried) => commasEndTrailing [x, ..done] next after end
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

theorem noneOf ∀ (option: Option Comment) (none: option.isNone = True): option = None := match option with
  | None => byComputing

--| No trailing comment comes out where none went in.
theorem settledEndNone ∀ (lexed: Lexed)
    (none: lexed.end.trailing.isNone = True):
    lexed.settled.end.trailing.isNone = True :=
  let homed := homeFrom False [] None lexed.leaves
  let kept: (commasFrom [] None homed lexed.end).end.trailing = None :=
    Eq.trans (commasEndTrailing [] None homed lexed.end) (noneOf lexed.end.trailing none)
  match trailing: (commasFrom [] None homed lexed.end).end.trailing with | None => byComputing

theorem wordsOfCons ∀ (leaf: Leaf) (first second: List Leaf)
    (same: wordsOf first = wordsOf second):
    wordsOf [leaf, ..first] = wordsOf [leaf, ..second] :=
  match isComma: leaf.token.kind == Comma with
    | True => same
    | False => Eq.cong (tail => [leaf.word, ..tail]) same

--| Line starts are no part of a word.
theorem wordsOfUnstarted ∀ (leaves: List Leaf): wordsOf (leaves.map Leaf.unstarted) = wordsOf leaves :=
  match leaves with
    | [] => byComputing
    | [leaf, ..rest] =>
      match isComma: leaf.token.kind == Comma with
        | True => wordsOfUnstarted rest
        | False => Eq.cong (tail => [leaf.word, ..tail]) (wordsOfUnstarted rest)

--| Dropping the last commas drops no word: a comma is no word.
theorem wordsOfDropF ∀ (behind rest: List Leaf): wordsOf (dropF behind rest) = wordsOf rest := match rest with
  | [] => byComputing
  | [leaf, ..after] =>
    match after with
      | [] => wordsOfCons leaf (dropF [leaf, ..behind] []) [] byComputing
      | [closer, ..after2] =>
        match pair: lastPair closer.token.kind leaf behind with
          | True =>
            let isComma: (leaf.token.kind == Comma) = True := Bool.andLeft pair
            rewrite wordsOfComma leaf [closer, ..after2] isComma then
              wordsOfCons closer
                (dropF [closer, leaf, ..behind] after2)
                after2
                (wordsOfDropF [closer, leaf, ..behind] after2)
          | False =>
            wordsOfCons leaf
              (dropF [leaf, ..behind] [closer, ..after2])
              [closer, ..after2]
              (wordsOfDropF [leaf, ..behind] [closer, ..after2])

theorem endTexts ∀ (trivia: Trivia): trivia.comments.texts = triviaTexts trivia :=
  rewrite noteTexts trivia.leading, optionTexts trivia.trailing

theorem endAfterNone ∀ (trivia: Trivia) (none: trivia.trailing.isNone = True): trivia.comments.after.isNone = True :=
  match trivia.trailing with | None => byComputing

-- The leaves the formatter parses, read as words, are settled.

--| `settledWords`, `Lexed.wordsSettled1` of `Syntax.ParseSettledStatements` for the leaves comment placement makes bare
--| (`settledOnce`).
def settledWordsOf (words: List Word): Bool :=
  homedBack words.reverse && arrowsBare words && words.all (word => word.comments.texts.all commentText)

--| The words of the leaves are settled, and so is the end.
def settledLexed (lexed: Lexed): Bool :=
  settledWordsOf (wordsOf lexed.leaves) && lexed.end.comments.texts.all commentText && lexed.end.comments.after.isNone

theorem settledFrom ∀ (once bare: Lexed)
    (wordsEq: wordsOf once.leaves = wordsOf bare.leaves)
    (endEq: once.end = bare.end)
    (homed: homedBack (wordsOf bare.leaves).reverse = True)
    (arrows: arrowsBare (wordsOf bare.leaves) = True)
    (texts: (wordsOf bare.leaves).all (word => word.comments.texts.all commentText) = True)
    (endTexts: bare.end.comments.texts.all commentText = True)
    (after: bare.end.comments.after.isNone = True):
    settledLexed once = True :=
  rewrite wordsEq, endEq then
    Bool.andIntro (Bool.andIntro homed (Bool.andIntro arrows texts)) (Bool.andIntro endTexts after)

--| The leaves the formatter parses, `settledOnce`, are settled as words: closers homed, `->` bare, every comment as
--| comment placement leaves it, and the end likewise. For leaves of slice 1's alphabet that are `sourcePlain1`, laid out as the lexer lays
--| them out, each token's text agreeing with its kind (`isMarked`), with comments `--` to the end of a line.
--|
--| Proof idea: `settledOnce` is `settledBare` with last commas, all bare, left in, up to line starts (`bareSettles`),
--| and a comma is no word, nor a line start part of one, so the words are those of `settledBare`, comment placement on `withoutLastCommas` of the leaves. That keeps the leaves
--| laid out, `plain`, in the alphabet and `marked`, and every comment's text (`laidWithout`, `plainWithout`,
--| `allTokensWithout`, `textsWithout`: a last comma that doesn't start its line holds no own-line comment, so only its
--| trailing comment moves, to the leaf before; one that does start its line moves its comments above the closer, which
--| then starts its line). So comment placement's facts apply to it: `settledHomed`,
--| `settledArrowsBare1`, `settledCommasBare`, `settledKeepsComments`. They are said of leaves; the words' versions
--| follow (`homedWords`: a closer's look back passes only bare commas, and `endsOnTrails` reads a comment ending the
--| line off the words; `arrowsWords`: no comma follows a `->`; `trimmedComment`: a trimmed `--` comment is a
--| `commentText`).
theorem onceSettledProved ∀ (lexed: Lexed)
    (within: alphabet1 lexed.leaves = True)
    (plain: sourcePlain1 (tokens lexed.leaves) = True)
    (laid: laidOut False lexed.leaves = True)
    (marked: lexed.leaves.all isMarked = True)
    (raw: (lexedTexts lexed).all (text => text.startsWith "--" && !text.contains "\n") = True)
    (noTrailing: lexed.end.trailing.isNone = True):
    settledLexed lexed.settledOnce = True :=
  let leaves := lexed.leaves
  let plainF := sourcePlainFromOf (tokens leaves) plain
  let out := withoutR [] leaves
  let swapped: withoutLastCommas [] leaves = out.reverseOnto [] := withoutFromR [] leaves
  let lexedB: Lexed := { lexed | leaves = withoutLastCommas [] lexed.leaves }
  let laidB: laidOut False lexedB.leaves = True :=
    rewrite swapped then laidOnto out [] (laidWithout [] leaves byComputing laid) byComputing
  let plainB: plain1 (tokens lexedB.leaves) = True :=
    rewrite swapped then plainOfJoin out (plainWithout [] leaves (joinStart leaves plain) plainF)
  let tokensB: ∀ (q: Token → Bool) (blind: ∀ (token: Token) (start: Bool) => q { token | lineStart = start }
    = q token) (kept: (tokens leaves).all q = True) => (tokens lexedB.leaves).all q = True :=
    q blind kept =>
      rewrite swapped, tokensReverseOnto out [], List.allReverseOntoAnd (tokens out) [] q then
        Bool.andIntro (allTokensWithout q blind [] leaves byComputing kept) byComputing
  let withinB: alphabet1 lexedB.leaves = True :=
    tokensB (token => token.kind.within1) (token start => byComputing) within
  let markedB: lexedB.leaves.all isMarked = True :=
    rewrite markedTokens lexedB.leaves then
      tokensB markedToken (token start => byComputing) (rewrite <- markedTokens leaves then marked)
  let rawSplit :=
    rewrite leavesTextsSplit leaves lexed.end,
        List.allAppendAnd (leafTexts leaves) (triviaTexts lexed.end) (text =>
          text.startsWith "--" && !text.contains "\n") at raw then
      raw
  let rawLeavesB: (leafTexts lexedB.leaves).all (text => text.startsWith "--" && !text.contains "\n") = True :=
    rewrite swapped, textsReverseOnto (text => text.startsWith "--" && !text.contains "\n") out [] then
      Bool.andIntro
        (textsWithout
          (text => text.startsWith "--" && !text.contains "\n")
          []
          leaves
          byComputing
          laid
          byComputing
          (Bool.andLeft rawSplit))
        byComputing
  let rawB: (lexedTexts lexedB).all (text => text.startsWith "--" && !text.contains "\n") = True :=
    rewrite leavesTextsSplit lexedB.leaves lexedB.end,
        List.allAppendAnd (leafTexts lexedB.leaves) (triviaTexts lexedB.end) (text =>
          text.startsWith "--" && !text.contains "\n") then
      Bool.andIntro rawLeavesB (Bool.andRight rawSplit)
  let settled := lexedB.settled
  let homedS := settledHomed lexedB withinB laidB plainB
  let bareS := settledCommasBare lexedB
  let tokensS: tokens settled.leaves = tokens lexedB.leaves := settledKeepsTokens lexedB
  let plainS: plainFrom (tokens settled.leaves) = True := rewrite tokensS then plainFromOf (tokens lexedB.leaves) plainB
  let markedS: settled.leaves.all isMarked = True :=
    rewrite markedTokens settled.leaves, tokensS, <- markedTokens lexedB.leaves then markedB
  let arrowsS := settledArrowsBare1 lexedB withinB
  let textsS: (lexedTexts settled).all commentText = True :=
    rewrite settledKeepsComments lexedB withinB laidB then allTrimmed (lexedTexts lexedB) rawB
  let (leavesEq, endEq) := bareSettles lexed within plain
  let dropped := dropF [] lexed.settledOnce.leaves
  let wordsEq: wordsOf lexed.settledOnce.leaves = wordsOf settled.leaves := calc wordsOf lexed.settledOnce.leaves
    _ = wordsOf dropped := (wordsOfDropF [] lexed.settledOnce.leaves).flipped
    _ = wordsOf (dropped.map Leaf.unstarted) := (wordsOfUnstarted dropped).flipped
    _ = wordsOf (settled.leaves.map Leaf.unstarted) := rewrite leavesEq
    _ = wordsOf settled.leaves := wordsOfUnstarted settled.leaves
  let reversedWords := wordsOfReverseOnto settled.leaves []
  let bareR: (settled.leaves.reverseOnto []).all bareComma = True :=
    rewrite List.allReverseOntoAnd settled.leaves [] bareComma then Bool.andIntro bareS byComputing
  let markedR: (settled.leaves.reverseOnto []).all isMarked = True :=
    rewrite List.allReverseOntoAnd settled.leaves [] isMarked then Bool.andIntro markedS byComputing
  let homedWordsS: homedBack (wordsOf settled.leaves).reverse = True :=
    rewrite <- reversedWords then homedWords (settled.leaves.reverseOnto []) homedS bareR markedR
  let textsSplit :=
    rewrite leavesTextsSplit settled.leaves settled.end,
        List.allAppendAnd (leafTexts settled.leaves) (triviaTexts settled.end) commentText at textsS then
      textsS
  let wordTextsS := wordsCommentTexts settled.leaves (leavesCommentTexts settled.leaves (Bool.andLeft textsSplit))
  let endTextsS: lexedB.settled.end.comments.texts.all commentText = True :=
    rewrite endTexts lexedB.settled.end then Bool.andRight textsSplit
  let afterNone := endAfterNone lexedB.settled.end (settledEndNone lexedB noTrailing)
  settledFrom lexed.settledOnce settled wordsEq endEq homedWordsS
    (arrowsWords settled.leaves arrowsS plainS markedS)
    wordTextsS
    endTextsS
    afterNone
