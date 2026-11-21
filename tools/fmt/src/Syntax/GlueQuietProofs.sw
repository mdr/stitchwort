--| Glued signs carry no comments (SW-4081): in the leaves the parser reads, a `-` or `!` with an atom's first token
--| glued to it on its line has no trailing comment, and that token no own-line comments. The parser reads a sign as a
--| call argument's (`f -x`) or a head's negative numeral (`-1 n`) only when the next item is glued, so this is what
--| `callArgument` and `callHead` need of the items (their `signQuiet`, through `GoodItems` in `Syntax.ParseWalk`).
--|
--| The lexer's leaves are laid out (`laidOut`: a leaf with own-line comments, or after a trailing comment, starts its
--| line), which gives it at once. Comment placement moves comments, and breaks `laidOut` (in `a, -- c` the comment goes back to
--| `a`, with the `,` still glued to it), but every comment it moves lands where no sign meets a glued atom: on a leaf
--| followed by a comma, closer or bar (the back-walk, and the last commas' comments), on a comma's next leaf (the comma carry), on
--| `->` or `:=` (the arrow lift and let lift), or nowhere new (trim).

namespace Syntax.GlueQuietProofs
import Std (Bool, DecEq, Eq, List, Nat, Option, Result, Text, Void)
import Syntax (..)
import Syntax.ParseProofs (..)
import Syntax.SettleProofs (alphabet1, laidOut)
import Syntax.SettleSplitProofs (groupsConcat)
import Syntax.LexLaidProofs (lexLaidProved)
import Syntax.SettleOnceProofs (intoTrailing)
import Syntax.SettleBareProofs (fwdPair, withBareFromR, withBareR)

-- The invariant.

--| A sign and the leaf after it: if that leaf opens an atom on the same line, the sign has no trailing comment and
--| the leaf no own-line comments.
def glueQuiet (sign next: Leaf): Bool :=
  quietOf sign.kind.signLike next.token.lineStart next.kind.opensAtom sign.trivia.trailing.isNone
      next.trivia.leading.isEmpty

--| `glueQuiet` of each leaf and the one after it.
def gluesQuiet: List Leaf → Bool
  | [] => True
  | [first, ..rest] => gluesQuietAfter first rest

def gluesQuietAfter (previous: Leaf) (rest: List Leaf): Bool := match rest with
  | [] => True
  | [next, ..more] => glueQuiet previous next && gluesQuietAfter next more

--| The same, newest leaf first: each leaf and the one before it.
def gluesQuietBack: List Leaf → Bool
  | [] => True
  | [newest, ..older] => gluesQuietBackAfter newest older

def gluesQuietBackAfter (newer: Leaf) (older: List Leaf): Bool := match older with
  | [] => True
  | [previous, ..earlier] => glueQuiet previous newer && gluesQuietBackAfter previous earlier

-- Facts about one pair.

theorem quietUntrail ∀ (s l o t e: Bool) (quiet: quietOf s l o t e = True): quietOf s l o True e = True :=
  match s, l, o, t, e, quiet with
    | False, _, _, _, _, _ => byComputing
    | True, True, _, _, _, _ => byComputing
    | True, False, False, _, _, _ => byComputing
    | True, False, True, True, True, _ => byComputing

theorem quietNotSign ∀ (l o t e: Bool): quietOf False l o t e = True := byComputing

theorem quietNotOpens ∀ (s l t e: Bool): quietOf s l False t e = True := cases s, l then byComputing

theorem quietStarts ∀ (s o t e: Bool): quietOf s True o t e = True := match s with | False | True => byComputing

theorem quietBoth ∀ (s l o: Bool): quietOf s l o True True = True := cases s, l, o then byComputing

theorem isNoneOfSome ∀ (option: Option Comment) (none: option.isSome = False): option.isNone = True := match option with
  | None => byComputing

-- The lexer's leaves.

--| A leaf laid out after `previous` is quiet after it: one with own-line comments, or after a trailing comment,
--| starts its line.
theorem laidQuietAfter ∀ (previous: Leaf) (rest: List Leaf)
    (laid: laidOut previous.trivia.trailing.isSome rest = True):
    gluesQuietAfter previous rest = True :=
  match rest with
    | [] => byComputing
    | [next, ..more] =>
      let ledOk := Bool.andLeft laid
      let afterOk := Bool.andLeft (Bool.andRight laid)
      let moreLaid := Bool.andRight (Bool.andRight laid)
      let pair: glueQuiet previous next = True := match starts: next.token.lineStart with
        | True =>
          quietStarts previous.kind.signLike next.kind.opensAtom previous.trivia.trailing.isNone
              next.trivia.leading.isEmpty
        | False =>
          let unled: next.trivia.leading.isEmpty = True := Bool.orFalseTrue _ ledOk
          let untrailed: previous.trivia.trailing.isSome = False := Bool.notTrue _ (Bool.orFalseTrue _ afterOk)
          rewrite isNoneOfSome previous.trivia.trailing untrailed, unled then
            quietBoth previous.kind.signLike False next.kind.opensAtom
      Bool.andIntro pair (laidQuietAfter next more moreLaid)

--| Leaves laid out as the lexer lays them out are quiet.
theorem laidQuiet ∀ (leaves: List Leaf) (pending: Bool)
    (laid: laidOut pending leaves = True):
    gluesQuiet leaves = True :=
  match leaves with
    | [] => byComputing
    | [first, ..rest] => laidQuietAfter first rest (Bool.andRight (Bool.andRight laid))

-- Trim: trimming keeps which comments there are.

def Leaf.trimmed (leaf: Leaf): Leaf := { leaf | trivia = leaf.trivia.trimmed }

theorem trailingTrimmed ∀ (leaf: Leaf): leaf.trimmed.trivia.trailing.isNone = leaf.trivia.trailing.isNone :=
  match leaf.trivia.trailing with | None | Some _ => byComputing

theorem leadingTrimmed ∀ (leaf: Leaf): leaf.trimmed.trivia.leading.isEmpty = leaf.trivia.leading.isEmpty :=
  match leaf.trivia.leading with | [] | [_, .._] => byComputing

theorem trimmedQuiet ∀ (sign next: Leaf): glueQuiet sign.trimmed next.trimmed = glueQuiet sign next := calc glueQuiet
    sign.trimmed next.trimmed
  _ = quietOf sign.kind.signLike next.token.lineStart next.kind.opensAtom sign.trimmed.trivia.trailing.isNone
        next.trimmed.trivia.leading.isEmpty := byComputing
  _ = glueQuiet sign next := rewrite trailingTrimmed sign, leadingTrimmed next

theorem trimmedQuietAfter ∀ (previous: Leaf) (rest: List Leaf)
    (quiet: gluesQuietAfter previous rest = True):
    gluesQuietAfter previous.trimmed (rest.map Leaf.trimmed) = True :=
  match rest with
    | [] => byComputing
    | [next, ..more] =>
      Bool.andIntro
        (rewrite trimmedQuiet previous next then Bool.andLeft quiet)
        (trimmedQuietAfter next more (Bool.andRight quiet))

theorem trimmedQuietAll ∀ (leaves: List Leaf)
    (quiet: gluesQuiet leaves = True):
    gluesQuiet (leaves.map (leaf => { leaf | trivia = leaf.trivia.trimmed })) = True :=
  match leaves with
    | [] => byComputing
    | [first, ..rest] => trimmedQuietAfter first rest quiet

-- The comma carry, arrow lift and let lift: comments taken off a leaf, or put on a leaf that opens no atom, or above the leaf after a comma.

--| `after` is `before` with no comment added where `glueQuiet` reads one: the same token, a trailing comment only
--| if `before` had one, and own-line comments on an atom's first token only if `before` had some or `free` (the leaf
--| before is a comma, which is no sign).
def Loose (free: Bool) (before after: Leaf): Prop :=
  after.token = before.token
    ∧ (!before.trivia.trailing.isNone || after.trivia.trailing.isNone) = True
    ∧ (free || !before.kind.opensAtom || !before.trivia.leading.isEmpty || after.trivia.leading.isEmpty) = True

--| `Loose` leaf by leaf, each leaf after a comma free.
def LooseAll (free: Bool) (befores afters: List Leaf): Prop := match befores, afters with
  | [], [] => Std.Unit
  | [before, ..more], [after, ..rest] => Loose free before after ∧ LooseAll (before.kind == Comma) more rest
  | _, _ => Void

theorem quietLoose ∀ (s l o t e t2 e2 f: Bool)
    (quiet: quietOf s l o t e = True)
    (trail: (!t || t2) = True)
    (lead: (f || !o || !e || e2) = True)
    (comma: (!f || !s) = True):
    quietOf s l o t2 e2 = True :=
  match s with
    | False => byComputing
    | True =>
      match l with
        | True => byComputing
        | False =>
          match o with
            | False => byComputing
            | True =>
              match f, t, e, t2, e2, quiet, trail, lead, comma with
                | False, True, True, True, True, _, _, _, _ => byComputing

theorem commaNotSign ∀ (kind: Tok): (!(kind == Comma) || !kind.signLike) = True := match kind with
  | Comma | _ => byComputing

theorem looseQuiet ∀ (free: Bool) (sign next sign2 next2: Leaf)
    (quiet: glueQuiet sign next = True)
    (signLoose: Loose free sign sign2)
    (nextLoose: Loose (sign.kind == Comma) next next2):
    glueQuiet sign2 next2 = True :=
  let (signToken, signTrail, signLead) := signLoose
  let (nextToken, nextTrail, nextLead) := nextLoose
  let signKind: sign2.kind = sign.kind := rewrite signToken
  calc glueQuiet sign2 next2
    _ = quietOf sign2.token.kind.signLike next2.token.lineStart next2.token.kind.opensAtom sign2.trivia.trailing.isNone
          next2.trivia.leading.isEmpty := byComputing
    _ = quietOf sign.token.kind.signLike next.token.lineStart next.token.kind.opensAtom sign2.trivia.trailing.isNone
          next2.trivia.leading.isEmpty := rewrite signToken, nextToken
    _ = True :=
      quietLoose sign.kind.signLike next.token.lineStart next.kind.opensAtom sign.trivia.trailing.isNone
          next.trivia.leading.isEmpty sign2.trivia.trailing.isNone next2.trivia.leading.isEmpty
          (sign.kind == Comma)
          quiet
          signTrail
          nextLead
          (commaNotSign sign.kind)

theorem looseQuietAfter ∀ (free: Bool) (previous previous2: Leaf) (rest rest2: List Leaf)
    (quiet: gluesQuietAfter previous rest = True)
    (loose: Loose free previous previous2)
    (looseRest: LooseAll (previous.kind == Comma) rest rest2):
    gluesQuietAfter previous2 rest2 = True :=
  match rest, rest2, looseRest with
    | [], [], _ => byComputing
    | [next, ..more], [next2, ..more2], (nextLoose, moreLoose) =>
      Bool.andIntro
        (looseQuiet free previous next previous2 next2 (Bool.andLeft quiet) loose nextLoose)
        (looseQuietAfter (previous.kind == Comma) next next2 more more2 (Bool.andRight quiet) nextLoose moreLoose)

theorem looseQuietAll ∀ (befores afters: List Leaf)
    (quiet: gluesQuiet befores = True)
    (loose: LooseAll False befores afters):
    gluesQuiet afters = True :=
  match befores, afters, loose with
    | [], [], _ => byComputing
    | [first, ..rest], [first2, ..rest2], (firstLoose, restLoose) =>
      looseQuietAfter False first first2 rest rest2 quiet firstLoose restLoose

theorem looseSelf ∀ (free: Bool) (leaf: Leaf): Loose free leaf leaf := (
  byComputing,
  match leaf.trivia.trailing.isNone with
    | True => byComputing
    | False => byComputing,
  match leaf.trivia.leading.isEmpty with
    | True | False =>
      match free with
        | True => byComputing
        | False =>
          match leaf.kind.opensAtom with
            | True | False => byComputing
)

--| A leaf that opens no atom, with its trailing comment taken off (if any) and own-line comments put on.
theorem loosePlain ∀ (free: Bool) (leaf after: Leaf)
    (token: after.token = leaf.token)
    (untrailed: after.trivia.trailing.isNone = True)
    (plain: leaf.kind.opensAtom = False):
    Loose free leaf after :=
  (
    token,
    rewrite untrailed then
      match leaf.trivia.trailing.isNone with
        | True => byComputing
        | False => byComputing,
    rewrite plain then match free with | True | False => byComputing
  )

theorem kindIs ∀ (kind: Tok) (is: kind = ColonEq): kind.opensAtom = False := rewrite is

-- The let lift.

theorem letsLoose ∀ (free: Bool) (behind rest: List Leaf):
    ∃ (out: List Leaf) => letsFrom behind rest = behind.reverseOnto out ∧ LooseAll free rest out :=
  match rest with
    | [] => ([], byComputing, Trivial)
    | [leaf, ..after] =>
      match trailing: leaf.trivia.trailing with
        | None =>
          let (out, same, loose) := letsLoose (leaf.kind == Comma) [leaf, ..behind] after
          ([leaf, ..out], same, (looseSelf free leaf, loose))
        | Some comment =>
          match guard: (leaf.kind == ColonEq && letBefore behind 0 && semicolonAfter after 0) with
            | True =>
              let moved := { leaf |
                trivia = { leaf.trivia | leading = leaf.trivia.leading ++ [comment.unspaced], trailing = None }
              }
              let (out, same, loose) := letsLoose (leaf.kind == Comma) [moved, ..behind] after
              (
                [moved, ..out],
                same,
                (
                  loosePlain free leaf moved byComputing byComputing
                    (kindIs leaf.kind (DecEq.sound (Bool.andLeft guard))),
                  loose
                )
              )
            | False =>
              let (out, same, loose) := letsLoose (leaf.kind == Comma) [leaf, ..behind] after
              ([leaf, ..out], same, (looseSelf free leaf, loose))

-- The arrow lift.

theorem looseUnled ∀ (free: Bool) (leaf: Leaf): Loose free leaf (leaf.withLeading []) := (
  byComputing,
  match leaf.trivia.trailing.isNone with
    | True => byComputing
    | False => byComputing,
  match free with
    | True => byComputing
    | False =>
      match leaf.kind.opensAtom with
        | True =>
          match leaf.trivia.leading.isEmpty with
            | True | False => byComputing
        | False => byComputing
)

theorem arrowKind ∀ (orig current: Leaf)
    (token: current.token = orig.token)
    (is: current.kind = Arrow):
    orig.kind.opensAtom = False :=
  let same: orig.kind = Arrow := rewrite <- token then is
  rewrite same

theorem arrowsLoose ∀ (free: Bool) (done: List Leaf) (orig current: Leaf) (rest: List Leaf)
    (loose: Loose free orig current):
    ∃ (out: List Leaf) => arrowsFrom done current rest = done.reverseOnto out ∧ LooseAll free [orig, ..rest] out :=
  match rest with
    | [] => ([current], byComputing, (loose, Trivial))
    | [next, ..more] =>
      match guard: (current.kind == Arrow && (!next.trivia.leading.isEmpty || current.trivia.trailing.isSome)) with
        | True =>
          let own := current.trivia.trailing.map (comment => [comment.unspaced]) |> .getOrElse []
          let moved := { current |
            trivia = { current.trivia |
              leading = current.trivia.leading ++ own ++ next.trivia.leading,
              trailing = None
            }
          }
          let (out, same, looseRest) :=
            arrowsLoose
              (orig.kind == Comma)
              [moved, ..done]
              next
              (next.withLeading [])
              more
              (looseUnled (orig.kind == Comma) next)
          let (token, _, _) := loose
          (
            [moved, ..out],
            same,
            (
              loosePlain free orig moved token byComputing
                (arrowKind orig current token (DecEq.sound (Bool.andLeft guard))),
              looseRest
            )
          )
        | False =>
          let (out, same, looseRest) :=
            arrowsLoose (orig.kind == Comma) [current, ..done] next next more (looseSelf (orig.kind == Comma) next)
          ([current, ..out], same, (loose, looseRest))

theorem arrowsQuiet ∀ (leaves: List Leaf) (quiet: gluesQuiet leaves = True): gluesQuiet (arrows leaves) = True :=
  match leaves with
    | [] => byComputing
    | [first, ..rest] =>
      let (out, same, loose) := arrowsLoose False [] first first rest (looseSelf False first)
      rewrite same then looseQuietAll [first, ..rest] out quiet loose

theorem letsQuiet ∀ (leaves: List Leaf) (quiet: gluesQuiet leaves = True): gluesQuiet (letsFrom [] leaves) = True :=
  let (out, same, loose) := letsLoose False [] leaves
  rewrite same then looseQuietAll leaves out quiet loose

-- The comma carry.

theorem looseReceived ∀ (leaf: Leaf) (carry: Carried): Loose True leaf { leaf | trivia = carry.into leaf.trivia } := (
  byComputing,
  rewrite intoTrailing carry leaf.trivia then
    match leaf.trivia.trailing.isNone with
      | True => byComputing
      | False => byComputing,
  byComputing
)

theorem looseEmptied ∀ (free: Bool) (leaf after: Leaf)
    (token: after.token = leaf.token)
    (untrailed: after.trivia.trailing.isNone = True)
    (unled: after.trivia.leading.isEmpty = True):
    Loose free leaf after :=
  (
    token,
    rewrite untrailed then
      match leaf.trivia.trailing.isNone with
        | True => byComputing
        | False => byComputing,
    rewrite unled then
      match free with
        | True => byComputing
        | False =>
          match leaf.kind.opensAtom with
            | True =>
              match leaf.trivia.leading.isEmpty with
                | True | False => byComputing
            | False => byComputing
  )

theorem commasLoose ∀ (free: Bool) (done: List Leaf) (carried: Option Carried) (rest: List Leaf) (end: Trivia)
    (freed: (!carried.isSome || free) = True):
    ∃ (out: List Leaf) => (commasFrom done carried rest end).leaves = done.reverseOnto out ∧ LooseAll free rest out :=
  match rest with
    | [] => ([], byComputing, Trivial)
    | [leaf, ..after] =>
      match carried with
        | None =>
          match carries: commaCarries leaf.trivia with
            | Some carry =>
              match comma: leaf.kind == Comma with
                | True =>
                  let emptied := { leaf | trivia = Trivia.empty }
                  let (out, same, looseRest) := commasLoose True [emptied, ..done] (Some carry) after end byComputing
                  (
                    [emptied, ..out],
                    same,
                    (looseEmptied free leaf emptied byComputing byComputing byComputing, looseRest)
                  )
                | False =>
                  let (out, same, looseRest) := commasLoose False [leaf, ..done] None after end byComputing
                  ([leaf, ..out], same, (looseSelf free leaf, looseRest))
            | None =>
              let (out, same, looseRest) := commasLoose (leaf.kind == Comma) [leaf, ..done] None after end byComputing
              ([leaf, ..out], same, (looseSelf free leaf, looseRest))
        | Some carried =>
          let isFree: free = True := rewrite <- freed
          let received := { leaf | trivia = carried.into leaf.trivia }
          rewrite isFree then
            match carries: commaCarries (carried.into leaf.trivia) with
              | Some carry =>
                match comma: leaf.kind == Comma with
                  | True =>
                    let emptied := { received | trivia = Trivia.empty }
                    let (out, same, looseRest) := commasLoose True [emptied, ..done] (Some carry) after end byComputing
                    (
                      [emptied, ..out],
                      same,
                      (looseEmptied True leaf emptied byComputing byComputing byComputing, looseRest)
                    )
                  | False =>
                    let (out, same, looseRest) := commasLoose False [received, ..done] None after end byComputing
                    ([received, ..out], same, (looseReceived leaf carried, looseRest))
              | None =>
                let (out, same, looseRest) :=
                  commasLoose (leaf.kind == Comma) [received, ..done] None after end byComputing
                ([received, ..out], same, (looseReceived leaf carried, looseRest))

theorem commasQuiet ∀ (leaves: List Leaf) (end: Trivia)
    (quiet: gluesQuiet leaves = True):
    gluesQuiet (commasFrom [] None leaves end).leaves = True :=
  let (out, same, loose) := commasLoose False [] None leaves end byComputing
  rewrite same then looseQuietAll leaves out quiet loose

-- Back-walk: a comment moved back lands on a leaf followed by a comma or closer.

--| The pair at the seam of `behind` (newest first) and `rest`.
def edgeQuiet (behind rest: List Leaf): Bool := match behind, rest with
  | [newest, .._], [next, .._] => glueQuiet newest next
  | _, _ => True

theorem tailQuiet ∀ (first: Leaf) (rest: List Leaf)
    (quiet: gluesQuietAfter first rest = True):
    gluesQuiet rest = True :=
  match rest with
    | [] => byComputing
    | [next, ..more] => Bool.andRight quiet

--| Leaves newest first, put back in order in front of `acc`, are quiet.
theorem reverseQuiet ∀ (behind acc: List Leaf)
    (back: gluesQuietBack behind = True)
    (quiet: gluesQuiet acc = True)
    (edge: edgeQuiet behind acc = True):
    gluesQuiet (behind.reverseOnto acc) = True :=
  match behind with
    | [] => quiet
    | [newest, ..older] =>
      let accQuiet: gluesQuietAfter newest acc = True := match acc with
        | [] => byComputing
        | [next, ..more] => Bool.andIntro edge quiet
      match older with
        | [] => accQuiet
        | [previous, ..earlier] =>
          reverseQuiet [previous, ..earlier] [newest, ..acc] (Bool.andRight back) accQuiet (Bool.andLeft back)

--| `glueQuiet` reads of the later leaf only its line start, kind and own-line comments.
theorem backUntrail ∀ (leaf: Leaf) (trailing: Option Comment) (older: List Leaf):
    gluesQuietBackAfter (leaf.withTrailing trailing) older = gluesQuietBackAfter leaf older :=
  match older with | [] | [_, .._] => byComputing

theorem closerPlain ∀ (kind: Tok) (closer: kind.isCloser = True): kind.opensAtom = False := match kind, closer with
  | RParen | RBracket | RBrace, _ => byComputing

--| What the back-walk walks past opens no atom.
theorem skippedPlain ∀ (leaf: Leaf) (behind ahead: List Leaf)
    (skips: skipped leaf behind ahead = True):
    leaf.kind.opensAtom = False :=
  match comma: leaf.kind == Comma with
    | True => rewrite DecEq.sound comma
    | False =>
      match pipe: leaf.kind == Pipe with
        | True => rewrite DecEq.sound pipe
        | False =>
          let closer: leaf.kind.isCloser = True :=
            rewrite skipped.eq.alt3 leaf behind ahead
                  (DecEq.soundFalse leaf.kind Comma comma)
                  (DecEq.soundFalse leaf.kind Pipe pipe) at skips then
              skips
          closerPlain leaf.kind closer

--| A bar whose comment starts the line below is no sign.
theorem barSign ∀ (leaf: Leaf) (behind ahead: List Leaf)
    (below: barBelow leaf behind ahead = True):
    leaf.kind.signLike = False :=
  match sign: leaf.kind.signLike with
    | False => byComputing
    | True =>
      let notPipe: leaf.kind ≠ Pipe := is => Bool.falseNotTrue (rewrite is at sign then sign)
      let off: barBelow leaf behind ahead = False :=
        barBelow.eq.alt2 leaf behind ahead (previous tail head tail2 isBehind isAhead => notPipe)
      (Bool.trueNotFalse (Eq.trans below.flipped off)).impossible

--| The leaves after the one `steps` back from `current` open no atom: `current` and the newest `steps - 1` of
--| `behind`.
def walkPlain (steps: Nat) (current: Leaf) (behind: List Leaf): Bool := match steps, behind with
  | Succ Zero, _ => !current.kind.opensAtom
  | Succ (Succ more), [previous, ..earlier] => !current.kind.opensAtom && walkPlain (Succ more) previous earlier
  | _, _ => False

--| The back-walk passes only leaves that open no atom.
theorem stepsPlain ∀ (bareLast: Bool) (current: Leaf) (behind ahead: List Leaf) (steps: Nat):
    ∃ (passed: Nat) => stepsBack bareLast current behind ahead steps = steps + passed
      ∧ (passed = 0 ∨ walkPlain passed current behind = True) :=
  match behind with
    | [] => (0, arithmetic, Inl byComputing)
    | [previous, ..earlier] =>
      match skips: skipped current [previous, ..earlier] ahead with
        | False => (0, arithmetic, Inl byComputing)
        | True =>
          match stops: startsWalk bareLast current [previous, ..earlier]
            && (!current.trivia.leading.isEmpty || endsWithComment [previous, ..earlier] [current, ..ahead]) with
            | True => (0, arithmetic, Inl byComputing)
            | False =>
              let plain := Bool.notOfFalse _ (skippedPlain current [previous, ..earlier] ahead skips)
              let (passed, walked, more) := stepsPlain bareLast previous earlier [current, ..ahead] (Succ steps)
              let here: walkPlain (Succ passed) current [previous, ..earlier] = True := match passed, more with
                | Zero, _ => plain
                | Succ fewer, Inl zero => cases
                | Succ fewer, Inr walk => Bool.andIntro plain walk
              (Succ passed, rewrite walked then arithmetic, Inr here)

--| A comment moved back over leaves that open no atom keeps the leaves quiet.
theorem trailingAtQuiet ∀ (steps: Nat) (current: Leaf) (behind: List Leaf) (comment: Comment)
    (plain: walkPlain steps current behind = True)
    (back: gluesQuietBackAfter current behind = True):
    gluesQuietBackAfter current (trailingAt behind steps comment) = True :=
  match steps, behind with
    | Succ Zero, [target, ..earlier] =>
      let first: glueQuiet (target.withTrailing (Some comment)) current = True :=
        rewrite Bool.notTrue current.kind.opensAtom plain then
          quietNotOpens target.kind.signLike current.token.lineStart False current.trivia.leading.isEmpty
      Bool.andIntro first (rewrite backUntrail target (Some comment) earlier then Bool.andRight back)
    | Succ (Succ more), [previous, ..earlier] =>
      Bool.andIntro
        (Bool.andLeft back)
        (trailingAtQuiet (Succ more) previous earlier comment (Bool.andRight plain) (Bool.andRight back))
    | Succ Zero, [] => byComputing

--| The seam of the back-walk's leaves settled (newest first) and the leaves left: a sign at the head of `behind` is quiet
--| with the next leaf, which carries no comment from a bar (`bumped`).
def homeEdge (behind: List Leaf) (bumped: Option Comment) (rest: List Leaf): Bool := match behind, rest with
  | [newest, .._], [next, .._] => !newest.kind.signLike || (bumped.isNone && glueQuiet newest next)
  | _, _ => True

theorem edgeNil ∀ (behind: List Leaf): edgeQuiet behind [] = True := match behind with | [] | [_, .._] => byComputing

theorem afterUnlead ∀ (leaf: Leaf) (leading: List Comment) (rest: List Leaf):
    gluesQuietAfter (leaf.withLeading leading) rest = gluesQuietAfter leaf rest :=
  match rest with | [] | [_, .._] => byComputing

theorem edgeOfAfter ∀ (leaf: Leaf) (behind after: List Leaf)
    (nextOk: gluesQuietAfter leaf after = True):
    homeEdge [leaf, ..behind] None after = True :=
  match after with
    | [] => byComputing
    | [next, ..more] => Bool.orRight (Bool.andLeft nextOk)

theorem edgeOfBar ∀ (leaf: Leaf) (behind after: List Leaf) (comment: Comment)
    (notSign: leaf.kind.signLike = False):
    homeEdge [leaf.withTrailing None, ..behind] (Some comment) after = True :=
  match after with
    | [] => byComputing
    | [next, ..more] => Bool.orLeft (Bool.notOfFalse leaf.kind.signLike notSign)

theorem edgeUntrailed ∀ (leaf: Leaf) (behind after: List Leaf)
    (nextOk: gluesQuietAfter leaf after = True):
    homeEdge [leaf.withTrailing None, ..behind] None after = True :=
  match after with
    | [] => byComputing
    | [next, ..more] =>
      Bool.orRight
        (quietUntrail leaf.kind.signLike next.token.lineStart next.kind.opensAtom leaf.trivia.trailing.isNone
            next.trivia.leading.isEmpty
            (Bool.andLeft nextOk))

theorem walkOfSteps ∀ (bareLast: Bool) (leaf: Leaf) (behind after: List Leaf) (fewer: Nat)
    (moved: stepsBack bareLast leaf behind after 0 = Succ fewer):
    walkPlain (Succ fewer) leaf behind = True :=
  let (passed, walked, plain) := stepsPlain bareLast leaf behind after 0
  let same: passed = Succ fewer := arithmetic [walked, moved]
  match plain with
    | Inl zero => (Nat.succNotZero fewer (Eq.trans same.flipped zero)).impossible
    | Inr walk => rewrite <- same then walk

--| The back-walk keeps glued signs quiet.
--|
--| Proof idea: by induction on the leaves left, keeping the settled ones (newest first) quiet and quiet with the next
--| leaf. A leaf whose comment stays is pushed as it is; a bar whose comment goes below pushes it onto the next leaf,
--| after a bar, which is no sign; a comment moved back lands on a leaf followed by leaves that open no atom
--| (`stepsPlain`, `trailingAtQuiet`), and the leaf it left has none.
theorem homeQuiet ∀ (bareLast: Bool) (behind: List Leaf) (bumped: Option Comment) (rest: List Leaf)
    (back: gluesQuietBack behind = True)
    (quiet: gluesQuiet rest = True)
    (edge: homeEdge behind bumped rest = True):
    gluesQuiet (homeFrom bareLast behind bumped rest) = True :=
  match rest with
    | [] => reverseQuiet behind [] back byComputing (edgeNil behind)
    | [leaf0, ..after] =>
      let afterQuiet := tailQuiet leaf0 after quiet
      let kept := (leaf: Leaf) (pushOk: gluesQuietBackAfter leaf behind = True) (nextOk: gluesQuietAfter leaf after
        = True) =>
        homeQuiet bareLast [leaf, ..behind] None after pushOk afterQuiet (edgeOfAfter leaf behind after nextOk)
      let barred := (leaf: Leaf) (comment: Comment) (pushOk: gluesQuietBackAfter leaf behind
        = True) (notSign: leaf.kind.signLike = False) =>
        homeQuiet bareLast
          [leaf.withTrailing None, ..behind]
          (Some comment.unspaced)
          after
          (rewrite backUntrail leaf None behind then pushOk)
          afterQuiet
          (edgeOfBar leaf behind after comment.unspaced notSign)
      let moved := (leaf: Leaf) (comment: Comment) (fewer: Nat) (pushOk: gluesQuietBackAfter leaf behind
        = True) (nextOk: gluesQuietAfter leaf after = True) (walk: stepsBack bareLast leaf behind after 0
        = Succ fewer) =>
        homeQuiet bareLast
          [leaf.withTrailing None, ..trailingAt behind (Succ fewer) comment]
          None
          after
          (rewrite backUntrail leaf None (trailingAt behind (Succ fewer) comment) then
            trailingAtQuiet (Succ fewer) leaf behind comment (walkOfSteps bareLast leaf behind after fewer walk) pushOk)
          afterQuiet
          (edgeUntrailed leaf (trailingAt behind (Succ fewer) comment) after nextOk)
      match bumped with
        | None =>
          let pushOk: gluesQuietBackAfter leaf0 behind = True := match behind with
            | [] => byComputing
            | [newest, ..older] =>
              let pair: glueQuiet newest leaf0 = True := match sign: newest.kind.signLike with
                | False =>
                  quietNotSign leaf0.token.lineStart leaf0.kind.opensAtom newest.trivia.trailing.isNone
                      leaf0.trivia.leading.isEmpty
                | True => edge
              Bool.andIntro pair back
          match trailing: leaf0.trivia.trailing with
            | None => kept leaf0 pushOk quiet
            | Some comment =>
              match mov: movable leaf0 behind after with
                | False => kept leaf0 pushOk quiet
                | True =>
                  match walk: stepsBack bareLast leaf0 behind after 0 with
                    | Zero =>
                      match bar: barBelow leaf0 behind after with
                        | True => barred leaf0 comment pushOk (barSign leaf0 behind after bar)
                        | False => kept leaf0 pushOk quiet
                    | Succ fewer => moved leaf0 comment fewer pushOk quiet walk
        | Some note =>
          let leaf := leaf0.withLeading [note, ..leaf0.trivia.leading]
          let nextOk: gluesQuietAfter leaf after = True :=
            rewrite afterUnlead leaf0 [note, ..leaf0.trivia.leading] after then quiet
          let pushOk: gluesQuietBackAfter leaf behind = True := match behind with
            | [] => byComputing
            | [newest, ..older] =>
              let notSign: newest.kind.signLike = False := Bool.notTrue _ (Bool.orFalseTrue _ edge)
              let pair: glueQuiet newest leaf = True :=
                rewrite notSign then
                  quietNotSign leaf.token.lineStart leaf.kind.opensAtom newest.trivia.trailing.isNone
                      leaf.trivia.leading.isEmpty
              Bool.andIntro pair back
          match trailing: leaf.trivia.trailing with
            | None => kept leaf pushOk nextOk
            | Some comment =>
              match mov: movable leaf behind after with
                | False => kept leaf pushOk nextOk
                | True =>
                  match walk: stepsBack bareLast leaf behind after 0 with
                    | Zero =>
                      match bar: barBelow leaf behind after with
                        | True => barred leaf comment pushOk (barSign leaf behind after bar)
                        | False => kept leaf pushOk nextOk
                    | Succ fewer => moved leaf comment fewer pushOk nextOk walk

-- The last commas made bare: their comments go to the closer after them (no atom) and the leaf before them (before
-- the comma, no atom).

theorem edgeHead ∀ (first: Leaf) (behind rest: List Leaf)
    (quiet: gluesQuietAfter first rest = True):
    edgeQuiet [first, ..behind] rest = True :=
  match rest with
    | [] => byComputing
    | [next, ..more] => Bool.andLeft quiet

theorem pushQuiet ∀ (leaf: Leaf) (behind: List Leaf)
    (back: gluesQuietBack behind = True)
    (edge: edgeQuiet behind [leaf] = True):
    gluesQuietBack [leaf, ..behind] = True :=
  match behind with
    | [] => byComputing
    | [newest, ..older] => Bool.andIntro edge back

theorem movedKind ∀ (comma closer: Leaf) (behind: List Leaf):
    (commaMoved comma closer behind).fst.token.kind = closer.token.kind :=
  match behind with
    | [] =>
      match trailing: comma.trivia.trailing with
        | None => byComputing
        | Some comment => byComputing
    | [previous, ..earlier] =>
      match trailing: comma.trivia.trailing with
        | None => byComputing
        | Some comment =>
          match starts: comma.token.lineStart with
            | True => byComputing
            | False => byComputing

theorem movedBack ∀ (comma closer: Leaf) (behind: List Leaf)
    (back: gluesQuietBack behind = True):
    gluesQuietBack (commaMoved comma closer behind).snd = True :=
  match behind with
    | [] =>
      match trailing: comma.trivia.trailing with
        | None => byComputing
        | Some comment => byComputing
    | [previous, ..earlier] =>
      match trailing: comma.trivia.trailing with
        | None => back
        | Some comment =>
          match starts: comma.token.lineStart with
            | True => back
            | False => rewrite backUntrail previous (Some comment) earlier then back

theorem closerNotSign ∀ (kind: Tok) (closer: kind.isCloser = True): kind.signLike = False := match kind, closer with
  | RParen | RBracket | RBrace, _ => byComputing

--| A bare last comma, between the leaves before it and the closer: a comma is no sign and opens no atom.
theorem bareBack ∀ (moved comma: Leaf) (earlier: List Leaf)
    (isComma: comma.token.kind = Comma)
    (back: gluesQuietBack earlier = True):
    gluesQuietBack [moved, { comma | trivia = Trivia.empty }, ..earlier] = True :=
  let first: glueQuiet { comma | trivia = Trivia.empty } moved = True :=
    rewrite isComma then quietNotSign moved.token.lineStart moved.kind.opensAtom True moved.trivia.leading.isEmpty
  match earlier with
    | [] => Bool.andIntro first byComputing
    | [previous, ..older] =>
      let second: glueQuiet previous { comma | trivia = Trivia.empty } = True :=
        rewrite isComma then
          quietNotOpens previous.kind.signLike comma.token.lineStart previous.trivia.trailing.isNone True
      Bool.andIntro first (Bool.andIntro second back)

theorem bareQuietR ∀ (behind rest: List Leaf)
    (back: gluesQuietBack behind = True)
    (quiet: gluesQuiet rest = True)
    (edge: edgeQuiet behind rest = True):
    gluesQuietBack (withBareR behind rest) = True :=
  match induct (withBareR behind rest) with
    | eq1 _ => back
    | eq2 behind comma closer after guard ih =>
      let (isCommaGuard, closerGuard, _) := guard
      let isComma: comma.token.kind = Comma := DecEq.sound isCommaGuard
      let movedSign: (commaMoved comma closer behind).fst.kind.signLike = False :=
        rewrite movedKind comma closer behind then closerNotSign closer.token.kind closerGuard
      let afterQuiet := tailQuiet closer after (tailQuiet comma [closer, ..after] quiet)
      let edge2: edgeQuiet
        [
          (commaMoved comma closer behind).fst,
          { comma | trivia = Trivia.empty },
          ..(commaMoved comma closer behind).snd
        ]
        after
        = True :=
        match after with
          | [] => byComputing
          | [next, ..more] =>
            rewrite movedSign then
              quietNotSign next.token.lineStart next.kind.opensAtom
                (commaMoved comma closer behind).fst.trivia.trailing.isNone
                next.trivia.leading.isEmpty
      ih
        (bareBack
          (commaMoved comma closer behind).fst
          comma
          (commaMoved comma closer behind).snd
          isComma
          (movedBack comma closer behind back))
        afterQuiet
        edge2
    | eq3 behind leaf after _ ih =>
      ih
        (pushQuiet leaf behind back
          (match behind with
            | [] => byComputing
            | [newest, ..older] => edge))
        (tailQuiet leaf after quiet)
        (edgeHead leaf behind after quiet)

theorem bareQuiet ∀ (leaves: List Leaf)
    (quiet: gluesQuiet leaves = True):
    gluesQuiet (withBareLastCommas [] leaves) = True :=
  rewrite withBareFromR [] leaves then
    reverseQuiet
      (withBareR [] leaves)
      []
      (bareQuietR [] leaves byComputing quiet byComputing)
      byComputing
      (edgeNil (withBareR [] leaves))

-- Comment placement, and the leaves the parser reads.

--| Comment placement keeps glued signs quiet.
theorem settledWithQuiet ∀ (lexed: Lexed) (bareLast: Bool)
    (quiet: gluesQuiet lexed.leaves = True):
    gluesQuiet (lexed.settledWith bareLast).leaves = True :=
  let homed := homeFrom bareLast [] None lexed.leaves
  let homedQuiet: gluesQuiet homed = True := homeQuiet bareLast [] None lexed.leaves byComputing quiet byComputing
  let commas := commasFrom [] None homed lexed.end
  trimmedQuietAll
    (letsFrom [] (arrows commas.leaves))
    (letsQuiet (arrows commas.leaves) (arrowsQuiet commas.leaves (commasQuiet homed lexed.end homedQuiet)))

--| The leaves the parser reads from a lexed source in slice 1's alphabet have glued signs quiet.
theorem onceQuiet ∀ (source: Text) (lexed: Lexed)
    (lexes: lex source = Ok lexed)
    (within: alphabet1 lexed.leaves = True):
    gluesQuiet lexed.settledOnce.leaves = True :=
  let (laid, _) := lexLaidProved source lexed lexes within
  settledWithQuiet
    { lexed | leaves = withBareLastCommas [] lexed.leaves }
    True
    (bareQuiet lexed.leaves (laidQuiet lexed.leaves False laid))

-- Items.

theorem quietAnyStart ∀ (s x o t e: Bool) (quiet: quietOf s False o t e = True): quietOf s x o t e = True :=
  match x with
    | True => quietStarts s o t e
    | False => quiet

theorem quietGlued ∀ (s l o t e c: Bool) (quiet: quietOf s l o t e = True): quietOf s (!(!l && c)) o t e = True :=
  match l with
    | True => quietStarts s o t e
    | False => quietAnyStart s (!c) o t e quiet

theorem itemsAfterQuiet ∀ (previous: Item) (rest: List Leaf) (index depth lineIndent: Nat)
    (quiet: gluesQuietAfter previous.leaf rest = True):
    itemsQuietAfter previous (itemsAfter (Some previous.leaf.token) index depth lineIndent rest) = True :=
  match rest with
    | [] => byComputing
    | [next, ..more] =>
      let token := next.token
      let glued := !token.lineStart && endColumn previous.leaf.token == token.column
      let afterOperand := previous.leaf.token.kind.closesOperand
      let afterDot := previous.leaf.token.kind == Dot
      let indent := if token.lineStart then token.column else lineIndent
      let after :=
        if token.kind.isOpener then depth + 1
        else if token.kind.isCloser then depth - 1
        else depth
      let item: Item := { leaf = next, glued, afterOperand, afterDot, index, depth, lineIndent = indent }
      Bool.andIntro
        (quietGlued previous.leaf.kind.signLike next.token.lineStart next.kind.opensAtom
            previous.leaf.trivia.trailing.isNone next.trivia.leading.isEmpty
            (endColumn previous.leaf.token == token.column)
            (Bool.andLeft quiet))
        (itemsAfterQuiet item more (index + 1) after indent (Bool.andRight quiet))

--| The items of quiet leaves are quiet.
theorem itemsQuietOf ∀ (leaves: List Leaf) (quiet: gluesQuiet leaves = True): itemsQuiet (items leaves) = True :=
  match leaves with
    | [] => byComputing
    | [first, ..rest] =>
      let token := first.token
      let indent := if token.lineStart then token.column else 0
      let after :=
        if token.kind.isOpener then 0 + 1
        else if token.kind.isCloser then 0 - 1
        else 0
      let item: Item := {
        leaf = first,
        glued = False,
        afterOperand = False,
        afterDot = False,
        index = 0,
        depth = 0,
        lineIndent = indent
      }
      itemsAfterQuiet item rest 1 after indent quiet

theorem appendQuietAfter ∀ (first: Leaf) (xs ys: List Leaf)
    (quiet: gluesQuietAfter first (xs ++ ys) = True):
    gluesQuietAfter first xs = True ∧ gluesQuiet ys = True :=
  match xs with
    | [] => (byComputing, tailQuiet first ys quiet)
    | [next, ..more] =>
      let (moreQuiet, ysQuiet) := appendQuietAfter next more ys (Bool.andRight quiet)
      (Bool.andIntro (Bool.andLeft quiet) moreQuiet, ysQuiet)

theorem appendQuiet ∀ (xs ys: List Leaf)
    (quiet: gluesQuiet (xs ++ ys) = True):
    gluesQuiet xs = True ∧ gluesQuiet ys = True :=
  match xs with
    | [] => (byComputing, quiet)
    | [first, ..rest] => appendQuietAfter first rest ys quiet

theorem groupsQuiet ∀ (groups: List (List Leaf))
    (quiet: gluesQuiet groups.concat = True):
    List.All (group => itemsQuiet (items group) = True) groups :=
  match groups with
    | [] => Trivial
    | [group, ..more] =>
      let (groupQuiet, moreQuiet) := appendQuiet group more.concat quiet
      (itemsQuietOf group groupQuiet, groupsQuiet more moreQuiet)

--| Every declaration's items, as `parseFile` reads them from a lexed source in slice 1's alphabet, have glued signs
--| quiet: what `parseShaped1` needs of them for `signQuiet`.
theorem settledItemsQuiet ∀ (source: Text) (lexed: Lexed)
    (lexes: lex source = Ok lexed)
    (within: alphabet1 lexed.leaves = True):
    List.All (group => itemsQuiet (items group) = True) (groupsOf lexed.settledOnce.leaves) :=
  groupsQuiet
    (groupsOf lexed.settledOnce.leaves)
    (rewrite groupsConcat lexed.settledOnce.leaves then onceQuiet source lexed lexes within)

--| The same of the leaves `lex` gave, before comment placement: the parser's `QuietItems` of the lexer's own groups, as the lexer
--| lays them out (`lexLaidProved`).
theorem lexedItemsQuiet ∀ (source: Text) (lexed: Lexed)
    (lexes: lex source = Ok lexed)
    (within: alphabet1 lexed.leaves = True):
    List.All (group => itemsQuiet (items group) = True) (groupsOf lexed.leaves) :=
  let (laid, _) := lexLaidProved source lexed lexes within
  groupsQuiet (groupsOf lexed.leaves) (rewrite groupsConcat lexed.leaves then laidQuiet lexed.leaves False laid)

-- Witnesses.

--| The items `parseFile` reads from a source, all its declarations' together, if it lexes.
def settledItemsOf (source: Text): List Item := match lex source with
  | Ok lexed => items lexed.settledOnce.leaves
  | Err _ => []

--| Glued signs with comments nearby, and comments on signs that aren't glued: the items are quiet.
theorem settledItemsQuietExample: itemsQuiet
      (settledItemsOf "def d: A := f -x !b (-1) (- -- c\n  1) - -- d\n  2 (-\n  -- o\n  y)\n")
      = True :=
  byComputing
