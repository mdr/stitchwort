--| Glued signs carry no comments (SW-4081): in the leaves the parser reads, a `-` or `!` with an atom's first token
--| glued to it on its line has no trailing comment, and that token no own-line comments. The parser reads a sign as a
--| call argument's (`f -x`) or a head's negative numeral (`-1 n`) only when the next item is glued, so this is what
--| the tree fact `signsQuiet1` needs of the items.
--|
--| The lexer's leaves are laid out (`laidOut`: a leaf with own-line comments, or after a trailing comment, starts its
--| line), which gives it at once. Rule N moves comments, and breaks `laidOut` (in `a, -- c` the comment goes back to
--| `a`, with the `,` still glued to it), but every comment it moves lands where no sign meets a glued atom: on a leaf
--| followed by a comma, closer or bar (rule 1, and the last commas' comments), on a comma's next leaf (rule 2), on
--| `->` or `:=` (rules 3 and 4), or nowhere new (rule 5).

namespace Syntax.GlueQuietProofs
import Std (Bool, DecEq, Eq, List, Nat, Option, Result, Text, Void)
import Syntax (..)
import Syntax.SettleProofs (laidOut)

-- The invariant.

--| A `-` or `!`.
def Tok.signLike (kind: Tok): Bool := kind == Minus || kind == Bang

--| The four facts `glueQuiet` reads, as Bools.
def quietOf (sign lineStart opens untrailed unled: Bool): Bool := !sign || lineStart || !opens || (untrailed && unled)

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

theorem quietUnlead ∀ (s l o t e: Bool) (quiet: quietOf s l o t e = True): quietOf s l o t True = True :=
  match s, l, o, t, e, quiet with
    | False, _, _, _, _, _ => byComputing
    | True, True, _, _, _, _ => byComputing
    | True, False, False, _, _, _ => byComputing
    | True, False, True, True, True, _ => byComputing

theorem quietNotSign ∀ (l o t e: Bool): quietOf False l o t e = True := byComputing

theorem quietNotOpens ∀ (s l t e: Bool): quietOf s l False t e = True := match s, l with
  | False, _ => byComputing
  | True, True => byComputing
  | True, False => byComputing

theorem quietStarts ∀ (s o t e: Bool): quietOf s True o t e = True := match s with
  | False => byComputing
  | True => byComputing

theorem quietBoth ∀ (s l o: Bool): quietOf s l o True True = True := match s, l, o with
  | False, _, _ => byComputing
  | True, True, _ => byComputing
  | True, False, False => byComputing
  | True, False, True => byComputing

theorem isNoneOfSome ∀ (option: Option Comment) (none: option.isSome = False): option.isNone = True := match option with
  | None => byComputing

-- The lexer's leaves.

theorem orFalseOf ∀ (b: Bool) (h: (b || False) = True): b = True := match b with | True => byComputing

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
          let unled: next.trivia.leading.isEmpty = True := orFalseOf _ ledOk
          let untrailed: previous.trivia.trailing.isSome = False := Bool.notTrue _ (orFalseOf _ afterOk)
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

-- Rule 5: trimming keeps which comments there are.

def Leaf.trimmed (leaf: Leaf): Leaf := { leaf | trivia = leaf.trivia.trimmed }

theorem trailingTrimmed ∀ (leaf: Leaf): leaf.trimmed.trivia.trailing.isNone = leaf.trivia.trailing.isNone :=
  match leaf.trivia.trailing with
    | None => byComputing
    | Some comment => byComputing

theorem leadingTrimmed ∀ (leaf: Leaf): leaf.trimmed.trivia.leading.isEmpty = leaf.trivia.leading.isEmpty :=
  match leaf.trivia.leading with
    | [] => byComputing
    | [comment, ..more] => byComputing

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

-- Rules 2 to 4: comments taken off a leaf, or put on a leaf that opens no atom, or above the leaf after a comma.

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
  | Comma => byComputing
  | other => byComputing

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
    | True =>
      match free with
        | True => byComputing
        | False =>
          match leaf.kind.opensAtom with
            | True => byComputing
            | False => byComputing
    | False =>
      match free with
        | True => byComputing
        | False =>
          match leaf.kind.opensAtom with
            | True => byComputing
            | False => byComputing
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
    rewrite plain then
      match free with
        | True => byComputing
        | False => byComputing
  )

theorem kindIs ∀ (kind: Tok) (is: kind = ColonEq): kind.opensAtom = False := rewrite is

-- Rule 4.

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

-- Rule 3.

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
            | True => byComputing
            | False => byComputing
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
