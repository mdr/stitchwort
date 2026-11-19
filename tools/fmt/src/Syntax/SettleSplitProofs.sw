--| What cutting a file's words into declarations keeps of `settledWords` (SW-4021, `parseSettled1`): the whole list's
--| facts hold of each piece, given that no piece starts with a closer.

namespace Syntax.SettleSplitProofs
import Std (Bool, Eq, List)
import Syntax (..)
import Fmt (..)
import Syntax.ParseCarries (codeWords)
import Syntax.SharedFacts (arrowsBarePrefix, arrowsBareSuffix, homedBackSuffix)

--| The words end (the oldest word, last of a newest-first list) in a word that is no closer, so no look back
--| (`trailsBack`) reaches past them.
def endsOpen: List Word → Bool
  | [] => False
  | [word] => !isCloserText word.text
  | [_, ..rest] => endsOpen rest

--| No closer starts the words: what a declaration's words guarantee (they start with `def`).
def startsOpen: List Word → Bool
  | [] => True
  | [word, .._] => !isCloserText word.text

theorem trailsBackOpen ∀ (word: Word) (rest: List Word)
    (open: isCloserText word.text = False):
    trailsBack [word, ..rest] = word.trails :=
  Eq.trans
    (byComputing: trailsBack [word, ..rest] = (word.trails || (isCloserText word.text && trailsBack rest)))
    (rewrite open then cases)

--| A look back that ends at an open word never reads what lies further back.
theorem trailsBackAppend ∀ (xs ys: List Word) (ends: endsOpen xs = True): trailsBack (xs ++ ys) = trailsBack xs :=
  match xs with
    | [word] =>
      let open := Bool.notTrue (isCloserText word.text) ends
      Eq.trans (trailsBackOpen word ys open) (Eq.flipped (trailsBackOpen word [] open))
    | [word, next, ..rest] =>
      let ih := trailsBackAppend [next, ..rest] ys ends
      calc trailsBack ([word, next, ..rest] ++ ys)
        _ = (word.trails || (isCloserText word.text && trailsBack ([next, ..rest] ++ ys))) := byComputing
        _ = (word.trails || (isCloserText word.text && trailsBack [next, ..rest])) := rewrite ih
        _ = trailsBack [word, next, ..rest] := byComputing

theorem homedBackOne ∀ (word: Word) (open: isCloserText word.text = False): homedBack [word] = True := rewrite open

--| A newest-first list homed as a whole is homed in its newer part, if the older part starts the look back at an
--| open word.
theorem homedBackPrefix ∀ (xs ys: List Word)
    (ends: endsOpen xs = True)
    (homed: homedBack (xs ++ ys) = True):
    homedBack xs = True :=
  match xs with
    | [word] => homedBackOne word (Bool.notTrue (isCloserText word.text) ends)
    | [word, next, ..rest] =>
      let ih := homedBackPrefix [next, ..rest] ys ends (Bool.andRight homed)
      let first := Bool.andLeft homed
      let back := trailsBackAppend [next, ..rest] ys ends
      Bool.andIntro (rewrite back at first then first) ih

--| Comments' texts: a test of every word of a joined list is a test of each part.
theorem allPrefix ∀ (xs ys: List Word) (p: Word → Bool) (h: List.all (xs ++ ys) p = True): List.all xs p = True :=
  match xs with
    | [] => byComputing
    | [word, ..rest] => Bool.andIntro (Bool.andLeft h) (allPrefix rest ys p (Bool.andRight h))

theorem allSuffix ∀ (xs ys: List Word) (p: Word → Bool) (h: List.all (xs ++ ys) p = True): List.all ys p = True :=
  match xs with
    | [] => h
    | [word, ..rest] => allSuffix rest ys p (Bool.andRight h)

theorem endsOpenSnoc ∀ (zs: List Word) (word: Word)
    (open: isCloserText word.text = False):
    endsOpen (zs ++ [word]) = True :=
  match zs with
    | [] | [_] => rewrite open
    | [first, next, ..rest] => endsOpenSnoc [next, ..rest] word open

--| The oldest word of a list read newest first is the first word of the list.
theorem endsOpenReverse ∀ (word: Word) (rest: List Word)
    (open: isCloserText word.text = False):
    endsOpen (List.reverse [word, ..rest]) = True :=
  rewrite List.reverseCons word rest then endsOpenSnoc (List.reverse rest) word open

--| `settledWords` (`ParseSettledStatements`), which that file's `settledIsWords` shows is `Decl.settled`'s test.
def settledOf (words: List Word): Bool :=
  homedBack words.reverse && arrowsBare words && words.all (word => word.comments.texts.all commentText)

--| `settledOf` of two lists joined, the second not starting with a closer, holds of each: a closer's look back
--| stops at the word the second list starts with.
theorem settledSplit ∀ (older newer: List Word)
    (open: startsOpen newer = True)
    (settled: settledOf (older ++ newer) = True):
    settledOf older = True ∧ settledOf newer = True :=
  match newer with
    | [] => (rewrite List.appendNil older at settled then settled, byComputing)
    | [word, ..rest] =>
      let newer := [word, ..rest]
      let homedWhole := Bool.andLeft settled
      let arrows := Bool.andLeft (Bool.andRight settled)
      let comments := Bool.andRight (Bool.andRight settled)
      let homed: homedBack (List.reverse newer ++ List.reverse older) = True :=
        rewrite List.reverseAppend older newer at homedWhole then homedWhole
      let ends := endsOpenReverse word rest (Bool.notTrue (isCloserText word.text) open)
      (
        Bool.andIntro
          (homedBackSuffix (List.reverse newer) (List.reverse older) homed)
          (Bool.andIntro
            (arrowsBarePrefix older newer arrows)
            (allPrefix older newer (word => word.comments.texts.all commentText) comments)),
        Bool.andIntro
          (homedBackPrefix (List.reverse newer) (List.reverse older) ends homed)
          (Bool.andIntro
            (arrowsBareSuffix older newer arrows)
            (allSuffix older newer (word => word.comments.texts.all commentText) comments))
      )

theorem startsOpenConcat ∀ (pieces: List (List Word))
    (open: pieces.all startsOpen = True):
    startsOpen pieces.concat = True :=
  match pieces with
    | [] => byComputing
    | [[], ..more] => startsOpenConcat more open
    | [[word, ..rest], ..more] => Bool.andLeft open

--| The words of a file cut into pieces none of which starts with a closer, `settledOf` of all of them together is
--| `settledOf` of each (the pieces are the file's declarations, each starting with `def`).
theorem settledPieces ∀ (pieces: List (List Word))
    (open: pieces.all startsOpen = True)
    (settled: settledOf pieces.concat = True):
    pieces.all settledOf = True :=
  match pieces with
    | [] => byComputing
    | [piece, ..more] =>
      let rest := Bool.andRight open
      match settledSplit piece more.concat (startsOpenConcat more rest) settled with
        | (first, others) => Bool.andIntro first (settledPieces more rest others)

-- `groupsOf` only splits.

theorem concatAppend ∀ (xss yss: List (List Leaf)): (xss ++ yss).concat = xss.concat ++ yss.concat := match xss with
  | [] => byComputing
  | [xs, ..more] => Eq.trans (rewrite concatAppend more yss) (Eq.flipped (List.appendAssoc xs more.concat yss.concat))

--| Closing the group in progress: the groups' leaves in order are the groups' and then the group's.
theorem flushConcat ∀ (current: List Leaf) (groups: List (List Leaf)):
    (if current.isEmpty then groups else [current.reverse, ..groups]).reverse.concat
      = groups.reverse.concat ++ current.reverse :=
  match current with
    | [] => Eq.flipped (List.appendNil groups.reverse.concat)
    | [leaf, ..rest] =>
      calc ([[leaf, ..rest].reverse, ..groups]).reverse.concat
        _ = (groups.reverse ++ [[leaf, ..rest].reverse]).concat :=
          rewrite List.reverseCons [leaf, ..rest].reverse groups
        _ = groups.reverse.concat ++ [[leaf, ..rest].reverse].concat :=
          concatAppend groups.reverse [[leaf, ..rest].reverse]
        _ = groups.reverse.concat ++ [leaf, ..rest].reverse := rewrite List.appendNil [leaf, ..rest].reverse

theorem splitStep ∀ (starts: Bool) (began state: Splitter) (current: List Leaf) (groups: List (List Leaf)):
    (if starts then (began, ([]: List Leaf), (if current.isEmpty then groups else [current.reverse, ..groups]))
     else (state, current, groups)).snd.snd.reverse.concat
      ++ (if starts then (began, ([]: List Leaf), (if current.isEmpty then groups else [current.reverse, ..groups]))
          else (state, current, groups)).snd.fst.reverse
      = groups.reverse.concat ++ current.reverse :=
  match starts with
    | False => byComputing
    | True => Eq.trans (rewrite flushConcat current groups) (List.appendNil _)

theorem stepAppend ∀ (older newer before now: List Leaf) (leaf: Leaf) (rest: List Leaf)
    (flushed: older ++ newer.reverse = before ++ now):
    older ++ ([leaf, ..newer].reverse ++ rest) = before ++ (now ++ [leaf, ..rest]) :=
  calc older ++ ([leaf, ..newer].reverse ++ rest)
    _ = older ++ ((newer.reverse ++ [leaf]) ++ rest) := rewrite List.reverseCons leaf newer
    _ = older ++ (newer.reverse ++ ([leaf] ++ rest)) := rewrite List.appendAssoc newer.reverse [leaf] rest
    _ = (older ++ newer.reverse) ++ ([leaf] ++ rest) :=
      Eq.flipped (List.appendAssoc older newer.reverse ([leaf] ++ rest))
    _ = (before ++ now) ++ [leaf, ..rest] := rewrite flushed
    _ = before ++ (now ++ [leaf, ..rest]) := List.appendAssoc before now [leaf, ..rest]

theorem splitFromConcat ∀ (state: Splitter) (current: List Leaf) (groups: List (List Leaf)) (leaves: List Leaf):
    (splitFrom state current groups leaves).concat = groups.reverse.concat ++ (current.reverse ++ leaves) :=
  match leaves with
    | [] => rewrite List.appendNil current.reverse then flushConcat current groups
    | [leaf, ..rest] =>
      Eq.trans (splitFromConcat _ _ _ rest) (stepAppend _ _ _ _ leaf rest (splitStep _ _ _ current groups))

theorem groupsConcat ∀ (leaves: List Leaf): (groupsOf leaves).concat = leaves :=
  Eq.trans (splitFromConcat Splitter.start [] [] leaves) byComputing

theorem codeWordsAppend ∀ (xs ys: List Leaf): codeWords (xs ++ ys) = codeWords xs ++ codeWords ys := calc codeWords
  (xs ++ ys)
  _ = (List.filter (xs ++ ys) (leaf => leaf.kind != Comma)).map Leaf.word := byComputing
  _ = (List.filter xs (leaf => leaf.kind != Comma) ++ List.filter ys (leaf => leaf.kind != Comma)).map Leaf.word :=
    rewrite List.filterAppend xs ys (leaf => leaf.kind != Comma)
  _ = codeWords xs ++ codeWords ys :=
    List.mapAppend (List.filter xs (leaf => leaf.kind != Comma)) (List.filter ys (leaf => leaf.kind != Comma)) Leaf.word

--| The words of the groups, joined, are the words of the leaves.
theorem groupWordsConcat ∀ (groups: List (List Leaf)): (groups.map codeWords).concat = codeWords groups.concat :=
  match groups with
    | [] => byComputing
    | [group, ..more] => Eq.trans (rewrite groupWordsConcat more) (Eq.flipped (codeWordsAppend group more.concat))

theorem declWordsOpen ∀ (decl: Decl): startsOpen decl.words = True := match decl with
  | Definition attributes header (Assigned colonEq value) => byComputing
  | _ => byComputing

theorem declsWordsOpen ∀ (decls: List Decl): (decls.map Decl.words).all startsOpen = True := match decls with
  | [] => byComputing
  | [decl, ..more] => Bool.andIntro (declWordsOpen decl) (declsWordsOpen more)

theorem declsSettled ∀ (decls: List Decl)
    (settled: (decls.map Decl.words).all settledOf = True):
    decls.all Decl.settled = True :=
  match decls with
    | [] => byComputing
    | [decl, ..more] => Bool.andIntro (Bool.andLeft settled) (declsSettled more (Bool.andRight settled))
