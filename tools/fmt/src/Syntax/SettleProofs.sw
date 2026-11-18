--| Proofs about rule N (`Syntax/Settle.sw`, `Lexed.settled`) for slice 1 of the proved formatter
--| (docs/proposals/self-hosted-fmt-s1-sketch.md, ticket 15).

namespace Syntax.SettleProofs
import Std (Bool, Char, DecEq, Eq, Finite, List, Nat, Option, Text)
import Syntax (..)
import Fmt (..)

--| The leaves' tokens, comments aside.
def tokens (leaves: List Leaf): List Token := leaves.map (leaf => leaf.token)

theorem tokensReverseOnto ∀ (xs acc: List Leaf): tokens (xs.reverseOnto acc) = (tokens xs).reverseOnto (tokens acc) :=
  List.mapReverseOnto xs acc (leaf => leaf.token)

--| `trailingAt` moves a comment between leaves and keeps their tokens.
theorem trailingAtTokens ∀ (behind: List Leaf) (steps: Nat) (comment: Comment):
    tokens (trailingAt behind steps comment) = tokens behind :=
  match behind, steps with
    | [], _ => byComputing
    | [leaf, ..earlier], Zero => byComputing
    | [leaf, ..earlier], Succ Zero => byComputing
    | [leaf, ..earlier], Succ (Succ more) =>
      Eq.cong (tail => [leaf.token, ..tail]) (trailingAtTokens earlier (Succ more) comment)

--| One step of a pass that keeps tokens: the leaf, maybe with other
--| comments, goes on the settled leaves, which keep their tokens.
theorem consTokens ∀ (x leaf: Leaf) (settled behind later after: List Leaf)
    (same: x.token = leaf.token)
    (sameBehind: tokens settled = tokens behind)
    (sameLater: tokens later = tokens after):
    tokens ([x, ..settled].reverseOnto later) = tokens (behind.reverseOnto [leaf, ..after]) :=
  calc tokens ([x, ..settled].reverseOnto later)
    _ = (tokens settled).reverseOnto (tokens [x, ..later]) := tokensReverseOnto settled [x, ..later]
    _ = (tokens behind).reverseOnto (tokens [leaf, ..after]) := rewrite same, sameBehind, sameLater
    _ = tokens (behind.reverseOnto [leaf, ..after]) := (tokensReverseOnto behind [leaf, ..after]).flipped

--| Rule 1 keeps the tokens.
theorem homeFromTokens ∀ (behind: List Leaf) (bumped: Option Comment) (rest: List Leaf):
    tokens (homeFrom behind bumped rest) = tokens (behind.reverseOnto rest) :=
  match rest with
    | [] => byComputing
    | [leaf, ..after] =>
      let step := (x: Leaf) (settled: List Leaf) (next: Option Comment) (same: x.token = leaf.token) (sameBehind: tokens
          settled
        = tokens behind) =>
        Eq.trans
          (homeFromTokens [x, ..settled] next after)
          (consTokens x leaf settled behind after after same sameBehind byComputing)
      match bumped with
        | None =>
          match leaf.trivia.trailing with
            | None => step leaf behind None byComputing byComputing
            | Some comment =>
              match movable leaf behind after with
                | False => step leaf behind None byComputing byComputing
                | True =>
                  match stepsBack leaf behind after 0 with
                    | Zero =>
                      match barBelow leaf behind after with
                        | True => step (leaf.withTrailing None) behind (Some comment.unspaced) byComputing byComputing
                        | False => step leaf behind None byComputing byComputing
                    | Succ more =>
                      step
                        (leaf.withTrailing None)
                        (trailingAt behind (Succ more) comment)
                        None
                        byComputing
                        (trailingAtTokens behind (Succ more) comment)
        | Some bump =>
          let lifted := leaf.withLeading [bump, ..leaf.trivia.leading]
          match lifted.trivia.trailing with
            | None => step lifted behind None byComputing byComputing
            | Some comment =>
              match movable lifted behind after with
                | False => step lifted behind None byComputing byComputing
                | True =>
                  match stepsBack lifted behind after 0 with
                    | Zero =>
                      match barBelow lifted behind after with
                        | True => step (lifted.withTrailing None) behind (Some comment.unspaced) byComputing byComputing
                        | False => step lifted behind None byComputing byComputing
                    | Succ more =>
                      step
                        (lifted.withTrailing None)
                        (trailingAt behind (Succ more) comment)
                        None
                        byComputing
                        (trailingAtTokens behind (Succ more) comment)

--| Rule 2 keeps the tokens.
theorem commasFromTokens ∀ (done: List Leaf) (carried: Option Carried) (rest: List Leaf) (end: Trivia):
    tokens (commasFrom done carried rest end).leaves = tokens (done.reverseOnto rest) :=
  match rest with
    | [] => byComputing
    | [leaf, ..after] =>
      let step := (x: Leaf) (next: Option Carried) (same: x.token = leaf.token) =>
        Eq.trans
          (commasFromTokens [x, ..done] next after end)
          (consTokens x leaf done done after after same byComputing byComputing)
      match carried with
        | None =>
          match commaCarries leaf.trivia with
            | None => step leaf None byComputing
            | Some carry =>
              match leaf.kind == Comma with
                | True => step { leaf | trivia = Trivia.empty } (Some carry) byComputing
                | False => step leaf None byComputing
        | Some held =>
          let received := { leaf | trivia = held.into leaf.trivia }
          match commaCarries received.trivia with
            | None => step received None byComputing
            | Some carry =>
              match leaf.kind == Comma with
                | True => step { leaf | trivia = Trivia.empty } (Some carry) byComputing
                | False => step received None byComputing

--| Rule 3 keeps the tokens.
theorem arrowsFromTokens ∀ (done: List Leaf) (current: Leaf) (rest: List Leaf):
    tokens (arrowsFrom done current rest) = tokens (done.reverseOnto [current, ..rest]) :=
  match rest with
    | [] => byComputing
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
          Eq.trans
            (arrowsFromTokens [moved, ..done] (next.withLeading []) more)
            (consTokens moved current done done
              [next.withLeading [], ..more]
              [next, ..more]
              byComputing
              byComputing
              byComputing)
        | False =>
          Eq.trans
            (arrowsFromTokens [current, ..done] next more)
            (consTokens current current done done [next, ..more] [next, ..more] byComputing byComputing byComputing)

theorem arrowsTokens ∀ (leaves: List Leaf): tokens (arrows leaves) = tokens leaves := match leaves with
  | [] => byComputing
  | [first, ..rest] => arrowsFromTokens [] first rest

--| Rule 4 keeps the tokens.
theorem letsFromTokens ∀ (behind rest: List Leaf): tokens (letsFrom behind rest) = tokens (behind.reverseOnto rest) :=
  match rest with
    | [] => byComputing
    | [leaf, ..after] =>
      match leaf.trivia.trailing with
        | None =>
          Eq.trans
            (letsFromTokens [leaf, ..behind] after)
            (consTokens leaf leaf behind behind after after byComputing byComputing byComputing)
        | Some comment =>
          match leaf.kind == ColonEq && letBefore behind 0 && semicolonAfter after 0 with
            | True =>
              let moved := { leaf |
                trivia = { leaf.trivia | leading = leaf.trivia.leading ++ [comment.unspaced], trailing = None }
              }
              Eq.trans
                (letsFromTokens [moved, ..behind] after)
                (consTokens moved leaf behind behind after after byComputing byComputing byComputing)
            | False =>
              Eq.trans
                (letsFromTokens [leaf, ..behind] after)
                (consTokens leaf leaf behind behind after after byComputing byComputing byComputing)

theorem trimmedTokens ∀ (leaves: List Leaf):
    tokens (leaves.map (leaf => { leaf | trivia = leaf.trivia.trimmed })) = tokens leaves :=
  match leaves with
    | [] => byComputing
    | [leaf, ..rest] => Eq.cong (tail => [leaf.token, ..tail]) (trimmedTokens rest)

--| Rule N moves comments and nothing else: the tokens are the lexer's.
theorem settledKeepsTokens ∀ (lexed: Lexed): tokens lexed.settled.leaves = tokens lexed.leaves :=
  let homed := homeFrom [] None lexed.leaves
  let commas := commasFrom [] None homed lexed.end
  calc tokens lexed.settled.leaves
    _ = tokens (letsFrom [] (arrows commas.leaves)) := trimmedTokens (letsFrom [] (arrows commas.leaves))
    _ = tokens (arrows commas.leaves) := letsFromTokens [] (arrows commas.leaves)
    _ = tokens commas.leaves := arrowsTokens commas.leaves
    _ = tokens homed := commasFromTokens [] None homed lexed.end
    _ = tokens lexed.leaves := homeFromTokens [] None lexed.leaves

theorem allReverseOnto ∀ (p: a → Bool) (xs acc: List a)
    (allXs: xs.all p = True)
    (allAcc: acc.all p = True):
    (xs.reverseOnto acc).all p = True :=
  match xs with
    | [] => allAcc
    | [x, ..rest] =>
      match held: p x with
        | True => allReverseOnto p rest [x, ..acc] allXs (rewrite held then allAcc)

--| A comma with no comment.
def bareComma (leaf: Leaf): Bool := (leaf.trivia.leading.isEmpty && leaf.trivia.trailing.isNone) || leaf.kind != Comma

theorem carriesNoneBare ∀ (trivia: Trivia)
    (none: commaCarries trivia = None):
    (trivia.leading.isEmpty && trivia.trailing.isNone) = True :=
  match trivia.leading, trivia.trailing with
    | [], None => byComputing
    | [_, .._], _ => cases

theorem notCommaBare ∀ (leaf: Leaf) (other: (leaf.kind == Comma) = False): bareComma leaf = True :=
  Bool.orRight (rewrite other)

--| After rule 2 no comma holds a comment.
theorem commasFromBare ∀ (done: List Leaf) (carried: Option Carried) (rest: List Leaf) (end: Trivia)
    (doneBare: done.all bareComma = True):
    (commasFrom done carried rest end).leaves.all bareComma = True :=
  match rest with
    | [] => allReverseOnto bareComma done [] doneBare byComputing
    | [leaf, ..after] =>
      let received := { leaf | trivia = carried.map (carry => carry.into leaf.trivia) |> .getOrElse leaf.trivia }
      match c: commaCarries received.trivia with
        | None =>
          commasFromBare
            [received, ..done]
            None
            after
            end
            (rewrite Bool.orLeft (carriesNoneBare received.trivia c) then doneBare)
        | Some carry =>
          match k: leaf.kind == Comma with
            | True => commasFromBare [{ received | trivia = Trivia.empty }, ..done] (Some carry) after end doneBare
            | False => commasFromBare [received, ..done] None after end (rewrite notCommaBare received k then doneBare)

theorem withoutLeadingBare ∀ (leaf: Leaf) (bare: bareComma leaf = True): bareComma (leaf.withLeading []) = True := cases

theorem kindNotComma ∀ (leaf: Leaf) (kind: Tok)
    (is: (leaf.kind == kind) = True)
    (other: (kind == Comma) = False):
    (leaf.kind == Comma) = False :=
  rewrite DecEq.sound is then other

--| Rule 3 gives a comma no comment.
theorem arrowsFromBare ∀ (done: List Leaf) (current: Leaf) (rest: List Leaf)
    (doneBare: done.all bareComma = True)
    (currentBare: bareComma current = True)
    (restBare: rest.all bareComma = True):
    (arrowsFrom done current rest).all bareComma = True :=
  match rest with
    | [] => allReverseOnto bareComma done [current] doneBare (rewrite currentBare)
    | [next, ..more] =>
      match nextBare: bareComma next with
        | True =>
          match moves: current.kind == Arrow && (!next.trivia.leading.isEmpty || current.trivia.trailing.isSome) with
            | True =>
              let moved := { current |
                trivia = { current.trivia |
                  leading = current.trivia.leading
                    ++ (current.trivia.trailing.map (comment => [comment.unspaced]) |> .getOrElse [])
                    ++ next.trivia.leading,
                  trailing = None
                }
              }
              arrowsFromBare
                [moved, ..done]
                (next.withLeading [])
                more
                (rewrite notCommaBare moved (kindNotComma current Arrow (Bool.andLeft moves) byComputing) then doneBare)
                (withoutLeadingBare next nextBare)
                restBare
            | False => arrowsFromBare [current, ..done] next more (rewrite currentBare then doneBare) nextBare restBare

theorem arrowsBareCommas ∀ (leaves: List Leaf)
    (bare: leaves.all bareComma = True):
    (arrows leaves).all bareComma = True :=
  match leaves with
    | [] => byComputing
    | [first, ..rest] =>
      match firstBare: bareComma first with
        | True => arrowsFromBare [] first rest byComputing firstBare bare

--| Rule 4 gives a comma no comment.
theorem letsFromBare ∀ (behind rest: List Leaf)
    (behindBare: behind.all bareComma = True)
    (restBare: rest.all bareComma = True):
    (letsFrom behind rest).all bareComma = True :=
  match rest with
    | [] => allReverseOnto bareComma behind [] behindBare byComputing
    | [leaf, ..after] =>
      match leafBare: bareComma leaf with
        | True =>
          match leaf.trivia.trailing with
            | None => letsFromBare [leaf, ..behind] after behindBare restBare
            | Some comment =>
              match moves: leaf.kind == ColonEq && letBefore behind 0 && semicolonAfter after 0 with
                | True =>
                  let moved := { leaf |
                    trivia = { leaf.trivia | leading = leaf.trivia.leading ++ [comment.unspaced], trailing = None }
                  }
                  letsFromBare
                    [moved, ..behind]
                    after
                    (rewrite notCommaBare moved (kindNotComma leaf ColonEq (Bool.andLeft moves) byComputing) then
                      behindBare)
                    restBare
                | False => letsFromBare [leaf, ..behind] after behindBare restBare

--| Rule 5 gives a comma no comment.
theorem trimmedBare ∀ (leaves: List Leaf)
    (bare: leaves.all bareComma = True):
    (leaves.map (leaf => { leaf | trivia = leaf.trivia.trimmed })).all bareComma = True :=
  match leaves with
    | [] => byComputing
    | [leaf, ..rest] =>
      match leafBare: bareComma leaf with
        | True =>
          let trimmedLeaf: bareComma { leaf | trivia = leaf.trivia.trimmed } = True := cases
          rewrite trimmedLeaf then trimmedBare rest bare

--| After rule N no comma holds a comment, so the tree needs no place for
--| one.
theorem settledCommasBare ∀ (lexed: Lexed): lexed.settled.leaves.all bareComma = True :=
  let homed := homeFrom [] None lexed.leaves
  let commas := commasFrom [] None homed lexed.end
  trimmedBare
    (letsFrom [] (arrows commas.leaves))
    (letsFromBare []
      (arrows commas.leaves)
      byComputing
      (arrowsBareCommas commas.leaves (commasFromBare [] None homed lexed.end byComputing)))

-- Under slice 1's alphabet there is no `let` and no `|`, so rule N's
-- clauses for an expression `let`'s `:=` and a record update's bar do
-- nothing.

--| Every leaf's token is in slice 1's alphabet.
def alphabet1 (leaves: List Leaf): Bool := (tokens leaves).all (token => token.kind.within1)

theorem alphabet1Leaves ∀ (leaves: List Leaf)
    (within: alphabet1 leaves = True):
    leaves.all (leaf => leaf.kind.within1) = True :=
  rewrite List.allMapBool leaves (token => token.kind.within1) (leaf => leaf.token) at within then within

--| Rule N keeps slice 1's alphabet, since it keeps the tokens.
theorem settledAlphabet1 ∀ (lexed: Lexed)
    (within: alphabet1 lexed.leaves = True):
    alphabet1 lexed.settled.leaves = True :=
  rewrite settledKeepsTokens lexed then within

theorem within1NotLet ∀ (kind: Tok) (within: kind.within1 = True): (kind == KwLet) = False :=
  let checked := Finite.check (kind => !kind.within1 || !(kind == KwLet)) byComputing kind
  Bool.notTrue (kind == KwLet) (rewrite within at checked then checked)

theorem within1NotPipe ∀ (kind: Tok) (within: kind.within1 = True): (kind == Pipe) = False :=
  let checked := Finite.check (kind => !kind.within1 || !(kind == Pipe)) byComputing kind
  Bool.notTrue (kind == Pipe) (rewrite within at checked then checked)

--| Without a `let` behind, no `:=` is an expression `let`'s.
theorem letBeforeNone ∀ (behind: List Leaf) (depth: Nat)
    (noLet: behind.all (leaf => leaf.kind.within1) = True):
    letBefore behind depth = False :=
  match behind with
    | [] => byComputing
    | [leaf, ..earlier] =>
      match within: leaf.kind.within1 with
        | True =>
          match leaf.kind.isCloser with
            | True => letBeforeNone earlier (depth + 1) noLet
            | False =>
              match leaf.kind.isOpener with
                | True => rewrite letBeforeNone earlier (depth - 1) noLet then Bool.andFalse (depth > 0)
                | False =>
                  match depth > 0 with
                    | True => letBeforeNone earlier depth noLet
                    | False =>
                      match isLet: leaf.kind == KwLet with
                        | True => Eq.trans isLet.flipped (within1NotLet leaf.kind within)
                        | False =>
                          match leaf.kind == Semi || leaf.kind == FatArrow || leaf.kind.startsDeclaration with
                            | True => byComputing
                            | False => letBeforeNone earlier depth noLet

--| Under slice 1's alphabet rule 4 does nothing.
theorem letsQuiet1 ∀ (behind rest: List Leaf)
    (behindWithin: behind.all (leaf => leaf.kind.within1) = True)
    (restWithin: rest.all (leaf => leaf.kind.within1) = True):
    letsFrom behind rest = behind.reverseOnto rest :=
  match rest with
    | [] => byComputing
    | [leaf, ..after] =>
      match within: leaf.kind.within1 with
        | True =>
          let next := letsQuiet1 [leaf, ..behind] after (rewrite within then behindWithin) restWithin
          match leaf.trivia.trailing with
            | None => next
            | Some comment =>
              rewrite letBeforeNone behind 0 behindWithin, Bool.andFalse (leaf.kind == ColonEq) then next

theorem notPipe1 ∀ (leaf: Leaf) (within: leaf.kind.within1 = True): leaf.kind ≠ Pipe :=
  DecEq.soundFalse leaf.kind Pipe (within1NotPipe leaf.kind within)

--| Under slice 1's alphabet rule 1 walks past commas and closers only.
theorem skippedQuiet1 ∀ (leaf: Leaf) (behind ahead: List Leaf)
    (within: leaf.kind.within1 = True):
    skipped leaf behind ahead = (leaf.kind == Comma || leaf.kind.isCloser) :=
  match comma: leaf.kind == Comma with
    | True => rewrite skipped.eq.comma leaf behind ahead (DecEq.sound comma)
    | False => rewrite skipped.eq.alt3 leaf behind ahead (DecEq.soundFalse leaf.kind Comma comma) (notPipe1 leaf within)

--| Under slice 1's alphabet rule 1 moves comments from commas that don't
--| start their lines and from closers only.
theorem movableQuiet1 ∀ (leaf: Leaf) (behind ahead: List Leaf)
    (within: leaf.kind.within1 = True):
    movable leaf behind ahead = ((leaf.kind == Comma && !leaf.token.lineStart) || leaf.kind.isCloser) :=
  match comma: leaf.kind == Comma with
    | True =>
      let isComma := DecEq.sound comma
      rewrite movable.eq.comma leaf behind ahead isComma, isComma, Bool.orFalse
    | False => rewrite movable.eq.alt3 leaf behind ahead (DecEq.soundFalse leaf.kind Comma comma) (notPipe1 leaf within)

--| Under slice 1's alphabet no bar's comment starts the line below.
theorem barsQuiet1 ∀ (leaf: Leaf) (behind ahead: List Leaf)
    (within: leaf.kind.within1 = True):
    barBelow leaf behind ahead = False :=
  rewrite barBelow.eq.alt2 leaf behind ahead (previous tail head tail2 isBehind isAhead => notPipe1 leaf within)

-- Rule 5: a comment's text, trimmed, has no space at its end.

theorem dropSpacesStart ∀ (chars: List Char):
    Text.startsWithChars [' '] (chars.dropWhile (char => char == ' ')) = False :=
  match chars with
    | [] => byComputing
    | [char, ..rest] =>
      match space: char == ' ' with
        | True => dropSpacesStart rest
        | False =>
          let other: Text.sameChar ' ' char = False := calc Text.sameChar ' ' char
            _ = Nat.equal (Char.toNat char) (Char.toNat ' ') := Nat.equalComm (Char.toNat ' ') (Char.toNat char)
            _ = False := space
          rewrite other

--| Trimming twice is trimming once.
theorem trimEndTwice ∀ (text: Text): trimEnd (trimEnd text) = trimEnd text := match spaced: text.endsWith " " with
  | False =>
    let unspaced: Text.startsWithChars [' '] (text.toList.reverseOnto []) = False := spaced
    rewrite unspaced
  | True =>
    let kept := (text.toList.reverseOnto []).dropWhile (char => char == ' ')
    let back: (kept.reverseOnto []).reverseOnto [] = kept := List.reverseReverse kept
    rewrite back, dropSpacesStart (text.toList.reverseOnto [])

def optionText: Option Comment → List Text
  | Some comment => [comment.text]
  | None => []

--| A token's comment texts, own-line ones first.
def triviaTexts (trivia: Trivia): List Text :=
  trivia.leading.map (comment => comment.text) ++ optionText trivia.trailing

def leavesTexts (leaves: List Leaf) (end: Trivia): List Text := match leaves with
  | [] => triviaTexts end
  | [leaf, ..rest] => triviaTexts leaf.trivia ++ leavesTexts rest end

--| The comment texts of a lexed file, in order.
def lexedTexts (lexed: Lexed): List Text := leavesTexts lexed.leaves lexed.end

theorem commentsTrimmed ∀ (comments: List Comment):
    ((comments.map Comment.trimmed).map (comment => comment.text)).map trimEnd
      = (comments.map Comment.trimmed).map (comment => comment.text) :=
  match comments with
    | [] => byComputing
    | [comment, ..rest] => rewrite trimEndTwice comment.text, commentsTrimmed rest

theorem triviaTrimmed ∀ (trivia: Trivia): (triviaTexts trivia.trimmed).map trimEnd = triviaTexts trivia.trimmed :=
  let leading := (trivia.leading.map Comment.trimmed).map (comment => comment.text)
  let trailing: (optionText (trivia.trailing.map Comment.trimmed)).map trimEnd
    = optionText (trivia.trailing.map Comment.trimmed) :=
    match trivia.trailing with
      | None => byComputing
      | Some comment => rewrite trimEndTwice comment.text
  calc (triviaTexts trivia.trimmed).map trimEnd
    _ = leading.map trimEnd ++ (optionText (trivia.trailing.map Comment.trimmed)).map trimEnd :=
      List.mapAppend leading (optionText (trivia.trailing.map Comment.trimmed)) trimEnd
    _ = triviaTexts trivia.trimmed := rewrite commentsTrimmed trivia.leading, trailing

theorem leavesTrimmed ∀ (leaves: List Leaf) (end: Trivia):
    (leavesTexts (leaves.map (leaf => { leaf | trivia = leaf.trivia.trimmed })) end.trimmed).map trimEnd
      = leavesTexts (leaves.map (leaf => { leaf | trivia = leaf.trivia.trimmed })) end.trimmed :=
  match leaves with
    | [] => triviaTrimmed end
    | [leaf, ..rest] =>
      let others := leavesTexts (rest.map (leaf => { leaf | trivia = leaf.trivia.trimmed })) end.trimmed
      calc (triviaTexts leaf.trivia.trimmed ++ others).map trimEnd
        _ = (triviaTexts leaf.trivia.trimmed).map trimEnd ++ others.map trimEnd :=
          List.mapAppend (triviaTexts leaf.trivia.trimmed) others trimEnd
        _ = triviaTexts leaf.trivia.trimmed ++ others := rewrite triviaTrimmed leaf.trivia, leavesTrimmed rest end

--| After rule N no comment's text ends in a space.
theorem settledTrimmed ∀ (lexed: Lexed): (lexedTexts lexed.settled).map trimEnd = lexedTexts lexed.settled :=
  let homed := homeFrom [] None lexed.leaves
  let commas := commasFrom [] None homed lexed.end
  leavesTrimmed (letsFrom [] (arrows commas.leaves)) commas.end

-- Rule 3: no `->` keeps a comment after it.

--| No `->` that a token follows has a trailing comment, and the token after
--| it has no own-line comments unless it is another `->` (which takes them
--| from the token after it in turn; no file that parses has `-> ->`).
def arrowsBare: List Leaf → Bool
  | [first, next, ..rest] =>
    (!(first.kind == Arrow) || (first.trivia.trailing.isNone && (next.trivia.leading.isEmpty || next.kind == Arrow)))
      && arrowsBare [next, ..rest]
  | _ => True

--| What `arrowsFrom` leaves before its current leaf is the leaves done, in
--| order.
theorem arrowsFromOnto ∀ (done: List Leaf) (current: Leaf) (rest: List Leaf):
    arrowsFrom done current rest = done.reverseOnto (arrowsFrom [] current rest) :=
  match rest with
    | [] => byComputing
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
          rewrite arrowsFromOnto [moved, ..done] (next.withLeading []) more,
              arrowsFromOnto [moved] (next.withLeading []) more
        | False => rewrite arrowsFromOnto [current, ..done] next more, arrowsFromOnto [current] next more

theorem emptyOf ∀ (xs: List a) (empty: xs.isEmpty = True): xs = [] := match xs with | [] => byComputing

theorem optionNone ∀ (option: Option a) (none: option.isSome = False): option.isNone = True := match option with
  | None => byComputing

theorem headBare ∀ (next head: Leaf)
    (empty: next.trivia.leading = [])
    (kind: head.kind = next.kind)
    (same: (next.kind == Arrow) = True ∨ head = next):
    (head.trivia.leading.isEmpty || head.kind == Arrow) = True :=
  match same with
    | Inl isArrow => Bool.orRight (rewrite kind then isArrow)
    | Inr isNext => rewrite isNext, empty

--| Rule 3's result is `arrowsBare`, and starts with its first leaf, which
--| changed only if it is an `->`.
--|
--| Proof idea: by induction on the leaves; the leaf after the current one
--| starts the rest's result unchanged unless it is an `->`, so when the
--| current leaf is an `->` the comments rule 3 took from that leaf are the
--| only ones it could have had.
theorem arrowsFromBare1 ∀ (current: Leaf) (rest: List Leaf):
    ∃ (head: Leaf) (tail: List Leaf) => arrowsFrom [] current rest = [head, ..tail]
      ∧ head.kind = current.kind
      ∧ ((current.kind == Arrow) = True ∨ head = current)
      ∧ arrowsBare [head, ..tail] = True :=
  match rest with
    | [] => (current, [], byComputing, byComputing, Inr byComputing, byComputing)
    | [next, ..more] =>
      let moved := { current |
        trivia = { current.trivia |
          leading = current.trivia.leading
            ++ (current.trivia.trailing.map (comment => [comment.unspaced]) |> .getOrElse [])
            ++ next.trivia.leading,
          trailing = None
        }
      }
      match isArrow: current.kind == Arrow with
        | False =>
          let (head, tail, gives, _, _, bare) := arrowsFromBare1 next more
          let result: arrowsFrom [] current [next, ..more] = [current, head, ..tail] :=
            rewrite arrowsFromOnto [current] next more, gives
          (current, [head, ..tail], result, byComputing, Inr byComputing, rewrite isArrow then bare)
        | True =>
          match moves: !next.trivia.leading.isEmpty || current.trivia.trailing.isSome with
            | True =>
              let (head, tail, gives, kind, same, bare) := arrowsFromBare1 (next.withLeading []) more
              let movedBare: arrowsBare [moved, head, ..tail] = True :=
                rewrite isArrow, headBare (next.withLeading []) head byComputing kind same then bare
              (
                moved,
                [head, ..tail],
                (rewrite arrowsFromOnto [moved] (next.withLeading []) more, gives),
                byComputing,
                Inl byComputing,
                movedBare
              )
            | False =>
              let (head, tail, gives, kind, same, bare) := arrowsFromBare1 next more
              let empty := emptyOf next.trivia.leading (Bool.notFalse _ (Bool.orFalseLeft _ _ moves))
              let untrailed := optionNone current.trivia.trailing (Bool.orFalseRight _ _ moves)
              let currentBare: arrowsBare [current, head, ..tail] = True :=
                rewrite isArrow, untrailed, headBare next head empty kind same then bare
              (
                current,
                [head, ..tail],
                (rewrite arrowsFromOnto [current] next more, gives),
                byComputing,
                Inr byComputing,
                currentBare
              )

theorem arrowsArrowsBare ∀ (leaves: List Leaf): arrowsBare (arrows leaves) = True := match leaves with
  | [] => byComputing
  | [first, ..rest] =>
    let (head, tail, gives, _, _, bare) := arrowsFromBare1 first rest
    rewrite gives then bare

theorem trimmedArrowsBare ∀ (leaves: List Leaf)
    (bare: arrowsBare leaves = True):
    arrowsBare (leaves.map (leaf => { leaf | trivia = leaf.trivia.trimmed })) = True :=
  match leaves with
    | [] => byComputing
    | [only] => byComputing
    | [first, second, ..rest] =>
      let later := trimmedArrowsBare [second, ..rest] (Bool.andRight bare)
      match first.trivia.trailing, second.trivia.leading with
        | None, [] => rewrite later, Bool.andTrue then Bool.andLeft bare
        | None, [_, .._] => rewrite later, Bool.andTrue then Bool.andLeft bare
        | Some _, [] => rewrite later, Bool.andTrue then Bool.andLeft bare
        | Some _, [_, .._] => rewrite later, Bool.andTrue then Bool.andLeft bare

--| After rule N no `->` holds a trailing comment, and the token after it
--| no own-line comments, unless that token is another `->`.
theorem settledArrowsBare1 ∀ (lexed: Lexed)
    (within: alphabet1 lexed.leaves = True):
    arrowsBare lexed.settled.leaves = True :=
  let homed := homeFrom [] None lexed.leaves
  let commas := commasFrom [] None homed lexed.end
  let arrowed := arrows commas.leaves
  let arrowedWithin: alphabet1 arrowed = True := calc alphabet1 arrowed
    _ = alphabet1 lexed.leaves :=
      rewrite arrowsTokens commas.leaves, commasFromTokens [] None homed lexed.end, homeFromTokens [] None lexed.leaves
    _ = True := within
  let quiet: letsFrom [] arrowed = arrowed := letsQuiet1 [] arrowed byComputing (alphabet1Leaves arrowed arrowedWithin)
  trimmedArrowsBare (letsFrom [] arrowed) (rewrite quiet then arrowsArrowsBare commas.leaves)

-- Comments kept in order. Rules 2 to 5 keep them for any leaves; rule 1
-- needs leaves as the lexer gives them.

--| The leaves' comment texts, in order.
def leafTexts: List Leaf → List Text
  | [] => []
  | [leaf, ..rest] => triviaTexts leaf.trivia ++ leafTexts rest

theorem leavesTextsSplit ∀ (leaves: List Leaf) (end: Trivia):
    leavesTexts leaves end = leafTexts leaves ++ triviaTexts end :=
  match leaves with
    | [] => byComputing
    | [leaf, ..rest] =>
      rewrite leavesTextsSplit rest end then
        (List.appendAssoc (triviaTexts leaf.trivia) (leafTexts rest) (triviaTexts end)).flipped

theorem leafTextsReverseOnto ∀ (xs acc: List Leaf):
    leafTexts (xs.reverseOnto acc) = leafTexts (xs.reverseOnto []) ++ leafTexts acc :=
  match xs with
    | [] => byComputing
    | [x, ..rest] =>
      calc leafTexts (rest.reverseOnto [x, ..acc])
        _ = leafTexts (rest.reverseOnto []) ++ (triviaTexts x.trivia ++ leafTexts acc) :=
          leafTextsReverseOnto rest [x, ..acc]
        _ = (leafTexts (rest.reverseOnto []) ++ triviaTexts x.trivia) ++ leafTexts acc :=
          (List.appendAssoc (leafTexts (rest.reverseOnto [])) (triviaTexts x.trivia) (leafTexts acc)).flipped
        _ = leafTexts (rest.reverseOnto [x]) ++ leafTexts acc :=
          rewrite leafTextsReverseOnto rest [x], List.appendNil (triviaTexts x.trivia)

--| One step of a pass that keeps each leaf's comments: the leaf, with the
--| same comment texts, goes on the settled leaves.
theorem consTexts ∀ (x leaf: Leaf) (settled behind after: List Leaf)
    (same: triviaTexts x.trivia = triviaTexts leaf.trivia)
    (sameBehind: leafTexts (settled.reverseOnto []) = leafTexts (behind.reverseOnto [])):
    leafTexts ([x, ..settled].reverseOnto after) = leafTexts (behind.reverseOnto [leaf, ..after]) :=
  calc leafTexts (settled.reverseOnto [x, ..after])
    _ = leafTexts (settled.reverseOnto []) ++ (triviaTexts x.trivia ++ leafTexts after) :=
      leafTextsReverseOnto settled [x, ..after]
    _ = leafTexts (behind.reverseOnto []) ++ (triviaTexts leaf.trivia ++ leafTexts after) := rewrite same, sameBehind
    _ = leafTexts (behind.reverseOnto [leaf, ..after]) := (leafTextsReverseOnto behind [leaf, ..after]).flipped

--| Rule 4 keeps the comments in order.
theorem letsFromTexts ∀ (behind rest: List Leaf):
    leafTexts (letsFrom behind rest) = leafTexts (behind.reverseOnto rest) :=
  match rest with
    | [] => byComputing
    | [leaf, ..after] =>
      match leaf.trivia.trailing with
        | None =>
          Eq.trans
            (letsFromTexts [leaf, ..behind] after)
            (consTexts leaf leaf behind behind after byComputing byComputing)
        | Some comment =>
          match leaf.kind == ColonEq && letBefore behind 0 && semicolonAfter after 0 with
            | True =>
              let moved := { leaf |
                trivia = { leaf.trivia | leading = leaf.trivia.leading ++ [comment.unspaced], trailing = None }
              }
              let same: triviaTexts moved.trivia = triviaTexts leaf.trivia :=
                rewrite List.mapAppend leaf.trivia.leading [comment.unspaced] (comment => comment.text), List.appendNil
              Eq.trans
                (letsFromTexts [moved, ..behind] after)
                (consTexts moved leaf behind behind after same byComputing)
            | False =>
              Eq.trans
                (letsFromTexts [leaf, ..behind] after)
                (consTexts leaf leaf behind behind after byComputing byComputing)

theorem arrowMovesTexts ∀ (current next: Leaf) (rest: List Text):
    triviaTexts { current.trivia |
      leading = current.trivia.leading
        ++ (current.trivia.trailing.map (comment => [comment.unspaced]) |> .getOrElse [])
        ++ next.trivia.leading,
      trailing = None
    }
      ++ (triviaTexts (next.withLeading []).trivia ++ rest)
      = triviaTexts current.trivia ++ (triviaTexts next.trivia ++ rest) :=
  match current.trivia.trailing with
    | None => rewrite repeatedly [List.mapAppend, List.appendAssoc, List.appendNil]
    | Some comment => rewrite repeatedly [List.mapAppend, List.appendAssoc]

--| Rule 3 keeps the comments in order.
theorem arrowsFromTexts ∀ (current: Leaf) (rest: List Leaf):
    leafTexts (arrowsFrom [] current rest) = leafTexts [current, ..rest] :=
  match rest with
    | [] => byComputing
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
          rewrite arrowsFromOnto [moved] (next.withLeading []) more, arrowsFromTexts (next.withLeading []) more then
            arrowMovesTexts current next (leafTexts more)
        | False => rewrite arrowsFromOnto [current] next more, arrowsFromTexts next more

theorem arrowsTexts ∀ (leaves: List Leaf): leafTexts (arrows leaves) = leafTexts leaves := match leaves with
  | [] => byComputing
  | [first, ..rest] => arrowsFromTexts first rest

def carriedTexts: Option Carried → List Text
  | Some carried => carried.comments.map (comment => comment.text)
  | None => []

theorem intoTexts ∀ (carried: Carried) (trivia: Trivia):
    triviaTexts (carried.into trivia) = carried.comments.map (comment => comment.text) ++ triviaTexts trivia :=
  match trivia.leading with
    | [] => byComputing
    | [first, ..more] => rewrite repeatedly [List.mapAppend, List.appendAssoc]

theorem receivedTexts ∀ (carried: Option Carried) (trivia: Trivia):
    triviaTexts (carried.map (carry => carry.into trivia) |> .getOrElse trivia)
      = carriedTexts carried ++ triviaTexts trivia :=
  match carried with
    | None => byComputing
    | Some carry => intoTexts carry trivia

theorem carriesTexts ∀ (trivia: Trivia) (carry: Carried)
    (carries: commaCarries trivia = Some carry):
    carriedTexts (Some carry) = triviaTexts trivia :=
  match trivia.leading, trivia.trailing with
    | [], Some comment => cases
    | [first, ..more], Some comment =>
      cases then rewrite List.mapAppend more [{ comment | blankLines = trivia.blankLines }] (comment => comment.text)
    | [first, ..more], None => rewrite List.appendNil then cases

--| Rule 2 keeps the comments in order: a comma's go to the token after it.
theorem commasFromTexts ∀ (done: List Leaf) (carried: Option Carried) (rest: List Leaf) (end: Trivia):
    leafTexts (commasFrom done carried rest end).leaves ++ triviaTexts (commasFrom done carried rest end).end
      = leafTexts (done.reverseOnto []) ++ (carriedTexts carried ++ (leafTexts rest ++ triviaTexts end)) :=
  match rest with
    | [] => rewrite receivedTexts carried end
    | [leaf, ..after] =>
      let received := { leaf | trivia = carried.map (carry => carry.into leaf.trivia) |> .getOrElse leaf.trivia }
      let receivedText: triviaTexts received.trivia = carriedTexts carried ++ triviaTexts leaf.trivia :=
        receivedTexts carried leaf.trivia
      let kept := commasFromTexts [received, ..done] None after end
      let keptText: leafTexts (commasFrom [received, ..done] None after end).leaves
        ++ triviaTexts (commasFrom [received, ..done] None after end).end
        = leafTexts (done.reverseOnto []) ++ (carriedTexts carried ++ (leafTexts [leaf, ..after] ++ triviaTexts end)) :=
        rewrite kept, leafTextsReverseOnto done [received], receivedText then
          rewrite repeatedly [List.appendAssoc, List.appendNil]
      match c: commaCarries received.trivia with
        | None => keptText
        | Some carry =>
          match leaf.kind == Comma with
            | True =>
              let emptied := { received | trivia = Trivia.empty }
              rewrite commasFromTexts [emptied, ..done] (Some carry) after end,
                  leafTextsReverseOnto done [emptied],
                  carriesTexts received.trivia carry c,
                  receivedText then
                rewrite repeatedly [List.appendAssoc]
            | False => keptText

theorem trimmedTriviaTexts ∀ (trivia: Trivia): triviaTexts trivia.trimmed = (triviaTexts trivia).map trimEnd :=
  let leading: (trivia.leading.map Comment.trimmed).map (comment => comment.text)
    = (trivia.leading.map (comment => comment.text)).map trimEnd :=
    rewrite List.mapMap trivia.leading (comment => comment.text) Comment.trimmed,
        List.mapMap trivia.leading trimEnd (comment => comment.text)
  match trivia.trailing with
    | None => rewrite List.mapAppend, leading
    | Some comment => rewrite List.mapAppend, leading

--| Rule 5 trims each comment and keeps them in order.
theorem trimmedTexts ∀ (leaves: List Leaf) (end: Trivia):
    leavesTexts (leaves.map (leaf => { leaf | trivia = leaf.trivia.trimmed })) end.trimmed
      = (leavesTexts leaves end).map trimEnd :=
  match leaves with
    | [] => trimmedTriviaTexts end
    | [leaf, ..rest] => rewrite List.mapAppend, trimmedTriviaTexts leaf.trivia, trimmedTexts rest end

--| Rules 2 to 5 keep the comments in order, trimmed: rule N keeps them if
--| rule 1 does.
theorem settledTextsAfterHome ∀ (lexed: Lexed):
    lexedTexts lexed.settled = (leafTexts (homeFrom [] None lexed.leaves) ++ triviaTexts lexed.end).map trimEnd :=
  let homed := homeFrom [] None lexed.leaves
  let commas := commasFrom [] None homed lexed.end
  let arrowed := arrows commas.leaves
  calc lexedTexts lexed.settled
    _ = (leavesTexts (letsFrom [] arrowed) commas.end).map trimEnd := trimmedTexts (letsFrom [] arrowed) commas.end
    _ = (leafTexts (letsFrom [] arrowed) ++ triviaTexts commas.end).map trimEnd :=
      rewrite leavesTextsSplit (letsFrom [] arrowed) commas.end
    _ = (leafTexts commas.leaves ++ triviaTexts commas.end).map trimEnd :=
      rewrite letsFromTexts [] arrowed, arrowsTexts commas.leaves
    _ = (leafTexts homed ++ triviaTexts lexed.end).map trimEnd := rewrite commasFromTexts [] None homed lexed.end
