--| Proofs about comment placement (`Syntax/Settle.sw`, `Lexed.settled`) for slice 1 of the proved formatter
--| (docs/proposals/self-hosted-fmt-s1-sketch.md, ticket 15).

namespace Syntax.SettleProofs
import Std (Bool, Char, DecEq, Eq, Finite, List, Nat, Option, Text, Void)
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
    | [_, .._], Zero | Succ Zero => byComputing
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

--| The back-walk keeps the tokens.
theorem homeFromTokens ∀ (bareLast: Bool) (behind: List Leaf) (bumped: Option Comment) (rest: List Leaf):
    tokens (homeFrom bareLast behind bumped rest) = tokens (behind.reverseOnto rest) :=
  match rest with
    | [] => byComputing
    | [leaf, ..after] =>
      let step := (x: Leaf) (settled: List Leaf) (next: Option Comment) (same: x.token = leaf.token) (sameBehind: tokens
          settled
        = tokens behind) =>
        Eq.trans
          (homeFromTokens bareLast [x, ..settled] next after)
          (consTokens x leaf settled behind after after same sameBehind byComputing)
      match bumped with
        | None =>
          match leaf.trivia.trailing with
            | None => step leaf behind None byComputing byComputing
            | Some comment =>
              match movable leaf behind after with
                | False => step leaf behind None byComputing byComputing
                | True =>
                  match stepsBack bareLast leaf behind after 0 with
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
                  match stepsBack bareLast lifted behind after 0 with
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

--| The comma carry keeps the tokens.
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

--| The arrow lift keeps the tokens.
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

--| The let lift keeps the tokens.
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

--| Comment placement moves comments and nothing else: the tokens are the lexer's.
theorem settledWithKeepsTokens ∀ (lexed: Lexed) (bareLast: Bool):
    tokens (lexed.settledWith bareLast).leaves = tokens lexed.leaves :=
  let homed := homeFrom bareLast [] None lexed.leaves
  let commas := commasFrom [] None homed lexed.end
  calc tokens (lexed.settledWith bareLast).leaves
    _ = tokens (letsFrom [] (arrows commas.leaves)) := trimmedTokens (letsFrom [] (arrows commas.leaves))
    _ = tokens (arrows commas.leaves) := letsFromTokens [] (arrows commas.leaves)
    _ = tokens commas.leaves := arrowsTokens commas.leaves
    _ = tokens homed := commasFromTokens [] None homed lexed.end
    _ = tokens lexed.leaves := homeFromTokens bareLast [] None lexed.leaves

theorem settledKeepsTokens ∀ (lexed: Lexed): tokens lexed.settled.leaves = tokens lexed.leaves :=
  settledWithKeepsTokens lexed False

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

--| After the comma carry no comma holds a comment.
theorem commasFromBare ∀ (done: List Leaf) (carried: Option Carried) (rest: List Leaf) (end: Trivia)
    (doneBare: done.all bareComma = True):
    (commasFrom done carried rest end).leaves.all bareComma = True :=
  match rest with
    | [] => List.allReverseOntoTrue bareComma done [] doneBare byComputing
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

--| The arrow lift gives a comma no comment.
theorem arrowsFromBare ∀ (done: List Leaf) (current: Leaf) (rest: List Leaf)
    (doneBare: done.all bareComma = True)
    (currentBare: bareComma current = True)
    (restBare: rest.all bareComma = True):
    (arrowsFrom done current rest).all bareComma = True :=
  match rest with
    | [] => List.allReverseOntoTrue bareComma done [current] doneBare (rewrite currentBare)
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

--| The let lift gives a comma no comment.
theorem letsFromBare ∀ (behind rest: List Leaf)
    (behindBare: behind.all bareComma = True)
    (restBare: rest.all bareComma = True):
    (letsFrom behind rest).all bareComma = True :=
  match rest with
    | [] => List.allReverseOntoTrue bareComma behind [] behindBare byComputing
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

--| Trim gives a comma no comment.
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

--| After comment placement no comma holds a comment, so the tree needs no place for
--| one.
theorem settledCommasBare ∀ (lexed: Lexed): lexed.settled.leaves.all bareComma = True :=
  let homed := homeFrom False [] None lexed.leaves
  let commas := commasFrom [] None homed lexed.end
  trimmedBare
    (letsFrom [] (arrows commas.leaves))
    (letsFromBare []
      (arrows commas.leaves)
      byComputing
      (arrowsBareCommas commas.leaves (commasFromBare [] None homed lexed.end byComputing)))

-- Under slice 1's alphabet there is no `let` and no `|`, so comment placement's
-- clauses for an expression `let`'s `:=` and a record update's bar do
-- nothing.

--| Every leaf's token is in slice 1's alphabet.
def alphabet1 (leaves: List Leaf): Bool := (tokens leaves).all (token => token.kind.within1)

theorem alphabet1Leaves ∀ (leaves: List Leaf)
    (within: alphabet1 leaves = True):
    leaves.all (leaf => leaf.kind.within1) = True :=
  rewrite List.allMapBool leaves (token => token.kind.within1) (leaf => leaf.token) at within then within

--| A kind in slice 1's alphabet is none of the kinds outside it. Decided for every pair of kinds at once.
theorem within1Not ∀ (kind other: Tok)
    (without: other.within1 = False)
    (within: kind.within1 = True):
    (kind == other) = False :=
  let checked :=
    Finite.check (((kind, other)) => !kind.within1 || other.within1 || !(kind == other)) byComputing (kind, other)
  Bool.notTrue (kind == other) (rewrite within, without at checked then checked)

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
                        | True => Eq.trans isLet.flipped (within1Not leaf.kind KwLet byComputing within)
                        | False =>
                          match leaf.kind == Semi || leaf.kind == FatArrow || leaf.kind.startsDeclaration with
                            | True => byComputing
                            | False => letBeforeNone earlier depth noLet

--| Under slice 1's alphabet the let lift does nothing.
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
  DecEq.soundFalse leaf.kind Pipe (within1Not leaf.kind Pipe byComputing within)

--| Under slice 1's alphabet the back-walk walks past commas and closers only.
theorem skippedQuiet1 ∀ (leaf: Leaf) (behind ahead: List Leaf)
    (within: leaf.kind.within1 = True):
    skipped leaf behind ahead = (leaf.kind == Comma || leaf.kind.isCloser) :=
  match comma: leaf.kind == Comma with
    | True => rewrite skipped.eq.comma leaf behind ahead (DecEq.sound comma)
    | False => rewrite skipped.eq.alt3 leaf behind ahead (DecEq.soundFalse leaf.kind Comma comma) (notPipe1 leaf within)

--| Under slice 1's alphabet the back-walk moves comments from commas that don't
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

-- Trim: a comment's text, trimmed, has no space at its end.

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

-- Arrow lift: no `->` keeps a comment after it.

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

--| The arrow lift's result is `arrowsBare`, and starts with its first leaf, which
--| changed only if it is an `->`.
--|
--| Proof idea: by induction on the leaves; the leaf after the current one
--| starts the rest's result unchanged unless it is an `->`, so when the
--| current leaf is an `->` the comments the arrow lift took from that leaf are the
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
              let empty := List.eqNilOfIsEmpty next.trivia.leading (Bool.notFalse _ (Bool.orFalseLeft _ _ moves))
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
    | [] | [_] => byComputing
    | [first, second, ..rest] =>
      let later := trimmedArrowsBare [second, ..rest] (Bool.andRight bare)
      match first.trivia.trailing, second.trivia.leading with
        | None, [] => rewrite later, Bool.andTrue then Bool.andLeft bare
        | None, [_, .._] => rewrite later, Bool.andTrue then Bool.andLeft bare
        | Some _, [] => rewrite later, Bool.andTrue then Bool.andLeft bare
        | Some _, [_, .._] => rewrite later, Bool.andTrue then Bool.andLeft bare

--| After comment placement no `->` holds a trailing comment, and the token after it
--| no own-line comments, unless that token is another `->`.
theorem settledArrowsBare1 ∀ (lexed: Lexed)
    (within: alphabet1 lexed.leaves = True):
    arrowsBare lexed.settled.leaves = True :=
  let homed := homeFrom False [] None lexed.leaves
  let commas := commasFrom [] None homed lexed.end
  let arrowed := arrows commas.leaves
  let arrowedWithin: alphabet1 arrowed = True := calc alphabet1 arrowed
    _ = alphabet1 lexed.leaves :=
      rewrite arrowsTokens commas.leaves,
          commasFromTokens [] None homed lexed.end,
          homeFromTokens False [] None lexed.leaves
    _ = True := within
  let quiet: letsFrom [] arrowed = arrowed := letsQuiet1 [] arrowed byComputing (alphabet1Leaves arrowed arrowedWithin)
  trimmedArrowsBare (letsFrom [] arrowed) (rewrite quiet then arrowsArrowsBare commas.leaves)

-- Comments kept in order. The comma carry, arrow lift, let lift and trim keep them for any leaves; the back-walk
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

--| The let lift keeps the comments in order.
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

--| The arrow lift keeps the comments in order.
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

--| The comma carry keeps the comments in order: a comma's go to the token after it.
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
  match trivia.trailing with | None | Some _ => rewrite List.mapAppend, leading

--| Trim trims each comment and keeps them in order.
theorem trimmedTexts ∀ (leaves: List Leaf) (end: Trivia):
    leavesTexts (leaves.map (leaf => { leaf | trivia = leaf.trivia.trimmed })) end.trimmed
      = (leavesTexts leaves end).map trimEnd :=
  match leaves with
    | [] => trimmedTriviaTexts end
    | [leaf, ..rest] => rewrite List.mapAppend, trimmedTriviaTexts leaf.trivia, trimmedTexts rest end

--| The comma carry, arrow lift, let lift and trim keep the comments in order, trimmed: comment placement keeps them if
--| the back-walk does.
theorem settledTextsAfterHome ∀ (lexed: Lexed):
    lexedTexts lexed.settled = (leafTexts (homeFrom False [] None lexed.leaves) ++ triviaTexts lexed.end).map trimEnd :=
  let homed := homeFrom False [] None lexed.leaves
  let commas := commasFrom [] None homed lexed.end
  let arrowed := arrows commas.leaves
  calc lexedTexts lexed.settled
    _ = (leavesTexts (letsFrom [] arrowed) commas.end).map trimEnd := trimmedTexts (letsFrom [] arrowed) commas.end
    _ = (leafTexts (letsFrom [] arrowed) ++ triviaTexts commas.end).map trimEnd :=
      rewrite leavesTextsSplit (letsFrom [] arrowed) commas.end
    _ = (leafTexts commas.leaves ++ triviaTexts commas.end).map trimEnd :=
      rewrite letsFromTexts [] arrowed, arrowsTexts commas.leaves
    _ = (leafTexts homed ++ triviaTexts lexed.end).map trimEnd := rewrite commasFromTexts [] None homed lexed.end

-- The back-walk keeps the comments in order, for leaves as the lexer gives them
-- under slice 1's alphabet. A trailing comment moves back past commas and
-- closers; the walk must pass no comment and land on a leaf with no
-- trailing comment of its own.

--| Leaves as the lexer lays them out: a leaf with own-line comments
--| starts its line, and so does the leaf after a trailing comment.
--| `pending`: the leaf before had a trailing comment.
def laidOut (pending: Bool) (leaves: List Leaf): Bool := match leaves with
  | [] => True
  | [leaf, ..rest] =>
    (leaf.trivia.leading.isEmpty || leaf.token.lineStart)
      && (!pending || leaf.token.lineStart)
      && laidOut leaf.trivia.trailing.isSome rest

--| A comma or closer: under slice 1's alphabet, what the back-walk walks past.
def passable (leaf: Leaf): Bool := leaf.kind == Comma || leaf.kind.isCloser

--| The back-walk back from `current` (`stepsBack`'s steps) passes no
--| comment: each leaf it passes has no own-line comments, and the leaf
--| before it no trailing comment.
def walkClean (current: Leaf) (behind ahead: List Leaf): Bool := match behind with
  | [] => True
  | [previous, ..earlier] =>
    if !skipped current behind ahead then True
    else if current.token.lineStart
      && (!current.trivia.leading.isEmpty || endsWithComment behind [current, ..ahead]) then
      True
    else
      current.trivia.leading.isEmpty && previous.trivia.trailing.isNone && walkClean previous earlier [current, ..ahead]

--| The `steps` newest leaves of `behind` (`steps` at least 1) hold no
--| comment a moved comment would pass or replace: the newest `steps - 1`
--| are commas or closers with no comments, and the one after has no
--| trailing comment.
def quietFor (steps: Nat) (behind: List Leaf): Bool := match steps, behind with
  | Succ Zero, [target, .._] => target.trivia.trailing.isNone
  | Succ (Succ more), [leaf, ..earlier] =>
    leaf.trivia.leading.isEmpty && leaf.trivia.trailing.isNone && passable leaf && quietFor (Succ more) earlier
  | _, _ => False

--| Where a clean walk ends: it passes no leaf, or `current` has no
--| own-line comments, is a comma or closer, and the leaves it passes are
--| quiet.
--|
--| Proof idea: by induction on `behind`, following `stepsBack` and
--| `walkClean`, which test the same conditions.
theorem walkSteps ∀ (current: Leaf) (behind ahead: List Leaf) (steps: Nat)
    (clean: walkClean current behind ahead = True)
    (within: current.kind.within1 = True)
    (behindWithin: behind.all (leaf => leaf.kind.within1) = True):
    ∃ (passed: Nat) => stepsBack False current behind ahead steps = steps + passed
      ∧ (passed = 0 ∨ (current.trivia.leading.isEmpty ∧ passable current ∧ quietFor passed behind)) :=
  match behind with
    | [] => (0, arithmetic, Inl byComputing)
    | [previous, ..earlier] =>
      match skips: skipped current [previous, ..earlier] ahead with
        | False => (0, arithmetic, Inl byComputing)
        | True =>
          match stops: current.token.lineStart
            && (!current.trivia.leading.isEmpty || endsWithComment [previous, ..earlier] [current, ..ahead]) with
            | True => (0, arithmetic, Inl byComputing)
            | False =>
              let leadEmpty := Bool.andLeft clean
              let previousUntrailed := Bool.andLeft (Bool.andRight clean)
              let previousClean := Bool.andRight (Bool.andRight clean)
              let currentPassable: passable current = True :=
                Eq.trans (skippedQuiet1 current [previous, ..earlier] ahead within).flipped skips
              let (passed, walked, quiet) :=
                walkSteps previous earlier
                  [current, ..ahead]
                  (Succ steps)
                  previousClean
                  (Bool.andLeft behindWithin)
                  (Bool.andRight behindWithin)
              let quietHere: quietFor (Succ passed) [previous, ..earlier] = True := match passed, quiet with
                | Zero, _ => previousUntrailed
                | Succ more, Inl zero => cases
                | Succ more, Inr (previousLead, previousPassable, quietEarlier) =>
                  Bool.andIntro previousLead
                    (Bool.andIntro previousUntrailed (Bool.andIntro previousPassable quietEarlier))
              (Succ passed, rewrite walked then arithmetic, Inr (leadEmpty, currentPassable, quietHere))

--| A comment moved back over quiet leaves comes after all their comments.
theorem movedTexts ∀ (behind: List Leaf) (steps: Nat) (comment: Comment)
    (quiet: quietFor steps behind = True):
    leafTexts ((trailingAt behind steps comment).reverseOnto [])
      = leafTexts (behind.reverseOnto []) ++ [comment.text] :=
  match steps, behind with
    | Succ Zero, [target, ..earlier] =>
      match target.trivia.trailing with
        | None =>
          rewrite leafTextsReverseOnto earlier [target.withTrailing (Some comment)],
              leafTextsReverseOnto earlier [target] then
            rewrite repeatedly [List.appendAssoc]
    | Succ (Succ more), [leaf, ..earlier] =>
      match leaf.trivia.leading, leaf.trivia.trailing with
        | [], None =>
          rewrite leafTextsReverseOnto (trailingAt earlier (Succ more) comment) [leaf],
              leafTextsReverseOnto earlier [leaf],
              movedTexts earlier (Succ more) comment (Bool.andRight quiet) then
            rewrite repeatedly [List.appendAssoc, List.appendNil]

--| After a comment moves back, the line still ends with it, seen from the
--| comma or closer it left.
theorem movedEnds ∀ (x: Leaf) (behind ahead: List Leaf) (steps: Nat) (comment: Comment)
    (untrailed: x.trivia.trailing.isNone = True)
    (xPassable: passable x = True)
    (xWithin: x.kind.within1 = True)
    (behindWithin: behind.all (leaf => leaf.kind.within1) = True)
    (quiet: quietFor steps behind = True):
    endsWithComment [x, ..trailingAt behind steps comment] ahead = True :=
  match x.trivia.trailing with
    | None =>
      match steps, behind with
        | Succ Zero, [target, ..earlier] =>
          rewrite skippedQuiet1 x [target.withTrailing (Some comment), ..earlier] ahead xWithin, xPassable
        | Succ (Succ more), [leaf, ..earlier] =>
          rewrite skippedQuiet1 x [leaf, ..trailingAt earlier (Succ more) comment] ahead xWithin, xPassable then
            movedEnds leaf earlier
              [x, ..ahead]
              (Succ more)
              comment
              (Bool.andLeft (Bool.andRight quiet))
              (Bool.andLeft (Bool.andRight (Bool.andRight quiet)))
              (Bool.andLeft behindWithin)
              (Bool.andRight behindWithin)
              (Bool.andRight (Bool.andRight (Bool.andRight quiet)))

--| The back-walk is clean from any next leaf laid out as the lexer lays
--| it out, given whether the leaf before had a trailing comment.
def CleanFor (behind: List Leaf) (pending: Bool): Prop :=
  ∀ (next: Leaf) (ahead: List Leaf) => (next.trivia.leading.isEmpty || next.token.lineStart) = True
    → (!pending || next.token.lineStart) = True
    → walkClean next behind ahead = True

theorem withinOfTokens ∀ (xs ys: List Leaf)
    (same: tokens xs = tokens ys)
    (within: ys.all (leaf => leaf.kind.within1) = True):
    xs.all (leaf => leaf.kind.within1) = True :=
  let viaTokens: (tokens ys).all (token => token.kind.within1) = True :=
    rewrite List.allMapBool ys (token => token.kind.within1) (leaf => leaf.token) then within
  rewrite <- List.allMapBool xs (token => token.kind.within1) (leaf => leaf.token), same then viaTokens

--| A leaf with no trailing comment keeps the walk clean.
theorem cleanUntrailed ∀ (leaf: Leaf) (behind: List Leaf) (pending later: Bool)
    (clean: CleanFor behind pending)
    (laid: (leaf.trivia.leading.isEmpty || leaf.token.lineStart) = True)
    (afterPending: (!pending || leaf.token.lineStart) = True)
    (untrailed: leaf.trivia.trailing.isNone = True):
    CleanFor [leaf, ..behind] later :=
  next ahead nextLaid nextPending =>
    match skipped next [leaf, ..behind] ahead with
      | False => byComputing
      | True =>
        match stops: next.token.lineStart
          && (!next.trivia.leading.isEmpty || endsWithComment [leaf, ..behind] [next, ..ahead]) with
          | True => byComputing
          | False =>
            match next.trivia.leading with
              | [] => Bool.andIntro untrailed (clean leaf [next, ..ahead] laid afterPending)
              | [first, ..more] => Void.impossible (Bool.trueNotFalse (rewrite nextLaid at stops then stops))

--| A leaf with a trailing comment stops every walk from the leaf after it,
--| which starts its line.
theorem cleanTrailed ∀ (leaf: Leaf) (behind: List Leaf)
    (ends: ∀ (ahead: List Leaf) => endsWithComment [leaf, ..behind] ahead = True):
    CleanFor [leaf, ..behind] True :=
  next ahead nextLaid nextPending =>
    match skipped next [leaf, ..behind] ahead with
      | False => byComputing
      | True => rewrite nextPending, ends [next, ..ahead], Bool.orTrue

--| The back-walk keeps the comments in order, for leaves laid out as the lexer
--| lays them out, under slice 1's alphabet.
--|
--| Proof idea: by induction on the leaves left, keeping `CleanFor`: the
--| walk from the next leaf passes no comment (`walkSteps`), so a comment
--| moved back lands after everything it passes (`movedTexts`); and a leaf
--| that held a trailing comment, kept or moved, stops the walk from the
--| leaf after it, which starts its line (`movedEnds`).
theorem homeFromTexts ∀ (behind rest: List Leaf) (pending: Bool)
    (clean: CleanFor behind pending)
    (laid: laidOut pending rest = True)
    (behindWithin: behind.all (leaf => leaf.kind.within1) = True)
    (restWithin: rest.all (leaf => leaf.kind.within1) = True):
    leafTexts (homeFrom False behind None rest) = leafTexts (behind.reverseOnto rest) :=
  match rest with
    | [] => byComputing
    | [leaf, ..after] =>
      let leafLaid := Bool.andLeft laid
      let leafPending := Bool.andLeft (Bool.andRight laid)
      let afterLaid := Bool.andRight (Bool.andRight laid)
      let within := Bool.andLeft restWithin
      let afterWithin := Bool.andRight restWithin
      let withLeaf: [leaf, ..behind].all (leaf => leaf.kind.within1) = True := rewrite within then behindWithin
      let kept := (later: Bool) (cleanLater: CleanFor [leaf, ..behind] later) (laidLater: laidOut later after = True) =>
        Eq.trans
          (homeFromTexts [leaf, ..behind] after later cleanLater laidLater withLeaf afterWithin)
          (consTexts leaf leaf behind behind after byComputing byComputing)
      match trailing: leaf.trivia.trailing with
        | None => kept False (cleanUntrailed leaf behind pending False clean leafLaid leafPending byComputing) afterLaid
        | Some comment =>
          let trailed := cleanTrailed leaf behind (ahead => byComputing)
          match movable leaf behind after with
            | False => kept True trailed afterLaid
            | True =>
              let (passed, walked, quiet) :=
                walkSteps leaf behind after 0 (clean leaf after leafLaid leafPending) within behindWithin
              rewrite walked then
                match passed, quiet with
                  | Zero, _ => rewrite barsQuiet1 leaf behind after within then kept True trailed afterLaid
                  | Succ more, Inl zero => cases
                  | Succ more, Inr (leadEmpty, leafPassable, quietBehind) =>
                    let moved := leaf.withTrailing None
                    let target := trailingAt behind (Succ more) comment
                    let movedWithin: [moved, ..target].all (leaf => leaf.kind.within1) = True :=
                      rewrite within then
                        withinOfTokens target behind (trailingAtTokens behind (Succ more) comment) behindWithin
                    let movedClean: CleanFor [moved, ..target] True := cleanTrailed moved target (ahead =>
                      movedEnds moved behind ahead
                        (Succ more)
                        comment
                        byComputing
                        leafPassable
                        within
                        behindWithin
                        quietBehind)
                    let empty := List.eqNilOfIsEmpty leaf.trivia.leading leadEmpty
                    calc leafTexts (homeFrom False [moved, ..target] None after)
                      _ = leafTexts ([moved, ..target].reverseOnto after) :=
                        homeFromTexts [moved, ..target] after True movedClean afterLaid movedWithin afterWithin
                      _ = leafTexts (target.reverseOnto []) ++ (triviaTexts moved.trivia ++ leafTexts after) :=
                        leafTextsReverseOnto target [moved, ..after]
                      _ = (leafTexts (behind.reverseOnto []) ++ [comment.text])
                          ++ (triviaTexts moved.trivia ++ leafTexts after) :=
                        rewrite movedTexts behind (Succ more) comment quietBehind
                      _ = leafTexts (behind.reverseOnto []) ++ (triviaTexts leaf.trivia ++ leafTexts after) :=
                        rewrite empty, trailing then rewrite repeatedly [List.appendAssoc]
                      _ = leafTexts (behind.reverseOnto [leaf, ..after]) :=
                        (leafTextsReverseOnto behind [leaf, ..after]).flipped

--| Comment placement keeps every comment, in order, less the spaces at its end, for
--| leaves laid out as the lexer lays them out, under slice 1's alphabet.
theorem settledKeepsComments ∀ (lexed: Lexed)
    (within: alphabet1 lexed.leaves = True)
    (laid: laidOut False lexed.leaves = True):
    lexedTexts lexed.settled = (lexedTexts lexed).map trimEnd :=
  let homed: leafTexts (homeFrom False [] None lexed.leaves) = leafTexts lexed.leaves :=
    homeFromTexts [] lexed.leaves False
      (next ahead nextLaid nextPending => byComputing)
      laid
      byComputing
      (alphabet1Leaves lexed.leaves within)
  calc lexedTexts lexed.settled
    _ = (leafTexts (homeFrom False [] None lexed.leaves) ++ triviaTexts lexed.end).map trimEnd :=
      settledTextsAfterHome lexed
    _ = (leavesTexts lexed.leaves lexed.end).map trimEnd := rewrite homed, leavesTextsSplit lexed.leaves lexed.end

-- The back-walk's result is homed: a closer keeps a trailing comment only where
-- the back-walk itself would stop it, so it starts its line and has own-line
-- comments or follows code that ends with a comment.

--| `endsWithComment` under slice 1's alphabet, where a bar never comes up.
def endsOn: List Leaf → Bool
  | [] => False
  | [leaf, ..earlier] =>
    if leaf.trivia.trailing.isSome then True
    else if earlier.isEmpty || !passable leaf then False
    else endsOn earlier

theorem endsOnQuiet1 ∀ (line ahead: List Leaf)
    (within: line.all (leaf => leaf.kind.within1) = True):
    endsWithComment line ahead = endsOn line :=
  match line with
    | [] => byComputing
    | [leaf, ..earlier] =>
      match leaf.trivia.trailing.isSome with
        | True => byComputing
        | False =>
          rewrite skippedQuiet1 leaf earlier ahead (Bool.andLeft within),
              endsOnQuiet1 earlier [leaf, ..ahead] (Bool.andRight within)

--| Where the back-walk stops a comment on `leaf`, `older` the leaves before it,
--| newest first.
def stopsAt (leaf: Leaf) (older: List Leaf): Bool :=
  leaf.token.lineStart && (!leaf.trivia.leading.isEmpty || endsOn older)

--| The leaf `steps` back from `current` is where a walk may end: not a
--| comma or closer, the first leaf, or one the back-walk stops on.
def landsAt (steps: Nat) (current: Leaf) (behind: List Leaf): Bool := match steps, behind with
  | Zero, _ => !passable current || behind.isEmpty || stopsAt current behind
  | Succ more, [previous, ..earlier] => landsAt more previous earlier
  | Succ _, [] => False

--| The back-walk ends on a leaf it may end on.
theorem walkLands ∀ (current: Leaf) (behind ahead: List Leaf) (steps: Nat)
    (within: current.kind.within1 = True)
    (behindWithin: behind.all (leaf => leaf.kind.within1) = True):
    ∃ (passed: Nat) => stepsBack False current behind ahead steps = steps + passed
      ∧ landsAt passed current behind = True :=
  match behind with
    | [] => (0, arithmetic, Bool.orRight byComputing)
    | [previous, ..earlier] =>
      let passes: skipped current [previous, ..earlier] ahead = passable current :=
        skippedQuiet1 current [previous, ..earlier] ahead within
      let ends: endsWithComment [previous, ..earlier] [current, ..ahead] = endsOn [previous, ..earlier] :=
        endsOnQuiet1 [previous, ..earlier] [current, ..ahead] behindWithin
      match skips: passable current with
        | False => (0, rewrite passes then arithmetic, rewrite skips)
        | True =>
          match stops: current.token.lineStart
            && (!current.trivia.leading.isEmpty || endsWithComment [previous, ..earlier] [current, ..ahead]) with
            | True =>
              let stopsHere: stopsAt current [previous, ..earlier] = True := rewrite ends at stops then stops
              (0, rewrite passes then arithmetic, rewrite skips, stopsHere)
            | False =>
              let (passed, walked, lands) :=
                walkLands previous earlier
                  [current, ..ahead]
                  (Succ steps)
                  (Bool.andLeft behindWithin)
                  (Bool.andRight behindWithin)
              (Succ passed, rewrite passes, walked then arithmetic, lands)

--| A closer with a trailing comment is one the back-walk stops on, given the
--| leaves before it, newest first; a comma with one starts its line.
def homedLeaf (leaf: Leaf) (older: List Leaf): Bool :=
  leaf.trivia.trailing.isNone
    || ((!leaf.kind.isCloser || older.isEmpty || stopsAt leaf older)
      && (!(leaf.kind == Comma) || older.isEmpty || leaf.token.lineStart))

--| `homedLeaf` of every leaf, newest first.
def homedBehind: List Leaf → Bool
  | [] => True
  | [leaf, ..older] => homedLeaf leaf older && homedBehind older

theorem closerLands ∀ (leaf: Leaf) (rest: Bool)
    (lands: (!passable leaf || rest) = True):
    (!leaf.kind.isCloser || rest) = True :=
  match closer: leaf.kind.isCloser with
    | False => byComputing
    | True => rewrite Bool.orTrue at lands then lands

theorem commaLands ∀ (leaf: Leaf) (older: List Leaf)
    (lands: (!passable leaf || older.isEmpty || stopsAt leaf older) = True):
    (!(leaf.kind == Comma) || older.isEmpty || leaf.token.lineStart) = True :=
  match comma: leaf.kind == Comma with
    | False => byComputing
    | True =>
      match older.isEmpty with
        | True => byComputing
        | False => Bool.andLeft lands

--| Where a walk may end, a comment is homed.
theorem landsHomed ∀ (leaf: Leaf) (older: List Leaf)
    (lands: (!passable leaf || older.isEmpty || stopsAt leaf older) = True):
    homedLeaf leaf older = True :=
  Bool.orRight
    (Bool.andIntro (closerLands leaf (older.isEmpty || stopsAt leaf older) lands) (commaLands leaf older lands))

--| A comment the back-walk can't move is homed: on a comma that starts its line
--| or a leaf that is neither comma nor closer.
theorem fixedHomed ∀ (leaf: Leaf) (behind ahead: List Leaf)
    (within: leaf.kind.within1 = True)
    (fixed: movable leaf behind ahead = False):
    homedLeaf leaf behind = True :=
  let fixed1 := rewrite movableQuiet1 leaf behind ahead within at fixed then fixed
  let notCloser: leaf.kind.isCloser = False := Bool.orFalseRight _ _ fixed1
  let commaStarts := Bool.orFalseLeft _ _ fixed1
  let commaPart: (!(leaf.kind == Comma) || behind.isEmpty || leaf.token.lineStart) = True :=
    match comma: leaf.kind == Comma with
      | False => byComputing
      | True => Bool.orRight (Bool.notFalse _ commaStarts)
  Bool.orRight (Bool.andIntro (rewrite notCloser) commaPart)

--| A comment moved back over quiet leaves to where the walk ends keeps the
--| leaves homed.
theorem trailingAtHomed ∀ (behind: List Leaf) (steps: Nat) (comment: Comment) (current: Leaf)
    (homed: homedBehind behind = True)
    (quiet: quietFor steps behind = True)
    (lands: landsAt steps current behind = True):
    homedBehind (trailingAt behind steps comment) = True :=
  match steps, behind with
    | Succ Zero, [target, ..earlier] =>
      Bool.andIntro (landsHomed (target.withTrailing (Some comment)) earlier lands) (Bool.andRight homed)
    | Succ (Succ more), [leaf, ..earlier] =>
      Bool.andIntro
        (Bool.orLeft (Bool.andLeft (Bool.andRight quiet)))
        (trailingAtHomed earlier
          (Succ more)
          comment
          leaf
          (Bool.andRight homed)
          (Bool.andRight (Bool.andRight (Bool.andRight quiet)))
          lands)

--| The back-walk's result is homed, for leaves laid out as the lexer lays them
--| out, under slice 1's alphabet.
--|
--| Proof idea: by induction on the leaves left, keeping `homedBehind` of
--| the leaves settled: a comment the back-walk keeps or moves ends on a leaf its
--| walk may end on (`walkLands`), the leaves it passes have none
--| (`walkSteps`), and the leaves before the one it lands on don't change.
theorem homeFromHomed ∀ (behind rest: List Leaf) (pending: Bool)
    (clean: CleanFor behind pending)
    (laid: laidOut pending rest = True)
    (behindWithin: behind.all (leaf => leaf.kind.within1) = True)
    (restWithin: rest.all (leaf => leaf.kind.within1) = True)
    (homed: homedBehind behind = True):
    homedBehind ((homeFrom False behind None rest).reverseOnto []) = True :=
  match rest with
    | [] => rewrite List.reverseReverse behind then homed
    | [leaf, ..after] =>
      let leafLaid := Bool.andLeft laid
      let leafPending := Bool.andLeft (Bool.andRight laid)
      let afterLaid := Bool.andRight (Bool.andRight laid)
      let within := Bool.andLeft restWithin
      let afterWithin := Bool.andRight restWithin
      let withLeaf: [leaf, ..behind].all (leaf => leaf.kind.within1) = True := rewrite within then behindWithin
      let kept := (later: Bool) (cleanLater: CleanFor [leaf, ..behind] later) (laidLater: laidOut later after
        = True) (homedLater: homedBehind [leaf, ..behind] = True) =>
        homeFromHomed [leaf, ..behind] after later cleanLater laidLater withLeaf afterWithin homedLater
      match trailing: leaf.trivia.trailing with
        | None =>
          kept False (cleanUntrailed leaf behind pending False clean leafLaid leafPending byComputing) afterLaid homed
        | Some comment =>
          let trailed := cleanTrailed leaf behind (ahead => byComputing)
          match fixed: movable leaf behind after with
            | False => kept True trailed afterLaid (Bool.andIntro (fixedHomed leaf behind after within fixed) homed)
            | True =>
              let (passed, walked, quiet) :=
                walkSteps leaf behind after 0 (clean leaf after leafLaid leafPending) within behindWithin
              let (landed, walkedToo, lands) := walkLands leaf behind after 0 within behindWithin
              let same: landed = passed := arithmetic [walked, walkedToo]
              let landsHere := rewrite same at lands then lands
              rewrite walked then
                match passed, quiet with
                  | Zero, _ =>
                    rewrite barsQuiet1 leaf behind after within then
                      kept True trailed afterLaid (Bool.andIntro (landsHomed leaf behind landsHere) homed)
                  | Succ more, Inl zero => cases
                  | Succ more, Inr (leadEmpty, leafPassable, quietBehind) =>
                    let moved := leaf.withTrailing None
                    let target := trailingAt behind (Succ more) comment
                    let movedWithin: [moved, ..target].all (leaf => leaf.kind.within1) = True :=
                      rewrite within then
                        withinOfTokens target behind (trailingAtTokens behind (Succ more) comment) behindWithin
                    let movedClean: CleanFor [moved, ..target] True := cleanTrailed moved target (ahead =>
                      movedEnds moved behind ahead
                        (Succ more)
                        comment
                        byComputing
                        leafPassable
                        within
                        behindWithin
                        quietBehind)
                    homeFromHomed
                      [moved, ..target]
                      after
                      True
                      movedClean
                      afterLaid
                      movedWithin
                      afterWithin
                      (trailingAtHomed behind (Succ more) comment leaf homed quietBehind landsHere)

-- From the back-walk's result to comment placement's: the comma carry, arrow lift, let lift and trim take comments off commas
-- and `->`, and add own-line comments, so a closer the back-walk stops on still
-- stops, given that no comma that starts its line and no `->` comes just
-- before a comma or closer.

--| A comma or closer, by kind.
def passableKind (kind: Tok): Bool := kind == Comma || kind.isCloser

--| What may not follow `->`: a comma, a closer, or another `->`.
def arrowFollow (kind: Tok): Bool := passableKind kind || kind == Arrow

--| `plain` (spike K1) for slice 1's alphabet, from the second token on:
--| no `->` before a comma, closer or `->`, and no comma that starts its
--| line before a comma or closer.
def plainFrom: List Token → Bool
  | [first, second, ..rest] =>
    (!(first.kind == Arrow) || !arrowFollow second.kind)
      && (!(first.kind == Comma && first.lineStart) || !passableKind second.kind)
      && plainFrom [second, ..rest]
  | _ => True

--| `plain` for slice 1's alphabet: as `plainFrom`, and the first token is
--| no comma or closer. Almost every file that parses is `plain`: K1's case
--| (a comma starting its line before a closer, whose comments comment placement parks)
--| parses and isn't, and the proofs under `plain1` leave it out.
def plain1 (tokens: List Token): Bool := match tokens with
  | [] => True
  | [first, .._] => !passableKind first.kind && plainFrom tokens

--| `plain1` read newest first.
def backOk: List Token → Bool
  | [newer, older, ..rest] =>
    (!(older.kind == Arrow) || !arrowFollow newer.kind)
      && (!(older.kind == Comma && older.lineStart) || !passableKind newer.kind)
      && backOk [older, ..rest]
  | [only] => !passableKind only.kind
  | [] => True

theorem plainBack ∀ (ahead: List Token) (newest: Token) (behind: List Token)
    (ok: backOk [newest, ..behind] = True)
    (plain: plainFrom [newest, ..ahead] = True):
    backOk (ahead.reverseOnto [newest, ..behind]) = True :=
  match ahead with
    | [] => ok
    | [next, ..rest] =>
      plainBack rest next
        [newest, ..behind]
        (Bool.andIntro (Bool.andLeft plain) (Bool.andIntro (Bool.andLeft (Bool.andRight plain)) ok))
        (Bool.andRight (Bool.andRight plain))

theorem plainReversed ∀ (tokens: List Token) (plain: plain1 tokens = True): backOk (tokens.reverseOnto []) = True :=
  match tokens with
    | [] => byComputing
    | [first, ..rest] => plainBack rest first [] (Bool.andLeft plain) (Bool.andRight plain)

--| How a pass may change a leaf's comments: take a trailing comment away,
--| keeping those of leaves other than commas and `->`, and keep a
--| closer's own-line comments.
def relatedLeaf (before after: Leaf): Bool :=
  (after.trivia.trailing.isNone || before.trivia.trailing.isSome)
    && (before.kind == Comma || before.kind == Arrow || before.trivia.trailing.isNone || after.trivia.trailing.isSome)
    && (!before.kind.isCloser || before.trivia.leading.isEmpty || !after.trivia.leading.isEmpty)

def related: List Leaf → List Leaf → Bool
  | [], [] => True
  | [before, ..befores], [after, ..afters] => relatedLeaf before after && related befores afters
  | _, _ => False

theorem headToken ∀ (before after: Leaf) (befores afters: List Leaf)
    (same: tokens [before, ..befores] = tokens [after, ..afters]):
    after.token = before.token :=
  (Eq.cong (list => list.head.getOrElse before.token) same).flipped

theorem tailTokens ∀ (before after: Leaf) (befores afters: List Leaf)
    (same: tokens [before, ..befores] = tokens [after, ..afters]):
    tokens befores = tokens afters :=
  Eq.cong (list => list.drop 1) same

--| A line that ends with a comment before any of the later steps (the comma carry to trim) still does
--| after it, seen from a comma or closer.
--|
--| Proof idea: by induction on the line, newest first. The comment the
--| line ends with is on a leaf the pass keeps it on: not a comma, which
--| would start its line before a comma or closer (or be the first token),
--| nor a `->` before one.
theorem endsTransfer ∀ (befores afters: List Leaf) (newer: Token)
    (same: tokens befores = tokens afters)
    (rel: related befores afters = True)
    (ok: backOk [newer, ..tokens befores] = True)
    (newerPassable: passableKind newer.kind = True)
    (homed: homedBehind befores = True)
    (ends: endsOn befores = True):
    endsOn afters = True :=
  match befores, afters with
    | [before, ..older], [after, ..olders] =>
      let kind := headToken before after older olders same
      match trailing: before.trivia.trailing with
        | Some comment =>
          match comma: before.kind == Comma with
            | True =>
              match older with
                | [] => Void.impossible (Bool.falseNotTrue (Bool.andRight (Bool.andRight ok)))
                | [first, ..rest] =>
                  let starts := Bool.andRight (Bool.andLeft homed)
                  let clause := rewrite starts, newerPassable at Bool.andLeft (Bool.andRight ok)
                  Void.impossible (Bool.falseNotTrue clause)
            | False =>
              match arrow: before.kind == Arrow with
                | True => Void.impossible (Bool.falseNotTrue (rewrite newerPassable at Bool.andLeft ok))
                | False => Bool.orLeft (Bool.andLeft (Bool.andRight (Bool.andLeft rel)))
        | None =>
          match older, olders with
            | [first, ..rest], [next, ..nexts] =>
              match passes: passable before with
                | True =>
                  let untrailed := Bool.andLeft (Bool.andLeft rel)
                  let later :=
                    endsTransfer
                      [first, ..rest]
                      [next, ..nexts]
                      before.token
                      (tailTokens before after [first, ..rest] [next, ..nexts] same)
                      (Bool.andRight rel)
                      (Bool.andRight (Bool.andRight ok))
                      passes
                      homed
                      ends
                  match after.trivia.trailing with
                    | None => rewrite kind, passes then later
            | [first, ..rest], [] => cases

theorem backOkTail ∀ (newer: Token) (older: List Token) (ok: backOk [newer, ..older] = True): backOk older = True :=
  match older with
    | [] => byComputing
    | [_, .._] => Bool.andRight (Bool.andRight ok)

--| A pass that changes comments only as `relatedLeaf` allows keeps the
--| leaves homed.
--|
--| Proof idea: by induction on the leaves, newest first. A trailing
--| comment after the pass was there before; a closer that held one keeps
--| its line start and own-line comments, and the line before it still ends
--| with a comment (`endsTransfer`); a comma that held one still starts its
--| line.
theorem homedTransfer ∀ (befores afters: List Leaf)
    (same: tokens befores = tokens afters)
    (rel: related befores afters = True)
    (ok: backOk (tokens befores) = True)
    (homed: homedBehind befores = True):
    homedBehind afters = True :=
  match befores, afters with
    | [], [] => byComputing
    | [before, ..older], [after, ..olders] =>
      let kind := headToken before after older olders same
      let sameOlder := tailTokens before after older olders same
      let rest :=
        homedTransfer older olders sameOlder
          (Bool.andRight rel)
          (backOkTail before.token (tokens older) ok)
          (Bool.andRight homed)
      let here: homedLeaf after olders = True := match trailing: after.trivia.trailing with
        | None => byComputing
        | Some comment =>
          match before.trivia.trailing with
            | Some kept =>
              let parts := Bool.andLeft homed
              let closerBefore := Bool.andLeft parts
              let commaBefore := Bool.andRight parts
              rewrite kind then
                match older, olders with
                  | [], [] => rewrite repeatedly [Bool.orTrue]
                  | [first, ..others], [next, ..nexts] =>
                    let closerPart: (!before.token.kind.isCloser
                      || ([next, ..nexts].isEmpty
                        || (before.token.lineStart && (!after.trivia.leading.isEmpty || endsOn [next, ..nexts]))))
                      = True :=
                      match closer: before.token.kind.isCloser with
                        | False => byComputing
                        | True =>
                          match before.trivia.leading with
                            | [] =>
                              Bool.andIntro
                                (Bool.andLeft closerBefore)
                                (Bool.orRight
                                  (endsTransfer
                                    [first, ..others]
                                    [next, ..nexts]
                                    before.token
                                    sameOlder
                                    (Bool.andRight rel)
                                    ok
                                    (Bool.orRight closer)
                                    (Bool.andRight homed)
                                    (Bool.andRight closerBefore)))
                            | [_, .._] =>
                              Bool.andIntro (Bool.andLeft closerBefore) (Bool.orLeft (Bool.andRight (Bool.andLeft rel)))
                    Bool.andIntro closerPart commaBefore
      Bool.andIntro here rest

theorem relatedReverseOnto ∀ (befores afters befores2 afters2: List Leaf)
    (rel: related befores afters = True)
    (rel2: related befores2 afters2 = True):
    related (befores.reverseOnto befores2) (afters.reverseOnto afters2) = True :=
  match befores, afters with
    | [], [] => rel2
    | [before, ..rest], [after, ..rests] =>
      relatedReverseOnto rest rests
        [before, ..befores2]
        [after, ..afters2]
        (Bool.andRight rel)
        (Bool.andIntro (Bool.andLeft rel) rel2)

--| A leaf whose trailing comment is kept and whose own-line comments are
--| kept or added to.
theorem relatedKeeping ∀ (leaf: Leaf) (trivia: Trivia)
    (trailing: trivia.trailing = leaf.trivia.trailing)
    (leading: (leaf.trivia.leading.isEmpty || !trivia.leading.isEmpty) = True):
    relatedLeaf leaf { leaf | trivia } = True :=
  let leadingPart := Bool.orRight [a := !leaf.kind.isCloser] leading
  match own: leaf.trivia.trailing with
    | None | Some _ => rewrite trailing then Bool.andIntro (rewrite repeatedly [Bool.orTrue]) leadingPart

theorem receivedLeading ∀ (carried: Option Carried) (trivia: Trivia):
    (trivia.leading.isEmpty || !(carried.map (carry => carry.into trivia) |> .getOrElse trivia).leading.isEmpty)
      = True :=
  match trivia.leading with
    | [] => byComputing
    | [first, ..more] =>
      match carried with
        | None => byComputing
        | Some carry =>
          rewrite List.isEmptyAppendCons carry.comments
            { first | blankLines = Nat.max first.blankLines carry.blankLines }
            more

--| The comma carry only takes comments off commas and adds own-line comments.
theorem commasRelated ∀ (doneBefore done: List Leaf) (carried: Option Carried) (rest: List Leaf) (end: Trivia)
    (rel: related doneBefore done = True):
    related (doneBefore.reverseOnto rest) (commasFrom done carried rest end).leaves = True :=
  match rest with
    | [] => relatedReverseOnto doneBefore done [] [] rel byComputing
    | [leaf, ..after] =>
      let receivedTrivia := carried.map (carry => carry.into leaf.trivia) |> .getOrElse leaf.trivia
      let received := { leaf | trivia = receivedTrivia }
      let receivedTrailing: receivedTrivia.trailing = leaf.trivia.trailing := match carried with
        | None => byComputing
        | Some carry =>
          match leaf.trivia.leading with
            | [] => byComputing
            | [_, .._] => byComputing
      let keep := relatedKeeping leaf receivedTrivia receivedTrailing (receivedLeading carried leaf.trivia)
      match commaCarries received.trivia with
        | None => commasRelated [leaf, ..doneBefore] [received, ..done] None after end (Bool.andIntro keep rel)
        | Some carry =>
          match comma: leaf.kind == Comma with
            | True =>
              let notCloser: leaf.kind.isCloser = False := rewrite DecEq.sound comma
              let emptied: relatedLeaf leaf { received | trivia = Trivia.empty } = True :=
                Bool.andIntro (Bool.orLeft comma) (Bool.orLeft (rewrite notCloser))
              commasRelated
                [leaf, ..doneBefore]
                [{ received | trivia = Trivia.empty }, ..done]
                (Some carry)
                after
                end
                (Bool.andIntro emptied rel)
            | False => commasRelated [leaf, ..doneBefore] [received, ..done] None after end (Bool.andIntro keep rel)

theorem relatedSelf ∀ (leaf: Leaf): relatedLeaf leaf leaf = True :=
  relatedKeeping leaf leaf.trivia byComputing
    (match leaf.trivia.leading with
      | [] => byComputing
      | [_, .._] => byComputing)

theorem relatedCleared ∀ (leaf: Leaf)
    (notCloser: leaf.kind.isCloser = False):
    relatedLeaf leaf (leaf.withLeading []) = True :=
  let leadingPart: (!leaf.kind.isCloser || leaf.trivia.leading.isEmpty || !([]: List Comment).isEmpty) = True :=
    Bool.orLeft (rewrite notCloser)
  match leaf.trivia.trailing with | None | Some _ => Bool.andIntro (rewrite repeatedly [Bool.orTrue]) leadingPart

--| The arrow lift only takes comments off `->` and the own-line comments off the
--| token after it, which is no closer in a `plain` file.
theorem arrowsRelated ∀ (original current: Leaf) (rest: List Leaf)
    (rel: relatedLeaf original current = True)
    (kind: current.token = original.token)
    (plain: plainFrom (tokens [original, ..rest]) = True):
    related [original, ..rest] (arrowsFrom [] current rest) = True :=
  match rest with
    | [] => Bool.andIntro rel byComputing
    | [next, ..more] =>
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
          let originalArrow: original.token.kind = Arrow :=
            Eq.trans (Eq.cong (token => token.kind) kind.flipped) (DecEq.sound (Bool.andLeft moves))
          let movedRelated: relatedLeaf original moved = True := rewrite originalArrow
          let follows := rewrite originalArrow at Bool.andLeft plain
          let notFollow := Bool.notTrue _ follows
          let notCloser: next.kind.isCloser = False := Bool.orFalseRight _ _ (Bool.orFalseLeft _ _ notFollow)
          rewrite arrowsFromOnto [moved] (next.withLeading []) more then
            Bool.andIntro movedRelated
              (arrowsRelated next
                (next.withLeading [])
                more
                (relatedCleared next notCloser)
                byComputing
                (Bool.andRight (Bool.andRight plain)))
        | False =>
          rewrite arrowsFromOnto [current] next more then
            Bool.andIntro rel
              (arrowsRelated next next more (relatedSelf next) byComputing (Bool.andRight (Bool.andRight plain)))

--| Trim changes no comment's place.
theorem trimRelated ∀ (leaves: List Leaf):
    related leaves (leaves.map (leaf => { leaf | trivia = leaf.trivia.trimmed })) = True :=
  match leaves with
    | [] => byComputing
    | [leaf, ..rest] =>
      let here: relatedLeaf leaf { leaf | trivia = leaf.trivia.trimmed } = True := cases
      Bool.andIntro here (trimRelated rest)

theorem tokensReversed ∀ (xs ys: List Leaf)
    (same: tokens xs = tokens ys):
    tokens (xs.reverseOnto []) = tokens (ys.reverseOnto []) :=
  rewrite tokensReverseOnto xs [], tokensReverseOnto ys [], same

theorem backOkOf ∀ (leaves: List Leaf) (original: List Token)
    (same: tokens leaves = original)
    (plain: plain1 original = True):
    backOk (tokens (leaves.reverseOnto [])) = True :=
  rewrite tokensReverseOnto leaves [], same then plainReversed original plain

theorem plainFromOf ∀ (original: List Token) (plain: plain1 original = True): plainFrom original = True :=
  match original with
    | [] => byComputing
    | [_, .._] => Bool.andRight plain

-- The source's test: `plain1` with a last comma allowed to start its line (SW-4131).

--| A token with its line start forgotten: what comment placement's bare last commas keep (they only ever change a closer's line
--| start).
def flatToken (token: Token): Token := { token | lineStart = False }

--| Whether a comma may follow a leaf of this kind as a last one: `hasItem`'s test of the leaf before it.
def itemKind (kind: Tok): Bool := match kind with
  | Comma | Pipe => False
  | other => !other.isOpener

--| `plainFrom`, with a comma that starts its line allowed before a closer when it is a last comma: the closer comes
--| right after it and an item is before it. `item` says whether one is before the first token (`hasItem`), which
--| decides whether the driver treats such a comma as a last one at all.
def sourcePlainFrom (item: Bool): List Token → Bool
  | [first, second, ..rest] =>
    (!(first.kind == Arrow) || !arrowFollow second.kind)
      && (!(first.kind == Comma && first.lineStart) || !passableKind second.kind || (second.kind.isCloser && item))
      && sourcePlainFrom (itemKind first.kind) [second, ..rest]
  | _ => True

--| `plain1` for a source file: as `plainFrom`, a last comma may start its line. Its other clauses are `plain1`'s: the
--| first token is no comma or closer, and no `->` comes before a comma, closer or `->`.
def sourcePlain1 (tokens: List Token): Bool := match tokens with
  | [] => True
  | [first, .._] => !passableKind first.kind && sourcePlainFrom False tokens

--| The clause about `->` alone, which is all the arrow lift's proofs need.
def arrowFrom: List Token → Bool
  | [first, second, ..rest] => (!(first.kind == Arrow) || !arrowFollow second.kind) && arrowFrom [second, ..rest]
  | _ => True

theorem sourceOfPlain ∀ (item: Bool) (toks: List Token)
    (plain: plainFrom toks = True):
    sourcePlainFrom item toks = True :=
  match toks with
    | [] => byComputing
    | [first, ..rest] =>
      match rest with
        | [] => byComputing
        | [second, ..more] =>
          Bool.andIntro
            (Bool.andLeft plain)
            (Bool.andIntro
              (Bool.orExtend _ _ _ (Bool.andLeft (Bool.andRight plain)))
              (sourceOfPlain (itemKind first.kind) [second, ..more] (Bool.andRight (Bool.andRight plain))))

--| `plain1` is `sourcePlain1`: the driver accepts every source it did before.
theorem sourcePlainOfPlain ∀ (toks: List Token) (plain: plain1 toks = True): sourcePlain1 toks = True := match toks with
  | [] => byComputing
  | [first, ..rest] => Bool.andIntro (Bool.andLeft plain) (sourceOfPlain False [first, ..rest] (Bool.andRight plain))

theorem sourcePlainFromOf ∀ (toks: List Token) (plain: sourcePlain1 toks = True): sourcePlainFrom False toks = True :=
  match toks with
    | [] => byComputing
    | [_, .._] => Bool.andRight plain

theorem arrowOfSource ∀ (item: Bool) (toks: List Token)
    (plain: sourcePlainFrom item toks = True):
    arrowFrom toks = True :=
  match toks with
    | [] => byComputing
    | [first, ..rest] =>
      match rest with
        | [] => byComputing
        | [second, ..more] =>
          Bool.andIntro
            (Bool.andLeft plain)
            (arrowOfSource (itemKind first.kind) [second, ..more] (Bool.andRight (Bool.andRight plain)))

theorem flatKind ∀ (token: Token): (flatToken token).kind = token.kind := match token with
  | { kind, text, column, lineStart } => byComputing

--| Tokens equal once line starts are forgotten have the same `->` clauses.
theorem arrowFromFlat ∀ (xs ys: List Token) (same: xs.map flatToken = ys.map flatToken): arrowFrom xs = arrowFrom ys :=
  match xs, ys, same with
    | [], [], _ => byComputing
    | [x, ..xr], [y, ..yr], same =>
      let head: flatToken x = flatToken y := List.consInjectiveHead same
      let tail: xr.map flatToken = yr.map flatToken := Eq.cong (.drop 1) same
      let kind: x.kind = y.kind := rewrite <- flatKind x, <- flatKind y then Eq.cong (token => token.kind) head
      match xr, yr, tail with
        | [], [], _ => byComputing
        | [x2, ..xr2], [y2, ..yr2], tail2 =>
          let head2: flatToken x2 = flatToken y2 := List.consInjectiveHead tail2
          let kind2: x2.kind = y2.kind :=
            rewrite <- flatKind x2, <- flatKind y2 then Eq.cong (token => token.kind) head2
          rewrite kind, kind2, arrowFromFlat [x2, ..xr2] [y2, ..yr2] tail2
    | [], [y, ..yr], never => (List.nilNotCons (flatToken y) (yr.map flatToken) never).impossible
    | [x, ..xr], [], never => (List.nilNotCons (flatToken x) (xr.map flatToken) never.flipped).impossible

--| A test that reads no line start holds of tokens equal once line starts are forgotten.
theorem allFlat ∀ (p: Token → Bool)
    (blind: ∀ (token: Token) => p (flatToken token) = p token) (xs ys: List Token)
    (same: xs.map flatToken = ys.map flatToken):
    xs.all p = ys.all p :=
  match xs, ys, same with
    | [], [], _ => byComputing
    | [x, ..xr], [y, ..yr], same =>
      let head: flatToken x = flatToken y := List.consInjectiveHead same
      let tail: xr.map flatToken = yr.map flatToken := Eq.cong (.drop 1) same
      let px: p x = p y := rewrite <- blind x, <- blind y then Eq.cong p head
      rewrite px, allFlat p blind xr yr tail
    | [], [y, ..yr], never => (List.nilNotCons (flatToken y) (yr.map flatToken) never).impossible
    | [x, ..xr], [], never => (List.nilNotCons (flatToken x) (xr.map flatToken) never.flipped).impossible

theorem arrowsRelatedAll ∀ (leaves: List Leaf)
    (plain: plainFrom (tokens leaves) = True):
    related leaves (arrows leaves) = True :=
  match leaves with
    | [] => byComputing
    | [first, ..rest] => arrowsRelated first first rest (relatedSelf first) byComputing plain

--| Comment placement's result is homed: every closer that keeps a trailing comment
--| starts its line, and has own-line comments or follows code ending with
--| a comment, looking back past commas and closers; every comma that keeps
--| one starts its line. For `plain` leaves laid out as the lexer lays
--| them out, under slice 1's alphabet (K1's `settledHomed`).
--|
--| Proof idea: the back-walk's result is homed (`homeFromHomed`), and the comma carry,
--| arrow lift and trim only take trailing comments off commas and `->`, which in a
--| `plain` file no closer's line ends with, and keep closers' own-line
--| comments (`homedTransfer`); the let lift does nothing.
theorem settledHomed ∀ (lexed: Lexed)
    (within: alphabet1 lexed.leaves = True)
    (laid: laidOut False lexed.leaves = True)
    (plain: plain1 (tokens lexed.leaves) = True):
    homedBehind (lexed.settled.leaves.reverseOnto []) = True :=
  let homed := homeFrom False [] None lexed.leaves
  let commas := commasFrom [] None homed lexed.end
  let arrowed := arrows commas.leaves
  let trimmed := arrowed.map (leaf => { leaf | trivia = leaf.trivia.trimmed })
  let leavesWithin := alphabet1Leaves lexed.leaves within
  let homedTokens: tokens homed = tokens lexed.leaves := homeFromTokens False [] None lexed.leaves
  let commasTokens: tokens commas.leaves = tokens lexed.leaves :=
    Eq.trans (commasFromTokens [] None homed lexed.end) homedTokens
  let arrowedTokens: tokens arrowed = tokens lexed.leaves := Eq.trans (arrowsTokens commas.leaves) commasTokens
  let trimmedTokens1: tokens trimmed = tokens lexed.leaves := Eq.trans (trimmedTokens arrowed) arrowedTokens
  let homedFirst: homedBehind (homed.reverseOnto []) = True :=
    homeFromHomed [] lexed.leaves False
      (next ahead nextLaid nextPending => byComputing)
      laid
      byComputing
      leavesWithin
      byComputing
  let homedCommas: homedBehind (commas.leaves.reverseOnto []) = True :=
    homedTransfer
      (homed.reverseOnto [])
      (commas.leaves.reverseOnto [])
      (tokensReversed homed commas.leaves (Eq.trans homedTokens commasTokens.flipped))
      (relatedReverseOnto homed commas.leaves [] [] (commasRelated [] [] None homed lexed.end byComputing) byComputing)
      (backOkOf homed (tokens lexed.leaves) homedTokens plain)
      homedFirst
  let homedArrows: homedBehind (arrowed.reverseOnto []) = True :=
    homedTransfer
      (commas.leaves.reverseOnto [])
      (arrowed.reverseOnto [])
      (tokensReversed commas.leaves arrowed (Eq.trans commasTokens arrowedTokens.flipped))
      (relatedReverseOnto commas.leaves arrowed [] []
        (arrowsRelatedAll commas.leaves (rewrite commasTokens then plainFromOf (tokens lexed.leaves) plain))
        byComputing)
      (backOkOf commas.leaves (tokens lexed.leaves) commasTokens plain)
      homedCommas
  let arrowedWithin := withinOfTokens arrowed lexed.leaves (Eq.trans arrowedTokens byComputing) leavesWithin
  let quiet: letsFrom [] arrowed = arrowed := letsQuiet1 [] arrowed byComputing arrowedWithin
  rewrite quiet then
    homedTransfer
      (arrowed.reverseOnto [])
      (trimmed.reverseOnto [])
      (tokensReversed arrowed trimmed (Eq.trans arrowedTokens trimmedTokens1.flipped))
      (relatedReverseOnto arrowed trimmed [] [] (trimRelated arrowed) byComputing)
      (backOkOf arrowed (tokens lexed.leaves) arrowedTokens plain)
      homedArrows

-- Comment placement applied to its own result changes nothing.

--| With every comma bare the comma carry moves nothing.
theorem commasIdle ∀ (done rest: List Leaf) (end: Trivia)
    (bare: rest.all bareComma = True):
    commasFrom done None rest end = { leaves = done.reverseOnto rest, end } :=
  match rest with
    | [] => byComputing
    | [leaf, ..after] =>
      let next := commasIdle [leaf, ..done] after end (Bool.andRight bare)
      match carries: commaCarries leaf.trivia with
        | None => next
        | Some carry =>
          match comma: leaf.kind == Comma with
            | False => next
            | True =>
              let leafBare := Bool.andLeft bare
              let empty := rewrite Bool.orFalse at leafBare then leafBare
              match leaf.trivia.leading, leaf.trivia.trailing with
                | [], None => cases

--| With no comment after an `->` and no `->` before another, the arrow lift moves
--| nothing.
theorem arrowsIdle ∀ (done: List Leaf) (current: Leaf) (rest: List Leaf)
    (bare: arrowsBare [current, ..rest] = True)
    (plain: plainFrom (tokens [current, ..rest]) = True):
    arrowsFrom done current rest = done.reverseOnto [current, ..rest] :=
  match rest with
    | [] => byComputing
    | [next, ..more] =>
      let later := arrowsIdle [current, ..done] next more (Bool.andRight bare) (Bool.andRight (Bool.andRight plain))
      match arrow: current.kind == Arrow with
        | False => later
        | True =>
          let follows := Bool.notTrue _ (Bool.andLeft plain)
          let notArrow: (next.kind == Arrow) = False := Bool.orFalseRight _ _ follows
          let clause := Bool.andLeft bare
          let empty: next.trivia.leading.isEmpty = True :=
            rewrite notArrow, Bool.orFalse at clause then Bool.andRight clause
          match current.trivia.trailing with
            | None => rewrite empty then later

theorem arrowsIdleAll ∀ (leaves: List Leaf)
    (bare: arrowsBare leaves = True)
    (plain: plainFrom (tokens leaves) = True):
    arrows leaves = leaves :=
  match leaves with
    | [] => byComputing
    | [first, ..rest] => arrowsIdle [] first rest bare plain

-- Comment placement's result, written out again in any layout that starts a line at
-- each closer holding a comment, settles to itself (spike K1's
-- `settledAnyLayout`). The layouts are K1's `laidFrom` with `keeping`.

--| Whether the leaf is one the back-walk may leave a trailing comment on only
--| under its limits: a closer or a record update's `|` (K1).
def holder (leaf: Leaf) (behind ahead: List Leaf): Bool := leaf.kind != Comma && skipped leaf behind ahead

--| What the layout leaves of a leaf: its kind, text and comments.
type Shape = { kind: Tok, text: Text, trivia: Trivia }

theorem trailingAtZero ∀ (behind: List Leaf) (comment: Comment): trailingAt behind 0 comment = behind :=
  match behind with | [] | [_, .._] => byComputing

--| The `steps` newest leaves of `behind` are a comment's way back to
--| where it was: commas and closers that don't start their lines, then a
--| leaf the back-walk ends on.
def chainTo (steps: Nat) (behind: List Leaf): Bool := match steps, behind with
  | Succ Zero, [target, ..older] => !passable target || older.isEmpty || stopsAt target older
  | Succ (Succ more), [leaf, ..earlier] => passable leaf && !leaf.token.lineStart && chainTo (Succ more) earlier
  | _, _ => False

theorem landedHere ∀ (leaf: Leaf) (older ahead: List Leaf) (steps: Nat)
    (within: leaf.kind.within1 = True)
    (olderWithin: older.all (leaf => leaf.kind.within1) = True)
    (lands: (!passable leaf || older.isEmpty || stopsAt leaf older) = True):
    stepsBack False leaf older ahead steps = steps :=
  match older with
    | [] => byComputing
    | [previous, ..earlier] =>
      let passes := skippedQuiet1 leaf [previous, ..earlier] ahead within
      match p: passable leaf with
        | False => rewrite passes
        | True => rewrite passes, endsOnQuiet1 [previous, ..earlier] [leaf, ..ahead] olderWithin, lands

--| A carried comment's walk back is exactly its chain.
theorem chainSteps ∀ (current: Leaf) (behind ahead: List Leaf) (steps acc: Nat)
    (within: current.kind.within1 = True)
    (behindWithin: behind.all (leaf => leaf.kind.within1) = True)
    (passes: passable current = True)
    (notStart: current.token.lineStart = False)
    (chain: chainTo steps behind = True):
    stepsBack False current behind ahead acc = acc + steps :=
  match steps, behind with
    | Succ Zero, [target, ..older] =>
      let skips := skippedQuiet1 current [target, ..older] ahead within
      rewrite skips, passes, notStart then
        calc stepsBack False target older [current, ..ahead] (Succ acc)
          _ = Succ acc :=
            landedHere target older
              [current, ..ahead]
              (Succ acc)
              (Bool.andLeft behindWithin)
              (Bool.andRight behindWithin)
              chain
          _ = acc + 1 := arithmetic
    | Succ (Succ more), [leaf, ..earlier] =>
      let skips := skippedQuiet1 current [leaf, ..earlier] ahead within
      let later :=
        chainSteps leaf earlier
          [current, ..ahead]
          (Succ more)
          (Succ acc)
          (Bool.andLeft behindWithin)
          (Bool.andRight behindWithin)
          (Bool.andLeft chain)
          (Bool.notTrue _ (Bool.andLeft (Bool.andRight chain)))
          (Bool.andRight (Bool.andRight chain))
      rewrite skips, passes, notStart, later then arithmetic
