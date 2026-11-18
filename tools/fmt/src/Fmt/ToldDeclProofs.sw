--| What the rules' documents tell of a whole declaration (SW-4050, F3 of SW-4042).
namespace Fmt.ToldDeclProofs
import Std (Bool, DecEq, Doc, Eq, List, Nat, Option, Text)
import Std.Doc (..)
import Std.Doc.Proofs (..)
import Syntax (Comments, Decl, DefBody, DefKind, Expr, Header, InfixKind, Note, SourceFile, Tok, Word)
import Fmt (..)
import Fmt.SpellProofs (..)
import Fmt.ToldWordProofs (..)

-- What a reading says, as a list of entries to refine.

--| One entry no wider than another: a blank line for a blank line, a word for the same word with flags that allow no
--| more.
def EntryRefines: Told → Told → Prop
  | _, MaybeGap => False
  | _, Lost => False
  | Gap, Gap => True
  | Said text starts follows, Said other first second =>
    text = other ∧ (starts = True → first = True) ∧ (follows = True → second = True)
  | _, _ => False

--| `told` is no wider than `shape`: the same entries, each word's flags allowing no more than the shape's.
def Refines: List Told → List Told → Prop
  | [], [] => True
  | [entry, ..more], [other, ..rest] => EntryRefines entry other ∧ Refines more rest
  | _, _ => False

theorem refinesAppend ∀ (one two three four: List Told)
    (front: Refines one three)
    (back: Refines two four):
    Refines (one ++ two) (three ++ four) :=
  match one, three with
    | [], [] => back
    | [entry, ..more], [other, ..rest] =>
      let (head, tail) := front
      (head, refinesAppend more two rest four tail back)

--| An exact entry refines itself.
theorem entrySelf ∀ (entry: Told) (exact: entryExact entry = True): EntryRefines entry entry := match entry with
  | Gap => byComputing
  | Said text starts follows => (byComputing, (x => x, x => x))

--| An exact list refines itself.
theorem refinesSelf ∀ (told: List Told) (exact: toldExact told = True): Refines told told := match told with
  | [] => byComputing
  | [entry, ..rest] => (entrySelf entry (Bool.andLeft exact), refinesSelf rest (Bool.andRight exact))

theorem orImplies ∀ (x y z: Bool)
    (left: x = True → z = True)
    (right: y = True → z = True)
    (both: (x || y) = True):
    z = True :=
  match x with
    | True => left byComputing
    | False => right both

theorem mergeEntryRefines ∀ (one other shape: Told)
    (left: EntryRefines one shape)
    (right: EntryRefines other shape):
    ∃ (entry: Told) => mergeEntry one other = Some entry ∧ EntryRefines entry shape :=
  match shape, one, other with
    | Gap, Gap, Gap => (Gap, byComputing, byComputing)
    | Said text first second, Said x s f, Said y s2 f2 =>
      let (hx, (hs, hf)) := left
      let (hy, (hs2, hf2)) := right
      rewrite hx, hy, DecEq.refl text then
        (
          Said text (s || s2) (f || f2),
          byComputing,
          (byComputing, (both => orImplies s s2 first hs hs2 both, both => orImplies f f2 second hf hf2 both))
        )

--| Two layouts that each refine a shape, merged, refine it: the rules' choices tell the same words.
theorem mergeRefines ∀ (one other shape: List Told)
    (left: Refines one shape)
    (right: Refines other shape):
    Refines (mergeTold one other) shape :=
  match shape, one, other with
    | [], [], [] => byComputing
    | [entry, ..rest], [first, ..more], [second, ..later] =>
      let (leftHead, leftTail) := left
      let (rightHead, rightTail) := right
      let (merged, same, refines) := mergeEntryRefines first second entry leftHead rightHead
      rewrite same then (refines, mergeRefines more later rest leftTail rightTail)

-- A word.

--| A closer that holds a comment after it.
def closerTrails (word: Word): Bool := isCloserText word.text && word.trails

--| What a printed word says: its comments above it and blank line, its text, its trailing comment. A closer that holds
--| a comment starts its line; any other word is left to the layout.
def Word.shapeW (word: Word): List Told :=
  word.comments.toldAbove ++ [Said word.text True (!closerTrails word)] ++ word.toldTrail

--| The rules give a closer that holds a comment a line start: it is not hoisted, and has own-line comments or follows
--| code that ends with a comment.
def Word.homes (word: Word) (around: Around): Bool :=
  !closerTrails word || (!around.hoisted && (word.noted || around.before))

theorem forcedBool ∀ (hoisted before item blank closer trails: Bool) (above: List Note)
    (shut: (closer && trails) = True)
    (homed: (!hoisted && (!above.isEmpty || before)) = True):
    ((!hoisted && (!above.isEmpty || (item && blank))) || (closer && !(!above.isEmpty) && before && trails)) = True :=
  match hoisted, above with
    | False, [x, ..xs] => Bool.orLeft byComputing
    | False, [] =>
      match before, closer, trails with
        | True, True, True => Bool.orRight byComputing

theorem forcedOfHomes ∀ (word: Word) (around: Around)
    (closer: closerTrails word = True)
    (homes: word.homes around = True):
    word.forced around = True :=
  forcedBool around.hoisted around.before around.item word.comments.blankBefore
    (isCloserText word.text)
    word.trails
    word.comments.above
    closer
    (Bool.orElim homes (never => (Bool.falseNotTrue (rewrite closer at never then never)).impossible) (same => same))

theorem textSpotForced ∀ (word: Word) (around: Around) (spot: Spot)
    (forced: word.forced around = True):
    word.textSpot around spot = Spot.lineStart :=
  match word.leadsLine around, word.ownsLine around with
    | True, _ => byComputing
    | False, True => byComputing

theorem printedText ∀ (word: Word) (around: Around): (word.printed around).text = word.text := match around.hoisted with
  | True => byComputing
  | False => byComputing

theorem printedTrail ∀ (word: Word) (around: Around): (word.printed around).toldTrail = word.toldTrail :=
  match around.hoisted with
    | True => byComputing
    | False => byComputing

theorem printedCloser ∀ (word: Word) (around: Around): closerTrails (word.printed around) = closerTrails word :=
  match around.hoisted with
    | True => byComputing
    | False => byComputing

theorem refinesOne ∀ (text: Text) (starts follows first second: Bool)
    (left: starts = True → first = True)
    (right: follows = True → second = True):
    Refines [Said text starts follows] [Said text first second] :=
  ((byComputing, (left, right)), byComputing)

--| A word's text refines the shape where it is told as the shape says, and is left to the layout otherwise.
theorem wordTellingRefines ∀ (text: Text) (spot: Spot) (flag: Bool)
    (home: flag = False → spot = Spot.lineStart):
    Refines (wordTelling text spot).said [Said text True flag] :=
  match flag with
    | True =>
      match closing text, spot.held with
        | True, True => refinesOne text _ _ True True (x => byComputing) (x => byComputing)
        | True, False => refinesOne text _ _ True True (x => byComputing) (x => byComputing)
        | False, True => refinesOne text _ _ True True (x => byComputing) (x => byComputing)
        | False, False => refinesOne text _ _ True True (x => byComputing) (x => byComputing)
    | False =>
      rewrite home byComputing, wordTellingLine text then refinesOne text True False True False (x => x) (x => x)

theorem trailExact ∀ (word: Word): toldExact word.toldTrail = True := match word.comments.after with
  | Some comment => byComputing
  | None => byComputing

theorem shapePrinted ∀ (word: Word) (around: Around):
    (word.printed around).shapeW
      = word.toldLead around ++ [Said word.text True (!closerTrails word)] ++ word.toldTrail :=
  match around.hoisted with
    | True => byComputing
    | False => byComputing

--| What a leaf tells refines the printed word's shape.
theorem leafTellingShape ∀ (word: Word) (around: Around) (spot: Spot)
    (homes: word.homes around = True):
    Refines (word.leafTelling around spot).said (word.printed around).shapeW :=
  rewrite shapePrinted word around then
    refinesAppend _ _ _ _
      (refinesSelf (word.toldLead around) (toldAboveExact (word.printed around).comments))
      (refinesAppend _ _ _ _
        (wordTellingRefines word.text (word.textSpot around spot) (!closerTrails word) (flag =>
          textSpotForced word around spot (forcedOfHomes word around (Bool.notFalse _ flag) homes)))
        (refinesSelf word.toldTrail (trailExact word)))

--| A token's document tells the printed word's shape, from any spot.
--|
--| Proof idea: `leafTell` gives the own-line comments, the word and its trailing comment (`leafTellingShape`): the
--| comments and the trailing comment are exact, and the word is told as the shape says: a closer that holds a comment
--| starts its line (`homes`).
theorem leafShape ∀ (word: Word) (around: Around) (key: Nat) (spot: Spot)
    (sound: word.sound = True)
    (homes: word.homes around = True):
    Refines ((word.leaf around key).tell spot).said (word.printed around).shapeW :=
  rewrite leafTell word around key spot sound then leafTellingShape word around spot homes

theorem homesOpen ∀ (word: Word) (around: Around) (open: isCloserText word.text = False): word.homes around = True :=
  rewrite open

--| An opening bracket's document tells the printed word's shape, from any spot.
theorem openingShape ∀ (word: Word) (around: Around) (closer: Word) (spot: Spot)
    (sound: word.sound = True)
    (open: isCloserText word.text = False):
    Refines ((word.opening around closer).tell spot).said (word.printed around).shapeW :=
  rewrite openingTell word around closer spot sound open then
    leafTellingShape word around spot (homesOpen word around open)

-- What an expression tells.

--| The word with the comments the rules keep (`item`: it starts an item of a comma bracket), or, `hoisted`, with none
--| above it.
def Word.shapeK (word: Word) (item hoisted: Bool): List Told :=
  (if hoisted then { word | comments = { above = [], after = word.comments.after, blankBefore = False } }
   else word.kept item (isCloserText word.text)).shapeW

theorem printedShape ∀ (word: Word) (around: Around):
    (word.printed around).shapeW = word.shapeK around.item around.hoisted :=
  match around.hoisted with
    | True => byComputing
    | False => byComputing

--| Where the shape of a document is told, whatever the spot.
def Is (doc: Doc) (shape: List Told): Prop := ∀ (spot: Spot) => Refines (doc.tell spot).said shape

--| What an expression of the slice tells: each token's own-line comments, text and trailing comment, with a bare comma
--| between a bracket's items; `item` and `hoisted` as for `Word.shapeK` of the first token.
def Expr.shape: Expr → Bool → Bool → List Told
  | Atom _ word, item, hoisted => word.shapeK item hoisted
  | Paren open inner close, item, hoisted =>
    open.shapeK item hoisted ++ inner.shape False False ++ close.shapeK False False
  | Tuple open items _ close, item, hoisted =>
    open.shapeK item hoisted ++ itemsShape True items ++ close.shapeK False False
  | ListOf open items _ close, item, hoisted =>
    open.shapeK item hoisted ++ itemsShape (!items.all Expr.plainItem) items ++ close.shapeK False False
  | App head arguments, item, hoisted => head.shape item hoisted ++ argumentsShape arguments
  | Infix _ left operator right, item, hoisted =>
    left.shape item hoisted ++ operator.shapeK False False ++ right.shape False False
  | Prefix operator operand, item, hoisted => operator.shapeK item hoisted ++ operand.shape False False
  | _, _, _ => []

--| A bracket's items, `first` for the first's item flag, the rest items; a bare comma after each but the last.
def itemsShape (first: Bool): List Expr → List Told
  | [] => []
  | [item] => item.shape first False
  | [item, ..rest] => item.shape first False ++ [Said "," True True] ++ itemsShape True rest

def argumentsShape: List Expr → List Told
  | [] => []
  | [argument, ..rest] => argument.shape False False ++ argumentsShape rest

theorem shapeKLead ∀ (word: Word) (item: Bool):
    word.shapeK item False = (word.kept item (isCloserText word.text)).comments.toldAbove ++ word.shapeK item True :=
  byComputing

--| Leaving the first token's own-line comments out takes their reading from the front.
--|
--| Proof idea: Induction down the first operands, with `shapeKLead` at the token.
theorem shapeLead ∀ (expr: Expr) (item: Bool)
    (within: expr.within1 = True):
    expr.shape item False
      = (expr.lead.kept item (isCloserText expr.lead.text)).comments.toldAbove ++ expr.shape item True :=
  match expr with
    | Atom kind word => shapeKLead word item
    | Paren open inner close =>
      rewrite shapeKLead open item,
          List.appendAssoc
            (open.kept item (isCloserText open.text)).comments.toldAbove
            (open.shapeK item True)
            (inner.shape False False ++ close.shapeK False False)
    | Tuple open items comma close =>
      rewrite shapeKLead open item,
          List.appendAssoc
            (open.kept item (isCloserText open.text)).comments.toldAbove
            (open.shapeK item True)
            (itemsShape True items ++ close.shapeK False False)
    | ListOf open items comma close =>
      rewrite shapeKLead open item,
          List.appendAssoc
            (open.kept item (isCloserText open.text)).comments.toldAbove
            (open.shapeK item True)
            (itemsShape (!items.all Expr.plainItem) items ++ close.shapeK False False)
    | App head arguments =>
      rewrite shapeLead head item (Bool.andLeft within),
          List.appendAssoc
            (head.lead.kept item (isCloserText head.lead.text)).comments.toldAbove
            (head.shape item True)
            (argumentsShape arguments)
    | Infix kind left operator right =>
      match kind with
        | InfixBinary =>
          rewrite shapeLead left item (Bool.andLeft within),
              List.appendAssoc
                (left.lead.kept item (isCloserText left.lead.text)).comments.toldAbove
                (left.shape item True)
                (operator.shapeK False False ++ right.shape False False)
        | InfixArrow =>
          rewrite shapeLead left item (Bool.andLeft within),
              List.appendAssoc
                (left.lead.kept item (isCloserText left.lead.text)).comments.toldAbove
                (left.shape item True)
                (operator.shapeK False False ++ right.shape False False)
        | _ => cases
    | Prefix operator operand =>
      rewrite shapeKLead operator item,
          List.appendAssoc
            (operator.kept item (isCloserText operator.text)).comments.toldAbove
            (operator.shapeK item True)
            (operand.shape False False)

--| A node's frame tells its first token's own-line comments, then the node's document, which tells the rest.
theorem framedShape ∀ (expr: Expr) (around: Around) (doc: Doc)
    (within: expr.within1 = True)
    (sound: expr.lead.sound = True)
    (inner: Is doc (expr.shape around.item True)):
    Is (expr.framed around doc) (expr.shape around.item around.hoisted) :=
  spot =>
    rewrite firstWordLead expr within, framedTell expr.lead around doc spot sound then
      match around.hoisted with
        | True => inner (expr.lead.placedSpot around spot)
        | False =>
          rewrite shapeLead expr around.item within then
            refinesAppend _ _ _ _ (refinesSelf _ (toldAboveExact _)) (inner (expr.lead.placedSpot around spot))

-- Brackets and prefix operators.

--| `( … )` tells its opener, its inner expression and its closer.
theorem parenShape ∀ (open: Word) (inner: Expr) (close: Word) (around: Around)
    (openSound: open.sound = True)
    (closeSound: close.sound = True)
    (opens: isCloserText open.text = False)
    (homes: close.homes (around.next inner.trails (1 + inner.size)) = True)
    (each: Is (inner.el (around.next open.trails 1)) (inner.shape False False)):
    Is
      (parenDoc open inner close around)
      (open.shapeK around.item around.hoisted ++ inner.shape False False ++ close.shapeK False False) :=
  spot =>
    rewrite parenTell open inner close around spot openSound closeSound opens then
      refinesAppend _ _ _ _
        (rewrite <- printedShape open around then leafTellingShape open around spot (homesOpen open around opens))
        (refinesAppend _ _ _ _
          (each (inner.innerSpot (open.leafTelling around spot).after))
          (rewrite <- printedShape close (around.next inner.trails (1 + inner.size)) then
            leafTellingShape close (around.next inner.trails (1 + inner.size)) _ homes))

--| A prefix operator and its operand.
theorem prefixShape ∀ (operator: Word) (operand: Expr) (around: Around)
    (sound: operator.sound = True)
    (opens: isCloserText operator.text = False)
    (each: Is (operand.el (around.next operator.trails 1)) (operand.shape False False)):
    Is
      (Doc.concat [
        operator.leaf { around | hoisted = True } around.at,
        prefixGap operator operand,
        operand.el (around.next operator.trails 1)
      ])
      (operator.shapeK around.item True ++ operand.shape False False) :=
  spot =>
    rewrite prefixTell operator operand around spot sound then
      refinesAppend _ _ _ _
        (rewrite <- printedShape operator { around | hoisted = True } then
          leafTellingShape operator
            { around | hoisted = True }
            spot
            (homesOpen operator { around | hoisted = True } opens))
        (each _)

-- Documents together.

--| A list of documents tells a shape, one after another from where the one before left the printer.
def IsAll (docs: List Doc) (shape: List Told): Prop := ∀ (spot: Spot) => Refines (Doc.tellAll docs spot).said shape

--| Each document of a list has a shape of its own.
def IsEach: List Doc → List (List Told) → Prop
  | [], [] => True
  | [doc, ..docs], [shape, ..shapes] => Is doc shape ∧ IsEach docs shapes
  | _, _ => False

def joinShapes: List (List Told) → List Told
  | [] => []
  | [shape, ..shapes] => shape ++ joinShapes shapes

theorem isNil: IsAll [] [] := spot => byComputing

theorem isCons ∀ (doc: Doc) (docs: List Doc) (first second: List Told)
    (head: Is doc first)
    (tail: IsAll docs second):
    IsAll [doc, ..docs] (first ++ second) :=
  spot => refinesAppend _ _ _ _ (head spot) (tail (doc.tell spot).after)

theorem isLast ∀ (doc: Doc) (shape: List Told) (only: Is doc shape): IsAll [doc] shape := spot =>
  rewrite <- List.appendNil shape then refinesAppend _ _ _ _ (only spot) byComputing

theorem isAllSame ∀ (docs: List Doc) (shape shape': List Told)
    (all: IsAll docs shape)
    (same: shape = shape'):
    IsAll docs shape' :=
  rewrite same at all then all

theorem isSame ∀ (doc: Doc) (shape shape': List Told) (is: Is doc shape) (same: shape = shape'): Is doc shape' :=
  rewrite same at is then is

theorem isConcat ∀ (docs: List Doc) (shape: List Told) (all: IsAll docs shape): Is (Doc.concat docs) shape := spot =>
  rewrite concatTell docs spot then all spot

theorem isAppend ∀ (front back: List Doc) (one two: List Told)
    (first: IsAll front one)
    (second: IsAll back two):
    IsAll (front ++ back) (one ++ two) :=
  spot =>
    rewrite tellAllAppend front back spot then
      refinesAppend _ _ _ _ (first spot) (second (Doc.tellAll front spot).after)

theorem eachAll ∀ (docs: List Doc) (shapes: List (List Told))
    (each: IsEach docs shapes):
    IsAll docs (joinShapes shapes) :=
  match docs, shapes with
    | [], [] => isNil
    | [doc, ..more], [shape, ..rest] =>
      let (head, tail) := each
      isCons doc more shape (joinShapes rest) head (eachAll more rest tail)

theorem sepsTell ∀ (docs: List Doc) (shapes: List (List Told))
    (each: IsEach docs shapes) (spot: Spot):
    Refines (Doc.tellSeps docs spot).said (joinShapes shapes) :=
  match docs, shapes with
    | [], [] => byComputing
    | [doc, ..more], [shape, ..rest] =>
      let (head, tail) := each
      refinesAppend _ _ _ _ (head spot.afterSep) (sepsTell more rest tail (doc.tell spot.afterSep).after)

theorem isFill ∀ (docs: List Doc) (shapes: List (List Told))
    (each: IsEach docs shapes):
    Is (Fill docs) (joinShapes shapes) :=
  match docs, shapes with
    | [], [] => spot => byComputing
    | [doc, ..more], [shape, ..rest] =>
      let (head, tail) := each
      spot => refinesAppend _ _ _ _ (head spot) (sepsTell more rest tail (doc.tell spot).after)

theorem isNest ∀ (indent: Nat) (doc: Doc) (shape: List Told) (is: Is doc shape): Is (Nest indent doc) shape := is

theorem isGroup ∀ (doc: Doc) (hard: Bool) (shape: List Told) (is: Is doc shape): Is (Group doc hard) shape := is

theorem isIdGroup ∀ (id: Nat) (doc: Doc) (hard: Bool) (shape: List Told)
    (is: Is doc shape):
    Is (IdGroup id doc hard) shape :=
  is

theorem isFlatten ∀ (doc: Doc) (shape: List Told) (is: Is doc shape): Is (Flatten doc) shape := is

theorem isOneLineBelow ∀ (doc: Doc) (shape: List Told) (is: Is doc shape): Is (OneLineBelow doc) shape := spot =>
  is Spot.lineStart

theorem isIfBroken ∀ (id: Nat) (broken flat: Doc) (shape: List Told)
    (left: Is broken shape)
    (right: Is flat shape):
    Is (IfBroken id broken flat) shape :=
  spot => mergeRefines _ _ _ (left spot) (right spot)

def AllIs: List Doc → List Told → Prop
  | [], _ => True
  | [doc, ..docs], shape => Is doc shape ∧ AllIs docs shape

theorem optionsTell ∀ (first: Doc) (more: List Doc) (shape: List Told)
    (all: AllIs [first, ..more] shape) (spot: Spot):
    Refines (Doc.tellOptions [first, ..more] spot).said shape :=
  match more with
    | [] => (all.left spot)
    | [second, ..others] => mergeRefines _ _ _ (all.left spot) (optionsTell second others shape all.right spot)

theorem isChoice ∀ (first: Doc) (more: List Doc) (shape: List Told)
    (all: AllIs [first, ..more] shape):
    Is (Choice [first, ..more]) shape :=
  spot => optionsTell first more shape all spot

theorem isBreakParent: Is BreakParent [] := spot => byComputing
theorem isHardLine: Is HardLine [] := spot => byComputing
theorem isSoftLine: Is SoftLine [] := spot => byComputing
theorem isLine: Is Line [] := spot => byComputing
theorem isSpace: Is (Doc.text " ") [] := spot => byComputing

theorem isComma: Is (Closing ",") [Said "," True True] := spot =>
  rewrite pieceTell "," spot byComputing then
    wordTellingRefines "," spot True (never => (Bool.trueNotFalse never).impossible)
