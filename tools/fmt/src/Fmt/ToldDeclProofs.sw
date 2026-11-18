--| What the rules' documents tell of a whole declaration (SW-4050, F3 of SW-4042).
namespace Fmt.ToldDeclProofs
import Std (Bool, DecEq, Doc, Eq, List, Nat, Option, Text)
import Std.Doc (..)
import Std.Doc.Proofs (..)
import Syntax (Comments, Decl, DefBody, DefKind, Expr, Header, InfixKind, Note, SourceFile, Tok, Word)
import Fmt (..)
import Fmt.CalmProofs (bracketFrom, bracketIs, lambdaHugNone, matchedNone, plainDef, plainDefIs, valueElPlain)
import Fmt.SpellProofs (..)
import Fmt.ToldWordProofs (..)
import Fmt.TrailsProofs (Coded, trailsBackCoded)

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

-- Where the code before a closer ends with a comment.

--| Settled words, newest first, stay settled from any point on.
theorem homedSuffix ∀ (front back: List Word) (homed: homedBack (front ++ back) = True): homedBack back = True :=
  match front with
    | [] => homed
    | [word, ..rest] => homedSuffix rest back (Bool.andRight homed)

theorem codedSnoc ∀ (front: List Word) (last: Word)
    (code: isCloserText last.text = False):
    Coded (front ++ [last]) = True :=
  match front with
    | [] => rewrite code
    | [word, ..rest] =>
      match isCloserText word.text with
        | True => codedSnoc rest last code
        | False => byComputing

theorem closeBool ∀ (closer trails noted before: Bool)
    (cond: (!(closer && trails) || False || noted || before) = True):
    (!(closer && trails) || (!False && (noted || before))) = True :=
  match closer, trails, noted, before with
    | False, _, _, _ => byComputing
    | True, False, _, _ => byComputing
    | True, True, True, _ => byComputing
    | True, True, False, True => byComputing

--| A closer that holds a comment is homed when the code before it ends with one, or it has own-line comments: the
--| rules' `before` for it is what `homedBack` reads.
theorem closeHomes ∀ (close: Word) (xs prior: List Word) (around: Around)
    (code: Coded xs = True)
    (same: around.before = trailsBack xs)
    (unhoisted: around.hoisted = False)
    (homed: homedBack ([close, ..xs] ++ prior) = True):
    close.homes around = True :=
  match xs, code with
    | [first, ..more], code =>
      rewrite unhoisted, same then
        closeBool
          (isCloserText close.text)
          close.trails
          close.noted
          (trailsBack [first, ..more])
          (rewrite <- trailsBackCoded [first, ..more] prior code then Bool.andLeft homed)

-- What the tree's tokens are.

--| The tokens that are no brackets' closers: names and numerals, openers, operators.
def Expr.nonCloser: Expr → Bool
  | Atom _ word => !isCloserText word.text
  | Paren open inner _ => !isCloserText open.text && inner.nonCloser
  | Tuple open items _ _ => !isCloserText open.text && allNonCloser items
  | ListOf open items _ _ => !isCloserText open.text && allNonCloser items
  | App head arguments => head.nonCloser && allNonCloser arguments
  | Infix _ left operator right => left.nonCloser && !isCloserText operator.text && right.nonCloser
  | Prefix operator operand => !isCloserText operator.text && operand.nonCloser
  | _ => False

def allNonCloser: List Expr → Bool
  | [] => True
  | [expr, ..rest] => expr.nonCloser && allNonCloser rest

theorem leadNonCloser ∀ (expr: Expr) (nonCloser: expr.nonCloser = True): isCloserText expr.lead.text = False :=
  match expr with
    | Atom kind word => Bool.notTrue _ nonCloser
    | Paren open inner close => Bool.notTrue _ (Bool.andLeft nonCloser)
    | Tuple open items comma close => Bool.notTrue _ (Bool.andLeft nonCloser)
    | ListOf open items comma close => Bool.notTrue _ (Bool.andLeft nonCloser)
    | App head arguments => leadNonCloser head (Bool.andLeft nonCloser)
    | Infix kind left operator right => leadNonCloser left (Bool.andLeft nonCloser)
    | Prefix operator operand => Bool.notTrue _ (Bool.andLeft nonCloser)

--| An expression read back has a word that is no closer.
theorem codedOf ∀ (expr: Expr)
    (within: expr.within1 = True)
    (nonCloser: expr.nonCloser = True):
    Coded expr.words.reverse = True :=
  let (rest, words) := wordsLead expr within
  rewrite words, List.reverseCons expr.lead rest then codedSnoc rest.reverse expr.lead (leadNonCloser expr nonCloser)

-- Items.

--| What stands among the words before an item: its own words read back, then the earlier items'.
theorem itemsHomed ∀ (item: Expr) (rest: List Expr) (prior: List Word)
    (homed: homedBack ((itemsWords [item, ..rest]).reverse ++ prior) = True):
    homedBack (item.words.reverse ++ prior) = True
      ∧ homedBack ((itemsWords rest).reverse ++ (item.words.reverse ++ prior)) = True :=
  let split: (itemsWords [item, ..rest]).reverse ++ prior
    = (itemsWords rest).reverse ++ (item.words.reverse ++ prior) :=
    rewrite List.reverseAppend item.words (itemsWords rest),
        List.appendAssoc (itemsWords rest).reverse item.words.reverse prior
  let whole := rewrite split at homed then homed
  (homedSuffix (itemsWords rest).reverse (item.words.reverse ++ prior) whole, whole)

--| Every item of a list tells its shape, wherever it stands.
def ElShape (expr: Expr): Prop :=
  ∀ (around: Around) (prior: List Word) => expr.within1 = True
    → expr.sound = True
    → expr.nonCloser = True
    → homedBack (expr.words.reverse ++ prior) = True
    → Is (expr.el around) (expr.shape around.item around.hoisted)

def AllElShape: List Expr → Prop
  | [] => True
  | [expr, ..rest] => ElShape expr ∧ AllElShape rest

theorem isSeparator ∀ (first: Bool): Is (if first then SoftLine else Line) [] := match first with
  | True => isSoftLine
  | False => isLine

--| A broken bracket's lines tell its items, a bare comma after each but the last.
--|
--| Proof idea: Induction on the items, a separator before each.
theorem brokenItemsShape ∀ (bare arm first before: Bool) (at: Nat) (items: List Expr) (prior: List Word)
    (within: allWithin1 items = True)
    (sound: allSound items = True)
    (nonCloser: allNonCloser items = True)
    (each: AllElShape items)
    (homed: homedBack ((itemsWords items).reverse ++ prior) = True):
    IsAll (brokenItems bare arm first before at items) (itemsShape (!bare) items) :=
  match items, each with
    | [], _ => isNil
    | [item], (kept, _) =>
      let (head, _) := itemsHomed item [] prior homed
      isCons
        (if first then SoftLine else Line)
        [item.el (firstAround bare arm before at)]
        []
        (item.shape (!bare) False)
        (isSeparator first)
        (isLast
          (item.el (firstAround bare arm before at))
          (item.shape (!bare) False)
          (kept
            (firstAround bare arm before at)
            prior
            (Bool.andLeft within)
            (Bool.andLeft sound)
            (Bool.andLeft nonCloser)
            head))
    | [item, ..rest], (kept, others) =>
      let (head, tail) := itemsHomed item rest prior homed
      isCons
        (if first then SoftLine else Line)
        [
          item.el (firstAround bare arm before at),
          Closing ",",
          ..brokenItems False arm False False (at + item.size) rest
        ]
        []
        (item.shape (!bare) False ++ [Said "," True True] ++ itemsShape True rest)
        (isSeparator first)
        (isCons
          (item.el (firstAround bare arm before at))
          [Closing ",", ..brokenItems False arm False False (at + item.size) rest]
          (item.shape (!bare) False)
          ([Said "," True True] ++ itemsShape True rest)
          (kept
            (firstAround bare arm before at)
            prior
            (Bool.andLeft within)
            (Bool.andLeft sound)
            (Bool.andLeft nonCloser)
            head)
          (isCons
            (Closing ",")
            (brokenItems False arm False False (at + item.size) rest)
            [Said "," True True]
            (itemsShape True rest)
            isComma
            (brokenItemsShape False arm False False
              (at + item.size)
              rest
              (item.words.reverse ++ prior)
              (Bool.andRight within)
              (Bool.andRight sound)
              (Bool.andRight nonCloser)
              others
              tail)))

--| What each cell of a filled list tells: an item, a bare comma after each but the last.
def cellShapes (first: Bool): List Expr → List (List Told)
  | [] => []
  | [item] => [item.shape first False]
  | [item, ..rest] => [item.shape first False ++ [Said "," True True], ..cellShapes True rest]

theorem joinCells ∀ (first: Bool) (items: List Expr): joinShapes (cellShapes first items) = itemsShape first items :=
  match items with
    | [] => byComputing
    | [item] => List.appendNil (item.shape first False)
    | [item, ..rest] =>
      rewrite joinCells True rest then
        List.appendAssoc (item.shape first False) [Said "," True True] (itemsShape True rest)

--| A filled list's cells tell its items, a bare comma after each but the last.
theorem cellsShape ∀ (bare arm before: Bool) (at: Nat) (items: List Expr) (prior: List Word)
    (within: allWithin1 items = True)
    (sound: allSound items = True)
    (nonCloser: allNonCloser items = True)
    (each: AllElShape items)
    (homed: homedBack ((itemsWords items).reverse ++ prior) = True):
    IsEach (cells bare arm before at items) (cellShapes (!bare) items) :=
  match items, each with
    | [], _ => byComputing
    | [item], (kept, _) =>
      let (head, _) := itemsHomed item [] prior homed
      (
        kept
          (firstAround bare arm before at)
          prior
          (Bool.andLeft within)
          (Bool.andLeft sound)
          (Bool.andLeft nonCloser)
          head,
        byComputing
      )
    | [item, ..rest], (kept, others) =>
      let (head, tail) := itemsHomed item rest prior homed
      (
        isConcat
          [item.el (firstAround bare arm before at), Closing ","]
          (item.shape (!bare) False ++ [Said "," True True])
          (isCons
            (item.el (firstAround bare arm before at))
            [Closing ","]
            (item.shape (!bare) False)
            [Said "," True True]
            (kept
              (firstAround bare arm before at)
              prior
              (Bool.andLeft within)
              (Bool.andLeft sound)
              (Bool.andLeft nonCloser)
              head)
            (isLast (Closing ",") [Said "," True True] isComma)),
        cellsShape False arm False
          (at + item.size)
          rest
          (item.words.reverse ++ prior)
          (Bool.andRight within)
          (Bool.andRight sound)
          (Bool.andRight nonCloser)
          others
          tail
      )

--| A comma bracket's document tells its opener, its items and its closer.
--|
--| Proof idea: `bracketFrom`'s three layouts (none, filled, broken), each a concat of the opener, the items' lines and
--| the closer, with the items' shapes joined.
theorem bracketFromShape ∀ (list empty plain holds: Bool) (prefix closer: Doc) (filled broken: List Doc)
    (opens items closes: List Told) (shapes: List (List Told))
    (prefixIs: Is prefix opens)
    (closerIs: Is closer closes)
    (filledIs: IsEach filled shapes)
    (joined: joinShapes shapes = items)
    (brokenIs: IsAll broken items)
    (emptyItems: empty = True → items = []):
    Is (bracketFrom list empty plain holds prefix closer filled broken) (opens ++ items ++ closes) :=
  match empty with
    | True =>
      rewrite emptyItems byComputing then
        isConcat _ _ (isCons prefix [closer] opens closes prefixIs (isLast closer closes closerIs))
    | False =>
      match list && !holds && plain with
        | True =>
          isConcat
            [prefix, Nest 2 (Fill filled), closer] _
            (isCons prefix
              [Nest 2 (Fill filled), closer]
              opens
              (items ++ closes)
              prefixIs
              (isCons
                (Nest 2 (Fill filled))
                [closer]
                items
                closes
                (isNest 2 (Fill filled) items (rewrite <- joined then isFill filled shapes filledIs))
                (isLast closer closes closerIs)))
        | False =>
          match holds with
            | True =>
              isConcat _ _
                (isAllSame _ _ _
                  (isAppend
                    [prefix, Nest 2 (Doc.concat broken), SoftLine, closer]
                    [BreakParent]
                    (opens ++ items ++ closes)
                    []
                    (isCons prefix
                      [Nest 2 (Doc.concat broken), SoftLine, closer]
                      opens
                      (items ++ closes)
                      prefixIs
                      (isCons
                        (Nest 2 (Doc.concat broken))
                        [SoftLine, closer]
                        items
                        closes
                        (isNest 2 (Doc.concat broken) items (isConcat broken items brokenIs))
                        (isCons SoftLine [closer] [] closes isSoftLine (isLast closer closes closerIs))))
                    (isLast BreakParent [] isBreakParent))
                  (List.appendNil _))
            | False =>
              isConcat _ _
                (isCons prefix
                  [Nest 2 (Doc.concat broken), SoftLine, closer]
                  opens
                  (items ++ closes)
                  prefixIs
                  (isCons
                    (Nest 2 (Doc.concat broken))
                    [SoftLine, closer]
                    items
                    closes
                    (isNest 2 (Doc.concat broken) items (isConcat broken items brokenIs))
                    (isCons SoftLine [closer] [] closes isSoftLine (isLast closer closes closerIs))))

theorem bracketBack ∀ (open: Word) (items: List Expr) (close: Word):
    ([open, ..itemsWords items] ++ [close]).reverse = [close, ..((itemsWords items).reverse ++ [open])] :=
  rewrite List.reverseSnoc [open, ..itemsWords items] close, List.reverseCons open (itemsWords items)

theorem trailsBeforeCloseIs ∀ (open: Word) (items: List Expr) (close: Word):
    (ListOf open items False close).trailsBeforeClose = trailsBack ((itemsWords items).reverse ++ [open]) :=
  rewrite bracketBack open items close

--| A tuple or list's content tells its opener, its items with bare commas, and its closer.
--|
--| Proof idea: `bracketIs`, then `bracketFromShape` with the opener (`openingShape`), the closer (`leafShape`, homed
--| by `closeHomes`: what `homedBack` says of the closer is the code before it read back, which is the `before` the
--| rule passes), the cells (`cellsShape`) and the lines (`brokenItemsShape`).
theorem bracketContentShape ∀ (list: Bool) (open: Word) (items: List Expr) (close: Word)
    (around: Around) (prior: List Word)
    (within: allWithin1 items = True)
    (sound: allSound items = True)
    (nonCloser: allNonCloser items = True)
    (openSound: open.sound = True)
    (closeSound: close.sound = True)
    (opens: isCloserText open.text = False)
    (each: AllElShape items)
    (homed: homedBack (([open, ..itemsWords items] ++ [close]).reverse ++ prior) = True):
    Is
      (bracketContent list open items close around)
      (open.shapeK around.item around.hoisted
        ++ itemsShape (!(list && items.all Expr.plainItem)) items
        ++ close.shapeK False False) :=
  let inner: homedBack ((itemsWords items).reverse ++ ([open] ++ prior)) = True :=
    rewrite <- List.appendAssoc (itemsWords items).reverse [open] prior then
      homedSuffix [close] _ (rewrite bracketBack open items close at homed then homed)
  rewrite bracketIs list open items close around then
    bracketFromShape list items.isEmpty
      (items.all Expr.plainItem)
      (ListOf open items False close).holdsTrailingComment
      (open.opening around close)
      (close.leaf
        (around.next (ListOf open items False close).trailsBeforeClose ((ListOf open items False close).size - 1))
        around.at)
      (cells (list && items.all Expr.plainItem) around.inArm open.trails (around.at + 1) items)
      (brokenItems (list && items.all Expr.plainItem) around.inArm True open.trails (around.at + 1) items)
      (open.shapeK around.item around.hoisted)
      (itemsShape (!(list && items.all Expr.plainItem)) items)
      (close.shapeK False False)
      (cellShapes (!(list && items.all Expr.plainItem)) items)
      (spot => rewrite <- printedShape open around then openingShape open around close spot openSound opens)
      (spot =>
        leafShape close
          (around.next (ListOf open items False close).trailsBeforeClose ((ListOf open items False close).size - 1))
          around.at
          spot
          closeSound
          (closeHomes close
            ((itemsWords items).reverse ++ [open])
            prior
            (around.next (ListOf open items False close).trailsBeforeClose ((ListOf open items False close).size - 1))
            (codedSnoc (itemsWords items).reverse open opens)
            (trailsBeforeCloseIs open items close)
            byComputing
            (rewrite bracketBack open items close at homed then homed)))
      (cellsShape
        (list && items.all Expr.plainItem)
        around.inArm
        open.trails
        (around.at + 1)
        items
        ([open] ++ prior)
        within
        sound
        nonCloser
        each
        inner)
      (joinCells (!(list && items.all Expr.plainItem)) items)
      (brokenItemsShape
        (list && items.all Expr.plainItem)
        around.inArm
        True
        open.trails
        (around.at + 1)
        items
        ([open] ++ prior)
        within
        sound
        nonCloser
        each
        inner)
      (empty => match items, empty with | [], _ => byComputing)

-- Calls.

--| A token's own-line comments and kept blank line, as the document `Word.leading` writes them.
theorem leadingIs ∀ (word: Word) (around: Around) (key: Nat)
    (sound: word.sound = True):
    Is (Doc.concat (word.leading around key)) (word.toldLead around) :=
  spot =>
    rewrite concatTell (word.leading around key) spot, leadingTell word around key spot sound then
      refinesSelf _ (toldAboveExact (word.printed around).comments)

--| The own-line comments a frame writes, then the token hoisted, are the token's shape.
theorem toldLeadShape ∀ (word: Word) (around: Around):
    word.toldLead around ++ word.shapeK around.item True = word.shapeK around.item around.hoisted :=
  match around.hoisted with
    | True => byComputing
    | False => (shapeKLead word around.item).flipped

--| A hugged bracket and its hug tell the bracket's shape.
--|
--| Proof idea: the opener's own-line comments (`leadingIs`), then the bracket's content in a group
--| (`bracketContentShape`, with the opener hoisted); `toldLeadShape` puts the comments back on the opener.
theorem huggedBracketShape ∀ (list: Bool) (open: Word) (items: List Expr) (close: Word)
    (around: Around) (prior: List Word)
    (within: allWithin1 items = True)
    (sound: allSound items = True)
    (nonCloser: allNonCloser items = True)
    (openSound: open.sound = True)
    (closeSound: close.sound = True)
    (opens: isCloserText open.text = False)
    (each: AllElShape items)
    (homed: homedBack (([open, ..itemsWords items] ++ [close]).reverse ++ prior) = True):
    Is
      (huggedBracket list open items close around).fst
      (open.shapeK around.item around.hoisted
        ++ itemsShape (!(list && items.all Expr.plainItem)) items
        ++ close.shapeK False False)
      ∧ ∀ (hugged: Doc) => (huggedBracket list open items close around).snd = Some hugged
        → Is hugged
          (open.shapeK around.item around.hoisted
            ++ itemsShape (!(list && items.all Expr.plainItem)) items
            ++ close.shapeK False False) :=
  let content :=
    bracketContentShape list open items close
      { around | hoisted = True }
      prior
      within
      sound
      nonCloser
      openSound
      closeSound
      opens
      each
      homed
  let leading := leadingIs open around around.at openSound
  let moved: open.toldLead around
    ++ (open.shapeK around.item True
      ++ itemsShape (!(list && items.all Expr.plainItem)) items
      ++ close.shapeK False False)
    = open.shapeK around.item around.hoisted
      ++ itemsShape (!(list && items.all Expr.plainItem)) items
      ++ close.shapeK False False :=
    rewrite <- toldLeadShape open around,
        List.appendAssoc
          (open.toldLead around)
          (open.shapeK around.item True)
          (itemsShape (!(list && items.all Expr.plainItem)) items ++ close.shapeK False False)
  (
    isSame _ _ _
      (isConcat _ _
        (isCons _ _ _ _ leading
          (isLast _ _
            (isGroup
              (bracketContent list open items close { around | hoisted = True })
              (bracketContent list open items close { around | hoisted = True }).forcesBreak _
              content))))
      moved,
    hugged same =>
      rewrite <- Option.someInjective same then
        isSame _ _ _
          (isConcat _ _
            (isCons _ _ _ _ leading
              (isLast _ _ (isGroup (bracketContent list open items close { around | hoisted = True }) True _ content))))
          moved
  )

--| What a call's last argument and its hug tell.
def LastShape (last: (Doc, Option Doc)) (shape: List Told): Prop :=
  Is last.fst shape ∧ (∀ (hugged: Doc) => last.snd = Some hugged → Is hugged shape)

--| A call's last argument and its hug tell the argument's shape.
--|
--| Proof idea: Cases on the argument as `lastArgument` has them: a tuple or list hugs (`huggedBracketShape`), any
--| other is its element.
theorem lastArgumentShape ∀ (argument: Expr) (around: Around) (prior: List Word)
    (within: argument.within1 = True)
    (sound: argument.sound = True)
    (nonCloser: argument.nonCloser = True)
    (each: ElShape argument)
    (homed: homedBack (argument.words.reverse ++ prior) = True):
    LastShape (lastArgument argument around) (argument.shape around.item around.hoisted) :=
  match argument with
    | Tuple open items comma close =>
      huggedBracketShape False open items close around prior within
        (Bool.andLeft (Bool.andRight sound))
        (Bool.andRight nonCloser)
        (Bool.andLeft sound)
        (Bool.andRight (Bool.andRight sound))
        (Bool.notTrue _ (Bool.andLeft nonCloser))
        (allElShape items within (Bool.andLeft (Bool.andRight sound)) (Bool.andRight nonCloser))
        homed
    | ListOf open items comma close =>
      huggedBracketShape True open items close around prior within
        (Bool.andLeft (Bool.andRight sound))
        (Bool.andRight nonCloser)
        (Bool.andLeft sound)
        (Bool.andRight (Bool.andRight sound))
        (Bool.notTrue _ (Bool.andLeft nonCloser))
        (allElShape items within (Bool.andLeft (Bool.andRight sound)) (Bool.andRight nonCloser))
        homed
    | Paren open inner close =>
      match inner with
        | Binding _ _ _ _ _ => cases
        | Block _ _ _ => cases
        | _ => (each around prior within sound nonCloser homed, (hugged same => cases))
    | Record _ _ _ _ _ => cases
    | _ => (each around prior within sound nonCloser homed, (hugged same => cases))

def LastOpt: Option (Doc, Option Doc) → List Told → Prop
  | None, shape => shape = []
  | Some last, shape => LastShape last shape

--| What `argumentDocs` makes of arguments tells: the documents before the last, each its shape, and the last.
def ArgsShape (made: (List Doc, Option (Doc, Option Doc))) (front: List (List Told)) (last: List Told): Prop :=
  IsEach made.fst front ∧ LastOpt made.snd last

theorem argsShapeEq ∀ (made made': (List Doc, Option (Doc, Option Doc))) (front: List (List Told)) (last: List Told)
    (same: made = made')
    (shape: ArgsShape made' front last):
    ArgsShape made front last :=
  rewrite same then shape

--| A call's arguments tell their shapes, split into the documents before the last and the last.
--|
--| Proof idea: Induction on the arguments; each stands after the one before.
theorem argumentDocsShape ∀ (arm: Bool) (previous: Expr) (at: Nat) (arguments: List Expr) (prior: List Word)
    (within: allWithin1 arguments = True)
    (sound: allSound arguments = True)
    (nonCloser: allNonCloser arguments = True)
    (each: AllElShape arguments)
    (homed: homedBack ((itemsWords arguments).reverse ++ prior) = True):
    ∃ (front: List (List Told)) (last: List Told) => ArgsShape (argumentDocs arm previous at arguments) front last
      ∧ joinShapes front ++ last = argumentsShape arguments :=
  match arguments, each with
    | [], _ => ([], [], (byComputing, byComputing), byComputing)
    | [argument], (kept, _) =>
      let (head, _) := itemsHomed argument [] prior homed
      (
        [],
        argument.shape False False,
        (
          byComputing,
          lastArgumentShape argument
            { before = previous.trails, hoisted = False, item = False, at, inArm = arm }
            prior
            (Bool.andLeft within)
            (Bool.andLeft sound)
            (Bool.andLeft nonCloser)
            kept
            head
        ),
        (List.appendNil (argument.shape False False)).flipped
      )
    | [argument, next, ..more], (kept, others) =>
      let (head, tail) := itemsHomed argument [next, ..more] prior homed
      let (front, last, (docsShape, lastShape), joined) :=
        argumentDocsShape arm argument
          (at + argument.size)
          [next, ..more]
          (argument.words.reverse ++ prior)
          (Bool.andRight within)
          (Bool.andRight sound)
          (Bool.andRight nonCloser)
          others
          tail
      (
        [argument.shape False False, ..front],
        last,
        (argsShapeEq _ _ _ _ (argumentDocsConsTest arm previous argument next at more) (
          (
            kept
              { before = previous.trails, hoisted = False, item = False, at, inArm = arm }
              prior
              (Bool.andLeft within)
              (Bool.andLeft sound)
              (Bool.andLeft nonCloser)
              head,
            docsShape
          ),
          lastShape
        )),
        rewrite <- joined then List.appendAssoc (argument.shape False False) (joinShapes front) last
      )

theorem allElShape ∀ (items: List Expr)
    (within: allWithin1 items = True)
    (sound: allSound items = True)
    (nonCloser: allNonCloser items = True):
    AllElShape items :=
  match items with
    | [] => byComputing
    | [first, ..rest] => (
      around prior w s n h => elShape first around prior w s n h,
      allElShape rest (Bool.andRight within) (Bool.andRight sound) (Bool.andRight nonCloser)
    )

theorem eachTake ∀ (docs: List Doc) (shapes: List (List Told)) (count: Nat)
    (each: IsEach docs shapes):
    IsEach (docs.take count) (shapes.take count) :=
  match docs, shapes, count with
    | [], [], Zero => byComputing
    | [], [], Succ less => byComputing
    | [doc, ..more], [shape, ..rest], Zero => byComputing
    | [doc, ..more], [shape, ..rest], Succ less =>
      let (head, tail) := each
      (head, eachTake more rest less tail)

theorem eachDrop ∀ (docs: List Doc) (shapes: List (List Told)) (count: Nat)
    (each: IsEach docs shapes):
    IsEach (docs.drop count) (shapes.drop count) :=
  match docs, shapes, count with
    | [], [], Zero => byComputing
    | [], [], Succ less => byComputing
    | [doc, ..more], [shape, ..rest], Zero => each
    | [doc, ..more], [shape, ..rest], Succ less =>
      let (head, tail) := each
      eachDrop more rest less tail

theorem takeDropJoin ∀ (shapes: List (List Told)) (count: Nat):
    joinShapes (shapes.take count) ++ joinShapes (shapes.drop count) = joinShapes shapes :=
  match shapes, count with
    | [], Zero => byComputing
    | [], Succ less => byComputing
    | [shape, ..rest], Zero => byComputing
    | [shape, ..rest], Succ less =>
      rewrite List.appendAssoc shape (joinShapes (rest.take less)) (joinShapes (rest.drop less)), takeDropJoin rest less

theorem joinedAll ∀ (docs: List Doc) (shapes: List (List Told))
    (each: IsEach docs shapes):
    IsAll (Doc.joinedWith (Doc.text " ") docs) (joinShapes shapes) :=
  match docs, shapes with
    | [], [] => isNil
    | [only], [shape] => isAllSame _ _ _ (isLast only shape each.left) (List.appendNil shape).flipped
    | [only], [first, second, ..rest] => cases
    | [doc, next, ..more], [shape] => cases
    | [doc, next, ..more], [shape, second, ..rest] =>
      let (head, tail) := each
      isCons doc
        [Doc.text " ", ..Doc.joinedWith (Doc.text " ") [next, ..more]]
        shape
        (joinShapes [second, ..rest])
        head
        (isCons
          (Doc.text " ")
          (Doc.joinedWith (Doc.text " ") [next, ..more])
          []
          (joinShapes [second, ..rest])
          isSpace
          (joinedAll [next, ..more] [second, ..rest] tail))

theorem isSpaced ∀ (docs: List Doc) (shapes: List (List Told))
    (each: IsEach docs shapes):
    Is (spaced docs) (joinShapes shapes) :=
  isConcat _ _ (joinedAll docs shapes each)

theorem concatMapAll ∀ (docs: List Doc) (shapes: List (List Told))
    (each: IsEach docs shapes):
    IsAll (docs.concatMap (doc => [HardLine, doc])) (joinShapes shapes) :=
  match docs, shapes with
    | [], [] => isNil
    | [doc, ..more], [shape, ..rest] =>
      let (head, tail) := each
      isCons HardLine
        [doc, ..more.concatMap (doc => [HardLine, doc])]
        []
        (shape ++ joinShapes rest)
        isHardLine
        (isCons doc
          (more.concatMap (doc => [HardLine, doc]))
          shape
          (joinShapes rest)
          head
          (concatMapAll more rest tail))

--| A call that breaks keeps some elements on its line and the rest each on a line of its own: the shape is the
--| elements'.
theorem frontRestShape ∀ (id keep: Nat) (fillFront: Bool) (docs: List Doc) (shapes: List (List Told))
    (each: IsEach docs shapes):
    Is
      (Doc.concat [
        if fillFront then IdGroup id (Nest 4 (Fill (docs.take keep))) False else spaced (docs.take keep),
        if fillFront then
          IfBroken id
            (Nest 4 (Doc.concat (docs.drop keep |> .concatMap (doc => [HardLine, doc]))))
            (Nest 2 (Doc.concat (docs.drop keep |> .concatMap (doc => [HardLine, doc]))))
        else Nest 2 (Doc.concat (docs.drop keep |> .concatMap (doc => [HardLine, doc])))
      ])
      (joinShapes shapes) :=
  let kept := eachTake docs shapes keep each
  let rest := isConcat _ _ (concatMapAll (docs.drop keep) (shapes.drop keep) (eachDrop docs shapes keep each))
  rewrite <- takeDropJoin shapes keep then
    isConcat _ _
      (isCons
        (if fillFront then IdGroup id (Nest 4 (Fill (docs.take keep))) False else spaced (docs.take keep))
        [
          if fillFront then
            IfBroken id
              (Nest 4 (Doc.concat (docs.drop keep |> .concatMap (doc => [HardLine, doc]))))
              (Nest 2 (Doc.concat (docs.drop keep |> .concatMap (doc => [HardLine, doc]))))
          else Nest 2 (Doc.concat (docs.drop keep |> .concatMap (doc => [HardLine, doc])))
        ]
        (joinShapes (shapes.take keep))
        (joinShapes (shapes.drop keep))
        (match fillFront with
          | True => isIdGroup id (Nest 4 (Fill (docs.take keep))) False _ (isNest 4 _ _ (isFill _ _ kept))
          | False => isSpaced (docs.take keep) (shapes.take keep) kept)
        (isLast
          (if fillFront then
             IfBroken id
               (Nest 4 (Doc.concat (docs.drop keep |> .concatMap (doc => [HardLine, doc]))))
               (Nest 2 (Doc.concat (docs.drop keep |> .concatMap (doc => [HardLine, doc]))))
           else Nest 2 (Doc.concat (docs.drop keep |> .concatMap (doc => [HardLine, doc]))))
          (joinShapes (shapes.drop keep))
          (match fillFront with
            | True => isIfBroken id _ _ _ (isNest 4 _ _ rest) (isNest 2 _ _ rest)
            | False => isNest 2 _ _ rest)))

theorem eachSnoc ∀ (docs: List Doc) (shapes: List (List Told)) (last: Doc) (shape: List Told)
    (each: IsEach docs shapes)
    (is: Is last shape):
    IsEach (docs ++ [last]) (shapes ++ [shape]) :=
  match docs, shapes with
    | [], [] => (is, byComputing)
    | [doc, ..more], [first, ..rest] =>
      let (head, tail) := each
      (head, eachSnoc more rest last shape tail is)

theorem joinSnoc ∀ (shapes: List (List Told)) (shape: List Told):
    joinShapes (shapes ++ [shape]) = joinShapes shapes ++ shape :=
  match shapes with
    | [] => List.appendNil shape
    | [first, ..rest] => rewrite joinSnoc rest shape then (List.appendAssoc first (joinShapes rest) shape).flipped

--| What a call's pieces tell, and what its hug tells.
def AppShape (applied: Applied) (shape: List Told): Prop :=
  Is applied.doc shape ∧ (∀ (hugged: Doc) => applied.hug = Some hugged → Is hugged shape)

--| A call's document and its hug tell the function and its arguments.
--|
--| Proof idea: Cases on whether every element stays on its line; else each option of the choice (flat, hugged if the
--| last argument hugs, the front and the rest) tells the same shape (`isChoice`).
theorem appFromShape ∀ (id keep: Nat) (between betweenFront: Bool) (headDoc lastDoc: Doc) (front: List Doc)
    (hug: Option Doc) (headShape lastShape: List Told) (frontShapes: List (List Told))
    (headIs: Is headDoc headShape)
    (frontEach: IsEach front frontShapes)
    (lastIs: Is lastDoc lastShape)
    (hugIs: ∀ (hugged: Doc) => hug = Some hugged → Is hugged lastShape):
    AppShape
      (appFrom id keep between betweenFront headDoc front lastDoc hug)
      (headShape ++ joinShapes frontShapes ++ lastShape) :=
  let each: IsEach ([headDoc, ..front] ++ [lastDoc]) ([headShape, ..frontShapes] ++ [lastShape]) :=
    eachSnoc [headDoc, ..front] [headShape, ..frontShapes] lastDoc lastShape (headIs, frontEach) lastIs
  let joined: joinShapes ([headShape, ..frontShapes] ++ [lastShape])
    = headShape ++ joinShapes frontShapes ++ lastShape :=
    rewrite joinSnoc [headShape, ..frontShapes] lastShape, List.appendAssoc headShape (joinShapes frontShapes) lastShape
  rewrite <- joined then
    match keep == ([headDoc, ..front] ++ [lastDoc]).length with
      | True => (
        (match between with
          | True => isSpaced ([headDoc, ..front] ++ [lastDoc]) ([headShape, ..frontShapes] ++ [lastShape]) each
          | False =>
            isNest 4
              (Fill ([headDoc, ..front] ++ [lastDoc])) _
              (isFill ([headDoc, ..front] ++ [lastDoc]) ([headShape, ..frontShapes] ++ [lastShape]) each)),
        (hugged none => cases)
      )
      | False =>
        let third :=
          frontRestShape id keep
            (keep > 2 && !betweenFront)
            ([headDoc, ..front] ++ [lastDoc])
            ([headShape, ..frontShapes] ++ [lastShape])
            each
        let all :=
          isFlatten _ _ (isSpaced ([headDoc, ..front] ++ [lastDoc]) ([headShape, ..frontShapes] ++ [lastShape]) each)
        match hug with
          | None => (
            isChoice
              (Flatten (spaced ([headDoc, ..front] ++ [lastDoc])))
              [
                Doc.concat [
                  if keep > 2 && !betweenFront then
                    IdGroup id (Nest 4 (Fill (([headDoc, ..front] ++ [lastDoc]).take keep))) False
                  else spaced (([headDoc, ..front] ++ [lastDoc]).take keep),
                  if keep > 2 && !betweenFront then
                    IfBroken id
                      (Nest 4
                        (Doc.concat
                          (([headDoc, ..front] ++ [lastDoc]).drop keep |> .concatMap (doc => [HardLine, doc]))))
                      (Nest 2
                        (Doc.concat
                          (([headDoc, ..front] ++ [lastDoc]).drop keep |> .concatMap (doc => [HardLine, doc]))))
                  else
                    Nest 2
                      (Doc.concat (([headDoc, ..front] ++ [lastDoc]).drop keep |> .concatMap (doc => [HardLine, doc])))
                ]
              ]
              (joinShapes ([headShape, ..frontShapes] ++ [lastShape]))
              (all, (third, byComputing)),
            (hugged same => cases)
          )
          | Some opened =>
            let huggedIs: Is
              (Doc.concat [Flatten (spaced [headDoc, ..front]), Doc.text " ", opened])
              (joinShapes ([headShape, ..frontShapes] ++ [lastShape])) :=
              isConcat _ _
                (isAllSame _ _ _
                  (isCons
                    (Flatten (spaced [headDoc, ..front]))
                    [Doc.text " ", opened]
                    (headShape ++ joinShapes frontShapes)
                    ([] ++ lastShape)
                    (isFlatten _ _ (isSpaced [headDoc, ..front] [headShape, ..frontShapes] (headIs, frontEach)))
                    (isCons
                      (Doc.text " ")
                      [opened]
                      []
                      lastShape
                      isSpace
                      (isLast opened lastShape (hugIs opened byComputing))))
                  (rewrite joinSnoc [headShape, ..frontShapes] lastShape))
            (
              isChoice
                (Flatten (spaced ([headDoc, ..front] ++ [lastDoc])))
                [
                  Doc.concat [Flatten (spaced [headDoc, ..front]), Doc.text " ", opened],
                  Doc.concat [
                    if keep > 2 && !betweenFront then
                      IdGroup id (Nest 4 (Fill (([headDoc, ..front] ++ [lastDoc]).take keep))) False
                    else spaced (([headDoc, ..front] ++ [lastDoc]).take keep),
                    if keep > 2 && !betweenFront then
                      IfBroken id
                        (Nest 4
                          (Doc.concat
                            (([headDoc, ..front] ++ [lastDoc]).drop keep |> .concatMap (doc => [HardLine, doc]))))
                        (Nest 2
                          (Doc.concat
                            (([headDoc, ..front] ++ [lastDoc]).drop keep |> .concatMap (doc => [HardLine, doc]))))
                    else
                      Nest 2
                        (Doc.concat
                          (([headDoc, ..front] ++ [lastDoc]).drop keep |> .concatMap (doc => [HardLine, doc])))
                  ]
                ]
                (joinShapes ([headShape, ..frontShapes] ++ [lastShape]))
                (all, (huggedIs, (third, byComputing))),
              (hugged same => rewrite <- Option.someInjective same then huggedIs)
            )

theorem pickShape ∀ (option: Option (Doc, Option Doc)) (shape: List Told)
    (last: LastOpt option shape):
    LastShape (option.getOrElse (Nothing, None)) shape :=
  match option, last with
    | None, same => (rewrite same then (spot => byComputing), (hugged same => cases))
    | Some pair, shape => shape

--| A call tells its function and its arguments.
--|
--| Proof idea: `appDocsIs` (the facts `appDocs` reads, as projections) and `appFromShape`, with the arguments' shapes
--| from `argumentDocsShape`; the function stands where the call does, each argument after the words before it.
theorem appDocsShape ∀ (head: Expr) (arguments: List Expr) (around: Around) (prior: List Word)
    (headWithin: head.within1 = True)
    (headSound: head.sound = True)
    (headNonCloser: head.nonCloser = True)
    (eachHead: ElShape head)
    (within: allWithin1 arguments = True)
    (sound: allSound arguments = True)
    (nonCloser: allNonCloser arguments = True)
    (each: AllElShape arguments)
    (homed: homedBack ((head.words ++ itemsWords arguments).reverse ++ prior) = True):
    AppShape (appDocs head arguments around) (head.shape around.item around.hoisted ++ argumentsShape arguments) :=
  let split: (head.words ++ itemsWords arguments).reverse ++ prior
    = (itemsWords arguments).reverse ++ (head.words.reverse ++ prior) :=
    rewrite List.reverseAppend head.words (itemsWords arguments),
        List.appendAssoc (itemsWords arguments).reverse head.words.reverse prior
  let whole := rewrite split at homed then homed
  let (front, last, (frontIs, lastIs), joined) :=
    argumentDocsShape around.inArm head
      (around.at + head.size)
      arguments
      (head.words.reverse ++ prior)
      within
      sound
      nonCloser
      each
      whole
  let picked := pickShape (argumentDocs around.inArm head (around.at + head.size) arguments).snd last lastIs
  rewrite <- joined, appDocsIs head arguments around then
    appFromShape
      (around.at + 1)
      (1 + keptFront head arguments)
      (commentBetween head arguments)
      (commentBetween head (arguments.take (1 + keptFront head arguments - 1)))
      (head.el around)
      ((argumentDocs around.inArm head (around.at + head.size) arguments).snd.getOrElse (Nothing, None)).fst
      (argumentDocs around.inArm head (around.at + head.size) arguments).fst
      ((argumentDocs around.inArm head (around.at + head.size) arguments).snd.getOrElse (Nothing, None)).snd
      (head.shape around.item around.hoisted)
      last
      front
      (eachHead around prior headWithin headSound headNonCloser
        (homedSuffix (itemsWords arguments).reverse (head.words.reverse ++ prior) whole))
      frontIs
      picked.left
      picked.right

-- Chains.

theorem concatTailSaid ∀ (head: Doc) (indent: Nat) (tail: List Doc) (spot: Spot):
    (Doc.tellAll [head, Nest indent (Doc.concat tail)] spot).said = (Doc.tellAll [head, ..tail] spot).said :=
  rewrite concatTell tail (head.tell spot).after, List.appendNil (Doc.tellAll tail (head.tell spot).after).said

--| A chain's lines, grouped, tell what the lines do.
theorem chainOfShape ∀ (arms: Bool) (links: List Doc) (shape: List Told)
    (all: IsAll links shape):
    Is (chainOf arms links) shape :=
  match links, all with
    | [], all => spot => all spot
    | [head, ..tail], all =>
      isGroup
        (Doc.concat [head, Nest (if arms then 0 else 2) (Doc.concat tail)])
        (Doc.concat [head, Nest (if arms then 0 else 2) (Doc.concat tail)]).forcesBreak _
        (isConcat _ _ (spot => rewrite concatTailSaid head (if arms then 0 else 2) tail spot then all spot))

theorem chainRightShape ∀ (level: Option Nat) (right: Expr) (around: Around)
    (within: right.within1 = True)
    (link: IsAll (linkDocs level False right around) (right.shape around.item around.hoisted)):
    IsAll (chainRight level right around) (right.shape around.item around.hoisted) :=
  match right with
    | Block _ _ _ => cases
    | _ =>
      isCons (Doc.text " ") (linkDocs level False right around) [] (right.shape around.item around.hoisted) isSpace link

theorem infixHomed ∀ (left: Expr) (operator: Word) (right: Expr) (prior: List Word)
    (homed: homedBack ((left.words ++ [operator, ..right.words]).reverse ++ prior) = True):
    homedBack (left.words.reverse ++ prior) = True
      ∧ homedBack (right.words.reverse ++ ([operator] ++ (left.words.reverse ++ prior))) = True :=
  let split: (left.words ++ [operator, ..right.words]).reverse ++ prior
    = right.words.reverse ++ ([operator] ++ (left.words.reverse ++ prior)) :=
    rewrite List.reverseAppend left.words [operator, ..right.words],
        List.reverseCons operator right.words,
        List.appendAssoc (right.words.reverse ++ [operator]) left.words.reverse prior,
        List.appendAssoc right.words.reverse [operator] (left.words.reverse ++ prior)
  let whole := rewrite split at homed then homed
  (
    homedSuffix
      (right.words.reverse ++ [operator])
      (left.words.reverse ++ prior)
      (rewrite List.appendAssoc right.words.reverse [operator] (left.words.reverse ++ prior) then whole),
    whole
  )

--| A chain's lines tell the first operand, the operator and the last operand.
--|
--| Proof idea: The first operand's lines (`linkDocsShape`), a `Line`, the operator's leaf and what follows it
--| (`chainRightShape`).
theorem chainLinksShape ∀ (level: Option Nat) (first: Bool) (left: Expr) (operator: Word) (right: Expr)
    (around: Around) (prior: List Word)
    (leftWithin: left.within1 = True)
    (rightWithin: right.within1 = True)
    (leftSound: left.sound = True)
    (operatorSound: operator.sound = True)
    (rightSound: right.sound = True)
    (leftNonCloser: left.nonCloser = True)
    (operatorOpens: isCloserText operator.text = False)
    (rightNonCloser: right.nonCloser = True)
    (homed: homedBack ((left.words ++ [operator, ..right.words]).reverse ++ prior) = True):
    IsAll
      (chainLinks level first left operator right around)
      (left.shape around.item around.hoisted ++ operator.shapeK False False ++ right.shape False False) :=
  let (leftHomed, rightHomed) := infixHomed left operator right prior homed
  isAppend
    (linkDocs level first left around)
    [
      Line,
      operator.leaf (around.next left.trails left.size) (around.next left.trails left.size).at,
      ..chainRight level right (around.next operator.trails (left.size + 1))
    ]
    (left.shape around.item around.hoisted)
    (operator.shapeK False False ++ right.shape False False)
    (linkDocsShape level first left around prior leftWithin leftSound leftNonCloser leftHomed)
    (isCons Line
      [
        operator.leaf (around.next left.trails left.size) (around.next left.trails left.size).at,
        ..chainRight level right (around.next operator.trails (left.size + 1))
      ]
      []
      (operator.shapeK False False ++ right.shape False False)
      isLine
      (isCons
        (operator.leaf (around.next left.trails left.size) (around.next left.trails left.size).at)
        (chainRight level right (around.next operator.trails (left.size + 1)))
        (operator.shapeK False False)
        (right.shape False False)
        (spot =>
          rewrite <- printedShape operator (around.next left.trails left.size) then
            leafShape operator
              (around.next left.trails left.size)
              (around.next left.trails left.size).at
              spot
              operatorSound
              (homesOpen operator (around.next left.trails left.size) operatorOpens))
        (chainRightShape level right
          (around.next operator.trails (left.size + 1))
          rightWithin
          (linkDocsShape level False right
            (around.next operator.trails (left.size + 1))
            ([operator] ++ (left.words.reverse ++ prior))
            rightWithin
            rightSound
            rightNonCloser
            rightHomed))))

--| A chain operand's documents tell what the operand does.
--|
--| Proof idea: A chain of the level is its links, any other operand its element, as in `linkDocsSpells`.
theorem linkDocsShape ∀ (level: Option Nat) (first: Bool) (expr: Expr) (around: Around) (prior: List Word)
    (within: expr.within1 = True)
    (sound: expr.sound = True)
    (nonCloser: expr.nonCloser = True)
    (homed: homedBack (expr.words.reverse ++ prior) = True):
    IsAll (linkDocs level first expr around) (expr.shape around.item around.hoisted) :=
  match expr with
    | Infix kind left operator right =>
      match kind with
        | InfixBinary =>
          match (Infix InfixBinary left operator right).inChain level with
            | True =>
              chainLinksShape level first left operator right around prior
                (Bool.andLeft within)
                (Bool.andLeft (Bool.andRight within))
                (Bool.andLeft sound)
                (Bool.andLeft (Bool.andRight sound))
                (Bool.andRight (Bool.andRight sound))
                (Bool.andLeft nonCloser)
                (Bool.notTrue _ (Bool.andLeft (Bool.andRight nonCloser)))
                (Bool.andRight (Bool.andRight nonCloser))
                homed
            | False =>
              isLast
                ((Infix InfixBinary left operator right).el around)
                ((Infix InfixBinary left operator right).shape around.item around.hoisted)
                (elShape (Infix InfixBinary left operator right) around prior within sound nonCloser homed)
        | InfixArrow =>
          match (Infix InfixArrow left operator right).inChain level with
            | True =>
              chainLinksShape level first left operator right around prior
                (Bool.andLeft within)
                (Bool.andLeft (Bool.andRight within))
                (Bool.andLeft sound)
                (Bool.andLeft (Bool.andRight sound))
                (Bool.andRight (Bool.andRight sound))
                (Bool.andLeft nonCloser)
                (Bool.notTrue _ (Bool.andLeft (Bool.andRight nonCloser)))
                (Bool.andRight (Bool.andRight nonCloser))
                homed
            | False =>
              isLast
                ((Infix InfixArrow left operator right).el around)
                ((Infix InfixArrow left operator right).shape around.item around.hoisted)
                (elShape (Infix InfixArrow left operator right) around prior within sound nonCloser homed)
        | _ => cases
    | Match _ _ _ _ => cases
    | _ =>
      isLast
        (expr.el around)
        (expr.shape around.item around.hoisted)
        (elShape expr around prior within sound nonCloser homed)

-- Elements.

theorem bracketBackWords ∀ (open: Word) (middle: List Word) (close: Word):
    ([open, ..middle] ++ [close]).reverse = [close, ..(middle.reverse ++ [open])] :=
  rewrite List.reverseSnoc [open, ..middle] close, List.reverseCons open middle

--| What stands before a bracket's inside and its closer, from what stands before the bracket.
theorem bracketHomed ∀ (open: Word) (middle: List Word) (close: Word) (prior: List Word)
    (homed: homedBack (([open, ..middle] ++ [close]).reverse ++ prior) = True):
    homedBack (middle.reverse ++ ([open] ++ prior)) = True :=
  rewrite <- List.appendAssoc middle.reverse [open] prior then
    homedSuffix [close] _ (rewrite bracketBackWords open middle close at homed then homed)

--| The rules print an expression telling its shape, wherever it stands.
--|
--| Proof idea: Induction on the expression, as `elSpells`: a token by `leafShape`, a node by its rule's lemma inside
--| `framedShape`; every closer is homed by what `homedBack` says of the code before it.
theorem elShape ∀ (expr: Expr) (around: Around) (prior: List Word)
    (within: expr.within1 = True)
    (sound: expr.sound = True)
    (nonCloser: expr.nonCloser = True)
    (homed: homedBack (expr.words.reverse ++ prior) = True):
    Is (expr.el around) (expr.shape around.item around.hoisted) :=
  match expr with
    | Atom kind word => spot =>
      rewrite <- printedShape word around then
        leafShape word around around.at spot sound (homesOpen word around (Bool.notTrue _ nonCloser))
    | Paren open inner close =>
      framedShape
        (Paren open inner close)
        around
        (parenDoc open inner close { around | hoisted = True })
        within
        (leadSound (Paren open inner close) sound)
        (parenShape open inner close
          { around | hoisted = True }
          (Bool.andLeft sound)
          (Bool.andRight (Bool.andRight sound))
          (Bool.notTrue _ (Bool.andLeft nonCloser))
          (closeHomes close
            (inner.words.reverse ++ [open])
            prior
            ({ around | hoisted = True }.next inner.trails (1 + inner.size))
            (codedSnoc inner.words.reverse open (Bool.notTrue _ (Bool.andLeft nonCloser)))
            (trailsBackCoded inner.words.reverse [open] (codedOf inner within (Bool.andRight nonCloser))).flipped
            byComputing
            (rewrite bracketBackWords open inner.words close at homed then homed))
          (elShape inner
            ({ around | hoisted = True }.next open.trails 1)
            ([open] ++ prior)
            within
            (Bool.andLeft (Bool.andRight sound))
            (Bool.andRight nonCloser)
            (bracketHomed open inner.words close prior homed)))
    | Tuple open items comma close =>
      framedShape
        (Tuple open items comma close)
        around
        (commaBracket (list := False) open items close { around | hoisted = True })
        within
        (leadSound (Tuple open items comma close) sound)
        (isGroup
          (bracketContent False open items close { around | hoisted = True })
          (bracketContent False open items close { around | hoisted = True }).forcesBreak _
          (bracketContentShape False open items close
            { around | hoisted = True }
            prior
            within
            (Bool.andLeft (Bool.andRight sound))
            (Bool.andRight nonCloser)
            (Bool.andLeft sound)
            (Bool.andRight (Bool.andRight sound))
            (Bool.notTrue _ (Bool.andLeft nonCloser))
            (allElShape items within (Bool.andLeft (Bool.andRight sound)) (Bool.andRight nonCloser))
            homed))
    | ListOf open items comma close =>
      framedShape
        (ListOf open items comma close)
        around
        (commaBracket (list := True) open items close { around | hoisted = True })
        within
        (leadSound (ListOf open items comma close) sound)
        (isGroup
          (bracketContent True open items close { around | hoisted = True })
          (bracketContent True open items close { around | hoisted = True }).forcesBreak _
          (bracketContentShape True open items close
            { around | hoisted = True }
            prior
            within
            (Bool.andLeft (Bool.andRight sound))
            (Bool.andRight nonCloser)
            (Bool.andLeft sound)
            (Bool.andRight (Bool.andRight sound))
            (Bool.notTrue _ (Bool.andLeft nonCloser))
            (allElShape items within (Bool.andLeft (Bool.andRight sound)) (Bool.andRight nonCloser))
            homed))
    | App head arguments =>
      framedShape
        (App head arguments)
        around
        (appDocs head arguments { around | hoisted = True }).doc
        within
        (leadSound (App head arguments) sound)
        (appDocsShape head arguments
          { around | hoisted = True }
          prior
          (Bool.andLeft within)
          (Bool.andLeft sound)
          (Bool.andLeft nonCloser)
          (around prior w s n h => elShape head around prior w s n h)
          (Bool.andRight within)
          (Bool.andRight sound)
          (Bool.andRight nonCloser)
          (allElShape arguments (Bool.andRight within) (Bool.andRight sound) (Bool.andRight nonCloser))
          homed).left
    | Prefix operator operand =>
      framedShape
        (Prefix operator operand)
        around
        (Doc.concat [
          operator.leaf { around | hoisted = True } around.at,
          prefixGap operator operand,
          operand.el (around.next operator.trails 1)
        ])
        within
        (leadSound (Prefix operator operand) sound)
        (prefixShape operator operand around
          (Bool.andLeft sound)
          (Bool.notTrue _ (Bool.andLeft nonCloser))
          (elShape operand
            (around.next operator.trails 1)
            ([operator] ++ prior)
            (Bool.andLeft within)
            (Bool.andRight sound)
            (Bool.andRight nonCloser)
            (rewrite <- List.appendAssoc operand.words.reverse [operator] prior then
              rewrite List.reverseCons operator operand.words at homed then homed)))
    | Infix kind left operator right =>
      match kind with
        | InfixBinary =>
          framedShape
            (Infix InfixBinary left operator right)
            around
            (chain (Infix InfixBinary left operator right).chainLevel left operator right { around | hoisted = True })
            within
            (leadSound (Infix InfixBinary left operator right) sound)
            (chainOfShape
              (left.opensArms (Infix InfixBinary left operator right).chainLevel)
              (chainLinks (Infix InfixBinary left operator right).chainLevel True left operator right { around |
                hoisted = True
              }) _
              (chainLinksShape
                (Infix InfixBinary left operator right).chainLevel
                True
                left
                operator
                right
                { around | hoisted = True }
                prior
                (Bool.andLeft within)
                (Bool.andLeft (Bool.andRight within))
                (Bool.andLeft sound)
                (Bool.andLeft (Bool.andRight sound))
                (Bool.andRight (Bool.andRight sound))
                (Bool.andLeft nonCloser)
                (Bool.notTrue _ (Bool.andLeft (Bool.andRight nonCloser)))
                (Bool.andRight (Bool.andRight nonCloser))
                homed))
        | InfixArrow =>
          framedShape
            (Infix InfixArrow left operator right)
            around
            (chain (Infix InfixArrow left operator right).chainLevel left operator right { around | hoisted = True })
            within
            (leadSound (Infix InfixArrow left operator right) sound)
            (chainOfShape
              (left.opensArms (Infix InfixArrow left operator right).chainLevel)
              (chainLinks (Infix InfixArrow left operator right).chainLevel True left operator right { around |
                hoisted = True
              }) _
              (chainLinksShape
                (Infix InfixArrow left operator right).chainLevel
                True
                left
                operator
                right
                { around | hoisted = True }
                prior
                (Bool.andLeft within)
                (Bool.andLeft (Bool.andRight within))
                (Bool.andLeft sound)
                (Bool.andLeft (Bool.andRight sound))
                (Bool.andRight (Bool.andRight sound))
                (Bool.andLeft nonCloser)
                (Bool.notTrue _ (Bool.andLeft (Bool.andRight nonCloser)))
                (Bool.andRight (Bool.andRight nonCloser))
                homed))
        | _ => cases

-- The body after `:=`.

theorem unnotedToldAbove ∀ (word: Word) (item closer: Bool)
    (unnoted: word.noted = False)
    (low: item = False):
    (word.kept item closer).comments.toldAbove = [] :=
  match word with
    | { text, comments = { above = [], after, blankBefore } } =>
      match blankBefore with
        | True => rewrite low
        | False => rewrite low

--| An expression with no own-line comments above it tells the same where an enclosing element wrote them.
theorem shapeUnnoted ∀ (expr: Expr)
    (within: expr.within1 = True)
    (unnoted: expr.noted = False):
    expr.shape False False = expr.shape False True :=
  rewrite shapeLead expr False within,
      unnotedToldAbove expr.lead
        (False)
        (isCloserText expr.lead.text)
        (rewrite <- firstWordLead expr within then unnoted)
        byComputing

theorem allIsAppend ∀ (front back: List Doc) (shape: List Told)
    (first: AllIs front shape)
    (second: AllIs back shape):
    AllIs (front ++ back) shape :=
  match front with
    | [] => second
    | [doc, ..rest] => (first.left, allIsAppend rest back shape first.right second)

theorem allIsOption ∀ (option: Option Doc) (shape: List Told)
    (is: ∀ (doc: Doc) => option = Some doc → Is doc shape):
    AllIs (optionList option) shape :=
  match option, is with
    | None, _ => byComputing
    | Some doc, is => (is doc byComputing, byComputing)

theorem callHugShape ∀ (value: Expr) (inside: Around) (prior: List Word)
    (within: value.within1 = True)
    (sound: value.sound = True)
    (nonCloser: value.nonCloser = True)
    (homed: homedBack (value.words.reverse ++ prior) = True):
    ∀ (hugged: Doc) => value.callHug inside = Some hugged → Is hugged (value.shape inside.item inside.hoisted) :=
  match value with
    | App head arguments =>
      (hugged same =>
        (appDocsShape head arguments inside prior
              (Bool.andLeft within)
              (Bool.andLeft sound)
              (Bool.andLeft nonCloser)
              (around prior w s n h => elShape head around prior w s n h)
              (Bool.andRight within)
              (Bool.andRight sound)
              (Bool.andRight nonCloser)
              (allElShape arguments (Bool.andRight within) (Bool.andRight sound) (Bool.andRight nonCloser))
              homed).right hugged same)
    | _ => (hugged same => cases)

--| A hug after a space tells what the hug does.
theorem spacedHugShape ∀ (hug: Option Doc) (shape: List Told)
    (each: ∀ (hugged: Doc) => hug = Some hugged → Is hugged shape):
    ∀ (doc: Doc) => hug.map (open => Doc.concat [Doc.text " ", open]) = Some doc → Is doc shape :=
  match hug, each with
    | None, _ => (doc same => cases)
    | Some opened, each =>
      (doc same =>
        rewrite <- Option.someInjective same then
          isConcat _ _
            (isCons (Doc.text " ") [opened] [] shape isSpace (isLast opened shape (each opened byComputing))))

--| A body after `:=` tells the value in both its forms.
--|
--| Proof idea: The value's element (`elShape`); below it is a nest, the choice's options (flat, one line below, the hug
--| on the line, below) each tell the same; the hug leaves out the value's own-line comments, which it has none of.
theorem bodyAfterShape ∀ (value: Expr) (assign: Word) (around: Around) (semi: Bool) (prior: List Word)
    (within: value.within1 = True)
    (sound: value.sound = True)
    (nonCloser: value.nonCloser = True)
    (homed: homedBack (value.words.reverse ++ prior) = True)
    (low: around.hoisted = False)
    (plain: around.item = False):
    Is (bodyAfter value assign around semi).fst (value.shape False False)
      ∧ Is (bodyAfter value assign around semi).snd (value.shape False False) :=
  let docIs: Is (value.el around) (value.shape False False) :=
    isSame _ _ _ (elShape value around prior within sound nonCloser homed) (rewrite low, plain)
  let belowIs: Is (Nest 2 (Doc.concat [HardLine, value.el around])) (value.shape False False) :=
    isNest 2 _ _
      (isConcat _ _ (isCons HardLine [value.el around] [] (value.shape False False) isHardLine (isLast _ _ docIs)))
  let inside: Around := { around | hoisted = True }
  rewrite matchedNone value inside within,
      valueElPlain value around semi within,
      lambdaHugNone value semi inside (value.el around) within then
    match same: assign.trails || value.noted || value.isBlock with
      | True => (belowIs, belowIs)
      | False =>
        let unnoted: value.noted = False :=
          Bool.orFalseLeft value.noted value.isBlock
            (Bool.orFalseRight assign.trails (value.noted || value.isBlock) same)
        let hugIs: ∀ (hugged: Doc) => value.callHug inside = Some hugged → Is hugged (value.shape False False) :=
          (hugged is =>
            isSame _ _ _
              (callHugShape value inside prior within sound nonCloser homed hugged is)
              (rewrite plain then (shapeUnnoted value within unnoted).flipped))
        let flat: Is (Flatten (Doc.concat [Doc.text " ", value.el around])) (value.shape False False) :=
          isFlatten _ _
            (isConcat _ _
              (isCons (Doc.text " ") [value.el around] [] (value.shape False False) isSpace (isLast _ _ docIs)))
        (
          belowIs,
          isChoice (Flatten (Doc.concat [Doc.text " ", value.el around])) _ (value.shape False False) (
            flat,
            allIsAppend
              (if value.opensBracket || (value.callHug inside).isSome then [OneLineBelow (value.el around)] else [])
              ((if value.opensBracket then [Doc.concat [Doc.text " ", value.el around]]
                else optionList ((value.callHug inside).map (open => Doc.concat [Doc.text " ", open])))
                ++ [Nest 2 (Doc.concat [HardLine, value.el around])])
              (value.shape False False)
              (match value.opensBracket || (value.callHug inside).isSome with
                | True => (isOneLineBelow _ _ docIs, byComputing)
                | False => byComputing)
              (allIsAppend
                (if value.opensBracket then [Doc.concat [Doc.text " ", value.el around]]
                 else optionList ((value.callHug inside).map (open => Doc.concat [Doc.text " ", open])))
                [Nest 2 (Doc.concat [HardLine, value.el around])]
                (value.shape False False)
                (match value.opensBracket with
                  | True => (
                    isConcat _ _
                      (isCons (Doc.text " ") [value.el around] [] (value.shape False False) isSpace (isLast _ _ docIs)),
                    byComputing
                  )
                  | False => allIsOption _ _ (spacedHugShape _ _ hugIs))
                (belowIs, byComputing))
          )
        )

-- Declarations.

--| What a definition's document tells: the tokens in order, as `decl.stood` has them but for the blank lines and
--| own-line comments of its `def`, which the file prints, with a bare comma between a bracket's items.
def Decl.shape: Decl → List Told
  | Definition _ header (Assigned colonEq value) =>
    (fixedWord "def" header.keyword).shapeK False True
      ++ header.name.shapeK False False
      ++ (fixedWord ":" header.colon).shapeK False False
      ++ header.result.shape False False
      ++ (fixedWord ":=" colonEq).shapeK False False
      ++ value.shape False False
  | _ => []

--| The tokens a declaration prints that are no closers: its name and what its type and value hold.
def Decl.nonCloser: Decl → Bool
  | Definition _ header (Assigned _ value) =>
    !isCloserText header.name.text && header.result.nonCloser && value.nonCloser
  | _ => False

--| A definition's document tells its header, its `:=` and its body.
--|
--| Proof idea: A concat of the header in an `IdGroup`, a space, the `:=` and the body's `IfBroken`.
theorem defFromShape ∀ (headerDoc assignDoc below choice: Doc)
    (breaks: Bool) (headerShape assignShape bodyShape: List Told)
    (header: Is headerDoc headerShape)
    (assigns: Is assignDoc assignShape)
    (belowIs: Is below bodyShape)
    (choiceIs: Is choice bodyShape):
    Is (defFrom headerDoc breaks assignDoc below choice) (headerShape ++ assignShape ++ bodyShape) :=
  isConcat _ _
    (isCons
      (IdGroup 0 headerDoc breaks)
      [Doc.text " ", assignDoc, IfBroken 0 below choice]
      headerShape
      (assignShape ++ bodyShape)
      (isIdGroup 0 headerDoc breaks headerShape header)
      (isCons
        (Doc.text " ")
        [assignDoc, IfBroken 0 below choice]
        []
        (assignShape ++ bodyShape)
        isSpace
        (isCons assignDoc
          [IfBroken 0 below choice]
          assignShape
          bodyShape
          assigns
          (isLast (IfBroken 0 below choice) bodyShape (isIfBroken 0 below choice bodyShape belowIs choiceIs)))))

theorem typedShape ∀ (trails: Bool) (typeDoc: Doc) (shape: List Told)
    (is: Is typeDoc shape):
    IsAll (if trails then [Nest 4 (Doc.concat [HardLine, typeDoc])] else [Doc.text " ", Nest 4 typeDoc]) shape :=
  match trails with
    | True => isLast _ _ (isNest 4 _ _ (isConcat _ _ (isCons HardLine [typeDoc] [] shape isHardLine (isLast _ _ is))))
    | False => isCons (Doc.text " ") [Nest 4 typeDoc] [] shape isSpace (isLast _ _ (isNest 4 _ _ is))

theorem declHomed ∀ (keyword name colonWord: Word) (result: Expr) (assign: Word) (value: Expr)
    (homed: homedBack (([keyword, name, colonWord] ++ result.words ++ [assign] ++ value.words).reverse) = True):
    homedBack (result.words.reverse ++ [colonWord, name, keyword]) = True
      ∧ homedBack (value.words.reverse ++ ([assign] ++ (result.words.reverse ++ [colonWord, name, keyword]))) = True :=
  let split: ([keyword, name, colonWord] ++ result.words ++ [assign] ++ value.words).reverse
    = value.words.reverse ++ ([assign] ++ (result.words.reverse ++ [colonWord, name, keyword])) :=
    rewrite List.reverseAppend [keyword, name, colonWord] (result.words ++ [assign] ++ value.words),
        List.reverseAppend result.words ([assign] ++ value.words),
        List.reverseAppend [assign] value.words,
        List.appendAssoc (value.words.reverse ++ [assign]) result.words.reverse [colonWord, name, keyword],
        List.appendAssoc value.words.reverse [assign] (result.words.reverse ++ [colonWord, name, keyword])
  let whole := rewrite split at homed then homed
  (
    homedSuffix
      (value.words.reverse ++ [assign])
      (result.words.reverse ++ [colonWord, name, keyword])
      (rewrite List.appendAssoc value.words.reverse [assign] (result.words.reverse ++ [colonWord, name, keyword]) then
        whole),
    whole
  )

theorem assocSix ∀ (a b c d e f: List Told): (a ++ b ++ c ++ d) ++ e ++ f = a ++ b ++ c ++ d ++ e ++ f :=
  rewrite List.appendAssoc a (b ++ c ++ d) (e ++ f), List.appendAssoc b (c ++ d) (e ++ f), List.appendAssoc c d (e ++ f)

theorem assocHeader ∀ (a b c d: List Told): ((a ++ b) ++ c) ++ d = a ++ b ++ c ++ d :=
  rewrite List.appendAssoc (a ++ b) c d, List.appendAssoc a b (c ++ d)

--| A definition with no parameters tells its tokens in order.
--|
--| Proof idea: `defFromShape` with the header (the head words spaced, the colon, the type: `typedShape`), the `:=`'s
--| leaf and `bodyAfterShape`; every word is homed by `homedBack` of the declaration's words read back, split by
--| `declHomed`.
theorem plainDefShape ∀ (keyword: Comments) (name: Word) (colon: Comments) (result: Expr)
    (colonEq: Comments) (value: Expr)
    (resultWithin: result.within1 = True)
    (valueWithin: value.within1 = True)
    (keywordSound: (fixedWord "def" keyword).sound = True)
    (nameSound: name.sound = True)
    (colonSound: (fixedWord ":" colon).sound = True)
    (resultSound: result.sound = True)
    (assignSound: (fixedWord ":=" colonEq).sound = True)
    (valueSound: value.sound = True)
    (nameOpens: isCloserText name.text = False)
    (resultNonCloser: result.nonCloser = True)
    (valueNonCloser: value.nonCloser = True)
    (homed: homedBack
      ([fixedWord "def" keyword, name, fixedWord ":" colon]
        ++ result.words
        ++ [fixedWord ":=" colonEq]
        ++ value.words).reverse
      = True):
    Is
      (plainDef keyword name colon result colonEq value)
      ((fixedWord "def" keyword).shapeK False True
        ++ name.shapeK False False
        ++ (fixedWord ":" colon).shapeK False False
        ++ result.shape False False
        ++ (fixedWord ":=" colonEq).shapeK False False
        ++ value.shape False False) :=
  let start: Around := { before = False, hoisted = True, item = False, at = 0, inArm = False }
  let colonWord := fixedWord ":" colon
  let assign := fixedWord ":=" colonEq
  let (resultHomed, valueHomed) := declHomed (fixedWord "def" keyword) name colonWord result assign value homed
  let typeIs :=
    elShape result
      (start.next colonWord.trails 3)
      [colonWord, name, fixedWord "def" keyword]
      resultWithin
      resultSound
      resultNonCloser
      resultHomed
  let bodyIs :=
    bodyAfterShape value assign
      (start.next assign.trails (4 + result.size))
      False
      ([assign] ++ (result.words.reverse ++ [colonWord, name, fixedWord "def" keyword]))
      valueWithin
      valueSound
      valueNonCloser
      valueHomed
      byComputing
      byComputing
  let headIs: Is
    (spaced (headDocs start [fixedWord "def" keyword, name]))
    ((fixedWord "def" keyword).shapeK False True ++ name.shapeK False False) :=
    isSame
      (spaced (headDocs start [fixedWord "def" keyword, name]))
      ((fixedWord "def" keyword).shapeK False True ++ name.shapeK False False ++ [])
      ((fixedWord "def" keyword).shapeK False True ++ name.shapeK False False)
      (isSpaced
        (headDocs start [fixedWord "def" keyword, name])
        [(fixedWord "def" keyword).shapeK False True, name.shapeK False False]
        (
          spot =>
            rewrite <- printedShape (fixedWord "def" keyword) start then
              leafShape (fixedWord "def" keyword) start 0 spot keywordSound (homesOpen _ start byComputing),
          (
            spot =>
              rewrite <- printedShape name (start.next (fixedWord "def" keyword).trails 1) then
                leafShape name
                  (start.next (fixedWord "def" keyword).trails 1)
                  1
                  spot
                  nameSound
                  (homesOpen name (start.next (fixedWord "def" keyword).trails 1) nameOpens),
            byComputing
          )
        ))
      (rewrite List.appendNil (name.shapeK False False))
  let colonIs: Is
    (colonWord.leaf (start.next (trailsBack [name, fixedWord "def" keyword]) 2) 2)
    (colonWord.shapeK False False) :=
    spot =>
      rewrite <- printedShape colonWord (start.next (trailsBack [name, fixedWord "def" keyword]) 2) then
        leafShape colonWord
          (start.next (trailsBack [name, fixedWord "def" keyword]) 2)
          2
          spot
          colonSound
          (homesOpen colonWord (start.next (trailsBack [name, fixedWord "def" keyword]) 2) byComputing)
  let assignIs: Is
    (assign.leaf (start.next result.trails (3 + result.size)) (3 + result.size))
    (assign.shapeK False False) :=
    spot =>
      rewrite <- printedShape assign (start.next result.trails (3 + result.size)) then
        leafShape assign
          (start.next result.trails (3 + result.size))
          (3 + result.size)
          spot
          assignSound
          (homesOpen assign (start.next result.trails (3 + result.size)) byComputing)
  let headDoc := spaced (headDocs start [fixedWord "def" keyword, name])
  let colonLeaf := colonWord.leaf (start.next (trailsBack [name, fixedWord "def" keyword]) 2) 2
  let typed :=
    if colonWord.trails then [Nest 4 (Doc.concat [HardLine, result.el (start.next colonWord.trails 3)])]
    else [Doc.text " ", Nest 4 (result.el (start.next colonWord.trails 3))]
  let breaks :=
    (Doc.concat ([headDoc, colonLeaf] ++ typed)).forcesBreak
      || ([fixedWord "def" keyword, name].reverse.drop 1 |> .any Word.trails)
      || colonWord.trails
      || (result.words.reverse.drop 1 |> .any Word.trails)
      || (value.layoutBody && (lastCode [fixedWord "def" keyword, name]).trails)
  isSame
    (plainDef keyword name colon result colonEq value) _ _
    (defFromShape _ _ _ _ breaks _ _ _
      (isConcat
        ([headDoc, colonLeaf] ++ typed) _
        (isAllSame
          ([headDoc, colonLeaf] ++ typed)
          ((((fixedWord "def" keyword).shapeK False True ++ name.shapeK False False) ++ colonWord.shapeK False False)
            ++ result.shape False False)
          ((fixedWord "def" keyword).shapeK False True
            ++ name.shapeK False False
            ++ colonWord.shapeK False False
            ++ result.shape False False)
          (isAppend
            [headDoc, colonLeaf]
            typed
            (((fixedWord "def" keyword).shapeK False True ++ name.shapeK False False) ++ colonWord.shapeK False False)
            (result.shape False False)
            (isCons headDoc
              [colonLeaf]
              ((fixedWord "def" keyword).shapeK False True ++ name.shapeK False False)
              (colonWord.shapeK False False)
              headIs
              (isLast colonLeaf _ colonIs))
            (typedShape colonWord.trails _ _ typeIs))
          (assocHeader
            ((fixedWord "def" keyword).shapeK False True)
            (name.shapeK False False)
            (colonWord.shapeK False False)
            (result.shape False False))))
      assignIs
      bodyIs.left
      bodyIs.right)
    (assocSix
      ((fixedWord "def" keyword).shapeK False True)
      (name.shapeK False False)
      (colonWord.shapeK False False)
      (result.shape False False)
      (assign.shapeK False False)
      (value.shape False False))

theorem isEq ∀ (doc doc': Doc) (shape: List Told) (same: doc = doc') (is: Is doc' shape): Is doc shape :=
  rewrite same then is

--| The document a slice 1 declaration has tells its shape.
--|
--| Proof idea: `plainDefIs` and `plainDefShape`, with the tokens' soundness taken from the declaration's, and the
--| tokens' homes from `homedBack` of the declaration's words read back.
theorem doc1Shape ∀ (decl: Decl) (doc: Doc)
    (within: decl.within1 = True)
    (sound: decl.sound = True)
    (nonCloser: decl.nonCloser = True)
    (homed: homedBack decl.words.reverse = True)
    (shows: decl.doc1 = Some doc):
    Is doc decl.shape :=
  match decl with
    | Definition [] header (Assigned colonEq value) =>
      match header with
        | {
            exportKeyword = None,
            opaqueKeyword = None,
            kind = DefPlain,
            keyword,
            name,
            forallKeyword = None,
            params = [],
            colon,
            result,
            decreasingClause = None,
            unfoldingClause = None
          } =>
          rewrite <- Option.someInjective shows then
            isEq _ _ _
              (plainDefIs keyword name colon result colonEq value)
              (plainDefShape keyword name colon result colonEq value
                (Bool.andRight (Bool.andLeft within))
                (Bool.andRight within)
                (Bool.andLeft sound)
                (Bool.andLeft (Bool.andRight sound))
                (Bool.andLeft (Bool.andRight (Bool.andRight sound)))
                (Bool.andLeft (Bool.andRight (Bool.andRight (Bool.andRight sound))))
                (Bool.andLeft (Bool.andRight (Bool.andRight (Bool.andRight (Bool.andRight sound)))))
                (Bool.andRight (Bool.andRight (Bool.andRight (Bool.andRight (Bool.andRight sound)))))
                (Bool.notTrue _ (Bool.andLeft nonCloser))
                (Bool.andLeft (Bool.andRight nonCloser))
                (Bool.andRight (Bool.andRight nonCloser))
                homed)
        | _ => cases

--| `printedTold`'s first half: the printer's document for a declaration tells the declaration's shape from a line start.
theorem doc1Told ∀ (decl: Decl) (doc: Doc)
    (within: decl.within1 = True)
    (sound: decl.sound = True)
    (nonCloser: decl.nonCloser = True)
    (homed: homedBack decl.words.reverse = True)
    (shows: decl.doc1 = Some doc):
    Refines (doc.told Spot.lineStart) decl.shape :=
  doc1Shape decl doc within sound nonCloser homed shows Spot.lineStart
