--| `laysKinds` of a comma bracket's document (SW-4109): a tuple or list from the elements' steps (`Fmt.LaysEls`).
namespace Fmt.LaysBrackets
import Std (Bool, Doc, Eq, List, Nat, Option, Text, Void)
import Std.Doc (..)
import Syntax (Expr, Word)
import Fmt (..)
import Fmt.LaysKinds (..)
import Fmt.LaysRules (..)
import Fmt.SpellProofs (..)
import Fmt.AppHangProofs (lastArg)
import Fmt.TrailsProofs (Coded, itemsBack, trailsBackCoded)
import Fmt.ToldDeclProofs (..)
import Fmt.LaysWords (..)

--| Each item of a bracket passes the check, wherever it starts.
def ItemsEl: List Expr → Prop
  | [] => True
  | [item, ..rest] =>
    (∀ (around: Around) => Step (item.el around) (Starts around.hoisted around.before) (kinds =>
      Ends kinds item.trails))
      ∧ ItemsEl rest

--| What the last of the items ends with: the code before the first, if there are none.
def itemsEnd (before: Bool): List Expr → Bool
  | [] => before
  | [item, ..rest] => itemsEnd item.trails rest

theorem stepComma ∀ (trails: Bool): Step (Closing ",") (kinds => Ends kinds trails) (kinds => Ends kinds trails) :=
  kinds holds =>
    match kinds, holds with
      | { start = False, broken = False, mid, held }, holds =>
        ({ start = False, broken = False, mid = True, held }, closingKinds "," byComputing byComputing kinds, holds)

theorem stepSeparator ∀ (first trails: Bool):
    Step (if first then SoftLine else Line) (kinds => Ends kinds trails) (Starts False trails) :=
  match first with
    | True => stepSoftLine trails
    | False => stepLine trails

--| A broken bracket's items, each starting a line, with its comma after it.
theorem brokenItemsStep ∀ (bare arm first before: Bool) (at: Nat) (items: List Expr)
    (els: ItemsEl items):
    StepAll (brokenItems bare arm first before at items) (kinds => Ends kinds before) (kinds =>
      Ends kinds (itemsEnd before items)) :=
  match items with
    | [] => stepAllNil (kinds => Ends kinds before)
    | [item] =>
      stepAllCons
        (if first then SoftLine else Line)
        [item.el (firstAround bare arm before at)]
        (kinds => Ends kinds before)
        (Starts False before)
        (kinds => Ends kinds item.trails)
        (stepSeparator first before)
        (stepAllOne
          (item.el (firstAround bare arm before at))
          (Starts False before)
          (kinds => Ends kinds item.trails)
          (els.left (firstAround bare arm before at)))
    | [item, next, ..more] =>
      stepAllCons
        (if first then SoftLine else Line)
        [
          item.el (firstAround bare arm before at),
          Closing ",",
          ..brokenItems False arm False item.trails (at + item.size) [next, ..more]
        ]
        (kinds => Ends kinds before)
        (Starts False before)
        (kinds => Ends kinds (itemsEnd before [item, next, ..more]))
        (stepSeparator first before)
        (stepAllCons
          (item.el (firstAround bare arm before at))
          [Closing ",", ..brokenItems False arm False item.trails (at + item.size) [next, ..more]]
          (Starts False before)
          (kinds => Ends kinds item.trails)
          (kinds => Ends kinds (itemsEnd before [item, next, ..more]))
          (els.left (firstAround bare arm before at))
          (stepAllCons
            (Closing ",")
            (brokenItems False arm False item.trails (at + item.size) [next, ..more])
            (kinds => Ends kinds item.trails)
            (kinds => Ends kinds item.trails)
            (kinds => Ends kinds (itemsEnd before [item, next, ..more]))
            (stepComma item.trails)
            (brokenItemsStep False arm False item.trails (at + item.size) [next, ..more] els.right)))

--| A filled list's cells, each from where the one before ended.
theorem cellsChain ∀ (bare arm before: Bool) (at: Nat) (items: List Expr)
    (els: ItemsEl items):
    Chained (cells bare arm before at items) before (itemsEnd before items) :=
  match items with
    | [] => byComputing
    | [item] => (item.trails, els.left (firstAround bare arm before at), byComputing)
    | [item, next, ..more] => (
      item.trails,
      stepDocConcat _ _ _
        (stepAllCons
          (item.el (firstAround bare arm before at))
          [Closing ","]
          (Starts False before)
          (kinds => Ends kinds item.trails)
          (kinds => Ends kinds item.trails)
          (els.left (firstAround bare arm before at))
          (stepAllOne
            (Closing ",")
            (kinds => Ends kinds item.trails)
            (kinds => Ends kinds item.trails)
            (stepComma item.trails))),
      cellsChain False arm item.trails (at + item.size) [next, ..more] els.right
    )

-- A bracket's last token.

theorem itemsEndLast ∀ (before: Bool) (argument: Expr) (rest: List Expr):
    itemsEnd before [argument, ..rest] = (lastArg argument rest).trails :=
  match rest with
    | [] => byComputing
    | [next, ..more] => itemsEndLast argument.trails next more

--| A bracket trails as its closer does, or as what stands before it, past closers.
theorem bracketTrails ∀ (whole: Expr) (open: Word) (items: List Expr) (close: Word)
    (shape: whole.words = [open, ..itemsWords items] ++ [close]):
    whole.trails = (close.trails || (isCloserText close.text && whole.trailsBeforeClose)) :=
  rewrite shape, bracketBackWords open (itemsWords items) close

theorem bracketBeforeEmpty ∀ (whole: Expr) (open close: Word)
    (shape: whole.words = [open, ..itemsWords []] ++ [close])
    (openOpen: isCloserText open.text = False):
    whole.trailsBeforeClose = open.trails :=
  rewrite shape, openOpen, Bool.orFalse open.trails

theorem bracketBeforeItems ∀ (whole: Expr) (open: Word) (argument: Expr) (rest: List Expr) (close: Word)
    (shape: whole.words = [open, ..itemsWords [argument, ..rest]] ++ [close])
    (code: Coded (lastArg argument rest).words.reverse = True):
    whole.trailsBeforeClose = (lastArg argument rest).trails :=
  let (front, back) := itemsBack argument rest
  rewrite shape,
      bracketBackWords open (itemsWords [argument, ..rest]) close,
      back,
      List.appendAssoc (lastArg argument rest).words.reverse front [open],
      trailsBackCoded (lastArg argument rest).words.reverse (front ++ [open]) code

theorem stepIte ∀ (cond: Bool) (yes no: Doc) (pre post: Kinds → Bool)
    (first: cond = True → Step yes pre post)
    (second: cond = False → Step no pre post):
    Step (if cond then yes else no) pre post :=
  match cond with
    | True => first byComputing
    | False => second byComputing

--| A filled list's cells, the first from where it starts and the rest each after the one before.
theorem stepCells ∀ (bare arm before: Bool) (at: Nat) (argument: Expr) (rest: List Expr)
    (els: ItemsEl [argument, ..rest]):
    Step (Fill (cells bare arm before at [argument, ..rest])) (Starts False before) (kinds =>
      Ends kinds (itemsEnd before [argument, ..rest])) :=
  match rest with
    | [] =>
      stepFill
        (argument.el (firstAround bare arm before at))
        []
        (Starts False before)
        argument.trails
        argument.trails
        (els.left (firstAround bare arm before at))
        byComputing
    | [next, ..more] =>
      stepFill
        (Doc.concat [argument.el (firstAround bare arm before at), Closing ","])
        (cells False arm argument.trails (at + argument.size) [next, ..more])
        (Starts False before)
        argument.trails
        (itemsEnd before [argument, next, ..more])
        (stepDocConcat _ _ _
          (stepAllCons
            (argument.el (firstAround bare arm before at))
            [Closing ","]
            (Starts False before)
            (kinds => Ends kinds argument.trails)
            (kinds => Ends kinds argument.trails)
            (els.left (firstAround bare arm before at))
            (stepAllOne
              (Closing ",")
              (kinds => Ends kinds argument.trails)
              (kinds => Ends kinds argument.trails)
              (stepComma argument.trails))))
        (cellsChain False arm argument.trails (at + argument.size) [next, ..more] els.right)

theorem startsSame ∀ (kinds: Kinds) (hoisted trails trails': Bool)
    (same: trails = trails')
    (starts: Starts hoisted trails kinds = True):
    Starts hoisted trails' kinds = True :=
  rewrite <- same then starts

--| A bracket's closer, from where what stands before it ended.
theorem closeStepStarts ∀ (open: Word) (items: List Expr) (close: Word) (around: Around) (prior: Bool)
    (closeSound: close.sound = True)
    (closeShut: isCloserText close.text = True)
    (closes: Doc.Proofs.closesText close.text = True)
    (same: (ListOf open items False close).trailsBeforeClose = prior):
    Step
      (close.leaf
        (around.next (ListOf open items False close).trailsBeforeClose ((ListOf open items False close).size - 1))
        around.at)
      (Starts False prior)
      (kinds => Ends kinds (ListOf open items False close).trails) :=
  stepWeaken
    (close.leaf
      (around.next (ListOf open items False close).trailsBeforeClose ((ListOf open items False close).size - 1))
      around.at)
    (Starts False (ListOf open items False close).trailsBeforeClose)
    (Starts False prior)
    (kinds =>
      Ends kinds (close.trails || (isCloserText close.text && (ListOf open items False close).trailsBeforeClose)))
    (kinds => Ends kinds (ListOf open items False close).trails)
    (wordStep close
      (around.next (ListOf open items False close).trailsBeforeClose ((ListOf open items False close).size - 1))
      around.at
      closeSound
      (notCommaOf close (closerNotComma close.text closeShut))
      (closed => closes)
      (closed => byComputing))
    (kinds good => startsSame kinds False _ _ same.flipped good)
    (kinds good =>
      endsSame kinds _ _ (bracketTrails (ListOf open items False close) open items close byComputing).flipped good)

theorem closeStep ∀ (open: Word) (items: List Expr) (close: Word) (around: Around) (prior: Bool)
    (closeSound: close.sound = True)
    (closeShut: isCloserText close.text = True)
    (closes: Doc.Proofs.closesText close.text = True)
    (same: (ListOf open items False close).trailsBeforeClose = prior):
    Step
      (close.leaf
        (around.next (ListOf open items False close).trailsBeforeClose ((ListOf open items False close).size - 1))
        around.at)
      (kinds => Ends kinds prior)
      (kinds => Ends kinds (ListOf open items False close).trails) :=
  stepWeaken
    (close.leaf
      (around.next (ListOf open items False close).trailsBeforeClose ((ListOf open items False close).size - 1))
      around.at)
    (Starts False prior)
    (kinds => Ends kinds prior)
    (kinds => Ends kinds (ListOf open items False close).trails)
    (kinds => Ends kinds (ListOf open items False close).trails)
    (closeStepStarts open items close around prior closeSound closeShut closes same)
    (kinds good => endsStarts kinds prior good)
    (kinds good => good)

theorem stepConcatIf ∀ (cond: Bool) (yes no: List Doc) (pre post: Kinds → Bool)
    (first: StepAll yes pre post)
    (second: StepAll no pre post):
    Step (Doc.concat (if cond then yes else no)) pre post :=
  match cond with
    | True => stepDocConcat _ _ _ first
    | False => stepDocConcat _ _ _ second

--| A broken bracket's parts: the opener, the items each on a line, a soft line, the closer.
theorem brokenParts ∀ (open: Word) (items: List Expr) (close: Word) (around: Around) (bare prior: Bool)
    (openS: Step (open.opening around close) NoHeld (kinds => Ends kinds open.trails))
    (els: ItemsEl items)
    (closeS: Step
      (close.leaf
        (around.next (ListOf open items False close).trailsBeforeClose ((ListOf open items False close).size - 1))
        around.at)
      (Starts False (itemsEnd open.trails items))
      (kinds => Ends kinds (ListOf open items False close).trails)):
    StepAll
      [
        open.opening around close,
        Nest 2 (Doc.concat (brokenItems bare around.inArm True open.trails (around.at + 1) items)),
        SoftLine,
        close.leaf
          (around.next (ListOf open items False close).trailsBeforeClose ((ListOf open items False close).size - 1))
          around.at
      ]
      NoHeld
      (kinds => Ends kinds (ListOf open items False close).trails) :=
  stepAllCons
    (open.opening around close)
    [
      Nest 2 (Doc.concat (brokenItems bare around.inArm True open.trails (around.at + 1) items)),
      SoftLine,
      close.leaf
        (around.next (ListOf open items False close).trailsBeforeClose ((ListOf open items False close).size - 1))
        around.at
    ]
    NoHeld
    (kinds => Ends kinds open.trails)
    (kinds => Ends kinds (ListOf open items False close).trails)
    openS
    (stepAllCons
      (Nest 2 (Doc.concat (brokenItems bare around.inArm True open.trails (around.at + 1) items)))
      [
        SoftLine,
        close.leaf
          (around.next (ListOf open items False close).trailsBeforeClose ((ListOf open items False close).size - 1))
          around.at
      ]
      (kinds => Ends kinds open.trails)
      (kinds => Ends kinds (itemsEnd open.trails items))
      (kinds => Ends kinds (ListOf open items False close).trails)
      (stepNest 2 _ _ _
        (stepDocConcat _ _ _ (brokenItemsStep bare around.inArm True open.trails (around.at + 1) items els)))
      (stepAllCons SoftLine
        [
          close.leaf
            (around.next (ListOf open items False close).trailsBeforeClose ((ListOf open items False close).size - 1))
            around.at
        ]
        (kinds => Ends kinds (itemsEnd open.trails items))
        (Starts False (itemsEnd open.trails items))
        (kinds => Ends kinds (ListOf open items False close).trails)
        (stepSoftLine (itemsEnd open.trails items))
        (stepAllOne
          (close.leaf
            (around.next (ListOf open items False close).trailsBeforeClose ((ListOf open items False close).size - 1))
            around.at)
          (Starts False (itemsEnd open.trails items))
          (kinds => Ends kinds (ListOf open items False close).trails)
          closeS)))

--| A tuple's or list's document (`comma_bracket_content`): the opener, the items, the closer.
--|
--| Proof idea: by the three shapes the rules pick (no items; a filled list; broken items, with a `BreakParent` at the
--| end if a comment is held): the opener (`openStep`), the items from where it ended (`stepCells` or
--| `brokenItemsStep`), then the closer from where the last item ended (`closeStep`).
theorem bracketContentStep ∀ (list: Bool) (open: Word) (items: List Expr) (close: Word) (around: Around)
    (hoisted: around.hoisted = True)
    (openSound: open.sound = True)
    (closeSound: close.sound = True)
    (openOpen: isCloserText open.text = False)
    (openComma: open.notComma = True)
    (closeShut: isCloserText close.text = True)
    (closes: Doc.Proofs.closesText close.text = True)
    (els: ItemsEl items)
    (stops: ∀ (argument: Expr) (rest: List Expr) => items = [argument, ..rest]
      → Coded (lastArg argument rest).words.reverse = True):
    Step (bracketContent list open items close around) NoHeld (kinds =>
      Ends kinds (ListOf open items False close).trails) :=
  match items with
    | [] =>
      stepDocConcat _ _ _
        (stepAllCons
          (open.opening around close)
          [
            close.leaf
              (around.next (ListOf open [] False close).trailsBeforeClose ((ListOf open [] False close).size - 1))
              around.at
          ]
          NoHeld
          (kinds => Ends kinds open.trails)
          (kinds => Ends kinds (ListOf open [] False close).trails)
          (stepWeaken
            (open.opening around close)
            Anything
            NoHeld
            (kinds => Ends kinds open.trails)
            (kinds => Ends kinds open.trails)
            (openStep open close around hoisted openSound openComma openOpen)
            (kinds good => anything kinds)
            (kinds good => good))
          (stepAllOne
            (close.leaf
              (around.next (ListOf open [] False close).trailsBeforeClose ((ListOf open [] False close).size - 1))
              around.at)
            (kinds => Ends kinds open.trails)
            (kinds => Ends kinds (ListOf open [] False close).trails)
            (closeStep open [] close around open.trails closeSound closeShut closes
              (bracketBeforeEmpty (ListOf open [] False close) open close byComputing openOpen))))
    | [argument, ..rest] =>
      let whole := ListOf open [argument, ..rest] False close
      let same: whole.trailsBeforeClose = itemsEnd open.trails [argument, ..rest] :=
        Eq.trans
          (bracketBeforeItems whole open argument rest close byComputing (stops argument rest byComputing))
          (itemsEndLast open.trails argument rest).flipped
      let openS: Step (open.opening around close) NoHeld (kinds => Ends kinds open.trails) :=
        stepWeaken
          (open.opening around close)
          Anything
          NoHeld
          (kinds => Ends kinds open.trails)
          (kinds => Ends kinds open.trails)
          (openStep open close around hoisted openSound openComma openOpen)
          (kinds good => anything kinds)
          (kinds good => good)
      let closeS2 :=
        closeStepStarts open
          [argument, ..rest]
          close
          around
          (itemsEnd open.trails [argument, ..rest])
          closeSound
          closeShut
          closes
          same
      let closeS :=
        closeStep open
          [argument, ..rest]
          close
          around
          (itemsEnd open.trails [argument, ..rest])
          closeSound
          closeShut
          closes
          same
      stepIte
        (list && !whole.holdsTrailingComment && [argument, ..rest].all Expr.plainItem)
        (Doc.concat [
          open.opening around close,
          Nest 2
            (Fill
              (cells (list && [argument, ..rest].all Expr.plainItem) around.inArm open.trails (around.at + 1) [
                argument,
                ..rest
              ])),
          close.leaf (around.next whole.trailsBeforeClose (whole.size - 1)) around.at
        ])
        (Doc.concat
          (if whole.holdsTrailingComment then
             [
               open.opening around close,
               Nest 2
                 (Doc.concat
                   (brokenItems
                     (list && [argument, ..rest].all Expr.plainItem)
                     around.inArm
                     True
                     open.trails
                     (around.at + 1)
                     [argument, ..rest])),
               SoftLine,
               close.leaf (around.next whole.trailsBeforeClose (whole.size - 1)) around.at,
               BreakParent
             ]
           else
             [
               open.opening around close,
               Nest 2
                 (Doc.concat
                   (brokenItems
                     (list && [argument, ..rest].all Expr.plainItem)
                     around.inArm
                     True
                     open.trails
                     (around.at + 1)
                     [argument, ..rest])),
               SoftLine,
               close.leaf (around.next whole.trailsBeforeClose (whole.size - 1)) around.at
             ]))
        NoHeld
        (kinds => Ends kinds whole.trails)
        (fill =>
          stepDocConcat _ _ _
            (stepAllCons
              (open.opening around close)
              [
                Nest 2
                  (Fill
                    (cells (list && [argument, ..rest].all Expr.plainItem) around.inArm open.trails (around.at + 1) [
                      argument,
                      ..rest
                    ])),
                close.leaf (around.next whole.trailsBeforeClose (whole.size - 1)) around.at
              ]
              NoHeld
              (kinds => Ends kinds open.trails)
              (kinds => Ends kinds whole.trails)
              openS
              (stepAllCons
                (Nest 2
                  (Fill
                    (cells (list && [argument, ..rest].all Expr.plainItem) around.inArm open.trails (around.at + 1) [
                      argument,
                      ..rest
                    ])))
                [close.leaf (around.next whole.trailsBeforeClose (whole.size - 1)) around.at]
                (kinds => Ends kinds open.trails)
                (kinds => Ends kinds (itemsEnd open.trails [argument, ..rest]))
                (kinds => Ends kinds whole.trails)
                (stepWeaken
                  (Nest 2
                    (Fill
                      (cells (list && [argument, ..rest].all Expr.plainItem) around.inArm open.trails (around.at + 1) [
                        argument,
                        ..rest
                      ])))
                  (Starts False open.trails)
                  (kinds => Ends kinds open.trails)
                  (kinds => Ends kinds (itemsEnd open.trails [argument, ..rest]))
                  (kinds => Ends kinds (itemsEnd open.trails [argument, ..rest]))
                  (stepNest 2 _ _ _
                    (stepCells
                      (list && [argument, ..rest].all Expr.plainItem)
                      around.inArm
                      open.trails
                      (around.at + 1)
                      argument
                      rest
                      els))
                  (kinds good => endsStarts kinds _ good)
                  (kinds good => good))
                (stepAllOne
                  (close.leaf (around.next whole.trailsBeforeClose (whole.size - 1)) around.at)
                  (kinds => Ends kinds (itemsEnd open.trails [argument, ..rest]))
                  (kinds => Ends kinds whole.trails)
                  closeS))))
        (broken =>
          stepConcatIf whole.holdsTrailingComment
            [
              open.opening around close,
              Nest 2
                (Doc.concat
                  (brokenItems
                    (list && [argument, ..rest].all Expr.plainItem)
                    around.inArm
                    True
                    open.trails
                    (around.at + 1)
                    [argument, ..rest])),
              SoftLine,
              close.leaf (around.next whole.trailsBeforeClose (whole.size - 1)) around.at,
              BreakParent
            ]
            [
              open.opening around close,
              Nest 2
                (Doc.concat
                  (brokenItems
                    (list && [argument, ..rest].all Expr.plainItem)
                    around.inArm
                    True
                    open.trails
                    (around.at + 1)
                    [argument, ..rest])),
              SoftLine,
              close.leaf (around.next whole.trailsBeforeClose (whole.size - 1)) around.at
            ]
            NoHeld
            (kinds => Ends kinds whole.trails)
            (stepAllAppend
              [
                open.opening around close,
                Nest 2
                  (Doc.concat
                    (brokenItems
                      (list && [argument, ..rest].all Expr.plainItem)
                      around.inArm
                      True
                      open.trails
                      (around.at + 1)
                      [argument, ..rest])),
                SoftLine,
                close.leaf (around.next whole.trailsBeforeClose (whole.size - 1)) around.at
              ]
              [BreakParent]
              NoHeld
              (kinds => Ends kinds whole.trails)
              (kinds => Ends kinds whole.trails)
              (brokenParts open
                [argument, ..rest]
                close
                around
                (list && [argument, ..rest].all Expr.plainItem)
                False
                openS
                els
                closeS2)
              (stepAllOne BreakParent
                (kinds => Ends kinds whole.trails)
                (kinds => Ends kinds whole.trails)
                (stepBreakParent _)))
            (brokenParts open
              [argument, ..rest]
              close
              around
              (list && [argument, ..rest].all Expr.plainItem)
              False
              openS
              els
              closeS2))
