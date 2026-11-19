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
import Fmt.LaysEls (notCommaOf, wordStep, openStep)

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

--| A bracket's closer, from where what stands before it ended.
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
    (Starts False (ListOf open items False close).trailsBeforeClose)
    (kinds => Ends kinds prior)
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
    (kinds good => endsStarts kinds _ (endsSame kinds _ _ same.flipped good))
    (kinds good =>
      endsSame kinds _ _ (bracketTrails (ListOf open items False close) open items close byComputing).flipped good)
