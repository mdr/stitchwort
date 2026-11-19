--| `laysKinds` of a call's document (SW-4116, `doc1Checks`' walk): the function and its arguments (`appDocs`), each
--| argument from where the one before ended, the last as it stands or opened. The theorems take what `Fmt.LaysEls`'s
--| induction on the expression proves (the arguments' items, `AllElStep`) as hypotheses.
namespace Fmt.LaysApp
import Std (Bool, Doc, Eq, List, Nat, Option, Text, Void)
import Std.Doc (..)
import Syntax (Expr, Word)
import Fmt (..)
import Fmt.LaysKinds (..)
import Fmt.LaysRules (..)
import Fmt.SpellProofs (..)
import Fmt.ToldDeclProofs (..)
import Fmt.AppHangProofs (lastArg)
import Fmt.TrailsProofs (Coded, appTrails)
import Fmt.LaysWords (..)
import Fmt.LaysBrackets (..)

--| Every bracket's items, from the facts about them: `Fmt.LaysEls.allElStep`.
def AllElStep: Prop :=
  ∀ (items: List Expr) => allWithin1 items = True
    → allSound items = True
    → allNonCloser items = True
    → allSpelled items = True
    → allLexical1 items = True
    → ItemsEl items

--| Documents spaced apart: the first, then each after a space.
theorem spacedCons ∀ (first: Doc) (rest: List Doc):
    spaced [first, ..rest] = Doc.concat [first, ..sepBefore (Doc.text " ") rest] :=
  rewrite joinedWithCons (Doc.text " ") first rest

--| Spaced documents: the first, then a chain of the rest.
theorem spacedStep ∀ (first: Doc) (rest: List Doc) (pre: Kinds → Bool) (middle trails: Bool)
    (head: Step first pre (kinds => Ends kinds middle))
    (chain: Chained rest middle trails):
    Step (spaced [first, ..rest]) pre (kinds => Ends kinds trails) :=
  rewrite spacedCons first rest then
    stepDocConcat _ _ _
      (stepAllCons first
        (sepBefore (Doc.text " ") rest)
        pre
        (kinds => Ends kinds middle)
        (kinds => Ends kinds trails)
        head
        (chainSeparated
          (Doc.text " ")
          rest
          middle
          trails
          (trails =>
            stepWeaken
              (Doc.text " ")
              (kinds => Ends kinds trails)
              (kinds => Ends kinds trails)
              (kinds => Ends kinds trails)
              (Starts False trails)
              (stepSpace trails)
              (kinds good => good)
              (kinds good => endsStarts kinds trails good))
          chain))

--| One more document at the end of a chain.
theorem chainedAppend ∀ (front: List Doc) (before middle trails: Bool) (last: Doc)
    (chain: Chained front before middle)
    (step: Step last (Starts False middle) (kinds => Ends kinds trails)):
    Chained (front ++ [last]) before trails :=
  match front with
    | [] => (trails, rewrite chain then step, byComputing)
    | [doc, ..rest] =>
      let (between, first, more) := chain
      (between, first, chainedAppend rest between middle trails last more step)

--| A chain cut after `count` documents: the two parts are chains, one after the other.
theorem chainedSplit ∀ (docs: List Doc) (count: Nat) (before trails: Bool)
    (chain: Chained docs before trails):
    ∃ (middle: Bool) => Chained (docs.take count) before middle ∧ Chained (docs.drop count) middle trails :=
  match count, docs with
    | Zero, docs => (before, byComputing, chain)
    | Succ n, [] => (before, byComputing, chain)
    | Succ n, [doc, ..rest] =>
      let (between, first, more) := chain
      let (middle, front, back) := chainedSplit rest n between trails more
      (middle, (between, first, front), back)

--| What follows a place that is no line start and holds no comment is a fresh start for a document from a chain.
theorem freshStarts ∀ (kinds: Kinds) (before: Bool) (fresh: Fresh kinds = True): Starts False before kinds = True :=
  match kinds, fresh with | { start = False, broken, mid, held = False }, _ => byComputing

--| A chain of documents each on a line of its own, below the line break.
theorem hardChain ∀ (docs: List Doc) (before trails: Bool)
    (chain: Chained docs before trails):
    StepAll (docs.concatMap (doc => [HardLine, doc])) (kinds => Ends kinds before) (kinds => Ends kinds trails) :=
  match docs with
    | [] => kinds holds => (kinds, byComputing, rewrite <- chain then holds)
    | [doc, ..rest] =>
      let (between, step, more) := chain
      stepAllCons HardLine
        [doc, ..rest.concatMap (doc => [HardLine, doc])]
        (kinds => Ends kinds before)
        Fresh
        (kinds => Ends kinds trails)
        (stepHardLineEnds before)
        (stepAllCons doc
          (rest.concatMap (doc => [HardLine, doc]))
          Fresh
          (kinds => Ends kinds between)
          (kinds => Ends kinds trails)
          (stepWeaken doc
            (Starts False before)
            Fresh
            (kinds => Ends kinds between)
            (kinds => Ends kinds between)
            step
            (kinds good => freshStarts kinds before good)
            (kinds good => good))
          (hardChain rest between trails more))

theorem itemsCoded ∀ (argument: Expr) (rest: List Expr)
    (within: allWithin1 [argument, ..rest] = True)
    (nonCloser: allNonCloser [argument, ..rest] = True):
    Coded (lastArg argument rest).words.reverse = True :=
  match rest with
    | [] => codedOf argument (Bool.andLeft within) (Bool.andLeft nonCloser)
    | [next, ..more] => itemsCoded next more (Bool.andRight within) (Bool.andRight nonCloser)

--| A bracket as a call's last argument: its own-line comments, then the bracket's content grouped, whether it stands
--| as it is or opened (`hard`).
--|
--| Proof idea: the comments (`leadingStep`), then the content from where they leave the printer (`LeadHeld`), which
--| `bracketContentStepFrom` takes as it is.
theorem huggedStep ∀ (list: Bool) (open: Word) (items: List Expr) (close: Word) (place: Around) (hard: Bool)
    (openSound: open.sound = True)
    (closeSound: close.sound = True)
    (openOpen: isCloserText open.text = False)
    (openComma: open.notComma = True)
    (closeShut: isCloserText close.text = True)
    (closes: Doc.Proofs.closesText close.text = True)
    (els: ItemsEl items)
    (stops: ∀ (argument: Expr) (rest: List Expr) => items = [argument, ..rest]
      → Coded (lastArg argument rest).words.reverse = True):
    Step
      (Doc.concat [
        Doc.concat (open.leading place place.at),
        Group (bracketContent list open items close { place | hoisted = True }) hard
      ])
      (Starts place.hoisted place.before)
      (kinds => Ends kinds (ListOf open items False close).trails) :=
  match open with
    | { text, comments = { above, after, blankBefore } } =>
      stepDocConcat _ _ _
        (stepAllCons
          (Doc.concat (Word.leading ({ text, comments = { above, after, blankBefore } }) place place.at))
          [
            Group
              (bracketContent list ({ text, comments = { above, after, blankBefore } }) items close { place |
                hoisted = True
              })
              hard
          ]
          (Starts place.hoisted place.before)
          (LeadHeld (!above.isEmpty && isCloserText text) place.before)
          (kinds => Ends kinds (ListOf ({ text, comments = { above, after, blankBefore } }) items False close).trails)
          (stepDocConcat _ _ _
            (leadingStep text above after blankBefore place place.at (Bool.andLeft (Bool.andRight openSound)) (closed =>
              Void.impossible (Bool.falseNotTrue (Eq.trans openOpen.flipped closed)))))
          (stepAllOne
            (Group
              (bracketContent list ({ text, comments = { above, after, blankBefore } }) items close { place |
                hoisted = True
              })
              hard)
            (LeadHeld (!above.isEmpty && isCloserText text) place.before)
            (kinds => Ends kinds (ListOf ({ text, comments = { above, after, blankBefore } }) items False close).trails)
            (stepGroup _ hard _ _
              (bracketContentStepFrom
                (LeadHeld (!above.isEmpty && isCloserText text) place.before)
                list
                ({ text, comments = { above, after, blankBefore } })
                items
                close
                { place | hoisted = True }
                byComputing
                openSound
                closeSound
                openOpen
                openComma
                closeShut
                closes
                els
                stops))))

--| A call's last argument, as it stands and opened.
--|
--| Proof idea: a tuple or list is a bracket (`huggedStep`); every other argument is laid as its own element, with no
--| hug.
theorem lastArgStep ∀ (argument: Expr) (place: Around)
    (within: argument.within1 = True)
    (sound: argument.sound = True)
    (nonCloser: argument.nonCloser = True)
    (spelled: argument.spelled = True)
    (lexical: argument.lexical1 = True)
    (each: ∀ (around: Around) => Step (argument.el around) (Starts around.hoisted around.before) (kinds =>
      Ends kinds argument.trails)) (inner: AllElStep):
    Step (lastArgument argument place).fst (Starts place.hoisted place.before) (kinds => Ends kinds argument.trails)
      ∧ (∀ (opened: Doc) => (lastArgument argument place).snd = Some opened
        → Step opened (Starts place.hoisted place.before) (kinds => Ends kinds argument.trails)) :=
  match argument, within with
    | Tuple open items comma close, within =>
      let els :=
        inner items within
          (Bool.andLeft (Bool.andRight sound))
          (Bool.andRight nonCloser)
          (Bool.andLeft (Bool.andRight spelled))
          (Bool.andRight (Bool.andRight lexical))
      let stops: ∀ (first: Expr) (rest: List Expr) => items = [first, ..rest]
        → Coded (lastArg first rest).words.reverse = True :=
        first rest same =>
          itemsCoded first rest
            (rewrite same at within then within)
            (rewrite same at nonCloser then Bool.andRight nonCloser)
      (
        huggedStep False open items close place
          (bracketContent False open items close { place | hoisted = True }).forcesBreak
          (Bool.andLeft sound)
          (Bool.andRight (Bool.andRight sound))
          (Bool.notTrue _ (Bool.andLeft nonCloser))
          (Bool.andLeft spelled)
          (Bool.andRight (Bool.andRight spelled))
          (closesOfParen close.text (Bool.andLeft (Bool.andRight lexical)))
          els
          stops,
        opened same =>
          rewrite <- Option.someInjective same then
            huggedStep False open items close place True
              (Bool.andLeft sound)
              (Bool.andRight (Bool.andRight sound))
              (Bool.notTrue _ (Bool.andLeft nonCloser))
              (Bool.andLeft spelled)
              (Bool.andRight (Bool.andRight spelled))
              (closesOfParen close.text (Bool.andLeft (Bool.andRight lexical)))
              els
              stops
      )
    | ListOf open items comma close, within =>
      let els :=
        inner items within
          (Bool.andLeft (Bool.andRight sound))
          (Bool.andRight nonCloser)
          (Bool.andLeft (Bool.andRight spelled))
          (Bool.andRight (Bool.andRight lexical))
      let stops: ∀ (first: Expr) (rest: List Expr) => items = [first, ..rest]
        → Coded (lastArg first rest).words.reverse = True :=
        first rest same =>
          itemsCoded first rest
            (rewrite same at within then within)
            (rewrite same at nonCloser then Bool.andRight nonCloser)
      (
        huggedStep True open items close place
          (bracketContent True open items close { place | hoisted = True }).forcesBreak
          (Bool.andLeft sound)
          (Bool.andRight (Bool.andRight sound))
          (Bool.notTrue _ (Bool.andLeft nonCloser))
          (Bool.andLeft spelled)
          (Bool.andRight (Bool.andRight spelled))
          (closesOfBracket close.text (Bool.andLeft (Bool.andRight lexical)))
          els
          stops,
        opened same =>
          rewrite <- Option.someInjective same then
            huggedStep True open items close place True
              (Bool.andLeft sound)
              (Bool.andRight (Bool.andRight sound))
              (Bool.notTrue _ (Bool.andLeft nonCloser))
              (Bool.andLeft spelled)
              (Bool.andRight (Bool.andRight spelled))
              (closesOfBracket close.text (Bool.andLeft (Bool.andRight lexical)))
              els
              stops
      )
    | Atom kind word, _ => (each place, opened same => (Option.noneNotSome opened same).impossible)
    | Prefix operator operand, _ => (each place, opened same => (Option.noneNotSome opened same).impossible)
    | Paren open (Atom k w) close, _ => (each place, opened same => (Option.noneNotSome opened same).impossible)
    | Paren open (Paren o i c) close, _ => (each place, opened same => (Option.noneNotSome opened same).impossible)
    | Paren open (Tuple o is m c) close, _ => (each place, opened same => (Option.noneNotSome opened same).impossible)
    | Paren open (ListOf o is m c) close, _ => (each place, opened same => (Option.noneNotSome opened same).impossible)
    | Paren open (App h xs) close, _ => (each place, opened same => (Option.noneNotSome opened same).impossible)
    | Paren open (Infix k l o r) close, _ => (each place, opened same => (Option.noneNotSome opened same).impossible)
    | Paren open (Prefix o x) close, _ => (each place, opened same => (Option.noneNotSome opened same).impossible)
    | App head arguments, _ => (each place, opened same => (Option.noneNotSome opened same).impossible)
    | Infix kind left operator right, _ => (each place, opened same => (Option.noneNotSome opened same).impossible)

--| A call's arguments after the function (`argumentDocs`): all but the last a chain from where the function ended, then
--| the last, and its hug, from where that chain ends; all end as the last argument does.
--|
--| Proof idea: induction on the arguments, each from `elStep` (`ItemsEl`) after the one before; the last from
--| `lastArgStep`.
theorem argsStep ∀ (arm: Bool) (previous: Expr) (at: Nat) (arguments: List Expr)
    (filled: arguments ≠ [])
    (within: allWithin1 arguments = True)
    (sound: allSound arguments = True)
    (nonCloser: allNonCloser arguments = True)
    (spelled: allSpelled arguments = True)
    (lexical: allLexical1 arguments = True) (inner: AllElStep):
    ∃ (middle: Bool) => Chained (argumentDocs arm previous at arguments).fst previous.trails middle
      ∧ Step
        ((argumentDocs arm previous at arguments).snd.getOrElse (Nothing, None)).fst
        (Starts False middle)
        (kinds => Ends kinds (itemsEnd previous.trails arguments))
      ∧ (∀ (opened: Doc) => ((argumentDocs arm previous at arguments).snd.getOrElse (Nothing, None)).snd = Some opened
        → Step opened (Starts False middle) (kinds => Ends kinds (itemsEnd previous.trails arguments))) :=
  match arguments with
    | [] => (filled byComputing).impossible
    | [argument] =>
      let place: Around := { before = previous.trails, hoisted = False, item = False, at, inArm = arm }
      let els := inner [argument] within sound nonCloser spelled lexical
      let (last, hug) :=
        lastArgStep argument place
          (Bool.andLeft within)
          (Bool.andLeft sound)
          (Bool.andLeft nonCloser)
          (Bool.andLeft spelled)
          (Bool.andLeft lexical)
          els.left
          inner
      (previous.trails, byComputing, last, hug)
    | [argument, next, ..more] =>
      let place: Around := { before = previous.trails, hoisted = False, item = False, at, inArm = arm }
      let els := inner [argument, next, ..more] within sound nonCloser spelled lexical
      let (middle, chain, last, hug) :=
        argsStep arm argument
          (at + argument.size)
          [next, ..more]
          (List.consNotNil next more)
          (Bool.andRight within)
          (Bool.andRight sound)
          (Bool.andRight nonCloser)
          (Bool.andRight spelled)
          (Bool.andRight lexical)
          inner
      (middle, (argument.trails, els.left place, chain), last, hug)

--| The layout of a call that breaks (`appFrom`): the function and the arguments kept on its line, the others each on a
--| line below.
def brokenDoc (id k: Nat) (betweenFront: Bool) (headDoc: Doc) (front: List Doc) (lastDoc: Doc): Doc := Doc.concat [
  if 1 + k > 2 && !betweenFront then IdGroup id (Nest 4 (Fill (([headDoc, ..front] ++ [lastDoc]).take (1 + k)))) False
  else spaced (([headDoc, ..front] ++ [lastDoc]).take (1 + k)),
  if 1 + k > 2 && !betweenFront then
    IfBroken id
      (Nest 4 (Doc.concat ((([headDoc, ..front] ++ [lastDoc]).drop (1 + k)).concatMap (doc => [HardLine, doc]))))
      (Nest 2 (Doc.concat ((([headDoc, ..front] ++ [lastDoc]).drop (1 + k)).concatMap (doc => [HardLine, doc]))))
  else Nest 2 (Doc.concat ((([headDoc, ..front] ++ [lastDoc]).drop (1 + k)).concatMap (doc => [HardLine, doc])))
]

--| The layout of a call that hugs its last argument (`appFrom`).
def hugDoc (headDoc: Doc) (front: List Doc) (opened: Doc): Doc :=
  Doc.concat [Flatten (spaced [headDoc, ..front]), Doc.text " ", opened]

--| A call hugging its last argument opened: the function and the arguments before it flattened, then the last.
theorem hugLayout ∀ (headDoc: Doc) (front: List Doc) (opened: Doc) (headTrails middle final: Bool)
    (headStep: Step headDoc NoHeld (kinds => Ends kinds headTrails))
    (chain: Chained front headTrails middle)
    (hugStep: Step opened (Starts False middle) (kinds => Ends kinds final)):
    Step (hugDoc headDoc front opened) NoHeld (kinds => Ends kinds final) :=
  stepDocConcat _ _ _
    (stepAllCons
      (Flatten (spaced [headDoc, ..front]))
      [Doc.text " ", opened]
      NoHeld
      (kinds => Ends kinds middle)
      (kinds => Ends kinds final)
      (stepFlatten _ _ _ (spacedStep headDoc front NoHeld headTrails middle headStep chain))
      (stepAllCons
        (Doc.text " ")
        [opened]
        (kinds => Ends kinds middle)
        (kinds => Ends kinds middle)
        (kinds => Ends kinds final)
        (stepSpace middle)
        (stepAllOne opened
          (kinds => Ends kinds middle)
          (kinds => Ends kinds final)
          (stepWeaken opened
            (Starts False middle)
            (kinds => Ends kinds middle)
            (kinds => Ends kinds final)
            (kinds => Ends kinds final)
            hugStep
            (kinds good => endsStarts kinds middle good)
            (kinds good => good)))))

theorem optionsTwo ∀ (one two: Doc) (pre: Kinds → Bool) (trails: Bool)
    (first: Step one pre (kinds => Ends kinds trails))
    (second: Step two pre (kinds => Ends kinds trails)):
    Options [one, two] pre trails :=
  (first, second, byComputing)

theorem optionsThree ∀ (one two three: Doc) (pre: Kinds → Bool) (trails: Bool)
    (first: Step one pre (kinds => Ends kinds trails))
    (second: Step two pre (kinds => Ends kinds trails))
    (third: Step three pre (kinds => Ends kinds trails)):
    Options [one, two, three] pre trails :=
  (first, second, third, byComputing)

--| A call from its parts (`appFrom`): each layout the printer may take passes the check.
theorem appFromStep ∀ (id k: Nat) (between betweenFront: Bool) (headDoc lastDoc: Doc) (front: List Doc)
    (hug: Option Doc) (headTrails middle final: Bool)
    (headStep: Step headDoc NoHeld (kinds => Ends kinds headTrails))
    (chain: Chained front headTrails middle)
    (lastStep: Step lastDoc (Starts False middle) (kinds => Ends kinds final))
    (hugStep: ∀ (opened: Doc) => hug = Some opened → Step opened (Starts False middle) (kinds => Ends kinds final)):
    Step (appFrom id (1 + k) between betweenFront headDoc front lastDoc hug).doc NoHeld (kinds => Ends kinds final) :=
  let whole: Chained (front ++ [lastDoc]) headTrails final :=
    chainedAppend front headTrails middle final lastDoc chain lastStep
  let flat := spacedStep headDoc (front ++ [lastDoc]) NoHeld headTrails final headStep whole
  match full: 1 + k == ([headDoc, ..front] ++ [lastDoc]).length with
    | True =>
      stepIte between
        (spaced [headDoc, ..front, lastDoc])
        (Nest 4 (Fill [headDoc, ..front, lastDoc]))
        NoHeld
        (kinds => Ends kinds final)
        (_ => flat)
        (_ => stepNest 4 _ _ _ (stepFill headDoc (front ++ [lastDoc]) NoHeld headTrails final headStep whole))
    | False =>
      let (split, kept, rest) := chainedSplit (front ++ [lastDoc]) k headTrails final whole
      let hard := stepDocConcat _ _ _ (hardChain ((front ++ [lastDoc]).drop k) split final rest)
      let broken: Step (brokenDoc id k betweenFront headDoc front lastDoc) NoHeld (kinds => Ends kinds final) :=
        stepDocConcat _ _ _
          (stepAllCons _ _ NoHeld
            (kinds => Ends kinds split)
            (kinds => Ends kinds final)
            (match fill: 1 + k > 2 && !betweenFront with
              | True =>
                stepNest 4
                  (Fill [headDoc, ..(front ++ [lastDoc]).take k]) _ _
                  (stepFill headDoc ((front ++ [lastDoc]).take k) NoHeld headTrails split headStep kept)
              | False => spacedStep headDoc ((front ++ [lastDoc]).take k) NoHeld headTrails split headStep kept)
            (stepAllOne _
              (kinds => Ends kinds split)
              (kinds => Ends kinds final)
              (match fill: 1 + k > 2 && !betweenFront with
                | True =>
                  stepIfBroken id _ _ (kinds => Ends kinds split) final (stepNest 4 _ _ _ hard) (stepNest 2 _ _ _ hard)
                | False => stepNest 2 _ _ _ hard)))
      let flatOption := stepFlatten (spaced [headDoc, ..front, lastDoc]) _ _ flat
      match hug with
        | None =>
          stepChoice
            (Flatten (spaced [headDoc, ..front, lastDoc]))
            [brokenDoc id k betweenFront headDoc front lastDoc]
            NoHeld
            final
            (optionsTwo _ _ NoHeld final flatOption broken)
        | Some opened =>
          stepChoice
            (Flatten (spaced [headDoc, ..front, lastDoc]))
            [hugDoc headDoc front opened, brokenDoc id k betweenFront headDoc front lastDoc]
            NoHeld
            final
            (optionsThree _ _ _ NoHeld final flatOption
              (hugLayout headDoc front opened headTrails middle final headStep chain (hugStep opened byComputing))
              broken)

--| A call's document (`appDocs`, its `Applied`'s `doc`) passes the check, from a place with no comment waiting.
--|
--| Proof idea: the function from its own step (`headEach`), the arguments from `argsStep`, and `appFromStep` over the
--| layouts `appFrom` chooses between; the call trails as its last argument does (`appTrails`, `itemsEndLast`).
theorem appStep ∀ (head: Expr) (arguments: List Expr) (around: Around)
    (filled: arguments ≠ [])
    (within: (App head arguments).within1 = True)
    (sound: (App head arguments).sound = True)
    (nonCloser: (App head arguments).nonCloser = True)
    (spelled: (App head arguments).spelled = True)
    (lexical: (App head arguments).lexical1 = True)
    (headEach: ∀ (around: Around) => Step (head.el around) (Starts around.hoisted around.before) (kinds =>
      Ends kinds head.trails)) (inner: AllElStep):
    Step (appDocs head arguments { around | hoisted = True }).doc NoHeld (kinds =>
      Ends kinds (App head arguments).trails) :=
  match arguments, filled with
    | [], filled => (filled byComputing).impossible
    | [argument, ..rest], _ =>
      let inside := { around | hoisted = True }
      let (middle, chain, last, hug) :=
        argsStep inside.inArm head
          (inside.at + head.size)
          [argument, ..rest]
          (List.consNotNil argument rest)
          (Bool.andRight within)
          (Bool.andRight sound)
          (Bool.andRight nonCloser)
          (Bool.andRight spelled)
          (Bool.andRight lexical)
          inner
      let headStep: Step (head.el inside) NoHeld (kinds => Ends kinds head.trails) :=
        stepWeaken
          (head.el inside)
          (Starts inside.hoisted inside.before)
          NoHeld
          (kinds => Ends kinds head.trails)
          (kinds => Ends kinds head.trails)
          (headEach inside)
          (kinds good => startsOfNoHeld kinds inside.before good)
          (kinds good => good)
      let same: itemsEnd head.trails [argument, ..rest] = (App head [argument, ..rest]).trails :=
        Eq.trans
          (itemsEndLast head.trails argument rest)
          (appTrails head argument rest
            (itemsCoded argument rest (Bool.andRight within) (Bool.andRight nonCloser))).flipped
      rewrite <- same then
        appFromStep
          (inside.at + 1)
          (keptFront head [argument, ..rest])
          (commentBetween head [argument, ..rest])
          (commentBetween head ([argument, ..rest].take (1 + keptFront head [argument, ..rest] - 1)))
          (head.el inside)
          ((argumentDocs inside.inArm head (inside.at + head.size) [argument, ..rest]).snd.getOrElse (
            Nothing,
            None
          )).fst
          (argumentDocs inside.inArm head (inside.at + head.size) [argument, ..rest]).fst
          ((argumentDocs inside.inArm head (inside.at + head.size) [argument, ..rest]).snd.getOrElse (
            Nothing,
            None
          )).snd
          head.trails
          middle
          (itemsEnd head.trails [argument, ..rest])
          headStep
          chain
          last
          hug
