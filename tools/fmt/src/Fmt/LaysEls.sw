--| `laysKinds` of the rules' element documents (SW-4109, `doc1Checks`' walk, after `Fmt.LaysRules`'s tokens): a token
--| from a calm place, then the nodes of slice 1 by induction on the expression.
namespace Fmt.LaysEls
import Std (Bool, DecEq, Doc, Eq, List, Nat, Option, Text, Void)
import Std.Doc (..)
import Syntax (Expr, InfixKind, Word)
import Fmt (..)
import Fmt.LaysKinds (..)
import Fmt.LaysRules (..)
import Fmt.SpellProofs (..)
import Fmt.ToldDeclProofs (..)
import Fmt.AppHangProofs (lastArg)
import Fmt.TrailsProofs (Coded, atomCoded, parenTrails, trailsBackCoded)
import Fmt.LaysWords (..)
import Fmt.LaysBrackets (..)
import Fmt.LaysApp (ArgsEl, BracketEl, ItemsFacts, appStep)

--| What a paren holds and its two brackets.
--|
--| Proof idea: the opening bracket, what it holds from where the bracket ended, and the closing bracket from where
--| that ended; a comment waits at the end if the closer or what it holds trails.
theorem parenStep ∀ (open: Word) (inner: Expr) (close: Word) (around: Around)
    (hoisted: around.hoisted = True)
    (within: inner.within1 = True)
    (openSound: open.sound = True)
    (innerSound: inner.sound = True)
    (closeSound: close.sound = True)
    (openOpen: isCloserText open.text = False)
    (openComma: open.notComma = True)
    (closeShut: isCloserText close.text = True)
    (closeText: (close.text == ")") = True)
    (stops: Coded inner.words.reverse = True)
    (each: ∀ (around: Around) => Step (inner.el around) (Starts around.hoisted around.before) (kinds =>
      Ends kinds inner.trails)):
    Step (parenDoc open inner close around) NoHeld (kinds => Ends kinds (Paren open inner close).trails) :=
  stepDocConcat _ _ _
    (stepAllCons
      (open.opening around close)
      [parenInner inner (around.next open.trails 1), close.leaf (around.next inner.trails (1 + inner.size)) around.at]
      NoHeld
      (kinds => Ends kinds open.trails)
      (kinds => Ends kinds (Paren open inner close).trails)
      (stepWeaken
        (open.opening around close)
        Anything
        NoHeld
        (kinds => Ends kinds open.trails)
        (kinds => Ends kinds open.trails)
        (openStep open close around hoisted openSound openComma openOpen)
        (kinds good => anything kinds)
        (kinds good => good))
      (stepAllCons
        (parenInner inner (around.next open.trails 1))
        [close.leaf (around.next inner.trails (1 + inner.size)) around.at]
        (kinds => Ends kinds open.trails)
        (kinds => Ends kinds inner.trails)
        (kinds => Ends kinds (Paren open inner close).trails)
        (rewrite parenInnerEl inner (around.next open.trails 1) within then
          stepWeaken
            (inner.el (around.next open.trails 1))
            (Starts False open.trails)
            (kinds => Ends kinds open.trails)
            (kinds => Ends kinds inner.trails)
            (kinds => Ends kinds inner.trails)
            (each (around.next open.trails 1))
            (kinds good => endsStarts kinds _ good)
            (kinds good => good))
        (stepAllOne
          (close.leaf (around.next inner.trails (1 + inner.size)) around.at)
          (kinds => Ends kinds inner.trails)
          (kinds => Ends kinds (Paren open inner close).trails)
          (stepWeaken
            (close.leaf (around.next inner.trails (1 + inner.size)) around.at)
            (Starts False inner.trails)
            (kinds => Ends kinds inner.trails)
            (kinds => Ends kinds (close.trails || (isCloserText close.text && inner.trails)))
            (kinds => Ends kinds (Paren open inner close).trails)
            (wordStep close
              (around.next inner.trails (1 + inner.size))
              around.at
              closeSound
              (notCommaOf close (closerNotComma close.text closeShut))
              (closed => closesOfParen close.text closeText)
              (closed => byComputing))
            (kinds good => endsStarts kinds _ good)
            (kinds good =>
              endsSame kinds _ _
                (Eq.trans (rewrite closeShut) (parenTrails open inner close closeShut (Inr stops)).flipped)
                good)))))

theorem prefixTrails ∀ (operator: Word) (operand: Expr)
    (stops: Coded operand.words.reverse = True):
    (Prefix operator operand).trails = operand.trails :=
  rewrite List.reverseCons operator operand.words, trailsBackCoded operand.words.reverse [operator] stops

--| A prefix operator and its operand.
--|
--| Proof idea: the operator's token, a space or nothing, the operand from where the operator ended.
theorem prefixStep ∀ (operator: Word) (operand: Expr) (around: Around)
    (operatorSound: operator.sound = True)
    (operatorOpen: isCloserText operator.text = False)
    (operatorComma: operator.notComma = True)
    (stops: Coded operand.words.reverse = True)
    (each: ∀ (around: Around) => Step (operand.el around) (Starts around.hoisted around.before) (kinds =>
      Ends kinds operand.trails)):
    Step
      (Doc.concat [
        operator.leaf { around | hoisted = True } around.at,
        prefixGap operator operand,
        operand.el (around.next operator.trails 1)
      ])
      NoHeld
      (kinds => Ends kinds (Prefix operator operand).trails) :=
  stepDocConcat _ _ _
    (stepAllCons
      (operator.leaf { around | hoisted = True } around.at)
      [prefixGap operator operand, operand.el (around.next operator.trails 1)]
      NoHeld
      (kinds => Ends kinds operator.trails)
      (kinds => Ends kinds (Prefix operator operand).trails)
      (stepWeaken
        (operator.leaf { around | hoisted = True } around.at)
        (Starts True around.before)
        NoHeld
        (kinds => Ends kinds operator.trails)
        (kinds => Ends kinds operator.trails)
        (plainWordStep operator { around | hoisted = True } around.at operatorSound operatorComma operatorOpen)
        (kinds good => startsOfNoHeld kinds around.before good)
        (kinds good => good))
      (stepAllCons
        (prefixGap operator operand)
        [operand.el (around.next operator.trails 1)]
        (kinds => Ends kinds operator.trails)
        (kinds => Ends kinds operator.trails)
        (kinds => Ends kinds (Prefix operator operand).trails)
        (spaceOpt _ operator.trails)
        (stepAllOne
          (operand.el (around.next operator.trails 1))
          (kinds => Ends kinds operator.trails)
          (kinds => Ends kinds (Prefix operator operand).trails)
          (stepWeaken
            (operand.el (around.next operator.trails 1))
            (Starts False operator.trails)
            (kinds => Ends kinds operator.trails)
            (kinds => Ends kinds operand.trails)
            (kinds => Ends kinds (Prefix operator operand).trails)
            (each (around.next operator.trails 1))
            (kinds good => endsStarts kinds _ good)
            (kinds good => endsSame kinds _ _ (prefixTrails operator operand stops).flipped good)))))

-- Operator chains.

theorem infixTrails ∀ (kind: InfixKind) (left: Expr) (operator: Word) (right: Expr)
    (stops: Coded right.words.reverse = True):
    (Infix kind left operator right).trails = right.trails :=
  rewrite List.reverseAppend left.words [operator, ..right.words],
      List.reverseCons operator right.words,
      List.appendAssoc right.words.reverse [operator] left.words.reverse,
      trailsBackCoded right.words.reverse ([operator] ++ left.words.reverse) stops

theorem appendCons ∀ (front: List Doc) (next: Doc) (rest: List Doc):
    ∃ (head: Doc) (tail: List Doc) => front ++ [next, ..rest] = [head, ..tail] :=
  match front with
    | [] => (next, rest, byComputing)
    | [doc, ..more] => (doc, more ++ [next, ..rest], byComputing)

theorem chainOfKinds ∀ (arms: Bool) (head: Doc) (tail: List Doc) (kinds: Kinds):
    laysKinds (chainOf arms [head, ..tail]) kinds = laysAllKinds [head, ..tail] kinds :=
  Eq.trans
    (concatKinds [head, Nest (if arms then 0 else 2) (Doc.concat tail)] kinds)
    (match found: laysKinds head kinds with
      | None => byComputing
      | Some middle =>
        Eq.trans (allSingle (Nest (if arms then 0 else 2) (Doc.concat tail)) middle) (concatKinds tail middle))

--| A chain's document passes from where its links do.
theorem stepChainOf ∀ (arms: Bool) (links: List Doc) (pre post: Kinds → Bool)
    (nonEmpty: ∃ (head: Doc) (tail: List Doc) => links = [head, ..tail])
    (all: StepAll links pre post):
    Step (chainOf arms links) pre post :=
  match nonEmpty with
    | (head, tail, same) =>
      let cons := rewrite same at all then all
      rewrite same then
        kinds holds =>
          let (after, found, good) := cons kinds holds
          (after, Eq.trans (chainOfKinds arms head tail kinds) found, good)

-- Elements.

--| The rules' document for every element of slice 1 passes the check, and leaves words on the line, a comment
--| waiting only if the element ends its line with one.
--|
--| Proof idea: induction on the expression. A token is `plainWordStep`; every node but a token is its first token's
--| own-line comments (`framedStep`) and its parts (`parenStep`, `prefixStep`, and for the rest the open lemmas
--| below), each part after the one before from where that left the printer.
theorem elStep ∀ (expr: Expr) (around: Around)
    (within: expr.within1 = True)
    (sound: expr.sound = True)
    (nonCloser: expr.nonCloser = True)
    (spelled: expr.spelled = True)
    (lexical: expr.lexical1 = True):
    Step (expr.el around) (Starts around.hoisted around.before) (kinds => Ends kinds expr.trails) :=
  match expr with
    | Atom kind word =>
      stepWeaken
        (word.leaf around around.at)
        (Starts around.hoisted around.before)
        (Starts around.hoisted around.before)
        (kinds => Ends kinds word.trails)
        (kinds => Ends kinds (Atom kind word).trails)
        (plainWordStep word around around.at sound spelled (Bool.notTrue _ nonCloser))
        (kinds good => good)
        (kinds good => endsSame kinds _ _ (atomTrails kind word (Bool.notTrue _ nonCloser)).flipped good)
    | Paren open inner close =>
      framedStep
        (Paren open inner close).firstWord
        around
        (parenDoc open inner close { around | hoisted = True })
        (Paren open inner close).trails
        (rewrite firstWordLead (Paren open inner close) within then leadSound (Paren open inner close) sound)
        (rewrite firstWordLead (Paren open inner close) within then leadNonCloser (Paren open inner close) nonCloser)
        (parenStep open inner close
          { around | hoisted = True }
          byComputing
          within
          (Bool.andLeft sound)
          (Bool.andLeft (Bool.andRight sound))
          (Bool.andRight (Bool.andRight sound))
          (Bool.notTrue _ (Bool.andLeft nonCloser))
          (Bool.andLeft spelled)
          (Bool.andRight (Bool.andRight spelled))
          (Bool.andLeft (Bool.andRight lexical))
          (codedOf inner within (Bool.andRight nonCloser))
          (inside =>
            elStep inner inside within
              (Bool.andLeft (Bool.andRight sound))
              (Bool.andRight nonCloser)
              (Bool.andLeft (Bool.andRight spelled))
              (Bool.andRight (Bool.andRight lexical))))
    | Tuple open items comma close =>
      framedStep
        (Tuple open items comma close).firstWord
        around
        (commaBracket (list := False) open items close { around | hoisted = True })
        (Tuple open items comma close).trails
        (rewrite firstWordLead (Tuple open items comma close) within then
          leadSound (Tuple open items comma close) sound)
        (rewrite firstWordLead (Tuple open items comma close) within then
          leadNonCloser (Tuple open items comma close) nonCloser)
        (stepGroup
          (bracketContent False open items close { around | hoisted = True })
          (bracketContent False open items close { around | hoisted = True }).forcesBreak
          NoHeld
          (kinds => Ends kinds (Tuple open items comma close).trails)
          (bracketContentStep False open items close
            { around | hoisted = True }
            byComputing
            (Bool.andLeft sound)
            (Bool.andRight (Bool.andRight sound))
            (Bool.notTrue _ (Bool.andLeft nonCloser))
            (Bool.andLeft spelled)
            (Bool.andRight (Bool.andRight spelled))
            (closesOfParen close.text (Bool.andLeft (Bool.andRight lexical)))
            (allElStep items within
              (Bool.andLeft (Bool.andRight sound))
              (Bool.andRight nonCloser)
              (Bool.andLeft (Bool.andRight spelled))
              (Bool.andRight (Bool.andRight lexical)))
            (argument rest same =>
              lastCoded argument rest
                (rewrite same at within then within)
                (rewrite same at nonCloser then Bool.andRight nonCloser))))
    | ListOf open items comma close =>
      framedStep
        (ListOf open items comma close).firstWord
        around
        (commaBracket (list := True) open items close { around | hoisted = True })
        (ListOf open items comma close).trails
        (rewrite firstWordLead (ListOf open items comma close) within then
          leadSound (ListOf open items comma close) sound)
        (rewrite firstWordLead (ListOf open items comma close) within then
          leadNonCloser (ListOf open items comma close) nonCloser)
        (stepGroup
          (bracketContent True open items close { around | hoisted = True })
          (bracketContent True open items close { around | hoisted = True }).forcesBreak
          NoHeld
          (kinds => Ends kinds (ListOf open items comma close).trails)
          (bracketContentStep True open items close
            { around | hoisted = True }
            byComputing
            (Bool.andLeft sound)
            (Bool.andRight (Bool.andRight sound))
            (Bool.notTrue _ (Bool.andLeft nonCloser))
            (Bool.andLeft spelled)
            (Bool.andRight (Bool.andRight spelled))
            (closesOfBracket close.text (Bool.andLeft (Bool.andRight lexical)))
            (allElStep items within
              (Bool.andLeft (Bool.andRight sound))
              (Bool.andRight nonCloser)
              (Bool.andLeft (Bool.andRight spelled))
              (Bool.andRight (Bool.andRight lexical)))
            (argument rest same =>
              lastCoded argument rest
                (rewrite same at within then within)
                (rewrite same at nonCloser then Bool.andRight nonCloser))))
    | App head arguments =>
      match arguments with
        | [] => ?
        | [argument, ..rest] =>
          framedStep
            (App head [argument, ..rest]).firstWord
            around
            (appDocs head [argument, ..rest] { around | hoisted = True }).doc
            (App head [argument, ..rest]).trails
            (rewrite firstWordLead (App head [argument, ..rest]) within then
              leadSound (App head [argument, ..rest]) sound)
            (rewrite firstWordLead (App head [argument, ..rest]) within then
              leadNonCloser (App head [argument, ..rest]) nonCloser)
            (appStep head
              [argument, ..rest]
              around
              (List.consNotNil argument rest)
              within
              sound
              nonCloser
              spelled
              lexical
              (inside =>
                elStep head inside
                  (Bool.andLeft within)
                  (Bool.andLeft sound)
                  (Bool.andLeft nonCloser)
                  (Bool.andLeft spelled)
                  (Bool.andLeft lexical))
              (allElStep
                [argument, ..rest]
                (Bool.andRight within)
                (Bool.andRight sound)
                (Bool.andRight nonCloser)
                (Bool.andRight spelled)
                (Bool.andRight lexical))
              (argsBracketEl [argument, ..rest] (Bool.andRight within)))
    | Prefix operator operand =>
      framedStep
        (Prefix operator operand).firstWord
        around
        (Doc.concat [
          operator.leaf { around | hoisted = True } around.at,
          prefixGap operator operand,
          operand.el (around.next operator.trails 1)
        ])
        (Prefix operator operand).trails
        (rewrite firstWordLead (Prefix operator operand) within then leadSound (Prefix operator operand) sound)
        (rewrite firstWordLead (Prefix operator operand) within then leadNonCloser (Prefix operator operand) nonCloser)
        (prefixStep operator operand around
          (Bool.andLeft sound)
          (Bool.notTrue _ (Bool.andLeft nonCloser))
          (Bool.andLeft spelled)
          (codedOf operand (Bool.andLeft within) (Bool.andRight nonCloser))
          (next =>
            elStep operand next
              (Bool.andLeft within)
              (Bool.andRight sound)
              (Bool.andRight nonCloser)
              (Bool.andRight spelled)
              (Bool.andRight lexical)))
    | Infix kind left operator right =>
      match kind with
        | InfixBinary =>
          framedStep
            (Infix InfixBinary left operator right).firstWord
            around
            (chain (Infix InfixBinary left operator right).chainLevel left operator right { around | hoisted = True })
            (Infix InfixBinary left operator right).trails
            (rewrite firstWordLead (Infix InfixBinary left operator right) within then
              leadSound (Infix InfixBinary left operator right) sound)
            (rewrite firstWordLead (Infix InfixBinary left operator right) within then
              leadNonCloser (Infix InfixBinary left operator right) nonCloser)
            (stepChainOf
              (left.opensArms (Infix InfixBinary left operator right).chainLevel)
              (chainLinks (Infix InfixBinary left operator right).chainLevel True left operator right { around |
                hoisted = True
              })
              NoHeld
              (kinds => Ends kinds (Infix InfixBinary left operator right).trails)
              (appendCons
                (linkDocs (Infix InfixBinary left operator right).chainLevel True left { around | hoisted = True })
                Line
                [
                  operator.leaf
                    (({ around | hoisted = True }).next left.trails left.size)
                    (({ around | hoisted = True }).next left.trails left.size).at,
                  ..chainRight
                    (Infix InfixBinary left operator right).chainLevel
                    right
                    (({ around | hoisted = True }).next operator.trails (left.size + 1))
                ])
              (stepAllWeaken
                (chainLinks (Infix InfixBinary left operator right).chainLevel True left operator right { around |
                  hoisted = True
                })
                (Starts True around.before)
                NoHeld
                (kinds => Ends kinds right.trails)
                (kinds => Ends kinds (Infix InfixBinary left operator right).trails)
                (chainLinksStep
                  (Infix InfixBinary left operator right).chainLevel
                  True
                  left
                  operator
                  right
                  { around | hoisted = True }
                  (Bool.andLeft within)
                  (Bool.andLeft (Bool.andRight within))
                  (Bool.andLeft sound)
                  (Bool.andLeft (Bool.andRight sound))
                  (Bool.andRight (Bool.andRight sound))
                  (Bool.andLeft nonCloser)
                  (Bool.notTrue _ (Bool.andLeft (Bool.andRight nonCloser)))
                  (Bool.andRight (Bool.andRight nonCloser))
                  (Bool.andLeft spelled)
                  (Bool.andLeft (Bool.andRight spelled))
                  (Bool.andRight (Bool.andRight spelled))
                  (Bool.andLeft lexical)
                  (Bool.andRight (Bool.andRight lexical)))
                (kinds good => startsOfNoHeld kinds around.before good)
                (kinds good =>
                  endsSame kinds _ _
                    (infixTrails InfixBinary left operator right
                      (codedOf right
                        (Bool.andLeft (Bool.andRight within))
                        (Bool.andRight (Bool.andRight nonCloser)))).flipped
                    good)))
        | InfixArrow =>
          framedStep
            (Infix InfixArrow left operator right).firstWord
            around
            (chain (Infix InfixArrow left operator right).chainLevel left operator right { around | hoisted = True })
            (Infix InfixArrow left operator right).trails
            (rewrite firstWordLead (Infix InfixArrow left operator right) within then
              leadSound (Infix InfixArrow left operator right) sound)
            (rewrite firstWordLead (Infix InfixArrow left operator right) within then
              leadNonCloser (Infix InfixArrow left operator right) nonCloser)
            (stepChainOf
              (left.opensArms (Infix InfixArrow left operator right).chainLevel)
              (chainLinks (Infix InfixArrow left operator right).chainLevel True left operator right { around |
                hoisted = True
              })
              NoHeld
              (kinds => Ends kinds (Infix InfixArrow left operator right).trails)
              (appendCons
                (linkDocs (Infix InfixArrow left operator right).chainLevel True left { around | hoisted = True })
                Line
                [
                  operator.leaf
                    (({ around | hoisted = True }).next left.trails left.size)
                    (({ around | hoisted = True }).next left.trails left.size).at,
                  ..chainRight
                    (Infix InfixArrow left operator right).chainLevel
                    right
                    (({ around | hoisted = True }).next operator.trails (left.size + 1))
                ])
              (stepAllWeaken
                (chainLinks (Infix InfixArrow left operator right).chainLevel True left operator right { around |
                  hoisted = True
                })
                (Starts True around.before)
                NoHeld
                (kinds => Ends kinds right.trails)
                (kinds => Ends kinds (Infix InfixArrow left operator right).trails)
                (chainLinksStep
                  (Infix InfixArrow left operator right).chainLevel
                  True
                  left
                  operator
                  right
                  { around | hoisted = True }
                  (Bool.andLeft within)
                  (Bool.andLeft (Bool.andRight within))
                  (Bool.andLeft sound)
                  (Bool.andLeft (Bool.andRight sound))
                  (Bool.andRight (Bool.andRight sound))
                  (Bool.andLeft nonCloser)
                  (Bool.notTrue _ (Bool.andLeft (Bool.andRight nonCloser)))
                  (Bool.andRight (Bool.andRight nonCloser))
                  (Bool.andLeft spelled)
                  (Bool.andLeft (Bool.andRight spelled))
                  (Bool.andRight (Bool.andRight spelled))
                  (Bool.andLeft lexical)
                  (Bool.andRight (Bool.andRight lexical)))
                (kinds good => startsOfNoHeld kinds around.before good)
                (kinds good =>
                  endsSame kinds _ _
                    (infixTrails InfixArrow left operator right
                      (codedOf right
                        (Bool.andLeft (Bool.andRight within))
                        (Bool.andRight (Bool.andRight nonCloser)))).flipped
                    good)))
        | _ => cases

--| The links of a chain: its first operand's, then a line break, the operator and what follows it.
theorem chainLinksStep ∀ (level: Option Nat) (first: Bool) (left: Expr) (operator: Word) (right: Expr) (around: Around)
    (leftWithin: left.within1 = True)
    (rightWithin: right.within1 = True)
    (leftSound: left.sound = True)
    (operatorSound: operator.sound = True)
    (rightSound: right.sound = True)
    (leftNonCloser: left.nonCloser = True)
    (operatorOpen: isCloserText operator.text = False)
    (rightNonCloser: right.nonCloser = True)
    (leftSpelled: left.spelled = True)
    (operatorComma: operator.notComma = True)
    (rightSpelled: right.spelled = True)
    (leftLexical: left.lexical1 = True)
    (rightLexical: right.lexical1 = True):
    StepAll (chainLinks level first left operator right around) (Starts around.hoisted around.before) (kinds =>
      Ends kinds right.trails) :=
  stepAllAppend
    (linkDocs level first left around)
    [
      Line,
      operator.leaf (around.next left.trails left.size) (around.next left.trails left.size).at,
      ..chainRight level right (around.next operator.trails (left.size + 1))
    ]
    (Starts around.hoisted around.before)
    (kinds => Ends kinds left.trails)
    (kinds => Ends kinds right.trails)
    (linkDocsStep level first left around leftWithin leftSound leftNonCloser leftSpelled leftLexical)
    (stepAllCons Line
      [
        operator.leaf (around.next left.trails left.size) (around.next left.trails left.size).at,
        ..chainRight level right (around.next operator.trails (left.size + 1))
      ]
      (kinds => Ends kinds left.trails)
      (Starts False left.trails)
      (kinds => Ends kinds right.trails)
      (stepLine left.trails)
      (stepAllCons
        (operator.leaf (around.next left.trails left.size) (around.next left.trails left.size).at)
        (chainRight level right (around.next operator.trails (left.size + 1)))
        (Starts False left.trails)
        (kinds => Ends kinds operator.trails)
        (kinds => Ends kinds right.trails)
        (plainWordStep operator
          (around.next left.trails left.size)
          (around.next left.trails left.size).at
          operatorSound
          operatorComma
          operatorOpen)
        (chainRightStep level right
          (around.next operator.trails (left.size + 1))
          rightWithin
          rightSound
          rightNonCloser
          rightSpelled
          rightLexical)))

--| What follows a chain's operator: a space and the right operand.
theorem chainRightStep ∀ (level: Option Nat) (right: Expr) (around: Around)
    (within: right.within1 = True)
    (sound: right.sound = True)
    (nonCloser: right.nonCloser = True)
    (spelled: right.spelled = True)
    (lexical: right.lexical1 = True):
    StepAll (chainRight level right around) (kinds => Ends kinds around.before) (kinds => Ends kinds right.trails) :=
  match right with
    | Block _ _ _ => cases
    | _ =>
      stepAllCons
        (Doc.text " ")
        (linkDocs level False right around)
        (kinds => Ends kinds around.before)
        (kinds => Ends kinds around.before)
        (kinds => Ends kinds right.trails)
        (stepSpace around.before)
        (stepAllWeaken
          (linkDocs level False right around)
          (Starts around.hoisted around.before)
          (kinds => Ends kinds around.before)
          (kinds => Ends kinds right.trails)
          (kinds => Ends kinds right.trails)
          (linkDocsStep level False right around within sound nonCloser spelled lexical)
          (kinds good => endsStartsAny kinds around.hoisted around.before good)
          (kinds good => good))

--| An operand of a chain: its links if it is a chain of the level, else its element.
theorem linkDocsStep ∀ (level: Option Nat) (first: Bool) (expr: Expr) (around: Around)
    (within: expr.within1 = True)
    (sound: expr.sound = True)
    (nonCloser: expr.nonCloser = True)
    (spelled: expr.spelled = True)
    (lexical: expr.lexical1 = True):
    StepAll (linkDocs level first expr around) (Starts around.hoisted around.before) (kinds =>
      Ends kinds expr.trails) :=
  match expr with
    | Infix kind left operator right =>
      match kind with
        | InfixBinary =>
          match (Infix InfixBinary left operator right).inChain level with
            | True =>
              stepAllWeaken
                (chainLinks level first left operator right around)
                (Starts around.hoisted around.before)
                (Starts around.hoisted around.before)
                (kinds => Ends kinds right.trails)
                (kinds => Ends kinds (Infix InfixBinary left operator right).trails)
                (chainLinksStep level first left operator right around
                  (Bool.andLeft within)
                  (Bool.andLeft (Bool.andRight within))
                  (Bool.andLeft sound)
                  (Bool.andLeft (Bool.andRight sound))
                  (Bool.andRight (Bool.andRight sound))
                  (Bool.andLeft nonCloser)
                  (Bool.notTrue _ (Bool.andLeft (Bool.andRight nonCloser)))
                  (Bool.andRight (Bool.andRight nonCloser))
                  (Bool.andLeft spelled)
                  (Bool.andLeft (Bool.andRight spelled))
                  (Bool.andRight (Bool.andRight spelled))
                  (Bool.andLeft lexical)
                  (Bool.andRight (Bool.andRight lexical)))
                (kinds good => good)
                (kinds good =>
                  endsSame kinds _ _
                    (infixTrails InfixBinary left operator right
                      (codedOf right
                        (Bool.andLeft (Bool.andRight within))
                        (Bool.andRight (Bool.andRight nonCloser)))).flipped
                    good)
            | False =>
              stepAllOne
                ((Infix InfixBinary left operator right).el around)
                (Starts around.hoisted around.before)
                (kinds => Ends kinds (Infix InfixBinary left operator right).trails)
                (elStep (Infix InfixBinary left operator right) around within sound nonCloser spelled lexical)
        | InfixArrow =>
          match (Infix InfixArrow left operator right).inChain level with
            | True =>
              stepAllWeaken
                (chainLinks level first left operator right around)
                (Starts around.hoisted around.before)
                (Starts around.hoisted around.before)
                (kinds => Ends kinds right.trails)
                (kinds => Ends kinds (Infix InfixArrow left operator right).trails)
                (chainLinksStep level first left operator right around
                  (Bool.andLeft within)
                  (Bool.andLeft (Bool.andRight within))
                  (Bool.andLeft sound)
                  (Bool.andLeft (Bool.andRight sound))
                  (Bool.andRight (Bool.andRight sound))
                  (Bool.andLeft nonCloser)
                  (Bool.notTrue _ (Bool.andLeft (Bool.andRight nonCloser)))
                  (Bool.andRight (Bool.andRight nonCloser))
                  (Bool.andLeft spelled)
                  (Bool.andLeft (Bool.andRight spelled))
                  (Bool.andRight (Bool.andRight spelled))
                  (Bool.andLeft lexical)
                  (Bool.andRight (Bool.andRight lexical)))
                (kinds good => good)
                (kinds good =>
                  endsSame kinds _ _
                    (infixTrails InfixArrow left operator right
                      (codedOf right
                        (Bool.andLeft (Bool.andRight within))
                        (Bool.andRight (Bool.andRight nonCloser)))).flipped
                    good)
            | False =>
              stepAllOne
                ((Infix InfixArrow left operator right).el around)
                (Starts around.hoisted around.before)
                (kinds => Ends kinds (Infix InfixArrow left operator right).trails)
                (elStep (Infix InfixArrow left operator right) around within sound nonCloser spelled lexical)
        | _ => cases
    | Match _ _ _ _ => cases
    | _ =>
      stepAllOne
        (expr.el around)
        (Starts around.hoisted around.before)
        (kinds => Ends kinds expr.trails)
        (elStep expr around within sound nonCloser spelled lexical)

theorem lastCoded ∀ (argument: Expr) (rest: List Expr)
    (within: allWithin1 [argument, ..rest] = True)
    (nonCloser: allNonCloser [argument, ..rest] = True):
    Coded (lastArg argument rest).words.reverse = True :=
  match rest with
    | [] => codedOf argument (Bool.andLeft within) (Bool.andLeft nonCloser)
    | [next, ..more] => lastCoded next more (Bool.andRight within) (Bool.andRight nonCloser)

--| Every item of a bracket passes the check.
theorem allElStep ∀ (items: List Expr)
    (within: allWithin1 items = True)
    (sound: allSound items = True)
    (nonCloser: allNonCloser items = True)
    (spelled: allSpelled items = True)
    (lexical: allLexical1 items = True):
    ItemsEl items :=
  match items with
    | [] => byComputing
    | [item, ..rest] => (
      around =>
        elStep item around
          (Bool.andLeft within)
          (Bool.andLeft sound)
          (Bool.andLeft nonCloser)
          (Bool.andLeft spelled)
          (Bool.andLeft lexical),
      allElStep rest
        (Bool.andRight within)
        (Bool.andRight sound)
        (Bool.andRight nonCloser)
        (Bool.andRight spelled)
        (Bool.andRight lexical)
    )

--| What an argument that is a bracket needs to hug: its items' steps.
theorem bracketEl ∀ (argument: Expr) (within: argument.within1 = True): BracketEl argument :=
  match argument, within with
    | Tuple open items comma close, within => within sound nonCloser spelled lexical =>
      allElStep items within sound nonCloser spelled lexical
    | ListOf open items comma close, within => within sound nonCloser spelled lexical =>
      allElStep items within sound nonCloser spelled lexical
    | Atom kind word, _ => byComputing
    | Prefix operator operand, _ => byComputing
    | Paren open inner close, _ => byComputing
    | App head arguments, _ => byComputing
    | Infix kind left operator right, _ => byComputing

--| Each argument's bracket steps.
theorem argsBracketEl ∀ (arguments: List Expr) (within: allWithin1 arguments = True): ArgsEl arguments :=
  match arguments with
    | [] => byComputing
    | [argument, ..rest] => (bracketEl argument (Bool.andLeft within), argsBracketEl rest (Bool.andRight within))
