--| `laysKinds` of the rules' element documents (SW-4109, `doc1Checks`' walk, after `Fmt.LaysRules`'s tokens): a token
--| from a calm place, then the nodes of slice 1 by induction on the expression.
namespace Fmt.LaysEls
import Std (Bool, DecEq, Doc, Eq, List, Nat, Option, Text, Void)
import Std.Doc (..)
import Syntax (Expr, Word)
import Fmt (..)
import Fmt.LaysKinds (..)
import Fmt.LaysRules (..)
import Fmt.SpellProofs (..)
import Fmt.ToldDeclProofs (..)
import Fmt.TrailsProofs (Coded, atomCoded, parenTrails, trailsBackCoded)

--| Where an element starts, from where its predecessor ended: the predecessor's trailing comment is the one waiting.
theorem endsStarts ∀ (kinds: Kinds) (trails: Bool) (ends: Ends kinds trails = True): Starts False trails kinds = True :=
  match kinds, trails, ends with
    | { start = False, broken = False, mid, held = False }, _, _ => byComputing
    | { start = False, broken = False, mid, held = True }, True, _ => byComputing

theorem noHeldStarts ∀ (kinds: Kinds) (hoisted before: Bool)
    (clear: NoHeld kinds = True):
    (!kinds.held || before) = True :=
  match kinds, clear with | { start, broken, mid, held = False }, _ => byComputing

--| A place with no comment waiting starts an element whose first token's comments are written elsewhere.
theorem startsOfNoHeld ∀ (kinds: Kinds) (before: Bool) (clear: NoHeld kinds = True): Starts True before kinds = True :=
  match kinds, clear with | { start, broken, mid, held = False }, _ => byComputing

theorem parenInnerEl ∀ (inner: Expr) (around: Around)
    (within: inner.within1 = True):
    parenInner inner around = inner.el around :=
  match inner with
    | Atom kind word => byComputing
    | Paren open middle close => byComputing
    | Tuple open items comma close => byComputing
    | ListOf open items comma close => byComputing
    | App head arguments => byComputing
    | Infix kind left operator right => byComputing
    | Prefix operator operand => byComputing

theorem closesOfParen ∀ (text: Text) (is: (text == ")") = True): Doc.Proofs.closesText text = True := rewrite is

theorem closesOfBracket ∀ (text: Text) (is: (text == "]") = True): Doc.Proofs.closesText text = True :=
  match text == ")" with
    | True => byComputing
    | False => rewrite is

theorem spaceOpt ∀ (flag trails: Bool):
    Step (if flag then Doc.text " " else Nothing) (kinds => Ends kinds trails) (kinds => Ends kinds trails) :=
  match flag with
    | True => kinds holds =>
      match kinds, holds with
        | { start = False, broken = False, mid, held }, holds =>
          ({ start = False, broken = False, mid, held }, byComputing, holds)
    | False => kinds holds => (kinds, byComputing, holds)

-- Tokens.

--| A token, from what its record holds.
theorem wordStep ∀ (word: Word) (around: Around) (key: Nat)
    (sound: word.sound = True)
    (comma: word.notComma = True)
    (closes: isCloserText word.text = True → Doc.Proofs.closesText word.text = True)
    (home: isCloserText word.text = True → around.hoisted = False):
    Step (word.leaf around key) (Starts around.hoisted around.before) (kinds =>
      Ends kinds (word.trails || (isCloserText word.text && around.before))) :=
  match word with
    | { text, comments = { above, after, blankBefore } } =>
      leafStep text above after blankBefore around key
        (Bool.notTrue _ (Bool.andLeft sound))
        (Bool.andLeft (Bool.andRight sound))
        (Bool.andRight (Bool.andRight sound))
        (Bool.notTrue _ comma)
        closes
        home

--| A token that is no closer leaves words on its line, a comment waiting if it has a trailing one.
theorem plainWordStep ∀ (word: Word) (around: Around) (key: Nat)
    (sound: word.sound = True)
    (comma: word.notComma = True)
    (open: isCloserText word.text = False):
    Step (word.leaf around key) (Starts around.hoisted around.before) (kinds => Ends kinds word.trails) :=
  stepWeaken
    (word.leaf around key)
    (Starts around.hoisted around.before)
    (Starts around.hoisted around.before)
    (kinds => Ends kinds (word.trails || (isCloserText word.text && around.before)))
    (kinds => Ends kinds word.trails)
    (wordStep word around key sound comma
      (closed => Void.impossible (Bool.falseNotTrue (Eq.trans open.flipped closed)))
      (closed => Void.impossible (Bool.falseNotTrue (Eq.trans open.flipped closed))))
    (kinds good => good)
    (kinds good => endsSame kinds _ _ (rewrite open, Bool.orFalse word.trails) good)

theorem notCommaOf ∀ (word: Word) (is: (word.text == ",") = False): word.notComma = True := rewrite is

theorem atomTrails ∀ (kind: Syntax.Tok) (word: Word)
    (open: isCloserText word.text = False):
    (Atom kind word).trails = word.trails :=
  rewrite open, Bool.orFalse word.trails

--| An opening bracket, its own-line comments written by an enclosing element.
theorem openStep ∀ (word closer: Word) (around: Around)
    (hoisted: around.hoisted = True)
    (sound: word.sound = True)
    (comma: word.notComma = True)
    (open: isCloserText word.text = False):
    Step (word.opening around closer) Anything (kinds => Ends kinds word.trails) :=
  match word with
    | { text, comments = { above, after, blankBefore } } =>
      openingStep text above after blankBefore closer around hoisted
        (Bool.notTrue _ (Bool.andLeft sound))
        (Bool.andRight (Bool.andRight sound))
        (Bool.notTrue _ comma)
        open

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
