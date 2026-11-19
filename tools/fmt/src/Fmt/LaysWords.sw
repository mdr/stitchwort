--| Tokens and openers for the check's walk (SW-4109): `laysKinds` of a token from a calm place.
namespace Fmt.LaysWords
import Std (Bool, DecEq, Doc, Eq, List, Nat, Option, Text, Void)
import Std.Doc (..)
import Syntax (Expr, InfixKind, Word)
import Fmt (..)
import Fmt.LaysKinds (..)
import Fmt.LaysRules (..)
import Fmt.SpellProofs (..)
import Fmt.ToldDeclProofs (..)
import Fmt.TrailsProofs (Coded, atomCoded, parenTrails, trailsBackCoded)

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

theorem endsStartsAny ∀ (kinds: Kinds) (hoisted trails: Bool)
    (ends: Ends kinds trails = True):
    Starts hoisted trails kinds = True :=
  match kinds, hoisted, trails, ends with
    | { start = False, broken = False, mid, held = False }, _, _, _ => rewrite Bool.orTrue hoisted
    | { start = False, broken = False, mid, held = True }, _, True, _ => rewrite Bool.orTrue hoisted
