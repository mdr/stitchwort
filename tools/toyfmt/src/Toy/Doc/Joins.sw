--| What the printer puts next to what. Through every reading, each piece
--| of output that isn't layout is followed by a line break, or by a piece
--| the document allowed after it (`readingJoins`, `printedJoins`): no reading
--| brings two chunks together, or puts a space after one, that the
--| document's own predicate (`Joins`) didn't list. `follows word next` is
--| the caller's relation: for the toy, that `word` still lexes as itself
--| before `next`. A space written after a word asks `follows word " "`, so
--| a comment, which runs to the end of its line, is only ever followed by
--| a line break. A closer (`Closing`) that joins the line of a comment
--| still waiting is written before it, so it asks what any piece asks of
--| the piece it follows, and that the comment's space may follow it.
--|
--| `Joins` is in continuation style: from the edge the printer is at, a
--| document asks its conditions and hands each edge it may leave to what
--| comes after. It lists outcomes instead of approximating them, so it
--| holds of exactly the layouts some reading can make, up to the mode of
--| a `Line` (a space is asked for also where the group is broken).

namespace Toy.Doc.Proofs
import Toy.Doc (..)
import Std (Bool, Eq, List, Nat, Option, Text, Void)

--| What the next piece on the line would stand after.
type Edge =
  --| No trailing comment waits: the next text follows `touching`, the
  --| last piece if it isn't layout, or nothing (a line start, or after
  --| spaces).
  | Plain (touching: Option Text)
  --| A trailing comment waits for the end of the line: a chunk starts a
  --| new line, and a closer joins this one, after `touching`.
  | Waiting (touching: Option Text)

--| Spaces of any length ask what one space asks.
def gapOr (later: Text): Text := if later.all (char => char == ' ') then " " else later

def textTouch (text: Text): Option Text := if isLayout text then None else Some text

def outTouch: List Text → Option Text
  | [] => None
  | [last, .._] => textTouch last

def edgeOf (suffixes out: List Text): Edge := if suffixes.isEmpty then Plain (outTouch out) else Waiting (outTouch out)

def Printer.edge (printer: Printer): Edge := edgeOf printer.suffixes printer.out

--| `text` may be put after what the line ends with.
def PutOk (follows: Text → Text → Prop) (touching: Option Text) (text: Text): Prop := match touching with
  | Some word => follows word (gapOr text)
  | None => True

--| A chunk: nothing if empty; after a waiting comment, spaces are dropped
--| and text starts a new line.
def WriteJoins (follows: Text → Text → Prop) (edge: Edge) (text: Text) (next: Edge → Prop): Prop :=
  if text.isEmpty then next edge
  else
    match edge with
      | Plain touching => PutOk follows touching text ∧ next (Plain (textTouch text))
      | Waiting touching =>
        if text.all (char => char == ' ') then next (Waiting touching) else next (Plain (textTouch text))

--| A closer: a chunk where no comment waits. Where one waits, the closer
--| joins its line before it: so it isn't spaces, it may follow what the
--| line ends with, and the comment's space may follow it.
def CloseJoins (follows: Text → Text → Prop) (edge: Edge) (text: Text) (next: Edge → Prop): Prop := match edge with
  | Plain touching => WriteJoins follows (Plain touching) text next
  | Waiting touching =>
    text.all (char => char == ' ') = False
      ∧ text.isEmpty = False
      ∧ PutOk follows touching text
      ∧ follows text " "
      ∧ next (Waiting (textTouch text))

--| A `Line` or a fill's separator: a space or a line break.
def SepJoins (follows: Text → Text → Prop) (edge: Edge) (next: Edge → Prop): Prop := match edge with
  | Plain touching => PutOk follows touching " " ∧ next (Plain None)
  | Waiting _ => next (Plain None)

--| A `SoftLine`: nothing or a line break; a line break if a comment waits.
def SoftJoins (edge: Edge) (next: Edge → Prop): Prop := match edge with
  | Plain touching => next (Plain touching) ∧ next (Plain None)
  | Waiting _ => next (Plain None)

--| A `LineStart` or `LineStartHere`: a line break unless a line starts
--| here, where a comment may still wait from the line before.
def StartJoins (edge: Edge) (next: Edge → Prop): Prop := match edge with
  | Plain touching => next (Plain None)
  | Waiting touching => next (Waiting touching) ∧ next (Plain None)

--| A trailing comment (`Joins` asks that it isn't empty): written after a
--| space at the end of the line. A
--| second one while the first waits is refused: both would be flushed on
--| one line, the second inside the first.
def SuffixJoins (follows: Text → Text → Prop) (edge: Edge) (next: Edge → Prop): Prop := match edge with
  | Plain touching => PutOk follows touching " " ∧ next (Waiting touching)
  | Waiting _ => False

--| From `edge`, every way `doc` may print puts each piece after one it
--| may follow, and every edge it may leave satisfies `next`.
def Joins (follows: Text → Text → Prop) (doc: Doc) (edge: Edge) (next: Edge → Prop): Prop := match doc with
  | Empty => next edge
  | BreakParent => next edge
  | Blank => next edge
  | Chunk text _ => WriteJoins follows edge text next
  | Closing text => CloseJoins follows edge text next
  | Line => SepJoins follows edge next
  | SoftLine => SoftJoins edge next
  | HardLine => next (Plain None)
  | CommentEnd => next (Plain None)
  | LineStart => StartJoins edge next
  | LineStartHere => StartJoins edge next
  | Nest _ inner => Joins follows inner edge next
  | Group inner _ => Joins follows inner edge next
  | Flatten inner => Joins follows inner edge next
  | OneLineBelow inner => Joins follows inner (Plain None) next
  | Concat docs => JoinsAll follows docs edge next
  | Fill items => FillJoins follows items edge next
  | Choice options => OptionsJoin follows options edge next
  | LineSuffix comment => comment.isEmpty = False ∧ SuffixJoins follows edge next

--| The documents one after another.
def JoinsAll (follows: Text → Text → Prop) (docs: List Doc) (edge: Edge) (next: Edge → Prop): Prop := match docs with
  | [] => next edge
  | [doc, ..rest] => Joins follows doc edge (after => JoinsAll follows rest after next)

--| A fill's items, a separator before each but the first.
def FillJoins (follows: Text → Text → Prop) (items: List Doc) (edge: Edge) (next: Edge → Prop): Prop := match items with
  | [] => next edge
  | [first, ..others] => Joins follows first edge (after => SepsJoin follows others after next)

def SepsJoin (follows: Text → Text → Prop) (items: List Doc) (edge: Edge) (next: Edge → Prop): Prop := match items with
  | [] => next edge
  | [item, ..more] =>
    SepJoins follows edge (middle => Joins follows item middle (after => SepsJoin follows more after next))

--| Whichever option a choice takes.
def OptionsJoin (follows: Text → Text → Prop) (options: List Doc) (edge: Edge) (next: Edge → Prop): Prop :=
  match options with
    | [] => next edge
    | [last] => Joins follows last edge next
    | [option, ..others] => Joins follows option edge next ∧ OptionsJoin follows others edge next

--| The work list, from `edge` to the end.
def StackJoins (follows: Text → Text → Prop) (stack: List Cmd) (edge: Edge): Prop := match stack with
  | [] => True
  | [Print _ _ doc, ..rest] => Joins follows doc edge (after => StackJoins follows rest after)
  | [FillSep _ item, ..rest] =>
    SepJoins follows edge (middle => Joins follows item middle (after => StackJoins follows rest after))

-- A weaker continuation still holds: what comes after may ask less.

theorem writeWeaker ∀ (follows: Text → Text → Prop) (edge: Edge) (text: Text)
    (strong weak: Edge → Prop) (implies: ∀ (after: Edge) => strong after → weak after)
    (joins: WriteJoins follows edge text strong):
    WriteJoins follows edge text weak :=
  match empty: text.isEmpty, joins with
    | True, joins => implies edge joins
    | False, joins =>
      match edge, joins with
        | Plain touching, Both ok after => (ok, (implies _ after))
        | Waiting touching, joins =>
          match spaces: text.all (char => char == ' '), joins with
            | True, joins => implies (Waiting touching) joins
            | False, joins => implies _ joins

theorem closeWeaker ∀ (follows: Text → Text → Prop) (edge: Edge) (text: Text)
    (strong weak: Edge → Prop) (implies: ∀ (after: Edge) => strong after → weak after)
    (joins: CloseJoins follows edge text strong):
    CloseJoins follows edge text weak :=
  match edge, joins with
    | Plain touching, joins => writeWeaker follows (Plain touching) text strong weak implies joins
    | Waiting touching, (word, filled, ok, tail, after) => (word, filled, ok, tail, (implies _ after))

theorem sepWeaker ∀ (follows: Text → Text → Prop) (edge: Edge)
    (strong weak: Edge → Prop) (implies: ∀ (after: Edge) => strong after → weak after)
    (joins: SepJoins follows edge strong):
    SepJoins follows edge weak :=
  match edge, joins with
    | Plain touching, Both ok after => (ok, (implies _ after))
    | Waiting _, after => implies _ after

theorem softWeaker ∀ (edge: Edge) (strong weak: Edge → Prop) (implies: ∀ (after: Edge) => strong after → weak after)
    (joins: SoftJoins edge strong):
    SoftJoins edge weak :=
  match edge, joins with
    | Plain touching, Both same broken => ((implies _ same), (implies _ broken))
    | Waiting _, after => implies _ after

theorem startWeaker ∀ (edge: Edge) (strong weak: Edge → Prop) (implies: ∀ (after: Edge) => strong after → weak after)
    (joins: StartJoins edge strong):
    StartJoins edge weak :=
  match edge, joins with
    | Plain touching, after => implies _ after
    | Waiting _, Both same broken => ((implies _ same), (implies _ broken))

theorem suffixWeaker ∀ (follows: Text → Text → Prop) (edge: Edge)
    (strong weak: Edge → Prop) (implies: ∀ (after: Edge) => strong after → weak after)
    (joins: SuffixJoins follows edge strong):
    SuffixJoins follows edge weak :=
  match edge, joins with
    | Plain touching, Both ok after => (ok, (implies _ after))
    | Waiting _, never => never

--| What holds with a continuation holds with any it implies.
theorem joinsWeaker ∀ (follows: Text → Text → Prop) (doc: Doc) (edge: Edge)
    (strong weak: Edge → Prop) (implies: ∀ (after: Edge) => strong after → weak after)
    (joins: Joins follows doc edge strong):
    Joins follows doc edge weak :=
  match doc, joins with
    | Empty, joins => implies edge joins
    | BreakParent, joins => implies edge joins
    | Blank, joins => implies edge joins
    | Chunk text width, joins => writeWeaker follows edge text strong weak implies joins
    | Closing text, joins => closeWeaker follows edge text strong weak implies joins
    | Line, joins => sepWeaker follows edge strong weak implies joins
    | SoftLine, joins => softWeaker edge strong weak implies joins
    | HardLine, joins => implies _ joins
    | CommentEnd, joins => implies _ joins
    | LineStart, joins => startWeaker edge strong weak implies joins
    | LineStartHere, joins => startWeaker edge strong weak implies joins
    | Nest more inner, joins => joinsWeaker follows inner edge strong weak implies joins
    | Group inner hard, joins => joinsWeaker follows inner edge strong weak implies joins
    | Flatten inner, joins => joinsWeaker follows inner edge strong weak implies joins
    | OneLineBelow inner, joins => joinsWeaker follows inner (Plain None) strong weak implies joins
    | Concat docs, joins => allWeaker follows docs edge strong weak implies joins
    | Fill items, joins => fillWeaker follows items edge strong weak implies joins
    | Choice options, joins => optionsWeaker follows options edge strong weak implies joins
    | LineSuffix comment, Both filled joins => (filled, (suffixWeaker follows edge strong weak implies joins))

theorem allWeaker ∀ (follows: Text → Text → Prop) (docs: List Doc) (edge: Edge)
    (strong weak: Edge → Prop) (implies: ∀ (after: Edge) => strong after → weak after)
    (joins: JoinsAll follows docs edge strong):
    JoinsAll follows docs edge weak :=
  match docs, joins with
    | [], joins => implies edge joins
    | [doc, ..rest], joins =>
      joinsWeaker follows doc edge
        (after => JoinsAll follows rest after strong)
        (after => JoinsAll follows rest after weak)
        (after later => allWeaker follows rest after strong weak implies later)
        joins

theorem fillWeaker ∀ (follows: Text → Text → Prop) (items: List Doc) (edge: Edge)
    (strong weak: Edge → Prop) (implies: ∀ (after: Edge) => strong after → weak after)
    (joins: FillJoins follows items edge strong):
    FillJoins follows items edge weak :=
  match items, joins with
    | [], joins => implies edge joins
    | [first, ..others], joins =>
      joinsWeaker follows first edge
        (after => SepsJoin follows others after strong)
        (after => SepsJoin follows others after weak)
        (after later => sepsWeaker follows others after strong weak implies later)
        joins

theorem sepsWeaker ∀ (follows: Text → Text → Prop) (items: List Doc) (edge: Edge)
    (strong weak: Edge → Prop) (implies: ∀ (after: Edge) => strong after → weak after)
    (joins: SepsJoin follows items edge strong):
    SepsJoin follows items edge weak :=
  match items, joins with
    | [], joins => implies edge joins
    | [item, ..more], joins =>
      sepWeaker follows edge
        (middle => Joins follows item middle (after => SepsJoin follows more after strong))
        (middle => Joins follows item middle (after => SepsJoin follows more after weak))
        (middle inner =>
          joinsWeaker follows item middle
            (after => SepsJoin follows more after strong)
            (after => SepsJoin follows more after weak)
            (after later => sepsWeaker follows more after strong weak implies later)
            inner)
        joins

theorem optionsWeaker ∀ (follows: Text → Text → Prop) (options: List Doc) (edge: Edge)
    (strong weak: Edge → Prop) (implies: ∀ (after: Edge) => strong after → weak after)
    (joins: OptionsJoin follows options edge strong):
    OptionsJoin follows options edge weak :=
  match options, joins with
    | [], joins => implies edge joins
    | [last], joins => joinsWeaker follows last edge strong weak implies joins
    | [option, next, ..others], Both first rest => (
      (joinsWeaker follows option edge strong weak implies first),
      (optionsWeaker follows [next, ..others] edge strong weak implies rest)
    )

-- What a step pushes on the work list joins as the document it came from.

theorem printsJoin ∀ (follows: Text → Text → Prop) (indent: Nat) (mode: Mode) (docs: List Doc)
    (rest: List Cmd) (edge: Edge)
    (joins: JoinsAll follows docs edge (after => StackJoins follows rest after)):
    StackJoins follows (docs.map (Print indent mode) ++ rest) edge :=
  match docs, joins with
    | [], joins => joins
    | [doc, ..later], joins =>
      joinsWeaker follows doc edge
        (after => JoinsAll follows later after (final => StackJoins follows rest final))
        (after => StackJoins follows (later.map (Print indent mode) ++ rest) after)
        (after others => printsJoin follows indent mode later rest after others)
        joins

--| A flat fill is its items with a `Line` between each two.
theorem linesJoin ∀ (follows: Text → Text → Prop) (first: Doc) (others: List Doc) (edge: Edge) (next: Edge → Prop)
    (joins: Joins follows first edge (after => SepsJoin follows others after next)):
    JoinsAll follows (Doc.joinLines [first, ..others]) edge next :=
  match others, joins with
    | [], joins => joins
    | [second, ..rest], joins =>
      joinsWeaker follows first edge
        (after => SepsJoin follows [second, ..rest] after next)
        (after => JoinsAll follows [Line, ..Doc.joinLines [second, ..rest]] after next)
        (after later =>
          sepWeaker follows after
            (middle => Joins follows second middle (final => SepsJoin follows rest final next))
            (middle => JoinsAll follows (Doc.joinLines [second, ..rest]) middle next)
            (middle inner => linesJoin follows second rest middle next inner)
            later)
        joins

--| A broken fill's separators and items, as the work list holds them.
theorem fillSepsJoin ∀ (follows: Text → Text → Prop) (indent: Nat) (items: List Doc) (rest: List Cmd) (edge: Edge)
    (joins: SepsJoin follows items edge (after => StackJoins follows rest after)):
    StackJoins follows (items.map (FillSep indent) ++ rest) edge :=
  match items, joins with
    | [], joins => joins
    | [item, ..more], joins =>
      sepWeaker follows edge
        (middle =>
          Joins follows item middle (after => SepsJoin follows more after (final => StackJoins follows rest final)))
        (middle => Joins follows item middle (after => StackJoins follows (more.map (FillSep indent) ++ rest) after))
        (middle inner =>
          joinsWeaker follows item middle
            (after => SepsJoin follows more after (final => StackJoins follows rest final))
            (after => StackJoins follows (more.map (FillSep indent) ++ rest) after)
            (after later => fillSepsJoin follows indent more rest after later)
            inner)
        joins

theorem optionJoins ∀ (follows: Text → Text → Prop) (chosen: Doc) (options: List Doc) (edge: Edge) (next: Edge → Prop)
    (isOption: IsOption chosen options)
    (joins: OptionsJoin follows options edge next):
    Joins follows chosen edge next :=
  match options, isOption, joins with
    | [], picked, joins => rewrite picked then joins
    | [last], picked, joins => rewrite picked then joins
    | [option, second, ..others], Inl picked, Both first _ => rewrite picked then first
    | [option, second, ..others], Inr later, Both _ rest =>
      optionJoins follows chosen [second, ..others] edge next later rest

theorem headOrJoins ∀ (follows: Text → Text → Prop) (options: List Doc) (edge: Edge) (next: Edge → Prop)
    (joins: OptionsJoin follows options edge next):
    Joins follows (options.headOr Empty) edge next :=
  match options, joins with
    | [], joins => joins
    | [last], joins => joins
    | [option, second, ..others], Both first _ => first

-- The printer's side: what its output must satisfy between steps.

--| `later` may stand straight after `earlier`: after layout anything
--| may, a line break may follow anything, and otherwise the document
--| allowed it.
def Pair (follows: Text → Text → Prop) (earlier later: Text): Prop :=
  isLayout earlier = True ∨ later = "\n" ∨ follows earlier (gapOr later)

--| `later` may be written after the pieces `out` (the last first).
def Accepts (follows: Text → Text → Prop) (out: List Text) (later: Text): Prop := match out with
  | [] => True
  | [earlier, .._] => Pair follows earlier later

--| Every piece of `out` (the last first) has at least one character and
--| may stand after the one before.
def Pairs (follows: Text → Text → Prop): List Text → Prop
  | [] => True
  | [later, ..earlier] => later.isEmpty = False ∧ Accepts follows earlier later ∧ Pairs follows earlier

--| Nothing is on the last line of `out`.
def Fresh: List Text → Prop
  | [] => True
  | [last, .._] => last = "\n"

--| A space may be written after `out`.
def HeadReady (follows: Text → Text → Prop): List Text → Prop
  | [] => True
  | [last, .._] => isLayout last = True ∨ follows last " "

--| At most one trailing comment waits; it has at least one character and
--| may be written, after a space, at the end of the line once the spaces
--| there are dropped.
def WaitsParts (follows: Text → Text → Prop) (suffixes out: List Text): Prop := match suffixes with
  | [] => True
  | [only] => only.isEmpty = False ∧ HeadReady follows (trimSpaces out)
  | _ => False

def SoundParts (follows: Text → Text → Prop) (out: List Text) (owed: Option Nat)
    (atLineStart: Bool) (suffixes: List Text):
    Prop :=
  Pairs follows out
    ∧ (owed = None ∨ atLineStart = True)
    ∧ (atLineStart = False ∨ Fresh out)
    ∧ WaitsParts follows suffixes out

--| The output so far is joined as allowed, indentation is owed only at a
--| line start, a line marked as only started has nothing on it, and the
--| waiting comment can be flushed.
def Sound (follows: Text → Text → Prop) (printer: Printer): Prop :=
  SoundParts follows printer.out printer.owed printer.atLineStart printer.suffixes

--| The printer is sound and its edge satisfies `next`.
def Holds (follows: Text → Text → Prop) (next: Edge → Prop) (printer: Printer): Prop :=
  Sound follows printer ∧ next printer.edge

theorem freshAccepts ∀ (follows: Text → Text → Prop) (out: List Text) (later: Text)
    (fresh: Fresh out):
    Accepts follows out later :=
  match out, fresh with
    | [], _ => byComputing
    | [last, ..earlier], isBreak => Inl (rewrite isBreak)

theorem breakAccepts ∀ (follows: Text → Text → Prop) (out: List Text): Accepts follows out "\n" := match out with
  | [] => byComputing
  | [last, ..earlier] => Inr (Inl byComputing)

theorem freshTouch ∀ (out: List Text) (fresh: Fresh out): outTouch out = None := match out, fresh with
  | [], _ => byComputing
  | [last, ..earlier], isBreak => rewrite isBreak

theorem freshWhen ∀ (flag: Bool) (out: List Text) (start: flag = True) (either: flag = False ∨ Fresh out): Fresh out :=
  match either with
    | Inr fresh => fresh
    | Inl other => Void.impossible (Bool.falseNotTrue (Eq.trans other.flipped start))

theorem touchAccepts ∀ (follows: Text → Text → Prop) (out: List Text) (text: Text)
    (ok: PutOk follows (outTouch out) text):
    Accepts follows out text :=
  match out, ok with
    | [], _ => byComputing
    | [last, ..earlier], ok =>
      match layout: isLayout last, ok with
        | True, _ => Inl byComputing
        | False, ok => Inr (Inr ok)

theorem touchReady ∀ (follows: Text → Text → Prop) (out: List Text)
    (ok: PutOk follows (outTouch out) " "):
    HeadReady follows out :=
  match out, ok with
    | [], _ => byComputing
    | [last, ..earlier], ok =>
      match layout: isLayout last, ok with
        | True, _ => Inl byComputing
        | False, ok => Inr ok

theorem headAccepts ∀ (follows: Text → Text → Prop) (out: List Text)
    (ready: HeadReady follows out):
    Accepts follows out " " :=
  match out, ready with
    | [], _ => byComputing
    | [last, ..earlier], Inl layout => Inl layout
    | [last, ..earlier], Inr ok => Inr (Inr ok)

theorem trimPairs ∀ (follows: Text → Text → Prop) (out: List Text)
    (pairs: Pairs follows out):
    Pairs follows (trimSpaces out) :=
  match out, pairs with
    | [], _ => byComputing
    | [last, ..earlier], Both filled (Both first rest) =>
      match spaces: last.all (char => char == ' ') with
        | True => trimPairs follows earlier rest
        | False => (filled, first, rest)

theorem trimFresh ∀ (out: List Text) (fresh: Fresh out): Fresh (trimSpaces out) := match out, fresh with
  | [], _ => byComputing
  | [last, ..earlier], isBreak => rewrite isBreak

theorem trimFreshOr ∀ (flag: Bool) (out: List Text)
    (either: flag = False ∨ Fresh out):
    flag = False ∨ Fresh (trimSpaces out) :=
  match either with
    | Inl other => Inl other
    | Inr fresh => Inr (trimFresh out fresh)

--| A space may be written where the comment will be flushed, also before
--| the spaces at the end of the line are dropped.
theorem readyAccepts ∀ (follows: Text → Text → Prop) (out: List Text)
    (ready: HeadReady follows (trimSpaces out)):
    Accepts follows out " " :=
  match out, ready with
    | [], _ => byComputing
    | [last, ..earlier], ready =>
      match spaces: last.all (char => char == ' '), ready with
        | True, _ => Inl (spacesIsLayout last spaces)
        | False, Inl layout => Inl layout
        | False, Inr ok => Inr (Inr ok)

theorem gapSpaces ∀ (text: Text) (spaces: text.all (char => char == ' ') = True): gapOr text = " " := rewrite spaces

--| What stands before spaces may be followed by one space.
theorem gapBefore ∀ (follows: Text → Text → Prop) (earlier: List Text) (last: Text)
    (spaces: last.all (char => char == ' ') = True)
    (accepts: Accepts follows earlier last):
    HeadReady follows earlier :=
  match earlier, accepts with
    | [], _ => byComputing
    | [before, ..more], Inl layout => Inl layout
    | [before, ..more], Inr (Inl isBreak) =>
      let breakSpaces: "\n".all (char => char == ' ') = True := rewrite <- isBreak then spaces
      Void.impossible (Bool.falseNotTrue breakSpaces)
    | [before, ..more], Inr (Inr ok) => Inr (rewrite <- gapSpaces last spaces then ok)

--| If a space may follow the output, it may once the spaces at its end
--| are dropped.
theorem trimmedReady ∀ (follows: Text → Text → Prop) (out: List Text)
    (pairs: Pairs follows out)
    (ready: HeadReady follows out):
    HeadReady follows (trimSpaces out) :=
  match out, pairs, ready with
    | [], _, _ => byComputing
    | [last, ..earlier], Both _ (Both first rest), ready =>
      match spaces: last.all (char => char == ' ') with
        | True => trimmedReady follows earlier rest (gapBefore follows earlier last spaces first)
        | False => ready

theorem payOwed ∀ (printer: Printer): printer.payIndent.owed = None := match owed: printer.owed with
  | None => owed
  | Some Zero => byComputing
  | Some (Succ less) => byComputing

--| Indentation is paid on an empty line, so text may follow it.
theorem payPairs ∀ (follows: Text → Text → Prop) (printer: Printer) (text: Text)
    (pairs: Pairs follows printer.out)
    (owedOk: printer.owed = None ∨ printer.atLineStart = True)
    (freshOk: printer.atLineStart = False ∨ Fresh printer.out)
    (filled: text.isEmpty = False)
    (accepts: Accepts follows printer.out text):
    Pairs follows [text, ..printer.payIndent.out] :=
  match owed: printer.owed, owedOk with
    | None, _ => (filled, accepts, pairs)
    | Some Zero, _ => (filled, accepts, pairs)
    | Some (Succ less), Inr start => (
      filled,
      (Inl (spacesIsLayout _ (indentSpaces (Succ less)))),
      byComputing,
      (freshAccepts follows printer.out _ (freshWhen _ printer.out start freshOk)),
      pairs
    )
    | Some (Succ less), Inl none => cases

theorem putSound ∀ (follows: Text → Text → Prop) (printer: Printer) (text: Text) (width: Nat)
    (sound: Sound follows printer)
    (clear: printer.suffixes = [])
    (filled: text.isEmpty = False)
    (accepts: Accepts follows printer.out text):
    Sound follows (printer.put text width) :=
  match sound, payIndentWritten printer with
    | (pairs, owedOk, freshOk, _), (_, suffixes) =>
      let parts: SoundParts follows
        [text, ..printer.payIndent.out]
        printer.payIndent.owed
        False
        printer.payIndent.suffixes :=
        rewrite payOwed printer, suffixes, clear then
          (
            (payPairs follows printer text pairs owedOk freshOk filled accepts),
            (Inl byComputing),
            (Inl byComputing),
            byComputing
          )
      parts

theorem putEdge ∀ (printer: Printer) (text: Text) (width: Nat)
    (clear: printer.suffixes = []):
    (printer.put text width).edge = Plain (textTouch text) :=
  match payIndentWritten printer with
    | (_, suffixes) =>
      let edge: edgeOf printer.payIndent.suffixes [text, ..printer.payIndent.out] = Plain (textTouch text) :=
        rewrite suffixes, clear
      edge

theorem flushOnePairs ∀ (follows: Text → Text → Prop) (printer: Printer) (comment: Text)
    (pairs: Pairs follows printer.out)
    (owedOk: printer.owed = None ∨ printer.atLineStart = True)
    (freshOk: printer.atLineStart = False ∨ Fresh printer.out)
    (filled: comment.isEmpty = False)
    (gap: Accepts follows printer.out " "):
    Pairs follows (printer.flushOne comment).out :=
  match start: printer.atLineStart, freshOk with
    | True, freshOk =>
      payPairs follows printer comment pairs owedOk
        (Inr (freshWhen True printer.out byComputing freshOk))
        filled
        (freshAccepts follows printer.out comment (freshWhen True printer.out byComputing freshOk))
    | False, _ => (filled, (Inl byComputing), byComputing, gap, pairs)

--| The comment waiting at a line break is written where it may stand.
theorem flushedPairs ∀ (follows: Text → Text → Prop) (printer: Printer)
    (sound: Sound follows printer):
    Pairs follows ({ printer | out = trimSpaces printer.out }).flushSuffixes.out :=
  match sound with
    | (pairs, owedOk, freshOk, waits) =>
      match suffixes: printer.suffixes, waits with
        | [], _ => trimPairs follows printer.out pairs
        | [only], Both filled ready =>
          flushOnePairs follows
            { printer | out = trimSpaces printer.out, suffixes = [] }
            only
            (trimPairs follows printer.out pairs)
            owedOk
            (trimFreshOr printer.atLineStart printer.out freshOk)
            filled
            (headAccepts follows (trimSpaces printer.out) ready)
        | [first, second, ..more], never =>
          match never with
            | ()

--| The comment waiting at the end of the print is written where it may
--| stand.
theorem finalPairs ∀ (follows: Text → Text → Prop) (printer: Printer)
    (sound: Sound follows printer):
    Pairs follows printer.flushSuffixes.out :=
  match sound with
    | (pairs, owedOk, freshOk, waits) =>
      match suffixes: printer.suffixes, waits with
        | [], _ => pairs
        | [only], Both filled ready =>
          flushOnePairs follows
            { printer | suffixes = [] }
            only
            pairs
            owedOk
            freshOk
            filled
            (readyAccepts follows printer.out ready)
        | [first, second, ..more], never =>
          match never with
            | ()

theorem newlineSound ∀ (follows: Text → Text → Prop) (printer: Printer) (indent: Nat)
    (sound: Sound follows printer):
    Sound follows (printer.newline indent) :=
  match flushWritten { printer | out = trimSpaces printer.out } with
    | (_, none) =>
      let parts: SoundParts follows
        ["\n", ..({ printer | out = trimSpaces printer.out }).flushSuffixes.out]
        (Some indent)
        True
        ({ printer | out = trimSpaces printer.out }).flushSuffixes.suffixes :=
        rewrite none then
          (
            ((byComputing, (breakAccepts follows _), (flushedPairs follows printer sound))),
            (Inr byComputing),
            (Inr byComputing),
            byComputing
          )
      parts

theorem newlineClear ∀ (printer: Printer) (indent: Nat): (printer.newline indent).suffixes = [] :=
  match newlineWritten printer indent with | (_, none) => none

theorem newlineEdge ∀ (printer: Printer) (indent: Nat): (printer.newline indent).edge = Plain None :=
  let edge: edgeOf (printer.newline indent).suffixes [
    "\n",
    ..({ printer | out = trimSpaces printer.out }).flushSuffixes.out
  ]
    = Plain None :=
    rewrite newlineClear printer indent
  edge

--| After a line break the printer is sound, at a line start.
theorem newlineHolds ∀ (follows: Text → Text → Prop) (next: Edge → Prop) (printer: Printer) (indent: Nat)
    (sound: Sound follows printer) (after: next (Plain None)):
    Holds follows next (printer.newline indent) :=
  ((newlineSound follows printer indent sound), (rewrite newlineEdge printer indent then after))

--| A chunk written where the document allowed it.
theorem writeHolds ∀ (follows: Text → Text → Prop) (next: Edge → Prop) (printer: Printer) (indent: Nat)
    (text: Text) (width: Nat)
    (sound: Sound follows printer)
    (joins: WriteJoins follows printer.edge text next):
    Holds follows next (printer.write indent text width) :=
  match empty: text.isEmpty, joins with
    | True, joins => (sound, joins)
    | False, joins =>
      match waiting: printer.suffixes.isEmpty, joins with
        | True, Both ok after => (
          (putSound follows printer text width sound
            (emptyNil printer.suffixes waiting)
            empty
            (touchAccepts follows printer.out text ok)),
          (rewrite putEdge printer text width (emptyNil printer.suffixes waiting) then after)
        )
        | False, joins =>
          match spaces: text.all (char => char == ' '), joins with
            | True, joins => (sound, joins)
            | False, joins => (
              (putSound follows
                (printer.newline (printer.continuation indent))
                text
                width
                (newlineSound follows printer (printer.continuation indent) sound)
                (newlineClear printer (printer.continuation indent))
                empty
                (Inl byComputing)),
              (rewrite putEdge
                    (printer.newline (printer.continuation indent))
                    text
                    width
                    (newlineClear printer (printer.continuation indent)) then
                joins)
            )

--| With no comment waiting, a closer asks what a chunk asks.
theorem closePlain ∀ (follows: Text → Text → Prop) (suffixes out: List Text) (text: Text) (next: Edge → Prop)
    (clear: suffixes.isEmpty = True)
    (joins: CloseJoins follows (edgeOf suffixes out) text next):
    WriteJoins follows (edgeOf suffixes out) text next :=
  match suffixes, clear, joins with | [], _, joins => joins

theorem closeWaiting ∀ (follows: Text → Text → Prop) (suffixes out: List Text) (text: Text) (next: Edge → Prop)
    (waits: suffixes.isEmpty = False)
    (joins: CloseJoins follows (edgeOf suffixes out) text next):
    text.all (char => char == ' ') = False
      ∧ text.isEmpty = False
      ∧ PutOk follows (outTouch out) text
      ∧ follows text " "
      ∧ next (Waiting (textTouch text)) :=
  match suffixes, waits, joins with | [first, ..more], _, joins => joins

--| A closer put on a line where a comment waits: the comment still
--| waits, and can be flushed after the closer.
theorem putWaiting ∀ (follows: Text → Text → Prop) (printer: Printer) (text: Text) (width: Nat)
    (sound: Sound follows printer)
    (waits: printer.suffixes.isEmpty = False)
    (word: text.all (char => char == ' ') = False)
    (filled: text.isEmpty = False)
    (ok: PutOk follows (outTouch printer.out) text) (tail: follows text " "):
    Sound follows (printer.put text width) ∧ (printer.put text width).edge = Waiting (textTouch text) :=
  match sound, payIndentWritten printer with
    | (pairs, owedOk, freshOk, held), (_, same) =>
      match suffixes: printer.suffixes, held, waits with
        | [], _, never =>
          match never with
            | ()
        | [first, second, ..more], never, _ =>
          match never with
            | ()
        | [only], (commentFilled, ready), _ =>
          let parts: SoundParts follows
            [text, ..printer.payIndent.out]
            printer.payIndent.owed
            False
            printer.payIndent.suffixes :=
            rewrite payOwed printer, same then
              (
                (payPairs follows printer text pairs owedOk freshOk filled (touchAccepts follows printer.out text ok)),
                (Inl byComputing),
                (Inl byComputing),
                commentFilled,
                (rewrite trimKeep text printer.payIndent.out word then Inr tail)
              )
          let edge: edgeOf printer.payIndent.suffixes [text, ..printer.payIndent.out] = Waiting (textTouch text) :=
            rewrite same
          (parts, edge)

--| A closer written where the document allowed it.
theorem closeHolds ∀ (follows: Text → Text → Prop) (next: Edge → Prop) (printer: Printer) (text: Text)
    (sound: Sound follows printer)
    (joins: CloseJoins follows printer.edge text next):
    Holds follows next (printer.close text) :=
  match trueOrFalse printer.suffixes.isEmpty with
    | Inl clear =>
      rewrite closeClear printer 0 text clear then
        writeHolds follows next printer 0 text text.length sound
          (closePlain follows printer.suffixes printer.out text next clear joins)
    | Inr waits =>
      match closeWaiting follows printer.suffixes printer.out text next waits joins with
        | (word, filled, ok, tail, after) =>
          match putWaiting follows printer text text.length sound waits word filled ok tail with
            | (soundAfter, edge) => rewrite closePut printer text filled then (soundAfter, (rewrite edge then after))

theorem sepBreak ∀ (follows: Text → Text → Prop) (next: Edge → Prop) (edge: Edge)
    (joins: SepJoins follows edge next):
    next (Plain None) :=
  match edge, joins with
    | Plain touching, Both _ after => after
    | Waiting _, after => after

--| A separator's space, written where no comment waits.
theorem sepWrite ∀ (follows: Text → Text → Prop) (next: Edge → Prop) (printer: Printer) (indent: Nat)
    (sound: Sound follows printer)
    (clear: printer.suffixes.isEmpty = True)
    (joins: SepJoins follows printer.edge next):
    Holds follows next (printer.write indent " " 1) :=
  match waiting: printer.suffixes.isEmpty, clear, joins with
    | True, _, Both ok after => (
      (putSound follows printer " " 1 sound
        (emptyNil printer.suffixes waiting)
        byComputing
        (touchAccepts follows printer.out " " ok)),
      (rewrite putEdge printer " " 1 (emptyNil printer.suffixes waiting) then after)
    )
    | False, never, _ =>
      match never with
        | ()

theorem softBreak ∀ (next: Edge → Prop) (edge: Edge) (joins: SoftJoins edge next): next (Plain None) :=
  match edge, joins with
    | Plain touching, Both _ broken => broken
    | Waiting _, after => after

theorem softStay ∀ (next: Edge → Prop) (printer: Printer)
    (clear: printer.suffixes.isEmpty = True)
    (joins: SoftJoins printer.edge next):
    next printer.edge :=
  match waiting: printer.suffixes.isEmpty, clear, joins with
    | True, _, Both same _ => same
    | False, never, _ =>
      match never with
        | ()

theorem startBreak ∀ (next: Edge → Prop) (edge: Edge) (joins: StartJoins edge next): next (Plain None) :=
  match edge, joins with
    | Plain touching, after => after
    | Waiting _, Both _ broken => broken

--| At a line start the edge is the same after a `LineStart`: nothing is
--| on the line, or a comment still waits.
theorem startStay ∀ (follows: Text → Text → Prop) (next: Edge → Prop) (printer: Printer)
    (sound: Sound follows printer)
    (start: printer.atLineStart = True)
    (joins: StartJoins printer.edge next):
    next printer.edge :=
  match sound with
    | (_, _, freshOk, _) =>
      let touch := freshTouch printer.out (freshWhen printer.atLineStart printer.out start freshOk)
      match waiting: printer.suffixes.isEmpty, joins with
        | True, after => rewrite touch then after
        | False, Both same _ => same

theorem lineStartHolds ∀ (follows: Text → Text → Prop) (next: Edge → Prop) (printer: Printer) (indent: Nat)
    (sound: Sound follows printer)
    (joins: StartJoins printer.edge next):
    Holds follows next (printer.lineStart indent) :=
  match start: printer.atLineStart with
    | True => (sound, (startStay follows next printer sound start joins))
    | False =>
      newlineHolds follows next printer (printer.continuation indent) sound (startBreak next printer.edge joins)

theorem hereHolds ∀ (follows: Text → Text → Prop) (next: Edge → Prop) (printer: Printer) (indent: Nat)
    (sound: Sound follows printer)
    (start: printer.atLineStart = True) (after: next printer.edge):
    Holds follows next { printer | owed = Some indent, lineIndent = indent } :=
  match sound with | (pairs, _, freshOk, waits) => (((pairs, (Inr start), freshOk, waits)), after)

theorem breakWaits ∀ (follows: Text → Text → Prop) (suffixes out: List Text)
    (waits: WaitsParts follows suffixes out):
    WaitsParts follows suffixes ["\n", ..out] :=
  match suffixes, waits with
    | [], _ => byComputing
    | [only], Both filled _ => (filled, (Inl byComputing))
    | [first, second, ..more], never => never

theorem breakEdge ∀ (suffixes out: List Text) (fresh: Fresh out): edgeOf suffixes ["\n", ..out] = edgeOf suffixes out :=
  match empty: suffixes.isEmpty with
    | True => rewrite freshTouch out fresh
    | False => rewrite freshTouch out fresh

--| A kept blank line: the edge is as it was, a line start.
theorem blankedHolds ∀ (follows: Text → Text → Prop) (next: Edge → Prop) (printer: Printer)
    (sound: Sound follows printer)
    (start: printer.atLineStart = True) (after: next printer.edge):
    Holds follows next { printer | out = ["\n", ..printer.out], newlinesAtEnd = printer.newlinesAtEnd + 1 } :=
  match sound with
    | (pairs, owedOk, freshOk, waits) =>
      let edge: next (edgeOf printer.suffixes ["\n", ..printer.out]) :=
        rewrite breakEdge printer.suffixes printer.out (freshWhen printer.atLineStart printer.out start freshOk) then
          after
      (
        ((
          ((byComputing, (breakAccepts follows printer.out), pairs)),
          owedOk,
          (Inr byComputing),
          (breakWaits follows printer.suffixes printer.out waits)
        )),
        edge
      )

theorem blankHolds ∀ (follows: Text → Text → Prop) (next: Edge → Prop) (printer: Printer)
    (sound: Sound follows printer) (after: next printer.edge):
    Holds follows next printer.blank :=
  match blank: printer.atLineStart && printer.started && printer.newlinesAtEnd < 2 with
    | False => (sound, after)
    | True => blankedHolds follows next printer sound (andTrueLeft _ _ blank) after

--| A trailing comment starts waiting where a space may follow the line.
theorem suffixHolds ∀ (follows: Text → Text → Prop) (next: Edge → Prop) (printer: Printer) (comment: Text)
    (sound: Sound follows printer)
    (filled: comment.isEmpty = False)
    (joins: SuffixJoins follows printer.edge next):
    Holds follows next { printer | suffixes = printer.suffixes ++ [comment] } :=
  match sound with
    | (pairs, owedOk, freshOk, _) =>
      match waiting: printer.suffixes.isEmpty, joins with
        | False, never => (Bool.falseNotTrue never).impossible
        | True, Both ok after =>
          let none := emptyNil printer.suffixes waiting
          let parts: SoundParts follows printer.out printer.owed printer.atLineStart (printer.suffixes ++ [comment]) :=
            rewrite none then
              (
                pairs,
                owedOk,
                freshOk,
                filled,
                (trimmedReady follows printer.out pairs (touchReady follows printer.out ok))
              )
          let edge: next (edgeOf (printer.suffixes ++ [comment]) printer.out) := rewrite none then after
          (parts, edge)

theorem eitherStep ∀ (follows: Text → Text → Prop) (flat clear: Bool) (yes no: Printer) (rest: List Cmd)
    (whenYes: clear = True → Holds follows (edge => StackJoins follows rest edge) yes)
    (whenNo: Holds follows (edge => StackJoins follows rest edge) no):
    Holds follows
      (edge => StackJoins follows (if flat && clear then (yes, rest) else (no, rest)).snd edge)
      (if flat && clear then (yes, rest) else (no, rest)).fst :=
  match flat, clear, whenYes with
    | True, True, whenYes => whenYes byComputing
    | True, False, _ => whenNo
    | False, True, _ => whenNo
    | False, False, _ => whenNo

--| A step of a reading keeps the printer sound, and the work list it
--| leaves joins from the edge it leaves.
theorem stepJoins ∀ (follows: Text → Text → Prop) (printer: Printer) (cmd: Cmd)
    (rest: List Cmd) (result: (Printer, List Cmd))
    (steps: StepsTo printer cmd rest result)
    (sound: Sound follows printer)
    (joins: StackJoins follows [cmd, ..rest] printer.edge):
    Holds follows (edge => StackJoins follows result.snd edge) result.fst :=
  match cmd, steps, joins with
    | FillSep indent item, Inl (Both clear flat), joins =>
      rewrite flat then
        sepWrite follows
          (edge => Joins follows item edge (after => StackJoins follows rest after))
          printer
          indent
          sound
          clear
          joins
    | FillSep indent item, Inr broken, joins =>
      rewrite broken then
        newlineHolds follows
          (edge => Joins follows item edge (after => StackJoins follows rest after))
          printer
          indent
          sound
          (sepBreak follows
            (edge => Joins follows item edge (after => StackJoins follows rest after))
            printer.edge
            joins)
    | Print indent mode doc, steps, joins =>
      match doc, steps, joins with
        | Empty, steps, joins => rewrite steps then (sound, joins)
        | BreakParent, steps, joins => rewrite steps then (sound, joins)
        | Chunk text width, steps, joins =>
          rewrite steps then
            writeHolds follows (edge => StackJoins follows rest edge) printer indent text width sound joins
        | Closing text, steps, joins =>
          rewrite steps then closeHolds follows (edge => StackJoins follows rest edge) printer text sound joins
        | Line, steps, joins =>
          rewrite steps then
            eitherStep follows mode.isFlat printer.suffixes.isEmpty
              (printer.write indent " " 1)
              (printer.newline indent)
              rest
              (clear => sepWrite follows (edge => StackJoins follows rest edge) printer indent sound clear joins)
              (newlineHolds follows
                (edge => StackJoins follows rest edge)
                printer
                indent
                sound
                (sepBreak follows (edge => StackJoins follows rest edge) printer.edge joins))
        | SoftLine, steps, joins =>
          rewrite steps then
            eitherStep follows mode.isFlat printer.suffixes.isEmpty printer
              (printer.newline indent)
              rest
              (clear => (sound, (softStay (edge => StackJoins follows rest edge) printer clear joins)))
              (newlineHolds follows
                (edge => StackJoins follows rest edge)
                printer
                indent
                sound
                (softBreak (edge => StackJoins follows rest edge) printer.edge joins))
        | HardLine, steps, joins =>
          rewrite steps then newlineHolds follows (edge => StackJoins follows rest edge) printer indent sound joins
        | CommentEnd, steps, joins =>
          rewrite steps then
            newlineHolds follows (edge => StackJoins follows rest edge) printer printer.lineIndent sound joins
        | LineStart, steps, joins =>
          rewrite steps then lineStartHolds follows (edge => StackJoins follows rest edge) printer indent sound joins
        | LineStartHere, steps, joins =>
          match start: printer.atLineStart with
            | True =>
              rewrite steps then
                hereHolds follows
                  (edge => StackJoins follows rest edge)
                  printer
                  indent
                  sound
                  start
                  (startStay follows (edge => StackJoins follows rest edge) printer sound start joins)
            | False =>
              rewrite steps then
                newlineHolds follows
                  (edge => StackJoins follows rest edge)
                  printer
                  indent
                  sound
                  (startBreak (edge => StackJoins follows rest edge) printer.edge joins)
        | Blank, steps, joins =>
          rewrite steps then blankHolds follows (edge => StackJoins follows rest edge) printer sound joins
        | Nest more inner, steps, joins => rewrite steps then (sound, joins)
        | OneLineBelow inner, steps, joins => rewrite steps then (sound, joins)
        | Flatten inner, steps, joins => rewrite steps then (sound, joins)
        | LineSuffix comment, steps, Both filled joins =>
          rewrite steps then
            suffixHolds follows (edge => StackJoins follows rest edge) printer comment sound filled joins
        | Group inner hard, Inl (Both _ flat), joins => rewrite flat then (sound, joins)
        | Group inner hard, Inr (Both _ broken), joins => rewrite broken then (sound, joins)
        | Concat docs, steps, joins =>
          rewrite steps then (sound, (printsJoin follows indent mode docs rest printer.edge joins))
        | Fill [], steps, joins => rewrite steps then (sound, joins)
        | Fill [first, ..others], Inl (Both _ flat), joins =>
          rewrite flat then
            (
              sound,
              (printsJoin follows indent Flat
                (Doc.joinLines [first, ..others])
                rest
                printer.edge
                (linesJoin follows first others printer.edge (edge => StackJoins follows rest edge) joins))
            )
        | Fill [first, ..others], Inr (Both _ (Witness firstMode broken)), joins =>
          rewrite broken then
            (
              sound,
              (joinsWeaker follows first printer.edge
                (after => SepsJoin follows others after (edge => StackJoins follows rest edge))
                (after => StackJoins follows (others.map (FillSep indent) ++ rest) after)
                (after later => fillSepsJoin follows indent others rest after later)
                joins)
            )
        | Choice options, Inl (Both _ flat), joins =>
          rewrite flat then
            (sound, (headOrJoins follows options printer.edge (edge => StackJoins follows rest edge) joins))
        | Choice options, Inr (Both _ (Witness chosen (Both isOption broken))), joins =>
          rewrite broken then
            (
              sound,
              (optionJoins follows chosen options printer.edge (edge => StackJoins follows rest edge) isOption joins)
            )

--| Through every reading of a work list that joins from the printer's
--| edge, however far it gets, the printer stays sound.
theorem readingJoins ∀ (follows: Text → Text → Prop) (printer: Printer) (fuel: Nat) (stack: List Cmd) (final: Printer)
    (reads: Reads printer fuel stack final)
    (sound: Sound follows printer)
    (joins: StackJoins follows stack printer.edge):
    Sound follows final :=
  match fuel, stack, reads, joins with
    | Zero, [], reads, _ => rewrite reads then sound
    | Succ more, [], reads, _ => rewrite reads then sound
    | Zero, [cmd, ..rest], reads, _ => rewrite reads then sound
    | Succ more, [cmd, ..rest], Witness next (Witness later (Both steps laterReads)), joins =>
      match stepJoins follows printer cmd rest (next, later) steps sound joins with
        | Both nextSound nextJoins => readingJoins follows next more later final laterReads nextSound nextJoins

theorem startSound ∀ (follows: Text → Text → Prop) (width: Nat): Sound follows (Printer.start width) :=
  (byComputing, (Inl byComputing), (Inr byComputing), byComputing)

--| `printedPieces` are the pieces `print` joins, so that what is said of
--| `print`'s text can be said of the same pieces as `printLays`: what
--| holds of every word of the document holds of every word printed, and
--| each piece stands after one it may follow.
theorem printedJoins ∀ (follows: Text → Text → Prop) (holds: Text → Prop) (doc: Doc) (width: Nat)
    (uniform: Uniform doc)
    (joins: Joins follows doc (Plain None) (after => True))
    (all: Every holds doc.words):
    print doc width = (printedPieces doc width).joinWith ""
      ∧ Every holds (wordsOf (printedPieces doc width))
      ∧ Pairs follows (printedPieces doc width).reverse :=
  let fuel := 3 * doc.size + 3
  let ran := (Printer.start width).run fuel fuel [Print 0 Break doc]
  let read: Every holds ran.words :=
    readingEvery holds
      (Printer.start width)
      fuel
      [Print 0 Break doc]
      ran
      (runIsReading (Printer.start width) fuel fuel [Print 0 Break doc])
      ((uniform, byComputing))
      (rewrite List.appendNil doc.words then all)
  let sound: Sound follows ran :=
    readingJoins follows
      (Printer.start width)
      fuel
      [Print 0 Break doc]
      ran
      (runIsReading (Printer.start width) fuel fuel [Print 0 Break doc])
      (startSound follows width)
      joins
  match flushWritten ran with
    | (written, _) =>
      let flushed: Every holds ran.flushSuffixes.written := rewrite written then read
      (byComputing, flushed, (rewrite List.reverseReverse ran.flushSuffixes.out then finalPairs follows ran sound))

--| The words `print` writes are the document's, at every width, in an
--| order no filter can tell from the document's if it keeps no closer,
--| or keeps no trailing comment (`readingWords`, of `print`'s own
--| reading).
theorem printedWords ∀ (keep: Text → Bool) (closer suffix: Text → Prop) (doc: Doc) (width: Nat)
    (uniform: Uniform doc)
    (marked: Marked closer suffix doc)
    (apart: (∀ (text: Text) => closer text → keep text = False)
      ∨ (∀ (comment: Text) => suffix comment → keep comment = False)):
    (wordsOf (printedPieces doc width)).filter keep = doc.words.filter keep :=
  let fuel := 3 * doc.size + 3
  let ran := (Printer.start width).run fuel fuel [Print 0 Break doc]
  let bound := stepsUnderSize doc
  let read: ran.words.filter keep = ((Printer.start width).words ++ stackWords [Print 0 Break doc]).filter keep :=
    readingWords keep closer suffix
      (Printer.start width)
      fuel
      [Print 0 Break doc]
      ran
      (runIsReading (Printer.start width) fuel fuel [Print 0 Break doc])
      ((uniform, byComputing))
      ((marked, byComputing))
      byComputing
      apart
      (arithmetic)
  match flushWritten ran with
    | (written, _) =>
      calc ran.flushSuffixes.written.filter keep
        _ = ran.words.filter keep := Eq.cong ((words: List Text) => words.filter keep) written
        _ = (doc.words ++ []).filter keep := read
        _ = doc.words.filter keep := Eq.cong ((words: List Text) => words.filter keep) (List.appendNil doc.words)

--| `printedWords` computes, and its hypotheses can be met: of `x) -- c`,
--| printed from `x`, the comment, then the closer, a filter that drops
--| the closer sees the document's order.
theorem printedWordsExample ∀ (width: Nat):
    (wordsOf (printedPieces (Concat [Chunk "x" 1, LineSuffix "-- c", Closing ")"]) width)).filter (word => word != ")")
      = ["x", "-- c"] :=
  printedWords
    (word => word != ")")
    (text => text = ")")
    (comment => True)
    (Concat [Chunk "x" 1, LineSuffix "-- c", Closing ")"])
    width
    ((byComputing, byComputing, byComputing, byComputing))
    ((byComputing, byComputing, byComputing, byComputing))
    (Inl (text isCloser => rewrite isCloser))
