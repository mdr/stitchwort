--| Which printed words touch the piece before them: no space or line
--| break between, so the lexer reads the two as glued. `touchesOf` lists
--| every word of the printed pieces, in the order printed, with whether
--| the piece straight before it is a word too.
--|
--| `Touches` says it of the document, in continuation style as `Joins`
--| and `Puts` are: from where the printer is (`Seam`: at a line start,
--| after pieces on the line, or with a trailing comment waiting) and the
--| words printed so far, a document hands every seam and list of words
--| it may leave to what comes after. It doesn't follow modes: a `Line`
--| may be a space or a break wherever it stands, and either way the word
--| after it touches nothing. A word straight after another, with only
--| silent documents between (`Nothing`, `Mark`, `BreakParent`, a group's
--| edge), touches it at every width; one after a `Line`, a space or a
--| line break touches nothing (`printTouches`).
--|
--| The list is in the order printed, which is the document's: a closer
--| written while a trailing comment waits comes before the comment in the
--| text, and the comment is listed where it is printed, when its line
--| ends (`Seam.ending`).

import Doc (..)
import Bool (not)
import Doc.Proofs (..)

--| A printed word, and whether it touches the piece before it: that
--| piece is a word too, with no space or line break between them.
type Doc.Proofs.Touch = { word: Text, touching: Bool }

--| Whether the output (its pieces the last first) ends with a word: a
--| piece that isn't layout.
def Doc.Proofs.endsInWord: List Text → Bool
  | [] => False
  | [last, .._] => not (isLayout last)

--| The words so far, with `text` written next after a piece that is a
--| word or not (`word`): layout adds none.
def Doc.Proofs.touchAfter (word: Bool) (text: Text) (trace: List Touch): List Touch :=
  if isLayout text then trace else trace ++ [{ word = text, touching = word }]

--| The words of the output (its pieces the last first), in the order
--| printed, each with whether it touches the piece before it.
def Doc.Proofs.touchesOf: List Text → List Touch
  | [] => []
  | [piece, ..earlier] => touchAfter (endsInWord earlier) piece (touchesOf earlier)

--| Where the printer is on its line, as far as touching goes.
type Doc.Proofs.Seam =
  --| At the start of a line, nothing on it: the next word touches
  --| nothing.
  | Begun
  --| Pieces on the line and no trailing comment waiting; `word` says the
  --| last piece is a word, which the next word would touch.
  | Along (word: Bool)
  --| `comment` waits for the end of the line. A closer joins the line
  --| before it, touching what is there if `word`; any other word starts
  --| the next line.
  | Awaiting (word: Bool) (comment: Text)

--| The words a line break at `seam` writes: the comment waiting, after a
--| space.
def Doc.Proofs.Seam.ending: Seam → List Touch
  | Awaiting _ comment => [{ word = comment, touching = False }]
  | _ => []

--| Text put on the line after a piece that is a word or not (`word`).
def Doc.Proofs.PutTouches (word: Bool) (text: Text) (trace: List Touch) (next: Seam → List Touch → Prop): Prop :=
  next (Along (not (isLayout text))) (touchAfter word text trace)

--| A chunk: nothing if empty; after a waiting comment spaces are held,
--| touching nothing later, and anything else starts a new line.
def Doc.Proofs.WriteTouches (seam: Seam) (text: Text) (trace: List Touch) (next: Seam → List Touch → Prop): Prop :=
  if text.isEmpty then next seam trace
  else
    match seam with
      | Begun => PutTouches False text trace next
      | Along word => PutTouches word text trace next
      | Awaiting _ comment =>
        if text.all (char => char == ' ') then next (Awaiting False comment) trace
        else PutTouches False text (trace ++ seam.ending) next

--| A closer: a chunk where no comment waits; where one waits, on its
--| line, before it.
def Doc.Proofs.CloseTouches (seam: Seam) (text: Text) (trace: List Touch) (next: Seam → List Touch → Prop): Prop :=
  match seam with
    | Awaiting word comment =>
      if text.isEmpty then next seam trace
      else next (Awaiting (not (isLayout text)) comment) (touchAfter word text trace)
    | _ => WriteTouches seam text trace next

--| A `Line` or a fill's separator: a space (held after a waiting
--| comment) or a line break.
def Doc.Proofs.SepTouches (seam: Seam) (trace: List Touch) (next: Seam → List Touch → Prop): Prop := match seam with
  | Awaiting _ comment => next (Awaiting False comment) trace ∧ next Begun (trace ++ seam.ending)
  | _ => next (Along False) trace ∧ next Begun trace

--| A `Displaced` element's contents, from where they start: a waiting
--| comment's line ends first.
def Doc.Proofs.DisplacedTouches (seam: Seam) (trace: List Touch) (inner: Seam → List Touch → Prop): Prop :=
  match seam with
    | Awaiting _ _ => inner Begun (trace ++ seam.ending)
    | _ => inner seam trace

--| A trailing comment, after pieces on its line, with no other waiting.
def Doc.Proofs.SuffixTouches (comment: Text) (seam: Seam) (trace: List Touch) (next: Seam → List Touch → Prop): Prop :=
  match seam with
    | Along word => isLayout comment = False ∧ next (Awaiting word comment) trace
    | _ => False

--| From `seam` with the words `trace` printed, every way `doc` may print
--| lists its words as `next` is told, and every seam it may leave
--| satisfies `next`. A line break ends the line: the comment waiting is
--| printed, and the next word touches nothing.
def Doc.Proofs.Touches (doc: Doc) (seam: Seam) (trace: List Touch) (next: Seam → List Touch → Prop): Prop :=
  match doc with
    | Doc.Nothing => next seam trace
    | BreakParent => next seam trace
    | Blank => next seam trace
    | Mark _ => next seam trace
    | Chunk text _ => WriteTouches seam text trace next
    | Closing text => CloseTouches seam text trace next
    | Line => SepTouches seam trace next
    | SoftLine => next seam trace ∧ next Begun (trace ++ seam.ending)
    | HardLine => next Begun (trace ++ seam.ending)
    | LineStart => next Begun (trace ++ seam.ending)
    | LineStartHere => next Begun (trace ++ seam.ending)
    | CloserLine _ => next Begun (trace ++ seam.ending)
    | Nest _ inner => Touches inner seam trace next
    | Align inner => Touches inner seam trace next
    | AlignInset inner => Touches inner seam trace next
    | Displaced inner => DisplacedTouches seam trace (start written => Touches inner start written next)
    | Group inner _ => Touches inner seam trace next
    | NarrowGroup _ inner _ => Touches inner seam trace next
    | IdGroup _ inner _ => Touches inner seam trace next
    | IfBroken _ broken flat => Touches broken seam trace next ∧ Touches flat seam trace next
    | Flatten inner => Touches inner seam trace next
    | OneLineBelow inner => Touches inner Begun (trace ++ seam.ending) next
    | Concat docs => TouchesAll docs seam trace next
    | Fill items => FillTouches items seam trace next
    | Choice options => OptionsTouch options seam trace next
    | LineSuffix comment => SuffixTouches comment seam trace next

--| The documents one after another.
def Doc.Proofs.TouchesAll (docs: List Doc) (seam: Seam) (trace: List Touch) (next: Seam → List Touch → Prop): Prop :=
  match docs with
    | [] => next seam trace
    | [doc, ..rest] => Touches doc seam trace (after later => TouchesAll rest after later next)

--| A fill's items, a separator before each but the first.
def Doc.Proofs.FillTouches (items: List Doc) (seam: Seam) (trace: List Touch) (next: Seam → List Touch → Prop): Prop :=
  match items with
    | [] => next seam trace
    | [first, ..others] => Touches first seam trace (after later => SepsTouch others after later next)

--| The items of a fill, each after a separator.
def Doc.Proofs.SepsTouch (items: List Doc) (seam: Seam) (trace: List Touch) (next: Seam → List Touch → Prop): Prop :=
  match items with
    | [] => next seam trace
    | [item, ..more] => SepTouches seam trace (middle between =>
      Touches item middle between (after later => SepsTouch more after later next))

--| Whichever option a choice takes.
def Doc.Proofs.OptionsTouch (options: List Doc) (seam: Seam) (trace: List Touch) (next: Seam → List Touch → Prop):
    Prop :=
  match options with
    | [] => next seam trace
    | [last] => Touches last seam trace next
    | [option, ..others] => Touches option seam trace next ∧ OptionsTouch others seam trace next

--| The work list, from `seam` to the end, where `spec` is asked of the
--| seam and the words at the end.
def Doc.Proofs.StackTouches (spec: Seam → List Touch → Prop) (stack: List Cmd) (seam: Seam) (trace: List Touch): Prop :=
  match stack with
    | [] => spec seam trace
    | [Print _ _ doc, ..rest] => Touches doc seam trace (after later => StackTouches spec rest after later)
    | [FillSep _ item, ..rest] => SepTouches seam trace (middle between =>
      Touches item middle between (after later => StackTouches spec rest after later))

-- A weaker continuation still holds.

--| `WriteTouches` holds with a weaker continuation.
theorem Doc.Proofs.writeTouchesWeaker ∀ (seam: Seam) (text: Text) (trace: List Touch)
    (strong weak: Seam → List Touch → Prop)
    (implies: ∀ (after: Seam) (later: List Touch) => strong after later → weak after later)
    (touches: WriteTouches seam text trace strong):
    WriteTouches seam text trace weak :=
  match empty: text.isEmpty, touches with
    | True, touches => implies _ _ touches
    | False, touches =>
      match seam, touches with
        | Begun, touches => implies _ _ touches
        | Along word, touches => implies _ _ touches
        | Awaiting word comment, touches =>
          match spaces: text.all (char => char == ' '), touches with
            | True, touches => implies _ _ touches
            | False, touches => implies _ _ touches

--| `CloseTouches` holds with a weaker continuation.
theorem Doc.Proofs.closeTouchesWeaker ∀ (seam: Seam) (text: Text) (trace: List Touch)
    (strong weak: Seam → List Touch → Prop)
    (implies: ∀ (after: Seam) (later: List Touch) => strong after later → weak after later)
    (touches: CloseTouches seam text trace strong):
    CloseTouches seam text trace weak :=
  match seam, touches with
    | Begun, touches => writeTouchesWeaker Begun text trace strong weak implies touches
    | Along word, touches => writeTouchesWeaker (Along word) text trace strong weak implies touches
    | Awaiting word comment, touches =>
      match empty: text.isEmpty, touches with
        | True, touches => implies _ _ touches
        | False, touches => implies _ _ touches

--| `SepTouches` holds with a weaker continuation.
theorem Doc.Proofs.sepTouchesWeaker ∀ (seam: Seam) (trace: List Touch) (strong weak: Seam → List Touch → Prop)
    (implies: ∀ (after: Seam) (later: List Touch) => strong after later → weak after later)
    (touches: SepTouches seam trace strong):
    SepTouches seam trace weak :=
  match seam, touches with
    | Begun, Both flat broken => ((implies _ _ flat), (implies _ _ broken))
    | Along word, Both flat broken => ((implies _ _ flat), (implies _ _ broken))
    | Awaiting word comment, Both flat broken => ((implies _ _ flat), (implies _ _ broken))

--| `Touches` holds with a weaker continuation, if it holds with a
--| stronger one.
theorem Doc.Proofs.touchesWeaker ∀ (doc: Doc) (seam: Seam) (trace: List Touch) (strong weak: Seam → List Touch → Prop)
    (implies: ∀ (after: Seam) (later: List Touch) => strong after later → weak after later)
    (touches: Touches doc seam trace strong):
    Touches doc seam trace weak :=
  match doc, touches with
    | Doc.Nothing, touches => implies _ _ touches
    | BreakParent, touches => implies _ _ touches
    | Blank, touches => implies _ _ touches
    | Mark key, touches => implies _ _ touches
    | Chunk text width, touches => writeTouchesWeaker seam text trace strong weak implies touches
    | Closing text, touches => closeTouchesWeaker seam text trace strong weak implies touches
    | Line, touches => sepTouchesWeaker seam trace strong weak implies touches
    | SoftLine, Both flat broken => ((implies _ _ flat), (implies _ _ broken))
    | HardLine, touches => implies _ _ touches
    | LineStart, touches => implies _ _ touches
    | LineStartHere, touches => implies _ _ touches
    | CloserLine key, touches => implies _ _ touches
    | Nest more inner, touches => touchesWeaker inner seam trace strong weak implies touches
    | Align inner, touches => touchesWeaker inner seam trace strong weak implies touches
    | AlignInset inner, touches => touchesWeaker inner seam trace strong weak implies touches
    | Displaced inner, touches =>
      match seam, touches with
        | Begun, touches => touchesWeaker inner Begun trace strong weak implies touches
        | Along word, touches => touchesWeaker inner (Along word) trace strong weak implies touches
        | Awaiting word comment, touches =>
          touchesWeaker inner Begun (trace ++ [{ word = comment, touching = False }]) strong weak implies touches
    | Group inner hard, touches => touchesWeaker inner seam trace strong weak implies touches
    | NarrowGroup max inner hard, touches => touchesWeaker inner seam trace strong weak implies touches
    | IdGroup id inner hard, touches => touchesWeaker inner seam trace strong weak implies touches
    | IfBroken id broken flat, Both brokenTouches flatTouches => (
      (touchesWeaker broken seam trace strong weak implies brokenTouches),
      (touchesWeaker flat seam trace strong weak implies flatTouches)
    )
    | Flatten inner, touches => touchesWeaker inner seam trace strong weak implies touches
    | OneLineBelow inner, touches => touchesWeaker inner Begun (trace ++ seam.ending) strong weak implies touches
    | Concat docs, touches => allTouchesWeaker docs seam trace strong weak implies touches
    | Fill items, touches => fillTouchesWeaker items seam trace strong weak implies touches
    | Choice options, touches => optionsTouchWeaker options seam trace strong weak implies touches
    | LineSuffix comment, touches =>
      match seam, touches with
        | Along word, Both word touches => (word, (implies _ _ touches))
        | Begun, never => never
        | Awaiting word comment, never => never

--| `TouchesAll` holds with a weaker continuation.
theorem Doc.Proofs.allTouchesWeaker ∀ (docs: List Doc) (seam: Seam) (trace: List Touch)
    (strong weak: Seam → List Touch → Prop)
    (implies: ∀ (after: Seam) (later: List Touch) => strong after later → weak after later)
    (touches: TouchesAll docs seam trace strong):
    TouchesAll docs seam trace weak :=
  match docs, touches with
    | [], touches => implies _ _ touches
    | [doc, ..rest], touches =>
      touchesWeaker doc seam trace
        (after later => TouchesAll rest after later strong)
        (after later => TouchesAll rest after later weak)
        (after later others => allTouchesWeaker rest after later strong weak implies others)
        touches

--| `FillTouches` holds with a weaker continuation.
theorem Doc.Proofs.fillTouchesWeaker ∀ (items: List Doc) (seam: Seam) (trace: List Touch)
    (strong weak: Seam → List Touch → Prop)
    (implies: ∀ (after: Seam) (later: List Touch) => strong after later → weak after later)
    (touches: FillTouches items seam trace strong):
    FillTouches items seam trace weak :=
  match items, touches with
    | [], touches => implies _ _ touches
    | [first, ..others], touches =>
      touchesWeaker first seam trace
        (after later => SepsTouch others after later strong)
        (after later => SepsTouch others after later weak)
        (after later others' => sepsTouchWeaker others after later strong weak implies others')
        touches

--| `SepsTouch` holds with a weaker continuation.
theorem Doc.Proofs.sepsTouchWeaker ∀ (items: List Doc) (seam: Seam) (trace: List Touch)
    (strong weak: Seam → List Touch → Prop)
    (implies: ∀ (after: Seam) (later: List Touch) => strong after later → weak after later)
    (touches: SepsTouch items seam trace strong):
    SepsTouch items seam trace weak :=
  match items, touches with
    | [], touches => implies _ _ touches
    | [item, ..more], touches =>
      sepTouchesWeaker seam trace
        (middle between => Touches item middle between (after later => SepsTouch more after later strong))
        (middle between => Touches item middle between (after later => SepsTouch more after later weak))
        (middle between inner =>
          touchesWeaker item middle between
            (after later => SepsTouch more after later strong)
            (after later => SepsTouch more after later weak)
            (after later others => sepsTouchWeaker more after later strong weak implies others)
            inner)
        touches

--| `OptionsTouch` holds with a weaker continuation.
theorem Doc.Proofs.optionsTouchWeaker ∀ (options: List Doc) (seam: Seam) (trace: List Touch)
    (strong weak: Seam → List Touch → Prop)
    (implies: ∀ (after: Seam) (later: List Touch) => strong after later → weak after later)
    (touches: OptionsTouch options seam trace strong):
    OptionsTouch options seam trace weak :=
  match options, touches with
    | [], touches => implies _ _ touches
    | [last], touches => touchesWeaker last seam trace strong weak implies touches
    | [option, second, ..others], Both first rest => (
      (touchesWeaker option seam trace strong weak implies first),
      (optionsTouchWeaker [second, ..others] seam trace strong weak implies rest)
    )

-- What a step pushes on the work list touches as the document it came from.

--| Docs printed in order, then the work list.
theorem Doc.Proofs.printsTouch ∀ (spec: Seam → List Touch → Prop) (indent: Nat) (mode: Mode) (docs: List Doc)
    (rest: List Cmd) (seam: Seam) (trace: List Touch)
    (touches: TouchesAll docs seam trace (after later => StackTouches spec rest after later)):
    StackTouches spec (docs.map (Print indent mode) ++ rest) seam trace :=
  match docs, touches with
    | [], touches => touches
    | [doc, ..later], touches =>
      touchesWeaker doc seam trace
        (after written => TouchesAll later after written (final words => StackTouches spec rest final words))
        (after written => StackTouches spec (later.map (Print indent mode) ++ rest) after written)
        (after written others => printsTouch spec indent mode later rest after written others)
        touches

--| A flat fill is its items with a `Line` between each two.
theorem Doc.Proofs.linesTouch ∀ (first: Doc) (others: List Doc) (seam: Seam)
    (trace: List Touch) (next: Seam → List Touch → Prop)
    (touches: Touches first seam trace (after later => SepsTouch others after later next)):
    TouchesAll (Doc.joinLines [first, ..others]) seam trace next :=
  match others, touches with
    | [], touches => touches
    | [second, ..rest], touches =>
      touchesWeaker first seam trace
        (after later => SepsTouch [second, ..rest] after later next)
        (after later => TouchesAll [Line, ..Doc.joinLines [second, ..rest]] after later next)
        (after later seps =>
          sepTouchesWeaker after later
            (middle between => Touches second middle between (final words => SepsTouch rest final words next))
            (middle between => TouchesAll (Doc.joinLines [second, ..rest]) middle between next)
            (middle between inner => linesTouch second rest middle between next inner)
            seps)
        touches

--| A broken fill's separators and items, as the work list holds them.
theorem Doc.Proofs.fillSepsTouch ∀ (spec: Seam → List Touch → Prop) (indent: Nat) (items: List Doc) (rest: List Cmd)
    (seam: Seam) (trace: List Touch)
    (touches: SepsTouch items seam trace (after later => StackTouches spec rest after later)):
    StackTouches spec (items.map (FillSep indent) ++ rest) seam trace :=
  match items, touches with
    | [], touches => touches
    | [item, ..more], touches =>
      sepTouchesWeaker seam trace
        (middle between =>
          Touches item middle between (after later =>
            SepsTouch more after later (final words => StackTouches spec rest final words)))
        (middle between =>
          Touches item middle between (after later =>
            StackTouches spec (more.map (FillSep indent) ++ rest) after later))
        (middle between inner =>
          touchesWeaker item middle between
            (after later => SepsTouch more after later (final words => StackTouches spec rest final words))
            (after later => StackTouches spec (more.map (FillSep indent) ++ rest) after later)
            (after later seps => fillSepsTouch spec indent more rest after later seps)
            inner)
        touches

--| A doc that is one of the options of a choice touches as the options do.
theorem Doc.Proofs.optionTouches ∀ (chosen: Doc) (options: List Doc) (seam: Seam)
    (trace: List Touch) (next: Seam → List Touch → Prop)
    (isOption: IsOption chosen options)
    (touches: OptionsTouch options seam trace next):
    Touches chosen seam trace next :=
  match options, isOption, touches with
    | [], picked, touches => rewrite picked then touches
    | [last], picked, touches => rewrite picked then touches
    | [option, second, ..others], Inl picked, Both first _ => rewrite picked then first
    | [option, second, ..others], Inr later, Both _ rest =>
      optionTouches chosen [second, ..others] seam trace next later rest

--| The first option of a choice touches as the options do.
theorem Doc.Proofs.headOrTouches ∀ (options: List Doc) (seam: Seam) (trace: List Touch) (next: Seam → List Touch → Prop)
    (touches: OptionsTouch options seam trace next):
    Touches (options.headOr Doc.Nothing) seam trace next :=
  match options, touches with
    | [], touches => touches
    | [last], touches => touches
    | [option, second, ..others], Both first _ => first

--| The branch an `IfBroken` takes touches if both do.
theorem Doc.Proofs.pickTouches ∀ (modes: List (Nat, Mode)) (id: Nat) (broken flat: Doc) (seam: Seam)
    (trace: List Touch) (next: Seam → List Touch → Prop)
    (touches: Touches (IfBroken id broken flat) seam trace next):
    Touches (pickBranch modes id broken flat) seam trace next :=
  match pickEither modes id broken flat, touches with
    | Inl isBroken, Both brokenTouches _ => rewrite isBroken then brokenTouches
    | Inr isFlat, Both _ flatTouches => rewrite isFlat then flatTouches

-- The printer's side.

--| What the printer has printed, as touches: its output's words.
def Doc.Printer.touches (printer: Printer): List Touch := touchesOf printer.out

--| The seam of a printer with these parts.
def Doc.Proofs.seamOf (suffixes: List Text) (atLineStart: Bool) (heldSpaces: Nat) (out: List Text): Seam :=
  match suffixes with
    | [] => if atLineStart then Begun else Along (endsInWord out)
    | [comment, .._] => Awaiting (heldSpaces == 0 && endsInWord out) comment

--| Where the printer is, as a seam.
def Doc.Printer.seam (printer: Printer): Seam :=
  seamOf printer.suffixes printer.atLineStart printer.heldSpaces printer.out

--| What may wait: nothing, with no spaces held; or one comment that isn't
--| layout, on a line with pieces on it.
def Doc.Proofs.WaitsTouch (suffixes: List Text) (atLineStart: Bool) (heldSpaces: Nat): Prop := match suffixes with
  | [] => heldSpaces = 0
  | [only] => isLayout only = False ∧ atLineStart = False
  | _ => False

--| `SeamSound`, from the printer's parts.
def Doc.Proofs.SeamParts (out: List Text) (owed: Option Nat) (atLineStart: Bool)
    (suffixes: List Text) (heldSpaces: Nat):
    Prop :=
  (owed = None ∨ atLineStart = True) ∧ (atLineStart = False ∨ Fresh out) ∧ WaitsTouch suffixes atLineStart heldSpaces

--| Indentation is owed only at a line start, a line start has nothing on
--| it, and what waits is as `WaitsTouch` says.
def Doc.Proofs.SeamSound (printer: Printer): Prop :=
  SeamParts printer.out printer.owed printer.atLineStart printer.suffixes printer.heldSpaces

--| The printer is sound and its seam and words satisfy `next`.
def Doc.Proofs.SeamHolds (next: Seam → List Touch → Prop) (printer: Printer): Prop :=
  SeamSound printer ∧ next printer.seam printer.touches

--| Spaces add no word.
theorem Doc.Proofs.touchesSpaces ∀ (gap: Text) (out: List Text)
    (spaces: gap.all (char => char == ' ') = True):
    touchesOf [gap, ..out] = touchesOf out :=
  rewrite spacesIsLayout gap spaces

--| A line that has only started ends in no word.
theorem Doc.Proofs.freshEnds ∀ (out: List Text) (fresh: Fresh out): endsInWord out = False := match out, fresh with
  | [], _ => byComputing
  | [last, ..earlier], isBreak => rewrite isBreak

--| Dropping the spaces at the end of the output keeps its words.
theorem Doc.Proofs.touchesTrim ∀ (out: List Text): touchesOf (trimSpaces out) = touchesOf out := match out with
  | [] => byComputing
  | [last, ..earlier] =>
    match spaces: last.all (char => char == ' ') with
      | True => touchesTrim earlier
      | False => byComputing

--| Paying the indentation owed adds no word.
theorem Doc.Proofs.payTouches ∀ (printer: Printer): touchesOf printer.payIndent.out = touchesOf printer.out :=
  match owed: printer.owed with
    | None => byComputing
    | Some Zero => byComputing
    | Some (Succ less) => touchesSpaces (" ".repeat (Succ less)) printer.out (indentSpaces (Succ less))

--| At a line start, text put on the line touches nothing.
theorem Doc.Proofs.payFresh ∀ (printer: Printer) (fresh: Fresh printer.out): endsInWord printer.payIndent.out = False :=
  match owed: printer.owed with
    | None => freshEnds printer.out fresh
    | Some Zero => freshEnds printer.out fresh
    | Some (Succ less) => rewrite spacesIsLayout (" ".repeat (Succ less)) (indentSpaces (Succ less))

--| With nothing owed, text put on the line touches the line's last piece
--| if that is a word.
theorem Doc.Proofs.payNone ∀ (printer: Printer)
    (none: printer.owed = None):
    endsInWord printer.payIndent.out = endsInWord printer.out :=
  match owed: printer.owed, none with
    | None, _ => byComputing
    | Some indent, never => Void.impossible (Option.someNotNone indent never)

--| Paying the indentation owed holds no spaces.
theorem Doc.Proofs.payHeld ∀ (printer: Printer): printer.payIndent.heldSpaces = printer.heldSpaces :=
  match owed: printer.owed with
    | None => byComputing
    | Some Zero => byComputing
    | Some (Succ less) => byComputing

--| With nothing waiting, after pieces on the line, the seam is `Along`.
theorem Doc.Proofs.seamAlong ∀ (printer: Printer)
    (clear: printer.suffixes = [])
    (mid: printer.atLineStart = False):
    printer.seam = Along (endsInWord printer.out) :=
  match same: printer.suffixes, clear with | [], _ => rewrite mid

--| With nothing waiting, at a line start, the seam is `Begun`.
theorem Doc.Proofs.seamBegun ∀ (printer: Printer)
    (clear: printer.suffixes = [])
    (start: printer.atLineStart = True):
    printer.seam = Begun :=
  match same: printer.suffixes, clear with | [], _ => rewrite start

--| Text put on a line with no comment waiting: the next word, touching
--| what the line ends with.
theorem Doc.Proofs.putSeams ∀ (next: Seam → List Touch → Prop) (printer: Printer) (text: Text) (width: Nat)
    (sound: SeamSound printer)
    (clear: printer.suffixes = [])
    (after: next (Along (not (isLayout text))) (touchAfter (endsInWord printer.payIndent.out) text printer.touches)):
    SeamHolds next (printer.put text width) :=
  match sound, payIndentWritten printer with
    | (_, _, waits), (_, suffixes) =>
      let held: printer.heldSpaces = 0 := match same: printer.suffixes, waits, clear with
        | [], waits, _ => waits
      let parts: SeamParts
        [text, ..printer.payIndent.out]
        printer.payIndent.owed
        False
        printer.payIndent.suffixes
        printer.payIndent.heldSpaces :=
        rewrite payOwed printer, suffixes, clear, payHeld printer, held then
          ((Inl byComputing), (Inl byComputing), byComputing)
      let seam: (printer.put text width).seam = Along (not (isLayout text)) :=
        seamAlong (printer.put text width) (Eq.trans suffixes clear) byComputing
      let words: (printer.put text width).touches
        = touchAfter (endsInWord printer.payIndent.out) text printer.touches :=
        let unfolded: (printer.put text width).touches
          = touchAfter (endsInWord printer.payIndent.out) text (touchesOf printer.payIndent.out) :=
          byComputing
        rewrite unfolded, payTouches printer
      (parts, (rewrite seam, words then after))

--| With one comment waiting, the seam is `Awaiting` it.
theorem Doc.Proofs.seamWaits ∀ (printer: Printer) (comment: Text)
    (one: printer.suffixes = [comment]):
    printer.seam = Awaiting (printer.heldSpaces == 0 && endsInWord printer.out) comment :=
  rewrite one

--| What a comment waiting among `suffixes` writes when its line ends.
def Doc.Proofs.endingOf: List Text → List Touch
  | [] => []
  | [comment, .._] => [{ word = comment, touching = False }]

--| What the comment waiting writes when its line ends.
def Doc.Printer.ending (printer: Printer): List Touch := endingOf printer.suffixes

--| The seam's ending is the printer's.
theorem Doc.Proofs.seamEnding ∀ (printer: Printer): printer.seam.ending = printer.ending :=
  match same: printer.suffixes with
    | [] =>
      match start: printer.atLineStart with
        | True => byComputing
        | False => byComputing
    | [comment, ..more] => byComputing

--| Writing the comment that waits adds it, touching nothing: it is
--| written after a space.
theorem Doc.Proofs.flushTouches ∀ (printer: Printer)
    (waits: WaitsTouch printer.suffixes printer.atLineStart printer.heldSpaces):
    touchesOf printer.flushSuffixes.out = touchesOf printer.out ++ printer.ending :=
  match same: printer.suffixes, waits with
    | [], _ => (List.appendNil (touchesOf printer.out)).flipped
    | [only], Both word mid => rewrite mid, word
    | [first, second, ..more], never =>
      match never with
        | ()

--| A line break leaves the printer sound, at a line start.
theorem Doc.Proofs.newlineSeamSound ∀ (printer: Printer) (indent: Nat): SeamSound (printer.newline indent) :=
  match flushWritten { printer | out = trimSpaces printer.out } with
    | (_, none) =>
      let parts: SeamParts
        ["\n", ..({ printer | out = trimSpaces printer.out }).flushSuffixes.out]
        (Some (floored printer.carry indent))
        True
        ({ printer | out = trimSpaces printer.out }).flushSuffixes.suffixes
        0 :=
        rewrite none then ((Inr byComputing), (Inr byComputing), byComputing)
      parts

--| A line break writes the comment waiting, and nothing more.
theorem Doc.Proofs.newlineTouches ∀ (printer: Printer) (indent: Nat)
    (sound: SeamSound printer):
    (printer.newline indent).touches = printer.touches ++ printer.seam.ending :=
  match sound with
    | (_, _, waits) =>
      let unfolded: (printer.newline indent).touches
        = touchesOf ({ printer | out = trimSpaces printer.out }).flushSuffixes.out :=
        byComputing
      rewrite unfolded,
          flushTouches { printer | out = trimSpaces printer.out } waits,
          touchesTrim printer.out,
          seamEnding printer

--| A line break: the comment waiting is written, and the printer is at a
--| line start.
theorem Doc.Proofs.newlineSeams ∀ (next: Seam → List Touch → Prop) (printer: Printer) (indent: Nat)
    (sound: SeamSound printer) (after: next Begun (printer.touches ++ printer.seam.ending)):
    SeamHolds next (printer.newline indent) :=
  let seam: (printer.newline indent).seam = Begun :=
    seamBegun (printer.newline indent) (newlineClear printer indent) byComputing
  ((newlineSeamSound printer indent), (rewrite seam, newlineTouches printer indent sound then after))

--| Spaces held after a waiting comment, written, and the held count, as
--| a closer sees them.
theorem Doc.Proofs.heldTouches ∀ (printer: Printer)
    (mid: printer.atLineStart = False):
    printer.writeHeld.heldSpaces = 0
      ∧ endsInWord printer.writeHeld.out = (printer.heldSpaces == 0 && endsInWord printer.out)
      ∧ touchesOf printer.writeHeld.out = touchesOf printer.out
      ∧ printer.writeHeld.suffixes = printer.suffixes
      ∧ printer.writeHeld.atLineStart = False
      ∧ printer.writeHeld.owed = printer.owed :=
  match start: printer.atLineStart, mid with
    | False, _ =>
      match held: printer.heldSpaces with
        | Zero => (byComputing, byComputing, byComputing, byComputing, byComputing, byComputing)
        | Succ less => (
          byComputing,
          (rewrite spacesIsLayout (" ".repeat (Succ less)) (indentSpaces (Succ less))),
          (touchesSpaces (" ".repeat (Succ less)) printer.out (indentSpaces (Succ less))),
          byComputing,
          byComputing,
          byComputing
        )

--| A closer put on the line of a waiting comment, before it.
theorem Doc.Proofs.putWaitingSeams ∀ (next: Seam → List Touch → Prop) (printer: Printer) (text: Text)
    (width: Nat) (comment: Text)
    (owedNone: printer.owed = None)
    (mid: printer.atLineStart = False)
    (one: printer.suffixes = [comment])
    (word: isLayout comment = False)
    (held: printer.heldSpaces = 0)
    (after: next (Awaiting (not (isLayout text)) comment) (touchAfter (endsInWord printer.out) text printer.touches)):
    SeamHolds next (printer.put text width) :=
  match payIndentWritten printer with
    | (_, suffixes) =>
      let parts: SeamParts
        [text, ..printer.payIndent.out]
        printer.payIndent.owed
        False
        printer.payIndent.suffixes
        printer.payIndent.heldSpaces :=
        rewrite payOwed printer, suffixes, one then ((Inl byComputing), (Inl byComputing), (word, byComputing))
      let seam: (printer.put text width).seam = Awaiting (not (isLayout text)) comment :=
        rewrite seamWaits (printer.put text width) comment (Eq.trans suffixes one), payHeld printer, held
      let words: (printer.put text width).touches = touchAfter (endsInWord printer.out) text printer.touches :=
        let unfolded: (printer.put text width).touches
          = touchAfter (endsInWord printer.payIndent.out) text (touchesOf printer.payIndent.out) :=
          byComputing
        rewrite unfolded, payTouches printer, payNone printer owedNone
      (parts, (rewrite seam, words then after))

--| Spaces add no held count a closer would miss: any spaces held stop it
--| touching.
theorem Doc.Proofs.heldMore ∀ (held: Nat) (text: Text)
    (filled: text.isEmpty = False):
    (held + text.length == 0) = False :=
  match text, filled with
    | MkText [], never => (Bool.falseNotTrue never.flipped).impossible
    | MkText [char, ..chars], _ => byComputing

--| A chunk written where the document said.
theorem Doc.Proofs.writeSeams ∀ (next: Seam → List Touch → Prop) (printer: Printer) (indent: Nat)
    (text: Text) (width: Nat)
    (sound: SeamSound printer)
    (touches: WriteTouches printer.seam text printer.touches next):
    SeamHolds next (printer.write indent text width) :=
  match empty: text.isEmpty, touches with
    | True, touches => (sound, touches)
    | False, touches =>
      match sound with
        | (owedOk, freshOk, waits) =>
          match same: printer.suffixes, waits with
            | [], _ =>
              match start: printer.atLineStart with
                | True =>
                  putSeams next printer text width sound same
                    (rewrite payFresh printer (freshWhen True printer.out start freshOk) then touches)
                | False =>
                  let owedNone: printer.owed = None := match owedOk with
                    | Inl none => none
                    | Inr never => (Bool.falseNotTrue (Eq.trans start.flipped never)).impossible
                  putSeams next printer text width sound same (rewrite payNone printer owedNone then touches)
            | [only], Both word mid =>
              match spaces: text.all (char => char == ' '), touches with
                | True, waiting =>
                  ((owedOk, freshOk, (word, mid)), (rewrite heldMore printer.heldSpaces text empty then waiting))
                | False, waiting =>
                  let broken := printer.newline (printer.continuation indent)
                  let fresh: Fresh broken.out := byComputing
                  putSeams next broken text width
                    (newlineSeamSound printer (printer.continuation indent))
                    (newlineClear printer (printer.continuation indent))
                    (rewrite payFresh broken fresh,
                        newlineTouches printer (printer.continuation indent) sound,
                        seamWaits printer only same then
                      waiting)
            | [first, second, ..more], never =>
              match never with
                | ()

--| A closer written where the document said: as a chunk where no comment
--| waits; where one waits, after the spaces held, on the comment's line.
theorem Doc.Proofs.closeSeams ∀ (next: Seam → List Touch → Prop) (printer: Printer) (text: Text)
    (sound: SeamSound printer)
    (touches: CloseTouches printer.seam text printer.touches next):
    SeamHolds next (printer.close text) :=
  match trueOrFalse printer.suffixes.isEmpty with
    | Inl clear =>
      rewrite closeClear printer 0 text clear then
        writeSeams next printer 0 text text.length sound
          (closeWritesClear printer text printer.touches next (emptyNil printer.suffixes clear) touches)
    | Inr waiting => closeWaitingSeams next printer text sound waiting touches

--| With nothing waiting, a closer is a chunk.
theorem Doc.Proofs.closeWritesClear ∀ (printer: Printer) (text: Text)
    (trace: List Touch) (next: Seam → List Touch → Prop)
    (clear: printer.suffixes = [])
    (touches: CloseTouches printer.seam text trace next):
    WriteTouches printer.seam text trace next :=
  match same: printer.suffixes, clear, touches with
    | [], _, touches =>
      match start: printer.atLineStart, touches with
        | True, touches => touches
        | False, touches => touches

--| A closer on the line of a waiting comment, after the spaces held.
theorem Doc.Proofs.closeWaitingSeams ∀ (next: Seam → List Touch → Prop) (printer: Printer) (text: Text)
    (sound: SeamSound printer)
    (waiting: printer.suffixes.isEmpty = False)
    (touches: CloseTouches printer.seam text printer.touches next):
    SeamHolds next (printer.close text) :=
  match sound with
    | (owedOk, freshOk, waits) =>
      match same: printer.suffixes, waits, touches, waiting with
        | [], _, _, never => (Bool.falseNotTrue never.flipped).impossible
        | [only], Both word mid, touches, _ =>
          match empty: text.isEmpty, touches with
            | True, touches => (sound, touches)
            | False, touches =>
              let owedNone: printer.owed = None := match owedOk with
                | Inl none => none
                | Inr never => (Bool.falseNotTrue (Eq.trans mid.flipped never)).impossible
              match heldTouches printer mid with
                | (held, ends, words, suffixes, start, owed) =>
                  putWaitingSeams next printer.writeHeld text text.length only
                    (Eq.trans owed owedNone)
                    start
                    (Eq.trans suffixes same)
                    word
                    held
                    (rewrite ends, words then touches)
        | [first, second, ..more], never, _, _ =>
          match never with
            | ()

--| A separator that stays flat is a space: a chunk of one.
theorem Doc.Proofs.sepWrites ∀ (seam: Seam) (trace: List Touch) (next: Seam → List Touch → Prop)
    (touches: SepTouches seam trace next):
    WriteTouches seam " " trace next :=
  match seam, touches with
    | Begun, Both flat _ => flat
    | Along word, Both flat _ => flat
    | Awaiting word comment, Both flat _ => flat

--| A separator that breaks ends the line.
theorem Doc.Proofs.sepBreaks ∀ (seam: Seam) (trace: List Touch) (next: Seam → List Touch → Prop)
    (touches: SepTouches seam trace next):
    next Begun (trace ++ seam.ending) :=
  match seam, touches with
    | Begun, Both _ broken => rewrite List.appendNil trace then broken
    | Along word, Both _ broken => rewrite List.appendNil trace then broken
    | Awaiting word comment, Both _ broken => broken

--| A step that goes one way or the other holds if each way does.
theorem Doc.Proofs.eitherSeams ∀ (spec: Seam → List Touch → Prop) (flat: Bool) (yes no: Printer) (rest: List Cmd)
    (whenYes: SeamHolds (seam trace => StackTouches spec rest seam trace) yes)
    (whenNo: SeamHolds (seam trace => StackTouches spec rest seam trace) no):
    SeamHolds
      (seam trace => StackTouches spec (if flat then (yes, rest) else (no, rest)).snd seam trace)
      (if flat then (yes, rest) else (no, rest)).fst :=
  match flat with
    | True => whenYes
    | False => whenNo

--| At a line start nothing waits, and a line break the document asks for
--| there leaves the printer where it is.
theorem Doc.Proofs.startStays ∀ (next: Seam → List Touch → Prop) (printer: Printer)
    (sound: SeamSound printer)
    (start: printer.atLineStart = True) (after: next Begun (printer.touches ++ printer.seam.ending)):
    next printer.seam printer.touches :=
  match sound with
    | (_, _, waits) =>
      match same: printer.suffixes, waits with
        | [], _ =>
          match begun: printer.atLineStart, start with
            | True, _ => rewrite List.appendNil printer.touches at after then after
        | [only], Both _ mid => (Bool.falseNotTrue (Eq.trans mid.flipped start)).impossible
        | [first, second, ..more], never =>
          match never with
            | ()

--| The comment floor and the marks are no part of what touches.
theorem Doc.Proofs.floorSeams ∀ (next: Seam → List Touch → Prop) (printer: Printer) (carry: Carry)
    (holds: SeamHolds next printer):
    SeamHolds next { printer | carry = carry } :=
  holds

--| A `LineStart`: a line break unless a line starts here.
theorem Doc.Proofs.lineStartSeams ∀ (next: Seam → List Touch → Prop) (printer: Printer) (indent: Nat)
    (sound: SeamSound printer) (after: next Begun (printer.touches ++ printer.seam.ending)):
    SeamHolds next (printer.lineStart indent) :=
  match start: printer.atLineStart with
    | True => (sound, (startStays next printer sound start after))
    | False =>
      floorSeams next
        (printer.newline (printer.continuation indent))
        (printer.carry.startFloor (printer.continuation indent))
        (newlineSeams next printer (printer.continuation indent) sound after)

--| A line moved at its start, with nothing on it.
theorem Doc.Proofs.movedSeams ∀ (next: Seam → List Touch → Prop) (printer: Printer) (indent: Nat) (carry: Carry)
    (sound: SeamSound printer)
    (start: printer.atLineStart = True) (after: next Begun (printer.touches ++ printer.seam.ending)):
    SeamHolds next { printer | owed = Some indent, lineIndent = indent, carry = carry } :=
  match sound with | (_, freshOk, waits) => (((Inr start), freshOk, waits), (startStays next printer sound start after))

--| A `LineStartHere` at a line start: the line moves.
theorem Doc.Proofs.hereSeams ∀ (next: Seam → List Touch → Prop) (printer: Printer) (indent: Nat)
    (sound: SeamSound printer)
    (start: printer.atLineStart = True) (after: next Begun (printer.touches ++ printer.seam.ending)):
    SeamHolds next { printer | owed = Some indent, lineIndent = indent } :=
  match sound with | (_, freshOk, waits) => (((Inr start), freshOk, waits), (startStays next printer sound start after))

--| A closer's line: a line break, or at a line start with nothing
--| waiting, the line moved.
theorem Doc.Proofs.closerLineSeams ∀ (next: Seam → List Touch → Prop) (printer: Printer) (key indent: Nat)
    (sound: SeamSound printer) (after: next Begun (printer.touches ++ printer.seam.ending)):
    SeamHolds next (printer.closerLine key indent) :=
  let broken :=
    newlineSeams next { printer | carry = printer.carry.close key } (printer.carry.closerAt key indent) sound after
  match start: printer.atLineStart with
    | True =>
      match waiting: printer.suffixes.isEmpty with
        | True =>
          movedSeams next printer
            (printer.carry.closerAt key indent)
            ((printer.carry.close key).breakTo (printer.carry.closerAt key indent))
            sound
            start
            after
        | False => broken
    | False => broken

--| A `Blank`: a line break at a line start, which leaves the seam as it
--| was; nothing elsewhere.
theorem Doc.Proofs.blankSeams ∀ (next: Seam → List Touch → Prop) (printer: Printer)
    (sound: SeamSound printer) (after: next printer.seam printer.touches):
    SeamHolds next printer.blank :=
  match blank: printer.atLineStart && printer.started && printer.newlinesAtEnd < 2 with
    | False => (sound, after)
    | True =>
      let start: printer.atLineStart = True := andTrueLeft _ _ blank
      match sound with
        | (owedOk, freshOk, waits) =>
          match same: printer.suffixes, waits with
            | [], held =>
              match begun: printer.atLineStart with
                | True => ((owedOk, (Inr byComputing), held), after)
            | [only], Both _ mid => (Bool.falseNotTrue (Eq.trans mid.flipped start)).impossible
            | [first, second, ..more], never =>
              match never with
                | ()

--| A trailing comment starts waiting after pieces on its line.
theorem Doc.Proofs.suffixSeams ∀ (next: Seam → List Touch → Prop) (printer: Printer) (comment: Text)
    (sound: SeamSound printer)
    (touches: SuffixTouches comment printer.seam printer.touches next):
    SeamHolds next { printer | suffixes = printer.suffixes ++ [comment] } :=
  match sound with
    | (owedOk, freshOk, waits) =>
      match same: printer.suffixes, waits, touches with
        | [], held, touches =>
          match start: printer.atLineStart, touches with
            | True, never =>
              match never with
                | ()
            | False, Both word touches => ((owedOk, freshOk, (word, byComputing)), (rewrite held then touches))
        | [only], _, never =>
          match never with
            | ()

--| With a comment waiting, the line has pieces on it.
theorem Doc.Proofs.waitingMid ∀ (printer: Printer)
    (sound: SeamSound printer)
    (waiting: printer.suffixes.isEmpty = False):
    printer.atLineStart = False :=
  match sound with
    | (_, _, waits) =>
      match same: printer.suffixes, waits, waiting with
        | [], _, never => (Bool.falseNotTrue never.flipped).impossible
        | [only], Both _ mid, _ => mid
        | [first, second, ..more], never, _ =>
          match never with
            | ()

--| With nothing waiting, a `Displaced` element starts where the printer
--| is.
theorem Doc.Proofs.displacedClear ∀ (printer: Printer) (trace: List Touch) (next: Seam → List Touch → Prop)
    (clear: printer.suffixes = [])
    (touches: DisplacedTouches printer.seam trace next):
    next printer.seam trace :=
  match same: printer.suffixes, clear, touches with
    | [], _, touches =>
      match start: printer.atLineStart, touches with
        | True, touches => touches
        | False, touches => touches

--| With a comment waiting, a `Displaced` element starts a line.
theorem Doc.Proofs.displacedWaiting ∀ (printer: Printer) (trace: List Touch) (next: Seam → List Touch → Prop)
    (waiting: printer.suffixes.isEmpty = False)
    (touches: DisplacedTouches printer.seam trace next):
    next Begun (trace ++ printer.seam.ending) :=
  match same: printer.suffixes, waiting, touches with
    | [], never, _ => (Bool.falseNotTrue never.flipped).impossible
    | [first, ..more], _, touches => touches

--| With nothing waiting, `displace` does nothing.
theorem Doc.Proofs.displaceClearIs ∀ (printer: Printer) (indent: Nat)
    (clear: printer.suffixes.isEmpty = True):
    printer.displace indent = printer :=
  rewrite clear

--| With a comment waiting, `displace` breaks the line.
theorem Doc.Proofs.displaceWaitingIs ∀ (printer: Printer) (indent: Nat)
    (waiting: printer.suffixes.isEmpty = False)
    (mid: printer.atLineStart = False):
    printer.displace indent = printer.newline (printer.continuation indent) :=
  rewrite waiting, mid

--| A `Displaced` element: a comment waiting ends its line first.
theorem Doc.Proofs.displaceSeams ∀ (next: Seam → List Touch → Prop) (printer: Printer) (indent: Nat)
    (sound: SeamSound printer)
    (touches: DisplacedTouches printer.seam printer.touches next):
    SeamHolds next (printer.displace indent) :=
  match trueOrFalse printer.suffixes.isEmpty with
    | Inl clear =>
      rewrite displaceClearIs printer indent clear then
        (sound, (displacedClear printer printer.touches next (emptyNil printer.suffixes clear) touches))
    | Inr waiting =>
      rewrite displaceWaitingIs printer indent waiting (waitingMid printer sound waiting) then
        newlineSeams next printer
          (printer.continuation indent)
          sound
          (displacedWaiting printer printer.touches next waiting touches)

-- Every step, every reading, and `print`.

--| A step of a reading keeps the printer sound, and the work list it
--| leaves touches from the seam and words it leaves.
--|
--| Proof idea: one case per command, as `stepJoins`; each printer
--| operation has its lemma above (`writeSeams`, `closeSeams`,
--| `newlineSeams`, ...), and a composite only pushes its parts, whose
--| work list touches as the composite did (`printsTouch`, `linesTouch`,
--| `fillSepsTouch`, `optionTouches`).
theorem Doc.Proofs.stepTouches ∀ (spec: Seam → List Touch → Prop) (printer: Printer) (cmd: Cmd)
    (rest: List Cmd) (result: (Printer, List Cmd))
    (steps: StepsTo printer cmd rest result)
    (sound: SeamSound printer)
    (touches: StackTouches spec [cmd, ..rest] printer.seam printer.touches):
    SeamHolds (seam trace => StackTouches spec result.snd seam trace) result.fst :=
  match cmd, steps, touches with
    | FillSep indent item, Inl (Both clear flat), touches =>
      rewrite flat then
        writeSeams
          (seam trace => Touches item seam trace (after later => StackTouches spec rest after later))
          printer
          indent
          " "
          1
          sound
          (sepWrites printer.seam printer.touches
            (seam trace => Touches item seam trace (after later => StackTouches spec rest after later))
            touches)
    | FillSep indent item, Inr broken, touches =>
      rewrite broken then
        newlineSeams
          (seam trace => Touches item seam trace (after later => StackTouches spec rest after later))
          printer
          indent
          sound
          (sepBreaks printer.seam printer.touches
            (seam trace => Touches item seam trace (after later => StackTouches spec rest after later))
            touches)
    | Print indent mode doc, steps, touches =>
      match doc, steps, touches with
        | Doc.Nothing, steps, touches => rewrite steps then (sound, touches)
        | BreakParent, steps, touches => rewrite steps then (sound, touches)
        | Chunk text width, steps, touches =>
          rewrite steps then
            writeSeams (seam trace => StackTouches spec rest seam trace) printer indent text width sound touches
        | Closing text, steps, touches =>
          rewrite steps then closeSeams (seam trace => StackTouches spec rest seam trace) printer text sound touches
        | Line, steps, touches =>
          rewrite steps then
            eitherSeams spec mode.isFlat
              (printer.write indent " " 1)
              (printer.newline indent)
              rest
              (writeSeams
                (seam trace => StackTouches spec rest seam trace)
                printer
                indent
                " "
                1
                sound
                (sepWrites printer.seam printer.touches (seam trace => StackTouches spec rest seam trace) touches))
              (newlineSeams
                (seam trace => StackTouches spec rest seam trace)
                printer
                indent
                sound
                (sepBreaks printer.seam printer.touches (seam trace => StackTouches spec rest seam trace) touches))
        | SoftLine, steps, Both stays broken =>
          rewrite steps then
            eitherSeams spec mode.isFlat printer
              (printer.newline indent)
              rest
              (sound, stays)
              (newlineSeams (seam trace => StackTouches spec rest seam trace) printer indent sound broken)
        | HardLine, steps, touches =>
          rewrite steps then newlineSeams (seam trace => StackTouches spec rest seam trace) printer indent sound touches
        | Mark key, steps, touches =>
          rewrite steps then
            floorSeams
              (seam trace => StackTouches spec rest seam trace)
              printer
              (printer.carry.mark key printer.lineIndent)
              (sound, touches)
        | CloserLine key, steps, touches =>
          rewrite steps then
            closerLineSeams (seam trace => StackTouches spec rest seam trace) printer key indent sound touches
        | LineStart, steps, touches =>
          rewrite steps then
            lineStartSeams (seam trace => StackTouches spec rest seam trace) printer indent sound touches
        | LineStartHere, steps, touches =>
          match start: printer.atLineStart with
            | True =>
              rewrite steps then
                hereSeams (seam trace => StackTouches spec rest seam trace) printer indent sound start touches
            | False =>
              rewrite steps then
                newlineSeams (seam trace => StackTouches spec rest seam trace) printer indent sound touches
        | Blank, steps, touches =>
          rewrite steps then blankSeams (seam trace => StackTouches spec rest seam trace) printer sound touches
        | Nest more inner, steps, touches => rewrite steps then (sound, touches)
        | Align inner, steps, touches => rewrite steps then (sound, touches)
        | AlignInset inner, steps, touches => rewrite steps then (sound, touches)
        | Displaced inner, steps, touches =>
          rewrite steps then
            displaceSeams
              (seam trace => StackTouches spec [Print (printer.displacedAt indent) mode inner, ..rest] seam trace)
              printer
              indent
              sound
              touches
        | OneLineBelow inner, steps, touches => rewrite steps then (sound, touches)
        | Flatten inner, steps, touches => rewrite steps then (sound, touches)
        | LineSuffix comment, steps, touches =>
          rewrite steps then suffixSeams (seam trace => StackTouches spec rest seam trace) printer comment sound touches
        | Group inner hard, Inl (Both _ flat), touches => rewrite flat then (sound, touches)
        | NarrowGroup max inner hard, Inl (Both _ flat), touches => rewrite flat then (sound, touches)
        | Group inner hard, Inr (Both _ broken), touches => rewrite broken then (sound, touches)
        | NarrowGroup max inner hard, Inr (Both _ broken), touches => rewrite broken then (sound, touches)
        | IdGroup id inner hard, Inl (Both _ flat), touches => rewrite flat then (sound, touches)
        | IdGroup id inner hard, Inr (Both _ broken), touches => rewrite broken then (sound, touches)
        | IfBroken id broken flat, steps, touches =>
          rewrite steps then
            (
              sound,
              (pickTouches printer.modes id broken flat printer.seam printer.touches
                (after later => StackTouches spec rest after later)
                touches)
            )
        | Concat docs, steps, touches =>
          rewrite steps then (sound, (printsTouch spec indent mode docs rest printer.seam printer.touches touches))
        | Fill [], steps, touches => rewrite steps then (sound, touches)
        | Fill [first, ..others], Inl (Both _ flat), touches =>
          rewrite flat then
            (
              sound,
              (printsTouch spec indent Flat
                (Doc.joinLines [first, ..others])
                rest
                printer.seam
                printer.touches
                (linesTouch first others printer.seam printer.touches
                  (seam trace => StackTouches spec rest seam trace)
                  touches))
            )
        | Fill [first, ..others], Inr (Both _ (Witness firstMode broken)), touches =>
          rewrite broken then
            (
              sound,
              (touchesWeaker first printer.seam printer.touches
                (after later => SepsTouch others after later (seam trace => StackTouches spec rest seam trace))
                (after later => StackTouches spec (others.map (FillSep indent) ++ rest) after later)
                (after later seps => fillSepsTouch spec indent others rest after later seps)
                touches)
            )
        | Choice options, Inl (Both _ flat), touches =>
          rewrite flat then
            (
              sound,
              (headOrTouches options printer.seam printer.touches
                (seam trace => StackTouches spec rest seam trace)
                touches)
            )
        | Choice options, Inr (Both _ (Witness chosen (Both isOption broken))), touches =>
          rewrite broken then
            (
              sound,
              (optionTouches chosen options printer.seam printer.touches
                (seam trace => StackTouches spec rest seam trace)
                isOption
                touches)
            )

--| Through a reading of a work list that touches from the printer's
--| seam, with the fuel to finish it, the printer stays sound and ends
--| where `spec` allows.
theorem Doc.Proofs.readingTouches ∀ (spec: Seam → List Touch → Prop) (printer: Printer) (fuel: Nat)
    (stack: List Cmd) (final: Printer)
    (reads: Doc.Proofs.Reads printer fuel stack final)
    (sound: SeamSound printer)
    (touches: StackTouches spec stack printer.seam printer.touches)
    (enough: stackCost stack ≤ fuel):
    SeamHolds spec final :=
  match fuel, stack, reads, touches with
    | Zero, [], reads, touches => rewrite reads then (sound, touches)
    | Succ more, [], reads, touches => rewrite reads then (sound, touches)
    | Zero, [cmd, ..rest], _, _ =>
      let positive := costPositive cmd
      Void.impossible (arithmetic)
    | Succ more, [cmd, ..rest], Witness next (Witness later (Both steps laterReads)), touches =>
      let lighter := readingLighter printer cmd rest (next, later) steps
      match stepTouches spec printer cmd rest (next, later) steps sound touches with
        | Both nextSound nextTouches =>
          readingTouches spec next more later final laterReads nextSound nextTouches (arithmetic)

--| The waiting comment written at the end of the print adds its word.
theorem Doc.Proofs.finalTouches ∀ (printer: Printer)
    (sound: SeamSound printer):
    touchesOf printer.flushSuffixes.out = printer.touches ++ printer.seam.ending :=
  match sound with | (_, _, waits) => rewrite flushTouches printer waits, seamEnding printer

--| A document that touches from the start of a line, printed at any
--| width, lists its words as the document said: `spec` holds of the
--| words of the printed pieces in order, each with whether it touches
--| the piece before it. The comment still waiting at the end is printed
--| last (`Seam.ending`).
theorem Doc.Proofs.printTouches ∀ (spec: List Touch → Prop) (doc: Doc) (width: Nat)
    (touches: Touches doc Begun [] (seam trace => spec (trace ++ seam.ending))):
    spec (touchesOf (printedPieces doc width).reverse) :=
  let fuel := 3 * doc.size + 3
  let ran := (Printer.start width).run fuel fuel [Print 0 Break doc]
  let bound := stepsUnderSize doc
  let start: SeamSound (Printer.start width) := ((Inl byComputing), (Inr byComputing), byComputing)
  match readingTouches
    (seam trace => spec (trace ++ seam.ending))
    (Printer.start width)
    fuel
    [Print 0 Break doc]
    ran
    (runIsReading (Printer.start width) fuel fuel [Print 0 Break doc])
    start
    touches
    (arithmetic) with
    | Both finalSound holds => rewrite List.reverseReverse ran.flushSuffixes.out, finalTouches ran finalSound then holds

-- The words, and witnesses.

--| The words listed are the output's words, in order: `touchesOf` only
--| adds to `wordsOf` whether each touches the piece before it.
theorem Doc.Proofs.touchesWords ∀ (out: List Text): (touchesOf out).map (touch => touch.word) = wordsOf out.reverse :=
  match out with
    | [] => byComputing
    | [piece, ..earlier] =>
      match layout: isLayout piece with
        | True => rewrite layoutSnoc piece earlier layout then touchesWords earlier
        | False => rewrite wordsSnoc piece earlier, List.mapAppend, touchesWords earlier then (rewrite layout)

--| A sign glued to its operand, after a space: at every width `- x`
--| reads `f -x`, the `-` touching nothing and `x` touching it, with a
--| `Mark` between them that prints nothing. A `Line` before the sign
--| keeps it apart whether it breaks or not.
theorem Doc.Proofs.printTouchesExample ∀ (width: Nat):
    touchesOf (printedPieces (Group (Concat [Chunk "f" 1, Line, Chunk "-" 1, Mark 0, Chunk "x" 1]) False) width).reverse
      = [{ word = "f", touching = False }, { word = "-", touching = False }, { word = "x", touching = True }] :=
  printTouches
    (touches =>
      touches = [{ word = "f", touching = False }, { word = "-", touching = False }, { word = "x", touching = True }])
    (Group (Concat [Chunk "f" 1, Line, Chunk "-" 1, Mark 0, Chunk "x" 1]) False)
    width
    (byComputing, byComputing)

--| A closer after a trailing comment joins the comment's line before it,
--| touching the word before: `x) -- c`. The comment, printed when the
--| line ends, touches nothing.
theorem Doc.Proofs.closerTouchesExample ∀ (width: Nat):
    touchesOf (printedPieces (Concat [Chunk "x" 1, LineSuffix "-- c", Closing ")"]) width).reverse
      = [{ word = "x", touching = False }, { word = ")", touching = True }, { word = "-- c", touching = False }] :=
  printTouches
    (touches =>
      touches
        = [{ word = "x", touching = False }, { word = ")", touching = True }, { word = "-- c", touching = False }])
    (Concat [Chunk "x" 1, LineSuffix "-- c", Closing ")"])
    width
    (byComputing, byComputing)
