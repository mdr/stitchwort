--| An edge-quiet slice 1 declaration (`Decl.edgeQuiet1`) meets `DeclElements` (SW-4099, SW-4096's half B): its type's
--| and value's facts from `edgeFacts` (`Fmt.EdgeHangProofs`), the value's first token after its own-line comments,
--| if it has any, by `edgeElHangs`, and its hug by `edgeHug`. `edgeQuiet1` is a test of the calmed type and value;
--| the rules print a tree and its calm tree the same (`elCalm`, `callHugKept`), so the calmed parts' facts are the
--| tree's.

namespace Fmt.EdgeDeclProofs
import Std (Bool, DecEq, Doc, Eq, List, Nat, Option, Text, Void)
import Std.Doc.Proofs (..)
import Syntax (Comments, Decl, DefBody, DefKind, Expr, Header, InfixKind, Note, Tok, Word)
import Fmt (..)
import Fmt.HangProofs (..)
import Fmt.AppHangProofs (lastArg)
import Fmt.ChainHangProofs (HangsAt)
import Fmt.ExprHangProofs (..)
import Fmt.SpellProofs (..)
import Fmt.CalmProofs (..)
import Fmt.TreeJoinProofs (lexKind)
import Fmt.TokenProofs (declRealOfLexical)
import Fmt.DeclHangProofs (BodyLays, OnLine, declStart, plainBody)
import Fmt.DeclFactsProofs (
  DeclElements,
  HugOnLine,
  appDocsHug,
  leadNotCloser,
  leadSound,
  notesOfWord,
  plainBodyEl,
  trailsOfSound
)
import Fmt.OneLineStatements (..)
import Fmt.EdgeKeyProofs (..)
import Fmt.EdgeHangProofs (..)

-- What `calm` keeps.

theorem keptSound ∀ (word: Word) (item closer: Bool): (word.kept item closer).sound = word.sound := match word with
  | { text, comments = { above, after, blankBefore } } =>
    match above with
      | [] => byComputing
      | [note, ..rest] => byComputing

theorem soundAllCalm ∀ (items: List Expr) (item: Bool)
    (sound: allSound items = True):
    allSound (calmAll item items) = True :=
  match items with
    | [] => byComputing
    | [first, ..rest] =>
      Bool.andIntro (soundCalm first item (Bool.andLeft sound)) (soundAllCalm rest item (Bool.andRight sound))

theorem soundLeadCalm ∀ (items: List Expr) (sound: allSound items = True): allSound (calmLead items) = True :=
  match items with
    | [] => byComputing
    | [first, ..rest] =>
      Bool.andIntro (soundCalm first False (Bool.andLeft sound)) (soundAllCalm rest True (Bool.andRight sound))

--| `calm` keeps a sound tree sound: it clears only blank-line flags.
theorem soundCalm ∀ (expr: Expr) (item: Bool) (sound: expr.sound = True): (expr.calm item).sound = True :=
  match expr, sound with
    | Atom kind word, sound => rewrite keptSound word item False then sound
    | Paren open inner close, sound =>
      Bool.andIntro
        (rewrite keptSound open item False then Bool.andLeft sound)
        (Bool.andIntro
          (soundCalm inner False (Bool.andLeft (Bool.andRight sound)))
          (rewrite keptSound close False True then Bool.andRight (Bool.andRight sound)))
    | Tuple open items comma close, sound =>
      Bool.andIntro
        (rewrite keptSound open item False then Bool.andLeft sound)
        (Bool.andIntro
          (soundAllCalm items True (Bool.andLeft (Bool.andRight sound)))
          (rewrite keptSound close False True then Bool.andRight (Bool.andRight sound)))
    | ListOf open items comma close, sound =>
      Bool.andIntro
        (rewrite keptSound open item False then Bool.andLeft sound)
        (Bool.andIntro
          (match items.all Expr.plainItem with
            | True => soundLeadCalm items (Bool.andLeft (Bool.andRight sound))
            | False => soundAllCalm items True (Bool.andLeft (Bool.andRight sound)))
          (rewrite keptSound close False True then Bool.andRight (Bool.andRight sound)))
    | App head arguments, sound =>
      Bool.andIntro (soundCalm head item (Bool.andLeft sound)) (soundAllCalm arguments False (Bool.andRight sound))
    | Infix kind left operator right, sound =>
      Bool.andIntro
        (soundCalm left item (Bool.andLeft sound))
        (Bool.andIntro
          (rewrite keptSound operator False False then Bool.andLeft (Bool.andRight sound))
          (soundCalm right False (Bool.andRight (Bool.andRight sound))))
    | Prefix operator operand, sound =>
      Bool.andIntro
        (rewrite keptSound operator item False then Bool.andLeft sound)
        (soundCalm operand False (Bool.andRight sound))

theorem lexicalAllCalm ∀ (items: List Expr) (item: Bool)
    (lexical: allLexical1 items = True):
    allLexical1 (calmAll item items) = True :=
  match items with
    | [] => byComputing
    | [first, ..rest] =>
      Bool.andIntro (lexicalCalm first item (Bool.andLeft lexical)) (lexicalAllCalm rest item (Bool.andRight lexical))

theorem lexicalLeadCalm ∀ (items: List Expr) (lexical: allLexical1 items = True): allLexical1 (calmLead items) = True :=
  match items with
    | [] => byComputing
    | [first, ..rest] =>
      Bool.andIntro (lexicalCalm first False (Bool.andLeft lexical)) (lexicalAllCalm rest True (Bool.andRight lexical))

--| `calm` keeps a lexical tree lexical: it keeps every token's text.
theorem lexicalCalm ∀ (expr: Expr) (item: Bool) (lexical: expr.lexical1 = True): (expr.calm item).lexical1 = True :=
  match expr, lexical with
    | Atom kind word, lexical => lexical
    | Paren open inner close, lexical =>
      Bool.andIntro
        (Bool.andLeft lexical)
        (Bool.andIntro
          (Bool.andLeft (Bool.andRight lexical))
          (lexicalCalm inner False (Bool.andRight (Bool.andRight lexical))))
    | Tuple open items comma close, lexical =>
      Bool.andIntro
        (Bool.andLeft lexical)
        (Bool.andIntro
          (Bool.andLeft (Bool.andRight lexical))
          (lexicalAllCalm items True (Bool.andRight (Bool.andRight lexical))))
    | ListOf open items comma close, lexical =>
      Bool.andIntro
        (Bool.andLeft lexical)
        (Bool.andIntro
          (Bool.andLeft (Bool.andRight lexical))
          (match items.all Expr.plainItem with
            | True => lexicalLeadCalm items (Bool.andRight (Bool.andRight lexical))
            | False => lexicalAllCalm items True (Bool.andRight (Bool.andRight lexical))))
    | App head arguments, lexical =>
      Bool.andIntro
        (lexicalCalm head item (Bool.andLeft lexical))
        (lexicalAllCalm arguments False (Bool.andRight lexical))
    | Infix kind left operator right, lexical =>
      Bool.andIntro
        (lexicalCalm left item (Bool.andLeft lexical))
        (Bool.andIntro
          (Bool.andLeft (Bool.andRight lexical))
          (lexicalCalm right False (Bool.andRight (Bool.andRight lexical))))
    | Prefix operator operand, lexical =>
      Bool.andIntro (Bool.andLeft lexical) (lexicalCalm operand False (Bool.andRight lexical))

-- Comments above the first token.

--| `notedNodeHangs`, trailing what the node does.
theorem edgeNotedNodeHangs ∀ (expr: Expr) (word: Word) (node: Around → Doc) (around: Around) (indent: Nat)
    (trails: Bool) (note: Note) (rest: List Note)
    (elIs: ∀ (at: Around) => expr.el at = framedBy word at (node at))
    (same: node { around | hoisted = True } = node around)
    (hoisted: around.hoisted = False)
    (noted: word.comments.above = [note, ..rest])
    (closer: isCloserText word.text = False)
    (comments: NotesComment [note, ..rest])
    (quiet: (note.blankBefore && around.item) = False)
    (hoistedHangs: ∀ (inset: Nat) => ElHangs lexKind
      (expr.el { around | hoisted = True })
      inset
      inset
      around.before
      trails
      wordStart):
    ElHangs lexKind (expr.el around) indent indent around.before trails leadStart :=
  let lifted := { around | hoisted = True }
  let isNoted: word.noted = True := rewrite noted
  let unwrapped: framedBy word lifted (node lifted) = Doc.concat [Doc.concat [], Displaced (node around)] :=
    rewrite isNoted, same
  rewrite elIs around then
    notedFramedHangs lexKind word around
      (node around)
      indent
      trails
      note
      rest
      hoisted
      noted
      closer
      comments
      quiet
      (inset =>
        let fact := hoistedHangs inset
        rewrite elIs lifted, unwrapped at fact then fact)

--| An edge-quiet slice 1 expression standing where it writes the comments above its first token (not hoisted, not
--| an item) hangs as an element from its seat at the indentation, trailing what it does: its first token where
--| `startFor` says, after the comments if it has any.
--|
--| Proof idea: `leadElHangs`' cases, from `edgeFacts` in place of `leadFacts`: with no comments, the element where it
--| is bare; with comments, a name or numeral by `notedLeafHangs` (its trailing comment from `sound`) and a node by
--| `edgeNotedNodeHangs` from its hoisted form's facts. The first token may keep a blank line below its comments:
--| neither lemma asks about it.
theorem edgeElHangs ∀ (expr: Expr) (around: Around) (indent: Nat) (lead end: Bool)
    (within: expr.within1 = True)
    (lexical: expr.lexical1 = True)
    (sound: expr.sound = True)
    (edge: expr.edgeQuiet1 lead end = True)
    (hoisted: around.hoisted = False)
    (item: around.item = False):
    ElHangs lexKind (expr.el around) indent indent around.before expr.trails (startFor expr.noted) :=
  let facts := edgeFacts expr lead end within lexical sound edge
  let sameNoted: expr.noted = expr.lead.noted := Eq.cong Word.noted (firstWordLead expr within)
  let hoistedHangs: ∀ (inset: Nat) => ElHangs lexKind
    (expr.el { around | hoisted = True })
    inset
    inset
    around.before
    expr.trails
    wordStart :=
    inset => edgeHangsOf expr facts { around | hoisted = True } byComputing inset inset
  let comments: NotesComment expr.lead.comments.above := notesOfWord expr.lead (leadSound expr sound)
  let closer := leadNotCloser expr within lexical
  rewrite sameNoted then
    match above: expr.lead.comments.above with
      | [] =>
        let unnoted: expr.lead.noted = False := Eq.cong (notes => !notes.isEmpty) above
        edgeHangsOf expr facts around (unnotedBare expr around unnoted) indent indent
      | [note, ..rest] =>
        let quiet: (note.blankBefore && around.item) = False := rewrite item then Bool.andFalse note.blankBefore
        match expr, within with
          | Atom kind word, within =>
            let (plain, (notComment, solid, wordCloser, comma)) := wordFacts kind word.text within
            let el: ElHangs lexKind (word.leaf around around.at) indent indent around.before word.trails leadStart :=
              state entry =>
                notedLeafHangs lexKind word around around.at indent state entry note rest plain notComment solid
                    wordCloser comma hoisted above comments
                    (trailsOfSound word sound)
                    (unblankedAt (plainStart entry) note.blankBefore around.item quiet)
            trailsSwap lexKind _ indent indent around.before _ _ leadStart (atomTrailsIs kind word).flipped el
          | Paren open inner close, _ =>
            edgeNotedNodeHangs
              (Paren open inner close)
              open
              (at => parenDoc open inner close { at | hoisted = True })
              around
              indent
              (Paren open inner close).trails
              note
              rest
              (at => byComputing)
              byComputing
              hoisted
              above
              closer
              comments
              quiet
              hoistedHangs
          | Tuple open items trailing close, _ =>
            edgeNotedNodeHangs
              (Tuple open items trailing close)
              open
              (at => commaBracket (list := False) open items close { at | hoisted = True })
              around
              indent
              (Tuple open items trailing close).trails
              note
              rest
              (at => byComputing)
              byComputing
              hoisted
              above
              closer
              comments
              quiet
              hoistedHangs
          | ListOf open items trailing close, _ =>
            edgeNotedNodeHangs
              (ListOf open items trailing close)
              open
              (at => commaBracket (list := True) open items close { at | hoisted = True })
              around
              indent
              (ListOf open items trailing close).trails
              note
              rest
              (at => byComputing)
              byComputing
              hoisted
              above
              closer
              comments
              quiet
              hoistedHangs
          | App head arguments, within =>
            let node: Around → Doc := at => (appDocs head arguments { at | hoisted = True }).doc
            edgeNotedNodeHangs
              (App head arguments)
              head.lead
              node
              around
              indent
              (App head arguments).trails
              note
              rest
              (at =>
                let unfolded: (App head arguments).el at = framedBy (App head arguments).firstWord at (node at) :=
                  byComputing
                Eq.trans unfolded
                  (Eq.cong (word => framedBy word at (node at)) (firstWordLead (App head arguments) within)))
              byComputing
              hoisted
              above
              closer
              comments
              quiet
              hoistedHangs
          | Infix InfixBinary left operator right, within =>
            let expr := Infix InfixBinary left operator right
            let node: Around → Doc := at => chain expr.chainLevel left operator right { at | hoisted = True }
            edgeNotedNodeHangs expr left.lead node around indent expr.trails note rest
              (at =>
                let unfolded: expr.el at = framedBy expr.firstWord at (node at) := byComputing
                Eq.trans unfolded (Eq.cong (word => framedBy word at (node at)) (firstWordLead expr within)))
              byComputing
              hoisted
              above
              closer
              comments
              quiet
              hoistedHangs
          | Infix InfixArrow left operator right, within =>
            let expr := Infix InfixArrow left operator right
            let node: Around → Doc := at => chain expr.chainLevel left operator right { at | hoisted = True }
            edgeNotedNodeHangs expr left.lead node around indent expr.trails note rest
              (at =>
                let unfolded: expr.el at = framedBy expr.firstWord at (node at) := byComputing
                Eq.trans unfolded (Eq.cong (word => framedBy word at (node at)) (firstWordLead expr within)))
              byComputing
              hoisted
              above
              closer
              comments
              quiet
              hoistedHangs
          | Prefix operator operand, _ =>
            edgeNotedNodeHangs
              (Prefix operator operand)
              operator
              (at =>
                Doc.concat [
                  operator.leaf { at | hoisted = True } at.at,
                  prefixGap operator operand,
                  operand.el (at.next operator.trails 1)
                ])
              around
              indent
              (Prefix operator operand).trails
              note
              rest
              (at => byComputing)
              byComputing
              hoisted
              above
              closer
              comments
              quiet
              hoistedHangs

-- The value's hug.

--| An edge-quiet slice 1 value's hug, if it has one, hangs on the `:=`'s line.
theorem edgeHug ∀ (value: Expr) (around: Around) (lead end: Bool)
    (within: value.within1 = True)
    (lexical: value.lexical1 = True)
    (sound: value.sound = True)
    (edge: value.edgeQuiet1 lead end = True):
    HugOnLine lexKind value around :=
  let inside := { around | hoisted = True }
  match value, within with
    | App head arguments, within => open same =>
      match arguments, edge with
        | [argument, ..rest], edge =>
          let headEdge: head.edgeQuiet1 lead False = True := Bool.andLeft edge
          let headFacts :=
            edgeFacts head lead False (Bool.andLeft within) (Bool.andLeft lexical) (Bool.andLeft sound) headEdge
          let facts :=
            edgeArgsHang inside.inArm head
              (inside.at + head.size)
              [argument, ..rest]
              end
              (edgeOffTrails head lead headEdge)
              (Bool.andRight within)
              (Bool.andRight lexical)
              (Bool.andRight sound)
              (Bool.andRight edge)
          let headHangs: ElHangs lexKind (head.el inside) 0 0 False head.trails wordStart :=
            elUnheld lexKind
              (head.el inside)
              0
              0
              inside.before
              head.trails
              wordStart
              (edgeHangsOf head headFacts inside byComputing 0 0)
          ((lastArg argument rest).trails, appDocsHug lexKind head argument rest inside 0 0 headHangs facts open same)
    | Atom _ _, _ => open never => cases
    | Paren _ _ _, _ => open never => cases
    | Tuple _ _ _ _, _ => open never => cases
    | ListOf _ _ _ _, _ => open never => cases
    | Infix InfixBinary _ _ _, _ => open never => cases
    | Infix InfixArrow _ _ _, _ => open never => cases
    | Prefix _ _, _ => open never => cases

-- The declaration's parts, from their calm forms.

--| A slice 1 type whose calm form is edge-quiet, not leading, hangs as `DeclElements` asks, where it stands in a
--| declaration (`declStart.next`'s place: not hoisted, not an item).
theorem edgeType ∀ (result: Expr) (before: Bool) (at: Nat) (inArm: Bool)
    (within: result.within1 = True)
    (lexical: result.lexical1 = True)
    (sound: result.sound = True)
    (edge: (result.calm False).edgeQuiet1 False True = True):
    ElHangs lexKind
      (result.el { before, hoisted = False, item = False, at, inArm })
      4
      4
      before
      result.trails
      (startFor result.noted) :=
  let around: Around := { before, hoisted = False, item = False, at, inArm }
  let calmed := result.calm False
  let good: result.good = True := Bool.andIntro within (lexicalClosed result lexical)
  let el :=
    edgeElHangs calmed around 4 False True
      (withinCalm result False within)
      (lexicalCalm result False lexical)
      (soundCalm result False sound)
      edge
      byComputing
      byComputing
  rewrite <- elCalm result around good, <- notedCalm result False within, <- trailsCalm result False within then el

--| A slice 1 value whose calm form is edge-quiet, with no comment waiting and none above its first token, lays on the
--| `:=`'s line, and so does its hug, if it has one.
theorem edgeOnLine ∀ (value: Expr) (at: Nat) (inArm: Bool)
    (within: value.within1 = True)
    (lexical: value.lexical1 = True)
    (sound: value.sound = True)
    (edge: (value.calm False).edgeQuiet1 True True = True)
    (unnoted: value.noted = False):
    OnLine lexKind (plainBody value { before = False, hoisted = False, item = False, at, inArm })
      ∧ (∀ (open: Doc) => value.callHug { before = False, hoisted = True, item = False, at, inArm } = Some open
        → OnLine lexKind open) :=
  let around: Around := { before = False, hoisted = False, item = False, at, inArm }
  let calmed := value.calm False
  let good: value.good = True := Bool.andIntro within (lexicalClosed value lexical)
  let calmedWithin := withinCalm value False within
  let calmedLexical := lexicalCalm value False lexical
  let calmedSound := soundCalm value False sound
  let facts := edgeFacts calmed True True calmedWithin calmedLexical calmedSound edge
  let calmUnnoted: calmed.lead.noted = False := calc calmed.lead.noted
    _ = calmed.noted := (Eq.cong Word.noted (firstWordLead calmed calmedWithin)).flipped
    _ = value.noted := notedCalm value False within
    _ = False := unnoted
  let line: ElHangs lexKind (calmed.el around) 0 0 False calmed.trails wordStart :=
    edgeHangsOf calmed facts around (unnotedBare calmed around calmUnnoted) 0 0
  (
    (calmed.trails, rewrite plainBodyEl value around, <- elCalm value around good then line),
    open same =>
      edgeHug calmed around True True calmedWithin calmedLexical calmedSound edge open
        (rewrite callHugKept value { around | hoisted = True } good then same)
  )

--| A slice 1 value whose calm form is edge-quiet lays as a body, below the `:=` and on its line when no comment waits
--| and it has none above its first token.
theorem edgeBody ∀ (value: Expr) (before: Bool) (at: Nat) (inArm: Bool)
    (within: value.within1 = True)
    (lexical: value.lexical1 = True)
    (sound: value.sound = True)
    (edge: (value.calm False).edgeQuiet1 True True = True):
    BodyLays lexKind value { before, hoisted = False, item = False, at, inArm } before :=
  let around: Around := { before, hoisted = False, item = False, at, inArm }
  let good: value.good = True := Bool.andIntro within (lexicalClosed value lexical)
  let below :=
    edgeElHangs
      (value.calm False)
      around
      2
      True
      True
      (withinCalm value False within)
      (lexicalCalm value False lexical)
      (soundCalm value False sound)
      edge
      byComputing
      byComputing
  (
    (
      value.trails,
      rewrite plainBodyEl value around,
          <- elCalm value around good,
          <- notedCalm value False within,
          <- trailsCalm value False within then
        below
    ),
    waiting unnoted =>
      match before, waiting with | False, _ => edgeOnLine value at inArm within lexical sound edge unnoted
  )

-- The declaration.

--| An edge-quiet slice 1 declaration meets `DeclElements`: the type's facts from `edgeType`, the value's from
--| `edgeBody`, each part's tokens sound by `settled1` (`declSoundOfSettled`).
theorem edgeElementsOf ∀ (decl: Decl)
    (within: decl.within1 = True)
    (settled: decl.settled1 = True)
    (lexical: decl.lexical1 = True)
    (edge: decl.edgeQuiet1 = True):
    DeclElements lexKind decl :=
  match decl, edge with
    | Definition [] header (Assigned colonEq value), edge =>
      let sound := declSoundOfSettled _ within settled (declRealOfLexical _ within lexical)
      let typeWithin: header.result.within1 = True := headerResultWithin header (Bool.andLeft within)
      let valueWithin: value.within1 = True := Bool.andRight within
      let typeLexical: header.result.lexical1 = True := Bool.andLeft (Bool.andRight lexical)
      let valueLexical: value.lexical1 = True := Bool.andRight (Bool.andRight lexical)
      let rest := Bool.andRight (Bool.andRight (Bool.andRight sound))
      let typeSound: header.result.sound = True := Bool.andLeft rest
      let valueSound: value.sound = True := Bool.andRight (Bool.andRight rest)
      (
        (
          header.result.trails,
          edgeType header.result header.colon.after.isSome
            (0 + 3)
            False
            typeWithin
            typeLexical
            typeSound
            (Bool.andLeft edge)
        ),
        edgeBody value colonEq.after.isSome
          (0 + (4 + header.result.size))
          False
          valueWithin
          valueLexical
          valueSound
          (Bool.andRight edge)
      )

--| The hangs (SW-4096's B): an `edgeQuiet1` slice 1 declaration meets `DeclElements`, however it is laid out. With
--| `edgeQuietOneLine1` (`Fmt.OneLineStatements`) it gives `declElementsOneLine1` (`Fmt.TopStatements`).
--|
--| Proof idea: `edgeElementsOf`; `shaped1` is not needed.
theorem edgeElements1 ∀ (decl: Decl)
    (within: decl.within1 = True)
    (shaped: decl.shaped1 = True)
    (settled: decl.settled1 = True)
    (lexical: decl.lexical1 = True)
    (edge: decl.edgeQuiet1 = True):
    DeclElements lexKind decl :=
  edgeElementsOf decl within settled lexical edge
