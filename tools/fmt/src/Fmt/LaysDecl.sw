--| The declaration's document passes the check (SW-4117, `doc1Checks`' walk, after `Fmt.LaysEls`): a definition's
--| header, its `:=` and the body in either of `IfBroken`'s forms, each from where the one before leaves the printer.
namespace Fmt.LaysDecl
import Std (Bool, Doc, Eq, List, Nat, Option, Text, Void)
import Std.Doc (..)
import Syntax (Comments, Decl, DefBody, DefKind, Expr, Word)
import Fmt (..)
import Fmt.LaysKinds (..)
import Fmt.LaysRules (..)
import Fmt.SpellProofs (..)
import Fmt.ToldDeclProofs (..)
import Fmt.TrailsProofs (Coded, atomCoded, parenTrails, trailsBackCoded)
import Fmt.CalmProofs (lambdaHugNone, matchedNone, plainDef, plainDefIs, valueElPlain)
import Fmt.LaysEls (allElStep, argsBracketEl, elStep)
import Fmt.LaysApp (appHugStep)
import Fmt.LaysWords (..)
import Fmt.JoinProofs (DeclJoins)
import Fmt.TreeJoinProofs (lexKind)

-- Places.

--| After a line break forced by `OneLineBelow`, an element starts wherever it is written.
theorem startsBroken ∀ (hoisted before: Bool): Starts hoisted before { Kinds.none | broken = True } = True :=
  match hoisted with
    | True => byComputing
    | False => byComputing

--| A document written on one line below, when `OneLineBelow` has the printer break first.
theorem stepOneLineBelow ∀ (doc: Doc) (pre post: Kinds → Bool) (before: Bool)
    (inner: Step doc pre post)
    (good: pre { Kinds.none | broken = True } = True):
    Step (OneLineBelow doc) (kinds => Ends kinds before) post :=
  kinds holds =>
    match kinds, holds with
      | { start = False, broken = False, mid, held }, _ => inner { Kinds.none | broken = True } good

-- Choices.

theorem optionsAppend ∀ (front back: List Doc) (pre: Kinds → Bool) (trails: Bool)
    (first: Options front pre trails)
    (second: Options back pre trails):
    Options (front ++ back) pre trails :=
  match front, first with
    | [], _ => second
    | [option, ..rest], (step, more) => (step, optionsAppend rest back pre trails more second)

theorem optionsOne ∀ (doc: Doc) (pre: Kinds → Bool) (trails: Bool)
    (step: Step doc pre (kinds => Ends kinds trails)):
    Options [doc] pre trails :=
  (step, byComputing)

theorem optionsIf ∀ (cond: Bool) (doc: Doc) (pre: Kinds → Bool) (trails: Bool)
    (step: cond = True → Step doc pre (kinds => Ends kinds trails)):
    Options (if cond then [doc] else []) pre trails :=
  match cond with
    | True => optionsOne doc pre trails (step byComputing)
    | False => byComputing

theorem optionsOfHug ∀ (hug: Option Doc) (pre: Kinds → Bool) (trails: Bool)
    (step: ∀ (open: Doc) => hug = Some open → Step (Doc.concat [Doc.text " ", open]) pre (kinds => Ends kinds trails)):
    Options (optionList (hug.map (open => Doc.concat [Doc.text " ", open]))) pre trails :=
  match hug, step with
    | None, _ => byComputing
    | Some open, step => optionsOne _ pre trails (step open byComputing)

-- The body.

--| After a `:=`, a value's element goes after a space or below, and its hug after a space.
--|
--| Proof idea: each option of `bodyAfter` is the value's element or its hug after a space or a line break
--| (`OneLineBelow` included); `matchedNone`, `valueElPlain` and `lambdaHugNone` leave the element and the hug.
theorem bodyAfterStep ∀ (value: Expr) (assign: Word) (around: Around) (semi: Bool)
    (within: value.within1 = True)
    (element: Step (value.el around) (Starts around.hoisted around.before) (kinds => Ends kinds value.trails))
    (hug: ∀ (open: Doc) => value.callHug { around | hoisted = True } = Some open
      → Step open (Starts True around.before) (kinds => Ends kinds value.trails)):
    Step (bodyAfter value assign around semi).fst (kinds => Ends kinds around.before) (kinds => Ends kinds value.trails)
      ∧ Step (bodyAfter value assign around semi).snd (kinds => Ends kinds around.before) (kinds =>
        Ends kinds value.trails) :=
  let inside: Around := { around | hoisted = True }
  let pre := kinds => Ends kinds around.before
  let post := kinds => Ends kinds value.trails
  let afterSpace: Step (Doc.text " ") pre pre := stepSpace around.before
  let below: Step (Nest 2 (Doc.concat [HardLine, value.el around])) pre post :=
    stepNest 2 _ _ _
      (stepDocConcat
        [HardLine, value.el around] _ _
        (stepAllCons HardLine
          [value.el around]
          pre
          Fresh
          post
          (stepHardLineEnds around.before)
          (stepAllOne
            (value.el around)
            Fresh
            post
            (stepWeaken
              (value.el around)
              (Starts around.hoisted around.before)
              Fresh
              post
              post
              element
              (kinds good => freshStarts kinds around.hoisted around.before good)
              (kinds good => good)))))
  let spaced: Step (Doc.concat [Doc.text " ", value.el around]) pre post :=
    stepDocConcat
      [Doc.text " ", value.el around] _ _
      (stepAllCons
        (Doc.text " ")
        [value.el around]
        pre
        pre
        post
        afterSpace
        (stepAllOne
          (value.el around)
          pre
          post
          (stepWeaken
            (value.el around)
            (Starts around.hoisted around.before)
            pre
            post
            post
            element
            (kinds good => endsStartsAny kinds around.hoisted around.before good)
            (kinds good => good))))
  let lowered: Step (OneLineBelow (value.el around)) pre post :=
    stepOneLineBelow
      (value.el around)
      (Starts around.hoisted around.before)
      post
      around.before
      element
      (startsBroken around.hoisted around.before)
  let hugged: ∀ (open: Doc) => value.callHug inside = Some open → Step (Doc.concat [Doc.text " ", open]) pre post :=
    open found =>
      stepDocConcat
        [Doc.text " ", open] _ _
        (stepAllCons
          (Doc.text " ")
          [open]
          pre
          pre
          post
          afterSpace
          (stepAllOne open pre post
            (stepWeaken open
              (Starts True around.before)
              pre
              post
              post
              (hug open found)
              (kinds good => endsStartsAny kinds True around.before good)
              (kinds good => good))))
  rewrite matchedNone value inside within,
      valueElPlain value around semi within,
      lambdaHugNone value semi inside (value.el around) within then
    match plain: assign.trails || value.noted || value.isBlock with
      | True => (below, below)
      | False => (
        below,
        stepChoice
          (Flatten (Doc.concat [Doc.text " ", value.el around]))
          ((if value.opensBracket || (value.callHug inside).isSome then [OneLineBelow (value.el around)] else [])
            ++ ((if value.opensBracket then [Doc.concat [Doc.text " ", value.el around]]
                 else optionList ((value.callHug inside).map (open => Doc.concat [Doc.text " ", open])))
              ++ [Nest 2 (Doc.concat [HardLine, value.el around])]))
          pre
          value.trails
          (
            stepFlatten _ _ _ spaced,
            optionsAppend
              (if value.opensBracket || (value.callHug inside).isSome then [OneLineBelow (value.el around)] else [])
              ((if value.opensBracket then [Doc.concat [Doc.text " ", value.el around]]
                else optionList ((value.callHug inside).map (open => Doc.concat [Doc.text " ", open])))
                ++ [Nest 2 (Doc.concat [HardLine, value.el around])])
              pre
              value.trails
              (optionsIf (value.opensBracket || (value.callHug inside).isSome) _ pre value.trails (_ => lowered))
              (optionsAppend
                (if value.opensBracket then [Doc.concat [Doc.text " ", value.el around]]
                 else optionList ((value.callHug inside).map (open => Doc.concat [Doc.text " ", open])))
                [Nest 2 (Doc.concat [HardLine, value.el around])]
                pre
                value.trails
                (match value.opensBracket with
                  | True => optionsOne _ pre value.trails spaced
                  | False => optionsOfHug (value.callHug inside) pre value.trails hugged)
                (optionsOne _ pre value.trails below))
          )
      )

-- The header.

theorem stepIdGroup ∀ (id: Nat) (doc: Doc) (hard: Bool) (pre post: Kinds → Bool)
    (step: Step doc pre post):
    Step (IdGroup id doc hard) pre post :=
  step

--| A definition's type: below the `:` if a comment follows it, else after a space.
theorem typedStep ∀ (trails: Bool) (typeDoc: Doc) (after: Bool)
    (typeStep: Step typeDoc (Starts False trails) (kinds => Ends kinds after)):
    StepAll
      (if trails then [Nest 4 (Doc.concat [HardLine, typeDoc])] else [Doc.text " ", Nest 4 typeDoc])
      (kinds => Ends kinds trails)
      (kinds => Ends kinds after) :=
  match trails with
    | True =>
      stepAllOne
        (Nest 4 (Doc.concat [HardLine, typeDoc]))
        (kinds => Ends kinds True)
        (kinds => Ends kinds after)
        (stepNest 4 _ _ _
          (stepDocConcat
            [HardLine, typeDoc] _ _
            (stepAllCons HardLine
              [typeDoc]
              (kinds => Ends kinds True)
              Fresh
              (kinds => Ends kinds after)
              (stepHardLineEnds True)
              (stepAllOne typeDoc Fresh
                (kinds => Ends kinds after)
                (stepWeaken typeDoc
                  (Starts False True)
                  Fresh
                  (kinds => Ends kinds after)
                  (kinds => Ends kinds after)
                  typeStep
                  (kinds good => freshStarts kinds False True good)
                  (kinds good => good))))))
    | False =>
      stepAllCons
        (Doc.text " ")
        [Nest 4 typeDoc]
        (kinds => Ends kinds False)
        (kinds => Ends kinds False)
        (kinds => Ends kinds after)
        (stepSpace False)
        (stepAllOne
          (Nest 4 typeDoc)
          (kinds => Ends kinds False)
          (kinds => Ends kinds after)
          (stepNest 4 _ _ _
            (stepWeaken typeDoc
              (Starts False False)
              (kinds => Ends kinds False)
              (kinds => Ends kinds after)
              (kinds => Ends kinds after)
              typeStep
              (kinds good => endsStarts kinds False good)
              (kinds good => good))))

--| What a definition's words after the header do: the header, a space, the `:=` and the body.
theorem defFromStep ∀ (headerDoc: Doc) (breaks: Bool)
    (assignDoc below choice: Doc) (resultTrails assignTrails trails: Bool)
    (header: Step headerDoc (Starts True False) (kinds => Ends kinds resultTrails))
    (assign: Step assignDoc (Starts False resultTrails) (kinds => Ends kinds assignTrails))
    (body: Step below (kinds => Ends kinds assignTrails) (kinds => Ends kinds trails)
      ∧ Step choice (kinds => Ends kinds assignTrails) (kinds => Ends kinds trails)):
    Step (defFrom headerDoc breaks assignDoc below choice) (Starts True False) (kinds => Ends kinds trails) :=
  stepDocConcat
    [IdGroup 0 headerDoc breaks, Doc.text " ", assignDoc, IfBroken 0 below choice] _ _
    (stepAllCons
      (IdGroup 0 headerDoc breaks)
      [Doc.text " ", assignDoc, IfBroken 0 below choice]
      (Starts True False)
      (kinds => Ends kinds resultTrails)
      (kinds => Ends kinds trails)
      (stepIdGroup 0 headerDoc breaks _ _ header)
      (stepAllCons
        (Doc.text " ")
        [assignDoc, IfBroken 0 below choice]
        (kinds => Ends kinds resultTrails)
        (kinds => Ends kinds resultTrails)
        (kinds => Ends kinds trails)
        (stepSpace resultTrails)
        (stepAllCons assignDoc
          [IfBroken 0 below choice]
          (kinds => Ends kinds resultTrails)
          (kinds => Ends kinds assignTrails)
          (kinds => Ends kinds trails)
          (stepWeaken assignDoc
            (Starts False resultTrails)
            (kinds => Ends kinds resultTrails)
            (kinds => Ends kinds assignTrails)
            (kinds => Ends kinds assignTrails)
            assign
            (kinds good => endsStarts kinds resultTrails good)
            (kinds good => good))
          (stepAllOne
            (IfBroken 0 below choice)
            (kinds => Ends kinds assignTrails)
            (kinds => Ends kinds trails)
            (stepIfBroken 0 below choice _ trails body.left body.right)))))

--| A name, a `:` and the type after it, from a line start.
theorem backName ∀ (keyword name: Word)
    (open: isCloserText name.text = False):
    trailsBack [name, keyword] = name.trails :=
  rewrite open, Bool.orFalse name.trails

--| A plain definition's document passes the check from a line start, and leaves words on the line, a comment waiting
--| only if the value ends its line with one.
--|
--| Proof idea: the header's tokens each after the one before, the type after a space or a line break (`typedStep`),
--| then the `:=` after a space and the body in either of `IfBroken`'s forms (`bodyAfterStep`).
theorem plainDefStep ∀ (keyword: Comments) (name: Word) (colon: Comments) (result: Expr)
    (colonEq: Comments) (value: Expr)
    (keywordSound: (fixedWord "def" keyword).sound = True)
    (nameSound: name.sound = True)
    (colonSound: (fixedWord ":" colon).sound = True)
    (assignSound: (fixedWord ":=" colonEq).sound = True)
    (nameOpen: isCloserText name.text = False)
    (nameComma: name.notComma = True)
    (valueWithin: value.within1 = True)
    (resultEl: ∀ (around: Around) => Step (result.el around) (Starts around.hoisted around.before) (kinds =>
      Ends kinds result.trails))
    (valueEl: ∀ (around: Around) => Step (value.el around) (Starts around.hoisted around.before) (kinds =>
      Ends kinds value.trails))
    (hug: ∀ (around: Around) (open: Doc) => value.callHug { around | hoisted = True } = Some open
      → Step open (Starts True around.before) (kinds => Ends kinds value.trails)):
    Step (plainDef keyword name colon result colonEq value) (Starts True False) (kinds => Ends kinds value.trails) :=
  let start: Around := { before = False, hoisted = True, item = False, at = 0, inArm = False }
  let keywordWord := fixedWord "def" keyword
  let colonWord := fixedWord ":" colon
  let assign := fixedWord ":=" colonEq
  let colonAround := start.next (trailsBack [name, keywordWord]) 2
  let typeDoc := result.el (start.next colonWord.trails 3)
  let typed := if colonWord.trails then [Nest 4 (Doc.concat [HardLine, typeDoc])] else [Doc.text " ", Nest 4 typeDoc]
  let keywordStep: Step (keywordWord.leaf start 0) (Starts True False) (kinds => Ends kinds keywordWord.trails) :=
    plainWordStep keywordWord start 0 keywordSound byComputing byComputing
  let nameStep: Step (name.leaf (start.next keywordWord.trails 1) 1) (Starts False keywordWord.trails) (kinds =>
    Ends kinds name.trails) :=
    plainWordStep name (start.next keywordWord.trails 1) 1 nameSound nameComma nameOpen
  let headStep: Step (spaced (headDocs start [keywordWord, name])) (Starts True False) (kinds =>
    Ends kinds name.trails) :=
    stepDocConcat
      [keywordWord.leaf start 0, Doc.text " ", name.leaf (start.next keywordWord.trails 1) 1] _ _
      (stepAllCons
        (keywordWord.leaf start 0)
        [Doc.text " ", name.leaf (start.next keywordWord.trails 1) 1]
        (Starts True False)
        (kinds => Ends kinds keywordWord.trails)
        (kinds => Ends kinds name.trails)
        keywordStep
        (stepAllCons
          (Doc.text " ")
          [name.leaf (start.next keywordWord.trails 1) 1]
          (kinds => Ends kinds keywordWord.trails)
          (kinds => Ends kinds keywordWord.trails)
          (kinds => Ends kinds name.trails)
          (stepSpace keywordWord.trails)
          (stepAllOne
            (name.leaf (start.next keywordWord.trails 1) 1)
            (kinds => Ends kinds keywordWord.trails)
            (kinds => Ends kinds name.trails)
            (stepWeaken
              (name.leaf (start.next keywordWord.trails 1) 1)
              (Starts False keywordWord.trails)
              (kinds => Ends kinds keywordWord.trails)
              (kinds => Ends kinds name.trails)
              (kinds => Ends kinds name.trails)
              nameStep
              (kinds good => endsStarts kinds keywordWord.trails good)
              (kinds good => good)))))
  let colonStep: Step (colonWord.leaf colonAround 2) (Starts False name.trails) (kinds =>
    Ends kinds colonWord.trails) :=
    stepWeaken
      (colonWord.leaf colonAround 2)
      (Starts False (trailsBack [name, keywordWord]))
      (Starts False name.trails)
      (kinds => Ends kinds colonWord.trails)
      (kinds => Ends kinds colonWord.trails)
      (plainWordStep colonWord colonAround 2 colonSound byComputing byComputing)
      (kinds good => rewrite backName keywordWord name nameOpen then good)
      (kinds good => good)
  let headerStep: Step
    (Doc.concat ([spaced (headDocs start [keywordWord, name]), colonWord.leaf colonAround 2] ++ typed))
    (Starts True False)
    (kinds => Ends kinds result.trails) :=
    stepDocConcat
      ([spaced (headDocs start [keywordWord, name]), colonWord.leaf colonAround 2] ++ typed) _ _
      (stepAllAppend
        [spaced (headDocs start [keywordWord, name]), colonWord.leaf colonAround 2]
        typed
        (Starts True False)
        (kinds => Ends kinds colonWord.trails)
        (kinds => Ends kinds result.trails)
        (stepAllCons
          (spaced (headDocs start [keywordWord, name]))
          [colonWord.leaf colonAround 2]
          (Starts True False)
          (kinds => Ends kinds name.trails)
          (kinds => Ends kinds colonWord.trails)
          headStep
          (stepAllOne
            (colonWord.leaf colonAround 2)
            (kinds => Ends kinds name.trails)
            (kinds => Ends kinds colonWord.trails)
            (stepWeaken
              (colonWord.leaf colonAround 2)
              (Starts False name.trails)
              (kinds => Ends kinds name.trails)
              (kinds => Ends kinds colonWord.trails)
              (kinds => Ends kinds colonWord.trails)
              colonStep
              (kinds good => endsStarts kinds name.trails good)
              (kinds good => good))))
        (typedStep colonWord.trails typeDoc result.trails (resultEl (start.next colonWord.trails 3))))
  let assignAround := start.next result.trails (3 + result.size)
  let bodyAround := start.next assign.trails (4 + result.size)
  let headWords := [keywordWord, name]
  let inside :=
    (headWords.reverse.drop 1 |> .any Word.trails)
      || colonWord.trails
      || (result.words.reverse.drop 1 |> .any Word.trails)
      || (value.layoutBody && (lastCode headWords).trails)
  defFromStep
    (Doc.concat ([spaced (headDocs start [keywordWord, name]), colonWord.leaf colonAround 2] ++ typed))
    ((Doc.concat ([spaced (headDocs start [keywordWord, name]), colonWord.leaf colonAround 2] ++ typed)).forcesBreak
      || inside)
    (assign.leaf assignAround (3 + result.size))
    (bodyAfter value assign bodyAround False).fst
    (bodyAfter value assign bodyAround False).snd
    result.trails
    assign.trails
    value.trails
    headerStep
    (plainWordStep assign assignAround (3 + result.size) assignSound byComputing byComputing)
    (bodyAfterStep value assign bodyAround False valueWithin (valueEl bodyAround) (open found =>
      hug bodyAround open found))

-- A call's hug.

--| A call's hug on a `:=` line passes the check from where a space leaves the printer (open).
theorem callHugStep ∀ (value: Expr) (around: Around) (open: Doc)
    (within: value.within1 = True)
    (sound: value.sound = True)
    (nonCloser: value.nonCloser = True)
    (spelled: value.spelled = True)
    (lexical: value.lexical1 = True)
    (shaped: value.shaped1 = True)
    (found: value.callHug { around | hoisted = True } = Some open):
    Step open (Starts True around.before) (kinds => Ends kinds value.trails) :=
  match value, within with
    | App head [argument, ..rest], within =>
      appHugStep head
        [argument, ..rest]
        around
        open
        (List.consNotNil argument rest)
        within
        sound
        nonCloser
        spelled
        lexical
        shaped
        (inside =>
          elStep head inside
            (Bool.andLeft within)
            (Bool.andLeft sound)
            (Bool.andLeft nonCloser)
            (Bool.andLeft spelled)
            (Bool.andLeft lexical)
            (Bool.andLeft (Bool.andRight shaped)))
        (allElStep
          [argument, ..rest]
          (Bool.andRight within)
          (Bool.andRight sound)
          (Bool.andRight nonCloser)
          (Bool.andRight spelled)
          (Bool.andRight lexical)
          (Bool.andRight (Bool.andRight (Bool.andRight shaped))))
        (argsBracketEl [argument, ..rest] (Bool.andRight within))
        found

-- The declaration.

--| A slice 1 declaration's document passes the check from the start of the output (`laysCheck`'s test).
--|
--| Proof idea: `doc1` is `plainDef` (`plainDefIs`), which `plainDefStep` steps from the start of the output, each
--| expression's element by `elStep`; the declaration's facts are each token's.
theorem declChecks ∀ (decl: Decl) (doc: Doc)
    (within: decl.within1 = True)
    (shaped: decl.shaped1 = True)
    (sound: decl.sound = True)
    (joins: DeclJoins lexKind decl)
    (lexical: decl.lexical1 = True)
    (shows: decl.doc1 = Some doc):
    (laysKinds doc { Kinds.none | start = True }).isSome = True :=
  match decl, joins with
    | Definition [] header (Assigned colonEq value), (_, _, _, _, _, _) =>
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
          let (nonCloser, spelled) :=
            declTexts
              (Definition []
                {
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
                }
                (Assigned colonEq value))
              joins
          rewrite <- Option.someInjective shows, plainDefIs keyword name colon result colonEq value then
            match plainDefStep keyword name colon result colonEq value
              (Bool.andLeft sound)
              (Bool.andLeft (Bool.andRight sound))
              (Bool.andLeft (Bool.andRight (Bool.andRight sound)))
              (Bool.andLeft (Bool.andRight (Bool.andRight (Bool.andRight (Bool.andRight sound)))))
              (Bool.notTrue _ (Bool.andLeft nonCloser))
              (Bool.andLeft spelled)
              (Bool.andRight within)
              (around =>
                elStep result around
                  (Bool.andRight (Bool.andLeft within))
                  (Bool.andLeft (Bool.andRight (Bool.andRight (Bool.andRight sound))))
                  (Bool.andLeft (Bool.andRight nonCloser))
                  (Bool.andLeft (Bool.andRight spelled))
                  (Bool.andLeft (Bool.andRight lexical))
                  (Bool.andLeft shaped))
              (around =>
                elStep value around
                  (Bool.andRight within)
                  (Bool.andRight (Bool.andRight (Bool.andRight (Bool.andRight (Bool.andRight sound)))))
                  (Bool.andRight (Bool.andRight nonCloser))
                  (Bool.andRight (Bool.andRight spelled))
                  (Bool.andRight (Bool.andRight lexical))
                  (Bool.andRight shaped))
              (around open found =>
                callHugStep value around open
                  (Bool.andRight within)
                  (Bool.andRight (Bool.andRight (Bool.andRight (Bool.andRight (Bool.andRight sound)))))
                  (Bool.andRight (Bool.andRight nonCloser))
                  (Bool.andRight (Bool.andRight spelled))
                  (Bool.andRight (Bool.andRight lexical))
                  (Bool.andRight shaped)
                  found)
              { Kinds.none | start = True }
              byComputing with
              | (after, found, _) => rewrite found
