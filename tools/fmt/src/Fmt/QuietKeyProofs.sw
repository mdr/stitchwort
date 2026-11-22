--| Key facts of documents (ticket 18h): what `allKeysFrom` says of concatenations, joins and the pieces of a call.

namespace Fmt.QuietKeyProofs
import Std (Bool, Doc, Eq, List, Nat, Option, Text, Void)
import Std.Doc (..)
import Syntax (Comments, Expr, InfixKind, Word)
import Fmt (..)
import Fmt.AppHolds (AppHolds, appFromHolds)
import Fmt.HangProofs (Gap, prefixGapIs)
import Fmt.MarkProofs (allKeysFrom, keysFrom)
import Fmt.AppHangProofs (appDocsIs, argAround)
import Fmt.ExprHangProofs (..)

-- Lists of documents.

theorem allKeysAppend ∀ (low: Nat) (front back: List Doc)
    (first: allKeysFrom low front = True)
    (second: allKeysFrom low back = True):
    allKeysFrom low (front ++ back) = True :=
  match front with
    | [] => second
    | [doc, ..rest] => rewrite Bool.andLeft first, allKeysAppend low rest back (Bool.andRight first) second

theorem allKeysFront ∀ (low: Nat) (front back: List Doc)
    (all: allKeysFrom low (front ++ back) = True):
    allKeysFrom low front = True :=
  match front with
    | [] => byComputing
    | [doc, ..rest] => rewrite Bool.andLeft all, allKeysFront low rest back (Bool.andRight all)

theorem allKeysTake ∀ (low: Nat) (docs: List Doc) (count: Nat)
    (all: allKeysFrom low docs = True):
    allKeysFrom low (docs.take count) = True :=
  match docs, count with
    | _, Zero => byComputing
    | [], Succ _ => byComputing
    | [doc, ..rest], Succ count => rewrite Bool.andLeft all, allKeysTake low rest count (Bool.andRight all)

theorem allKeysDrop ∀ (low: Nat) (docs: List Doc) (count: Nat)
    (all: allKeysFrom low docs = True):
    allKeysFrom low (docs.drop count) = True :=
  match docs, count with
    | _, Zero => all
    | [], Succ _ => byComputing
    | [doc, ..rest], Succ count => allKeysDrop low rest count (Bool.andRight all)

theorem allKeysHard ∀ (low: Nat) (docs: List Doc)
    (all: allKeysFrom low docs = True):
    allKeysFrom low (docs.concatMap (doc => [HardLine, doc])) = True :=
  match docs with
    | [] => byComputing
    | [doc, ..rest] => rewrite Bool.andLeft all, allKeysHard low rest (Bool.andRight all)

theorem joinedKeys ∀ (low: Nat) (docs: List Doc)
    (all: allKeysFrom low docs = True):
    allKeysFrom low (Doc.joinedWith (Doc.text " ") docs) = True :=
  match docs with
    | [] => byComputing
    | [only] => all
    | [doc, next, ..more] => rewrite Bool.andLeft all, joinedKeys low [next, ..more] (Bool.andRight all)

theorem keysSpaced ∀ (low: Nat) (docs: List Doc)
    (all: allKeysFrom low docs = True):
    keysFrom low (spaced docs) = True :=
  keysConcat low (Doc.joinedWith (Doc.text " ") docs) (joinedKeys low docs all)

theorem keysIf ∀ (low: Nat) (cond: Bool) (yes no: Doc)
    (first: keysFrom low yes = True)
    (second: keysFrom low no = True):
    keysFrom low (if cond then yes else no) = True :=
  match cond with
    | True => first
    | False => second

theorem allKeysIf ∀ (low: Nat) (cond: Bool) (yes no: List Doc)
    (first: allKeysFrom low yes = True)
    (second: allKeysFrom low no = True):
    allKeysFrom low (if cond then yes else no) = True :=
  match cond with
    | True => first
    | False => second

-- Tokens.

theorem pieceKeys ∀ (low: Nat) (text: Text): keysFrom low (piece text) = True :=
  keysIf low _ (Closing text) (Doc.text text) byComputing byComputing

-- Calls.

theorem allKeysBack ∀ (low: Nat) (front back: List Doc)
    (all: allKeysFrom low (front ++ back) = True):
    allKeysFrom low back = True :=
  match front with
    | [] => all
    | [doc, ..rest] => allKeysBack low rest back (Bool.andRight all)

theorem allKeysAll ∀ (low: Nat) (first: Doc) (more: List Doc)
    (all: List.All (doc => keysFrom low doc = True) [first, ..more]):
    allKeysFrom low [first, ..more] = True :=
  match more with
    | [] => rewrite all.left
    | [second, ..others] => rewrite all.left, allKeysAll low second others all.right

--| The elements of a call that break keep their keys: those kept on its line, spaced or filled, and each of the rest
--| after a `HardLine`.
theorem frontRestKeys ∀ (low id keep: Nat) (fillFront: Bool) (docs: List Doc)
    (all: allKeysFrom low docs = True):
    keysFrom low
      (Doc.concat [
        if fillFront then IdGroup id (Nest 4 (Fill (docs.take keep))) False else spaced (docs.take keep),
        if fillFront then
          IfBroken id
            (Nest 4 (Doc.concat (docs.drop keep |> .concatMap (doc => [HardLine, doc]))))
            (Nest 2 (Doc.concat (docs.drop keep |> .concatMap (doc => [HardLine, doc]))))
        else Nest 2 (Doc.concat (docs.drop keep |> .concatMap (doc => [HardLine, doc])))
      ])
      = True :=
  let kept := allKeysTake low docs keep all
  let rest := keysConcat low _ (allKeysHard low (docs.drop keep) (allKeysDrop low docs keep all))
  let restTail := Doc.concat (docs.drop keep |> .concatMap (doc => [HardLine, doc]))
  let frontDoc :=
    keysIf low fillFront
      (IdGroup id (Nest 4 (Fill (docs.take keep))) False)
      (spaced (docs.take keep))
      kept
      (keysSpaced low (docs.take keep) kept)
  let restDoc :=
    keysIf low fillFront (IfBroken id (Nest 4 restTail) (Nest 2 restTail)) (Nest 2 restTail) (rewrite rest) rest
  keysConcat low _ (rewrite frontDoc, restDoc)

--| The combinators a call's layouts use keep a document's keys, with no reading to keep (`[]` serves).
def keysHolds (low: Nat):
    AppHolds Nat
      (List Nat)
      (doc texts => keysFrom low doc = True)
      (docs texts => allKeysFrom low docs = True)
      (texts => texts)
      (a b => a ++ b)
      (a b => a ++ b) :=
  {
    nest = (indent doc texts keys => keys),
    flatten = (doc texts keys => keys),
    idGroup = (id hard doc texts keys => keys),
    ifBroken = (id broken plain texts left right => rewrite left, right),
    choice = (first more texts all => allKeysAll low first more all),
    fillOf = (docs texts keys => keys),
    spacedOf = (docs texts keys => keysSpaced low docs keys),
    hugged = (docs open texts last keys opened =>
      keysConcat low [Flatten (spaced docs), Doc.text " ", open] (rewrite keysSpaced low docs keys, opened)),
    frontRest = (id keep fillFront docs texts keys => frontRestKeys low id keep fillFront docs keys),
    consed = (doc docs first rest head tail => rewrite head, tail),
    snoced = (docs doc rest last front only => allKeysAppend low docs [doc] front (rewrite only)),
    consFlat = (first rest => byComputing),
    snocFlat = (first rest last => List.appendAssoc first rest last)
  }

--| A call's layouts keep its elements' keys, and its hug's.
--|
--| Proof idea: `appFromHolds`, with the combinators keeping a document's keys (`keysHolds`).
theorem appFromKeys ∀ (low id keep: Nat) (between betweenFront: Bool) (headDoc: Doc) (front: List Doc)
    (lastDoc: Doc) (hug: Option Doc)
    (all: allKeysFrom low ([headDoc, ..front] ++ [lastDoc]) = True)
    (hugKeys: ∀ (open: Doc) => hug = Some open → keysFrom low open = True):
    keysFrom low (appFrom id keep between betweenFront headDoc front lastDoc hug).doc = True :=
  let frontKeys := allKeysFront low [headDoc, ..front] [lastDoc] all
  (appFromHolds
    (keysHolds low)
    id
    keep
    between
    betweenFront
    headDoc
    lastDoc
    front
    hug
    []
    []
    []
    (Bool.andLeft frontKeys)
    (Bool.andRight frontKeys)
    (Bool.andLeft (allKeysBack low [headDoc, ..front] [lastDoc] all))
    hugKeys).left

--| What a call's arguments' documents keep: the documents before the last, the last's and its hug's.
def ArgKeys (low: Nat) (docs: (List Doc, Option (Doc, Option Doc))): Prop :=
  allKeysFrom low docs.fst = True
    ∧ keysFrom low (docs.snd.getOrElse (Nothing, None)).fst = True
    ∧ (∀ (open: Doc) => (docs.snd.getOrElse (Nothing, None)).snd = Some open → keysFrom low open = True)

-- Chains.

theorem chainOfKeys ∀ (low: Nat) (arms: Bool) (links: List Doc)
    (all: allKeysFrom low links = True):
    keysFrom low (chainOf arms links) = True :=
  match links with
    | [] => byComputing
    | [head, ..tail] =>
      rewrite keysConcat low
        [head, Nest (if arms then 0 else 2) (Doc.concat tail)]
        (rewrite Bool.andLeft all, keysConcat low tail (Bool.andRight all))
