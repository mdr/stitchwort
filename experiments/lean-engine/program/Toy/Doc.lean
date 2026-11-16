/-
The layout engine's documents: a port, function for function, of
`tools/toyfmt/src/Toy/Doc/Doc.sw`. Constructors keep their Stitchwort
names, so `Doc.Concat` (the node) and `Doc.concat` (the function that
drops empty documents) stay apart as they do there.
-/
import Toy.Text

namespace Toy

inductive Doc where
  | Empty
  | Chunk (text : Text) (width : Nat)
  | Line
  | SoftLine
  | HardLine
  | Blank
  | Nest (indent : Nat) (inner : Doc)
  | Group (inner : Doc) (hard : Bool)
  | Concat (docs : List Doc)
  | Fill (items : List Doc)
  | Flatten (inner : Doc)
  | Choice (options : List Doc)
  | OneLineBelow (inner : Doc)
  | LineSuffix (comment : Text)
  | LineStart
  | CommentEnd
  | LineStartHere
  | BreakParent

namespace Doc

def text (text : Text) : Doc := Chunk text text.length

def isEmpty : Doc → Bool
  | Empty => true
  | _ => false

mutual
  def forcesBreak : Doc → Bool
    | HardLine => true
    | LineStart => true
    | CommentEnd => true
    | LineStartHere => true
    | BreakParent => true
    | OneLineBelow _ => true
    | Group _ hard => hard
    | Nest _ inner => inner.forcesBreak
    | Flatten inner => inner.forcesBreak
    | Concat docs => anyForcesBreak docs
    | Fill items => anyForcesBreak items
    | Choice options => allForceBreak options
    | _ => false

  def anyForcesBreak : List Doc → Bool
    | [] => false
    | doc :: docs => doc.forcesBreak || anyForcesBreak docs

  def allForceBreak : List Doc → Bool
    | [] => true
    | doc :: docs => doc.forcesBreak && allForceBreak docs
end

def group (inner : Doc) : Doc := Group inner inner.forcesBreak

def concat (docs : List Doc) : Doc :=
  match docs.filter (fun doc => !doc.isEmpty) with
  | [] => Empty
  | [only] => only
  | several => Concat several

def joinedWith (separator : Doc) : List Doc → List Doc
  | [] => []
  | [only] => [only]
  | doc :: docs => doc :: separator :: joinedWith separator docs

def joined (docs : List Doc) (separator : Doc) : Doc := concat (joinedWith separator docs)

mutual
  def size : Doc → Nat
    | Nest _ inner => 1 + inner.size
    | Group inner _ => 1 + inner.size
    | Flatten inner => 1 + inner.size
    | OneLineBelow inner => 2 + inner.size
    | Concat docs => 1 + sizes docs
    | Fill items => 1 + 2 * sizes items
    | Choice options => 1 + sizes options
    | _ => 1

  def sizes : List Doc → Nat
    | [] => 0
    | doc :: docs => doc.size + sizes docs
end

end Doc
end Toy
