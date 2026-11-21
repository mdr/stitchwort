-- An `_` for an argument that a later argument's proof fixes is what that
-- proof's type says, not what an unfolding equates with it. `Joins` reads a
-- `Group` as the document inside it, so comparing `Pass ?doc pre post` with
-- `Pass (Doc.group (inner flag)) pre post` by their unfoldings solves `?doc`
-- with the group's contents, and the call's type then doesn't match the goal,
-- which has the group. After that failure the call is elaborated again with
-- the later argument's type compared by the arguments of the two calls,
-- which makes `_` the group (SW-4480).
import Std (Bool, Doc, Nat)
import Std.Doc (..)
import Std.Doc.Proofs (..)

def Pass (doc: Doc) (pre post: Edge → Prop): Prop :=
  ∀ (edge: Edge) (next: Edge → Prop) => pre edge
    → (∀ (after: Edge) => post after → next after)
    → Joins (follows left => True) doc edge next

type Node = | Leaf (flag: Bool) | Box (flag: Bool)

def inner (flag: Bool): Doc := if flag then Chunk "a" 1 else Chunk "b" 1

def Node.framed (node: Node) (doc: Doc): Doc := Doc.concat [Chunk "x" 1, if node.flag then Displaced doc else doc]

def Node.shown (node: Node): Doc := match node with
  | Leaf flag => Chunk "l" 1
  | Box flag => node.framed (Doc.group (inner flag))

theorem shownPass ∀ (node: Node) (pre post: Edge → Prop)
    (framedPass: ∀ (node: Node) (doc: Doc) (pre post: Edge → Prop) (passes: Pass doc pre post) => Pass
      (node.framed doc)
      pre
      post)
    (groupedPass: ∀ (flag: Bool) (pre post: Edge → Prop) => Pass (Doc.group (inner flag)) pre post)
    (leafPass: ∀ (flag: Bool) (pre post: Edge → Prop) => Pass (Chunk "l" 1) pre post):
    Pass node.shown pre post :=
  match node with
    | Leaf flag => leafPass flag pre post
    | Box flag => framedPass (Box flag) _ pre post (groupedPass flag pre post)
