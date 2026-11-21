-- Split as deep as the case needs: once `edge` is `Plain o` or `Waiting o`,
-- the goal is stuck on the field `o`, which is split next. Nothing the proof
-- didn't name is split: `first` and `trails` stay as they are.
import Std (Bool, Option, Text)

type Edge = | Plain (word: Option Text) | Waiting (word: Option Text)

def Follows (word next: Text): Prop := word ≠ next

def Ready (trails: Bool) (first: Text) (edge: Edge): Prop := match edge with
  | Plain None => True
  | Plain (Some word) => Follows word first
  | Waiting None => trails = True
  | Waiting (Some word) => trails = True ∧ word ≠ ""

def Free (trails: Bool) (edge: Edge): Prop := match edge with
  | Plain None => True
  | Plain (Some word) => ∀ (next: Text) => Follows word next
  | Waiting None => trails = True
  | Waiting (Some word) => trails = True ∧ word ≠ ""

theorem freeReady ∀ (trails: Bool) (first: Text) (edge: Edge) (free: Free trails edge): Ready trails first edge :=
  cases edge then free first
