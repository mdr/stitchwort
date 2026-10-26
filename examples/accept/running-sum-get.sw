-- Start times as a running sum of durations, read back with `get`: start k
-- is the sum of the durations before it, each task's slot pairs its start
-- with its end, and durations that are themselves spans (end minus begin)
-- fold over the pairs of the first k spans.
import Std (Eq, List, Nat)

def starts (start: Nat) (durations: List Nat): List Nat := durations.scanLeft start (total duration => total + duration)

def slots (start: Nat) (durations: List Nat): List (Nat, Nat) :=
  durations.zipWith (starts start durations) (duration begin => (begin, begin + duration))

test "starts" := starts 10 [2, 3, 4] == [10, 12, 15, 19]

test "slots" := slots 10 [2, 3, 4] == [(10, 12), (12, 15), (15, 19)]

theorem startAt (start: Nat) (durations: List Nat) (k: Nat) (h: k ≤ durations.length):
    (starts start durations).get k = Some (start + (durations.take k |> .sumBy (duration => duration))) :=
  rewrite List.getScanLeft (total duration => total + duration) durations start k h in
  Eq.cong Some (List.sumByFrom (durations.take k) start (duration => duration))

theorem slotAt (start: Nat) (durations: List Nat) (k: Nat):
    (slots start durations).get k
      = (durations.get k).map (duration => (start + (durations.take k |> .sumBy (d => d)), start + (durations.take k |> .sumBy (d => d)) + duration)) :=
  rewrite List.getZipWithScanLeft (total duration => total + duration) (duration begin => (begin, begin + duration)) durations start k,
    List.sumByFrom (durations.take k) start (d => d) in
  rfl

-- Durations from spans: start k folds over the first k (end, begin) pairs.
theorem startFromSpans (ends: List Nat) (begins: List Nat) (k: Nat) (h: k ≤ (ends.zipWith begins Nat.sub).length):
    (starts 0 (ends.zipWith begins Nat.sub)).get k
      = Some (List.zip (ends.take k) (begins.take k) |> .foldLeft 0 (total span => total + (span.fst - span.snd))) :=
  rewrite List.getScanLeft (total duration => total + duration) (ends.zipWith begins Nat.sub) 0 k h,
    List.takeZipWith Nat.sub ends begins k,
    List.foldLeftZipWith Nat.sub (total duration => total + duration) (ends.take k) (begins.take k) 0 in
  rfl
