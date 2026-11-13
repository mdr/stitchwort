# SW-3111: the deletion oracle over the whole corpus

Run by Overmind on main at 0e0665b6c, 13 Nov 2026, 17:33–19:53 (2 h 20 min),
release build, fresh check caches, `Promise::ProofsOnly`. Every step exited 0
with no skipped files.

| Step | Wall time | Sites | Still needed | Can go | Changed meaning | Unparseable |
|---|---|---|---|---|---|---|
| `oracle readings --std` | 2317 s | 196 `.read` | 179 | 17 | 0 | 0 |
| `oracle builds --std` | 893 s | 49 helpers | 29 | 20 | 0 | 0 |
| `oracle readings` (aoc) | 4651 s | 304 `.read` | 296 | 8 | 0 | 0 |
| `oracle builds` (aoc) | 550 s | 48 helpers | 34 | 14 | 0 | 0 |

**Nothing changed meaning silently.** 59 sites can go: 25 `.read`s and 34
build helpers. Removable helpers by name: `Bool.falseOfNotTrue` 15 (14 in std,
11 of them in `Float/Float.sw`), `List.memContains.backward` 10,
`DecEq.trueOfNe` 3, `Nat.dividesIff.backward` 2, `List.isLeHeadIff.backward`
1, `List.isDistinctIff.backward` 1, `Nat.leqFalseOfLess` 1. The rest of the
helper uses (63) are still needed.

## Sites

std paths are relative to `crates/elab/src/std/`, aoc paths to `aoc/`.
Lines with "…" are shortened; the full replacement is the helper's last
explicit argument (or the `.backward`'s argument).

### `.read` that can go (std, 17)

```
Float/Theory.sw:26:43
Float/Theory.sw:468:57
Float/Theory.sw:494:57
Float/Theory.sw:530:14
Float/Theory.sw:536:31
Float/Theory.sw:540:33
Float/Theory.sw:552:33
Float/Theory.sw:554:26
Float/Theory.sw:949:6
Float/Theory.sw:951:6
Float/Theory.sw:1396:24
Float/Theory.sw:1628:24
Int/Lemmas.sw:248:38
List/Lemmas.sw:1675:53
List/Lemmas.sw:1732:57
Nat/Bits.sw:53:50
Nat/Pigeonhole.sw:27:65
```

### Build helpers that can go (std, 20)

```
Bool/Bool.sw:68:60   Bool.falseOfNotTrue (Nat.leq 3 2) Bool.falseNotTrue -> Bool.falseNotTrue
Float/Float.sw:163:7   Bool.falseOfNotTrue (Nat.equal (n - 9223372036854775808) 9221120237041090560) (h => omega [Float.highBound n v hk]) -> (h => omega [Float.highBound n v hk])
Float/Float.sw:166:7   Bool.falseOfNotTrue (Nat.equal (n + 9223372036854775808) 9221120237041090560) (h => omega) -> (h => omega)
Float/Float.sw:431:46  Bool.falseOfNotTrue (Nat.equal m 0) (e => omega) -> (e => omega)
Float/Float.sw:458:38  Bool.falseOfNotTrue (Nat.equal m 0) (e => omega) -> (e => omega)
Float/Float.sw:460:7   Bool.falseOfNotTrue (Nat.equal m 9223372036854775808) (e => omega [Float.highBound m vm hp]) -> (e => omega [Float.highBound m vm hp])
Float/Float.sw:463:38  Bool.falseOfNotTrue (Nat.equal m 0) (e => omega) -> (e => omega)
Float/Float.sw:466:60  Bool.falseOfNotTrue (Nat.equal m 9223372036854775808) (e => omega) -> (e => omega)
Float/Float.sw:469:60  Bool.falseOfNotTrue (Nat.equal n 9223372036854775808) (e => omega) -> (e => omega)
Float/Float.sw:475:56  Bool.falseOfNotTrue (Nat.equal m 9223372036854775808) (e => omega) -> (e => omega)
Float/Float.sw:476:38  Bool.falseOfNotTrue (Nat.equal n 0) (e => omega) -> (e => omega)
Float/Float.sw:477:56  Bool.falseOfNotTrue (Nat.equal n 9223372036854775808) (e => omega) -> (e => omega)
List/Lemmas.sw:3378:76 List.memContains.backward: (List.memContains xs x).backward (rewrite <- same.read in member) -> (rewrite <- same.read in member)
List/Sort.sw:144:37   List.isLeHeadIff.backward: (List.isLeHeadIff le x rest).backward head -> head
Nat/Digits.sw:222:8   Nat.leqFalseOfLess 9 (a * 10 + d) (Nat.leTrans …) -> the (Nat.leTrans …) argument
Nat/Divides.sw:68:7   Nat.dividesIff.backward: Iff.backward (Nat.dividesIff d (a + b)) (Witness (s + t) (ring [es, et])) -> (Witness (s + t) (ring [es, et]))
Nat/Divides.sw:74:22  Nat.dividesIff.backward: Iff.backward (Nat.dividesIff d (q * n)) (Witness (q * t) (ring [q * e])) -> (Witness (q * t) (ring [q * e]))
Set/Spec.sw:606:9    Bool.falseOfNotTrue (Set.contains a key) (inA => …) -> (inA => …)
Set/Spec.sw:622:9    Bool.falseOfNotTrue (Set.contains (Set.map t f) (f key)) (inImage => match …) -> (inImage => match …)
Set/Spec.sw:736:85   List.memContains.backward: (List.memContains universe key).backward there -> there
```

### `.read` that can go (aoc, 8)

```
src/Aoc/Year2020/Day04/Proofs/Rules.sw:62:25
src/Aoc/Year2020/Day05/Proofs/Proofs.sw:37:25
src/Aoc/Year2020/Day05/Proofs/Proofs.sw:69:28
src/Aoc/Year2020/Day13/Proofs/Part1.sw:71:45
src/Aoc/Year2021/Day15/Proofs/Levels.sw:50:27
src/Aoc/Year2021/Day15/Proofs/Levels.sw:54:28
src/Aoc/Year2024/Day07/Proofs/Proofs.sw:29:26
src/Aoc/Year2024/Day07/Proofs/Proofs.sw:33:29
```

### Build helpers that can go (aoc, 14)

```
src/Aoc/Year2020/Day05/Proofs/Proofs.sw:112:63  List.memContains.backward: (List.memContains ids seat).backward member -> member
src/Aoc/Year2020/Day06/Proofs/Parse.sw:25:15    List.memContains.backward: (List.memContains letters question).backward ((Set.containsFromListIff letters question).forward …) -> the inner argument
src/Aoc/Year2020/Day09/Proofs/Window.sw:16:52    DecEq.trueOfNe (same => differ (omega)) -> (same => differ (omega))
src/Aoc/Year2020/Day14/Proofs/Decode.sw:90:15   List.memContains.backward: (List.memContains (mask.decode address) target).backward (decodeComplete mask address target decodes…) -> the inner argument
src/Aoc/Year2020/Day17/Proofs/Neighbours.sw:58:61 DecEq.trueOfNe (differ => e.read.read (Eq.sym differ)) -> (differ => e.read.read (Eq.sym differ))
src/Aoc/Year2020/Day20/Proofs/Corners.sw:33:47   DecEq.trueOfNe different -> different
src/Aoc/Year2020/Day20/Proofs/Monsters.sw:145:20 List.memContains.backward: (List.memContains cells at).backward ((listed.right at).backward found) -> ((listed.right at).backward found)
src/Aoc/Year2021/Day12/Proofs/Parts.sw:18:9     List.memContains.backward: (List.memContains (smallCaves passages) c).backward (List.memFilterIntro …) -> (List.memFilterIntro …)
src/Aoc/Year2021/Day12/Proofs/Rules.sw:77:11    List.memContains.backward: (List.memContains caves c).backward (And.left both) -> (And.left both)
src/Aoc/Year2021/Day12/Proofs/Rules.sw:79:5     List.memContains.backward: (List.memContains _ c).backward (List.memFilterIntro caves …) -> (List.memFilterIntro …)
src/Aoc/Year2024/Day12/Proofs/Sides.sw:116:45   List.memContains.backward: (List.memContains region.plots plot).backward member -> member
src/Aoc/Year2024/Day12/Proofs/Sides.sw:188:12   List.memContains.backward: (List.memContains region.plots plot).backward member -> member
src/Aoc/Year2024/Day14/Proofs/Proofs.sw:52:3    List.isDistinctIff.backward: (List.isDistinctIff (space.positionsAfter seconds robots)).backward (rewrite <- positionsCorrect …) -> (rewrite <- positionsCorrect …)
src/Aoc/Year2024/Day15/Proofs/Part2.sw:229:11   Bool.falseOfNotTrue (moved.contains position) (inMoved => match Iff.forward …) -> (inMoved => match …)
```

The oracle's per-site JSON (`removable[].text` and `.replacement`) can be
regenerated with `stitchwort oracle readings|builds --json` on the files
named here.
