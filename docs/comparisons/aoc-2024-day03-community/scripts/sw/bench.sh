T=/Users/matt/repos/mdr/stitchwort/.claude/worktrees/agent-a3e3864e75e2601d3/docs/comparisons/aoc-2024-day03-community/scripts/time3.sh
D=/private/tmp/claude-501/-Users-matt-repos-mdr-stitchwort/3eef38f5-69c2-4f26-b1b3-39bd97dd0fd4/scratchpad/d2024-03
P=$D/proj
IN=/Users/matt/repos/mdr/stitchwort/.claude/worktrees/agent-a3e3864e75e2601d3/aoc/inputs/2024/day03.txt
SW=/Users/matt/repos/mdr/stitchwort/target/release/stitchwort
for m in Hello Starting Scan Split; do
  (cd $P && $SW build --native -o $D/native-$m Scratch.$m.main 2>&1 | tail -3)
done
for m in Hello Starting Scan Split; do
  echo "== $m run";    sh $T $P $IN 3 $SW run Scratch.$m.main
  echo "== $m js";     sh $T $P $IN 3 $SW run --js Scratch.$m.main
  echo "== $m native"; sh $T $P $IN 3 $D/native-$m
done
for m in Starting Scan Split; do
  echo "== $m x10 run";    sh $T $P $D/x10.txt 1 $SW run Scratch.$m.main
  echo "== $m x10 js";     sh $T $P $D/x10.txt 1 $SW run --js Scratch.$m.main
  echo "== $m x10 native"; sh $T $P $D/x10.txt 1 $D/native-$m
  echo "== $m x100 native"; sh $T $P $D/x100.txt 1 $D/native-$m
  echo "== $m x100 js"; sh $T $P $D/x100.txt 1 $SW run --js Scratch.$m.main
done
