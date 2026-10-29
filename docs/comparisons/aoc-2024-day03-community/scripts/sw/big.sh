T=/Users/matt/repos/mdr/stitchwort/.claude/worktrees/agent-a3e3864e75e2601d3/docs/comparisons/aoc-2024-day03-community/scripts/time3.sh
A=/Users/matt/repos/mdr/stitchwort/.claude/worktrees/agent-a3e3864e75e2601d3/aoc
D=/private/tmp/claude-501/-Users-matt-repos-mdr-stitchwort/3eef38f5-69c2-4f26-b1b3-39bd97dd0fd4/scratchpad/d2024-03
SW=/Users/matt/repos/mdr/stitchwort/target/release/stitchwort
echo run x10; sh $T $A $D/x10.txt 2 $SW run Aoc.Year2024.Day03.main
echo js x10; sh $T $A $D/x10.txt 2 $SW run --js Aoc.Year2024.Day03.main
echo native x10; sh $T $A $D/x10.txt 2 $D/day03-native
echo native x100; sh $T $A $D/x100.txt 2 $D/day03-native
echo js x100; sh $T $A $D/x100.txt 1 $SW run --js Aoc.Year2024.Day03.main
