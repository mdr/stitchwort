rev=$1
cd /Users/agent/repos/mdr/stitchwort/.claude/worktrees/SW-4464
for n in signSymbolic closerNotComma endedWeaker allAppendB itemsParsed givesExpect givesTupleClose givesParenClose givesTupleEnd parenParsed tupleParsed givesCommaListFrom commaEnd followsPeek followsBump followsExpect followsExpectOn followsParenClose alikeParen allTokensWithout joinsWeaker writeWeaker sepWeaker passesCons joinsAllAppend passesAppend; do
 for f in $(git ls-tree -r --name-only $rev tools/fmt/src std | grep '\.sw$'); do
   c=$(git show $rev:$f | awk -v n="$n" '$0 ~ "^(pub )?(theorem|def|lemma) "n"( |:|$)" {p=1} p&&/^$/{exit} p{c++} END{print c+0}')
   [ "$c" != 0 ] && echo "$n $f $c"
 done
done
