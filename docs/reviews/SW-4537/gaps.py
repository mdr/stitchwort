"""Where the gap is. usage: python3 gaps.py results-reserve.csv

Each drawn theorem's proof-line gap is Stitchwort's proof lines less the shorter port's (negative where
both ports are longer), filed under the cause that the batch notes and the ports show. Two theorems are
split between causes as measured: homeStands' layout is about 75 of its lines (batch B), and unaryHung has
19 lines restating a hypothesis after a rewrite and 32 lines holding one argument (counted in its source).
The share of slice 1 is the Hansen-Hurwitz estimate, sum over strata of W_s * mean(gap_i / x_i), over all
slice-1 lines. exprBlanks is counted (the orchestrator kept it); appFromSpells, the printer reserve, is
reported apart.
"""
import sys, csv, collections
W = {'walk': 7032, 'two-run': 6850, 'readback': 10299, 'tree': 7035, 'lexer': 3575, 'settle': 7783,
     'printer': 27509, 'top': 1703}
CAUSE = {
    'exprBlanks': 'case split', 'headerResult1': 'case split', 'wordsCalmKeep': 'case split',
    'closerFitsOf': 'case split', 'walkAttributesAlike': 'case split', 'heldItemSeat': 'case split',
    'parenInnerKept': 'case split', 'refinesAppend': 'case split', 'anyHangsOf': 'case split',
    'blankItemHangs': 'layout', 'homeStands': {'layout': 75, 'Boolean bookkeeping': None},
    'unaryHung': {'equation transport': 19, 'layout': 32, 'mixed': None},
    'runsBlockOneLine': 'Honest dropped', 'runsWalkHere': 'Honest dropped',
    'settledHomed': 'small steps', 'notedCloserHangs': 'small steps', 'plainOfShapes': 'small steps',
    'itemsShapesOfKinds1': 'small steps', 'endsQuietJoin': 'small steps', 'statementsWalk': 'small steps',
    'witnessUnreturned': 'small steps', 'firstThreeKeepMeaning': 'small steps', 'openWithin': 'small steps',
    'stepsIfBroken': 'small steps', 'placedSteps': 'small steps', 'readsAtAtValue': 'small steps',
    'followsParenAtom': 'monad steps', 'followsListPatternStep': 'monad steps', 'readsBlockResult': 'monad steps',
    'argumentMinusDeaf': 'unfolding records', 'appFromSpells': 'restated terms',
}
rows = list(csv.DictReader(open(sys.argv[1])))
by = collections.Counter(r['stratum'] for r in rows if r['role'] == 'main')
lines, share = collections.Counter(), collections.Counter()
for r in rows:
    sw = int(r['sw_proof']); x = int(r['sw_stmt']) + sw
    gap = sw - min(int(r['lean_proof']), int(r['rocq_proof']))
    c = CAUSE[r['name']]
    parts = {c: gap} if isinstance(c, str) else {k: (v if v is not None else gap - sum(
        u for u in c.values() if u is not None)) for k, v in c.items()}
    for k, g in parts.items():
        key = k + (' (reserve)' if r['role'] != 'main' else '')
        lines[key] += g
        if r['role'] == 'main': share[key] += W[r['stratum']] * g / x / by[r['stratum']]
total = sum(W.values())
print('| Cause | Proof lines on the sample | Est. share of slice 1 lines |')
print('|---|---|---|')
for k, g in sorted(lines.items(), key=lambda kv: -share.get(kv[0], 0)):
    print(f"| {k} | {g} | {100 * share[k] / total:.1f}% |" if k in share else f"| {k} | {g} | (reserve) |")
print(f"| all | {sum(v for k, v in lines.items() if 'reserve' not in k)} | {100 * sum(share.values()) / total:.1f}% |")
