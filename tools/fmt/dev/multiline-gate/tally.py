"""Counts the gate's results (run.sh): check A by outcome, check B by outcome, the hand cases apart.

Usage: tally.py WORK_DIR. Exits with status 1 if a file fails a check: check A's tests on an accepted file, or check
B's prediction (a layout whose groups keep `hangs` parses to its one-line form's tree).
"""
import collections, glob, os, sys

work = sys.argv[1]


def outcome_a(line):
    if line in ('nolex', 'leaves', 'noparse'):
        return "not accepted: doesn't parse"
    if line == 'outside':
        return 'not accepted: parses outside within1'
    shape, flags = line.split(' ')
    if set(flags) == {'T'}:
        return 'accepted, %s line%s, all seven tests pass' % (shape, '' if shape == 'one' else 's')
    return 'FAIL: accepted, and a test fails'


def outcome_b(line):
    if not line.startswith(('one ', 'multi ')):
        return 'one-line form is no slice 1 program'
    parts = line.split(' ')
    shape, hung, rest = parts[0], parts[1], parts[2]
    if hung == 'hung=T':
        if rest == 'same=T':
            return 'hangs, %s, same tree' % ('several lines' if shape == 'multi' else 'one line')
        return 'FAIL: hangs, and a different tree or no parse'
    if rest == 'same=T':
        return 'breaks hangs, same tree anyway'
    if rest == 'PARSEFAIL':
        return "breaks hangs, doesn't parse"
    return 'breaks hangs, parses to another tree'


failed = False
for label, pattern in (('generated', '[!h]*'), ('hand', 'hand')):
    for check, outcome in (('A', outcome_a), ('B', outcome_b)):
        counts = collections.Counter()
        for path in sorted(glob.glob(os.path.join(work, 'res', '%s.%s' % (check, pattern)))):
            cases = open(os.path.join(work, 'chunks', path.split('.', 1)[1].split('/')[-1] + '.cases')).read()
            lines = [l for l in open(path).read().split('\n') if l]
            if len(lines) != cases.count('###\n'):
                print('%s: %d results for %d cases' % (path, len(lines), cases.count('###\n')))
                failed = True
            counts.update(outcome(l) for l in lines)
        print('Check %s, %s files: %d' % (check, label, sum(counts.values())))
        for key, n in sorted(counts.items()):
            print('  %6d  %s' % (n, key))
            failed = failed or key.startswith('FAIL')
sys.exit(1 if failed else 0)
