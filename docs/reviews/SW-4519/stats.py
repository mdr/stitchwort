# Figures for SW-4519's map. Usage, from the repo root:
#   python3 -I docs/reviews/SW-4519/count.py tools/fmt/src thms.json
#   python3 -I docs/reviews/SW-4519/count.py tools/fmt/src raw.json --raw
#   python3 -I docs/reviews/SW-4519/stats.py thms.json
#   python3 -I docs/reviews/SW-4519/arms.py raw.json
import json, re, sys, collections
t = [x for x in json.load(open(sys.argv[1])) if '/Tests/' not in x['file']]
L = [(x, l) for x in t for l in x['body'].split('\n')]
atom = re.compile(r"^[A-Za-z_][\w.']*( _)*$|^_$")
lone = lambda l: atom.match(l) and l not in ('byComputing', 'cases', 'byWalking')
print('theorems', len(t), 'proof lines', sum(x['proof'] for x in t), 'statement lines', sum(x['stmt'] for x in t))
print('lone-argument lines: a bare name or _', sum(1 for x, l in L if lone(l)))
simple = re.compile(r"^\[[^\]]*\]$|^\([^()]*\)$")
print('... or a bracketed argument with no brackets inside', sum(1 for x, l in L if lone(l) or simple.match(l)))
print('lines naming Bool.andLeft/andRight/andIntro', sum(1 for x, l in L if re.search(r'Bool\.and(Left|Right|Intro)', l)))
print('match arms', sum(1 for x, l in L if l.startswith('|')), 'of them => byComputing', sum(1 for x, l in L if re.match(r'^\|.*=> byComputing$', l)))
w = [x for x in t if 'byWalking' in x['body']]
print('walk theorems', len(w), 'their proof lines', sum(x['proof'] for x in w))
hand = [x for x in t if re.search(r'\b(Parse\.followsThen|Parse\.givesThen|Parse\.readsThen|Parse\.readsAtThen|reads0Then|followsThenEq)\b', x['body']) and 'byWalking' not in x['body']]
print('hand parser steps (a then-lemma, no walk)', len(hand), sum(x['proof'] for x in hand))
