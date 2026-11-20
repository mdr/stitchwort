import random, os, glob, re
from thm import theorems, ROOT
S=ROOT+'/tools/fmt/src/'
def pool(globs, pred=lambda n,b: True):
    out=[]
    for g in globs:
        for p in sorted(glob.glob(S+g)):
            for n,l,b in theorems(p):
                if pred(n,b): out.append((os.path.relpath(p,ROOT),l,n,b))
    return out
walky=re.compile(r'Parse\.(Gives|ReadsIn|ReadsAt|Follows|Reads)|Kept|Carries')
pools={
 'dispatcher': pool(['Fmt/Kinds.sw','Fmt/SpellProofs.sw','Fmt/TokenProofs.sw','Syntax/Settle*Proofs.sw','Fmt/Spacing*Proofs.sw']),
 'tree': pool(['Syntax/ParseWalk*.sw','Syntax/ParseProofs.sw'], lambda n,b: not walky.search('\n'.join(b))),
 'printer': pool(['Fmt/JoinProofs.sw','Fmt/PassProofs.sw','Fmt/TreeJoinProofs.sw','Fmt/GlueProofs.sw']),
}
r=random.Random(4242)
for k,p in pools.items():
    tot=sum(len(b) for *_,b in p)
    print(f'=========== POOL {k}: {len(p)} theorems, {tot} lines')
    for path,l,n,b in r.sample(p,10):
        print(f'### [{k}] {path}:{l} {n} ({len(b)} lines)'); print('\n'.join(b)); print()
