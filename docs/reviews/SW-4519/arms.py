import json, re, collections, sys
t = [x for x in json.load(open(sys.argv[1])) if '/Tests/' not in x['file']]
def norm(b, loose):
    b=re.sub(r'"[^"]*"','S',b); b=re.sub(r"\b[A-Za-z_][\w']*\b",'I',b)
    if loose: b=re.sub(r'\((I ?)+\)','I',b)  # constructor applications collapse
    return re.sub(r'\s+',' ',b)
def run(loose):
    per=[]
    for x in t:
        L=x['body'].split('\n')
        # collect arms with (start,end,indent,parent-match-line)
        arms=[]
        for i,s in enumerate(L):
            st=s.lstrip()
            if st.startswith('|'):
                ind=len(s)-len(st); j=i+1
                while j<len(L) and (len(L[j])-len(L[j].lstrip()))>ind: j+=1
                arms.append((i,j,ind))
        covered=set(); saved=0
        # group siblings: consecutive arms at same indent with no line of smaller-or-equal indent non-arm in between
        groups=collections.defaultdict(list); gid=0; last=None
        for a in arms:
            i,j,ind=a
            if last and last[2]==ind and last[1]==i: groups[gid].append(a)
            else: gid+=1; groups[gid].append(a)
            last=a
        for g in sorted(groups.values(), key=lambda g:g[0][0]):
            if any(g[0][0] in r for r in covered): continue
            c=collections.defaultdict(list)
            for i,j,ind in g:
                st=L[i].lstrip(); rhs=st.split('=>',1)[1] if '=>' in st else ''
                c[norm(rhs+'\n'+'\n'.join(L[i+1:j]),loose)].append((i,j))
            for n,v in c.items():
                if len(v)>=2:
                    saved+=sum(j-i for i,j in v)-(v[0][1]-v[0][0])
                    for i,j in v: covered.add(range(i,j))
        if saved: per.append((saved,x['file'],x['name'],x['proof']))
    per.sort(reverse=True)
    return per
for loose in (False,True):
    p=run(loose); print('loose' if loose else 'strict', sum(a[0] for a in p), len(p))
    if loose:
        for a in p[:12]: print(a)
