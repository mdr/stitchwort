import sys,os,re,collections
root=sys.argv[1]
kinds=collections.Counter(); hyp=collections.Counter(); nthm=0; eqTrue=0; stmt_lines=0
binder=re.compile(r'\((\w[\w\' ]*): ([^()]*(?:\([^()]*\)[^()]*)*)\)')
perthm=[]
for dp,dn,fn in os.walk(root):
    if '/Tests' in dp: continue
    for f in fn:
        if not f.endswith('.sw'): continue
        L=open(os.path.join(dp,f)).read().split('\n')
        in_stmt=False; depth=0; cur=[]
        for l in L:
            s=l.strip()
            if not in_stmt:
                if s=='' : kinds['blank']+=1
                elif s.startswith('--|'): kinds['doc comment']+=1
                elif s.startswith('--'): kinds['comment']+=1
                elif l.startswith('import') or l.startswith('namespace') or (l.startswith('  ') and False): kinds['import/namespace']+=1
                if l.startswith('theorem '):
                    in_stmt=True; cur=[]
            if in_stmt:
                cur.append(s)
                if re.search(r':=\s*(--.*)?$',s) or ':= ' in s:
                    in_stmt=False; nthm+=1
                    text=' '.join(cur); text=text[:text.rfind(':=')]
                    bs=binder.findall(text)
                    hs=[(n,t.strip()) for n,t in bs]
                    perthm.append(len(hs))
                    for n,t in hs:
                        hyp[n.strip()+': '+t]+=1
                        if t.endswith('= True'): eqTrue+=1
                    stmt_lines+=len(cur)
print('theorems',nthm,'stmt lines',stmt_lines, kinds)
tot=sum(hyp.values()); print('binder groups',tot,'distinct',len(hyp),'ending = True',eqTrue)
rep=[(c,h) for h,c in hyp.items() if c>=20]
print('binders repeated >=20 times: kinds',len(rep),'occurrences',sum(c for c,h in rep))
for c,h in sorted(rep,reverse=True)[:45]: print(c,h[:110])
import statistics
print('binders per theorem median',statistics.median(perthm),'mean',sum(perthm)/len(perthm),'>=8:',sum(1 for p in perthm if p>=8))
