import sys,os,re,collections,json
root=sys.argv[1]; t=[x for x in json.load(open(sys.argv[2])) if '/Tests/' not in x['file']]
w=[x for x in t if 'byWalking' in x['body']]
print('walk theorems',len(w),'proof',sum(x['proof'] for x in w),'stmt',sum(x['stmt'] for x in w))
one=[x for x in t if x['proof']==1]
print('one-line-proof theorems',len(one),'their stmt lines',sum(x['stmt'] for x in one))
long=[x for x in t if x['proof']>15]
# per-file repeated own-line binders in statements; docs
own=0; ownrep=0; docd=0; idea=0; nlong=0; suffix1=collections.Counter(); bylen=collections.Counter()
for dp,dn,fn in os.walk(root):
    if '/Tests' in dp: continue
    for f in fn:
        if not f.endswith('.sw'): continue
        L=open(os.path.join(dp,f)).read().split('\n')
        for m in re.finditer(r'\b([A-Za-z][A-Za-z]*[a-z])1\b', '\n'.join(L)): suffix1[m.group(0)]+=1
        c=collections.Counter(); 
        i=0
        stm=[]
        while i<len(L):
            if L[i].startswith('theorem '):
                if i>0 and L[i-1].startswith('--|'): docd+=1
                j=i; 
                while j<len(L) and ':=' not in L[j]: j+=1
                for k in range(i+1,j+1):
                    s=L[k].strip() if k<len(L) else ''
                    if re.match(r'^\([\w\' ]+: [^()]*(\([^()]*\)[^()]*)*\):?$',s): c[s.rstrip(':')]+=1; own+=1
                # proof length & idea
                k=j+1; n=0
                while k<len(L) and (L[k].startswith(' ') or L[k].strip()==''):
                    if L[k].strip(): n+=1
                    k+=1
                if n>15:
                    nlong+=1
                    d=i-1; txt=''
                    while d>=0 and L[d].startswith('--|'): txt+=L[d]; d-=1
                    if 'Proof idea' in txt or 'proof idea' in txt: idea+=1
                i=j
            i+=1
        ownrep+=sum(v-1 for v in c.values() if v>=5)
print('statement lines that are one binder alone:',own,'; repeats beyond the first, of binders written >=5 times in one file:',ownrep)
print('theorems with a doc comment',docd,'of',len(t),'; proofs over 15 lines',nlong,'with a proof idea',idea)
print('identifiers ending in 1: distinct',len(suffix1),'uses',sum(suffix1.values()),suffix1.most_common(12))
