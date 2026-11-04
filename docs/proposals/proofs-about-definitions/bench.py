# Writes a parser of N steps (nat, then char, alternately) and its proof in
# the shape of Day 2's readsLine, for proofs-about-definitions.md §1:
#   python3 bench.py 8 copy  > c8.sw   # the parser's body copied as `j`
#   python3 bench.py 8 under > u8.sw   # `_` for every `j` (fails today)
#   STITCHWORT_TIMINGS=decls stitchwort check c8.sw   # the `steps` column
import sys
# n steps: alternating nat() and char '-', starting with nat; gives a record of the nats.
def steps(n):
    out=[]
    for i in range(n):
        out.append(('nat', f'x{i}') if i%2==0 else ('char', f'u{i}'))
    return out

def body_lines(st, indent, nats=None):
    lines=[]
    for kind,v in st:
        if kind=='nat': lines.append(f'{indent}let {v} := Parse.nat()')
        else: lines.append(f"{indent}Parse.char '-'")
    nats=nats or [v for k,v in st if k=='nat']
    lines.append(f'{indent}{{ {", ".join(f"f{v} = {v}" for v in nats)} }}')
    return lines

def proof_chain(st, i, indent, copy_j):
    kind,v=st[i]
    lemma = 'Parse.readsNat' if kind=='nat' else "(Parse.readsChar '-')"
    p = 'Parse.nat' if kind=='nat' else "(() => Parse.char '-')"
    nats=[x for k,x in st if k=='nat']
    if i==len(st)-1:
        rest='Parse.readsPure { ' + ', '.join(f'f{v} = {v}' for v in nats) + ' }'
    else:
        rest=proof_chain(st,i+1,indent+'  ',copy_j)
    if copy_j=='copy' and i==0:
        j='(' + v + ' =>\n' + '\n'.join(body_lines(st[1:], indent+'    ', nats)) + ')'
        return f'Parse.readsBind {p} {j} _ _ {lemma} ({v} =>\n{indent}  {rest})'
    return f'Parse.readsBind _ _ _ _ {lemma} ({v} =>\n{indent}  {rest})'

def file(n, copy_j):
    st=steps(n)
    nats=[v for k,v in st if k=='nat']
    out=['import Std (Parse)','','type R = { ' + ', '.join(f'f{v}: Nat' for v in nats) + ' }','',f'def p{n}(): {{Parse}} R :=']+body_lines(st,'  ')
    out+=['',f'theorem reads{n}: Parse.Reads p{n} (read value => read = read) :=',
          f'  Parse.readsWeaken p{n} _ _',
          '    ('+proof_chain(st,0,'    ',copy_j)+')',
          '    (read value h => rfl)','']
    return '\n'.join(out)

n=int(sys.argv[1]); mode=sys.argv[2] if len(sys.argv)>2 else 'copy'
print(file(n,mode))
