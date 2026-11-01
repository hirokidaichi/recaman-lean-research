"""Generate the transparent full Q graph and all closure checks."""
import hashlib
import json
from pathlib import Path

p=Path(__file__).parent
raw=(p/'q4-certificate.json').read_bytes();data=json.loads(raw)
assert data['graph_exhausted'] and data['minZ']>=1
lines=['/- Generated from q4-certificate.json; SHA256 '+hashlib.sha256(raw).hexdigest()+' -/',
       (p/'q_checker_prefix.txt').read_text(), 'def rowAt (i : Nat) : Row :=']
packed=[]
for row in data['rows']:
    root,w,ay=row['state'];code=1
    for c in w:code=code*2+(c=='A')
    value=code*32+ay*16+root
    edges=dict(row['edges'])
    children=[edges[tag]+1 if tag in edges else 0 for tag in ['S','A0','A1']]
    packed.append('('+','.join(map(str,[value]+children))+')')

def tree(lo,hi,indent):
    if hi-lo==1:return[indent+packed[lo]]
    mid=(lo+hi)//2
    return[indent+f'if i < {mid} then']+tree(lo,mid,indent+'  ')+[indent+'else']+tree(mid,hi,indent+'  ')

lines+=tree(0,len(packed),'  ')
lines+=['',f'def rows : Table := ⟨{len(packed)},rowAt⟩','']
chunks=[(lo,min(32,len(packed)-lo)) for lo in range(0,len(packed),32)]
for lo,count in chunks:
    lines+=['set_option maxHeartbeats 10000000 in',f'theorem rows_checked_{lo} : verifiedRange rows {lo} {count}=true := by decide','']
lines+=['theorem rows_verified : verified rows=true := by','  apply List.all_eq_true.mpr','  intro i hi',
        f'  have hbound : i < {len(packed)} := List.mem_range.mp hi']

def proof(parts,depth):
    indent='  '*depth
    if len(parts)==1:
        lo,count=parts[0]
        return[indent+f'exact verifiedRange_at rows {lo} {count} rows_checked_{lo} i (by omega) (by omega)']
    mid=len(parts)//2;boundary=parts[mid][0]
    left=proof(parts[:mid],depth+1);right=proof(parts[mid:],depth+1)
    left[0]=indent+'· '+left[0].lstrip();right[0]=indent+'· '+right[0].lstrip()
    return[indent+f'by_cases h{boundary} : i < {boundary}']+left+right

lines+=proof(chunks,1)
lines+=['','theorem initial_member (w : List Bool) (hw : w ∈ endpointWords) : Member rows ⟨w,w,0⟩ := by',
        '  simp only [endpointWords, Recaman.ThreeNonsuppliedData.endpointWords, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hw',
        '  rcases hw with '+ ' | '.join('h'+str(i) for i in range(16))]
for i in range(16):
    lines += [f'  · subst w; exact ⟨{i}, by decide, by decide⟩']
lines += ['','end Recaman.SixteenRootAreaData','']
out=Path('Recaman/SixteenRootAreaData.lean');out.write_text('\n'.join(lines))
print(json.dumps(dict(path=str(out),rows=len(packed),sha256=hashlib.sha256(out.read_bytes()).hexdigest())))
