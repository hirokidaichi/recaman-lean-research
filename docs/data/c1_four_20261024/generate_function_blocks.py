"""Serialize the frozen event graph; every decoded child is checked by the kernel."""
import argparse,hashlib,json
from pathlib import Path
base=Path(__file__).parent
ap=argparse.ArgumentParser();ap.add_argument('--bench',action='store_true');args=ap.parse_args()
data=json.loads((base/'macro-certificate.json').read_text());ind=json.loads((base/'macro-independent.json').read_text())
assert data['graph_exhausted'] and data['highest_A']==10 and ind['all_states_and_edges_match']
assert data['states']<16384
rows=[]
for row in data['rows']:
 w,a,s,r=row['state'];code=1
 for c in w:code=2*code+(c=='A')
 assert len(w)<=29 and a<16 and s<32 and r<8
 packed=4096*code+512*r+16*s+a
 edges=sum((0 if target is None else target+1)<<(14*i) for i,target in enumerate(row['edges']))
 rows.append(f'({packed}, {edges})')
def tree(lo,hi,depth):
 indent='  '*depth
 if hi-lo==1:return [indent+rows[lo]]
 mid=(lo+hi)//2
 return [indent+f'if i < {mid} then']+tree(lo,mid,depth+1)+[indent+'else']+tree(mid,hi,depth+1)
# Small transparent constants keep the kernel from duplicating one13k-row expression.
parts=[(lo,min(lo+64,len(rows))) for lo in range(0,len(rows),64)]
header=[]
for lo,hi in parts:
 header+=['set_option maxHeartbeats 1000000 in',f'noncomputable def rowBlock_{lo} (i : Nat) : Row :=']+tree(lo,hi,1)+['']
def select(parts,depth):
 indent='  '*depth
 if len(parts)==1:return [indent+f'rowBlock_{parts[0][0]} i']
 mid=len(parts)//2;cut=parts[mid][0]
 return [indent+f'if i < {cut} then']+select(parts[:mid],depth+1)+[indent+'else']+select(parts[mid:],depth+1)
header+=['noncomputable def rowAt (i : Nat) : Row :=']+select(parts,1)+['',f'noncomputable def rows : Table := ⟨{len(rows)},rowAt⟩','']

if args.bench:
 lines=['import Recaman.FourNonsuppliedData','namespace Recaman.FourNonsuppliedBench','open Recaman.FourNonsuppliedData']+header
 for i in [0,3200,6400,9600,12836]:
  lines+=['set_option maxHeartbeats 20000000 in',f'theorem checked_{i} : checkOne rows {i}=true := by decide',f'#check checked_{i}','']
 lines+=['end Recaman.FourNonsuppliedBench']
 out=base/'bench_four.lean'
else:
 lines=[f'/- Generated transparent certificate SHA256 {hashlib.sha256((base/"macro-certificate.json").read_bytes()).hexdigest()}. -/',(base/'checker_prefix.txt').read_text(),(base/'checker_suffix.txt').read_text()]+header
 lines+=['set_option profiler true','set_option profiler.threshold 50']
 chunks=[(lo,min(8,len(rows)-lo)) for lo in range(0,len(rows),8)]
 for lo,count in chunks:
  lines+=['set_option maxHeartbeats 50000000 in',f'theorem rows_checked_{lo} : verifiedRange rows {lo} {count}=true := by decide']
  if lo%256==0:lines+=[f'#check rows_checked_{lo}']
  lines+=['']
 lines+=['theorem rows_verified : verified rows=true := by','  apply List.all_eq_true.mpr','  intro i hi',f'  have hbound : i < {len(rows)} := List.mem_range.mp hi']
 def blocks(parts,depth):
  indent='  '*depth
  if len(parts)==1:
   lo,count=parts[0];return [indent+f'exact verifiedRange_at rows {lo} {count} rows_checked_{lo} i (by omega) (by omega)']
  mid=len(parts)//2;cut=parts[mid][0];left=blocks(parts[:mid],depth+1);right=blocks(parts[mid:],depth+1)
  left[0]=indent+'· '+left[0].lstrip();right[0]=indent+'· '+right[0].lstrip()
  return [indent+f'by_cases h{cut} : i < {cut}']+left+right
 lines+=blocks(chunks,1)
 lines+=['','theorem initial_member : Member rows ⟨[],0,0,0⟩ := by','  exact ⟨0,by decide,by decide⟩','','end Recaman.FourNonsuppliedData']
 out=Path('Recaman/FourNonsuppliedData.lean')
out.write_text('\n'.join(lines)+'\n');print(json.dumps(dict(file=str(out),bytes=out.stat().st_size,rows=len(rows),sha256=hashlib.sha256(out.read_bytes()).hexdigest())))
