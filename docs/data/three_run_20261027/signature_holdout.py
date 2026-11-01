from pathlib import Path
import json
P=Path(__file__).parent
A=('A','SAAA','SSAAAASAAA')
def summary(w):
 mass=area=0
 for c in w:mass+=1 if c=='A' else -1;area+=mass
 return mass,area

def direct(w,R):
 # Independent backwards-interval calculation: prepend c changes area by
 # mass(c)+area(suffix)+len(suffix)*mass(c).
 mass=area=length=0;sig=set()
 for c in reversed(w):
  sign=1 if c=='A' else -1
  area=sign+area+length*sign;mass+=sign;length+=1
  if 1<=mass<=R:sig.add((mass,area))
 return sig

def forward(atoms,R):
 state=set()
 for atom in atoms:
  d,e=summary(atom)
  state={(r+d,a+len(atom)*r+e) for r,a in state if r+d<=R}
  state|={summary(atom[t:]) for t in range(len(atom)) if 1<=summary(atom[t:])[0]<=R}
 return state
rng=2026102710;count=0;bad=[];lengths=[];checksum=0
for index in range(400):
 depth=32+index%24;seq=[]
 for k in range(depth):
  rng=(1664525*rng+1013904223)%(2**32);seq.append(A[(rng>>8)%3])
 seq[0]=A[2];seq[-1]=A[2]
 w=''.join(seq);lengths.append(len(w))
 for R in (5,7,11,19):
  got=forward(seq,R);want=direct(w,R);count+=1
  if got!=want:bad.append({'index':index,'R':R,'word':w,'got':sorted(got),'want':sorted(want)})
  checksum+=sum(r*1009+a for r,a in got)
  if bad:break
 if bad:break
out={'protocol':'JOINT_SIGNATURE_PROTOCOL.json','words':index+1,'comparisons':count,'word_length_range':[min(lengths),max(lengths)],'seed':2026102710,'checksum':checksum,'mismatches':bad,'complete_declared_domain':not bad,'scope':'independent actual suffix replay; no automaton completeness or C1 proof'}
(P/'signature-holdout.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out));assert not bad
