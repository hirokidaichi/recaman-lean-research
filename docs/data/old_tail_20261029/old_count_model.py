"""Finite necessary model ONLY. Discovery mass1..3, reserved holdout mass4..5.
Frozen all run/target bands come from E438/E440. No actual full-old history existence claim.
"""
import sys,json,math,hashlib
from pathlib import Path
mode=sys.argv[1]
lo,hi=(1,3) if mode=='discovery' else (4,5)
assert mode in ('discovery','holdout')
atoms=((1,(True,)),(2,(False,True,True,True)),(4,(False,False,True,True,True,True,False,True,True,True)))
def words(c):
 if c==0:return [()]
 return [u+v for d,u in atoms if d<=c for v in words(c-d)]
def area(u):return sum((len(u)-k)*(1 if b else -1) for k,b in enumerate(u))
def second(h,M,m,i):
 q=i+M-m-1
 return i==2 or (1<=q<=h and (q+m)**2==2*m*M+1)
def sources(h,M,m,L,s,i):
 q=i+M+L-m-s-1;e=m+s+1-L-i;v=i+L-s-1
 return [n for n,p in [('lastS',i==2),('initialS',1<=q<=h and (q+m+s)**2==2*M*(m+s)+2*L*s+1),('firstA',1<=e<=M and 2*e*(m+s)+2*L*s==(m+s)**2-1),('middleS',1<=v<=m and (v+s)**2==2*L*s+1)] if p]
rows=[];hist={};survivors=[];strict=0;word_count=0
for C in range(lo,hi+1):
 for u in words(C):
  word_count+=1;D=area(u)
  for R in range(5,9):
   j=R-1
   for A in range(2*R+1,18):
    H=C+A-R
    if H>14:continue
    for M in range(1,A-1):
     for L in range(1,A-M):
      T=A-M-L
      for m in range(1,H):
       for s in range(1,H-m+1):
        h=H-m-s
        I=M*(m+s)+L*s
        if 2*D+C*(C-1)!=2*A*(A-2*R)-4*I:continue
        c2=[i for i in range(L) if second(h,M,m,i)]
        c3=[(i,sources(h,M,m,L,s,i)) for i in range(T) if sources(h,M,m,L,s,i)]
        # Check E442 necessary consequence. No initialS source on final band.
        assert all('initialS' not in src for i,src in c3 if i+j>=T)
        first=min(2,max(0,M-2));sec=min(L,len(c2)+1);third=min(T,len(c3)+(1 if T>j else 0))
        oldthird=min(T,len(c3)+1)
        if third<oldthird:strict+=1
        # Relaxed upper counts, also paid against true positive-prefix end bounds.
        maxsup=-1;best=None
        for b1 in range(first+1):
         for b2 in range(sec+1):
          for b3 in range(third+1):
           if h<1 or b1>=h or b1+b2>=h+m or b1+b2+b3>=H:continue
           if b1+b2+b3>maxsup:maxsup=b1+b2+b3;best=(b1,b2,b3)
        lb=A-maxsup if maxsup>=0 else A+1
        row={'C':C,'D':D,'u':''.join('A' if b else 'S' for b in u),'h':h,'M':M,'m':m,'L':L,'s':s,'T':T,'j':j,'A':A,'second':c2,'third':c3,'first_bound':first,'second_bound':sec,'third_bound':third,'free_lower':lb,'max_supply':best}
        rows.append(row)
        if lb<=j:survivors.append(row)
        key=(C,j,A);hist[str(key)]=hist.get(str(key),0)+1
out={'mode':mode,'scope':'finite necessary source/count model, no actual full-history existence or proof','target_mass_range':[lo,hi],'target_words':word_count,'candidate_rows':len(rows),'old_band_strict_count_improvements':strict,'count_survivors':len(survivors),'histogram':hist,'survivors':survivors,'all_rows':rows}
p=Path(__file__).parent/(mode+'-model.json');p.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k not in ('all_rows','survivors')}))
print('SURVIVORS',json.dumps(survivors[:8]))
