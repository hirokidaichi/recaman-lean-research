"""Actual-State attack on the filled-prefix/source consumer; old stock never dropped."""
import json,sys
from pathlib import Path
cfg=json.loads(Path(sys.argv[1]).read_text());rows=[];excluded=0;checked=0
for label,cases in [('discovery',cfg['discovery']),('unused_parameter_controls',cfg['parameter_controls'])]:
 for M,x,b in cases:
  seen=set(range(M))|{x};cur=x;X=[x];H=[0];B=[0];w='';stocks=[sorted(seen)]
  for q in range(cfg['length']):
   n=b+q+1;cand=cur-n;A=cand<=0 or cand in seen;w+='A'if A else'S'
   cur=cur+n if A else cand;seen.add(cur);X.append(cur);H.append(H[-1]+(1 if A else-1));B.append(B[-1]+H[-1]);stocks.append(sorted(seen))
  c=0 if x>=M else max(0,M-b-1)+1
  assert b+c>=M or c==0
  assert X[c]>=M and min(X[c:])>=M
  y=X[c]-M+1;a=b+c;D=0
  while a*(D+1)+(D+1)*(D+2)//2<y:D+=1
  oldmax=max(H[:c],default=None)
  j=max(1,oldmax+2-H[c]+D)if c else 1
  P=a+2*y;bound=3**(j-1)*P-(3**(j-1)-1)//2;cut=c+bound-a-1
  for q,ch in enumerate(w):
   if ch!='A':continue
   sources=[u for u in range(q)if H[q]==H[u]+1 and B[q]-B[u]==(q-u)*H[u]]
   if c and q>=cut:
    checked+=1;assert all(u>=c for u in sources),(M,x,b,c,q,sources,cut)
    excluded+=c
  rows.append(dict(label=label,M=M,x=x,b=b,word=w,original_cut=c,residual_y=y,triangular_D=D,old_source_height_max=oldmax,raising_index=j,old_source_cutoff=cut,full_values=X,full_original_H=H,full_initial_stock=stocks[0]))
assert checked>0
out=dict(PASS=True,rows=rows,nonvacuous_late_A_checks=checked,old_source_positions_excluded=excluded,scope='NEW actual filled-stock consumer, original sources before cut kept; no non-P2/new-source elimination')
Path(sys.argv[2]).write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(dict(PASS=True,cases=len(rows),nonvacuous_late_A_checks=checked,old_source_positions_excluded=excluded)))
