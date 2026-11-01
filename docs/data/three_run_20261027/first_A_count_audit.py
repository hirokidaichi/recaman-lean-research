from pathlib import Path
import json
P=Path(__file__).parent
out={'protocol':'FIRST_A_COUNT_AUDIT_PROTOCOL.json','tuples_examined':0,'witnesses':[],'complete_declared_domain':False,'claim_attacked':'existing necessary count inequalities plus first-A source square identity imply no source','not_attacked':'actual first-A source exclusion, parent free-gap or C1'}
stop=False
for M in range(1,21):
 if stop:break
 for L in range(21-M):
  if stop:break
  for T in range(21-M-L):
   if stop:break
   A=M+L+T
   for R in range(5,11):
    if stop:break
    for d in range(1,M+1):
     if stop:break
     U=L+T;v=U*(U-2*R)-d*d
     if v<0:continue
     if L==0:
      if v:continue
      candidates=range(39)
     elif v%(2*L)==0:candidates=[v//(2*L)]
     else:continue
     for s in candidates:
      m=d+U-R-s
      if not(0<=m<39 and 0<=s<39):continue
      for a1 in range(min(M,2),M+1):
       if M>2*a1 or M-a1>2:continue
       for a2 in range(max(0,L-3),L+1):
        if M+L>2*(a1+a2)+1:continue
        for a3 in range(max(0,T-6),T+1):
         out['tuples_examined']+=1;r=a1+a2+a3
         if 4<=r<R and A-r<=11:
          out['witnesses'].append({'M':M,'L':L,'T':T,'R':R,'d':d,'s':s,'m':m,'free_counts':[a1,a2,a3],'free':r,'total_A':A})
          if len(out['witnesses'])==5:stop=True;break
        if stop:break
       if stop:break
      if stop:break
out['complete_declared_domain']=not stop
out['status']='count-bound-only elimination REFUTED by numeric tuple; actual model unresolved' if out['witnesses'] else 'finite necessary system UNSAT; not a C1 proof'
(P/'first-A-count-audit.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
