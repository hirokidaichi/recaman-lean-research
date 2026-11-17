from pathlib import Path
import ast,json,sys,hashlib
P=Path(__file__).resolve().parent
tree=ast.parse((P/'two_level_balance.py').read_text())
exec(compile(ast.Module(body=[x for x in tree.body if isinstance(x,ast.FunctionDef)],type_ignores=[]),'frozen-two-level-checkers','exec'))
mode=sys.argv[1];rows=[]
for N in ([1,2] if mode=='discovery' else [3,7]):
 w='SSAAASSSSAAAASAS'*N+'A';H,B,src,free,positive=forward(w)
 assert positive and min(H)==-3 and max(H)==1 and H[-1]==1
 for q,c in enumerate(w):
  if c=='A':assert src[q]==reverse(w,q)
 for j in range(N):
  for q,u in [(4,1),(11,8),(12,1),(14,7)]:assert 16*j+u in src[16*j+q]
 V0=sum(h==0 for h in H[:-1]);Vm2=sum(h==-2 for h in H[:-1])
 F0=sum(H[q]<=0 for q in free);band=sum(-2<H[q]<=0 for q in free)
 assert V0==5*N+1 and Vm2==3*N and F0<=4*N+1 and band<=N+1
 assert V0-F0>=N and V0-Vm2-band>=N
 rows.append({'N':N,'length':len(w),'height_band':[min(H),max(H)],'positive':positive,'V0':V0,'Vminus2':Vm2,'F_le0':F0,'F_band':band,'whole_error':V0-F0,'recurrence_error':V0-Vm2-band,'all_A_reverse_checked':True,'word_sha256':hashlib.sha256(w.encode()).hexdigest()})
(P/('two-level-family-'+mode+'-summary.json')).write_text(json.dumps({'mode':mode,'rows':rows},indent=2)+'\n');print(json.dumps(rows))
