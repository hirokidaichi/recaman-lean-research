import itertools,json,sys
from pathlib import Path
def hb(w):
 H=[0];B=[0]
 for c in w:H.append(H[-1]+(1 if c=='A' else -1));B.append(B[-1]+H[-1])
 return H,B
Z='ASSSSAAA';rows=[]
for positions in itertools.combinations(range(1,8),3):
 w=''.join('A'if i==0 or i in positions else'S'for i in range(8));H,B=hb(w);rows.append({'word':w,'area':B[-1]})
assert min(r['area']for r in rows)==-8
assert [r['word']for r in rows if r['area']==-8]==[Z]
w='SSAA'+Z*2+'A';H,B=hb(w);src=[];F=[];E=S=0;delta=[]
for q,c in enumerate(w):
 ss=[u for u in range(q)if H[q]==H[u]+1 and B[q]-B[u]==(q-u)*H[u]]if c=='A'else[];src.append(ss)
 if c=='S':S+=1
 elif ss:E+=1
 else:F.append(q)
 delta.append(S-E)
assert min(delta)>=1
assert all(src[q]==[1]for q in[4,12,20])
assert H[7]==H[15]==-1 and B[15]-B[7]==8*H[7]
b=10000;x=10000000;X=[x+(b+i+1)*H[i]-B[i]for i in range(len(H))]
assert X[7]==X[15]and w[6]==w[14]=='S'
out={'balanced8_startA':rows,'unique_minimum_word':Z,'raw_positive_counter':{'word':w,'sources':src,'deficits':delta,'free':F,'hits':[4,12,20],'source':1,'raw_span':16,'proposed_greedy_span_lower':20,'S_landing_collision':[7,15],'same_value':X[7],'clock':b,'current':x},'scope':'fixed structural counterfactuals, no finite absence/C1 claim'}
Path(sys.argv[1]).write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items()if k!='balanced8_startA'}))
