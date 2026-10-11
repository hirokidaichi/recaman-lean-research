import json
A='AAASSSASASA'; S='SASASAASAAAASSSASAS'
def stats(w):
 m=M=q=0; hits=[]
 for i,b in enumerate(w,1):
  v=1 if b=='A' else -1; m+=v; M+=i*v
  q+=i>1 and w[i-2:i]=='SS'
  if (m,M)==(1,0): hits.append(i)
 return {'length':len(w),'mass':m,'moment':M,'ss':q,'p2_prefixes':hits}
e={i:b for i,b in enumerate(S[::-1])};e[-1]='A';e[19]='A'
p=''.join(e[i] for i in range(16))
print(json.dumps({'A':stats(A),'S':stats(S),'C':stats(A[:-1]),'X':stats(S[:-10]),'period16':p,'period_mass':p.count('A')-p.count('S'),'compatible':all(p[i%16]==b for i,b in e.items()),'source_A':10,'source_S':19,'oldest':0},sort_keys=True))
