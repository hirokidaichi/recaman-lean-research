import itertools
for L in (3,7,11):
  for w in itertools.product('AS',repeat=L):
    x=''.join(w)+'A'; F=[0]
    for c in x: F.append(F[-1]+(1 if c=='A' else -1))
    b=L
    if F[b]!=1 or sum(F[1:b+1])!=0: continue
    # minimal?
    if any(F[b]==F[t]+1 and sum(F[t+1:b+1])==(b-t)*F[t] for t in range(b-3,0,-4)): continue
    h=0; P=lambda u: sum(F[1:u+1])-h*u; v=P(b)
    clean=all(P(u)<v for u in range(1,b) if F[u]==h)
    if not clean: print(L,x,'UNCLEAN')
  print('done',L)
