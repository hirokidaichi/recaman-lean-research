import itertools
exec(open('verify.py').read().split('for w in sys.argv')[0])
res=[]
for m in range(0,6):
  for k in range(1,8):
    for pre in ["SSAAA","SAAA","SSSAAA",""]:
     for mid in ["SSAAA","SSSAAA","SAAA",""]:
      for tail in ["AA","A","AAA","SAA",""]:
        w=pre+"SSSAAA"*m+mid+"SA"*k+tail
        run,out,st=analyze(w)
        if run: 
          r,q,sl=out[0]; res.append((r,sl,w))
best={}
for r,sl,w in res:
    if r not in best or sl<best[r][0]: best[r]=(sl,w)
for r in sorted(best): print(r,best[r])
