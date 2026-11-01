import json
three=['AAA','SAAAA','ASAAA'];four=['AAAA','AASAAA','ASAAAA','SAAAAA','SAAASAAA','SSAAAASAAA']
def p(w):
 m=a=0
 for b in w:m+=1 if b=='A' else -1;a+=m
 return m,a
def independent(w):return sum((i+1)*(1 if x=='A' else -1) for i,x in enumerate(w[::-1]))
pairs=set();words=[]
for x in four:
 assert p(x)[0]==4 and p(x)[1]==independent(x)
 for y in three:
  assert p(y)[0]==3 and p(y)[1]==independent(y)
  assert (x.endswith(y) or y.endswith(x))==(x[::-1].startswith(y[::-1]) or y[::-1].startswith(x[::-1]))
  if x.endswith(y) or y.endswith(x):pairs.add((p(x)[1],p(y)[1]));words.append((x,y,p(x)[1],p(y)[1]))
expected={(10,6),(10,5),(13,7),(13,6),(11,5),(11,6),(9,6),(12,7),(12,6),(9,7)}
assert pairs==expected
kept={}
for a,b in sorted(pairs):
 Smod=a%2;delta=3+a-b;mod=(2*Smod+delta)%4
 kept[str((a,b))]={'S_mod2':Smod,'R_square_delta':delta,'R_square_mod4':mod,'survives':mod in (0,1)}
remain={p for p in pairs if kept[str(p)]['survives']}
assert remain=={(10,5),(13,6),(9,6),(12,7),(12,6)}
print(json.dumps({'scope':'finite audit of the paper pair/parity table only; not kernel or actual free proof; previously inspected words, no fresh holdout claim','word_pairs':words,'area_pairs':kept,'remaining':sorted(remain)},sort_keys=True))
