# Check the two density facts used in the paper reduction:
# (D1) for a block word w in (SAAA|SSAAAASAAA|A)*, j>=0: the last clock of w A^j A is never endable (from 0).
# (D2) for w block word, i,j>=0: last clock of w A^i S A^j A endable  => j==2 and minimal window = SAA.
import itertools,sys
def endwins(s,b):
    F=[0]
    for ch in s: F.append(F[-1]+(1 if ch=='A' else -1))
    out=[]
    for t in range(b-3,-1,-4):
        h=F[t]
        if s[b]=='A' and F[b]==h+1 and sum(F[u]-h for u in range(t+1,b+1))==0: out.append(t)
    return out
N=int(sys.argv[1])
blocks=['SAAA','SSAAAASAAA','A']
words={''}
frontier={''}
while frontier:
    new=set()
    for w in frontier:
        for B in blocks:
            if len(w)+len(B)<=N and w+B not in words: new.add(w+B)
    words|=new; frontier=new
print("block words up to",N,":",len(words))
bad1=0;bad2=[]
for w in words:
    for j in range(0,4):
        s=w+'A'*j+'A'
        if endwins(s,len(s)-1): bad1+=1
        for i in range(0,3):
            s=w+'A'*i+'S'+'A'*j+'A'
            ws=endwins(s,len(s)-1)
            if ws and not (j==2 and ws[0]==len(s)-4): bad2.append(s)
print("D1 violations",bad1,"D2 violations",len(bad2),bad2[:5])
