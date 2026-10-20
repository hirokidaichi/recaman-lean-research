// For equality cases (sigma(0)=S), list multiplicity of P2 windows: check each endable b has exactly one window with t>=0,
// and that it is the block window (lengths 3 or 7, i.e. t=b-3 or t=b-7 pattern-consistent)
#include <stdio.h>
#include <stdlib.h>
int n; int F[64]; long G[64]; char sg[64]; int E[64]; int nw[64]; int tw[64];
long eqc=0,multi=0,longw=0; int shown=0;
void rec(int k,int e,int s){
  if(k>0 && E[k-1] && e==s){ eqc++; for(int i=0;i<k;i++) if(E[i]){ if(nw[i]>1){multi++; if(shown<5){shown++;printf("MULTI %.*s b=%d\n",k,sg,i);}} if(i-tw[i]>7){longw++;} } }
  if(k==n) return;
  for(int a=0;a<2;a++){ 
    sg[k]=a?'A':'S'; F[k+1]=F[k]+(a?1:-1); G[k+1]=G[k]+F[k+1];
    E[k]=0; nw[k]=0; int ne=e,ns=s;
    if(a){ for(int t=k-3;t>=0;t-=4) if(F[k]==F[t]+1 && G[k]-G[t]==(long)(k-t)*F[t]){E[k]=1;nw[k]++;tw[k]=t;} } else ns++;
    if(E[k]) ne++;
    rec(k+1,ne,ns);
  }
}
int main(int c,char**v){n=atoi(v[1]);rec(0,0,0);printf("n=%d eq=%ld multiwindow-instances=%ld long(>7)=%ld\n",n,eqc,multi,longw);}
