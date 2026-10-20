// Level Hall: for all prefixes and levels l: #E with F(b)=l+1  <=  #S clocks c with F(c)=l
#include <stdio.h>
#include <stdlib.h>
#define OFF 40
int n; int F[64]; long G[64]; char sg[64]; int dE[100]; // dE[l+OFF] = #S at l - #E at l
long bad=0; int shown=0; int minD=100;
void rec(int k){
  if(k==n) return;
  for(int a=0;a<2;a++){
    sg[k]=a?'A':'S'; F[k+1]=F[k]+(a?1:-1); G[k+1]=G[k]+F[k+1];
    int lev=-1000;
    if(a){ for(int t=k-3;t>=0;t-=4) if(F[k]==F[t]+1 && G[k]-G[t]==(long)(k-t)*F[t]){lev=F[k]-1;break;} }
    else lev=F[k];
    int delta = a? -1 : +1;
    if(lev>-1000){ dE[lev+OFF]+=delta; if(dE[lev+OFF]<0){bad++; if(shown<5){shown++;printf("BAD %.*s level %d\n",k+1,sg,lev);} } }
    if(!(a && dE[lev+OFF]<0)) rec(k+1);
    if(lev>-1000) dE[lev+OFF]-=delta;
  }
}
int main(int cc,char**v){n=atoi(v[1]);rec(0);printf("n=%d bad=%ld\n",n,bad);}
