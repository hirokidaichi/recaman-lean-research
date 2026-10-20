// list equality cases e(k)=s(k)>=2 for walks from p=0 with no earlier equality point k'<k with s(k')>=1 and the first clock... 
#include <stdio.h>
#include <stdlib.h>
int n; int F[64]; long G[64]; char sg[64]; int isE[64];
void rec(int k, int e, int s, int hadEq){
  if(k>0 && e==s && s>=2 && !hadEq){ printf("k=%d e=s=%d  %.*s  ends:",k,s,k,sg); for(int i=0;i<k;i++) if(isE[i]) printf(" %d",i); printf("\n"); }
  int eqnow = (k>0 && e==s && s>=1);
  if(k==n) return;
  for(int a=0;a<2;a++){
    sg[k]=a?'A':'S'; F[k+1]=F[k]+(a?1:-1); G[k+1]=G[k]+F[k+1];
    int ne=e, ns=s; isE[k]=0;
    if(a){ for(int t=k-3;t>=0;t-=4) if(F[k]==F[t]+1 && G[k]-G[t]==(long)(k-t)*F[t]){ne++;isE[k]=1;break;} } else ns++;
    rec(k+1,ne,ns,hadEq||eqnow);
  }
}
int main(int c,char**v){n=atoi(v[1]);rec(0,0,0,0);}
