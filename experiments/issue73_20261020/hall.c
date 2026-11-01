// Conjecture H check: for every sigma on [0,n), for every k<=n:
//  e(k) = #{A-clocks b < k : exists t>=0, [t,b-1] P2 window}  <=  s(k) = #S in [0,k-1]
// (b is a clock; condition uses F(b) and clock b itself must be A, so b<k means clock b in [0,k-1])
#include <stdio.h>
#include <stdlib.h>
int n; int F[64]; long G[64]; char sg[64];
long cnt=0; int maxD=-100; int worst=0;
void rec(int k, int e, int s){ // clocks 0..k-1 decided, F[0..k], G[0..k]
  int D=e-s; if(D>maxD){maxD=D; printf("new maxD=%d at k=%d: ",D,k); for(int i=0;i<k;i++)putchar(sg[i]); printf("\n"); fflush(stdout);}
  if(k==n){cnt++;return;}
  for(int a=0;a<2;a++){ // a=1:A
    sg[k]=a?'A':'S'; F[k+1]=F[k]+(a?1:-1); G[k+1]=G[k]+F[k+1];
    int ne=e, ns=s;
    if(a){ // clock k is A: is it a P2 end? need t with F(k)=F(t)+1, G(k)-G(t)=(k-t)F(t), k-t>=3
      for(int t=k-3;t>=0;t-=4){ if(F[k]==F[t]+1 && G[k]-G[t]==(long)(k-t)*F[t]){ne++;break;} }
    } else ns++;
    rec(k+1,ne,ns);
  }
}
int main(int c,char**v){n=atoi(v[1]);F[0]=0;G[0]=0;rec(0,0,0);printf("n=%d strings=%ld maxD=%d\n",n,cnt,maxD);}
