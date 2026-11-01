// all x of length n=4m+4 with [0,n-2] a P2 window of n-1: report min slack = #S - #endables-from-0 in [0,n-1]
#include <stdio.h>
#include <stdlib.h>
int main(int argc,char**argv){ int n=atoi(argv[1]); int L=n-1; int F[64]; long G[64]; int minsl=99; long cnt=0,tight=0;
  for(long msk=0; msk<(1L<<L); msk++){ F[0]=0;G[0]=0;
    for(int i=0;i<L;i++){F[i+1]=F[i]+((msk>>i)&1?1:-1); G[i+1]=G[i]+F[i+1];}
    if(F[L]!=1 || G[L]!=0) continue; cnt++;
    int s=0,e=1; // L endable
    for(int b=0;b<L;b++){ if(!((msk>>b)&1)){s++;continue;} int h=F[b]-1;
      for(int t=b-3;t>=0;t-=4) if(F[t]==h && G[b]-G[t]==(long)(b-t)*h){e++;break;} }
    int sl=s-e; if(sl<minsl) minsl=sl; if(sl<=0) tight++; }
  printf("n=%d windows=%ld minslack=%d tight=%ld\n",n,cnt,minsl,tight); }
