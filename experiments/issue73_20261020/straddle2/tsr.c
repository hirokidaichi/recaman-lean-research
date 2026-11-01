// TS_r: last clock n-1 endable; take the last r A-clocks b_1<...<b_r=n-1 (consecutive A's), all endable from 0;
// q* = start of S-run before b_1. min slack(0,q*) as function of r.
#include <stdio.h>
#include <stdlib.h>
int main(int c,char**v){int n=atoi(v[1]); int mins[6]={99,99,99,99,99,99}; long cnt[6]={0};
 for(long m=0;m<(1L<<(n-1));m++){ int s[64],F[65],G[65];
  for(int i=0;i<n-1;i++) s[i]=((m>>i)&1)?1:-1; s[n-1]=1; F[0]=G[0]=0; for(int i=0;i<n;i++){F[i+1]=F[i]+s[i];G[i+1]=G[i]+F[i+1];}
  #define END(b) ({int r_=0; for(int t=(b)-3;t>=0;t-=4) if(F[b]==F[t]+1&&G[b]-G[t]==((b)-t)*F[t]){r_=1;break;} r_;})
  int b=n-1; int r=0;
  while(r<5){ if(b<0||!END(b)) break; r++; int qs=b; while(qs>0&&s[qs-1]<0) qs--;
    int d=0; for(int u=0;u<qs;u++){ if(s[u]<0)d++; else if(END(u)) d--; }
    cnt[r]++; if(d<mins[r]) mins[r]=d;
    b=qs-1; }
 }
 printf("n=%d:",n); for(int r=1;r<=5;r++) printf(" r=%d: cnt=%ld min=%d;",r,cnt[r],mins[r]); printf("\n");}
