// verify: for every string (p=0), every k, every level h:
//  #{b<k : sigma(b)=A, exists t, [t,b-1] P2, F(t)=h, min_{[t,b]}F >= h-1} <= #{s<k-1... dips: sigma(s)=S, F(s)=h, sigma(s+1)=A, s+1<=k-1}
#include <stdio.h>
#include <stdlib.h>
int n; int F[80]; long G[80]; char sg[80]; int cntE[200], cntD[200]; long viol=0, checked=0; int OFF=100;
void rec(int k){ // clocks 0..k-1 decided
  if(k==n) return;
  for(int a=0;a<2;a++){
    sg[k]=a?'A':'S'; F[k+1]=F[k]+(a?1:-1); G[k+1]=G[k]+F[k+1];
    int eh=-999, dh=-999; if(!a) dh=F[k];
    if(a){ for(int t=k-3;t>=0;t-=4){ int h=F[t]; if(F[k]!=h+1||G[k]-G[t]!=(long)(k-t)*h) continue; int lo=1,hi=1; for(int u=t;u<=k;u++){ if(F[u]<h-1) lo=0; if(F[u]>h+1) hi=0;} int ok=(MODE==0?(lo||hi):MODE==1?lo:hi); if(ok){eh=h;break;} }
        }
    if(eh!=-999) cntE[eh+OFF]++; if(dh!=-999) cntD[dh+OFF]++;
    for(int h=0;h<200;h++){ if(cntE[h]>cntD[h]) viol++; } checked++;
    rec(k+1);
    if(eh!=-999) cntE[eh+OFF]--; if(dh!=-999) cntD[dh+OFF]--;
  }
}
int main(int c,char**v){n=atoi(v[1]);rec(0);printf("n=%d prefixes=%ld violations=%ld\n",n,checked,viol);}
