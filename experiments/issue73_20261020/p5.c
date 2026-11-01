// For every string of length n: fix clean b -> t*_b; then greedy (by b increasing, earliest free S in [t*_b,b-1]) for unclean b.
// MODE 1: unclean may use any window start (all P2 starts give nested windows; minimal one is smallest -> same as t*)
#include <stdio.h>
#include <stdlib.h>
int n; int F[64]; long G[64]; char sg[64]; int ts[64], cl[64];
long strings,fail; int sh;
long P(int h,int u){return G[u]-(long)h*u;}
void check(){
  int used[64]={0};
  for(int b=0;b<n;b++) if(ts[b]>=0 && cl[b]) used[ts[b]]=1;
  for(int b=0;b<n;b++) if(ts[b]>=0 && !cl[b]){ int c; for(c=ts[b];c<b;c++) if(sg[c]=='S'&&!used[c]) break;
     if(c==b){ fail++; if(sh<10){sh++; printf("FAIL %.*s b=%d t*=%d\n",n,sg,b,ts[b]);} return;} used[c]=1; }
}
void rec(int k){
  if(k==n){strings++; check(); return;}
  for(int a=0;a<2;a++){
    sg[k]=a?'A':'S'; F[k+1]=F[k]+(a?1:-1); G[k+1]=G[k]+F[k+1];
    int t=-1;
    if(a){ for(int tt=k-3;tt>=0;tt-=4) if(F[k]==F[tt]+1 && G[k]-G[tt]==(long)(k-tt)*F[tt]){t=tt;break;} }
    ts[k]=t; cl[k]=1;
    if(t>=0){ int h=F[t]; long v=P(h,k); for(int u=t+1;u<k;u++) if(F[u]==h && P(h,u)>v) cl[k]=0; }
    rec(k+1);
  }
}
int main(int c,char**v){n=atoi(v[1]);rec(0);printf("n=%d strings=%ld fail=%ld\n",n,strings,fail);}
