// Claim L: at q (last clock A, prefix-H from 0), any t with D=i>=1, Q=-(2i+1): min of d(q)-d(t) per i; also with t<k1 flag
#include <stdio.h>
#include <stdlib.h>
int N,s[128],F[129],G[129],E[128],dd[129]; int mn[40],mnb[40];
int endab(int b){ if(s[b]<0) return 0; for(int t=b-3;t>=0;t-=4) if(F[b]==F[t]+1&&G[b]-G[t]==(b-t)*F[t]) return 1; return 0;}
void node(int n){ if(s[n-1]<0) return; int k1=0; for(int k=0;k<=n;k++) if(dd[k]==0) k1=k;
  for(int t=0;t<n;t++){ int D=F[n]-F[t]; if(D<1||D>=40) continue; long Q=G[n]-G[t]-(long)(n-t)*F[t]+(long)D*(D-1)/2;
    if(Q==-(2*D+1)){ int v=dd[n]-dd[t]; if(v<mn[D]){mn[D]=v; printf("i=%d d(q)-d(t)=%d t-k1=%d x=",D,v,t-k1); for(int k=0;k<n;k++){if(k==t)putchar('[');putchar(s[k]<0?'S':(E[k]?'a':'A'));} printf("\n");}
      if(t<k1 && dd[n]<mnb[D]) mnb[D]=dd[n]; } } }
void dfs(int n){ if(n>0) node(n); if(n==N) return;
  for(int v=-1;v<=1;v+=2){ s[n]=v; F[n+1]=F[n]+v; G[n+1]=G[n]+F[n+1]; E[n]=endab(n);
    int d=dd[n]+(v<0?1:0)-(E[n]?1:0); if(d<0) continue; dd[n+1]=d; dfs(n+1); } }
int main(int c,char**v){N=atoi(v[1]); for(int a=0;a<40;a++){mn[a]=99;mnb[a]=99;} dfs(0);
 for(int a=1;a<10;a++) printf("i=%d min d(q)-d(t)=%d  min slack with t<k1=%d\n",a,mn[a],mnb[a]); return 0;}
