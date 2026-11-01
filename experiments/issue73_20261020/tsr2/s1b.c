// prefixes with prefix-H (p=0), last clock A, slack s<=SM; starts t with D=i>=1, Q=-(2i+1). print x (a=endable A), k1, t
#include <stdio.h>
#include <stdlib.h>
int N,SM,s[128],F[129],G[129],E[128],dd[129];
int endab(int b){ if(s[b]<0) return 0; for(int t=b-3;t>=0;t-=4) if(F[b]==F[t]+1&&G[b]-G[t]==(b-t)*F[t]) return 1; return 0;}
void node(int n){ int d=dd[n]; if(s[n-1]<0||d>SM) return; int k1=0; for(int k=0;k<=n;k++) if(dd[k]==0) k1=k;
  for(int t=0;t<n;t++){ int D=F[n]-F[t]; if(D<1) continue; long Q=G[n]-G[t]-(long)(n-t)*F[t]+(long)D*(D-1)/2;
    if(Q==-(2*D+1)){ printf("s=%d i=%d t-k1=%d u=",d,D,t-k1); for(int k=k1;k<n;k++) putchar(s[k]<0?'S':(E[k]?'a':'A')); printf(" x="); for(int k=0;k<n;k++){ if(k==t) putchar('['); if(k==k1) putchar('|'); putchar(s[k]<0?'S':(E[k]?'a':'A'));} printf("\n"); } } }
void dfs(int n){ if(n>0) node(n); if(n==N) return;
  for(int v=-1;v<=1;v+=2){ s[n]=v; F[n+1]=F[n]+v; G[n+1]=G[n]+F[n+1]; E[n]=endab(n);
    int d=dd[n]+(v<0?1:0)-(E[n]?1:0); if(d<0) continue; dd[n+1]=d; dfs(n+1); } }
int main(int c,char**v){N=atoi(v[1]); SM=atoi(v[2]); dfs(0); return 0;}
