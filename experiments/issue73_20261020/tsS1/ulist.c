// list distinct u = x[k1,n) for prefix-H prefixes with d(n)=S0, last clock A; mark endables in u with uppercase/lowercase (a = endable A)
#include <stdio.h>
#include <stdlib.h>
int N,S0,s[128],F[129],G[129],E[128],dd[129];
int endab(int b){ if(s[b]<0) return 0; for(int t=b-3;t>=0;t-=4) if(F[b]==F[t]+1&&G[b]-G[t]==(b-t)*F[t]) return 1; return 0;}
void dfs(int n){
  if(n>0 && s[n-1]>0 && dd[n]==S0){ int k1=0; for(int k=0;k<=n;k++) if(dd[k]==0) k1=k;
     for(int k=k1;k<n;k++) putchar(s[k]<0?'S':(E[k]?'a':'A')); printf("\n"); }
  if(n==N) return;
  for(int v=-1;v<=1;v+=2){ s[n]=v; F[n+1]=F[n]+v; G[n+1]=G[n]+F[n+1]; E[n]=endab(n);
    int d=dd[n]+(v<0?1:0)-(E[n]?1:0); if(d<0) continue; dd[n+1]=d; dfs(n+1); }
}
int main(int c,char**v){N=atoi(v[1]); S0=atoi(v[2]); dfs(0); return 0;}
