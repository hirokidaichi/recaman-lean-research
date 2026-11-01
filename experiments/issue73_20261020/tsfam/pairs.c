// DFS over prefix-H strings x=sigma[0,n) (d(k)>=0 all k). At each node with d<=2, collect states (D,Q) of starts t<n
// with |D|<=DM, |Q|<=QM. Record min d over occurrences of each unordered pair, split by last clock (A/S).
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define DM 6
#define QM 16
#define ND (2*DM+1)
#define NQ (2*QM+1)
#define NS (ND*NQ)
int N,s[128],F[129],G[129],E[128],dd[129];
unsigned char mn[2][NS][NS]; unsigned char mn1[2][NS];
int endab(int b){ if(s[b]<0) return 0; for(int t=b-3;t>=0;t-=4) if(F[b]==F[t]+1&&G[b]-G[t]==(b-t)*F[t]) return 1; return 0;}
void node(int n){ int d=dd[n]; if(d>2) return; int last=s[n-1]>0; int st[130],m=0; static char seen[NS]; 
  for(int t=0;t<n;t++){ int D=F[n]-F[t]; if(D<-DM||D>DM) continue; long Q=G[n]-G[t]-(long)(n-t)*F[t]+(long)D*(D-1)/2; if(Q<-QM||Q>QM) continue;
    int id=(D+DM)*NQ+(Q+QM); if(seen[id]==2) continue; seen[id]++; st[m++]=id; }
  for(int a=0;a<m;a++){ if(d<mn1[last][st[a]]) mn1[last][st[a]]=d; for(int b=0;b<m;b++){ if(a==b && seen[st[a]]<2) continue; if(d<mn[last][st[a]][st[b]]) mn[last][st[a]][st[b]]=d; } }
  for(int a=0;a<m;a++) seen[st[a]]=0; }
void dfs(int n){ if(n>0) node(n); if(n==N) return;
  for(int v=-1;v<=1;v+=2){ s[n]=v; F[n+1]=F[n]+v; G[n+1]=G[n]+F[n+1]; E[n]=endab(n);
    int d=dd[n]+(v<0?1:0)-(E[n]?1:0); if(d<0) continue; dd[n+1]=d; dfs(n+1); } }
int main(int c,char**v){ N=atoi(v[1]); memset(mn,9,sizeof mn); memset(mn1,9,sizeof mn1); dfs(0);
  FILE*f=fopen(v[2],"wb"); fwrite(mn,1,sizeof mn,f); fwrite(mn1,1,sizeof mn1,f); fclose(f); return 0; }
