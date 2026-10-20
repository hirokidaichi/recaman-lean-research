// DFS over prefix-H strings; record for every unordered pair of DISTINCT starts t1<t2<=n (incl. t=n fresh (0,0)) with states in window
// the min d(n) (cap CAP), split by last clock (0=S,1=A); and singles. Time 0 handled separately in fixpoint.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define DM 7
#define QM 20
#define NQ (2*QM+1)
#define NS ((2*DM+1)*NQ)
#define CAP 7
int N,s[128],F[129],G[129],E[128],dd[129];
unsigned char mn[2][NS][NS], mn1[2][NS];
int endab(int b){ if(s[b]<0) return 0; for(int t=b-3;t>=0;t-=4) if(F[b]==F[t]+1&&G[b]-G[t]==(b-t)*F[t]) return 1; return 0;}
void node(int n){ int d=dd[n]; if(d>CAP) d=CAP; int last=s[n-1]>0; int st[130],m=0;
  for(int t=0;t<=n;t++){ int D=F[n]-F[t]; if(D<-DM||D>DM) continue; long Q=G[n]-G[t]-(long)(n-t)*F[t]+(long)D*(D-1)/2; if(Q<-QM||Q>QM) continue; st[m++]=(D+DM)*NQ+(Q+QM);}
  for(int a=0;a<m;a++){ if(d<mn1[last][st[a]]) mn1[last][st[a]]=d; for(int b=a+1;b<m;b++){ int x=st[a],y=st[b]; if(d<mn[last][x][y]){mn[last][x][y]=d; mn[last][y][x]=d;} } } }
void dfs(int n){ if(n>0) node(n); if(n==N) return;
  for(int v=-1;v<=1;v+=2){ s[n]=v; F[n+1]=F[n]+v; G[n+1]=G[n]+F[n+1]; E[n]=endab(n);
    int d=dd[n]+(v<0?1:0)-(E[n]?1:0); if(d<0) continue; dd[n+1]=d; dfs(n+1); } }
int main(int c,char**v){ N=atoi(v[1]); memset(mn,CAP+1,sizeof mn); memset(mn1,CAP+1,sizeof mn1); dfs(0);
  FILE*f=fopen(v[2],"wb"); fwrite(mn,1,sizeof mn,f); fwrite(mn1,1,sizeof mn1,f); fclose(f); return 0; }
