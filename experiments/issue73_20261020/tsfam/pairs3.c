// localized data: all strings w of length n<=N (H verified <=34). Older start = 0 (translation invariance).
// phi[c][xo][xn] = min slack(0,n) over w with state of start 0 = xo, some start 0<tn<=n with state xn, last clock c.
// psi[c][xo] = min slack(0,n). c: 0=S,1=A,  n=0 recorded into both.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define DM 7
#define QM 20
#define NQ (2*QM+1)
#define NS ((2*DM+1)*NQ)
#define CAP 9
int N,s[128],F[129],G[129],dd[129];
unsigned char phi[2][NS][NS], psi[2][NS];
int endab0(int b){ if(s[b]<0) return 0; for(int t=b-3;t>=0;t-=4) if(F[b]==F[t]+1&&G[b]-G[t]==(b-t)*F[t]) return 1; return 0;}
static inline int st(int n,int t){ int D=F[n]-F[t]; if(D<-DM||D>DM) return -1; long Q=G[n]-G[t]-(long)(n-t)*F[t]+(long)D*(D-1)/2; if(Q<-QM||Q>QM) return -1; return (D+DM)*NQ+(Q+QM);}
void node(int n){ int d=dd[n]; if(d>CAP) d=CAP; int xo=st(n,0); if(xo<0) return;
  for(int c=0;c<2;c++){ if(n>0 && c!=(s[n-1]>0)) continue; if(d<psi[c][xo]) psi[c][xo]=d;
    for(int t=1;t<=n;t++){ int xn=st(n,t); if(xn<0) continue; if(d<phi[c][xo][xn]) phi[c][xo][xn]=d; } } }
void dfs(int n){ node(n); if(n==N) return;
  for(int v=-1;v<=1;v+=2){ s[n]=v; F[n+1]=F[n]+v; G[n+1]=G[n]+F[n+1]; dd[n+1]=dd[n]+(v<0?1:0)-(endab0(n)?1:0); dfs(n+1); } }
int main(int c,char**v){ N=atoi(v[1]); memset(phi,CAP+1,sizeof phi); memset(psi,CAP+1,sizeof psi); dfs(0);
  FILE*f=fopen(v[2],"wb"); fwrite(phi,1,sizeof phi,f); fwrite(psi,1,sizeof psi,f); fclose(f); return 0; }
