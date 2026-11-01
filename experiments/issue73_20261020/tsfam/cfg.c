// dump distinct configurations: (d,last, sorted multiset of window states incl. fresh (0,0) for t=n) for d<=SM
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define DM 6
#define QM 16
#define NQ (2*QM+1)
int N,SM,s[128],F[129],G[129],E[128],dd[129];
int endab(int b){ if(s[b]<0) return 0; for(int t=b-3;t>=0;t-=4) if(F[b]==F[t]+1&&G[b]-G[t]==(b-t)*F[t]) return 1; return 0;}
int cmp(const void*a,const void*b){return *(int*)a-*(int*)b;}
void node(int n){ int d=dd[n]; if(d>SM) return; int st[130],m=0;
  for(int t=0;t<=n;t++){ int D=F[n]-F[t]; if(D<-DM||D>DM) continue; long Q=G[n]-G[t]-(long)(n-t)*F[t]+(long)D*(D-1)/2; if(Q<-QM||Q>QM) continue;
    st[m++]=(D+DM)*NQ+(Q+QM);} qsort(st,m,sizeof(int),cmp);
  printf("%d %c",d,n==0?'-':(s[n-1]>0?'A':'S')); int prev=-1,c=0; for(int a=0;a<m;a++){ if(st[a]==prev){c++; if(c>=2) continue;} else c=0; prev=st[a]; printf(" %d,%d",st[a]/NQ-DM,st[a]%NQ-QM);} printf("\n"); }
void dfs(int n){ node(n); if(n==N) return;
  for(int v=-1;v<=1;v+=2){ s[n]=v; F[n+1]=F[n]+v; G[n+1]=G[n]+F[n+1]; E[n]=endab(n);
    int d=dd[n]+(v<0?1:0)-(E[n]?1:0); if(d<0) continue; dd[n+1]=d; dfs(n+1); } }
int main(int c,char**v){ N=atoi(v[1]); SM=atoi(v[2]); dfs(0); return 0; }
