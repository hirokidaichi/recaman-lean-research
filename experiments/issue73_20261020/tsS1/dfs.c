// DFS over prefixes x=sigma[0,n) with prefix-H (d>=0). At nodes with last clock A and d in {1,2} (or <=SMAX):
// t1-states (D=j+1, Q=0), t2-states (D=i+j, Q=-(2i+1)), Q = area(t,n] + D(D-1)/2.
// prints classification lines: kind s j i t-k1 u  (u = x[k1,n)), aggregated via sort|uniq -c outside.
// also flags TS violations (t1(j) and t2(j,i) both present, i.e. same j).
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int N,SMAX,s[128],F[129],G[129],E[128],dd[129];
int endab(int b){ if(s[b]<0) return 0; for(int t=b-3;t>=0;t-=4) if(F[b]==F[t]+1&&G[b]-G[t]==(b-t)*F[t]) return 1; return 0;}
void out(int n,int k1){ for(int k=k1;k<n;k++)putchar(s[k]>0?'A':'S'); }
void node(int n){
  int d=dd[n]; if(s[n-1]<0||d<1||d>SMAX) return;
  int k1=0; for(int k=0;k<=n;k++) if(dd[k]==0) k1=k;
  int has1[130]; memset(has1,0,sizeof has1); int t1pos[130];
  for(int t=0;t<n;t++){ int D=F[n]-F[t]; if(D<1) continue; long Q=G[n]-G[t]-(long)(n-t)*F[t]+(long)D*(D-1)/2;
    if(Q==0){ int j=D-1; has1[j]=1; t1pos[j]=t; if(j>=1||d>=2){printf("T1 s=%d j=%d tk=%d u=",d,j,t-k1); out(n,k1); printf("\n");} } }
  for(int t=0;t<n;t++){ int D=F[n]-F[t]; if(D<1) continue; long Q=G[n]-G[t]-(long)(n-t)*F[t]+(long)D*(D-1)/2;
    if(Q<0 && (-Q)%2==1){ int i=(-Q-1)/2; if(i<=D){ int j=D-i; if(i+j>=1){ printf("T2 s=%d j=%d i=%d tk=%d u=",d,j,i,t-k1); out(n,k1); printf("\n");
        if(has1[j]){ printf("TSVIOL s=%d j=%d i=%d x=",d,j,i); out(n,0); printf("\n"); } } } } }
}
void dfs(int n){
  if(n>0) node(n);
  if(n==N) return;
  for(int v=-1;v<=1;v+=2){ s[n]=v; F[n+1]=F[n]+v; G[n+1]=G[n]+F[n+1]; E[n]=endab(n);
    int d=dd[n]+(v<0?1:0)-(E[n]?1:0); if(d<0) continue; dd[n+1]=d; dfs(n+1); }
}
int main(int c,char**v){N=atoi(v[1]); SMAX=atoi(v[2]); F[0]=G[0]=0; dd[0]=0; dfs(0); return 0;}
