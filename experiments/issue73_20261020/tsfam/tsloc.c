// all strings (H verified <=34 so no restriction). At node n (last clock A), TS' pair t1:(j+1,0), t2:(i+j,-(2i+1)).
// report min slack from p=min(t1,t2), from max(t1,t2), and from p=0, per order (t1<t2 or t2<t1).
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int N,s[128],F[129],G[129],ms[128]; int mnA[2][8][8],mnB[2][8][8],mn0[2][8][8]; char wit[2][8][8][130];
int maxstart(int b){ if(s[b]<0) return -1; for(int t=b-3;t>=0;t-=4) {} int best=-1; for(int t=b-3;t>=0;t-=4) if(F[b]==F[t]+1&&G[b]-G[t]==(b-t)*F[t]){best=t;break;} return best;}
int slack(int t,int n){ int v=0; for(int b=t;b<n;b++){ if(s[b]<0) v++; else if(ms[b]>=t) v--; } return v; }
void node(int n){ if(s[n-1]<0) return; int D[130]; long Q[130];
  for(int t=0;t<n;t++){ D[t]=F[n]-F[t]; Q[t]=G[n]-G[t]-(long)(n-t)*F[t]+(long)D[t]*(D[t]-1)/2; }
  for(int t1=0;t1<n;t1++){ if(Q[t1]!=0||D[t1]<1||D[t1]>8) continue; int j=D[t1]-1;
    for(int t2=0;t2<n;t2++){ if(t2==t1||Q[t2]>=0||((-Q[t2])&1)==0) continue; int i=(-Q[t2]-1)/2; if(D[t2]!=i+j||i>=8) continue;
      int o=t2<t1; int lo=o?t2:t1, hi=o?t1:t2; int a=slack(lo,n),b=slack(hi,n),z=slack(0,n);
      if(a<mnA[o][j][i]){ mnA[o][j][i]=a; int k=0; for(int c=lo;c<n;c++) wit[o][j][i][k++]=s[c]<0?'S':(ms[c]>=lo?'a':'A'); wit[o][j][i][k]=0; }
      if(b<mnB[o][j][i]) mnB[o][j][i]=b; if(z<mn0[o][j][i]) mn0[o][j][i]=z; } } }
void dfs(int n){ if(n>0) node(n); if(n==N) return;
  for(int v=-1;v<=1;v+=2){ s[n]=v; F[n+1]=F[n]+v; G[n+1]=G[n]+F[n+1]; ms[n]=maxstart(n); dfs(n+1); } }
int main(int c,char**v){ N=atoi(v[1]); for(int o=0;o<2;o++)for(int a=0;a<8;a++)for(int b=0;b<8;b++)mnA[o][a][b]=mnB[o][a][b]=mn0[o][a][b]=99; dfs(0);
  for(int o=0;o<2;o++){ printf("order %s: entries minSlack(from older)/from newer/from 0\n",o?"t2<t1":"t1<t2");
    for(int j=0;j<5;j++){ for(int i=0;i<5;i++) printf(" %2d/%2d/%2d",mnA[o][j][i],mnB[o][j][i],mn0[o][j][i]); printf("\n"); }
    for(int j=0;j<5;j++)for(int i=0;i<5;i++) if(mnA[o][j][i]<3) printf("  j=%d i=%d wit(from older)=%s\n",j,i,wit[o][j][i]); } }
