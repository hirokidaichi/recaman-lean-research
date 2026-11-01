// all strings with prefix-H (d>=0 from p=0), length<=N. For each endable b (tau=t>=0): hist of (d(t), min_{u in (t,b]} d(u))
#include <stdio.h>
#include <stdlib.h>
int s[256],F[257],G[257],D[257]; int N; long h[12][12]; char ex[12][12][80];
int tauof(int b){ for(int t=b-3;t>=0;t-=4) if(F[b]==F[t]+1 && G[b]-G[t]==(b-t)*F[t]) return t; return -1;}
void dfs(int len){
  if(len>=N) return;
  for(int v=-1;v<=1;v+=2){
    s[len]=v; F[len+1]=F[len]+v; G[len+1]=G[len]+F[len+1];
    int nd=D[len],t=-1; if(v<0) nd++; else { t=tauof(len); if(t>=0) nd--; } if(nd<0) continue; D[len+1]=nd;
    if(t>=0){ int m=99; for(int u=t+1;u<=len;u++) if(D[u]<m) m=D[u]; int a=D[t]>11?11:D[t], b=m>11?11:m; if(!h[a][b]){ int i; for(i=0;i<=len&&i<79;i++) ex[a][b][i]=s[i]>0?'A':'S'; ex[a][b][i]=0; } h[a][b]++; }
    dfs(len+1);
  }
}
int main(int c,char**v){ N=atoi(v[1]); dfs(0); for(int a=0;a<12;a++)for(int b=0;b<12;b++) if(h[a][b]) printf("d(t)=%d min=%d : %ld  e.g. %s\n",a,b,h[a][b],ex[a][b]); }
