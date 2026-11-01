// prefix-H words from 0 (d>=0). For every q0 with d(q0)=1, k1 = last zero of d before q0.
// For non-endable A clocks M in (k1,q0) with F(M) = min_{[k1,q0]} F: histogram of F(M)-h2 (h2=F(q0)), and a_z.
#include <stdio.h>
#include <stdlib.h>
int s[256],F[257],G[257],D[257],NE[257]; int LW; long H[40][12]; 
int tauof(int b){ for(int t=b-3;t>=0;t-=4) if(F[b]==F[t]+1 && G[b]-G[t]==(b-t)*F[t]) return t; return -1;}
void dfsw(int len,int lastz){
  if(D[len]==1 && len>0){ int q0=len,k1=lastz,h2=F[q0]; int mn=999; for(int u=k1;u<=q0;u++) if(F[u]<mn) mn=F[u];
    int az=0; for(int u=k1;u<q0;u++) az+=NE[u];
    for(int M=k1+1;M<q0;M++) if(NE[M] && F[M]==mn){ int v=F[M]-h2+20; H[v<0?0:v][az>11?11:az]++; if(F[M]-h2<=-2){ for(int i=k1;i<q0;i++)putchar(s[i]>0?'A':'S'); printf(" M=%d h=%d\n",M-k1,F[M]-h2);} } }
  if(len>=LW) return;
  for(int v=-1;v<=1;v+=2){ s[len]=v; F[len+1]=F[len]+v; G[len+1]=G[len]+F[len+1];
    int nd=D[len]; NE[len]=0; if(v<0) nd++; else if(tauof(len)>=0) nd--; else NE[len]=1; if(nd<0) continue;
    D[len+1]=nd; dfsw(len+1,nd==0?len+1:lastz); }
}
int main(int c,char**v){ LW=atoi(v[1]); dfsw(0,0); for(int i=0;i<40;i++)for(int a=0;a<12;a++) if(H[i][a]) printf("F(M)-h2=%d az=%d: %ld\n",i-20,a,H[i][a]); }
