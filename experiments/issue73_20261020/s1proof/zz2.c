#include <stdio.h>
#include <stdlib.h>
int s[256],F[257],G[257],D[257],NE[257]; int LW; long H[80][12];
int tauof(int b){ for(int t=b-3;t>=0;t-=4) if(F[b]==F[t]+1 && G[b]-G[t]==(b-t)*F[t]) return t; return -1;}
void dfsw(int len,int lastz){
  if(D[len]==1 && len>0){ int q0=len,k1=lastz; int az=0; for(int u=k1;u<q0;u++) az+=NE[u]; int Z=0; for(int u=k1+1;u<=q0;u++) Z+=F[u]-F[k1];
    int v=Z+40; H[v<0?0:(v>79?79:v)][az>11?11:az]++; if(az==2 && q0-k1>5){ for(int i=k1;i<q0;i++)putchar(s[i]>0?'A':'S'); printf(" Z=%d\n",Z);} }
  if(len>=LW) return;
  for(int v=-1;v<=1;v+=2){ s[len]=v; F[len+1]=F[len]+v; G[len+1]=G[len]+F[len+1];
    int nd=D[len]; NE[len]=0; if(v<0) nd++; else if(tauof(len)>=0) nd--; else NE[len]=1; if(nd<0) continue;
    D[len+1]=nd; dfsw(len+1,nd==0?len+1:lastz); }
}
int main(int c,char**v){ LW=atoi(v[1]); dfsw(0,0); for(int a=0;a<6;a++){ printf("az=%d:",a); for(int i=0;i<80;i++) if(H[i][a]) printf(" Z%d:%ld",i-40,H[i][a]); printf("\n");} }
