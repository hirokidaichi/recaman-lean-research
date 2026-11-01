// prefix-H from 0; at each q0 with d(q0)=1 (k1 = last zero of d): histogram of (a_z, g - min_z F)
// and whether some endable z-clock has a window starting < k1, and min level of endable z-clocks rel running min.
#include <stdio.h>
#include <stdlib.h>
int s[256],F[257],G[257],D[257],AN[257],EN[257]; int LW; long H[16][16]; long Hs[16][16]; int pr=0;
int isw(int b,int t){ return t>=0 && F[b]==F[t]+1 && G[b]-G[t]==(b-t)*F[t]; }
void dfsw(int len,int lastz){
  if(D[len]==1 && len>0){ int q0=len,k1=lastz,g=F[k1],mn=g; for(int i=k1;i<=q0;i++) if(F[i]<mn) mn=F[i];
    int az=AN[q0]-AN[k1]; if(az>15)az=15; int dp=g-mn; if(dp>15)dp=15; H[az][dp]++;
    int strad=0; for(int b=k1;b<q0;b++) if(s[b]>0&&EN[b]){ for(int t=b-3;t>=0&&t<k1;t-=4) {} for(int t=b-3;t>=0;t-=4) if(t<k1&&isw(b,t)) strad=1; }
    if(strad) Hs[az][dp]++;
    if(dp>=2 && pr<15){pr++; for(int i=0;i<q0;i++){ if(i==k1)putchar('|'); putchar(s[i]>0?'A':'S');} printf(" az=%d dip=%d strad=%d\n",az,dp,strad);} }
  if(len>=LW) return;
  for(int v=-1;v<=1;v+=2){
    s[len]=v; F[len+1]=F[len]+v; G[len+1]=G[len]+F[len+1];
    int nd=D[len],isn=0,end=0; if(v>0){ for(int t=len-3;t>=0;t-=4) if(isw(len,t)){end=1;break;} }
    if(v<0) nd++; else if(end) nd--; else isn=1; if(nd<0) continue;
    EN[len]=end; D[len+1]=nd; AN[len+1]=AN[len]+isn; dfsw(len+1,nd==0?len+1:lastz);
  }
}
int main(int c,char**v){ LW=atoi(v[1]); dfsw(0,0);
 for(int a=0;a<16;a++){ printf("az=%d:",a); for(int d=0;d<16;d++) if(H[a][d]) printf(" dip%d=%ld(strad %ld)",d,H[a][d],Hs[a][d]); printf("\n");} }
