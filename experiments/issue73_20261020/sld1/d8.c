// Verify Lemma T on completed configurations (a_y<=1, d(q0)=1): d>=1 on (q0,k) -- by searching y with only d>=0 and
// recording any completion where some d(c)=0, q0<c<k. Also count completions where y starts with A.
#include <stdio.h>
#include <stdlib.h>
int s[256],F[257],G[257]; int q0,h2,k1,LW,LY; long bad=0,comps=0,ystartA=0;
int tauof(int b){ for(int t=b-3;t>=0;t-=4) if(F[b]==F[t]+1 && G[b]-G[t]==(b-t)*F[t]) return t; return -1;}
void dfsy(int len,int ay,int d,int z0){
  if(len-q0>=LY) return;
  for(int v=-1;v<=1;v+=2){
    s[len]=v; F[len+1]=F[len]+v; G[len+1]=G[len]+F[len+1];
    int nay=ay,nd=d,comp=0,t=-1;
    if(v<0) nd=d+1; else { t=tauof(len); if(t<0){ nay++; if(nay>1) continue; } else { nd=d-1; if(nd<0) continue; if(t==q0) comp=1; } }
    if(comp){ comps++; if(z0) bad++; if(s[q0]>0) ystartA++; continue; }
    dfsy(len+1,nay,nd,z0||nd==0);
  }
}
void dfsw(int len,int d,int lastz){
  if(d==1 && len>0){ q0=len; h2=F[len]; k1=lastz; dfsy(len,0,1,0); }
  if(len>=LW) return;
  for(int v=-1;v<=1;v+=2){
    s[len]=v; F[len+1]=F[len]+v; G[len+1]=G[len]+F[len+1];
    int nd=d; if(v<0) nd++; else if(tauof(len)>=0) nd--; if(nd<0) continue;
    dfsw(len+1,nd,nd==0?len+1:lastz);
  }
}
int main(int c,char**v){ LW=atoi(v[1]); LY=atoi(v[2]); F[0]=G[0]=0; dfsw(0,0,0);
  printf("LW=%d LY=%d comps=%ld comps-with-interior-zero=%ld ystartA=%ld\n",LW,LY,comps,bad,ystartA); }
