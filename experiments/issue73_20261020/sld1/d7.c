// y-DFS with Lemma T constraint: d>=1 on (q0,k) (d(k)=0 at completion). Report y-length histogram of surviving prefixes
// and distinct y-prefix patterns (with z suffix tail) at max depth.
#include <stdio.h>
#include <stdlib.h>
int s[256],F[257],G[257]; int q0,h2,k1,LW,LY; long hist[128],x2=0,comps=0;
int tauof(int b){ for(int t=b-3;t>=0;t-=4) if(F[b]==F[t]+1 && G[b]-G[t]==(b-t)*F[t]) return t; return -1;}
void dfsy(int len,int ay,int d,int X){
  hist[len-q0]++;
  if(len-q0>=LY) { printf("DEEP "); for(int i=k1;i<len;i++){ if(i==q0)putchar('|'); putchar(s[i]>0?'A':'S');} printf("\n"); return; }
  for(int v=-1;v<=1;v+=2){
    s[len]=v; F[len+1]=F[len]+v; G[len+1]=G[len]+F[len+1];
    int nay=ay,nd=d,comp=0,t=-1,nX=X;
    if(v<0) nd=d+1; else { t=tauof(len); if(t<0){ nay++; if(nay>1) continue; } else { nd=d-1; if(t<q0) nX++; if(t==q0) comp=1; } }
    if(comp){ if(nd==0) comps++; continue; }
    if(nd<1) continue;
    if(nX>=2) x2++;
    dfsy(len+1,nay,nd,nX);
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
  printf("comps=%ld X2=%ld\n",comps,x2); for(int i=0;i<128;i++) if(hist[i]) printf(" ylen %d: %ld\n",i,hist[i]); }
