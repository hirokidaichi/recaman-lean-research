// Same setting as c1. For every cap u in y (F(u)=h2+1, u<=len), with return A b=u-1, classify:
// 0 = alpha-cap, 1 = coverable (tau_b>=q0), 2 = straddler (tau_b<q0). Histogram of P(u)=sum_{(q0,u]}(h2-F) by (az,class,first-straddler?)
#include <stdio.h>
#include <stdlib.h>
int s[256],F[257],G[257],D[257],AN[257]; int q0,h2,k1,LW,LY; long H[12][3][2][40]; long minZb=999;
int tauof(int b){ for(int t=b-3;t>=0;t-=4) if(F[b]==F[t]+1 && G[b]-G[t]==(b-t)*F[t]) return t; return -1;}
void pr(int len){ for(int i=k1;i<=len;i++){ if(i==q0)putchar('|'); putchar(s[i]>0?'A':'S');} }
void dfsy(int len,int ay,int P,int nst){
  if(len-q0>=LY) return;
  for(int v=-1;v<=1;v+=2){
    s[len]=v; F[len+1]=F[len]+v; G[len+1]=G[len]+F[len+1];
    int nay=ay,nd=D[len],t=-1,isn=0,cp=0;
    if(v<0) nd++; else { t=tauof(len); if(t<0){ nay++; if(nay>1) continue; isn=1;} else { nd--; if(t==q0 && nd==0) cp=1; } }
    if(nd<1 && !cp) continue;
    D[len+1]=nd; AN[len+1]=AN[len]+isn;
    int az=AN[q0]-AN[k1]; int nP=P+(h2-F[len+1]); int ns=nst;
    if(F[len+1]==h2+1 && len+1<=len+1){ int cl= isn?0:(t>=q0?1:2); int fs=0; if(cl==2){ fs=(ns==0); ns++; }
      int pv=nP+20; if(pv<0)pv=0; if(pv>39)pv=39; H[az<11?az:11][cl][fs][pv]++;
      if(cl==2 && fs && nP<-2){ printf("LOWZB az=%d P=%d ",az,nP); pr(len); printf("\n"); } }
    if(cp) continue;
    dfsy(len+1,nay,nP,ns);
  }
}
void dfsw(int len,int lastz){
  if(D[len]==1 && len>0){ q0=len; h2=F[len]; k1=lastz; dfsy(len,0,0,0); }
  if(len>=LW) return;
  for(int v=-1;v<=1;v+=2){
    s[len]=v; F[len+1]=F[len]+v; G[len+1]=G[len]+F[len+1];
    int nd=D[len], isn=0; if(v<0) nd++; else if(tauof(len)>=0) nd--; else isn=1; if(nd<0) continue;
    D[len+1]=nd; AN[len+1]=AN[len]+isn;
    dfsw(len+1,nd==0?len+1:lastz);
  }
}
int main(int c,char**v){ LW=atoi(v[1]); LY=atoi(v[2]); dfsw(0,0);
  for(int a=0;a<12;a++)for(int cl=0;cl<3;cl++)for(int f=0;f<2;f++){ int any=0; for(int p=0;p<40;p++) if(H[a][cl][f][p]){ if(!any){printf("az=%d class=%d firststr=%d:",a,cl,f);any=1;} printf(" P=%d:%ld",p-20,H[a][cl][f][p]); } if(any) printf("\n"); }
}
