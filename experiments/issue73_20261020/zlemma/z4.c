// prefix-H x, d(q0)=1, y with a_y<=1, d>=1 on (q0,len]. For each straddler b in y (tau in [p,q0)):
// histogram of (t-k1==0?, d(t), a[t,q0), a[q0,b), d(b), F(t)-h2, min_{[t,b]}F - F(t), #S-run at start of z)
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int s[256],F[257],G[257],D[257],AN[257]; int q0,h2,k1,LW,LY; long hist[2][6][6][3][8][8]; long ev=0, tk=0;
int tauof(int b){ for(int t=b-3;t>=0;t-=4) if(F[b]==F[t]+1 && G[b]-G[t]==(b-t)*F[t]) return t; return -1;}
void dfsy(int len,int ay){
  if(len-q0>=LY) return;
  for(int v=-1;v<=1;v+=2){
    s[len]=v; F[len+1]=F[len]+v; G[len+1]=G[len]+F[len+1];
    int nay=ay,nd=D[len],comp=0,t=-1,isn=0;
    if(v<0) nd++; else { t=tauof(len); if(t<0){ nay++; if(nay>1) continue; isn=1;} else { nd--; if(t==q0) comp=1; } }
    if(nd<0) continue; if(comp && nd!=0) {/*still fine*/}
    D[len+1]=nd; AN[len+1]=AN[len]+isn;
    if(v>0 && t>=0 && t<q0){ ev++; if(t<k1) tk++;
      int a1=AN[q0]-AN[t], a2=AN[len]-AN[q0]; int mn=999; for(int u=t;u<=len;u++) if(F[u]<mn) mn=F[u];
      int i0=(t>k1), i1=D[t]<5?D[t]:5, i2=a1<5?a1:5, i3=a2, i4=D[len]<7?D[len]:7, i5=F[t]-mn; if(i5>7)i5=7;
      hist[i0][i1][i2][i3][i4][i5]++; for(int i=k1;i<=len;i++){ if(i==q0)putchar('|'); putchar(s[i]>0?'A':'S');} printf(" az=%d\n",i2); }
    if(!comp) dfsy(len+1,nay);
  }
}
void dfsw(int len,int lastz){
  if(D[len]==1 && len>0){ q0=len; h2=F[len]; k1=lastz; dfsy(len,0); }
  if(len>=LW) return;
  for(int v=-1;v<=1;v+=2){
    s[len]=v; F[len+1]=F[len]+v; G[len+1]=G[len]+F[len+1];
    int nd=D[len], isn=0; if(v<0) nd++; else if(tauof(len)>=0) nd--; else isn=1; if(nd<0) continue;
    D[len+1]=nd; AN[len+1]=AN[len]+isn;
    dfsw(len+1,nd==0?len+1:lastz);
  }
}
int main(int c,char**v){ LW=atoi(v[1]); LY=atoi(v[2]); dfsw(0,0);
  printf("ev=%ld t<k1=%ld\n(t>k1,d(t),a[t,q0),a[q0,b),d(b),F(t)-min)\n",ev,tk);
  for(int a=0;a<2;a++)for(int b=0;b<6;b++)for(int c2=0;c2<6;c2++)for(int d=0;d<3;d++)for(int e=0;e<8;e++)for(int f=0;f<8;f++) if(hist[a][b][c2][d][e][f]) printf("%d %d %d %d %d %d : %ld\n",a,b,c2,d,e,f,hist[a][b][c2][d][e][f]);
}
