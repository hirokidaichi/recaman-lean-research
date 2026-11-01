// Setting: prefix-H w (d>=0), q0 with d(q0)=1, k1=last zero of d before q0. y-prefix: d>=1 on (q0,len], a_y<=1.
// Unlike z3, we do NOT stop at endables with tau=q0 (continue while d>=1).
// Records: straddlers (tau<q0): tau-k1 histogram, #straddlers with tau=k1 (S2), minF-g on [q0,len] after 1st straddler,
// minF-g on y overall, and d - (a_z + a[q0,u)) max.
#include <stdio.h>
#include <stdlib.h>
int s[256],F[257],G[257],D[257],AN[257]; int q0,h2,k1,LW,LY; long ev=0,tlt=0,tgt=0,s2bad=0; long hmin[40],hminall[40],hd[40];
int tauof(int b){ for(int t=b-3;t>=0;t-=4) if(F[b]==F[t]+1 && G[b]-G[t]==(b-t)*F[t]) return t; return -1;}
void pr(int len){ for(int i=k1;i<=len;i++){ if(i==q0)putchar('|'); putchar(s[i]>0?'A':'S');} }
void dfsy(int len,int ay,int nstr,int minafter,int miny){
  if(len-q0>=LY) return;
  for(int v=-1;v<=1;v+=2){
    s[len]=v; F[len+1]=F[len]+v; G[len+1]=G[len]+F[len+1];
    int nay=ay,nd=D[len],t=-1,isn=0;
    if(v<0) nd++; else { t=tauof(len); if(t<0){ nay++; if(nay>AYMAX) continue; isn=1;} else nd--; }
    if(nd<DMIN) continue;
    D[len+1]=nd; AN[len+1]=AN[len]+isn;
    int g=F[k1]; int ns=nstr, ma=minafter, my=miny;
    if(F[len+1]-g<my) my=F[len+1]-g;
    if(ns>0 && F[len+1]-g<ma) ma=F[len+1]-g;
    if(v>0 && t>=0 && t<q0){ ev++; if(t<k1){tlt++; if(tlt<6){printf("TLT az=%d ",AN[q0]-AN[k1]); pr(len); printf(" t=%d k1=%d\n",t,k1);}} if(t>k1){tgt++; if(tgt<6){printf("TGT az=%d ",AN[q0]-AN[k1]); pr(len); printf(" t=%d k1=%d\n",t,k1);}}
       if(t==k1){ ns++; if(ns>=2){ s2bad++;  } if(ns==1) ma=F[len+1]-g; } }
    int az=AN[q0]-AN[k1]; int ex=nd-(az+AN[len+1]-AN[q0]); hd[ex+20<0?0:(ex+20>39?39:ex+20)]++;
    if(ns>0) hmin[ma+20<0?0:(ma+20>39?39:ma+20)]++;
    hminall[my+20<0?0:(my+20>39?39:my+20)]++;
    dfsy(len+1,nay,ns,ma,my);
  }
}
void dfsw(int len,int lastz){
  if(D[len]==1 && len>0){ q0=len; h2=F[len]; k1=lastz; int my=F[q0]-F[k1]; dfsy(len,0,0,99,my); }
  if(len>=LW) return;
  for(int v=-1;v<=1;v+=2){
    s[len]=v; F[len+1]=F[len]+v; G[len+1]=G[len]+F[len+1];
    int nd=D[len], isn=0; if(v<0) nd++; else if(tauof(len)>=0) nd--; else isn=1; if(nd<0) continue;
    D[len+1]=nd; AN[len+1]=AN[len]+isn;
    dfsw(len+1,nd==0?len+1:lastz);
  }
}
int main(int c,char**v){ LW=atoi(v[1]); LY=atoi(v[2]); dfsw(0,0);
  printf("ev=%ld t<k1=%ld t>k1=%ld S2bad=%ld\n",ev,tlt,tgt,s2bad);
  printf("min F-g on y after first straddler (over nodes):\n"); for(int i=0;i<40;i++) if(hmin[i]) printf("  %d: %ld\n",i-20,hmin[i]);
  printf("min F-g on [q0,len] all nodes:\n"); for(int i=0;i<40;i++) if(hminall[i]) printf("  %d: %ld\n",i-20,hminall[i]);
  printf("d-(a_z+a[q0,u)) :\n"); for(int i=0;i<40;i++) if(hd[i]) printf("  %d: %ld\n",i-20,hd[i]);
}
