// prefix-H (d>=0) from 0; q0 with d(q0)=1, k1 last zero before q0; y: a_y<=AYMAX, d>=1 (stop extension when d would be <1, but record the clock).
// Count A clocks c in (k1, len] having ANY P2 window starting in [0,k1): in z (c<q0) and in y.
#include <stdio.h>
#include <stdlib.h>
int s[256],F[257],G[257],D[257]; int q0,h2,k1,LW,LY; long inz=0,iny=0,iny_last=0,nodes=0;
int tauof(int b){ for(int t=b-3;t>=0;t-=4) if(F[b]==F[t]+1 && G[b]-G[t]==(b-t)*F[t]) return t; return -1;}
int below(int b,int lim){ for(int t=b-3;t>=0;t-=4) if(t>k1 && t<lim && F[b]==F[t]+1 && G[b]-G[t]==(b-t)*F[t]) return 1; return 0;}
void pr(int len){ for(int i=0;i<=len;i++){ if(i==k1)putchar('['); if(i==q0)putchar('|'); putchar(s[i]>0?'A':'S');} }
void dfsy(int len,int ay){
  if(len-q0>=LY) return;
  for(int v=-1;v<=1;v+=2){
    s[len]=v; F[len+1]=F[len]+v; G[len+1]=G[len]+F[len+1]; nodes++;
    int nay=ay,nd=D[len];
    if(v<0) nd++; else { if(tauof(len)<0){ nay++; if(nay>AYMAX) continue;} else nd--; }
    if(v>0 && below(len,q0)){ if(nd>=1){ iny++; if(iny<4){printf("Y ");pr(len);printf("\n");} } else { iny_last++; if(iny_last<4){printf("YL ");pr(len);printf("\n");} } }
    if(nd<1) continue;
    D[len+1]=nd; dfsy(len+1,nay);
  }
}
void dfsw(int len,int lastz){
  if(D[len]==1 && len>0){ q0=len; h2=F[len]; k1=lastz;
    for(int c=k1+1;c<q0;c++) if(s[c]>0 && below(c,k1)){ inz++; if(inz<4){printf("Z ");pr(q0-1);printf(" c=%d\n",c);} }
    dfsy(len,0); }
  if(len>=LW) return;
  for(int v=-1;v<=1;v+=2){
    s[len]=v; F[len+1]=F[len]+v; G[len+1]=G[len]+F[len+1];
    int nd=D[len]; if(v<0) nd++; else if(tauof(len)>=0) nd--; if(nd<0) continue;
    D[len+1]=nd; dfsw(len+1,nd==0?len+1:lastz);
  }
}
int main(int c,char**v){ LW=atoi(v[1]); LY=atoi(v[2]); dfsw(0,0); printf("nodes=%ld inz=%ld iny(d>=1 after)=%ld iny(last, d->0)=%ld\n",nodes,inz,iny,iny_last); }
