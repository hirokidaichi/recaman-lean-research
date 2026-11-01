// Setting: prefix-H w (d>=0 on [p,q0]), d(q0)=1, k1 last zero of d before q0; y with a_y<=1, d>=1 on (q0,len];
// completion: A at len with tau==q0 and d->0 (k=len+1). Report completions (y, a_z) and, for ALL y-prefixes after alpha,
// counts: straddler caps (return A at level h2 with tau<q0), straddlers with tau=k1 by level.
#include <stdio.h>
#include <stdlib.h>
int s[256],F[257],G[257],D[257],AN[257]; int q0,h2,k1,LW,LY; long comp=0,compSAAA=0,ev=0;
long stcap=0, stcapaz[12]; long nk1[12][8];
int tauof(int b){ for(int t=b-3;t>=0;t-=4) if(F[b]==F[t]+1 && G[b]-G[t]==(b-t)*F[t]) return t; return -1;}
void pr(int len){ for(int i=k1;i<=len;i++){ if(i==q0)putchar('|'); putchar(s[i]>0?'A':'S');} }
void dfsy(int len,int ay,int nst){
  if(len-q0>=LY) return;
  for(int v=-1;v<=1;v+=2){
    s[len]=v; F[len+1]=F[len]+v; G[len+1]=G[len]+F[len+1];
    int nay=ay,nd=D[len],t=-1,isn=0,cp=0;
    if(v<0) nd++; else { t=tauof(len); if(t<0){ nay++; if(nay>1) continue; isn=1;} else { nd--; if(t==q0 && nd==0) cp=1; } }
    if(nd<1 && !cp) continue;
    D[len+1]=nd; AN[len+1]=AN[len]+isn;
    int az=AN[q0]-AN[k1]; int ns=nst;
    if(v>0 && t>=0 && t<q0){ ev++; if(t==k1){ ns++; int lv=F[len]-h2+4; if(lv<0)lv=0; if(lv>7)lv=7; nk1[az<11?az:11][lv]++; }
       if(F[len]==h2){ stcap++; stcapaz[az<11?az:11]++; if(t!=k1){printf("STCAP_notk1 "); pr(len); printf("\n");} } }
    if(cp){ comp++; int isS=(len==q0+3 && s[q0]<0 && s[q0+1]>0 && s[q0+2]>0); if(isS) compSAAA++; else { printf("COMP_nonSAAA az=%d ",az); pr(len); printf("\n"); }
       continue; }
    if(ns>=2){ printf("TWO_k1 az=%d ",az); pr(len); printf("\n"); }
    dfsy(len+1,nay,ns);
  }
}
void dfsw(int len,int lastz){
  if(D[len]==1 && len>0){ q0=len; h2=F[len]; k1=lastz; dfsy(len,0,0); }
  if(len>=LW) return;
  for(int v=-1;v<=1;v+=2){
    s[len]=v; F[len+1]=F[len]+v; G[len+1]=G[len]+F[len+1];
    int nd=D[len], isn=0; if(v<0) nd++; else if(tauof(len)>=0) nd--; else isn=1; if(nd<0) continue;
    D[len+1]=nd; AN[len+1]=AN[len]+isn;
    dfsw(len+1,nd==0?len+1:lastz);
  }
}
int main(int c,char**v){ LW=atoi(v[1]); LY=atoi(v[2]); dfsw(0,0);
  printf("comp=%ld SAAA=%ld straddlers=%ld straddler-caps=%ld\n",comp,compSAAA,ev,stcap);
  for(int a=0;a<12;a++) if(stcapaz[a]) printf(" stcap az=%d: %ld\n",a,stcapaz[a]);
  for(int a=0;a<12;a++) for(int l=0;l<8;l++) if(nk1[a][l]) printf(" tau=k1 straddler az=%d level-h2=%d : %ld\n",a,l-4,nk1[a][l]);
}
