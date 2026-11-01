// After the first straddler b' (first endable A in y): test
// R1: F(q) >= F(b') for all q>b' ; R2: F(q) >= min_{[q0,b']}F + 1 for q > b'  (on all y-prefixes)
// also: is first endable A of y always a straddler (sanity), n1 position stats relative to b'.
#include <stdio.h>
#include <stdlib.h>
int s[256],F[257],G[257]; int q0,h2,k1,LW,LY; long r1=0,r2=0,ev=0,nadj[5];
int tauof(int b){ for(int t=b-3;t>=0;t-=4) if(F[b]==F[t]+1 && G[b]-G[t]==(b-t)*F[t]) return t; return -1;}
void pr(int len){ for(int i=0;i<len;i++){ if(i==k1)putchar('^'); if(i==q0)putchar('|'); putchar(s[i]>0?'A':'S'); } }
void dfsy(int len,int ay,int d,int bp,int mn,int n1){
  if(len-q0>=LY) return;
  for(int v=-1;v<=1;v+=2){
    s[len]=v; F[len+1]=F[len]+v; G[len+1]=G[len]+F[len+1];
    int nay=ay,nd=d,comp=0,t=-1,nbp=bp,nn1=n1;
    if(v<0) nd=d+1; else { t=tauof(len); if(t<0){ nay++; if(nay>1) continue; nn1=len; } else { nd=d-1; if(nd<0) continue; if(bp<0){ nbp=len; if(t>=q0) printf("FIRST NOT STRADDLER\n"); } if(t==q0) comp=1; } }
    int nmn = mn; if(nbp<0 && F[len+1]<nmn) nmn=F[len+1];
    if(bp>=0){ if(F[len+1]<F[bp]){ r1++; if(r1<5){printf("R1fail ");pr(len+1);printf("\n");} }
               if(F[len+1]<mn+1){ r2++; if(r2<5){printf("R2fail ");pr(len+1);printf("\n");} } }
    if(comp){ ev++; if(nn1>=0){int dlt=nn1-nbp; if(dlt>=-2&&dlt<=2) nadj[dlt+2]++; else printf("n1 far: %d\n",dlt);} }
    else dfsy(len+1,nay,nd,nbp,nmn,nn1);
  }
}
void dfsw(int len,int d,int lastz){
  if(d==1 && len>0){ q0=len; h2=F[len]; k1=lastz; dfsy(len,0,1,-1,h2,-1); }
  if(len>=LW) return;
  for(int v=-1;v<=1;v+=2){
    s[len]=v; F[len+1]=F[len]+v; G[len+1]=G[len]+F[len+1];
    int nd=d; if(v<0) nd++; else if(tauof(len)>=0) nd--; if(nd<0) continue;
    dfsw(len+1,nd,nd==0?len+1:lastz);
  }
}
int main(int c,char**v){ LW=atoi(v[1]); LY=atoi(v[2]); F[0]=G[0]=0; dfsw(0,0,0);
  printf("R1fail=%ld R2fail=%ld comps=%ld nadj:",r1,r2,ev); for(int i=0;i<5;i++)printf(" %ld",nadj[i]); printf("\n"); }
