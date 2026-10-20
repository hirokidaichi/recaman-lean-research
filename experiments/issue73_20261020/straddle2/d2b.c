// d=2,a_y=0: max #A in y; print strings achieving max A count
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int q0,LY,dw; int s[256],F[257],G[257]; int maxa; long cntA[20];
int tauof(int b){ for(int t=b-3;t>=0;t-=4) if(F[b]==F[t]+1 && G[b]-G[t]==(b-t)*F[t]) return t; return -1;}
void pr(int len){for(int i=0;i<len;i++){if(i==q0)putchar('|');putchar(s[i]>0?'A':'S');}}
void dfs(int len,int dq,int na){ if(na>maxa) maxa=na;
  if(len-q0>=LY) return;
  for(int v=-1;v<=1;v+=2){ s[len]=v;F[len+1]=F[len]+v;G[len+1]=G[len]+F[len+1]; int nd=dq;
    if(v<0) nd++; else { int t=tauof(len); if(t<0) continue; nd--; if(nd<0) continue; if(na+1<20)cntA[na+1]++; if(na+1>=3){pr(len+1);printf(" nA=%d tau=%d\n",na+1,t);} }
    dfs(len+1,nd,na+(v>0));} }
int main(int c,char**v){int L=atoi(v[1]);LY=atoi(v[2]);
 for(long m=0;m<(1L<<L);m++){ q0=L; F[0]=G[0]=0; for(int i=0;i<L;i++){s[i]=((m>>i)&1)?1:-1;F[i+1]=F[i]+s[i];G[i+1]=G[i]+F[i+1];}
  dw=0; int ok=1; for(int b=0;b<L;b++){ if(s[b]<0) dw++; else if(tauof(b)>=0) dw--; if(dw<0){ok=0;break;}} if(!ok||dw!=2) continue;
  dfs(L,2,0);}
 printf("L=%d LY=%d maxA=%d ; counts of A-index reached:",L,LY,maxa); for(int i=1;i<20;i++)printf(" %ld",cntA[i]); printf("\n");}
