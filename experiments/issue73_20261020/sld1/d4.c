// check Y: endables in [k1,k) (z or y) whose all windows start < k1. Also print z of completions.
#include <stdio.h>
#include <stdlib.h>
int s[256],F[257],G[257]; int q0,h2,k1,LW,LY; long Yz=0,Yy=0,comps=0;
int tauof(int b){ for(int t=b-3;t>=0;t-=4) if(F[b]==F[t]+1 && G[b]-G[t]==(b-t)*F[t]) return t; return -1;}
void pr(int len){ for(int i=0;i<len;i++){ if(i==k1)putchar('^'); if(i==q0)putchar('|'); putchar(s[i]>0?'A':'S'); } }
int zY; // whether z has a Y-endable
void dfsy(int len,int ay,int d){
  if(len-q0>=LY) return;
  for(int v=-1;v<=1;v+=2){
    s[len]=v; F[len+1]=F[len]+v; G[len+1]=G[len]+F[len+1];
    int nay=ay,nd=d,comp=0,t=-1;
    if(v<0) nd=d+1; else { t=tauof(len); if(t<0){ nay++; if(nay>1) continue; } else { nd=d-1; if(nd<0) continue; if(t<k1){Yy++; if(Yy<6){printf("Yy ");pr(len+1);printf("\n");}} if(t==q0) comp=1; } }
    if(comp){ comps++; if(zY){printf("COMP with zY ");pr(len+1);printf("\n");} printf("CZ "); for(int i=k1;i<q0;i++)putchar(s[i]>0?'A':'S'); printf("|"); for(int i=q0;i<=len;i++)putchar(s[i]>0?'A':'S'); printf("\n"); }
    else dfsy(len+1,nay,nd);
  }
}
void dfsw(int len,int d,int lastz){
  if(d==1 && len>0){ q0=len; h2=F[len]; k1=lastz; zY=0; for(int b=k1;b<q0;b++) if(s[b]>0){int t=tauof(b); if(t>=0&&t<k1) zY=1;} if(zY)Yz++; dfsy(len,0,1); }
  if(len>=LW) return;
  for(int v=-1;v<=1;v+=2){
    s[len]=v; F[len+1]=F[len]+v; G[len+1]=G[len]+F[len+1];
    int nd=d; if(v<0) nd++; else if(tauof(len)>=0) nd--; if(nd<0) continue;
    dfsw(len+1,nd,nd==0?len+1:lastz);
  }
}
int main(int c,char**v){ LW=atoi(v[1]); LY=atoi(v[2]); F[0]=G[0]=0; dfsw(0,0,0);
  printf("Yz(w with z-endable windowed from beta)=%ld Yy=%ld comps=%ld\n",Yz,Yy,comps); }
