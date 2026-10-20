// Residual a_z=2: x = w z SAAA, w prefix-H with d(|w|)=0 (k1=|w|), z: S-start, mass +1, area Z1=-1 rel F(k1), len n = 1 mod 4.
// Conditions: d>=0 on w; d>=1 on (k1,k-1]; d(k)=0; a_z=2; tau(q0+3)=q0. Report histogram of failures (first failing).
#include <stdio.h>
#include <stdlib.h>
int s[256],F[257],G[257]; int LW,NZ; long fail[10]; long tot=0;
int tauof(int b){ for(int t=b-3;t>=0;t-=4) if(F[b]==F[t]+1 && G[b]-G[t]==(b-t)*F[t]) return t; return -1;}
void setc(int i,int v){ s[i]=v; F[i+1]=F[i]+v; G[i+1]=G[i]+F[i+1]; }
int Dw[257];
void tryz(int k1,int n){ // enumerate z of length n
  for(long m=0;m<(1L<<n);m++){ if(m&1) continue; // first clock S (bit0=0 means S)
    int fs=0,ar=0; for(int i=0;i<n;i++){ int v=(m>>i)&1?1:-1; fs+=v; ar+=fs; } if(fs!=1||ar!=-1) continue;
    for(int i=0;i<n;i++) setc(k1+i,(m>>i)&1?1:-1);
    int q0=k1+n; setc(q0,-1); setc(q0+1,1); setc(q0+2,1); setc(q0+3,1); int k=q0+4;
    tot++; int d=0,az=0,code=0;
    for(int i=k1;i<k;i++){ if(s[i]<0) d++; else { int t=tauof(i); if(t<0){ if(i<q0) az++; } else d--; }
      if(i+1<k && d<1){ code=1; break;} }
    if(!code && az!=2) code=2;
    if(!code && d!=0) code=3;
    if(!code && tauof(q0+3)!=q0) code=4;
    if(!code && tauof(q0+1)>=0) code=5;
    if(!code){ code=9; for(int i=0;i<k;i++){ if(i==k1)putchar('['); if(i==q0)putchar('|'); putchar(s[i]>0?'A':'S'); } printf(" tau(b1)=%d\n",tauof(q0+2)); }
    fail[code]++;
  }
}
void dfsw(int len){
  if(Dw[len]==0) for(int n=5;n<=NZ;n+=4) tryz(len,n);
  if(len>=LW) return;
  for(int v=-1;v<=1;v+=2){ setc(len,v); int nd=Dw[len]; if(v<0) nd++; else if(tauof(len)>=0) nd--; if(nd<0) continue; Dw[len+1]=nd; dfsw(len+1); }
}
int main(int c,char**v){ LW=atoi(v[1]); NZ=atoi(v[2]); dfsw(0); printf("tot=%ld",tot); for(int i=0;i<10;i++) printf(" f%d=%ld",i,fail[i]); printf("\n"); }
