// case (ii): d(q0)=1, a_y<=1, d>=0. For each w: max F-h2 over y-prefixes; and record y-prefix reaching h2+1 (first time).
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int q0,h2,LY,k1; int s[256],F[257],G[257]; int mx; char seg[64];
int tauof(int b){ for(int t=b-3;t>=0;t-=4) if(F[b]==F[t]+1 && G[b]-G[t]==(b-t)*F[t]) return t; return -1;}
int shown=0;
void dfs(int len,int ay,int dq){
  if(len-q0>=LY) return;
  for(int v=-1;v<=1;v+=2){
    s[len]=v; F[len+1]=F[len]+v; G[len+1]=G[len]+F[len+1];
    int nay=ay,ndq=dq;
    if(v<0) ndq++; else { int t=tauof(len); if(t<0){nay++; if(nay>1) continue;} else { ndq--; if(ndq<0) continue; } }
    if(F[len+1]-h2>mx) mx=F[len+1]-h2;
    if(F[len+1]==h2+1){ printf("REACH seg=%s y=",seg); for(int i=q0;i<=len;i++)putchar(s[i]>0?'A':'S'); printf("\n"); continue;}
    dfs(len+1,nay,ndq);
  }
}
int main(int argc,char**argv){int L=atoi(argv[1]); LY=atoi(argv[2]);
 for(long m=0;m<(1L<<L);m++){ q0=L; F[0]=G[0]=0;
   for(int i=0;i<L;i++){ s[i]=((m>>i)&1)?1:-1; F[i+1]=F[i]+s[i]; G[i+1]=G[i]+F[i+1]; }
   int dw=0,ok=1; k1=0; for(int b=0;b<q0;b++){ if(s[b]<0) dw++; else if(tauof(b)>=0) dw--; if(dw<0){ok=0;break;} if(dw==0)k1=b+1;}
   if(!ok||dw!=1) continue; h2=F[q0]; int n=0; for(int i=k1;i<q0;i++) seg[n++]=s[i]>0?'A':'S'; seg[n]=0; mx=-99; dfs(q0,0,1);
   printf("MAX seg=%s k1>0=%d max=%d\n",seg,k1>0,mx); }
}
