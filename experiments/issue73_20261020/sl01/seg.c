#include <stdio.h>
#include <stdlib.h>
int s[64],F[65],G[65];
int tauof(int b){ for(int t=b-3;t>=0;t-=4) if(F[b]==F[t]+1 && G[b]-G[t]==(b-t)*F[t]) return t; return -1;}
int main(int argc,char**argv){int L=atoi(argv[1]);
 for(long m=0;m<(1L<<L);m++){ F[0]=G[0]=0;
   for(int i=0;i<L;i++){ s[i]=((m>>i)&1)?1:-1; F[i+1]=F[i]+s[i]; G[i+1]=G[i]+F[i+1]; }
   int dw=0,ok=1,k1=0; for(int b=0;b<L;b++){ if(s[b]<0) dw++; else if(tauof(b)>=0) dw--; if(dw<0){ok=0;break;} if(dw==0)k1=b+1; }
   if(!ok||dw!=1) continue; for(int i=k1;i<L;i++) putchar(s[i]>0?'A':'S'); printf(" k1=%d\n", k1>0); }
}
