// d=D: enumerate w, DFS y; record max y depth and print leaves (dead ends) distribution of y words.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int q0,LY,amax,dw,D,k1; int s[256],F[257],G[257]; int maxd=0; long leaves=0;
int tauof(int b){ for(int t=b-3;t>=0;t-=4) if(F[b]==F[t]+1 && G[b]-G[t]==(b-t)*F[t]) return t; return -1;}
int verbose;
void dfs(int len,int ay,int X,int dq){
  if(len-q0>maxd){maxd=len-q0;}
  if(verbose && len-q0>=verbose){ for(int i=0;i<len;i++){if(i==k1)putchar('^');if(i==q0)putchar('|');putchar(s[i]>0?'A':'S');} printf(" X=%d ay=%d dq=%d\n",X,ay,dq); }
  if(len-q0>=LY) return;
  for(int v=-1;v<=1;v+=2){
    s[len]=v; F[len+1]=F[len]+v; G[len+1]=G[len]+F[len+1];
    int nay=ay,nX=X,ndq=dq;
    if(v<0) ndq=dq+1;
    else { int t=tauof(len); if(t<0){nay++; if(nay>amax) continue;} else { ndq=dq-1; if(ndq<0) continue; if(t<q0) nX++; } }
    dfs(len+1,nay,nX,ndq);
  }
}
int main(int argc,char**argv){int L=atoi(argv[1]); LY=atoi(argv[2]); D=atoi(argv[3]); verbose=argc>4?atoi(argv[4]):0;
 for(long m=0;m<(1L<<L);m++){ q0=L; F[0]=G[0]=0;
   for(int i=0;i<L;i++){ s[i]=((m>>i)&1)?1:-1; F[i+1]=F[i]+s[i]; G[i+1]=G[i]+F[i+1]; }
   dw=0; int ok=1; k1=0; for(int b=0;b<q0;b++){ if(s[b]<0) dw++; else if(tauof(b)>=0) dw--; if(dw<0){ok=0;break;} if(dw==0)k1=b+1; }
   if(!ok||dw!=D) continue; amax=2-D; dfs(q0,0,0,dw); }
 printf("maxdepth=%d\n",maxd);
}
