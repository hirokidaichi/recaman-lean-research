#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int q0,LY,amax,dw,D,k1; int s[256],F[257],G[257];
int tauof(int b){ for(int t=b-3;t>=0;t-=4) if(F[b]==F[t]+1 && G[b]-G[t]==(b-t)*F[t]) return t; return -1;}
void pr(int len,int t,const char*tag){ for(int i=0;i<len;i++){if(i==k1)putchar('^');if(i==q0)putchar('|');if(i==t)putchar('[');putchar(s[i]>0?'A':'S');} printf(" %s\n",tag);}
void dfs(int len,int ay,int X,int dq){
  if(len-q0>=LY) return;
  for(int v=-1;v<=1;v+=2){
    s[len]=v; F[len+1]=F[len]+v; G[len+1]=G[len]+F[len+1];
    int nay=ay,nX=X,ndq=dq;
    if(v<0) ndq=dq+1;
    else { int t=tauof(len); if(t<0){nay++; if(nay>amax) continue;} else { ndq=dq-1; if(ndq<0) continue; if(t<q0){ nX++; char b[80]; sprintf(b,"STRAD len=%d at y+%d ay=%d",q0-t+len-q0,len-q0,nay); pr(len+1,t,b);} } }
    dfs(len+1,nay,nX,ndq);
  }
}
int main(int argc,char**argv){int L=atoi(argv[1]); LY=atoi(argv[2]); D=atoi(argv[3]);
 for(long m=0;m<(1L<<L);m++){ q0=L; F[0]=G[0]=0;
   for(int i=0;i<L;i++){ s[i]=((m>>i)&1)?1:-1; F[i+1]=F[i]+s[i]; G[i+1]=G[i]+F[i+1]; }
   dw=0; int ok=1; k1=0; for(int b=0;b<q0;b++){ if(s[b]<0) dw++; else if(tauof(b)>=0) dw--; if(dw<0){ok=0;break;} if(dw==0)k1=b+1; }
   if(!ok||dw!=D) continue; amax=2-D; dfs(q0,0,0,dw); }
}
