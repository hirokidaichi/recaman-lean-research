// case d=1 (or d given). For each w with d(q0)=D, DFS y with a_y<=2-D, d>=0.
// Print first examples of: X>=2 events; straddler windows (t, k1, w-part, y-part).
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int q0,h2,LY,amax,dw,k1,D; int s[256],F[257],G[257];
long xs2=0,shown2=0,stradn=0,comps=0,bad=0; long hist[64][64];
int tauof(int b){ for(int t=b-3;t>=0;t-=4) if(F[b]==F[t]+1 && G[b]-G[t]==(b-t)*F[t]) return t; return -1;}
void pr(int len,int t,const char*tag){ for(int i=0;i<len;i++){if(i==k1)putchar('^');if(i==q0)putchar('|');if(i==t)putchar('[');putchar(s[i]>0?'A':'S');} printf(" %s\n",tag);}
int maxX=0;
void dfs(int len,int ay,int X,int dq){
  if(len-q0>=LY) return;
  for(int v=-1;v<=1;v+=2){
    s[len]=v; F[len+1]=F[len]+v; G[len+1]=G[len]+F[len+1];
    int nay=ay,nX=X,ndq=dq,comp=0;
    if(v<0) ndq=dq+1;
    else { int t=tauof(len); if(t<0){nay++; if(nay>amax) continue;} else { ndq=dq-1; if(ndq<0) continue;
       if(t<q0){ nX++; stradn++; hist[q0-t][len-q0]++; if(nX>=2){ xs2++; if(shown2<15){shown2++; char b[64]; sprintf(b,"X=%d ay=%d",nX,nay); pr(len+1,t,b);} } }
       if(t==q0) comp=1; } }
    if(comp){ comps++; char b[64]; sprintf(b,"COMP X=%d ay=%d",nX,nay); if(nX>D || len+1-q0!=4){bad++;} static int sc=0; if(sc<40){sc++;pr(len+1,-1,b);} }
    dfs(len+1,nay,nX,ndq);
  }
}
int main(int argc,char**argv){int L=atoi(argv[1]); LY=atoi(argv[2]); D=atoi(argv[3]); char w[64];
 for(long m=0;m<(1L<<L);m++){ q0=L; F[0]=G[0]=0;
   for(int i=0;i<L;i++){ s[i]=((m>>i)&1)?1:-1; F[i+1]=F[i]+s[i]; G[i+1]=G[i]+F[i+1]; }
   h2=F[q0]; dw=0; int ok=1; k1=0; for(int b=0;b<q0;b++){ if(s[b]<0) dw++; else if(tauof(b)>=0) dw--; if(dw<0){ok=0;break;} if(dw==0) k1=b+1; }
   if(!ok||dw!=D) continue; amax=2-D;
   dfs(q0,0,0,dw); }
 printf("L=%d LY=%d D=%d: straddlers=%ld X>=2 events=%ld comps=%ld bad=%ld\n",L,LY,D,stradn,xs2,comps,bad);
 for(int a=0;a<64;a++)for(int b=0;b<64;b++) if(hist[a][b]) printf(" q0-t=%d, b-q0=%d : %ld\n",a,b,hist[a][b]);
}
