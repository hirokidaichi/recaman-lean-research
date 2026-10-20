// DFS over y given prefix w. p=0, q0=|w|. d = #S(w) - #endable(w) (computed). Budget a_y <= amax = 2-d.
// Pruning: every A in y has tau<0 counts toward a_y (<= amax); cap d(q)>=0 (H at p on prefixes).
// Completion: A at b with tau_b == q0. Report completions with X>0 (or y != SAAA).
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int n, q0, h2, LY, amax, dw; int s[256], F[257], G[257];
long nodes=0, comps=0, bad=0, shown=0;
int tauof(int b){ for(int t=b-3;t>=0;t-=4) if(F[b]==F[t]+1 && G[b]-G[t]==(b-t)*F[t]) return t; return -1;}
void pr(int len,const char*tag,int X,int ay){ for(int i=0;i<len;i++){if(i==q0)putchar('|');putchar(s[i]>0?'A':'S');} printf(" %s X=%d ay=%d d=%d\n",tag,X,ay,dw);}
long early=0, earlyshown=0, strad=0; int maxjst=0;
void dfs(int len,int ay,int X,int dq){ // len = current length, dq = d(len)
  nodes++;
  if(len-q0>=LY) return;
  for(int v=-1;v<=1;v+=2){
    s[len]=v; F[len+1]=F[len]+v; G[len+1]=G[len]+F[len+1];
    int nay=ay,nX=X,ndq=dq, comp=0;
    if(v<0){ ndq=dq+1; }
    else { int t=tauof(len); if(t<0){ nay++; if(nay>amax) continue; } else { ndq=dq-1; if(ndq<0) continue; if(t<q0){ nX++; strad++; int reached=0; for(int u=q0+1;u<=len;u++) if(F[u]>=h2) reached=1; if(!reached && dw==0){ early++; if(earlyshown<8){earlyshown++; pr(len+1,"EARLY-STRAD",nX,nay);} } } if(t==q0) comp=1; } }
    if(comp){ comps++; int isS=(len+1-q0==4 && s[q0]<0 && s[q0+1]>0 && s[q0+2]>0);
      if(!isS || nX>dw){ bad++; if(shown<30){shown++; pr(len+1, isS?"SAAA-but-X":"NONSAAA", nX, nay);} } }
    dfs(len+1,nay,nX,ndq);
  }
}
int main1(char*w,int ly){
  LY=ly; nodes=comps=0; q0=strlen(w); F[0]=0;G[0]=0;
  for(int i=0;i<q0;i++){ s[i]=w[i]=='A'?1:-1; F[i+1]=F[i]+s[i]; G[i+1]=G[i]+F[i+1]; }
  h2=F[q0]; dw=0; for(int b=0;b<q0;b++){ if(s[b]<0) dw++; else if(tauof(b)>=0) dw--; if(dw<0)return 0; }
  amax=2-dw; if(amax<0)return 0;
  dfs(q0,0,0,dw);
  return 1;
}

long tot[3],totc[3],maxnodes;
int main(int argc,char**argv){int L=atoi(argv[1]),ly=atoi(argv[2]); char w[64];
 for(long m=0;m<(1L<<L);m++){ for(int i=0;i<L;i++) w[i]=((m>>i)&1)?'A':'S'; w[L]=0;
   if(main1(w,ly)){ tot[dw]++; totc[dw]+=comps; if(nodes>maxnodes)maxnodes=nodes; } }
 printf("Lw=%d LY=%d: w's with d=0,1,2: %ld %ld %ld ; completions %ld %ld %ld ; bad=%ld maxnodes=%ld strad=%ld early=%ld\n",L,ly,tot[0],tot[1],tot[2],totc[0],totc[1],totc[2],bad,maxnodes,strad,early);}
