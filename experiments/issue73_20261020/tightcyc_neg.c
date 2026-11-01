// Periodic EqClass_L: every cycle in the V-tight subgraph on full states (len=L) reads a bi-infinite block word
// (SAAA|SSAAAASAAA|A)^Z with endable A's exactly at block members (unique window).
// Method: SCCs of tight full-state graph; subset-DFA product restricted to intra-SCC edges, from full subset; report if
// the empty subset is reachable (a factor of some cycle word that is not a factor of any block word).
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int L;
static inline long idx(int len,unsigned bits){ return ((long)1<<len)-1+bits; }
int nwin(int len,unsigned bits){ int c=0; for(int d=3; d<=len; d+=4){ long mass=0, mom=0; for(int i=0;i<d;i++){ int s=((bits>>i)&1)?1:-1; mass+=s; mom+=(long)(i+1)*s; } if(mass==1&&mom==0) c++; } return c; }
int dfa(int st,char c){
  switch(st){
   case 0: if(c=='a') return 0; if(c=='S') return 1; return -1;
   case 1: if(c=='a') return 2; if(c=='S' && !getenv("NOTRIPLE")) return 10; return -1;
   case 2: if(c=='a') return 3; return -1;
   case 3: if(c=='1') return 0; return -1;
   case 10: if(c=='a') return 11; return -1;
   case 11: if(c=='a') return 12; return -1;
   case 12: if(c=='1') return 13; return -1;
   case 13: if(c=='a') return 14; return -1;
   case 14: if(c=='S') return 15; return -1;
   case 15: if(c=='1') return 16; return -1;
   case 16: if(c=='a') return 17; return -1;
   case 17: if(c=='1') return 0; return -1;
  } return -1; }
int dinv[12]={0,1,2,3,10,11,12,13,14,15,16,17}; int dmap[18];
int stepset(int set,char c){ int out=0; for(int k=0;k<12;k++) if(set>>k&1){ int n=dfa(dinv[k],c); if(n>=0) out|=1<<dmap[n]; } return out; }
int main(int c,char**v){ L=atoi(v[1]); long N=((long)1<<(L+1))-1; for(int k=0;k<12;k++) dmap[dinv[k]]=k;
  signed char *nw=malloc(N); unsigned char *V=calloc(N,1);
  for(int len=0;len<=L;len++) for(unsigned b=0;b<(1u<<len);b++) nw[idx(len,b)]=nwin(len,b);
  int changed=1; while(changed){ changed=0;
    for(int len=L;len>=0;len--) for(unsigned b=0;b<(1u<<len);b++){ long i=idx(len,b); int best=0;
      for(int a=0;a<2;a++){ int nl=len<L?len+1:L; unsigned nb=((b<<1)|a)&((1u<<nl)-1); int ch=a?(nw[i]?1:0):-1; int val=ch+V[idx(nl,nb)]; if(val>best) best=val; }
      if(best>V[i]){ V[i]=best; changed=1; } } }
  unsigned M=1u<<L; long base=idx(L,0);
  // tight edges among full states: edge u->w (w = (u<<1|a)&mask) tight if ch+V[w]==V[u]
  #define TIGHT(u,a) ( ((a)?(nw[base+(u)]?1:0):-1) + V[base+((((u)<<1)|(a))&(M-1))] == V[base+(u)] )
  // Tarjan iterative
  int *index=malloc(sizeof(int)*M), *low=malloc(sizeof(int)*M), *comp=malloc(sizeof(int)*M); char *onst=calloc(M,1);
  unsigned *st=malloc(sizeof(unsigned)*M); unsigned *cs=malloc(sizeof(unsigned)*M); char *ci=malloc(M);
  for(unsigned u=0;u<M;u++){index[u]=-1;comp[u]=-1;}
  int idc=0, ncomp=0; long sp=0, csp=0; long tightE=0;
  for(unsigned s=0;s<M;s++){ if(index[s]>=0) continue;
    cs[csp]=s; ci[csp]=0; csp++; index[s]=low[s]=idc++; st[sp++]=s; onst[s]=1;
    while(csp){ unsigned u=cs[csp-1]; int a=ci[csp-1];
      if(a<2){ ci[csp-1]++; if(!TIGHT(u,a)) continue; tightE++; unsigned w=((u<<1)|a)&(M-1);
        if(index[w]<0){ index[w]=low[w]=idc++; st[sp++]=w; onst[w]=1; cs[csp]=w; ci[csp]=0; csp++; }
        else if(onst[w] && index[w]<low[u]) low[u]=index[w]; }
      else { csp--; if(csp){ unsigned p=cs[csp-1]; if(low[u]<low[p]) low[p]=low[u]; }
        if(low[u]==index[u]){ unsigned w; do{ w=st[--sp]; onst[w]=0; comp[w]=ncomp; }while(w!=u); ncomp++; } } } }
  // nontrivial: comp with an internal tight edge
  char *nontriv=calloc(ncomp,1); long ntnodes=0;
  for(unsigned u=0;u<M;u++) for(int a=0;a<2;a++) if(TIGHT(u,a)){ unsigned w=((u<<1)|a)&(M-1); if(comp[w]==comp[u]) nontriv[comp[u]]=1; }
  for(unsigned u=0;u<M;u++) if(nontriv[comp[u]]) ntnodes++;
  printf("L=%d tight edges(full)=%ld SCCs=%d nodes in nontrivial SCCs=%ld\n",L,tightE,ncomp,ntnodes);
  // product BFS: (u, set) ; visited via hash of 12-bit sets per node: use array of small lists -> simple: bitmap of 4096 per node too big; use per-node visited sets stored as dynamic? nodes few hopefully.
  long bad=0, visited=0;
  for(unsigned s=0;s<M;s++){ if(!nontriv[comp[s]]) continue;
    // DFS from (s, full) inside comp
    // local visited via open-addressing hash
    static unsigned long *H=NULL; static long HC=1<<22; if(!H) H=malloc(sizeof(unsigned long)*HC); memset(H,0xff,sizeof(unsigned long)*HC);
    static unsigned long *stk=NULL; if(!stk) stk=malloc(sizeof(unsigned long)*(1<<24)); long tp=0;
    unsigned long key=((unsigned long)s<<12)|0xfff; stk[tp++]=key;
    while(tp){ unsigned long k=stk[--tp]; unsigned long h=(k*11400714819323198485ul)>>42; while(H[h&(HC-1)]!=~0ul && H[h&(HC-1)]!=k) h++; if(H[h&(HC-1)]==k) continue; H[h&(HC-1)]=k; visited++;
      unsigned u=k>>12; int set=k&0xfff;
      for(int a=0;a<2;a++){ if(!TIGHT(u,a)) continue; unsigned w=((u<<1)|a)&(M-1); if(comp[w]!=comp[u]) continue;
        char lab=!a?'S':(nw[base+u]==0?'a':(nw[base+u]==1?'1':'2')); int ns=stepset(set,lab);
        if(ns==0){ bad++; if(bad<4) printf("BAD factor from start %x at node %x lab %c\n",s,u,lab); continue; }
        stk[tp++]=((unsigned long)w<<12)|ns; } }
    if(bad) break; }
  printf("product visited=%ld bad=%ld\n",visited,bad); return bad?3:0; }
