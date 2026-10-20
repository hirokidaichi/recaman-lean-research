// memory-lean version of potL.c for large L. V uint8, endable bits precomputed.
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
int L;
static int endable(int l, uint32_t bits){
  int F[64]; F[0]=0; for(int i=0;i<l;i++) F[i+1]=F[i]+(((bits>>i)&1)?1:-1);
  long G[64]; G[0]=0; for(int i=1;i<=l;i++) G[i]=G[i-1]+F[i];
  for(int t=l-3;t>=0 && l-t<=L;t-=4) if(F[l]==F[t]+1 && G[l]-G[t]==(long)(l-t)*F[t]) return 1;
  return 0;
}
static inline uint64_t nxt(int l, uint32_t b, int a){ uint32_t nb; int nl;
  if(l<L){nl=l+1; nb=b|((uint32_t)a<<l);} else {nl=L; nb=(b>>1)|((uint32_t)a<<(L-1));}
  return ((uint64_t)1<<nl)-1+nb; }
int main(int c,char**v){
  L=atoi(v[1]); uint64_t N=((uint64_t)1<<(L+1))-1;
  uint8_t *V=calloc(N,1); uint8_t *E=calloc(N/8+1,1); uint8_t *lenof=NULL;
  for(int l=0;l<=L;l++) for(uint64_t b=0;b<((uint64_t)1<<l);b++){ uint64_t q=((uint64_t)1<<l)-1+b; if(endable(l,(uint32_t)b)) E[q>>3]|=1<<(q&7); }
  fprintf(stderr,"precomputed\n");
  int it;
  for(it=0;it<1000;it++){ long changed=0;
    for(int l=L;l>=0;l--) for(int64_t b=((int64_t)1<<l)-1;b>=0;b--){ uint64_t q=((uint64_t)1<<l)-1+b;
      int e=(E[q>>3]>>(q&7))&1;
      int w1 = e + V[nxt(l,(uint32_t)b,1)];
      int w0 = -1 + V[nxt(l,(uint32_t)b,0)];
      int best=0; if(w1>best)best=w1; if(w0>best)best=w0;
      if(best!=V[q]){V[q]=best;changed++;} }
    fprintf(stderr,"sweep %d changed %ld\n",it,changed);
    if(!changed) break; }
  printf("L=%d sweeps=%d V(empty)=%d\n",L,it,V[0]);
  int mx=0; long hist[256]={0};
  for(uint64_t b=0;b<((uint64_t)1<<L);b++){int x=V[((uint64_t)1<<L)-1+b]; hist[x]++; if(x>mx)mx=x;}
  printf("full states: maxV=%d hist:",mx); for(int i=0;i<=mx;i++) printf(" %d:%ld",i,hist[i]); printf("\n");
  // verify certificate independently of iteration: local inequalities
  long bad=0;
  for(int l=0;l<=L;l++) for(uint64_t b=0;b<((uint64_t)1<<l);b++){ uint64_t q=((uint64_t)1<<l)-1+b;
    int e=(E[q>>3]>>(q&7))&1; if(e+V[nxt(l,b,1)]>V[q]) bad++; if(-1+V[nxt(l,b,0)]>V[q]) bad++; }
  printf("certificate check: violations=%ld\n",bad);
}
