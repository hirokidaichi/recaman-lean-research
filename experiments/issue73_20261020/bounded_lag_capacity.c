// Independent check of H_L: on any interval, #A-clocks ending a P2 window of length <= L inside the interval <= #S.
// States: (len<=L, last len bits; bit i = clock z-1-i, 1=A). Forward max-plus relaxation from empty state.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int L; 
static inline long idx(int len,unsigned bits){ return (1u<<len)-1+bits; }
int endable(int len,unsigned bits){ // window of last d bits, d<=len, d=3,7,..
  for(int d=3; d<=len; d+=4){ long mass=0, mom=0; for(int i=0;i<d;i++){ int s=((bits>>i)&1)?1:-1; mass+=s; mom+=(long)(i+1)*s; } if(mass==1&&mom==0) return 1; }
  return 0; }
int main(int c,char**v){ L=atoi(v[1]); long N=(1L<<(L+1))-1; int *D=malloc(sizeof(int)*N); signed char *en=malloc(N); if(!D||!en){puts("oom");return 2;}
  for(long i=0;i<N;i++) D[i]=-1000000;
  for(int len=0;len<=L;len++) for(unsigned b=0;b<(1u<<len);b++) en[idx(len,b)]=endable(len,b);
  D[0]=0; int changed=1, it=0, maxD=0;
  while(changed && it<10000){ changed=0; it++;
    for(int len=0;len<=L;len++) for(unsigned b=0;b<(1u<<len);b++){ long i=idx(len,b); if(D[i]<-999999) continue;
      for(int a=0;a<2;a++){ int nl = len<L? len+1 : L; unsigned nb = ((b<<1)|a) & ((1u<<nl)-1);
        int ch = a ? (en[i]?1:0) : -1; long j=idx(nl,nb); int val=D[i]+ch; if(val>D[j]){D[j]=val;changed=1; if(val>maxD) maxD=val;} } }
    if(maxD>0){ printf("VIOLATION maxD=%d it=%d\n",maxD,it); return 1; } }
  printf("L=%d iterations=%d converged=%d max cumulative charge=%d\n",L,it,!changed,maxD); }
