// EqClass_L for all spans: equality words of H_L are exactly tight paths w.r.t. the backward potential V.
// Check every tight path from the empty state that ends (via an endable-A step) at a V=0 state parses as
// (SAAA|SSAAAASAAA|A)* with endable A's exactly at block members, each having exactly one P2 window (len<=L, start>=p).
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int L;
static inline long idx(int len,unsigned bits){ return ((long)1<<len)-1+bits; }
int nwin(int len,unsigned bits){ int c=0; for(int d=3; d<=len; d+=4){ long mass=0, mom=0; for(int i=0;i<d;i++){ int s=((bits>>i)&1)?1:-1; mass+=s; mom+=(long)(i+1)*s; } if(mass==1&&mom==0) c++; } return c; }
// DFA: state 0 = block boundary. labels: 'S', 'a' (A non-endable), '1' (A endable unique), '2' (A endable multi)
// SAAA: S a a 1 ; triple: S S a a 1 a S 1 a 1 ; free: a
// states: 0 boundary; after S:1 ; after SA: 2; SAA:3 ; after SS: 10, SSa:11, SSaa:12, SSaa1:13, SSaa1a:14, ..S:15, ..S1:16, ..S1a:17
int dfa(int st,char c){
  switch(st){
   case 0: if(c=='a') return 0; if(c=='S') return 1; return -1;
   case 1: if(c=='a') return 2; if(c=='S') return 10; return -1;
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
int dmap[18]={0,1,2,3,-1,-1,-1,-1,-1,-1,4,5,6,7,8,9,10,11}; // compress to 12 + dead(12)
int dinv[12]={0,1,2,3,10,11,12,13,14,15,16,17};
int main(int c,char**v){ L=atoi(v[1]); long N=((long)1<<(L+1))-1;
  signed char *nw=malloc(N); unsigned char *V=malloc(N);
  for(int len=0;len<=L;len++) for(unsigned b=0;b<(1u<<len);b++) nw[idx(len,b)]=nwin(len,b);
  memset(V,0,N); int changed=1,it=0;
  while(changed){ changed=0; it++;
    for(int len=L;len>=0;len--) for(unsigned b=0;b<(1u<<len);b++){ long i=idx(len,b); int best=0;
      for(int a=0;a<2;a++){ int nl=len<L?len+1:L; unsigned nb=((b<<1)|a)&((1u<<nl)-1); int ch=a?(nw[i]?1:0):-1; int val=ch+V[idx(nl,nb)]; if(val>best) best=val; }
      if(best>V[i]){ if(best>100){puts("diverge");return 1;} V[i]=best; changed=1; } } }
  printf("L=%d V iterations=%d V(empty)=%d\n",L,it,V[0]);
  if(V[0]!=0) return 1;
  // BFS over product (graph state, dfa state 0..12 where 12=dead) along tight edges
  unsigned char *vis=calloc(N,2); // 13 bits per state -> use uint16
  unsigned short *vs=(unsigned short*)vis; 
  long *queue=malloc(sizeof(long)*64*1024*1024); // will grow? use stack of (i,d)
  long qh=0,qt=0, cap=64L*1024*1024; 
  #define PUSH(i,d) do{ if(!(vs[i]&(1<<(d)))){ vs[i]|=(1<<(d)); if(qt>=cap){puts("queue overflow");return 2;} queue[qt++]=((i)<<4)|(d);} }while(0)
  // need len,bits from index: store via decode
  PUSH(0L,0);
  long viol=0, eqends=0;
  while(qh<qt){ long it2=queue[qh++]; long i=it2>>4; int d=it2&15;
    // decode i -> len,bits
    int len=0; while((((long)1<<(len+1))-1)<=i) len++; unsigned b=(unsigned)(i-(((long)1<<len)-1));
    for(int a=0;a<2;a++){ int nl=len<L?len+1:L; unsigned nb=((b<<1)|a)&((1u<<nl)-1); long j=idx(nl,nb);
      int ch=a?(nw[i]?1:0):-1; if(ch+V[j]!=V[i]) continue; // not tight
      char lab = !a ? 'S' : (nw[i]==0?'a':(nw[i]==1?'1':'2'));
      int nd = (d==12)?12: dmap[ dfa(dinv[d],lab)<0 ? 4 : dfa(dinv[d],lab) ];
      if(d!=12 && dfa(dinv[d],lab)<0) nd=12;
      if(a && nw[i] && V[j]==0){ eqends++; if(nd!=0){ viol++; if(viol<5) printf("VIOLATION at state len=%d bits=%x dfa=%d lab=%c\n",len,b,d,lab);} }
      PUSH(j,nd); } }
  printf("product states visited=%ld equality endpoints=%ld violations=%ld\n",qt,eqends,viol);
  return viol?3:0; }
