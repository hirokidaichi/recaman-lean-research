// Independent periodic brute force: all words w of period P (bi-infinite w^Z), window bound L.
// endable b (sig=+1): exists d in 1..L with window [b-d,b-1]: sum sig = 1, sum sig(c)*(b-c) = 0.
// periodic H: e <= s per period. equality: w^Z admits a parse in (SAAA|SSAAAASAAA|A)^Z, labels exact, unique windows.
#include <stdio.h>
#include <stdlib.h>
static int L,P,NOTRIPLE=0; static int sg[64], lab[64]; // lab: 0 = S, 1 = A nonendable, 2 = A unique, 3 = A multi
// DFA over labels, states as in grammar: 0 boundary
static int step(int q,int l){
  switch(q){
   case 0: return l==1?0: l==0?1:-1;
   case 1: return l==1?2: (l==0&&!NOTRIPLE)?10:-1;
   case 2: return l==1?3:-1;
   case 3: return l==2?0:-1;
   case 10: return l==1?11:-1; case 11: return l==1?12:-1; case 12: return l==2?13:-1;
   case 13: return l==1?14:-1; case 14: return l==0?15:-1; case 15: return l==2?16:-1;
   case 16: return l==1?17:-1; case 17: return l==2?0:-1; }
  return -1; }
static int cycparse(void){
  for(int r=0;r<P;r++){ int q=0; for(int k=1;k<=10*P+12;k++){ q=step(q,lab[(r+k-1)%P]); if(q<0) break; if(q==0 && k%P==0) return 1; } }
  return 0; }
int main(int argc,char**argv){ L=atoi(argv[1]); int PMAX=atoi(argv[2]); if(argc>3) NOTRIPLE=1;
  for(P=1;P<=PMAX;P++){ long neq=0,nviol=0,nh=0;
    for(unsigned long m=0;m<(1ul<<P);m++){
      for(int i=0;i<P;i++) sg[i]=(m>>i&1)?1:-1;
      int e=0,s=0;
      for(int b=0;b<P;b++){ if(sg[b]<0){ lab[b]=0; s++; continue; }
        int c=0; long mass=0,mom=0;
        for(int d=1;d<=L;d++){ int x=sg[((b-d)%P+P)%P]; mass+=x; mom+=(long)x*d; if(mass==1&&mom==0) c++; }
        lab[b]= c==0?1: c==1?2:3; if(c) e++; }
      if(e>s){ nh++; continue; }
      if(e==s){ neq++; if(!cycparse()){ nviol++; if(nviol<3){ printf(" viol P=%d ",P); for(int i=0;i<P;i++) putchar(sg[i]>0?'A':'S'); puts(""); } } }
    }
    printf("L=%d P=%d eq=%ld viol=%ld Hfail=%ld\n",L,P,neq,nviol,nh); fflush(stdout); }
  return 0; }
