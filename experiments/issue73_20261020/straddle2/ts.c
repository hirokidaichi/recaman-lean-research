// Lemma TS check: all strings of length n with last clock b2=n-1 endable (from 0); b1 = previous A; if b1 endable:
// q* = start of S-run before b1 (q*-1 is A or q*=0). d(q*) = #S[0,q*) - #endable[0,q*). Record min d(q*), histogram.
#include <stdio.h>
#include <stdlib.h>
int main(int c,char**v){int n=atoi(v[1]),part=atoi(v[2]),np=atoi(v[3]); long hist[64]={0}; int mind=99; long cnt=0;
 for(long m=part;m<(1L<<(n-1));m+=np){ int s[64],F[65],G[65];
  for(int i=0;i<n-1;i++) s[i]=((m>>i)&1)?1:-1; s[n-1]=1; F[0]=G[0]=0; for(int i=0;i<n;i++){F[i+1]=F[i]+s[i];G[i+1]=G[i]+F[i+1];}
  #define END(b) ({int r_=0; for(int t=(b)-3;t>=0;t-=4) if(F[b]==F[t]+1&&G[b]-G[t]==((b)-t)*F[t]){r_=1;break;} r_;})
  int b2=n-1; if(!END(b2)) continue; int b1=b2-1; while(b1>=0&&s[b1]<0) b1--; if(b1<0||!END(b1)) continue;
  int qs=b1; while(qs>0&&s[qs-1]<0) qs--;
  int d=0; for(int b=0;b<qs;b++){ if(s[b]<0)d++; else if(END(b)) d--; }
  cnt++; if(d<mind)mind=d; hist[d+20]++;
 }
 printf("n=%d part=%d: configs=%ld min d(q*)=%d hist:",n,part,cnt,mind); for(int i=0;i<64;i++) if(hist[i]) printf(" d%d:%ld",i-20,hist[i]); printf("\n");}
