// Equality cases of H: walks from p=0 with sigma(0)=S, Delta_0(k)=0 where clock k-1 is endable (a P2 end with window start>=0).
// Check: string parses as (SAAA | SSAAAASAAA | A)* and the endable set equals the set of block-final clocks.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int n; int F[64]; long G[64]; char sg[64]; int E[64];
long eqc=0, bad=0; int shown=0;
int parse(int k){ // DP: can [0,k) parse, with endables exactly block ends
  static int ok[64]; ok[0]=1;
  for(int i=1;i<=k;i++){ ok[i]=0;
    if(sg[i-1]=='A' && !E[i-1] && ok[i-1]) ok[i]=1;
    if(i>=4 && ok[i-4] && !strncmp(sg+i-4,"SAAA",4) && E[i-1] && !E[i-2] && !E[i-3]) ok[i]=1;
    if(i>=10 && ok[i-10] && !strncmp(sg+i-10,"SSAAAASAAA",10) && E[i-1]&&E[i-3]&&E[i-6]&&!E[i-2]&&!E[i-5]&&!E[i-7]&&!E[i-8]) ok[i]=1;
  }
  return ok[k];
}
void rec(int k,int e,int s){
  if(k>0 && E[k-1] && e==s){ eqc++; if(!parse(k)){bad++; if(shown<10){shown++;printf("NOPARSE %.*s ends:",k,sg);for(int i=0;i<k;i++)if(E[i])printf(" %d",i);printf("\n");}} }
  if(k==n) return;
  for(int a=(k==0?0:0);a<2;a++){ 
    sg[k]=a?'A':'S'; F[k+1]=F[k]+(a?1:-1); G[k+1]=G[k]+F[k+1];
    E[k]=0; int ne=e,ns=s;
    if(a){ for(int t=k-3;t>=0;t-=4) if(F[k]==F[t]+1 && G[k]-G[t]==(long)(k-t)*F[t]){E[k]=1;break;} } else ns++;
    if(E[k]) ne++;
    rec(k+1,ne,ns);
  }
}
int main(int c,char**v){n=atoi(v[1]);rec(0,0,0);printf("n=%d equality cases=%ld nonparsing=%ld\n",n,eqc,bad);}
