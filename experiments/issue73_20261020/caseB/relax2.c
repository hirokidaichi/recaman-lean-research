// Like relax.c but no endability during DFS; at the end check which A's are endable; 
// mode: print counts of solutions where L-1 is endable; and distribution of #nonendable.
#include <stdio.h>
#include <stdlib.h>
int L,J; int F[256]; long G[256]; char s[256]; long cnt,cntL1; int hist[256];
int endable(int b){ int h=F[b]-1;
  for(int t=b-3;t>=0;t-=4){ if(F[t]==h && G[b]-G[t]==(long)(b-t)*h) return 1;} return 0;}
int verbose;
void dfs(int c){
  if(c==L){ if(F[L]==1 && G[L]==0){ s[L]='A'; s[L+1]=0; cnt++;
      int ne=0; for(int b=J+2;b<L;b++) if(s[b]=='A' && !endable(b)) ne++;
      hist[ne]++;
      if(endable(L-1)){ cntL1++; if(verbose) printf("L-1 endable ne=%d %s\n",ne,s);} }
    return; }
  for(int a=0;a<2;a++){ int nf=F[c]+(a?1:-1);
    if(nf>1 || nf< -J+1) continue; if(abs(1-nf) > L-(c+1)) continue;
    s[c]=a?'A':'S'; F[c+1]=nf; G[c+1]=G[c]+nf; dfs(c+1);} }
int main(int argc,char**argv){ int n=atoi(argv[1]); verbose=argc>2; L=n-1;
  for(J=2;4*J+3<=L;J++){ F[0]=0;G[0]=0; for(int i=0;i<J;i++){s[i]='S';F[i+1]=-(i+1);G[i+1]=G[i]+F[i+1];}
    int c=J; for(int i=0;i<3;i++){s[c]='A';F[c+1]=F[c]+1;G[c+1]=G[c]+F[c+1];c++;}
    dfs(c);}
  printf("n=%d total=%ld L-1endable=%ld  hist(nonendable):",n,cnt,cntL1);
  for(int i=0;i<n;i++) if(hist[i]) printf(" %d:%d",i,hist[i]); printf("\n");}
