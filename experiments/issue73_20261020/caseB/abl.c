// ablation: enforce endability only for A clocks b>=J+2 with F(b) in [lo,hi]
// band: F<=1 on (0,L], F>=-J+1 after J (option floor=0 disables lower band)
#include <stdio.h>
#include <stdlib.h>
int L,J,lo,hi,floorband; int F[256]; long G[256]; char s[256]; long cnt; int maxpr=3,pr;
int endable(int b){ int h=F[b]-1;
  for(int t=b-3;t>=0;t-=4){ if(F[t]==h && G[b]-G[t]==(long)(b-t)*h) return 1;} return 0;}
void dfs(int c){
  if(c==L){ if(F[L]==1 && G[L]==0){ s[L]='A'; s[L+1]=0; cnt++; if(pr++<maxpr) printf("  %s\n",s);} return; }
  for(int a=0;a<2;a++){ int nf=F[c]+(a?1:-1);
    if(nf>1) continue; if(floorband && nf< -J+1) continue; if(abs(1-nf) > L-(c+1)) continue;
    s[c]=a?'A':'S'; F[c+1]=nf; G[c+1]=G[c]+nf;
    if(a && F[c]>=lo && F[c]<=hi && !endable(c)) continue;
    dfs(c+1);} }
int main(int argc,char**argv){ int n=atoi(argv[1]); lo=atoi(argv[2]); hi=atoi(argv[3]); floorband=atoi(argv[4]); L=n-1;
  for(J=2;4*J+3<=L;J++){ F[0]=0;G[0]=0; for(int i=0;i<J;i++){s[i]='S';F[i+1]=-(i+1);G[i+1]=G[i]+F[i+1];}
    int c=J; for(int i=0;i<3;i++){s[c]='A';F[c+1]=F[c]+1;G[c+1]=G[c]+F[c+1];c++;}
    dfs(c);}
  printf("n=%d lo=%d hi=%d band=%d count=%ld\n",n,lo,hi,floorband,cnt);}
