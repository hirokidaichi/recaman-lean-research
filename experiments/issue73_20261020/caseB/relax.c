// Case B relaxed search: x = S^j A A A ..., positions 0..L (L=4m+3), F(0)=0.
// Constraints: F<=1 on (0,L], F(L)=1, F>=-j+1 on [j+1,L], sum_{u=1}^{L}F(u)=0,
// every A clock b in [j+2,L-1] endable from 0 except at most R exceptions.
// print solutions with exactly minimal exceptions.
#include <stdio.h>
#include <stdlib.h>
int L,J,R; int F[256]; long G[256]; char s[256]; int best; long cnt;
int endable(int b){ // A at b: F(b+1)=F(b)+1
  int h=F[b]-1;
  for(int t=b-3;t>=0;t-=4){ if(F[t]==h && G[b]-G[t]==(long)(b-t)*h) return 1;}
  return 0;}
void dfs(int c,int ex){ // decide sigma(c), F[c] known, G[c] known
  if(c==L){ // sigma(L)=A, need F(L)=1, G(L)=0
    if(F[L]==1 && G[L]==0){ int e=endable(L); if(!e) return;
      cnt++; s[L]='A'; s[L+1]=0; printf("ex=%d j=%d %s\n",ex,J,s); fflush(stdout);} return; }
  // remaining steps: need to reach 1 at L
  for(int a=0;a<2;a++){
    int nf=F[c]+(a?1:-1);
    if(nf>1 || nf< -J+1) continue;
    if(abs(1-nf) > L-(c+1)) continue;
    int nex=ex;
    s[c]=a?'A':'S'; F[c+1]=nf; G[c+1]=G[c]+nf;
    if(a && c>=J+2){ if(!endable(c)){ nex++; if(nex>R) continue; } }
    dfs(c+1,nex);
  }
}
int main(int argc,char**argv){ int n=atoi(argv[1]); R=atoi(argv[2]); L=n-1;
  for(J=2;4*J+3<=L;J++){
    F[0]=0;G[0]=0; for(int i=0;i<J;i++){s[i]='S';F[i+1]=-(i+1);G[i+1]=G[i]+F[i+1];}
    int c=J; for(int i=0;i<3;i++){s[c]='A';F[c+1]=F[c]+1;G[c+1]=G[c]+F[c+1];c++;}
    if(F[c]>1) continue;
    dfs(c,0);
  }
  fprintf(stderr,"n=%d R=%d count=%ld\n",n,R,cnt);
}
