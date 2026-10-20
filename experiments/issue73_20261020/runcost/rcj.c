// DFS over all strings up to length N. Track runs of consecutive endable A's (only S's between consecutive A's).
// For run of length r, q* = start of S-run before b_1 (prev clock A or q*=0). Record min slack(0,q*) per r,
// and per (r, J) where J = # S's strictly between b_1 and b_r. Also record witness.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define MAXN 64
#define RM 10
int N; int s[MAXN],F[MAXN+1],G[MAXN+1];
int best[RM+1]; char wit[RM+1][MAXN+1]; int bestJ[RM+1][40]; int bestj1[RM+1][20]; int ext[RM+1][20];
static int endable(int b){ for(int t=b-3;t>=0;t-=4) if(F[b]==F[t]+1 && G[b]-G[t]==(b-t)*F[t]) return 1; return 0;}
// state: k=current length, d=slack(0,k), r=current run length (A's in run), dq=slack at q* of run, J=S's inside run so far,
// runS = S's since last A (pending), dstart = slack at start of current S-run (after last A)
void dfs(int k,int d,int r,int dq,int J,int runS,int dstart,int j1){
  if(k==N) return;
  // append S
  s[k]=-1; F[k+1]=F[k]-1; G[k+1]=G[k]+F[k+1];
  dfs(k+1,d+1,r,dq,J,runS+1,dstart,j1);
  // append A
  s[k]=1; F[k+1]=F[k]+1; G[k+1]=G[k]+F[k+1];
  if(endable(k)){
    int nr,ndq,nJ,nj1;
    if(r>0){nr=r+1; ndq=dq; nJ=J+runS; nj1=j1;} else {nr=1; ndq=dstart; nJ=0; nj1=runS;}
    if(nr<=RM && nj1<20 && ndq<bestj1[nr][nj1]) bestj1[nr][nj1]=ndq;
    if(nr<=RM){ if(ndq<best[nr]){best[nr]=ndq; for(int i=0;i<=k;i++) wit[nr][i]=s[i]>0?'A':'S'; wit[nr][k+1]=0;}
      if(nJ<40 && ndq<bestJ[nr][nJ]) bestJ[nr][nJ]=ndq; }
    dfs(k+1,d-1,nr,ndq,nJ,0,d-1,nj1);
  } else {
    dfs(k+1,d,0,0,0,0,d,0);
  }
}
int main(int c,char**v){N=atoi(v[1]); for(int i=0;i<=RM;i++){best[i]=99; for(int j=0;j<40;j++) bestJ[i][j]=99;}
  F[0]=G[0]=0; for(int i=0;i<=RM;i++)for(int j=0;j<20;j++)bestj1[i][j]=99; dfs(0,0,0,0,0,0,0,0);
  printf("N=%d\n",N); for(int r=1;r<=RM;r++) if(best[r]<99){ printf("r=%d min=%d wit=%s  byJ:",r,best[r],wit[r]);
    for(int j=0;j<40;j++) if(bestJ[r][j]<99) printf(" J%d:%d",j,bestJ[r][j]); printf("\n   byj1:"); for(int j=0;j<20;j++) if(bestj1[r][j]<99) printf(" j%d:%d",j,bestj1[r][j]); printf("\n");}
}
