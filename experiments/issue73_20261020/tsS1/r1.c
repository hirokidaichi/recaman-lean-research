// R1 test without t2: nodes with last clock A endable, t1(j) present (any j>=0); report min slack per (j, jprime)
#include <stdio.h>
#include <stdlib.h>
int N,s[128],F[129],G[129],E[128],dd[129]; int mn[20][20];
int endab(int b){ if(s[b]<0) return 0; for(int t=b-3;t>=0;t-=4) if(F[b]==F[t]+1&&G[b]-G[t]==(b-t)*F[t]) return 1; return 0;}
void dfs(int n){
  if(n>0 && s[n-1]>0 && E[n-1] && dd[n]<20){ int jp=0; while(n-2-jp>=0 && s[n-2-jp]<0) jp++;
    for(int t=0;t<n;t++){ int D=F[n]-F[t]; if(D<1||D>20) continue; long Q=G[n]-G[t]-(long)(n-t)*F[t]+(long)D*(D-1)/2;
      if(Q==0 && jp<20){ int j=D-1; if(dd[n]<mn[j][jp]) mn[j][jp]=dd[n]; } } }
  if(n==N) return;
  for(int v=-1;v<=1;v+=2){ s[n]=v; F[n+1]=F[n]+v; G[n+1]=G[n]+F[n+1]; E[n]=endab(n);
    int d=dd[n]+(v<0?1:0)-(E[n]?1:0); if(d<0) continue; dd[n+1]=d; dfs(n+1); }
}
int main(int c,char**v){N=atoi(v[1]); for(int a=0;a<20;a++)for(int b=0;b<20;b++)mn[a][b]=99; dfs(0);
 printf("rows j=0..6, cols j'=0..6: min slack at q with q-1 endable and t1(j) present\n");
 for(int a=0;a<7;a++){ for(int b=0;b<7;b++) printf("%3d",mn[a][b]); printf("\n");} }
