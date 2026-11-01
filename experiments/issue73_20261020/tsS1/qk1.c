// for prefix-H prefixes (last clock A), starts t<k1 with D>=1: min Q per slack s and D; print witness for Q<=0
#include <stdio.h>
#include <stdlib.h>
int N,s[128],F[129],G[129],E[128],dd[129]; long mn[8][40];
int endab(int b){ if(s[b]<0) return 0; for(int t=b-3;t>=0;t-=4) if(F[b]==F[t]+1&&G[b]-G[t]==(b-t)*F[t]) return 1; return 0;}
void dfs(int n){
  if(n>0 && s[n-1]>0 && dd[n]<8){ int d=dd[n]; int k1=0; for(int k=0;k<=n;k++) if(dd[k]==0) k1=k;
    for(int t=0;t<k1;t++){ int D=F[n]-F[t]; if(D<1||D>=40) continue; long Q=G[n]-G[t]-(long)(n-t)*F[t]+(long)D*(D-1)/2;
      if(Q<mn[d][D]){ mn[d][D]=Q; if(Q<=0){ printf("s=%d D=%d Q=%ld t=%d x=",d,D,Q,t); for(int k=0;k<n;k++){if(k==k1)putchar('|');putchar(s[k]<0?'S':(E[k]?'a':'A'));} printf("\n");} } } }
  if(n==N) return;
  for(int v=-1;v<=1;v+=2){ s[n]=v; F[n+1]=F[n]+v; G[n+1]=G[n]+F[n+1]; E[n]=endab(n);
    int d=dd[n]+(v<0?1:0)-(E[n]?1:0); if(d<0) continue; dd[n+1]=d; dfs(n+1); }
}
int main(int c,char**v){N=atoi(v[1]); for(int a=0;a<8;a++)for(int b=0;b<40;b++)mn[a][b]=999; dfs(0);
 for(int a=0;a<6;a++){printf("s=%d:",a); for(int D=1;D<14;D++) printf(" %ld",mn[a][D]); printf("\n");} }
