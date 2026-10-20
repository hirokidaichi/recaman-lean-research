// for prefixes with prefix-H, d(q0)=1, k1 last zero (<q0): for each t in (k1,q0): record (h-Mz, h2-h, min area sign class)
// Mz = min_{[k1,q0)} F ; Mt = min_{[t,q0]} F ; Az = sum_{u=t+1}^{q0} (F(u)-h)
#include <stdio.h>
#include <stdlib.h>
int s[256],F[257],G[257],D[257]; int LW; long tab[10][10][3]; int minAz[10][10];
int isw(int b,int t){ return t>=0 && F[b]==F[t]+1 && G[b]-G[t]==(b-t)*F[t]; }
void rec(int q0,int k1){ int Mz=1000; for(int u=k1;u<q0;u++) if(F[u]<Mz)Mz=F[u];
  for(int t=k1+1;t<q0;t++){ int h=F[t]; int Az=G[q0]-G[t]-(q0-t)*h; int a=h-Mz,b=F[q0]-h; if(a>9)a=9; if(b>9)b=9;
    int c=Az<0?0:(Az==0?1:2); tab[a][b][c]++; if(Az<minAz[a][b]) minAz[a][b]=Az; } }
void dfsw(int len,int lastz){
  if(D[len]==1 && len>0) rec(len,lastz);
  if(len>=LW) return;
  for(int v=-1;v<=1;v+=2){
    s[len]=v; F[len+1]=F[len]+v; G[len+1]=G[len]+F[len+1];
    int nd=D[len],end=0; if(v>0){ for(int t=len-3;t>=0;t-=4) if(isw(len,t)){end=1;break;} }
    if(v<0) nd++; else if(end) nd--; if(nd<0) continue;
    D[len+1]=nd; dfsw(len+1,nd==0?len+1:lastz);
  }
}
int main(int c,char**v){ LW=atoi(v[1]); for(int a=0;a<10;a++)for(int b=0;b<10;b++)minAz[a][b]=99999; dfsw(0,0);
 for(int a=0;a<10;a++)for(int b=0;b<10;b++) if(tab[a][b][0]+tab[a][b][1]+tab[a][b][2]) printf("h-Mz=%d h2-h=%d : Az<0 %ld, =0 %ld, >0 %ld  minAz=%d\n",a,b,tab[a][b][0],tab[a][b][1],tab[a][b][2],minAz[a][b]); }
