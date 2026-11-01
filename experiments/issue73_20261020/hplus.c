#include <stdio.h>
#include <stdlib.h>
/* prefix scan with p=0: for each prefix k: e + u <= s ? clean per minimal window, def: all h-visits u in (t,b) have P(u)<P(t) */
int n; int F[64]; long G[64]; int maxv=-99; long cnt;
void rec(int k,int e,int u,int s){ if(e+u-s>maxv){maxv=e+u-s;printf("max %d at k=%d\n",maxv,k);}
 if(k==n)return;
 for(int a=0;a<2;a++){F[k+1]=F[k]+(a?1:-1);G[k+1]=G[k]+F[k+1];int ne=e,nu=u,ns=s;
  if(a){ for(int t=k-3;t>=0;t-=4){ int h=F[t]; if(F[k]==h+1 && G[k]-G[t]==(long)(k-t)*h){ /* minimal = first found (latest t) */
        int clean=1; for(int w=t+1;w<k;w++) if(F[w]==h && !(G[w]-G[t]-(long)(w-t)*h<0)) {clean=0;break;}
        ne++; if(!clean) nu++; break;}}
  } else ns++;
  rec(k+1,ne,nu,ns);} }
int main(int c,char**v){n=atoi(v[1]);F[0]=0;G[0]=0;rec(0,0,0,0);printf("n=%d max(e+u-s)=%d\n",n,maxv);}
