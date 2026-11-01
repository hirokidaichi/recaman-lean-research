// classify minimal windows: clean (pi-walk at level h never jumps over v), ssCount<=1, depth1. t* injectivity on clean∪ss1.
#include <stdio.h>
#include <stdlib.h>
int n; int F[64]; long G[64]; char sg[64]; int owner[64];
long cnt[2][2][2], coll, startA_cs; int sh,sh2;
long P(int h,int u){return G[u]-(long)h*u;}
void rec(int k){
  if(k==n) return;
  for(int a=0;a<2;a++){
    sg[k]=a?'A':'S'; F[k+1]=F[k]+(a?1:-1); G[k+1]=G[k]+F[k+1];
    int t=-1, set=-1;
    if(a){ for(int tt=k-3;tt>=0;tt-=4) if(F[k]==F[tt]+1 && G[k]-G[tt]==(long)(k-tt)*F[tt]){t=tt;break;} }
    if(t>=0){ int h=F[t]; long v=P(h,k);
      int clean=1; int prev=t; for(int u=t+1;u<k;u++) if(F[u]==h){ if(P(h,prev)>v && P(h,u)<v) clean=0; prev=u; }
      int ss=0; for(int u=t;u<k-1;u++) if(sg[u]=='S'&&sg[u+1]=='S') ss++;
      int mn=h; for(int u=t;u<=k;u++) if(F[u]<mn) mn=F[u];
      int d1 = (h-mn)<=1;
      cnt[clean][ss<=1][d1]++;
      if(!clean && ss<=1 && sh2<4){sh2++; printf("SS1 UNCLEAN %.*s b=%d t*=%d\n",k+1,sg,k,t);}
      if(clean||ss<=1){ if(sg[t]!='S') startA_cs++;
        if(owner[t]>=0){coll++; if(sh<5){sh++;printf("COLL %.*s b=%d t*=%d other=%d\n",k+1,sg,k,t,owner[t]);}} else {owner[t]=k;set=t;} }
    }
    rec(k+1);
    if(set>=0) owner[set]=-1;
  }
}
int main(int c,char**v){n=atoi(v[1]);for(int i=0;i<64;i++)owner[i]=-1;rec(0);
 for(int a=0;a<2;a++)for(int b=0;b<2;b++)for(int d=0;d<2;d++) printf("clean=%d ss<=1=%d depth1=%d : %ld\n",a,b,d,cnt[a][b][d]);
 printf("n=%d coll(clean∪ss1)=%ld startA=%ld\n",n,coll,startA_cs);}
