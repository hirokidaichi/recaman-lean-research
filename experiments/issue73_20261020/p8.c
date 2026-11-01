// for prefixes [0,k): tally (e-s, #unclean). Max of e-s+#unclean? also: equality/slack-1 cases with uncleans.
#include <stdio.h>
#include <stdlib.h>
int n; int F[64]; long G[64]; char sg[64];
long tab[8][8]; int sh0,sh1;
long P(int h,int u){return G[u]-(long)h*u;}
void rec(int k,int e,int s,int u){
  int d=s-e; if(d<8&&u<8) tab[d][u]++;
  if(u>d&&sh0<10){sh0++;printf("VIOL H+: %.*s u=%d\n",k,sg,u);}
  if(k==n) return;
  for(int a=0;a<2;a++){
    sg[k]=a?'A':'S'; F[k+1]=F[k]+(a?1:-1); G[k+1]=G[k]+F[k+1];
    int t=-1,ne=e,ns=s+(a?0:1),nu=u;
    if(a){ for(int tt=k-3;tt>=0;tt-=4) if(F[k]==F[tt]+1 && G[k]-G[tt]==(long)(k-tt)*F[tt]){t=tt;break;} }
    if(t>=0){ ne++; int h=F[t]; long v=P(h,k); for(int w=t+1;w<k;w++) if(F[w]==h && P(h,w)>v){nu++;break;} }
    rec(k+1,ne,ns,nu);
  }
}
int main(int c,char**v){n=atoi(v[1]);rec(0,0,0,0);
 printf("rows: slack s-e (0..7); cols: #unclean (0..7)\n");
 for(int d=0;d<8;d++){printf("slack %d:",d);for(int u=0;u<8;u++)printf(" %ld",tab[d][u]);printf("\n");}}
