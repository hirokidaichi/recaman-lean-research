// H-start: for all J=[p,q] : #uncleans(window in J) + #distinct clean starts in J (cleans ended so far) <= #S in J. depth<=DMAX
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int n,DMAX=2,SHOW=20; char sg[80]; int F[81]; long G[81];
int ne, eb[80], et[80]; int cst[80]; long nf; int sh;
long P(int h,int u){return G[u]-(long)h*u;}
int checkJ(int k){ for(int p=0;p<=k;p++){ int cs=0,cu=0,s=0; for(int q=p;q<=k;q++){ if(sg[q]=='S'){s++; if(cst[q])cs++;} for(int e=0;e<ne;e++) if(eb[e]==q+1&&et[e]>=p) cu++; if(cu+cs>s) return 0; } } return 1; }
void rec(int k){
  if(k==n) return;
  for(int a=0;a<2;a++){
    sg[k]=a?'A':'S';F[k+1]=F[k]+(a?1:-1);G[k+1]=G[k]+F[k+1];
    int added=0,cadd=-1,bad=0;
    if(a){int t=-1; for(int tt=k-3;tt>=0;tt-=4) if(F[k]==F[tt]+1 && G[k]-G[tt]==(long)(k-tt)*F[tt]){t=tt;break;}
      if(t>=0){int mn=F[t];for(int w=t;w<=k;w++)if(F[w]<mn)mn=F[w]; if(F[t]-mn>DMAX) t=-1;}
      if(t>=0){int h=F[t]; long v=P(h,k); int cl=1; for(int u=t+1;u<k;u++) if(F[u]==h&&P(h,u)>v){cl=0;break;}
        if(cl){ if(!cst[t]){cst[t]=1;cadd=t;} } else { eb[ne]=k+1;et[ne]=t;ne++;added=1; }
        if(!checkJ(k)){bad=1;nf++; if(sh<SHOW){sh++;printf("FAIL %.*s b=%d t=%d %s\n",k+1,sg,k,t,cl?"clean":"unclean");fflush(stdout);}}
      }}
    if(!bad) rec(k+1);
    if(added) ne--; if(cadd>=0) cst[cadd]=0;
  }
}
int main(int c,char**v){n=atoi(v[1]); if(c>2)SHOW=atoi(v[2]); if(c>3)DMAX=atoi(v[3]); rec(0);printf("n=%d D=%d minimal-fails=%ld\n",n,DMAX,nf);}
