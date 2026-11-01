// (HD): for all p<k: #{depth<=DMAX uncleans b: t*>=p, b<k} <= #{S c in [p,k): walk reaches F(c)-3 before F(c)+1 within (c,k]}
// MODE 0: D = deep-forced (any height). MODE 1: D = deep-forced with F(c)>= (some) ... (unused)
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int n,DMAX=2,SHOW=20; char sg[80]; int F[81]; long G[81];
int ne, eb[80], et[80]; int df[80]; // df[c]=1 if c deep-forced witnessed so far
long nf,nunc; int sh;
long P(int h,int u){return G[u]-(long)h*u;}
void rec(int k){
  if(k==n) return;
  for(int a=0;a<2;a++){
    sg[k]=a?'A':'S';F[k+1]=F[k]+(a?1:-1);G[k+1]=G[k]+F[k+1];
    // update deep-forced: S c<k+1 with F(c)-3==F(k+1), not reached F(c)+1 in (c,k], not yet df
    int newdf[80],nn=0;
    if(!a){ for(int c=k;c>=0;c--){ if(sg[c]=='S'&&!df[c]&&F[c]-3==F[k+1]){ int okk=1; for(int w=c+1;w<=k;w++){ if(F[w]==F[c]+1||F[w]==F[c]-3){okk=0;break;} } if(okk){df[c]=1;newdf[nn++]=c;} } } }
    int added=0,bad=0;
    if(a){int t=-1; for(int tt=k-3;tt>=0;tt-=4) if(F[k]==F[tt]+1 && G[k]-G[tt]==(long)(k-tt)*F[tt]){t=tt;break;}
      if(t>=0){int mn=F[t];for(int w=t;w<=k;w++)if(F[w]<mn)mn=F[w]; if(F[t]-mn>DMAX) t=-1;}
      if(t>=0){int h=F[t]; long v=P(h,k); int cl=1; for(int u=t+1;u<k;u++) if(F[u]==h&&P(h,u)>v){cl=0;break;}
        if(!cl){ eb[ne]=k;et[ne]=t;ne++;added=1;nunc++;
          // check all p<=t: count uncleans with et>=p vs df in [p,k]
          int cu=0,cd=0; // scan p downward from t
          for(int p=k;p>=0;p--){ if(sg[p]=='S'&&df[p]) cd++; for(int e=0;e<ne;e++) if(et[e]==p) cu++; if(cu>cd){bad=1;break;} }
          if(bad){nf++; if(sh<SHOW){sh++;printf("FAIL %.*s b=%d t=%d\n",k+1,sg,k,t);fflush(stdout);} }
        }}}
    if(!bad) rec(k+1);
    if(added) ne--;
    for(int i=0;i<nn;i++) df[newdf[i]]=0;
  }
}
int main(int c,char**v){n=atoi(v[1]); if(c>2)DMAX=atoi(v[2]); if(c>3)SHOW=atoi(v[3]); rec(0);printf("n=%d D=%d uncleans=%ld minimal-fails=%ld\n",n,DMAX,nunc,nf);}
