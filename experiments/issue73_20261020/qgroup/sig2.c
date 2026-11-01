// Scheme Sigma check: groups of depth<=2 uncleans by q. mid(q)=[q+1,R). Check
// (I) mids pairwise disjoint, no q in another group's mid; (II) #S in mid not depth<=2 clean start >= m-1;
// also (III) q not clean start; also stats: min slack, max c_hm1.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define MX 256
int D=2,SHOW=10; char sg[MX]; int F[MX+1]; long G[MX+1]; long nt,nf[8],nc1; int sh; long ngroups;
int ne,eb[MX],et[MX],eh[MX],eq[MX],ecl[MX]; int cst[MX];
int gq[MX],gR[MX],gm[MX],gh[MX],ng;
int check(int len){
  ne=0; memset(cst,0,sizeof(int)*len);
  for(int k=0;k<len;k++) if(sg[k]=='A'){
    int t=-1; for(int tt=k-3;tt>=0;tt-=4) if(F[k]==F[tt]+1&&G[k]-G[tt]==(long)(k-tt)*F[tt]){t=tt;break;}
    if(t<0) continue; int h=F[t]; int mn=h; for(int w=t;w<=k;w++) if(F[w]<mn)mn=F[w]; if(h-mn>D) continue;
    long v=G[k]-(long)h*k; int r=-1; for(int u=t+1;u<k;u++) if(F[u]==h&&G[u]-(long)h*u>v) r=u;
    eb[ne]=k;et[ne]=t;eh[ne]=h;ecl[ne]=(r<0);eq[ne]=-1;
    if(r>=0){int q=r-1; while(!(sg[q]=='S'&&F[q]==h+1)) q--; eq[ne]=q;} else cst[t]=1;
    ne++; }
  ng=0;
  for(int e=0;e<ne;e++) if(!ecl[e]){ int g=-1; for(int i=0;i<ng;i++) if(gq[i]==eq[e]) g=i;
    if(g<0){ g=ng++; gq[g]=eq[e]; gh[g]=eh[e]; gm[g]=0; int R=eq[e]+1; while(!(F[R]==eh[e]&&sg[R]=='A')) R++; gR[g]=R; }
    if(gh[g]!=eh[e]) return 5; gm[g]++; if(!(eb[e]>gR[g])) return 5; }
  int bad=0;
  for(int g=0;g<ng;g++){ ngroups++;
    if(cst[gq[g]]) bad|=8;
    int fr=0; for(int c=gq[g]+1;c<gR[g];c++) if(sg[c]=='S'&&!cst[c]) fr++;
    if(fr<gm[g]-1) bad|=2;
    { long K=0; for(int w=gq[g]+2;w<=gR[g];w++) K-= (F[w]-gh[g]); int c0=0,c1=0; for(int c=gq[g]+1;c<gR[g];c++) if(sg[c]=='S'&&cst[c]){ if(F[c]==gh[g]) c0++; else c1++; }
      if(gm[g]+c0+c1 > (K-1)/3+2) bad|=16; if(gm[g]+c0 > (K-1)/3+1) bad|=32; if(c1>1) nc1++; }
    for(int g2=0;g2<ng;g2++) if(g2!=g){
      if(gq[g2]+1>=gq[g]+1 && gq[g2]+1<gR[g]) bad|=1;
      if(gq[g2]>=gq[g]+1 && gq[g2]<gR[g]) bad|=4; } }
  return bad;
}
void rep(int len,int r){ nt++; if(r){ for(int i=0;i<6;i++) if(r&(1<<i)) nf[i]++;  if(sh<SHOW){sh++;printf("FAIL%d %.*s\n",r,len,sg);fflush(stdout);}}}
void setw(int len){F[0]=0;G[0]=0;for(int i=0;i<len;i++){F[i+1]=F[i]+(sg[i]=='A'?1:-1);G[i+1]=G[i]+F[i+1];}}
int main(int argc,char**argv){ int n=atoi(argv[1]); if(argc>2)SHOW=atoi(argv[2]);
 if(n>0){ for(long m=0;m<(1L<<n);m++){ for(int i=0;i<n;i++) sg[i]=(m>>i)&1?'A':'S'; setw(n); rep(n,check(n)); } }
 else { char buf[MX+2]; while(fgets(buf,sizeof buf,stdin)){ int len=strcspn(buf,"\r\n"); if(len<4) continue; memcpy(sg,buf,len); setw(len); rep(len,check(len)); } }
 printf("n=%d tested=%ld groups=%ld overlap=%ld count=%ld qInMid=%ld qClean=%ld struct=%ld IIstar=%ld IIb=%ld groups_c1ge2=%ld\n",n,nt,ngroups,nf[0],nf[1],nf[2],nf[3],nf[4]-0,nf[4],nf[5],nc1);}
