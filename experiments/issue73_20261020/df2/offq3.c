// offline: for every string of length n compute depth<=2 endables; cleans->t*; uncleans grouped by r (and h);
// member i (t desc) -> i-th latest S in [t_i, r) with F>=h+1 [and not clean start if EXCL]; check existence+injectivity.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int n,EXCL=1,RULE=1,SHOW=10; char sg[80]; int F[81]; long G[81];
int eb[80],et[80],eh[80],er[80]; int ne;
long nfail[3],sh;
int main(int c,char**v){ n=atoi(v[1]); RULE=atoi(v[2]); if(c>3)EXCL=atoi(v[3]); if(c>4)SHOW=atoi(v[4]);
 for(long m=0;m<(1L<<n);m++){
  F[0]=0;G[0]=0; for(int i=0;i<n;i++){sg[i]=(m>>i)&1?'A':'S';F[i+1]=F[i]+(sg[i]=='A'?1:-1);G[i+1]=G[i]+F[i+1];}
  ne=0; int cst[80]={0}; int used[80]={0};
  for(int k=0;k<n;k++) if(sg[k]=='A'){ int t=-1; for(int tt=k-3;tt>=0;tt-=4) if(F[k]==F[tt]+1&&G[k]-G[tt]==(long)(k-tt)*F[tt]){t=tt;break;}
    if(t<0) continue; int mn=F[t]; for(int w=t;w<=k;w++) if(F[w]<mn)mn=F[w]; if(F[t]-mn>2) continue;
    int h=F[t]; long vv=G[k]-(long)h*k; int r=-1; for(int u=t+1;u<k;u++) if(F[u]==h&&G[u]-(long)h*u>vv) r=u;
    if(r<0){cst[t]++;} else {int q=r-1; while(!(sg[q]=='S'&&F[q]==h+1)) q--; eb[ne]=k;et[ne]=t;eh[ne]=h;er[ne]=q+1;ne++;} }
  int bad=0; for(int x=0;x<ne;x++)for(int y=x+1;y<ne;y++) if(er[x]==er[y]&&et[x]==et[y]) {nfail[2]+=0; if(sh<SHOW){sh++;printf("SAMEQT %.*s b=%d,%d\n",n,sg,eb[x],eb[y]);}} for(int i=0;i<80;i++) if(cst[i]>1) bad=1; // clean starts distinct (theorem)
  for(int i=0;i<80;i++) used[i]=cst[i];
  // process groups: by r; members sorted by t desc
  int done[80]={0}; int ord[80],no=0; for(int e=0;e<ne;e++){int fl=1; for(int f=0;f<e;f++) if(er[f]==er[e]) fl=0; if(fl) ord[no++]=e;}
  for(int x=0;x<no;x++)for(int y=x+1;y<no;y++) if(er[ord[y]]<er[ord[x]]){int tm=ord[x];ord[x]=ord[y];ord[y]=tm;}
  for(int oo=0;oo<no&&!bad;oo++){ int e=ord[oo]; int r=er[e]; int mem[80],mm=0; for(int f=0;f<ne;f++) if(er[f]==r){mem[mm++]=f;done[f]=1;}
    for(int x=0;x<mm;x++) for(int y=x+1;y<mm;y++) if(et[mem[y]]>et[mem[x]]||(et[mem[y]]==et[mem[x]]&&eb[mem[y]]<eb[mem[x]])){int tmp=mem[x];mem[x]=mem[y];mem[y]=tmp;}
    int h=eh[e]; int c0=r-1;
    for(int x=0;x<mm;x++){ int f=mem[x]; int cc=-1;
      if(RULE==1){ int cnt=0; for(int cc2=r-1;cc2>=et[f];cc2--) if(sg[cc2]=='S'&&F[cc2]>=h+1&&!(EXCL&&cst[cc2])){cnt++; if(cnt==x+1){cc=cc2;break;}} }
      else if(RULE==3){ for(int cc2=r-1;cc2>=et[f];cc2--) if(sg[cc2]=='S'&&F[cc2]>=h+1&&!used[cc2]){cc=cc2;break;} }
      else { // RULE 2: next available going back from previous pick
        for(int cc2=c0;cc2>=et[f];cc2--) if(sg[cc2]=='S'&&F[cc2]>=h+1&&!(EXCL&&cst[cc2])&&!used[cc2]){cc=cc2;break;} if(cc>=0) c0=cc-1; }
      if(cc<0){bad=1;nfail[1]++;break;} if(used[cc]){bad=2;nfail[2]++;break;} used[cc]=1; } }
  if(bad){ nfail[0]++; if(sh<SHOW){sh++; printf("FAIL%d %.*s\n",bad,n,sg);} }
 }
 printf("n=%d rule=%d excl=%d failstrings=%ld none=%ld collide=%ld\n",n,RULE,EXCL,nfail[0],nfail[1],nfail[2]);}
