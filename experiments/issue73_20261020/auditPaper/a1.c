// independent brute force. p=0. Enumerate all strings of length N via DFS.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int N; int s[64]; int F[65]; int endab[64]; int tau[64]; int d[65];
long cnt1=0, bad1=0, cntT=0, badT=0, cntSL[4][4]; char seen[200][64]; int nseen=0;
// window [t,b-1] P2 for A-clock b: sum sigma=1, sum sigma(c)(b-c)=0
int isP2(int t,int b){ int m=0,mo=0; for(int c=t;c<b;c++){m+=s[c]; mo+=s[c]*(b-c);} return m==1&&mo==0; }
void pr(int a,int b){ for(int i=a;i<b;i++) putchar(s[i]>0?'A':'S'); }
void check(int n){ // n = current length; examine k=n
  // claim1: q0=n with d(n)=1
  if(d[n]==1){ int k1=n-1; while(d[k1]!=0) k1--; int az=0; for(int u=k1;u<n;u++) if(s[u]>0&&!endab[u]) az++;
    if(az==2){ cnt1++; int L=n-k1; int ok=(L==3&&s[k1]<0&&s[k1+1]>0&&s[k1+2]>0)||(L==5&&s[k1]<0&&s[k1+1]<0&&s[k1+2]>0&&s[k1+3]>0&&s[k1+4]>0);
      if(!ok){ bad1++; if(bad1<10){printf("C1 BAD: "); pr(0,k1); printf("|"); pr(k1,n); printf("\n");} } } }
  // SL setting: k=n, c=k-1 endable
  int k=n; if(k>=4 && s[k-1]>0 && endab[k-1]){ int q0=tau[k-1]; int ay=0,X=0; for(int u=q0;u<k;u++) if(s[u]>0){ if(!endab[u]) ay++; else if(tau[u]<q0) X++; }
    int dd=d[q0]; if(ay+dd==2){ cntSL[dd][X>3?3:X]++;
      if(dd==1){ cntT++; int okT=1; for(int q=q0+1;q<k;q++) if(d[q]<1) okT=0; if(!okT){ badT++; if(badT<10){printf("T BAD: "); pr(0,q0); printf("|"); pr(q0,k); printf("\n");}} }
    } }
}
void dfs(int n){
  if(n>0) check(n);
  if(n==N) return;
  for(int v=-1;v<=1;v+=2){ s[n]=v; F[n+1]=F[n]+v; endab[n]=0; tau[n]=-1;
    if(v>0){ for(int t=n-3;t>=0;t-=4) if(isP2(t,n)){ endab[n]=1; tau[n]=t; break; } }
    d[n+1]=d[n]+(v<0?1:(endab[n]?-1:0));
    if(d[n+1]<0){ printf("H violated?!\n"); exit(1);} 
    dfs(n+1); }
}
int main(int c,char**v){ N=atoi(v[1]); d[0]=0; dfs(0);
  printf("N=%d claim1 (a_z=2 => z in {SAA,SSAAA}): instances %ld bad %ld\n",N,cnt1,bad1);
  printf("LemmaT instances (d=1,a_y=1) %ld bad %ld\n",cntT,badT);
  for(int a=0;a<3;a++){printf("d=%d X-hist:",a); for(int x=0;x<4;x++) printf(" %ld",cntSL[a][x]); printf("\n");} }
