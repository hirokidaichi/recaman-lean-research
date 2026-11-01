// Independent brute force for H_L and EqClass_L (line version), p = 0 WLOG.
// sig[c] in {+1,-1}; F(t)=sum_{c<t} sig, G(t)=sum_{c<t} c*sig(c).
// window [t,b-1]: F(b)-F(t)==1 and b*(F(b)-F(t)) - (G(b)-G(t)) == 0.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static int L, NMAX, NOTRIPLE=0;
static int sig[64]; static long F[65], G[65];
static int nwinat[64]; // number of windows ending at b (b with sig=+1), else 0
static long cnt_eq[64], cnt_viol[64], cnt_hfail[64], cnt_blockwords_end[64];
static int countw(int b){ int c=0; for(int t=b-1;t>=0 && b-t<=L;t--){ long m=F[b]-F[t]; long mom=(long)b*m-(G[b]-G[t]); if(m==1&&mom==0) c++; } return c; }
// parse check: returns 1 if sig[0..n-1] parses in (SAAA|SSAAAASAAA|A)* with endable exactly members & unique windows
static int parse(int n){
  int i=0;
  while(i<n){
    if(sig[i]==1){ if(nwinat[i]!=0) return 0; i++; continue; }
    // S
    if(i+1<n && sig[i+1]==-1){ // triple SSAAAASAAA
      if(NOTRIPLE) return 0;
      if(i+10>n) return 0;
      static const int pat[10]={-1,-1,1,1,1,1,-1,1,1,1};
      static const int mem[10]={0,0,0,0,1,0,0,1,0,1};
      for(int j=0;j<10;j++){ if(sig[i+j]!=pat[j]) return 0; if(pat[j]==1){ int e=nwinat[i+j]; if(mem[j]? e!=1 : e!=0) return 0; } }
      i+=10;
    } else {
      if(i+4>n) return 0;
      static const int pat[4]={-1,1,1,1}; static const int mem[4]={0,0,0,1};
      for(int j=0;j<4;j++){ if(sig[i+j]!=pat[j]) return 0; if(pat[j]==1){ int e=nwinat[i+j]; if(mem[j]? e!=1 : e!=0) return 0; } }
      i+=4;
    }
  }
  return 1;
}
static void pr(int n){ for(int i=0;i<n;i++) putchar(sig[i]>0?'A':'S'); }
static void rec(int n,int e,int s){
  // string of length n set; e,s counts
  if(n>0){
    if(e>s){ cnt_hfail[n]++; if(cnt_hfail[n]<3){printf("H FAIL n=%d ",n);pr(n);puts("");} }
    if(e==s && sig[n-1]==1 && nwinat[n-1]>0){ cnt_eq[n]++; if(!parse(n)){ cnt_viol[n]++; if(cnt_viol[n]<3){printf("VIOL n=%d ",n);pr(n);puts("");} } }
  }
  if(n==NMAX) return;
  for(int v=-1;v<=1;v+=2){ sig[n]=v; F[n+1]=F[n]+v; G[n+1]=G[n]+(long)n*v;
    int ne=e, ns=s; if(v==1){ nwinat[n]=countw(n); if(nwinat[n]) ne++; } else { nwinat[n]=0; ns++; }
    rec(n+1,ne,ns); }
}
int main(int argc,char**argv){ L=atoi(argv[1]); NMAX=atoi(argv[2]); if(argc>3) NOTRIPLE=1; F[0]=G[0]=0; rec(0,0,0);
  long tv=0,te=0,th=0; printf("L=%d NMAX=%d%s\n n eqwords viol hfail\n",L,NMAX,NOTRIPLE?" NOTRIPLE":"");
  for(int n=1;n<=NMAX;n++){ if(cnt_eq[n]||cnt_viol[n]||cnt_hfail[n]) printf("%2d %ld %ld %ld\n",n,cnt_eq[n],cnt_viol[n],cnt_hfail[n]); tv+=cnt_viol[n]; te+=cnt_eq[n]; th+=cnt_hfail[n]; }
  printf("TOTAL eqwords=%ld viol=%ld hfail=%ld\n",te,tv,th); return 0; }
