// Does every collision of the oldest-S charge come with its own spare subtraction?
//   c = |U| - |image of the oldest-S map|   (collision excess, E-069's failure)
//   slack = |D| - |U|
// Test the self-strengthening inequality   |U| + c <= |D|   i.e.  slack >= c.
// Also: how many supplied A have a window whose oldest sign is an A (the E-130 shape)?
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <vector>
#include <string>
using I=std::int64_t;
static int p; static int sgn[64]; static int Gmin;
static bool isMinRotation(uint64_t w){
  for(int r=1;r<p;++r){uint64_t x=((w>>r)|(w<<(p-r)))&((1ULL<<p)-1);if(x<w)return false;}
  return true;
}
int main(int argc,char**argv){
  int plo=atoi(argv[1]),phi=atoi(argv[2]);
  printf("protocol=H-20260911-09 collision excess vs slack\n");
  for(p=plo;p<=phi;++p){
    uint64_t full=(1ULL<<p)-1; I bad=0,words=0,maxC=0; std::string firstBad;
    I minMargin=9999;
    for(uint64_t w=0;w<=full;++w){
      int pc=__builtin_popcountll(w); int sigma=2*pc-p; int nS=p-pc;
      if(sigma<=0||!isMinRotation(w)) continue;
      ++words;
      for(int i=0;i<p;++i) sgn[i]=((w>>i)&1)?1:-1;
      Gmin=0;
      for(int s=0;s<p;++s){int acc=0;for(int l=1;l<=p;++l){acc+=sgn[((s-l)%p+p)%p];if(acc<Gmin)Gmin=acc;}}
      int stopS=1-Gmin; int nU=0; uint64_t image=0; int noEdge=0;
      for(int i=0;i<p;++i){
        if(sgn[i]<0) continue;
        int S=0,idx=i; I M=0; bool ok=false; I dd=0;
        for(I d=1;;++d){
          idx=(idx-1+p)%p; int v=sgn[idx]; S+=v; M+=d*v;
          if(S==1&&M==0){ok=true;dd=d;break;}
          if(S>stopS) break;
        }
        if(!ok) continue;
        ++nU;
        int oldest=-1;
        for(I k=1;k<=dd&&k<=(I)p;++k){int q=((i-k)%p+p)%p; if(sgn[q]<0) oldest=q;}
        if(oldest<0) ++noEdge; else image|=1ULL<<oldest;
      }
      int c=nU-__builtin_popcountll(image);
      int slack=nS-nU;
      if(c>maxC)maxC=c;
      if(slack-c<minMargin)minMargin=slack-c;
      if(slack<c){ ++bad; if(firstBad.empty()){std::string s(p,'S');for(int i=0;i<p;++i)if((w>>i)&1)s[i]='A';
        firstBad=s+" |U|="+std::to_string(nU)+" |D|="+std::to_string(nS)+" c="+std::to_string(c);} }
    }
    printf("p=%2d necklaces=%lld  slack>=c violations=%lld  maxC=%lld  min(slack-c)=%lld  %s\n",
      p,(long long)words,(long long)bad,(long long)maxC,(long long)minMargin,firstBad.c_str());
    fflush(stdout);
  }
  return 0;
}
