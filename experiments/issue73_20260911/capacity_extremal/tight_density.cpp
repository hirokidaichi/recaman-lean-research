// Protocol H-20260911-11: max net |U|-|D| broken down by the number of subtractions.
// Shows that tightness is not an artefact of S-sparse words: the largest |D| attaining
// |U| = |D| grows with the period, and slack appears only above an S-density threshold.
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
  printf("protocol=H-20260911-02 slack by subtraction count\n");
  for(p=plo;p<=phi;++p){
    uint64_t full=(1ULL<<p)-1;
    std::vector<int> best(p+1,-1000);          // max (|U|-|D|) among words with that many S
    std::vector<std::string> wit(p+1);
    for(uint64_t w=0;w<=full;++w){
      int pc=__builtin_popcountll(w); int sigma=2*pc-p; int nS=p-pc;
      if(sigma<=0) continue;
      if(!isMinRotation(w)) continue;
      for(int i=0;i<p;++i) sgn[i]=((w>>i)&1)?1:-1;
      Gmin=0;
      for(int s=0;s<p;++s){int acc=0;for(int l=1;l<=p;++l){acc+=sgn[((s-l)%p+p)%p];if(acc<Gmin)Gmin=acc;}}
      int stopS=1-Gmin; int supplied=0;
      for(int i=0;i<p;++i){
        if(sgn[i]<0) continue;
        int S=0; I M=0; int idx=i;
        for(I d=1;;++d){
          idx=(idx-1+p)%p; int v=sgn[idx]; S+=v; M+=d*v;
          if(S==1&&M==0){++supplied;break;}
          if(S>stopS) break;
        }
      }
      int surplus=supplied-nS;
      if(surplus>best[nS]){best[nS]=surplus;std::string s(p,'S');for(int i=0;i<p;++i)if((w>>i)&1)s[i]='A';wit[nS]=s;}
    }
    printf("p=%2d",p);
    for(int k=0;k<=p;++k) if(best[k]>-1000) printf(" | S=%d:%+d",k,best[k]);
    printf("\n");
    for(int k=0;k<=p;++k) if(best[k]==0) printf("   TIGHT p=%d S=%d %s\n",p,k,wit[k].c_str());
    fflush(stdout);
  }
  return 0;
}
