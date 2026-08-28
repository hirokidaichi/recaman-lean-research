#include <cstdint>
#include <iostream>
#include <limits>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

struct Bits {
  std::vector<std::uint64_t> w;
  bool get(std::uint64_t x) const {
    std::uint64_t i=x>>6;
    return i<w.size() && ((w[i]>>(x&63))&1ULL);
  }
  void set(std::uint64_t x) {
    std::uint64_t i=x>>6;
    if(i>=w.size()) w.resize(i+1);
    w[i]|=1ULL<<(x&63);
  }
};

int main(int argc,char**argv){
  std::uint64_t N=argc>1?std::stoull(argv[1]):1000000000ULL;
  const std::uint64_t blockersArr[]={6,843,656510,1179863,5784585,
    36799569,203538457,1023122439};
  std::unordered_set<std::uint64_t> watch(std::begin(blockersArr),std::end(blockersArr));
  std::unordered_map<std::uint64_t,std::uint64_t> firstWatch;
  std::unordered_map<std::uint64_t,char> firstWatchBranch;
  Bits seen;seen.set(0);
  std::uint64_t a=0;
  bool currentFirst=true;
  char enteredBy='I';
  std::uint64_t minR[64], minRAt[64];
  std::int64_t minG[64];
  long double uniformExpected[64]{};
  std::uint64_t stateCount[64]{}, borrowCount[64]{};
  for(int i=0;i<64;++i){
    minR[i]=std::numeric_limits<std::uint64_t>::max();
    minRAt[i]=0;
    minG[i]=std::numeric_limits<std::int64_t>::max();
  }
  std::cout<<"n,branch,q,r,G,y,prestateFirst,enteredBy,yFirstAt,yFirstBranch,nextQ,nextG\n";
  std::cerr<<"n,branch,b,q,r,G,candidate,currentFirst,enteredBy\n";
  for(std::uint64_t step=1;step<=N;++step){
    std::uint64_t old=a;
    bool sub=old>step&&!seen.get(old-step);
    std::uint64_t next=sub?old-step:old+step;
    bool nextFirst=!seen.get(next);
    if(nextFirst && watch.count(next)) {
      firstWatch[next]=step;
      firstWatchBranch[next]=sub?'-':'+';
    }
    seen.set(next);
    if(step>1){
      std::uint64_t n=step-1,q=old/n,r=old%n;
      std::int64_t G=(std::int64_t)r-(std::int64_t)(q*(q+1)/2);
      if(q<64 && r<minR[q]){minR[q]=r;minRAt[q]=n;}
      if(q<64 && G<minG[q])minG[q]=G;
      if(q<64){
        stateCount[q]++;
        uniformExpected[q]+=(long double)q/(long double)n;
      }
      std::uint64_t d=q>r?q-r:0;
      std::uint64_t b=d?(d+n)/(n+1):0;
      if(G<0){
        std::uint64_t cand=old>(n+1)?old-(n+1):0;
        std::cerr<<n<<","<<(sub?'-':'+')<<","<<b<<","<<q<<","<<r
          <<","<<G<<","<<cand<<","<<(currentFirst?1:0)<<","<<enteredBy<<"\n";
      }
      if(b==1){
        if(q<64)borrowCount[q]++;
        std::uint64_t y=old>(n+1)?old-(n+1):0;
        std::uint64_t nq=next/step,nr=next%step;
        std::int64_t nG=(std::int64_t)nr-(std::int64_t)(nq*(nq+1)/2);
        std::cout<<n<<","<<(sub?'-':'+')<<","<<q<<","<<r<<","<<G
          <<","<<y<<","<<(currentFirst?1:0)<<","<<enteredBy<<",";
        auto it=firstWatch.find(y);
        if(it==firstWatch.end()) std::cout<<"NA,NA";
        else std::cout<<it->second<<","<<firstWatchBranch[y];
        std::cout<<","<<nq<<","<<nG<<"\n";
      }
    }
    a=next; currentFirst=nextFirst; enteredBy=sub?'-':'+';
  }
  std::cerr<<"MINIMA\n";
  for(int q=0;q<64;++q) if(minR[q]!=std::numeric_limits<std::uint64_t>::max())
    std::cerr<<q<<","<<minR[q]<<","<<minRAt[q]<<","<<minG[q]
      <<","<<stateCount[q]<<","<<(double)uniformExpected[q]
      <<","<<borrowCount[q]<<"\n";
}
