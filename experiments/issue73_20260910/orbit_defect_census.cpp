// H-20260910-10, derived from the frozen H-07b census: exact finite-history P2 supply census, with no lag cutoff.
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <map>
#include <stdexcept>
#include <unordered_map>
#include <vector>

using I = std::int64_t;
using N = std::uint64_t;

struct Key {
  I p, w;
  bool operator==(const Key& b) const { return p == b.p && w == b.w; }
};
struct Hash {
  static N mix(N x) {
    x += 0x9e3779b97f4a7c15ULL;
    x = (x ^ (x >> 30)) * 0xbf58476d1ce4e5b9ULL;
    x = (x ^ (x >> 27)) * 0x94d049bb133111ebULL;
    return x ^ (x >> 31);
  }
  std::size_t operator()(const Key& k) const {
    return mix(static_cast<N>(k.p)) ^ mix(static_cast<N>(k.w) + 0x123456789ULL);
  }
};

struct Stats {
  N A=0, S=0, supplied=0, short11=0, no_supply=0, sharp12=0, pointwise_union=0;
  N nonsharp_union=0, max_run=0, max_lag=0;
  N local_clean=0, long_clean=0, hybrid=0;
  std::map<N,N> clean_runs, clean_lag_bins, defect_hist, residual_defect_hist;
  N one_defect=0, one_defect_residual=0;
  std::array<N,7> fixedR{};
  std::map<N,N> all_A_runs, supplied_runs, residual_runs, lag_bins;
};

template<class K,class V> void PrintMap(const std::map<K,V>& m) {
  std::cout << '{';
  bool first=true;
  for (auto [k,v]:m) {
    if (!first) std::cout << ',';
    first=false;
    std::cout << '"' << k << "\":" << v;
  }
  std::cout << '}';
}

void Report(const Stats& s,N lo,N hi) {
  std::cout << "RANGE={\"from\":" << lo << ",\"through\":" << hi
    << ",\"A\":" << s.A << ",\"S\":" << s.S << ",\"finite_history_P2_A\":" << s.supplied
    << ",\"U11\":" << s.short11 << ",\"no_finite_history_P2_A\":" << s.no_supply
    << ",\"old_sharp_m_ge_12\":" << s.sharp12
    << ",\"diagnostic_union_over_R\":" << s.pointwise_union
    << ",\"nonsharp_in_diagnostic_union\":" << s.nonsharp_union
    << ",\"max_preceding_A_run\":" << s.max_run << ",\"max_minimum_P2_lag\":" << s.max_lag
    << ",\"fixed_R_0_1_2_3_4_8_16\":[";
  for (std::size_t i=0;i<s.fixedR.size();++i) {if(i)std::cout<<',';std::cout<<s.fixedR[i];}
  std::cout << "],\"A_by_preceding_run\":"; PrintMap(s.all_A_runs);
  std::cout << ",\"supplied_A_by_run\":"; PrintMap(s.supplied_runs);
  std::cout << ",\"supplied_outside_U11_and_oldsharp_and_diagnostic_union_by_run\":"; PrintMap(s.residual_runs);
  std::cout << ",\"minimum_lag_bin_upper_bounds\":"; PrintMap(s.lag_bins);
  std::cout << ",\"local_clean\":" << s.local_clean << ",\"long_clean\":" << s.long_clean
    << ",\"U11_union_local_clean\":" << s.hybrid << ",\"clean_by_run\":";
  PrintMap(s.clean_runs); std::cout << ",\"clean_lag_bins\":"; PrintMap(s.clean_lag_bins);
  std::cout << ",\"even_S_count_hist\":"; PrintMap(s.defect_hist);
  std::cout << ",\"residual_even_S_count_hist\":"; PrintMap(s.residual_defect_hist);
  std::cout << ",\"one_defect\":" << s.one_defect << ",\"one_defect_residual\":" << s.one_defect_residual;
  std::cout << "}\n" << std::flush;
}

int main() {
  constexpr I limit=10000000;
  constexpr I valueCap=2000000000;
  constexpr std::array<I,7> Rs={0,1,2,3,4,8,16};
  constexpr std::array<I,15> known={1,3,6,2,7,13,20,12,21,11,22,10,23,9,24};
  std::vector<N> seen(1,1);
  auto contains=[&](I v) {N q=static_cast<N>(v);return q/64<seen.size() && ((seen[q/64]>>(q%64))&1);};
  auto record=[&](I v) {
    if (v<0 || v>valueCap) throw std::runtime_error("declared value cap exceeded");
    N q=static_cast<N>(v);
    if (q/64>=seen.size()) seen.resize(q/64+1,0);
    seen[q/64]|=1ULL<<(q%64);
  };
  std::unordered_map<Key,std::uint32_t,Hash> latest;
  latest.reserve(static_cast<std::size_t>(limit*11/10));
  latest[{0,0}]=0;
  I a=0,P=0,W=0,run=0,maxValue=0;
  std::array<I,2> lastS={-1,-1};
  std::array<std::vector<I>,2> subTimes;
  std::vector<bool> signS(limit,false), usedCharge(limit,false);
  const std::map<int,int> phi11={{1795,10},{1669,3},{1609,4},{1417,4},{1585,6},{1361,7},{913,8},{1606,10},{1414,9},{1578,4},{1354,4},{906,4},{1330,6},{738,7},{1144,6},{696,6},{472,7}};
  N first19=0,lo=1;
  Stats st;
  for (I n=1;n<=limit;++n) {
    I t=n-1;
    const bool isS=a>n && !contains(a-n);
    I bit=isS?-1:1;
    if (isS) {++st.S;} else {
      ++st.A; ++st.all_A_runs[run]; st.max_run=std::max<N>(st.max_run,run);
      auto it=latest.find({P-1,W-t});
      if (it==latest.end()) ++st.no_supply;
      else {
        I d=t-it->second;
        if (d<3 || d%4!=3 || (run>=3 && d<4*run-1))
          throw std::runtime_error("P2 classification/lower-bound audit failure");
        ++st.supplied; ++st.supplied_runs[run];
        st.max_lag=std::max<N>(st.max_lag,d);
        bool short11=d<=11;
        bool oldsharp=run>=12 && d==4*run-1;
        bool anyR=run>=13 && d<=5*run-14;
        st.short11+=short11; st.sharp12+=oldsharp; st.pointwise_union+=anyR;
        st.nonsharp_union+=anyR && d>4*run-1;
        for (std::size_t j=0;j<Rs.size();++j)
          st.fixedR[j]+=run>=4*Rs[j]+13 && d<=4*run-1+4*Rs[j];
        if (!short11 && !oldsharp && !anyR) ++st.residual_runs[run];
        N bin=d<=11?d:d<=100?100:d<=1000?1000:d<=10000?10000:d<=100000?100000:10000000;
        ++st.lag_bins[bin];
        const auto& sameParity=subTimes[t%2];
        I b=sameParity.end()-std::lower_bound(sameParity.begin(),sameParity.end(),t-d);
        I bbin=b<=10?b:b<=100?100:b<=1000?1000:b<=10000?10000:10000000;
        ++st.defect_hist[bbin];
        st.one_defect+=b==1;
        st.one_defect_residual+=b==1 && !short11;
        if(b%2!=((d-3)/4)%2)throw std::runtime_error("defect parity identity failure");
        bool clean=std::min(lastS[0],lastS[1])<t-d;
        if(clean!=(b==0))throw std::runtime_error("clean orientation mismatch");
        if(!short11 && !clean)++st.residual_defect_hist[bbin];
        st.local_clean+=clean; st.long_clean+=clean && d>=19; st.hybrid+=short11 || clean;
        if(clean){
          if(d%8!=3)throw std::runtime_error("local clean lag classification mismatch");
          ++st.clean_runs[run]; ++st.clean_lag_bins[bin];
        }
        if(short11 || clean){
          I off=(d+3)/2;
          if(d==7)off=signS[t-1]?7:5;
          if(d==11){int mask=0;for(int i=1;i<=11;++i)if(signS[t-i])mask|=1<<(i-1);off=phi11.at(mask);}
          I q=t-off;
          if(q<0 || !signS[q] || usedCharge[q])throw std::runtime_error("hybrid charge collision or non-S target");
          usedCharge[q]=true;
        }
      }
    }
    if(isS){lastS[t%2]=t;signS[t]=true;subTimes[t%2].push_back(t);}
    a+=bit*n; record(a); maxValue=std::max(maxValue,a);
    if (n<=15 && a!=known[n-1]) throw std::runtime_error("standard prefix mismatch");
    if (a==19 && first19==0) first19=n;
    P+=bit; W+=t*bit; latest[{P,W}]=static_cast<std::uint32_t>(t+1);
    run=isS?0:run+1;
    if (n==100000 || n==1000000 || n==limit) {
      Report(st,lo,n); st=Stats{};lo=n+1;
      std::cout << "CHECKPOINT={\"n\":" << n << ",\"value\":" << a << ",\"P\":" << P
        << ",\"W\":" << W << ",\"prefix_keys\":" << latest.size()
        << ",\"maximum_value\":" << maxValue << ",\"first_19\":" << first19 << "}\n" << std::flush;
    }
  }
  if(first19!=99734)throw std::runtime_error("first-19 Lean reference mismatch");
  std::cout << "PASS: exact parity-defect census and defect parity identity through 10000000 steps\n";
}
