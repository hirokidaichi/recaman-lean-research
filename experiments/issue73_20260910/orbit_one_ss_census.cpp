#include <algorithm>
#include <cstdint>
#include <iostream>
#include <map>
#include <stdexcept>
#include <unordered_map>
#include <vector>
using I=std::int64_t;using U=std::uint64_t;
struct Key{I p,w;bool operator==(const Key&b)const{return p==b.p&&w==b.w;}};
struct Hash{static U mix(U x){x+=0x9e3779b97f4a7c15ULL;x=(x^(x>>30))*0xbf58476d1ce4e5b9ULL;x=(x^(x>>27))*0x94d049bb133111ebULL;return x^(x>>31);}std::size_t operator()(const Key&k)const{return mix(k.p)^mix(k.w+0x123456789ULL);}};
int main(){
 constexpr I limit=10000000;std::vector<U> seen(1,1);
 auto has=[&](I v){return U(v)/64<seen.size()&&((seen[U(v)/64]>>(v%64))&1);};
 auto add=[&](I v){if(v<0||v>2000000000)throw std::runtime_error("value cap");if(U(v)/64>=seen.size())seen.resize(U(v)/64+1);seen[U(v)/64]|=1ULL<<(v%64);};
 std::unordered_map<Key,std::uint32_t,Hash> latest;latest.reserve(11000000);latest[{0,0}]=0;
 std::vector<I> subs,ss;std::vector<std::pair<I,I>> giants;std::vector<bool> signs(limit);
 std::map<I,std::vector<std::pair<I,I>>> demand;
 I value=0,P=0,W=0,run=0,A=0,B=0,supplied=0,one=0,maxlag=0,rangeA=0,rangeB=0;
 for(I step=1;step<=limit;++step){I t=step-1;bool S=value>step&&!has(value-step);
  if(S){if(run>=3)giants.push_back({t,run});}
  else{auto it=latest.find({P-1,W-t});if(it!=latest.end()){
   ++supplied;I d=t-it->second,u=t-d;
   I ssCount=ss.end()-std::lower_bound(ss.begin(),ss.end(),u+1);
   if(ssCount==1){
    ++one;maxlag=std::max(maxlag,d);I pair=ss.back();
    if(giants.empty())throw std::runtime_error("no giant");auto [E,len]=giants.back();
    if(E-len-1<u)throw std::runtime_error("giant not internal");
    if(giants.size()>1&&giants[giants.size()-2].first-giants[giants.size()-2].second-1>=u)throw std::runtime_error("two giants");
    I j=subs.end()-std::lower_bound(subs.begin(),subs.end(),E);
    I z=subs.end()-std::lower_bound(subs.begin(),subs.end(),pair);I n=(d-1)/2;
    if(!signs[u]||j==z||j<1||z<1||j>=n||z>=n)throw std::runtime_error("gap boundary");
    if(run==0){if(len!=4||n!=6*j-2*z+1)throw std::runtime_error("family A");++A;++rangeA;}
    else if(run==1){if(len!=3||n!=4*j-2*z+1)throw std::runtime_error("family B");++B;++rangeB;}
    else throw std::runtime_error("bad leading gap");
    demand[pair].push_back({t,d});
   }
  }}
  signs[t]=S;if(S){subs.push_back(t);if(t>0&&signs[t-1])ss.push_back(t);run=0;}else ++run;
  I sign=S?-1:1;P+=sign;W+=t*sign;value+=step*sign;add(value);latest[{P,W}]=step;
  if(step==100000||step==1000000||step==limit){
   std::size_t max=0;I arg=-1;std::map<std::size_t,I>hist;
   for(auto&[k,v]:demand){++hist[v.size()];if(v.size()>max){max=v.size();arg=k;}}
   std::cout<<"CHECKPOINT={\"through\":"<<step<<",\"finite_P2_A\":"<<supplied<<",\"one_SS\":"<<one<<",\"family_A\":"<<A<<",\"family_B\":"<<B<<",\"increment_A\":"<<rangeA<<",\"increment_B\":"<<rangeB<<",\"max_lag\":"<<maxlag<<",\"max_sources_per_SS\":"<<max<<",\"SS_sign_times\":["<<arg-1<<','<<arg<<"],\"sources\":[";
   bool first=true;for(auto[t,d]:demand[arg]){if(!first)std::cout<<',';first=false;std::cout<<"{\"t\":"<<t<<",\"lag\":"<<d<<'}';}
   std::cout<<"],\"multiplicity_hist\":{";first=true;for(auto[k,v]:hist){if(!first)std::cout<<',';first=false;std::cout<<'"'<<k<<"\":"<<v;}std::cout<<"}}\n"<<std::flush;rangeA=rangeB=0;
  }
 }
 if(supplied!=1315896)throw std::runtime_error("old census total mismatch");
 std::cout<<"PASS: exact one-SS classification and shared-defect multiplicity on canonical prefix\n";
}
