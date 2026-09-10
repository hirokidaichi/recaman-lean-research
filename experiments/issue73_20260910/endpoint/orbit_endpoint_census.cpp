// H-20260910-28 canonical endpoint audit, reusing E-111's exact prefix key.
// Derived from orbit_ss_census.cpp at baseline 2ed8606; no lag cutoff.
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <unordered_map>
#include <vector>
using I=std::int64_t;using N=std::uint64_t;
struct Key{I p,w;bool operator==(const Key&b)const{return p==b.p&&w==b.w;}};
struct Hash{static N mix(N x){x+=0x9e3779b97f4a7c15ULL;x=(x^(x>>30))*0xbf58476d1ce4e5b9ULL;x=(x^(x>>27))*0x94d049bb133111ebULL;return x^(x>>31);}std::size_t operator()(const Key&k)const{return mix(k.p)^mix(k.w+0x123456789ULL);}};
int main(){
 constexpr I limit=10000000,valueCap=2000000000;
 constexpr std::array<I,15> known={1,3,6,2,7,13,20,12,21,11,22,10,23,9,24};
 std::vector<N> seen(1,1);std::vector<bool> signS(limit),used(limit);
 std::vector<I> ssTimes;
 auto contains=[&](I v){N q=v;return q/64<seen.size()&&((seen[q/64]>>(q%64))&1);};
 auto record=[&](I v){if(v<0||v>valueCap)throw std::runtime_error("value cap exceeded");N q=v;if(q/64>=seen.size())seen.resize(q/64+1);seen[q/64]|=1ULL<<(q%64);};
 std::unordered_map<Key,std::uint32_t,Hash> latest;latest.reserve(limit*11/10);latest[{0,0}]=0;
 I a=0,P=0,W=0,maxValue=0,first19=0,lo=1;
 N A=0,S=0,supplied=0,clean=0,oneSS=0,newBeyondOld=0,oldBeyondNew=0,maxLag=0;
 for(I n=1;n<=limit;++n){
  I t=n-1;bool isS=a>n&&!contains(a-n);I bit=isS?-1:1;
  if(isS)++S;else{
   ++A;auto it=latest.find({P-1,W-t});
   if(it!=latest.end()){
    ++supplied;I q=it->second,d=t-q;
    if(d<3||d%4!=3)throw std::runtime_error("minimum P2 lag parity");
    I ss=ssTimes.end()-std::lower_bound(ssTimes.begin(),ssTimes.end(),q+1);
    if(ss<=1){
     if(!signS[q]||used[q])throw std::runtime_error("minimum endpoint non-S or collision");
     used[q]=true;clean+=ss==0;oneSS+=ss==1;newBeyondOld+=ss==1&&d>11;
     maxLag=std::max<N>(maxLag,d);
    }else if(d<=11){
     ++oldBeyondNew;
     std::cout<<"SHORT_OUTSIDE_NEW={\"step\":"<<n<<",\"sign_time\":"<<t<<",\"lag\":"<<d<<",\"SS\":"<<ss<<",\"endpoint\":"<<q<<",\"endpoint_is_A\":"<<(!signS[q]?"true":"false")<<",\"backward_word\":\"";
     for(I j=1;j<=d;++j)std::cout<<(signS[t-j]?'S':'A');
     std::cout<<"\"}\n";
    }
   }
  }
  if(isS){if(t>=1&&signS[t-1])ssTimes.push_back(t);if(t>=3&&signS[t-3]&&!signS[t-2]&&!signS[t-1])throw std::runtime_error("canonical SAAS");signS[t]=true;}
  a+=bit*n;record(a);maxValue=std::max(maxValue,a);if(n<=15&&a!=known[n-1])throw std::runtime_error("initial prefix");if(a==19&&!first19)first19=n;
  P+=bit;W+=t*bit;latest[{P,W}]=t+1;
  if(n==100000||n==1000000||n==limit){
   std::cout<<"RANGE={\"from\":"<<lo<<",\"through\":"<<n<<",\"A\":"<<A<<",\"S\":"<<S<<",\"finite_P2_A\":"<<supplied<<",\"clean\":"<<clean<<",\"one_SS\":"<<oneSS<<",\"low_SS_joint\":"<<(clean+oneSS)<<",\"new_beyond_old_U11_clean\":"<<newBeyondOld<<",\"old_short_outside_new\":"<<oldBeyondNew<<",\"max_low_SS_minimum_lag\":"<<maxLag<<",\"endpoint_violations\":0}\n";
   std::cout<<"CHECKPOINT={\"step\":"<<n<<",\"value\":"<<a<<",\"P\":"<<P<<",\"W\":"<<W<<",\"prefix_keys\":"<<latest.size()<<",\"maximum_value\":"<<maxValue<<",\"first_19\":"<<first19<<"}\n"<<std::flush;
   A=S=supplied=clean=oneSS=newBeyondOld=oldBeyondNew=maxLag=0;lo=n+1;
  }
 }
 if(first19!=99734)throw std::runtime_error("first 19 reference");
 std::cout<<"PASS: all low-SS minimum suppliers use distinct actual S endpoints through 10000000 steps\n";
}
