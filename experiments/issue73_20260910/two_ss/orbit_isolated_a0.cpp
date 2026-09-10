// H-20260910-31: isolated a=0 previous-S vs E-128 low-SS endpoints.
// Exact prefix-key minimum P2, no lag cutoff. Standard 10^7 steps.
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <unordered_map>
#include <vector>
using I=std::int64_t;using N=std::uint64_t;
struct Key{I p,w;bool operator==(const Key&b)const{return p==b.p&&w==b.w;}};
struct Hash{
 static N mix(N x){x+=0x9e3779b97f4a7c15ULL;x=(x^(x>>30))*0xbf58476d1ce4e5b9ULL;x=(x^(x>>27))*0x94d049bb133111ebULL;return x^(x>>31);}
 std::size_t operator()(const Key&k)const{return mix(k.p)^mix(k.w+0x123456789ULL);}
};
int main(){
 constexpr I limit=10000000,valueCap=2000000000;
 constexpr std::array<I,15> known={1,3,6,2,7,13,20,12,21,11,22,10,23,9,24};
 std::vector<N> seen(1,1);
 std::vector<bool> signS(limit);
 std::vector<I> low_who(limit,-1), iso_who(limit,-1);
 std::unordered_map<Key,std::uint32_t,Hash> latest;latest.reserve(limit*11/10);latest[{0,0}]=0;
 I a=0,P=0,W=0,first19=0,lo=1;
 N A=0,S=0,supplied=0,low=0,iso=0,comp=0,joint=0,shown=0,maxLag=0;
 auto contains=[&](I v){N q=v;return q/64<seen.size()&&((seen[q/64]>>(q%64))&1);};
 auto record=[&](I v){if(v<0||v>valueCap)throw std::runtime_error("value cap");N q=v;if(q/64>=seen.size())seen.resize(q/64+1);seen[q/64]|=1ULL<<(q%64);};
 for(I n=1;n<=limit;++n){
  I t=n-1;bool isS=a>n&&!contains(a-n);
  if(isS) ++S;
  else{
   ++A;
   auto it=latest.find({P-1,W-t});
   if(it!=latest.end()){
    ++supplied;I q=it->second,d=t-q;
    if(d<3||d%4!=3)throw std::runtime_error("min P2 lag parity");
    I lead=0;
    while(lead<d && !signS[t-(lead+1)]) ++lead;
    I ss=0;bool prevS=false;
    for(I j=1;j<=d;++j){bool s=signS[t-j];if(s&&prevS)++ss;prevS=s;}
    if(ss<=1){
     ++low;
     I endp=t-d;
     if(endp<0||endp>=limit)throw std::runtime_error("endpoint range");
     if(!signS[endp])throw std::runtime_error("low-SS endpoint not S");
     if(low_who[endp]>=0)throw std::runtime_error("low-SS endpoint collision");
     low_who[endp]=t;
    }else if(ss==2 && lead==0){
     ++iso;maxLag=std::max<N>(maxLag,(N)d);
     if(t<1||!signS[t-1])throw std::runtime_error("isolated a=0 previous not S");
     I prev=t-1;
     if(iso_who[prev]>=0)throw std::runtime_error("isolated previous-S self collision");
     iso_who[prev]=t;
    }else if(ss==2) ++comp;
   }
  }
  if(isS) signS[t]=true;
  I bit=isS?-1:1;
  a+=bit*n;record(a);
  if(n<=15&&a!=known[n-1])throw std::runtime_error("initial prefix");
  if(a==19&&!first19)first19=n;
  P+=bit;W+=t*bit;latest[{P,W}]=t+1;
  if(n==100000||n==1000000||n==limit){
   N j=0;
   for(I i=0;i<n && i<limit;++i) if(low_who[i]>=0 && iso_who[i]>=0) ++j;
   std::cout<<"RANGE={\"from\":"<<lo<<",\"through\":"<<n
     <<",\"A\":"<<A<<",\"S\":"<<S<<",\"finite_P2_A\":"<<supplied
     <<",\"low_SS\":"<<low<<",\"isolated_a0\":"<<iso<<",\"other_ss2\":"<<comp
     <<",\"joint_hits_cumulative\":"<<j<<",\"max_iso_lag\":"<<maxLag<<"}\n"<<std::flush;
   A=S=supplied=low=iso=comp=maxLag=0;lo=n+1;
  }
 }
 if(first19!=99734)throw std::runtime_error("first 19 reference");
 for(I i=0;i<limit;++i){
  if(low_who[i]>=0 && iso_who[i]>=0){
   ++joint;
   if(shown<12){
    I t=iso_who[i], u=low_who[i];
    std::cout<<"JOINT={\"S\":"<<i<<",\"iso_source\":"<<t<<",\"low_source\":"<<u
      <<",\"iso_lag\":"<<(t-(i))<<",\"low_lag\":"<<(u-i)<<"}\n";
    ++shown;
   }
  }
 }
 std::cout<<"TOTAL_JOINT="<<joint<<"\n";
 if(joint==0) std::cout<<"PASS: isolated a=0 previous-S disjoint from low-SS endpoints through "<<limit<<" steps\n";
 else std::cout<<"FAIL: isolated a=0 previous-S hits low-SS endpoints, count="<<joint<<"\n";
}
