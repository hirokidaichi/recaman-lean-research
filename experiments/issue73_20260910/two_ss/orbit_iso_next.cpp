// For the five isolated a=0 SS=2 sources with e(t+1)=A, record the next
// current-A min P2 if it exists (not a named S-charge).
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
 const std::array<I,5> targets={196641,2866284,7906786,8642654,8775876};
 std::array<int,5> follow={};
 std::vector<N> seen(1,1);
 std::vector<bool> signS(limit);
 std::unordered_map<Key,std::uint32_t,Hash> latest;latest.reserve(limit*11/10);latest[{0,0}]=0;
 I a=0,P=0,W=0,first19=0;
 std::cout<<"protocol=H-20260910-35 isolated a=0 nonsingleton following A-run P2\n"<<std::flush;
 auto contains=[&](I v){N q=v;return q/64<seen.size()&&((seen[q/64]>>(q%64))&1);};
 auto record=[&](I v){if(v<0||v>valueCap)throw std::runtime_error("cap");N q=v;if(q/64>=seen.size())seen.resize(q/64+1);seen[q/64]|=1ULL<<(q%64);};
 for(I n=1;n<=limit;++n){
  I t=n-1; bool isS=a>n&&!contains(a-n);
  for(size_t i=0;i<targets.size();++i){
   if(follow[i]){
    if(isS){
     std::cout<<"RUNEND={\"iso_t\":"<<targets[i]<<",\"s_at\":"<<t<<"}\n"<<std::flush;
     follow[i]=0;
    }else{
     auto it=latest.find({P-1,W-t});
     if(it==latest.end())
      std::cout<<"FOLLOW={\"iso_t\":"<<targets[i]<<",\"t\":"<<t<<",\"no_p2\":1}\n"<<std::flush;
     else{
      I d=t-(I)it->second;
      I ss=0; bool prevS=false;
      for(I j=1;j<=d;++j){bool s=signS[t-j]; if(s&&prevS)++ss; prevS=s;}
      I lead=0; while(lead<d && !signS[t-(lead+1)]) ++lead;
      std::cout<<"FOLLOW={\"iso_t\":"<<targets[i]<<",\"t\":"<<t<<",\"d\":"<<d
        <<",\"ss\":"<<ss<<",\"lead\":"<<lead<<"}\n"<<std::flush;
     }
    }
   }
   if(t==targets[i]) follow[i]=1;
  }
  if(isS) signS[t]=true;
  I bit=isS?-1:1; a+=bit*n; record(a);
  if(n<=15&&a!=known[n-1])throw std::runtime_error("prefix");
  if(a==19&&!first19)first19=n;
  P+=bit;W+=t*bit;latest[{P,W}]=t+1;
 }
 if(first19!=99734)throw std::runtime_error("19");
 std::cout<<"DONE\n";
}
