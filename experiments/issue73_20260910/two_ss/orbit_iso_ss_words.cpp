// Isolated singleton SS-started windows: print newest-first word and SS-gap.
#include <array>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <string>
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
 std::unordered_map<Key,std::uint32_t,Hash> latest;latest.reserve(limit*11/10);latest[{0,0}]=0;
 I a=0,P=0,W=0,first19=0;
 N sing=0, startSS=0;
 I pend_t=-1, pend_ss=-1, pend_d=-1, pend_g=-1;
 std::cout<<"protocol=H-20260910-40 isolated singleton SS-start words\n"<<std::flush;
 auto contains=[&](I v){N q=v;return q/64<seen.size()&&((seen[q/64]>>(q%64))&1);};
 auto record=[&](I v){if(v<0||v>valueCap)throw std::runtime_error("cap");N q=v;if(q/64>=seen.size())seen.resize(q/64+1);seen[q/64]|=1ULL<<(q%64);};
 for(I n=1;n<=limit;++n){
  I t=n-1;bool isS=a>n&&!contains(a-n);
  if(pend_t>=0 && t==pend_t+1){
   if(isS){
    ++sing;
    if(pend_ss){
     ++startSS;
     std::string w;
     I cap=std::min<I>(pend_d,80);
     for(I j=1;j<=cap;++j) w.push_back(signS[pend_t-j]?'S':'A');
     if(pend_d>80) w += "...";
     std::cout<<"WORD={\"t\":"<<pend_t<<",\"d\":"<<pend_d
        <<",\"gap\":"<<pend_g<<",\"w\":\""<<w<<"\"}\n"<<std::flush;
    }
   }
   pend_t=-1;
  }
  if(!isS){
   auto it=latest.find({P-1,W-t});
   if(it!=latest.end()){
    I d=t-(I)it->second;
    I lead=0; while(lead<d && !signS[t-(lead+1)]) ++lead;
    I ss=0; bool prevS=false; I first=-1, second=-1;
    for(I j=1;j<d;++j){
     bool s=signS[t-j], nxt=signS[t-(j+1)];
     if(s && nxt){
      ++ss;
      if(first<0) first=j-1; else if(second<0) second=j-1;
     }
    }
    if(ss==2 && lead==0 && d>=2){
     pend_t=t; pend_d=d; pend_ss=signS[t-2]?1:0;
     pend_g=(first>=0 && second>=0)? (second-first) : -1;
    }
  }
  }
  if(isS) signS[t]=true;
  I bit=isS?-1:1; a+=bit*n; record(a);
  if(n<=15&&a!=known[n-1])throw std::runtime_error("prefix");
  if(a==19&&!first19)first19=n;
  P+=bit;W+=t*bit;latest[{P,W}]=t+1;
 }
 if(first19!=99734)throw std::runtime_error("19");
 if(sing!=52193) throw std::runtime_error("sing");
 if(startSS!=15) throw std::runtime_error("ss");
 std::cout<<"DONE={\"singleton\":"<<sing<<",\"SS\":"<<startSS<<"}\n";
}
