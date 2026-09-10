// Search SS=2 min windows whose extra is minWord, and dump a=1 windows.
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
static bool is_minword(const std::vector<bool>& S, I t, I start, I r){
 // extra newest-first from lag start, length 2r+3: AA (SA)^r S
 // lag j=start .. start+2r+2, signS[t-j]
 I L=2*r+3;
 if(start+L-1>t) return false;
 auto at=[&](I k){return S[t-(start+k)];}; // k=0 newest of extra
 if(at(0)||at(1)) return false; // need A A (signS false means A)
 for(I i=0;i<r;i++){
  I k=2+2*i;
  if(!at(k) || at(k+1)) return false; // S A
 }
 if(!at(2*r+2)) return false; // final S
 return true;
}
int main(){
 constexpr I limit=10000000,valueCap=2000000000;
 constexpr std::array<I,15> known={1,3,6,2,7,13,20,12,21,11,22,10,23,9,24};
 std::vector<N> seen(1,1);
 std::vector<bool> signS(limit);
 std::unordered_map<Key,std::uint32_t,Hash> latest;latest.reserve(limit*11/10);latest[{0,0}]=0;
 I a=0,P=0,W=0,first19=0;
 N ss2=0,lead1=0,minword_hits=0,d_mod3_1=0,d_ge31=0;
 std::cout<<"protocol=H-20260910-34 SS=2 minWord extra search canonical 10^7\n";
 auto contains=[&](I v){N q=v;return q/64<seen.size()&&((seen[q/64]>>(q%64))&1);};
 auto record=[&](I v){if(v<0||v>valueCap)throw std::runtime_error("cap");N q=v;if(q/64>=seen.size())seen.resize(q/64+1);seen[q/64]|=1ULL<<(q%64);};
 for(I n=1;n<=limit;++n){
  I t=n-1;bool isS=a>n&&!contains(a-n);
  if(!isS){
   auto it=latest.find({P-1,W-t});
   if(it!=latest.end()){
    I q=it->second,d=t-q;
    I ss=0;bool prevS=false;
    for(I j=1;j<=d;++j){bool s=signS[t-j];if(s&&prevS)++ss;prevS=s;}
    if(ss==2){
     ++ss2;
     I lead=0; while(lead<d && !signS[t-(lead+1)]) ++lead;
     if(lead==1){
      ++lead1;
      std::string w; I m=0,M=0;
      for(I j=1;j<=std::min<I>(d,16);++j){w.push_back(signS[t-j]?'S':'A');}
      std::cout<<"LEAD1={\"t\":"<<t<<",\"d\":"<<d<<",\"head\":\""<<w<<"\"}\n";
     }
     if(d>=31){
      ++d_ge31;
      if((d-4)%3==0){
       ++d_mod3_1;
       I r=(d-4)/3;
       I n_v=r+1;
       if(is_minword(signS,t,n_v+1,r)){
        ++minword_hits;
        std::cout<<"MINWORD={\"t\":"<<t<<",\"d\":"<<d<<",\"r\":"<<r<<"}\n";
       }
      }
     }
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
 std::cout<<"SS2={\"count\":"<<ss2<<",\"lead1\":"<<lead1
   <<",\"d_ge31\":"<<d_ge31<<",\"len_3r4\":"<<d_mod3_1
   <<",\"minword_suffix\":"<<minword_hits<<"}\n";
 if(ss2!=52357) throw std::runtime_error("ss2 count");
 std::cout<<(minword_hits==0?"PASS: no minWord extra on SS=2 through 10000000\n"
                            :"FAIL: minWord extra present\n");
}
