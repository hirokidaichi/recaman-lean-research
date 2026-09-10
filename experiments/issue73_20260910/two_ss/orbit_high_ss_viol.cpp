// Same-ss run violations for min P2 with ss>=64.
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
 std::unordered_map<Key,std::uint32_t,Hash> latest;latest.reserve(limit*11/10);latest[{0,0}]=0;
 I a=0,P=0,W=0,first19=0;
 I run_last_t=-1,run_last_d=-1,run_last_ss=-1; N nviol=0;
 std::cout<<"protocol=H-20260910-36 high-SS same-run min P2 pairs ss>=64\n"<<std::flush;
 auto contains=[&](I v){N q=v;return q/64<seen.size()&&((seen[q/64]>>(q%64))&1);};
 auto record=[&](I v){if(v<0||v>valueCap)throw std::runtime_error("cap");N q=v;if(q/64>=seen.size())seen.resize(q/64+1);seen[q/64]|=1ULL<<(q%64);};
 for(I n=1;n<=limit;++n){
  I t=n-1;bool isS=a>n&&!contains(a-n);
  if(isS){run_last_t=-1; run_last_ss=-1;}
  else{
   auto it=latest.find({P-1,W-t});
   if(it!=latest.end()){
    I d=t-(I)it->second;
    I ss=0;bool prevS=false;
    for(I j=1;j<=d;++j){bool s=signS[t-j];if(s&&prevS)++ss;prevS=s;}
    if(ss>=64){
     if(run_last_t>=0 && run_last_ss>=64){
      ++nviol;
      I extra_len=run_last_d-(d-1);
      I em=0,eM=0,ess=0; bool prev=false, first=true;
      I start=d; // newest-first extra starts at lag d of old window = lag (f) of old? old=v++extra, v len=d-1? later lag f=d, v len=f-1=d-1, extra from lag d of old window
      // extra = oldest extra_len signs of previous window, newest-first index f-1 = d-1
      for(I j=d; j<=run_last_d; ++j){
       bool s=signS[run_last_t-j];
       I bit=s?-1:1; em+=bit; eM+=(j-(d-1))*bit;
       if(!first && s && prev) ++ess; prev=s; first=false;
      }
      std::cout<<"VIOL={\"prev_t\":"<<run_last_t<<",\"prev_d\":"<<run_last_d
        <<",\"t\":"<<t<<",\"d\":"<<d<<",\"ss\":"<<ss
        <<",\"gap\":"<<(t-run_last_t)
        <<",\"extra_len\":"<<extra_len
        <<",\"extra_mass\":"<<em<<",\"extra_moment\":"<<eM
        <<",\"extra_ss\":"<<ess
        <<",\"need_moment\":"<<(1-(I)(d-1))
        <<"}\n"<<std::flush;
     }
     run_last_t=t; run_last_d=d; run_last_ss=ss;
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
 std::cout<<"HIGH_VIOL="<<nviol<<"\n";
}
