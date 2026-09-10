// SS=3 minimum P2: leading A-run, one-per-run, S-ended prefix existence.
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
 N ss3=0,lead0=0,lead1=0,leadge3=0,lead2=0,run_ss3=0,run_viol=0,endS=0,g_run_viol=0;
 I run_last_t=-1,run_last_d=-1;
 auto contains=[&](I v){N q=v;return q/64<seen.size()&&((seen[q/64]>>(q%64))&1);};
 auto record=[&](I v){if(v<0||v>valueCap)throw std::runtime_error("cap");N q=v;if(q/64>=seen.size())seen.resize(q/64+1);seen[q/64]|=1ULL<<(q%64);};
 for(I n=1;n<=limit;++n){
  I t=n-1;bool isS=a>n&&!contains(a-n);
  if(isS){run_ss3=0;}
  else{
   auto it=latest.find({P-1,W-t});
   if(it!=latest.end()){
    I q=it->second,d=t-q;
    I lead=0; while(lead<d && !signS[t-(lead+1)]) ++lead;
    I ss=0;bool prevS=false;
    for(I j=1;j<=d;++j){bool s=signS[t-j];if(s&&prevS)++ss;prevS=s;}
    if(ss==3){
     ++ss3;
     if(run_ss3){
      ++run_viol;++g_run_viol;
      if(g_run_viol<=8)
       std::cout<<"VIOL={\"prev_t\":"<<run_last_t<<",\"prev_d\":"<<run_last_d
         <<",\"t\":"<<t<<",\"d\":"<<d<<",\"gap\":"<<(t-run_last_t)<<"}\n";
     }
     ++run_ss3; run_last_t=t; run_last_d=d;
     if(lead==0) ++lead0; else if(lead==1) ++lead1; else if(lead==2) ++lead2; else ++leadge3;
     if(signS[t-d]) ++endS;
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
 std::cout<<"SS3={\"count\":"<<ss3<<",\"lead0\":"<<lead0<<",\"lead1\":"<<lead1
   <<",\"lead2\":"<<lead2<<",\"lead_ge3\":"<<leadge3
   <<",\"window_ends_S\":"<<endS<<",\"run_violations\":"<<g_run_viol<<"}\n";
 if(g_run_viol) std::cout<<"FAIL: SS=3 one-per-run violations\n";
 else std::cout<<"PASS: SS=3 census through "<<limit<<"\n";
}
