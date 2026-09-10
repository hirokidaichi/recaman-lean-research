// Histogram of min-P2 ssCount, lead, and per-SS one-per-run violations.
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
 constexpr I limit=10000000,valueCap=2000000000, SSMAX=64;
 constexpr std::array<I,15> known={1,3,6,2,7,13,20,12,21,11,22,10,23,9,24};
 std::vector<N> seen(1,1);
 std::vector<bool> signS(limit);
 std::unordered_map<Key,std::uint32_t,Hash> latest;latest.reserve(limit*11/10);latest[{0,0}]=0;
 I a=0,P=0,W=0,first19=0;
 std::array<N,SSMAX+1> cnt{}, lead0{}, lead1{}, lead2{}, leadge3{}, viol{};
 N p2=0, ss_hi=0;
 std::array<I,SSMAX+1> run_last{};
 run_last.fill(-1);
 std::cout<<"protocol=H-20260910-36 min-P2 ssCount histogram canonical 10^7\n"<<std::flush;
 auto contains=[&](I v){N q=v;return q/64<seen.size()&&((seen[q/64]>>(q%64))&1);};
 auto record=[&](I v){if(v<0||v>valueCap)throw std::runtime_error("cap");N q=v;if(q/64>=seen.size())seen.resize(q/64+1);seen[q/64]|=1ULL<<(q%64);};
 for(I n=1;n<=limit;++n){
  I t=n-1;bool isS=a>n&&!contains(a-n);
  if(isS){run_last.fill(-1);}
  else{
   auto it=latest.find({P-1,W-t});
   if(it!=latest.end()){
    I q=it->second,d=t-q;
    I lead=0; while(lead<d && !signS[t-(lead+1)]) ++lead;
    I ss=0;bool prevS=false;
    for(I j=1;j<=d;++j){bool s=signS[t-j];if(s&&prevS)++ss;prevS=s;}
    ++p2;
    I bucket=ss>SSMAX?SSMAX:ss;
    if(ss>SSMAX) ++ss_hi;
    ++cnt[bucket];
    if(lead==0) ++lead0[bucket]; else if(lead==1) ++lead1[bucket];
    else if(lead==2) ++lead2[bucket]; else ++leadge3[bucket];
    if(run_last[bucket]>=0) ++viol[bucket];
    run_last[bucket]=t;
   }
  }
  if(isS) signS[t]=true;
  I bit=isS?-1:1; a+=bit*n; record(a);
  if(n<=15&&a!=known[n-1])throw std::runtime_error("prefix");
  if(a==19&&!first19)first19=n;
  P+=bit;W+=t*bit;latest[{P,W}]=t+1;
 }
 if(first19!=99734)throw std::runtime_error("19");
 if(p2!=1315896) throw std::runtime_error("p2");
 if(cnt[2]!=52357) throw std::runtime_error("ss2");
 if(cnt[3]!=21727) throw std::runtime_error("ss3");
 if(cnt[4]!=16455) throw std::runtime_error("ss4");
 std::cout<<"P2="<<p2<<" HIGH_SS="<<ss_hi<<"\n";
 for(I s=0;s<=SSMAX;++s){
  if(!cnt[s]) continue;
  std::cout<<"SS={\"ss\":"<<s<<",\"count\":"<<cnt[s]
    <<",\"lead0\":"<<lead0[s]<<",\"lead1\":"<<lead1[s]
    <<",\"lead2\":"<<lead2[s]<<",\"lead_ge3\":"<<leadge3[s]
    <<",\"run_viol_same_ss\":"<<viol[s]<<"}\n";
 }
}
