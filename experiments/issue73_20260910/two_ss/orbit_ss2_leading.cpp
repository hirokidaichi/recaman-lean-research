// H-20260910-30: SS=2 minimum windows by leading A-run; one-per-run audit.
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
 std::unordered_map<Key,std::uint32_t,Hash> latest;latest.reserve(limit*11/10);latest[{0,0}]=0;
 I a=0,P=0,W=0,maxValue=0,first19=0,lo=1;
 N A=0,S=0,supplied=0,ss2=0,companion=0,isolated0=0,isolated1=0,other_lead=0;
 N run_ss2=0,run_viol=0,sibling_ok=0,sibling_fail=0,maxLag=0;
 N g_run_viol=0,g_sibling_fail=0;
 auto contains=[&](I v){N q=v;return q/64<seen.size()&&((seen[q/64]>>(q%64))&1);};
 auto record=[&](I v){if(v<0||v>valueCap)throw std::runtime_error("value cap");N q=v;if(q/64>=seen.size())seen.resize(q/64+1);seen[q/64]|=1ULL<<(q%64);};
 for(I n=1;n<=limit;++n){
  I t=n-1;bool isS=a>n&&!contains(a-n);
  if(isS){
   ++S;run_ss2=0;
  }else{
   ++A;
   auto it=latest.find({P-1,W-t});
   if(it!=latest.end()){
    ++supplied;I q=it->second,d=t-q;
    if(d<3||d%4!=3)throw std::runtime_error("min P2 lag parity");
    I lead=0;
    while(lead<d && !signS[t-(lead+1)]) ++lead;
    I ss=0;bool prevS=false;
    for(I j=1;j<=d;++j){
     bool s=signS[t-j];
     if(s&&prevS)++ss;
     prevS=s;
    }
    if(ss==2){
     ++ss2;maxLag=std::max<N>(maxLag,(N)d);
     if(run_ss2){++run_viol;++g_run_viol;}
     ++run_ss2;
     if(lead==0) ++isolated0;
     else if(lead==1) ++isolated1;
     else if(lead>=3){
      ++companion;
      I u=t-(lead-2);
      bool siblingA=u>=0 && !signS[u];
      bool aas=siblingA && u>=3 && !signS[u-1] && !signS[u-2] && signS[u-3];
      if(aas) ++sibling_ok; else {++sibling_fail;++g_sibling_fail;}
     }else ++other_lead;
    }
   }
  }
  if(isS) signS[t]=true;
  I bit=isS?-1:1;
  a+=bit*n;record(a);maxValue=std::max(maxValue,a);
  if(n<=15&&a!=known[n-1])throw std::runtime_error("initial prefix");
  if(a==19&&!first19)first19=n;
  P+=bit;W+=t*bit;latest[{P,W}]=t+1;
  if(n==100000||n==1000000||n==limit){
   std::cout<<"RANGE={\"from\":"<<lo<<",\"through\":"<<n
     <<",\"A\":"<<A<<",\"S\":"<<S<<",\"finite_P2_A\":"<<supplied
     <<",\"ss2\":"<<ss2<<",\"companion_a_ge_3\":"<<companion
     <<",\"isolated_a0\":"<<isolated0<<",\"isolated_a1\":"<<isolated1
     <<",\"other_lead\":"<<other_lead
     <<",\"run_violations\":"<<run_viol
     <<",\"sibling_ok\":"<<sibling_ok<<",\"sibling_fail\":"<<sibling_fail
     <<",\"max_ss2_lag\":"<<maxLag<<"}\n"<<std::flush;
   A=S=supplied=ss2=companion=isolated0=isolated1=other_lead=0;
   run_viol=sibling_ok=sibling_fail=maxLag=0;lo=n+1;
  }
 }
 if(first19!=99734)throw std::runtime_error("first 19 reference");
 if(g_run_viol)throw std::runtime_error("one-per-run violation");
 if(g_sibling_fail)throw std::runtime_error("companion without AAS sibling");
 std::cout<<"PASS: SS=2 one-per-run and leading-run siblings through "<<limit<<" steps\n";
}
