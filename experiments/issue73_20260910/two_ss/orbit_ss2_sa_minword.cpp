// SS=2 min windows: suffix of the form (SA)^k ++ minWord r, with prefix mass 0 moment -1 ss 2.
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
 N ss2=0,suf=0,glue=0;
 std::cout<<"protocol=H-20260910-34 SS=2 (SA)^k minWord suffix search\n"<<std::flush;
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
     std::vector<char> w(d);
     for(I j=1;j<=d;++j) w[j-1]=signS[t-j]?'S':'A';
     std::vector<char> sa_ok(d+2,0);
     sa_ok[d]=1; sa_ok[d-1]=1;
     for(I i=d-2;i>=0;--i){
      if(i+1<=d-2 && w[i]=='S' && w[i+1]=='A' && sa_ok[i+2]) sa_ok[i]=1;
     }
     std::vector<char> ismw(d+1,0);
     if(d>=3 && w[d-1]=='S'){
      for(I p=0;p+2<d;++p){
       I len=d-p;
       if(len%2==0) continue;
       if(w[p]=='A' && w[p+1]=='A' && sa_ok[p+2]) ismw[p]=1;
      }
     }
     std::vector<I> sa_run(d+2,0);
     for(I i=d-2;i>=0;--i){
      if(w[i]=='S' && w[i+1]=='A') sa_run[i]=1+sa_run[i+2];
     }
     std::vector<I> pmass(d+1,0), pmom(d+1,0), pss(d+1,0);
     for(I i=0;i<d;++i){
      I bit=w[i]=='S'?-1:1;
      pmass[i+1]=pmass[i]+bit;
      pmom[i+1]=pmom[i]+(i+1)*bit;
      pss[i+1]=pss[i]+(i && w[i]=='S' && w[i-1]=='S');
     }
     for(I p=0;p<d-2;++p){
      I k=sa_run[p];
      I q2=p+2*k;
      if(q2>d || !ismw[q2]) continue;
      ++suf;
      if(pmass[p]==0 && pmom[p]==-1 && pss[p]==2){
       ++glue;
       I r=(d-q2-3)/2;
       std::cout<<"GLUE={\"t\":"<<t<<",\"d\":"<<d<<",\"n_v\":"<<p
         <<",\"k\":"<<k<<",\"r\":"<<r<<"}\n"<<std::flush;
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
 std::cout<<"SS2={\"count\":"<<ss2<<",\"sa_minword_suffixes\":"<<suf
   <<",\"glue_prefix\":"<<glue<<"}\n";
 if(ss2!=52357) throw std::runtime_error("ss2");
 std::cout<<(glue==0?"PASS: no SS=2 glue prefix+(SA)^k minWord through 10000000\n"
                    :"FAIL: glue present\n");
}
