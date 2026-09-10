// Isolated a=0 shapes on the standard 10^7 orbit.
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
 std::vector<bool> signS(limit+1);
 std::vector<I> iso_t, iso_d;
 std::unordered_map<Key,std::uint32_t,Hash> latest;latest.reserve(limit*11/10);latest[{0,0}]=0;
 I a=0,P=0,W=0,first19=0;
 auto contains=[&](I v){N q=v;return q/64<seen.size()&&((seen[q/64]>>(q%64))&1);};
 auto record=[&](I v){if(v<0||v>valueCap)throw std::runtime_error("cap");N q=v;if(q/64>=seen.size())seen.resize(q/64+1);seen[q/64]|=1ULL<<(q%64);};
 for(I n=1;n<=limit;++n){
  I t=n-1;bool isS=a>n&&!contains(a-n);
  if(!isS){
   auto it=latest.find({P-1,W-t});
   if(it!=latest.end()){
    I q=it->second,d=t-q;
    I lead=0; while(lead<d && !signS[t-(lead+1)]) ++lead;
    I ss=0;bool prevS=false;
    for(I j=1;j<=d;++j){bool s=signS[t-j];if(s&&prevS)++ss;prevS=s;}
    if(ss==2 && lead==0){iso_t.push_back(t);iso_d.push_back(d);}
   }
  }
  if(isS) signS[t]=true;
  I bit=isS?-1:1; a+=bit*n; record(a);
  if(n<=15&&a!=known[n-1])throw std::runtime_error("prefix");
  if(a==19&&!first19)first19=n;
  P+=bit;W+=t*bit;latest[{P,W}]=t+1;
 }
 if(first19!=99734)throw std::runtime_error("19");
 N sing=0,nosaas=0,endS=0,sss=0,lag11=0,saas=0;
 for(size_t k=0;k<iso_t.size();++k){
  I t=iso_t[k],d=iso_d[k];
  bool singleton=(t+1>=limit)||signS[t+1];
  if(singleton) ++sing;
  if(d==11) ++lag11;
  if(signS[t-d]) ++endS;
  bool hasSAAS=false,hasSSS=false;
  for(I j=1;j+3<=d;++j){
   bool a1=signS[t-j],a2=signS[t-(j+1)],a3=signS[t-(j+2)],a4=signS[t-(j+3)];
   if(a1&&!a2&&!a3&&a4) hasSAAS=true; // S A A S newest-first
  }
  for(I j=1;j+2<=d;++j){
   if(signS[t-j]&&signS[t-(j+1)]&&signS[t-(j+2)]) hasSSS=true;
  }
  if(hasSAAS) ++saas; else ++nosaas;
  if(hasSSS) ++sss;
 }
 N nonsing=0;
 for(size_t k=0;k<iso_t.size();++k){
  I t=iso_t[k],d=iso_d[k];
  bool singleton=(t+1>=limit)||signS[t+1];
  if(!singleton && nonsing<8){
   std::cout<<"NONSING={\"t\":"<<t<<",\"d\":"<<d<<",\"next_is_A\":true}\n";
   ++nonsing;
  }
 }
 std::cout<<"ISO_SHAPE={\"count\":"<<iso_t.size()<<",\"singleton_or_last\":"<<sing
   <<",\"NoSAAS\":"<<nosaas<<",\"has_SAAS\":"<<saas<<",\"has_SSS\":"<<sss
   <<",\"window_ends_S\":"<<endS<<",\"lag11\":"<<lag11<<"}\n";
 std::cout<<"PASS: isolated a=0 shapes through "<<limit<<"\n";
}
