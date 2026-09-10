// Dump the six SS=3 one-per-run violators: extra remainder of reverse-nested gap-1 pairs.
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
 I run_last_t=-1,run_last_d=-1; N run_ss3=0,g_run_viol=0;
 auto contains=[&](I v){N q=v;return q/64<seen.size()&&((seen[q/64]>>(q%64))&1);};
 auto record=[&](I v){if(v<0||v>valueCap)throw std::runtime_error("cap");N q=v;if(q/64>=seen.size())seen.resize(q/64+1);seen[q/64]|=1ULL<<(q%64);};
 auto dump_word=[&](I t,I d){
  std::string w; w.reserve(d);
  I mass=0,moment=0,ss=0; bool prevS=false;
  for(I j=1;j<=d;++j){
   bool s=signS[t-j];
   w.push_back(s?'S':'A');
   I bit=s?-1:1; mass+=bit; moment+=j*bit;
   if(s&&prevS) ++ss; prevS=s;
  }
  return std::tuple<std::string,I,I,I>(w,mass,moment,ss);
 };
 std::cout<<"protocol=H-20260910-33 SS=3 reverse-nested extras\n";
 for(I n=1;n<=limit;++n){
  I t=n-1;bool isS=a>n&&!contains(a-n);
  if(isS){run_ss3=0;}
  else{
   auto it=latest.find({P-1,W-t});
   if(it!=latest.end()){
    I q=it->second,d=t-q;
    I ss=0;bool prevS=false;
    for(I j=1;j<=d;++j){bool s=signS[t-j];if(s&&prevS)++ss;prevS=s;}
    if(ss==3){
     if(run_ss3){
      ++g_run_viol;
      I pt=run_last_t, pd=run_last_d;
      I f=d, extra_len=pd-(f-1);
      auto [nw,nm,nM,nss]=dump_word(t,d);
      auto [ow,om,oM,oss]=dump_word(pt,pd);
      // extra is oldest extra_len signs of the old window (newest-first suffix)
      std::string extra=ow.substr(f-1);
      I em=0,eM=0,ess=0; bool prev=false; bool first=true;
      for(size_t i=0;i<extra.size();++i){
       bool s=extra[i]=='S'; I bit=s?-1:1; em+=bit; eM+=(i+1)*bit;
       if(!first && s && prev) ++ess; prev=s; first=false;
      }
      // join SS at the v|extra boundary
      bool join = (f-1>0 && ow[f-2]=='S' && extra.size() && extra[0]=='S');
      I sa_pairs=0;
      while(2*sa_pairs+1< (I)extra.size() && extra[2*sa_pairs]=='S' && extra[2*sa_pairs+1]=='A')
        ++sa_pairs;
      I as_pairs=0; I pos=2*sa_pairs;
      while(pos+1< (I)extra.size() && extra[pos]=='A' && extra[pos+1]=='S')
        { ++as_pairs; pos+=2; }
      std::string inner= extra.size()> (size_t)pos ? extra.substr(pos, std::min<size_t>(12, extra.size()-pos)) : "";
      bool inner_min = inner.size()>=3 && inner[0]=='A' && inner[1]=='A' && inner.back()=='S';
      std::cout<<"EXTRA={\"prev_t\":"<<pt<<",\"prev_d\":"<<pd
        <<",\"t\":"<<t<<",\"d\":"<<d
        <<",\"extra_len\":"<<extra.size()
        <<",\"extra_mass\":"<<em<<",\"extra_moment\":"<<eM
        <<",\"extra_ss\":"<<ess<<",\"join_ss\":"<<(join?1:0)
        <<",\"need_moment\":"<<(1-(I)(f-1))
        <<",\"v_len\":"<<(f-1)
        <<",\"new_head\":\""<<nw.substr(0,std::min<size_t>(8,nw.size()))<<"\""
        <<",\"extra_head\":\""<<extra.substr(0,std::min<size_t>(24,extra.size()))<<"\""
        <<",\"sa_pairs\":"<<sa_pairs<<",\"as_pairs\":"<<as_pairs
        <<",\"inner_head\":\""<<inner<<"\",\"inner_minword_shape\":"<<(inner_min?1:0)
        <<"}\n";
     }
     ++run_ss3; run_last_t=t; run_last_d=d;
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
 std::cout<<"VIOL_COUNT="<<g_run_viol<<"\n";
}
