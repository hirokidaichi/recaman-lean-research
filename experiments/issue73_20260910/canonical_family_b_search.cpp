#include <algorithm>
#include <chrono>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <vector>
using I=std::int64_t;using U=std::uint64_t;
struct Event{I t=-1,len=0,subBefore=0;};
int main(){
 constexpr I limit=1000000000,valueCap=16000000000LL;
 auto start=std::chrono::steady_clock::now();
 std::vector<U>seen(1,1),signs((limit+63)/64,0);
 auto has=[&](I v){return U(v)/64<seen.size()&&((seen[U(v)/64]>>(v%64))&1);};
 auto SAt=[&](I t){return (signs[t/64]>>(t%64))&1;};
 auto add=[&](I v){if(v<0||v>valueCap)throw std::runtime_error("declared value cap exceeded");if(U(v)/64>=seen.size())seen.resize(U(v)/64+1);seen[U(v)/64]|=1ULL<<(v%64);};
 Event ss,lastss,giant,lastgiant;I value=0,run=0,subs=0,As=0,A3=0,candidates=0;
 for(I step=1;step<=limit;++step){I t=step-1;bool S=value>step&&!has(value-step);
  if(!S&&run==1&&giant.len==3&&ss.t>=0){
   ++candidates;I j=subs-giant.subBefore,z=subs-ss.subBefore,n=4*j-2*z+1,d=2*n+1,u=t-d;
   if(n>=2&&j>=1&&z>=1&&j<n&&z<n&&j!=z&&d<=t&&u>=0&&ss.t>=u+1&&lastss.t<u+1&&giant.t-giant.len-1>=u&&(lastgiant.t<0||lastgiant.t-lastgiant.len-1<u)&&SAt(u)){
    I m=0,M=0,first=-1;for(I k=1;k<=d;++k){I e=SAt(t-k)?-1:1;m+=e;M+=k*e;if(m==1&&M==0&&first<0)first=k;}
    if(m!=1||M!=0||first!=d)throw std::runtime_error("derived B candidate failed direct minimum check");
    std::cout<<"FOUND={\"step\":"<<step<<",\"sign_time\":"<<t<<",\"lag\":"<<d<<",\"old_time\":"<<u<<",\"n\":"<<n<<",\"j\":"<<j<<",\"z\":"<<z<<",\"SS\":["<<ss.t-1<<','<<ss.t<<"],\"A3_end_S\":"<<giant.t<<",\"value\":"<<value<<",\"word\":\"";
    for(I k=1;k<=d;++k)std::cout<<(SAt(t-k)?'S':'A');std::cout<<"\"}\n";
    std::cout<<"REFUTED: canonical family-B absence; direct full prefix scan passed\n";return 0;
   }
  }
  if(S){if(run>=3){lastgiant=giant;giant={t,run,subs};if(run==3)++A3;}if(t>0&&SAt(t-1)){lastss=ss;ss={t,0,subs};}signs[t/64]|=1ULL<<(t%64);++subs;run=0;}
  else{++As;++run;}
  value+=S?-step:step;add(value);
  if(step==10000000){if(value!=20438710||As!=5000014||subs!=4999986)throw std::runtime_error("10M checkpoint mismatch");}
  if(step==10000000||step%100000000==0){
   double seconds=std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();
   std::cout<<"CHECKPOINT={\"through\":"<<step<<",\"value\":"<<value<<",\"A\":"<<As<<",\"S\":"<<subs<<",\"completed_A3\":"<<A3<<",\"candidate_checks\":"<<candidates<<",\"elapsed_seconds\":"<<seconds<<",\"seen_bytes\":"<<seen.size()*8<<"}\n"<<std::flush;
   if(seconds>900){std::cout<<"STOPPED: declared wall-clock cap; search incomplete\n";return 0;}
  }
 }
 std::cout<<"COMPUTED: no canonical family-B window through1000000000 steps; no universal exclusion claimed\n";
}
