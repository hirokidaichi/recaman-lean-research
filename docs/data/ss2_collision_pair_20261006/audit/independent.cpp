// Independent audit replay, exactly the parent's frozen p=1..22 domain.
// Direct prefix accumulation; no mass quotient or moment formula.
#include <cassert>
#include <cstdint>
#include <iostream>
#include <vector>
using Mask=uint32_t;
struct W {int phase,len,ss,old,tail; Mask n;};
int bit(Mask m,int p,int t) { t%=p;if(t<0)t+=p;return (m>>t)&1; }
int main(){
 for(int p=1;p<=22;++p){
  int reps=0;long long weighted=0,lp=0,tp=0,wr=0,pairs=0,subsets=0;
  int maxgroup=0,slackmin=1000000;
  for(Mask m=0;m<(Mask(1)<<p);++m){
   if(2*__builtin_popcount(m)<=p)continue;
   // Canonical rotations by independent bit-by-bit construction.
   bool canonical=true;int stabilizer=0;
   for(int r=0;r<p;++r){
    Mask rot=0;for(int t=0;t<p;++t)if(bit(m,p,t+r))rot|=Mask(1)<<t;
    if(rot<m){canonical=false;break;}
    if(rot==m)++stabilizer;
   }
   if(!canonical)continue;
   assert(p%stabilizer==0);++reps;weighted+=p/stabilizer;
   std::vector<W> low,two;
   for(int t=0;t<p;++t)if(bit(m,p,t)){
    int mass=0,moment=0,ss=0,prev=1,lastS=0;Mask n=0;
    for(int d=1;d<=p*(p+1);++d){
     int a=bit(m,p,t-d),s=2*a-1;mass+=s;moment+=d*s;
     if(!a){lastS=d;int q=(t-d)%p;if(q<0)q+=p;n|=Mask(1)<<q;}
     if(!a&&!prev)++ss;prev=a;
     // SS never decreases with extension. Once >2, no later prefix can
     // be eligible lowSS or SS2, irrespective of where its first P2 is.
     if(ss>2)break;
     if(mass==1&&moment==0){
      int old=(t-lastS)%p;if(old<0)old+=p;
      W w{t,d,ss,old,d-lastS,n};
      if(ss<=1){low.push_back(w);++lp;}else{two.push_back(w);++tp;if(d>=p)++wr;}
      break;
     }
    }
   }
   for(const auto&a:two){int group=0;for(const auto&b:two)group+=a.old==b.old;if(group>maxgroup)maxgroup=group;}
   for(unsigned i=0;i<two.size();++i)for(unsigned j=i+1;j<two.size();++j){
    const auto&a=two[i];const auto&b=two[j];if(a.old!=b.old)continue;++pairs;
    for(Mask chosen=0;chosen<(Mask(1)<<low.size());++chosen){
     Mask n=a.n|b.n;int size=2;
     // Independent union loop rather than parent's dynamic subset recurrence.
     for(unsigned q=0;q<low.size();++q)if((chosen>>q)&1){n|=low[q].n;++size;}
     int slack=__builtin_popcount(n)-size;++subsets;
     if(slack<slackmin)slackmin=slack;
     assert(slack>=0);
    }
   }
  }
  std::cout<<p<<' '<<reps<<' '<<weighted<<' '<<lp<<' '<<tp<<' '<<wr<<' '<<maxgroup<<' '<<pairs<<' '<<subsets<<' '<<(slackmin==1000000?-999:slackmin)<<'\n';
 }
}
