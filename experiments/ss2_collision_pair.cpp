// H-20261006-01. Exhaustive positive-mass periodic falsifier; not a proof.
#include <algorithm>
#include <cassert>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <map>
#include <string>
#include <vector>
using U = uint32_t;
struct Win { int t, d, ss, oldest, tail; U nb; std::string word; };
int mod(int x, int p) { x %= p; return x < 0 ? x + p : x; }
int sign(U mask, int p, int t) { return ((mask >> mod(t,p)) & 1) ? 1 : -1; }
Win window(U mask, int p, int t, int d) {
  Win w{t,d,0,-1,0,0,""};
  int last=1, lastS=0, mass=0, moment=0;
  for (int j=1;j<=d;j++) {
    int s=sign(mask,p,t-j);
    w.word += s==1?'A':'S'; mass+=s; moment+=j*s;
    if (s==-1) { w.nb |= U(1)<<mod(t-j,p); lastS=j; }
    if (s==-1 && last==-1) w.ss++;
    last=s;
  }
  assert(mass==1 && moment==0 && lastS>0);
  w.oldest=mod(t-lastS,p); w.tail=d-lastS;
  return w;
}
// d=kp+r, 0<=r<p. Mass gives k=(1-m_r)/M uniquely when M>0.
// Moment is k Q + p M k(k-1)/2 + kp m_r + Q_r.
int minlag(U mask,int p,int t) {
  std::vector<int> m(p+1),q(p+1);
  for(int j=1;j<=p;j++) {int s=sign(mask,p,t-j);m[j]=m[j-1]+s;q[j]=q[j-1]+j*s;}
  int best=0;
  for(int r=0;r<p;r++) {
    int n=1-m[r];
    if(n<0 || n%m[p]) continue;
    int k=n/m[p],d=k*p+r;
    long long mom=1LL*k*q[p]+1LL*p*m[p]*k*(k-1)/2+1LL*k*p*m[r]+q[r];
    if(d>0 && mom==0 && (!best || d<best)) best=d;
  }
  return best;
}
int brute(U mask,int p,int t) {
  int m=0,q=0;
  for(int d=1;d<=p*(p+1);d++) {
    int s=sign(mask,p,t-d);m+=s;q+=d*s;
    if(m==1 && q==0) return d;
  }
  return 0;
}
void jsonwin(const Win&w) {
  std::cout<<"{\"phase\":"<<w.t<<",\"lag\":"<<w.d<<",\"ss\":"<<w.ss
    <<",\"oldest\":"<<w.oldest<<",\"tail_A\":"<<w.tail<<",\"neighbors_mask\":"<<w.nb
    <<",\"word\":\""<<w.word<<"\"}";
}
int main(int argc,char**argv) {
  assert(argc==3);
  int lo=std::atoi(argv[1]),hi=std::atoi(argv[2]); assert(lo>=1 && hi<=22 && lo<=hi);
  for(int p=lo;p<=hi;p++) {
    long long reps=0,weighted=0,pairs=0,subsets=0,donors=0,lowcount=0,wrap=0,crosschecks=0;
    int maxgroup=0,minslack=1000000;
    U full=(U(1)<<p)-1;
    for(U mask=0;mask<=full;mask++) {
      if(2*__builtin_popcount(mask)<=p) continue;
      U rot=mask;int orbit=p;bool canonical=true;
      for(int i=1;i<p;i++) {
        rot=((rot<<1)&full)|(rot>>(p-1));
        if(rot<mask) {canonical=false;break;}
        if(rot==mask) {orbit=i;break;}
      }
      if(!canonical) continue;
      reps++;weighted+=orbit;
      std::vector<Win> low,two;
      for(int t=0;t<p;t++) if(sign(mask,p,t)==1) {
        int d=minlag(mask,p,t);
        if(p<=12) {assert(d==brute(mask,p,t));crosschecks++;}
        if(!d)continue;
        Win w=window(mask,p,t,d);
        if(w.ss<=1) {low.push_back(w);lowcount++;}
        if(w.ss==2) {assert(w.tail<=1);two.push_back(w);donors++;if(d>=p)wrap++;}
      }
      std::map<int,int> groups;
      for(const Win&w:two) maxgroup=std::max(maxgroup,++groups[w.oldest]);
      assert(maxgroup<=2);
      for(size_t a=0;a<two.size();a++)for(size_t b=a+1;b<two.size();b++) {
        const Win&v=two[a];const Win&w=two[b];
        if(v.oldest!=w.oldest)continue;
        pairs++;assert(v.tail!=w.tail);
        // Check optimized lag discovery against a direct full bound on every collision word.
        for(int t=0;t<p;t++) if(sign(mask,p,t)==1) {
          assert(minlag(mask,p,t)==brute(mask,p,t));crosschecks++;
        }
        U fixed=v.nb|w.nb;
        assert(low.size()<23);
        const U count=U(1)<<low.size();
        std::vector<U> unions(count,fixed);
        for(U subset=0;subset<count;subset++) {
          if(subset) {
            U rest=subset&(subset-1);
            unions[subset]=unions[rest]|low[__builtin_ctz(subset)].nb;
          }
          int slack=__builtin_popcount(unions[subset])-__builtin_popcount(subset)-2;
          subsets++;
          if(slack<minslack) {
            minslack=slack;
            std::cout<<"{\"kind\":\"record\",\"p\":"<<p<<",\"mask\":"<<mask
              <<",\"period_mass\":"<<2*__builtin_popcount(mask)-p
              <<",\"slack\":"<<slack<<",\"neighbors_mask\":"<<unions[subset]<<",\"donors\":[";
            jsonwin(v);std::cout<<",";jsonwin(w);std::cout<<"],\"low\":[";
            bool first=true;
            for(size_t i=0;i<low.size();i++)if(subset&(U(1)<<i)){
              if(!first)std::cout<<",";first=false;jsonwin(low[i]);
            }
            std::cout<<"]}\n";
          }
          if(slack<0) {std::cout<<"{\"kind\":\"counterexample\"}\n";return 2;}
        }
      }
    }
    std::cout<<"{\"kind\":\"summary\",\"p\":"<<p<<",\"positive_mass_necklaces\":"<<reps
      <<",\"positive_mass_words\":"<<weighted<<",\"lowSS_phases\":"<<lowcount
      <<",\"minimal_SS2_phases\":"<<donors<<",\"SS2_lag_ge_period\":"<<wrap
      <<",\"max_oldest_group\":"<<maxgroup<<",\"collision_pairs\":"<<pairs
      <<",\"all_low_subsets\":"<<subsets<<",\"direct_lag_crosschecks\":"<<crosschecks
      <<",\"min_slack\":"<<(minslack==1000000?-999:minslack)<<",\"violations\":0}\n"<<std::flush;
  }
}

