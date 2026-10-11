// H-20261006-02. Strong endpoint/core diagnostic on the previously frozen period domain.
#define main previous_falsifier_entry_unused
#include "ss2_collision_pair.cpp"
#undef main

std::vector<Win> all_low_endpoints(U mask,int p) {
  std::vector<Win> out;
  for(int t=0;t<p;t++) if(sign(mask,p,t)==1) {
    std::vector<int> m(p+1),q(p+1);
    for(int j=1;j<=p;j++){int s=sign(mask,p,t-j);m[j]=m[j-1]+s;q[j]=q[j-1]+j*s;}
    for(int r=0;r<p;r++) {
      int n=1-m[r];if(n<0 || n%m[p])continue;
      int k=n/m[p],d=k*p+r;
      long long mom=1LL*k*q[p]+1LL*p*m[p]*k*(k-1)/2+1LL*k*p*m[r]+q[r];
      if(d>0 && mom==0 && sign(mask,p,t-d)==-1) {
        Win z=window(mask,p,t,d);
        if(z.ss<=1)out.push_back(z);
      }
    }
  }
  return out;
}
bool nosaas(U mask,int p) {
  for(int t=0;t<p;t++)
    if(sign(mask,p,t)==-1 && sign(mask,p,t+1)==1 &&
       sign(mask,p,t+2)==1 && sign(mask,p,t+3)==-1) return false;
  return true;
}
int main(int argc,char**argv) {
  assert(argc==3);int lo=std::atoi(argv[1]),hi=std::atoi(argv[2]);
  assert(1<=lo && lo<=hi && hi<=22);
  for(int p=lo;p<=hi;p++) {
    long long reps=0,pairs=0,violations=0,ns_pairs=0;int minimum=1000;
    U full=(U(1)<<p)-1;
    for(U mask=0;mask<=full;mask++) {
      if(2*__builtin_popcount(mask)<=p)continue;
      bool canon=true;U rot=mask;
      for(int i=1;i<p;i++){
        rot=((rot<<1)&full)|(rot>>(p-1));
        if(rot<mask){canon=false;break;}if(rot==mask)break;
      }
      if(!canon)continue;reps++;
      std::vector<Win> two;
      for(int t=0;t<p;t++)if(sign(mask,p,t)==1){
        int d=minlag(mask,p,t);if(d){Win z=window(mask,p,t,d);if(z.ss==2)two.push_back(z);}
      }
      bool has_pair=false;
      for(size_t a=0;a<two.size();a++)for(size_t b=a+1;b<two.size();b++)
        has_pair |= two[a].oldest==two[b].oldest;
      if(!has_pair)continue;
      auto low=all_low_endpoints(mask,p);U E=0;
      for(const Win&z:low) E|=U(1)<<mod(z.t-z.d,p);
      for(size_t a=0;a<two.size();a++)for(size_t b=a+1;b<two.size();b++){
        const Win&v=two[a];const Win&z=two[b];if(v.oldest!=z.oldest)continue;
        U nb=v.nb|z.nb, free=nb&(~E);int n=__builtin_popcount(free);
        assert(free&(U(1)<<v.oldest));pairs++;ns_pairs+=nosaas(mask,p);
        minimum=std::min(minimum,n);violations+=n<2;
        std::cout<<"{\"kind\":\"pair\",\"p\":"<<p<<",\"mask\":"<<mask
          <<",\"nosaas\":"<<(nosaas(mask,p)?"true":"false")
          <<",\"endpoint_mask\":"<<E<<",\"donor_union_mask\":"<<nb
          <<",\"uncovered_mask\":"<<free<<",\"uncovered_count\":"<<n<<",\"donors\":[";
        jsonwin(v);std::cout<<",";jsonwin(z);std::cout<<"],\"all_lowSS_Sended_witnesses\":[";
        for(size_t i=0;i<low.size();i++){if(i)std::cout<<",";jsonwin(low[i]);}
        std::cout<<"]}\n";
      }
    }
    std::cout<<"{\"kind\":\"summary\",\"p\":"<<p<<",\"representatives\":"<<reps
      <<",\"pairs\":"<<pairs<<",\"nosaas_pairs\":"<<ns_pairs
      <<",\"min_uncovered\":"<<(minimum==1000?-999:minimum)
      <<",\"violations\":"<<violations<<"}\n"<<std::flush;
  }
}

