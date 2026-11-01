#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <map>
#include <set>
#include <string>
#include <sys/resource.h>
#include <unordered_set>
#include <vector>

using U=std::uint64_t;
using Clock=std::chrono::steady_clock;
std::vector<std::set<std::string>> words(14);
std::unordered_set<U> saturated;
U visited=0, merged=0, unsup_cuts=0, deficit_cuts=0, exact_old_checks=0;
U prefix_count=0, long_holdouts=0;
std::array<U,4> endpoint_counts{};
std::array<std::set<std::string>,4> endpoint_words;
int maximum_a=0, maximum_endpoint_depth=0;
bool exhausted=true;
std::string witness_p, witness_t;
Clock::time_point start,deadline;

// Independent representation: absolute levels and their prefix integrals;
// no lag/mod-four filter or old-window exclusion is used to calculate E.
bool end_direct(const std::string& w, int*old_start=nullptr, int n=0) {
  std::vector<long long> f(w.size()+1),g(w.size()+1);
  for(int i=0;i<(int)w.size();++i) {f[i+1]=f[i]+(w[i]=='A'?1:-1);g[i+1]=g[i]+f[i+1];}
  int b=w.size(); bool answer=false;
  for(int t=0;t<b;++t) if(f[b]-f[t]==1 && g[b]-g[t]==(b-t)*f[t]) {
    answer=true; if(old_start && t<n) *old_start=t;
  }
  return answer;
}

bool end_weighted(const std::string& w) {
  int mass=0,moment=0,b=w.size();
  for(int t=b-1;t>=0;--t) {int x=w[t]=='A'?1:-1;mass+=x;moment+=(b-t)*x;if(mass==1&&moment==0)return true;}
  return false;
}

U age_key(const std::string& tail, int a, int az) {
  U key=U(a)|(U(az)<<4); int shift=8,b=tail.size();
  for(int i=b-1;i>=0;--i) if(tail[i]=='A') {
    key |= U(std::min(14,b-i))<<shift; shift+=4;
  }
  return key;
}

void walk(const std::string& p, const std::string& tail, int a,int s,int az,int low,int f) {
  if(!exhausted || !witness_t.empty()) return;
  if((++visited&4095)==0 && Clock::now()>deadline) {exhausted=false;return;}
  if(tail.size()>256) {exhausted=false;return;}
  maximum_a=std::max(maximum_a,a);
  if(a==8) {witness_p=p;witness_t=tail;return;}
  if(s<13 && s-(a-az)==1) {
    endpoint_counts[az]++;endpoint_words[az].insert(tail);
    maximum_endpoint_depth=std::max(maximum_endpoint_depth,-low);
  }
  if(s>=13) {
    if(!saturated.insert(age_key(tail,a,az)).second) {merged++;return;}
  }
  std::string full=p+tail;
  int old=-1; bool e=end_direct(full,&old,p.size());++exact_old_checks;
  if(s>=13 && old>=0) {exhausted=false;std::cerr<<"count barrier failed\n";return;}
  // Long-gap holdouts use literal new words, independent of the compressed graph.
  if(s>=13 && tail.size()>=13 && tail.substr(tail.size()-13)==std::string(13,'S') && long_holdouts<128) {
    for(int more:{13,26,257,4097}) {
      std::string long_word=full+std::string(more,'S');
      if(end_direct(long_word)!=end_weighted(long_word) || end_direct(long_word)) {
        exhausted=false;std::cerr<<"long-gap mismatch\n";return;
      }
    }
    ++long_holdouts;
  }
  int new_az=az+!e;
  // Reverse traversal order from the discovery implementation.
  if(new_az>3) unsup_cuts++;
  else if(s<13 && s-(a+1-new_az)<1) deficit_cuts++;
  else walk(p,tail+'A',a+1,s,new_az,std::min(low,f+1),f+1);
  walk(p,tail+'S',a,std::min(13,s+1),az,std::min(low,f-1),f-1);
}

int main() {
  rlimit limit{120,122};if(setrlimit(RLIMIT_CPU,&limit))return 3;
  start=Clock::now();deadline=start+std::chrono::seconds(115);
  words[0].insert("");
  for(int m=1;m<=13;++m) {
    if(m>=1)for(const auto&w:words[m-1])words[m].insert(w+"A");
    if(m>=2)for(const auto&w:words[m-2])words[m].insert(w+"SAAA");
    if(m>=4)for(const auto&w:words[m-4])words[m].insert(w+"SSAAAASAAA");
  }
  for(int m=13;m>=0 && exhausted && witness_t.empty();--m)for(const auto&p:words[m]) {
    ++prefix_count;
    int d=0;
    for(int b=0;b<(int)p.size();++b) {
      if(p[b]=='S') ++d;else d-=end_direct(p.substr(0,b));
      if(d<0) {exhausted=false;std::cerr<<"negative prefix deficit\n";return 5;}
    }
    if(d!=0) {exhausted=false;std::cerr<<"nonzero prefix deficit\n";return 5;}
    walk(p,"",0,0,0,0,0);
    if(!exhausted || !witness_t.empty())break;
  }
  rusage usage{};getrusage(RUSAGE_SELF,&usage);
  auto sec=[](timeval t){return t.tv_sec+t.tv_usec/1e6;};
  std::cout<<"{\"graph_exhausted\":"<<(exhausted&&witness_t.empty()?"true":"false")
    <<",\"prefixes_checked\":"<<prefix_count<<",\"visited\":"<<visited<<",\"memo_cuts\":"<<merged
    <<",\"saturated_states\":"<<saturated.size()<<",\"budget_cuts\":"<<unsup_cuts<<",\"zero_cuts\":"<<deficit_cuts
    <<",\"all_start_queries\":"<<exact_old_checks<<",\"highest_A\":"<<maximum_a
    <<",\"endpoint_depth_max\":"<<maximum_endpoint_depth<<",\"long_gap_contexts\":"<<long_holdouts
    <<",\"long_gap_extra_S\":[13,26,257,4097],\"classes\":[";
  for(int a=0;a<4;++a){if(a)std::cout<<",";std::cout<<"{\"az\":"<<a<<",\"count\":"<<endpoint_counts[a]<<",\"words\":[";
    bool first=true;for(const auto&w:endpoint_words[a]) {if(!first)std::cout<<",";first=false;std::cout<<"\""<<w<<"\"";}std::cout<<"]}";}
  std::cout<<"],\"witness_prefix\":\""<<witness_p<<"\",\"witness_tail\":\""<<witness_t<<"\""
    <<",\"elapsed_seconds\":"<<std::chrono::duration<double>(Clock::now()-start).count()
    <<",\"user_seconds\":"<<sec(usage.ru_utime)<<",\"system_seconds\":"<<sec(usage.ru_stime)<<"}\n";
  return exhausted?0:4;
}
