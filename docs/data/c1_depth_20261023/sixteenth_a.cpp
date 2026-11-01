#include <algorithm>
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

using Clock = std::chrono::steady_clock;
using U = std::uint64_t;
int lower_mass, upper_mass, seconds_limit;
U nodes=0, before_nodes=0, saturated_nodes=0, memo_cuts=0, budget_cuts=0, zero_cuts=0;
U old_calls=0, local_calls=0, prefixes_started=0, prefixes_finished=0;
bool complete=true, found=false;
std::string reason="complete", witness_prefix, witness_tail, longest_tail;
int highest_a=0, longest_s=0;
Clock::time_point deadline;
std::vector<std::pair<int,std::string>> prefixes;
std::unordered_set<U> saturated_seen;
std::map<int,U> prefix_counts;

void make_prefixes(const std::string& w, int m) {
  if(m>=lower_mass) prefixes.emplace_back(m,w);
  for(auto [dm,atom]:std::vector<std::pair<int,std::string>>{{1,"A"},{2,"SAAA"},{4,"SSAAAASAAA"}})
    if(m+dm<=upper_mass) make_prefixes(w+atom,m+dm);
}

bool supplied(const std::string& prefix, const std::string& tail, int a, int s) {
  std::string w=prefix+tail;
  int b=w.size(), n=prefix.size();
  int mass=0, moment=0;
  // With at most fifteen previous A every local P2 has length at most twenty-nine.
  int local_lower=std::max(n,b-29);
  ++local_calls;
  for(int t=b-1;t>=local_lower;--t) {
    int sign=w[t]=='A'?1:-1;
    mass+=sign; moment+=(b-t)*sign;
    if(mass==1 && moment==0) return true;
  }
  if(s>=29) return false; // count barrier excludes every old window
  ++old_calls;
  mass=0; moment=0;
  for(int t=b-1;t>=0;--t) {
    int sign=w[t]=='A'?1:-1;
    mass+=sign; moment+=(b-t)*sign;
    if(t<n && mass==1 && moment==0) return true;
  }
  return false;
}

void walk(const std::string& prefix, const std::string& tail, int a, int s, int az, U mask) {
  if(!complete || found) return;
  if((++nodes & 4095)==0 && Clock::now()>=deadline) {complete=false;reason="wall_guard";return;}
  if(tail.size()>1024) {complete=false;reason="unexpected_stack_guard";return;}
  if(a>highest_a) {highest_a=a; longest_tail=tail;}
  longest_s=std::max(longest_s,s);
  if(a==16) {found=true;reason="sixteenth_A_witness";witness_prefix=prefix;witness_tail=tail;return;}
  if(s>=29) {
    U key=(U(a)<<32)|(U(az)<<29)|mask;
    if(!saturated_seen.insert(key).second) {++memo_cuts;return;}
    ++saturated_nodes;
    if(saturated_seen.size()>1000000) {complete=false;reason="memo_guard";return;}
  } else ++before_nodes;
  // The S transition is always allowed; after saturation this closes a finite self-loop.
  walk(prefix,tail+'S',a,std::min(29,s+1),az,(mask<<1)&((U(1)<<29)-1));
  if(!complete || found) return;
  bool e=supplied(prefix,tail,a,s);
  int new_az=az+!e;
  if(new_az>4) {++budget_cuts;return;}
  if(s<29 && s-(a+1-new_az)<1) {++zero_cuts;return;}
  walk(prefix,tail+'A',a+1,s,new_az,((mask<<1)|1)&((U(1)<<29)-1));
}

int main(int argc,char**argv) {
  if(argc!=4) return 2;
  lower_mass=std::atoi(argv[1]); upper_mass=std::atoi(argv[2]); seconds_limit=std::atoi(argv[3]);
  if(lower_mass<0 || upper_mass>14 || lower_mass>upper_mass || seconds_limit<1 || seconds_limit>30) return 2;
  rlimit cap{static_cast<rlim_t>(seconds_limit+1),static_cast<rlim_t>(seconds_limit+2)};
  if(setrlimit(RLIMIT_CPU,&cap)) return 3;
  make_prefixes("",0);
  deadline=Clock::now()+std::chrono::seconds(seconds_limit);
  auto start=Clock::now();
  for(const auto&[m,prefix]:prefixes) {
    ++prefixes_started; ++prefix_counts[m];
    walk(prefix,"",0,0,0,0);
    if(!complete || found) break;
    ++prefixes_finished;
  }
  rusage usage{}; getrusage(RUSAGE_SELF,&usage);
  auto timeval_seconds=[](timeval t){return t.tv_sec+t.tv_usec/1e6;};
  std::cout << "{\"complete\":"<<(complete?"true":"false")<<",\"found\":"<<(found?"true":"false")
    <<",\"graph_exhausted\":"<<(complete&&!found?"true":"false")<<",\"reason\":\""<<reason<<"\",\"prefix_mass_range\":["<<lower_mass<<","<<upper_mass<<"]"
    <<",\"prefixes_total\":"<<prefixes.size()<<",\"prefixes_started\":"<<prefixes_started
    <<",\"prefixes_finished\":"<<prefixes_finished<<",\"nodes\":"<<nodes
    <<",\"before_saturation_states\":"<<before_nodes<<",\"saturated_states\":"<<saturated_nodes
    <<",\"memo_cuts\":"<<memo_cuts<<",\"budget_cuts\":"<<budget_cuts<<",\"zero_cuts\":"<<zero_cuts
    <<",\"old_calls\":"<<old_calls<<",\"local_calls\":"<<local_calls
    <<",\"highest_A\":"<<highest_a<<",\"highest_A_tail\":\""<<longest_tail<<"\",\"largest_stored_S\":"<<longest_s
    <<",\"witness_prefix\":\""<<witness_prefix<<"\",\"witness_tail\":\""<<witness_tail<<"\""
    <<",\"elapsed_seconds\":"<<std::chrono::duration<double>(Clock::now()-start).count()
    <<",\"user_seconds\":"<<timeval_seconds(usage.ru_utime)<<",\"system_seconds\":"<<timeval_seconds(usage.ru_stime)
    <<"}\n";
  return complete?0:4;
}
