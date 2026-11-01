#include <algorithm>
#include <array>
#include <chrono>
#include <climits>
#include <cstdlib>
#include <iostream>
#include <set>
#include <string>
#include <vector>
#include <sys/resource.h>

// Independent verifier: direct backwards signed mass/moment, no F/G or lag filter.
using Count = unsigned long long;
using Clock = std::chrono::steady_clock;
struct Summary {
  Count count=0;
  int maxS=-1, maxDepth=-1, maxLength=-1;
  long long minAz=LLONG_MAX, minR=LLONG_MAX;
  std::set<std::string> words;
};
std::array<Summary,4> summaries;
std::vector<std::set<std::string>> prefixes;
int signs[256], levels[257], N, R, n, g, smax;
Count nodes=0, scuts=0, acuts=0, zcuts=0, rcuts=0, checked=0;
bool complete=true;
std::string reason="complete";
Clock::time_point deadline;

bool supplied(int length) {
  int mass=0, moment=0;
  for(int j=length-1;j>=0;--j) {
    mass+=signs[j];
    moment+=(length-j)*signs[j];
    if(mass==1 && moment==0) return true;
  }
  return false;
}

void visit(int length,int deficit,int az,int subs) {
  if(!complete) return;
  ++nodes;
  if((nodes&65535)==0 && Clock::now()>=deadline) {
    complete=false; reason="wall_limit"; return;
  }
  int used=length-n;
  if(deficit==1) {
    auto &s=summaries[az];
    ++s.count;
    s.maxS=std::max(s.maxS,subs);
    s.maxLength=std::max(s.maxLength,used);
    int low=g;
    long long area=0, qarea=0;
    std::string word;
    for(int j=n;j<length;++j) {
      word += signs[j]==1 ? 'A':'S';
      area+=levels[j+1]-g+1;
      qarea+=levels[j+1]-levels[length]+1;
      low=std::min(low,levels[j+1]);
    }
    s.maxDepth=std::max(s.maxDepth,g-low);
    s.minAz=std::min(s.minAz,area);
    int h=levels[length]-g;
    long long recover=h>0 ? area+1LL*h*(h+1)/2 : qarea;
    s.minR=std::min(s.minR,recover);
    s.words.insert(word);
    if(g-low>=5) { complete=false; reason="deep_counterexample"; return; }
  }
  if(used==N) return;
  if(deficit-1>N-used) { ++rcuts; return; }
  for(char c:std::string("SA")) {
    if(c=='S' && subs==smax) { ++scuts; continue; }
    bool endable=c=='A' && supplied(length);
    int nextaz=az+(c=='A'&&!endable);
    int nextd=deficit+(c=='S')-endable;
    if(nextaz>3) { ++acuts; continue; }
    if(nextd<1) { ++zcuts; continue; }
    signs[length]=c=='A' ? 1:-1;
    levels[length+1]=levels[length]+signs[length];
    visit(length+1,nextd,nextaz,subs+(c=='S'));
    if(!complete) return;
  }
}

int main(int argc,char**argv) {
  if(argc!=4) return 2;
  N=std::atoi(argv[1]); R=std::atoi(argv[2]); int seconds=std::atoi(argv[3]);
  if(N<1||R<1||N+3*R>250||seconds<1||seconds>300) return 2;
  smax=(N+1)/2;
  if(R<smax+1) return 2;
  rlimit limit{300,302}; if(setrlimit(RLIMIT_CPU,&limit)) return 3;
  deadline=Clock::now()+std::chrono::seconds(seconds);
  prefixes.resize(R+1); prefixes[0].insert("");
  for(int m=0;m<=R;++m)
    for(const auto &w:prefixes[m])
      for(const std::string atom:{"A","SAAA","SSAAAASAAA"}) {
        int dm=0; for(char c:atom) dm+=c=='A'?1:-1;
        if(m+dm<=R) prefixes[m+dm].insert(w+atom);
      }
  for(int m=0;m<=R&&complete;++m) for(const auto &w:prefixes[m]) {
    n=w.size(); levels[0]=0; int deficit=0;
    for(int j=0;j<n;++j) {
      deficit+=(w[j]=='S')-(w[j]=='A'&&supplied(j));
      signs[j]=w[j]=='A'?1:-1;
      levels[j+1]=levels[j]+signs[j];
      if(deficit<0) { complete=false; reason="negative_prefix"; break; }
    }
    if(!complete) break;
    if(deficit!=0||levels[n]!=m) { complete=false; reason="invalid_prefix"; break; }
    g=levels[n]; visit(n,0,0,0);
    if(!complete) break;
    ++checked;
  }
  std::cout<<"{\"complete\":"<<(complete?"true":"false")<<",\"reason\":\""<<reason
    <<"\",\"nodes\":"<<nodes<<",\"prefixes_finished\":"<<checked<<",\"prefix_counts\":[";
  for(int m=0;m<=R;++m) { if(m)std::cout<<",";std::cout<<prefixes[m].size(); }
  std::cout<<"],\"S_cuts\":"<<scuts<<",\"A_cuts\":"<<acuts<<",\"zero_cuts\":"<<zcuts
    <<",\"return_cuts\":"<<rcuts<<",\"classes\":[";
  for(int j=0;j<4;++j) {
    if(j)std::cout<<",";
    const auto&s=summaries[j];
    std::cout<<"{\"az\":"<<j<<",\"count\":"<<s.count<<",\"maxS\":"<<s.maxS
      <<",\"maxDepth\":"<<s.maxDepth<<",\"maxLength\":"<<s.maxLength<<",\"minAz\":"<<s.minAz
      <<",\"minR_or_Q0\":"<<s.minR<<",\"zwords\":[";
    bool first=true;for(const auto&w:s.words) {if(!first)std::cout<<",";first=false;std::cout<<"\""<<w<<"\"";}
    std::cout<<"]}";
  }
  std::cout<<"]}\n";
  return complete?0:4;
}
