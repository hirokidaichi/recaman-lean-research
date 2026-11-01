#include <algorithm>
#include <array>
#include <chrono>
#include <climits>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <set>
#include <string>
#include <vector>
#include <sys/resource.h>
using Clock=std::chrono::steady_clock;using U=std::uint64_t;
int sg[256],F[257],D[257],AN[257];long long G[257];
int N,R,n,g,SMAX;bool complete=true;std::string reason="complete",witness="";int witness_n=-1,witness_q=-1;
Clock::time_point deadline;U nodes=0,started=0,finished=0,scuts=0,acuts=0,zcuts=0,returncuts=0;
std::vector<U> prefix_counts;
struct Stat {U count=0;int maxS=-1,maxDepth=-1,maxLength=-1;long long minAz=LLONG_MAX,minR=LLONG_MAX;std::set<std::string> words;};
std::array<Stat,4> stats;
std::string word(int lo,int hi){std::string w;for(int i=lo;i<hi;i++)w+=sg[i]>0?'A':'S';return w;}
bool endable(int b){for(int t=b-3;t>=0;t-=4)if(F[b]==F[t]+1&&G[b]-G[t]==1LL*(b-t)*F[t])return true;return false;}
void add(int b,int v){sg[b]=v;F[b+1]=F[b]+v;G[b+1]=G[b]+F[b+1];bool e=v>0&&endable(b);
 D[b+1]=D[b]+(v<0)-e;AN[b+1]=AN[b]+(v>0&&!e);}
bool tick(){++nodes;if((nodes&65535)==0&&Clock::now()>=deadline){complete=false;reason="wall_limit";}return complete;}
void tail(int len,int ns,int low){
 if(!tick())return;int used=len-n,az=AN[len]-AN[n];
 if(D[len]==1){auto&s=stats[az];s.count++;s.maxS=std::max(s.maxS,ns);s.maxDepth=std::max(s.maxDepth,g-low);s.maxLength=std::max(s.maxLength,used);
  s.words.insert(word(n,len));long long A=G[len]-G[n]-1LL*used*(g-1);int h=F[len]-g;
  long long rr=h>0?A+1LL*h*(h+1)/2:A-1LL*used*h;
  s.minAz=std::min(s.minAz,A);s.minR=std::min(s.minR,rr);
  if(low<=g-5){complete=false;reason="actual_deep_counterexample";witness=word(0,len);witness_n=n;witness_q=len;return;}}
 if(used==N)return;
 if(D[len]-1>N-used){returncuts++;return;}
 for(int v:{-1,1}){
  if(v<0&&ns==SMAX){scuts++;continue;}
  add(len,v);
  if(AN[len+1]-AN[n]>3){acuts++;continue;}
  if(D[len+1]<1){zcuts++;continue;}
  tail(len+1,ns+(v<0),std::min(low,F[len+1]));if(!complete)return;
 }
}
void prefixes(const std::string&w,int mass){
 if(!complete)return;++started;prefix_counts[mass]++;n=w.size();F[0]=0;G[0]=0;D[0]=0;AN[0]=0;bool bad=false;
 for(int i=0;i<n;i++){add(i,w[i]=='A'?1:-1);if(D[i+1]<0)bad=true;}
 if(F[n]!=mass||D[n]!=0||bad){complete=false;reason="prefix_not_equal_or_negative";witness=w;witness_n=n;witness_q=n;return;}
 g=F[n];tail(n,0,g);if(!complete)return;++finished;
 const std::vector<std::pair<int,std::string>> atoms={{1,"A"},{2,"SAAA"},{4,"SSAAAASAAA"}};
 for(const auto&[dm,B]:atoms)if(mass+dm<=R){prefixes(w+B,mass+dm);if(!complete)return;}
}
int main(int argc,char**argv){if(argc!=4)return 2;N=std::atoi(argv[1]);R=std::atoi(argv[2]);int seconds=std::atoi(argv[3]);
 if(N<1||R<1||N+3*R>250||seconds<1||seconds>240)return 2;SMAX=(N+1)/2;
 if(R<SMAX+1)return 2;rlimit lim{250,252};if(setrlimit(RLIMIT_CPU,&lim))return 3;
 prefix_counts.resize(R+1);deadline=Clock::now()+std::chrono::seconds(seconds);prefixes("",0);
 std::cout<<"{\"complete\":"<<(complete?"true":"false")<<",\"reason\":\""<<reason<<"\",\"tail_lengths\":[1,"<<N
 <<"],\"max_prefix_mass\":"<<R<<",\"total_S_bound\":"<<SMAX<<",\"nodes\":"<<nodes
 <<",\"prefixes_started\":"<<started<<",\"prefixes_finished\":"<<finished<<",\"prefix_counts\":[";
 for(int j=0;j<=R;j++){if(j)std::cout<<",";std::cout<<prefix_counts[j];}
 std::cout<<"],\"S_cuts\":"<<scuts<<",\"A_cuts\":"<<acuts<<",\"zero_cuts\":"<<zcuts<<",\"return_cuts\":"<<returncuts<<",\"classes\":[";
 for(int j=0;j<4;j++){if(j)std::cout<<",";auto&s=stats[j];std::cout<<"{\"az\":"<<j<<",\"count\":"<<s.count<<",\"maxS\":"<<s.maxS
 <<",\"maxDepth\":"<<s.maxDepth<<",\"maxLength\":"<<s.maxLength<<",\"minAz\":"<<s.minAz<<",\"minR_or_Q0\":"<<s.minR<<",\"zwords\":[";
  bool first=true;for(const auto&w:s.words){if(!first)std::cout<<",";first=false;std::cout<<"\""<<w<<"\"";}std::cout<<"]}";}
 std::cout<<"],\"witness\":{\"k1\":"<<witness_n<<",\"q0\":"<<witness_q<<",\"word\":\""<<witness<<"\"}}\n";
}
