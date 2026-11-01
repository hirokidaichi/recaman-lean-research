#include <algorithm>
#include <array>
#include <chrono>
#include <climits>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <map>
#include <set>
#include <string>
#include <sys/resource.h>
using Clock=std::chrono::steady_clock;using U=std::uint64_t;
int sg[1024],F[1025],D[1025],AN[1025];long long G[1025];
int n,baseg,max_tail=0;U nodes=0,zends=0,guards=0,depth_cuts=0,budget_cuts=0,zero_cuts=0;
bool complete=true;std::string reason="complete";Clock::time_point deadline;
std::string phase="",stopped_word="",stopped_phase="";int current_q=-1,stopped_n=-1,stopped_q=-1;
std::map<std::string,std::string> reps;
struct Stat {U count=0;int maxS=-1;long long minR=LLONG_MAX,minAz=LLONG_MAX;std::set<std::string> zwords;};
std::array<Stat,4> stats;
struct Best {long long value=LLONG_MAX;std::string word;int k=-1,q=-1,b=-1;
 void take(long long v,int q0,int end){if(v>=value)return;value=v;k=n;q=q0;b=end;word.clear();for(int i=0;i<=end;i++)word+=sg[i]>0?'A':'S';}};
Best minZ,minR;
void make_reps(const std::string&w){
 if(w.size()>11)return;std::string key=w.size()<11?"short:"+w:"suffix:"+w;
 auto it=reps.find(key);if(it==reps.end()||w.size()<it->second.size()||(w.size()==it->second.size()&&w<it->second))reps[key]=w;
 for(const std::string B:{"A","SAAA","SSAAAASAAA"})make_reps(w+B);
}
bool tick(int len){
 ++nodes;max_tail=std::max(max_tail,len-n);
 if(len-n>=512){complete=false;reason="stack_guard_512";}
 if((nodes&4095)==0&&Clock::now()>=deadline){complete=false;reason="wall_limit";}
 if(!complete){stopped_n=n;stopped_q=current_q;stopped_phase=phase;for(int i=0;i<len;i++)stopped_word+=sg[i]>0?'A':'S';return false;}
 return complete;
}
bool endable(int b){for(int t=b-3;t>=0;t-=4)if(F[b]==F[t]+1&&G[b]-G[t]==1LL*(b-t)*F[t])return true;return false;}
bool add(int len,int v){sg[len]=v;F[len+1]=F[len]+v;G[len+1]=G[len]+F[len+1];bool e=v>0&&endable(len);
 D[len+1]=D[len]+(v<0)-e;AN[len+1]=AN[len]+(v>0&&!e);return e;}
std::string word(int lo,int hi){std::string w;for(int i=lo;i<hi;i++)w+=sg[i]>0?'A':'S';return w;}
void ywalk(int len,int q){
 phase="y";current_q=q;
 if(!tick(len))return;
 for(int v:{-1,1}){
  add(len,v);if(AN[len+1]-AN[q]>1){budget_cuts++;continue;}if(D[len+1]<1){zero_cuts++;continue;}
  // Domain ends at b=len for depth; the last sign is nevertheless counted in ay/d.
  if(F[len]<=baseg){++guards;long long Z=G[len]-G[n]-1LL*(len-n)*(F[len]-1);minZ.take(Z,q,len);
   if(Z<0){complete=false;reason="Q_counterexample";return;}}
  if(F[len+1]<baseg-4){depth_cuts++;continue;}
  ywalk(len+1,q);if(!complete)return;
 }
}
void zwalk(int len,int ns){
 phase="z";current_q=-1;
 if(!tick(len))return;int az=AN[len]-AN[n];
 if(D[len]==1){++zends;auto&r=stats[az];r.count++;r.maxS=std::max(r.maxS,ns);r.zwords.insert(word(n,len));
  long long Az=G[len]-G[n]-1LL*(len-n)*(baseg-1);int h=F[len]-baseg;
  long long R=h>0?Az+1LL*h*(h+1)/2:Az-1LL*(len-n)*h;
  r.minAz=std::min(r.minAz,Az);r.minR=std::min(r.minR,R);
  // R witness ends immediately before q0; b=q0-1 is only a storage endpoint.
  minR.take(R,len,len-1);ywalk(len,len);if(!complete)return;
 }
 for(int v:{-1,1}){
  add(len,v);if(F[len+1]<baseg-4){depth_cuts++;continue;}
  if(AN[len+1]-AN[n]>3){budget_cuts++;continue;}if(D[len+1]<1){zero_cuts++;continue;}
  zwalk(len+1,ns+(v<0));if(!complete)return;
 }
}
void emit_best(const char*key,const Best&r){std::cout<<"\""<<key<<"\":";
 if(r.value==LLONG_MAX){std::cout<<"null";return;}std::cout<<"{\"value\":"<<r.value<<",\"k1\":"<<r.k
 <<",\"q0\":"<<r.q<<",\"b\":"<<r.b<<",\"word\":\""<<r.word<<"\"}";}
int main(int argc,char**argv){if(argc!=3)return 2;int seconds=std::atoi(argv[1]);if(seconds<1||seconds>120)return 2;
 rlimit lim{130,132};if(setrlimit(RLIMIT_CPU,&lim))return 3;make_reps("");
 std::ofstream contexts(argv[2]);contexts<<"[\n";bool first=true;
 for(const auto&[key,w]:reps){if(!first)contexts<<",\n";first=false;contexts<<"{\"key\":\""<<key<<"\",\"prefix\":\""<<w<<"\"}";}contexts<<"\n]\n";contexts.close();
 deadline=Clock::now()+std::chrono::seconds(seconds);U done=0;
 for(const auto&[key,w]:reps){n=w.size();F[0]=0;G[0]=0;D[0]=0;AN[0]=0;
  for(int i=0;i<n;i++)add(i,w[i]=='A'?1:-1);
  if(D[n]!=0){complete=false;reason="representative_prefix_not_equal";break;}
  baseg=F[n];zwalk(n,0);if(!complete)break;++done;
 }
 std::cout<<"{\"complete\":"<<(complete?"true":"false")<<",\"reason\":\""<<reason<<"\",\"context_count\":"<<reps.size()
 <<",\"contexts_finished\":"<<done<<",\"nodes\":"<<nodes<<",\"max_tail_length\":"<<max_tail
 <<",\"z_endpoints\":"<<zends<<",\"guard_endpoints\":"<<guards<<",\"depth_cuts\":"<<depth_cuts
 <<",\"budget_cuts\":"<<budget_cuts<<",\"zero_cuts\":"<<zero_cuts<<",\"classes\":[";
 for(int j=0;j<4;j++){if(j)std::cout<<",";auto&r=stats[j];std::cout<<"{\"az\":"<<j<<",\"count\":"<<r.count
  <<",\"maxS\":"<<r.maxS<<",\"minAz\":"<<r.minAz<<",\"minR\":"<<r.minR<<",\"zwords\":[";
  bool firstz=true;for(const auto&w:r.zwords){if(!firstz)std::cout<<",";firstz=false;std::cout<<"\""<<w<<"\"";}std::cout<<"]}";}
 std::cout<<"],";emit_best("minQ",minZ);std::cout<<",";emit_best("minR",minR);
 std::cout<<",\"stopped_trace\":{\"phase\":\""<<stopped_phase<<"\",\"k1\":"<<stopped_n<<",\"q0\":"<<stopped_q
 <<",\"word\":\""<<stopped_word<<"\"}}\n";
}
