#include <algorithm>
#include <array>
#include <chrono>
#include <climits>
#include <cstdlib>
#include <cstdint>
#include <iostream>
#include <string>
#include <sys/resource.h>
using C=std::chrono::steady_clock;using U=std::uint64_t;
int s[1024],f[1025],d[1025],a[1025];long long g[1025];
int WMAX,SMAX,AMAX,k1;U nodes=0,prefixes=0,finished_prefixes=0,scuts=0,acuts=0,ends=0;
bool complete=true;C::time_point deadline;
struct Stat{U n=0;int maxs=-1;long long minaz=LLONG_MAX,minr=LLONG_MAX;std::string maxword,minword;int k=-1,q=-1;};
std::array<Stat,16> stats;
bool tick(){++nodes;if((nodes&65535)==0&&C::now()>=deadline)complete=false;return complete;}
bool endable(int b){for(int t=b-3;t>=0;t-=4)if(f[b]==f[t]+1&&g[b]-g[t]==1LL*(b-t)*f[t])return true;return false;}
std::string word(int n){std::string r;for(int i=0;i<n;i++)r+=s[i]>0?'A':'S';return r;}
void add(int n,int v){s[n]=v;f[n+1]=f[n]+v;g[n+1]=g[n]+f[n+1];bool e=v>0&&endable(n);
 d[n+1]=d[n]+(v<0)-e;a[n+1]=a[n]+(v>0&&!e);}
void tail(int n,int ns,int na){
 if(!tick())return;
 if(d[n]==1){++ends;auto&r=stats[na];r.n++;if(ns>r.maxs){r.maxs=ns;r.maxword=word(n);}
  long long az=g[n]-g[k1]-1LL*(n-k1)*(f[k1]-1);int h=f[n]-f[k1];
  long long R=h>0?az+1LL*h*(h+1)/2:az-1LL*(n-k1)*h;
  if(az<r.minaz)r.minaz=az;
  if(R<r.minr){r.minr=R;r.minword=word(n);r.k=k1;r.q=n;}}
 if(ns<SMAX){add(n,-1);tail(n+1,ns+1,na);}else scuts++;
 if(!complete)return;add(n,1);int nn=a[n+1]-a[k1];
 if(nn>AMAX){acuts++;return;}if(d[n+1]<1)return;tail(n+1,ns,nn);
}
void prefixes_dfs(int n){
 if(!tick())return;++prefixes;k1=n;tail(n,0,0);if(!complete)return;++finished_prefixes;
 for(const std::string B:{"A","SAAA","SSAAAASAAA"}){
  if(n+(int)B.size()>WMAX)continue;bool ok=true;
  for(int j=0;j<(int)B.size();j++){add(n+j,B[j]=='A'?1:-1);if(d[n+j+1]<0)ok=false;}
  if(!ok||d[n+B.size()]!=0){std::cerr<<"prefix equality failed "<<word(n+B.size())<<"\n";complete=false;return;}
  prefixes_dfs(n+B.size());if(!complete)return;
 }
}
int main(int argc,char**argv){if(argc!=5)return 2;WMAX=std::atoi(argv[1]);SMAX=std::atoi(argv[2]);AMAX=std::atoi(argv[3]);
 int wall=std::atoi(argv[4]);if(WMAX<0||SMAX<1||AMAX<0||AMAX>15||WMAX+2*SMAX+AMAX+2>=1024||wall<1)return 2;
 rlimit cpu{600,602};if(setrlimit(RLIMIT_CPU,&cpu))return 3;deadline=C::now()+std::chrono::seconds(wall);prefixes_dfs(0);
 std::cout<<"{\"WMAX\":"<<WMAX<<",\"SMAX\":"<<SMAX<<",\"AMAX\":"<<AMAX<<",\"complete\":"<<(complete?"true":"false")
 <<",\"nodes\":"<<nodes<<",\"prefixes_started\":"<<prefixes<<",\"prefixes_finished\":"<<finished_prefixes
 <<",\"S_cutoffs\":"<<scuts<<",\"A_cutoffs\":"<<acuts<<",\"d1_endpoints\":"<<ends<<",\"classes\":[";
 for(int j=0;j<=AMAX;j++){if(j)std::cout<<",";auto&r=stats[j];std::cout<<"{\"a_z\":"<<j<<",\"count\":"<<r.n
  <<",\"maxS\":"<<r.maxs<<",\"minAz\":"<<r.minaz<<",\"minR\":"<<r.minr
  <<",\"maxS_word\":\""<<r.maxword<<"\",\"minR_word\":\""<<r.minword<<"\",\"k1\":"<<r.k<<",\"q0\":"<<r.q<<"}";}
 std::cout<<"]}\n";
}
