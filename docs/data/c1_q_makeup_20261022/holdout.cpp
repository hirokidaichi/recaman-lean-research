#include <algorithm>
#include <array>
#include <chrono>
#include <climits>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <string>
#include <vector>
#include <sys/resource.h>
using U=std::uint64_t;
U rng=0x20261022c1a5b17dULL;
U next() { U z=(rng+=0x9e3779b97f4a7c15ULL);z=(z^(z>>30))*0xbf58476d1ce4e5b9ULL;
  z=(z^(z>>27))*0x94d049bb133111ebULL;return z^(z>>31); }
int pick(int n) { return next()%n; }
struct Walk {
  std::string w;std::vector<int> f{0},d{0},a{0},tau;std::vector<long long> g{0};
  bool window(int t,int b) const {return f[b]==f[t]+1&&g[b]-g[t]==1LL*(b-t)*f[t];}
  int latest() const {int b=w.size();for(int t=b-3;t>=0;t-=4)if(window(t,b))return t;return -1;}
  void add(char c) { int t=c=='A'?latest():-1;int v=c=='A'?1:-1;
    w+=c;tau.push_back(t);f.push_back(f.back()+v);g.push_back(g.back()+f.back());
    d.push_back(d.back()+(v<0)-(t>=0));a.push_back(a.back()+(v>0&&t<0)); }
};
Walk gen(int kind,int n) {
  Walk x;std::string raw;
  const std::array<std::string,3> blocks={"A","SAAA","SSAAAASAAA"};
  if(kind==0||kind==1) {while((int)raw.size()<n)raw+=pick(kind==0?2:3)?'A':'S';}
  if(kind==2) {bool a=pick(2);while((int)raw.size()<n){raw+=std::string(1+pick(24),a?'A':'S');a=!a;}}
  if(kind==3) {while((int)raw.size()<n)raw+=blocks[pick(3)];
    for(int j=0;j<8;j++){int k=pick(raw.size());raw[k]=raw[k]=='A'?'S':'A';}}
  if(kind==4) {while((int)raw.size()<n/3)raw+=blocks[pick(3)];raw+="SSSSAAAASAAA";
    while((int)raw.size()<n) {if(pick(3)==0)raw+=std::string(1+pick(12),'S');else raw+=blocks[pick(3)];}}
  if(kind==5) {while((int)raw.size()<n)raw+=std::string(1+pick(32),'S')+std::string(1+pick(64),'A');}
  if(kind<6) {raw.resize(n);for(char c:raw)x.add(c);return x;}
  while((int)x.w.size()<n) {
    bool e=x.latest()>=0;bool a;
    if(kind==6) a=pick(100)<(e?95:55);
    else a=pick(100)<(e?(x.d.back()>1?99:40):35);
    if(a&&e&&x.d.back()==0)a=false;
    x.add(a?'A':'S');
  }
  return x;
}
struct Best {long long v=LLONG_MAX;U sample=0;int kind=-1,q=-1,k=-1,b=-1;std::string w;
 void take(long long z,const Walk&x,U sample_,int kind_,int q_,int k_,int b_){
  if(z>=v)return;v=z;sample=sample_;kind=kind_;q=q_;k=k_;b=b_;w=x.w;}
 void emit(const char*name)const{std::cout<<"\""<<name<<"\":";
  if(v==LLONG_MAX){std::cout<<"null";return;}
  std::cout<<"{\"value\":"<<v<<",\"sample\":"<<sample<<",\"kind\":"<<kind<<",\"q0\":"<<q
    <<",\"k1\":"<<k<<",\"b\":"<<b<<",\"word\":\""<<w<<"\"}";}
};
int main(int argc,char**argv) {
 if(argc!=4)return 2;U samples=std::strtoull(argv[1],nullptr,10);int wall=std::atoi(argv[2]),cpu=std::atoi(argv[3]);
 if(samples<1||wall<1||cpu<1)return 2;rlimit lim{(rlim_t)cpu,(rlim_t)(cpu+2)};if(setrlimit(RLIMIT_CPU,&lim))return 3;
 auto start=std::chrono::steady_clock::now();U done=0;
 std::array<U,8> accepted{},guards{},endguards{},words{};Best B,R,Q,Y,Q0,HV;
 bool complete=true,violation=false;U hviol=0,completion_numeric=0;
 for(U i=0;i<samples;i++) {
  if(std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()>=wall){complete=false;break;}
  int kind=i%8,n=80+pick(305);Walk x=gen(kind,n);words[kind]++;done++;
  int lastzero=0;bool prefix=true;
  for(int q=1;q<n;q++) {
   prefix=prefix&&x.d[q]>=0;if(!prefix){hviol++;HV.take(x.d[q],x,i,kind,q,lastzero,q);break;}
   if(x.d[q]==0){lastzero=q;continue;}if(x.d[q]!=1)continue;
   int k=lastzero,g=x.f[k],h=x.f[q]-g;accepted[kind]++;
   long long az=x.g[q]-x.g[k]-1LL*(q-k)*(g-1);
   if(h>0)R.take(az+1LL*h*(h+1)/2,x,i,kind,q,k,q);
   else Q0.take(x.g[q]-x.g[k]-1LL*(q-k)*(x.f[q]-1),x,i,kind,q,k,q);
   for(int b=q;b<n;b++) {
    if(x.d[b+1]<1||x.a[b+1]-x.a[q]>1) {
     if(x.d[b+1]==0&&x.tau[b]==q&&x.a[b+1]-x.a[q]<=1)completion_numeric++;
     break;
    }
    if(x.f[b]>g)continue;guards[kind]++;endguards[kind]+=(x.tau[b]>=0);
    long long y=x.g[b]-x.g[q]-1LL*(b-q)*(x.f[b]-1);
    long long z=x.g[b]-x.g[k]-1LL*(b-k)*(x.f[b]-1);
    B.take(az+y,x,i,kind,q,k,b);Q.take(z,x,i,kind,q,k,b);Y.take(y,x,i,kind,q,k,b);
   }
  }
  if(hviol||B.v<0||R.v<0||Q.v<0||Y.v<0||Q0.v<0){violation=true;complete=false;break;}
 }
 std::cout<<"{\"samples\":"<<done<<",\"complete\":"<<(complete?"true":"false")<<",\"stopped_on_violation\":"
  <<(violation?"true":"false")<<",\"rng_state\":"<<rng<<",\"H_prefix_violations\":"<<hviol
  <<",\"numeric_completions\":"<<completion_numeric<<",\"groups\":[";
 for(int j=0;j<8;j++){if(j)std::cout<<",";std::cout<<"{\"kind\":"<<j<<",\"words\":"<<words[j]
  <<",\"splits\":"<<accepted[j]<<",\"guard_endpoints\":"<<guards[j]<<",\"endable_guard_endpoints\":"<<endguards[j]<<"}";}
 std::cout<<"],";B.emit("B");std::cout<<",";R.emit("R");std::cout<<",";Q.emit("Q");std::cout<<",";
 Y.emit("Y");std::cout<<",";Q0.emit("Q_at_q0");std::cout<<",";HV.emit("H_failure");std::cout<<"}\n";
 return 0;
}
