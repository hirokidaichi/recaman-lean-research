#include <algorithm>
#include <chrono>
#include <climits>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <string>
#include <vector>

// Exact depth-first discovery; completion and strict/broad endpoints are explicit.
using Clock = std::chrono::steady_clock;
struct Best {
  long long value=LLONG_MAX;
  std::string word;
  int q0=-1,k1=-1,b=-1,after=-999;
};
int s[513],F[514],G[514],D[514],AN[514];
int LW,LY,q0,k1;
std::uint64_t nodes=0,prefixes=0,strict_candidates=0,broad_candidates=0;
bool complete=true;
Clock::time_point deadline;
Best az,y_strict,y_broad,z_strict,z_broad,combined,negaz_z,negaz_y;
std::uint64_t negaz_candidates=0;
long long current_az=0;

bool tick() {
  if(nodes==UINT64_MAX) { std::cerr<<"counter overflow\n"; std::exit(3); }
  ++nodes;
  if((nodes&65535)==0 && Clock::now()>=deadline) complete=false;
  return complete;
}
bool isw(int b,int t) {
  return F[b]==F[t]+1 && G[b]-G[t]==(b-t)*F[t];
}
bool endable(int b,int v) {
  if(v<0) return false;
  for(int t=b-3;t>=0;t-=4) if(isw(b,t)) return true;
  return false;
}
void save(Best& best,long long value,int len,int d_after) {
  if(value>=best.value) return;
  best.value=value;best.q0=q0;best.k1=k1;best.b=len;best.after=d_after;
  best.word.clear();
  for(int i=0;i<=len;i++) best.word.push_back(s[i]>0?'A':'S');
}
void walk_y(int len,int ay) {
  if(!complete || len-q0>=LY) return;
  for(int v: {-1,1}) {
    if(!tick()) return;
    s[len]=v;F[len+1]=F[len]+v;G[len+1]=G[len]+F[len+1];
    bool e=endable(len,v);
    int nay=ay+(v>0&&!e),nd=D[len]+(v<0)-(e?1:0);
    if(nay>1) continue;
    if(F[len]<=F[k1]) {
      long long Y=(G[len]-G[q0])-1LL*(len-q0)*(F[len]-1);
      long long Z=(G[len]-G[k1])-1LL*(len-k1)*(F[len]-1);
      ++broad_candidates;save(y_broad,Y,len,nd);save(z_broad,Z,len,nd);
      if(nd>=1) {
        ++strict_candidates;save(y_strict,Y,len,nd);save(z_strict,Z,len,nd);
        save(combined,current_az+Y,len,nd);
        if(current_az<0) { ++negaz_candidates; save(negaz_z,Z,len,nd);save(negaz_y,Y,len,nd); }
      }
    }
    if(nd<1) continue;
    D[len+1]=nd;walk_y(len+1,nay);
  }
}
void walk_prefix(int len,int lastzero) {
  if(!tick()) return;
  if(D[len]==1 && len>0) {
    ++prefixes;q0=len;k1=lastzero;
    long long A=(G[len]-G[k1])-1LL*(len-k1)*(F[k1]-1);
    // Prefix witness has b=q0-1; q0 remains the split immediately after it.
    save(az,A,len-1,D[len]);current_az=A;walk_y(len,0);
  }
  if(!complete || len>=LW) return;
  for(int v: {-1,1}) {
    if(!complete) return;
    s[len]=v;F[len+1]=F[len]+v;G[len+1]=G[len]+F[len+1];
    bool e=endable(len,v);int nd=D[len]+(v<0)-(e?1:0);
    if(nd<0) continue;
    D[len+1]=nd;AN[len+1]=AN[len]+(v>0&&!e);
    walk_prefix(len+1,nd==0?len+1:lastzero);
  }
}
void emit(const char* name,const Best& best,bool comma=true) {
  std::cout<<"\""<<name<<"\":";
  if(best.value==LLONG_MAX) std::cout<<"null";
  else std::cout<<"{\"value\":"<<best.value<<",\"word\":\""<<best.word
    <<"\",\"q0\":"<<best.q0<<",\"k1\":"<<best.k1<<",\"b\":"<<best.b
    <<",\"d_after\":"<<best.after<<"}";
  if(comma) std::cout<<",";
}
int main(int argc,char**argv) {
  if(argc!=4) return 2;
  LW=std::atoi(argv[1]);LY=std::atoi(argv[2]);int seconds=std::atoi(argv[3]);
  if(LW<1||LY<1||LW+LY>512||seconds<1) return 2;
  deadline=Clock::now()+std::chrono::seconds(seconds);walk_prefix(0,0);
  std::cout<<"{\"LW\":"<<LW<<",\"LY\":"<<LY<<",\"complete\":"<<(complete?"true":"false")
    <<",\"nodes\":"<<nodes<<",\"prefixes\":"<<prefixes<<",\"strict_candidates\":"<<strict_candidates
    <<",\"broad_candidates\":"<<broad_candidates<<",";
  emit("Az",az);emit("Y_strict",y_strict);emit("Y_broad",y_broad);
  emit("Z_strict",z_strict);emit("Z_broad",z_broad);emit("Az_plus_Y",combined);
  emit("negAz_Z",negaz_z);emit("negAz_Y",negaz_y);std::cout<<"\"negaz_candidates\":"<<negaz_candidates<<"}\n";
}
