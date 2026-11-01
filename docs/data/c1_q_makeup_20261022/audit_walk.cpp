#define main holdout_main
#include "holdout.cpp"
#undef main
int main(int argc,char**argv) {
  if(argc!=2)return 2;Walk x;for(char c:std::string(argv[1]))x.add(c);
  std::cout<<"{\"F\":[";for(int i=0;i<(int)x.f.size();i++){if(i)std::cout<<",";std::cout<<x.f[i];}
  std::cout<<"],\"d\":[";for(int i=0;i<(int)x.d.size();i++){if(i)std::cout<<",";std::cout<<x.d[i];}
  std::cout<<"],\"a\":[";for(int i=0;i<(int)x.a.size();i++){if(i)std::cout<<",";std::cout<<x.a[i];}
  std::cout<<"],\"tau\":[";for(int i=0;i<(int)x.tau.size();i++){if(i)std::cout<<",";std::cout<<x.tau[i];}
  std::cout<<"]}\n";
}
