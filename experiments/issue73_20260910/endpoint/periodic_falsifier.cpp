// H-20260910-28. Direct integer sums; independent of the Lean proof.
#include <algorithm>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <string>
#include <vector>

int main(int argc, char** argv) {
  const int first=argc>1?std::stoi(argv[1]):1;
  const int last=argc>2?std::stoi(argv[2]):22;
  if (first<1 || last>25 || first>last) return 2;
  std::cout << "protocol=H-20260910-28 all-word S-ended low-SS endpoint map\n";
  std::cout << "scan=4p; discovery=1..13; holdout=14..22; all period masses; SAAS allowed\n";
  for (int p=first;p<=last;++p) {
    uint64_t sources=0,witnesses=0,noSAASwords=0,jointSources=0;
    uint64_t endpointA=0,nonminimumWitnesses=0;
    int maxLag=0;
    for (uint64_t mask=0;mask<(uint64_t(1)<<p);++mask) {
      std::vector<int> e(p);
      int S=0;
      for (int i=0;i<p;++i) { e[i]=(mask>>i&1)?1:-1; S+=e[i]<0; }
      auto sign=[&](int t) {return e[(t%p+p)%p];};
      bool noSAAS=true;
      for(int i=0;i<p;++i)
        if(sign(i)==-1 && sign(i+1)==1 && sign(i+2)==1 && sign(i+3)==-1) noSAAS=false;
      noSAASwords+=noSAAS;
      std::vector<int> image(p,-1);
      int count=0,joint=0;
      for(int t=0;t<p;++t) if(e[t]==1) {
        int mass=0,moment=0,ss=0,prev=1,minimum=0;
        bool supplied=false;
        for(int d=1;d<=4*p;++d) {
          int s=sign(t-d);mass+=s;moment+=d*s;
          ss+=s==-1 && prev==-1;prev=s;
          if(ss>1) break;
          if(mass!=1 || moment!=0) continue;
          bool isFirst=minimum==0;
          if(isFirst) minimum=d;
          if(noSAAS && isFirst) {
            ++joint;
            if(s!=-1) {
              std::cerr<<"FAIL NoSAAS minimum ends A p="<<p<<" mask="<<mask<<" t="<<t<<" d="<<d<<'\n';return 1;
            }
          }
          if(s==1) {++endpointA;continue;}
          ++witnesses;nonminimumWitnesses+=!isFirst;maxLag=std::max(maxLag,d);
          int q=(t-d)%p;if(q<0)q+=p;
          assert(e[q]==-1);
          if(image[q]!=-1 && image[q]!=t) {
            std::cerr<<"FAIL endpoint p="<<p<<" mask="<<mask<<" q="<<q<<" t="<<t<<" d="<<d<<" other="<<image[q]<<'\n';return 1;
          }
          image[q]=t;supplied=true;
        }
        count+=supplied;
      }
      assert(count<=S);assert(joint<=S);
      sources+=count;jointSources+=joint;
    }
    std::cout<<(p<=13?"DISCOVERY=":"HOLDOUT=")
      <<"{\"period\":"<<p<<",\"words\":"<<(uint64_t(1)<<p)
      <<",\"sources\":"<<sources<<",\"witnesses\":"<<witnesses
      <<",\"nonminimum_S_witnesses\":"<<nonminimumWitnesses
      <<",\"A_ended_P2_witnesses\":"<<endpointA
      <<",\"NoSAAS_words\":"<<noSAASwords<<",\"NoSAAS_joint_sources\":"<<jointSources
      <<",\"max_S_ended_lag\":"<<maxLag<<",\"violations\":0}"<<std::endl;
  }
  std::cout<<"PASS: all tested endpoints are S and distinct across different current A phases; joint capacity holds\n";
}
