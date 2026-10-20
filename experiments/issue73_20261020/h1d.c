#include <stdio.h>
#include <stdlib.h>
int n; long V[64]; int F[64]; int maxD=-99; int mode;
void rec(int k,int e,int s){int D=e-s; if(D>maxD){maxD=D;printf("maxD=%d k=%d\n",D,k);}
 if(k==n) return;
 for(int a=0;a<2;a++){F[k+1]=F[k]+(a?1:-1);V[k+1]=V[k]+(a?k:-k);int ne=e,ns=s;
  if(a){for(int t=k-1;t>=0;t--){ if(V[t]==V[k]-k && (mode==0 || F[t]==F[k]-1)){ne++;break;}}} else ns++;
  rec(k+1,ne,ns);} }
int main(int c,char**v){n=atoi(v[1]);mode=atoi(v[2]);V[0]=0;F[0]=0;rec(0,0,0);printf("done maxD=%d\n",maxD);}
