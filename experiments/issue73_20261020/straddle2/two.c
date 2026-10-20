// w (mode 0: prefix-H required; mode 1: none) with d(w)=dd ; y = S^j A S^i A, j,i<=J ; both A endable from 0 (=> straddlers). Count / show.
#include <stdio.h>
#include <stdlib.h>
int s[120],F[121],G[121];
int tauof(int b){ for(int t=b-3;t>=0;t-=4) if(F[b]==F[t]+1 && G[b]-G[t]==(b-t)*F[t]) return t; return -1;}
void put(int u,int v){s[u]=v;F[u+1]=F[u]+v;G[u+1]=G[u]+F[u+1];}
int main(int c,char**v){int L=atoi(v[1]),dd=atoi(v[2]),mode=atoi(v[3]),J=atoi(v[4]); long tot=0; int shown=0;
 for(long m=0;m<(1L<<L);m++){ F[0]=G[0]=0; for(int i=0;i<L;i++) put(i,((m>>i)&1)?1:-1);
  int dw=0,ok=1,mind=0; for(int b=0;b<L;b++){ if(s[b]<0) dw++; else if(tauof(b)>=0) dw--; if(dw<mind)mind=dw;} if(mode==0&&mind<0) continue; if(dw!=dd) continue;
  for(int j=0;j<=J;j++){ int u=L; for(int a=0;a<j;a++)put(u++,-1); put(u,1); int b1=u; if(tauof(b1)<0) continue;
    for(int i=0;i<=J;i++){ int w2=b1+1; for(int a=0;a<i;a++)put(w2++,-1); put(w2,1); int t2=tauof(w2); if(t2<0) continue; tot++;
      if(shown<12){shown++; for(int q=0;q<=w2;q++){if(q==L)putchar('|');putchar(s[q]>0?'A':'S');} printf(" j=%d i=%d t1=%d t2=%d mind=%d\n",j,i,tauof(b1),t2,mind);} } } }
 printf("L=%d d=%d mode=%d: total=%ld\n",L,dd,mode,tot);}
