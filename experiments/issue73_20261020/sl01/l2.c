// check Lemma 2 (d=0): in DFS (a_y<=2,d>=0), any endable A in y at level <= runmin+1 ?
#include <stdio.h>
#include <stdlib.h>
int q0,h2,LY; int s[256],F[257],G[257]; long viol=0,chk=0;
int tauof(int b){ for(int t=b-3;t>=0;t-=4) if(F[b]==F[t]+1 && G[b]-G[t]==(b-t)*F[t]) return t; return -1;}
void dfs(int len,int ay,int dq,int mu){
  if(len-q0>=LY) return;
  for(int v=-1;v<=1;v+=2){
    s[len]=v; F[len+1]=F[len]+v; G[len+1]=G[len]+F[len+1];
    int nay=ay,ndq=dq;
    if(v<0) ndq++; else { int t=tauof(len); if(t<0){nay++; if(nay>2) continue;} else { ndq--; if(ndq<0) continue; chk++; if(F[len]<=mu+1){viol++; if(viol<5){for(int i=0;i<=len;i++){if(i==q0)putchar('|');putchar(s[i]>0?'A':'S');}printf(" viol\n");}} } }
    int nmu = F[len+1]<mu?F[len+1]:mu;
    dfs(len+1,nay,ndq,nmu);
  }
}
int main(int argc,char**argv){int L=atoi(argv[1]); LY=atoi(argv[2]);
 for(long m=0;m<(1L<<L);m++){ q0=L; F[0]=G[0]=0;
   for(int i=0;i<L;i++){ s[i]=((m>>i)&1)?1:-1; F[i+1]=F[i]+s[i]; G[i+1]=G[i]+F[i+1]; }
   int dw=0,ok=1; for(int b=0;b<q0;b++){ if(s[b]<0) dw++; else if(tauof(b)>=0) dw--; if(dw<0){ok=0;break;} }
   if(!ok||dw!=0) continue; h2=F[q0]; dfs(q0,0,0,F[q0]); }
 printf("checked=%ld viol=%ld\n",chk,viol);
}
