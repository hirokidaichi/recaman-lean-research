// case (i): d(q0)=0, y starts S^4. DFS a_y<=2, d>=0 only. Report max F-h2 reached over all y-prefixes, by j.
#include <stdio.h>
#include <stdlib.h>
int q0,h2,LY; int s[256],F[257],G[257]; int mx[64]; long nodes=0; int ex=0;
int tauof(int b){ for(int t=b-3;t>=0;t-=4) if(F[b]==F[t]+1 && G[b]-G[t]==(b-t)*F[t]) return t; return -1;}
void pr(int len){ for(int i=0;i<len;i++){if(i==q0)putchar('|');putchar(s[i]>0?'A':'S');} printf("\n");}
void dfs(int len,int ay,int dq,int j){
  nodes++;
  if(len-q0>=LY) return;
  for(int v=-1;v<=1;v+=2){
    int nj=j; if(len-q0==j && v<0 && j==len-q0) nj=j+1; // count leading S
    if(len-q0<4 && v>0) continue;
    s[len]=v; F[len+1]=F[len]+v; G[len+1]=G[len]+F[len+1];
    int nay=ay,ndq=dq;
    if(v<0) ndq++; else { int t=tauof(len); if(t<0){nay++; if(nay>2) continue;} else { ndq--; if(ndq<0) continue; } }
    int jj = (v<0 && len-q0==j)? j+1 : j;
    if(F[len+1]-h2 > mx[jj]){ mx[jj]=F[len+1]-h2; if(ex<12){ex++; printf("j=%d new max %d: ",jj,mx[jj]); pr(len+1);} }
    dfs(len+1,nay,ndq,jj);
  }
}
int main(int argc,char**argv){int L=atoi(argv[1]); LY=atoi(argv[2]);
 for(int i=0;i<64;i++) mx[i]=-99;
 for(long m=0;m<(1L<<L);m++){ q0=L; F[0]=G[0]=0;
   for(int i=0;i<L;i++){ s[i]=((m>>i)&1)?1:-1; F[i+1]=F[i]+s[i]; G[i+1]=G[i]+F[i+1]; }
   int dw=0,ok=1; for(int b=0;b<q0;b++){ if(s[b]<0) dw++; else if(tauof(b)>=0) dw--; if(dw<0){ok=0;break;} }
   if(!ok||dw!=0) continue; h2=F[q0]; dfs(q0,0,0,0); }
 printf("nodes=%ld\n",nodes); for(int j=4;j<64;j++) if(mx[j]>-99) printf("j=%d maxF-h2=%d\n",j,mx[j]);
}
