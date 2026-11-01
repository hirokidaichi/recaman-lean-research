// DFS over x from 0 with prefix-H (d>=0). At each q0 with d(q0)=1, DFS y with a_y<=1, d>=0.
// Record straddlers: t-k1, F(t)-h2, F(t)-F(k1), b-q0, F(b)-h2, which A of y, before/after n1.
#include <stdio.h>
#include <stdlib.h>
int s[256],F[257],G[257],dd[257]; int q0,h2,k1,LW,LY; long cnt[8][64]; long ev=0,x2=0,tbelowk1=0; long nodesW=0;
int tauof(int b){ for(int t=b-3;t>=0;t-=4) if(F[b]==F[t]+1 && G[b]-G[t]==(b-t)*F[t]) return t; return -1;}
void pr(int len){ for(int i=0;i<len;i++){ if(i==k1)putchar('^'); if(i==q0)putchar('|'); putchar(s[i]>0?'A':'S'); } }
int mz; int na_pos; int st[8]; int nst;
void dfsy(int len,int ay,int X,int d,int nA){
  if(len-q0>=LY) return;
  for(int v=-1;v<=1;v+=2){
    s[len]=v; F[len+1]=F[len]+v; G[len+1]=G[len]+F[len+1];
    int nay=ay,nX=X,nd=d,comp=0,isn=0,isst=0,t=-1;
    if(v<0) nd=d+1; else { t=tauof(len); if(t<0){ nay++; if(nay>1) continue; isn=1; } else { nd=d-1; if(nd<0) continue; if(t<q0){ nX++; isst=1; } if(t==q0) comp=1; } }
    if(isst){ ev++; if(t<k1){ tbelowk1++; if(tbelowk1<10){ printf("T<K1 "); pr(len+1); printf(" t=%d\n",t);} }
      if(nX>=2){ x2++; if(x2<10){ printf("X2 "); pr(len+1); printf("\n"); } }
      // classify: index of A in y (nA = #A before), before/after n1
      int ia = nA; int after = ay; // ay = 1 if n1 already
      if(ia<8) cnt[after][ia]++; printf("PAT "); for(int i=t;i<=len;i++){ if(i==q0)putchar('|'); putchar(s[i]>0?'A':'S');} printf(" Ft-h2=%d Ft-Fk1=%d minz-h2=%d\n",F[t]-h2,F[t]-F[k1],mz-h2);
    }
    int sv=na_pos; if(isn) na_pos=len;
    if(!comp) dfsy(len+1,nay,nX,nd,nA+(v>0));
    else if(nX>1) { printf("BADCOMP "); pr(len+1); printf("\n"); }
    na_pos=sv;
  }
}

void dfsw(int len,int d,int lastz){
  nodesW++;
  if(d==1 && len>0){ q0=len; h2=F[len]; k1=lastz; mz=99; for(int i=k1;i<=q0;i++) if(F[i]<mz) mz=F[i]; dfsy(len,0,0,1,0); }
  if(len>=LW) return;
  for(int v=-1;v<=1;v+=2){
    s[len]=v; F[len+1]=F[len]+v; G[len+1]=G[len]+F[len+1];
    int nd=d; if(v<0) nd++; else if(tauof(len)>=0) nd--; if(nd<0) continue;
    dfsw(len+1,nd,nd==0?len+1:lastz);
  }
}
int main(int c,char**v){ LW=atoi(v[1]); LY=atoi(v[2]); F[0]=G[0]=0; dfsw(0,0,0);
  printf("LW=%d LY=%d nodesW=%ld straddler events=%ld t<k1=%ld X>=2=%ld\n",LW,LY,nodesW,ev,tbelowk1,x2);
  for(int a=0;a<2;a++) for(int i=0;i<8;i++) if(cnt[a][i]) printf(" afterN1=%d Aindex=%d : %ld\n",a,i,cnt[a][i]);
}
