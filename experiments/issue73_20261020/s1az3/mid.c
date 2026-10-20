// y-prefix setting of s1rest/m3 (prefix-H from 0, d(q0)=1, k1 last zero, a_y<=1, d>=1 on y-prefix).
// For every straddler b in y (endable, no window starting >= q0): classify start t (<k1, =k1, mid) and
// whether y has an S in [q0,b) (#S[q0,b)) ; print distinct mid patterns with an S before b.
#include <stdio.h>
#include <stdlib.h>
int s[256],F[257],G[257],D[257],AN[257]; int q0,k1,LW,LY; long cnt[12][3][2]; int pr=0;
int isw(int b,int t){ return t>=0 && F[b]==F[t]+1 && G[b]-G[t]==(b-t)*F[t]; }
void dfsy(int len,int ay,int ns){
  if(len-q0>=LY) return;
  for(int v=-1;v<=1;v+=2){
    s[len]=v; F[len+1]=F[len]+v; G[len+1]=G[len]+F[len+1];
    int nay=ay,nd=D[len],end=0; if(v>0){ for(int t=len-3;t>=0;t-=4) if(isw(len,t)){end=1;break;} }
    if(v<0) nd++; else if(!end){ nay++; if(nay>1) continue;} else nd--;
    int az=AN[q0]-AN[k1]; if(az>11)az=11;
    if(v>0&&end){ int any=0,lo=0,eq=0,mid=0; for(int t=len-3;t>=0;t-=4) if(isw(len,t)){ if(t>=q0) any=1; else if(t<k1) lo=1; else if(t==k1) eq=1; else mid=1; }
      if(!any){ int hs=ns>0; if(lo) cnt[az][0][hs]++; if(eq) cnt[az][1][hs]++; if(mid){ cnt[az][2][hs]++; if(hs && pr<20){pr++; for(int i=k1;i<=len;i++){ if(i==q0)putchar('|'); putchar(s[i]>0?'A':'S');} printf(" az=%d d_after=%d\n",az,nd);} } } }
    if(nd<1) continue;
    D[len+1]=nd; dfsy(len+1,nay,ns+(v<0));
  }
}
void dfsw(int len,int lastz){
  if(D[len]==1 && len>0){ q0=len; k1=lastz; dfsy(len,0,0); }
  if(len>=LW) return;
  for(int v=-1;v<=1;v+=2){
    s[len]=v; F[len+1]=F[len]+v; G[len+1]=G[len]+F[len+1];
    int nd=D[len],isn=0,end=0; if(v>0){ for(int t=len-3;t>=0;t-=4) if(isw(len,t)){end=1;break;} }
    if(v<0) nd++; else if(end) nd--; else isn=1; if(nd<0) continue;
    D[len+1]=nd; AN[len+1]=AN[len]+isn; dfsw(len+1,nd==0?len+1:lastz);
  }
}
int main(int c,char**v){ LW=atoi(v[1]); LY=atoi(v[2]); dfsw(0,0);
 for(int a=0;a<12;a++) printf("az=%d  t<k1:[noS %ld, S %ld]  t=k1:[noS %ld, S %ld]  mid:[noS %ld, S %ld]\n",a,cnt[a][0][0],cnt[a][0][1],cnt[a][1][0],cnt[a][1][1],cnt[a][2][0],cnt[a][2][1]); }
