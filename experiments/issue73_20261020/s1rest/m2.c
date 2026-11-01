// prefix-H from 0; q0: d(q0)=1, k1 last zero; y: a_y<=1, d>=1 on y-prefix (and also record the clock dropping d to 0).
// For each a_z: min over y-prefix of F-F(k1); count straddler windows by start class.
#include <stdio.h>
#include <stdlib.h>
int s[256],F[257],G[257],D[257],AN[257]; int q0,k1,LW,LY; long hm[12][60]; long st[12][4];
int isw(int b,int t){ return t>=0 && F[b]==F[t]+1 && G[b]-G[t]==(b-t)*F[t]; }
void dfsy(int len,int ay,int my){
  if(len-q0>=LY) return;
  for(int v=-1;v<=1;v+=2){
    s[len]=v; F[len+1]=F[len]+v; G[len+1]=G[len]+F[len+1];
    int nay=ay,nd=D[len],end=0; if(v>0){ for(int t=len-3;t>=0;t-=4) if(isw(len,t)){end=1;break;} }
    if(v<0) nd++; else if(!end){ nay++; if(nay>1) continue;} else nd--;
    int az=AN[q0]-AN[k1]; if(az>11)az=11;
    if(v>0&&end){ int any=0,lo=0,eq=0,mid=0; for(int t=len-3;t>=0;t-=4) if(isw(len,t)){ if(t>=q0) any=1; else if(t<k1) lo=1; else if(t==k1) eq=1; else mid=1; }
       if(lo) st[az][0]++; if(!any){ if(eq) st[az][1]++; if(mid){ st[az][2]++; if(st[az][2]<3){ for(int i=k1;i<=len;i++){ if(i==q0)putchar('|'); putchar(s[i]>0?'A':'S');} printf(" az=%d (straddler with mid start)\n",az);} } } else if(mid) st[az][3]++; }
    int m2=my; if(F[len+1]-F[k1]<m2) m2=F[len+1]-F[k1];
    if(nd<1) { hm[az][my+30]++; continue; }
    D[len+1]=nd; dfsy(len+1,nay,m2);
  }
}
void dfsw(int len,int lastz){
  if(D[len]==1 && len>0){ q0=len; k1=lastz; dfsy(len,0,F[q0]-F[k1]); }
  if(len>=LW) return;
  for(int v=-1;v<=1;v+=2){
    s[len]=v; F[len+1]=F[len]+v; G[len+1]=G[len]+F[len+1];
    int nd=D[len],isn=0,end=0; if(v>0){ for(int t=len-3;t>=0;t-=4) if(isw(len,t)){end=1;break;} }
    if(v<0) nd++; else if(end) nd--; else isn=1; if(nd<0) continue;
    D[len+1]=nd; AN[len+1]=AN[len]+isn; dfsw(len+1,nd==0?len+1:lastz);
  }
}
int main(int c,char**v){ LW=atoi(v[1]); LY=atoi(v[2]); dfsw(0,0);
 for(int a=0;a<12;a++){ printf("az=%d straddle-starts t<k1:%ld t=k1:%ld k1<t<q0:%ld  (mid-start but also window>=q0:%ld)  minF-g on y at completion:",a,st[a][0],st[a][1],st[a][2],st[a][3]);
  for(int i=0;i<60;i++) if(hm[a][i]) printf(" %d:%ld",i-30,hm[a][i]); printf("\n"); } }
