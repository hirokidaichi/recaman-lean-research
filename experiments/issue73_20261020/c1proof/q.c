// Setting of s1az3/mid.c. Test:
// (P) prefix positivity: for all t<k1: F(k1)-F(t)>=1 and sum_{u in (t,k1]}(F(u)-F(t))>=1.
// (Q) for every clock b in y (b>=q0, prefix with d>=1, a_y<=1) with F(b)<=g, h=F(b)-1: Z(b)=sum_{u in (k1,b]}(F(u)-h) >= 0.
// Qs: same only for A-clocks b that are straddlers. Report min Z.
#include <stdio.h>
#include <stdlib.h>
int s[256],F[257],G[257],D[257]; int q0,k1,LW,LY; long viol=0,violS=0,pviol=0,npos=0; int minZ=1000,minZs=1000; int pr=0;
int isw(int b,int t){ return t>=0 && F[b]==F[t]+1 && G[b]-G[t]==(b-t)*F[t]; }
void dfsy(int len,int ay){
  if(len-q0>=LY) return;
  for(int v=-1;v<=1;v+=2){
    s[len]=v; F[len+1]=F[len]+v; G[len+1]=G[len]+F[len+1];
    int nay=ay,nd=D[len],end=0; if(v>0){ for(int t=len-3;t>=0;t-=4) if(isw(len,t)){end=1;break;} }
    if(v<0) nd++; else if(!end){ nay++; if(nay>1) continue;} else nd--;
    int b=len, g=F[k1];
    if(F[b]<=g){ int h=F[b]-1; long Z=(G[b]-G[k1])-(long)(b-k1)*h; if(Z<minZ)minZ=Z; if(Z<0){viol++; if(pr<10){pr++; for(int i=k1;i<=b;i++){if(i==q0)putchar('|');putchar(s[i]>0?'A':'S');} printf(" Z=%ld\n",Z);} }
      if(v>0&&end){ int any=0; for(int t=len-3;t>=q0;t-=4) if(isw(len,t)) any=1; if(!any){ if(Z<minZs)minZs=Z; if(Z<0)violS++; } } }
    if(nd<1) continue;
    D[len+1]=nd; dfsy(len+1,nay);
  }
}
void dfsw(int len,int lastz){
  if(D[len]==1 && len>0){ q0=len; k1=lastz; 
    for(int t=0;t<k1;t++){ npos++; if(F[k1]-F[t]<1 || (G[k1]-G[t])-(long)(k1-t)*F[t]<1) {pviol++; break;} }
    dfsy(len,0); }
  if(len>=LW) return;
  for(int v=-1;v<=1;v+=2){
    s[len]=v; F[len+1]=F[len]+v; G[len+1]=G[len]+F[len+1];
    int nd=D[len],end=0; if(v>0){ for(int t=len-3;t>=0;t-=4) if(isw(len,t)){end=1;break;} }
    if(v<0) nd++; else if(end) nd--; if(nd<0) continue;
    D[len+1]=nd; dfsw(len+1,nd==0?len+1:lastz);
  }
}
int main(int c,char**v){ LW=atoi(v[1]); LY=atoi(v[2]); dfsw(0,0);
 printf("Q viol=%ld minZ=%d | straddler viol=%ld minZs=%d | prefix-positivity viol (settings)=%ld\n",viol,minZ,violS,minZs,pviol); }
