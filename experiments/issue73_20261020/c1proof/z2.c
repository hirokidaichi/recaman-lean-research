// prefix-H settings (d(k1)=0, d>=1 on (k1,q0], d(q0)=1). Stats:
// Az = sum_{u in (k1,q0]} (F(u)-g+1): min.  Also min over u in (k1,q0] of F(u)-g vs a_z.
// Also: Ymin = min over y-prefix b (d>=1,a_y<=1), F(b)<=g, of sum_{u in (q0,b]}(F(u)-F(b)+1).
#include <stdio.h>
#include <stdlib.h>
int s[256],F[257],G[257],D[257],AN[257]; int LW,LY,q0,k1; long minAz=1000000,minY=1000000; long minAzA[20]; int pr=0;
int isw(int b,int t){ return t>=0 && F[b]==F[t]+1 && G[b]-G[t]==(b-t)*F[t]; }
void dfsy(int len,int ay){
  if(len-q0>=LY) return;
  for(int v=-1;v<=1;v+=2){
    s[len]=v; F[len+1]=F[len]+v; G[len+1]=G[len]+F[len+1];
    int nay=ay,nd=D[len],end=0; if(v>0){ for(int t=len-3;t>=0;t-=4) if(isw(len,t)){end=1;break;} }
    if(v<0) nd++; else if(!end){ nay++; if(nay>1) continue;} else nd--;
    int b=len; if(F[b]<=F[k1]){ long Y=(G[b]-G[q0])-(long)(b-q0)*(F[b]-1); if(Y<minY){minY=Y;} }
    if(nd<1) continue; D[len+1]=nd; dfsy(len+1,nay);
  }
}
void dfsw(int len,int lastz){
  if(D[len]==1 && len>0){ q0=len;k1=lastz; int g=F[k1]; long Az=(G[q0]-G[k1])-(long)(q0-k1)*(g-1); int az=AN[q0]-AN[k1]; if(az>19)az=19;
    if(Az<minAzA[az])minAzA[az]=Az; if(Az<1 && pr<8){pr++; for(int i=0;i<q0;i++){if(i==k1)putchar(0x7c);putchar(s[i]>0?65:83);} printf(" az=%d Az=%ld\n",az,Az);} if(Az<minAz)minAz=Az; dfsy(len,0);}
  if(len>=LW) return;
  for(int v=-1;v<=1;v+=2){
    s[len]=v; F[len+1]=F[len]+v; G[len+1]=G[len]+F[len+1];
    int nd=D[len],isn=0,end=0; if(v>0){ for(int t=len-3;t>=0;t-=4) if(isw(len,t)){end=1;break;} }
    if(v<0) nd++; else if(end) nd--; else isn=1; if(nd<0) continue;
    D[len+1]=nd; AN[len+1]=AN[len]+isn; dfsw(len+1,nd==0?len+1:lastz);
  }
}
int main(int c,char**v){ LW=atoi(v[1]); LY=atoi(v[2]); for(int i=0;i<20;i++)minAzA[i]=1000000; dfsw(0,0);
 printf("minAz=%ld minY=%ld\n",minAz,minY); for(int i=0;i<20;i++) if(minAzA[i]<1000000) printf(" az=%d minAz=%ld\n",i,minAzA[i]); }
