// variant of s1az3/mid.c: params LW LY AYMAX YDMIN ZDMIN
// counts mid straddlers (some window start t in (k1,q0), no window start >= q0) with/without S in [q0,b)
#include <stdio.h>
#include <stdlib.h>
int s[256],F[257],G[257],D[257],AN[257]; int q0,k1,LW,LY,AYMAX,YDMIN,ZDMIN; long cS=0,cN=0; int pr=0;
long hist[8][8];
int isw(int b,int t){ return t>=0 && F[b]==F[t]+1 && G[b]-G[t]==(b-t)*F[t]; }
void dfsy(int len,int ay,int ns){
  if(len-q0>=LY) return;
  for(int v=-1;v<=1;v+=2){
    s[len]=v; F[len+1]=F[len]+v; G[len+1]=G[len]+F[len+1];
    int nay=ay,nd=D[len],end=0; if(v>0){ for(int t=len-3;t>=0;t-=4) if(isw(len,t)){end=1;break;} }
    if(v<0) nd++; else if(!end){ nay++; if(nay>AYMAX) continue;} else nd--;
    if(v>0&&end){ int any=0,mid=0,tm=-1,b_L=0; for(int t=len-3;t>=0;t-=4) if(isw(len,t)){ if(t>=q0) any=1; else if(t>k1){ if(!mid||len-t>b_L){b_L=len-t;} mid=1; tm=t;} }
      if(mid){ if(b_L>3){cS++; if(pr<15){pr++; printf("k1=%d t=%d q0=%d b=%d: ",k1,tm,q0,len); for(int i=0;i<=len;i++){ if(i==k1)putchar('['); if(i==tm)putchar('<'); if(i==q0)putchar('|'); putchar(s[i]>0?'A':'S');} printf("  ay=%d\n",nay);} } else {cN++; int x=len-q0; if(x>7)x=7; int y=q0-tm; if(y>7)y=7; hist[x][y]++;} } }
    if(nd<YDMIN) continue;
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
int main(int c,char**v){ LW=atoi(v[1]); LY=atoi(v[2]); AYMAX=atoi(v[3]); YDMIN=atoi(v[4]); dfsw(0,0);
 printf("withS=%ld noS=%ld\n",cS,cN); for(int x=0;x<8;x++)for(int y=0;y<8;y++) if(hist[x][y]) printf(" b-q0=%d q0-t=%d : %ld\n",x,y,hist[x][y]); }
