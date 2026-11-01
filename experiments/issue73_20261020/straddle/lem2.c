// Check Lemma 2 (d=0): w in B* (all block words up to length LW), y arbitrary up to LY (all strings),
// every A b in y with F(b) <= min_{[q0,b]}F + 1 has no P2 window [t,b-1] with t>=0.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int s[128],F[129],G[129],q0,LY; long checks=0,viol=0;
int endable(int b){ for(int t=b-3;t>=0;t-=4) if(F[b]==F[t]+1 && G[b]-G[t]==(b-t)*F[t]) return 1; return 0;}
void ydfs(int len,int mn){ if(len-q0>=LY) return;
  for(int v=-1;v<=1;v+=2){ s[len]=v;F[len+1]=F[len]+v;G[len+1]=G[len]+F[len+1];
    if(v>0 && F[len]<=mn+1){ checks++; if(endable(len)){viol++; if(viol<5){for(int i=0;i<=len;i++){if(i==q0)putchar('|');putchar(s[i]>0?'A':'S');}puts(" VIOL");}}}
    int nm=F[len+1]<mn?F[len+1]:mn; ydfs(len+1,nm);} }
const char*B[3]={"SAAA","SSAAAASAAA","A"};
void wdfs(int len,int LW){ q0=len; ydfs(len,F[len]);
  for(int i=0;i<3;i++){int l=strlen(B[i]); if(len+l>LW)continue; for(int j=0;j<l;j++){s[len+j]=B[i][j]=='A'?1:-1;F[len+j+1]=F[len+j]+s[len+j];G[len+j+1]=G[len+j]+F[len+j+1];} wdfs(len+l,LW);} }
int main(int c,char**v){int LW=atoi(v[1]);LY=atoi(v[2]);F[0]=G[0]=0; wdfs(0,LW); printf("LW=%d LY=%d checks=%ld viol=%ld\n",LW,LY,checks,viol);}
