// case (i): d(q0)=0, y starts with S^4. DFS with a_y<=2, d>=0, d'(from q0+2)>=0.
// At r = first time F=h2+1: record d'(r-1), whether r-1 endable from q0+2, Y(r-1).
#include <stdio.h>
#include <stdlib.h>
int q0,h2,LY,k1; int s[256],F[257],G[257]; long cnt[8][8][2]; long tot=0,shown=0;
int tauof(int b){ for(int t=b-3;t>=0;t-=4) if(F[b]==F[t]+1 && G[b]-G[t]==(b-t)*F[t]) return t; return -1;}
int endfrom(int b,int p){ int t=tauof(b); return t>=p; }
void pr(int len,const char*tag){ for(int i=0;i<len;i++){if(i==q0)putchar('|');putchar(s[i]>0?'A':'S');} printf(" %s\n",tag);}
void dfs(int len,int ay,int dq,int dp,int Y){ // dp = d'(len) for len>=q0+2
  if(len-q0>=LY) return;
  for(int v=-1;v<=1;v+=2){
    if(len-q0<4 && v>0) continue;
    s[len]=v; F[len+1]=F[len]+v; G[len+1]=G[len]+F[len+1];
    int nay=ay,ndq=dq,ndp=dp,nY=Y; int t=-1;
    if(v<0){ ndq++; if(len>=q0+2) ndp++; }
    else { t=tauof(len); if(t<0){nay++; if(nay>2) continue;} else { ndq--; if(ndq<0) continue;
        if(len>=q0+2){ if(t>=q0+2) ndp--; else nY++; } } }
    if(len>=q0+2 && ndp<0) continue;
    if(F[len+1]==h2+1){ // r = len+1 first time
      int e2 = (v>0 && t>=q0+2);
      cnt[dp<8?dp:7][Y<8?Y:7][e2]++; tot++;
      if((dp!=0||e2) && shown<20){shown++; char b[80]; sprintf(b,"dp(r-1)=%d Y=%d e2=%d tau=%d",dp,Y,e2,t-q0); pr(len+1,b);}
      continue; // stop at r
    }
    dfs(len+1,nay,ndq,ndp,nY);
  }
}
int main(int argc,char**argv){int L=atoi(argv[1]); LY=atoi(argv[2]);
 for(long m=0;m<(1L<<L);m++){ q0=L; F[0]=G[0]=0;
   for(int i=0;i<L;i++){ s[i]=((m>>i)&1)?1:-1; F[i+1]=F[i]+s[i]; G[i+1]=G[i]+F[i+1]; }
   int dw=0,ok=1; for(int b=0;b<q0;b++){ if(s[b]<0) dw++; else if(tauof(b)>=0) dw--; if(dw<0){ok=0;break;} }
   if(!ok||dw!=0) continue; h2=F[q0]; dfs(q0,0,0,0,0); }
 printf("tot=%ld\n",tot); for(int a=0;a<8;a++)for(int b=0;b<8;b++)for(int c=0;c<2;c++) if(cnt[a][b][c]) printf("dp=%d Y=%d e2=%d : %ld\n",a,b,c,cnt[a][b][c]);
}
